-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3302
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:15:38.46099+00:00
-- url     : https://prove2.me/submissions/169eb2e8-4f86-4a94-9b8c-62b05cd8f72c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 593705035 ≤ n < 593884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 593706285 1250 593705035 593705041
    0x611031803120601050a1b06090b0c1305060705070302180402040513020105031b0f0a110f0c030703151d03120702010b010e130e07080304180902010c0b090f0706030b18 74
    0x5030b4051116440807080c24210303564041c1543c00c61b104c0940d07012103809903010280c400c04215071074000401c40d5014002c1d560864588540d40503042c8541c04052180d100852020003107414800c0140038505d01420645061507034a4003c65110080d8003441245003800c84100801c514140c425142c0105000d402c1000200381d1b503001a0880c8809801002d024004019160100020038202c44a02880500f550b0f1a0303150114041e1016400344002d88890044104a090000c40060601c219801c002c0040000b50301c1c0d52a29409003000551820300315031941c0c000c0000c01c9459903510041d4440d5001180e603001440c2e0985003108010f04020110b905040d001030aaaa0100d02d02000038001c40e0100b0111a10741c1040c0010a003800c0c0c1d8a040740180c62001a10b10720101c058411619001c600d4101d421240800d90202c9485001c0240420500c061070000b042a642c2110b5000483e901202c40c2c40640311410303458841580d108200094407044118105c1c1841d10007806022245110304005003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 593707535 1250 593706285 593706307
    0x1b0b030c0c160e011e03140703140c030a17040f03080d0507030605030d122301081c020d0305090c15090111060402150c16030305030103021e0a150c0611031803 70
    0x5281881004520804801041700b00408081060f0045074032a032800781021040d60141d07164101440191b42c0020130340e44042d541d41002c20401d9404000401130040809195180102a4000d240280481c081400046001403030f0811420266000c1c0e01056262410303020103006681004244008150815004103d6034800242e00c005407007a50800360440403034148100024106070760701190750800008144951440c01161505aa0f1000e0a5802c5400319000b02450440b0003004240160710ac04d003038150503880303540301c203810180b00416100000002800940e044214015080040780c000a455155680169081000c0198000038281c1032402d6000249061021424002404800640e250007200140f061001c0000e109001d0411903860b402c0080480e0024001203000d0f802d0300111500302040302c00082071501d00140100540b41c2480b02d40a511118051404c0a001842c00c2d50350006070140607030a850041c0c00c04081d180c1c942009401403034401c690115107190802c01c0301d00350701 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 593708785 1250 593707535 593707559
    0x1003060f0e1203151f2a020f0d020d0302010b0306060a03020a1a090904060504050d1d0d031806230405130908161101030605090c071b0b030c0c16 64
    0x20781045010b054880d0b9039108410b504402e00d050803940320003000c803000704000000c00e0a0328880d149a41d008040090340c2c044a1105002004e44000030b2144141c5900500e040c01004040f0b0714007920078801c5007415070200380c0f6103d00c6003040700580d450303500072185420208400d645c0078000322284c04020b482c513008a801c000e224054001c002c2042100240035800c24021560104806000901b0a28090500c03100a12081c0c83c200e441d030056400c0c49907014031071600300c0302c0070f081d001c07031621030010400c10030200001c0100c0c01c80a01075404d090b00310b142c4802c422a801480c0b240c5650a4054064003030341c44000411201c8088120148014003942d210450303148074074640070100281d04d40701402e20341c2c5940182c854445000740380e50809002c01880c0c2400311540407003a00e090040c00d427200c0800c5078030041250b40080802050007400c1c00309070007441081078110070b001c0c004d14035a107840c841402e0707034412544240a050b0000e86162034503020480c070040b041400000402007400c04010f0030b00e07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 593710035 1250 593708785 593708803
    0x5030d0e0706120b030a051c03060e060a180f060f0806010503031305090c0c100f0f050402030606130b09010608071d0d141c0e0a05010c0506060d0f05061003060f0e 72
    0x4100d513955a41d64640c0c80400042c1c040c0c0f42c00004031a03138880c1a02c80401807441d45154240000d040c000000303a05140c501040d17018001c02050b0030034090402036a10b030566490f540541041e40c42e0b004c0032407041e9003841040090041d1003444034106061903127140c98248181e1095020740d10420042c803242030710f5080b4201303a850407230382d6036203503240e214034440d442c0144103c000e03250054416002585103503030f001e03401d90301f80319105000d000d440702203810403604100c401039015002540020340f1841d0404480c0c10f500b04c40303580042e402e40c0c0e01c070204241c404240c06c02008151460248503819400c50441c0d0716010b81c009040c00300a5460001c03541c002924000201a18140003904c2c14a0300140182c00c2401c403000e20795444041820002841e886541e80580e0050f1190040814154442d0000b00310583d0410010211611800141f009203880340505562070f61301c003115134000030802d002d424001d040c4883c0412070703d420b50401d801180c80700c0c078003615068601490349000400101c0e814803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 593711285 1250 593710035 593710067
    0x50f0307030f0f1b060f0c1104050a020705011b032f0f0c030a02010902041b2c360403020d0c1407091508030a0c150f0905030d0e0706 59
    0x25210b021807401a03180c88003000d000b4000321000d80b503003800880d800c5102044400541c0c031440da03900b200b0019113800107125000350500e05200102002800d03e5001550000380d101401894100c1365102c050864004403030224200f800a13409601c0f42c0e92500501a0040300d000d5071240303080391900086a0300400302200310946030b01081829030543c0e40e0041d221440302c03d005a039911044640000d00901422908a2080c0c0c500084521021210394500d0b030a501d51b500c502045d4048161040714003440d075584403481c5a14802064504d0b1a204c4480b91020020742920490441000c5080c07101500f54203015900580c0c032082001196001034403403144d41d014100f2005d80c06083c14031590401640344012058820440d000801c03079903030f03404103103100260340d0742403074403a00d0307103651900e038421080040000340a0310b0789400816910039014440c988064000030b054014140e0041c281d450207002070356190000718040c804074600e0f024401c001001c100181c410942405400341920768070f40c0440e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 593712535 1250 593711285 593711303
    0x9010603061511030f0408010902090106031506120902041b12020a08130f0203071203090b0a05091c0f0305030405100c05220b03100816030201050f030402210c0109050f030703 77
    0x546240c03c00e00459000030490503590740c0d1140c80e01c01c44c40c0a0001910100e0140100c140001000d51083c42100040d0b0300550882d824203162000849048100c440c15481d072655421414005076524801c0341c00031500010360b10200c010014014003803c0104441d171558500401600b50140e92012450345c1c0801c240d00990003004007405c03c18900c0042c0c50000f5007512800c88082006812100c0501a5a01c00d41e20290780a8480d4144001800340e0030140d030200b90103212490081c6416a030302d4002145440002401070031603200c00c8441c0406001c1030b00072510010500c02807110a0000c21000c18040f042404103000e0700000500500c241c08031480a82e001408070419a11886069801800c440140503103a04101d89500020b0065104469542c032655141141314002d034800402165016112036080241420000d001584000c004076030003101e001c08001442c14802c0100680440c5900030800c0141c03000000d8060901500154464100740e0f80d284000d94002546100752a840070180e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 593713785 1250 593712535 593712557
    0x111207050c01060b0301150203040806220516030204060e0f01210f051c140f0a0e10020c011803020d060902061c020a090609030201020a0b09031b010b090106030615 72
    0x80340c0c540a0a41580700c65401e000000607a2491200514141c4041c0d00100d901442910f005907520f2085111310312039504084000741c0440450700050116034103408104400051599625084c01003000c90700d40601210359040c4207504062080c00090015207101f1209803c0244507055901014070581000080c0c4580d641b1000795014140c900e41648030b02c00d09006280d42c900341c3d40b0f46608a9481c0390441300c4c00030b6020303520f11500390013040f892210003491800c0d964044000350756102c0c1c03040c40244800000400d49035283d90300c20305242c0d5042d40c003402040700300d00c0004003464198104012030b070350350b1102071004d0380d100032984210660200002425184a1000c03030f242e402184000804144070b8801c401d010b0900b03400070041407850341d482450b0113444a00559403505140000707401039004075002000509d610105170f0308000f506084074140b0340c0140e0031402600703010400302e4507030751241a440801e0816000140c090959810300340012420181d540d0000f007040d11480c42000714207184 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 593715035 1250 593713785 593713787
    0xf021203090c3615030109080301060f020717100609020309030a0c020f0612010f05220c030905030316120606050703080403050906160203060603010b0a061d030706030e10111207 78
    0x22455644281d040b2440040000490000690480b60b5500f18101510011300914041c820036048541c8214114296400d06000700d6101820204484c154810044045051407450020120040e4840000d02d09000c42140a20541d0401d078003654520f0700610a100d41d0b20804802c0c1c41e0701d22954581290003161500003d02a2030b1030085040c1c10034000140543d0500f01d40b00958180c4035500c0505198a40c2e8609200c024400c2c040c02c5444484031040807180343c0f0031038104501d0508249000300d0040f0b883d850786c41c11540b05885000720360348442c8540075080d40100b4130b511009a404c0c0c00308946490039038041c18601c02d001c401000c1003007540004007090b0240084e20b44441c0040c02150721409000100350304801190fa05070710a100d81000200d031464140104003410310080d01c007542040c03a1440940d02501043d401080304c2000081d42d03d45074800300f10700303402801540e4000c21698649031350310703041c107001501640440b414600c0c0c10012001c0c24040743c030740d0014000f0107031481e661100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 593716285 1250 593715035 593715079
    0x8010c0e0a061404031e050d0906050a050904150602010f140f0402010804031103030114120c010c020906010e0429010f0207140103020f0c06010812040f1214030a0f021203090c 77
    0xc00c03140518000340c031140142d0f03d14000c200c0c0725004807008c840700490255000003081c455003002034400c000500e400b034800c0d4040d04441c41c010708081074400c18141c040b022800c054200c003006039902c520b40220f00c961030098003900407404c11004803d042c894421810010000c0001c4d040c0b021550105007054400c2e401c000c95080030a00b91394407544c44200c1140140c400c4040240b06130359416100d0710fa201c3c08541408003ca05844810b0f82c1c09080d800c4c840200c85c0200910306020314401004800c0e00c46016051054103039048920011444180d42040c05e629030a42604000b2540c010011254002503800705541119002030080c81c101e0340100d000c0d00c100b07541e0401d49400420744c50140340002690364140d405036010b43d5119140a5800305050240d807180c028920814101040004108185064403074090351401c006004400c040d1880c65001007846c10001d03002032070302c2e0780c1c0503818044605403070101640545181020042590344000d001300180c0f1416107024102c4c24404414 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 593717535 1250 593716285 593716289
    0x70f020d0b0114010206010605160201030c0e04020f04030b0c120c0d0b0d060504032c0108040203010609060e07030e06040b22150c030f06080303220b1008010c0e0a061404 75
    0x11481c1116603150200e50a0395081e416042d400b5200e020004185140030320191101e15481d84080307003107514582c00460203003404041c03850905c4100d142042d41e58613280001c00a0355a0815400d0b5203d15601d040810382100801c1018000c2c1c060003120742400c2c1040c6200d030008444031003c3d488501c84000c2100501400c0d403196448103103104035004000c49900418406ca00a4480e11030300c0348207455158010410244581c5c0b152210b280c1f003d40c40d8041d01d1080d812038006800080c202d074485001d2000c4403002c1d0807000c1d140d6000b408101d2885c0c1c0c140030301459a01f500d03000c0c02d800d04141e55072401c111009090f11a200d08066840b05030b01c1910159116203503003049070030040c51441c1c0c102c80001c0103ca440a00083d081450003110000203004034000c5804d100c0c001c501d51340d141c008080b40890507035042c44c1408010400341003c40c45101100d070044e0909030304d817040ea52418090900b160b48045001080c0315120740138910703d61307403c203031001200c1c190b05120f0158180e200c60b1428910540d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 593718785 1250 593717535 593717543
    0x90c0402040e0a05150f15041a090a0b0a0e0409020f040c051e071218080a0812060f030c090604090c1d1b031501111014130503070f020d 60
    0xc01e0001d03901801c07566450044004000401441c0c807400c000981841c0c0f00642c041d08076001d100f0b411300070308242003e080040041c6030702c03e00f0a80c4484070a402c01e000c5c10400c40040c00080390300305041c50190075103401411850501883c0c61a42d10004e0700c43c5030684c8165203c2c41e81c0706000001e43d02c4a0b003101e207082074014002c00500030880ca003e001c0340c01c00d481401a9901810040c003154003034208403000240c02c030b140e800c000507043d0011a91204c0000400d10360903102880001c150320100a0301840f9489010300c0d54840503842c00c0d100c2c62210040c903c07031040052450040f56a1000b0035103070280802503c04640503503950001c41d018000f40d0310b00601d83c4941c100c0000c0c2c010721004240d0600c01c40804200307603549802c2c0409514000890603020071150030000700321175408014000001039410304240c03a1601e070f0f0701e0340b99050248600d91091040e0b11041c02403071140101a40e280d02c1440b042031091301c0c00494488a61700c1c015920010007103070005c4240401d5650711241340030100e0380 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 593720035 1250 593718785 593718787
    0x608190204030f0b0406050c04180b03070f0b04080d0311070f0203190503030105100f050d180b0f0702061b2a01110c0f0d1b0c0f060309020a05060909010b03090c0402 73
    0x344c41c0128185008031400e0740d140e03103010041070fa9029001c045408942c201440e09a8020041040c240140300b035004065040c800d01c000016001c3c0c030820340c50011b103513105525440354036105445051102ca9454541090714106100780165400025100c215801ca9003c441d100a1440428074142408118181c0c00d0000100030081040000c000e40c10b881044d210a4400217048109407412107400c2c244901051082c4485840c0d04860b9010304600540d00710028803070001511542280802910500349440c0c10b1010403c400350100701c0300340c00c0004088100e20340700e14036030944650300032203500040111100e4201d80c110403948020302c2104600c98002c228603840d80b007080d0b4296010038403a00b842e0165902225030500d01041d107801c030200b180c0790440e8000500c00354800c00ca25500d81210080b19140020410104c040c518102408844e10006500d8141d40100940c21241c0e9000c1849201c041045030072549031031210504503040782020076266103074a444241401c0070f2042a0b600b00f44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 593721285 1250 593720035 593720063
    0x100b100c23010b010311090916020721021c170a021213060f08010e0f0606130807060929160f0302031b06070215070504030501092109060819020403 65
    0x48190b2041029003c2624104150001107045003200e004224601c6d6210310684001080c5000620125580c200640b05441c1030a2700d0380400410741c000111840a40c0a030b144010085042520b40342d071021080508903040c900311941d485104c8c0756081131020307180d9030215103c595607008001440070041d648942a890303030704116001e03901041612841000405104a0a515500070b10405058032040b1300303104003d40d54030a9030001c104014040c9a003000c41000102072500c2e42243c0300d40a0001e84c0060418140f803e5001442040c1c035401004603400f44441c0300165480000f208004031944810164a68008a403018400c9005100c041d100c10f10f03a1046108040e40071000300f008603043c5196105961000e40d4542d51180201d85040140e0f0000d400d2045d4130403a482d0030355000340545009031805440742d035102c3c2941d401440842c0c40d5000030007500d01002007010b00d00b18a61062801020300c5151940c000d01d100d070301506001c100a00030640c8560341080340c04072405142c200c1c50540320f9203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 593722535 1250 593721285 593721353
    0x120e03030f0d06121101050313081315020312040b040302070803030906010509130b06010c061b030f05070806101202210603120c0a02010e060409110705100b100c 71
    0x60b02101d00d41c141180351042c080744400140c02290304268020340000b0781113007101e0041d201680701401c1010360200e100d400e98001012440280a00070b000c00000302d040e8030304000c00c001028506200415508240722036200205e080407442d500a030415030b92056a2a24281a81030201942000d082400f000040201a070320000740e03141201e074159003000e081e43e2502c090304648020300c40020041c00701000403610710341c440c19034140090b000c0c84000643c2d10502d9405100c690f140380c0c41002294540081421400c130310722400f5445085400d18446629054001402040300c040e028800d2007005515209006056815111122041d8041007911003007080300d003528000440c5c01034441c1c4070380e00010b4007412801003a40c920340705200c028400310707902d42d0040d81e1f06081d00c052030b5084001803000141c0a20300e40502c20345180c0210450366240320318184942003060b0650440380341828415031030343c1a110041d008001810074641510780c000240361058080902161099500c051905140019 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 593723785 1250 593722535 593722537
    0xe01021b2b05061803040b12060a0506130330080702010e07060c050c1e0f03030f04090203010513051e090f0d0e0a08010605030a0f031107090f060819120e03030f 71
    0x80c00c044d030904802c0c28400c6201558900c01c070f0042c004280d009001c1460078240b40009150008001080e2000760364840c070200d00c44d500a1400c44950a00c044020070500c65903101e5500b030001d1180084041007814124002c0e007d004d244c907082003104d00400a00d0940c805c0d8026001c1c160b58000b500c0b091983c5850041800c0102d180c140c40320301070000c4c0b080c00c07840d01c0041d00600a0803c2d5120400c403c1c14002c201c4142c9000060700d4041c0401c010300000d154080f801032003c4e040c02a401603c1e94104010b0124003407421a904007030300c1c60300b42800184107220501c01c0040b0319551410a1a41d40e0700219810300c100e985000145202e840c81400c0c3e41500005980741401d810b80700031110316655801c95003030319414402c0d1074043d04520b203010040341a03420034000070750203400c0c9100b541840d0480980761400d150310840c0e03010781d25038240301d2191181c060600104000001031211130100e118000010300581e000500d4a030307040603080c8060740038010044c0c56013401015651100b0050800c1025 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 593725035 1250 593723785 593723791
    0x909020405010602030c07032006030a1d151902041d04530301080319050316080603010b0315040b061c060207060b0d05030a0e01021b2b0506 62
    0x108a091100101e400d1348000140c07200c00d0807003002404110700d1602c900e11921a181038980921408210805e02c646401004500404400000003035900e91507182521f2038040000c100087d401c1508000403190584c0780150b00842c940031000e040072000d116900c001d2185500c400e40020740d00740a480c3d0380117204591031049005020070804c9900071030a03101100840111450010b5103008004034403000942c440714040b01e4100c070f4000c1c1250807a0304544a0700300b64010155a400003403030441540d01c010140e420301e80c250410f903045051a0b43c61400015008901100f0000c0d00c400040c40d554094010784c00030350303000c0c060740c1001e1440c250001c50001c0458050702e2425070309010032080d04100460302400c5a050079002c0c04281d20780d551070069404000306070352840d203650329160b140e9501004054020f01c100021039172603502403409480d4281082c800d9055402c00100a4203500c0c0c1d611603450420030848400c8070285243c00c5411040110207010107010b40340c040c110040080001d21140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 593726285 1250 593725035 593725039
    0x10c02060a11160f0f050f0c1e0d030210050718050d17070303020c06012c0906070e030106080118170301060f0f021f2705030f0f0f0301090902 63
    0xe80c9a8801d03640e8029611100c1c8442c1505404100e0003039038078600b0f488a10f45501c01c0d5032803040070250340c50724610101c140e80103483d540c22000008959040c04c012030300d080307d01034581c0c003400d244c800880030303441200e880424020700d08008880c08140c400e1000400b0505070074010080b6051205000300380ba91705012052949a81c100041000d05e040031011303403010f9000c6c040000361010405030701e18541001c013089003410b03000d01031502c1583d0107010140c06040d440002e54803007102180108411025400c10540e0015007400b4407c03607070804110140e10007440c0c24681032402e00040484d005041550101995500c1c0c100038140e0b070301050404451241c042ca9109a403c0480c0d03c00402502c000e00c580004140c034074039a02c0c1098081c40b200c00c5045258010340302c44002507000208901190a451404580d803144054104050700b0a08841c502d4100c0c0d201c0c1c0301c14110380c0c0e15a0b991141d02103c1c0009103000c5014880c20021504941920b010710603c076840e541d40d03601d2507000e40a401e100300c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 593727535 1250 593726285 593726293
    0x5070c1b05040605150703200609030904050705070c03021917030301091d061b07060f0e0d020c06120405070b0d020418111c060801020f1317030307270305010c02 71
    0x281600e00320030150701c2d170391140318414a0320380190b400f6100c00c4c6c4442081c4c003030a605c5060300c202c0d0000512110307220b000fa141c0074550369108041008110b800c000c2c4503e0070b000017402840045101c04d041d240030349505a460a0b280e5410100c0341d80d150156a00200c001014202e0848403c007020001e94100e650086040c49100e62242160412265100c6801f40a034008000685602503210080a039011402461440c0079455115602074903050035554004603243c3c803403118030810803c00c112408140c1d10240081038602c600080c1c0030310500d039008003107200f1038003c6014400d05010590041851390303980d941d50001448104040d4106216000c178032403034407844d8074200d5843c0c05a6220756103072566aa20307088814042c15600300d50358014803000c543d2444045220b0700c0904c020680c00d02c04d43c4201d030710740e40d44819012070a0040c2d0812480c03941d81c0c0f402031071701d42400015a034204103a0b0910010741100c254110007124000100240d00000039640002840410752203149040215802d603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 593728785 1250 593727535 593727539
    0x1e060601110d05030a060302120a020901080d0f050d0e0f1e1605060a0908030307030905121812010b0904140c10210f0609020318010507080a05070c1b050406 69
    0x54442142401062616400c68200100c42c40c0c4150003c560002040e680014030030b4490300443c90a0b01c0c0100080d0041d1300800c4840294900b103403200c2d0051160a0081003c1d80643c000104112140030014052000100d00b641085020340c0008440d202c00c241107031101c1c11400c01c8103a03580404040880744901100c5483c141c240b0200c0e221014080c001c02d2074584615100c14000785030321505140382004251403010440b80ca003440114000c1c10150b85c04141e4001030300341541000401003403008000010407a1038000106505081c03a210011511901c000040030238150142ca19903500b0b5601656000c2004104190b5a20714401c07600e940c0211000031454006012508100d9155403000c21a40549003600405820f12148140c9503d0404034017004051100410b0301d2480d0407581402e5004000c004000c1001c0384501101e10240000f4811414540b0002d401031001400324034180343c07130310300044100d4040d038403803500345070b01001c1d0081c40024000011101d01c00d5001d52031080b4149100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 593730035 1250 593728785 593728787
    0xe01061e03030801050105031f1e0902030f040609020a120506220b0109050c0c07080d020c09040803040204050a1805010c031a0102100f06050a080a03080a0612060f0e1e060601 77
    0x125030035258152182c907004d0742007074019203454200400e066038031448080207a00d40300c003410419009240300541c540c0461018040803410304c089800c8114850302c10300400c2460715404450541081c0c222000069011032400072501c40b4180303400441403916020040e0081010024000748030b42e03004250030000400e50b2807808075035125410b020701300004100c018868400c00f640540e41061518444500d0220700814190414245603c141115001300304594030498041c00052503608084a083c0c0c06441c1c0303a980c200640c00054000f85c0201d03501e100084054055038003811a254070a007000d80140320528056000e443d00040e07a00000c0c4c1401101c0b20032042074080d40c03882c83c505802803c1d51840f0800484020801006560302e0503448003030001d0760b6100c07151403101404140000d8401401c1e141000340c00750101600c1d03003540da4034008007085007900803004109038550001002c0759129207020344c01c0281064250000540c0100466456025105004a81642c809005482c515511000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 593731285 1250 593730035 593730089
    0x9060409020d060f020415051c05070801140a050d080c0114012126280e04200c030703170708041e0f0b0a18110f0a0503010e0106 57
    0x203401c000c04030200b000166942c0c121020100000d000181400d549042e54022090030120314804103600180d00d00c50f940d001040d20b02024410780c414481401e140c1c80041c42c0840520400b2400d003080c203507100050755040407804c0204002040203003410704601305800254003580110301c2c40e6103080790021048007001c1220341202c401c065a003241d5110303c85039614614079044c04070380d109502031a0781c00c85900c890394927034452401c00103580c032103c84030040300385c40c03030640c07980030050015400460aa56000031481007000b0266400705a1256a980a007089808805425031402010403007041295001020340002806942e82c02900c0d03040d54050790f56480180ea5400c00a0125000100407444d805500f0302d45801e4003034107080864103070326004141000c0e10001c444950381d22060141c00c1d00b03d401070000c5004a410081c41c01440c59a07441c070340b0000000224050031a184581c000c035a140c08190000b480c020b8001d000344200d041030a80200524060b0412070120300c0c0d0010980b40d680c1c0c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 593732535 1250 593731285 593731301
    0x804151b05030a11030f0c060414010912031113030302011a01051201120c0b0d09060b0f01020718020c1005071812060506120d1125090207081201060e090604 69
    0x401030b5280c0710981c001200d0011159510000620082009030b140130070010003452020070006c050f2180741003a10f048417150184410202d46681040c44100104104000d540850100390400184115054085c0c406074000d03025001107555a50341d001081c0742c0c041d0040b01c08a20007405030524803810340c0c010749060003180245c492007040080140704c0c8450350320842220a0007003c095200303a039900b0a080e5079a02c241c650980251f1030350340b44000c102d40303800b40c0c512114003224840f440111420000b0743d604442c4c070500700000da0461540444440c254100c840c20780f081e80c20740d0f100c4503119804002401c400d07500200003503040702c240802030307108244081c140e550f01503080c40c0c0320394a51111800ba003000f4110380c5c0d22010b000003000740440100010611182d45468440d4000044145a410b000f05a40003083c103817a07000c149620715001c0c500c407106850f0035583c0161208141c1c20020b19038000c1882c0400181e00c8440041485500f00c1d8503d01c408408075421255551854144002e1f034000c9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 593733785 1250 593732535 593732543
    0x6171c050f072307030804050915032a030a20060a021504020f060d0b0f09070e040e070e072c1f0c02090a060302090901060522090804151b 61
    0x5200c1540060300c4030308041e5900702544003010b405001c0002e080d00780204d643c4100d5241303c00140030802410401000e6a01c03411000381040c40d0907030300340401c1d12240c0019422084071070f003c0190075510010000005090303000780848011220518007440081041101070710003c8555291090310f16014044510b629001d9000d80600120001c900300d0361a0702505c120f0703010101a406441c4c907100c0700013400c070900c040c1101240340705c1c007034050003d811a22401e4501940d1000100684030382c0055944601c44026280000c02c0001d44e5484d030b0801100b604821503c0074840148203081360b116001401c0440496030051402c0c8030184010005100e1045141c0c01103e1000700d40d507440800220459404a582068640398115a000900861080707070418481070795048144154102030840c0340d4051800002004040d0900c03000900c211009816194103c1c41d140c0c4d0021030082c02c0e000882090350003031041e501d80703840d2810109081c800071100d100041803001c15000280521307183c0b8441d6070300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 593735035 1250 593733785 593733787
    0x20901030b120c090702030910091806030b0c0c0a060f0209190e0411010e031501180908072604081c0309260705060a0222030c0909030306171c050f 65
    0x1d00f00a024101c600107125100390f01082c03040b40e000c4d0320b8402001007082825170300d80211905219541c4101150b42c10b8402040c0d14040003440081c20860510350440362901090f6200e0002d030480a1620b0581c0a004207441d09080040e00c0301c030f5440c1c019148185007201c1010504441c4240072094151034030031030a0068561b00400c012030700740175040c0b400c2081890001002e12084000c03a280000740468000c1781c04003000100510104441410400b02d80c1035414400d10209456107111b42c000d1410141c0445828800f8040c00106a04203811818090781300315166580e03045256265081419512035807501c0b4100411464420b21404003540d9102c07207054601520071901c52000d4000703000b10803035076200304a4030021030303400c00085105043c0e034080960303100014240c6804003003241e1402c0d44000300d820000c0c40001d0723001450b0341c180c0e107450400251110345401c04801410342ea60104c0302070b24500c0611300d03100748041448520103103c0c2e034030240d03941038420088441d44600c1895284201c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 593736285 1250 593735035 593735053
    0x50c03070f031d1f1a010909050a06170d02011103061f0216030503090a1403030703080a0617061b03070905010e030307050312040303150308070f0215040603020901030b12 75
    0x30080d841004040c3c108407207081d10503410020a8513281c1c2441114000752030901e441c56095000703004843c005030710070200304c0e0304540d81c07400a00b80700e0b0b06000300e01e05242c0750800681806581d501541c002e0101c10484420f45514070b1045441e070942d50b180400550a01002d0401a0480e8003142d0041d04040d2003083c48005d00c58000300c0d0300000f20044001c41c000c00240c42c1b4941e0b260076201e40138500850185941d880a01c041000005940d0700080c02c0410448000c80c0d03903540401070b1451650075051400e01540d500c4c401c0350041c17902e50000c04050207c0030b07282d42440c0740000c42a205982202403104034010f0003898441d603003c100c0b05a000640030800c1480a94820102c03002e51180240c01c407400c02007941d07681270841e00301c2c118021120101c03074108000e0580c5401449015159209007040480c15602d5803841441403440103004e901e098903080085460356191190352401000c8692f0700c46072240401006940081802c90000b41016030155041c030b00488800c0e104100324000b4103c6c16 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 593737535 1250 593736285 593736287
    0x40306020310031b210309170f0d03140a05090c0112090506040f03202a09090106050111010506060d0c09150806120f060612011104030b0a050c03070f 66
    0x26000030403031500c042d034180c0c00000190260740c15086104c94209000a000d0400e545120a0200302a840b40030079440707000100882e400004050690342010b04505c01510545001c5240c00b03034119091701c081c03050505e008422540340c0c1c4003080049001c12a80020345a820140c0141e4900303584404170360f00320902074040c5601400c043e000c0303c1c40014012a203032905442c0c450800d28112015a40c1c0d88100f0307600010503910524400700701c0038612030685800d4211055690712180b0900480c29484180340011084000640303200c80c2c20030042031b9011601e4801c145038041c004605c81c040c0440c03501c003084040b420040c040c0d580319103c05001ca07410101009aa4000352103500c041105102c1c1d00007010414a0031085000010503594880700d00c0e0b401d080c03080c800700c40c40080f02c0310b180d60001100e800f90402c01042e6150406000c540560380000003841490040030100070740e214420b00010001304100d0344981242c881c03001d680c01040079a03640c0426008a10003240c4540000c0c02042d8014a01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 593738785 1250 593737535 593737537
    0x12010f0e2e05060c280b062101050a0b01030f1103040809040905070f05090703020403050d0c0c080717370f12030b090601090506121e070c11031204030602 68
    0x82625203480509079641c0b6804150103500c4400201e0454125400d03501c0e1a004040300403008207000b03001448841000c1d160420700c0ca4014040a01c1142c00e520403d80300800c00070b4907042031000c60300801560404d40c54500c01002c84844040c003003030904c490b50001c1d1036079101c1c3e10444046060004d18558443d41c841641c0c0d40004607841d40266260760900c003207041000528050f00d0f813000154000c60405040241c0c0c0f440c010040e0b010140108024000104003181d101804001420010007101a600d8400300c40c0415801981c00f500c030b03145000640800380c9804403280d91f414401e5075050380b0b0702113010104901c40c903204100507418070081d603296400c0c1c4101d541e08501039a04010229865551213032104443d000c10b07000130b51104542d007028508440d40c01d40111090030301d0358803a440c1901140c00d5000e09401d04070507440000008680844498820402d0b1500840c107440900d01424080c01114401e0170030f403540c622005107080030b03041c001903000c0c0000040d0401c5d41400e155603100806 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 593740035 1250 593738785 593738851
    0x405060307150302130317130b0403080a0f030902060310141813150212070806180105011206091503030908010507020a121b06050a0b010c0b2a12010f0e 67
    0x2110451302c400001147c42010000340c688444480700c1e070b0711200d450341c805801a9a401c6031102042c20001000056111411070f504c1803024245203e05290410303096006145442e0081d402000020800c0307612010803511505640d2807005004504615400f0f1100100548420440c80701109010170404420782d1164624113100d200303018072b07032910010f6800580c1c0203040000b9800c0101c0041c0314440317030805011580070205889510683c0c90001c0841c0c1c0000c0e06104060510840e1404c01007042007540015003d010002001d00449160f00840e40340c10b500784c4030540c0040c11100012a0389030701806850f010303030941e40c0148181109500d81c4445451902c0300101030210095014122150441e003260300f030ba0148200044030314100c98518181d45035030845038100321211041c240051b00e0078a200e90452087c1d4070301e0008040000004100e130074560350060b08448041000c1501951040e00c960684040e40701d0940b1450b031310084000080e03001e890300560f20040c5803400c5025020340800d000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 593741285 1250 593740035 593740057
    0x718110304060e1c0801050f0d050a06020313050708071a0c0607050904140a0b04180206030f06033a090b071502041a0d06060801030c150c061a0405060307150302 71
    0x150355420300113807820f1190121400404115158010010b80c038041075404420030041c0c42c811043c0c5038a984958948070602001800d803076020022079181c040725040000700075480710444071056121021240d86614a2144001c3d460105a800d00321149070f40c01e44075100702400040a464032011015940c42d080651030540169031184581c80a50701011316900403607103100c0018241d038889003804141c4a609003e1240f1050180e904401a215001201c0d8005201281000103495010001e41842c0e0f003401401074400445003540100d000ba055913010340014401004e56440000038282c2e8091114420345041401c20320203600403411140d03e802040d141044014a05a1220100342091040200ea001c09a202140194200205118641c05002c084c2040d01c02036245a0b920060141140901014000703122040480c181c09100e26a90403a030000c3d0510202078110711018000e8190201d03648141d050001140f058100031a03108142c41c54100000b100140240c800d501030b5000c100c0d809 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 593742535 1250 593741285 593741293
    0x130201031b0e131104050103090c0506040816081501060f0c020316030c09060528030210030e06100b2505060702010912051804050c07140718110304060e 67
    0x4400d01025512500040459222403880c000b400e4107000b0032402c1919510310103450001c40e00341201c0c2c500190317811139400740303404105000d007483c0a14103900e5a50000303801030004500814201c00105a003014050301c009220380640d80d410315036a075004080c8030440745811a40061181e107104a0030030000c01d582d82000150307018607601017481d004803600140c6c0c4c00d401840d000d100300080442c0800c000c2c0014401440301e103080100080091580c1529034690448288590f003026003443c0039000211340090200d99410240c00740035015003041d1a52072041e0091600194116000c1003024007132b5075001065a00f448400c815248060403d2850444c0600018100f040000c030204000e42c440d03c2591b001103500d400900e0145000e9007240145400e00209200e00503212003a56032442d5220001c40b07001c14161a841c48849040c8a140303406885260b41d04801000c000001031800e0840c0c010001716038100c6454848071080300c03e4080300350085a010004130700802e00a8110094040a40c82aa = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 593743785 1250 593742535 593742551
    0x901120c0512070207090f1a102a02010f210f020c0303010b1201080a03080a110f070525030b0604050402151801080c0313032007080f0606040209030613020103 70
    0x8808180401c0324043c0050340002c00900181025000ba04480054103a00703016203150550a554244a2400254082c4a1206010030228800c5481c5042c6000b0810303981065926500110b80752a10b0000a03408120011100c2200c0c52050150203d078501c1c030361000740e510140031304c001c1c0507102001140565175028401c80c0d10403402030000707500030b2204020a40c0c0d55040c0c0842d640c032481c030507448984036030060038080f00800d800591165201142d10700014220380b04008824150040299120000c0e001107202c00810100140710015118040000d484001d503196150200320070034040101404098008221281016000706402910051015842c44c03181100d241080e000030f100c40b0000d40411290102c00c0d600b101a00390010080d002e01c038910700e001c420400d40021004001030401940110550f846810310404da400c80000609540503c0d684041642d07030707207605440d8418580280170104c0d80c0382c0340500c22501404405400b601c1e0599440e0714042856818050a9041c5502c541c80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 593745035 1250 593743785 593743807
    0x22050105011418091f0e010e0604020c030f0d0f110c100605060702040f270c05100503150d230601080604230709020313060c030903081302010c05030721050901120c05 73
    0x481805440804806d00b440c0d031503d07400744549032010303000340c0c0034510421a440c10080c003c0116600546846000caa482c607844203404000c0c4240d02d072922401c0d282c001890440300082e8001c0c5103203107101c000c1f1036812454942d0002180c01a21401d0b500c003d04104000050610b50002440b1409403140014140301070592035620181200a1b541e4404110a002040080355203e4802421040d1030000c2201c038900000342c0584009841c01141c140750003000e490a81d1b07000e001c4d0340160390040c4c1500300750100242140550540c0740410460380240400400c0114000403200d110315000300503d40808114418440d221611342d00140f414020540e01040052090004502480c042100041c0501d914217207003049542c0810309a0816040580e0280405d40c0003400e1504030b40b0365030000540b0b204078401a54421581c0070001c0c21030201060342c009010b1130703c400036082410f0500c6a05a03400f0845e04450600c10360107400d01082110a5903ca00c80c0311b40c1c0306401220342405d05d1490701e410004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 593746285 1250 593745035 593745091
    0x2010c0b07090611060705070809061e131e06030507120e0a020f030a02010903120e04090503090108010e0c0a030b060403020d1407060912020d022205010501141809 72
    0x2804004112048400c024541d88803400113951801d02d8054003007420b0905004009110b80540079041c2040071401c98100c0d55800115240340030001114080440d120b65504800e401c22a46845640703486100055044c5200d40f210510031a04c00c550746289052210540c0100406050170f010044401c140c15080d000d148201c0541450034001028104024810808a0351900d00602d001e80c2040b4134607001070b42c1000c44070003520b44c41b114006040f009124102e5511400c1c103081d582c01800c0800d4001800400300051203001c00c21703600c2c4c0c1c1083ea00c94006032002d000c1030365490b44400040113032004c1e0501c42d91005400c030000030010380c80d00e562500050205418000e064460109144060a00c0401003000c03c000307000d02d040511006141840e20300c403640c0c2d100301c0603026040d44140c2008541e07483e0280800750040300010384143e0061400c1e44014503007405001d0100380182d4210204000d1541598145035601e001d0504136402881402030036080074205d08080d007030316841d401c101d032a916 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 593747535 1250 593746285 593746291
    0x3021908060906160e0105030a0e030f04060507021306030312050406060f0803030a050a0501060f05180406151407020a03030c112110110307050a110304090605011e1b02010c0b 77
    0x100300311304001800c0f495468011402d403003444131a180c55141660044d040d2030f8016020400024804514010ba500b944030310303c86c11105110004020840701d4103c80640b80c001e00a5a4010075030070381c805410f048568030b00018001c0340080300e41c48280c20781a0441513005101d60808114180d441c1400d9950748803513000203800703401c01b00810100010b18411281e10102d848030500c229450030601502c0c4019100b0b400003000000900c500c08000c8611003515a208050010000d1b00d0b950f00442e295101811018000540305425010b000b403031507000d03199003a4004040495280ca503a5096500698101c0e0807216845045400d00c01071f6940501c0c20840d92803050340c0100f10300c100540c64241800d5501e0b441c03001e481c024140034420384110070b6903445925414010f0b036a003d108019242e80d4040e907000e1603280300004010541c10142e400910032034500fa258940c140d8640c0442c0c40010b0f150b40c0b00c4000103516112001e40d1100c044d625000318034018100021507d01c95212091540021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 593748785 1250 593747535 593747551
    0x80903151f03020f121213240e09130b040c1521021e0d06031205120609070e0303030a0c0f020a0c15090905041101140909010302190806 60
    0x424100104031490015982000e100140c4640d95141180d0018404c0151840100d010320402003000008603003c110313110340d92002c0b02059844141140d004170002c40240544405440c1100b15546c811b0041010700002c0b041644582000d11681c1c4240414a60028800802c6c0f02c505500900030403002c201c4180214010b8003c442c165040c2082105c011413040317604010042c040303100c81001c40c4140040703c2c0d0507800fc140940d4aa2813190680d07135640c43d40e2042090311030000fa116075410b0403688840c0489124691080710403003100400e648500580140640e40e115000000d0039030b145ca82c8255500c5442800d207011004910808203185070021640c6015150b1f41b440c0301c50701d01d80c010000340242c11452005100b040c65a83d1081c0d5401c10611600f00201d141440340e40d0b10324002e104c20000b038421400100100d16242c02d003e0303052682d58500354085185810441101a41e0307004a03601c0e09009400305a159203182d00b03108103142d011582c0c2c0c0f41205140008600000c0c01d0205500508071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 593750035 1250 593748785 593748823
    0x4090602180906012105251106130305180103020f0409090b06041b0804050705060703200c01020c010c080d020406020d030b030105060907050d090c09020c0c1804020d080903 76
    0xc401c0920000450152800703052240d140780c40c240e03103480070004041c441511030010543d611a40e0f41009090b403111000308840002d50320708030300250300c003520841302c0c2034040c100c80c1140c9400e03c0384221545408405000540b08002c01a002c600c1b98403801801e96041c034005182c001070000e140106c0e08281c100914154407840100c0610100760305558204030111010094580840480d1104222508240060100c00300000d014010284800c0008040180071583c0e03443c0d41e841d0041000342041c612000346150284420240c02c03000030070740a07040047c1c0044c181c1d12800c000644080011400403a4840070400458602100d03900140c401004c06030010156000c85101c0602622440c00c0280c0c000d0385050300700300817542d0300e416003600300e851424140c0d07030351700c2204c2400c028054003403002d4100c01e0000c0c1d000404184940c0140300000007035050700c8000e400e50b0100b009810943d00520f0264106801003000341c41c04801c040d10f054800c0701034900e0040c0d0540030038248081078501820b030904c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 593751285 1250 593750035 593750077
    0x6090d180e040320150f39070305040626071404030c06090305072108030403020a0c031b080106033201060806100519150e041b030606050c03160204090602 68
    0x40b1071500d54101d0404000300030185041c1c101f804540070f04090740110fa00030031411241441c01041548100305241320740303030b59410f10707424050a1a0303c984215070010b03a0a990701090f4001c40b8012a2002144940d101c40d1500c45030f00c00c44000b680d08544144070401040000002182c0304600002002284c40700511a440e50800c80d040011581c0603043c02c2801e4021354006810301ea6800da05564400b81c8291a03455a00b8220310785400808000c02a82407034101000b031000d42c21468200c00716002c0c026282d42c0d26840d000e82614000c0c40003e2440041d09115010f901860185610514127000010580f0b51030101c52400d44800d0f0340301500381d0b000b00d42440010801f810340040a003400f55103d050304075503110030002c2070205215200601903510011200684100e0140070b41001c001e00030700007980d00810584144032003039103520100b0718082c00080d0580c040c00035564080004000b560510120340c08001c41c08803101c00880c2c0c425510f4056800142ca1840501001c3c0303a40e4400c4c0304007032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 593752535 1250 593751285 593751313
    0xe090a110c010e0f03070528020d061b020d050423090f011404020403030c060c0908010e03030114030c030d05030907090c020102030a0c08150d020310020c06090d180e040320 76
    0x2000f43c10f040113a0750000c208110120302c0014a0f0544580d0130b0240c29400c09021410a00d0082e001400940c0510555001d030140911074201d8030141f101c8400d5086100940380c400d90762412011041301c0032502c240002c10001801800c04400c06501500c1c440b0031f4140d800c00140c40b40c9085500700c12040c500c03801401b00f40f0030031040894101d81910214500703411070710007810000980100511081d140c5405040c0703103100301c80b000e0003884148000c2c0940404038440d076840c1d030803d0003024002009031322501c071a45000501c81402c0600503015203030381c40742210226050340c402070642015100301c02c80082c1000e50f82c03065000d007240550005840381840d440000c10703070301602c8500040200c1003082c042681d414611501c10b175003040300c7d014804c14051020a050440b0401210318243c401700300300810501c085403240c800c02d10380b8103644160001d914142d8003d50303a100586822860b9041c113000045a411000c3d802074003a0603c4552000c1c0b00303018030b00294078003400800c00d42004131008460 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 593753785 1250 593752535 593752543
    0x4031a0f07050f0421051605090c0910121104030c0518071d1207121a040f02130b0d03091d130204090206070816150c0e090a110c010e 59
    0x10640d180780c21483c101111480d03a0180c003480c0551501c85414101e540d04031112800c03d0205140d200080e20346052060804120101d0148260f6026a22150008940c0706842d4200c80d28110300510b14040c280001a088840030300c2c03071200580c0c0d0350b0360742002d01c02180e06c60040c0008502c00c040000c04a420101400000d20030101d0740c801d00950308060204007030300400b101c0110b035990341103031030021a0300000402d40481c02d07903000d032240607900000c5620104a0213030300c000c1e8050000f150340700300242550811020b04a4001d08144a150484401843d02044000711000e0540001c602d01601d0000171308100c0c0e42c9141280401c981d04810050000041e582c0034160345c90320fa1021403450180071030700c50b9030001c00c00280f04564400c180d604558a00054400700c68000c900240c540e424081c1a98400504500565040700c400061140c000d644c0c0c081c12042001640d65100b4491411051103107485011f02a80a07032600c800d0541440c001d000302401e040d60204001042c068040050340d418 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 593755035 1250 593753785 593753791
    0x60127050406091404020118090f140105100c1112030315010311130b0c030c0f0d12020c03070b0a0216080304060e0601080a080703020102091c0302010501050f1e03010204031a0f 78
    0x240f5070400081400903446075034903540c815020f080c0201c000144c480740110005154105920444c901596080e140c00d140d80705c15141e04961003020300c5032341c031802044410a4541c85c48400240810140000100c102c02c80404081e4060810541d01c002d0382a401e00350740044840c1250803200c440101c00c65130b070500039820a80c211001c110300d0b00c0d008001305030451070726005100340481e000511000c600b6041048456046511040e41e02c0c48082e6582180c940c1d414480da50002081001d01451005040c406ca8465000072002140b4143e80c075600c20b40010360007840c003107a0941c00d10020300b81c0240b003801c5202961144030341a40c2c1c1d141a1078982c041716003201c01800540e20a400500164400043c03200210b41c11010007901e4842c9850308a01910a1a100f540c11008110800400104c60a030a00702144250020b0203103030380703604c01c3c000401d222503c801c1e88808203000f400780103083c01d00c0c0032003030100c041c0015240a80301c2c0c440380e4103103041d410794200c1d81d240c000802c80311608a5580d250 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 593756285 1250 593755035 593755049
    0x60f050d090809180c0724060f1d1023041b18030203030703080a061d090d020f100c020f1b10081e220503040f050109081203060127050406 61
    0x68141085e00d5403480a008002d0000c103040e0300c0803c0440502c554041c101c0c0c0702100300c1d905105c00340e10b40082000151551203020007040c080c1300c000300700410083c0070710702c41c103080c22101480d1b034600b52a0300b250321461500030310b910f850500c0b0400c003900c40d80038180341060722034900e00445402c450003c220400070400c80c5078080e002c00d070502c01690003100f02c400054151609128035114000080c005002c158040d9011011144400c038600f641c00072050b00c6000e5150a544002036601d0701a82c80381024024034680303400145140c580703003006a000d0200703a45948102d81c1c041c1e9054000030311f810054030008c21483c60811001e071f0b480c0391280e001841d4504030300c2c00300c08031306120107040e4402d0204042081c9164003600080c0034a080f82181401079064402c05402c14052070030510745a03401405107160078400ba540108165014003804400c8a0b17220000b40410b154004000b10990809840c540c1000440c80002c40f191220010751a4220040806484e51514240800c0200d44842e440340c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 593757535 1250 593756285 593756329
    0x60c050c120903061b0c010207050c0103050c030f0105090c070b0c07020f01090b0409091a1509070c050a020d05011415191d0403051e0301050405180601060f050d090809 74
    0x229580c4004c20090340040340c8808003140100020603441103805526158203240d880446c0000078810f0020310a4485403080c0c030304008075122168000e003544000c5455025400c1010010862414486a40c80d4000c01800c642c5060104940c1c40c0e884600c0161901486000082005002c1d860305100924406c4002d013400d0b040c8500e00030049140c0e02991280b00a501d80c2c071840c5078107000c1401e404230303240180100c00d103038140b8110004490004503010709038020750013180050070503405141e1481415810030002c1501100a80c02c000e80d6508441080311103540300e00816040e04508041c41d402150030400c13119158402c1004d2007448141035161601c640111841000100100100402045200c0045000c030341e44904040d600780c45a001c0500c0340304041c003050a96050141c0186040e1102114144210b84550f00039201c0d8107582c04440d00960003480040291900498180404036080d040060501d90242c25200c11121010010750b604680000ca00741c881ca8106107440910010116035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 593758785 1250 593757535 593757547
    0x70516032610091812080709090b210f010504300903060b0a0e010611070902040305060c1b03122502031b070906150f020307020112090807060c050c12 66
    0x1440142d070040c800c2c05005507454a030740074018030520000034403030b4016403903d200860821000f80030744021909400043c42d02e40001c0780d000420300901ca00310300c0050044181d50700803150014102e0901100c100144a110b42034155090300b03002d402c0c8218040c1c885160320b98448180d001d0074185406240021500d4040301d290100c1d000401801540e070030a0340011a400e400380450301d00080c1d608580e41150781d130300c00000c1c3d03181e0100801c010b041e045000d8800483d41c5180d902c00b680641d0200625682242c000544090880d00140a0340b851804170000c10243d030305552401e41d8408070002c050380107848104008400c102d9040301701c0c5003010010100b04003004e034000b5205d00a4600040c5100804004840e0b00d0030200004006020015020040160b65080f01000382855030038520102e0070040c418400d4034004030580303c065806840e500d40026043c040a030049c2003102d001c6400c1e0106100c1403000c184117204518401e400f580328282d40d81c02c2a1200d1380380103c00981951100410016 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 593760035 1250 593758785 593758801
    0x120405100c0318080d14070c06030506130609020a09170a03030c1101050a090203010b010801030b040807020d061401030203070b0901170601030608030a0302091e0d02090705160326 79
    0x2000c08038004a1519801e107400d140360407201a4164002001209401080400c4013100410034000203001512580e40c2c1415100001489009290300a0311402e071900c0200b100c0ca019801450340100001c20940c42904032070081c000711406a080891025404a0621a61600b00c0f1104000c1e0100d8401e0b03481c0340b10340c521215900e4200c40c00c014201070302d0700c0c80c0b200c0b00343c080ca4030400c4180851001388001c0c50049100c0006001c681001d034820341c00c2a03904140c55005900690680750002c000000695694442525950000c2c000b00c1c0c00401441414011036202d2080c00c4690070b013000302014a500d10b0042620b490720540184a005904000681c1c55a800ca0f030950080c0a00220210a550390040185c0041003542d000d42d105001c00941d0b4020395034541e0082507058811516440c1080f4001401c440d460960340c0d40d01c0e0030104804081000d40f800d1420315a00c41c10303502d400d524119000d40e10101c1d40d40d01e07400440100340c0c2484094095542c0d0b00d4002e141c0c0c800c00d055a06c0034500865 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 593761285 1250 593760035 593760049
    0x3020a14130212130201110d230f0318030403080304080c060121060b04092102010c09060518210f010f05070203030403180503010507200106080c060a170702060702120405 75
    0x1008142041136590f05404690041500c24000c02c984010340e0200c0094070005040c1901b05501c00422841c0342c0b100040c020182d5060f500798196004201d400c5503070700122408590703103140e0403010030720051200100007806100114400c910503502ca40c0c0b05e44042d44003514102041e00108188000c14034607042c641424034400800d690000000300b00d03030b03050b40c020070024182c0241c040c00315592007641a528070003541c40542074210703a40c020040201c140100f1030700070101e4025240014801c10040401000e0350502003420f03034000f0b1414000d0b642071440d0583d5030032000d0302c008598208107101040c00c1800c0c800d171a40c2001048090080385020300000751240b0004000600b80710401c0d01061a0003e03004001c03014260180003004142040080940590300310130f1810110340c42c0c1c80d0a105542c5060103550110b510380e03002484450301d034104000054111003501020081600408401d022142086078000d40d140e8000e0030440c100810700070304050002400841c031400400c400c010340e0300c0b404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 593762535 1250 593761285 593761291
    0x3020f0a21080909010306050f070f1b03031b030c030c08060f090403020f030c06150d0507091d1c02210a030c030207081206011e1704080403020a14130212 68
    0x3880e109a00d0003a842c012506004100b031403600880b6103000401001210b80c8064014289200862036560b9008811240417190341079000008103e2000315070603d00c06204120082e00c03d09010a00b80d0301c5a07200c2e0107c0c0310005404002030f40b5407170009160340d018801c00001032a86d00d062a018a402d1010030031b40062441d80324026241c410001e01414400c1c031000d4000e052801c1640e90381d400429040c0d90314030041d50b20904411020886504c035182451614102a03400009480341c40c0c80c0c007660708020a001c003d80310400d44500580c0d00c0c1c04d101401007207902c41c80c09210506840551400030b18080d04400312801040d01c1c80e0030803188801a1040e21200100c40c580403070b880c507010300202c010703000707102000309828000b240d58801da10140c06c04522074502a0384000182000020055032800d803404d00d04040350a4501004944899001c06607020b8014140c0918007603403903000c07851040f11903000c41e03242d08411035840010b203801014001803440f028130542c100340100381c084221340005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 593763785 1250 593762535 593762579
    0xf090c060f09050a052e0507120e1c110d03020a05060f060a140a1a0d1118152206080703021201090f06030b0c0c16030c030b0903070c0b0403020f0a 65
    0x41b80101c80818100841921748100e82a001c111410000001500342d8002c028101d0310b403684d2001d0790350081c0c81a0703c0c0e03c14980c0018640c60040310a15600002110102c80a03104c1c014140d13000c2d00c41d40c481c1fa100c0c660581c03103980100f89003503180c10800c1c00c0c1200508a1140c1c04000c2d030621195648102030342041e03c2c0b2031808034812582140000743d200c0030540c45005a00c03010350500510b15a0f03000a0000b21500340c1041c80100d00e804243d00e0a0b2081070b90642c440d04100307821942c07505014400100c01018010141e14000302c0d4892010b40c0441c101c0c0c440d851a00420062100540c413848154101c0d2490a007542010b05618140521140501a601c2d00d1355070381d0340300c50a214054104600541e0071070032403051070404000f10001d40d40a00020340c03251299443c05001c2803154440401180c6c0c12888055120b42103558000550001501c4c0c8a075030b10050095001003041e4204001c01098140074407030b07a992852051080d04112b03160564490000d0207800c014500c1e440113030036410084 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 593765035 1250 593763785 593763799
    0x60f0608071d0d0c051201110415020f0118050d1704060b040b10050c070b0403050a02010c02060c0601080a0c06021f05060604180b01170c0712030f090c060f09050a05 73
    0x940c1012107070250500c5203a0b11914402c0d280701031044602403003080c2c0360b00f1b80d82902c1c0e0f03032018000301e4284d41d80c6916a40c4d00b000100410040315810104070001140340f841a40c412140f1061030301d083d203050035001c11240e408110100e041010070007034460010560304088545041d03030700341d03121070340002072000c0c1ca49900c1c0e001d003031101d1755141d00c01c02c1d10210040c00c1442240304403400901a8003c0c4100c90709500c101500071410016190a030f40c1200d03804002050800141e9004660030240020126044842403203041080802400014040e10b00d072401003c07013440074200071082c0341b403503417156055401800e00c0c6001666003034540a1180c0c5606004245600c07414082501440b5036800f030480d0012107030100843c5400c0350803d071012982680ca40242007507081a40d03900d03001c19500c50192050030840900061050681104084694200003800030a084446010740d44111411038070004400028840345801c0724802e8101d80c02842e00d00116030030400400c1003034040d801001d2141c7c0d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 593766285 1250 593765035 593765057
    0xd080402042007030804120c20060715020309070605190806032a03010501080102040b0712030609050903070b0901020915030402040906020a050a170c0405011b02100210060f060807 79
    0x90000c55000c0646074400c1a40c3c54841e414024030414080c1d60032030f000c1041004680040d445001c510300c0f440d400c004041003031070b0703031020701814842e400c0e0701c2d0b0342c0285052200101041400c0c0842048007141c500141c2c0d685400c000050030440079070011000d01c6000e00c10482d441c090010881d0010802d428810f00c02e4071181b000a01d01100001015614001b2617110400780d800e5880c0c402c0b1041060300203000c60b0742c0f0f80c130b0032078281d01130b0740140c208811080c080ea401140810322040001e03905030900184041d00d031112081625012220807003a940005110303800c0100c01c4844aa02401900085040a15010006e0701ca80000c40c4420306000b408400301c1c0543d50b0399802100c4c5580e01c0502155503614500000c0c01c140c005440d1207010603c403240d04031040f001040d81d54814090900c040b8030301814400151184048000b0444081403848100b40058071590080e031120385c02d40d0024400c642d4000c0c0c8190507a039040c0c20104807207242031020402c41d50840700346034000c00d59080c2000184 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 593767535 1250 593766285 593766311
    0xf14181207080105070f0314063a0b04050d0c0213090813030c05090f01260a1a06040b0d0503030c0307050d1509050f0603060403030209031009060b0a080d08040204 72
    0x1441034001c08183d52a050070710120381c1d040400100751080c140c4003880324040700c04001c0880f080460342950020100241801d46800c10358211402103007100070040c044107480343c007490304004010300310b66011504090105100d0104040c5280d0401c910b00a4040229175011582d003094000a00d810103458091700740030440d88005a070520394802500c482402d642e41002e5013808924450207000301c0c09480810b1324114400c00c5907042c0d90b04000c6482e610342c50843c148110403a4a01201142e019480404000403a43d02d0740e110460a04e0407142c0181c20b20400300002c6401c03070051540708010060309080005c5002c0b0640b0350111141c0c0701b240c1c40741c1d100d01e0151082e124044a8100c3c0b03a00d040d20f44c4001c00c00e0b540c2458151450000c1c2084990f6490211440c025015a003c2c0c2d4183d0200e00020300082c800c1e0010913140d2000740990b421031203d580010300b1354801d008100c60041d100e400c41041750600c031560034001c00004000707003d8800c01c4800031304019000343c0081e014544030302e00c01c1801c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 593768785 1250 593767535 593767543
    0xf0e010207020f130f150311011e080c2118070f1a071a0a0506040203071d03070819061812050c07050a03051e0c031e011401060f141812 60
    0xd0f105c035880c107001c00d4441a4000c1903ea2a6001c2150840720070194020554803582c15507100c0c03501c0d07002c0d09083c4454100141d8880390020b0215001c00c004106800d02062600703950054090401440c84203400c00c11608002a07000b501c1401c0d0300d500100d4208102000000d0306011140c1c180303c0c019101000300b14030b42ca244580c0c000074000008c5d950103800003041c0c450050b445500d0040040080b03403115020002a488155140d03c0011201c2020584110314801d02c0500044001c0441d4115a42e0365885400c0204810603e0700402140244c00c0c14000170307001e00000c8458003814040b840c2810382d11212203001c400881d03010004086a00407001c8401c20001e07001c2c18005040e2650f86950b450811360390b0080b190240704100315407a03556003603d030004074181106001005404c40c1c00140403600c0f401c020044070761782950740301c3d00c4074070302401a0382003d03001e4101c03507803590546240f0b58405406c60740b9038044c00b102580c08000000700340c141c9900740311030340000301d815058030740c1940c0c40c00340340c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 593770035 1250 593768785 593768801
    0x50a05090d02071811223203011407110c0409031707171326040506090604052e0504050607021e0a0e100807030b0a020322060f0e010207020f13 63
    0x7509600003101120b252004c02240960006140840b941c507456114030107842d120700040700e41001c0c001c0c81442c2c05009981c51f5000d800000b500026100541803841c5400c00070541d4924045610b00e00e0a913421072061081008089081d2801d00402c041390b500200700070301c03121499400c80794950100e0f01c040d1007907965500a036040c01070070f803e034200a4a500494022041c1c1100d2250148a418085058201005010712280e80125003080d10305814001a9480a0411548010b04000c0802c056a0740c0c0403a41c880422a0840d41800e0001c01084030900320300881c00c01032180500c410001a901d410417543c40a80c155903a280c02c2848501c181e078000d01a299040c0c0c064424038000c40c1a40350801c19510400101503002e81080e518140d003600c0d04198040a818a03c000d800034403122800c0d0020350b00070000003450041c5d40700406c405c1925410b90081105c0540e142c0c010020300e8446809200032010b0211b00841c03800c0e50a0340010b41540d0014182801428080c9103010140459030041c10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 593771285 1250 593770035 593770061
    0xf3b090f070c0309170d1b0b06090c040504021201080c010c110d2d17040612020306060712050c012a0c080904090c0306060812030a11041503050a05090d020718 70
    0x845440700c0171036844482900e000d034001180c2c100181c408802402c0c52a4681d030b0045505420390f2100400d1201e0000c00404004a055042000041944451000b09001c6400c1c000745442941030407500f50400403410316603410402d5a81c068030200d20102d400c085003031001c5a882c001003007285044a0b0310b801c0c0d4040072820030201c00c5080c00d12403c00c0184100f0611844026034102d01c0075012900394090b9025050000d03a04601829050140764002e50b0003423402010282005803965850420301091b00100000500200e05200425403d0081d201000446540020b600d400708000e500d66038501c005803410000c046501900b448184000c40300080c0000d0b0080c03041e00b10074244000f0104851004840f400c2c43c1040010300c00c4400b2525590f000c070302d001c102d0714503140d802148000d054280024240f01004000004544150b400c0200074180c00d5100460f0905e40b030001801106c0008221101c107070082241400b120350302003648001d81d004080310600c44a0b50b10990030090081c1c03d6598 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 593772535 1250 593771285 593771309
    0xc060320091914030c03030301080d080c0c0f0a0c05030601050105190c020405100e090c0906060c010609020313140a02060d0c030615020304290403030f3b090f070c0309 74
    0x420710883c80d410300d000f025000d0301100c400c01c074224141581c0f40302c2442401c4181d042104441411889001c16913003107400ca402403030400c1c080340451814501c0d03074441d0410359409200303018104000882032000034002200503001a41c5454006803651044042c8078404e510f480180c20111405182c205d4140c40c0c0180c0100010302d44410080e684036018014840c194a0703043c00168042c0001840d02c04101014125141c030713448847c1800099080010803043c503540724800419048003a1024600c6a13400d03502d090450342c07503803c0100d059410741c0040c045503000001c501c0090786030f1a04454801d079070b80f04001420744080070100d0040200ea040700b8100c46130804d5011880b58000007038405d50700c0815881000c40341d103c452682c0b003400c0790351030032a0020900003007010078002d00840012a240b0304010100340034040c000c103100801d10074000e442e141c000c4a00c502070802c120001e60700000682e0421540e0a003a030001144d200020607040400c0801d06204042510a0303158038010081c1001103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 593773785 1250 593772535 593772539
    0x81812030717130807052a011d0306070e04020d1a0f090f0a0f0b0603091b01050702090c070311031206190506191103040603090c0603200919 62
    0x14440980c801d94244000070401c0c01000c40003020381034034901500015245201d8000d07503586401050f003042c081a9664043d040c0c3c00c00709014a04021004006003400c07481c0307017222a000150100f8a01e0340010060088800501d450380c0380000c640f9004010360406a82030242ca0300018064170482401000c0b072420084070003c5010960039000c002d5031b00f140c0308622140d4807001d000b807211084440085180c0c030310f000306440400c6035005d82a40098041c0c003052030b02c0346901180141d442540c4580480e4014051002c1c62247e00103d04c030410002d1a03d14900003680d000a50756140180100c041c10100060181c01c15000e6110030380c1050a0405407134841100d03103800302014104556540c0500040305006980064451001c0c06441000f0801e508012216824800780018001e522040c429410382c042c11346041040030340020f01c60740d6008100401145000402c10140d584680c1c245410483e03a00a0503203c1c1800c2001720003881c40359a02e5025410001d14200300034081c9a8500d1460000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 593775035 1250 593773785 593773813
    0x60d0207050c0a0b090901090c020a020a140a0605090102030a030b06131206050a0920150c0109050708030a2a020a140319080a0e060c030f04082b0818 66
    0x850340e20040480340007900f00d642d00c081c10581d10880e449158800e2201d00180070b040001d80c084135076440e5a00c110707000c041d22903020401c0811a078210549883d238240202080d49407104900010b08201d19141c3e092005210001c0d40d28010300c0014418903848070741c2c12107940c4030402510180d5107000100309605959600407030000c0c801d1002070350703000d0070080021049204c5000c2c00680d01e41c01040342c4040030303140a08a07544140e00700c50315803201201c0701d0040c0e0360446c0e90151844541c1c03007000003061030303c1c1d107415403402c205036001d00215081840500701558100070203461481440c1600d5003482c52708448556a042c103400c00944c004520702c0003150814464603601e0450b9410f030210b54012510b0b0f40c01d5901c0118800c1c0c0107203000d404108a0300a144908400710401c02c0c00f514135424850ba07601d406055801001d0103080390300003c6010046000100300d05031440b40d000035070120340034003425107090390982c00e007500f0203101004000ca8800b100485035880200c10b41000d40740e652030f100038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 593776285 1250 593775035 593775043
    0xc0314040e0402180103020a031e02030f100b030f030405090915160f0c020928090b15120d050a120c02010c030b0415030209090307050f1c0903051b060d020705 70
    0xb07800d0740100e02840c011800d0b140c8000259050ba0340042810503414690359030025061070881820071041d02d59a030840058500700312141c80212600088c2241e410003074000b508994403004030764403135804498403600000c0080129400c0e9002035501d02c0c81c81d07030344c4841d03d458581e0001d000c8070051182000c02058107a1085c4190744e03500c40740c1d038054040c0d81d0345108440d0801500c101135808500c40012818402031102d00142896590406900030030181000d0011030749200403c1c0c503445171250400c42502c040d100f00c010300380002c540c0200501d00061045540718540050720741400000030700e1148081c091000c1100702c242e091800d02102d000820000d000e81058110a40828140b869003580d0385040d010b010011001d06290f1503030546507808000343c0c0d000240051540e4007080000102203001131140603580c0307482100a2440d002c0000d44120100c02c040006d030b0400c1002141440040c03000b162026001c071488400400034410340340000c0c041c0c402d448410f50040e100040706020030002107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 593777535 1250 593776285 593776291
    0x3040602163204090f06050c0a02060403030902030114011d061023070b01270b060403060c02150106030b0405150609011d04060605040e09010e06070c0314040e 70
    0xd0309a80020703850810490301000c0e5400303480310016010035108845841d00801e1849114082c0c11207070b0301c44503000450210348040206550701c090040c40c00052005601803c0c2c0c2013555035040c0780c540444001e0081d01c40201800003020151285510415958250041c1d8192020200340010300c6d40d40e01d940c03c003260115001c10710741c0391804002074014500a084107a0103449501d941105a504000610b80410303454450809070009010300703000319098142c0305010302071003c1078003100070000400b40c0c0d501a18603da00007080c1802c50740380c059101d0340c0a03901140d0b44079801042e08149400d080e42008441710069000300141000044c406526420440c5000300c1a5010411912440d0440b0794480c4420350982d00a01c0403c1200f100703520590a01c1c600000c80c40c0614400920300c030001e41594440d034060b000007000400d007801b551300407400c0241c102c00c072400200128a2084003c5441c0c04c401031000c000d00c242c042c00001418094070300041007500c1486115950f035103400c100300395100c00f6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 593778785 1250 593777535 593777537
    0xa050a02010f06080d0f1101020a03020403031e0c0602091f080601200d0e12100501031719030c02030d1d0f070305070504022a0114091203060d02030313030302030406 73
    0x1207607401c4680040b6210f12401d0700c91180241c6075180b00b0759010388045400d1072401c070030800851400004000700784040c0c85802265540940d95502e50305004060b040c248489148040d000f03100c0c04001600000b03490803240c2d00010250703c4005d41000107039155a95206003080071b0f00640790220f40703548a0700c2c4901c211806d89540302444000040c204200c0751715606d154240c2c0c0001d1400c1c051074000c40d006a075100e402000425464840405a030800440f440609070b0103032a50014800c00402a0310041187d100090349800e00250000305074010120803a9002410b607225240d0613494400d02c22242200c00e40741003800001241039a1035600c401255803140d0b1030140c1e80d01900038620204d43e0404880e000002400780d6418038040100039840360511400000348082814a041c0002d5101c1407152030350b000008603030b401040740545407840100a080305030081000c150f070f400f9040094940004d0207807554400c01c104d0340b0201c1e02e14841c0f5101035a040743c0c500000402c147c3d0000040003a5002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 593780035 1250 593778785 593778791
    0x610090c03090302120c07080d030f181a06240309071707090e0705091905060103022721030304060b03070e06132424020c1509060a050a0201 62
    0xc8900490444180820043c01a04814940e069011480000c0e10311241c0305015500000c2da00c08046260614860b42500480d0300c502c4500404800e44c840d0f4200003d01e40082002c008079550f64800782a0280e00d1484480712000100d680d81d2684550b030030407104000c1295000040026a108003500200d820610300c0c42820004603600c01d0b100c1c401c04c0c420103014010100d99061003031290241c004079030b8000862240c508005640d035525910940903210130750f41b0101880b80c00d070281d000c0e5900108440c2c1814010071001c040c080198a4007041d1040200c1d803400a000340390002030140d89003025440d58803000c0c18a005442e5004402140034600c07500c01040181184014152145698454100c2c6111280c0000d686410300c20ba0145001c030310010000b51030403440c0c0300c02c040484103400d1030306503400f625400c0c00141810128810301d20140300e0880f440c40c0010400035a0b80c101c1c0c41e401070007035101d44550f040010b116401e5800c00c01c4010441c0d9201d0801e560002e11980020b082c640040d82 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 593781285 1250 593780035 593780051
    0x8280218060a05040314010b0616030e0102070303121503050a2f090420090f060f0a0315021c0509160504051501050318060c0c15011401140903061009 66
    0x501142120010b00c81601c40c41c1c1480e1461721140549141804086030381c0d5211a19002113a43d241d00070204020288440c14400c401400c1c000c02200000381160305660004006101203600010100002d248410020640002412080c2e41c208030540c0010311701d2041000d00ba0030000e1301a1850b10800050040006c0d800800503001401c0b10710b1030500342c000c0101400b0a020881d02800100d0044000c101c00040c4903d40000c42e401c03650844110390142c150320180002d500d003141c0e990b600a0000c07100d172890607046464503860700007004007280c07081385d00240a6200030300c0f2003010074000139607002c01c2009103082d45520392606442c200f03c1607074002c040c0010840e0702d0140300340d80c06182e4051202c0010060ba000540d0150302c090f020080d00f11004540080000040000d584030300031034000c4030b40710000c50070824500304040c4034401c8490303600c1005000034810045014260002460100c08005c20b1034801c01300740c451262001e0300342c01004100300680c5001200c0707408580c3c20402c200a038113 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 593782535 1250 593781285 593781289
    0x110706050405040f060509040606081e07150c0c030c0603060f0608150a05031f11120c0f270f0102030f0a05090307050604031a0702071508280218 64
    0x145801608041103003408144918181a80142c60105078000000340d000c0d2070340c0006107089000c40c0c00702e415540712541809600d00500418030440002d00000365001070080b02291110014003400401480040c95500498881c10802060b92b400500410b866600c0342884100007405e030141401007401c00e100041d551580005040807503003030381c1d10350400da265a10342c080855020204aa40170341e5001000c2600e48c0c0611554101d00111400340500c01070b010041016a0414040e442091100340031651107110141c0340345a000003060a0141d8403014802046001c1c0202c00b21182d0f8604100345214408000030f080c42000030f001c4826929010484004a90383d00c110885807100100c140080120a401003000d000040350003410344116a48a5012030000d420643c426143c405800f5888030807411460003090b0071640c40d00c06071040e5800c003461107400c0f03183ca0002100300140b003c00200700060103911320708c26101c211502d0b40e0003e44000804080e401c8420403400c100844841c4400c0b80c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 593783785 1250 593782535 593782543
    0x5090403080a02031b04080708070b120705160f030e010e0a1a0a05070605041115041a07060f0c020c01110334080d0f0b1c11030a0203061611 62
    0x6503030681c1d80c400e0564808841c10065040509001500c0354440c0200c0101c42c840400341024000680003041c14030701c0d0640d400d03c2c2550719030003040100c0c0308014494010308034203d03030355001a01e42046607681e00e42601c0e62540da011031034007510705500d000100c0101769004031000308042c000d99680c612040b05200300030080c1c00c1c920501c101080c04041c400d280c0045107010b4581c8000c01d040c5035013070131035945076101610b9044804480521080620416502e080303001060811800220141003500702081d07c0a910480042112a5040401c800c2c3c1085043e4100803400400444280105000140c02079a40c0b00800383c0680454070784200c10440400000a0342c0c640411010a01c0c00780b0030f1368121141500b03606102d0b16034408c4000c008004100302d2802441038a09400000410100c0040040200c4d1a0080b40b42d100c1c5504281e40614182c3ea14100d14071540c200d40503151540340c03680003d2500807101c1000b5018000c00b002c010142c0c0f00e01d510711b5940d02017529400010000104050f8807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 593785035 1250 593783785 593783791
    0x30301032a0317070b0a021b160e130503190305060117221a01050f0a080a150609060e06030f16091e020414191d0c190c0c0509 56
    0x516400504101203002050f000c001c1100c400c01441c40c064842e01c840103103140444d80455081d40002d800d501d1803e0030480e89203207088040103424241d589100ba20090011031040011a40c1c0d501e010039025203002c841d4404083d4824204c2b50741d000300c15800811048420781260210b0301d0a0b0001c0c8065006070b80003041403c0d0b0f11a80304c62552034a00000702c00311146511104140d009050100050581e215900b181d0200000400550b24240401207111788140301c4070301620180c6820030400c0c0000074030309a0141d1200907000d0005035014900024007840d849903894509020002a07500010703c00240643c600b54107880300402c079840710540e00c0e8604420701d5203805694200300809010759100c0c40100f50070340744440503080a4100e00c000c0c0e0300240c101001c070b008022401100d0303160081401424040789504c414103c0e1808205e1852100f08040c0c40000c51294800210001d120404450007083d80042c00e02d0880f9000c1c0380100f244020074800c403003d01c180c03200450f551622060580c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 593786285 1250 593785035 593785103
    0x60f021905070f06150e010602070b0406030e01090b150f150405010804050304030b04110415050a060c020102010608060703051905040b0c210106050d0c0302040503070501030c2003030103 82
    0x1880c0c0d000d0841103485a0100005644050802c141000000c0c0d8500aa0501c0b901c00519071000c1420400e1a40e641c2c60181d002d041550710140080100b4030102050324111103041c2800211031250048541c00351102c40e20003046d0040c100100401140d0384d5034040c00b040006c1c2c1c0c0300100320a060081c00882041e048888581c0003040c002004658032035142564024480c0007602d04040d5650b44400360058107036005ca6060b0540c0c01c620220307050a01c92032080380004403c42000302c2c1307050301049001d6038a000715000c0107801091801964002d40065004007040400c503081440c0c1280010300418050310003000900451000e4030007490303d1b010702402690400c1c40302030340c0d481c3c0c22550100e40e840058555270800411340407044a00c221510b0078024101a00ca6640d02e41920074064100ca50315030100342410710501c420f02154400250743c3e411b075042803d00065070030b10700d1001d444503000141c900c4001c008154040491190110145049911440c0081000c24003008601c0141c090a4103e04c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 593787535 1250 593786285 593786317
    0x601060f090f0506070c1d0a11090d02060f1e0c0f03120c07020a03060903120e0106030c0e070509030601090605240d151205030315090609150105040b070f060f02 71
    0x3c80725140581c01040d400d849030f03016513240f41e901c0f07c0e6501190052543d903604108a501000400142e41c000c401540031080d00750352074140400e002402d00e03c00031a002e8010880400e4408004001c84116040070607503a1031a20207402141d210202e0b41d00a6115541f5402030300c50304200560b0003c2520001305490302c07045842c0e980d152800b0b10365081035000742e03404880d02d4030000c04941c680c0b040a20301c03802642c61902512808601206541250744007202d10384c5400020008103a00c1400708051341c0d10642c0750001030700d900303e044515010701c101080c2e16000d004000a207152403a8858801c40b02305540f0007070000d081000e48056010f215080f083d0b40c007410002903080d80d080707032b128007488100072902000302303600c80c0c030312280003078002e03c3c21521a4000800e010f0f45480f40a070070031101e6011104011189088804103031b8031503000e4070000d058181100390540320307801841503030094a1107400654030f82000b42003500c0020a00c01082c4c91072494080141610a070728004c80721405d8194001d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 593788785 1250 593787535 593787539
    0xb131d0102131502100e060601200d121401060206040c080102040605030705130812040801110315010f11060f220c051e0d0b07110a0203070303111504050601060f090f 73
    0xe1000350102c06a02003140610010010000c10034414504920304506c005d00f00c3d45441c0d40003610101c04d00d0301482c42c2e8881d048080c0c5a1b4007001814140d0701c00e4514104140307401126020f00a405014640f20324428200d001054040d4001001c602c590b0145040b0b040301a980d102240c02c0744600d005410000740c1c05c10010706064040c1004000d01c1e18942d619610303c1c2e40e2114803e08008ca1b1491a41300003800050030402c00b80c0901403081c4080b01302c1c10031441c5080c8415184881c41ca845030845c10300c80c695040d141d80c0e0340206500e81c3d50381c51800c195401c1c0d141030684507051141c201c0d100700901c003981078007100d9590f04101001405902600004030a400c1c0010400c10265010915505d0340042c01482e000d41c80345801103004034402e1000300000d00340308002401d00428006658143d038410561310005d6a0b00184210403240c150800d950496500c0010707504002140b020b20034521055001e0004014000400074100c5030b1564a00060001c00241110510600e200d111000c050100301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 593790035 1250 593788785 593788799
    0x603080c240610260106120204080601090902060d0e06041e0309032003011d07120f061d01051306110c0a1101020307021c03092c07030b131d010213 65
    0x210314101040e600389803500d000742c194411959001c2e40b03101c26031001040010410a42c1100c0200c0405071f0000b8250308084c01d001c00d40340e030f07250140300d000314058a5880050541d16800111a0f41925a56007070020034142314036581c0d200c1080d03a0460301c202e4949080b401c02001f070600b0b03022050340b65455082207451903d0360402c0e05089040041401407410408155641c2440341540c01d0039800a980300321801448141c0c1003081981c0407209540c850b010000008110300e103000200d66100c0f02c00503070780c0341c101e00d00c1565504c0242d1207540c641c0b030002449114150304410b2040641300d0b410a100403515007800c90150301410354984c03180e9104034801d03800220103040e0308030b15201c1803040320f04220309500000c841031614940300b108060b54000040074954030100c1d180142a521098100d19842ca00c981550240c00c2d07032401240341054000306078114400d0700800764403440140b0b41140030419602d5600100b0002a4580001f0801d00181c3d90310303207041c0250b426100e03100710b03226060351920b45 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 593791285 1250 593790035 593790049
    0x60f010c02011809060608011e050102070b0a050904020a11010b0604050f0609041808040608010801063b01080c01020c04050c1e13090236010f0c02040603080c2406 72
    0x3015560701c070f4800310118900403144505801040a940ea10706030354902150486802000c01480e00d54050030001400f040c0d03000101d0800711000a660260303100000e0341e04071514051321640d1a44207000044540e48141c3c030400200c407907075840008020114008040050754411071103640c0d0081003494070441c080c6040ca000d080446400342c0b0110b01c90414000e01e80e110500258100d600c0100894140041d0f607009000c5409055550001c00c1400c0c2030401d0145600303550304e1042d0160105103c22824112101600e8442165144419140d03503115035402e900c8040e22030605005200e41c20392000c00389030034000c450140c01c503101014500700a0001c0710b480b2070300881c030b050b02c003500400091302c040c6800c2010000424801e1001a290f440d02130300100310210550f824850401510041d0312458558020881c2924003420045c1c12804240001e0f5100b05101c40080d500030b292a900005001da1000104001076020040e50b105038103240340d1010030640102c500c48043c3c03403c2d00040352820040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 593792535 1250 593791285 593791307
    0x140c030d03110906040b07030f020712020603190f0e161d061206040308041a040b0a02090324010e0c0310120311010c030603030e032829010e060f010c0201 68
    0x20007540c503120f1181c0c0401c0030b07030b8400d610440707102900140143c2403542c0441d02c5044d0326000d101901d12145031442040c3c0408101d00040e10426000010504000000d18044828810a8014003004007040403010080622400081541c000c0c0b5503001c03000c108000320041510701840900d440ca1007580079900035040001d180d15000051702c151040120001c1006a1042c0e100b5070b1602040d10b054035103000ea04034000404400110804180000903101d803500d19400607401c1c1005840c0c25450b00080c0c5031031085d03042d051007a1240903100300c040c400328641e00c0c140d8401010a120503142c825801032148811160340450200500342440025506043c41442901a00d00141219440710079103003112101015070000c26900c0c0820030415400400c01e84071a8811809000304c0c0c584100d00b1852910108607220042003081c4608040140d4503040c810610305030602210210441a110b80f5060000c0c0954014101008002a024542414200c24040040e5902001c101d825801994524103507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 593793785 1250 593792535 593792561
    0xa0b07020d02161e1d150d0b060d0302120f04140901050a0311060d050c0d061401020d0c0812042f0604090c1e05120a0e070b0a05071e140c030d03 64
    0xa0080080d0a011055400d107202c070340c4802105d468100131600241c07400d000c07900c803401075041d20610408a510000c400317030710002c2038811544005142c50100d0502040c0c5802c407461002c0401d580ca00300d031241000c0c005517603080602408005014040042d204024400d50303902c205441c009100142c1c01c5e40c1c0c1e0302500c0303038050085400e0184d01c800940c29680304a60840502c0004030760600d24075001d0003110014460031210464481c010703c0001d44500050250b60f0501404000b030504200f03210381240d80d40c0d400b2801c0300116007410300c0c0c6144000301c14150155110602c061f60b648001d810803815090060040c091440c041c90810600094680b40c0e14282c1030080300c501c0c0d818042000072081c0510041507070382c02d607101c0340031910645110010344007403002441c00722032507108080043c204041d0b8076503e5210b500c0704401e0204075807910070b03844020162881e02ea00300f04152581c2a451005500c55154540708118068107a55076040310006990705920507101d1300000e40c025800500b80d80c0ca6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 593795035 1250 593793785 593793839
    0x30e030f030f0706110406030b03060a0614040c09030f0303050103050d08090318060c010603030e0301060905011809391d070e010e090906060103060f06021c0306080a0b07020d0216 79
    0x48288078032503031b41140c0c3c081c43c00703c0e4a6402000707442c6400d10107580d00c425610780400c8440c2c181601c122142c80e4590549000d59922140440d11900440002c0000c6034800000300c952002d900e002401740c1001e20048a00d41b107803644915400b070141b0100ea00c01c80c5100000c50170900150140c410451100410f140c02010400130002068000c0c004c03980514002d4480900240e00c0d0f00525003190300d42c1d804840f10900e0a4014881c104a40d01d1000b4800010400410000c0840c01c00d407044180324041001e40540b11480540c5051122180807420400d00314020241d5603100d880e0000784503002e08040e503401c0524002a0241c0c000c0030041203089040c5800c002ea0300300903011910707801341502c41100541c420300c10050710350f82c1030181d00007074000f00e4090800986080c0e40a0743d1f480360b003003070035100b602e5013002800e502d44294001d0000b000c02004032450b41c1100d04114034682801d079507580c01402030380d2001c1031013400040e9090f0041c0e41d000003540a40d18000124072095141c09040600c3c8030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 593796285 1250 593795035 593795051
    0x70f020d050a0506040b070309080d0209040209061308100903020319050c100203010906050d21031404080903010b0901050a03110a09020f0408150f0c03131e030e030f030f0706 77
    0x1040088540b628402c10040a09060506014480d03040040c2003608042c20701e04100c000801900a44d1085400b0701e1000d6198210000014041c4c011885c100c2d81011010940e050740c4401140c000044800840683d096a600214001e060364040800034004d03034420460380e421805401a644280c60f00c07403400701c0c145052110103d042c00028407915004035000300040c80411803e20809004043c00c0361801071110b4195103d0300000c5041c00d01c0700742c0305407140d241000c0c28026004401207200c06164400c035031070306150000281d008140340b07a0296180c840c21221500303080010a05a40004008045013403079540c071007009803544442160803c10401c00000c103008640090302802d65002c401544a03800e104c801840d0070a00c0036080c003850101000c2c0281a194106001c2d0030001c071f01900b503a2a510311f030070280307604030344900245003030700c040254807810316006501c582c014440e0365400b80c20702d140303010103517219900c4048582d50341080100c04688001240184004d80c800c10700429994 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 593797535 1250 593796285 593796293
    0xf250501020d0204050f0d02090c0f0904021605011808181201180b0f1b0f0c060108100b0607020913020307031209090e011a15092805090c070f020d 65
    0x604094140b064207600400d0034425440d105118020303240f42668040b0b094151500001e600250152004040c800300150700000002d00c0c504803100c4080107801036640c4e02c1c0088110110262900c1d0030b6940d5441c082221a4201141d034400504a800c0301c0c43c0c6007000d00d1009002035400e5070317024442e4000035241401010140c280903100c0480c54000b0103002c08001c500f400102c2d102c000700703c15800c240034000c001200140c144507014481c92414659140c2480e206194000c2c030541d04000907603c2003100000d01c603000001c450100401c800710070710240006505201c440e02940d0300c000e500a410303200180c804407280c03420750001800107088881441e5030b0b4680d005041b80d421141c0700000d40c40b01050003044058028554410044c000821013406100d0146500d8112f03441c80d10b03c03d41c1051620941c1500180c240ea02d500c0b4000c00b5501405800c50641c0405c1d50800074401d030001c09010002100d2404030b0403644107000c48000e543c17070b018455843c0f0b0310907803005c0401c03a03014a210130b84d40007103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 593798785 1250 593797535 593797537
    0xf03070c3b101a030405010e1504030311040e04060b0f040207080d02090414040b070f0f0206061513060c0611190503041a010902090120070b03151c03030506010201020f25050102 78
    0x3c8082044540c0e2400c00d4181242914811113002520b94490064210180c80d44668294001e82501e400924007640212400780e0344250380c401421070242100344810702210b43e00407150764104845450748600b211080c0810380c002d03860040c00c291400d0044071141c0015400801d01240000c0c40040d00c1c070140750344202541b1065809844030b030003a0040141894109102004c0b1000c141094900410750900003941e81c6401403a090080301c14040408070714184c101501d08480095456661868684400425084018000fa181c241c01c0401e01c481500034107085442030340300103000c01120030030000d09550a50010b40308486c401c4103c0c2d5400c000243c5c0c1e0031041d020780400000540d5982d10800018042c0e03851850800c00c1c0400b49010103990040041d041085901c045003050700c9940e000c0314000407894120a403900203c1c034401c03054109104050600c5035622a4600f001240c0f0344200480c01c078010018041181d4600300040020504207082201050700f0a171207040003071090380d03181826 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 593800035 1250 593798785 593798819
    0x9051302040905150606040509040f1106041502071a041208070f0303050604241502100c080f0c0406090603090206070c0f08010b030a021c02030f03070c3b10 69
    0x150000401a5020740051005170340100c2c0c00c40300c0906182c00c0a000602001004d0801440d464600d18004104070001c41c45060244c4000c104513280c80d500d241c1f000603c1c24a6074803030018061044003140424100246038040803680b94440d04140c00c2501031500030b218600c040c4c490410501080f000280c0780942402460321958021400e410000c044c041035602e83c210020311000100d1020f1005600010b10000301c96a0490200d8480381c410000d83c2010001a00280214100491610020341040c0400d01131515000515078607138584200c400d2600540c000c04000844d0740004204140c46904010700441c0010103041c035105080d540c14403040020380c8507250700d0314100b4003006003240a100b101007050081c2d01078554240c4a900061075100d00604075002588002d6001f429174504000040c80b04409034101c9546d280c0d142000c46084030a44969529a445520b95240e490303100425844800b0f0340d008144400070280d0305090162000034080b01c2c4402d1035240000e0580c100011a100d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 593801285 1250 593800035 593800043
    0xa0302090405060409050a061d0102040801061508010e130c0e090718020903030304021c051504021903021c060f230c040b04270c02030c07061107090513020409 70
    0x180c0c84100c5024442951401000c05120300d1030700030500045640441e81403601941f0490018640980710b54500b140038032606680c42035840031a012800c0c03a01540241c05407980f00741100b61680e060301003110700a40034020042c0c0d26403004003207000007840c0380650310150f114507c5000f03a607071200507004114800322080380b61980010820800b8004c0841541c03051220f1030419460f108180c00441e0b942d02c0f0140009000d480704000143c034120000d41070a11096009094071707580e0b0513440910040c1001a00c09a11606064004004c401e0325440c0d0401240d07400b030642c0818807a040022406240ea00e80c00ba1401a00c0302c84041040240e8424914885800b5046003100d049500f02048942d400070916070912030204002d20002c510301060310700b101c0a80b01804000e441c410b54040500c003007540648070850a2810403000384d0380110160040d006118225405191359100403240035190009074200c58100c03c0052085c02c105030886c2d58001c28280040c8900081a400306080380c01002c0c05603 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 593802535 1250 593801285 593801287
    0x115031a120d0e09012105160b0d0e061b1c060807030b0a0b0307150909060b09090a0b13020a0219030503041b0b0406030e0c0405150a060c0807030e12030a0302 70
    0x1a1243d4003c0000340c5440426100c0c07100305d40c186481c452803003030802100440750070009901c0c01007190403c0f00b03015512070740746203000072984c9442c2d01086401c1044800907050424541c05480400051004d1181d980e42c101820354200070442403516a0203500700c600002142c0441c5901a0007034018034005004e03000c01803000e6451070404008154000d44528950340c1082110029039600240c06010794035040b10300400e102c0c08000035210702c000c0c1c0c1d11a59600d8100400082e140c3d1811002d045141d000f170f25000c4480d034458070508100c0b812141c005600095454030201188416400b030401d512442c01150719802d011072903801c200c101030700101c000690000410040114200c0603071300070803204030480542c9081100280140c0580c4c040d0604040d41c1d03815902c50301204000c10380490101400820423401c1254019482d0090002914050300074a84001140303403007241d4040d20316800c008554200302499404840d1784800099043d440354400c0d9060b81050420b100134003210f01103407001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 593803785 1250 593802535 593802553
    0x105040b01080d0203070f1b08010e0706140a0f1b140604050c09040302060a020a050f0a090603050606070c0e0a060503030d020d060501080f16030f0903030b090a050115031a12 77
    0x1d00e10f4030025a400100f150418080b41001134042d0445172102c990155003140b6290500e4a01c96403c001070b44802101c0d070070603020344618031000c10303030b44155415680d420441145400c4040024480e0f621060001100d0b0880a20500d101c0c030910b011031a210204022000d486484481d44804203442201440d00f01d8011700040000c00c11113101d0300a0182c81c0e01100c0d15140e2400780d225640201042c3c42d00b0f80018180c901c1d10301ca0f030125480c001103010259150382c20100014591481d0380038940c0440e01e000040344243c90904160341805910002c001041410062180310610020300341c640c950384c035201b0205240c2e805002420099000860040c3c656508044090540314207510550502c2100030a02c03a1801d041d502a0750320200300007011000464840c022030040280010b00c0ea00b191400c0212420560b140d040807988081c00c071454243c584604051008941c000c2c40391b540c031a1a05007002c0000c5000740c100d90686008440920210341c015404100200ca4454102895170080000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 593805035 1250 593803785 593803799
    0x609041e0612020d08030a14180d03020c0a060f060b03190f0b0f0108130c1e0806070c0f03090f0f0e0a09080a031109060d051803090105030105130e0105040b01 70
    0x416005140065207002101030b150085604180c000c140600207070780000c0018001c440c03540060030507100340f11100545240c485000d0582110900c0420703800d004210560000c00c2c400e0090700c406a80800c00340001c0c4000e6641e541c000c01d403419076001441d4440741c00217012024000694801c5180903464a4802c80c41d204117400c40d98008580041c41d481d00c01e1944180e16000e82c0307041107200a003050011601c99259071040c0403001e004c000c11406c1d1850000c110040c1c980044024441c2044500d021a521114556121131040341c80c80d000a07aa2004080402c0c02103400e820042d00a0910071541526040e428501c00d04503040134114842c2c450003048880300d0600d80da9440744d0440c3c4c042000f0300e5030340d071500954418540c0483c10940c6940300042d128043c2030813948041c4e00101841da8400451312007001815088880284041603aa07403000408030100495120103030580d181450f580c24941000701d180c65209403600340f16a20844449850401d200e070f0b5021b02e004400226096140c911 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 593806285 1250 593805035 593805041
    0x3090c0e040308060108060f040606030b03070603050405030906070309121112150c0d02040e0f040219030f0b0a110a110d0c0206070809030c03031602030c0a0308030a09020609041e 79
    0x121580036010300c00e08010110340d000c070340f20760045001d01c0d210303101e622941e0000704810602a1015800381c80c103500010780d550103500c02848050b090742554401a681c40c800d80c11903001b21000b40c0982c10030410100985005002080407501c607003030207804141c68110710008541d52322421524039900c5042c0040c989800c5c1c49241d18080d144008281d8030802c5641c00f60b400602418840d0082800b1807040002d00a44e0142c0c1c2c060702d0212038103042850401b17050403002340e0580741a0300a00041c2e0b50405200030810902068076003100904400c001266142d50b8070301802014084c1d1990f941524030f840001c40002001001160384e1001544068131665501b000242c403600b80500c000305c0800d50041c0ca5260590340c295401100130303a1203450741c0d00400e09040d081ca190320b91601000270b5070703048039046001c0006001d000790104e44c01402c125044c0200c2582030300000e00366800520008083c0c82fa103410110425101821042c240724415000c01e0a0303801c0844121110b0307100b584608200f642502c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 593807535 1250 593806285 593806289
    0x8131b08060108100c020a020433030204110301030b04030e01200d0e030705031e0a0f05060f070f080609061203041701050a0615050f04050a03080a0e0f0a062d03090c 73
    0x1002c04c1201185c0468040e43e1010740610080c0070320746846041c01121280003003401c4810701075008070380c03096050580e9000700000e400201c0c85540b400980394000080541680d0503203034400c4d5000707160345554506403841d070443c003809410001c00c41801c50980504d04851080705440b00000e244050511502814503445500303028000c0e0300030360003000140d400059618000c2041c02c2840280721009110030304203130034044050320f1a1103048000d41044000500c2c1486542d1141085400381c85050003164400350181d1034000240518010174164584815100e0b00a00d0013407121401da6405010903095411950101902003e0044800100c031002c1c011160710017043e540400c0818209070150045400b910494002c104020038810420072240b01110050100141245d0700d050392032034092120f91091180100140728040000340303c0c200300482c90f00510008003802c10306414440120f03401861189442c10003000e400384400c0c501d250124500d071203c500d83d4003050072601400c00a80b418125 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 593808785 1250 593807535 593807563
    0x3060306070e060406120e030406180909082709090f150f0c13120503180d0c0b030702030d090507050f010f0f0c02010c1a01060e030d08131b08060108 66
    0x941545141d540c40404907810358000c1d04101228205241c600f1b0010035411002529a2000050100d6401d400c252400c891203c05000c00100070340300c43d0500309841718580700500300c06040c13111a00b0440c0c0580c50f11b42d42140e5904000710316030b0003000601034403006e40340d143c1141c1123042c1c10130a0032400d0040006c00c6004054014450403c0780d200d030960340c4024007039441d503000450f0703003081d651411040d2002400002416140c01c1e4a80c02e08940725881203912800300d40c000c0c1c0921107242024108854125000100580c1c40e5151010005580d07000602d0b040840c0401c01646844a085100c1c00c0007840c0214020030100d800c0105000712601c4980440781880700c1040c0714600d059008040700c1d01c4100e42d2810048501e5144010b03a50b038076100c40001c0850282051142c040302450134000e0403154991f5600382155001010b154031815249050800586801c00150300d840341d0300080094148548940b915030004004454445000c2d5000403801c2e4014600400152208112406000e510 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 593810035 1250 593808785 593808797
    0x801090501121707030314090115092901021e03091003020721051e18011107050402160b0106201506100c06020c0a1a0f060d0606080709020306030607 66
    0x2c151102c00c2e80b01502e503c00700801c200001d0140030180300c1d81119904140c1c0d0301d8029400c1c2020b03c1c16074080e01c2c0d00d401186410800c1c01c00080c070240580290310201e00520244000348404034103031301c083e0300f107442854198483c1400ca9043d04000240b08c407140701c5800048c42d00e03000080f003000700c000b10f650840c20416006009070000304280b03c11084408201c2c401480d0703004e0308000240d4035070080b03280480320100380c0559411244880301c002d0602204083e021240000d81c50015208000c1c03005004103541c1c40710b42c2c244114249a0f000742004183c0e4480740352440c3c0540d4910580714800d0f0003600020b02481c400c613500135011030444010030080f8001c0d10380c0490009599140350001084203100f40c07002c40500ca00c00d030040c1c1c181d45415402c400e06555903d0900c0215540d1024054125046100c0c14101e2452030701d40c800c09805290426500007160304d580007008080003825000303aa080e65101d2001403007200400c22580200007060025031223203040020982824401012402446a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 593811285 1250 593810035 593810069
    0x60c04030201140f250501110a0e0306010b041a1909050306250509180a061502030f040909230c0108010503060f06100201020c0a082a100f0209100801090501 69
    0x107982501c1e224501700c04074211340c080114902a00e0880100c000c0c00652904104080445911008040c01c4450781c49117a01c6111800038190343d401d0905c00d1191a0105001c1407080f02a00020041081540c56a00c0e003411100c90301e10803e100060000c402003810581e00300124103080c0601036010700c12101070314014016010251241645440c14020068001040c2c07803260346030109020314001300b031605415841c04040c080b00a15031402512002c09050341e040801604c0007080301d59940210001604007841d25080c1c4001d8800c4800442d09910560481c0e191801c9507800880c4884400000381803a000b5078001608400040e00494040d40181c810000d90280d81d500568011600340e40d202042074088604074020b0050020340640c9004c0c50041d001480070031000f90100503500c402811300000c500382010507019103080e1020781e5800c107030b01d96044c2c0c1c034565208410340c031845000940740c09880d50006291003da1005240401d402c10018081303e01c6070f10540e8003500c00c0e4184074040c10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 593812535 1250 593811285 593811307
    0x8070608011505070f061425020a120c08030a060f120812150d031101050903070b0c070c17100b010906050d09060e01140411040605090402060714060c0403020114 71
    0x68200d481c02e00307103c0c00141301e030104441c80307595080444e000070003048804040b400403008440281c40c1034180352100c0750100b010709400c0301090210603035030b0020b00781c0c1000703070b5140c0c910540d00070500001e01001010300c00100d03500c600114403551008000040d16414000a1000c0340005d812080c104a62581c0340c02c0060703411400c4404201e9900344004041c1d84080f440c0342020002000c8903000605000c48904140e000b620043e00c040c45080284604e65815084075502e00821308003400d4035041c2008608140302d0100100355841c0508403c5400315140d400304042204000310000c3d03203610004580980b04414422030640003408d20b003102d401894108c00500c103000b14042c5184040d80c1c5d1002c2d03000c000c441c1d84000901001280240510103400d030502050b9602100c05a4040c201c440344a1124130b401e118900540704018404419038035213070240003150f0803d0204a55219445070300501ea5402000280c7c880c9880780d082c03650740ca042d440010f0400b55051300105031200b080c082172001c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 593813785 1250 593812535 593812559
    0x12010303030c0e1302181e090f0f0402150f03070903110409240e07080106030b0c1c0903050d050c030a11090a050418080a050d0b03030712030b03070f0f0807060801 72
    0x28031a82640981c1b60490103101c6c000f103910000c0210340c44407004180e4264082d094050340c0300340b4003c40f041c4045070354100300980b20810444c2d51208644680780010010301d02800b000f543c4441d9481001d04040388000c040225900607900c0001090000d0f50800c1000385030403052500800070749040c40003418664484400c42001407840705100a48110b8000200c01ca6001d20403034030f6800300706c03032130b560b51500b84c0d0740200018041941c00f00c4d542400130b0300f400380c014201c0b0314401c40032820341420703009000884020440d01034118100041003240c410b070341c109402650302501c49403145a076a0b0503d41d14030004c49800701b0b40e0000341e0206101a030600c1c0d50b032021990490754162008030300c4400762917401194400d903801c0203098102c007041644c0c0e4198064041c020291003801c1c00c024201901e4105541d030f00422500900e0741c8102c01d01c440c40705200303030040003002c0e001504a030002500d40101c8481020190000e2125920f141c0040040a0f010004640180a42e003001c0c822541004850019 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 593815035 1250 593813785 593813809
    0x304030b06120c1c0c090b01030e07140d0204020f0a08012409120305041e0503070f0b0a030e010e01020408010b0306060f06030412091710050114130509010b0612010303030c0e 77
    0x440c1c8000c0d03452060045103d504d8010700d80d40060071964131900c61078082d0060a0f04141180000e04d004907000d60340200080607029030744100300000d6900000c00401104e40f01c00c40b0b00700d820030f0b024803000e0075a840b01d0f00509902e8403540c0303d82e513496040c00000d0161a19028002200400044401201540010400f000d4540c90b040c403030103040c4c0c0c60030309031014840c0c0d0b480050302c1d00441d020902030841600b124020388604038240c4070801d9842081a03000001740c0240b101040e410400c4007402030190f48000e5400b10250004100c503040c14450f24220382090f400460340ea512907500441c9440d05001da0740d4000c9003180d01d2807110004001080003030000410090104015200702808913000326241c0f00200408030201c401c00a00003182c0343c0ba8000303000c0c210401400c0c640041000100b14002501c0342a0140440440c00070141c0f084020b000090443d5240e5542e8008000301d5071600001810700711074403071003480554550b10300102103450540b896000c20501d0182e0740303250307500d5035030480d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 593816285 1250 593815035 593815039
    0x6040216022713050705040507140c070305060a0609110712181208120702060105010219020d06020a050c0d080705120a0e06040b0907090e030a03020a0c060603050304030b06120c 78
    0x3007004807840304010b00302018001611504030804100030100900140311500c0d101d08141d514007656042803206640065440303070007003841d19003c40c005106030ba01420b5100588805c03038626580ea516018200101070329001c20068888105010f07100140c061f4940c0c00910b00d507450300e40020358913240d03c052952045c140c10000c401c1c00000c00c0300700c0042c1c094080e0080b290510b403032021619000142d0790262040701603030300c80c140010b000b4600105a9a0495006130040c00c000310000b04a14240801c20004a90144008e01000045a15031015020075200b6890b916501c08c03003207100b81c1c070342015051003e003080a00c10400a050340d22109840003803401c0518110a07454038641c080c043c00c024200c1c040507100d002d04010500c032800d41568000c1c0610410703a07101a40307600035201540d407054008405e550080080e5010144250300a012700391740361612002000080d500c201c1918126842941c60744d001080c14410710661510ba25042102210f40503d942c207802211622040c28050b068 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 593817535 1250 593816285 593816299
    0xc18071b0f1218060305070f0c17030615040f0f0503030403050718090614060a0f120b0702010608030a020304091104140f0303220306140601080f09030715090201080604021602 77
    0x1e0b0055006201d0908490480403556442544a460050040000b1248400010082d0071054400340c01042c4840d801600003100000240303030881d0000c1c1e160f0025101d241c0020045802049aa001e00040c10107042c80d2514a08402d00e4540c160b2144001f03170700031038407a8000f0032003000050000079808080300e202c080105040d50740c89500c1d00081030012400307841c42e401c0040f8500180106a401032160000301d8910018540b100c10300846125140110050380c03100348043e101055820201d02c1d13202c001840081070142d21140300c1c0781550800c0344000096480070800348441c60243c042d800c50154801c1c55107080624000110905003e04001140501d2801c6640541c03138406000b144c00b0306443d43c60b00d400e00c000001c0c1c10bc146559911040c0c4041c2c0c509000748071500038500c00b560003904165200071791b079115000000709002e0080d298000e02e05c010003d1f0f01c001008071a10a032a0340142c400010241103a000143c6560b80c01030199120381e02c100104c0100300700c100f40303106a1940695a00c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 593818785 1250 593817535 593817563
    0xa15080115020a02041a0a081908070c0305160306111606090c08060126010902060a080a0912080108010c020c130c0302040e0c0714030a0f030902030c18071b0f 70
    0xe9003000f102c000040d4225042c034a2056504e80c84404240308450159141000e00350f40303400d0700d9202d0b021240d070092400005020440425511005441c03901c0c040c0e10a00e0005a40707548007490000d026001000e040020034042091184601c101c85008080d149601c2c40c100c180c841441d008100500002d1890369240d80305400c0c040d004002c0000340500360111000c9503141c1800750380e0310b040e00c0342e8003041420580803141a06418040c3c0d1070500d48c050160342c00c080c0c0001055802d0711000b8080c01189942d0740981e800310300910746901e82d01c01d00352109005541041707100340c20744140c1c4500c0130540d8403c20b00010252180740c1c0750300c40440792440000301906e151604801038410759001d040244030500c18003900d210510002c0001a2003030150003400b40001c0802c545900902980c600840d010310300c1307441a18042d0300403001043c070040070f80748403483e9800043d00c1c00d04046009201210800200186640c122030303030700031040424220740f40300c030480da803084007150f00802c00600040e00c1c6005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 593820035 1250 593818785 593818787
    0x2c0f100c14011b2708061803040503060403050f0f07082104120315090e01150608010b0313030e06130e10030f0809120d02030a09173d0b0a15080115 65
    0x460180d00c215580080301350391111070641c4d07040103490440040010300c0652000840000072074040b5031024000d485e0b103a4458070305646580214482030b0041c4000c020b00b5040310800c00c01068500c0c4141d07080f5455020344004094900300b80d1081104000d500c43c1400046242142a0803001d2210b14003c00c080c0c54002c1c03e00440c04441c1d011200140c1018000c1a081c00190000c410b0080d0500c50f01e80f84c1c550f00c05040f43c030741c0020f01c10380301c8014081010070510056180c004c2c590a000b800e040c0e0115a8034004140ca81c1c0c40240c600041d901201424401c20b88440c040680100866400302e0710b103419611004e20103c581d0000408104d00050011280e48581a0400f4151854000d0f01c80652000c0e8020f902c0341e10600122002504510005c5420703804d5204007680c1d1109400101401c4c586c003099040780d480a440d000282080120880c042000340c000d150041040a1201146155502d0b00b404a640b100b508000c50000148091096650b40640140d0440e610030f100b40a00d4079807004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 593821285 1250 593820035 593820077
    0xa0204081e0c031f0c0e0607060c0314040308061002030306280b04060503010303020c010503010312050703020a290a05071704151401152c0f100c14011b 67
    0x3005405000d04030030008031034032a41010030080d00aa50034041041174000441c0c0783d13204582c25a074803010900645012a441d9030141c80b58025600300090200d641c0a18250805030031201100000c5051040100d05c0c100f101030004040c1c2540011425401c1990009000d010392004004035607214032071810700c400a98000cc4000c14601a2655079161203590040541c0e0017400f00b5005403181c0b070b071894020b5220f1001c60b41280e03040070425042030321140d011a000c1c0d010440c00d40c11441f80010380004564490058072040f40c58940490315a00e840d07691a2094400500c402c0c00280307842c080005564009005e90b41c040036140a9200079511880e1030001d01c2070522154081514141c1c1707102c1400382e0f41e0f1a1a058440d105094082256501011203081c17244d4141d179800b1403c0900c0314500500030303000a1046d00340007820f54a0800b51180402e0182c0c0707030340003994000b90800c0c000c44280311000d5000d2070481000c50007032003100b00c1181c002d80380d008802507203800c110079400180c03d481d410385 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 593822535 1250 593821285 593821303
    0x1410120c030b0114011106070207060c1401060f1502010b090604020306060c06040f02040e0c0120030c03161b1d060103021b0a0c050a0311060a051603170a0204081e 72
    0x20580b10403035610341402c840710f030702180119804101502c11031130740e0140003d06240706140c81c0d8024502d09052000489440780141c00482d0441c40c81000c800c00c820742801444007901030818525603003840e000080e9501144032501c1c0040d649400c2c01c1c14100e0300c5403403400342d002509035009130f500e842c1c03103000c6402171007040351a499500502052000700301d9000c020f2307140749008860a1200d0541c480c4900e468018408016012408500070050300c2c0c060040240b45e1407050809985c10710280c1400d007400c0da880610740a0202d044c50507102c04000044c0711407407070803001085c40c0c0d4520f4109503543c103004c504100c0403440c5510304000500707030340e00c01c0d011164002d5184541041010101c00d881d50744028004080310701461010021800c3d04069190750116900442c5250700c0861074400d2146603401783d011207041202c1048080c40d40b80e400b400344d00c10a8400e039580021682003000340081d0784006003102900600401c81048520b1000441401e254420015040c001110b070140c20718010b920 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 593823785 1250 593822535 593822543
    0x608030f0c0712080c06180606012a061b0f0906030e120d0507080f07050d09020607060e1f020f040b0a0e0406090b090c03011d040311011e1410120c03 66
    0x2c00a0b0f0204284000507141c1c400d400310031110a0380f82c0348503ca43c84c0d107840140360190350042c40002d50ba50f01c200c82103000100074200c040400b00864036200d410901c41c00b0269605070300c50705100f1000910120306c2d00304000e140342010b8081c0028a009100120030b04c580010144c81d61503100501200f404480c00c00d9a011001e80d50790f4000d40d002501920080720448042084400003034501005001202d02c2451070f41d07546c920b8403102965140042400c40d00aa070400c08c21301071800015442d00c190f8481d011824004e25245c01c051988800381d00c80b080607029100c2c0103118180c04031050605a0f010756071400c22141c0c441c012080115442c070b49050200c2d60050600078001030001160780200c000040a03188010300366504000316255110038481c0001c4015041d42480c1e803081c10a9825800c640709140c0490b00f400c2500901d801c1d28501c81b00e04186c045a10050440501148941140b10150729800003840c41d0003006068138100d5072040010303030103207005a8010002030855490245500c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 593825035 1250 593823785 593823809
    0x200405010906090f111e160b060a062c03031c02040602010b0a05030a020409150509010506090610020624060705010212010506070c03030f09090c021f0608030f0c07 72
    0x7441001c0750190070184143c201062820142400c008910700030030310045484030240b031402c8507016541c05030010f02c10038204441070a02c0160742104001c0c0d81d540c0014064154034906042a82c01c0004540d0203a02c48411b000c400e516440441d4071440003030004080e80551140100c07203620120342503106110002d00b60007044480203281450300da000d8001c3d6000740d4020410070340010280062603925006195140c0c1c00710880000510303081c1c01c810f8407e440b0749001d00c0c031251001c4070750341621000e940610090751034508100d99401d180d41182ea103c90115030381000b0741c4228074042e4444602601c1d1001644107001c028110521044519a0100014124070ba40b1801340c10719038002c2d081214140004e92201000144138a000e2080e9042550440f5071841000c0c51650280c0d54082003013554410301480020001307c03103030544141c101005503600a040c21110030400b10240c401d803048a0740030b2528000c82030003001000001d0705d0320003c410030002d6a40c401c820056141504550140f030400c14 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 593826285 1250 593825035 593825039
    0x15080a110f100c0501050c1e0a2a030f0e0603070c330501170d0c02010c02150304120504060905240408031e0406051c06030b09010b01080112020a0320040501 69
    0xf80c481100b0314904d0083d8000c103d0340d143d500300b0040500c145d0081008500e5030140f5880752603da54002c0c9650000b0703043c02c01ca004540150b01450700a503540301c1595100c0d08070744400b40b540114100d050704650380340c04031001142c2800940030707010152080082051903141c2104103c19580c0340b10300c803c1240c1180220003400b1079108425400c1d80149140c0d2424500001178409210308046020721403140034007034142c124641140c05211450f03080c4c0c10803103c002030901684442d0140540124991951692441c142c01e1460304000c41c00700c01c00811604020400c1310a034019080300913584111369094001801c42480a00348104444816154200280020b22000e00000402c01038680d0080030306080d049084482541c001e41c800e01000c40e41c05c00a0110841c0c541851132003120b080b4000045190f1030741c5511282110450f0410380980d552284c408407581c00250b4140100328980d1441c50400c2140d0100303d04035a1480010301c00142c41c00c0c0701c007004141850000c031600010708200415a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 593827535 1250 593826285 593826287
    0x10030f020a082d060c030705032a0c01140606090d020423010e01080706120c0201020d060e01180527030c0a080d1b020d11070e0a050a15080a110f10 65
    0x74603e00c64000307400c2000140040d42404a10140b060108803c0b01c1c2c01c55484460030748d034503880248203044411b2440c3c580c4420142c8500b000341e92543c070000143c0c80300e50034200306007181e042c281401130804050741046541e940d050201c5800c40800e0b60361181d602c52500c003240c0541200326101e80440f881e00d4030042100d105c1455030707040700c1001207004602d0743d03a030000c0c40d100d000390b004003000030f01c510003408024141078104030003030003551000605d01410a8154800c444843d08004901c071071081c010491695031132905407103800c22040c100900c1c01e0003911012489846140303500380140c0c03000c500c2d20b43c440c01d00680f1031056051095511060003440d10f26115400450b00c0b05840e807401d01c40c0310440c441440307242c550140039001840200da2084050300c02da880c1483e903c40d0b034407801c1d03c0402c551602c100128058091840b0101d094102541c044050f107805c0e028800070745050714400c0200305400545280080d0300050100e48250002000c280711a090000494010558540c080013203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 593828785 1250 593827535 593827573
    0x304080c010506010815091005060316110c0108150409020a0f030302060c03371505030706021c0e04020909040f050f0c0a030b190c05040f050910030f020a08 69
    0x200e18440003000a036441c50b005481c07642c41501c081c210703201c0d90800c0138124148030380c00035000350b090311100207140c0c0d50718009007840c1d2044030a4081d03900d070380d000d004810360017441141103443c4003c0078000c01020358000806c0107800501080001e14203480c401d03004d813110b5000c140002d402400350b160440c1c031400000b0b03c101303680c4402c400610070030001038010000d0b641600d01038040c00c05016004408201113400b00103c4800d41e001c889500302022551192900c12209024a0b6030440c0b92201d00d40380806080040941c03081040d900008184480f0030b802c80184c0e03d1040e0380e401c1c41f9011110000c04038000b030190558568020725039000340020702040c01c80c891541403241048617540050354005540306c03843c800c80d0b19000006901c00b0b000081c17403103c809074800d00218030014600d0400340240b096808612194000c240e0000301440b20302092884080981030545440c070743c906140080c61000d02051002400414504200c02c0456858a641c200105002411514a00070301503040180c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 593830035 1250 593828785 593828797
    0x903150702060c090a03032001020c01090b0109020c0c060310080109060209040f2a050c19020a080609030f0705100f0615020c030309040b030f031603030b0108060a030311070308030408 81
    0x1d4030400b40050300c40051802150f1261070040d00802d442443d566054031a0441d40d00082d1928082491900c542c4e0000d1024100c1e1416400000c00c040d0294100410b5107003060b00800c900600400030711250b00000036000941c40780c00d0703414640d40e540700c4680c0125818603801011155003800d02d0403003405803e4019103140d0308229010001c1c0011000c5941c02c40754000e11418250720220601c10780f011810071400c0c2150001e00740a490014460000c600b0044000030030304412100b40006029810040c1c0303258041c00c0d034040106000c1c10008041c03543c0380910000b68603041400140d4404012081c0201400385071807a1301071160050064214000c3e008038003d46480c690b03041101c02c1e405100240c400707c0040068081c600d010508014000600418a006900340c4903012441a020074104002d0542c00e80b20074400c410910030303140043c1a18669548941040f0780c0b10300784003c0d40c0c0ca40342e0701021690304d41005620805c00d00009400c2444690014121038000b100300301c2402a01d4004202c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 593831285 1250 593830035 593830037
    0x21050d0504060e0d1a0612010e030d0b24070c090c08180c180406061a0a0e0d031709070f0303020f06091513030207180b0301061a07061109031507 64
    0x31043c4100d0051202014800c1030103401c040a07000c031304420310764601c000ca81111002c1c20095403c0300d0754401e242962800e8180c0b60b0540d1001418a0000d8094420020480400c4404903825020b440031011600300c0850800000c000001e58401004110000e000c0104100c1c14107001543c1601c0c80500444c0742100c60300074004840603103100444020580c60000c0c02c00402c100c03c042c0200d00c820380c01d010000d2080360510b030307905008500c500701109040c0e292110110368030340c0d960a01074001c11041c01c0881c428019005108450002500010302100215107034911100e0ba41d144603a440c81c00440c1c0e8806402e502030414007000741680402e88030407210b2904101c444646640110f25603d1349000e80b002040c15058000c03034078507000140c454000030702a01c1221300c402d07200c0c40a80c13452200120300c00c0340180d40c1e0f40f0301083c600f0f003070240000800881200401441c008188503d891013010401000580d41e5100181040d81e0301080c1c90b600ca0000e01100d0400e00e60a6a80c0b0410300b050f10305e00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 593832535 1250 593831285 593831297
    0x902090609040606080907062c0d020d0f06111801110709050921041212021501060e031e0606040902030106470703050f0d0e010c030c02060f0121050d050406 69
    0x300f0614058540c00549103c0030450500b0b40c03241d04203c01d100c0c02c01827019640480c4e05c00120003d81c3e40d03a509850710380c2c003070380c0700d071042c401245002c0d802c84c2c5040103401c0001030f05010802e02c901e0f10701001c0402070400c2c20043c00700b0000074106810013a0540094406505d014244003d62100044032180215005d82e010b80f41e50b01100d25500f540214450381440d041d020b01c4040c00034000121610140c100c6004841507d41049440c15a00074242c1100b030000d030851160703803800c0c90708001c49020900c1409180c032007818043c00c000c0e00c2c2c040c000c1c85180200c2e200c02a10045440c00d500c16002024105500c103111541680d01e110006500e0001044500321401114190001c01401d50008e10b20180c06034079045256030181d440c0d422a03d00401440b106100b4045885036a009001c580090a000022051004207000d4102e900b2450324030304550081e410806895110005030341921030103810680e00604003400b159403905802001061401080c0b1009a45900138019100f5605076440d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 593833785 1250 593832535 593832539
    0x3090c0b0408100b100c0302030d0c0f031a151e07051b090717181e0d170f090a02030f0d090b091807030204270501060302040f0902090609040606080907 67
    0x10f80903030701008103150b40081841e07143d9040c41e00848580e00300a10a006513401d08504011078411203020201d0803000c6032600503040d544662610400c0d94040f110f0703480300d00c003c0d0000c01140d0b05958a02c0101c00d0b29400146600107518228089400505000302e440d41da48000d242081d200c0480f26041002c0780c0b00b01d000d103100c0707143c40d050706031244c1d24a545041000300005190204901c01070405103101600c3d401d904002c0034103000704120050060851000b5008a240c141d1501e030780c4001000800c011400c3e810441c0045000190300440ca11540710500c0d10341080315410561420b200940c9131040d500c10440d80b9501180011214000303803a0020312a0b500c200c5841148200126198070451131500c201c1e20082d05040c09400c99030b64580141403a0b2100030091210002c103d502c07400581da5031074030030352032040e0081501500d620301d400c1d414a071034000c0c444901140c50080300c250507001f02d001c44054465000703548142800800911545030f0f1000302811080c4240c880300c03a90f001d00800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 593835035 1250 593833785 593833813
    0x513060e0f0f1e010c0f1a01290702030f190b07020102040e0a180b01060207080f0106080c13020f130e090c0105030106030c05040909060b011209030c03050a03090c0b0408 75
    0x380300d900364000303000302e0103800f000c0300c1d0180405260440d035418000e480c150103003c1070031000002c9142d44650350303002d41c00b101f115850030301d000140c5c80340c5c03100004245601250801428000c81d40c103010b24881e501e4030360314030000b42452806901090306209407010303a80c00c621003c46c0345403850700440c0344218503124000103d00780e10a500a00c01c07807850410208107190110b07801100d000412946201441d0f60079a41d803d54a4400e074800401a400002c0a208071217051104511202c91040200b055602c0d00203030320785038002054014401d4500c40f2420f10540c00b1a01240d40040b220800d03030343d0318400f559490b040301c1294010000114202070000d01d182400049207810700341c0584820307046a10b012001c078080c1902030740700820401d0a0200203035803541401031404452081d41e000c2040304031790740010610703c000c0c0d05083d0030b5418600e090f404039410044103610b050b05131800c590340c0c00441c4d4003030700a04206440280079014503280041c0030031203200035105558030001a24501005024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 593836285 1250 593835035 593835049
    0x20120d05100b1602011d0907020303190b0a1a0408030309100b010201022d04030503070f2607060507210504050c22050703090515010f0b030919030513060e0f 69
    0x210780d80d4440501c040710f03000740d80504a02d0391502ca00d42000f800c45070080012404900050b54054003690002c01406690041d0050500780c10f80172090810040025600040e20275803584507040540f00c3c001e90800006065908890240910404617543e82c10f2a04c9060766a48941d01a510501d1800f440014590704c1802102c0500100c02c16030b0300040002284001a50203682c52003007820020070000000036818406407960500070940001c003288942070204d01e0700803103501d80300007500e04404d00b49010240c1080c1e4400039040580090303160345030181510071010b0b4900b902d1840d80304004816100c035942d005203116911950913100909549401d214480640c0a8400d445d28400c02f803c0072210215406158806081d2a002c51030750392584407203041481070380c060380c2080c2040006001411259081c032000b030102c0c5a40914520b003041c0c0a5031907a182081c0341ca06119103a92107030070301d4407070700c26601d62185c071006a404031640d518016060880c4103158900401100a02c8801854158 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 593837535 1250 593836285 593836297
    0x30501050f09010e07112506031b0f05090301090b040b0604020a0c110d080714071505071e0f08030f01060c0c0e1e07050c160302100f03110307080118060620120d05100b 74
    0x151b6403602e01103895509452f4580c0e01041001040414041c2401d1035a0901401321424060364510417982094203000300c60748001030041340110300411548601c140d200b00d00601043c2c200c140d6008a500030070024515003003c00002c2c01110004c9101010700544900b140c442000d05002c03905486c0d139407292440a8000004c20b1004205d05120520204900a03079104084824605074140440c19942c5d00200f49117012090b144100044100b08040c00c0c80d018040c00340440e8200102942d007d5074800300400306034004c11206541000c00305201c21501a0342240b603004c4010a804140361180b0002c01c6504946020b15681c4102c1000092050170b44035950182c980191040c144040a01030590b039040200f41a0300415503112107a60030100aa405140108070f256a161100e52600f083c0b034081c80c0c0301c05c8220401c0391402e0340400c103c54102d211403a401c7c00140c04c040060541c602e4407810f010504054801c41c100000740f51074024010781c4503c0c800c1c5400303201d802509807201941d00700e03400341d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 593838785 1250 593837535 593837561
    0x150f09150c0503090d03050a08090316321b06090603070f02120a03020306040605062d0904150e0702121e0403080d0606030501050f09010e0711250603 66
    0x101044a940034492003100703006a00500880f841c2c07510560110f498590690002e0700011004600301c94059440301415402c9180c800056007000c00c100b0800c0c1c00094480070040440d590345d003009080c0001810080c8409520500c805843c03140496510f48880c021403032400300314040070302c20140c0d150841c1642c1d50700c4005044c1d030b8116030b6400c40a440f0003620034503207401d40c0b1407007207140e100301da5117402070500c10390f03a035005600c83c14814103210a8a03000e4020380e00c200000e0082d004200300c00442941c841e030101c184001c40007080740360b0f1441d502c500140c10fa08141400c2903146c2002a04130a40201d5241ca07101a0555640c000101d881c0c98800b01d4403105581c04100003c001a0780310161407180558501c0c051400360340c1c0d5034094140d8801c2199444454650300c0c2008145d030180700740380c0140810b481192001c21000c1c0024803090050056030302c1d0302415004219110311840c514040f182c2e41034111a00601440124801c1041078850310a80944010340880d07590f01c03d0284103220102 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 593840035 1250 593838785 593838809
    0x609080a02041505270c0702030d0f03060515040317030402100305060f04020705010b030d091404020711031f0b01090e2a0a180b120103141006150f09 66
    0x3041d420400500101d504441d2540010701000c605540c0d15000c0d100c410307840c100d04410310001a0a002c0d80100000c000c000310703200501801d00580c80200741016034004030700d080c0c0203811425000340c0040070160469500001010340414118020070010001d0300d009036495500340b4600e0b2400c40701440f003220001d40160808400800d00b82c001c1d0446904200014a031846001e200740c0810120b0300098000e9403a81e444440904040c10207011b00050b1030054942030380d2039801c06c001e24440110041450780625400034469040c446103c0b21188190300040640750103074402c190072991120071201c0300020300c1c42c0220011441d8068044681291880c40f400c80d0280d48440404000c2401400c01d544040c41404035100030403582d0b802002c0d1700c01c2a460b50519000c00702201d801ea00c02d644c1021441240400c8449400445c60764554112503010801003108500d580107142080b0340100a01011400c060340403079140e007042c0c50600b14200c41d07940c0341640c11000c441110000620300c210382142030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 593841285 1250 593840035 593840053
    0x8010b161e0b0a0b120d200313030602030f01170c060d021204060c0f08011406030907030606090f0e010b15090f1c02100212090607030e210601060908 66
    0x5510001c403400802441a61441c00c50380740c0b68458001411034088030510354410f80b0203001e1924040c0d10200e41c1080e4001c08030360004501c00f4201c1c41074039010140442d022a1800d2000408108442080444412603600103035030385803c2c4060740003510141d601704000400801c5d407509100141c00c845072100d00918003142d41d0000e201b0250f00400c80c43c036895808024140e80707850301c2c8900c603029600c910340006001c102c903c00140300d1001c4120403410000381c9801004800601241d1086a400c200c0d092640c940b50321441501d8481c0a90008203414148240000e0403000c61348440400001c0c2c18051125030280b40b00c1e18221030b071034034501358424140d2424441c000542400b400607031202a18000c03404001900090041000f0500d285040511521000031810170088118500c041ca00091804294004d044089402050703060740c045c00010034018149881010b0b12001d07e08090187c21800607400c2d04074441c5858044c04003000c0c0328400000840034407641e91201211400c0014000c480 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 593842535 1250 593841285 593841293
    0x90f200406081b070b04060b041a27100602010507110607030c110307060207061505010807080601050418050405010c180b03180607050c0607030501032312030a0204030308010b16 78
    0x40c4094800f40c61909441031000c003210151004165480c0151400761480c5464030f4204280c1c0d10307055041e4000c60074181200d080d444510800161100704440000380c01c008901c4844094903108003003480c0804a400b481490510403124a040d2481a40240300755034a5203000e4a03c6c4810803610380407513000c0c0e0001001c0c14400e81c00303c1e603d15039034642040c001c04400c1e0482e01e15085074000361107141e40058160200071135803180c1d8000240780b80c41c5011241c0303424006409110700818140910494000059003607100d20111000381030700b0700c0c140555800303030f15184000b00000c480c2256290310b07000c142c2851900070001304034940e8200300d0302e089250800300950b0158101505d0b40740d2000d503480710f1844040b01482494070030b0010313540701c07602c403200c405016250240c09081034041c9464900180042202e441c08000d00000e41c2040188003400000810304d0191002c10410f402440807017840070010460f0018404c0703d0081d926000d40c4d90b01c4004c010001e01c12004ea002c01381c032412001c44002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 593843785 1250 593842535 593842547
    0x106090612090206040f0905060d021507081c06060f18091a040c08040b1305190327080f120304020f0112020a03020d0c08280b0a090f200406 62
    0x198010460110b0401030542c013045080c3c125421005401c12295014095105a44109236020b00300312821800c5028130340210f2121a0038400c1c0d01065240010031800740800b81c4200d8001c0b06000380405400f2440740800001011680107000000721441803821203240301d003107000c85a110b20100b91902c070f45000050784c0200104121180540b9603406400415542d52103487e05011080c2c64480c1e40c0e18051600d210107400040007140c483d6031064a24001c030f280090141001d54040d81c451000091506041e40d030762054100b07141007000624a19142161a20f64140c21507409000315510300d20f0402d0142e450b03080c0c2483c2900750150a200250141c681a00030075640309041c1452421000f96650342002d9a10081e41000865000211045410030350301c039450128142d807400842a04260743c0c0ca51140c0100c0389494051a8a00089500d0f03004542c841c00d150b61009003943d00c0e00b9503c8003108090141404244c1ea002c0c03a21a0300c40403030030040f07803805050101650880c074040c1440070682d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 593845035 1250 593843785 593843807
    0x4110108090c04050421170408031008031b190203060c0d090c090501081501031227090e010509060f070c1502040305030c0c1005092202031611030301060906 69
    0x7280328090404540c0e4035544280d0380961300800c0402c2185203c4580304c541040d6121844e8200b06034070703003490f4045491004160700580d010303492654a40b68580b0440e061150341e0400c0040c0e0200080d00524a0100105424a1411030040d580180e0200d621004044c0300e046010390150031102c00241e05060b100b00400b098550307008002690b000d5910303801c144d0510783c1c211546865480d401400540010015203000313588081c1c15403219811a80c0b08440100b4101c0d41c9401e0014110070007121105110301141801c0c0817464100c0742d10741d500d01d5079020300001c00014005510741004911440740118400f07124079521680e505617521a04012100c6451481c002d4a14600d505021004010b06000034130046000d00001d5880d88004c00006003070002c0080ca40d44603040030b9010000d410741040a03228058000c90301c000f44100c0d540c1e00d04426680d203003003c5100c148004200240c2c0c0050b034807028005209503841400d08043c203c40d0b55030701d100a000300e9002c00c503060702c01c0003641d101e161401d607 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 593846285 1250 593845035 593845051
    0x150e1002090315010608010819030e0409030909110a080c040501021c03062402160e0127050a1e02040b0306060304050a0c0b04170307080405151309020405010e03030304110108 77
    0xc1400519a010078044400f17811490024003110010040f0001c10056015103008030001051840701558001c0d20030b1031000d0120380980d454143c00414036020300004001400c14042c1800b1926808107080e6003580310070341c0d0310040747c4c016020134410304815094509990303060300180805030482c01c1440b0a054040741040405442ea41d020401c4a00711004601e040500e0104541e0b4200c10350005e4244202001600318640b030f02041000b0101c1c4004a45d8111000030401c984210440c0703000b011091400d00d005180c044c00d0006022400342e01d5800704c01580e404020112107880b41c24200403d0707105d1481644600342082c0042421803030000b00940d00548102d0443e1650b002035516075a4038062a8040c40b0200d41c00f1808120004562842105085151000d14500f00055a42d003600c0d0080340521405070347c403166290300c01d014000071940460305018864450568803181c01d00650300ca800745c01d00007488503280c00c030030f0300703002040d21b005503400003a000b40055480011944020000c10b00c030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 593847535 1250 593846285 593846293
    0x70809060705030c0c0111060f0c03090109080c030703030b0603130201031104080a110906030d02060103080c01150b041505030103030e09040c0909150507020609150712020c010207150e10020903 85
    0x1400501c04000070042180c0c13590144c54180160760014140106170040e0f8007058016004100d000c1c0788100303040341c0c041c0d10441159225154121082e004004500006040040016264103581000805040c0481c400c0c0e87c1480b03240805403c0c00b55602013681c01e820715100d80c81441d0015030013900000c2441d00c010391224146075450155614290700d040040d1403001c0c0f092050000350410b5070750340d54401c4050b00280602401ca040080d654041480007410040011502c12800301c2c0130b401c07614001004152660b00703103840b0100003034203500620a01d50154800142000103502a00c1907a04a94060301d4000b241084007040c801d4211004000720342450880c2c0000c0707000281886001c04c82c41c0960300e406107400700c0030300600441d0070207000903056611010401c4602c1c41d00040b40b5042031045c2103050105d440707004054843c200d1000c20b51300b009002240043e8007484c154080c02d02035000d4844c55600100d40d8107040300700d6149461380c40c080e8000c0101e640482490303800030100164003800311303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 593848785 1250 593847535 593847547
    0x10239160b21010914060418020105030c190237030f0306210c121101051b030a171303050a0e0f06040311010f0302430312060602030702030307080906 66
    0x42c4011140980226294654135178103901c00c2a20811403690007001a6420400d40746003400c480c450352480b6000074100603002001440154016082e1414502c40030342c0030781c1c0b0200941c8080d413114100d00b00c450308880e03984900340601c0c8001d0101002d60008203e0008800c0140c1c60459548503801020300906031615800070304a03c9005601880440000704100c40c5007841c684060034100a51100c2c00040030803640314003161040a240c040240e0909149944080384441c003c0c081c0305092055031036000214000b000b49402078840c160000c21200304450681d1818000e000e080d5503001c01900142c018064058014010762503802001401400c07004090094000103500e49d009030411242c0c2c005000c4c0c2c030040303035800c60030801000041b400c0650070031080d2020b03010304000c1312450340203202003030aa190300f41044484100f107401c5d019400c0e86124000381005082c0705060358514924500d04003001030030b00d00c080b0036140c115900402851030440592030304400c0d9000b441d0842d80c0040d0030001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 593850035 1250 593848785 593848837
    0xa14040b04030c12020d02070b0408100513050f0a020108160f030c0504090515090601050a17070e100e01020c0307030512180a090f0f060308030402010c05010239160b 73
    0x41c040c04c0c5800344e8000d0032040c0300300c0002818411283d200d4540c400040c8802c1c000a10003245020400042074030003d195500c0741c050000c002c144d054050100e004250308542032501c0030404101e000d000383c0390b00d1900c0d10742102c1d011901c06a014042c0004441148259207240301380c10041403190346245c05401d154231118054200c032002e40f0364104d25030340508203030040d091590b007455100b00b0074241203060002c03042d400341412106004050040f01d00c1e00015501034098200c0d000d1861003d070003488a0310794060702419040c01c103a0300074090300c100038403000a4600054210252580301010b004c0107489043c8007281c5070054030390500728a4008c5207800c410340f0f030203100000034210b940b00400c035190b07900110002c46008500c184001400d140052020074140e00889810035421328103800008140d052003402409140324030b0050b9580080d0600070410311350000201041c0c40e25070082c0c145052801560340c1d0a001c0160264640c041104001c219403201c003512010b81a0b0051290101c40002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 593851285 1250 593850035 593850053
    0x4120909141b16060b0105040306110d0609050c1b0c031c0f03061406030714041206060b03090d0c11090a2c03041a0d050702060108060a14040b04030c 66
    0x141c400114080c10402c003141e207094201c900c190038034846642c500700b0340302034120460210b1400900500c1d15444080003c1e4424400c031001075421400800c0801c1007030742c51640c036030311400c05400311505025021a8007107080c828940983d418202c9245410794580010706502d0150190050341d025040404280340c034280880070802036031550300400c05200341c4002c1d00c80c080d03000341d0004140c50000c1c10312000000b0510184003403002c942e1551650b03a0404226900c0309404c40c40b8948010110700000d0241072683c503d000c1d80d21410082c4140307a00c2e80542426400b0880d41d40200e5401905003c2840340260b0341561303c01e024540c0c86c91422000f0010414060b41a00c91080741a507ea80c0301c207140d1048071301c45101ea0300c0030408043d00c5101c001d00e03075901d008500481c254495410480d0f40d900c4074a504503181440c02100500c15031034030b01000303521181700344110b012500981c000904004154458071407036a0007000c645426032120785990030551401803044003071003001e402c0d100c0800d8060f0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 593852535 1250 593851285 593851301
    0x6260708010e010e1e03030c0f09040f0c030f0510141c0b040605010b190809030d15031e08040303030203060d0506040605040c05100212070204060302090405010f14060904120909 78
    0x10300007103140d982c54080e07180303001d180d0405c17410f20b07044070380c80c03125105000701c01c0742e821a40c910032031034840c604410040078612030102e280d40e0040c907282c0308941260f9240c02a2074030f5105a00c0c100f101006502d618420b4410880b001d007803070445584140a520f40002c02c0032501c00340601100e0840d21a044025080c04c0c208509843c07c005503030410040040394000c05002d4240701c12414180300a480d04c103991039000086030000c0c01034039000283d040c03208101b901d41c950280300c001d01c0602c00407a4250401411404251021060348000c0c1640c1170041c80c009036025407090f40c0c1031030207255440850094202403c807e900503614520b05000c07540070480e26000d140508000105c078200703441e080400078410303440a0700942542c10402401c503008030b09880f06001d0100c200742c0d1a40c43d48002070050000c2c0d000250b200705140b01780010b0001c1540400c50310040103208116000518801035001e1208503451a80320718214000750000da080500100a0811424100915500c0e800041c05540c03002d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 593853785 1250 593852535 593852561
    0x901090302152b05130809103005070503240402090d121101150501031503050304061e09050d020d061d030904050c03011202010507050f100504020f040626070801 71
    0xa1980c3d40c01606180711300e031340021000081c8599803c880e5241081400f0741c1c01c40b6441580e00342501001c29001d407010143c9092036840c0c00842d581940c003000c070040710111710810300c0c5281c0000103d0560062080324050700c000c800c1d1003041101c40002100c1820740b043d81c16002034080c01140329a495080100d1880c41c441d400f8030f003111032401001004000210210700d000da0400d10f014205c84a00c08a40341558001c3c600810700d221410450355060896900c003d01074880014001178003684640c001c540c0c044a0950b03200036000d1040c0c111b84000c1c8038003400d540840218070580c0149404c03001780902d1840380201288105542d03040c1c000071b14000802007100e410009102d00c46203170510074194005030810040c3d00f19410850015010030700c4d180002d05104001503550b090000c1000b4601c065256501152002c1c0c3c1c106004002074a42520204d01503a04100342c3c4c0018907160040341c6c01c0e01c181c3c2010103100096042030301901124000400d40703d000303940010600c0034080c082c01c81b8040c91 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 593855035 1250 593853785 593853847
    0x7170403110f06040b0105130e1509060c04060816030b1503090706111504030c0c06091805160311090607350306040b010306051009031403090109030215 67
    0x40500e150341006070001c10b62150390810020440000c0c078240d40b82d130548a0035100030340385900c04648a0010200c240c0d0080481c81181200b60302d040550441c48c0c841c201050940d5000e84402e06a500903000c0d80c0110404104203c0c0002c580108a044445000c4002e14002c101a030700344022502da85440e110500401100001b048201a4104540d030300409680c5020a00c025200ca5601e0321014854595425881e107100428103152140042c1460940c10000c01a046a940d42002e0080c00c103e102e15040c00003034585a000d400c09070304c42c05115001078640c55101510240c000c03001449014103ca01154003841018126121080500091803048c000b11240c0440307480d0400d00c00034203488062080380c0300384a00401544070002d503900024107450204c0d07a10281c400617409880c0a40055801c0a070519070501025030000b2948100d03802907490003102c1c100d84032196101c0c840e4004442c041104901c0400045c10aa044090500e4540480c2400d000314240300300e40f8041000700500340105 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 593856285 1250 593855035 593855057
    0x20103091218150e0d0203031e0304050606100f030b1f0306051f0f0309020a030605070c0611041d0c0d020a09060e040510030609020a05100201021c09020603040b07170403 75
    0xc030842d641406003030f801050300a203000003200141460002115240035060304404502151010030954150420340a11001d2016400c040945513410032901504c1c20300c1510302144140c280007181d00301014056403042c00035210184150003404940e041e282d0402c1400500ca03441368030461100e1880041e0340d4022500318607200c00c0105a40b0071152008403080001d4003e00142d03041600204d08078210f05001c41c5c1d1080c5070000400b07031960382d44042d150034203010401040355070012845691030721034a02040b02e01088000142140240e015884030400740b1135031205c1e408071003240c140e0300a0b410b404540c6002c020a000b01c040e40c0001100c8804a28005130621005030801c031180d107142e601740c0b010440351602c2c40301d00400d030a20303110186c01150349440a9056441d08013003500907280240001400c0a01110000e00039401066a40e540070b0101c01099415913850113204c0341650001c1a180c2151126140d0554050014094005001c0f0192040c10390900140549100c0d6009465000000e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 593857535 1250 593856285 593856317
    0x1e050a030b060a081b090d0c06080f040c05060705010f0e0106080f030c0d11011d100e0c03031e0712080106030509010b1509150d1d071d040201030912 66
    0xa8500d1041c248551414081c840c0807542c8440c0c916800800c0310904078600c0600c2104c64103034403031000c01e140c10a81c0c940308401030040c44050501250380d981d84a04c0c071540c4002d1290085030f826500104000040c1408210519021001d010868010400050500d4200a81000b11001111050b003540d4568a00300b08640c030600100d144504080051490411908a03094a4103100f107000030500c5148160300002c81e40948c80502d41007081d15415000b05603060400b40d6038803600c00c01c201d490307050450000310810042804084404044e0085080000354061500d000d200c1d191180070b046000d21240d0301240340d03035a80011040660302c0360011941014401001c1d1074006040c003a4584c10100c0807841616180288601c034074030b0050340c94451400c00300107017000c5590f4800340285034000c10360366032002c036540c0030131121140c4c00a04081404045041500c60072240700303072995000603044090803050716900480c2c0c01481450000341c000200e5580f02080414006460b002030320030345c0c04400c2c81c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 593858785 1250 593857535 593857541
    0x6150c0c090f0405101503050a15060b090306010b090f1005071b0303021c030e0111030a0f050f07140403060501032f060a120209090c0703120b1509011e050a03 70
    0x7100154041003024034082d1075045d03444011a210f03129003569140a400502c880c4482c000203141e01c40c2c241c2e031990600d810000034002008000740111031400c81c00003540c00c41c64080700c41040001c1c000d405142c0c40d02002071181c2d00480c1d0b86039042001424150403d03519208000c43d03900c1944c40321902c91865041914900d0001c10b08102806082101400400d4002a0341081000207003183d51600c0080c48003140075041110000000d07608000c20f035130a202944001d1171140c3c1c03215400300050403841030640e040d6403060302c00800000708880414000303840755050301d80d512100c040b95440c040d174030750710003088030001d80c42035a842c00c08860200451821070074501e0f142c00801c442055036910079002410300d1054844a409004001407500d4448249806803000c82c07100400b40a03007031403d260b40a0300350f40301c0001140041c43c0c00a1520007030305188590780d13522202a1001507409040c0700034038440e07400909054107210000e401e10039a40c85444000c407120f01d082d42e410381c41d40005000603081d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 593860035 1250 593858785 593858791
    0x1e010204050301150e06091e0912130e0a0c140304080f041d061e01050a0c060603050a030216061407023106090e06040305031003050f0601060f1b0b06150c0c09 70
    0x45890400180501c01c200501e001c0d58441d123001842290b520345c40c080324a4414040541090040c02098020b50700c8a20503003007003220a60000c00d1003d5071582c0794441142e10740720488002c2010001000040e01e810300156034040c0c8140b440c1c600d023500e440350200e10b40c0c019900100c00c0d00f101000004464504803030a5812180075541c6042c1003440f10b007142211555410004e04102000c6180c586291203402c4001000307070802c2007000056140d0a000b138840c0f0300f0800c242c0251092420706e041d07980300803064404540943d80c2d18114484900c03a01e201d16888070006aa00c0700b56500c1150451400c1c5030400501445040c0980d10740c4100b10b070060540d2020303400002503900e043c00400f590100810502d40c05035140c82d0540e502da448030f0030950444110341001e041c5125104030881051000036195069030456111280b8006d001c0100b11111101d10b030130001c084602400e100c0016154201042d08800c0040904c64071080921907140c01c1d4214a60480e1a03034002d5440c80c9442c140481d4844e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 593861285 1250 593860035 593860039
    0x803040c1a09091506040306021911070608010509181c0f1b0f1b0602030703091703120a021b0c0a08121b0102040306020f03060916021e010204050301150e06 69
    0xc00c0c040c0711800980724800007005410324000c1c4d0021902a0750f54003040760003541c1d110364115103034070305114507c01420402101d5000300390b1003250084201c1000620400700c81b035036036a58400b0b03820181880001c3e4009421001c041c0000300030740c58400e40034421940310014064441c12003264001d4000e0040e036002006005101c1e40703024034a00b042c64002c844491540210b501e014000483c500100b420350320407030b1083c285007007800100c0c01ca58040021301e40c0c40d0282d515820340b146c4540c80f08402c0d04400d1140b0f59103910810040381c01c000307825401d40c1c2c0000d500300d00509142c210341104030f000d16031301240117003034112044080e424a01960014050040d1078014854091000c1c0c40e1a4148111420072681034181c404004036400250111006140d0241055454a01d500016071885c0c005454481c41220104000354a00f0860f07036012920080c55802080f4140d4202210000310342821030240055408010200700c58400f400354512031178142000513a0a80f81c00c03c503c281307090150010b4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 593862535 1250 593861285 593861287
    0x601090512030a140c0703030c15060f0909060b0325090b010203040b0d0b0d03050c0d0f050d0f090f0507080d02030724090f050615030c090a09020d0803040c1a 70
    0x1e903038044000295441a80c60307003450300200354042d107002c2c0a4000c40850281500c81d00001108041d030280707a4012051049050285003e1051b0380d1605545481c0143e01c0b448001080030032030941030303070040a00540030702000a0341d030302d44401007428000e000355110400440c0c1c1203a10407070007554540c80c0040c400440c04006140171540003d480b4070452180701c071400070100d540035240c0078607070115540681c01004120340840c1c91801400503000081c40300307454081d44080e2140c40d4021046850190129514207103822280c116140050100c101030301203903592166102e000910003140e0000d428001c85c010460185400325180c507000c9030601200c1150818401c04c4001840002c1000855114003280980315404250b00c20040489280c081c11a407800c612007428464040350103402210595851011590b03500c003455585c2140c4125184c00c0014140050018040e40c0d101244461009040c1214a0f07001d4543c00c0040c0c0040c2d034140d03210750a00204016281240854041a26502c0c45c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 593863785 1250 593862535 593862559
    0x270a030309051923060c0105090618030a020d080901020c010623100c03080403030e0102070f0501061e050909150403021b120a11030709091b05010504180c0c0b040b06010905 76
    0x7448210010407000718400d000314044069990317810281c031440c5078600020803c40c81c00d5442e40303035508016900a82504c000351310110082c0030100c00c0310103072210340c2c0080501440b80c840460360a4001082150155821301880c0500942070040304010a1104042d413801e5911440d001c121500d11804103114505a082a108080d00604800846034140c20300c01e080b552141802d9010b0080c034401e10313229502c00100202040146050a500a8080c0008020b074948520170f0010310014004424518120040100074514200060396070000c9104151801c001c4084484880e281056a084000d604480d900c914807800c0b4035403c2c0c050301c404550800c01520b007503100c42e445007802e420182482c80c14050403034084d1800c000201c002c240c80b10042044018605203180e1440c0c40c0349100d100840c41280004180d03206e002035400340c4481c0a21400c0c0e000b8500d036204000c050285504052114603045140801c0744440b00c244698054034140045140000004003600351f00d40001744255144080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 593865035 1250 593863785 593863799
    0x1e171c050c0c0a03030e0102070b011e0f050a18022208060702060f070e1f02010221041e0c050a0b040302040b01080c0412030507020910080706030b06270a0303090519 73
    0x3203c03075920b40504000602089951659019100e05070f4060010502c0d0000001c1d110103101210741c4c02405150311946443e260400840b02d00501c1c410790364410038420742404028010b02100c2c00704a55200014608441c900210a004044c48141c49900324123110400c9612802e2001503400201840544071910707011203015440d010140420017040541800c104454a40c142520410911803584c2080c0002002c0024040d500c070302080017107161800b505203011b03031607407203c107014603405444060000c00c1031440d4400118806170a07030380e40c82c514600242584816503c0400f502c400390b00c0c15611825801400213032003003541c0787d504001c0480304004d41400d0f440f060b40c06440c1e40109032490381c40e20b81001c86090280001c06980030100c0402e02521441400e038140031190304009035424290ba40745d0580c1201d00b410402074114204121081c08100c4100032480d400101924000401d10b0f02c0d40881e441d1802c1c2c2c2c1080f800700b500c0366400e1006203044034201d00340f080c9000200c000310b0b0034545c0f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 593866285 1250 593865035 593865043
    0x3070201020a060221091b0102060c07060504150216060c1706040203070507080f0318240709170f010b0402040308180402090d0507030c050a031e171c050c0c 69
    0x1d02514990380400c9841d4804000030704540c5c00c40142c941e100715810315051154035807484000f25415245034840000c040d50010414070300c50030312160766034241b8506464001c0a080d00600455406032000040310a00034103101505650800c8200e1440c038a015146c600102c407a5800240c06100560b0408a01c62a8a8034104d90000c4117560260b100c0c1c440c074a05a650780241840101082c10120340d4082d4148480003440c441c00d5010220102542844034081e00c505400900d00906440800e10403202181160a50780041d0a80f400c41c803400d5a51032a014255410311056110350030090311141040400d02070114122001c80f400c62400d403070b46d5584221403094134540041c1d050000010701195a4960655a070004064014020307040701d85041521b8500c240011690204066001b040c2818840c110f2016654001c490250b000b0041c69040280075104000f100e8560b40f038210302100c40f0201c0064400c604404003805003007900403803810203a40d0000c0c585000040305200078bd2541d04005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 593867535 1250 593866285 593866303
    0x905130203071e0b191409030129041e02032203020a060b0a0510030b180103140105010806040812061f02010b0f0607050705091f0f050f03060f15030a1a06120307020102 74
    0x1041150700c01c5c210040019803401400e08440d8554032b002e100481190000314180c8880100700f040407604000d400401044a44200410041e9056020702d503014802550040d80c01084561000481c41c0d0520700d083c000403902c100071030040e0003140c0001c0800801e40140701015504440c03506d0058100404202100c5103e41e10704109521448820829154505074801002480c0c000000c29030312414030b8030b02c8a091120350240d640c40e20300006a03900000c20b015001300e40c002401c526011009500d4240264007520050388000d00f0807280e004d00421540e42a1b002c603041c5c00110314000c3d04010400d10a0302c10035800d0003614200508000550049800320070b60f1800c0b10b80c0c041c143c40d103503061110b0b0034042340c0458002a62480210340483c2c0c2c80c1d010400c075038088440c81c98200c903107002d02d5110002a0703000f40c903e40100001c240344003180d051001c0c800c0b2014007190403c140c10b8540bc0c1903484d60820103800b1128800901c4500d00305852201c3d1140c00c0100110710305055940000c0d62000b4417 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 593868785 1250 593867535 593867537
    0x9010e060d110904050c0307061d060a20060a0c0c120f02160902040f090e0a1203090206031509010b0f0a030203180105072d02070905130203071e0b19 66
    0x46042160b0280c6245080601601040700c910341494040d0341d407142e0080543c403034450b41200060b40340c8554000e0070358215600428058040002c14498942c001c803503214107020007079166030038100400580e010b10b203032018010401070825914207001c8943c01c0e40c45c40c0130040e502c410880440c0348bd070501440103071a07182001d07481004c503608905000c685000803030f0b203000103140010540010b8004d4000d84140e10000300e00a40d54042c0c078022230340c81502e80e80d001d07044841000c0220f6980b0350032210790342442c2000301f5402c01c2540014490381c01141c00740d1041c940c542900219042c01103c150141091602c8607141c001103010384411802014255420103800000080004c5c131400742c06014601194001d101c24207210901030200b001c0040000407130184042d500114a62130b43c05060b1212081c0c000d03004a03070410070075102400d0010075880c644c1e440f40c0088030058804000d82c4008200f04210300c0300e91214868280c1402d90076a0008075030304014004240c0b020707011074540041101ca = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 593870035 1250 593868785 593868799
    0x12080d18170903030f0d15030303050108070f05030d0f0311070b0f09010b010801140109030606090b0310020a0504030201080a11040b0c0f010207020109060509042d060f08030405150f18040b09010e06 87
    0x1c00600b03c050000c6c8803455501480f400c7d400070070907400d500800e050701d0280007625461525001c40301990280e43c402e1581c16403209910b2441c3c44e01917001c00794151814900400c02024030450010940d110b81411580120300368108110540001c4400e0f0304002420300038080480b044000901c6050103000b209c8842481c4420140d00d80c2c01903032840c0065500c16000d2200c0ea58400881e4000c20502000c54081c4c0207041e9000309030301241c0708440100c0c5003511142d041a046400441d00040010041c4165595a16100001001000280009040c0c0751941d40d0349603060211182840054401d2489a07030040c440000140e81001410051300e25618003a9141c24982c03001501030020702a035070b0082d0088205040b41c12220301000d000f12560b00b4828011103030b84105540092043e03102d480180e810a00c01072040d444d103880c030704030400b4a117100c15040031000c00170128640e10012211002d0241400001e8560038140164101448100c65114083d0700d00035102e0b03034001000340f1840c85030360 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 593871285 1250 593870035 593870047
    0x15150e152205030604030305061e01080106050f0d0204030f1a0c090d110a090b0a0501050304050709022b020711030d0801150c0f0c0f1e12080d18170903030f 69
    0x1075000114000e0000504031159414141005001040143d40d00c501800942d42a4664200112000d401c0740f44180d446002d0b0fa0310b0b05808850640103c16401c014032020882000c2e184c03200d0000c0c00195010ba461103080b02441c0c606900f020041d801c201e036103556440d00b04000c207145c89080c0d0311107070401d40d5030084910062070034458603482ea001c1c00d81e001c40042c00206454080b58020042c80b50140c618a00d07080d02c0f40015140c80c00102c0e0b0041c40390b4070035802440507610a0300584441450b6115940010040300b60140104824a4169600c40d6010075000203000c04c240040c50444230a0b03000d00003501059030028641d0005020300001c400020fa0804943c40c880c03148a4040ca41051440280d03400c02d140400580c00b9922541078170110f281c8d0b022600700304000c100a10340342602c00c000d040ca407810008100c070418200d400c0d00e003840244490ee40b540606d0044884508010041c0411240207142c28240340242006140900c40c041c0807110194500100f1a076881207040c1d0480d032108 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 593872535 1250 593871285 593871337
    0x1050f010810110f030a0905010f0b0f10020304170d0305071e0804020105091305160e0d120903150507120605030c0f0303070f0503031501021207080c0115150e15 71
    0x13106072026143c01d424000200091041183d0102107010300c11402808141c144a40b01b130f05465403000d8281e03119000050882d03823460100302c05130094400d40107481c03c203550350800c4441101c5046090215800400d8100041541441596030001050404410140c0200380b000f01002c2000c1a110611070750401050135680607809071103003513030010320a00c56202280940307000b83c44159a01ca820400c07601040b44c5480c09101c0310780e8030100c068a150241c4449031221103113000d001c051071081c0102d41d034011001c240300303880c8500480b0b005d00300410281800394009141c7c850343d0302c1046a59103001f40520803a6404640c000c201c0c0070440340b2001702c88050000a085115094000b0080349230001d44408108022001c2c1d4840c0c03900d1008040c49644000059071220311240e80040c6c1444108141c0f000120900040c010042450000003a0ba8090a00b2a2a25152074100200c89104151000c0d07607103500c12031802142c54141d4851240700ca0300405440c403070283c078100f9104841d038114038030145 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 593873785 1250 593872535 593872537
    0x712060b0f030f01020903060c0702090714190f0f0903030503060f060d1503031101050606030c0d020d0504030e15090901050d170406080615120601080a0b090901020c01050f01081011 80
    0x10078004058625000e003140e10b00d8001e5000e018028064050b460000300c0300c0d40048160742d01141c0283c0011510341c0c4441e42203c0c180300000440d440050203008202081c29049582d811000c1d094503540c1040b86c2611014220903005009d00007003004100741070001070f500c00c090b08e400c0074082d1004142181070400180d664051001c040912a2900d6113100c2d87c45809826241140d000b611800000741c6a82c036038600f641e40842d400c03600007000f00b000c0b0b481003030a08000c040101540b0401030034481c0c0d000c1a0b5040d240d00b070350b0a40010301e541d0307416a0b60345012103680441c046054010340c9801d0052010841c440c0c414420980700d01041074a14050100c1460351112005682010f01e6840b600ca9070302800f81c0e80c081d14801e02070741d51401e50220356009001140c0d07651281b2a03126125907202c00044420340401406004450380b100d52802c12900c525034080d00952001001507203030003550041508442009045546070042c800040182e008041920315000000107400300e49074040c3d803400012 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 593875035 1250 593873785 593873809
    0x1118090903270103061509030b0711031305010e0d0b130204090503120907050105030106020a2604080c040b0d03080106260106020a030806030c0f090402040f09080703020d020712060b 80
    0xd40710100b82c4401044014450141d089200340c07003c0140c161200d09120020514604190200c0d110345020f0000c0741902011a038800040d10704035000309910b115030307419900b0140341c070317044440c07600d00c1030005681240002a07401c41c180e851101d820b03095200e180050402401d01034000000c09181400e640b900e4210301c0e81950803504480c2d9a515050307103420405811594094280103d0700080b59540c414003c5030b040700c040341e00406106105440b040780030700041507070300525020402070080c0e8025000c080c10041c117504000d888821002410704c0f060b562010f10241c0b0480032082c5c2100007a4016070703800c0c1540e14500c3c21200781d005540d18920000c183c14044400e040850000085840e400514459007134800c0e0b94240c0285c6030348092507900c166020f07400e64040e800c480e04280ca41030400751a0b038054001000864160740306124001181c260340e0003074498000004090b4203041e01005401c10141080c80100189458903460f085203620044008181e03d8540c01d01000070390302d000d07040403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 593876285 1250 593875035 593875057
    0x1e160c02040b0612070801080304060e0f0109151d0402090315102301120e061302010e180f0708040f03030b010315080d1812062315041118090903 64
    0x150702c00000700104c20507034080b12500300280b00c00d4008510351101006236821203089890341c1700100304101c00c100d9a40240c549481c10400307810b0f0001010380f42c45200c245d4a03903180d101e00b41e43c8540844042001c040c0600030b20f016500401c0521065100001c0310902250171621494203130b11800092141c000c0190311031742d068400e8000418030340c0c0b24549102c103502c03026261305e64110f00c035001c03840a4403240a0400540d17008040003070300d0444030300c00b02c042c200e105241100c680124a0300144405041d448411940c8070560104852240c1c4044c3c00758101d0100d05220311030b444c0660352610403848001005040540781da61610b4a80d0294102404010000e0000c0e1182e0381c0360040c641c0d60f540118180c50000341006030320307180ca110f00101502900c2042854011601da9034403500040c103020307081d015000040042d002010a074400c075843c041d01d0342c81031070044048100e0400041d102200107221808004200411036071200410107a1030030400e84110f6800c0c0c1e20004490300b18090814401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 593877535 1250 593876285 593876287
    0x61303150516080423160801020703200601180906020a0f0909090b0610021203040c0e06010f2012070302070503010c05030610030b0a050a0b031e160c02040b06 70
    0x1000405058115910484440180d034411040c00181241d10701421369000e00302113040c100295a500b910b0301e844e003429100700f04071386640521200c0050f0310405644010103e03580401e20341c00301544400b0303018a500109840c0036050300c01d144410340300c0340f0600c900381c0c8600344100c51034105541600601d1846400007002c40d102c917000a005403c500d00d42d43d4600c0001c1c000c18010401032024410f05241d40c2d0401031425175683d035001803188100d00450880250700c140004204c000544400641c410f600c160700545000e4500310ba502c4c145140604024180000202c41e80b05031540301840005030f40d000840003040d0580845046e003046040012800031960000310705041c1900000c1c2e40c0111a002d400800c00d99401000444041c0000d4981ca03600c50001036403118000c3c400e80284680202c000c100032100e42e607500010300211b41e10340c4560310f03941d004004c00403a086180c1030303251450524232481e0f03128600702030210030340014600484140011600f41d1415921540d104a4011001030611 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 593878785 1250 593877535 593877563
    0x815181911130b011101060807030204020702120703080d050702030405010c03030b0d15140604020a1407140601120b090c03030906071502040e06092809020f1504060e030a020a05061303 81
    0x1910141494010f42804503204180140901e4014802e86044551590103400f229040d5401c02000c1d610109040e03034000814030001d0a401018047c18004521821500740c1e107a154082c60300c141c510050500080d03400510007004140d8100c420810400e901d03150014840d202d41380001c4101c01c017110013820301d031100c45001075180c0d0541d004400c00b01c04408c86172070307944e1400c0401081e44a803140078000a911071a501c044441c070300016080c43da10030840035071096080080c2c00d00d8161f090b40900070107152302c040c160611800460540d001448400074001262031310f4042560780c40307010b0000c5d0040340d0000303501c0107104d05c004013054240103481e810741d55960744031305211500c141515010f11075203615000c1151010014003101050351855540b40800c5c3c0040c2c10301c0300801c07000c80240d0300000310a02d4041980d8640204c20f120f4a8125072064481d4200703a0028102800940814006c0c2e00103c0c0102c09a03a9070b118440464404132401c80c1c0e035000d158210354004161f50300080c1042c040340c2c40b03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 593880035 1250 593878785 593878819
    0x50706020609010e0a2d15050601030b030105040c0b030c09040f0e0c0612060607030309081204031d0102060a1503020303070515070305010b070314130815181911 71
    0x16a00402c4034030300a0003154407401e042602d500843c1c800520440450400810461480814450301584403003030000c40c1c60303aa11101c24802240511704a40d568640c200043e1f903030035201d041d000c01b03015030080000c2e2405590b03e844482c07190080c00c14500012002445a040d940120380c0001c030050424000c2c014200071000140c6a00e02c1c180500d030240480007140303814400280d8007200405184030318030f0b894103024046a80e012040070b400301900d40340e4dc4000315035142d0042c5034000501d081000949440c0c1070051100d0008420480c0c4034004a070600341341da81c009406a0803441e071200005854aa49205400d1000680d200940500000c549a0140440843c0105564000c0c0e20103040f144d940d0007080b022138009004501504005100b6180400c0c840c0003440d0b62614500c2a462802040c0000c040c0380c200030398494481d9520403860402c1c810001c44038a0f400002c100e545240200e002c030340c8543ca80e0f201640054802c074240484070107108051111201c4104041c1160030100d0002007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 593881285 1250 593880035 593880043
    0x3050a0e07060e032428090812060405070c02120f0a0308160c08040902211f0512060610021204240c380a09150903081b0705070602 58
    0x1040511034040c2c1d41c0c0302d4044440603032412102605484d0b603046240e40f0a200101c2540b003d08001040c221411150804d200f014440c20390720728003035030340240c540b03040940b109c04142005005d0b90045d402d202c14002d000c0d030030a10b20b120803907048501780224006851402c2c07078000c0c9880c94024502c62140001d0030f040d0801c4881d4041e081d503048030302c60510144401d90f443c03410700100920040007040104030008090307003d0201180c000c5000540e1503904210003040300d0381039665030080381d51410000c0b0501390b5600410001d2000341ca83c42415107029190589580e1300070005800342c0411000821228424005d00c03c02100050209440c5d684599017401400c4078041d081d0a104c101d032000440d203038000d114100740b05038000040c1e80101d0100a4406010300281d106001c40415405401c017281c1c42c10035804d00c1190391030310004215529040542604042d451004d17201440d2010364030120b0f912041241e4090514040c407103c0c003040506d0180903118440c006041401100008501c1c3c0c1d501003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 593882535 1250 593881285 593881307
    0x30902030309060f1c050402031e0c040912030605040501121b0e0910050f060907050d150e0f011a071e020402030a0903080a0204061d061303110a14090703050a0e0706 73
    0x4074954105d1004401c1004507102540c002c1d60507801111035a410380000c0500d21703451a007000035910020b0780c800100781550300381032040356007142040344c905009906208620040004031000c0c000d9501d40380501001280c2a203024060b8450000000721071900303580f13140002c0c0307101100c0d09841d2a10802c125198a80e009c40e0081c0941050003207140240444299030080074014149141601c0303000c010f80e1181d000c507100440498803000c1000103035210200d1040100304410740014240b901c40941c2d0250324050304140400003140103e0007482031032500b9121215800a4a58003000244e403800c0c03006004540025031040c000001c014003052140c010700c8100e4800e0303d410f0107548544034948140d014500660001542030303142c401600c000c4140d000002e40d006090b0528000309030000d0f44051450f600103544c1c021403900108880d0818216620007403402c0705070344e1300c00840040000c0c25424098071390400c050f102c4012a848103865070000b031404c0d0403042150b046690712600681400004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 593883785 1250 593882535 593882557
    0x3a06060507150e190210052703010e1203011d010b1204030c0c03050c0f0405090307060b0a03080f0a020706050a050a0302030711060702070603050c090d080c0f101e0902030706030902030309060f 85
    0x2c49602c5c0f65031b030b00a005591000c0e02240301c4c86182100c07100c05a04400d032585406a0540d240c0382c500c2100303e070030322084481200e5541015640d6040500d11078445000359020280002c00c1f00040040324818401e4602d00d65040810b504c0e1a00c40d03090464801c0031040018140e2800d10000108101c0c0c00145990021002e5600780c0259402c08100030031030300b0844840039250010000040010f04541c049224a00c00034003d514880c1c8940f00e14000340c008605076410307042c00040d6a00c01a404004000c0248242d00e8400c1c030b0310f052600001c084d406059002c034281034010000c40d000d1801403c0440303038009030104031074052420003002980c1381d0891190b140070924050205000c00c4000d001c6820034007024004062040243d6240c55050f4081c0400740b4143c09054001d0041c1c410a00110100054070000459280b60019000440880c0a002d101009250021480040c0c40129101c01215058180003d4007009400428118420110030304c0e401880091605542040807024214002d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 593884892 1107 593883785 593883799
    0x20d0207050a02090f010b121302030a0b2707060804030c1a0f07020f10050c1c020a0801080d020c060904023a06060507150e1902 57
    0x605400c454a811450084080d441d0140020342c1200b0b01c440c030804113500d420507c0c0742510801e0010510b842004000031003110501c2d9a500b103542e0040e068550300e0310070f840c10403103c22007159212051680c0c100444007400e0b4001c604d00384581d002d0005c0c42080d040110a40d0f40b404014000c8003004203550b03410303001070514100841280e880f4a00f40c1500e0601252540b450040249440210361100c0300d810005100000e01080b090404c0c400001d280e210340c1e185803454801d0008280082c1d0001400d41036280780c1d0b03401800c402100748d8a18030075989840320f454644400c60072001c01039211440740f01840c6801c40041901d840000d0006140202c3e9400a0900702d43c80503000d8204039a1041d869400045508400da0101c01e00104020141c10002c0c00780c0b5900800c04082d20511948070f4070100c12813250720182c0a10358000482d0300b010039803142c108a0b0000188102c0c05059 = true := by decide +kernel

theorem cover : BRFrame.Cov 593705035 593884892 := by
  have h0 := BRFrame.cov_init 593705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 593705035 ≤ n) (h2 : n < 593884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
