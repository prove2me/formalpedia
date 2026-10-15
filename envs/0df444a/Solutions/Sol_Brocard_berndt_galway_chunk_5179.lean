-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5179
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:00:41.272766+00:00
-- url     : https://prove2.me/submissions/5a1cc639-de1e-4d5b-8966-2f1aecc3b7ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 931294964 ≤ n < 931474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 931296214 1250 931294964 931294979
    0x3030204090510210212030c0c0a09060305031902070e07050901180b12061f110601080d050406050d2004030b060f062d03010b0d0b0a1a0d02070b0c030f01 68
    0x284900882d103801030701d0024440e0b80700661342d03000307070f03442c8040c0141d840700030b0941010b411174012551b504001c0e04a445409040c0c070b84640c41d40050425130000301700b0603046490f4603540e406400c041004515841d0041003e090003004503030003d00444403680707100c0ca000080280150840c1c0055400f041203100080700c0e0b80313800400305050300e2007280e8060502094601540038143e014201e00d410203201001e1040ca52000c0c899001c000c41182c80b02010700030850402490254140e00c41c60700358001c541c4c1c940040b5171140465007256600d1408948806000711000001d02c48118140020b086174401e075201c61030f41d8000361003140e004004010b4660398000a108002689000c1a94001070400c040541112020f070880e01c3c001c4083c107201001d41000821450355402a08110f813220720100e21000399003680d00600c85012000c1e156070400a1400345208086028610011450300740400e9100c1d07021a5941038403006a009501d45107142410391841c141366206407803061030f5171003a40010a03500c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 931297464 1250 931296214 931296241
    0x7030b0310150306020304080a021e060c030c360405010f0308070f0b0f040209070e01140a11070306060501030e0706050405040b01050c0a03110f0d0c0b070c0c03030302040905 77
    0x142809009001c9a2600c0c021500003440011200340a48404120100108100d840a10f1089120300d012a60750115400041c1c42c040d0401e10300860542d88005210701036002140301500300581402e01516502c401412003018040c20072810340e184011880500355400d051400e1180c0d502031036440c59464111018031041c2c44090050b1292920030361002c100040307600b001001c03110301400032807850078059554204200416a00c007111302d09240140402e40c505490041e4014078a81882c1802c0391071140042e040d902c007810807800d0030b44042940d0100b00d008501a48414802c4025940440c2d200c2c03900800a1409019846c00a403510340011042500054400241c5e00030740c403040c1c101454001000f010300036071040303a8108401031060700d1612108012000890780720340c841004142031170308814544501c0c13003d10303c59648000081700c015900400003c3c441d903000354079a4610307680c00005584450a00038020030454000000005055055020f40306551400c001840716807150014491907 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 931298714 1250 931297464 931297481
    0x41a061621080c090a050901090b0a0b03040b04020d03020c030d020303040c08012f070206070b04050c04022a010e070b0a080f060f060703020115090f1113050d0309150302040e0703 79
    0x40703500070002c508070316503d101074081030b2002010341513031725141c4000c2150444d00b0f034050040300f91141294100ca2808044440240420070400703403e41c90240c40d03e1500c520083c1020b8054800051a0800e0620910510b00c6481c00502201d254584d0101c1c003d5883e8001c60b0180c803c02c0e0303500f0f0045032000043c0241c0381c02c0c40c0340e1040d41e512203544000c41d440a450780311042c4000d080030400d250050b158174015021081c0502244206072820382009820311900341d4085c3d00c00c501c104600c0d5040d140c4410150216020042e6100f03588810352006401086c84086010451165210001c0e01520181c000e101d10845070b514100c840d11000048400030005985940d40551502203815941c10032001401c07446009200100d44864507403c4c045440641c0d4000c02c080743d031180411580c1c411680502c0b1300344518200c80c0d40c41c090a09072200f041007813901401b031040703800da001107003414490484000600000070700f842d42e808070054040c000b548684194482003191000042c0c005019100360700f036 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 931299964 1250 931298714 931298717
    0x506180c0a2c1201020712050d1406090c070203010b06071b060c0b0f091501141002030f0d111903050a050c070b0406020a180b0c06060a080705041a061621 68
    0x8050300580200b1a541c4802c0005800030343d400d100071000307e901c80a1500302550143c81b484d0340c03841c61404490540340103042c0d10590042290034400140c88140d441941b0200103100325440b48218800240074000301d01c4000d5001001054032024400c11004c0707102c401030740022201e00c0719640c2c4d8003603401c0102100094124201103001655882c070b0809055403062100701a14051047c1110607040c000c1c081e0040800c507079001d00000c0e028103050680e4041440b45000071410200101c500c050300d1300c03501003800c070150744500d040910040303c003094401c110004c18407005501c5088800800034001100d44510300742c10500401ea8008500d4106c03403940e034202c1c0c1a208a60703215200c0304065070007981a0820001000303210242420380401d030701c01521105180715075644160060f01c0c50200090400391040b0341c0f0044c1046420030000c2c40c00101d420545010880e01400300c0000d403c0b00c10790142c103401100002e81c5010b0a03003800c0800718164482d1041e500140e026900742046002c04500900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 931301214 1250 931299964 931300037
    0x5120a0b01090b0d061d06010815040210030e15040506100509070c0318030c0306050a0216060903031104080d030e0c060702010c020a1203050307021b01120506180c0a 73
    0x400c031225044000c84200203445a060b00d6200c5e40c4281c00c513a1080a1001070011201e00226191b60501c0b1841c010f10316440280300c00701001c800b01e03003d0440508000e1103542140e803801e102500940041548181c401e0a43e8424100089888420b03601100e04907420b00982c0c0021f02d406c1951820182a99005401d03103260342d48003101a01c175203940400c01c1e8240003070b20301000800070354150440003840c0b02d100514009451450400240d8070041c0601244a0045c032a8103000000441c0942d0415084800070541c0072540c10701741c00030008418002c41000000402051905001070386003205409580c1c20407101d03180d1350942d1f44132880300315441e510880800a0101640c0b19080c1d07005528002095200c21644c3d0703007035620f00d03041000422408104003104200e462170301400003140f03188492410030070410642e00000e11114441c0ca1030301290383e0300c1c000b0504e03d481c1c00c801712040400f510f08507052030034020921070300f40e000008460f0000c0c014070420004035030344d42c5540d84440558010070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 931302464 1250 931301214 931301219
    0x1701050c070b040c0506040902071a0c0a080a0f050a060501081f0b09040b0301181403040612110c0706110d05040b25060c0c0b0c070b061005160c05120a0b01 69
    0x1610711400c058010b90b0044044c84000c1210799581d8000c00080065041c010780e601c5041c9402c2272031590060030a080102841c041000350400e00046440ca10040d25140c180c580d1007030248401024130b6007108000618101c1048052a080e900c080c042e10401d0702ea101080d0784103594002c240d9400047c0c14522908110708104032a44403018042001d001003010070b5481c0440c021a00b12100d100020840d50784d43c200c0c01d018004000301c20000708205501641c0350604040700503188039a508504140141d46d1410180c0e8203c0701c20641c0c44070911700094516186e9202001042d10690466046050180041ea41ca00b280074108840c12039180c00900360908010f980c1000c1d41c500b90200d241041080c10403840c00213840c0d80301e0011105516200c002401003e420030f003081800052490b614a82c00b007000c080170899810381749a00103422503110b8000e011030740d01140d42d80110000d410030b41460104a10800c102d00404034203480d006c2c0c41d480d2030700300c008441503914020008081e25005400300103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 931303714 1250 931302464 931302473
    0x8070312200901140d06150c120e0f030d0201090506060307030f0b070c0c030506010905130809040c020c0310020d0b0303190507021504080a0302010509010b0f06131502071701050c07 80
    0x50100382e14141002c0c000c0b21101c0031041d14a62041910551942c4e481d401400000070808150398000030616050301c02001e00d95030150070f007001c40300c1d0303105100c00607140000301c3e5070b85c0d290f0500000c0050151101a80044c070080c1c041c0c400100115003500407400001c3c40d07420002403003422a038222110f1040c0311507548a105024101400c08000c110203c48000c01151690000d1001580710760010822585801c0c50030701120405440e810203691031240388004599503c054901c054000c031000198004291001d900e866900303401160036028201d00b40c46040300c55800380c03202c6441e140003031200b402c036001007540320311911040307400c1f1016140541c401a40715030f0151829078070281c54099001d00300749060310385400c10341c410441a4401c10300c080c20140e0a02070380e50004160b01c024001c0615041c0001c07007001103401824010040402c1c0d141800300001d2010000304402c000344410003c040b54002c0d01e6005600420365049032000984104580521a1512414120781c805040c40026a074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 931304964 1250 931303714 931303717
    0x1803050708090406150e030106030f060b030705190801060b040545010312110c0103090312090624150804050f0601090c14120c071506030807031220 65
    0x106545507002403044642c0d0352220300c60540035008000c0d004c142c44074401c0c0e000b000000601c0700c072802a41003000410008054056071340410381e00c901c01158180610b0f002ca4940310a95100d00d0f8802802e000c2081c07c01002e45034482903815040c0240007181d20f8107040001c1c0e1003588161034109a4000710741c1403c68031080d04082e1b09030003075440d420043c03403010740c61801303500700c8030800540d0b01040040040100c0c0d00d900040c000c646043c0301280c800351900b100d84800d01303842158145a25580580100b520a1000260f02c0c90303009020001306c0c002d03003464801440d41440100e200389048204403d07054603641003400b241d990035481840650801c2c0c04884010016008031924803400c09070351410744050144c1406410503c10001c1c030f00e4502400107101d501c40e0325504028040030441000c62280301c601c0c0c2c44d03001d41d06041ca503035203803600c0c40e01320101c5d22000c1010300c1c3c1e185082c070301008100c000f400510016003c0d61f1400c100ba0b20b045005004c40301c80e08680e14107031048c1ca40c0c01000300300210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 931306214 1250 931304964 931304977
    0xa170c0a050a0308071d0d03120605090907030b0714070611040305010f051b09010212090d0f030806040b04051312030f11300c0c0705060c0c040b04180305 68
    0x1050380c100c4551561000c1c81c04608450843c080b40c01e66041050a684c41540d01101c0303d1040c501181010702c00001c0b44d14440302c01c102404110140c4200f00184180b50800c0000f0440034203c4951841d0042140c0c0d00c401113800200c0f9a41140404941d000e481012011006904844001d2806074107035112401014501641d208023001440008007240b8288a5101070000401d00419103250070030661900001207000f0180c440001e004060b0309903800a80e04040c0c01c0782c000c0141d40e403401140005e5140004c10320050500300340d00f000c0c004050740030a10b40d01400c002d840c14005045580100300c25240c040380c855a614844104020106a8516581e4085c040c01c0c18001070301c0031a462058280c070607015821694a000040c24044280780845140b8000c0040b810390358102201c10000a04540290441e6489400840d189030005420320039000200001010265a10903012915844503009158644910b181010b0061282814011210500071050010007c0803840d50103075010782110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 931307464 1250 931306214 931306237
    0x18060e0606090621010f0c0f08160906120213080313291608031302090a090804050120030d090605090601061407030516080405100302130308090607020d0809040c020a17 74
    0x244154180c03080f61f4030034866009481e03500c0403040581d1580c081c0c54000040c155400e0b02c110071114049803640304401c0c6041d40d21503e030202e0341c0410420024040c1c0601c014a00310b442c241c003c001844c0700c0000040c54015400784090030b0181d074a801c4114450608440011640b50782e82031619401c591030011700085080780740351600c2440b50b1302d5050040e0021919004000040340707551041d45020b01c0965804146001c1c107119195050b5a9021240120310840d410b10880c4034920228850b10340690352101308941c00c598403800b407614400c0207803603c0d500580c0c0039403914001c2102107102107051414bc0d02c0340d40300d014900390ba010107403241e548800720640c01c0100901610074052040c072000404940500c10140d221800d120401100580c00c08070082458810400c0e08420200e10481c0400c990700403440d540c492520a010030440d02c41e04400a51116504007aa010071203103102408410600360341c03c01c4030400301780c0140d0b503a201454010300080390291039481d90004030b40c0240b508020700e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 931308714 1250 931307464 931307471
    0x51905041a091e03091e060c0a060605010e12061b040807080d030c0504080d080a0608030d06060207090204080c09090705030f0a15050606120a18060e060609062101 72
    0x100710100000d2042c2c03085030164021510500300700d540b481c54441031840810156184c00c03404030010b04640c02c0290002c0402d010030b800006d0741d0f5079000a0300d0041d005101a20850602c501e407640007041d00e402090301103a0b0b40d0350601818180f0704003c62000d501000140819100c14160a01c00039882d01d0184c2c2c00407003080f0100b018082845080020409840103008154001001070240c0701058000c108114081c04208441c040001d480707001c15409007062101c1d615140642c4019003c41d42081c0c01070b10002078108020b09040e071010741110f41a40c03e5410039511030064100346d12581c85119031030b9000f40514140d910f014060b031a082002242112415540c40012a0070704404a0041000e074020307160503028414600c44092443d10200c2d02001203207400e41c0010000d001e141e8039141419826130010342c0d10b02403988030b205542c011240e0003011955515240b00a0031b81140031105600498010030303420304112401d1402802c0c01000350b10044a038945522641d002c203400c0220942d01c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 931309964 1250 931308714 931308743
    0x80a1109041401030c1d0c0307020a3f020d030b040b15070c05090f0403080603010609240801020406140d090614061207051c030e13020a09060305190504 67
    0x540c1d10980000e090310342601c2e8215032440c149213641c244070754006506079034218203400c50300c3e01e180314041d40b060790126416225290003500b01d01d480c01d1000b00912103a503540b00e010714000d08010310306820001c445000a400583c01000790100262070380140562f0081800c1c0071118065040400042000b80c00000c440c020640000e808018064a80d026110009a800c081c441810002809844152080e00403810308410f04001100e0061000c1c08202a0101150042d40c00303401200c000c080c60304003030000144040000c80d2000d681c01031109842e04154000503113800c18000e1794222207040e12a00105040158040e90590010240c4900195950301610000d041881420684402c813500c034041441c0c120244034400070400d030360704001c1c2d11404042095a443c0340109a130641c990780e1207580ae10301494161203c442c45a12140c0c8002500c0704000941301c0c43d40600f07035203501542d40b00b48240e924441603040301e8050721501503600826a20015440031900101d0f009842810341c8400303a02e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 931311214 1250 931309964 931309969
    0xe0a02030d090f090905063121020703050a020118091b17270a060603140c09010f0312090b0a020a2d110105070533040201080a1109 58
    0x220610000001c5000d4030000e100281a100300e550203482045020030180c5c00030b440d159900d000007084101c3c001c4034001c2e1101c2d01b99101f20410100408807611540300c22091501c0301130f03081c0c80a2616010107514078010001c1d4030025165044039000806040036114640044038a18a00f003d44d20348200e0803480000c40c0915480f580e50002041c018802840501d00d2000703100103030114450700011119024081415182d2324460000040118102c2c0700224001c50300b8141004407034082c2607240303000000010f22480002c0c0845484a0100740c41c401a110010004108001c0c0220100d10030100e0092001a40da400c108408204a0900149840d601c0780307880c100350301c40c0303907020010781020030000100080124078112041c0340c0440f02408146c0340c48078060074841150050202e041c601040a90360340100200d500550300132003075036482d4013000800c5405040305410816000c1e1302c08017488602400c602068004c0f17034141d640d405140c0f03683c0546005000c41807000c6c10710103410032181100e503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 931312464 1250 931311214 931311223
    0x80901030b0901150f0302030903090103050414033108100b06090901081c0201020408030f1606060b03150102060705120a06051201060314010513240911030d020d0807030e0a0203 78
    0xa01071310101401c4660000002014024068040d00a050040c030910848201c0401642c1d4103040078030740000e071583d5508020010074010451203880b03010000ea4801c03295055a0099590500c1c000c0c0c001d02060140729041e1050228820280c190700900103a40419019412000e00104020529400e05050000064404801781e2210f1501e40c41412a40204008a076912015650500085007080d00c3d11944649911a02c2e181c80d90052001a070000103041503015603070900d0b00002e0801005445006506280d401a507107450004215500c1c9003d9600c0020014072644243d40c50b40e060440880d129880c250014004148882e203425009c6415141c0034180b54650724164004561240340d400c1110381d0043d80c00c54100740340d0500b01000444641d8210387c404080d44500d4482d0144040c89080c0c080f800b030890303003405c0b0904001425041c011503090b2401548001c406461412107000c40690f600c884003040100498424000242c44034040c0e0f01151000b1504030540da040d0107298002801c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 931313714 1250 931312464 931312469
    0xc0306050c0912070f06120f020c03031f05010905040509010e010905060709080109020f10050d09050c1507031d010225080f0601030305190c06141918080901030b0901 73
    0x50180400c80c1e030100d2802407901404144140044c0c4030721030502c81031a1180319180216414001c4444411082d0f610690200f018041c4112045484020840b00a9100d0784140c5205030b0151001c030703038140055160070150b012158141c64803e01c2c1854082800064a0b00801d003c0c003a550300c80504002000a006010b0b44900c0342e4007500c007500d23000c9400f030107803c143c0c0c0005400da0702d8034008a0050702c2d03019600c1d6500904980125005a5411044a05100c3c414010010314100030010040020008038500700b10011600d02511160304080d01005004001e0003400065411240e000303455031400710ba104420042c415034034602e184860304c5681d0b090031501030030354404800302040242000e01c103004517580100b0103401d4a500d1074070002c2040c05082c0c4c99060042c00313010440c100c2401600000d0340c641d480081031102c481000c4e14032000761811580f81e070001c544480946e0313220508e446640ca00d80303000b440300d06101c00a511050869002074142a0501d5643c40005000f03903144c8000900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 931314964 1250 931313714 931313731
    0x30c0c080a020109170405031002030a0204150c0605280902040b040207080903010b060301321210110415080a180c06020f06060f040b0a05040c021005100806060d0c030605 75
    0x2144c2400f0700d08085075404078080b400e030308001440188102d17500810303014142021130201580741d82700c0b110703810000c0c41035078800c3e02c4400d000e03d4038480c2c1a4020b000300050a025030810486941c9485040c000300c200a50700340da900350103d0401c001081c19a00c1503c03014005000020251401008582260702881c0b05a941d0b94010900c411540303030074014030b011000280c4280741154900f070fa80c800c10002d484103810203600c911200b444c6000721148401c5a0300c400400c81035260034440400c54442c1082015001c00d1810303c804140174401c00421101280c4d0105500342c002200c03580c0440f86031102a255809650300c809402e01801204070b4002d80c80b034045d50040c4e60f114a0040064601502150700e407072160490401c00806a4820940c0002420300707a6020a001c0e0070b84000030032944564000b00d922918010245001075030010361082c0e80c42c8603581c00c10141c2c4031041d034809c007210203101e0f0303c05503404240040c1c418106030b07481c1c00c00385100d210841e01030340e12940c0f40d6080d10011a0b02c0103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 931316214 1250 931314964 931314971
    0x20a0510090b03151c08040509041a010324060e07050703050c0f160603050f0f04050109020405040c06090f080601170307141c03020c0a030e010c02040203090c01080705040b030601030c0c080a0201 86
    0x410514000d11707640002c481d11442034125000396600c1e480709000e1481614800c00000002406114150102190b003100d2410700349450368482c5060b110511402030070301440030f031002031000c284105102d540e090710201507080d100c80d51009001c980030351081c5011410044244440e42c10f10100b001444410142c0901030300d161440c04041e80c1403a0b91b10707400b08040500305800c3c440031100408400b80c00c00b04080030287c040da03450030a24050100e0340c6009410505e80420130080c40f001c0285482501d503a603a520030007070743d500c0c0030f01022a0140907142c0c20b5004500104000904d4030141400344454200303503424180b042e140e00c0e502204040407904240c00c469081c4110442616048500c190b09080860505140d501c0c11036444105803801000d2004112040e10f450b801106914855070740144155542c0c6820301c2c15a03121440c03210f00034041000040428a182d0040d42500c0c20303281c0d0030012508658403400110054050b002d062814800c2ca0003244020823040c2c0000c00a0b620b1640011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 931317464 1250 931316214 931316251
    0xd05060901140f06060a111b030105061e0405100513020c0105100303020d081f03060902120c010507060c230324010219060b0d0308160507020a0510090b03 68
    0x34252102e40002410369030048080142031440c503a0f8454100c0e41c162000c81d202c1c802145d06541d00c4490b160307404060310445030040310011480c4d4152400e264154003d104c613448400912507055000c001c0c400d0408106045849581460762100e684a0300d414980b0311050790b10000316120040090741c60128540025040d19039000c24001c864100e00d40703e400540309491914000d444000040d44241003001c0c01003c0b0740d81c054502015036418944111400001e41d03030b468800300402002204a00641690100481025000c00c210243c203806846407072411100c1d90f2180001c004410400050003149094000d01380707009242d840503103030005c1c65556070b170400035170104882150190320080d00051008031903140e68045400181e88132107040140e2454200d241c010007403c500581c0c0354001084003d45414954803c84150007800c940d128182c940034841003c9541e44600d981c06904202c03030b210f0401845c18a01103080c0a0380342c0e8601040e0b00c1c1e4654450a0480d801581c4c400305550060665 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 931318714 1250 931317464 931317481
    0xc0f0f03040636050705190801050f0c1902030f072d03050a14160b010315021911011503050706110f15130501020a02010c090e060901051002010603020d0506 69
    0x240c000320080689220038182c00a0041201c468002c0b18495a55003d4500b4104002003040751002400f0000c20844408a5400243c2d031700450340e1064110070340c00e0001080c3d9803000c100046000d8880207030054070300301c0948400e03252034803214131580452100300102c00d0303030303102440150008a10a280c40c000f86070b04881603000541c1030400581c035034400c400441001075000000c4407140b0b03000742403840c4504003400c81d00301c2c2400b80842d900410011a0704031700400035040041c9068030311400000c1c0001c44d240169108074041c1048414200c5103559070b00d0f40040c050f00004940009071000403c520315403419441c3c250003107034412102035106200900105400c511744c0503821341e40704000c01d4006420308150385d840e100103402c50022450003021540025140c0900c00005400000a40d50780c40001030090080c49141032820020ba0300782c90205901844451050003400000c01d4590340d41d080c41c0401c0204030a140550055650358040000140c0702d04e5445203403180204054030586c604903c9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 931319964 1250 931318714 931318721
    0xc0e0106020d1e0207050901030b0403020f06010b160618050105010302100e0102060f090c0904151104061707030b030a0602030f07020105130f0326090c01031109090c0f0f030406 78
    0x10000c0d908800c0300040e0030780e0f012140e408821221581c21540050b00002a820210307035410080d00070079100300110501c031041d2076013030043e4882e0b400c075500202c249050755240e031001e00564070380682c200080c48115040c101c000e40341038090140000d1402c15200460301c0c4a00340788044410341d458000400952800c1d00d00e0301e10070700403410302e800600d02c2280001c0d20340100510070002504c4210204090880420910f0460400076011010701d003003d0900320600350300d00003040d0419083c034079501b04484000e01968100c505c02c2e2141111900d401032461000c0c80c0003008442095070780d4106113038603a4100070187e02c241c05018010396a00b441c0c1d204a101203001058801503a0600041c070429445030030345017074455013010200c81440c8240c50100c0d40010720900070400e0000751003100740e43d0803500750024041ca840ca0111a02d03c0c00320380042d4245c07075545080d81104401803080010030b0809460300360740490a11030326881c041c41c98a503808241c000f9416619542004010001003045510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 931321214 1250 931319964 931319969
    0x50c0d0c0e090c0f0706021b0d091a2701020f1009030e0d02030622020402030114030c0d0c0b0d0f020d021b06090d0f1e081b0313110604120c0e01 64
    0x4907501d41004141368407500e00c40c0c07110080501307500150b4000c2c2c41c2c010024009a44640f0f20950f028000c20302d0b8000e02030400f40c02401080c46240000038042c0040c50304030303802003403e0b6134015440030000301b02d006503010000c0c9e058194007484600d482602c8007440884086000d10100082088039818020190031522000b2809610070403120805070341c00203074195204520305501511000400701001c10501c0a401c0203402c02d0011001040904d00e001c40d0302d8030180f080d0708980a4007020700c1001034851032808040c0004800ca1001d000e1013602d00b0040c04420b104680c046035058078010002d0880e88504000d18910394041646054000440241c1031b2400741070008240d2130130102900d94a03007611038054418000035640c8588054000c2d10220389600d4030701a229100c01c00c0c641d0180080c10129a6040252134500b4920100e0003440180d90242c420a094103810804070390f0b8803598a540d142110b42c1c000028000020004000105a203815202d0090401000d01e0140f0240040380181c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 931322464 1250 931321214 931321231
    0x906091703181b1507060e0c0405070216230a080c0906060f0d0f06030206070b071e0c02091806101d0903071b0801181109010e0a050c0d0c0e09 63
    0x4607101483c5806110a941c15100031103504004007507041c80f407941e07803103901c0009000a05002c4010091000854000c1c0209001d9500380f009540300d9008036251070420049948007100322000f0701904640500c0702c00b06445101c000303200248501d000501d444029030183c481e643c4001940e8040f800c1171002c80745c0280c42625440c1c01c02010001010f0940079460115020650780e0710001241c03912500040011034001e0405e69440b070342818075620003402120b107030001c40c0c030f82110148100501d01c206040000c03a5554000803012503400c10003e028068414003641c0702c1c481c4413007030100e001d00249000d904c01c3c80401e00041d03d0800b00c00442c0507010942031207440b00100b00181210040126682e259001c4601400601c2402c1c0c0e01070042965008440783d50b00c1d0408180030481c00c1e82d60207210600401001c1c00c0e2039000b604100d5100e03c24010046d655904074045036a01c041a005a074009880302d203c18107044840012000300c4482030704082c0000c1e00b81600b0701260034201c2540760010301740e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 931323714 1250 931322464 931322473
    0xa05031219080609010b090406091b0215011512090c120302060708010b030a1806020a2705031510030f0807030f0305060f0f0f041107140c030a0303090609170318 71
    0x83c000080c0754a50500c5500c20800d00003959000c0d65499502c648041c0032560030801540800840312000007200710204000b5208041d04145040385480c000c0c0e0482e8003031204030001200c41c2d101240e1b17030342448804030041a181c095050015148200210240910102c102c0480b10217040003803900310302038a12000e00c00884010700c6071161803400c803a031100200c1004941160f2000c206440001e08210141006102007600c1c01401e52085a40e200300307600c6c1310b480481c0301c4034a241744411411817140c81d40c10f900119000710140d80f0490000d034010b602981e00351800e80c1da03072038060440c80410703c100c800c0e1000140000c1051341110040400c03030603901e0204031604c0c4c01004619000e42254030384d2f103d00308012a0f0069030b92801418400400090700500100c40c140303410603680e070850300b800c0350891420000a0300400d80001d120580b00c000030010100c80801352425402041a40703019903505445800410100350740108080c800e146070920107a0f83e2401d844a0043e145031a5000c0003190070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 931324964 1250 931323714 931323721
    0x81b2d0109150801030b07020f01050a020c0111040e040303050402061b0d1e0f052b0603031b08040b0906040b18041503110405101a070309050126060a0503121908 71
    0x1403003d81c1c20b040d01c1d0710113180750a0303485040c0305918008440c03071150078035800c220406c810900c00390081e255440080000748005003120301150190b00407030007802d00f0f0f403d81c2c0d0002808030340301c0e80100d60024000340c589441d040800603001d002034291441c0340410784c0903103a150905030340b18240014100310660502e090040e0020018620380c8013011075420003102044141035403040038015084101d0000188060100940400c000352015100540c0854003114895400c3c011300a0119403460340301800c54646420041d8000c180c2d0002008190415024080464000c1c0c0e55802400083c0c0201d000900c3c9900c1241040b00342c2e0400340f10b01c808004007001c10070001d1044da4110711003107800ca602051541c0c131900542c1e4001c8055115001c0072502d0031801300039101c1c103001440d2140c000d030384411003962130344c0040d1420b07500072408040d4440c07007040b2000b1030030024600d10b030000030040281c1d58041d51500007034034090b2000222015a03400160103c180703540c0105036400307522141031503607040c40d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 931326214 1250 931324964 931324967
    0x100306030809150c01060611060606030c0a1b14060a061e0e0903090d030507030906030209101b02030d032f0a08090f240a0501081b2d010915 62
    0x1d02d003405000d055503400b00c12540b10103000341d03610049004001c111a03030303594000a0044030084040342050240901090700703401c20a040703074402c1881c0302c03885242c015414401c48205a0052460798031040c00d08403000011501820100720848000040095061020b8074101302e407035aa10400384d001d40c1c0c0d190007071241c036440000811510011540700b4035698200d50682584201a102a845100e10a1020415401c54040e0a46078000d5443c90302d815110002030b4124031804500301d60001240c03180c4c02d4070038030681d1424079502910030307040401c05065010a1034070841503a0180480e84070903050b0078400e4510801c0c08031002002d04020003040c200310901085c407c10341034a040000d0280004c6c08500c0402c41ca150380280c003422109011406026407241c80421a071082d021901080070580305400781c0510350581d00180301034140c071042c0b20301030f95400505601440c2c000120480e210815510380380220403402040340c180c0352103540400014900204d0760000302400014000084403513 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 931327464 1250 931326214 931326217
    0x6031b09061d0f030304060c151a0d020607060f060603140f010b0309150903070b0a0e07050402030a0e100207110901180c03090b04050c030c1507170f07050105061003060308 76
    0x35482291144400141c50020503e80741d901c21109403d88000640010043da2004403140424001d00c1081203c102c1604501c065500986031085040c15801600b002450b10b40a1205c41603c0100b485260643c40d540e0314095904d00e00d5400c00c4203540d44000c104058160040354950401c500a20aa81c0341a00b40407000d5003040c000c8a0500c01c010000450700d0508000d070b41180716000e46181018609049004d41c0c1e50320041007126851401c501003540104903005140c0351400010280070510305100c20b10000f50070080c0800c4200703446020004841c1e106111014101c1d214840c0966202250f0070005040007801c601c0a0051741c0d640010440340d00305110390303403003940420030100d0b0002d00b4590842c0a0101404042d00c55811282030200700207000402240b0030b0b20030350907039611070420000c014403151083c000d42100c01d03040040d1800a0181a00500030705401019141411000c110305829071b00800400c5569a542ba4240403251030190940a000c44031440e0500000b421503403080c00c0d6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 931328714 1250 931327464 931327487
    0x12050717011a16020604180b01090f061b030216171212160921051e0c0d0212160602010e0c010509010810170c0a05100c031107030b0106031b0906 64
    0x50f144088000d08540d030361421a00103001c1c18812003080c01c0b84030380a00040c9411035015001c6210403000280303c8036500303c2203044900b0751320b60f45501c10051091289944c6841d000310214010640a401244200315090b009048480300c3c00800c403110307a20540c03410440784032179801e4000c14800c038042c5414082c800d5600c02d040f8140740115030450003082d50086021780000010300b6940d110700826204502400404601410848844003541030b6460f4103565482d5080c1c05c0c0ea08010049480d90412110052803144007030a5503040f49036044426042440310142c513000f1585848007003100503424014403045640d6040a0f005100596001820a20034486158144502000010711a030990319401e4010146a0991114803a5030000f55440b029081052482189040ca001c529414611072032030306104182c480804c881c0c4d10b40c6041d42c0c0100d0894205d00c0d40c2c4034001010001604541d04140240360584000c100100d079400840f05031180d9000b107004100e56041d041200d21750101d580000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 931329964 1250 931328714 931328737
    0x50c041a01050d020c1005070e0111060136021b01050601020604030c150c0e01141201050d0f050f030d0615170903070c1e052e12050717011a 62
    0x6480c201c0d80701c1d50001e17005080c1044868000d0403030703005220070180c015510461003541c4660072020840010f5a501030010a4900268000030041c020708100c900c110000c040b1807105100710310035221001c8180c0700e402ca82114850340201d0340d40e01a086500f42d2041000c80c01d802070145103440300000b9074030b80c0010400f4041040301c2d810041480400090142d03400a100c1703040c0418040408050104c8003403d08c0c481c00542d507000c5601105c2c0783c10741543d107aa06480d1a203115079107040100701d0741804d42001600c03005071983c01900003800401050040340c610300301035900c8800910030001221001d078070680100403001d0744061540d600c820300f0a0403c54020305543d1985501c0b44440c6180294117000b000c1c407030316130004240300e2541d2848007a03c800780580140390588032001e00400c0e00307400101c40d0500d000158005822480e400844c400020146000031010002c41102c0060782c0080c1ca0110114002c03111005a03081c64000d0680581035554030300c540d90010b00c000303200b18401c00d8941709 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 931331214 1250 931329964 931329967
    0x1a030402091305061302010906030e06010b070c0e0411030606010e0d02090a060f09050a0f0b061902100f0c030b04230606040b0403033b010503100e070903050c041a0105 74
    0x90b091502099440032041e002011030708140380581c1da0140900c00410280d000c02c40f180000150b59219000c0d01e035481c4088406400c03142d10b0034080078001d41080c2e008403650b851681001c94a00130024140348114040d060862000c014101410700f46030000c0c00e410f040160500303415481d5240c0c0034118607a903030b042c0d407811000d60b94140c84400034210340e00700e4250184034500001c2d6640c401d40115000300501c40e800c01c246808003003040d00b201e03060b0381055000b2009100ba03c5040c444c04580079482c00c064015140742a08214800e412101c003101c0000000360f4403500c800a841d030502c6041c0307a52030140c90400c20401450300c1d4000000c02d4458404620317403001f00140040e01c410054030000e00c5045c1320340783c0303442c0c580c41d02906401c00004054040380c2a0040c5409540800181d00784a002d207140e141400146e4900443d01e59000414000c000303603858200140b494030030300549106101e25900d4152180c11407030414145020484414880c90528003081c1005540c3c0401c0007240c03100b424072a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 931332464 1250 931331214 931331221
    0xf1c0f05040309031b08011a18060a050d030e0d03171e0c0a020312040501050f0903040302060f280806150f04050103020a0219031706061801050c030405041b091a03040209 75
    0x2016007174079035084043c3c15420100c171528014910b04e00300c0725121007119100041c0789202c045440007101150b03255032190010f4002c109c1400c01c2d040841c0124081d00e4100d901c2c101c5080803500700b030784403101100040c1003002d600c903c2079181d000c05a00140b05074185284c18075a020081070802000e864901000b01c001100182076000304115003080c4030500e0040c4052400d414143d00904003101d204c81024043c6000481c00d10300401100e054039070007401c1e54201180c0303040001c8150017024071102c0041d0582c0407400c1ea051118131401d502810307a40c1d1905d1920300341c4180040c4c0140c949004820003424404045100e6114041e101910002c4c640140c80d10702007517040b460880c203c0c1c0c0302007a04141c2600a0145a400101c8076448803070782200c03000c1621350708140308a40c07058094554100c0386003912102c1b1b82d845000181005001001142e0410741c0702d4000504880012021400c42e203640011151040c1e0030040080c000e1034000001500070b810302d401012140300081c0024800c88880300003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 931333714 1250 931332464 931332503
    0xd030606053105030a080c12120a050417030a05070e01030c05180102012c06070f120b01120e060f010519121b150e09011a09060f1c0f0504030903 64
    0x2c01040300130b045885602071400c00c804158000c04443c135180c050b6040e001c0e0f4074581401250400400c00560a0702a40c4580c250b070018000540704644901d500f071503101c06030301400b010314020f0b420a030340040c0d141801180071340000020240c29041c0760130000c250b20050342000507103905603000030000c0ba0707580400004030300500110005991124000192181441d10882000042000e19040b111151102e68041e180d4207a001d61050008170321308034151003044103400818907144e06041010a5490818082090302c412a1000340c09034880000c2115844000c0d03409401014151403460301e844002502c07a4142c000c9000e0084111021451403081040c031810034513105111080c2c10100c1510742410360050440c14001c0d100144543d000e912862030302e9512a8102c030812030405034107040c030444440840d04000c900d40c2e0701c0203050060302043c4041c1002080c0300d204118800c408004040308600c210b8003c5c07000001003a180c0010000041d0b00308000f0012307a60000c607425000602c5140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 931334964 1250 931333714 931333807
    0x10c0501140405031801050403020901050f0114030a09030801152a061d010507091401200a110901121703060d062d1103010e04031b050d03060605 64
    0x50741020818540108000e201001c030243c00c50306150861042c4101c2c0e05c2004503005c1c0154003002c0e6201600c10300400c02850701809003004a88181001d88554140d84100310345070b082200e540c44803035211480d00040542c490700250140131741c094100e500e550707130031002087c40e103080c0050000b0000903100c5c02004108052201c071910383c07120052140c4144812616410151440e514035590700386070120301100d00420428040c1c6280d024100070151050700110395019505212040c02403520341c500f10b5115040c4403001202d8011110005030510107414031881500c141d0000e1f0103a84a500380703200142c0002a00d8200c12144080e2a45a41301c007000604100311000f002402c0c4d81c0361080317003209041004c0803250140c100003990000c05812160383d0341950f00c0182040155407040006124110b9a0b41c07810b034000e8024a01444c400d01c16190300c0501203143c10007a501907104460309200b45d607060080c04081e1100e46015420003120b42425010f41c0488180401080d040045804c1017541501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 931336214 1250 931334964 931334981
    0x19021203041e0803071e0c1505131b0501090510050901030b060c0a0318060c11060f120411030c06190c05031c0e070803040605252009090607020a02010c0501 69
    0x1c40d141d4a0802e5000500050158240f071407000c1c00505542444600900117944000e40041235040f002e94003080500042400030540b190a1250b02403207400b049140c0c505400800000040314400c90401c00003501c0c2c01d120341e10543c4251649940018000d50080c10b031501d192081c00c0200300125043d0019001d40103a0f9481d07000740c403a04841e14180750b070001401381c1400c5203480e00c0300c0150711791004a413181580705000c3c24503e020100c01c5800d040000080c50306205050042d0300304040e1280c5043c0311a401e80301034411005880788011103140901c60040380134011540d851801c40c20741d102150030306140b251481840010805503050003001c1c07088481200300280c000815902e1412600014440ba101ca0003aa12501002143c0403600204980c01d98031240c07101400e080d05d2603248480e82c05891500141018522440700000303110140c08a0007284005003d080d264001085c4114042c0052820794950720000500ca4203c0c0c001c101130304201e80a00e031140829000f0b050990251000c070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 931337464 1250 931336214 931336223
    0x30709030803090c041d0d11071d010e0a0501140f0114130f08070819150f1a030715110a021203030601020601090e0601090c1106070519021203041e 65
    0x108540c6990119202a5511048a0401217403400301980e1139002c949403a00c00c0c3c2035000e10112088036010f00034188c464402032044416094454002c14419807000d01000070744405203005200e4101c6a044d41503000c100c1c2001000190302d410290080d00c060039403000e01404503044e15001991050032025000e1a030750301200c5d5502140e110038a4107010500c1780d0180c40070b09420100f14540041884812201c03c50000c15146043c0d81c00601c1d802d401003002c445401d040c142c80a598001d6010301f01441244c440e00040e98841104190101c01041c044144250401c0e5001d10070b42d0903a0040d0324403c0b11a01d0f000184034604a9901d10f030060108003c2e6004030011000ca8140a000006502c81c0074282d095032100d9907507010328002d1302d00c40080c0d401c46811840040c00700503101e40c0002d17022901417a16080f82052141d5103070520750103079510340005d100050608106141c0800390b0700c0d8852070f48010b10b11140094424190b900000d0b000a201402c40d0301c2404030b001c0c40c1a1034140765030f000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 931338714 1250 931337464 931337467
    0xf0702060d0608061603110901080c0d0c12110705070605030c13081c0207060c03080a0204180b0f0a080601030209040602090303030f0a05070f1e1e030e010b0a12080307090308 77
    0x50341c0c4515a03030070702101e1044000c034800903610a010f01c240900c915070820612108d05000c0c00304e0041d55106401802004960340034011449021280d029004003084161103000c0c0b0781000400300d10a4407002c0e103425003208010003485000420001c1d444089821a00d0310b2a160745480079559811b100c1c0011000011120880c08103500401088071402100381400790051a0402481a61240700b00c0c031459000c102118406e4001c24041c2c4003d03940080110001440c2540b1414205051b80901c03642c805003e03a0b50146c42c6c5036003030440d21b250900f501210001c401915010881c0c0d565041404000e004183c10004103040000640650300c03041e00040540c0d07160314120720716074502c401c110744041406042c440030503595030048a280045296660310090300420b243c44442000d070f8a1540c3c8010090320540b00c05000000403c020580c60070303642c000c6210300d19218424250f0710103260040c130902c1903e0f010401044413028001c01650f01448840d01d0b5038031036000b0b0769a9070f815032028083da0710 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 931339964 1250 931338714 931338719
    0x30501060f050a0b030a05040501140a0b120616030914060f040c09180b041103010501151701080a15150b041d063307080426030f0702060d06 62
    0x101904144103a808070400c0c6091141e840081060601c40b038400c1650080041010404621082d04450f9000e402640080b803c8282044c0c2801c4400003202c03555859550341900e00020728000b580144a40240d10003403115017000100d00304000f410a45c40810b055079011101c00304001c2d20504806550004180e030041d2134420700402800000300c07801c444052408601090945441c0f14983c46c0a0041707030308818603052686c603c2c403280005401035a60f65030300c010550311079409014150180030f846001009410040380050a0300c0340c0c200c0070346034070115400188400c5100041c000086134108013036002d204000c141660040c003414110700403c4802040204581c03054100a00c2260981c0007094003404c90b40410084900003030381c200b60300641d5285610b54000032341540d500c80e07010304007155101d06130a000a1410754810001240c01c0140031804001c515101341d6100861b01040003a1000c59807400d030610b4a9200d45d400c08046a070001c0380e080f065445045c1941c0ca854246082000140e8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 931341214 1250 931339964 931339973
    0x506010e070206100e0a1d01110c01290d140706080612030726090303071514070e010c1113060e01080a0c140402220303030c1103070b0601110703 64
    0x640c00c462160140c41004041010810109640c80442c0d90f40740003548035850b07002450b000b0b08000302242c180c5140e400c0c00000030381c0080c807a5000d880c2c1c20290a0f566194484110f50a65420320a000740c1111a0007904030707240114000764038240c600310380c500c6070003069290821801c5000c48146032180306151000c0f550580005070f003030050760102c52040545120302c00240c3d0f40d00c01d07468010f0010001c4e51017102080b004042d031140c550101c22000d0304184030310000c24516000044103681c6d0001d4020042c8541d80d49201d800124200c00c601c075100c1d07142119014080c02460042c80c1d04010101d500d40051054000030300c4283c1c41c0c000e10003000030020303c440034086c0160380940b840c00211040001182c0d84005420080c3c0c0740e00505d140401440c0980c0c0e0120380029a1190380c020ba001c000107244951071407080041d541000d00341c1d507129401e5080040844e10030b43c0c040c4083c001c0000344110384400000554202e6540079004140d82c4c0d48070b40c0102c1d008800c00400d1b903014441e004000c000c11 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 931342464 1250 931341214 931341239
    0x142a040f0303080a06060512090c181905040c060503090c040903020607020d03020a0c0212070306060b0318060f040b06030a02090705041d0105010c0b0735070c20010903050601 77
    0x101e00950300d2100302d413100e10340002280c9043c030448012600402c107000d503041105a40541c01411507080c3c035030000203040440c141e407960b0310b141a000341c034020400020141542d40740e08031401e000001c01c00c034981981c441041c4840d0303001e400c0510001100140020800700415101c4450140050000320745514010750355440c02d807011000b500904440142c000e10070300c02e50352100c415075980744280c4040e03008d000841c03100d03620110b84c90041141c04000715a25004420003082d10140f25580e070310703040d100101d0201c1401c40d4112550000000e000380d41401901e91500030750032507031340d0442d9128140020718101c0c00b40002500180020200210aa00304004d4001c640c12101042c41522142680d0001c0c2242400750703501003131048405401142d9420440b50f4420300070300b4050400c3c1306142000000c00140140706001d60110000e940f42c55425401c4030382c100f00c090a20027a40c0c41d0940c0c81c941000784160000340e059040d044c0d0020710741c1c840c0b81018001d613008019546656141e400d03110f40d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 931343714 1250 931342464 931342469
    0x5150304060e1513020301090804060c1a0105030601170c030a390e0717010308040f0b09010909020d021c020a0e0105030412030b0d02040c030b01020c04142a040f 71
    0x3503918040b0000001180400c6009184000c05880d90440d540d5852952030307403d80c420180d03010365959516800284c0654028006821a07884031b5048040c24940507038251054200c0c144204c010750300410068400142650644215541c00c50718080c06801380c43c0380080d00e030741c0350b40c0c148140d074151424481d010607042082c0c4480443c1003050301d014441500c8039459200e02d0203240c6494102080440014404203801c404640381c18014a4000b007404144080207804c00d071815000003070104007048042c10008010300480021a007850310780c00002c1c02001c00d6100d0a6205500000e80700c40b501c0380342c2d0460b0001c01c082c1c049440b05489440090b0f0080d008045000702149805402c00003031341c05102074030b10a5074022069414500040d004031301400ca42d0660b00e402041210100b00103a489002d601d008000e10b540003e03080300b54500080c41c00d04400c004502036807070034810001403c4801c1e0070430341c00503a06070049000c001c2da1000036014143d21000405c14400810040303030740220f0304c00d100308 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 931344964 1250 931343714 931343723
    0x601110d0f1b020901182c010510051f051614011d030319060e1f0509090a08160f1b0801021201060309030c080c010f050a0207111905150304 62
    0x25034800d5007800d03074460b829504002c1e5114090b0710040144409800741c0b185c255194440100e40c8851103000707044c1c05040341a40740c00c01131a000300740031903000c24032031198004001d001500c1c05601d400b01040f251030312000c9410725085488100d07441c06004008803335407800a201069410303112410650031264210000b000c5550800c103401e1402c0024442c035960402c010300c0507610756152400e00d011001644d0801002c1661106000600b000d10458118440c901d000c840c10800c00c00714030340e4190100f0980080b40310303070078001c00c2c010800c40006010036165403100b00142d0300c0d00d6110300f6041e14140707224020400070800e01c1c00c00c1002415824000006200c1c0b2003545c0302912000c0c658245d00441020018000f0043d0040208621981094603040d002c1d0400c1e07920100c986c2c44c5c0030703140c1c4c5c0715a00038905607440340364040b400c858907c14541c0c090740b40e11045082035280d503a04800c4109803064584034500e00180000071180c103400007401403100500131001c03d450001c0107591600103e5042e507 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 931346214 1250 931344964 931344977
    0x31b0c0203120403120810091803030b01020d0504170709060603060e0709031a040819030b150405090103060b01140705010605100e03070b030a091a040b0c1206090601110d0f 76
    0x40b07100003a054809603940044402d0f0601030000342210104001850882107800c199000100300c0e0241c0301d83d160051119200d01d64507082810003a040d070b27006c0c1002030b04650215480e00d419980c000c00381d40594019158200c900c1d00f80e28003481c900075a5800c9006814605000096000e4041c0c0c0110100c03414544143c41a98a19006403650103081c40098005c1160290041c501e05409001c158080c3c030070702503103081c01003403d648030147c0344030074465000c01e55400344c074200d0345003401c03408007100c131580b400c0344c030306810240480c01040062000918042e02e4480d503080b00c4c0e0081c1d000240307a00d220540984c4030b65450030300c0c0d800782103c2c0c85071600800c01d40c00c400315041d01c00c800301448250050b008044d010b150140c640c90540c0000c02c071403212591031034600700007010407603820302c5442070380c514111908040c2400c80d11043e006d0000346040c80d0822040b03c0e840b40c0f03880d00e10351054048450420310b035201001030341c0d9144074038126109400740034035404110360400720131a559011540c1d0360 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 931347464 1250 931346214 931346233
    0x1110c06010b0a02060402040f1b090302030c12150a0b0d0f03030c030501080d110c2107050619030b01020328030e0c060d0b040621060b0a120201050307031b0c0203 72
    0x2c143c1c0f00c0c5032802001038000d4400a009800c0581000354245407040b800904000c86e94000405081c140320003a0004440c0b031820419031401300400c480049040321124018501021959500e0004654818682603507600082c1c88084a6106038002c2101400d07840b1903075424030f004240800032010441c0031900e8400240d940384d10921403d41601c074880c006140c50180882c040d039007d1a10380f20745e82c0a01c51000c9224080d100d04151705804801c1d0b9100c4850000e903500400d00341006500218041e180c02e01c4155580c41c1d12031079102e000591030a000900428641c0100c0c1184520b00c100e560940051928090100c0918080002040030340da0800c2501400d40906841c4d150302203003154050700510520000407140e40c40303000700c0f40c5d00071b00004400740d035803c044180000c3c802c460700458404042e43e070300b0301919000e018510503080b21080002810310668103481c1001c00c1002e810400e011000803c094001d44c050344031317010f0b2301c0a5100c400b291050010000444001c0c01c81c000e020701c8038a07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 931348714 1250 931347464 931347479
    0x9010f0510060507050c22140f280219080f1b0f04261902150a0507061401141e0415030b0408270f010e06040801110c0601 54
    0x1440c1c060182480300180061900004444503080400c09441c140911709004106903a1214210840304800c81482540c42c4503e00c41c0c41121069240c5141c441440c0080008e603016061010f6488403101544654016605002c01490284101c0b404940e5100040b0742e0800e84049100c10303400350441c0e45402040c1d8038164111490f40080d5848080f02c3d9000201c640b04419440140c0001500301c444a800d1645d14046607140502c0c2044a030701d8520154001411540240078172168180580b450266500c840d601007100012802542000310102142c0714040c240304100319580746400081c1800100f03a894a1805208000e2040a12401d0140c810000c2c5040ca1920005030803400b404a61081c14481c0034030020340141e4440354000c16035400c0110001e5240742d445e0740100d0080503510344075200d0340c0300014029204031803015007800c0540360300c1c01540c6021404040302021700e81000034944850209207580141e80050555508003010a01c1521030000604102106c1100b2a605640d0f94103d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 931349964 1250 931348714 931348721
    0x1e2c0a02030a0816050709020309120a0f030209010903230d0f050d09050a020d0308150a03050a0204090221030d0b040612080f1c0203070f18030611040f0e09010f 71
    0x20000d4054202400060106003540050055600e5004954007819029a202030501300d490704000702450307000c4140306100b0000c00c0348641000f6200421407803d580200e002d000c180c0c00310030f5807080540004103040300340d11a034050002581d1220042d00c1070240f18004e626040c00282562420380b2540108402180c40744d003210000f04400d49880f8501405803580c90b024108940d4180c40f14030070b03214283d006071584100c5881d13190007035071014a6800c107962107510b184c100280700780c8240506d22061000c12400f0400d8080154102c074000b82c0f50707000d440410b1410006419411640c20400304401480303c000c0001d110a008071071042002100e840300b000120740a500030740000c0b04c6101107a200240850008040902c1401e540341d0800d04201103078509401c880124400154001c004d100303919401c210070b1280001c181c10410021505154101c00c58600c502c80034159a403200050780444419808031005001c44d00c00c2054500c2c0c0301d04801d000755400b80c0311298a03610f0802c482c01d56140a10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 931351214 1250 931349964 931349983
    0x406020405151231020d1202070614120f0901061a0a0305011e0e040f1e020f03060108100c090e01030609020111120f07051006030b100b1c1e2c 63
    0x110140d40d041540c0070000c0310445542c2260026205e04400c0c000c590000387d4040622150382c0200f00d80ba0400390000e00c3c03c10708002d4000e008505001042d1204440010135070f00822910420103140c3d5060304c0c00303000d000c040d40310010307462014022902d85020354000f4600c000035a202802980d81c2d4008204055169160340038140c14601000d0103020802c50000b9003150082604c0e04541e01140c82e8040c410201000c0c600c07440e22241511411801c0007440811654412401f40010b589000d002c540c0b24605182c031442010354a10446201c103002e451307810082c09801e60440101d40c2c4910f0074000805580109034045495040500c44507803001800180103400840c2d224100701c500c920800c03164100312000c0f43d9601482d4001d100d10032083c8100300056000d02400c2c1124103040c103802c807401007141c03c5040380c14410840b003000700819078000051500790910018510200c1080b0034010203070342c51400516424260700c480f8a0701e540341c6504000407407041c01c0700802513000c1e54654405144 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 931352464 1250 931351214 931351261
    0x50a03080915040b130e06040e0c010305130516050118060c0210090801021812010212010b0d060e07020d0f03060608071101020c0f1f060503060c0304060204051512 72
    0x40000d503509050688040e41c0002e02d41c1c0c061410192245402d07900c40c0c202c0d0700c42c0c80220011140c1004088605a1140d4110109a40410003800f48842554036900304086250506031981c02250118411003410060366400c02c4c265688542400c102c0340c9211283d1242d10f00040c4800d01d181200100c20980700d045403000d494184d400b140f15820f2145101206c0c100750140315004c040001e10250070b000030310740500c00f01005210444110100480321401d242d040390583c0c410b104404070881d0070040e09054815202c1c00740d448560294450018101540240d103841e0080c2040c84441a00000c00c900b02c100e0319103e072440421481000c80c1210200c4c4a4400022030000114103214014204002640311000015140003962641103241029050290405901c54001010100c2043c041c1050b911100c00303003440018504030000c0e030354120181c031500090301300101050800c01039038115801888050012404202500421803194226183c1484540c0d480b030005040ca81000c1c103400001c2800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 931353714 1250 931352464 931352467
    0x906020703060f06050a0803070c0b0c070e180102070309080628050a06080f030405010305060d0b1f0305120a0f030501051302090d17041e0501081618080303070207050a0308 76
    0x1c5407039440141c4040900f95401603035514002c211901c68484041c00b400b400341c0216900c500500e03001d084044a07a00c0190100c0c401e000c0f076400b01c58080b8003201290b03800b8985100c5511260a07841501803c3c4025000e19031001510108164000e0300000c100d0b18600700f070b50a160744406001404000181203286109484040b002144501e41c0c800394020400d0040001c0850325014214a0328052030b0b0882c407a54400b003000c0001c0e43c2d2500a141e4000f81c152145c10b4450803943e02d080344107202400c2c0d0485604103010305600300007902d2540c3c5c000c5801204542c3c0811001d51030030340c0b40d0700c00340d2000e0000d40030641450f00c5a0090250504070354020741050002009044200020f400840546611485000340403022402d81204009800e45060700303d552a444d0800360044c1d1180201004070740e202060080202c1d0784c210405a500c0102c2c1210080c0111004c039080300d51010100007901c0504054a010a00040003c0035611540e03ca0b000c645001e6228030400413856420320006014450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 931354964 1250 931353714 931353719
    0x100201090f03110a0f1524060f11060a020d0b0409020d24110417150f061c03030902130e071703120702010c1202070f02040902010e061c0b0109060207 66
    0xc2a00d0b4241c3c8049400b0980d903059541e640c81d803803419100d52040e40c112608603865034a403a0b00344600c5d40c401000c0d000e20003911610b03d0405d0001d000610400040c03000203103034107000901807180c003120140d044058905914040035031034000c0d0449010061011b00d880860b80301c9050501ca0060300a40040c0904266142580c403001c8044d11807180110046510070148440c3c84079009901170f41c0c07800c5500640740c505020704c6c0c48605164040c400400c1d842642c9402c40072210605c0140c02550305087c0003c4d0356580d1001c500c0341a185200210282c0116905100b03143e450b50104000c40e100302c0e036200200340070b03465a0b0103485665026640039000100c041050843d00400c103208a0310140a581c10594000003a0500103011181c60300943d445a040c0c1c1550380c2c1c00741d21004000b0441c141181000d070b2079141c0250000100000a00035645c0b007111206680c041c0300c503840074001c01441c05545216910000c11845102a111140ca07418042650f81070346c0109081030945004d603004015451 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 931356214 1250 931354964 931354967
    0xb1210120809150c0d0e03060718090506030717150c090102070b1303230f070e0103030c050c04060902070c0503070302090c1b0601240906050d0c0e0a1202100201090f03 74
    0x1070144043d0a0000c80c104036015140b5820704c00010761406a445545464112200741410508000c1262003045010411951013402c41c000e1941550908600000c0580e50100441d00e031006a401020b42c0c2211494a610640000200c5041d402410301524186440b10406001d0360301030801e0f0203015821601c4284424583c2001805c4000e0001035000d11042d92500c41c1d040401440076806031414660801d4455400d0801012070980c40410041103000d107082c145517000c0c1c20601000f400c210303040466000b8044101300d00c0c4503020005100b04a00c48d50768440c00001c0d448284200c408140c2d120b4005003d1030042610811a0340141c051040c0303594200030003205078807010001500410854182c01c0c1c07460108245c0f8003030003030413080c6826a4000220345820141d40704030082001038440c41070200640c0402a5515129460000b040ca180980303020340310102c40301c00c566081988004c0001c2d18001d48620703503441b40d00944580e21803200e450303c200d09851000c0005040c03409810304450009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 931357464 1250 931356214 931356229
    0x120a050a090e040b09060c04051005031e0c0a14070f0b091006081b040b10120612060b040b0108240105040e090721020d1b0b1210120809 60
    0x240064942005400c0d100e03035525000341c00c01c2d1801d482019140e810172201c86001c01240e074208420804580c100f0786401c00040c0c0544000030310008008001c40411059151207161081c1000095480310051410403100c030a00d4120303a003e01e00043e803954441c11000c0700a001c94034a0b542003100801d071550292900e03245401c010b045900144581c2c075015540d40110322604000d416810003811810483d142c040c5030300729a100409200d94502800c0c921240e45041c01c00c0f04060300e60a0000040e81d100000100030100da60001d84540b044510200c2003000d584e00c5105415004c540402810b61030500440744424120f44002d401e1000800096071856282569514424149042450b141d00c5164001d6410029102c0c1810387d80020000c1c031000700c41143c034201c84c01044036404005101e40d0001454040300003c06484000c5005010303130700d0804800700c440a0210054640d9440c012102e541c280004211404480003000c0740d804034100f503500300c903610030303941181819040011610401c07511 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 931358714 1250 931357464 931357477
    0x7020d0b37020c0c030706020601030b01050906030309040b010504051918060828300e01021f0b0303031e070302040f03020603060a05041b1112071e080d06090b0102120a05 75
    0x3d82c0700b091103800103503800f00101006400c16a014144a516501e42020001c0b010303040345100c3c01c8101704016040e2800001e41e061110b0031200429800300c400b005032007070f120755041182c0240d00c9015001034031b1120150901100d1103221240030340d1410450340001c6030320b44d0140080c079400c5200b074007400b03942603c13035080d40e40c03042c0c080c00340300e04507640d1140c0000c502554904549a811003034a441c1405810444122540a087c0300c0740c034480c0d41000031f44a264141c502a04020050001100c0c0c40450340400b030b40b000050300301da0350b03418150f018000c400d031006400707016803407480b0008010610900946007280c041e12a8112450306603401c100305504010262904105405000103241e40d4074040d00e240d40c503100e076a425880d540310000900d8251401075060a5501940e2400f40d4840e44104446a903a0840b00174100188451041e581c1807002607009808440302007181c000191140c0d114000b2118003840400c0000c00d0403006903154181c4040700b001881060191a2056002e03030010610b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 931359964 1250 931358714 931358737
    0xf0512120c090a180f060e09010c030b0f0103020c0118050115060f090501050307021c05041d040b0c0f0c0109031205090d0206010315091a07090e010b0d09060207020d0b3702 76
    0x6800c000f50000c50100d80187d84554001c3c4100310a00c80030400a1080c40300000c1a03140a00640d0f00355000705100110050a06041590019180e4420103003075000c041c56260300c5024040070505400c000d40a4940c4a241c0545158800340000c3d5250244000f04c861000a8031400320283c646070040d07a01e504001c0840055009403158091350010211610184080b2900d6440c0c0320f80c01c2020780e405501c1400701007c1004155030501003c07407007829409030310800484541e60f982070705000700c0319203019a8118800350342c02c20141508041d0450889901107111110030000d5595004001d5543c200d03100d4903a015820080060010403200f450110081c24585008210700c5550b559410400380800d0845000f040c0c04001d0008266201001500500040c15002025410541d02e80f02521030381031210210b42e502c9507404200140758050b40c01694000b4102c1010723108a0500a04440c02166080c0b840300740d20b0381442011181201002a00855819010300d00b043c21550030000c0d440708030081d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 931361214 1250 931359964 931359971
    0x8010317070506040c030501050c0a09090e03090a140906100f08040611070f06060b0304020102072304050903030402130c0504050d0c0521010c02010c08060d0f0512120c090a18 77
    0x8010402c01c01a507402a4030402c00308101600e14100b090071030380050441f4130803100c200000303e842c3d40d01409010036a15a90300000392440c950f016149548a414145038001359004000100180d41441404020301c007940d844015580d000e0410600302c10340740340040484c6c031200340c03503420510401c501075015224550008114541c1e0f00d1607105d60b04591003c03a603101480854400300050707402240c00515580c80040d0840c20a80e0010307465502c1c038003e4044070b880418002c4803030b40c460713641217080d141d028004001e50700309841c800d41c580c3e104a07030690064208900e5134100035414440c07072140c1c0703940b07541d16400c1a003440c3c2004405124141c040c0c450440440c0c001c54995a0004a2011028900d00b2445e000441030000383c00e44e02d400807040c055914001c0240076064104845c0d03544502c0464500140414503d448407200d090250003a00e14420740b03d010099000601c001d1a0407411546603503074581e03640102c801c680c410030f03100d41c0c2c1003803c0f202c04100d04500141b104a03040c0c039030800072 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 931362464 1250 931361214 931361227
    0x513150603060f0f0609090c0501050c21070b130201120c0c0204020c0d180e010311011101061509120f03080405030c010c09152f0109050102072a0608010317 69
    0x240c242d800a03007041003559600c401501c104c03030052080340002c140180c020b01c0001105d071a665081d681e14807485040c000c0c0040c0310844c51030188503003440e15201c14404001c03082c0043c601c03c0150800b43d003ca4041c004600840c150f400118a00310480c0c0d816034460075403141250b01880076120411041061040c06509500140d6580c000b0b001180490402030881003403e400041001107109132840303104402032400c4c000d2001c003083c1d06040d48e40080d898804071010700d004031030050074030380c03a8600c44d441c081c404620581c5880b0b00c0320061246a642e240d18640b54800d0320703034441e140b04000307000c00d009440300d40c00203010703002e00d41c0d119004900341c0e4200781d0480f1076076003524a1208200c1c0000c180c0001440903001e004070a0403a2a26860103400316609511000310f00744c00158440c0e1100f480c5a91380c08a00c9003500102d00c0e40354010029510782c1043d142c01c50700c840c0400c9a26101c1840019130720b01588501a28804440c0c2c103a07242c40f1640d01c2c684032610040000845022400401c1045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 931363714 1250 931362464 931362473
    0x7032d03020906070c09141e060103020304020a12060c020607020d0e3304050102060124030e0c13050109180f0312060321030c0e0a0303111606020a030e040513150603 73
    0x45c0d001411a0000468041d03c070441844051800502d16083c1341d560003000503015840d80740117a03105c9007e00780140d4030f0311a4000656004c07050760000070041250040042000303420f400c401682c0e40d2503021101c061300d48640036615800803d24083c0042d403000c000101d030b86030104c000c1c814001412081070101e010400260000030341080813900008000900f00716a503810401240140116505500c480300f0321300d113800464201510039001c05445074525100b428080c80b07240f031380c000001c2261480c0a400500407018000034825203210307034a07154032004420040f000c010100d0745c2c85249244021100c2d68140c032034a61814100c40544e5580501200041c103614401c3c9051700e03400000f003081c8100c1d40008080d20380c40f0441104200590222080342e031502d030642c0054aa043c18800c05822860250501d080c401d5005800301820f4a03400007061500450810360007030082e0354041065070f0580038071041d15002d450703021720342e86504241d01c046041203500078145801c2520101d08941d5940790b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 931364964 1250 931363714 931363733
    0x22120b1f03080a1713080a03111c0605030d0507260a1710030206161104020a030504021c110609040f050103111201110a08190e0307032d0302090607 65
    0x4440b074110009464072495006018a07040c8046072404400628000310703264140140650010684a000b0a4949141c0c1c06500f103c004106144001c0382c075402e80c0300e00b490a00055981400700a03182c50350105082c1130100e6500050340c00c0e44c48007031400d070342591a842c1341100e50001e01c2040031001110103e980d1081e00030b015404080d0f8030f000180780032400801c030403000070305015424184280c0810050720f8060070707589122980070320149941700a0a0090b443c0d0362681c41c40303511a00c0080c1a80034540c0551029003e980207503890101000c44050321044281c254070040d0008101145080c3c1f24501600140407a51000d0004115480280200d0007901e00a0f00300315946000c90f0741e00002418000c102281640c0444c0081c044800c0c800c14200052060348212801c00c40004002542c1200c01c4180281000601c0c0c0c0130000d0f80601030204e510b94100c800c041b000101c0700740c0b0b4110b1000408800803860320003001d00800c081254901580254070801c01103812200a018440104d0b00400e0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 931366214 1250 931364964 931364969
    0x8030424090525050909071a0f0426030309100e070e0408160203070b04050f0906011d0a0801020a050706150f061103071722120b1f 58
    0x501118500304080120280c1590050304200324074a800e9031030300031800010b0745004800c804205000d0b5081d80c078001c002181e140e500f000341c0049a010a10a1000c000501c07038048611030140200d0100144084030000d200e11221003c0b00340090100748501c0c1103040e00900815a4031007007040040080074030a0440d00b04945500140c0c0010114801c00100c6004280d9805841009061140d003004a0782e241c884000d04003a0444c400840c0342114a105400d441c204180c00a0450701c4042d0b40f0000440c07a0340c070600801c0e004000f40d0180e2001d500302903403a9801b824058543d402003001c8080c105004402e01d01c0c055600c195029800a040e00c0c1c00e03c001d1040c00c08544da0a95118110300701071041d03400c0a8400c103001e0071000000c0055070b28024050068a10700c1c54075004a01c000511285580030381d240140404000a20350b03074040b20450014048807020945207260b002440780d280042040610900e4074070070000b0215400501d15002e0303558003404580505440d038034400c0100801d00120b4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 931367464 1250 931366214 931366223
    0x60e0a03020f07060c14190804080c0105031005040b03390d030503010b03092404030e0901030c050d080c061302031e0c01140702130510080f0318010903080304 70
    0x81a10005060381440445070300d18840d001002d0315071912100400a5010903c090000010151410307045807007804000c030100c4107145004c5141141d0b045c6040c00740d0161003120b103d8410103050701074650107401501e204c0c4494001c150400d40c5008140f0018100244040303a05008000d0301c0015038000718004491007640c1550b499601100c1e00c54254074801d003000322882607440aa9002c0020740c0902200c0c1900c06480b0029103136210f0f99103542c07034507005000c04440380034008170351401041c0540c4001d00c642d000c1d40e44d6000030700204040c000108001e0001805440844009100381c0c20328800050304503100300c550a04d003003186032907507003800029a40100c541c03002d0162141507140030021b1044515100d40514609001d000c9041da9540f0307045d4a060501540c090250124050031061700c1c48150003a00450414128441010007000f046844401e800b281c00f00105034840b0002e034540d591001d1070011480c02001100050382c214415695504024848402100042d440406113000b1480b4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 931368714 1250 931367464 931367473
    0x130f0507030c03050c1605120f090a270c0e210105180a02132a030c090501050f0d060f090e0d1e1d04060b130506090612060d060e 57
    0x300800070107546110400100705030400062041680842040743c3c0c00ca451001d462002c1c0320580380c0507040050042003c0300f03005c4e0100307013a5406440c4100404804d00b04a0b41100c050f40c80350200484c614010300c071901c1d044001041f01d440300c04154007007120042d041c2888076914800d03d0000c5c150021031580036040d201403e5990007518000d00407942c000d03100c049040c01000c01d00c0c1c506681c40c40001c8003c1e1050500d100c1c2c1c0044070039194895049600008212114010303c881c01d08e0240c00c0b00d80a20000a191084150074070b40309003060816200142c0d555842c218290800081300d0300300b1805103030b515036a06030000f100807503a0103020041010010114160502480c810309007846454503c0a100c50300000644407001480e04501056090030700002035440d0340e400e280a0200c4030425a085032a00b80045060403030782d800f4209200c1c2801c01c0c070310302c80e40390401d000c454014105481d41248050043c4401e08030041c1099a01460181942c041a01951150020f0b18000c20320781d80b42d13810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 931369964 1250 931368714 931368721
    0x30d02011b0306030203031818130c0b032a090a08070f1d010e180d1814210a05010908091002010504051903020718021908010609060806130f05 63
    0x851041d44000c4030303090070042c0e240b075900882d440c1d01c1119200001c101d41e181c80d241559a4684200502c002d011281242c036103400e01008111800103001515400c81040c80001c1b200032050840f8840d00380c1c441a41c3c84004115545180c040d0310754402d0004540a22000707a840d100c0401742070041000c1300040030070614205031029185196000390110032081c41c0d00c4031115501500c0981180c0304050b9030800c0d5903e0042d81c1214104403c68090240101d41c526a015603000078440d04c150600302c142d10066560300e150043c4d81c0401d4041d16000700e81c05503201d20414845000c590410850010368084051710390301c1d1360031100b001000310f50086c0c012619448500f4061801c210340c80f4039000800c5a801d094842d81d80e11300e5000e9503449644281220041018402e11130304000b89603108031206016482102c1c03002940000584000f005c807004515114217120f0030740141220050389826440c00d0400c0001c6808180041c44150801d00400d541c100308245032007076001c1144a03080000305402e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 931371214 1250 931369964 931369991
    0xc0a05120f0f0c15040f0510050d06090506010f0302070c030b09071d07171b0309030d020f03090f1c030507090b0705070806010602280218040b09070608040f11010e030d0201 76
    0x80c4909001010454140011b018801843c00d007002518400c42d44004408410b01088a851186009012405092510000707911005401080c000c0000f42ca42c0071541000f020114224001c00002038150082d024007003010403203000c0d00b141c0150a48099808280d203640c203e600802d80000c464070540024000c00046c9644032032030590301c0321400c42c0004142071905040c6d4510b0f81041d94641c00d00c0000004c645500c90070412105610702e446025901e51001010007a03264108403024a031901a40500302800030000ca580c0300e0341c01c85c102e40758841e1031140c601107000b000020145c009002d240000410241e0204000d000d200d88940c0c01801d005081c11640344c188081179202c6000d650004104900480440b0f1215200200e801003030352a002c00c50000403000d4000303558040b95001043c0c140010303c09061200780c481c1e001181205e0245030348000490740600100e034040d01c902e00709d020407800298030703c41580441c0310501d08088590b0100340003a040541ca00b5508015039503480100d400c02d07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 931372464 1250 931371214 931371229
    0xa0203091f09120b16020106080d0e04050a020316030f06050901080a0606060f0c0f0f08070c080705010e131802090a020703030b03010c0c020111160905060306090c0a05120f0f0c 78
    0x24040614007616042d01a036440e842c1d00d0707024000e03074505c00003918000c1c2868402d500240c002c0c10020300725003d00950301d80150849520070f03445070280f420240050f00700000c2d0300840b40200d1070000401385515000002710028001d40409006031030304d41c030740003d00380d49580e4001d01a101400162070307007007544c0c50000201d903440c0d032045040c080240044191150010340c2d42201d82d41140d5200303c2ca03201845c0c024404030210f10001d103c0c51020410105025100301c607607041ea0500e00403101c025886000640d480241000110340c0801c1c000da07582c40f50403144c0c01c0283c0200514000341c9060726503a0000300b80880c1141c0d600b4007241d0100d201c0d020715600d80200d06107a01c096000b0000c0f90420700c0c0081900c00d00f0200139051001d40c1c14124070b2010308001c48000d529400c41751040164540b040c20000d06000d036134851180c070544011610103036002c54101d20030007006004642a5181c41c0a0003600c030060580000c050007400f101d8103070390303805228484c212000c00e0040e004034002c54080214070b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 931373714 1250 931372464 931372469
    0x109060918170f04090e0607140f0703110f0105071e090305030927040503090109060e010905090c090d0c060807020304030b0a1a04021611240a0203091f09 68
    0x2060a0740d010401058a0301100c5140d103244825481e510041e40560403000d102d140c1c440c200c4c4a280c00d9042044400c0411460b0040c0d40c580d0f2070002c6400d0b5000c800f916401450644e102001d41003003e0400030f40a424030180d044020341c192070442c96065003103421214120341000224010b260700501e981d04030f0385408008800c40c1400c100785410354540c41c1c0e0320300400c0c40880c01621600200040001c00c1100c00c01d1580c59158400080d05d018070b0402e03141d41080040c0360125101403000704185009135840071120340c0c10303036813150b1041c580000c1112a035030140030001f124008020502103500e480180021584c01040e24020040c0f800310003c007403100090400003190001c0c081400040c1d07000704000c1e000000104041107203048800e21046035040d041c43d840c1d2040c4009100032030032000d944400e1065004000d004002e0309400103010403080c150102d40600d6022028101700c2c40b0042000e400201024811207080240960120f200b000d1040346818452440000c4101880d5004456401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 931374964 1250 931373714 931373741
    0x606040b0a0e0a18050f07030203160e060f130c030603050d1e0503040c151d060408120c010f0501030807060b060703050d05061305070f110f06280501090609 69
    0x41d03040c038080c0b6040c0c0c2036802030b10316407040380c80d0020480905844800e002185401400303645109100e25400c81d5110400c0c8000c9009008a11000e05000c05101c44c1d0422589030031041c400c0b076550241040303400014410125408100d108180f01546000d1241c4082c030a202e4031f0000d03546065050140c0b4212201c08640d0400084542c11800101c03402d01a85402131541030088e180e0b100c5203001c415000b69a08441840701121880c9880c00d50b102c2201d4103a0130718090700c0620300107040e0900c401489240109000381e8803404c0d84d40d00b150030040c018003400d80308200000e41095511240e409543d02a40183c5204c4004540c410910a941c41080c43c940e070304984580c506003599074050810300903000031508203550358001420a03100d24010490398108c034034040040d4a003801c4080c1c8a090100d0848001504186400f12500e0000803011005d0760008000d01703007943c0304c0944100c507118002d2940c1b03240303d05003d000e4141c00940241ca0103042018808620343d4180340181080340d150202d0600b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 931376214 1250 931374964 931374979
    0x150415092a050f13030510020d050901110301170c040504121428050702090412030b031204090518150f0c09090118090b15031c02150a0b0907020606040b 67
    0xe0310709421008a6501c401602030041d10344640c07403044040410310ba03002034040e0090b0751580000320441e0707008000520b0751000400c010f8640c554242d08852840b0300d0954400800c00c010f11045171241c0084007240186800c99900001c0603000c81e0544105440c1120072815054072604003e4000c120308458604040d800d908044a0680c920303500c8416011013001114250802c108462059044428080c1c0207880c040003420245407403513050300c46900c0003000a26120581c102c514011807280c0c00400038105040c2010700707008a41000f00350140420b412042e516244840d000401e0010321314003050290391206918200e0450361944000a12503d8205000c0115002c1c690703404410a0558086528000e244540d552030394005100204d40500b104820301c0401440900301410607134403040c1a070540300300c0401d4440d6002070f1004d4140060242c1c100000d0b8002510404102590059801c00c1c0803030092440b0b408608440c00c183d0f405401600304400700030b094140307401004001c680035184034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 931377464 1250 931376214 931376291
    0x5030f120418060b12010510030605090c13030b01080f06010f0302181005120610120506130c0f06050c010b060406270b0301120314070b15041509 64
    0x40100d10440c020749100d0a40e00b0440044a5050390203074002d0250080040c4d07640755003a00107005c0c00000d1141c544900d48030842580306610074098041115805810580e1503121200d4074640e9800112036110007141491000010032035800d4110b00a02e41c1c18050130015040a807000c1c24030300142c0083c0505900c10104000680310f201403008024a4120003140701d444840415a03190300c0b51b445181d000450840380c40c1034800109115010301e001c190858511644c4d01c06840541d07945810144c2990400c40c00610079400601c0c2c24441c0601c648450305280c1c2c0c8503c500c265028172508508000345020601800004003407180030320620044036010308191070044c00820070700c0b401d40d0204900d03269600c0460f4800d0070300c0c5190058020882d0a0b43c5941c0c64102c43e42c12000400b2051340065a6002c83c4622010840c04817811280c100750118641d50381c000100001001540d415a0010750316030b02c0c12401c3c080c070b29041c805000400710114802c10354801041c030700c0f24407400480300c0e06045100c9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 931378714 1250 931377464 931377493
    0x703080319060b2b020f180906010c021302071b05041835070812010e0c0a110307060903020105071202040803041703130303020109031419050313050f0705030f 70
    0x55401e2109484a4074100c00c2c2d822004d2103440704008091055540081000301c88240c90030040c101040c00301700281000c4042004006603554191034660203e203100c0308030f0b400350820f6913041442e02d40c0e031203000d864060310350f60316800072106003a0f1040303802d03d040d400c2c0300c2d40c42e0038014003070791405541c04520769150640710744050f003e1003c0303080f003d03280103c41006103c0080b40546090703400941c103251100501d01f800d51403580011890400c00c16042c0022402c4072a80c03900038011082151141d05080d00304805640300b50080c96007a50511091000000013400360140812040c460f500120350760030011009001207000000e2064164010b11080c481d01c9c400205070317030071180c60050b060f000710f128501c3d6904611070344400d040d026201d04e0f004410300d0f80542080448512998420b043c2d0740c420022050b0f82e0080002c5298054080a0340e2000603105002035900100707001c14003060826642e607000d1429900c1358101c09640c000038030820a9280c1070191090000c001c00240c840780e18908070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 931379964 1250 931378714 931378717
    0x70b0a05010923100f1509050102072306070b1906140f0d020612090606010f03020913110415030609050601020d090e0a1b0e040f0e0c0108180703080319060b 69
    0xd1407103600f00c08000254103a080c0315580c00c01001d41e5030300e402580340c40d000007000c0030170200319820100c1e0f000040060503501c00030340903088400380e041c0a104440303d1a64200740607904020765a002c1010311505000c1014210b8203030007010301c000d0840581d15002c80000680740d555002c43c12a80081c55182c0254a9030038440c904000f0413151030210382103e200044041c000c0c0709002444056a00c104060010005801805140b090302e502003c00040b00040b4141d215220320f2540101181407143c01c0208a90840450032002d001d0032403d00d034551886185074601080260002515000c0401008190b882220b8004c030007840604100115200c0191140e9410b108170302c5081e60384000500d906045900200e9003103943c0d082c40884222011004044115042c000c9200354034105c0d00000c6240280308203598140c03440c0180c101800890015200700340300521740d035003507500c1c1d0359103040361403090008801139441032450b2903c1e400e1403403200b880c0402d071001c4454000e142140c01d00c04050b5880 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 931381214 1250 931379964 931380011
    0x102060709050a1404020d05070903110319080a0207030203011e050c040807030209070e090a0b12060115050a122f03070e0d020112090809040c0311190504030503070b0a050109 77
    0xc440001c60a58500484c5c02403003500d038420f10082c9464103100c0c031564804040e000b164080c06602c0c0e450b0043e40101915406100c1906551030b201403082000a10001c014065491190060320b41e8907942e034002c01d0030348000f10300700700448500100c600c45014813480354a8101010180b020304023814481c0b482c0d608c4900740800707403099584100084190340715200c03a03c0c0c07140024280d001b00c0e0800c00c4000700503048100605104501c1c0d40046101d1395400140981203800c6420140345030543c8030815a880c0d40004108020080100450400e080b447c0c06101c4c4440250000c1e0352040541c061b10040c0b1420b03035001048006401c00c1804099503200a1401049604440c0050140c0b598030058170b0000d07070045494400b80c01c12049400b031140c03403005410700d88801c1ea000d03c000a1500021000c0320b030001c01b00018000b06203c401101c40c05034985800818003804d0091070540c4079201c1d0386c030315048500d04840b10309040041100c0b05115005082c010131b5604410b110781803007070502070744444150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 931382464 1250 931381214 931381229
    0x204020705190803010906060f020c0906061b102a030b130903020d080c0a090e070c1b060905010908060a09020a12060b180708370b0102060709050a 65
    0xc40c2000c01e1007024050070518900010300040060781c2403800451a0f002407203201029458100000b41060107040d041c0d010f51007503405400c404034041e00308490680050300098210005111100c08900d4602d1031f11418100d0030000d0013000a5500f03414142d800201c0285005560088000700140c0115017407a00c19225040100f00d2408403004500c1521500d00444100c5090013038000034980c002c0b40f450050884d980c1c605115640f01140c000d100d00c9543d801e0000100c072803508100710450000a20f401112600c5c03c031f800410300707840700c0316190341c8c40881d1443d901e82031200300885a0400412001413800b8240380d8481450551000d031642002042034030803540f124003600456031a840c68001805d0b508054414000300c5007000703001022090f60f0507002d5800d500400040c04840c00209204190310343c1c5034100f607600c465000f501c21680300382201c4e82988040c48051982000c509940682c1e58400f80040d02c1e03174000300028a0518080c000130103024101206008a88600000320284c8145 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 931383714 1250 931382464 931382467
    0x111e030d051804060b0909060f0609040f0e03270307030b0c070c0b03090106090510030b070f03141302011d10050c030418021b0c030d082e0f0806040f020402 69
    0x321200038030318800200120b5031142c44c021020070005000005000c440e4007c0e00c810b03035580c0e500001d20441c1d000542060f688444144402c1155141640001c503c000d0418004500c003107800c010a4599040050003014449481509614984220380d607071182401c11002000c1e0586503444940303101c1d00c09000c00d00c01107800505141405a15400a401130068200055407450010481c80c004c003014003801510a05020100b610082c038040303503034203490300311031500142c1c0c6170ba0030b05903035180c8084490010306854a00d8a4054803101001e42e06ca184030b038040c070041e078000f8030006003000e0404240902191207540c1c2488181c868a21040401c0e507182001c035078a840d8001c855246000f40d9101c03045c04107118545044041880c1c01820007001001400300d24001c120f054280c50b02800e02070340390103620180c04008858411080e25401400d441350b1302d640091400c0b41e40512801f0319541c0f01030040d100104000e14680b00071480c0051120101600c0b160030a50358006540100c840d02a1003180c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 931384964 1250 931383714 931383727
    0x10302090402031e0c0102100b0f061b0106060f112109060c031c140411041a034806070606050d0302010903030f020f070615090207111e030d05 63
    0x1000c0290004c20303d0110144584001c80e01e016954074801c0d00e14990050048411851b200e03165070140c0c040555004042042c100107020274849a504034150302c0845190040d011000c02c1003e03c40c42015200f030b9034034420075401c2c9040181107529241c401031130b030b0f40c070500b01d01d40d03105040342000d022081e0080250780c0d2480d004001400314001c08039660307514000050240583c540404410000c0c1c1004001032200002001c9000e80b071603800c54000d010052918060081407515034410301c002101c01003408080d00c03895000c2451b1000c0716034503200b11151214154a640c1c442c00d00d00c030144251305a84020180e5154501340d04181d099042801407201140c120300b081560b070481c40141c480503103840000c070f51030f0070300074003030042004141c0200385004000482d110050003106d03000c80c42c000301d0306d14011442d9180001048601d2a6140d03000e284100800c0181490004180c0070380550206120380d8000400c101c02d0840b419148851000901002c951701c0e100400c48400d510300c50304180c0d44901 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 931386214 1250 931384964 931384969
    0x60f030f1214162405060315042105070f030c022103090409080408060c041502030909070c050a020a0b07062f1e1204150501030305161a040b0103031214010302090402 73
    0x21300411074002c0711912800550420580b0f5200380c0c40340c58200c00721001ba005007114101004800e480c0584201c81c0500384824100410140322003141c05894401d01d040469110041040340d440c03001c4000414418071002985092100c50040c10f41c40c2003460088207a282001ea645c3c426444060301032516000c0c071106002c10031003076500a21800081c0c6440c0d191190143c401070744070b40102014418640d072010741c0144008150340410601414070003094480c00780c04c0e6840706030f4510484840c42150320400050f11602c184100030005908038a40b83d404510f003580035034103c3c1c902c10040c1543e80c20500071684d05180f00101c13001c040038a00b540c41e0502002c5c80700b00e14544071030300141400014080c8031488100801e600c101c2c002c1c1a14404113600c03408a100b910028480030300000c0d0240440c0140e610102040c00c0064800c00c2d210400781a0454801b0f940b140c00c0b9000c0d07400c100c8800042040c55002104070400c14442c12040110074a40000a08c81a006000103030240c08584000303011034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 931387464 1250 931386214 931386233
    0x231609030f030504061706030705091306110901120e030304030e060d02030f0f0106021c050d060f1203020d080103150f0f0f0605010906020a0b041104060f030f121416 73
    0x458000381075441a42940c100904694458417035200002c03400001c0d2118805200001e030302800004020f8081c1c14940030400c298a580a00884040035134080103000040c0c4500c2802d440c811031102840e101d0a08a00150803a1200d004000c950f40c280031017029000d40100450790f00941c10f04203500d80400c0000030504c84d008426422078030f540b00000340500f254503102181d2144419003102e59003680c8800d01240c440c903074007204920194000c402d40c1d0805028030042c0401980c6018001461965001210f42d54642c0f6800180507112102a02c000e150b070610001e0212071113418425a40d502d140c1c0d40c03034880c030f08508800000b20340e6001300c84150f0f400394100202c144610042404021030700590040245a148103450205030044000a0041c1c008150402056044102625a9504c1c0e458141100b104009120350160317451402081c070000c60348150700a0740c0109000d607100740b100e140844194a0817400745041c8003c60f140c90440f42106421102024200c000ca409002d41520300034145 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 931388714 1250 931387464 931387469
    0x1080112051c210f1d03030a05060f0a03030c0c0b040e010b09180109140a0b03030a05091c0309030c0e0103020a120f02040e011517070522060603020904231609 70
    0x1003058070801061100f040e500003000a6045800810403908000080404a80341148600040e0800c0c00060400021a400903920500c003808100004c4c0540b00002d0f00203d0300d420480108207807102c00c2d41800841c0c0044000b4225455419160904101c04901c10303a01c14860350070b00140c00656215181c48071050000300804c0f001c0340da20296103441110024090ba8070307264011114840000301e551820380941242c1000c041d000c2d40c07602c000c2481c00c54013030f0311003420795810503000d018441e2414100425021024060380e140b4449a0843c40d07e41140c002560146403419001401400542d13140090341c0200c1d03c081407400c14118544c68008443d517003850000e5401391a109500350b4000040d003040c0c0311600c1c00104104555100c03a55180c0c08080140c20348031a900940c4244590300341a6020310801c0c04a82180c1d510380d14041040c0b003611060b0300404002034002c641146a400d0500840004644440b01490b400c2018040020514401803075240044464038060b0080c0e8000c0110102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 931389964 1250 931388714 931388747
    0xc0319020603072c030c0307051003020c1608060906010611100c021c0e121b0405092b300c030e01060312080f0c04030b0712090303050601080112051c 66
    0x1030b405450711030042180044e00240b40280254005001e040c034000c1024402d40c0c0c401080c035070f950003000d14118001d400250524000784500443d00039420342d010502c3c001406000010001d620300000c640b41083c030180d005100703002c3c40d41554410305c1000b06030004d5140b41920009410180c0130801c074035000700c00302c0c40c0c00120350300f0844403107103035110809001c2c85509540c1600d000300000c03581641c43d001030b00304002d00d070410940c5021618140c2c0280c0d0f0465a0392003245c00c50b40da100038210b00c0240e00d0b41582c1003924001c080490440d000130380801c80c08400341100d40321a800402caa070301e016100754021a07550352044601c0c002400799100103000c030f030000e00800000b5181c0c074245e00c0c0000d03070421090204841000240310b401049100a1040280d04182403d0174030f560740d40d44503030102400a200f80301181403640104040d074803c1a00082c041c0d9400300702c3d0b040030b0b400076041c2841070700035038020060311410001180001a5000c2410700f10089094803484c020301c119100030715561400c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 931391214 1250 931389964 931390007
    0xf080a090f1211070612200307051c020a2001060b12010f05060702060706110706020c06040201120e0a0212100c050406030f0212010e1005060a110c031902060307 71
    0x4248280412000b00d10316064440d00c00c0c50a650341041d9640280348900d100140f1280a0340d1000e45030394002071502d8080b0f090400401000c404440180d410480d001720000340041410079414450243d00380184142c0c3c4421468280c142c0c100601510b4000001c0b89601c03140e0468404100b800d40c00b2000402240d04038540350302040c545081050340030b214006c100300c8503031404107031840c221040f1006690300401c05480d0200a580e944090803200402404c2c030300d002e0041e1404944517000510b192039000d00900741c5481e00344005441e80504842c0c4520350343c980342c02c20201e03110001c0c84895141c0c040310030032405214421454500309098449006a41c1406a400045034114000d08256002a1024400e803c2e0b110780180032802000446100350840070010003010103041c8965400003400707400307210207940b82d030040b03000395006d0340092000030185905103d91032014040804200401c401074400142034480d610400e8a8800d0064420500000404c00c081c1c090003684020081c444e5190 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 931392464 1250 931391214 931391243
    0x703060e0c030606040c09030f030e130c020607210209060405100e0102061e04081b15090c0f1008222607031d0103020403080c071d04030f080a09 64
    0x1900c401c0440c03107181c002d118000c04907485241501420142e4541541c07503c440c2d900d0b5840341514840440000e03014070507654a400c02daa22000800d020001d03001c070300401c50b03811b83c81d002445c000c80140000104421f6210000341110710345d48000f0001c01003c80943c0326101030000459a10503030340300c560322000c81a11000031503080300f81b89542d00800d8082d0b03645559124005021000b0200246150456000001d0b000034850000b400064610550884d002d05680a101d481c10317413a18050105d1003c200c00700586003008000f11901c128098600c00388819034540440c51032800c9a800c0d1040c002d42100003014800c901060008296255104c1030310100c040c1840b5118103d000d0304220700200c46080203103260050004c23900415030542d2124001301615030130905401d0b8083d007040c10140c00700700c00404580403c01610a1300c10080281caa00c034940701042d41c003c0d00b8060f900700110603040402000c40e030004c070f40d40515000d42c202a001540c0380d1152000030081410018001510301000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 931393714 1250 931392464 931392491
    0x40204051c050606030303010b25080a2003040609090b0d021305040204200d200a081f08070e1b04170d090f050111010f110a090914130203070306 64
    0x5140c000b0b014000ba1129925040b06141d22480240120401d00d8010000911501d2040c008880d00e03900d03052a0102e0203416503103078142c55100e0144000007070ba0780321140540f1706d109810781c04000e140380010741c541450000c0152070004107124912501e6501d1500314559145c143c54281c2136035000b01904100030f64503403039800404043d541a40500d19040c030340e0307009900c1120b18064210ba400401810540c10101e0600607204440c804000d124581403030300e01881141018180745445516030200c107181c00210384e041008001c01c5d41c48000c00504042111150214100080c1e64906a40207040d45d942110b031640007407081c115000d040d0b000100040c0c92180c072014001c3c400703c01c0c010744140903d1424101d80c0790740c05010f50009881a0003082003e58007840f06c080518074514000703d050001c0149031400c40320310341c1c1c64108944000402003051540800b800c000780c01c1d205d208101c00c15210209660350300009004650b00300c11941d200040d50360411000004640c07141d014020003481001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 931394964 1250 931393714 931393759
    0x10c080d06032102240403110f010e01050c070206120a090804090605040b010903080313110a120c080a050c090403020f060a02041a1903110706050708010303110606010c020f04020405 80
    0x30002c1003c4881c80100d00881d10100c3c40003464144150344c913a4140045007007032281c5030040d004405001c07090300d000740b04070400d010384219000e83c88000114001c05000c002c0c25150300609003101c0324000c0095038010b0b590942564400c103842100680541c1e1585913050062a0209015103424070101e0001905a00d60b00002d064400540701403060386085801520403842c44d010040059205000050708a100c0c3d0081c56000b900450540304601c8100c00071510140b010341024801c803481c008a1400d010b17941402070020200c0703500528000c0070301c1e2070f8035441c0c0901c0d401c2240f24080300f0021a040c188200408a6003c10780000d446041c100380c0601070080d0320074450304036040a11a40c0b00340300c070004403d0715510040340d4018103a04004074000c40c000e0045a01015a9080910552011a1a912480c1e200d40d60a032100b01c6254110305029041c9100c0c600b044440307030300840030010540d034080b58403503070705a040e1813500c110450000000e003c0d001d2604080e410140113003640342c110942c4030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 931396214 1250 931394964 931394993
    0x30f1701120c0803071a070c060e0105091e0a02091305160503010c0e01170a1401030b0708061c1103010e0102121f1a03041104060b0702030d0914010c080d0603 70
    0x4902d903002c996200c80c1c15480f4052010041c08495132400b08460042c010b40c59a64402d1300e0f880c1c5001700d04016070f5000116000f1101034401c9030364900401800203000c001801185692400904a080c50f18404542d1151040b800a00803103440d00410800e144035003807909815405010740726900400304c2800c10000d07980c4a401e20039800c02d035081c04164000d20070f110100030182d45048842e002c000050150480282c21448055174841010032010b080b100058042c40c460390650b070481c24000700080c65440b000e449144101301d101d080b45043c0c2c4421090700a0740c7c0e44030030030413010707130750000024010a42588443c41035400015228040b00195503020b200329994480107902d0000f0314019040504a8000c010641440320403134036130000d080000d1580a4807030b48000c00030f03640300d50200d406d07665640c3c800d000e0220082021000c51074184424014200e007490315020940c5000380750544001c015468506001603044520240804981100d03045e484011091112a87c0c84c90850802c4070081c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 931397464 1250 931396214 931396223
    0xb04110a020609070f050a090b4011070303090212010c0e120312180a0c15120b01020607030207020a080714030610180e1504110a0e0f04030f170112 65
    0x20011420b5000f101030f45c17007607400150a11102505181c142e1340205551070050f13500c5005c2d03041d40c03400080003901c0c0d445095110320710104d17406150700d0b403c020040e601c14203d01a50404114a007803603201d0007606d400caa01480c001c22107505a0000c1201c031a1081c00703100c00c95007800f20079681150019403120250205441c903a13003040e03900082680305e005204601c442140d51402040c001802e243d1101c81d0384401d802960403510640d81d403590640216400803591080911910703400c15040b40122074440e003864014418004410300003903c0c1c180081240c2c06042d030100703038141507484044189015120450845250710788512117251000da00b1454207100340f02d640c0000309a000384150010449000c03000001242082b00c1030080500280382c2c00700d98511409503a04a0400701c510964050390086844d9900f51404d4014422041902d03042000c0e40005d0900f03118605d118164981d80c06900751900510784e030340800c2c049a01d0807540ca801d268050220001042010410503c044d90728442d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 931398714 1250 931397464 931397473
    0x204050f010e03031608210609010602010b09040312150b0d0e070303090b030c0f180a0b07080d050a09050d0e0108100b0d0f0f02070f17040b07060b04110a020609 71
    0xca5004403081010040410781540051100302c0010b42c420284c03040f4544104191402c00030203582038200c821482d841140b0349144402485030780d00341459514003401c42c40c8020b2048400301400300d910403202030700060420024004001902c410b65100d10361b105a0039001c1d11840750340350340c02e000036045408a01c1039503240080c280a031250000ea00c40c22280e00d61100400540740c51840c900c0c1e0b802c01040c045501e03a08102258903070311302c00010302e01c2e106c400686c0075000400d40306010300380521b50018009418208145004200224207680d00041c0001703010035656200c0480c4405402400402017040c03003034814074001c03aa0400302040b000c80b02a039034903c075996007101c0868000650b2140007a81c503c1008103841481c0b003504140c1751401000e502269054540e000941280d02440d0180e441c0031800013500f04001d0180c981240f10a00ba4480070b040c54100201208603114891b0002c10303255942e1501c00003134450307402208402c2200780f201a150305107044083d4450768222003407a828050b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 931399964 1250 931398714 931398739
    0x50403021503010305060f0a231801061809020607140d0806030610060c02011727060f010b07050c0a09061e030b06010f233c0703180306020405 63
    0x1c1c907001d4904890b0000020b00068880c94075108403140b000d480803050903200c4030054503003104041c00a00001e04d00d94150200e2405044002048541d801071a02c50303414000c040101c640041526070728204001400280310f0200c0c030008416105141004001407031040c262152000041022244030700b10342c880c0c280340d560703070300c00c040d240c0704104e40b81e10300070417419414096544a2448940c07424818144042d0326001c480802410100031600c0c040800d005201c1051060860703003c1d0122a0078080c000e051070b0510460542c182c4005000340d19800c940442d0040c140141000f264003491005007035408020f071101a6040501002c0c007402100c8140c1040c26580b041038400c1e418200c80c0c1003105540940c9a43c4011101d01442001d05810056402444510880c0e454404207140018103651940c9610b020046045a50100000440a000c00e00c1c58503100360107405000c0180798201c45507544481502d015110203500514800710244c9040d030100401c241c0d540200190b45040340c0c480b5001c3c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 931401214 1250 931399964 931399999
    0xb2805090a14070f02070603020f0d06180b061215031e010204050a05010e091506120c0903151303180b0c1506030c0d02060d021912050609090a0b060105091005040302 73
    0x80004d50340000603440044204500e42c800e81c041c20701740700041682460704003500c0241d000d0340c0083d08184050810030480380803441c024811542c00240c00c0d91020b0034000510001030b550080180221004640d628144803142c1d401c7c041c0001d1000350844001d26100054146c40c007d40103401079501965441c1c0b030204a1398003031b068041c505c0b480106103010555403480c4070000c401281c40100c0e009002402036400ea0103008009038420140c0380103076a00c81c0203420401d4a0908003a0f540c461700c00c2c0070810300c8110682c0b03e40c840030103901420084c000b084139000550280310641e0100d0766032a004203100300709050218038000e2001c0801c3d02c940702e5848040406440f0b954440d90158800310368103c2a0050402a02034041d03d020f5a800500304400c041c419204c200074041e141c00001e402c1030b0143c44036201403280c1500802c090710481100d02d089910345685041c40c44e000b620081600002640aa1081003140d141481c0a0310000a0500039036014126070003d000891003540700348512000c90 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 931402464 1250 931401214 931401227
    0x8060f010906030b0a0b012a170f12090a023c060a120b03060106111c0806040b0a08070f03031418060a090b1c0f0b2805090a1407 57
    0x140c3d0040c00f04c03000b81d11403543c91401002110f032528140120500380b002c01d050f090741c031030f910560903012980c2c1149075490030550504d04041040d03034040d024030405862341c5013482070700c91442410300e81409603112072600c54544003000c4c10080d0701c40400d03052030ba001c0b8a08e0380760029586006030840114040c42c500c00d1202c6012070700c080e422103011320010301d10364840d0019201e001e0368001d00080e03010380d010202e4100003003600948003140c03c03d0240c5c041140c1c2000100c1c0d00c841c072519051102000003000030100c01740a04031070312407900ea94013140c207565401890001403403800c0071a50310590f181166801f42060344400d50100e45910b1014040001000449e807207090112240e01c12080c01c01700308401604804410010450400c60104042d86000000c21542c1c100b41119901b0760780e00040c03042030f01ca0403140400c101381000790504944c1c9500002c1d4141066460340f02000c2032501c1c2e60701009600590141c0d81c010040024003a4a644c0f66022504002054000051540c4d5400050720403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 931403714 1250 931402464 931402469
    0xb040e0d0c02040f05250e101d0307060f0e09040b0106030504050f030d02090a050402070c050913051603060b060a090303031505130b010f030902030a0212010e060108060f010906 78
    0x40d08000041880da81c072079021185000e1008000207000401203620b0003c80d0400c44800206c520741e4a05008809010446088640c10703a00d4803244003980d43c400720b5403001584600400344400c4602400742c01c9001958107403200c9000e0700700c510883e03441e80014841e43d000001e1101113038400d1400385450415082440c031658200c00e007681c00e41d1807d02d0440007080000c00555440c001c030390780112058011700040844002c084000f6031510b01040070001e22001c60750103103100b01d10420012000070f181e0490041165070456a040c013a564147e01c105084011090042050203030441d0700044035403503090b403800d60380540c0c03081084141c1d01d401d1290902c554003886000c20100700f010030000b03110760030050b100c074044003d4040440d56100030400d440700c00030120b909140c0b6051304903240d5a2080f81c1d205d0ba09038528040c002c4403500c0c1c0119449001c2100041e0160504404041d8101000d40102c1040c1004400300d030229a5075102043d2034038020b82e01090940ca00500028000d80240140d605 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 931404964 1250 931403714 931403741
    0x303090d0f030c0c1e0b04120f020402090a0e09010f0c1707170403050c010e0c0a141503011701140f0a1d0f0706270b0715020403150b04 60
    0x40c149065100c840101054250450401c080341d4003603000100ca854242004001c01c041240004411a100c80c42180303594000e01000d446c140410007010358a0090392882030f80141c01a86d0304445400840c0203440b410307500382d0304060074040006250110082540c450003407035008012101c14100030005482d0000485400244400e08240c0c00032903030141c040d081119401c0c161300040010603001140720301203500b42d01003040450540071142080c02404031032640c07900980510310000b000950615030340e0166080fa2040000d210480d9103601c00648480e9420100d016101d6a48040d010110ba002ca128601d25508043d540c1c0c6082120248035070103031000f10002203641d40c6138000c0030006c00f6900d120f243c80769144403d008134000c0c1804040360b840c074001d0250481d49d05007040138000081e5120b0500e000c1c1e001580d20b404546401da9071074151000340741c51998072a61410150f0902c202d1a8002031800d100040000400906c5480e00100e111b0305201840380464410802c0304440c6003410560 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 931406214 1250 931404964 931404979
    0x307031412010302190e04110906030604030543170406090905220516140a0b030612011b1202130e0a090b0a09020f27070302070803070c060605030309 66
    0x4010314140c0300d4032110280d12042c42607425031b101642c041c4105e05503025034415911030016001424031004056003e44e09030000d094a01389070750010214072601d80143c0300340034440b00d0079101e03100f950a03a40e80a00407140300607144440c40f920410134102c00d8022241042905100c82100440318251000c480c40380d1500915a86080320400141900074140e410446a41082c40f20f407001e203040d0464034130300500080100d0b44540d02518004002500b08101401c1c00d072b205402d4940d2080d82c03140a0b29a110291034981d12000040f69005403048400c0d00781c3d50920500c0c02402030042c0c4025812800384c0d40f04010812a000c820040b4032481005041c0982242002c4c4502030704101c03066085218000d00280940c1c0903214031041e118140c0302c01400c503485080c803006601d0014180070400310229060080d18164844040d0b04044071010301400303603034280005010074000e5058900468100010540d00c1c90a6403006140c422000d00480b002440c184001c10030781400402d46410314400380564 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 931407464 1250 931406214 931406219
    0x106121a1605041a09061b0706090305030f0c010e0f030703090b090f0d0201182306160b09031317060c041d13060c0801080d0c031b1b0602030703141201 67
    0x80d00f065440500130424100304101c0d00440740c4441009040110822690f101700304003c5103181d050100b254040e00c1040911101072011440100880e41841c1c0c40c84159030303441070140201e074007500701c8105c65a8140074030007510320201d1001c03004206062103903540c060071079241d850361901801020149504448100c00441d158100041507000c1d050050403d0f401c0701c06803005a08480c84c460708550000d044220046049004000280c00326190482e0040c0c20007400000800b00350701d50410140000100c1008685509810700890340c1881c030880b43c0300c2d181a03c6806403601401f00c2e0b4510a032501c00c001c00142e0040711a03058400fa20007a401001070704244d038101072071041014081c400c0380f826201c10200020b03820321421450000035160b40c0341ca589404511414001c41c1c0c6143c006020061071200300081d4440c0c40310b4019200c001c441c040702c45841c24561a80c04c176441d02e40e80c091003e60004100c10b038001010309010f41c480e5032001082203050f0300012044c052840019035907801e09005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 931408714 1250 931407464 931407479
    0x705010315090f0b030607320f0f4305071a1c0c120b0607020d0819030e240106030903020307080f0a080603150a0203090106121a160504 60
    0x1034024400c100f0740814400e08100c00241480780941e022408070b4802d00b042d2403048085d031700501d440340c801c00e441c0c1d41c0c41d55500380541e5188038008040311765150008a40c500126408103881110f40c4c641c001040c56150015420400c0d14001012a0042000584c40c15151041c039010305075284c0c014040c001d8280340030340c100c40030380e41c203162251105001d00010306410305403084540f11840640d4082050040074001500c04a00091040d8a4508002101c60a611a030044880340d503419218000c110700b440c1000a4180980e060305105103481c2112404050350542292000110100c02e483c00404544c40025803054941d01031896000e51030010000540294800c052060080c010b9925041c0340c0d540e83ca51507400f00040c54502140401c03800400d940c0004080d50000d0140c0003070004641c40300540304404070050058145c141c00000140b071541d420f4001c5d1004111401d11800301842c1c0d490001d003210b42d05421009800048000600ca803074060b4000d402e082c0a0f81c03105031a0a040000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 931409964 1250 931408714 931408721
    0x10507020c0111240a0510080d080a1820030f0604020411071a0a110c0604390503010f050f130c0308040605270303160f051509070501031509 62
    0x240030f81400b6400c11111484402c40f203018030030802c40101026441d01c550300100b00d0303101038041c004807442c0043c00c0c820389400151900312400c0d01c2c100303086c541e5502e40c071045c09441401031180d1122400c8004030108400e01e59035101c03201921201c82c844440c1c0d5414190b50f01900d101910140e48020701280160900380d004c0100e0300c0d8120700c828503010035601c4e45014550b890703416225620b40c0e9810459241e042d441550981038100c1080380c07078801c46850340b41c0d1b200310203080a8054107030300ba0301c07025550144004408401e40a0001e108503e4500041c05843c10b42d449801d01035420710b01002c825410170b210300303881845046130014464076010501c100d4684222000c4880303004000010000c00e082c44050b000905050750303107039520321072903280c100f0780300011052001c200320800c90000d484c2d4002c01951021501c001d070582d00b000d407605041d188949125405407403401001188482d100500084510644c0c640c0120b90300b4030366075001101155040180140c02610114007408503022070780 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 931411214 1250 931409964 931409987
    0xb09150d0212040f030908120703080711070603140c03040503071527030e030f12282604030e0f010c170316090b04030f0206040f0620010507020c01 65
    0x84018204220520700c0b41d105041900c00f0395102c43e0350000c1a04050340002500080c24001c0c01130000c2140b1400740b10024002c1d08001070912614000040000e48568813142d002225542180ca60a6031008054014410380d00070b43c05e040741364400a000301650340101ca001b558403d00951800190351a180401c03800082801c000070f0f1144108002ca110a58041d1381c140755110311044050010b2901030840010261024004d4003c2c44c04141d029802060642a01914205190f55031407200b505602e2201081c081c10080800300098018181c1e00000c0000c2d0b000403110880e454262880c4046d1140408540081c00101000c05084050400e03100c061030311001030401101406069591407036440d000b0004140c241e40c00310030007030724401035608010620b0540c00c0000540b410302618400c207105900024046154035485a021512003504580041c0690308000b00d2a40c0c0320400200900c0000b2980d09d05d079001410b07429000b02c4c042c840c21740100642e40050071410007900054034403101d5003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 931412464 1250 931411214 931411237
    0xf01061a030c1b010f060e070f18050a030b070e1c03120e01090501050f0a0207020307120201051b07080d0e060a031e0c030509010e1f02131214070b0915 67
    0x707108140283c0c0381d81c1800c6109100580c004900c54011000c0030040712059070043c81000d80f40e01c10b0055041e0044112400c418503890320150040d01800b409000603503aa01c100e070001c3d0400d0000003408110001507001d004240e603201c00d407005c15010041c4016010301c0b18651680d0f0305494a00090244800c904a035141c0040461084200340d15070382107603521801038680e0b944506c10009103107903450000368030000f05c0c14214185002e0742c0101f90741d2680d60080c150010118417a41040d0b80c001c0781a00c022140c503803c07030941c0700109400d40e625100d417481101d480d4495404641d20183c00380308a0781180d4006003803a030400003034031012400340c2001e58030a8481c051740803038503484181a000f2041e43e00032a4030007003524200000d0341400c44105506000580d0440544000010880d80c25442e00081004c070140c2c03280391120b41c0f503551000b40c0c0e0048680341034024450041041884003080544072100540f5075456440b0f02190191040000980e84005e10000c1e400d066005100904446802d5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 931413714 1250 931412464 931412467
    0x50a050a0e040906050a200f03060613030c0f06030606120b12010c030b0906090708060105030702013911030d0905010608070e0f100303021902010224090f01061a030c 73
    0x182400b0a046508900301a41c950340c5a904204142c0314038000c000011844000e1001040121185095580101c000105000c80c00101240c506d81e0b42805585c441c80c00c0c00d0030181403594901d4429103102c3c1e0703803095141201c10b4200c006400c1e4042e20403942114402d8079000c032642140e40310080144803a0b1030603540450460f55401d5015424423900c812035400d030b100007660030032000030000400f50003814944945015400c000c2d0155220702c3c060b070070000a08080707840740c40d00c1c1c40c140e01400d040307111215656058101a00056044860030303c1500394016240d080070034040303080b18415800a4030392240e80c410042003100d18034a03485041384034010b1000103003040e1181203441c200b042603441a040709a07003909006072051801121900100c1d500d80d850a59451590042c3d12400202091514890315070068415039009000618680c8840d911030158501030807840001050180e0b00b002e0180306203404000004014485c0340192105008244004a1002c3c1901001d138001448a844440c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 931414964 1250 931413714 931413737
    0x16060e030325150b01030b0a1a21100608061f0f050d02030a0507030c0206070c02041e0509160501020f0604080c0c0307081f02270a05120a1a07050a050a 67
    0xf058240702c064488040410a8802000010b0940c1c1f041100c02344070b01d41200042014010100807110305290102c0200c0e103803105c13400000d10400852014080106942e4200060f511a6151080036143d251301e07510000d0721400e06100840520500d42c00e0300f01d09940c1003204c0240a84c1c0540c1c0f41c08114a4030310320382212480c580c03069030002e032142e804d5292610184801c2d00d401d03000c1d07011a01c0080c4001c10f1646043c000061100c10303608806405165a41c01031308182010b000354004402d004034091046007408025555142c180d043c1a5920540300c000c0840e007984041420482c181c0d091000b40001c0e281c54507000e20380e80c00110000707801e02c101950702915803400d10030440200a542c024050580c104140309401c020084504503100b0300c1041030070b2420f80080d141c208400005003820383c00448400c0440d646054a8000341c1d400391148040c1c0c1c0b80d4070740000e41c2ca010300c0c0c850840007143d0080c504104080200a031a0031000c65001c0c801c81030315910840c094800c11b01a4035001c00100e8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 931416214 1250 931414964 931414973
    0x1050c0f071433010504050c031609030804030b0402040f0605242203030f0915030b01020c0a1e090b0f121c08010815040305090111010204031416060e030325 69
    0x15800f02e1246402c0240300d07242e6108a03d518410700501041e03d00380300700d00e007a0780d40261178800103024110300101d1441141041b48115802d2002e107030b00c4061199250f03200d05200d004240d080724101d204030b0811203901e02a003454000d403003c46801900c60001c2403e6401651220605004c00321f0111006000e100e81c141003003034a409625007a103155901103030850400401c20400e5040200078481d0a4004000355006800104404296031030006441a00348004034203002d25118595880040100c0220b0000d00ca07000350703841c2c0c100b0450710b078038499610803160b005d4a18001c0d035580c3c0907210300ca103807460303050001b203a001a0f0690400da405903031410030300c01c0710142c0640c03850000070401801804448801c00c840d20070300042400351070503450b01ba0740050152140da0f074003e04010400d80c240380500e41c2501035a0103550701c422514680b46c10760514aa80704007030b100f074640861655a000507024000d00d0070500c41040580692b1404070f141c134800d00000c90408115900341011020300e008107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 931417464 1250 931416214 931416253
    0x150321050f04030b04030f050309070302010e1311030601030c08040c0621090809101805150c0a050d0f09061227030e0301061703030a050702070315050901050c0f0714 73
    0x85100b00342c080845d0805040c01081d4845a043c0f01090100400a010039900000303000d0044a50910b803a90307082e40a580480d031512030f842c0c00310714440d0800c465107400d5030015018502c240020380e8108101c15801d40c00b03c4024000f40c9010f840b642074002e09021003886190004000403038844010407111190100a0403600160802e03114400045080600c0b03242111004011311120b181104608907119074200c1e54400900c1500c1c8141c040104560302d032541075065a188044a00c00d80314140031504005480e00780b502c04420002d1100d61503400458020700d060000d80d00c150750f907160381203003030301c0d001d80144103c5102c07a05074903104505143d0341540281e10034143d4840c5d45c40480c2c4124540505081d1810358100705880d03059201c044000300c03000416a41d00c078242c48400700e072a44502d601a070409005400c00b60401d003a07585184c074046202d8102c01e00800b01030000704880d645187c080502c500841d408041004070400419020900740c0140010524500050355900303504080d80d134151 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 931418714 1250 931417464 931417469
    0x616051309090c0b0a0203130b03042f0312090301060f06020604080702180415050105120d1b0209040b011e061e120203010927020906010f050904090c09150321050f04 73
    0x60340b000414204405d2070f500450000c1c4036045005080d820965182107600c0020701c1981070004101450701d20401c40d2033105c422000380a0f040e00c1e101075450400305450b81c024240103000e5030074a20300184006100710745000f00e91295000d0135080c0c85030355990700641e1214401b0390f440040d50181c038025900203018a4010341c820703850030311141580500c40b421750304142d202a11594034601c62070080c80000c00c10301c0f80114903203081054159a51852100207078460006500410403004200030401c0015800d41a140c00c0102d883c121018030f01f5402c00810603001d03000004100400d80480307100d40184801c0c1c020f0b11820300401c58505084040100d82099105000c0c1c4e6481c0d88003c1c40c600744c4c003003480052201c4250320f0511440160089500b40350041c202c0d50400c5200c44001d04001d100c0d400b541c594500c000c20030300c82841c1d1030810110b084907500645011328900703283c00034078204280d6010200e0394002c0c0c020000100d041e001d00071642d044031000c0284682041808581c015030b0005102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 931419964 1250 931418714 931418717
    0x15091305060a0618050615160c03060b0a0911040e04030e150a0e0a030804150c050a050a020f1c060218190303081803180103021b0616051309090c0b0a 66
    0x25a940b411503240f44240c4222510f2213010f24090038004561034a001c85401c03182e44210069403441070075828940340c03503011405414074405107404010400260420704000070304580c00d01c1e40390386070506982140ea03c003481d000b00420400c010401d0b0581101c20303a501034064280b4118503030003032001c200036020540325000c07180c0000803410002d60704498141c01d20882a188c40342180d083d65201100c511a500030702c0d0f560035443c10100300d1240700701790403140b00d688a0190340d101c0501e46042a0340c0d40a2810480c82000c0d0b003181c484e82e5040208001d41c200481a00c00364060300b00341c44950083d8001c1541c0340401008842e824061f4a03029840c030240c0c8604600302191510f5414000c01c18040544a40c0302200c09142a001260f000015602d030042e54070340d42c441c6044110016002489082e11918034120015004290300c880800d605104101101c04100380310050441100c0c14820611240e0300980c3c1c041081c80146810707881040704078402d600c0c9480d1a5155a914580d50700040c40940 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 931421214 1250 931419964 931419971
    0x5061005090109021602040207060225020f01030e0a020904110a290702010207030303050901090b010306020307030c020102210c0d3815090a05100201061a0315091305060a 75
    0x5070400000450060220030307404c606045001d4150046180d40d0b400281c8035a40205462060001a0b4126116542912242d64070700301e11b00d0401080d40c11851040c3e200e03c9018204480301e501a0103401d03028200c21025005004280d0308001404402070810b0341e084504061f05481a203681074260050880c03000f1071a0480891920b0400d4a80b1000c4914035042042c02510010f0360002440d00c10340b41d00d42000b06a0390358440501d0f0040c50390003001307440900017500000521030741d0b9008601410441d60300344801c80305480c040c0e09034031540d151100c070503040d02c2420310f075421700b80070542d00a068039010703a1502148561040c242d42002c04070a80070840030306130190b2510030303181d01603191501c0a046126071200710001072880c40c1200b89585140000210b50740b683d900c1d076000c0f0011f092f0043c85c40c1d06d60f481c0d501000b4001c2c0f44900903c5142c015442d03840038040b10b0b070740540b40304010b08142444103107080b03014403e0017070025061040c4a00000e2100700021010f00c00503106e408040d0000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 931422464 1250 931421214 931421219
    0x406090213080706170a020f16020301050603011a0d03030e0f071e0b070b1f06021b040b030d1412010914130507170f190c05120d0e0d050610 62
    0x1451001c1a900c200655030100340e041100300d030003058a103c054016564410140c0e207100103c0e01074032403100d0070750f00e02500007001c0c0c256408490704840c07818000c0e0000c2012360f546509150880f00b0390041c50703683c491400c1a10f0b05926040c0d248202d014440e2402080f8014200c2c91640707401c10811514659421040b4141b192158901c251260b071200c80301035080145c0791003251191481070000c043c180d0122800003860340085190b0f40500258900100740060b0b41d509802900c60854181c0740305c02d51035001850f552490240500c5010890060103080c5405040c002920300d05012201c80130002c5d0f09000c3c1c006070085c64424180280040b08000c5500d12082081a416210040c103240100100700c980c400450030000c0e0101c00d075400c0c00c0d150700300c042d00c200505180a82031103074080b49100350005101d02805643e83c29403128440c00202140340c0d210020448840249035480c069075100803281004144904a41003032840054850341103103500742caa903801d100080300d64010b48a801d034401c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 931423714 1250 931422464 931422487
    0x181703070816020f010507082203050a0308101a0405090402010c080403060b13231005210c0301060b0d090314160311010e121b06240603010b03060d0507030204060902 73
    0x20b00410001b440c01502d009000c1e6221142801a19220b81c00700d00b1001c10041c0c0300303042c4000540a5900002115010001e40c90014500e10781124844100c0c0b41c085e800103045901d0300c403110310300d8603020b85d120708007428402840310a40c0c5c000c10581c10450000b18440c0440c0050009101440c010540440c0c800320310020f009450701210402c0007498504800a20764101c04480b445101200100800a9880c0e480da804181d10854000c90760000304144030700b050075042201c0c984031140c20820380341c1c0819510101800c035a200c0c41074a070700329400c0000341030360000c039403207007c01c01e02c40e00340300b03c00b510084040c1e441c4d0b800c5001e007140243e1130011003400b8035400428081000f88890028030106d200d8400a86d2a5844c8403000b1202c4c5c0c50203d142c4640000d00381903200c032681d1a204507501441c0c00d80003503800c9900c002202d0b00d014100c0345284102d041210480341a249002165403031902d4807000d002903049004410307904d9014017040440140d6841c011341303001708601c04000d42c440304001071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 931424964 1250 931423714 931423729
    0x50706060617010306020c0f030a03150b12040b0703090519110d081605030c0d02010b090c070803130812071805040207020a14010c062a18170307081602 67
    0x4000180000b007403000d000079421042c036034156507001d00050707265181001c105181c00740000c0750440c00d01000c1003504180382d0641c03103a140118040e1a901b005540c1c0c4443c0025403003132200c8000c40001c03040c009000b080001403c42e4018141c1c3c079000072500455100d4904000050307060010318000c018443c1c003031101d91250300590380001c80d480c2c1007600d61580c070210248144003010101100300810740c4140002402984c0c20302c08074400743c6280890b410002802490b54459540c4a40c001d8400b10394038102120139150041d074050001c62440e00d480c0d12000b0103003070f079003030449c2c1e9000c080041c51542071003a4900d50145180341c5580040342144032034a04541340d190005801380c0c0c4144485c50250b42c5000b001c0f4102c82e814002000203400c00310040700c40300f60310703d400b5258605285a0512100255000b0407480c0d03081e1440c03401803c0d814030110b400402c1e0303800c44203441c000c4050a21982c90b1400301c401221650100312860301c8d0b5250b940403240e8000345205019042418480740a50400c41b1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 931426214 1250 931424964 931424969
    0x131d0403030f0e0c011d04020408010e060f130318080a050601051e0604051302040b0307020706021608250f080105090d11070e040c090f1a120a02090408040f030305070606 75
    0x3041031103001030b01e00d84180c0e00c0c080c07000010304110307a01448100261b0411074800701240c010f4000d640d03990300c030544039003c0c00b2056038210051183c1e50000f040c0286560317040d40100700151004000280381d4400716011280880d030911465072142c00011071b10000c100d10310759030703115402a1207650700d80b204221113601c501000030a41207030a0010342d5541c0e10041124143d9604441400007a042090b40c1002070250703400c845092440001030007141d42d000107009088904a50868240728042845807010204920440603558808540103a82d9a1003079800d152844034121081c01056075a0707400b0848411070383c01041e00e80d65490074000c0500040c4120a5002c8550805e40b031a03c1445540700d54078056445075400c160004030204040024400c1800700030100390b40280903002c0d65100f4a0f0007000c041c0d09420011482c48840c01d00c82c02d282c2c11204007888114050300b1001c0440d024040510801842203418000801c00070440c1280104c071003000d980266251501d030f164500d0301c4c00454101c1d8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 931427464 1250 931426214 931426241
    0x102070e0601050a080c0904060803040806011a040902090312041502160f060804030c05060c03070e0f010206360a050f070803030604110702090c0903071d0a02131d040303 75
    0x214100003482e60000c0445005450070310f005102c50703170703040c4010075140035540410781e02c2414501c00040518002020f801901c02c15420b8900e00e9070303120210042c60400b0800d501c00400140400c000030905540503250445025051700d8028404008209150b03003c0c2d0062000c0281d40301d91411400d6040100b158240000c008103c3e11034102203e6104604045c4202d404021912001404041c4140c3c0f40c1e002e4190b020003220f01c1d80c00c08151002c80b03034000300c5103400024510078841041e403030180b4000c200c2c0e01d01a009021561140c501e801c0d4800c9a0000c2c0684030400c0612070f000d040d03000b52507120b07104181d00103080b00380d00c00d2402c80e0603d0b540c88882201980020820700440d240841180d400c90402c07200042d5100041c002100e613401098006903000c4071810401c0070200400c0c0082401c0c0301c046007620815915141010304002c000e0f907a803504540543e0000380314100c680e00620b45805450440a07006659018980301c40e154040d020300820086002e100070590940900d805600c140d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 931428714 1250 931427464 931427489
    0x13090609060b03060d0204050702150403050a110a211106040b01050405250f110d0906030f090c050d1407060e01021e0c01180f0f030b0603010903051209071211010207 73
    0x11200045c40304140c0d240c0648541d40d02da01260340c16008204103020001c174071a40481034901420f015129801240c20034010034144880c0841004000c1a40400c180d4428152080c418042802c540300c4e41d00c03510600c1c2480f98000d01500b5178002001894415403089103480d106d9070509080c401920400b41000580c142c00d441c0700e295815a008840c01015072510f4202c94811961004480001d10324007aa80c07140116425104280e6100800e04161800ca80b4140440510051600201c0c0d101e144050310250700d0340300903c05450500c4594140d14003a6a103442d018030035400315800c0203086d5000402040c0f5000715072801e940c05012400c1e4070080702040040c01081e04c4100d80c3c903079545180c11810000d99408101014910b40000805056110003281c1c040c0d07140c0c0341c920404003ea020680b41c070f070000380001303035149814001c070100594160b0342c0c54107102031080d80840541014100300c4040c0210440852905c3c0714404c000c22640c014149206905009070003e42440c03625040041d04518 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 931429964 1250 931428714 931428721
    0x3050601052115090a0605040b1e100b1605030c060f15010915022a03100213150219201813170403050a0b010909050a0f0813090609060b03 61
    0x7048881100100f0701e8425400d55404041a0900703d036030000400041c9070901f8803003842680418940f0800302201100e0042200400e180074041e0215039140e511800000140300c00c1810304c0142103a000214101e030180c4075150f640c181180c100c6003945500d90f019400300607100b149941c1d83d541010110100e0740c004600d210000300051001d01036912009645000402d006108106400362805501e40764030603800c1c2030480e917860030701c0742140324070910900680901101091085900035100041151000392803c1809602070034031542520550007180385441c0c00a4410320884c14141c4500001c00e8002001c1402c1403055445982c01401907100642410b0110002103404d038010103440010412407606250400084a00a603804a1010b01060020801c40b001800880c81407103800d40c2c04060ba203800406045508014016103164000195a8081402d821040e4025402240e906207058441103030f0105500c1a0741c4100011030341c0f81c50401c030381001445040060020000c1c101d00d90704 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 931431214 1250 931429964 931430029
    0x10020415020d0c08030105012006091c0206010e070c080c010509010501030606090915020d092004321009050702100501080a031409180a0c0e0a0303020d0807180305060105 75
    0x814021f60b4180290300e28030700309060200d091416005280d6045440910b04921031030307101d120080b070700b0354640c08102c440c500e02400480e401b030586811803140000c0350396462040385c5915015809030740250f0b0410190744140c4081c044c60b40324140e0103001298a52561410304111a200d41c0421103441c074000501c0b0014099100510a41c15540405602c0c0d030030804502004001308030303000f404010000d0b04d89902070480e25520310003d00440c0e007084880c440d50395400f00d0b090b03403e5410b801e107a912180c0c40001112400d0241d048108000c11007181900c45030054100c031b2050340c0d04405680b04170341d0000c007071000d8040c441c050300c000c0e0301030702c545003182d6006000030240d00d4070241c0000d000b05102140761103100e82d101581e00440d50700305150605038071010040c001c0c00d500b8000180f4899483c581408c02426000480fa49580205502844004101c40001c80541418104520384101e2039600b8500c100d000c0155010310003070020355140c00100054244460341202c083c0d08408100039111 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 931432464 1250 931431214 931431217
    0x60f0906130201020f1911060301080d0c031209030c170a1b021801170709060b0304020d0c05030304150e0411041703041d04050d03090b1810020415020d0c08 69
    0x40c1c0c4103078000301000a100507400c110300380d003070300041b441175460f0718060039420408900e616008640c86540d1001e00c1c0103004161100740521991356020404244490f4418000c1d5400340e4040d181600c5503180160304602507030402081903000a250503c501d043c40401c0207047d2545841604507450210560740141a00032155051001d01d804040543c0035516015410100995400300301c0e1561740c0c58103100c140c00e01c0e1304032021172507118452000c249002d05229120030750703100003600f504580d525401c101d80c1c20300000701240e415008071000a415182000504040e1040156611101e90200030052000307500171009407042d4201401402c0c96102001118250f910301030603e410a6a2030014030700e10310650b8082070b2503150442823507070000c1c910308046024038802c0007990820b905602040f01540c2e01504050010b42514002c107410a0b101035a400b042420041901c1c0c125040004d031a0403030300503622401402da0030080040340c00b0703810302c640d41808000d42881103000c2e08580301c07408dc6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 931433714 1250 931432464 931432471
    0x1b030813060905030f190e09061203160605060f0f0f010c0c18020d0f140f1e04050304050f0105030f192a090b1c0f020f030406060305060f0906 63
    0x40d081000d096005211440c0c11031260390760803000700c03603549000e414880051342c0300444582c1c600c2c1d190103081660a204200c0d840c101c26004112800310f440364010000031241807018600e8920040001c0d07900c1c40d510051030009140110400280ca02e0071f5014427015443c4003034154464899080c0b48180340d9580c80341d840c03440e03d007860032000318070041c0303807054107004603400546c91a40c8000e8042000074154004240c00c84c0c501500707200070f0410502c0c0c1829501c030036140b248044814800140400b000c101c8042d4423500c0b011480c82c50300c184c00030400042c0d4041d1405e41700754100040511160510640495600c1003e10340b05141d440c0040645100700320140003548000300e030303011036014042c403500700741e0309800d100c414162440d5483c2c161080400001c0342080202d8840680083c0c499290410b40d84038070782d5810f00328000c4140726036910040410b50303560211030b9820b02c110000d00d81c440010f103114910483c000502c080c19030a02c907140001c0140b20f01a0300ca045002c01400140100e0050340 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 931434964 1250 931433714 931433731
    0x3040e0f041a0910060f082518050f060a05090a020304170d050a05060a06120b0a3609030912030e031f050105040b010e061602130504031b0308 63
    0x1151100d18250036180e80d00c2c410301010030320581c107028841001103000041d550409408002160b03565840300100103840c0304e030703a50b95000583d80401d4026103107500c584500441c4024108140c41d441d00c0c0152080c9095148905941c0d0004c01031111300c0118020f4214404845984030107151a00091810000600c0d00c0480794011000c01e01300300f5500400718011510700746140d290301d0040003241c01041c0c1110703036082c2e1505290108285061200c51081554459a181d80810380010800800340c02c1480780282c2116021500141c00d010784118003080810101c0c801454502820440d08920443e0034102c4d03030706140c0038284000a80081421003107403105000301e01094200d09003514010012152584c0500905216420718240d03a00c14500d0781807101ca0400031030340c8500c00d100031100c50002041c08124152030784026490440c028200d01920080c0001d05010707640d000c1617005800140c000303103080d100c909010416420407144080303010780a9a440401c0b07041c2d140100005005000c082 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 931436214 1250 931434964 931434991
    0x9060c07110303070308160c0302031611060a031d010203010f03060902010e031b03010c0c0210050f070c0902030a060504180605070c1b0e01080a120e0d050105090c011103040e 77
    0x1410041d1801d00c941202800030b080c0c035150b107000c0c2000703011103000b00c90352180c4195051000c484a80121829101c20b60503030b00035820401002c0101502552103101950240d2030620552010740d100c0c00205689050390b5400308902d800103650081140541040141c180d00500061041c90b034043e050101300c0b90444404a4114098001a181414491000354260044170010b0020b00c1220020001200054008105281d010032007151503440d0040001e50001603218400045446000a00900a801c00009251020302c0e540d481d80c0741040c3d40003001d420b0b0040f042044110142c421800203140981d42403108110f4030194543e0102107110003030407280c3d2038001c50031242c0706030750081a9903401820712a20461200c16008071550350b1003001001a2101c0022410440216400e02407540c059040d40c0090b29003141540d82400354905180c121096860550109400b4003800e4011f00c0002c0141402034030303103400104a0501030307009003001e5000304010414042d00c1d500c9503a2010040b41d002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 931437464 1250 931436214 931436227
    0xc090103090f210801121e0510091106250c050d1a130f17041a04030b0a0c09090c1446030f0f1401080d080f040b0414060703090c05030609060c 63
    0x10091047c64440a0003503c0350a07842c0012228560004424038011003000400361600420007007a031196160300c10130640360307950680d0f0715500103d080070900e1003850741711402034880d004151b0b40c003a00041990b6201a408004a5508086021075041084005141d80c086101d8907002c0c240303007025400506644100e8050b01c00300301c20f982500c0c003800041014400401042071248600d070000d00080d40e8040f924804620009078610406402886980b5880810340c600b03840940108042040c2105003c25201e101a003002d0060003000c0c0d80201d580041210881c401d01079140e8460100308080b468000d000a9840180c10101c0c50914070b910700d07010030080d91039030325480035110003040301c44540d09100d0a1100c0c0700314a00444e06036242d11301102c3e0140400c4808075440741cad00b9103035007a03900c600d10049804554903c030416849801010401002084088114503002084030024002569021020108203100282c403008290450017441203040c98842a030300c0300700c054003404400c03000007640e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 931438714 1250 931437464 931437503
    0x9030c15091e0501020f01051302060c03210108160b0d15030f0b0118060b092106090106050a0b0c0334060b040e0102070b0c090103090f21080112 64
    0x6801a007100038400c228102a82c4400c0b028501d02d000b0640035000c0c1c0f0010041c01c020510a0500c5400c550543c0381140340b01c1c1c0c0030b21250368000340c410380c0c42d400301b00302030400c0300710320b21080c034811505038545036607585460a0541400800e40c580c80d03e0007213040040040c2000381050381c0706a00b10320030009144200c0444041d440c905940300400900a0440b094248a01620340d81d04030303500a2005001c0003071040c40c03c02114140e000350390700b2f04002d10500400b81441c041640700f146e440307650994100400c0c1880351615030b046582c1903050b91030700e40500288c10b0554125004000d400c072868240b41c0f015580603101e00420071031441102c1c1c2d91070070034004584032401c0070b030040300e1000000d6041c0032818540064039400401c24051400c040042c0c050040502c200d0b480f094100b40c0114054a0f0700640d080181e100307420440c10183ca8103600d0000c5292202200c1d440c0340304034100789902d00d07004054407082d026012818140100716004016044410840c8188140c5c80722003141c005045025 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 931439964 1250 931438714 931438727
    0x1106031807090f06080609030d230a0504020f0103091a0619140103050105010e0607020f01111b0306060303160b060301090b01080a15020301120201030e010b100c0b0709030c15 77
    0x40d52081032042001c0000e50709840c0d03211140b00c01d0720140c14808152130320200c5075203150a6404141c01d500401610103403ca45074094400c60360559030a4807000c0c0700a81000c0143c0c42640e40c1d260070340e40d8500340300c21880e2200381e01d100b220080c2428400440e541d00c1311340ae0038043e04160b042c20001240012429070f55658000c2084d03252000300b00d4010349800c22050001d20402206012034039000006c1507540c0a032400d000d007a44c00411081c40e0a4050303091001140c910841d080c1403008502081c2c0343c000f02030100023804184002c845900d200c0d048100743c50603101a0400d4080e4000300900d42d0184280907156010981003200e802c0707540c4801c00424010b080440c0041c0c003800c0c8800011400c00000f0a8400c1254041d000d81c0a41600c0c0c216098100c2c030081c8200c50500d4121941c000040d40070b50040b02c10940000c0000540080100c00b245030707541c9810b84d103070008004480382d00812100c002015040701c1a031600440b80d900316510341e4000300490003000e0b07400c030300c000c2c1c4000418451603 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 931441214 1250 931439964 931440001
    0xb0c0a050102071401060605040b032818060b0612061521063c010203160b0421080c071110021011090a03060b0112050c040f0e04110603 60
    0x200840d9900040c0c100201e60302d01303c0c03104d403c0d00d508050300001c00d24840c1050f5015030f80444011840c54440e806480b200e00600c041200803482540c46184000c8050301c110241002142c1038200b04406901e000d404070703003288000e184078450034003c403004139000c1400c4a601600640e400410189085100b0700c490144410f840100002c019142000c86c00e200d849600074801510003074540d010000116400c4c249000c41d4620095001d03c400240c01c11001000450201c10300650345041c03880070521550030300c0c8200c15207808844000340020460000c10301003003c002009404c40e00250200002e1030040d02825003240a0b001181540510605203a2525213130780081000c0391021407508060349900004204000c150710704008021300003000e4080394840c280060503400e84a045940d604014031641907414108001d0020403400c6800c07034440c09018240250b90b06489924090b81020a40003039042448071a00d40404d110000d0891101410151011078207940c40c0d50340d40303050119503441c44 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 931442464 1250 931441214 931441223
    0x40f08040906050117042f0a09060806060a08030301050108040c0e0906190923031213051b010c150f0c030905060105010c08030a0e160b0912160b0c0a 66
    0x30300015000c110394001011101d00303032140072032400000e5421308150380445000c0c28880c1d404401c1c403201e4040f4142c10001c0c010302003100c102200e0403008a840d80c0510740019040c5981c41c0c00901044804000241d4813040c21620b0ba40c419050401c0c56860b400b06202e600d050001200c0854104aa000b59190240c49500300f01301c12854190350b00380c0d0760801075503001148802d007000031503c010203000f405031b00c5400c4440c1042c1503c04410855110001c0324140c0b07070703d01040c41401042e20502d887d160041c801d18804601c0b0b1000e07428414205035111402e0b4408200ca807076442000d9801000044010b03400c580c07c01988019102e458025000204c00102c44500d4034001c0a41660141d0000400305d0181c0211041a84c90b8401500c01044000015204d99030520003c0c142001c25044000c03809042406d6130440034000c81100c0100030160000054004081132010150900c07100c8054500a080c0c002c1049010350401c00300706421600131880c0c03803000010004c69414080151542c0740340d10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 931443714 1250 931442464 931442467
    0x210405060c060a060906140d050c0d03020f07060906090605070609080a0c140d0c02060f0720132702060c03071a071e030c2f01060806010f060503040f08 67
    0x140a00300ba15560111660700d00140380c10701c0030a802c02c00c2e204403010f0b2503c0e807002c42401c000c0d5104000c0c04081680e0115082c2c807640d80002c0da1611070006100c58079110341c0080c14580d000f00105810042c3c3d58020300100850a0005c0205da940100702c0c408442c2141000c5950700346600740000640b20064018040560020341035400503400300300c03010064040d96802c0c020010580b200c6842d0700c4552500c0002070328200065001d45000d100030034548154000d110301c1c10720749988002a18a030050001d041003052420301c152410210349088155400990801644803001980f00d01040d50038000c01c02c109040c1d4992045444031400c50b440c070b54004045a40b5414145012090000409541007000c07420202161409000d8540d04032401e100d81a496400500307000203c0080505005400400405601c02515002028034551015180c241409a40c001e010401c03400e4500c19400322001d84e0281004120401c10340c140003050354468505035549841d070b4200b4110380001030502401c5040e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 931444964 1250 931443714 931443727
    0x4151e0509070e030a242a0c050322030c06030b04110a080f0c0d05010e0106020f0303160c0c0504051e1501050712110714131e110c2409060921040506 66
    0x1074100000780c03403010b80b2007600c04a20900c600300c48c0c1c0800c00030000d003658070170b111000c008207100001100e02c16081c002c180825940c1e032690390a40c0421b51000d00403d964046150341402d01e0b0048a2201042c0900c5074030b044484d003402009410010407204944036010045900c5120ba042180c0400d4040c500500403035848080c100400202841440007500c110a480601c001010095a100702605e12003240c103141c0102d070980c0c82c6040d40004503825190101d000c82d00f9070351807003214000d0500100e003c00903500b07200d11131908107000d007051082c8400d41c9000b0409030303801801c46484075800381e00c0314080801104182c07020b50107084d1109050042c800007040e5083d9688000c80c440104407082100e00c4950300501c41180d035405d0b4105500d50f011100c120100801d9004040d0b00b0a42184191405070003d24041c28407035404071031240954a0b890031102d4213568504070f0380000316140a0702407800e1030f400c4e613981d80000d0080640c2100f87c4003960821707020301c0d400340c60082c0380c040c040c15a80d01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 931446214 1250 931444964 931444991
    0x15090c010804050c0904111008010512010c140702030c06070b0a05010504050c09010e0a1d07080f0c0a03150e1e010b09100f030905060f012402070504151e0509070e030a24 75
    0x80b0300b402f0701030107081e4801c042d4040070b00500402c41e1840c1c1548a04034510403c185d20000c40e8030201003a80c051103034610070429519240002d0405602400c0302c211107042c015045030581c3c0040e880a44034500304014401d40c2e0591000301c4a100e142400c141c3c216007008000b1807146055940603098a00c47c5c10f03e0011544080302e1503501c5404599a8035a407540c84490700d02c501d5106607040000c081c01403021041c00e6000e40d000318000c005604c03a09015607582c03401d21084560480c0c10302003c000e820300406280b460240071901414a92107a42c1c10840d1240121320b41d1141801910100183c4602d6109003a029134806000e25810605444191405032101d407030f241001e200f8080004c15983d90110b10702110070140340c43d0100355001d000300300d1030507042001a00c108000c0b070000c0281040c0019405c2e4950200311403040248075521000c614100410a0000c0c0042c166003c0c0100c0201c0b0b50041d07940400e0550f8820307030040c00b030032805240c07660340e0082400c2c503000c00c0c1c0940d10703122289030841e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 931447464 1250 931446214 931446227
    0x905070603021902060123060c0d231801080402060f0a020a210c140312100603060806100e040618060b09070e2d0315090c010804050c09041110 63
    0x1540c5602c1d480c1c410f21084508a0740c9003402d100b040040924000c0311800124100e8424070099401440542403102601e002420b1160b541d280c013000c47e05201031081c440003c0180500f4401e00100e409040640000d48034400c000c40b185541d04200d1400f000404640d0b6090030f885070a05650b40b45c07515045500d00107541c45415407001d5410061034804100964450b5211805d10641507441418184141d6261096446050b02960740da020030f12008407a25205040d40e4840c00856208080551601c84094100c1e080e035002010070f13420400405c1070b5030302104916001c03907801e0201d201c165a82c5040c0f03d0010450f1107880c82018101304620300500130f0941160b0004182203a42c4480c42c0c850b01720555941040f46411070704030b600c0980a072508542c1c4c008440c0c0460400200e100c46001a000080c201014141c0003100c0d40c90b50300502005070410013509a082000f030a0010082c1401e0312460fa032030b80480c20356845641d01c0c000040c10801340c8103c40f6446072021701400d04d060242c003005000f1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 931448714 1250 931447464 931447477
    0x2206030506130204060f03110d11091908030708090a120b092e09021212070302010c050708040b070c03062c0604031704110a0e24030c13090507060302 66
    0xc09aa50b8070200058441c400c0b6801c48203903896031809001e904034158050072100c00e045014080c00d02c0301042d0800c46008051044142182e19591a4084030410003c8041d4808079509080182c0090201d59000802c5030b00c040d80220845894580303100006510036500e810107800d62080d141544200100114141d008240b10300941d0107613680216559280c0c0c81c250003041040c565960303550b40202c0c4a90052084900180038280810005000c0502d4450025452040c0b15030020b4210300741507081c89078200c04844c500c0c0c49480e0030703095202c001035402140201500e60324009035403410024095060401164098014030818005008a2041111000d04508103140d0101000740069010822520907039050f1296130000002070303042c0903241c9000b44121180076011400030780a640300881c2c10018040f1003155071062900d03140c0750050000b098080f80044800700340c1d04025603008202d45c00b5840c0c3c19070300c03500503031024a181400341508000140c400c0c0030320803012810380d80c5500240503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 931449964 1250 931448714 931448719
    0x30408030a2d0e120a050d020c0306160e012a0c0911120c1b0f2416030e012c070506130302060f0c01150314120d022206030506 56
    0x20100350a0050300d501c8489118010010f003400f104000d85183c512444e0010300c200300121000d90445503201d6182c000548103000c0503902034800d10000746010130003d580941111600044000074000180005e602c10703074a20f0610600e6254203903400080d40c5d18912546c0320703424560003c8901d0400c0088420940900740304a07040036102d10864007982d00721600d0003014190250155a0389100301e100b47c0144001050702c140b0142015120042085181c80e2030042402078501036100c0701c0e0061120b60b9000041441010400800070806040da0204a841d11141404a044804090703940d004000e001152400401110521000d101c1511400116500700380211a00c440d12070041041500486440403020b15004405000606000020744140c030500d042c40e609180302074110380c1c25105c141101e6035890282c103030100148182002503180f110b00d148050203014a017245d00b00340c82e1040300d10964481b600081c603030354040598403041c02e0b090494104404000e0b240c075001405454107460707091 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 931451214 1250 931449964 931450007
    0x9040f1b05150901140d060503030f13050a0503031209010b060a05070606050d150e1207060209010306051f0e151209070602010c1d191203031d0a0311030408030a 71
    0xb036400c500d140c102c0c2c042410584a008101c0c0d407581d0701040e10741c05002c000000a03207036a07000445450820260080d5590050030302e4980c0200000c5800740b400c140d010620402080c24100040e450202c2100c0d841c84090005070240e07602e5283d480e000d450744220050700040005074a0004c2d60703200c2c0191442074800c00c003e1104565070b008000001203a044080d0145560700000080b0b00b81960000c850b80e0302800546407002d540103160b42d000e412818041e00c1c89500054000d07510b41e8148601400307000110f030800c80d070300807114244401c0c01180f0029018001404d4602c1e0055485c508284010304400d2901ca80e214104440004280015030b861176482c800c10b580428114010301a01c0425510b1790344a88200348034061103044103e0b10280103401c404c000c24080914192848400050212020000c0e6140403e01c6e00800300e42d0b2a0544443c940d4039400c10342604613011442d4952550585060120415000080303070940c80356620410991100040031104260044000703241c1c3c142a03041d48 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 931452464 1250 931451214 931451239
    0x60a0312031a040e0706050a0908070612231302010e09100f06140f03130203010c020c0a06030b061e0d051003021203190f0210050f0402040e071409040f1b05 69
    0x4804d4030081a404889600000410700c000c1c0e110b20080c0091024524001e12081d03582c100340760411240e40c02c10340005018001007060180305001e000c04060068009454801038030340922540c10002c0c222101510b2040644410341e031207451140014400200401003030300b01840300c032038003d4451194001b000d185040000305940070b0380c001c01c020080001d480c0e2802c02c4000342080c5952000305520304a800440740940940c07000d12408581c010160014400761900c17a04111403125143d000804050030184455059201c0700c05981003008a07020205a90008070544080c81c040d0703000d64441d05150001f00010008941940c034110b0b4021b0b0f650711140c0a8030301170b107610b030f10803403407000c40050010445c48039443c4621880703400d020301031060365403940300311000d0000d036007058840d840c00801e4103081c4030175807a1a104503186140d1000091104a14001105081505200006200f10041d00004051024401b015450369a08c040c14802d000340e11055502161100d0040038011004403811 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 931453714 1250 931452464 931452469
    0x50a060e0606190f111933020c010902150702010e040c080403180801020a030204082b350f0f070c15060b040b0c010b0307050d0605060a0312031a 64
    0x301c60480c01001940f6400301c1e02034000303460402c0e1502c441c104118440c0507014a10105012802d900548003500b06801000c3e400e01e00d82e00f65002d0000c0c481004d40064a00e0600d07401c1e261603a60500c220409601c0da4085181a0300400c04440080d4020022086a03055165440c00800b0083c1c801d80380c66403100001428042181c1c00c800b0084081a54000030502090007a190148900c100310070000200d503c80b001982a0b800003000540880c1e00460248a517190a005503522189226442034441180000d4101401211900c0702d040c400c07000b4420544829442070594803171000e104810280c00c058170725031100b100131901c046c0c07824101b0022803942c02283c3c142c3c5010741d00c513603110340c10010f40751541d621400051480302c8500795101f50019400b038407107003d04018005000c20b1501d42c0700759120356094614a014552180d0403ca4041c0000d559003050000c01c3c81e00248001421380e41d800c04034051401680000d00482840510f011900e0380c950032041415031010050b810301d1400500307 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 931454964 1250 931453714 931453717
    0x60c0706150302090a090204090213021215010f1202090a0b030a150b0315030a05150105011101050f07050a020c120706180e0c0a02070e10030210020c01020715030b04050a060e0606 79
    0xc004c1d03002e0f480402140c07050000350017800c0d082d0300080000840003c2c80d03002072802800c3c11800340700703241c010035441d11107802c80c80281e9121010a041c101c48508400c0000c11148a091084040c01500c100f803800f070408643c1034441513280501003140380e40d164401c0c9403068001301c8a82481a003880c5d190301aa0520b212548211104050241c0c20740e150700c1c021200008c100081203405200380500a40441d1007003112901c080081c40701d4100035410301e0001401000d101d40c410407180c8c1800f0900441d004c50003002035000c1200d140c1640c0f00c02c80100124203140080551076031050303142d08021105240850031404450740b9495420180c039080c1c04806041000d40306440704c0355400d41c0000c418015420040144407194811b8459107a120314000603003038002c2d149000200340ca02802c0c07046003000065141c0003605030000f85040e840402c0000c0d9101280c0c007410801e019182007031803211380250070009541c0401003041c0003900c1c0580f000da000f08203905c0341aa03180c480714003180c000c0c01e040c0d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 931456214 1250 931454964 931454969
    0x90312011401020a02040b01050f040b0c07150e0405040804030602070c0905070c020a120311150714180d0303061d16080415050c09060d0516080c04170c03060c070615 73
    0x80144c94050322a03000c200c0207000d01c0050b9810320804000541880b40d100c8010006065050321258440ea10080c400b1716103c0b0b1a0403410030303020011100448285c206040f020092012100031a1585c0c452822035142d00a0740e0004250500201c0c2900400812004040503141c60100030401581c60b039604441c078041402002e0b4000c04064020320000c90302d9883c26011034040e0610799148007001c1c90316490141c58068002001c0c08840500003802d40c01013540c140c014103150410f041c80604180400145c08845140b84260021481c0c0c1e8105806a00414020654070140c50260280c8241d42403d1007000c03140281c1c0b46900d0008010316500aa00b0756001c0c3da00015207078400c61403881801d004001c040d0500f0034041082c014210f080d80c030b6030020080040f1018020800b820000e581441008d091842e000a101c1c800041110b412000d07016101101d400702d4143c03000c43e10301d081132410180300401080e0075001d410204607d18a10000601807075200300010042c1c84140b52000c0581c29850 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 931457464 1250 931456214 931456217
    0xa1b020d0c1103031e07170306060a050703030f0513030215090622080406170a0b130b040e0f07050108010605040e04030327030e0f0102010b061b0a0b090312011401 72
    0xc0320140c00b1820407100030b644403001034222440c0025001010034210354905003003540700e000140c0d40c3c042000b1551381080300c1c3e1b2844599810f40c1001c2d00060940c0c0240c10082040207004242c030350505100b0381000719090035100040080303080030707a60000004030f600c0e02034015206518110b101d040700d0b00e0f011403052180c10054103007510740342505416800007900400541d40c145442d603001c100f10030000c000814a940350100d002c211452138500c0aa00205500c400914003070070103083d612205400004c0c0c940141c1c0014140c41d1480001f00204250380d03543c6407038420080c0024801c40d0006086059881c262030b403480f00c0c1e0b0717508022280707031182e8040d00716614280030121340043d002c0d400c042c003800100c2da0005015910716143c0c407801e050000c020f60000c0d40c100e40b4541176080c8180000600402031000340301100705400030541c00d105d104248a6039040c2c0140a41c0750000511002125070b9020030403085508042485070b60302e81041c1c1045c1609860b00c00000741c0d4401c02c06035801450411b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 931458714 1250 931457464 931457477
    0x105010306050f0a090513080a0512070c02030d03020a182c0106140706091209140607030203041811030f040c05121f18050106080607030b011d01030b06030a1b020d 72
    0x18080171030054400a00002180540f0a02c010b0008196001519940ca02d954501c0d465400381050558000303400317400207081c800d80000d1079000d61400f050781c4940700d4003400c0142c0e4950520b041221004000c0051540c00304090101094000f41100317284421010000f01c6c5105d591180e41200c1644030a100d401b0205038030b06018066070448c0780c0034101c52030190100041d080c8030741d155803052000001800c0001400c1c0788003070110b405d000035503031460581503030240d00b801143e50300070b9580d05c603030f016845011020442401041609411460703006094074030194903402c001091880b0351409a40450740502144004903031030810010b0407100703181100003001c4601000c2c00c00000a9541060f2141031034490441e040039101c0701a8145100d48a40300000b4942d242c15031180c02e06101074012010981020554200741e80e12541c031221241159030001543c903580b000580c0184001851150014400302c10007401c4455980010320200886640540800031648200d846141c800421000b0400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 931459964 1250 931458714 931458719
    0x1514090721060c02010509070b0f0f0c120c0607080109110405010809100e0c190e041202030d0510080d17180a081b07090209030703020f1306080102030105010306050f0a 74
    0x400c1d900500510340a8032122185000351030300c10558014000d10800360791610b060042103101000520014a021144a0308000321805070001c01d06c12146200c6480c132004c40c908070080c0f014030101d001011407042c45070f51007090306a0036442e090225012008030b62a80c00000d403503051801041281d0701842c540c58a07080c01e003801503460700741c00780085c0e646100c1c440411782c1030b0002d0311a80d05210b030110010b0581559000c02c210308030483c00745004101c4400c07002000400861803440d0341190340101d40c0551404802c2041b4954003c2c070901030461418038050110349400f4030034490a80d080303031064031566034280d102520084d10080790b41d800721203044001800303010030001c0c0c845a100040290303420f01000e03440340c105540050605d2858040810341049200d20100072a02c0203102441c0198101000c00e00001d0b107401181c44080c0c003405210f5410000d613911400703040f112002d0680100540780c5c803408594003d400c2405064003081c41d00a0101701c030710340f2201e003004001c0300a042402903030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 931461214 1250 931459964 931459979
    0x1140304030e10091418010501050a020a05010524030a020f090613020c1605190303080c0f03040c0e2206020a0915020307170a020a0314041215140907 66
    0x9000600503400c2000001c0405000da44050070124500410740d2440a42400c15004050031401d04c00e90600c1070446d5800d8038850703500c096110341158800d003005512402c1480c0140d0a00907129070007440b95107403200f04070030b031500140c240040301c030324000080307034022040c0a044e41c078445640d000e5400300c3c0028500c442e62030541d10150307000402609081c0d44083d401c040d80c0c140c0c1c100111041454115030524240084204d03c1c00008240848403864540c0392443c082104200130300010b010002100002511180c604081354421051010b600f540c80c038042c04e01044902c428002c2100c01442d940104680c00364403140340c442600e0301d04074200d1303c4803103a40e854000c0d030048060109121152030000303480302d2050000c0c0c031840d9040e00610342e01c4c1854504021a2900200100c1c901c0006000c8101c2550b03000070f0881c02e0580c18140000000002000010315003d207030b01c98905684001448001c1155142203d088a0300c1f140f818403100e00a250400303081e6204507084107103035001c543e0800808 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 931462464 1250 931461214 931461217
    0x2071a0406020d0e0309040f0507050f0a0314070807020601080f12071e080715020f0708180a0f1d0402030c0d030309060906050108150c090d021503280b0114 69
    0x15110703200c014540390458000b8401c0e0f0f0250340214146800108560307400d424540501d85200d141a10204501d1500440c09001c60007180004e07111040089480d0b20818000d5210346540200f110300da00440c80d08900c000c080507011204200180141400020b50120020711006000c5030704010b40890fa600b8400403103d074000300402c0d104082c880a0750605c0c000b90f00c3d806d042840c000c081c00d55a81c10360b801e064000c034517800800500349204100403080641c131321040d00e44156001440c203036102d810003030240441d405c0c2c800c00c641c0101400000107101405100b004125240031081c0789212244000c00d625140d8101c0d0045e4154000c0c9100400c1441c0c504070407051248241030014180046890752030455540c0901110041e503214014007221004101c6180022001100d84103103203414454082c4902031105664060395030924464210b5568044604d0845000544a512440c1240c1c0394804124251500005d52011001c01014403001c2d005940d12104182c60300c104051390444189480d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 931463714 1250 931462464 931462471
    0x317090705010522090209030d110c010507080d29010c02100818030703021605041e0b0a03171e03090d1209120201051906032d050d030e1002071a 64
    0xe10508116a81114480c0014200030b01703098440181c83c0c1451009262a00d0300c5502c0880038040b00da42c540403900c00015046000311001e281c0300e40c59a005242840b054021416540380c214289041c1c00c051880040f6a1100e071141180c0c04103820b0314107001560540080c40d00a500301c0085408907544900907a2140c1d0003540c0a49003590185108042604503001010101d005810030f2005000070700e04c1140440142408071020400c117013012044100f9040110f0700f01014035121000381000d695040e240d45e00658100e9403c04a0303596000e11607505911003c1c00213800749442c1000b10382941d40b1070170b90b440b0b40307207040040072030b89032030142500d030080240205101c0c15181d1000718005403d1824104c074007081c0760000708890402030210389403403204252118900d031501c5010400300b403214559072041c00d00c0c84d030030040c10b00026950608050110b0009840382c8140606851050350640c081c295465800040e907081c01548801003003030744582c0c036001c2d2003002d01d04107440c0c800348000f400980 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 931464964 1250 931463714 931463737
    0x6021303050a0f05061e0411060910090e18190611040303030507030e0f070b090612160306050d0b0612150106020102090103110a05121003061803170907050105 70
    0x12960390751814076007401100100c400591070094001081000c00920b0782101420030301000d00024440d242140e0540104090048042100d00c41e8040d12040d080f18100e920240c03000001400c4c0400c09019400b080c413541e50018030740e8000481180c90003030b0040043c400640030b056140000c5041071860b06440109660f101d940d801d462a1051030b0100600095101c1d031404070380303403612240c060301f1105074400001c1d1503000b0b50240c240c40b0708007103206e40644440d40841070b00d4500400c0416071f280607000700b15a80901190510001c0e004070240d044814155660a216240e00e51382807148080751940e0040c00302c100030300440c070303149008104040c4400d900380840c0d417080356103101d0840025080e400200540d40c001042122964140500004980d040000301c0c03901d1840c0c000107101d03100b188d00a8104060a81c045059107030031042140007590402e0303041c843d4a840035070b40e211070228100120702080010950019060f01444040c3c07003a55504003070f0800e585003170015681703a40884140e01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 931466214 1250 931464964 931464997
    0x2060708090715030f0507022b180609050a0f14130905011a15030103050a03030b010504030507090c0801061803060b03030705030c0601060e120303310b04020901050a0b070602 77
    0x200103a079600703402e00c0405990f81c04581c20b0b170b088003000c0c101d52020303150754110f4005050300b0030b0740c81088011440784480c030000311100d1014450100c640440f000b06400c2d04d55881030b0005041d540c45083d41d400c0d01c400300c41140703245a0302ca41c81f541000203482800524400107498000f60325150b00c44070700d10700e9021000700b1608210f80c1c4d114210b40522010102c4032100400d42d8100d420000040c0c08c00301010400c80303265506680303e49030b42d110303001001010152103002c0382030641d205405860055901c50200c41c1080d45400d51400a0060020180001803c0b2000005d0b1a48212a0700b5030300700c8a140265512400d5888020141242941664040c070041002100240c400c1006040030450000940010350401e08010403816104e0480b1f031040345010304c216402e04002c07040301c2c0c015030303a101a481004000040d0240c08510304c504010540c00c1c42c04040103011790b452001d80324510840d07400b40c19a890750200640c0002501402800400a001c010009000ca0b4006d01c41000101da000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 931467464 1250 931466214 931466219
    0x108121201150c021c1e0b0a09050c0306092107021c0501022a0f0c0604140d0f1a1b0708030a060e191503110f04061a0c10060303020607080907 63
    0x40d4140302c1c1c5aa1606245c2d005030980f0050108840010381d802103060754201b024101c40c2c80710f01c003400d40540010441565603c464041040400400744e5840d005400e403a6145000c0440c603480d407009801508007503803082d050040030414076044500003a80101904c0b00032040b03a0704e014001c3c4500b00111070643d401c00511a4904102a24050301325003e010726103c2d10401d0710060600d1504d2840c0100c541c0141c00c50340c1c90303548000544042d41c60000320000f0840c0341e100012542c105114016050a0685001900740252084113942d180104004142103403650388140c0244d45040c100d40c00700780c1041c440d600c00100c8071801150040d011a81c0891442c0c2c541d04140c90b4032409489140701461140c64680c3c0410407070007802d0b041c020040205c400e807480c5803540030800c060b0000700c51091461642002c0c45a0300c5a010700c0141c50740207450000850842c09544031507100d00d82000b4240b040d8181c4442035111130080c035060f01c0c1e040e405803400f030301d8102c82a1004000503044098074010080302 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 931468714 1250 931467464 931467469
    0x120305190306082d06040b0117010603081315020d0f050c0c0604080601180b1f0225050a05030307080a0807110303090c040e0606010f140d050f0108121201150c02 71
    0x81c00070703850b0881c000c2c03008544c1004e85155078092080c6502c15411850802c40030500c07a2595904482e01e80340e4075114125030f010180c1c01024103420089c8540404a42c074400803081d940600c084c3e40f102a07540802d100c140c4000c1e130340c410a07408040001980b0a4244c0c0351148120b0280c00a41c0d40c010032034060a640000145603504142c0100c07044d40d10140c0100300a400d0901c1c0750007000c42c00c41c0200022180b13040400c80d0710354510032030b142c120001d403c010003da01c20807000b0246103c0340d4101c032088030f0000081040181500c41c141c85594036000c08255403a011049070441a8080c0b6010710300540c172881600ca1074401001e6800780228036100e0385011030705200852240b02c0340005411440200c000700f004449010b00c8050240d84118200314450f608002074101a402a0818a03004400702000c00d00510818034248901d07400c00042c05508014481701c1360681d0503000503502155024400080b071405540c030003843c2001181d004000120214829145100c2e20313140590304554036801 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 931469964 1250 931468714 931468723
    0x10815010e041419061707031b09022107020f0a020d02011e050c2e09061d03190302030601080412020a0b09030307140405010e13020705061f12030519030608 69
    0x801a09000c0e16584e1400394031282c0c070812014107142c1544a0034074900c8244aa924500f5000043c0600c00070032191420383c012555020060507884000d41d542c0c000e051a01170f03207640e00494130410145010214a250340080f0720b1001c3e44e58103400800041c4040c1d02046821404548103a040c0007000342c466041520920a00388004c0032503c585549000810788136103000030003c03142c100e0658800000101c103100c1034900034031a8200102154802c1141032420082c08110000e021051003c885104400c4010000d031142d5949810801a140c1007050203034240e07c0102c9000f400a0112000100041e010451030a0148954412900c0c00d046540c4c409a8a04090300c000078241e20110030040c000758071000c2e2008c03011106400c01d0400c1d10302000600640c40e158001c03441402d40300c4610514100503410350386641d8025003254424140301d0104146460800ae141c2c041c460988400306402c1d03081e42403032a509501d540c03240c1c50041136502c00d0035001240d803654070405441d158000784142d001c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 931471214 1250 931469964 931469971
    0x912110606130b060910050304050f0c22060b13030201080a0608030901110a0f0605150a080c13090816020a09090c03060209370602010b090a11041d01090b010815010e0414 75
    0x403031f41c030350323034100303030820510700004020840000c1c4e00a80f0400100d84841c040411590078a06011640a0313114051300094074440c1c1081c00102d002168445c05580d0b454150f50031a4003c4c0c0701e041154880c0000b0b81d0503195140103c0300141e10070007041810303502c10000c0201e04030040c0300b50341007202640e0711840034242c1201d064464a03180c0b81031141c401605440500d18410803501c03540c905107072603510381d16191040c1480c2d2003011040300341d54201030b040d0841010b213540104426600c0030004203848203c81c018409a000d041070500200c0c2d81c101a00c1024581c0380c01260340d4620754610342e5110041c0d44509005a0040c0c0640589804500170307409541382c0c8044800d002c0140106503488400c051019801a81168101440d00115072030703002c002ca070404074511011548070303003c80201c5414461548181c00300300034016207040c11700200304a24141c8800700424402e0303800c000011100b1a50584070080310350707250040c0d46080c0d80a521492100100904046410b480070a402c0311350706001c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 931472464 1250 931471214 931471217
    0xc030903080f0d0e010510090e0a0605090105070905032a0a051e0405310606030804080105010f0e07020303071101061a070c12150f0f0912110606130b060910 69
    0x210f00e5500c50b00aa015503020002c0480080026242000d0038621440b0a442401e041969074459103011043c14440c15100310f400ca5014401780c101010940d000b000b048a01d00001144240081034624000c1441e81b80344a8000d040040b5580b410225026480c17001c1d50b1301c1c0d101f85034003000601601c52001d00351009212a1019400820403401c2c0f0003a90001050b00e82d07084d03a00341303100126050000410340001c00b0741c120f0909088442c94094021f0500790000341074154049000141c0b51300542001d410b0700c0312214503c4440b696820240a40c4078182c5014026030014000142c0d1030340720340c0380c0d4000308103040004141e590381c544c0b0b04c1c03841103615001c0329090200010260b090043ea07040f07440007403c00203142c41c103821054a401d2175a040150b50794100ea500c4600843c2028444d8008170070401b4600341c100440c40c003510b0700c002518940e410304000f103004c0000c1d05000603c00300c1e1103407103104042d000070350384004e60543c0c100800b030744050641e02c00c81c01c1c0300b82a543c1d1101c2ca51200c0100a6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 931473714 1250 931472464 931472467
    0x1302090402070609140c060412140f060f010f0605030c0301060509180702011a0f06041809021005030405010c030605030d050f0d020a0c020307080109030c15090213050a060509160c030903080f 84
    0x401805c03402c2521118107907000c1d44003000100100030403240f04030070b01a0041020307007080e40c16902e4582031040114038a24544900700c1482200c1064655103412100280c1c0308080959407580305070b81901040301c0b03941c1032000a000400c88c4a010358028100d1090044c810746240091410340429020181c40d00780050b9515600a13909004d039054803038078900308030b40b440c01d40450400022194031903405441038850700c0090a0f81c10f40e1140d0003400c00194011300c0e004150404520081058104a0b0309480a6003000c0180171100d0080c4180c005681d07014000d0900c1d5101c2c0007050f50a41d1219030b40c0307102e009007000240a03d5082c2c1c0701a081f20142c036515510070303030994010146410740036002425681d00d042102d00c0041c1c2c000703407400d0b07009604c0080c80d1082c131a070747e1040d4010b14004502940040303d44d00d102041c0161580000c4c482e00ca442d20030042d080d2950280600403400310b501104940c403c880041646000f03070f807401c00c1103201f0310709149026266030710b03010141c10141045149800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 931474820 1106 931473714 931473743
    0x40f031404030605061c02150c07080f0303010303110303010f0303031521030216080a0b0a02040b0f04050a09090f0b06030717060919021302090402070609 68
    0x900c5142952aa80e9a04007a0081c060803130b21144912541d1429a41119411002d6204140c0241c042c20030700c8440100485036500a4180d181188503104c07001411130310070440528207082c0e070390107140c0303079450742c94050b002c80b0301c030410440260018001400340c10103400c0c0358401c90760140303000304040488180b0009040b20b1504400603426000b541d030100c1c1420740b04641d0762284a5400c45010881101d41d009000e0640d00506d403094112400b444c020880b40d141d1150098602d0000500e42595182c2c92840b5030f1100048800f00132011504102038074054020f0700040101600500000405641341501204070321802801c0098040202d0035580f030422140c00500703c0e9142860b001c0325009d825544d600c0d000c40742c0000034440c6400c10011403e03080007402074640d018045a1516a001c9021006508041c003141d42155081c0010300100d41c09010382400c80e40241184420000c = true := by decide +kernel

theorem cover : BRFrame.Cov 931294964 931474820 := by
  have h0 := BRFrame.cov_init 931294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 931294964 ≤ n) (h2 : n < 931474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
