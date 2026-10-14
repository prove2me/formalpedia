-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0560
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:26:41.503001+00:00
-- url     : https://prove2.me/submissions/28644f3c-adeb-4749-9d84-90824c55411c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 100539568 ≤ n < 100719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 100540818 1250 100539568 100539589
    0xf0302030604170d020a030603150c0206070c02061b0705090901050903070305092806170c0403061104030b01030309090605061207030b0a08070b0a020d021218010e041b0e 75
    0x3a0040805540d160744802e10001c40141100041400b8003941d1140403890000b400d0fa800e0350759010600c1459860501c09410302d40408440300b9043c8030302d016040d0380c0050901c1e030010403860a082d5020150022600d03500c158200e51141c1d46281c0101480400c000804408440082d60300c2c001c04d40e90070b80014200c0761300740c0b04901160800c00009002c80d10400207400032030700082110508441d62401c41400e207403491a101a00c076250001000722a42203000609040c4000e840404107180c021a51070b020f204a0200504143da00d00841081904580a40d00591390000c07001c1034030b507180e042c0540700103001d00c694210170b41020000319207030403c2c10a0b1522880195200511900c0300e400a90152507000386c001d07044440d404c1c0015115404210130402040a0101540c4e1010382500c001d0820802c00b0005066600402d56011908402d008854054140c20502d4004000501c0101d44041720b00b84066446401d0141c0342c3d0403044a1801c030b1500144a1b1a0310611082250034003401410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 100542068 1250 100540818 100540823
    0xa0203070801230906041d0606030115120b07051b03190302070f11030f07090e010b09040201020712060f0905030d0b04060f052b0506040302070f030b04060e010605040221010f03 78
    0x83c2c84002020f402c04c1c1036900d030014002400400c0300e0b126182c030312100b000c030b120111950350301890621015040a20414202840101810300101d082203030040307c070550818010000a840300000700c1c814801c03800c0d1103001003441d5112401040408415550f0380098443c001e0b1030b250382c1b281000c890f00a04c02c880006610400301507231130003e520386c54866a4040015034060240c649803c560b100180400b2018013907202e00000d0080300e00070311500b1203040c00701c0c16010703600b400c00740700260382c0001e00102190090307071516208149500e00b40c0d000e80030171414201c28030b0030714801c07208119000c0007038a08e01c224902c0410a4210140800003602c02c14416200b80c5560704105001c1d81c1020083d10210300800e00440581d91200c101544a691034900161402c1d0404d50610040550510046004042d0391900c1c1306039905503240d2101c07007500544000c00c002d5540f050580101001e400c10380042800400131925034146240604010040e881050080007100d40040b8040c0c00c043c90741400c1c0da4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 100543318 1250 100542068 100542119
    0x120c030e03012003070207150210061707031707020a12151509020906040302060d02030f100303050d0b01170c0408010c0305130b060a09020d0f11161214030a0203070801 74
    0xf00c29240d116003075407020b040c140840c0a540b80100e00d5000381c0c0203440c580082c1340c1c000d14840e02520380d00700403501941c10045036502d8a600f4480302c00400035001003074035044400e00106218075a82c0c050180711321000290064060a07000a1116140c0d110642460107140c00368581130003003200404407400350041e9909014200d00c20f015050740e5038013801800c0000742942d450141c8a40000c0ca098000c1d180390304143d42c00000700700745022038003d0142c10038034100c04a490b8900750f40d17014059004600a40d05032580e140715590b1a80e2040441602e00241d4114107000b9007402103d02c0c04a038410b0040c00d14039800d1803030002c5014841d101e0f15100b030543c01c1071061149c210b6a280341a050003c0c00c3d403a4450707801180890015070900c010325841004450010f606c611840320349040d40c038501d50880d8100401e0003424104100a040d81a207150b01001e100c80e0804070420a0301c2d10b096a88402c130164901108001609135035500940c090201c40d160a0882e0380c1e280c507080d410390b001564803400d84 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 100544568 1250 100543318 100543361
    0x5060408090307170102031501020f10020f190206070305060d0b0105190b0a0903030f0903020f0f040e031b010b060301180c0c080703030f05150a060e0607120c030e0301 74
    0x2039442010340741c080d000805603100b01d07a41d0b80c4d4560038142c00c91000d00e51130b5400400c0c0060419108400c4042c40d60a00180c041412401900b80e12000c2411111484540004451910f60305100466001c0c60480d0072485180084900084d5140d404484900200e464035001c12007038501805582460b9500516111190f0700704030074450b007442c55100c03015404401520100341145850084c1103082019914100c1d51491828000c00300e091240800e01842088038007400545c40d2040b13000200d0764140d40c0009140c1d40311010034000e20a404502c0070742d00001c280520f42901d4000b101460040301002809007807514005c0020600c4284140c0d4000d0121090403400e0801d80d4021b44948071281c10150701e040c1c015100c2d01500e90040108030300182da500c110301184c95180c400d0350f0304440a08510502d200ea240080b0305205040d003c0e0f2000d214440410400c150755000440e081d2540c0a0500e0582090000019102d501c801101b03d003c81c40e1101d040045d801d0501c982e003a0306200ca12000900d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 100545818 1250 100544568 100544573
    0x31b16051207080f060403081506070f02030709110d1112131a0406060e070e01092d09020a020d030504051005040f050f06070914030c10090f03052404050604 69
    0xc008040120701405000c10000ba402c03003e01c41000e5120000700034000130b04d8240b500512a0700010000551140c0051000540b0388503e403d580342103034000500c2e1101070b95400020314080056100540d420b00f4800111803010005010740320f40c502c407503000c0c000b0b08121a40800e050103402096085218014005440300c5240c0001380e00850040040c1041411310302004149080116000d68005132120f40c1000491000150030360700038910f190442d5140c81040c002040782415103d01c00c1d024101000e208a0300fa90f40000500300011200c0700d940c415603902118020b50061309101015000340c070500c412003070282c0989480f03541e11a0242c840d60404640d108010300300640259940d80094401c84009042006280074005414008040301d1900041c0101002481e0700003d80300e0140322030200326034070000380b045c42103081194100040c008161040340c000038241d1041c02d04c08a00f800c004240100030441a01c1600c88145031007641804e4254880101010b403001465948001c000401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 100547068 1250 100545818 100545829
    0x13260616050714010f021c050403090b030903040902160302010605060301030f02061b010e0705031c080c0d09020a0b03010608010611030306041a03010f060e09011e1a09040302031b1605 81
    0x14601e1056041e000440c609481060845581048001c85c0e554001600f44850036030155040030401d4400c01031100c0c0c40c080d034008004030380611030100200000f0020440040e000d000784d60242520b0041151100c1c043c10101c065902c1581082d00503529041000c0343d2410700108680c1a0380d0400340402c03070f03800c9a60a00065500100d01154411501448500c0042003030286501200680008046260a050803d8240702d80070351401e058280d608000422036800086040e071000d400c1a80710b0b04c2c2c2c80c9a031190001341490f01c1e0300a601001032880400c0203040a00514141c07a8240d80d0a10366a0321132006450000da10380100002d0392080c800205a13181a821104440e2840c18801502066880109080d1030412001c480d03050344407401840303295031804003550300948000080c0402c04082000d508044074800c8188129929003408401e0100141400d07000c54030040c04590103450181002500c80d0400e0003a4003030420481c400031189503000901c54001c603454414192000e00d00000c101 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 100548318 1250 100547068 100547077
    0x1d04060608011b051303020405071106060105041203031505030307050a060e06130204020703020109022d060901051b0f06041103010b010908060601030b0d06090f0506100e04171326061605 82
    0x81e040080d4170002c8016159401068029441900d41c06441e40f003550065003041030040040d810041c0a20040200400f001c040220494042c00d00080303030380c822242c0c05012925904016018407000950104028000800504590140303a08000d400108109261505c005450304041703240080707680310240c94264010402c4510a000020755000151b02041400a4a0b8174031011481f105401c6040300200364004c2500240031108189400c100b100064007600030708840d02003034500c0b142d0400d00050104045140d10003100c049510a28141c94100f600441100f011070095091103801581075000e112000300b5034a482000d04107940c0c40740011030080c6140d002071a030000c1900f01c01c00105205204d00f403800c0340114244507070300c103490038824600600607120100070601090100800701c21051990f401c507500c0386440c004155660388400d0395004454031010740048242c40051906505844000c041203951f011050f4000343d0b07080382d600e503c41105c1c031000e0f084000c0300c1041113a10400061 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 100549568 1250 100548318 100548337
    0x6020604030311130609060e01141b030d24050306070906110325020307230402030402180f07020d09060203030c0703031b0305040606050a080a1b1d04060608011b05 72
    0x20790078131200e420151210a4164000000300340e890605003c0d13540d005410030310380402800c107401c00c8908500c2c2c02070381e446066901401507064903007140c2c0c8501c06000300c42030310100c440103102181d00d0210b00ca031800c1c545401c006680501d003400103454100414410702c211400d4440c1603d542c03038004240c8640591080725000340c0800c10101011103a0103141c200086106014079550700b6003803040c98602841034001402c5004846245007445100c1e214641140805950150b20b90315903201080b21a00d025154902e1804c40380c1c100a04a02120302c024841c011035405c440c0060b6540b0383c151100e40c0c0500400b401600f081001a824081c03a00003440c03114030030b28001502000d444003150709400050001b40000b07845030240001d0001ca4002c04020380401c4440c1c1d03a0305407a0208265a40200110044c070a803001e02d00c481c4003083c0d80c0b0034140240210485020306a00c0807006c030407414411681124000d00e13111000c00c0c06101480f0700101c000314441c084c0c3e031a19055400303031081d0300105100d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 100550818 1250 100549568 100549601
    0x90a050406060206040f050f0a0302071a07020307030f020303040b0d09020a06030e070e100e01060503010801060b09092a030a0209030f0705010e0603040623070314040c06030207020d0c06020609100501060206040303 94
    0xe003d08030000c00c6400b41c9d040c000d6014241e240c4c1840c14090f840d0760840c0500342074074424012100541d0380030500e003049a0b0f01004101c07031b08c011840800d0641c0250b5010140c005004201ca4512a100c0c1d0050701d055482105d00d001c11644420b400d9048a45452507401aa800000c0070310400c1401482643c11026000054125580e01d01190800c40001d0300540c000403800f2004201c13146007401400080c240341c0b401d403402c1c40340b59404152510390050000395040f480071071108400c50b94030003401c543d090f0b205802d81e0380c1c980504250007130f5000c89030990003441440b140701e0042d24086091025113030160340380600d000001c070421210b600003800a035aa242d0350640052155442011714224000350f24400d9400d1810f245e002c3e00310340c130350340d030504202c00010100300001d04684c11a1003a50540e04006880b80715500220704003800316400103203c000840d9000c28170319000101c2c2c610038400101103881c1e00000d00040d13000c1e20340038442c0c240542d01c4240400c000034060f4000b4903260300042103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 100552068 1250 100550818 100550833
    0x90a0603200619050720011707050c0d0206011401080c07020f0111010f06030b0a05070e040e0f12130b0c03070215160c0501030c02010209030c13060f0b090a050406060206040f05 78
    0x1900f0a88140740c18409001c035100151400c01c01c44004c1407030094040f004058000c2000e0b64002800c000301c0780b02d42603140085840000c99a0303000701c082e40c9141a0220486841103003604020b5943c03042800740f6021803482081e4440d040d032240f11b0151060800c102c4050900d8565404e015088505000e828148603d8812081da1414244910030a1a804800109400c1d14508044480c51000f0b0000c1c090b1038105030070084026048000310480c01000c6e079000030b50f14208014103044c100ca40035504914001c0072000700442c40707030344050038030b80740100205000c41d941d03101907450074800c240e0098910f800c18010b00025103404031038400c4000c102e47d459440d1013a101031202d010340000344210f80040107664240700035685442a040109011b000840c40d243c0d4040000e0356a0070f240855a2088100070481404441150007400044c54910320182520351230b43c00c0088690802d03140c4502882d0410400115880d040c050f900480701076801400d0543c036143c5941403811021481910640704146 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 100553318 1250 100552068 100552087
    0x3021515120105040201030506061204032f01021209010e100213030b0f0403020d020105091905120408060108120a0509011d060307030e070f030210080702010b0d11090a06032006 78
    0x804041c90590040000143c0c0d00e850310024040307403001b4000f1401484180881d20038448885c07101e82e04250141170480a90080c00248200703e1041030b039040c85081d07000c02c00d070401c41054018240d00c00054001d00c0650b03450700051401c03200d45000754030701a4011081448841400d50003031031141051070750452015104d841c1e12000030b80031355100c0041032b0300c032040109150341401a100607540510082c8464180403100030380da4008005c0e0100462071002e502410004104001001000203074072440d21981d8548240b030302c60340c0911030740b4002d000d220a0310782c1c04281c42d0103c4010f02e140da1200c0f41020f01881c01150400500c4220404100c05c0c149104181c2e5500800396100366010f55000c074404401460043c149030325030b4400d101e5000030020074401039881c0e09006c01c4c40c03030f550300c0c110003642d448020803405410410390583d040141718410303909020000940b075511441c00d507403402080d04c8490f0100100c0d030740c0d84001b0f03080400c107010740b520043c00846c2500d80d81000402160030991100c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 100554568 1250 100553318 100553329
    0x6050c010b060a09030201020c01080c0406031802120d140a080109020c010e01050109020306040605030a05030409110d0614090705090a050f061201090e0f15070305061f020f1903021515 81
    0x182409004c242800005c008542e810401d000c1d400d8800c1c6031100c000d06180c140e403a102d000354010041030580320504404400b10401c00044030b140c000300035080b8103241c00c102907282c45041c1c0607000001c1c03144680900d82c840c41801c641c1c506000e03a0b6010315907072030401400000c0d044000c02990725503c3d020300c0b808110f024082c4c107000e0708640000590300d041a00802c000c484266214500070b401c100300340e4010078004404d40d4115503d6010210704d48001c0039030900141306554100381d1103850840081650b106185c0024907215054408602e6178a41850955240c0071f204d0700581d11024011003071201e410407911031f001d03400d8007420b02404c000d2889402389a1040903000310403415036039070340001090010000703c050000f0003006007071050141032080301811b2005240c0342c14145c4410104165443d00903d4940303800c0585400d40b50041c1305400251924603102000100e48100c0b0a0744008851350069a15141e905d07800511941100719502c0307400f62401403001f0a050781c403a0f005461078454 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 100555818 1250 100554568 100554577
    0x8011508010e1b07050f011b050906090d020904080403061811120304090e100606080405100506030a1502280c03030f0b03120c060a0c05040905060a09021605060114090106050c010b06 80
    0x901c0252002d804111b107040d003150744004042245184031074551100c1900601155041c01007a00d402c0d81c0c80032094085804140510402900002d000b01004140903003480a401524030a4030288442c0790fa21010320000003551502420500390380485d113040d8034101c0e215084250b25102900d0070959151010812214051800602c540100d030034080843c00a20400340a8051405c0144090500341c5690381c0e68007003030594507042e0340d440e00400c125035000c103e0030700309660000e1101201a8000081d401a400408281038840495954141c40c1366441010224641003559941c210341c00740c0c0c0741100503000c01180c0e4403090395140b0704034000d501e0600c50300590b06809526642d07154208400640b410300000c0018003d01c1c501502003030600d600c6021a021603415282c08521a11888000342003808141d001d100c1c8240700244c49501d200004181c448614015415540c10b47c0c3d0718440141001c29011000358061072010040c803d40d402440030748840811a80005410f045076000b080a81c0d01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 100557068 1250 100555818 100555823
    0x180b0a06030b0102060105040501031101080723040603050a29061204030c0201020d05040b1b0102120f01080d0c0f02190e011d1303140c010f060e010608011508010e1b07 74
    0x71a480350010b596010040280180001c0d14200034a40c5182c0316000c4000319031034030b1b50402c00c0c0c034404182aa442450607a05c03024070401c00c1e0800101c203200b0402c2543c0f1910510340802c1c10000011030203a4184140e8041c1e01300ea802c4d0108080141c0112190a188111899484202480442d9044180600c1d2522951007030319005103980e0140006890503032025009400c00c03000b00000e118144c21710041d05c04403015002c002d405448448c1484d4003a01074004c441d004010b041003008241c000c8030b01014100c4404a00303407482010f242000300d40c1e100451002500b445451036064005080218000c0c008c865104002e02102c1d8941d00070321481d032400e91028616a143c000007555402c0700100840c0c1150840242208203022a035000d0100e0540c901c0c13110b04640046903105107002c0a4118000c00b240700c2204110b8241c41f603644000c2040280203003000140b82000200309002c0d1104440031160709603c45041c02e03842c04c050458a003500a150002d510003012043d80b00000100242c5491031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 100558318 1250 100557068 100557071
    0x20d3801060314100b030a11160201030c020c03031206120706031a1c0609050c06210601020c010c15060e07020a030f0206060a030b09030c12120c090a180b0a0603 71
    0x14503100c0002e054450030014650301d40310301c4041c02800380e0000f0142c003c13140c00d040303c40d49a6450550b600d00910584041e4903606c500042c0c41c0c0344046007002d441040354400d8804000c0c81001030f800726500e401000c02a40c066104110000041c0c41481003c4e41c03040005102d1511110b000d2403141c1086c1e00c4d40e12420109440f40003081403200e0169a1544000080e01c00407801401d255809414034007085000d820700c1e9a80001406004d020b121441807030340c003c1d10381541c0751b8104070b04807141d292201200f50315a07000320100f8129031010031001100a0160b403501e00e6104035451b11440b10390041c44400c2015656840041c403001641d01c240d22540d0150040c03e4481e000d4100500000c9a45038401d0464001c0300c100810381e40d900740c80809998120b210005c0c130b40e45210b091440d622a650f822015031007007014034172480d21490000d00303d805080d0000318041d1034905412105014118140c1c0e03029144100521101c6a820842400c510503100003144070000c0001041c0001000d421180009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 100559568 1250 100558318 100558321
    0xc0f05160911071205071a090d02010501091119050705010606110f0703051e0c030a0c1508010602030d020906090d050106170c0306180709060902030703050c07020d38 73
    0x2201510802d0031070440e0080d42480d00115603503642c0108072243d0448140440415510140031200694030407080c0c0101c04031640341403510340507545048043e40c000040d800c0c40c0021440000c0c40c0a04410085060a4942402c82d00b9904600103210000041c0c1080710500001c03020032002d026141c0101780c035440c0c560903a80e221007001d0030304110f420f0103820f80d88480c0e4104002580020750031501c0c402d0400941d40000649031550420503070f50b0440d17030f052040c403d40400348102202c04034100c41503030800404203180c10380292542e10091043c840540c00a01080040e004aa001010b03541c20050080d8a4140340c0000510911a481c5007034446a64490b41408440303051501200002c8024004013105200340001981d956001004c10502c45c07005601c0d000c540ac2c08020301c1000d048014024440341c0d460750328090094104943c1000080d08050100b2a0904403e040b44e608607005451501040ba441c0c0310080c0010704590032401c2401000c02c3e035a900c005080c902981c14a1401d5032200704e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 100560818 1250 100559568 100559579
    0x30c0f130f0b010e240f090607060506040e060411060711130b030d0e061b010b060d0b03060c04120b0c0f0a05070b0618070f1e032c030a0c0f0516 64
    0x144c0350103803c180d00800740e941d0142852124009000d41090118403441d03039503194201a810107011307109600381c002034003040c06820802d00d600210301c41c82e4180c6041042c0943c1c1110b0340c0d914142a100940184004400e005250405034020b1082a01455020954040c084007080c030481d03602904201d21542c031506068189400d0004d034444081c546800b103100c0701c108001612900c80c007903600c0680140d41c101c0d695030160a4100740c205d410020909070701caa601c550841d0140c04c414880382c0c03090143c90000740015407003400b5101651032022400e41d180449684088484030013800381c404100051041170241c22820004251885071a596180c84009a00c5c1040711100040c01403446201111b5042009006095210f940700c90180f41c1001e10380c0c0c0b0312a05803003000c00144480b070410306d0010302c1507070729070180c2004040c0800c480d12a18505a000024815105107803030300032894004100c81c80406109076201da2100b40035201c0800c1703076500e0390388180ca81040c407031100c3c5021100395000c110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 100562068 1250 100560818 100560827
    0x605011d19080d1806050406030b0a0306110309010605030a0b0402040203061807050a0e0a061b170301141305060a17030f070303150f06050f18031509010c0905030c0f130f0b01 77
    0xe0780040c108011350021300f031002c082c1190041e4041c02c41015030794106c1000320b554003c2450029a0040401c0080a101e000740d06001c4d030046403030086642c03c1002c00125810001030740c4604a07041042400310303440300d608000195001070440e940c407583c840d60f84602200c4a0504a004002c9038482c0c59840d104400080c082124107011188543c02403a010000e064000312540c00845921400d01ca072202107113000101c626400703421400541c4048008141c0c2c92950407500c0320180112020059274554005160513600d00311081c0340c10070480b503420411183c201c070701e8044c41901c0c441a20705107003620600f40301d550030030403040d0002034640f11b0001034000c10140d201c020b072070290000e548a41c18100c1c041c09909c07500e00e0300c102148000402400710a400c08400b8490321004003030f200d0704548100c4c0c055400c2c80c140c4100046520700300041103102c2c0101c0c0c1c3c130011070f5030142c060001d400c0d036841000903da40c0a0341064100d0100581c1c0b0303000b00761601c07451140d22a1914009040001c1000052 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 100563318 1250 100562068 100562087
    0x601180f09080904020a0207090908041706040c3b07030c02030a0206010b0f041706150a031707030315080a05070603090506160908030c030403060f0605011d19080d 72
    0x10086250081d03a5000c50002001c80d01002010744001d030b0b6521540c20124a88003a5a1004203049d01c2c101605042201c00c0f0700410840d80780800a02c07080e1800b5204646030801605c0061001309540b0341005404a004403440105400d4461680d203990300034a007181c003543c40c4844e103091022200030401001d07014420140c0c0a0420b100560400b00116030180d07840e85d040c0500400028042480b04164403244110bc0241c9030303d02d08614441e070b090407003584d10340043e141076040c1c80d1188101c501d00c0c103225411000316904818801c0407940800542d034402c0e400404103800f00b54803422103c0384004034820300c8009060343c2c0d0003044103010506140382007000c10341004040506000400c030200da0005483d40c1c114955600204018603094020307186010190b00a040138000420700c0030121002101920031607000e10740c00d0148500c032428400c201e81483c0109401304181ea81c0c140a40c04601980d10b28500011742a8600500c060a040d0040181c680c090720403544120400c150f0181e00c9040764 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 100564568 1250 100563318 100563341
    0x31e09080115030f26070b0a0b150d05091014040b0604020703050307081003050d0f0809150106080c0405041802130605150903120f0301290406030914060118 69
    0x1500001d045075109100c1a1040202901c0ca0391400d1908000f00b060f2814041c1100b600d1171314036a5100c0780d2821207010a405c6880e404c0036403030604148140d041455104800842c007090325440d1105010b04034004010140640ca4140310300f13005004403a400d8860303c134089030300d841132501074a070910741807665001c001c2041c3e002e540103000d0b040c000707908101580d40141c0340e81050202d80d5034581d400449a1910343c009403503071043c0c804d1505c190390005150310040409584180060b624221115950124400042038450203000100003032482921030315004180c04916618043d61800041c0139a074020f0081c10045a00700c4d1010300f1031400c4254404054035540044c401d091414000441ca601d0b40350540940010016081a080d50144000103070081c960741c149864040460000f0181e4009024114005050b441c51555803400b04160700400d000c001c13480b0b880c1a003480001c4016141d511412282c0d500c6040340c0c40350715030040c808140a0324070705144003000c00084501310183c2d450b04061 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 100565818 1250 100564568 100564601
    0x90909010c0503010504110903060f01080d051c18060e0c090a15061d04020403050c150c120a0c0b0a09062301140a050910081027031e090801 62
    0x240e00381e2600a0240c1c0d04554080307400180d01d401000c00700040b445182902c80c1d040c0654402c00c40d00b410450302190603661040d048407442c010b026400d66461003400010529002110a0544040940c0c0c011140c00040211062120843c035581e84042d1075a0382100c030f2003504501eaa00600b030800c12401d580c0012001410f1100a940c9824000001c469010706820824400800a01003090605c00c0000b40c4001c1c0c011960b6a9407810125110b1140300310300d07482030300c40549042d40060120b003602e020758601405004a10075000c072880e0154061881030042c00100081d61002c2462099460302c0307614a1103003c21604024a030890880c3d050500c0711484120000300310340b22101e0031743c056056400900a200399004035038001078007484c030f17540002d901980840810056103640340d5440c0440390740101301c0d0700d0740164400d010151145079111503000c1128a0902403450300321545a03811600904040000c07010300383d1910880c044803d040008940110000c1000c40303024401d092400028404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 100567068 1250 100565818 100565831
    0xc0f03051e1b040b03010503060a0203090d1d06040801050f09010c020a08090a0806010b18030c01170406060308030108030c160602030912030c0312060306070903020102060c0d0e01090809090901 85
    0x1d1184291000c0841c16844030319800061501c220040b030080111001c0700c662a20ba03980e440036500310343e1090007070900a02030309001c24003641c0c0394001e51f4040e0403c480900304034071604e4401c8502c1c1045c0c910f4000c41801d00750600400751100802080600301e1440040f65516000d80004201c2d03c0181c034042c1c0981c9071001400c40e0960202c0c02e809900d078401403113907844403080005000c503449501300102c03a000d441d0000509641351001440b0302214045c04507180e0464604054550018100d2540031609008090b001071080e600e0466000344202000142e0944a8a580800d41c0003604004103e03480090422020310081000d41130303041c5046031251b1131908041d0029280d0050001c91405105000611041c2c0c500c1070095a80c90042e02c02241d448090807441403c207124203860300d502070701a40011032480d0348607540381c1c2c0940f501038000f4038854403041c0845c42c03580d014244d500040c0b55141c0d0400d60300344003802030195040c0142c041c25110b004030030820003c000c000e0009140c0d81cac134000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 100568318 1250 100567068 100567081
    0x3090302030c0906130209010207051e0108100e0a0903020102120a0c09121709030307061103011802121626010503011104080c010e0a030b040b010e011203082a0d0c0f0305 75
    0x59034500d43c01e80180540c880e89240700503452b00300c0703a41000740e00c5451040c0c4003402a03140c14a188044200b641c0b030002c261104044000f1366403843c020b004c1948400000110f2900c25034210308103103482840014900040002d8945466070305541c0307601c0080e00d550040010035070102e0f00344090300800494100240b0140e441c0c2e00383ea81d0144d5001ca85540110b410031071980d090043e1205c0d160040700c1800710501c204000c80e039944c4240544334040c001c160a400c060509413098594419400318010460f4a0314141c3c0c0361860034000b44c40c41048445000302c041c002c01d210700c0c19003940c00044400f8140d41060300309400e4a06110240006400900040200341800a403107541c001c020708060b540c185007240031030f12480040c0c1000c1c260340f1480d8240400c00145004c101e0407038038410442e0310141d8807400052042001180b000d0001040d03040031544c2141004035410f00c0c0c00255688030440c1185441d0298541c20020340c030440d03540d940200868083c0c000219094200d141d2408001a24160 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 100569568 1250 100568318 100568329
    0x5041406131214061605180609030f030904050a18060b13020d020304060c0c0218041a070f090608010f1715160306090606050a030e120408010b01030f090b010b07050a0f03090302030c0906 82
    0x1c08507101f251142e0040c54803548400044540e02c4001400352000710810001132540c036440084014043d600e0200043e01144c003034401c5030000c2c01066408290304041d1344918014051100300168800044007000c00f1650b15031000700100190b00601603140c0c81d01342003010440b02c410703200700213103e01c0c0e054980050f665200800d11180c8000b040600c030b0340390340c00d02c01c60b5078010051203d02c640f017032010300c18020741250300d082880f003480da03070b0303035400c80e100c0c401140c03688001c1c03007640081c0d51959001d00100214400b04c59182400c003080720440c0d0300701155008101b10540d800115030303c03550030b051340d00c81d854020600500101d101c180011460213000031b00c01d102b1080117208056480300c0080d0000740901a51050b008003070103080d1256240d8150034024059003800c2c42c0482d180c4280c2c0000710b1a107000303450300141c0002c042c400503840e101c409a50ba82c04010100c3c2d10380a41e40000001a6918202d011200d02030b0b83d88002c41415441410300d4002c0c1c0681903407090b45080108039495a40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 100570818 1250 100569568 100569577
    0x607020306040305161a151807030207110a0e040b0f040302070b0702060d06030b1008010b060306120703060207110405060607050c0f01091208030709050105041406131214061605 78
    0x6142c800da40381d52101071840c1c2850717900002003075401100d079012080480018410700440d0100b1905440b03411140400503030f01512107620201403c508005460603010780e0141598900401c0c40102070012040000d0b00c21509030080340c4004d019800780001c1c810ba14200641c0f0804804543e0000c0c2040c3d213001c0c2d940e1166100320004110001a4001151603040503180350075482c00d002e0120300e03140d01c0c0c01c2041801c111080108080700301030003c0c1d0307804140941303104450064103461442d00c50906105480005014281c0b65104021000000409501c000d1103041d0180032599444502c400801080d11009440140b0980341401644046180401c2c0c2c0324100d00111030440b20401084c4c0187d030005999400320803050514007103001403000100095100300d10950718042155124001510f0a0081c0c0c0542e0415026083d9a92014203100004150b0242c6103a01000d6181c0e070342e220415022114601292041e04000603201403c1040040c43c0e0081180100407031050111b010040c2203014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 100572068 1250 100570818 100570823
    0x212040504050a0b0603071e0c03090b0306030f060108030403020102010c0504081009020f0310050411150a03020a02030d1b020601080d0e0409020f04090305031803030403080403083c0105060702030604 88
    0x2a90404500b0f048004d50040c0180000030307145603140c1c40c000c1740c06040f004040c981207429110f15090304016a119007058042d266064482803074481c18018104480d0300010090782c1c241c41140d00001004004120050007400743c9001141c1c1c0300d046100090079145030200f88403d1060500c0280700d00280841da0074004800503000207082512400015a04003030301400c00c0e011300881c0d04660079400140c001034461402422164034482c28281400859580c03195075081c0c04a050007140001d0348260000d00441c03046104a03400c00460580c01e00440789084801c04000300107464440e0001c1e01800000e00501034100030340820400d02d100501051103c200c1c0d00d01c65039658004404654842c20400f420200103402084104d103030340340240446c0e0080d030b0208120000d03003410034518507000045030301c110f50590b40c136601070700c865406540910b0701414404850300b0906280720300e00c80f098100212202441800030500d40341c41c1c211840480180c100e03d0044c1803c0142d80056140003e20079003155 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 100573318 1250 100572068 100572071
    0x1060905010f0201140c0d0e030c030f07052803110f0601140103091505040b091b0d0203011d06100b04030c030305033309060402130614070506010e0a0c0212040504 72
    0xb41d0040b401422a031004c0c01102200302c051102d2400d901000d000f807400d41800800845001c034605a540c0c2c05140440c081e42d03882000701d4002c0f00904d001409105204004690000300ca14203041c40311001000c5d18000a24201a48001e06600c0920303517442e184148050700c2c0d1110484a1142c071910140181c1d01901c107207000c0c1d40f81c2644a50300150105400c0003c2c074074182c6508075501c2c05041c094a0603a042d85c08500407a80c00100032a412403d590300b041507071410120700c400d12aa8280c2034805a9055585803514100603004030308450860760084080c040928240e20072044000054003c40c07080d072420300050001500c03030181c40c8207a9405007481c41d102d03524441e040001d4041c0e20240311400454102c207005c2103110840e501174000040303032201c4040d80c6000c1030000301c3c042c040429100b800c21540400c02940503200190031100840c0d9001d140080e952521071400e1002c1c1d102c9001141207038204040056148256240841944050700a555440c0348424090140c0c0c0a5030348900d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 100574568 1250 100573318 100573337
    0x1d0312090310060b03040201200c0405100905090d1e1407060e1002070501060603020f091e030a1a09061b0a0306090c03020703080c0c1513140d090902030106090501 72
    0x103039070410580c488038224090a10031662103030100006600181c40c1240491281c0d108140e40500d00f60741c809035078034800e00910700304030180c2c20000a040c001d04019004210200c01244404881c0182e92259815030010800310051180091010742581002d070400521034219152032940400d035105070040400182d615007109040400c010001e10361030b44244c1c8030701100440c440c091030700030f402c2c070a000d00020012250350b00340540a91151148031020000d08000301201454004180400c004c0501102043c0250100102c0d1618605550660b6202581c4408030501459240100e50140f00c10002e0041c0d4107045103a242c410a5148000310f400700c000c5103940c0f409119910603401840b107180c0070722116501601c013500961065030305500207004d040003d5813050f82e00c000c4442c0251410020700c511890400f4400d007056003e40101c0681c001307841e140740403502c614038401401120710040c00c0c44001c0040c2c080c1604e51282d000076410350040c0010009650070003415021030f0021700f0904080c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 100575818 1250 100574568 100574587
    0x30f0c0807030b040302070e060a12030c0b0709030b0c04050102030a050703141306020c030601050f060903030f0d0213120c0501030b06090406090b0109080f120901050c06090109031d0312 82
    0x40900030303048100144078988002040c41480d00c5014040c1d4040c0e001e42d41c940f511005072549030302046030303c81d0f000b0f00b003807008001d006450a048402c10703020780b0b480624950f0654a5940000c000c2d1401000900c90b00300078801d020040011503040141822020f181034505000030303481e80a000c0e507032024003602050500030f2602913030840390350f024404d4a4960343c858038078031426988200d005000061040802901d090b0800103103150594000600891a0440e50700400050340d00041400d0b0b050b0006200c1c3d074040700700041c007a003403900e003441001d030b2208000c0d150500134003800c0d0b1010005426060181d0080307602c3c02000e800341e60003860040741d050390000104403580b264140c0160098601100011840d54607403007103440f032101b60b0350f4614450b0b41e00074150b40c4200c1040c0c0c0d0707003290b0484d0010602c00c142e8500248900601030410504011040c0c3c0d245041070811900345209035154000c42007055407001d01c1700341040d9031000004142400c4404250344088110242070310000c0058200b48 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 100577068 1250 100575818 100575833
    0xa0c020a0215031b030a051503150f07090f0f030311300f030f041103070614090a0f24031803140c010f06291801211d0c010207030f 58
    0x20130108418031956420080900c00082104480003504e003040804a070b00d481c50701190001d80c0580e100131030002926200c481c4512880050052810f0003a2030b40c00044d2451400c0c0c1c0040106650251050300034a103050151101c9107100d085030050708016070b0006030041c080e0080c130b00c1110741200c1d14200c1226170324404141c418598804c841c020088208556011a144498407503031017041700a22866406051555540030343c040c510200700018014a00d8280e084007400d41d80d10000e00d0420555615564a55010321540025030009000243c1240c001070302880131a42403182e1500700040c6200501100e80c41c1e18440c002030400814220340004031400c1d00981381070a4082c8020045a481042044002c085500c02c5c4600c01400740c800c001307103001e4808240c4400600700441843d0040c1d1410a040315030050103e1814060695014410343d0501100380c101c80d004004006002d141c15180c0c01c84410b4030022551882c0d000140e4095103907800314007841201d502200e0928503e0003803030200b2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 100578318 1250 100577068 100577101
    0x504050a09050915011a0304050c0604120615030c06050a02070e090c09060411031303090f0b0301051903020604090906060b0706140901050f0103030c0302240a0c020a021503 76
    0xd92001168602141e060120380c085030189400f0700841d00c0c61140c0c5001c10b03445213000d102e1102040346003045282da0b40c1641c030056900520a030150360104d00041c001601640007a005070504000b44000d500403c0200d1107603418409006820150051039561044480419402107908000703020410031646802000384c903000c0c0203421902001d600d071014840b40e40c0c103008501c452242c8d8001c0080b0341c1e00d040a00c81d0380f40e81b01454441c640f035981c4200c541e40c10116411011010890801d000040804800c003016000c2d000340d6035404da5952410b410090300001d079044036060b60715900c6041006a443ea001c450441d40601d4020a07407020f103090610040c50350364440c410140f400100c2d0320410500b684620035040d001c0d103501d04592116080302e8200c44088404a4041c95541c0060020070301992041070304074403d01c1103c800050302e01108440d4038031800003d402000180c28402c03500d4880c080c1c1310350742080b0310003041201c000340c0000303000344051090056807410000100320114240c030700c070301d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 100579568 1250 100578318 100578329
    0x40819080f040f03200120030c070605090a0506090c101107140312040905060405010e10060509040b180106020d020a0c120314030103030e18010b0a030b0310060303021c02011103010311010504 84
    0x5411284554041c1c040c1601c0c7d000c07401c0030307080a01503542ca00c5480d0141ca000e0302014540342e00704107882d070780c060041c031025106130014400c480d0144002030303041255030700c44c400310f90203090f1421044080c01040346400c1042c0c820300c450030a04881807040064000c08032150310000c007055400c8034010074101a4440c00c0c3c01398062000601141c100d1841c5c0042e0b02442055504010503a6240c4011400310410b88040d0702c0750090a50030483c20744100d000c0c01c1c03c42c90041001407249056400030b070351180c00110000e040e04528004100107134040c4120464050340d400074001d01c1c11641d4582d5450303882e50203810034410103240312109041c0716812040b095080744490654958407814007505031486612141d224240c03d00a040b080392906022038102c4040a0400e03060403103e020540203484118201758061245600380d1241e003219000780b07001180241c029280c07500c09461411843c480c160f000d0425681001000326401080c50304490449070080c01c20300901c110301004896503c41c0e035204 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 100580818 1250 100579568 100579607
    0xe09030a0c06061505070506011502030d0f3902161208090402030c040806070e0609011d0402042309010f051302070501020f0c0c0d080315030106030605040819080f040f03 75
    0x113021140e40280090004501800458540e6070b698060b46038840f600780c03941c1c4016002400f4462410181e03410080180c001d00c5004600300b00a42101d02c2000705501003840440d041448200300064000007079185141c0b00e10142c89081e65000c007922400c0b240340303d080414144882c0e60014400e60809580c90400c0c01481590b036070a140340c400752950003a0041070f43c5801043e0225025500881114802c4003001e04405d0601340140010340300070422a6090810401c1c2c07028020950f0f80d42d1008001802c001038041c0d2198042d000049e004075156483c040c054543c540050040e144c80d891450100c40302200c030501610070703070203544000c0e003c4e101e8002d0031580080b494000d0711040c0c030068200044007804880700390034101d0170031009513608500545888001c0012881081540b90a4200301c0d03000741c00070a260782d0f40d5840408685007190140c88001010070700f0b00006218505982c030180492414a18a091034440d0301845007010f8401045000400303500010580940419483c04000d03507003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 100582068 1250 100580818 100580849
    0x506120106090f0620030c0f010c17060a03060207050a060203090a030e0d110f03010608070906051807080a09030c02120c040501090627020c030715060e09030a0c0606 73
    0x92100088400303024440110b0704440d00820850303200301500045961503034410090340039a044480050080070034a10301760100700490b101c02d5104000090400210a0000a110b801c1e150700400d80e5951040804042c41c0301c00070b0000a90f80c600c20700040e650003d20060b55545940740440c9404031000000340b49a0002c02041414040441d40324000c0b40203480d42401d8280c2101009210304506500618141000c41e04461a0801c110f121030182d6000d400020140d403551001c81ca040d100b03138061040a0380320030042c44182800c55010340d6200c2c15408a00140c103218030050301d02d0f02d00070f000300d81c0c403940c440c04d034000d16103e0307a665081c080e00a40805040300a800c05503884a40410955004030f0425000182d40c029500c145800c80350080c00d12080340400120012803a98160110800e0503001c0c000126191020300041c980e441c4038011206010442c5142e000507101c50350b00c82c85c0b81d0b01107801003001c0808084211440c803612840e1014402c0b81c1450300000400d010b8020720606031100701d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 100583318 1250 100582068 100582087
    0x210020723011d06070b040201090b0c0709060503010606090614040f030f03031d120310030c0e040501060b0306010f030f0e0f010e010501080c0f01050a0e090703021b01050105010e10090506 83
    0xd0052401c2002e03660305030754914500e1052203840ca56845241c01c00000c110f06804651003050264005105140c50b110300c9070766400d2004150000c941c04162a041210b080000381c840d807180780d0041c24207038001c1c070005140c120040c052013500c1c420401072064910360210300c40a0841200e01406403840ca4600082e243d041147c6820b000201c1140824985101d032118000440b80040403010410001c090039142d0985181d01608050314482e00c2031003a02d00800040e2504460802a0004001d801002c0c68241002429101d956010f03036070604c400c2042c0700440c0d0b84190502c0c0100d14a050100d0351480110064000b08080500b03203906002e41c01c0259000c490640007600c200c03c90708001d01a030398071407485030f03181c403c80740f400c43e44540f03900b19000760f550040740600354904d19410040154111000410360b881811204039000130780c00107103040c00c0d02e0700400141400e48400b000308000e6040c40000b9011404404c041f82c0b01e500302c0c01c0c00c0204184503442000181c800a0300d20f603118440c29 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 100584568 1250 100583318 100583369
    0x20604080d090c030605160c0b070c050a020405070806090a0207210e0a090c121e05090a0b0f010f060806030c040f060b070c0f050907120906090206120f07090f0302100207 75
    0x50347c486041820300c0011403a9641f05000034107030f280d00028101401e0300c03130a8082d580301c100c0701c500b22643d0203249a4513000d661117204a900c211090f03290151240b809070100914514000c3c00c00c5101803040c420384000c1a0036058404200c0503080842511098011007541c95048a080c402d5021407102000720b02c0038441e4210000e40c00880d12030038030f001411112103055404440781009003400050320001c404e01c02e5000b1503005403014040d101c1100301ba0305d60440b00342003100c103030400c0c14941e4010030041403202d40801c02000646000b00103800c006002a4440a00800441c450340d01c130301c240304c03101707201c0c0d0720440050a051903841d0b90354003140740002c5060380511074106286d171407400c00500c905000c00110b1007a0000e80d14503d03e2402c0041060051424103c11b13100ca03940e881c450001611100000c0446940e410809501c51030301c80c2054000d028014691401c22602003400c00000c0c00e4400b0940c250b03030b41140e88030164400203104a02e020915031000e140d011001201400780c60a5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 100585818 1250 100584568 100584571
    0x1909050c03060c16110d05030c010209130203040b06010c140106141c02060301120602130308120604110403020105390f0a0b04060b0102070b0307090503011803020604080d090c030605 80
    0x2035042c1d90b5190340d003186a541c18041c203445894600030800c450350001c1c0c1591035000b08424018508240e108039500d0f16851500141e0304c5c3c00590b0f40c000740506581c030700706120400015043c0c43c00c1d8954601a55154503c40c005403241d814085805c90550400c090b000c602d01c074a00c0844020080c590f640c00280841c00d0003032403002e0080c01d400148004090008000b00001a000351126207035910f4010414141a00540182c0d00031340d080c000440001c00f0711840000643c0104041d9451301e410740018110924060035503480307286007088500c000b803404000d40d000c59409082041d100d001c050722810690320704900301c0e8100e420051000000c1240360520034510040300040b00c0c3c1c0106481691381c1e40b842c02400140c081c030030200c0001c001460796009900481c4041c4141c4180320794681042110f0b03001a5066008901b0052040c0021f04003440380c1404141800301718a030240b0151006521881b000d0070207001008000307242d02c10104103400422100b03071300c09400540c03140c0d40d0a01c42c004050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 100587068 1250 100585818 100585843
    0xf0f060e070e1003053a0306060e030f060c130503120406200604060f140411270705160c030606090615020c010509040f020301080f071d0f190905 64
    0x2825010440e12105140b12109580c1c2c03190007014014100710f001031000c1e5044540c134406d8001003030025540881500405034407101c0f6203022601030b081800203000c2c403401030001c0c0d0082d0321140c1081c00340d50340022140e401c5480300c148a540d8150484582610492070703001950923128221004510904400041040340c60710760b83c0200c4044c0040d42c8100c110b1a2000e61400d941c08a004107000c00d8a50744401c142c1800103100084c0030f0840e946185000c0300884060b07a6006c0740f00c01ca11030606080b580300700012410a04611850380142d68054918405040d803000c00c000403d0a9041114407640300c00d600e9042520040c00c2c036030303d161030f03806010240203107118281051000503045a46944102c000d0000b90003a2840990070f9004450542040e603120741d02c903403241d00d02840c44500780300540c060701f80100a8601c100541000c1c0d890701c80b0301d41c0100f18480405280c20400c2e0b20105c0300a0b001070442c443c0e55a140c5070345007030050440f40070b10f20440341d6150414003010440c0000345001c1090 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 100588318 1250 100587068 100587089
    0x303010317030411010f09090f050a0f060503250f030f030315080309150f0412060b010f120e01140903031024030e070b04030507031704120f0f060e07 66
    0x210880c0d07040a040c041910018056103405840c3c64196010b00408441100603141200107156501c10355015541542542d42403180e40c0c20600044060358080c4e41049220f10320180b010314030b8400400e03603d1554510383e017421900504019030607400003854034010803503200101d200603103d0a12061004a001c001c0700464a804181245008200c045d07604503411000038500308088a010300c402900703540480c1c00540410400301055122400143c00600800c00e103103800ca01291400e1400c565001a12030305010040003c50304641d030050041400403c4080d001c81c0800030101d070b83e0b0144c40b0380c0b40000040480d441c108454a000000650b106a40c1c01840726070341542c070111541221a84040142c54102d02c0c891580c0d07a50280d080008103054000456052950300d4075078108540027900211215000300408005004c1d040180480b60581c40074800c0c42c0c40d14040c040c0d0805464044000c1c081e002c0340e0310300e0003031105400b0003189550700300e101031000c811344400b000d4949915015554001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 100589568 1250 100588318 100588343
    0x4121106060a0603021809180709060b1b01020702061c05060907050a0c0c0e09061b0f0406080406090c08030a120e0c0f0a0b0406031b171501050c01050903030103 71
    0x80100262480c0201d901400c2c490006040141c1200a5800318a0005003001418203030203503502e41c94000351242e01041e500d21220080200901d0801d0410f500045985041c100c081c00786881480440302d10454400c03409001d00080b00c0258003902032241e0196014401007594250307007517040c0e50310101000000e01040156111420003400000985005e00010024031918a03498000d581888503580541c52901034141e650031201c64941044440000316004107051000e181d04500b8550103e20f00380d0140e03030500070b46000c5100356000711b201c1c00040059510115040c4195a400000100c2d0403080e4881807a8584400c55500c0c0c0c401280c01c0e002602c1c0c0c48846990311000d00c280d409100e5081c000e8011074035050200210303900e0400c200c40d8400204800052140000e100500083c01152070220780c06001e1f107002741c4203084540d0004180300c2040e0010480040c910103455200c200307038030b140802121000c012189401445041d4000d0340c64903052004141002001d18120ba1160360440d052 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 100590818 1250 100589568 100589597
    0xe06040b100815030f010204080a050c1c031d03030a031a041404021e0d0f0209010611030703080a290a0b0c0d0807030f0603031808031c0509010e01050412 68
    0x40d92000718860000030841804108485410810003803405070003011604070050406542e822a4410f0b44080c856900800c0c80d00200300d400c2c088114074071000c8038000b4101004041d4000050440d00d40201004900e585d08514005e1203000e03005281c402404498441c1070401d0054001c04400718000c40c440b001c2ea44450041ca0a80521085a150340204040c1502d5075070a00041942c2e680350b0310b40c4070300b4240440184d82c41c1d030782d104003100380540a14030340c3c4c00803401404044541a0060030411010715818051100004105c0d503147d50315240c2110303242d0340c04402c1801007840451031655001d0b410080c11103081080541140100300f2140c6c90758155443d904a8103030311800101049070307000040740d86030b494080c2407407550080d2207090102d410401480d0030300403685550422070110b40c000400c04060b01c00541001c2c05000124007e5113005100a8106002e1400a040154040c1c503400040c040f0f08080d0044200760228000a0105040c54940f150640c408010000300068007012441b90 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 100592068 1250 100590818 100590829
    0xd091a0a0c05070f08090603101409070f08070207030507150215011203210504150c0f0509101e0207060f0203040b03010504020307030902150405010e1212030402120102040e06040b 79
    0x340c42aa840b0300b07241014a43d03c900c91a21800b0017074502007803d010b0311040d03441e2031000754825480f44480b420703041c0c10000724041e02455140000d02901f2102c1c1080030b45600106002c51001e07250401d81d503a980ca15104910301025604020820b00072550000750145c000404451440724603004d9400035400ca4104400564003440faa0410001402c04900400c1c0603c42005a81c006e4000c0782802c3e00700b6040c3c0006954090710202d80b4541d03211080d2010700c026200b080ba017525180340580c1d056141180003492402015415445948042614032002d030160802954144010000d110340b00510b1401139221304003803003040045220720500c081c14600c08002c440c10b949041c104241141d00745400d01000f5040208100f090542c0c4a0141000d030351450707020250039291914466949040200050422a4807400c0500030549115100050100454031498441402041c00d4485d80c5034000120395000c84208050954800640420150000c03c0305038883c00060340c083c407484180505000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 100593318 1250 100592068 100592081
    0x605040e07060c05031605030403020f01051305090a140906010501141215010c081801020c0111060a27050a0201021504050d0c170f13080102130e0702030d091a0a 71
    0x10150081903050020b280281c00103a4403030b010f041100e04041e200c200181c4807056440d4295242d0340003107420811480d05825a002140c1d0038600319040001c200c10340800085a405403601c54640d090005044001551203014410020070400155040c6960541d0b00c0f584207001d040c0c00200c08000844648980c0f4040780c01003840d6070340c2c00d03540e81d4821802051030032184503818104003906c100c031008075441d14068000f207444101c10412010000d4006840c010741c2040ba141444040d10200c1180c03500070440030f90222000300b02285494042c8481c28000d80c3c003004614181c0c1c490180e0100380310001501902c560310030780866000d035545204801c0c0b1120100e4008056130f0140d90409030040c400d80c4501d581d5445680305005402c02458203c50342e407c52445c0c0d00003507002103074030b40400c114a060000204003890007140b40c21000d200801503441c050140d680303d108180c0120304894800c004988002c0e00481c0700b0440d040307807880c4c406034005540030b540840301d0520f00440e25200ca42d10488 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 100594568 1250 100593318 100593341
    0x110712050c030d0c030f21020307030b03010c050a051c020313030306090216020d023006060609060901050304030507020406031202150121020d0b0906071209030c1403070f15060504 79
    0x18004c10b10903036040b122195211400c000b0481180c1c0901501030045503214524400d9000141c0c4a1804000040844180141980c8283c0c10701c141c4002d017581100031640070345043e00d03100d0368500d5031070311940c0d588a000a4030010188004100903030800200303001e508052007a40e0503c40e4660360f55500090740100000c1d010301051340c0c035100c1700500d84810506000da2002e44212202c0c5005420344074120884034150010080c4a1140e8090300e105216260744500c085a42a0402400b080802c03403902440b0302d11418008000045000e142c0075105407520907900420501c152034030f0780382030150361185003003a0b00940715052140c00c8211030091024140c1306540394071990382d0740361030b5031440c10a2074100590300503070301203101004100a030b0b0300e091090003070384010030050034800d0000b807004501c050309100c21132400703c40b000000d80c0010391100158100b14400913080e403000881e4110310941000a00e0060005201c0040011361881f00b1048401c080302003100c0f0780d0711814801a55200040c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 100595818 1250 100594568 100594577
    0x608010821090112110c070e01241e020102090f06070f060203070512010e0f0106020303220201090b120f09010b09010e04080408122701120903110712050c030d 70
    0x60020058900d009014030b910145850b0070500c0940340c030801241e42c0b0000c2c201101400050468580c0020080c4c00028400c50784004495032501c4500001c0210340d10a51107803407a5020845040707449500040320059101c0ba24001200e01c94102038000c5d4404020f550003404d140d00d105806240000a4030140380c0c000b443d020717103882c40d691010002c0d800209200240724050000700421506c0000840c041c01d011000401e583c201074080d0040d400b0160311042c2158010000c11620401c820314450310844401c1e80c0740408100c601c01a910444690858918100d010603040210000340e00e1031401100f40190300081c5848551029082e9807504844a4014a098004110840350022041e6104d03028050150401e602c0f01003107800c0c480b804403443c1c00c0030404601102410352204014000e058050002c492036141c81c00041d081401c0c403a02e920456545045410905001e60724618100140310152441c0f10f4458040c01d2001965030000c3e81e00d8400d012910186040000d4801d04014080c0c40703 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 100597068 1250 100595818 100595863
    0xa180212014106060d050c0d0f02181e010507020609060a020601080c0603100303120e0706020f0106080d0c1b050d061d06040809011409060309010606080108 69
    0xe0150158031114a14620365a504800304880d00e00001844214140054505090320358808060030407045071526400718060403d001030b9940384401c88010010101001ca001d640c0c0058028075400340040204840c3d04116000507204000d500030640c1040043c41d21400c06407420500c80c2290018084c0d003080e0708140e030100055030060010342682440104103510b004558004030380d00c1e41046606ca00968410b000510000e00c05220000c07100748207441803401c6250009120101105c0f1344005802d005145c0c02d0300a458150350440d10320340700f0950032145826500c600080d41c2d000302c085400717801d5281070400304400034045a1a42801003950b200620700d01d082d12030101c6d00060105c0c1c0c0f02d0346920500b0000d100d49404100c170030424001d0320300055142980c0200e0b440710350582c910b40d009030018400c01c00003850010903203102420030318040050092041c040707011489a0f0b84010341c403030701c040108036854030f054202005071003440da03421045036650505035584d41c02818817429aa0b40400c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 100598318 1250 100597068 100597073
    0xe0c0102030418060801020403051c0e130504030509090f07110f03031f0e0109050403080a14040b06030703140c12121c0b040c030e07080f030712030e03130306050a18 73
    0x15a80c0c0f140548002000408641e110111402c99005600c21101d41e04000e040050000d0360718000c640c4000c0c2d03400c1c08420300010a0014080e00040e03a2080015591240402c1c281480b40041d200c403004064500038440c01c018088500c1100f040f50400d00103006c200740031303024980105449520700c0111000310f0a648500c00100c1604038502000ca4604003202e40c00141080c0b000c03403881c000c0c21100c0d800105800d00b400e0003008200010903d12403141401556056044c5050003958483e1700b0148491103500d036100040d0901c40150b00142c59480d85400c0300205440110340f48441f03850842d1102001e038942280e054035800c1c0c503804041056414401d4520b108100380102c0340c0c05c032000000041c840301c07031000181101c18a0188000117a5912011a0000c1c42000000040c1408070001c00500d60407a070355694a115007903009000c810303612901c1300000e0090f0086041c400f0080c003a45c1c0c45440c110300806e180403481c48140e0300581072a02180d2070070b4140c8110b1b0010321107245400104211074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 100599568 1250 100598318 100598339
    0x30f04110d1a010b0901050315120703080909100303090b03070216080c0a0603020316030e0a0c0b0309011404020117090f030a0203071a10051509060a09090e0c01020304 74
    0x204140e5a03080011280c681039501c03000c1400c82076201e002d441c166003401d106148050101600080d01c69603080005483d9682c00c4016241c0c028403110011250701241c1000c5004020b110510892500c03d421001c030822030280c020705260042a00c9071009943c41042800c20700c0036512018000c110640401e0010801c504000d50b844078050040710fa4509444210400398007482c1d0114005404c8140100f0b16072030030700f00d00c10050500f0b02e401c1d420350501041600300c6034031030b08443e03042c166603140714403141c8400c4c040684020f41001802c28010380d50541004d5030352044603511003a501c0d200f81e0036140b900c0800454016030b01a55103440ca031900c0d107482a034401018040c04050701c20240c4d201034400d000c100500741011240e000e980c50b9942450300a41d00c003113411800e0800e1460100b0400d56080c050810821240c04072902d50300d24001c4c1e85070345114400e10034030a81100c000110b2804954101300c2180842e840300342d01f002205140c040094550300200805401600208410424078669 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 100600818 1250 100599568 100599571
    0x307080c130905060f011409040902030106090501030303050717010f271505031b0310020a18090501050909010b0108070f0e1c14071415160507031101020d0203030f 72
    0x120909600d8080510300d44003410303031642d0107003010640300c00030441c07079050884142085071020f08000034a16102d06001d1300c54012100b8407800b0315550400d5000355a025000140204241c01c410000c03961203040c001d001c0c1404481c002c004c9048013088600d851540c507180da0403103952944a400050418034448940076004042201005503001904400f4419200303d280a0f00341ea84805615403500c0103040c104059000381801d505069200050707075031000b0980e54440c80d4003c4006941f00c0d8042010303a00c5458505501c400442e001c0c00105003503210381d2089058500c00ca407035400b0f540d00c0d032124509079440501c889000811110208490034050030500450000c2420034a601070308040200301d041c4c2c0900000c005041010b0742c272b00140200314035441c0079050740c0300c0905825800e2840350741840c47c03c0840f09008000489138010219801415960340410585820b041c3d0b441d00c3c14413640e100b1440c00140c680b800d03000f032541c0307080d8000542100c024401d5000b45095075100b441025401c0e00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 100602068 1250 100600818 100600831
    0xa0b010b030402010507320a05060f0703060f15170103030f0c0602090301020d021c05090303010621020a0f0305010602030301050a030b04150c0207060305010e010509010e09010b03070b0a0e15030708 87
    0x24044c260001c3e18200d20034a0340040003a15130303440044040843c8145c40e40c00d44050950b0004c44421002c27440110346543d000c106410800d0b042d071511081200280032990010541d006410800700b0b4048000c07820344400d01a96482c10745441004410300a80c0000b80b00050108406032035442d00e0b03500511541001900440e00141030074050000310b82a6403103c0c103480e6a90398001640c140101201c01c4119280c075608a08002624108810540d6840103000e1102400164841e14034a0600c3c10310805066501e440259126618024060541c044808181e80804d041600100e11648004280d84c101c8600801c1900c050707207543c0340c2d604201406041a101021032aa8000c41003c41d8001c02601d1340da25401851000e20f003460081c00c480041e003006014100b01c000401c440d5862000c010305691254142815588402e0742070390041a00203032054040c050242c001800001c1c0e000900740d08281a00e448001240c0e00c002c2000c00d44005080403554801400800d052901c02e80da802e03031028 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 100603318 1250 100602068 100602077
    0x705070e060901150309141209040f02090d14010b10080105040c0f02060a15230307120f0b07020a020306240906030304270203010816060c020306010e1f15030606020a0b010b03040201 80
    0x192010f40c81405c4c10180c0c2c0c8c02c5c09031007030300003190100c905140c8501c628108051904509200001300010415440d00e1409001e440f441d80c45110355100c20743c0410460400240140c800c48d10310359015000a00920406110320b04c4e0000c1c00006500a04a440c01d19140d64090b2207940d5621103020000d0902d24500c001d03444000c00086800100c601a109045a00002c3c822200c07604604042c40d245d250340000d146880d0079548100014030002c000c0d40610392090303100c140765980c16400ca142884507400070303625200c3c0c0018401d80d41d00041c2c2440e103c0c900d80b03554032900075208080c00010941074031040d415034410001001152065602940c000505903494412400702d0510403091b0780080c0c0160001c2d4010046004106000c8526600100500e01780320074220010740011b600c0301d5052084605031081031001580055081c401c2d00805142100b0380800d440d01e030f8005c044d91102e0040c0441c01f20f0315007403020501d42c0c000100e10f050706900c43d44502c8160300780081103000d0740003d0702c12418803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 100604568 1250 100603318 100603343
    0x2010f0c06020c1b0303040e070509061204030c060f0c0215090c06040f140a1805061201180c08031204060e010902060d020a18050607140c03030705070e060901150309 73
    0x6000e0b40024007500072080002d240d58518140000c800441907603206100b5030041208011040d4016030142c0e04c800c0e036042040c0c0b91a50034003c11a5446100d42c0000811103003820001010340041103100024002e103010012072030002500b1040b610205011000340c1e0114076000d80e0350410b20500c5500403242d005075203400b40f0740004101c00c2d4105820140c64040f150b02c040c01700390080b4a103584c0d0000c0807901c40e440246000342c0c14045940b00208804625103800005d58031b62140c11884a00918801c001c0215200c1c1c0c401000003800d1034502210410040b00b80065401400020350782c40150f8149840c00544540d5a00b030700401002c0e03011100e654035400c0380d00169031190050110300c40226000342e65010402d030014050b00c2d01b0908142d40f0081c4180034041512200141d4000e150f22150b40b00d290f540c48e03581540307020004903001e541031100041c0a020020f01040c04d001b20341072080700280c030740ca0780d200700502101c00f40680d04880200e4011208018485c1d044000220b010301001d2307080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 100605818 1250 100604568 100604573
    0x303090d020a05031e010c08071e090305060a02071106090102060601231c0b010305010803090d02031501030507050a090203090a063b0d030b0d0303110d02030907031109040f02010f0c 80
    0x80060440701015a117041c4c94000c60900b90a014042603201945400e107414038240300c1c0603004000d06080030040811000c1e09190b4240145800400740d6000300071280d4901c1d08066640107940306000448201024400741001030070400c003a9008558141c001d0000c5594142c01150100d03985141588015401410244d07a0001d401c01450003c1d0300040b80303101030b40e04100c0801030300c4100b041c9134105441e2000400480c0008400d4598004003100c0000e10700071680000f0340b5110b082d042d070003210070218000200b04000040d000045403425510003001560301c00c02c900407030101b1100703110a60461144034000403115802024810719034031001040f40b18042030b500d214400c015007441c03101080031400c1c4001d2000c0142c99004000341c5000e02c6010700307803c0441c0c00041044801801c0c1516044100540b9003241d00b9101c2c0300340d003010119240d1504680080c0c4d01c00d0f40788002d45031421984c00c1c0051505148403020301c41c0f0f410a5281e5841030459004450043d0048404400c206035110171400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 100607068 1250 100605818 100605823
    0x10f0e130c03060507031d0a03050c030d050a0e0c0604030c0b07210206040b0c07030507120504080a0309050a0e0c09090a1e06050907180e04051203041a0a0b0303090d020a0503 77
    0x1440c000d101c0000e0910301004050115030300e003492003117025103868484d00c0c07c03500042c0500000d0380c9407a02c80d884810200b0001c0c0b45009030402160300c1410b0904010249406074080f04200c00c1c040300b15020020500309000b0184104e0001416008a841e014041a40080020441a441601c0203413264810b90010308003030b03003401541c2c07005030007810a100910a0594007690848030400040d460644140d90140c41e078490705c03400a20b25038402124180c070074007810a50f80100310710700c02d4802903809840c5c000c01c0705645020311441190f42001c00300d40e044c2e40c0502c2c43c5c880c0041c010a41c9c079102482042202c1c000c4010101c0552a80b1203808407903604204044002c062078040000c580745040000300003404400421103800c12010b25800309215a40d00e00316002c48400c5020380c1041d89403810b1550802c03010030540307a6600c4000041c04100722464843c1d0070640300c11051101c0702d480e54003080050b5403c4001e5103915a02c10300284c102460401400c45a40d440107040042855550011a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 100608318 1250 100607068 100607093
    0x90312020a1514060301050115030b040e0304080d11010204061b0615080d0206060904030806090403050409020a0f020f070b0904150503060f2202010c03080915010e010f050405010f0e13 81
    0xc070860319540361041c070180703d800e455000740007100240706a604004e2044801030356500c40504140d21480c202640b501c44d1b40c40096148520000c1d2540c4680ba01d0000d0780d038805000040002501c403211314241d81e0418420307034040e2181c41d61000b141103081e900c0300b00c400c0c07032103481950340c1d50b43e5901011686d00842042401040c0c0c940c09860b229140c1d2402a0a200b001069140208408402c0000003944141c500b988808201c0d040025a150307420210b03458001c5801c18002c0a1000607034810450300b0507003494040d4503030740c00c840d00358440014442d11071400d07202d030031140342c800d03c1000c409281c181c1260386448ada540180ea2415a1075000a1800009454000a0380c81450500100c6081040003151401503d10355000195803940003c04840c101032000e01040038203808507015850500c504078100c41c0c50384200b50701e0b503162094040404022712840590328181480091075050900800b0304803056103090b44843c43c03900d02c1010284600902c0061150341c1d0280702c0c070001d50f9440e12031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 100609568 1250 100608318 100608353
    0x3240907030617010902092a070809040b031501210602040905010302010f0503040b010612110705070806100e06060a0e0603010b0301030309050a18091112030c0d030606090312020a 79
    0x100351149424543c03402c1842c0798001084690400c50b0010141e120315070a660050703103200620840c61498414625000e100040044d02500001003030300c14000c0301400303042d0000b403c41e410852140c03070404040d52136071071020040707051030031000400c61038249502c911030080d44010000e50404403503440c10101da0082d0042c00100d50784500501c25540d001000300c01ca0740340e038140f079403850600c1d44075854481e2051140c5000c224580c6140b0071444e00c69080030700e07103258201840c0c0e180c0c0e017103141240d125681c1c3e02400f40c0620030040012800200400b442c0116281081e50001d551602d41c00e000b4558003a00215050003080310300851252103040003140280241d200081c0c4a505524004003404503a621107441110458018000c0303850040f034800304001d4900c00010300c4135a9140241c1c0350b120322940145c0c41103400e180082895004001070a0840742c0c82c050f00d4003c020b580c0160100c40f11070166400140d2848002d0000410401c0e50141c400f03a540115804002141d441c04c400b1091007010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 100610818 1250 100609568 100609571
    0x804151b081f060507060506030a1e11040c050a030e0c09040506091902010e06070c0f0602010903030e0304080a02091b0409060510020c2805041805100605060324090703 74
    0x304200c102e41c50b00082e20822200201c241041d1414000070101c0c020004094810750383d0b1408075982e50350406c4082145030384480c402404820380c80038404140388281080da1040764100942d1030500e0b1a206000d01040c85445050800700d00c810200c0c010704c1150b00d19002d902c244450300c610303070342d900ca00750303105502c1000104914a444090641041e23001d0450f489024095200040181c0c0c0142c20722824040668a142d10342c0c5560610320083c01c605d90002c40d85414590740820240d5040d0400d6495900a880500501c903680311210b0740d9110320b20444c41c0315001000b07640d00600d08500c0440e0000315203c0e404c000b0342d62000c1149120345c41a03100611983c0e803040c0801140c02c054420440d499110b00140024408200104a05c03461000700d48812800f103100c042c8511160508003405081c002e0000c01c0005051200d902028100040aa60f9071041da044c3c01c6205602e4000c000c250f03580a00b9071404c50f22890350f07514042c80d0441d081c6400303540e12040c250413070b00c0743c0c180d651081015a50 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 100612068 1250 100610818 100610821
    0xa150215101706090a0303050925090605090f0403030c0c05060a1d011b031d030c072409151101090308010302010306060201020c122506020d11030402010804151b08 72
    0x1070404034030350041a003000c2c6800220030001c0031040401c0142103690076080200317056441000142c1404840d01460018041d9903400f04204008200e003c401d41e0005102004010740310340811144010031628410560706000c000b07000a803003500314503418803580c24030100d20b201070b80c1c03900c1c204071080324070012107940d81c030b082001c41d84400a07609285030800f00800c55025001012549203003160304820038961103040e1851504041c40d600700c1c0518141050742d45600e612400c6688900d601d10a00c045042d250244d90003121940901007401d42c055140c00e520f0902d0b022100300840000c08412050020641d501d0380c401c14207000b070144061103540c48481542c158400034013240d001c0e030003140440e8030500000a030f00d200000c2c00044980081529901c036a001080c1048007202d03107040500d0020b00c484a40d0402500e50090004000100310500007100140c0b4002c3c402d000458020340040d090b02c005c10040b60542e0041d280300399007074502117171102c030078440b140c03d0002d40c00c50304000405610 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 100613318 1250 100612068 100612079
    0x90209010902070b070f0216080601150e06340602070212071208031b0c030304060b01170f1320040f2310081209040c020c0a15021510 59
    0x586160240648200071410400661107a0207168001840401031250590700141040c0c000c0004035803a01c1d24050180c1c3d11600c911115886403420711449200c058a502c1c10081a800f13202600b89580025200d0340c20300c0c89092418a0f0a50031035246449030741c0d00404c0300002c0d05043d18411421740034540260351400c151040c40301d4010104603165450308104d4062080302c021fa4070b0443e01e5900f100b080c2c1e859844100e09030140400408420185000000b204c100302d4a000c4055480b03980109000c00940d00c040700150b40e010101915a0292142500040d00540708420f01c41d4004030480a802c0c0b48083d1680c1300511007008070445014031524004040e103c0c0341c82d00a5203000d0052500c140102e48044104a945080c5486c0715014003600100141c4905021040c280041c68400200c800e482001c14500000c3c0d445000311500640c00c02030414280f50001508a540c040046c03d5203002034501944800b440b036102400304118024601012162441800028083c8004002c0005450b1426 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 100614568 1250 100613318 100613329
    0x705090310091a1b07020609040905070810050f0c180a03060609150b120403051e04170f060a020d0915050901061508070305061f1107090b0a031502040b0408010902 72
    0x1d0b4002140028440b00f008a64850354544d5004541001c2c0119112941d034030008045006010344150050302c2c09050a043c030030001814001c0f58079030f6007500d000036040140c8005481d17040750180c00100316600440c00301810070008001811000d04110b400907080c10010340401884d903c151449602c0d80b40501911245200c0c01000312224180182d49a00d02031200805009211103042a200c0c50000141898090412504980b00c124055000b40c494507422030f00d02d8106008a11024000000d011a51100000c0c9400400514001806e691382c032014203402030340c0040009280355403105941c1000808410317040421144041c00401c09180c410f080d41d0845245074842c2e104002c2010600c20010f820000c0290082090701d0003141c2070382c80e000071070070f0144904808002d00074080304051499a1000910030000c001c2015a5196599114424142e40107c000030340d01080220041001942d440d00ba10035150314102c016041070340c0d90702d0500198029034860740e03c99460b81c40307040461500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 100615818 1250 100614568 100614593
    0x2c01110a061b170105041109190303020d030e1504051c020106031a040f0305090312031302010f0f021f0b0a080708060601020303070e06130513020c01050606030103030c0b070509031009 81
    0x1d074a030071049440003070f6002112000600c240c5001e00c0e50b60b0750725464000108121007103000c0c040c06002c030200b4101e19929505425102c150010b008604100d01c0a51103402070300850202180209410540b25021340b810303441c054001c480300d2040034850348041401d8045501c000c00c6e140c000060040c0ba6007840e1011811403500115034441c46010403001940307031070f44104181d4162400c25240c5008502080c544000040d038004a05404020403803903501101548108a10030385e105180e010f03100105a508400154540000d40c020520084000c0840085607001880b90a400b24040202300d021441039061600500000d41244c01d040c805204104051070b0040f40a200841c51441c10160086c100000c80110510034200000c2500114a2080000300a4400104010404808114242c0c000c0d0b21641d6400481e50901001070720307078504134003602c0c101c03900342d2661b00700e100c4c00e81e4449a6000300185084144007080c001a44c07691010040b03071400b0a1704407800109260182000f0150404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 100617068 1250 100615818 100615871
    0x8010903110703051e010902030718141605070f0210020d0807080606030705090301090209071d0109030503071b030506090102040f0503030304050709111b0601060e012c01110a06 78
    0x2002030200700180b03002030b1174009030024a40c0403c00c081e0b001c0889016003410f09001e9498401d0044c04503042e86441c0140440316a030b20b038100803039100740f00c004400361021a00c0c880030500844406140a000e400280f0009200d1108903d4281c856400110045000034100300143d02c013481255445800c000c44581101c003d0034200d12030f01d8000005078445c803000f841c00d020488042811440b503182500314411107503001b0321000303491030214001803040c040035940c0c2d0980c2c00c10003080011075001b40c070840c0560741c005c000741d4034003445034860403e0143c110b041d41641c4840b1080000c0422000e210a0380583c2d001c50001d40d48a1510710410388c00000c84e0030940c4207810400503c40001d0780065060210398440c00041500e0712801e002c003160b4095640d003c0c00440d2030034100701203107902082c694180c410a464501d9916003200045407101c0c0210f440394500c01101d1100c0a2070701884020003e056014500008028107140c822130034001c0d00402180c0391519031181c0303840d0012a00c0030022a80c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 100618318 1250 100617068 100617073
    0xb0105010e122d06090c28030f08070b040b09010516050901030507051303030c02100203070f0602030c09040f09020f030c060f0f070204060b0408190b150d0c0801090311 74
    0x318000081c50319050040c1118a40070900c020103000400c070544a58002c0000f00241c03a00d600c0e0855403151600c1c98490b840348191007034105c201c42698a40c01c0428003420202c0c0f550203140c216603070b4124440c03e00e00295481e95092042c1e4000800c0182c81c188140c1c8204030780405818181c42d01401c0d64400390481400c006c4000d28240c2c51907000c801d84141990034603001c500341d100c550041c0d07400d100d070524541c0c142040c040c010041c542c0103443d01c4259882a2400814131520a800720303140d00942d880280400c0040428070007003840c43c1c02454000501c40c0380c60f413500700c2c65000902140c400c00e00002400e41c95803610401d5140000145600c000154050499904a00000344031072180b1600d203040080080b03003040320b10030000d0035030b510b84d035000c0c0c41040f18a40b218010740c43c40c0c108d842604540c1c0704041c480410400080958420650300c01e8065100d80c482010b100c84a80c81c9401c0282c025100d84801c07800318491030a400d00501d03a400001945e80c200b8100200b600c5e03080411065280d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 100619568 1250 100618318 100618339
    0x3030908010501050d1101030b041b091a03041b0801020a0804060507090b09040e0a05030c0f070b090d020d06020702090c090102070e060303031f12030947160b0105010e 74
    0x603220404505d50b4942d02c403090b070441600900059000f450003d0060790400d00e0000b10448a107040f844860b42c0300200d80320018110390300c80c1010b0440083e0030502102c88001d0011a002a044203010403c5100c5000084410340d00e40501300d08a0700580d62220000d00031106000c14080503204180d0041c80d00d1800c1d480503414941c000c4494400d10b40300c14055941e866860182c01ea00303004100c0301c40e0f4000c003929540d1a061800c0d9540d440f0b421304131b995602400034001031810002080b541250400350000c8001445902009101c0c0c0e00310f103040e84c90366001c0040c100140c0c1c0b41d41c640c03880b40040320002c0751211003941c00207140480300e8005240d020400400c2c4101c5680000559502030544015130001c40485800300032a00201c1e0310000071304601e003010404050f0440844000d4410b04031401c06c000700c8a00340060742000c140b030701c1015101025070b62550300301a009940c02c501127401d0f0342442d0508080d041d485103070010700140c0d0040720300001800a5039009801c542101001c0f0303201941d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 100620818 1250 100619568 100619579
    0x3030b010314011712031608090d020a0201030c031803031a1518120f010506090c0307050714071701140a050606040902071a040f0309060206010b0a0c060b0409050703030908010501 79
    0x54041c18090a00008413084210390b02d00300802980d0700c6024004072007a100c0c108401c0c032003480b1a02505c2c0e4008122100e0014030500c000080d030b80a80605c03580107140c3c196170b48e00150014581017412130708142d114403039664807030b2040c112400c245200c4da400044401680010645441001007101d1203208007841140e1200c0452007941c1da420f0028405480c0c00150700c002030022690400c9104e600c0c01408a10640184190302103072048006079160042551540c18500852000b1500c480100b4028403159020030a80c4c4946540c0310881030480b465030b40c035103c1310b021552030715000301c1c000ea458559000c00d40c03000660068000d2140d1400348102e00b02900041e440380190300036890500e601241d01818032500340407012071209031999001079407c1c01c2c104144203e0265200f580494080440014454800207055048800d00b0b10800d0610701da21030121400754030540c041c0c461503280d10710704044e6981c03445800865440f500c0181103280c514580a49010425403000c01182d15000c0100031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 100622068 1250 100620818 100620851
    0x20c010807020610210204180b01082a0a050a09091703060a030b070201090c090b010e030c0604060c05070504020d020901090b040312080403051e031b03040f0b1e0a060303030b0103 79
    0x3c1d02e204400c400c1042403404448101e0005c8200041d40c41401c00c20200d820021054103841c2150240074104026a22404296649c455052440e24507060ba425040070480880d040100440380051105100c80e0740c9000048078006107400901c040e50791080460108080e0000b10380403007080c403003458114540170f03000502007a032601c0041c04201031000040c85481c400e500c88107196038010b030350012030b80e150f00c0d01c2c0005140c06000035020520715171500c0704130316001901c1f40f1124001448546403d0138000120351104d540340c0102c840388a001e00118480d690750008e0500460b00c180b00684800502000401c60b541c140d0011491400c10442817022420880e14449a410305003801d240b15156403508035040e00c11500b029929205920a0303c028040e240d0007103016030316000700114180c840788150b114611058a009200a121074480c000017000b14500c035031300c40d1070700400c04142c22a5020807200c1403070032039218024039640c0c10300303008241d094410201810020301e41086955148204c180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 100623318 1250 100622068 100622101
    0xd08040c05010c05030c0a08040512011e0c030209040e060709170a06020a050706021b060105010e0603181207030306210b18030903010903020a020a0918030f03060510020c0108070206 80
    0x141080410190142400010001c680380c1b1140310089074010955807c0c403645640090045078800e4101089084050b141409880903003100140d02e81050310f8a00703030b408000d0885900fa0020f040d024840074000703039a24400c0505040304080600341615114000528882c00368004150a003203041100c50748410021300100c0465010704c005a803503114000039101c600820000810f10760000a070540f5409040c0d070b8003580c0020020031900e440e41c84074011340e050320240d00d00d2a00140c0500009400c1207039607415001c05030301f03002950808130303014190018541c090f400c1030300407a8640c1800c0040c4141c0c01e0300b07603121410700c09011161280c140d0710b10034450009401e0703125900000d003040c8507087c3d09000300d0340320b032000030000c0201d40403030700c0c0194650b0392200c0103074490010302800260130109030241c0f4035416002103072800c0003c0c03284e50681d01d001c0d05044001c100343c2d032000d01060940300c0f88036000710601c83c1d40082010f010407900041011031b000f031020045421030b20620080113030441400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 100624568 1250 100623318 100623329
    0x90201111902120105071413030b07020f0709020406020d080c1b03030919020612060310050a061e0311010503070905090c030a0516141b0607050901090920090f0904060506030d08040c 80
    0x19540e0342c50302235556041e01c040342c001034403040c805d03800d101344960005000310403240500c003600c400c950340341180070803402244100c1c800b60300240210310310303580300d000c060f03900c03030650b000c2c0d5802d01700c42c1c803400582600b00001240382c0d42e04c00802d100d03e80c03008000e4001523000356614007101c03c6080d03002c10014040c0c01048400180700c4004030b41c040d5024010028249188081003004e03150400445000d042540704001c4510400030541c95980f101144c44410780b602300b0040c4040710614001101c80340c2c070040000040007400100842e00ea681d12034a280240403003e21107131281000481c9108598001d040040e07040000c5030a40c4a0350b800010040e240c0025400032038407005401032180c4503400d8420725411034080c0b181000fa61700d8016010340704c1500281da40c0240c00d500d035a04c400c11a2210002d25078401d00240c01d0003034070940c0a0081000e00000f0f002444000e003404041650100147c03811954151210204050f80c04e00b0801450141001d191140c0c42e414161a4129106441c4c000c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 100625818 1250 100624568 100624607
    0xb04180504030e1f0311030c12060a09020a050913020c120c03090402070c080f0a0b22050307050a0303050610050706050a091a010305060a0203150409020111190212010507 75
    0x107000e0600803400080d403040e0207481c007140410100d007907001c00e54641c00014086481d190f84c0324101ca032004240c80c4201c11201020b450002448000c0d00f0b02e400c018500d41c1c0c0401c07800303c0421801e049001030b007140c0c0c102c0d8842d10380782c0c0c108030200b041609004602034015481808080c4003c1030008025017019494003030f480e91000d219030b219007144901000300d60090b000140c504100b040601041040350204000d55022007a400c4c0d0050700ca0304180700c0501074020038008a8dc24a48000f442ea0311400030310f82e1500c425040740d44050650b00f000b007040d0303516003010325075405058050250350f601802c1100c1c000e401014034080900580203440c8058031407940c034800103c04010740e0744140190f0f40c2040e2034060b000c1d020b407050516030209001c1211a030045a010455014003802603900a045c0d94091024103120780003031000500d100d0340140d040bc44002c050810b0900107210b8603c0b41550b11142c0e4481d15010b00600a0ba0040541003038000c5c1c0c5044c00f000210b9034001d000292064642c204d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 100627068 1250 100625818 100625821
    0xd0c030b061201141816170c0a09321306150e03030403020a0302061315050403050c03030c19151a130902090105040906020c100603020102070b041805 66
    0x110014100c408120790000000142165204610380b10141291458030448101c0f480141c1400340710840d1740821480020001c0100f000c444608190b04010700d481d1810000300904403815420b4500191000c1144c032000240110b081d540c412031980103015180d00340c1442ca07824005025241d816009601c202210b404c100b10410340e02c654101e41c01524410301481940e44894500c0140320003071030030001007220308525001904001c0141c804680e001880001b003145903070280480d580c0842e4050300713416604200440c3c50f0200f40b0021006c1100c550742c07503840d41d040d031505c50318002284400c5813007035100307100c0341403500400190044107201103070002c001c201881c9000000d107100040041002030515420b80b070410714510718500c140c84101c0300400b80d10f604200c02c60456407104006508040704034010700c8be03401d09800072a40948540740062400c000d1500c007034100850b400c11280c4013504c0d50000c00966a042000c500a028007112952800340f40458032450b0440c0c0d801c0980a890b120320 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 100628318 1250 100627068 100627091
    0x90d0206042012100605031b060a03020903010b0915031e0d03151a070b0f04230f1b03070609060c1203060801020304061512020603040807020a0f03050303090d0309080d 74
    0x3c01e04280d4005504855007a840420490702070501805402d0183c801c0703404002c01900d0340441d41c0c01d0604040d040619003802c42004030080c0d40701d1103490360903640f1740e013482c001c5840d041ca8052280400384801c0100e0704c0c10307608250509441e074000080d04035669000342c814400106840a2013080b50034005803135044481c2034050544542d128100e041441e00c40380c400241d00310000c001071882070f4291443e582c0c0e511190b400003d0292405270900491594201c5001e21a6417000300c02c18040382128501921003c0013450b00e1806c00e21058a14150000c18101c0c0c10200003610141400d0304210b6041800c10f81c000700304c610021000b03002d8190400108002c64080e51220b8054002c0f14029540d03440d0a0070880045c201416095450900e1200001602003000d007041e400d45030700070426480d41c2c0319610307032044a4102e110266072024000b600020041007051105008501c200302554591070505d6249052003907100ea62000e150400080d81c0000d003200044071200304481030000340d8031103000f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 100629568 1250 100628318 100628329
    0x1501050909070803070302070602060105100f0c08041806090c02030a0c030e190b180a0503070504091e052802221b030207020307090b010824040212090d02060420 71
    0x90748003d41c01e010029a45082c187d0109841050700c0490b001c960a80e6680c205001400008800322000150915403106c4143d12038182409064003440c0c4403804c0540781c0a020a2004c0400f0959800983d07645017008502c9207070044480c0c4400ca0300203542008601c0d58044e1020141c00d00c000d08114010a081040341d071240203496000c03001070202e05000761140e1201410743e0000c942d120040320305000c1e081d142c0c5407665250f42512000750143c1078880c54042888054041c00d08201c403003074980d4070b0103000c007444c0c1508a0a40c0380100300428140c0300494203400b911244203221a01d26103005907840143e11000e41203080140022070362004201d03180e00700d030014501458102c00c1460414018240c03994590007514009000f102a140c1240e5560340c014110340148110f01c1c0882d0079030380003480886000b5422508505005606405081500d0000d0308a03440020505821060401800b4240e0310800220486941e540010659414152144480321030001007120814000603000c0a0507101d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 100630818 1250 100629568 100629583
    0x10302030a12170f0414010c12020a171303090803090907111603080301171f02090d08070b040c15080411150c0a030e01021605010305150d0f0201030e1501050909 71
    0x108408109030914080c461200202505d080d40e242c6103142c0f00044c4018184501130070035000f40c644070040030354484550003a41014840d8801d02494660b16041212006c084520030020002c3e00f0031004201e280107805c1806a4108440c02e0b842400881807548500b070030386400c0f00083c00d1800243c3d101c0301c0c0e10703890015103048007120320080f002c0000070440940085c505907074140d440208101d048607a026942e2003081d82c110f54046450502c503140c0c428542c0200711059010b46251901e030641d44901074513078040c83c411510f004000c0204401d00951128a1010304006c50f807243c40084000401002203001410103411000242c071610503ea46129242c1c0b07140c0d6481c40055201da080c8a409034484107440c10a070f01107880c03101c11010b15803001c600b0f003240b02d0814040d030f4199420680114010540200001d541c8050302e0f14a07031055a6042500000900c01c5101010706846840010306030361181c000f013142540005000300c0c000f83e4001034141540c0d0305070360886881c5c2e030300030078580703800035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 100632068 1250 100630818 100630847
    0xc09030109030804060f090b04020d02030a0515070201150e040318090c0201020702030106080c030a08032a070c060914040e15040812060a121101110d050a020114010302030a12 77
    0x703004461000c1580158000388160b014180800a00700680a44401d403078040b000103220303e045400040041c0f41140060281a0010b0308442001000d991450f140000c85403410050440040c1040f1000394240982030b1052610350000403071520340380808280e8080a00010180314034070002001402c01081c269008040c1d04509000d981050800a4001d5001d00b5043e0301a5003006d81c01b003115140007610042a2001900402c1680b020b80c455a069400150280e044454882e085140c210031a00c25602e41d0340002c12282e655800074548500a0480b96000c1c0c0c00b408090304042103040c1c8480c000103880b40d400d8a011890824000c040b41c02c0030180180b401c0505584000d2000b440140005004582d91034072842c0b0103502c0c4c0200700000361049100306030700c80e03010741c540000194500389103901c41e5070181032403040c00407031014207400c0a030394965040015501045001d01c0e20b44c240207240d8400c1405480781215419600401d031501c1d615071001c0d021400c08040740e0006445010545040d14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 100633318 1250 100632068 100632071
    0x608011a0a050d05130204050705042909090a0f050138040603090318090e0d030b0618040e06010e1005040b060d0c051209030403061b1718030409050108070b0a0504030b0c090301 78
    0xc4d00e002c3c01703050364111f4021003103842c04664492220350b40c4cc841151030a0b50841246051107030820030000d50380d03402032445070040e449142c007a407035031031a0203818040c0158541c4008600d0018114154401184c4c4080c02c90380c000c1c1c2406034164680703030300b154180d42e414503010445c03e40c94181501c102d0181904c038000034940e40030015600240740c1c03000c905c0c050820284c41300d4458400301141610510482e1582c05a010051460742c2401c4a6000c840d290700a00080348140308568907a05150090340400d6000880c1020860100300784401c2c20f02401046a08011000085021441c680224284007101685c0c030900c0f0f000140c011000d88182000d5201d03640541d2030315040494a0760043e11003260840d0405003440003d81800d551030215903250f1b602d000301003a190344030540c100c03009000c4400e4a4420005800c1c05001803000b8805802c51003030110b4a94505685c6a24009070359105442c803032011f0040114090384001150212500114501d985480d210030f241b8242c4a1a1401581036 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 100634568 1250 100633318 100633321
    0x503060604170c0a0b040e06011d100807080a11030604050c090307080307050d0e060d0519090c150207030201050d0c02030409060806150a180e010902030102040608011a0a050d0513020405 82
    0x302d00c00602c00c20f04000c1541c0821075641c2e1a9460300d690b02543c083e42d41d2003140c00d4001601948a412213045410708080350504200c4504085034441301a8400c1c0c80005515508219802c0c1e040b990107500841d02100400411400c0d40d4a40c4440c08041c01683c0f1031610f9502140044c902e0105442c5507000040540e81c07190b50b516102c5503a42c4c0032100c1240c20380a10344d00039051a0081410703503480d10028146615252034080d101006040090521001e0107080700f071340d07500d4030311841646080c5119a040f1545d45e400c029164034248240c615400855101500a10060340e21078107903905848009000300d0401004c2c40e040c1e0860181c2d421071050149040c00010321040c0020390607014004003010703294a0303015082400004181405941c0303000c00060843e031a08040c40c0e001200950564000003020101980000d09a900070750084e00002d4901c1c0042c400031020210000c010b0081c203072214940703103e0704000360190040c044030020079682d071000194500c152500b2003804550041c07040005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 100635818 1250 100634568 100634609
    0x8060f090706090b0f071a1008060601050a05130b040f0f0504180f260a0e01030e1e0102070c08150c070507091e0606020303070e121b010c06050705040e061f0503060604 74
    0x13054044030b965006d0148c840e800200c1d03c1c00851100d0148406075102803405407800420349141d40300e0360300c166100b00382c01e000045485c0b008003e000680304024103030007803600e000841c69405846401c040c0c8228075101c00007038145480c450000c0704503031198400c3c44410b45422311000b003440521200c080c030b6514070b03100e8100c10310706001082c2c180c103c0e846c1c204002003030300011402c64040401c4c441180d4892003c582d2254481505100a010028005481c0c0443c0f5643e4103000c082030341c40f569140e031025103410f07008502c500300113900c00c1c1c0b080d0b842810204161581581c541040c42101035881c0c0d06c1c0340240490666000d10030f13184010020038842aa540d0790000d550350300c12a081b10000381201d551201c02d1822140c003030b40d0011020300414071701c000c0b0190740200d4446440e4a905029041010100041c5940a051700c2079a650b240d0300d031518a000c815070749100e402800e80e8498a0095414406d41c680b00d0183c0b01e05219501d0001d85a65414010071814800d81d000300b008250200e015590 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 100637068 1250 100635818 100635863
    0xd0c0309030324050103110f070f031b080405040504080d0c090302010305011401052215091404050408160201021014010302031c05220f08060f090706090b0f07 70
    0x50688281e0b01004000002d28841005070120000f184007052079a4042240b98801d401903030154452607140d501d0251071810052056000d03410441d40c151108448406050300441d0417066800da00d103042c092801656142001d9105031702480c1d1003943d6442c045410b1040710300989a55000445d0100a04854844042c004160910040380020b05000001c0307900f006d0782c1055141c490040c0c503210700303100c400500208200a5402c07824070003803c00d20001008004218400e2540c4184e07107802900034100b0118411103001484410b00850401040c032000a048604441c001c07500005c03900e0001c1c02c5440102d081c17602580c083c003600c0f4207200c0b0340061020890318407412648200d04a4200c4040341030b00b102900c0c40c501c05500894002e0016442003045080440741c0e41c0c004207442c1c81c4407500c40c0034010100c032180c0c02440e0305610000c00c0004600380600103e0300640b0820050035958074116004142c0c0704070340686c0c8542200810036255604000e0142c48546920090b40c0202403201d150024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 100638318 1250 100637068 100637081
    0xc03041d100603020901140d0912090f06020a030504030813030b0a2a0203090d031704030e040e0a0b0105040c0306080706050304021e0315190515040b03070803070201140d0c03 77
    0x640001c100c0400041141c003034802c813040043c041c0c480c600c0b0000b4103a071040351a002405500c0665844000c9680064094a540c44102880c3c2c3c582101490518007850b0072030105070448400d56000158100c08030741c01c40162002c490303203c4465940e60030101c84280d45011035500041c140030060301801041c202a4201c8031034000c2030105007008815018040c8001c001003400880560003c200900103400d008560311181c034040e084c10103a51071320103c1000d10640071181503000030f54086d10071156140c280100e680b003503001d000a00c40350089803901c3c45c10174010300c83e592150b40d0341c2c60b8403150640290040c0c402020001d0a84074226903449001d0324a03441105d00300e214004d180340d2003403035401400c3c00310500e04000c3c0040c900b035031101102c1c2d00c581c0d00c040c240701e2034006808265401708155000b4180310382c005141c0040c00c640d40d00c0500c4161190610110701ca600105003e000c004000800e0b64185902441c04c280030f242d01780c0309440144242c3c803082503036a0905551b0480c06030183c0250 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 100639568 1250 100638318 100638331
    0x3020309010216140603060319030302030f060619080601090801020c030a030b0919020906070f12020f07030b0a0203150907170c0703081f0801090506010f090b03060106050c03041d 79
    0x25084607a0f00d04100c0d012a50900412071a03140048080c030003070030190065a40312101404940001803106540c0c1c0700005408001c40000740c00004102151814111150f0440320030f60b400c0b810140d05209a04051003146035000c20050350740c0002c0c4a0340e02c03680340c540051a2080085641d42541440503480b54011200440401d082100c1d52201e070810315142481500c1d04401c1d81d051059403030398034002c0c2d404502001c0d1700080600213a00401c40300800c100185206502d0741c03402c101c402402078100407202c0e9036000c45800c0000100301180c10380c44045e0b17001c4a080001a074a642d034080185040b04141101f03908040500104291941c0201d034511211140072100040b80d030300c5200c044000d200d29200140041c0030300005c183c02d505144007001d194079445d20321204d40b6072144891800c6400c948419201d030b0748114010400000d5102c1110b000d008503410a00245250401103079440806100b031031308000780010f440300d00b203405000b514084e18006000b0769080ea12107040810b401400c1d24030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 100640818 1250 100639568 100639573
    0x212010501020a02100e01030605090a0c02010e01050c071707120f080a020f090d0c030503030c071b050a0b03070908030310030201030b0d0201081302060702060f0c1b01020a02090a0b040504030203090102 89
    0x20540d580005048005994020000070b900c0002200865805039098801c0e41070540712032010a6643c1c4484007244140e0706201d000074060000300c2c0c001e0a445010b0440c0b0220391420b0b0074014003407200021510b103150030942c02e2549044500442065100c0d040d400341910042880f0000c05c0d9500009a07400d01c1056031f155a043d403110208402248568400301e4800801000940c00c21b040c600241e00c0c0300c40c0500080c03441c850f900e44400c0d04650049806483c10034000888030100300700c0016681c5005504081d0054040c24000440c01d06840b5000e10040d609002c000150100d10440342d000c00740444078240c82c2c40f8200451500482c40482c0012070200e0f0511108400b1420030311984100d441d016950300d1101c2e03c4411a0b01e0381c0540d5904140e0700300900300014805038a035100246501d18603c0d01c400e54915400300301c10b040c2210440c103238040390300f0303c242100140e030300080350410b9680454000c14540c407020041030003032a19400706900281003001300b105058000c070141110035401c0e000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 100642068 1250 100640818 100640821
    0x12020a0c17070608060609030a050f010c03090206030105010804150e0c01090905040b0114010c0c0e100b040f03021c1209030204110f0d0c02030903060c030109140601050307030e1905010212 83
    0x960849000504030790041503801040108040d91045000320780150380900070a1410113079102103400e05503881000d641a920058401c0e0902c6024170031840f00d00420329003040101d48550000703c00c2c2c4810301c20316040141c60000700742440021092407841882c0c500d010400520071098a039280c140f04d40c04140441c0c0407903c006007046907401114420b1b80c0c40642c42c11142e00308408203c403400b40c014021304100c400d06031040015a00e0700d006011740159500003d040c5400200445650310640004000410500c002c0160a00186116080d41d40c116081e007409001100c8070480d8814286010f041a140c4440d074484a0f600710020704182c034001e49040c021018900300340d240600c00c11507849488001040780ea42ca61a107507001c4009200c5030302c1074910b41100742c0000707403401800b078800c045481c1d40040100600109449405003075412002039101c0c62415000103841400000c0059080c140c45000b8058422014480e501d203d0110542da281100154180302d4004e40011500038074a9111a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 100643318 1250 100642068 100642079
    0x1206030d0c0213051b070c05040b01020f0a083007030b0303090117060d05010c0f02010b090c0a0305060a0305070b090301050901052a12010b0a0201050a0c09050f010c12020a0c 77
    0x1541aa50790041c000040b01208890703e400180001041d04160011540302c0102c0382518000402080e40100c541c01741c41400c00007044220b4010300e0702c46055510800005d07220030300124580400c0358021144580701c0103003648240f4083c07210403d40320782c1c2e402e01124105031031840d0500c80c00f40704550b41c01c0040020040a05a8a01c07406103141d011400c154041111210703801c01042c3c1c0180c000c2c002e80d602c2c20007943c49600303503480c1180c2c45000c2540c2940c1c0110300c540c24460b058011500710383d10785590814007000006031290100100030951076030b00250032611010390700d1000716440804c40317441ca55a00c000c60320306c5d001000510300c65400c1401040460314140141c50182088200c4006517102d5424010f82c0780000c64a0a9049001031040444649040c40c040c2d009156070840240e039001d07107410090031224020300a402903480c1c81040804942e201042000741c80b8107135844180b42003d10016030f40400300e110020001c0084030141c8102990110782c01200170301c6401350400c0903031103d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 100644568 1250 100643318 100643327
    0x115141308010534030902120601060807020a030503130501020732070f05040c12090f02040c0206310f0602130501093002030f070f090216080c121206030d 68
    0x6515203210040c1a044c0081402820038811440b00d00b11308000410642c0c0d030307000c240b80100e0601c90300d01d40d0308120010070500d600300041c02d5016007248003420401515581c080c040d0700003e00908144842c5101c0c174003c00201f54110f6140c02c0d0440c0030000c003030b2216030300c041070b02c40001381141505640c001191200c241c0099000d00366080010440700300741c1400244402054a016002c003040000c03040f40741c0d12141c502c964070005000e00740c0750146d05114014441607500c4007242804642c00002000420145c41c08040204001d808484c4001c40110065400c00007800c0406015004980150401c00000da0300803c3c10900100012141c03035500c80054806c00c0203481100c1c000d07a00f1440c21a0a541c82c80e008003000004105108034110342900481d1a05144000e4511282c4c00751400740445a42c1601038001081d40e02e8056190117100140b042105504110041c0154000300e4044002c242c24001c660700700c100c0300360450b11a44001d4031500c506a00717440e854007a009402d41140184c2c4036 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 100645818 1250 100644568 100644601
    0x80d2405030312060d0b01030807110a05010c1104020f0a02010e0c0109030b07030902040f0c0203090310060803090108180f15060603071b030306230406050901050901151413080105 79
    0x1d0195041c4903044545924408000300b90503480301c400c3c17101c600010a0214070038061405071a0041c1c4465441c40d2100490140241c0103116985c2d541d02040b070707030b0f0b030000d01c4c511400e0b40041c4161002840401241c080c0c05200240d40002401003140c03500d86605511603002c040c40d010032600d0151410005640c09002400082c06d0003016000103083c903802a0081c4201c58405800042c02105101850040b034110b29404001a0000034160341030307290802280f803e802c00030308200110b5140045295880c459a82041e042c0043d200001c2c141146540c0841605609001500c103900f1500c580c07141c0340c12503d038a40d1045180000854480d0500b2000c0d20f100708803a480c0da4240100c501c00380003403034803d00c00440070151151400710f102e808480021900d82070720b80907a034042c555001000162910342d08418011001080104031f1a41d8041c5100e0440d0580c0003051142c0921382800c40d100d01074018642d82408000074850800d083c3c0d06c01c2a01161481402081640c46400d91101c00240 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 100647068 1250 100645818 100645829
    0x1d0405040302120a11031201050405062d120d0503040309080606011209050c030109080408070503010209060f1b0a0f0b24010810051c0b09030a020d030b0d080d24 71
    0xc81403120440b500d0390001e02d201c1030203040812020b0303175a07502c3d249154072202c0c01c0014011240010000c40c240f034001e10340c100408448102c1081c0700e0134001c001100703c00c032030710508482c0034030308036855101d8154695404c0c1a080a0b22904e14400c14003402c10fa2003510214002500814001a0948082501c600a00d0305950785072100362140c03a680e0142100c60310a441501030120b061445030303000d01c564a01d4a2060310f0711034450789040311640c202801948107600903401040410b140e41d440700100c60000221120250702c030f40515014100b01041c2c116017440610810a1090074800b0004c40c0030810383c0b00741c00074400e40d40c84d9810300d240d5100d584e0341e40d888445c070814003000301d602601c1c0d05544900c0140c0060001c0c2d44d95030010750124680f106030302c11405011070a0040c01803079001c440e400307090381c00114545035603010025130392425038500b034003010369842c0000440e540312841500c1150308034172000d4442d41c0f1611090000e002480c0c80c0080400b18140300c03519901040141c008561 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 100648318 1250 100647068 100647073
    0x306021801090e012616050a060e03030f031302030303040609060b0a080c010c05011b05040e0105101b050a0f140c120703140a08070f0309050117010b0703020f0d1d0405040302 77
    0x2440d042041d00d9a11544070506171440e0a40100c400e085010007106110844030554880480c0c03410781031004051268120604200b0105802c100da03803000000ca42d007038518807460640d079a44044000500e4060220001d5141c00000300744401e00241ea046000341030302802082092403900b80801584550504c18001d0750f410883c1aa440e56000b21205d884050080e000030904405036812084124000000701c80801d80210b0b0a0005103840214603002d090261171400900b0417404018182ca17801c0301c0d03181408840d407103082c8204a03043c0300c45841180d100280509226141c50900f0021040c4540f040c40c1d03200d0291556407901e02018045204d4076440042c1000a007540c442094000000ca105050b503c21040003400240c0c0040081003240d015510300c0318100050f14009001030f441e40d0215040128241c001070703d20045002d0070741160078488215503a4081c80c602607007008540900c1039041e004800f0344009041d004110101d21003104039000e040c581d810010001224800d0f64054010b0703 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 100649568 1250 100648318 100648321
    0x30b010501030e010f1b110c0d080c0f0a0c240f030903020a150203010e0f282a030e0f07030b061f020c040b010c02030a02040203100b03010306021801090e 68
    0x55000303500610042d40c03c1e1002240e01440d20910800b0b8820002d14072160180c03d007440e0321096448103141403200d003110050b0111075880c20028004141082e40603000a10000b908044001708103e10100f2400300401e4800c2c503042c6041203070848005100340300501962848641c0e05070244000301e845002191111800c2e92403c1da0308034020040e20350f0850940c400c2c00c403001d011801c2d0400f800d2006825481c096529030400d20249034481018002c091001e00210034000c01c20074903540c01680c19148500c1444c084111542c040190803656030324802034280204540502e100384000b0b081c103c105440501a14066918941d03884410a07201c2409800100d41400050070000c00302d80c1009000300a204003004c1920f5900c0725250142c000c201603400320180c0760721410300e8080c0e00000c540c242000d0280c1400740e0082030700c5004014000707124903030000014807414292000c40c0b000d0000105003c0d201e41c0c4a290020003507000c26004011201d0501414649622030b010600c2030b10850080580b95 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 100650818 1250 100649568 100649579
    0x602030a02100b0d080304060e0c180103030302030c09090403090501020705101d010212030a02070201091502100f020c01060e0405070902070f11040f0216022121071403071704030b01 80
    0x103000c801e401c1c030380c13210030030000e0b101040d1200007460082d800f031380000806d498011310103464152000360050080c2c41020004071061320140400c0e04403501400d01603a07075031320041200c4a03031040341071055004403c00240810b15074041c00c81800d0700ca082e002c5505035a256420414422040c4001c0d00018103800d08000280b200c000b203200c061b203410b0046a010300211074130079103035800445420651680c046981c50079981d0126442c00108032118011012401c030180003901d0b85003841526840c2138031141044640c04c0160b0440d15001c09480082089c1d58850075040d00420f4213a40c142d80912030802c0200301250f0910848950944c00802c1c031280c5035459403413154004299855503400b0f40c1d40d4080030303541500c90004002051b48184000414880d40c0304000078803d9005200804510504500819580010769203180140f44010aa0f2351540031501021034030803184c004092100d644089980400d001016100d902c1c45480000030034020a81c1d0884180030724400a001444144010000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 100652068 1250 100650818 100650821
    0x10e0c0d1109040903120b04020708190e030d0c0317070c030c060212010b03010302040f050f0622020a050406020706030b0d02040c0507060e030c0f03090f3003130602030a0210 77
    0x3000ca00780252402d141590340014121201e0a60940c0070400e4101e0b0640001550310030320750035250888046081c85800e8851035901c0c010301c50a4540501c0e04000c0d100c4460080d01c0c001030030000201100c41038150910020714000b0140350403400704d210034410309241c00d09036940f0340c4190304588c1c40795020015500c3c1181d00e0081100c042d207403298200000c5074801c00d44039046001e0b104440c00b841c0c1d079500d184148030460741c2020280c900c403850300d01400301e52030b503042015412400440b001e9580c01d504440301000c4840320100003c1e164030010300459015000b0016008903021502961003096445100b42c05990400b103401c1e6101c51007094081c0140f500b5072003600c113920740d0319150303040c0b25080c2d4804007101c14910010105078008245061100c0c010000c802920b60440059070a0050a6000c40c0001003101c020314444c880440d00014030702e140705c1900500501d1790b0084100e0950b240c54058a81d484110300054a1b000d9400200d822030000088521101481c3c1c0100469100a8402e10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 100653318 1250 100652068 100652081
    0x314070e0417210405010c0e010206040c090506210c01030608070315020d021908100906180c05130f0807050a150f0e0414060910080304060c02011206031109010e0c0d 73
    0x10110202d0100d03c1041c43ca415281074403c900c80d400000316448101406081d02034440e00c0390b411940300004020000700c0d5020084101c0d146010041a02e03107414000030448280b40d200f05618000040c15110300c6100001c05503210082038a081081688855500e034499107540006014890072042c034084101055004000c007464148005007003c3d680c0a6084070000c07030400000005035458107028850080004030001060000d20401c61145081509282d9031320180002900c26522541209041c0c054002c0b00c86403003c3d0302800034101d4440a000903d140b890203910b000307100d007907804240e41c10031a03440820b448910040c42400745080404980c1c101c00d00e105a402c228440b1101d01640d11076028aa1a111072412109010304d400e00030300c172160400404214a04900000401184a02108440c25140185004000680f4500050f2241d0b400100e41d90501460000000280690240082508001160080c0c51640c1e03810020f42465002c3e106002c0c100307001c02c210190303110250b0040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 100654568 1250 100653318 100653337
    0x10140a050c070b070501090b010504060f0303030f180b010f0b0708030103060b18011404050a06050a0e071724010c0308060621010b0309070b070f060906020c01060314070e0417 77
    0x210000d03a11440f000740d55030041001110160b4440261504001000b5202c0b8003403d400c0e00d04010091810074054030710061840051306041c1d503002080703042074403504000c00c1102a500007841058035071810018480d024800d15070700826100021810401503811110256004181c0030b0560b400d68031070750028541088104c5d030080c00d0903e0140032500d0f0f4a540d50080c034280c1340c202c44000444042c401502e8004000240312490301000303020940d034801d441e0b07054550940c8040000e42d610f0000b5039401c0300042044444d00440010403049420107200f03c44c0c104600308441003a01000c0006544c016060140140481e07850000511581070480150400301c03000000b240811001c220081151202a0030114099500008000187d10100a0b500051528184070352901d002ca8858000d10407928000419180c1c60b0300910040c000b184d01a0746041c40c03894020003c031941d0313260000d03402c4c42084018541c0e028880000420201ca404560310441c3c01c00c0b103400032a00721100b1160641d200d030002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 100655818 1250 100654568 100654573
    0x3010b1602030f060a0e06040209150d06020f13052e0210090f03020c01090810150308031501090b130b0d020408070608010e0c270f1003020910140a050c 67
    0x11200580d8042110503c100c240d000500707541c0c2402903207030040c1caa03a404180800d500290921005894210140d640f03d40070307007901c0c1090010940050091008143c000e0106400403a090036524000001003450203003412070900c5d22556030090044070000200142075a00000190b03040c0c070b840d04030084404441d07520544d031001244000304000c0721500d038001c0d00d95100080051080540402507030300381303513000d0904050140c070f01481c080c2d43d02512000300d0302043e16a1101240e0780c281e04407000266070b07c0900e15803079180508421181d4040c8901c4140024900c000001c2c29900281c01c41d00c1c190761140c454405142001c0007039605902002d18100c010380d081000003051041404180b000e000c01d642c0d582c0d000d500d40549140058009028803d003100c0030080c0300304940542c1406140c507205800c0da81180101040081c010315000030800e60400c00d201949480303e036055009244121084500201e111705443c0100c40603010210042d1991204220804816000f01701a1808807400380c03c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 100657068 1250 100655818 100655857
    0x40507050d06030c0311010503090715091203030203070201050c040515030408070b0c0a0f030b090708090109120e030f0a05030912070b0a0804150506030c10050d0203101d0c03010b 79
    0x850380486002e6401610701440d008814400c11260301601c0e5004402407034143d05604103601a41d845041d28030139a140d0520010613580d5003070180143c68018640c21105c100c103841c050030064081e600031101a001540703414001a00641808280d909442d13014001d039002151082160101d50b10150007a2030540040c000a40020b2048468a209034040c01c0b10702c0e21600ca82c003016150840840e8040145420f10401c103e8070380398014030952084807881d04400d030303448114100307005000e0a0b46c060030394071800d00c041e252582c00c40c071002030450041c2d08583e490054100d00c980c8580c1c1403103000f4625002000800003914184450180d000c06000940341a15030364451840d440c2d0180c1e240e000071030210400c000501c11802600100720780c03500c009202d00c1c84d101c00005d44502d060b203c2580301d9000080408401c0c3d21030015205c8015101904559a0a01105590000300d01c0e1140c0c0c2c002000825854001903c0030035810b0041c0040c042190869090004441454100b01803031502c1e00728105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 100658318 1250 100657068 100657087
    0xb03010219020a02010f0c0809010311070212070501090e0c120714030f07030506030f0721020901030f0b1f0504020706110d270209181f0e010b0a03020d0204050705 72
    0x2440c1c014807054004052403905440050040f4402401c05400d01c203080f986200400c500d41c0440300145804d103000036255a07000f000103028021988040e410042040148954900010b03032030003a0f039002d0300c41c0a540366840c00000c1c4030510844050349007607003c3c44520000c074038508143c1d030082c1c0c4a0603d03032900c00c0c1d94030102d15a81c00803180d10080e088a14144046280c1610a55800c44000c1d4050300b40c5010761406695103081c02c0c402e8501a00d0072801c0c500842800043c0c07013184607030040c00801156524100030018802415098440c01800000f00750000280070103c1c00b050501c41091810b10728090402000b5009080251155a2a55030108074215000c00a210900c98000000f410b00c0030711002d000300c0110081d040c50300c9410000c550015aa5007100c03d07078060b4110284c1c0759400140e0181904160500c42c0050010245280403c5480c0e03460700300594a03001c0a00802103107001000300302d00003803d444042c1d002408903416102509041d000781e03a121800e810b00c5490500b580 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 100659568 1250 100658318 100658347
    0x50405030a03120c110a020f01030608010207060222060903080d020409050f04030e0402090609120a0c06170603011406091f0f06080901020301030201141806130801150303050a030b030102 82
    0x442003100060f80303840d07404256034078500c80d10180880311300c0c01e00d140c0c0c1c548002c0245c2c4d4a080e00e84c0a84502206c1c13404040d01c4c0e200e6085200036100500003951108921300e000c0021303401030309000c0003040c102d05171081d4a44060425204403802c540d0307015511460360715062200c0c1c0c81414400c032415020400810b42c4502c60088038007400d080300f072130f10551406044c0205412800c1d210540b04500400032800c80b951800255544050304440d13068102404605042c500403a1141c002c4c680ea20300403000929540050420201d401800d20b6401d0ba59203840806088a404901440480031000007144c41400c241c500305502c200002c0b07058190041b000720b031044a81041e031148601040085040c0802980710034682d03042020030f03000f5800c550541c0e001034160107492300726103500c4502141000f580201142c0c0b610a041c4050121903484210910005030346000b409020a04d41c01d080311442504d030907413900c070100ea816540c0c95003020703006503048014081d41482c8980c90364080c2302040c4a076011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 100660818 1250 100659568 100659583
    0x213110a11060619060509041509020403020109080703170f070209040b0a0e070b0f090303120c0304060605030a030f0e04060308041d07020604030e0d02060403080c010603201f05040503 81
    0x5540300c1c0490342007564146403034510020034081c020124011a44024440408688142c8015081079521002901c1c0801c0040404851240164080d484000341100503035000380f081d02c0c000e80e00d040c200751b155048540d943d001484020500e40e90200c1407401900c80a0180c1103540d09201c0b80c4c0e11388000380c0c0000f9480442902c1c2550720071800014000421118854482e20800302d10203055a05c0c641a641c2032070303020302450381034802c000083d41c00240d5418400c03030b115800c44031001c41c20f81c200300200e501150011a421039000b0314205011950f03103000185421280d5140d9581090114801030889418061a4126030000c2d110310011000400724030240c0054620306e80f1001c610425115100244030f8080c11001c00e64200c04248400701e0340c0401016a010010303104440100c079148049841480b0700e60003d4040c4c400072900031044801908003000700e9000b0700c0b002640000980380345a26160510303043d0b620903002d002c812880700140502085072001d40c10500d0606607504082810f1500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 100662068 1250 100660818 100660837
    0x19080715050f0915011203050f0c030403060c03111605011514041b080408070309050d03030e0601050402130509100e0c0c070605070c090509010f060b07031403090a021311 75
    0x4454040005000e1082c104a030711400c2000103040000004542d03070b10481042c080e0a1860101e0f4001d01c080c540650300705e441e0788150b08181035031544105d076200d4132070f0400d020031900d50313060401154049209001d807681c05080708108038904508210707445240f10204000721155522001c5d5041d000304444400c0e0300030008004140e0000542c4000c2104a44043e42d80030400400e901003000070540c045486a80951720020590343c87c40f4904003038404075480d50006a04c031b020000c48104069140d0802014030803681c003140c0b01a601d8504000c1680035100381e8401c181100c18040110b072a0510085070084501194070360708580b203d0160b8940c10b401c60b0310300d00d0f41e01d000903011225041086001c0c010161498407a0905a0994a02da0080020320030484082e403220003103441800b003903214111050841d4010002195150b083d80c045400900068002c94440c011100030080100c0460341f040040b4009040240e0081e0300700081e013210307080420707090341c0d6a140c041c407a0300a08008155120 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 100663318 1250 100662068 100662071
    0x90c0312040e0f090706050d0207050607090501110d0e190503070b21041a1503060103030305010609060302190305190e0a0c05030c010f03110c030d1406011119080715 73
    0x2e042001c4034000960241a0215510720300c02001588040403030b100c0203031520342c6401ca84e40d281c1c60340b54201a015140d03000d0003034004c0300240030300c1503004103080040b14400e80ba44107040300030600f03040c0c0754000d9281203c003203045002089402d10b05590891101c5601484c00b044564455001c2031030035883c0c0e00540c1d0103240c00504d8411f1921021018081d191030413070242064501941c034800d040c4010341800c688040d00101144060003c483c4800f0f4100b0007500301c411969417800d004024180a03c20b910105800f40c41c0460304a03c0780c000c460300c8068040340c5007503207404410101c000709402890543c1c6402c03441e4590004207041c0c040d0a100359410700040001040c00c0c2444000340c42c032a40898071a03444210441201d0b42c00c00100701c0d0300349840c140004d0070382c0740ca28145a5403040c1040f00c2c1e89030000141e50000000139900c041204da4950305403007003d41d9020011369410350444280d62003a0302522038010000305100807020b03294030580b00c407810166143e4505180700380e010138412415 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 100664568 1250 100663318 100663327
    0xb0301080a1b1203050d1e050601080108120301180e030705070504050f250207080d02010906050609010501120b030703120305090c06040b040e0604090b13031701060504050108090c0312 81
    0x210116110003003107040902e10700c0040c58074424483c4050204401418008003003024048a03656501034146a00c0c0d41074131010441141701880c000b0201154060301180c2803400204250038000ba200907030440040000740303164241018640042406500c003540241c0342c181c1071542036004c6c00613061940c031800c010882c443c241000c03c425684d00a011888484c0d00310700b003150559040350745031901d00d038804001c1c0311518026412801e0141a801540a074403491580c0e8a0319a415403000d101a0b0140c1f50030009610b40d9001c002c40a0303400c4c40703454005403c0300c21080c0b01441c1c40d4080d125000c40101140c90365903503650713840d070303501c8000c07500d04042a600c400f00180760400380b1003800100c200321419460a810000c0128050007a030180c8042501c10304006260740c3c079a40d100c071101940020040d00316203031400c8022451070342d40341c1c210005804020011000d000c80c841142c1a10038507106c0c0c41c2002d0501c4011240c0b54801089100140700300ca100000548081c003101c00b000c0014000103958 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 100665818 1250 100664568 100664573
    0x41a07060c050a09050d0c03020a18050a0207020f011d100503090c0405010302060a11011508011b020d1d21060106030b060c0316081309091a10030201080604060b0301080a 75
    0xc4a051a841d0710501900b04034080d0368603444080002074079422901076501c0045400d125000d0283d50b00001c1d00242c00c0d00c0301142c600c0c0d007503102d00855140421309010590b19000e008041e80503000009401011080003000a5802103078403410280001003220b05002030400024079003030119101c90045100001400754003c0c00b84080a80040203076003c0c0019451a400b00f80584034104200c0204030b00d480281c3c060f07400c2904030342003111a80d00712840d004e0711480c000e070082144a102000f41500203415450050000c50030345c46c2040103032110071040d0080c1d4603850081c050142019403041b04100021040c0c2c0b400880009040c0c1010028040b0358104070029080300c2c40c45041c94803a0400780300e1050344080020854084085005c00c00340308004601c1d210040740102080b41000c40c0400b1404508507030300340c3c0178400003401410b05180300e8012000c402034044050352441041c2c3c07030070442440954040d43d00c42d81c1141000e400090b10568810782c0b000960400e800c86204d580204032404107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 100667068 1250 100665818 100665821
    0x1c0816020c0108190204050a17060709140f010c05010f15060c02060304120c0203030403030309020f040207020d021519020601080705180f07090306020703021e030c0c0f06041a0706 79
    0x22025454001071840094110028103840c3c4010040d0784e1802100d0035503410102e541e01910010800a00f500f11a01d844003034003d40d007804517411b40e078176100d50b9001410312803040e201d2000b100c903000182030700200640180004045450101c07030500c800050a200050000d01c2749800c1c1078590b042c0050b6810500d0107140496205900200400170a10500c00141e40ca550481b03801582c4651980920f800c08078007030710b403038500304030182d4140004030780001403582503003002e06814802c82c1e03404c0000c00301500b004124061900042c0d003080010b40900010705003034805070007419041106a04156220070b00b4070742c8480301051440160001401001044802c106144c0074100c1190642c11000c0341d40341d9a101048014054100300441201291400380618a46c10207150414801e55403410b007420080c0d9500c0040314a01090509600c40400001c408001d881041055101a121818200040182c0e1a0080c0f10607a80a03400300f20000340c00c0d0700350034400c5200d105a08000c2d102c803003c1c01c0400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 100668318 1250 100667068 100667101
    0x102160f0b0f010605091207170f0601060503010f21060e0706020c031209010c030903020d060c0e0d05030a0c02010e09040b041a0f0f09210301090c090305030702040506031c08 77
    0x10840b03054200180820742c0c1013400d560120100703440701c034544020110b40780c0c504585541300c01d001303c2c4211180501441d010030030302d0710703c0459804c07207955990710038040b00d030740c842445840182a03003c0824040391510b43d840b084031107203146982003007400130784580080b80ca10b4080c0360010b03448010100600b035010710111240c11300860103428641030610542c00a42303e200801d904129030310308554205400780107031801840c0c01901d0a10116001c0c90319000802d002c0002d1000300d2044141e200b01d1f442d20702050840c0591000c095804d2020340d040945d0a00781e0100101c2c180f000f030081c0707040c12380c64600da0784c1d10a41c026100b442c3c1030300340b5042415602428203000d00c1601a80020052480440741e18580c0202808001c00d81c10b95481242508081a070000c1962070441c160916450170b501030050b505031104480b04100d5055207035016101e91001d844010242d41003444904050714141d8055a800344004c0c081c0c07205411110a8104203040554280700402c0f0401c0c01d11040407000031a06 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 100669568 1250 100668318 100668331
    0xe0f0f0c06090909030c010e03070311030306130e010e011e050106170708070e1215010b0c100c02010204051906080a111b1e0f011a01140a020102160f0b 67
    0x1081180204004141d8500c580012036016100b400c0200322105020000c40726164600e00080020584c420743c1940c480c1d00085043d0700007104044040c540c03003008821240100401800710360400a112102c80151455010038601c5541e103050700310a0310003e000e1580300340c803551801c01c0c501c03111085100c1201c10681120b810005281f03080007021070100d184d540c2046a509060a0326036607000c084808045003003116030000d0041e4404485024000360005084150b0300e440103051382c03140700c40441c80c020a02c0302c400a52040e0419410805154401e80340400e842c4005843c141d220004102241c101401d603209605c1c08032030801549500034501c542001d48024280180e00d2804584a86070250682800122013201c0d00b05c0405a000c120042400d000a15480c1d80c0031050080702d51119440d05008900b0f508001854400700c043c0080c410000d08140c4a924241204605141468015808490940d9800c1210300807960351180c10300d0b4820b100701c400d001c0d500403900d000700d12000e028201 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 100670818 1250 100669568 100669573
    0x12010203010f09151a04090204030602191407030804080d0e16050a1203050d06170c1f0903030c030c05150601031802060306040f0204051c0c081615050903010e0f0f 72
    0x810880c0101040440c049410400803806016040300102125200d07c3d03001c608450f2000600000b00403154002c2d0032512085002c0e450034401e060b81c00c7d540c000e03080c140c1c4100d07540108025030009004e2440e25403c94020310805003030410b1504d4850866284820700201039101c120394030a0030407410700300000b07401d0950742521700500d0007180a034100617400d07004040c07240c046002e000a54099002e04014851030b10701301114100c0304c01194407403009076481400740005c03490b00441c00c00f140e01601201d05680d0b80300b0394198a10b4400710340c803400010088042150b03007041400400e104000d01c405140d100d2440465030700b01540050201c0708101c4040426030442001302016a6592058170341c0138009480210f45100d400c002d41000f07101d690001079103c1604030341803c4041000c640c5c0141c040c800e9003c40710058072a001155144050701a5400c0703803139001c4050100c4a002c1e03400240c58004c0c0c0c1011800c141d40280000e094440b40c2c4003580c0181d01c002a0078584070000c1081004c0c146000c0003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 100672068 1250 100670818 100670831
    0xb120117120d0b01050d060303030c181805040203160303021501060c0b010b090d0203060f1f0b0306010e0f100827030906070503040e010b0301050f01090501020a110f12010203010f09 80
    0x40344072090151402c240070040e9039901c0c2c016145d00500481d202d94000c0d480420280f9101d15000e4005d001441c2d140700002c3d209501100c898804100c00416100a003130b0202e414a200000ca8001c1c2c48000d00c100d0301070051981c9030010031282030180016600c20b401034481c00708911140000007605920610400c4204400100800c40c000384040c11742c2c120008207a690024000812150f880c1488003e415200f0101007154810080362500c1c0212146c0b005e40300c852082000d100c0c0682c03028082c410070314908201041c25580a14a143c5082d28054001044c0c00303203010001300fa0481e5881d4103008606904100603000303448071a810b42000100c0811160300050f081d146a490054408440c0903c800080740d90600c181042a10024030409403444029a11030000110640080c130800b40200403581c0300041c10b41c004d02510023565010703401810039007180d0312003110308202c10a00680160480d00352042540394400c2224100145400160752175242c0340c00102c4581c420b0348180ca1b89803500c003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 100673318 1250 100672068 100672093
    0x40521030a15080d020c03070503010c17130f05010b100f0c02190308030127060b2203150c110105010503030708071b03030e280b0d060b120117 63
    0x40c0c0381c10403007010001078000650209030181003107680001c1d81138440e8031003030402c8139070010380078408000c00d906607504140d03140306042c262a20f2411103404180d9090004c240496545405688030b10501250043c101d00b07078440c0300c01c2c030038800429680c030b03511440c181425061850024040d00301c0c40c9442d0343d003c0740d08800204001294100244580c00051401c4401c07400c29607080e001e15044100b42c0c0c4c0c0c0756074810100304940c2d5951101102c018a100484100b0703821445070000b160380301101e1500e80600d41d00e49080c0c0b0080f43d0307220307102d00070b02c00c00c04808100101c203c2c0b102e911a00d4070000b6a89540600584504144400687c07680c0c1000c0051181e07072000320079a42c4a90703110310710980781d2800389014060304100d809641c1031895580c2000080c103078412050044008203461011082180c040503100c04107412081108117a08404100181c41c652001040301c072040d5000080c110b5203a07921505180e00580c00c0310008400c0c07034010300ca10104480380c460240d1203840142122032411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 100674568 1250 100673318 100673383
    0xc12210203150a3204020a0206010512070609060f05390a210909110316230a0e04090605060909030703020c09071e020f010b010201091110090b040b030405 68
    0xf0205002c941c5244136914208105118501c89200c9005206545520780c00c1802990340009206852054441528032072000b140403d0400c15a00c850f5611003d890900c60203a6451400b200d16104100c0d04101810080c40707004a503842e559241d840043d20402027410f80c2500403500c216100c01e0341c2140168000081e10781c407101011700e04011002d0182224041c4c2500c802004d0b40c4041d0030a4245075100c0903228540009502c103809038080001c41031880a0f040f6207001140ca0603c407a42045058541e443c007141024103552049403800c0600d0304e51060100d0169011050210341880e19031082c0706072444d02080a40d40001d01000850400c05d884e01d000355164002e400c12402104c590f004a42640d100c0c511128100da503807105044d0b02800003400170f6958134113000c104060351038100c91540540c0b0600450821540007511100b49160300c404100821040e040315905000f82d2101c0010101000c8010340000c00000c071010b0345a24040c1092401d000a16940d15403c80c0c1c04810503100c91280b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 100675818 1250 100674568 100674599
    0x2040602060a05060406080f010504061413020906030115141206091015090c02030306041a010e091e0c0a0305090303010303090905090a02031c02070f060c12210203150a 74
    0xc2c0119680d20341c8070104000300380c15000b030105e50140100c07100e00a00c05410260240788640c030308000c40760400c4130074600040706540e001403800c0014500c8000d4501000c2d0a0b41101c001000000c0303501280d44201445c1c80716501900d402d18020f40030000721319180c1d60030504881e6603005007800e0314095120f162a505001160203965681c2c0c41340d41c00c4208000c9450000e4860180200503410302d50802139500d42003220024030030740c1484075004641c6002001c040d500003041c1c4400e00c500c10b00030100b0045210081040c0d078004041000840c0e903100e103001141c001d56460b5151503480140c0080101079520040c105502d65000700010800244c0c8055004115402c140700058607441d2440c00e0b80c102018402c011390f151203070126903c1d502101001d007084550303294003100d10b07856940e6408410005ca030320420000c81c0c8031140c0314001c5002d01040346031130041807520421842e40303240c0c4c0c4075440008510000ca011350100401c080c031001561000c68140d0102e0b6040b600615010030754080c0c214 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 100677068 1250 100675818 100675831
    0x30c0e0415051e03070303082505030109090812040f02270c0708130b0301050415030503070303180c0815060d111c0206030a050a0c3b030f100c030204060206 69
    0x40501083c41031040c0368064a081c4001025528426983c0c1802030002c241902c074901405415000400480500c80d209407413040701d80c031061f003580e10b880840070003070000910545050604201010350200664519840340d44200b083c0c804039011401400800d07400d44403e240e00300440000703034044500c001c040d03d0744130004282c0c5a58900b80ca240441003070090100801140c840304801040c00002d0001840c16500706440402c565400c550340c141d0082d12910020b0980e410400081002c82e200303400100e40a00040030022404040d680d415a200f03c1550140354990000d00c2d2a1140064050301031350030600c2129496552134154840f126407541d00048148034501c4040c1c1c0526070000408102070b082e400030122038417890f0100b940e4001d400116900e00f5200e24048001d10018000c5404680114041e141c400401c08044010305825005031220700c420b5914408610060342c0c01c00c4412070f180051409450070421014448099403030060418090500501c82803000e0742c1e0028840340e0019 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 100678318 1250 100677068 100677079
    0x103050705061b061311010e0d1b0513022808071112070c030b13031b060b130207050705060901050a050d090c03081309110306130e01050106030c0e041505 68
    0x1425002910300b6004181d640b6082c2d80184010080d442e1184e100b00d10602d80600d034443c0c0303212006e20044400c400e01c02e00f01c59110f0b5208601e1400300e4069050744040200a5400b5680b06884030002404078069184136042a600061108040e802c0c010041551501c103000740d01c2290300000014100c6030004100900b08401e0040d920381007501003040d010500d0603208034554568444c07c011400d20094001903540000250105e0040d1464810450700c0700d03010354071035140344080c0000d0506032004040c01d54100c3d848408044840d51507220b0404d403620f0030b44006a0760340d000c2c58003e08000003980074500c50700081c01842d05998010342210005062443c2041c0c0c3c54103d1150304004008000c800b0340800c1400b9400f00412891700c000307001100700d0b08a00d50205035168a00419240800542c0079105404c6c004504d2608200c03a0700241c0c5030300303c0f03408510705080c0046c032401c4440981c4044000380e1600d84a4844c1a040404101500070503502841110300d80301c941c2203110440d100302070186 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 100679568 1250 100678318 100678327
    0x506040e15010c06051f140a031202070305031605010b01080c0f070611070b071206030503070210030b192606010e04030c0503040609060311090d0602090a050418031106010305070506 80
    0x3603204200c01c041444d4803040c02c029030b0600d101c0c040e0501c0d00f000c6070881d04510030000071074a1801215000c40300a00200011140d81c10b5a0b0f0720a0b01442c607111580c158031681401100150060020381003128141e0b12000a45007141880b500b55899000c070303581030002c03003001d02045104000c21502c0e031038514400d2640e9220703240f5080c2d0080c40d030300310041c00306640442c0d180d003040070804007207008416550710324800d01000d403103500031150203220090242c0c0c030400c03101b00142001414400000c46900b00013030000880408102003052000200810380580801481040d550300075038440503000302c003004000c01c2c1e11902d031581c07048180034034503180368400c6c00102010310621000d4051684901076907100c940e40c40002d00305840078020003020038149a0112140341d4103605407890007400800c04400c00a164450300002e41c04858050b411407103003200131400d07803600d025800042c03500c0003103465254001d041c01401e5100e4000d640108d034000000402c0454400110f02c02650011211160349 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 100680818 1250 100679568 100679611
    0x151416030503101d0a060806220602040801050702070609060e06031f1d040501051b0703180f030f0204060e0c0a030b01030b100f080702030f18060706150306060506040e 74
    0x2504150380040d00502c01e2480c0c5504c60340380c024006002e1000d940e414031080e51103c0c101c5445031011030780742080e010f40d240c40a8000d50901e10b042c2080f4085e0100628058a4060207802e447c003c55a41c8050780c8406c3c010426150b0005130030f8001c1c0941d1504040c4c98000200003144c80c03001900205000c0940303c9081403500900883d01c0c0140f4107200800e0500d100046d002600309011a0705070b94079442d1100141c0144001d4041d01d03a000c2402c40750501d00328107540e05440150248031200c61030307241030308086038000c1501f840d035010318011805950031210501c100b005850036600b1400001d103442c020320100601c112b00707441c00c0d003000f800c007c541501c004c0b0040b0010107484400c036034010fa03030b6017080403c55003210865080044030b41d03c5a00c140c1d42c0140907a940c2c414010740d05021001008201c0c02117a8170400c0c125012001042940780c4951034039100291809190340140600c0c282c1c1c0b042040258900c180d000a03c02079820324186840c100c008200d503400140080380801001d0981d001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 100682068 1250 100680818 100680841
    0x80702040219080906071b08131a1c022113060908091c0b071803060f15080c0a0303030203060d0210020f010f0506030a030c0201050d0501151416030503 67
    0x40e070307100344030803859002e00340030020301c807840980b06010980a15004546001d110b106003c00ca103c502240d801040b41551703d0707420710b621100100300704202c46100401c3c07803401054005200e4504082d4240c840000c400c2180fa8802900203d240ca10700c108541240d01003090b81102891084100c1c400701959940700d05c500703d240006004101c80e1409505108100c92000500308414041d11366030402149500040032152490380060700e400c4c1910006040d5910582140300445090b42d03007540d072240d881e90b4038029180c01c8401709400548800404c2103c03142141e26400900c6120300410301d0915000c082400700c85240000b134100341d0008001111074403200510042907034054618420314601000c0207448d0091415504000d508140300400100c025000d014020400100a0084c49801da50141d070183c17482c150884c103009083c0010346180b0007038031a250003082c000580b51941c02201000078003a213076080c0c1e000c41c552014410b109103005500d51501e00141d26007000350352a1100d404460 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 100683318 1250 100682068 100682077
    0x90d080702070e1f050913060c050d0218010e0a0e150105070f0c0602011a131a090f0402030601050109030317060a090908120c030402010804121701030f1a0c070807020402 75
    0x101803d110005101c210a501641905103c4062122050039910380c010012503500a862687d4101d9181640b00045115540040e110a10078140a850420603c10f42c0c0143c0e0800794000c61740348030900c003d80c15540c10000c001d00031101261500303407230303401d000e100508101d0251006106401018900034980d00501c1280c9940b031300003815440a550525003c016034034580034484c015401d010445e80254800b00380c1001c410401045255080400b0303d010005210b000c0c40200601d08101a000d01a180d450404d401180080c2a010742481c0030300505140c0801a8402410840c140508001103640810581c45001d5141485101a03c0c0c03940000e10803030094210800040c03400e410b62301040a14401080c50990507460002c455580d0318552485000c00ca03000b81c0451245030018001030a107200c074800030607240c10400801031102848442a040903001103400d6020381600c48140032030500320103d8840200074800d190f14041d40b51880c2d80c000c00000411070000418828210b41e116010745 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 100684568 1250 100683318 100683329
    0x70f0218090f0c030c01050c01060506040e07020f151f1503060f1203020729070b010e13030f0c06060e0a06170c010203040314010209030106080102190305090d08070207 74
    0x59028003001400c214080001d68214039103114500d200d03480500d000ca25030b07108410040141160004d05401990725a1000c06801c5440d540c50102080c1965000040c00107415443c070b440b821031412007406840c1c40c6201c0d0b041041c2d60300042d00d400401104181c141d60281400c0300d1000c41001d000d031541c1208030642c01030010178502c00c2011107810707850303401401180e444580084445950b140d02142e9400c1d241030240050b0407080052004002c03048811400106010028142c040081c52001441d0040d102c11a44040c404d00104004a4003244540d004121a4846165160383e680e01504040b8001d4046003400b0501c1d1000d01444032581c040001084100249407052400f030945100030081c6003d090074809401c48065000a0f00003614000e0102c10b8008624043c02e640307e0110001c04506004141e40d001c0008c1801d0b43ca0078002c0c41c000f4808000007684900f500500c01d404c00c0180340c1e00e1003c26203480f0410141203c0000c4c404207044917403e20b5040b544078010120704044154101c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 100685818 1250 100684568 100684579
    0x309020307060536041b020c0a0e010b09030304030f0f11090f1b070605041202061602030d090809041e0e16030b070302071704150e03030901181a0306100503010b0f070f02 75
    0x11b0314820080350031052842c0605500340d035002c13414041000300e40c1000340108030309811507100501c6100441d0004224881c00242100d051582d40d40c0c6411003070480c06004c803050316a6850090070450700070070600c00008121050030f9245002608050b001c0001020b9040d0b18030010ba003400050704601c00c81d035041d900507800380700a161a09200a041e0b60307080c7c0d900700500c03840e000200c00c1030f400040f003004041c440d4040c62600585010240140c45948070542c0ea1510810034200700c3d945a101d00321110b00b50845451420048203400021100308030101e15443d00301c4104980c0c07121056040b01d064075440390b5000895201d040045001340948075004054107909981c2c140000c44040261040300c1c02e42c8a07003114a04c554004680400c420001c5036010740c01408002da0540c0500004804a002080f1359510713207640e25002088105820304101c880c44c4000184915030900c410200060f40103400e15910395458a08a10454401c0c9104680d8905000c64403070100040b0000327904c8416001404d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 100687068 1250 100685818 100685831
    0x10030b060d020c0f0c030a021c0809040212060102073006090501090c15050406080f07020a0b070c030201061205030405010c0c05031c03050604110a031a03010606030902030706053604 80
    0xa55a9205a4043c00d0b648511400104071646e01d03002946c43e042503809444203200440300c01c1c5422800d0203825049030321600900030201c0301d44580c800381a9441c003030443e401b40c504012002a082820301d4101c90100110741c1c2e0032201d000d00200104006400141c50501540307428103014000740b02c0540001d00039420b24103a5814090307545549400d076140c129a4001020240a09031050f11580c45041c000c00d121000044850101d174408650180550054078000c0c92035507038051640d041110240089400315401d1000d043c0d091242c04043c020f80c4800c44540442d949485940740194412a810080715025400030420302035030b0800102005000c03504180542e69074080310b03600c03080003000068540f1000902c60b00d003a000d40c00540c016001d00300c0c03503c02e002e501100640076545240301c00940c0800c00219035102441644014801d1740ea0019115082317104250800950f940a081085001d1105032095002052811800700c0307030044003000d80140c900f00500621400e074000303034428909007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 100688318 1250 100687068 100687087
    0x3120c100f021e0c0601050108040501020909010306061503090503040e18030409050609130c090216020d0f0501110309060106050d060504050709090c0302040b07060203070c050f070905100510030b060d02 89
    0x801621991a40400c00740f2110100c0b03034070301940c2c022a80c448586502400041100f5405005500d400070300460025291103400380c0403504d4440d080c4d008031a0107540302c0040103070040309207010700080c0d024a020b0105941c0b64540c15078034007450080004003a042d80109020080303100c071a0100d1894001960717203882e0f0f9041802c0040400325052400b0310710981c002100310705d074200c0600170a9131160200000d03a042c0304ca2a0025000360b04421295940080c0b004007503900c21f801d40e1031943c41a9143c90444515181490950b010725010140301c0e4001c0c4280080000080355080c1910018540507803500f07a040c4604014051660019821500d000140031100d9400100041a900d20b640f05200240304040224200d100d2849004500d070002d100180014040342c004540151880c501442c400100e07032505400d0820320804902c003584020000c1101a14038021113900c01403030304003044424038240100d6044c210a0150b0010155100d00944c1c0642c1e96505844054814000c00c545420084 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 100689568 1250 100688318 100688321
    0x1e090103030206100f03030c0f080f040e04050f01090f240606020c030d0203030c0403140f06010b070b09010515040510180903080c07020f090a021c060302100e03120c100f 75
    0x20b98603040410310065020036034824a54185d422a80d140d5107411035282c1c0c13a15015829120a001120b107403004014140618581901400280106130b00115050409192940c43d141c0c42c0b007502501c50b411b00850a02241c07058142644454000400c00d042d0000c9440d20041680f801080031280c40c0303440400303c0c0280e40003410079440350f8190100c1719200351500c4240d9590208880c40c217460710b010081840019603420703456046114140444080039a055601c3c0d040680c243c10105901d500880d0050510a813015041c0d0050300c2000200700b281801480c6510608958000c5809035894030045006544007c04010050043c001c680804803403061056016203050701040d00001c9401020841c29a2800c08640b9007503802002c1c003075940420f03414400c03c841c00500c5225415424400d114000c650000b1a10340f000250200040d8035040d07204102a4480b900102c008104c0c1e240310510300303602c00040140e801c11000c0751803519016140c04076072410414040040802e810900080c1900c8810b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 100690818 1250 100689568 100689571
    0x13030c05010f020a11040f0e15340804020d02040507020619050903071211010c030b04060b0901022d0a0b100b071e06020f1209010b0d0c051e090103030206 68
    0x360395a03454040c0b00c0204980d5012004e80c0036000564485400e00c052074154010305000c00400008510406110403117824120088442c0b807210f10310408000c07140d0b4048814000c0c5d0b21000050303440c2155000c02001d110100914000e05100c442004103007955200b5101d50040342cbe0003002070010340342c404d2009403a03400c1940e0a40108160f4000c90309024100d01a60340300c1c0f004030004504200c416107032030340302d81003a01c030040c144054101901c80c00b082c28002c074200b00b159034074082020404002030104a03480f690204002d0802446040c43c903a1b07001c2500c070747c00124400c0c0c80080c0c41301d140040e000000d480084500d9803007216128003c00c290f001c8824801c03000f41c0420a8159500d0005c0c1d0110b1281e8500107284002e841c4800414038451005541c03568084c80b401410070402c0c19000240742c3c0441803034600c5910340800c10002400034010722000715001e85654124658980c2c900415588038065203109030039144c2040501d4100710301c4072106160003045130069581d207044c00380d142d400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 100692068 1250 100690818 100690829
    0x602030a1b021b06090103090c0f0503100c0203030604050603030d021209010e07050105040b071703090a05071413050402040b030102032401050307051b0a06020a050d06050d051203090313030c 84
    0x260500700e50034803800402c504000070246103081c881c6414140c200003650b80312000c054141980c5410b01070100c1d40380401c0a01900d07090741056103060401c008c040c170303268607503a10341c0c000c0d400c0040c01c00015038044256600080301f9500803c2c19280c000003e815405040020840540b02050080745170414010940c01040c10303100070000005425071494854030a1b004983c089901000708002100d0494000c0149500408000118402c641c148004030341c020340d58001151b01c40d860020921030107100c10300050090942c6105803101301d1b03021030ba1144000f0402490356540788001030954035a500403041c07400d8001c00855580c5485031036a030034281c144540d408604a40207582e503495000d6001c89000701d180d51120f50038014254401c0004803103200d05e00d01d050040050310350000e003240c0003800c00c015a03521180e85070480301640341c040791001c2e4022889103062601a001062020403204c000c00d800e150456075070750350030031954030314403490130112002d0146400001c24401d403c20100150fa4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 100693318 1250 100692068 100692101
    0x40507140a050a0e060301050102030a44070e01021b0607020306040b04170301030b0406050403020115060206011d0c040608040507031406070807021c1b080c010605010e010906050304120302070602030a 88
    0x144e010600602e80824010f29025902c200141d0700b00c98002ca07003611000c0096402e12000c0e5103500120300506003610b48287c0f44002c0154a4050a030800700942d0303001c00f061034800000010100000d40d544036810318009640343d00c01541c1e085886070b030101c500c1c6a4018044440302d040901c0c1c55200d264048405407010380a851004002180c401c04490407a0340001e4200b1190320742d515903030700030035001d4411801d641da43c11684031003440780c03101d8000400c00340d005000b8542c074149000101d10f102004006d4010080020018003400703100c00e990035504140352100013a6124545030307140072115080a030800e440e244a070010010000b801e0340c4100302d9603036501050b41352800103aa980c400c1c6110030f0100806200d1030040e042c440c1c441c4200b10310a84c1c08036403d204482d02e80c0c00d05c5600c140e982ca0341c0c40e51120014413055030449550118181700b880d010388814541207000f0050700025100a04049801c2c0b940345800703120f90141c80003560400300c110f584e4105800c1d01001420341811110195 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 100694568 1250 100693318 100693337
    0xf06030622061d01050a0f150503100302040f09020108010f0b030c0a1403010803070507051c11060f0c0312010b070b040303020306010507060f090201030b040b0a14030316030c03080105041a040507140a050a 90
    0x45400c1d44011502000b01c1110303070441000c0b044d181d8ae00300074052860100d070300e031000016039241d024a0003868260b0300d0004801642d0700004021542c141c1280c03a154160200400001c034120080341d070300543c4401d09030b44508002c841103d958a101c1c00b001c03049000840080b5008070080024080544a04120380a45588100380000304e818005561401540480d40310003054890050b10f0120030010b00c04c030314044015191150a40001034664250340c00400d5810440e0000c904c0d89025010741d80d0210304050890b915001c2c1504000c0009007015004400b0038007a90242c0181d4540c1540310400380074100c1c09032484e10080183d80c00c00c2c3d0001c0d003441d150311490304040c0304030410010007426995080b42000780e16102c050306001204d40501c4100801420b00b04001c0b808180d8a200740c3d0f503028180301600b07006040031410303041a48500d10704104590340c840c88410b40141e402e425540420940e03600c1d0025180c843c0e00003403500300c5040004161240da50300c5002050040c00944030800c02 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 100695818 1250 100694568 100694579
    0x50916030c08011a0a060e0102101503050c0d1101050a0201060302030303040b0901420506031f1d010311010c0b0f090d050c03030a240609050f06030622061d01050a 72
    0x807200c00261300e40c04c04900c0e4002e0041c284102480840560b040c0116414421800400f204488900d220750007049121402401000410721402070040d03000c9071a035110b521544c88003800480c0115525060000c001268080384c1d00039085400116002030940c0d859250908103041c40880850b18041d895280020001200c103071b103859610801b142016102803044d150499000b040b405504074110021000c40c000356036541e01000390310410400080c104074020020a102d040c10ba56080908a000100b005082804c50b400d4414110b942003102800025a00301c0143c03030404880341e01802c1c0050805c2081a03146d000d460507800340b66060100c603100f940c440000c848078004c1c1a0b80801303d80041000c2821480c41b5000407a03800d400340c69450100341c100403241d01581c9039500410108040c1001003100b444c28401d1150400e2041e03580924503e407240000311500b500702c50001408848003080c010502d06640718001070800c005294090200290583e200620240705403881418900c00c08030301d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 100697068 1250 100695818 100695851
    0x40b01030e06181f0c03050c040303050f03040c080f0c030d022103070e0a12030215060d030f02030d0f140105040603200607060c050d0506040b06070303050916030c0801 74
    0x2203542101c080c14094950400e0044042074000c0c003070b89203100b00d04140840c1680c9104c00c03030303440070103c03c00505002e504001400b90381c4000c11005012009000130400311360040c0c2226545005080c15030f40e00d0f503c514050344480000d8121070810302c107240c102580001d00203541c40c442d12003101110000f0010b403808903601e07001740918500154a000038000e00080000c05550032100f00c0c01c00c002c4d2412408007044021180d5030001074008800e03500c030414150180400940b0050200000c9001d242c0300c0c0c041081d2048a0500504020f00400c0c000502c40c402c2c030a540507003c46402c1803200800402000000d0f2001110b407099a2441ca000010350346000e10030340303086030f0340701c18051080741e48020a40458a5003001c0550048400c00403c0c0004005100320070100c41c0c25121551a43d000e03520400841e14010b00307407806a483c2180d08159070b96844141c0d42d0042d41840c000c02c031031b40c403840711604140000600155407004480e0100401900100c0082910f1004e80200860403000d42042c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 100698318 1250 100697068 100697081
    0x1c050415050c09190e07053705090409020406090c17060f010c05070f090507030e010b01050301050f041e0b1003150611210406020f06010807060302030402120303070c02040b0103 78
    0x155000e081004000d2428010260303d141c0075528040214556a012102c4440078200c44180c00103100180e100402c144210b01078188551010232040c1d0300200305050481074003103000f41307000e2140204818940399100d8101c03021043c3c0c00b13002441003503543d0070420003805107e007086000c640580703403c203000141000d405214101c011f100340002084280191903c0200480c10395007400380d40c80118409102200780c00050005c20300020b21450b0401c2c00400b00c80c03071241681c0a690415400d4841c0740e9004058a056940858204e03a040d6013200024000305081c05500c4200b1661410103210b01c500c590100d58000f2003a203403c50f0050f041c1104804503122003089550070403041c601845800d01c60f059403011440010200c4000800c032502d41030300700056400c0c5194844001601b444199818081720344081381c103070000c028550403c00c05507102c1559000c2c4808150340840020159950310300aa00c40f124042c042e240d907400c103024010030720460032000781e0080d81400c0c000c29141d4841e204c0ca4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 100699568 1250 100698318 100698331
    0x1e18060304020d0206130b0c0a0c0503030901120b03010e1b0102210a0c030c0501090b1501090b03010b07020a0506040305070504060f060c020904020a0515030610020102040b070f03051c05041505 85
    0x84024681c4d900301301c040e41010030034a0f21708040c5000420607444100040401d00703038080c01040c450216191511702ca4803180c110900940040c8004100ca0340c21211117101e80d401d0304000300d41c00f003514002c24010030100c40d15503010302c1105003402042c2c640b0302142d1403194081e8242d802c903034448101290780e4450051101c40442c410404884500d1040b2102016180319240c01500000e003620745e5802d46024250a0380c1c8007101070240b26101c0440e1300d0200102d80300b0308140184529090841d045400144500721958070005440021960303445101000b030403009140030b0f20307030342c407401c00b80da1700d2081c0c2c042c46014070315054000c252011a14052401c940c030964480340140702c6907083c002c3c40701000c1e004a030400910400840c4a07034031a03401c20403a42d01620016140e14282c020424618624078840095905c10001800b400f034804049441f8550004034030b071041203207450116918806e101c448400c169940b2000700000c0c64982045000c0c80c0141074001d4280460300f060000c0781c4054440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 100700818 1250 100699568 100699579
    0x603260a0c050106050a0314060f06030a02091e010e0a0b0d0f060f0b040c0e04050c03010e07050a02030708030106270b0a1202090a03030c02100c03090303030509031e1806030402 78
    0x404031220300c61080003240034812070000c20110341c2d030808200c000da000e800c1120780408010a007202200c04014081d48000700060744c4015003801004203840b02880c44000c5c0c0540c02d054000b49c2d40c0e9001031803180c200c429030341600d99690f030350b181408400d0b0804e0700c10303003140ca0034002c207901c0500d80900c40f811580d030000748000e090311b92585c1c0c2a00a08a59200441d801c2e01c901ca031000e9a070f902e1081203851460b58503110340644890041108843c0000d161242e0707a80d0500040c44504c803101ea180364050100d06140c1e0fa0346500c500181d28500a002d00240b40c89000800401e000e680180c10719081c603501c2e07040026407120284c490b01d80e99414003466408070401d0101040c00c0d44590182102068902c800615198680011034040a03a41d0000e5010036000c8446001310f08100300e100700443d29904d4440d501e48843d5400500440d00342c0b10280425031240f001c038800807402c2c0101c0c1c040c2400c40346154124022020001119001000c0040901042405800080c18401d040b2889141d00518 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 100702068 1250 100700818 100700827
    0x12060b060703020307120c0203101a100201060602010606140f0c030c0a05330705091201060905040c0b04030309030f020109150804120306060801031e050318040c0c0206120403030b03030d060326 85
    0x12b5071f45c001c0621885152000c00140d911013255216a8220590313880540e0002ca40340d410000081e080d2000d5a110804124000f103102c6111070107401a05e4a051142030702c13603607981103456001d10750301800c81c4903811401461341203400c00c40b0014441c0c08000541180c003110aa01c0603551951a0110115102e1035000c5000522501c6c460001410380e080020b141001008144e42400d084403200d07007001c802e05654206100074402001d01c40c100600607604214542401c540c0c0042c80b00b841440020550460948201d013103a00811a920103455500080201910700c140020b0006909803015204425203601c1c0d0b00540d4402c4c00780c10b0a8612940300c900c610b03440c60742c903c844030182c03803c2c032150029411800800075800303100418450000742580400d1a4203102088110350201c40c0719824031015058020050f02c40b04151607048141740d0030403105690b241010b60180010306d808036803501000800c1200485103901800981340102d4481c8043d58280c54001020b484010f5140089c1b0801e00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 100703318 1250 100702068 100702093
    0x6210106032d1211010f060509061207090b0411030c12070e0f09090109060c05040f0905010e0c07060e01061d0f09030313031e030e0f0a020a12060b060703020307120c0203 75
    0xc0d50b142c3c3d01486181c80400f054400c00918216132081141300c42c01d40c1c4175281040280b4122111607044902101c00300b00440d0103802441e6545041c0c445d81c254561902c1c0110111361391503010911030344460007117541d2441d00c1d6000581c142d0045000041b1902881c01140b812071203150070758803401d0f010300320410b041d01140401c80400310042c02d00002d99201c21010b000103c0c00e0103034018800490319210b4403141000003e40f1003480503007282030800d281c10010480402254005138011041510a0f80d071900c860070800003030b0081008041456080020000d06651420b0561200301e083d2042c611050b1074200c1010f0000c04281c0e03070500254130600200c1c400000c04c410110149101e401c103d603050044041d0b1030350085d003025500c00881d036130b5083c80c0d8020308140030b00d010403042c140241100710601d6000400c00311380780c0a407005103440404500100300195018504c000c800030a0145c440c20145002582d0360710141003240c10300d0f299484403080c0e0340141c2c101d0080940c010003810302e040003003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 100704568 1250 100703318 100703333
    0x80a0608030306061606020c150a05070206070305062706010306121110020f160302090106050306010c0303020a02030f040306061a0307171e040506010e060a060e0906210106032d 78
    0x9080180101d0a90311820011b0300920060145070211009000001c200400d12a40c1401c010100c600150901003041071056003c01c000b81d101c1418100002c2d2501c410021900c03407880c03280302c02d2b43c060418242d5050f270400391401c03500c00c0e0400d0342e042c0501c5442e0a00c4045407043c0d07607002000704060b00c08405040c41d00514a1448c07103224811251411205800a072a2038854a01901a03803000c200500542c00c01842060240140382452407a600309000001c0c00701c121200080c0c20154041028403201d8402e01c11281d480200e20000c546941e101e08004000380301e14401c2d500d0204602e56040074035031340042564420407140d221541550007003400224004001030494601c040d4860074111013030700405415006900404c01440b480d07040000c5010503100140c002449401c80b510104001d50340f011000540020503903032000702d6111303140802d03045c09801c0d1a0890003c45411504019101540101d085901410f803080c900400090b52102c485890741e1624005200d8500400c08560340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 100705818 1250 100704568 100704577
    0x90302090a0b031009061104051f09170606030f0a1703041a15091008030a031505060c0a060b102c030609010f0b1c03080903070210090303080a060803030606 69
    0x1181004102c4840840009050801c503824118084d41c3e1080481c06100442c81210b2440c0600001c06240c58204400500d450454071040b29803080c1c2840341040c801e21070030419004001803981200f05c9032200303a00d10741300c94044498078028801c1c2d44420307411180000d010404230b40c200da040c1d0b20011003081031141942c0002e1041d2140c2c50515111a0700703007031007501584280d442112031600c1c800683c041159009026041501c8880d2005040c0450803002c01150140042c9060004420320062000c010000d4150302460b400b00020942171032448000c20b62103882d911549007007010a4030a070402c6070b0307191000c0e650400903c000312002c8440000c00c07401d0740844180354140840b42d014000003440c200c802c40e0260340f070740d44640001e9841e0034a80102a054107048400b00ca0800f00d00600c031101e001180c0010b0304200401c40407412501040c41140c5400d0740250054484100c10704001e0141c44541c4030450018a02500140007990f15103d007009803041d4801452941d210b250401085410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 100707068 1250 100705818 100705831
    0x17040c05010c06061d04030e0a18020a02070f030c1e060e060d090204050a061403030705030304110d08030c131514090316080c03120705030301060305070c080a1205010f050109030209 80
    0x80d18075020620001545100c040380045c50460003ea24003458014517134005030710964001c000caa1000e1028000203841204001400b1800584490050008929140701580010380d600030440c408014062412698400d5401248651540480d0f1a014001070b0307405104440c0042d405400d103c005140c1500282075414000d03030089004c401c540c002034110758007654030243c60f42d650401040030710550540003403030500c02c034041c41c01c001c3c4503286d4584038800240001c009900d5814242429503554020a0701e041d000024142c0b42d10f0043c4464115a0010f942c581072000322000005001c541d003061b0520101e51562050020f1085420410250f00600000b507851300030384042c09031704c14071045110020017860009280b140741c180305050400c3d8164240c0703103001200b04401c00102e80d000044a044907403502d40002e459642c85002c44030707000c410314020010300c400200f4030100c1340d000c0d00701038038084007020030003140e40e132401c180070302038214131070349000c1007403040b0400142c40c201891641c80300c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 100708318 1250 100707068 100707071
    0x3080402090c04170a0c1d270607123b120c010b0f0108061f090510030e010507020304080d23040b03150906090f04110306130317040c05010c06 63
    0x7501c4e070341d040c036040319001e10025040d4000c0e4002c0c0140200021090014004c4102e0183c80c901d42c088403a2000320000d202480514034071088420104044418003038000491040ea0f0710b07401d04c1d08005041c2d030a41203000008608101814513024a0710403204039048131600f0042070743c880e80310126207180c00e400c149400e5010707169151841c074803580e005010201101000003204190700041000a4040c003070020704000b2484100002e580b82ca0040e1070034100c40b6041d2020a0440b0305d42103891003000c0e0001c9400020b04440ca8001a80603003004400700c0b0800020320266a400c0001c0340e49001c4c80c8220f544940c822404406001c3c01407002d000e0f02c00c40315104032182c1c24082468070469010f075000d604400d00000070840681102c0d801c004107444219601030203420100d00003010100042c0101d4503040c150004503040200c0101000200398010341902d1803442d040c01c2c05202085024810742c045280b26a0b0b1783e5080d18400c480318410380c5d0019500401e28202001195413000580d821904207 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 100709568 1250 100708318 100708327
    0x418060606020d020609070609120c0b0a0507050c04050601020c06091c030207060f030b0f042708040504060602060610030507050c060a020a030606050c0a02010e0117090106081903080402090c 84
    0x210540240c6001e050150010314210600210007441c0400082c03c00501da00008014042280d1082d02901100c41c0805440d41054150400340c40f12485e80e8050040c6e035000183d40c1c5145a041805407903014040e0043e15111f85c00b000034413054036000c60351140180c1101c080c0c81c1480c40e00d240900203104c0302622812420030640e01864026071503c90a401581c0700c44000c20100da807284101c8021941854240f00700304907040840c80000c0070910185c0304940390264107801801c094183c5d16132004403d25404010001d00b01100d0780da00a0060701c2c051800d0031000b08609000041c400c0c0a01d0002e0808004000c080c401100200405402c1c0e10800c44200612a1003640170042030340a00180300005076030f080c4031840901141e1655000ba020b0040030700c09500c034000c01051060b145034080c04c0c5505d5a5a01e680104c0d180c00303803083e520140d5600c0c4018004111070540c04501581e40c484102c540c44180c02c07200b4051110703016002000141c21000107001401e1403240c09411042e03a18449040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 100710818 1250 100709568 100709573
    0x1030209131709030609160522020a090609050109030c120305192a03051c02190809010c0309050a2a1401020d030c0e041508010501080a11040c0504050418 68
    0x103070b003114056220400002c91907511a10701480724035041103408004042012542d4104079594401d03200302840343e0407004c1d4031756850803584200c4040c8002d075201155511055a000362105c0703824029030000030102c0f9800b00721540207114040540703030042000481d10385046841880d1080c0243e046007000000e0180850381d18a180c02c0c07100d00c480c9601d030a68900d110058400c45000800b0840402480031051400465042022291020140591001043c410054040c0603102d00d020228100401c02d031100c1101d07500688090059071480002d014070760b09080304600b541c0c00090301510340c0d00b0208030400040c04003d50708001e9090b550035120740b503020180070200d40340280d00000da01c291030034008004d5030741880f14165951b40b0b418200560340350304200601d00c00300740d0b400301c0c050366651510703005104a021001008000c088002d002e030351703100c15215840b0b40003050100c1d41408a07038601c100390302d0b0034086d542c140645a680c003403d00c1d280004100241c06020112800c00300e0905e0034001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 100712068 1250 100710818 100710833
    0x1f0b04021c11030408090f01110f0109050609010b03030405100306090f091406090d0e0109030f050706021c050316170c090f060301030f02090903270109080c090103020913 75
    0x25a11592085820a058080e80d2034280e824840c82c010801104000f00000503001006489a82405aa01901c1aa01c02d0016241d0300e540611079803c61080502c0c40070606815000b5512951041003510700c281c44100200e03082e03554040d002a45504280403c1c4210300301040240070401181c07401040c0c4030341d189045012240210080200e0740d0320b540c400801d01c08010614034046440f14010b04031480d140507003940302c00049084004010304c2ca28000d50b183c1c4160400d00103540c010000e00004401850226035601c603a00c580e801502442004421500781c0141104121000d502c03143c0c515038916804112905520002c10180b0444000800d42004481c42491084c80c21081e211760b101901020404900c4103441f040b84542e4081005000089001024030f9003594103442c01c0d265929204007043c158001c1030604413031aa0744161311300042100311040743e482c10003a2900e64556403a00f10b840e40307400300b00644603003010a620041006080500c00aa40a03000c0c90201d034038040256034000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 100713318 1250 100712068 100712077
    0x11040b04120b010b07030e060c0c0910061403010b0a080a0f14040c0f030206040e1e04110f010504150f020c060a18090504050604080306060417100501060503091f0b0402 74
    0xc451541061401d81004400c2c0d0000780580308044200f420112181c0c0c00501100d007031201d850103203002280300f00e19032004108414043d030000f00644003601d80714600c01403030600d91040c000022151305803804602c0134442181d042c2c8a020001c0c62a000200c1401d07a54141d01400c41c0c10025600c0301115410000c500c07902c8000006c11601c041d46082500341215144550341065191034900745080005984040c02c44045412900300200640c0e5801000d0504d079420044002d540c3c6211810032040281c1d0400f40702c041ca404030750100320540e01200450305401203001d986210b20580401e40403140c060340d04205c104c1040c2c41240c0743c61500c3c2020131501d80180c01c5400c0840d01b440c0c0d038003038440741c404c2c42d00014120390101005a880d2644035030750348580c080d01c0a040640700002251a41c0c80d01800c80f405400d84000b80c440d04845005d060fa43c0b81740c0100080d942c5031a1074000308050740b0440844e400340c66140d0040284c04402c410040801c1801c0303610f9101d007591140c0000690f292400900f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 100714568 1250 100713318 100713329
    0x90f06160506071b0314130f030303110304080a0c320f0a0305030105060a0c0c030f1505040b0c0d021201090c0f020a0b01061103070b090102030709050a030c0911040b04 74
    0x20149428145811481e0680c00f626a1041c0100201450b0034a03656180d051040d94062600060513140d07030381105581e104d403079080b13800f04000d41d8020802c1031444000c6000c0303d02c079607010008900f000d40d8401e00d40c001038500410f40c0008000c00c4a80502c00c2c007003c0f107868003440760900030005908400b140405441000c1001d0a811925155160024041c41c00c00075070b040044c1040c0785d2680d400030150f01c41405100d11070315010071203a004c144199181100e0b03651000d0034030121a00d80c100680d41741180002100e00010f01c0f0142c070048141030140b0780c042c55004010044540300c044000c041500b140042507802c070303807d101d101c1c0c600c0340320100c040c000e01c1003140c001a07100c8a85401030080f00b400e02c00c034064bd0301c020401c4000076007040a40f411180c1a141500e000004100b6460540c49186000341084a04100f40000080c06600441c000d0f0800e440e861599603440c010321030001da140c80f0240046101c42810410010603030842200400042c50f03591030a40c5442c6050902d030071a4006 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 100715818 1250 100714568 100714597
    0x70215091011040503030403030302130305010c0206220c03020906220c0e1e040c0c050a030306140a0608040803090312090a0203060a05060619120204030b2514090f06 73
    0x48041440080c4109804003402c030181c0b514040c00e00001c240e8034400c5220090405500059800c0d540300380601c1078018640c8140240420580e541e0300965800c0b007a01d41115503014101c0103001d2240315000001c0c81a03100444212561864003006025880100200c0c2c0000002d407200d01c21017211442e148a417200a04002628031180100134001f505030086079024903100b0000110312000c04c80d1400d40d203e41183c02180c00821204111403072030005000405a202e00c0b504002059010380103032054a000c41c0003010030305041c804006920700340c3c0c820b40010800e00d40200d170103e22107034011a030100780b4130101d80c9400c0d84403072402800481218000c0301074110400c048110310f814040c40703412407003400b07003884582071080c0001c9079481030039607030039400103030070004c074000c50150040c0c1100d03002039402151a00e03600e04204d58088412681003d00546039040c221545041005200486040f95030310303920300000b640d1a0801d503021b45891540f000c404113052900d5902c0000170501000c00716032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 100717068 1250 100715818 100715833
    0xb0a120c0305100b01080130030203220f03020105071b031202010507080f070f020a060e03070201030b0d0f0f0c0306090818121c0509040c09031506050112020307021509 74
    0x1815401c20b0122030f10400d185003407401101c1a6a032240030b05040d2440c4601c42c0702000c014145001194100728a10302c1c0b8985102c4241d018540c000c00a0b180303081120b00d034080318807084a10003110360310a02540760b004108039814009035110310081c00000784102400d40c001e04042c5200f00201c1c00360f0f401120100159054072141990a004494000c800c03410809402d04114114442500c0020690f0007040744081d0400c11052007040303040049500a2001c204542d0300c20308441d200d501910003030b03003ca4180b214002c4181005020061110340006441400c00c00c80d03580c0c440e141001c1340c02564100d1002901001080c030910650082d18840c0c1520b0382d4604101117041074041040603082c0c82030a0205602c4501d02001c9510100e0010102113401c10281c041e00c1650f40d4000c0e28085030f0400d01c1c08401150040d00441d6600c180d900401c011006503002c601d090007551800e00034075001900801d0b0352030f030581c00c513009160015014010341e81c00800300441640301400444101ca041e41c0b1070301 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 100718318 1250 100717068 100717073
    0x109180203120c070909020a090b0303120709060e06071109041506080709060819020609010306080a080903071703040b07020a031a0609070302070b060f030a02190807090219030b0a120c03 82
    0x3000380024141c485e014000d9010640003d1141c1501e0701c502e842042d107402124046a405004940540041c10f402804500b00100300904104050180c3d0340071443d41110544a45049401c1c1e4100e5584803e10243c10308800050216150300a001112500564107103083c0c9014a4090300d40502403840040450a260542c1c1809403900f83e404a40c00d45c204580300814208108201c7d0a8643c042e9081603481440d140100c00502c0d0580c8a075100d80a00d042c08404c10854100a00b071074201142140c00158550058446440280c280404590300030441040760854003005480401d00040500b903101c0c6d0740f0786411a010b0030b502128031403e001042049114a00209071a41202d40ca00c0e0031420308142d550f58160340e01d40074241c40d12400c00304040008a60701080320b6007005601921030300f440e21141010b450081468050803401e80205400031800c2d146510130750b1100718078140c03030348442807001c2415001001c116a9040e003040e05a4400306468004082c04601184a1003801c4110352070350 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 100719424 1106 100718318 100718323
    0x120210230d0207060e0c010c0f031e05130902030702150406020f1b061b04030f110312090a0b120115021c0c02270109180203120c 57
    0x10903032194550364020f03249a6105001c20701500c60360350b5425440f6a510380d03c1c1400500c3c15140c1c2c0c808a4075454050032618041d00b8041224101c015140c9801d0005803105404940d0000700c8400500c03100b03081c1002032803400001c60550600300720007902c2d400c0425080c0c4000716014085024845158100e4103040900c00074103507a0900d81032004412099030300e040046024420010f0341c00c80c09600341c424413a0668010500d480d0465451116802c01002c0955001030340d040c1c070740425101000844026040703100c3c1d051301c80d2140010001c080340d45410488548205100f45001d14401d50b0b09141501c800080c50741c6060b905c4a030072450b00d25042e180c541c1ea9000c8040740a513190300a42d40d81c1515000340c80a030840c0844d0400d40c2010302841105c07078809070402004204407003a950181d6144034022034203884118036600068a80740484001040b01c90001418501c040b004 = true := by decide +kernel

theorem cover : BRFrame.Cov 100539568 100719424 := by
  have h0 := BRFrame.cov_init 100539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 100539568 ≤ n) (h2 : n < 100719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
