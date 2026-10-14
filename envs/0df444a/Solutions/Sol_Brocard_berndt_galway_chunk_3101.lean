-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3101
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:39:31.68543+00:00
-- url     : https://prove2.me/submissions/22ff8c29-c95e-4b20-9f13-c1949e4f4a2c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 557553956 ≤ n < 557733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 557555206 1250 557553956 557553959
    0x303070c03141e1b181e0705090a0509060a03020a03201f2102130801060f06050f0c0309030a050a03030b0a0b0a030f06182013030b04031b120305090601 67
    0xa05484514034a00380f20115081c1d02011451810f03603010421104403c070410807424510b101b2a101449058860b101c01e61307691380004982501484035107a6002c000c180b000c22483c9050300503550840e4000700f810070f08560300c2e800151080d041d50710031500d0a08941407580c1d074000d40703840178044080985940742142c0081e01541ca00c1040c0d080030745e090201d8020301d0b1130402c5a00b003120701c031003450003004c542c1c60307003450b405442d20211031041064940c02d001d00405c15031510b5075042c084402c503440e03142c100062002c2c582c1e030300d070801c2a40048502c010f000407403007a54200b228225230b41c003c0d406040760360600d0500a041e02d810101860150b4a451f408100a485810440d00108110701c2c00062003511040403c6c050111907001605103180d40024ec000c2c0d0038190b00003030050003200b207102c00c14141a2a60001d40c05007440507090303514840e2082011855030364400340e1040c460301d003191080d8a480070b11242d0000c204400c1d05c0d9200418074a0000c2a01407113074a8204100c1c400800056 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 557556456 1250 557555206 557555263
    0xf0f06060337090c0801061802030c0c070308120c0a09030f2a0f090e1f0e06010f081005010302031c0c020312120f0601020a0308060303070c0314 64
    0x500c80545241010641c018260182400c40821402542042c5010068946820030381201800386a40c0540d06542d04480002d10183c2c140318003001c5a480001901900b080120100c00a410040c04500a140c041014182d106801e0000c2d0007d18841c0c3c001c1602c404c5060140140200c00419140703820004010991800c0c0e0041d81342d104603580b2004c07802003600589003480c4401d0700038800c000000c0b04118648038104880c100c1406950f2680c040d038084030f40c0d8901c820255081911a81d203103030041c609502d030b0508198010030003aa032104000c210418101c01c0b00d0b01c1d04409a2010364500b48031a818012007200344a643d02c5149640300c10b004c0d550468000a40320300c008042031100360040d56414015a018a4201d84120f80040070786281500c40034a81445500c41f010301d02c3c2841103500000c80d1012804d4801c0c2c080c1d40b06030700402c404100e40c0c0e0203070341400001d080554184000e200c901c0000300350b10441000780d40704510802641001a441c189032514003c0790481d00f00040c412030003071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 557557706 1250 557556456 557556469
    0x30702060108070f030b15090a0b0102010f14070c0305070c1202010306050402090310020c120415020f06070509060f0906160605161b060612060527152d0f0f06 70
    0xa698101b2581181a202d022000030040c41c40c4404a400440c805c2c10416510030550180031850820f030020300c0403901c0101070384120351000c5079403040e032591100480c007494880c000b050301040c07083c20624a011016140e06581e651a54003042103c042102040d0455078036010f0307940106810742c0c05600f8100ca64000070380382c40c01d00103440340c1c2d96404160540c803610204441240301c0b2502095666075900c8950301c118010b00c5042220142c856202d8007a0b030408005a1a8070038001c2e941e50b18100b454400030803001c2e51024199040c074940901487c96103030f4034500107107920480741c009108070001905e402000d58000410280031031a084d112100da4541000c4009030384010760310184a1a806884c1110050440340c109101c511a034090900401c0101d510050203695880c1d0510301030000d00340b4446480c10301e81c01420044e00004008503c8610000810713420031210841c8002c0d4441000d2691004c544903880035258400510500a01c070710845100b6170090301000004440d89050001b1815 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 557558956 1250 557557706 557557709
    0x11100b0a051518010e181f0803070f020109050411030a060806011202040f0e06010e0103060e030910050c0a021c0b062b17030c040603050601030b0112150b040b030702060108070f 78
    0x80c2d4100384003d42283c0c4600c01c06202d0010003003031030144100c2c1204100803403000b00d40400c015000711211100c07228034112000b00301c401e01c20095140c03502503514078403408040c1400f00c3c1440300500000c28943d031a40595180c803044a25119142d180c103641d0740d01980c0300b40d0700644181c0c01400051012056403180d074800d141d016280030401e5185824008000d00349072103034800341d000752400411102e884180250403240504c03818010055580d047c2c4c2d80b61301c10b0552440d4030981521148908c503004030040c0210103140d0041d900c1448268000c03170900045107043c000b080101d00314200421070001d0320240c00140a0b92900c42094040074103d456503a001d1440d00c41a122400f0482008001032520002601414040391681825105d03c8501d8001e4003401c80400c0c203110001c0c40f00d52191181d4000c88605940754146282c0c3d958000c40145881d03201034200801225000c141d50861000071300040c8040c48480c0d90f02c4c41c090f40002c0c2403010607001454281c10010080040c0c0c0c61074043c910 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 557560206 1250 557558956 557558977
    0x130b0607030e030d0f2a0501060f03050f061918020d2109031502030903041e0306050601080f182b020c03070e070f09030f05150601032003040311100b0a0515 69
    0x206c998500c00e0004400e03546440042281d800e052000ca058401040c2d020200c070311030800c07125400741400c03601d515004d00700d40c4059050300101810003e81050303007101106074007a080d1580001020b8010602140340140d095030004640182d0070880c2801c0048020307150302c0c5203001c101c420304594030002080c492003d051003040d00031010074500c00301441200c000f00740c01070110450003036452409141401c14032040d59002d18000014a5950213048a244111040e00480000d0341d00c1401d15038030089244c80043c150f1140c4011681420140c0103904801c040b401c012810441c131403c0c1c02441c2c168090310642c02900104400c01026401e03c80c01c0b500001c06081603400300000d078408581c0d600043d0700141040003010648003d00c00c010030091050b15041505414555510006406540441d8002000030701020ba032016010182406190014802d14045404a20312840c1518001022018060140d41c070b260b155042c0c0b44c8810004020b100c04d0702c80001440e040f40380c108042c0259944c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 557561456 1250 557560206 557560247
    0xf13031e080f090612090d09090b03030703030f0b061303020f2e0c0c090222060f051608120901050106020a020a0509061f0e0a0f050a05130b0607030e030d0f 69
    0xf5880780d6074900c1a21030032403074180001c00618105039010760713031a9407072146408134440f220082015040c5028030b51a010010300114075000059404030000c3c001d49210b41ea00c5070355805605019611031006110782d60744088040b40c1d00d4103500401107201e800c0d2050502c581c500348010300b003003050b00c4403591000300c4034210000040b01d01c1e4419141113a520a00400c0b603030400b030b40400c214005601500810307401050726a2a0a036043c14026111218040c3c00d020551904c0750110644c031071402003800004003500000d08001c1030391054036030b400041068002184007020048510000d1040a004210910060107004d40301d8001c10f206c00a98002e140c01401d91000161040d20382003082004c0e9600c984041a186103030b07140c000c104203022042c69106140000001800e80b8644144205a07140104403042c4246448208040f00d80003070711000e080e64550094085680e541006401100d02984039031003016116803c0509001484c03845006202d41c00c40d440e81c04540c0402114140642c02944 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 557562706 1250 557561456 557561467
    0xc0b040c0b07080706140106052205040e010204061e14090409020904050c0102070512060c281d0108041a07020c0301091a010b040e0c0f0f13031e080f 66
    0x1400350400360004007039001c0000b86041040050307001440d140c1d010b558100450325001c2c5505804080c00e100ba800051000c1c03051040400310081d0951041c0106400c0149140c0da40004c20b0a94042003030841c0a81d50100e02000810741003900c4408011f41609a46103010200c4801781443c038495522a0058101150344181610741d90310094100d5002081d0040500e81444d0a41c5c2c2e810b2400104ca0040c0a00d07280040c16082030341480d000c0d8250440640880d07038503640d03e900a40c004103d070700710701640c1080240e0346a04034011818144a2a0b4603242c0310400340c02c10782d000b5159815040c0c1000181b0301000003041c2c80b03000c40304030007031610303e0800c0d0754540c103004078501b24243d00c040c0e42c954a080d024008001c4c101c038013810307442c175000840403c9030b0b65841482c5072401a4811410003109a01c006182c41424100400002c02c07240130485c18406410213244a64019511088440c0c0314803000303000b402143d64222842ca9a90a80803840011a0303442d1010703401022020708008902060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 557563956 1250 557562706 557562713
    0xf0112030e0609090a0515010e0f0909160308030a050c0315010c0305091507060b04091a1003060e0d020c1c1e020607080d0b010207140f150d0b030c090103030c0b04 72
    0x12607040460041002040317041100345540280300c203881300c0c0130040c500c0610020f194024118002120300050140c488840440c00703100c0c4410004144650500034a0700c8500d00380c2038444184055400780c00000c1d01ca02d0301d881842c00300c0d0000b03000414100030500c10000c5610050812156100c801e04e4581c130101d4840c03609940501400c1d00950784510288403a44031140340b14044c001d040d0081030180036400e4000c092200b15121200c0184c020411240721460944070f82d642550402500358011015640d203460b9107044800c03005640c0800d4001e0000c000312160f0400409658480c112102400828051000901740959080041070460401d410f0242681e61803611529181c01400d019500c00c900e242c03c01907a4440c00e410709485103800001001c0d035100081d13450603900100c0c1100004000581000440d601500f0361650060610464100b041001c4004e024182e41c941b9002c115215020200350806604008180c000c5142c00010408254004400080c498010300031145a0300c071800e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 557565206 1250 557563956 557563969
    0xb0a050d020112200901090e06011b0c05030d1101050f16031a0d2607020f150d06081e03131202010c0803040506060a051c02063403080f0112030e 64
    0x4415a034001e4901807001480c4c0e220402058039907026600e1042194803603481240c02c4909071403203030000e0300340c5507180c0c803040b503a810798403866004490301021242d840c2c00091419400c0c409090001d41070301402d644e910024010075401034500003550302075181000c0d800303e6403c00410b00354205503c4d08484103540b521031419480420300502440340040c9035043c46d11038002e00c0d0310744250010100608407400c00c803007819100d81683c01480014040424001c10045459150002d00184820050340d007100d00144201001489504061701840c52040c51900c584a0840150036054008001c103407109000c08107030308140c1d82c03041c3c00b40b4421062800100c41c4d1950410000f081000000103000602c800002d809204842c122035012805840307100384560403030286c443c2c41240e00d45841000040c40e001014011007014540c400740c415030a01c0c101000380c260742040f80d071040c1c80300d001002810790044000e5402141c1e20356130f00607949001d021119105034427030301034100a020300c4c64515950341c54 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 557566456 1250 557565206 557565221
    0x92d03020d0e24040611061005040c0917010608010b060a080402091e010303180b07030e101817011104030203150a020706020d02190f0203160c0f03030f030b0a050d020112 75
    0x32090a0520340800e204a22140d2060051402185c0b0b0761b2822501244001441403103016007481003c94546403205010141000c54641000d20a2208002c108112a2401d42c00790900100002c00d616240c0341032142145d0300b00b0b100a006da0010003180510701d401c41c0010350000c0e81924000684d9031094000112500c1401ca5002c0c08800600004149980060140700013410643c62030400780c4e0703405c45c011407032145002c014081014005200e040340780c0000f4040b0080d005040c08040040d4190394240c82110917040f03054101400c001d45040340704248210709103540c0b0098144c0c40d1a01b5500080d43d18007880c1003025280002c100001c4c900c2c0281d070150340c021030b40440e0070741d2030b5140c030500c0328080d40008100f0394034540c0b0040a8520766206003003007030260b03c3d40d070003843c50f040c01c500350345846480000702602c080e0011000020792070410502c2e00000d501a544000282c6540e242c0142921100c0e9002c030310544010b0000d1000d83e490051500885609091038144000442d29100140000e03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 557567706 1250 557566456 557566489
    0x20d0c0b070305030405070506041a090f06190305060a1d0c07061a0909011a10020a120801030b0a050106120b010e0909071a041202041e092d03020d0e 66
    0x401e4450400d80c200b4061801540b00303500740e658050f01d480901080d40210320950902d00c44801c00c0040108000c80107004d4100050000381c0440c0305540424042d5001c0203024004081100300c40b810b003580b51040c2900280c088481803000e501d000d1440c100186c0e07010a802e5106485004108064407040442c4e90003948000d0510102240c01c121040210345d544c1d8440c0611304c08000036510b0341c410b201e40d142440a40c18000040760b455401d2046c071303800c05940c0200354401c40c01158040340040200c10a81811607030b40c444690304511b40f8401544001e094420f800d030601c8014000e460300240184000c01c81701500046501194004036082ca001181c3c03e46c010301010709101e9a030b000800c20506860b20f58410394115480180240b4491065120315500f0340d261440c8580149016040091000840c640c2d00400782501000c000840785048802c5400000d01e1000d060071741a40d01c56018810b0303440c8a90740030032203503403000b03502e810303e0b08186010840400a0207903259242c2481c42d000340b54 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 557568956 1250 557567706 557567729
    0xf0741210f07170403120c120f0905030703050313060203070302070b07020a030210030e190c260610080c01080906060111030d0c0c141c030c2a0204050a110403020d0c 73
    0x1d00300d40c003d85903071250005a8070003511045102083e030003800c50004280e48005401100124000d0481d0040040008401003005407070f80065641e80c02c225a2014502503000b03596503103242c407807100b0160600e0b8411000d6402c01d000c82c030040781c6c01007410780c100e51400708070560f00d0300b82e4400100070040c2d58000039800040c0f6039500542035410b511100841c0c014400b00e845030b6601510588140142082c02490005006c07018445031100e03c140091607001c02e544041440e030369084544c2008402c03545194485500001001110340c10402c810b840d410a003062180c0d820014041e50300d03064002c1600e414006494040a03151a0410481c1c2183d800303030790304000a5039500002459010a42c1096882d50100ba0000c050040c0124001d010025a10216050305c00448001c0e4054601c912000d0184030717610150346803c2e00466440c0c500e4624500341c0010403401841048110f0318094031094080389000904501c02400000703c5e4240c0380c0440f0310400d04a503a10340700c406c080c05500100345148 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 557570206 1250 557568956 557568983
    0x30a080c0709020d0905060601030e07031e12020f1006060504050d02030a08130509010e1509070216030c05091b03010b1e0a03020702031c050f0741210f07 68
    0x1055205c0303181c05202d0310603544a52100c200441c1581c01c195403170300240c1c100300e40400c0065409402046042c218510980c076983e044e8030ba13001000309081c00e4102503000340401141d020b01c03c1c4004c01d0b0b1505541010420b03581005401071040c000c5000d60350140010030030740806c0d50343c01c0140400e407031782c0710540c0381d650080044002007a00091041601903070b0f0310301c0042072007a00c6001d02e82c801d2080740c40f840e0005080e14100491140090403881c01d50040200518542e0790b40b102c0c120186000c1c012188080d40b40c841840160f01000b00f041c00801003131050601c1ea40c90b0031041b68111001412034a0304c1310140d41040d08484403565407039100442c0010810202034154020b007800500883c00d44404620040c0b600d0f252407510711000740092010801c44c50302c00244000b4040d0380b03014203203c801c05e43e200742980036103a07290321081e0f080d04414400d8001080424140d000903e0b81c20002c2c20168074204040260202c516080401007030300800c50f07040c0440c0e50b90944104540201c0480d019a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 557571456 1250 557570206 557570227
    0x210030c02010c0e030307020f011403041211031611042301260a060518030a0309060f090b0a09112701120305121015021b0906030a080c070902 63
    0x14039411200030059420000d00e84421801040c01604209000d006507140280550801130010492282c5905200a803114441b0100b07145000e540306501c290034640480070380e05000382950301800d1641c0082d500402c01d180700c1b55040c0c0c940c070342100e1f804003420301c045030250005000f405040c00c1c540389280c10040c54002d1070400c0030740b042c121038060802c00c050141c0181e24140c41610b04455004682c415a108400948640d00255000112024005080444000044c296400580100b0000c0d07160800e4206210342ca119451003191a2030080084040c80c1d5164030140c000180b116000550755005201800058600ea0941c41c2006020107041d884000c0d04d0081e4918070203a111030312032070000200c2e0307100b820b040380308455030142c40d40e0703041002c18032190b0000b240c010b00d1008641d203480800184005528030024008a054000d002d0038075200c441c6c105c0608507131460074071841440041c02816240451644910740e0810b084990740e51441c2c61051401d08a0f40c08411032510015240640c07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 557572706 1250 557571456 557571461
    0xa1202040b090d17070b061311040e0709120f031e0c0b04110301090c0f060e06070213090b0c0d050903210411100309060b01030b061c0b06030408090108091606030513021003 76
    0x2050100c4185125100d00c0803100109d82494401891101081009105504401c4801507200001e813404c0c850041e00d828405401d04503540c03048540d1071012292004040d049140050600c850302041002c56180343c1005100114951001c0e2400302c0351404a4207001c0e070360140072030100b8050024095403500780342056004905116a180320918954049070700c0b40305192003020250000e000300e0400c0c0554082240300645003c2c41007845554402c04000a205040b80911035540450704685a2000c841c00d04140c41e001406c010390343d04100000105885690103444d90080d1300041c13100c3d180d81d207260901842003c861300540c00a140721000c198140e05401c02003006c2d2280c0014000302506000540030f6886a003410b80d030200c014000b80031751401c200b00c2104c00440e0000007203410184d41012072401e80c8140d40c182e6040c000000d00a11558000c81c0440c0c01c80e0601000388144801d00019180070304160040b2020562500003246507080340c004070b0a4041d8009000c1507940903c4070002c0c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 557573956 1250 557572706 557572711
    0x1b0d060507171005090105062a01050703060f0302090a0506030f2a0409020d0b1e09070801180b160e040e0d1d010c1203060b0c030a1202040b090d17070b 67
    0xa0342e01000058400d40e5030f6051142120005440c101c01c0e40d0070320040118541210200344540e5806802c5100c0c00c29200c07421800d80c100e810000207490802e06001070964121340c119550224486104100503101c5000381580603034103c400180035215400007034140f030b4003882c0800440c0301d1008a10010060940401000c1c0d90100d11112149581c400307001c01d4400c0b144020358454040401340c404218280d6603550700001c0d4a02c4c02000c07441f08944006548001c0c0c940351250b910080c02800309400034482e40c080d003501c0100681d191070741c039a10781882c44001411341c0200381f117075803e0380e030381a000d04800c10004000400500220b1510401e0981d038886009019000a61004000c14100f00e44000c0301d142400c103940301152181c451321074604000204c0c9505003010340c2e80c14001245400f00303001d0315403003250300003961303940004203001403207000c482100603051403041104100c0c6039a10001c440e03085106640a0500034441d050400700c80b8510390b050b94100000061170010850b054070241c1c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 557575206 1250 557573956 557573987
    0xa0b0901030c1d131101050c0a05070306060e100303030b01030902090a0b0906010801050d0303020714060f01090b0f0a05131d030c10112203020d0303020306211b0d060507 75
    0x90f412030034450404400c400c1522800110403850280e1400714a030010701c680c0c0c0002c103045c0181340c680300c203c216103003512070201903803607170850003040c020407026000d620000d04882149074250b00b0995280048110140300060500d41e07500c40640c1164040d0304041c52041d00107000c0350042c81c041c0c1065014160040c1074512a003c4003000400c40c1d80564a207a0582c0d0303010b044000788140700d54003139000b540043c90903980c2c0b008440152039000b80411020740b01d07084500b0841401d501d4100c180c019504001c4c242b61040f186904070204548030064540101d407011210310101d0981c000000c00180b41040c01264980da605140d19203810b000001480030141c42c10072511051031414140007221111540344420324801c11040b800b283d03204c15070480e0700c01c1c0c0f215050074503a03603135001401050001e4021400b0030b4000c03040080b135117071400c1029040050a04102c000300100c011590700c402603042d03070002ca2103c0d83d080d41c2032510382c8018110300c90344c0264200100d081610b00900a80300030b01505 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 557576456 1250 557575206 557575229
    0x102060f1e0109020d0e01050415180f03020c18071403151f0f020102090d26031509091f0c2f071205071404020c060718090608150a0b0901030c 63
    0x4845009051003401d100d541c000303c5c4071942b1081d4450309805002e040e0341440003803a0b0800018003092801c890f04121030300c00d400501044a40100344000241e495180c1500107c0c07070300400040d1500a80e284081c0604005410b40e03030740c0e9400070301d0b8000c0c00c0c4820941d08891302c42c06210b4001e04802e0b0001b072403442500c641407003401800c012801c1c6c3c0f03301490280c04c464015031100010b00c01c070100b5248003e006910100601c622600180c00b500110381c50707841007040d80c08078012800e00006d00764010500b03c0140c092400340503503030b01640c0750003150a50845d0740d8000d0740010a1003410640c0e01c071410010300c49440030003080810b007001c1c010030000885008003c070010350500c0904400701c0d885d5004c0c000d09507c620300420b203890013960550300c0360056000c10071840312030307010300505202d0045516001140b498903003660720459102d8101d031160300d00e411000c0c0108000040c42030708660400d20000e600c2e5582c603884401601424000a80040c404000071040112784a100700c207031048078001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 557577706 1250 557576456 557576471
    0x51215060d0f121709010c090306090f021815060406080f1506130e010b040f291b06010e070509041104050315011509030803041b050604080d0311090102060f1e0109020d 74
    0x5c2900f240c03551a125408148002030420000302c0542000f08a180102040040c41444d5004070700d035880359421300200360024604004c03080c500c00d102c4440348030f801c0d143e0b10701b402d04203440501040006800781600e0b400000020740c0b2000d03408000131303c44001604450311440e00780703180c280079001c0c0e000310381079451040004118042c010007500c04643c0c13980c0a0540c81c41c03400305004000b01440e540a040c2d8101c1908010000b076244000305400040080b60303410240200303003140c6c1440c0301038101c400000d603240103010303240b0390100a41e0b02c008822203000442d490242c202c28071621499204d15094000c565907107540d80b25040055041301e010109451600342e0142084910321954000142000424070208000c02c2041c009201c0381a010304d00c0c0d24032240c4841c0010b025421650240045600021170311076625498084c0c1c00010b007400d100a801e200d07041001039180e080040020301c506003800001980c4080d40070b116a1040c2d5840400c00c101d5850b1050f46000e58000e801d17290205007407500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 557578956 1250 557577706 557577721
    0xf0309030f0a020d02101205010609060e040c201c0f02070602031e090f03010603140705060405151c09030e090112200d06060e01051215060d0f1217 65
    0x142c480c00298010a4072440c2c010f654200280144ca00e0306210030440814550705c1c072500301d446428042d2865071900c4400070b192040003894420301580581c0508c3c00c00d8140b0401c1a000f4021031000d00d0000212614091860304061030728124016040c10303041034140c0c180100b0b411180c8900360714602e6090b6111541c40d218140e90b42c0c031030003000d00351141c00a1118248041808003030600140001e024201900e02d134000642541d40da90010b43e00104d0081c0200c440f140108003010050105894890909240600243c00d0000114400711023440009446054843e500c18468214800900c100000300141c180200400304405082d070069113690008a5260058000a0ba609500c80891101c2e440e42c0e031465901020003000c40b036001198248a007001980034001c200240045251103149503261601300547c0707105030440016240c225074019402e9002208489074000c000f41c41c07014452070145071025010f14105009040341c41d6000030809119882a1040d2045114004964060300c0c0d805 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 557580206 1250 557578956 557578963
    0xf100b070b040813050d1b050f010219080f0d05010906090921020304053a05150403230307030c02060601020a030c0611030c040602100203101403010e0f0309030f 71
    0x25006007028403100c0000300090140c00041c00300b1003510460300d6000b692000840c0e030190031201d088600401c1a0316900c002e080484104006050032521801d61109020020392101001090340300180145007840d010304c1882c20407114502e0900006a903a8685e4603009002007900707021300e40c0b031503041032030015005401d070181440458001504804480b008070700400d41111060415055020610000400e43d0340c11500411442d0001031050454407004045a8004004030100c8205407441c031000001c5180054210151441020036954545032130034150f940e068441d20f0004681c80c40c150741c14034820500099405441142c90a1100f55034100080c3d0301c5000c100e481c20b005070f0014035280c010038400e44101585a002d100d00040c83c15035058000119441141c084401d500001420402c00e5810801c100c80700c01e81080844c114140401d9504014029200b8407511014210148400b90380a502c0b04111125071022200c00c1d203213004210b522a0854074441c0d1182c014100030a80d06407010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 557581456 1250 557580206 557580217
    0xa08070308010b091e130f0207021203130b0c1006180c030b130b0d14070303120903020c12030d061509050a0311010305041401230703020a0c080f0c060f100b 69
    0x104080b80e00345041d40302c1091941d645c22980e0b480001e00108500c0580c16108082d284580540050b83e610b2480c014007090484040c0d45041d180c0c410480300008080692014090707422803188259aa02c00c0030400c1c0c0380122100c0004840c0349807581c00180c00780c650714940204415000d050044118240c02503089440c0d036110140c1001120390761010383d200591103c2d11041000300700c500c071070405407100a503140b101c0c8100c1c5c21943c00890f0070b100307150700480c40200550342c90b5800d200000a41c2d074003d45a20212100a00640b100e000c0340360341001c1032007a61f0f20024491010410b16655030081c05a4240d01b00718840030495045010503075040441c035180540c0d810519009200f10154011401090000c0c415a000c0400d1143e10480400138005c00c11a59a034010b070642210850480d500c1e112405030204040c94410800504000c0c1c011030f01804803038000a0190b141c18081103500254415048014420b010f0302d820014803e0f00d070070526000d12404100c0d402d0441e00d5210306040ca1050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 557582706 1250 557581456 557581459
    0x1090302070512010f14100e0903070303090804030b0709053c1f030902040c26040501020c010c09081005040206041a19031d07051305180a08070308010b09 68
    0x70801071180742001800c0e0b00d1842040d07000040d9901089032404100c44084030000d034810451024010050a03000003140a800c0e00c11016105d4100a118203541c0c0c440e0200090615840b8680d6030184079102c41960001c50300b000f4000e0040c640088010441e05803801b50781e1040303112a81800303805003001e01e1850390020142c409012000c542e644d1035003a0540390007440c4c1c03000c5044007444981d03500c504c051200e20380716140424520190305c1040140d514054501003040700a80c99500301141100c02d000a10f075070340c105464561104c0c00e00501a120307980c3e5a030700c550b0800d0303d007041d041e0384110407104036001c0c00140c5140100c1c00c24074070b0946d18140da010f90b200b08140301c01e01c500c004c194240c4c3c45102140ca219464400140d460345000070000004e1030100e590340c0091503103040c44d19601c100d40c4031400c000c0d120b8075050a0002d100b004002c15407003503250b61480010554212380d280e817050014800100c44154036540f0302011a41e2091800300d00240001c0d000113802d04610081e617418410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 557583956 1250 557582706 557582713
    0x20d1505100806060c0d050a08010b09060405101e020d02060603070b121807090207020f0d0305030703020c070302040501030c1a0c0604080702030c04090b010f0b031501052a010504110301090302 85
    0xc030700700120740449014240f0b5610450805c1002d88258080003500120505916001e88031041500050202c00c016485818652000c00c11000240e495008a80907100100e80d145817210007008112840e11030348603001c6040c0c01c3d0880380200d46800103203509028100b07500710b4003160703150418107841e014540f00c0c050340e80405000000480c220308182952200c3e6a00c01441da021003440090b2a201c3c10f80d0100104a80c001403e005504060030988011401618004000e09041c0d90040103440f0048c4410100741d408959a00002014049000210780080c000c0c040c4d561241440c0d940b40c545c0b403142070401600303400c4024008102c402960350454280c400352120345c1ea0f40c2c5420481c0c0d0f00480040303903d80641d20b96a01d0700c1d0748030b200380200c480c0203403c01201e541c1030010700750f9181450b401018202009104021307014072983c402c1d0058000038a081e40e00c0b51403c2d0111241c54452100c0783c1c0d0482008140144e500d00154001481140140e0b000c3d4240003540c4c003407500301c40c44d459002c0c00580 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 557585206 1250 557583956 557583979
    0x30d09080315032d16031214121f08030c01050108060f040b0423010f05010311010504232214100302090f1909030509030c150d0f0f0c0201020d1505 65
    0x200e03e0138035625412407510035108800b580403211151140250011120038401180b0322240f5a849007400168107552103003240341c0b507810031107001103410041c201c09503420184c004090521111043e40300400c0031070304403034950a14101160290600340900001c520038900040d90340003001420700d0050f80c00c002c1104013502c81c3d40b00c100b8030b00c070742e94599424580000d02c038a0703440c0070910a020f80c003048503600042550540c50310000c1c0c1001d08035a00c3c10007202307000c11710511122015407030203291049091103c9041200115000c1c1048140c400700c0b0403203081415080c500e0982210350040c00d114400d0340241d892045407680c03091640000b82d004285540083e0125000805c1d40c0e802c60710301000c108640c016800c40700c007035881820044000504c00310341413041d4241004400700301502262644102c1c0096a004042806031078252128203403113400d404074081550f402843d0246503000b082c0040510400003901031351012401985040ca001c070f22010b0300c420b0001c100103680e00142000040b5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 557586456 1250 557585206 557585263
    0x403030c031806020a050d021c030905010e15010306110f0a21110408100204060c08221d092817031003140f0d11030d0908031503 57
    0x854400100310180030186001d103607110050400b40005001d15030040060786042c0c40c16900b820560460311007554041744146c0520a15003500840f9a01149400540540075041480c0583303050b1000081d00d0146201500c1c640e80c40300e8801d81030341e006400c01e00c1200e91243c0001900c0c803071018800554070040c010000391510420b080065050303102112034170496132600030001c80301d14980329403980340009020090f100c000d0000c226004002c0100714203041c41d065019040c8045030310000d02482000a46800d003a04000c002070700005a040001840764407000c10000d0b00c02074010440c0080d290100268078014005201280e201a40c5240b1000c0e03104a07442c1c00035a0444602103030148030340e41111031200402c9001d1413049038001d0120f840780345141008081c07590b04180c40c0c000fa800c41030340500020000a0b08041c507842619107100410080e88100f1b0460240000071500d4500f420600002d103d000d101460240c04030080b00d208000c00042050364030282201c0510414001c1d14034144174 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 557587706 1250 557586456 557586467
    0x403020405070c1401060815060a0608070c0b0108030405040e010504110f1804080a030506011805090421031b0c0c09020d1d150f0405100b01030209060c032706040303 73
    0x2050b00360805042c24101956080c0c085019040700d190316a541c0c2c2d1007001040b00421000e00f02503e90007801ca81400d0000205403900d050340103003824841c9020225031000d02c590261076925400c100c901c140c55840f284490780b00e5201e0310a00d0712450400092408583d018400d40f0b0141d41e10007a011441500003052000c0f4001044804da4042c0900d0a007600c074881010005110300e200d1585295203209111024007120705c080c10071410000351045849010300c44044580640e0b40031501c0300c000c2d640340d182900d001d401c0324116000ea6507003008001061500354000c3d03803a459440340c1201501e5241c101c11030740780490107006047c01c500c02c81c04004914091380103013101a0402d4000c503d2130b5140c5850807007030168501109466110028401c1d41c0f6103103c5203250030030006e402080c01424991200c0e6a107074101e01591110369520781404146a00071f0b4102d0b41d20b040e005d01140d4440103100c1c159622a04900b456484420b20340d00c0c407070402c08050a160301038120040950b400c2c60b0458808950 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 557588956 1250 557587706 557587711
    0xe010c080d090309170604051504060f140702010f1a21010c17010902120402010f020a02150a08090307020a0303180b0d09050c03122d03010603050f07140403020405 72
    0x348140100200382140c502405010010b034001c4d121028440e00c0c0201e1342a80c80d820b5008a1042d030030070001d07c0300245011500c0031001040c00d20710075054540c0e080c00c4000745070104045040902d4410030f00c0080e030300c0d02121882102c450700200308103c00007a240003558014810b040c00e50ba883c00c0c05000c24502440402385441e41181040a8001c803c400300d400c6412401c108004180000c0c2d01c0402c011100c0e0500c2e0140c18518019800c0c464400c001010340344000c0c2c0024107205004094942c038a101300510000c9540051541155407030030801d81c2150742c06400c0407000500c0e128005640013900200f15001e40b075002c1c02c120945461510120341c1c1c41450429900b641340f00700341c001081c00705100946000c6e02e020b80002010011031a00768500401040d01c1c9001e070b0000040b500c180881c000a45510348407401c0c1d401714441841410300100010010091030919021001152050781030344014410340841404100544460304c0c15544d5640d4810215143d0f0004c00040c001810242c0000d038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 557590206 1250 557588956 557588963
    0x40f050f0901060e010c030210020d06051905060d0f0e0616020d03050c1603020f1f0c170c0a05041e0305010b060408030403081e1207120b090a0c020f19120f0e010c 72
    0x441070b40c009c89080040e81d10034403e600c2010748480f014411460301c0c01c400c20080382011000e40000e460100410380b14003a503800e2004103903440004c10b0b10345840e9045a940080000f041c0d4040b464a0304442207801c000b02401c400512032482e4401038540030381300d29402030520b21910f508200c65606503010190361040200d0441c001e070361030500c010004002c40c4d00c080010700700f01e003500c40761041c80700200c0d001c7c80107210400030044901c2510b60b081c020040e4024111042d600c1c0e0350b642840c001d80c2c0c28460341c0c0c0710349449150310403a100e070000b68204c05030130780f41b0550080c03101481c40717030402405009500404003113410411040001650030001001c0c9031105079030810241ea81280907000315003005801070315040f00300c0e04006001c0d520640c10b0f8082c0014120400801a0300da0100c1c14160b002012402500d50301d605a00c101402000508071507011407040f910f0034440c04000c801d0034a0000d4048400340c907410090740340c650040101200500302c594484108101007001112411101001036 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 557591456 1250 557590206 557590213
    0xf15060303071b1e140409020604050d0812010e010602031206040617010f060906120201080603010f1b080622092a061b020108070c060e0102040f050f0901060e010c0302 74
    0x1140000e2245420920303049080e04501c82e0145010a03120320701128001d00400001034010a101c6040b00980040e45d2900554000880480d5440271846602c516006180d1025420140000f000346a01c01003003000c1d9004840e00f07031666990706064404100380189009a00709000c1d2050030400a2441c5030700a60082c80814000d594441d1004078003050000c0c9502030b5121281d9081e10f09140c0102c00042c000c5003010411030b80380c00d00e001d2a500c82d000000781004007050110300075580075002649550b0003040c08100000304080d07455490801020213070041381c62200041e00c00d10f040442405402e070540319a4130544542200744004050b807000c11510b0020400c4020329100050a0301c08000071651a00902503090003005400f040c03084484d041000090019040141d9001e103a05401c440542070100d020f0b1820310f04070b005800007600082940d072001c980081d41c00f00208145081b2441900c02d0b4000544440500490f107409000c1e0002049111419440c954400c0c40e0f40c00100303000388103a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 557592706 1250 557591456 557591467
    0x70807050313020a03060b01030c020a12031104080d0f020d0203040501080c0a030e010504050d1812170c0a03020d03060506070c0329040b06010e030318040504061b0c0b01080f15060303 81
    0x30b60b140044d9042581c0d01d5542d08074112a650f0144030303000800382c06000a0410410560f900512131006054071000c050315200501c0c480e030140016100684a008180c038105001c0040003400a0045408040140700b910340300e10100d030000c01140d09844040e0340e400d0701c0390744005116019074405003407c0c04040e54ee24285075013080c284201402680b185000d172245d00c0803150010801c025000100c6a03210911004000010b09002403c0c81164490400c0300d017035000340c0420640317020b04c80004405001e441225000c05a000c01c0d5814800240e450400040361104140005030291500003402001c11010a001003024002c0302c003c0d194080c14503a00403a20340c900e040c2d030500b0580c1c04031122990001400b0741981c206115692041056004500306907188104c00802044900b84c0c50042d6a01c20108041c016180c006296910b003051010544146ca9500104403141c0c42d54251265441c1d038002140300c10300465400c01c1151003400429441441003880c00b50010302401c40c0350304d440304115 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 557593956 1250 557592706 557592709
    0x41e08060f01080106051e090604061a030106090603020301140f060d061d0c0f040303030b0a05061803010e1f0209061b150f13030c020a180e070e07080705031302 71
    0x19204200c0d52607160159403400350702c5800c0d64004e030803241c0304001d52550259040304102044100b0081180c200c082a25100042401805c858028807000c400d07402c50504003a940da40254100c0e21a46e50382001c081d550b0008404900081c003861002e0384091070819110716041410706050000100881d01d000d0f0050748100440e107159101020390380004103058a81e10205242c0781c1d02070040c0440703038600500c608443e411482035003c0101032507030700c02e600040b0f519240c403004013400d4040c02d02c55480090407820350410b174401865910960900c490062400d9000c20341e0f42c00c980311502c005851003154020300019402258006030055801c1c00003800d10000c9004282061040801901001800644161071400001c04803182d449444050100d420222409500d070031307405150441680c034440c40084c2c50740c082c0d0351000b01e400440ca079096481d1a25503204a00d189010b0302103c10380d60365840460b180201c1150342e0300124010740006085a0700400007141d01c4940d64408080380900c660 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 557595206 1250 557593956 557593963
    0x6091603050a1e0f060f270207051603050610151103090d030804230303010608070309020a0f0623030708040203070b040303050d1a03100b0a0305013201060203041e08 73
    0x3000040843c0e1204d105107000f004030b1094601620b8180c003505071032400d02041c40b90007005800031501c156024101c1d000c01290550503580402d504c001602c004c1c0c0d44501a200284030700317000c1503445024a0700440c400e41d119400c914125000d1a132207015215051006032600c1d040c40d42100081e000c00c2052a80e10760750076110b003099521035119401d81781400d0401090000c0c07007400404850469031038151100c04004280c904685480c5008a00e45c4d903800740031400f03001c010310000e41003c00601c0108081042e199448144c3d1022381d1349114032000e070400e11040305910700c104410000104041080c96100d01c180641c854006812205843c0d666551011141e2080c2d1090f0005200072408190020060060424400c0c01d44148031140c00c0160010b503e0300742a0460401c9582d480c01e81812545910880f40011508440200080c82500d021000b084040070111b6005188692014040300152010b0714140c0c1c10981c01103050030b04080d0003101d80d1603404a040100900d488001443c00c2042 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 557596456 1250 557595206 557595251
    0x1d19060f08160803250f060216020306062b020f090106020309090c070213090222021c1506080703150909050f011116021f050a0806091603050a 63
    0x1030007860308444088600c0c1c40001c66800c60400343d0010042a8200c1012688003800c84002e52802030303032005c0c01d28009001003014040140464004520f40243d011591268103805000b5829110785d03588010403c4524856244a80c04605400704880c861110a1406c455010710140ca20451654620000745107030009030300c04401078bc00019001d616040c9449003942008030003410301d0800c0e28550014a6880c1d29422950001d0741da8440681903640d0411008401084290710304c5181000140c2030001c0d5105070410102c8902880c000600720314640704048105408a1902400030f04244c030880c0d8000c8042c003100c04042d25046003120382c00121442c2401000d96500000300310038203180c5541481800345c0b040b5281d92500d800000c1e900300c01d2044a8600400a0710041984000d02c0010300506401e1884148640141c013000102d1740c104004180c00d14890b25252202c0da101410440d40880807500d4244111710541010201e501a80140d50400c1081002046510481e0003415291110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 557597706 1250 557596456 557596469
    0x40608160603110405012109060c110c09130314070204051611010903020303010510050d060609210309060f050c012f090a030222150f1d19060f 63
    0x310420040c0700d81501c01c241003520b240c583d442c01c00340341c0000a0f1001d10039600e5003d20840c005007111110b0703d2a030103c510242c0c04203003048810001c0b0001031040c010b1030031100407407050a5098505250400750a44110074407200140360001c04d1b03900316240d4281815280d8062403d10403400143c1c1c440c000e552007400e0b00345400e140c40828000040a800d0318420302100ca034985882c40c2c010079804812030f4152002a980a000389250000c00c803103512801c003030031001c94940840455041c2d4440c50110441300c0c640044449004e01440c980080000c44000a01054419008000c941d020302c1c001107000f111030070400d003009407142c074281c29248110785007603001c3d9604c038281d154005141184607140b4407541500b42441b042c500424114609400040e1040e40e00d409104001443d00d07950403003042400c0b07001d124001e10456100115865402031051300728031020049240800f2040b001c00f405040c400540a43c0c0710050200202d0680c09480a602601c411012840301040282140103280 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 557598956 1250 557597706 557597743
    0x30f03071e200f060309070509130206070501050601020c03191106040b0d0507021b030604080708130e040501060b0c0606010305150d08270102122a030d0c0e1509040608 74
    0x40ca007004200d140c3c140000d48207003030500c10310054220000e002c40a42e2800e6515141c0c1d0f44903080e80786030030304a411000b076200b400003c5400c00c01c08107400c02401408281c08562030604c0060804d07485a445811400c0344420a941c4040031811460058000c204068103091406440c0c0b540c52072158020200c50021700c0c1c441c4203010100b54101300400080d001c81c42c14424991300b20300020b443d43c8000d00081c040400c00305aa0303082c00a40f0707080f21a40c80c80f142c1509680d03580d800c880f010071002164103a034954038040f000504e4940f41c40c1100c6c541c613513400c080e04481e030352030300150000e00010304860a00c20000f05100c0454603005459080d0f14015800b294917102243c4c0c11002d81a058400203641c5a0101c00005069070001030074003c0042c4420801e4503138080034152001050680f40e0420071000c40401006506004401894001c01c0c3c20000d1191003029901910f20004030303203103150040782155a0f100c2e00d110b84030103401d03c081c001f80045400c55031000c4561400c0030300c0c0c032010171106 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 557600206 1250 557598956 557599013
    0x150d02060a11060604050603030a050903030c07030c0608010902030c0301180905030a0306050405100b0403021e030a11122b030902040218090108060103020607030309020d0f051b030f03071e 83
    0x184100b06070f0350b010404840500c450329203140800d03228052680e041050200108805200ba9414403d5070b258244c1c1034101c40007266a420900101c2c9041d10540c0c0220300114000f14056100d802244e11510498803898038603460041545502c8240594041d0601c0c0e0b030704800000030301e0038030003888000c034940d9000c910207041400300001c0f9800544a071000c1c0b801c000080003a00200420703181201c1c0c04031417030501c1041800115100c881c0385504c1d07583c1070144d03241d86410000d03000090fa00c080003d40d60400c1c60341040c036a0715921405001c01010100401f01014481981c18004401a031401c0c90045680402640482d003682c00c0b0b000d000900030034594540c6118184000c0381f070300400300c1c02d00824003540f5640104180307100c0d00801504041e1118841d1040d5100e41100501c02944890700c0b101c0a0002e0501640b00c0031f0740034100200c04515002c9030501d1500260381e2014a2200004c3d44ca00b0505580d144160310203404098403a50a11001e8030200c1c255001c0f109980c06460450501017 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 557601456 1250 557600206 557600237
    0x180d03020c010c17160909020c010c03180507171e07090c021903050304020f1807030c0207030b01090f1d070e07091805180a03020c030118020603150d02060a 69
    0x101c50240d000c0c02000120b0758130030020f4035000300301c94000da400c0104100d01d0750115012540100960080d000d00341c0001b8000c0c21082c0c0551120460401c43c1d5410080e200d0340600030b6080707080b000300c080c4c01030303020f8001407015600480703552180e00610760446031200404031641c500b131800c083c42c040b0243c02031101088a54024040d008502903d44054003003038608900d5100103040d072101c040c0400c107000c000281191102c2c4003a00782600000c02d0305034405012140e442410700c04a61050019060900628400c0c0c00020a10184c0b640300300c40750402e03801c10740c03020f00400c46c5810740034200b038941420030064a240500c0c0031034000b48401a0104604040080c10f031002c0c040c0aa90400114034420004903103060711074010401040c101281075103070b06000303081011a041001c602c1e030082203d0740c01016000900c0d0901480c0645c000c1c00200555410390450303402c822000382d08214108001881016080100180c09400400812441c24103401007031454100b502040046041e1500d000c909 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 557602706 1250 557601456 557601461
    0x40905010b0f01020d0215090705042903030f18061e130617041103011b092105060403050d2003150a080c0409080d0905010501050a0902070515180d03020c01 69
    0x2002001e00085c041c05004880003991007503100200c0e0105050729010515111081c0f0040004284c010014015030104032044051720401040ca0100351030b0f240e401001c0e5080c0842600d002c0c04034a410300781051800560064810311456003107501003000c10480c40c0d940541098030010a00e40c0c10324940b00c00034425107c00101e001d030005018054410045050200700c2a41264030542c050101054401020007181c003410301da80711700341c46125058400383b00aa0010a601c2101c00925180005031132515459181e0160040e014005402260004004c01e004100406420820840000d2903203240022166a00140074000d55015000404c3c4440b10265000010345000c003210700c4100e051030080410740e1a0b420590300d40c092074842a545080c80909025202c0301c205400051220041c180f428500070301d02400740b2032084c800c0d00c00208a01c0c0940c03085c2c52100d54481c1c02040c120068282e00c0c41c488100602041a10702900300710080751b2018410848000c100d5180541c5412011046909 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 557603956 1250 557602706 557602729
    0x90901060602120301120f1b06051c0e06070c0807080301060c0c050103050613050702100f020408011404030e1504090903020115050102191103031306110c041e1a040905010b 76
    0x3c0300c201c03d000600480a030100050486a030110343c134180058a403a103440f203040000004018481c4003500000d90b207400c0b030000c0c40034480040c4001407401424455a00b00d030145d2902c01519445a0000b8014038015454420102c1c001d6403ea030601403250740e600e00903442600300c600010840c40281c010001f5a20aa101804c000d0030140700d1480c103540440c4400304803003400c011a54071030020900c210b00030311050030b814041040c180030468142030085d000c2c4d8094813482d0b030a5032a0040f800b0b02d00f0b1000c500ca60065a0540e108841c071a402c0082200d005810050744c80c001d0743c01c002c0020551014440c01c12518441d40000c140c01c2c601c1382d6171890ca1202030740000d040d50407002c011029220700d059000035003036108540482d11900000868650b0203004891102c044041c4404104a500484091060031448046400510011041c4001d45120091038409030f122504003a91030056500b051295840c5480c4440b2905098000102a1814010260382c0d99654804041c040c0c1020b031403003803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 557605206 1250 557603956 557603983
    0xa0209041401032a0f060206180d090b070c050607030806040e0c13020c01180b04051902010e011b06061206050c070b01120c0803030708160c030504061409090901060602 74
    0x109614584400081c1e40d030580920142084c001002c10319910a1242c207000380500882001c10603444140107942c0380c00a5a0015500030b036414805283c64000404018070b20301038bea0500d42c01d262001c0580d1741d40160b102200e1080c0a500045a00d4940d1310242807214000d6440a4860901d0010700086410806d040003498214a0b4038040b03c1e00e44503145801b0f559101001030b42c80c680d00c46968010005407410007440e400e4040c1880038044080210b07806140140c1c25105003980d07903005a002c0394100c0d84000c0c0440c0c040c16401010f5030060840a90100626100001003841c6030b45040c00c5920300e80000080301c45984600003408201e21505501c2000c094500e49801010349400c02e45807014481c2d04064414803100004100740c0c07002d414000c2211400b01c0c1c0c5c50b41040c5201800c00d020440b0204803d90300609a00c043c28411410720342650b40548841e0b2078a0b003040c2003201c010381410305a4500b000d04014021217903c0f00c0c0280da2040300e8903c00001c4943c182840207040c8291b020100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 557606456 1250 557605206 557605241
    0x10f1d0d080c0903070305011a031c0e12190c061704080301140303042102040e0d08040b13080c03030106300b1305040b16090609090207050a0b0a020904 67
    0x850481e04910714030b801001e20a40162202e4075000000d10f0807106800060842d404c05450051040040752102c070303070103800c6041c1d0703075220042c81088201040e8104044002403021280e0072039030130220fa10a03a085146000d0b02d4003010342c0003480114a180400c2210f0074080840c04000c00c0e5401030200d5525001a20318240508064070340c020680010700820f1412100e415840104da82d04004640082112078400c03910000708402e82e0300604550b505c240d01490400400480000001c00ea03070420400c9526220100e441e40d850340c01d102070b00200044001c203402007281010542c2e41c0007801c1000c5840005541d40d606002004220750100c0055100f0045140d080c000a5140c140c0c1d8601361805244d40064007241c04030000303c002c1a140c0d00c100d100c0b8a05010b1200703204000740c50300e00c1040c282184011070000d4040071180100c1502ca10780010380e0240341809030070429001040418002c404030b50742c0e003a03140c46001040d233069501800480e0300040501c140e0078680a0f9865000144001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 557607706 1250 557606456 557606473
    0x12020a0503041506050d060e070905090a0605060f121c210b0105121311060c070623040b0414040209060405130e0f010605030c060705120307020f010f1d 67
    0x2400600014100502a00c4510f40440c02c40020340d010314014003004000d442420841d0038150010034090110b4140c900600d00041428a1207010b01401010940024800c039000c41d00d6400050002808156020141e840c500b0303c140d94000350316400c00c08a02c0940108020150b12003004500148ae0405114108052020544c0c0c6c400303080740710490740c0402142c1c8403401710040b110341c412405519881051001440407201522000c00a114803407280000741c03183c10000c22003140903140c00140d06611460040c00010310030550554a10603000c0f402050440002c0640f00503003064202c103442c0c04010030100030368510710030b08502d0803406650441c58641181d0119819200d98060300d4014102d112031000c0d8041c6035032000c0c56004100040d60505065148610302800d13543c42258071a01c240d0082601900c0c1039070440d00c099074024010900d2880000500c055600000c04100c00d40c09007101810014400b0701543e8581c1c02d0400d000181015800020301000c1001000302c205176000b40784 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 557608956 1250 557607706 557607727
    0xf0608073209010e1e0103080432060705070308120f010b041a1b010c0509010f090b030a1112151201020a02060601080901020c1603030905060307091208120f0103031202 74
    0x169181594000074502245036150552415035614090a40f1151805070300001305101202300900181c0300c040e99007200714400c186050320030707800214900202855046c0035205c949002c4000701002c51045c0d0540c3c13000c0e44d07242c41d0203040ea041800b10101040c240380800282c0d07064170720024058049a116941002d04202c88580c1200001d9074110111100190801981416841c060400281c1038024010728450410007070480c4c03c45a44070f0702194062200c1001d070343c040c1300030609561441030140d0941d41c94621002c0503083c49290701036100f10400c120203203001100c949a00c03c090490125021190300303001e10100800b05403000703115920600204101070f5010070141d4100000340790240d81034684a5202c1d00900c01c21009031903510030440714600149001d9900c608503070081d15180f0302659101c052000a110894000300042c020034000d01080c200b03540c01107103d5004a5450b410f203035410310381c1108a441554404c0c40d110440c80108209644500214a00c03c1030b24403d608007a60300c0d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 557610206 1250 557608956 557608969
    0x91a01020d0e09060d050d0f09091e020d020f19080609070c060c0e18011e06080a020708040918120906300203010b04080705091303030f06080732 64
    0x110114807030821030b004240a590b80c0d001070361001b07400a068074148003c400300a09030011015694010685020340042e0074100c40c0304500031081c40d8400740104034109544030000b540a400c0f2500707080c0d4280540841110560081c01031b42c1f4081c1d0340100d05000b240c0c8050211000100001c1c8145904420440107550011644055a900c40404039900001c0081911010392100105030000f09105000d06400f2040441d54121703030801e2443d2540c6440b0008003640d444003030080e14003045105000c140a0a01907005203074030f900a40003142455211000c48096a845043d81d9480c3c12030480040240030340c1c0081941c40c848941070404c40c091030040e025008104004500401000805201102d900700c7c1d540362501100c0f0110840d9290f07102c1010041540007402815028031916101088609120f05071b00d00525050801c1c40c42002c1a9908402030f181c51214217440303946500e000510040c0410051010b000c03030510120304503100034161031207640c100a44c00d0800b0120503054038180c441c4c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 557611456 1250 557610206 557610227
    0x40516030812150a05040b0d05060901290603071d1e040c082202030a0f06140703020c030415020309030d0e120a0b01030b1312080f010b03090705010f18091a01020d 72
    0x46d60702042c2c00100e60006030003114440c802610300c0c0203003001c00182c0c50f0107600000d9070056440c46208528a6910520340e9492400d581c7c5801c14030800108587e5070251003110f250314140f81c2e03032030324040114010851400c1d4040b604082c418a800540350285031601818800103964035020081e444d14803103203942100c40c0c88140c003406580d14014400d64030300b409068860307a0090842000080302d40f41c0840109041c02c401a1004040e2000c40c022038800d00072a21591500c2c002582041c1c10070520010b401031030381070b1400b94032041020791069102440328015002960f1078107480b0701b110343c2c20f1091303008042c200202e590300403804038000980320180c4d50341036076005041c110855a41c000040c402e0a11400090007036100310310400c25141d030100703c1d180300c0c0c004c0541c4030300745990b609620070140c0800c4d60442041d4004840901103548103011007514003055203411070801c0000d2030701c502000c400307411501696444000100302001a440f01e012002028801005005500c4600a200c05203c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 557612706 1250 557611456 557611459
    0x3090c0e060f04200705060a0605061908190f05091006061409010e060d021903020a02061504020f0d0e0c010509010906110c09011401200a0308040516030812150a05 72
    0x191165541242100034828403d054006134a59840751141411691050221500742d289401c002003c03480d414641d0945402446407030808101d54010102a6280440180b1f4098400e10505182c44480680d0054540e5103000342c5d000030381ca0402c48035407400d150b448d05076aa00c150401500300080d541c00800c804c5416480c404035915070200d280100c9412103101c0001da440f100214032454a400107034020080c1d41d42c1c0302004464094190b0f001e50170f90060710016000b58208000180c50b04044c10310341c00070a813006000601e448a4421402e00540001d1018501240d0300c03010511303010001c00080100d000700b420f00c213003862a80000200b291101e40200410030a1b0940c0c0451144000c1001c00417140700103001a11568480403160000c404110b04640051007140061038030042110051802c1070043c006003443e185140c9044d142114050022969880740d180c421284680c14814200654455040140e0780e003083d0401e141a21809044128818255800420741c0d5845010420032640e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 557613956 1250 557612706 557612711
    0x606031603050a021b0f070e0421021c0207050a05062d1e180411031503150f0403080901151202042d0606020c0d1e0f0303090c0e060f04 60
    0x710f01011901030f001d9000c08004600d0102c40341914884007094900c0d80d0b140c854115800f036540d8881d078000201c4140c5e006404000f603030b032420740700008041000c264145240111210720a00e804d400c00c40c2c012178030760000180c014a200344107520340b0076008401000e0840e4998108140100e40f00700103002484400e0981602c820800e0341c001244060310b0901c0c1d041182c24000c16146416003059510030112400f2850310103244003114a8184100d031610440744002d582503945141520580c5070840e1502507042c850b403000c3c0d20504072911401c521a542e07030500007030a41031a00d80079205010180c00d030202a4105540c400b155680c0022030300449190081d4030b1120030690020400a016419440d00009041d003504181c50764a140400340021440f00100300c6640e54000490b100c11440400d00d5010300340400c81d40100720700b180e5214041d0034000301001a008181d86000c1d40a80a003000c0380400c3c3c8400d40c030014402c0100d681001840401c08040440c038100002a9010011307041142c486d56 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 557615206 1250 557613956 557613961
    0xf03031b0a0804030503031909030c0312060e090109050609030304050d0e04020d18171201140609030709092607030815060406020a020a060f090905041a0703090605060603160305 78
    0x9a0800041c1c810030780089030540e8403074481c200903840f6031007200c0814000140c9080c000f070182983c42220545a019a900544a00680d40c100c81030806002c0000768140c45000105028580c6014640101c80303100c00040c0440c3c051900c0d41c1004001421a0b069030000d00c10400820404a172031098035001d440d20104840344800003070001e014482d00344d03d006251140241c21001a044071648086c05240320851040141884000c24811980c1c6e184001cbd250200401844400742511000144020026400c0c1000440400c1c41c004e000d6010740c0e40c45480e50080700c03d018011721140d80e4141c040350141a2060074078a031404034481d00390010100900c04000600d8050400052208110001c01880d59079070f40d820003d40da18036a14059106924242000605600650030130710034030160345828452915003501c1100400c0002c0064440b650a60703103048901044e1021180b1032070395601c00040710401824140100c8070000c000d50700402d0104288041e01b0790000c008209c2144600c4d0200e2641d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 557616456 1250 557615206 557615257
    0xc040308040905130b090d02060603011a090c09030a030513150c020127080d030e03041413090b0703050f07090b160f0506420d061d03090a050f0303 65
    0x1821a4000c2c254500755418014541c43c00b058507c05022581e003280c032280c95450405003210800034145506e10a085c80f80f01355030401e807030402d600040000b43c49080c903140b080407a0a080710304108400044000808161240110f854080a400500142c500b2448440710240030420b5805010b0305100891001c42d100e141b45541030000c03400c030514a0350072940d684106941c0d9100c01c1c02c41c00082800d1202529043c00000305880403183c240c4c40d00780000c0305440c20b100c0401c0180c400325403010f464242032804500d02903006801103210b41e4000640d4600400203124140b00503002108001440c0d02c02c21064100304252548640b0881c084441035441e4600151812a1000028800d01800080086100700c0301071054a80034106240410132078180344281841c1600900500d00e00e454100310034007411b1407203144003070f41c0c480e001c00aa80782145400c441458520002d0444903840000e48000c02c1c1031110302c0200801091703500f0740880c10740400007030b10703405101c9003a00c1080d00b8041c0b06422 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 557617706 1250 557616456 557616481
    0x12110415091a250609020411031501030510120c1d012115020f1608090301060e010f0618170c01230301211401050a0c0e01080a111b030904050c040308040905 69
    0x24250b00070020000102100c007010003e4008503103100b0900c038411892b00d41940240038a03489403851030860101a03042c280440c031008645c0105680386032105001242845040784030b03000010f400e400000c050b40c9444110740310507050015a880c550800c0402c040020030182e42d1446040c00840d002da255001d2454210340b902554140b40d02144000b01aa406c0c401001c3c0200a2044150004e10415441d0780700f0310803081c0c080c801c03824035440521041080c58401e002180d024215180c0c2c41e0500c03540ca01c0815480304002d84803000a401c13080b41c1202540c0c000c4029207021040401000f0400410341390860507010500c5200f078802d5814070080c1044010700400008a9403054000403401042220ba5009201c2101e000c080c03c1d02c0d02c01d40700d0b1240d02940d00f21040c1c08050399114240e81d6040303920005890102101c0400c2e420a100a003030282a13001d441010a10103002952140c4042081000351031014010104040d0300700b00c00c0c008154440110307000d544502002146984400118104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 557618956 1250 557617706 557617721
    0x1603030b0627030604050a03080604020706090b0a0e070f06030e0102040e1009050606070f0f0c08100c14090d021212160201030f0c12110415091a2506 66
    0x6002100040160201e00d10668007020b0241e07400d0540c2e0303070081d0003052554030034040d1409001e0354024070312840024071035a440e1340e014102420160800c1121b40c0d07024150f4107160421207010703000c8000c02414203100e04c20440f032044600c008008603842d2404140401d903241c0117400401d5110299241703002000d4045030020700c0c007000d8010f0b41c3e140040098040381c6150284032245411300b008a50b89242c41c078107407407910381c1200c01c1c4d04010265503260701d606030b03002008568102140cbd400248801c41480700380c840e20b4548101140c03013031940c80020103030301085801c420300c50b4091201113441c1e12040c0c03810501e168140c600c10980c20030100316500d0814044601c0e10010b00009131910b0700b654034000d00d410b5034401c0c0c070700b40b103d4407404c200c010945d909400400000350f0b00605100e103640c880e4014800e0024001c844a203003e0326103100d010740c1c003010b504280214032a82000c00c2401866921340421020740300c05981090460001d4009842c41c1c5060000b0700114a100081071111a82c4400e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 557620206 1250 557618956 557618959
    0x70914030a1403090a0609060f05030a14010312180b041502030c012f0a2c190f06050c0706050a030b1008040201081b030c0a03090b24060403081603030b 67
    0x10b482c00704200c00540e81d52001c1a400e00130b8501030800a00280114054030603034503a622500c643c1ca0b00d280d000c69007078000408803180740386c891310780c07026440780400858040c6010b036025034040c3c0b80b02e24002c0e00000c044964004e250700c2c0c0620030003070314600b107090780c00b51a151908421111442e010480c0307140600f50f0800303265460416424241440c0305400710101c02081d107004021501900d20340c0e00d5006406014002c5601030030300c40e0600c0d4100401d0038496800c001c00c10215000040450001c0030b4000319031a0f080d003414814415200325480f440001c041c140740c813030718001c080c6103d00d032070700302c00d12030743d010f216000c501400b0b900e000341c1108008540c09003400842d0414031100420000701607130140c0c08243c85802250f15181c4040f0420f6103490510303041413468407007401d90200d59202c40000010103507a01d0844002440c0000c942d406a04d161010108818841e4100c05600c07a0f0550102d200e041c04020070030001d01428140c407243c500440d00e240504140c1d04050f00500ba8000209 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 557621456 1250 557620206 557620223
    0x201170709050a0e070804030e060f071b08010603030507060905150c1e0c0706081314060a380a05031c030e0a0c150c02030a0303090203060a05070914030a 68
    0x810580e006540c1c10440c1e2088880d0682140d80d0b10203442454405e030f84100002c0d40200c002000b00c1c0c010001d03410804006040545847c02d444002d1a103604618400c030380c10b006020311038860b01300e04420200540f4001000b004540d140d90b40c083e00522542d800148030307a841e0503990007801000d200c0004540c4140710705010300d2070400c040d00c13a00e902498900c0d02040968102c161000d2681054600d8014100d00a280300383c1484816500010000c00c060080c1840003001030006511802e90001c6005403801000e803400e0045d1400295101c1c000050000c8a0306007035900851481d200b41c40d049031407040e61113019526140401c03502d44032900103d4040c030540c0480c01e00031031003030340b04072102d44113a600700581569a60b030140c03a86803d0a014045003101c00d401d0041d000b40070038104160324039007040b0051806582c0400c2c01c2200b03081046e40400e48c3d81c00308006504060040950000540004001c141740c1a9000f03800040ca601507100504020011008652400c2000781c48480c0c0000c0b88 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 557622706 1250 557621456 557621461
    0x30103030c0312050402030601060c060f0c020a141504150b0d08090a0b091e12151506070f1101050f1303020a05090f0604180f050c0109082107020117 66
    0x3600d0029180c008400007120078003c1d0003500305601c1400d000b164000c0203040c050f4684841102c03020001c2c202a51b00726543c80c500519154503110b074440311103050b0090551401c3c0ca003012350001e80d101c250400380390800c443e101031404032015441d500c0750b0702375542d400f00c00304194984011b00008008a03045140b00c0703000306c14000d0300710203029401c3c421960314240070744891031083c05018560300d464001c000d80d801400c2c0c588030503541034020f400162034030001c100f00d5001146050000f0341c0c00c01c03054440e03400b808040d40002c0051802c0c00e0050380e640780303002125612003c1141e8100320203892404444001034540e03100e40308461500d02450341190302ca0401c5001c0050f451510b10049119064035000004c150500340c01c400d2040c000c910080c007199a405041c0700280620044a44074410200d000c0740016034007400c1d0141090040004210024071400050001e040c1a000100309920441c8604024010700e0b4040300ea0484182c4030a840b00b80500c0141c0e1340034100201e2081d200d840d40304 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 557623956 1250 557622706 557622713
    0x21305030d031b0c05150a110d09060c090303020d080903160506010f0603050c04030f051005010b0c1b062d280309120509031002040803181e19080102030103 69
    0x43c0080030884100101d101e040100282d41100300c041004015030002e201c40708584c4032041006912500c08400881d9103101460140e4403070340266064514541d44d1040f100034404a482400c001c902141465a54107065482c082d545145021082d000c00a0100c00078001d0003040c0305075110952000d05e50501c800581c60031a85030b00d801d0140c40746012a0070400555284207001d407500800154202c03901c0d29003103885050310410b483c1015190340c0300d9101603890042c4148030707460080401c844220303152400d0304405c6050602ca4481e541150310010350070f41d299a5a02d0440750300300350303010341c064a565902c480c5205080c0840c07426a600200460911202c140c40340b0401c0c402640b1980039240e102c58128180c04035040402c0207004000c1c5501d030480458051402051030721002001c403400100344400600981e480303500a2000c9420100e8841c45484035007415408001c0c044820311640c0e5152000e0307081c0d41c40da141010f441400c0700d1910110925409580902030407040d8000d559075a101d0a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 557625206 1250 557623956 557623961
    0x3010b181c030e0604210602040b0a03061d0403021c1112191b0212030c0715020c010207030b060d02060c0109110a050409110909071d01150801060f03021305030d03 72
    0x4070140c020072000300b86000d084c6070000840e416100d29040b09007507003090102036200003500c0c98080b1402c070303802c00010401c00c288602400080101b0f40c0c000ca5400d050007024a0800e048824034580c6001c1030042c0b00009402088441741c04d4000c000300c81910513010400c940a1a01c1c0918074018091a0100d690001c990801429109410003000341d6011290500b15440062200d07007190900242c41c200c001440c0002e20010315032006402c43e402c00700303c003a241c0c2c1481103550250300c511800011011101d030301488019088002400a01030a80c0b55440304484420700500303042c801c03520300490a04654611007503e13207900c0d07120003c01285c202441c220494030344c0c2c080c13840c0c40f804443e03200007103501e0140142d4021550240c0344100080003141440032a41c4007410700c055501449902041400090004400006100403613401952510300d0a0b0f51940c09000440c0c10002e03900018010a60400c0c01c0d0326550390070b0300c1c00581e5103c00000c03840d4108000c1e000103030705001d00b10300c10b074080e036064 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 557626456 1250 557625206 557625259
    0x120e011812171309090201030f05090a03121109100c0b04050d09050a030510050604230109050906060108130507090e0d0909051006030b0f1807030e1203010b18 70
    0x4090345605803401400400d00ca001d203564a07610184082e2003070004d1803298000c00141c80c410b040100e0305114524407401512400ca80f060b5443e0302c03810b49107042c5a0311800c1e03403509444189080001d00a951200d410b90311407948040d0045810460450300306e0f204610605c095a08802801c00c60304091401985400800740c41c0e4000a54000b0b002c5410311340451a6002c5030713031100013013081d0310a2885071702c080c19004020942c402d07502c0341000c0859082910400005e82543c003065169814200241c0460b60b020303140001c2c03a80010100302903a40c000c00440d0304a52500680804407450f80b615914114940d042610801e0a10200d0621494000740071500c03c01251501402a0307110038040c81150743c2150070040e40c0a0f041f03401c0003158001e40c0500d2490002814549500d0840300c04104142400c84091a0b8081c1501c20044081d0340b61103900e91840c50340014250f0084120f11249041c0018080d24409001c0050320716040c0003d080c0203901140b0141c02c40c444803103064800003000030301303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 557627706 1250 557626456 557626463
    0x121401090b040c0b0f0301091d0d0302040801050a0e031b1006060309020102060a0c020d03020901020709181a0403020c1c05010e030c150912130305012f07120e011812 73
    0x4000801c0d55013203203058910010307482c082203055070b03c2e2a0058010307003030f0b100e0301101071301c2c100c4500d2642400900c6040c440b01250b8501582d15858071030708a0840e180107184200b840d1030700742032881948000c030403175003000301d465644010300180c1041e6030708040f00b00f542219446d01c1d003c40001c0d6190940c1142c007442d4000d80944101d40d540b41c41c06801d80303000e51881001a00040641006540280d003c2d00c08000c041c81100c140945962010007110407103800c9020030495200d9480030403406643d0070503c0ba0195103004000e040c1a5006551074202c020114410414802d00584503002c3c5c0d410600140c5c1c0041c02400f4587d505c003017040d2280c0c441c2c46034944034054803801d080070102c160322450140e0b50000042c0000701010302019159003180c040115200d0100e48008081842402510140c02425441c1c0d00c441c4c0140d403015146901d0000008054401408410f0104444501841c1076800e541001c150209007403004850f0583d48c403410b51414a40c0d10000300d0096214400714201511 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 557628956 1250 557627706 557627723
    0x604060b0603040515070905090408040905070906020a110d0203100606110a021e010203041802181507060b0f0d060e06010e0103020901171e0a0201020601090c09121401090b04 77
    0x540105110701403000710750242041c0c1c08003000c40b4203c41c1181c0c034030340c0c000300e10310301b00c42040d4071100014200001600d09a0700180c0c0450240030f41c502c1442001c0e00000d8500700060100d00d041806911805480b202900104150f011282c1c0b41d113130400d01d000700310303401000d540320143c0c52408040240000d014880028000c0d10001d00708120000b440c81849800400c02c041c1681c04600240d840782c50b5085130307030450005000000b20f000d4418441844400a4440940c5440c481c440040c1e00ba94400e6105200d001103a100041002050040328012900908045620070310303400402c54105685243c2c0d6044007012091900f4402c03141d100026a042800a036206a40e07a00d014091100b8207000183d031001c00c4000400c031540310404440e40c80703010001a1090343c0161805000d44001c0e0401a850f1a04003910110456a0611205024044080f82003000400d0740b00014100d4280d40601c03c0c0d1a1100b0f5200c00030b01c004400b9411420044000a02c03040285103081300c0c1c0f404098a08541034172 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 557630206 1250 557628956 557628971
    0x403061d12130e1302040c1115013b130218010302090606030406060f24091505090406080709021c0b060f0702010e090106030203150d110111030f0705060406 69
    0x450504032000694900510752501e400c10102291541020f00344c04c500d085503110050050f00c03a40154106482152244040c107400d000c42942480000052014a401000014010701080070308200c2000701e614140020880a2a075204048100e050240040b01180702007110032555248a640c001c3e1095441d43c0b000d19041c904400d01003000c2c000298048010b100045460500102545c4d010740a02c0c2e010880079a07440c06e039038201d401f54000c00c48a41c420080789003050258441d28034a00c140380303003100d0b00c40d03e000504607410969401100c104100022a2400b540c1c0c0c40e0482400351840703030291404a980c41002100a501492103a030f5200c894201100004042c0c1c0710301042204041c011502d45000c0218901807a031064004906102086484160b90f8840103420741c00303803100d40c50045c4c1d20704203800c10404200400c01c2c228801c480541e03900e000901e000090032442c220a080c403001400081c00381c1070440c09000400315644a02142100500c1000250f442c003507400b8400420521 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 557631456 1250 557630206 557630233
    0xf0f18091e060b0712050d020f030a05070815010f0903140a020f010813080310030609140601050316030813120614160503240301020a09030b0f0603100b060403061d 72
    0xa405a114516210b0b00c2444800e0101d0b4280002c5c000503001850328601d000d40c0028a50105d0b0071264081c45210310210030015014007501c10242c0000450030700f030b0703038070b20b4004084100d42e10000001410000d440002891060140000801a40c1c2c46103081000c2c401c0c5004c49995100003482c00e038403526034225a0a403a5001d00034490042d0300d151304800003492203442e02d0155038005003243e01c090034220f4001011500702d21030040550320a0501c9600700350001a42450040c0c107030822803007500142040c012a001d03c0c19120201d030ba001c280309407108069501e8106494640d8040448101140b084800300a00e903030082944581c150204011a10380501d540d19604404501001003101000413481d05480b9030b18041c003076083e41d50140300d012150004203003640c0000c03014101282220406000304042261101d078000411105503046291400c0040d07903861043c03072903094190781c400e10401c50b07445803c02c0302d0195403c080305100c0382c010041052003203170401800907880e011345082e94045 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 557632706 1250 557631456 557631461
    0x204080f0616020304150c060e0102070b01050402040b04052803050a29040602090d020303130f120302030313050a080a090612090c15051b1e030a0f0f18091e 69
    0x100b028550045040c6403c009050011022004505c03051140000f030400000e03020740101c0a0440c05000003507140e003054035029030300d00c006030001c85c41940180802d00c41c0014481c182c1d002c94000304c2c0c850036045941c25512410400301c1d480780385030203c5044084284100024400e501030302c0741d4444403580c0e0f4400e06110381491104a0460304007003110104012803100e030040c116204005048000c900aa039000900c1c65200c1e1090b00f00d0000001010000349501c064210010b000030450969244003d56000b91240700003402c108102d407144060350706001003040101d41071948200209c4d41c0e007100c002c02408410b01441241c0000d4400d036540d60311400240601c2e41e0140e030114095100e01c1c2000591001400c6c0d9a00c0d4208004d41400421054020b403614941c589800b1406041200c05000c51013005034a8100c0106117035108211024a540d44018289640ea4061403c08042e0582c0303a030440ba070300705408041c174a011400c040403900170320710342c0200c0309907041041d231000f0003081c00c0001c0c05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 557633956 1250 557632706 557632741
    0xd0e1c2108010e07050c15010821130b03180703030e0f01030b0102101109040f060306060501020303010b0f03180115080f150a0b0f03030c0a11010c080306040903050c010204080f06 79
    0xa41c3c840b60760210340c50728040c3c0c018011889600c4280c846058040428401c801ca007603105590943c0011048240c2c00d108a182d01541e80c510510390307161190803c02c0106002c264402d403e030b04031002001950f190317004007501d0394a43c41c24040d129103a66a0030000c082d005081600c51141c04840808455036001c2c0c86049c200b1501a0064103029034110340d030000800101da00c0c030010182c01c2000c04032170b40e1984a10b8020b1440e1a400103071150071410050f080b42c4041d0030050541d8400c00060204061030420358015114031100d2503501d54034280d402d08002e8254840707405560801c00510101d104601104054980ea4422188040020b80e0615914040b1140d50700e03220fa0350030003240c211415034001034240d002c054160b41213041c0e08004249907074030007020141d46802600a4001b0003080200b043d507184424039000d581003009407241520380c400a8201c40c42140da9519000030140500d0540c0c5065486a00071906c17550b403060401e44801d82501682d00f2030042500040784183c4a04030a0b1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 557635206 1250 557633956 557633969
    0x31201092306010c061b05030108120a0804121412060f01050f0d02090d0506040b04030f02030906041403070504110723060708180604030924020d0e1c210801 69
    0x946840b02c0e001501c480518840035904a61190030380341c6072048080030b050408106569103660f135850089280d0070910b021500100b500c41c03c000c4201c040e03522007140c9070400d801000d1004c1401a0b10025030f05c1320350340c001025140f01c1c0411000c01640c0c807518114481c2c074040e2000c40198030900b0044a0611811822041c240401d100d8103030000d50302e81c0900030985000c1e0070401e04000c507880d280c1c035107142218212400c1d00e9230400c01003096400003a09009000030300042d8140214030000505c1c5021b10f004002c84110025880403465a00f0400d95000f000060b0013044058583c0354102c4090b8402c0109640c1d84040c2c0c1f48014490740b4200400c507005800b0000341c9055162120115001c000c0944908003218050f00c5814a81c0c1c030600007a070080c0d00c02d45840c0d852600d08480f603000803030a51328013a007800e40a40543d2901c2d07008500541c148a0b0b52400c503044e030a049000400080007100c0504041d801059000c0c07c2100188a060f1811424010000c4035042240c003124014400d02070312 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 557636456 1250 557635206 557635271
    0x90c0c1c3207060603060501151106010f060305072001020a0e06071502070c030b070306091a0a03140a0f1124040b03181504030f020307052a0303120109 67
    0x40581c00d0105000d06041d5218490115109540c2e44501c8242c0c0d00c282c000310515140c03040c0c215402504000740700d052104000c0074004a600d03000015030032152503c41c0d21305240d1500e0024201e40d105400183c20701c0562172812036000114003109000b90012007085c400314405848035807492030300e5001d64032150b62040c1c5000202443c55603036000383d00400001c40d068030032580040b001401105000344074441c0c40d079000036070500d0031141c42c058810181e1385c07001512120b100100641c0f90440035400b41e94100390b0036039203070350b400f04d60b1840c0c0724031110060701002000500d20100700280203c2c2030f408000b00c89158510100c500d035100a82e1034900c0c000d01420f4204402c0001640400145900490403404104444803510120382001c1400100c0c0d04641000c1080000f055005030400039a43d44602c000c2d0b0038400c0c20703079510740e8410041c0c11105215448802c4200e140ea61107c284040c85e00c0541966110750691300e0000100000f80124920030b8101018401600c0500c0003160f00011490141e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 557637706 1250 557636456 557636537
    0x21605060301091a030703150f020a02191b090501090c0905031507140d0c09090506010509041109040e0d1202090f010c0c0e0c09030f06060f090c0c1c 66
    0x20010154200c482584c42d216480c4c14626940c103020b4240154018100c4924070205a25044112664880303801040d41c8148407513a06142d00080546e6001409440c0d07001c0c1500300d081189041c000903a41341c0c0c08028034132000c164608a60000c504841c2c10385020b000e002d11482090b40d004565008054055000b0300d403038815118551001074114441d410082e449000100d4039984540c404d011991529841c0c0c003801810541c4503840301c3c01849001ca08015504001d000241a4460f1891680c4903c3c0c0302e62602c9000d10f0303801c00b00c03002d4100007007080040742c40d6102010748a04800d407150012403ca011020303803401760707130086031b004010040a08083c58481401502d40c3c4140307501c19201640c4041000c590b038040031036420701400440d0015a00d40700c1482c1054505800d51030049115080320052281c2921400310641c0c9041d07044841c501c0030303562824040041d0150181c61846442180280d00b001d0a080040380380d03041481e0f40d001000c485416132070080d030050030a0440c4240343c00e0b46 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 557638956 1250 557637706 557637719
    0xc060f051f24120f06090902330f0906340b040803190903110c0d1208070513091d160b0c070b03101e06020706080a06031b0501021605060301 62
    0x50044201020f19000602803800402c41d0300300c5403150810810660341d03240036419440c0214190300c1c03a1070041c442810031510003005554121041814041c00302000c14080c3c150b2250b00184c1c1c2031100d02801c1c450b00c0320040c40c0e088410b1082404210301c440b084d0003000ca001055010640007281d0051501d407023644603030380c80248660000348035002191040000900741c0788103000d029400c0b4001da8440c2034038040d0751503107410040308941c0d45103e138020401d5900050420a0110749282c01e500f004041552030500580340d5116010390b8000c540715203032021800c0801c0390711544030421502008440e000f40d1901480c1d454480030b200c09440b19480e6010000b441441c0010000440c0300401c4e50083c5541b01071000c810b0300144d58982101a5141c1c062200c2c0998400c0750312040c0d00620041d40c3e0f40e24004d4060344a0030300c0d0055000b00448400040c00c0c0c000a41c1103040196800020248101e11440b5860240620340c0691030050003040841ca40c1080f004e5400e80589100a00c9185903034030b00170 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 557640206 1250 557638956 557638967
    0x1207080f060d06060e04050a1101020102070c180603080d02070c0e040f0b06060c010e0303010e0709030b07050d0b0d080901020114060a060c050a081c060503120a0c060f051f24 77
    0x200c22120a604c4d11000f194002060301c02c140100e100d0001003819583e43e03d08004040985140340d411684103020a1000c07551541c08842250703403c120044403039100c201e52002500a94002502da1100013440742542c009aa00410032940685c0402c180d0030380700c5210102c0c4020644e0040c001d143c10020780d902140c08004c100d50800f800900c03c9142004180095094503442618000369420100040082e411019121035200c015454403030700c0d403415a034840f400c903070303015050008012011581901c61031656001c410358800045c803039800c2607074502d81120158400c50b040b500550034221121450017a04943c42d018203c001d1100c2c040e14203091046400210302a81034840f48203014080300404c43e400e0003409003200d28081512618041d0750031209503110303988024040c0c2d10040c40e200110a00c0000c0e50440c06180c5410364008445040000140a1604402c1e0509141500388251040290760020b94489500102800150795201c015000b44852007455101030890700030199640c400d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 557641456 1250 557640206 557640229
    0x2130203060a0e130506090f07030320030d020c010b040501030b190b09091c0507110906041d0607110105010b0f130f120201093c0e0c1207080f06 64
    0x19000a003078a41c0e0b41840700f100c150580e8500d800038040060003007800740910402d0b80c003c182800400054144481166680c0001d200103010402c02c21001220550251001c084503c00e41040f01d89558100c1103070002540b15180d001740300d41c030f80492038556050600510b4100c9030401243c0c0c20640d0303204600365481d040301e941180c5056540100150940d5094121030281401c5d0004140b0001c0b0b03192003c0000509164100500c030080c4514000114503c00c100070300402034500c1c4c007558541e03e0108018003403481064240110007000840d646d680081d6041c4180303c00d40d282c0c2010003e1214040c2220005e0260300c20b0180f0402140c180f0075405d0009207017030042502c00a8401d46d0366120049000c01c9600030080104010b14040250347e0702c084004040d000d070841500141004004076180c11480004a040c21103c5486645c3c100354800c0c00c00006104860800041c1d1500c064018420340c40012000560f08c10503000c241458030625580d88541e0300001d103194603894440402c42c0c9070201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 557642706 1250 557641456 557641459
    0xc03030203070212041403190804031b080f01052d0103020d11060403031d0406120f020a0b0d050105101103030406090221030306040e010c0207030b09031303030f14070213020306 78
    0xc2113030a10300d410303111000380300405000e6039012549400f141050304200c80b070701003401031095403000f42d00881d508004580403a580140419510300702c481c20403800361900e90111213076000b1024540741802064001c6403048011a075105c0300080d040022204410313030b041741d100069a0800040c401824122912010303503028625952886d10071000241e00e0394450780007100011440c0fa1820502420072512480a03d0102e03418003e150612000d001c0d00803030381801034503a041d2405280e00b076480f090210780103480c810480781c0d070740c1c0b40c280203901c090328081c891540664410010158028840d500d01004048102c01541ca16255610380c40003030f00341c071501a40d00900700600205680001c81010100c00f100c40d014503240d20b400c0741048110341c82c00007990b4944c2d040030400d0740d81645c00300d03c10058a500003e04051500c03490025440c0d40603601d4503208018002c440441415008800174506d8080c0e940d440602c1c628001d42400c083c010090001e4100c1c8040380410304000503a009544d22020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 557643956 1250 557642706 557642713
    0x50318010809070e1005060703051c060e061c0b100f050604030b011a1c050708060405150d03020c100908060108070e15010516060f0e010e15060315072d0c030302030702 74
    0x1120400031321f01d540314030012404036400083c000d22500171035240d80f014501d200b400f04040c2e468a00c1440300c1e66001800c591203100070003400c3c0c000c3e07207460203518145600080301103e280762281c0c8050030f04900c0c0c003c03c00001d070001c8001415141c888102d43c1520760084c000e600a9103406000d0200f02c2d403c0c0d5229020ba0024014070b2848106040000203074884498080741500b001b0700050b00c02540603003198002d6007840c040003000402c0040d41820074405480d42c491a041605049050441e000982a4001e4520f920915602c2d0311450807010780756400c003500d6181e6610024035580d15040e1003004a1001c45000042c41041d842d84006018107041c10302034500a4003074071401072003915081c1115195501c203400c440c044124403603194081c9115008100700982141407030f5a5002622402e03492403001e00006400362000d01141c1880c441c4a21a8156802c22090240c08a05104a00341c2010b460024480c41e000800e0509a1200358a450300e620311070068404502a40c4018480d809521 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 557645206 1250 557643956 557643959
    0x40510110d022d16031421091e0d050d09050d0306031205070b0604020c1e0f1009030531080c0406151202071e050318010809070e10 58
    0x32040d000500b0208000300f80403c1000b5041c4528103086400c1d0744062420354144007994040a00541a80400e605420302c1e00c0031045d10b00d940f0a080c03042a0b40c4030145070034240141d1078000040707107090240441505807400e000008200b90000407c080d066005a070001300480a81c0b8000c0000b070403001d080e00000301322207441d91070352403800c1d00150090000035581c52040051084681088107101d04501c1c0091400e0307040d0b00c46c145200da01900d5140714540c00598240040b00c1005410314100b140110941d40c4c000010036907443e20400c0000352820b008024280e4244a034070b104a00c1c1071a81921480e0a0001e18460405e080d54000d00c1983c03443c0020f8a020030f020006082880100000001004030810301070900096038102e61040c21100040691490b900790400c2c0d044442c510030600068503018503041000c6000c00c80c030381d81c0c040b4144250608040c001c000c0014200205851503611074100100d00440d4600e104550909650704510428000c0340441a01c03150442c040c0a103084220303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 557646456 1250 557645206 557645227
    0x61d220303110a0c0b06060315040518060c041403010b0a2c0903090a0e01080a030f02010f02030f040203011505011d04110c0610080703030c02010806011209060e011404051011 77
    0x40c3d1000c3c507100c0205540300b200c00104a1a038408603448503043d02c8a50850518913420031404001982e030764880d07501c0320009142c1c054170040d6a056030b07000d0740c200c0e2090304001c05140a198840d00072020807030640c00c010050b5042c1405103100d21607001d801154542e02e041044019030500e40c01d030010901d0804249030b18494000d184500a0030008003560f41d8240c0c11082140940d000d620404001840000402281c0b13404200d0380e4045401d8144528007003c5240d040303004005a0145c0b0380501c2c40801448015080d5659983c45548268000c0000000c80d000c0440540454400e0a0002d100030090041c5681d001044400c150030260001c03c16144000c4407540c9600254103104d02d81e40503500b04101958a1603070900140700d41005002c1003415510010541d9040c40400f83c140a401008035120f41d10514161180058400080041d40b03c117181c0000906010305400030250700304646403403240308101c03599004a41c048010032408003006030120103010084480300c102d09043c4580b5559 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 557647706 1250 557646456 557646491
    0x4050a09050601090209010e0a150c23030a090e09060c0d020d14070f09060c03050711060a0909051f051201020705030a1806050405030d1d060706061d220303 69
    0x1c0c024641001d03854015160004028410301c01e119827066102070f0080081d1844124000100074080c5481c1000340301c9070400c1c20f20000312417008580e450b2543c101282a90000c0041d0403a18003d0f0741d094541643d4414001070b51800b9a4507218642110780401d485003000402070060348401d4001605100407020700b00c0403510303071040c0c01481c0c0c10b180e01040341155002c00001b14080d40c50520480351401d20400030004422160000c060200c00180c90341800307100c44406004003030081c030b019500c00c3c102400034150b6521744100c40c4010b040401051900707104404855540029054000321540341404001600c0f54001031b542d45950308110303410206d44188010802c41c846500da40074000c8550281c0030100b50b103a40080108001803006204036540419a241d0b0740c00c092030203081059590300106020303650000340591040c80040c5031410817041e80c003c001240c03418580d01c40c1403541c0301002c0742014800c6505121905440041c00c00308011500758030515406403030005460340562000c07102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 557648956 1250 557647706 557647709
    0x31a0d081b1f0204030b1b0f160b040f03030e010b010c08130e010e15180a0902180a1a1f0c030201020d050a0e061f210b0103030e0108150109030204050a09050601 71
    0x225800080c00c2c01440054000142c000005003101003e42c3c25400659015008800300d140c023440001a40c1c130000122000d411803400e0b000b550039211801d0600d80554035008011045020078148841e60040c400180704800300c1e8841a100c03142600503969420b101c0d58005040340c001d10701051390100e690400e0b8941036010344a10251030003e4103005050f800c144c401740c0e006500c544040d03030300c0320180d0ba40e00d0f10154209000030340124241e60b0502c001303840302401c1010100c44000d24010041c8440154118017400c401090f003030120b04a860b010b02610f01001007022201040c0026042d01127072141c451058500d0191000604244060301131a09451007070f645040451b4458503400c8103c4414400310b90404006550740825281c1c0540c2c611005403a441030494040314070f0072021050002000300e0a030301740e0101124415603101d140c05412982c85000c02c0f800100b00400040501c000100500170407030050711002c911528550070000a1f1000600c0c0b1540d15807603224220016204000150 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 557650206 1250 557648956 557649013
    0x70303021c0213090c1209050c090403022d0c091f03030f08010608060117070302040914070207050306040b0f19020a030e06060607022b050d031a0d081b 67
    0x10b07500d09400300f0208440e401074200c440c18500e004078a10550b0f801031220f528041c1203030f034081021246410698102405151110782000e094400c002c2016408a030b9482c030207000c10b1032903021112880303051a5600007907210380001d500c215200001482c00807101d03684801c80c6482045000310f410b40001d0302040d183d0044000c11000804400241d800000c2640500f079603203032402003450031800007000c01392244612080d540a520110f980301e03200e50100c40c0a020300c484180050885080700f203d01c0e070011200d05d030041c004c043d008503641ca00420719038080c1e40c1117150507036241c840d8170215014800142003182c0c1c149503d10380103080c11140c0060880689030340c03000070f07000503d65941030401c1d0b00201032603c5483c003006018016510681282e8090303401c00b940420510400000d194400e034881409000ba108080c0c280d503016070300d50000900c00070044081c00041001c50300340300c200c450340d01009000140074403942d02d6044069419207080c1550340b0444090402808003d01141c1c0e40440c100d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 557651456 1250 557650206 557650211
    0xf0414070806060a1406090f06090307180f060303020d08090c10020f06010504020f070f08160c03150b0604060e2206060201151d0a060305010c080103030e0f0312070303021c 76
    0xa00c0c28021000003840f6544421035011705201c00140c40b407040058003071103484c540038032000a03150380050303590444028007140c0085031240d8100c4100000c0100d001b100c0783c20008910320381745140c0114812603501da002010b16103030480090352001d50007441840396200fa800e03000c00b695070304051640d150380d00e9005001c0340e000001c0c0260034900b052b0452030003240104000703a641c3e0601c10403244001c3c1c200e540c02c06100002d19203604244140c6441c00745042e0341c40080c509214100303400c1d204581c495203403204040201e01103101500c5034000160f41c0480305000c00c02640b4020361481c024800700605041056003c1c031032945403101403038080040c256455001f44a855024403900420714507031245400198038100b040300d40030141461050708445420082041400c10303030081d0002d5540540280001c60707540d0300051211409102c1a000161004038091f01420404480401104064058000300c4045903000043d9072102c0c000720b00301a8204490901b515446c10444a90309004002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 557652706 1250 557651456 557651461
    0x2070609060507090305030a050703090503060c0a1b0803060d06090b0c220302060f0919030b041e0b0a02090312072109060203030105040f0e0a05010605040e150f0414070806 76
    0x20400b00c620007002501488210f50f0140007080000050390f0f8620180d01d00700b0740d0f880700703481c003251200702a500480e0180715150500c8072242d41000540030040b00e0365100180d0f044002d60044528803400c074003801c0702d481000801e06500b405206015058000c03c0041360040703c5598001c1c0e011400c8a030031f40540408100403966483e041d81c2c18480450801003035031a281590002000c40c4540a1007107a890ba00040d00e181945a0500d400046400400d00b039417526664100425000f1007118122040c28040c0111400d0a600c02c000d0303c100c94000c118020345a50340a0107100035406204480e40c10700c103181c0e200c40b00292420041c00071910410b00d4007409441050004941c0c0c0e070a411200601c10602401c1c0602a030000582c0e0443c1e204440c0440d1f040c601c0c1d04180c0c01414a982c241c46a1301070041481c0902005400030021030390f060b6001c11074400c0d0501040e413602100b0b1403811b00024084086110380f0910740009030490b000700582c07034491140000031450200720754456811078100404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 557653956 1250 557652706 557652713
    0xe0f0d02281a0904020702040e061f150210200403200d030c170d02070305120108010204051c1401060807031a07080c0c0f06070306030c0504022d070602070609 70
    0x94400800b40c03105000109950100001140d0090401c0f00b0f01855000c5241420340d1364641010304040b0144007a14440d0601c50b541c0031381c500040d0f0721b1036072003440e080001841d00208188ac0ca0a55415400340484401038404c070b4001d4014010301d8888600032000280c420044240103000a601c0b90602d11780d000840704140b42c840c04c20942e85485100c1c0090040d0100e078001014001c040d03404003540c05984143d902c408500d000e295040265107101040d02802c00d604400144a00030040c000005e40b680d80300681400c3c0e102d1805801d030030695a40030000a0802d407217041030031903c500012103402402c1040c0d1801c440c03d40c0c1c4104e41d264040c01d0100244540300000840219111b401d4503114a0644c2000c0c180d0240a44550580240064031502070070f010b01680320a0f0381640c0c01d07110399080c42c1c10002c0207050503010540d0220480000042d040c42d00740308440c04400360040260803a003031040e09803801e00c4036905049441e02c080100384006469440280082c0f071095000207092051400c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 557655206 1250 557653956 557654029
    0x17040f0302070504230a0902090408030a1e050717010344040312030203060f120a060509060601020c0301050108102408210a0207090c02160e040318060e0f0d02 70
    0x108058103092501803a840549c4489a085500507040121590b03291140b080e408000c1012501001e80483c42c580d0800c000e80a640007903015034460ba07905c0b40350100404409903403240c203102c01801b032900103001100300e6400c603200700540c9032114071004103005010301ca082c0c41d810409010003900c3c0d0006003801048a5050803840701c05e450700e401c60441ca80303800881e1010105d4410b45128200c0717452001c03111a41001166503055100c4418071035410420b5446503100400c0e40c110f03000d4000d4200f00026418140304071412124040000c04504c008010b03420000c1180c5d003101c5d800c1d80761880c0c0c003580d00e055291020000342404030050140394000000d8070075042d81c402c000c11000c4030411512400e60b134000b5440080c1c448044000900200c81303102a803509680f00f8001882c030440c0000040d1040800d000c044c46a0b00030b031155031001142e0b03142e8450050aa02841001c5144410304002c142414400c40c514040c0181074009001c4560700010840307402890010000ba060060032009000c401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 557656456 1250 557655206 557655211
    0x11107120b092103060a231018050f01050417030405010f03020405033a11010b010302040f031101020102070606090203040201181511010b0901060206100617040f030207050423 77
    0x84010b440f1800c4110181c070314446440000c070b803900c0004000703e001d541e110309199000748545e844502112030316410315452018080c401e036100c0c225803441048514003030b01c100c2d540d03805100803018410b0308080401484007400241c141c104941400040742c1152240003000a10b10ba1100464a42d03181c000010011041c4580c0c1d14205030060108003c0364800055400350078140aa13482c03440c1d0b804145100d00c82c9524440312402c034544d46a5044660b0b0407140c0c41102400c204028409590f04038010b4050388510302c0303001c42c680c4642008002165607040e4000c1b11080510015207081d40340d848090030358000360418803c10303500000703000442d81c10050100750320920b60421194a03140441d010150130000300e40c04140311011407001600c0c4400e600868849000501051703c42d44c403000300941e6080c04455150380d00c000e1740d1002c241580102e00210502120502d0100d003540c441d5101c1d075904100000450070342c42a101d021420f680c55004480000b166500310300001491256a49020f0802 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 557657706 1250 557656456 557656471
    0xa050d11010c0e09271e07050d020a0e040525260607050f07081603080906130206090616110429150d09060b0a06020309130b011107120b 60
    0x298580a500da40f00d40b18003e070301c5103000350180c0012021302000c0032174040440030700b207150158000d00300752400202c40c21010189070100300e400140d212414070640c46281c2101a6000595040c00c1009118402c0e00c1c90b4003910070300945100b121001c0e0340400400545a40464030f0141d840b080c40540da0001500d141c0011001400e515070004402058035244007a014904000d00040c0c6000348120250449424643c85400255640c5035640d20384642e050b028000c40c0007813040c101080f0007100c0011074038003900200f600441c0c5007045030b003000340d16400700003241c0d046041444143d10450303401c071058001c81e020f80032808040340d0190401080f03542a10201c0100b4280c103120101203914803404518051040e9182c1c444401c010075050030f103000703a60f0b043d1401030801c4094001c000c1907810610600005507840c0940c592190020790310b900503944906d41082c01c0d1406000d50040c0345d0005048104107040a0507502a01c0b001c03541061020303002640400c181202a20130080340000040d446410b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 557658956 1250 557657706 557657717
    0xc120905060a11071110050906030f090f0f030a0e0d020315040303050c072001182d030308240d0503031608010e04061e02030a0c080c040b040504020c0a050d11010c 72
    0x4075030359550a038029007a0420b005006c4c2c2109100c01500807011140d003490000c065a8a034034080e0810040302c4c804680080b03880c001d0305618a070758000080d01020440c00700300950308005142808a0744005420401a4080c4840350300c0e00c0540c8060028000c0b070030071181100b0091415080103402d030384024000c803240400130010f14001c9140b01c501c0d0300340b001d1800350107a054045500100c072401803542c0d030315229078150b401c00142c03001100f01d10100c0400038180885a500040e041c010f101500b0700c400740100e0444000210000c00d00340d400380d0810744568a01e03c02074031200126007003400b24a0300311525840002407002054200ca01110b05c2500c81c64040c0c002d60400d0040c607850280a000140207070341740d20b140f01444003094514040e8017a446811074592500440c0c07000a007910b06500c10110792440c0c0440c0803038a51354126806c1d100e0644909262a04d48020301c030003540b1800c400041030284a000100281c0c0a000345000d4540c01d03076074542d02d40380b28004542142c0148003060280310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 557660206 1250 557658956 557658967
    0x50d09050c2d01030b030c0603010806190c1710080d050714010509070501080c0d092103050601230f0a09050316080a060c1e050301080706210c120905060a11 69
    0x2e81192160440400a280200e044000100400d2600100e00c1260340c3c000004400419843c0c00004d000784a00e000a0015108260250314841260f5a5214010008402c071020700b82c00703155155465000500b01d02000034069032104203d050404104401c00080c10004080c001d02002c80c00c81c501c201d1201c00200150f003810103000369075110f24815641030202c1c00002640c0038008a068131000c110700d100c14000128945011000c500280207c618114590000800740d00d02c40d2182c80d1066006840c0c0b07003800b03a03401c810300c50207056007505429245401c01540e880c4808580207802d035814641c4800440500701341c2018182000102104048000040c00b000503190014a410b402500070500240204054000b2a100c1e807914500302428440c2e00c10401c4030a1b0700000540c100d40c0700c5000e42c2c45194407050b00700c1e64604030801040940d204903610401d002c0345580200d44903001410140045040080400190b9200d441e05030f50f42c0d08480f0400c0129a03081c064940d003140400760152805 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 557661456 1250 557660206 557660269
    0x1e0f040b0d030c0201050d1b030c05120f060a0305120301090e030304050c0d080f070f030f02120d050a18050106090501061704060e0708101a030a0302030d0507050d09050c 75
    0x80c0c002a00150800200e42c40c09015079001b00101d91101d4000e807014400848c5440380c1034202c01c448442c2c900060701d800b90320840c1c0c0b80f00e1000da6007040030030342001203540c880d03100c080540c0302d000e42020b0b84958102c0c0000009641001156480341a9610342901d0b9850803443da0112104048024070710382080003000001400070600029034813040310503100d14250342c1061210b03402187c00d075208445000403158188145210052090b603c03a5031604521b50100808986500e1840300c5c1d021045030a201c80b1110280d2604000d0740b04442c50f2001403c441240c0038007080e46c200640550b010b0750340e00d409104410701409a107014201a041440d03403908200e69072032004400038006085a5502c26481e040b2081c1401000300600d5040d08680713101d40c00e03041a0b401440e41c140d2003251030b241c9450100c01ea007808501c0742107007501744c1c0185040c0240c03210090042c000090002c03003005000c0045140c0d40a0500c41c1e0420310b8001c100420285111009108040b1568550368000c5502d900400222 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 557662706 1250 557661456 557661469
    0x3070509041a100f0e25120e03090312030702150c190201090204050a1a15120a14040b1905010b0a05160f0803100e06090402120c1e0f040b 61
    0x100c50354000d000c081c0ba6520358680649403c0d640100b038203041403074000916003880c3d1584c1405440d88013400e031a11822601d0144c0c0718180b980c061b10100e400c00f081500f2948850b402035107428441026a458185440b00281c200b1007003003007200c0103032008010f000ca5203904101040c4100c82c000180ca40e2401d010120040b1401004c501c1001d042d022242204054400e40000644a501034006e00a50a06101e05030103442c8840c080c1d190840c40510700c254501d401180c000b9071088803601146003040001203510080e100410f0b603038003a40c0b5140e0030301400300b403110254400e42c024040404941043e281c4e031000c108130144025611802d140045c0302c2995150100c90548459051844d5140310400014809110181c80580301c5031234078840c2800d10044c2c40086100e2504011fa10f042d56490f034050000c0c403c0160b9069420001c0080014018181a0311038400002440d04482c80c00ca00d6400294002591400201c5800c0880c009a022424502c0d240ca810000440c3d09001c10f00c54000440c51 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 557663956 1250 557662706 557662733
    0xb03010e10034d030d05030f3105010c030506100806120705150702040b0303040b070206072f011e02030d020306060906070f1203022701210501050307050904 69
    0x2c0080f9000c0c0203081e0301c07020700d00144044101d01c0304141c42c6207107100c06941003800010554024018000e40001c56449030080343d00c0398201541c46043c90303c4085010a051a00301e624510341a40007000104030b1003080c0c04403203a80e10500010a40321400800142580c1010302018020800710302c7d00103046810a0440341c0c4040241c502c06240d03040d00300600e1401805512468102042041e18110300c04464001c0003250300985050102034440030905d0b580e84103503c90300e080450280800b00062400400900a060103049400d031115400002078032580381070220050745101c1d0110003019035800c60620f056408000184260000020070040d440340702d040f40e40e800043c0e0000c001500c0c0e0792244141c801c0d0300c0c4040e050302d4031124545040d11030b903110030000380c910740c20484030740c00750f035100c2d000303c0d0741512240e6141c0c022100d01d540c1078101c00619001250500441c0c40980f840d841007003000c061400c60764400441d4175454002032509010140d0811805031242808000209065402001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 557665206 1250 557663956 557663993
    0x31c18020112240329090601150207050a1e0602060732120106030f0b0f011d1c150b1807110a1a0901091e0201030b040203010b03010e1003 61
    0x740e00303104400110f04200f001002c1002c50412074404001d000b050b18030607184a07208000e01140c00004001c1c544080300490308604143d0100c0c0c01444100f02607001010b1079542401210300860301c410010f0300d03aa4064200c100700306d03241416220740141a0542c00024a100c0c00030380003604108000038820f40c45007000b03203844480009550481c804150005201554007603c041e10b4911090208410200c2841402c00180c10016070b00c8040d030042c465a500b0400c010251010031440b5001034403848004560340441c0d10040341c0c50119501c0700100305902000d02d078041d072042e51452604030000408801c01e1800d076450003101143e50340741c4200380c042818101052082c0f40d030382e0380022240425034180250700341c02000603503010031841500140d40c07094005001d0b4000e96401c0380702f07822619a00030240c900000d10901d0a080001034405401c1540185004100c075240b400108050341d0080c2d2010050300c00000042110035003003440300340c0140701106000c02140c65600c400e82034180701007408 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 557666456 1250 557665206 557665211
    0xb011103040b090d1203020a090e0c04060c0303140903091003150302120f0f03040f0e0702060708100b160b01172107050d0905120d090e04060608031c18020112 70
    0x40c3e100341d0f51440f03001c0a65510010340a0090391800005000c0c3d000f5001841c04210300030408115a0300380b0010512030044200c0090500b4503000080394021b90703480c425418141d844803801164414401000e106140c000001d59544102c43c040c00041c005c008101420140740001c00c01d13204034012825801c4a40440b528461812540103840c105a040315000302c55100d00c01000000505c04400741044606d4000c0c440600303941e4030021442900103c49041c0160000d1000a0400303010f491110f80001c02100711050454442c3c448421076804852403140040d001d04000f070070450781141c2207001d4900070340040c0b1074101104405079208485400c0b42030604003100c103500b08043d20300968504941040403541118500840500b914165001c2d160054602c694500c4100b00000b6441505150b03d03070780c207401545096100311800101a000315900758403007800040e152410005480d80402c0408001441b641d28081d00b012500e00e05044140301000d02401c02c0941e0300001c2e84080012031308c030701 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 557667706 1250 557666456 557666467
    0x114041203110315090a020301081015120503030f0105030c032e060e0a0605090613110f21060a03080304081c0507031d0102191407150903030b011103040b 68
    0x55001d0044448030301200100072080045a8818202600701c8440c05d4602c800541c0b50740700300303c0992000340030744001a444800000005015540320006020440c4a203000d16912980c9400f00b5440c541c1044d10756a00202c1403021454541d01c026004000841c014078030010f18001003904c45201403110aa001042032110055141040a1a52030640c46004100481d04c807942c0302e441301800d4403921091441c048011405081828010b0700070703070380100885889a550040381010b00900010b442c40700a050212802c3d02d16240b000e44641402e104c3d07103490180140502107400123000f0b10140c4500c101c001d003000455000d030212030f049504500090343d280a400c4030700145207421051000c0c282e25042c200142c1642c194000c6489140c5c91070032003c4881c44c480e0441c02e07400340c03444500c821550881d84d6895240150162100000304961041c24510071f81c4035507682645007809224161f0311203d440303040503410700c00d803c8202d01c2404e00449814080010a981e4000c034001e520800200140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 557668956 1250 557667706 557667743
    0x3070501110f1e010f050c0f090a050301050c0a080c0702010915020109050f0f070617010909020d0b090a021206040b0105010f0309020406260616080a2912011404 71
    0x20b49200505a0400c85107104528114030240607101c920142d429440c0410925007490b15000711801224035802590428a00c101d040301c603648605030039a0f1160218800043c0c40d00c0a01889103d44001a9800e40780c074048030010b088640020200c0c610150100702e80e0700180c2e0010140300c1a0356400141440305180510203a00500780c03408050214800d8840e1f10340006000141401204115002d0300c2c0200e82d2980103441c0522103590304160000078100501c0103142e039520001c6400d00003052000311600c1c0e5150308440301c42c103030340113040307904150241420342c2000301c84a07a1030380340b040040001d45010744a0303402c00141070051a040101c00924012035610030b03085006035503002007040201030f40c2c5614101e101000071a22080b40404900380300c0e607040b0f0108540f0f109044034003204800346041c190884840b140100040030a540d201c0c41071100c05004403040103c00c9840c860100150648420020b00ca07050111b4800345038140b40801030007081135120b00341c005a2085046000500000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 557670206 1250 557668956 557668963
    0x3140f1b0406051c0302010b030106140f0a0b0d050f130506040f0c09150509010b07150f06180519020c0d0e0a150f0e010f1403131202010c030b0405060307050111 71
    0x244503640c030001e413444001c2140051102418902d2094000b0040c2500c0700c018582a986a84658029030341d6110041100c0d041840014507030380e00040c0000001a2a8200310f002d0303420bc0c2c4409000c0310742c0ca4040188084082400d41d820041d19030325054017140703a54a00380d075064014001404208910760400402c400260309801500b40d0000c244280d81441c071101c44101c90301c0c4199481290110000a070342ea03900c2c42251106038120400140c41c022884440300981f805080b0420121703511000054035010031000702501c0c0c1c0b800c0601042da4200341880ea40c0c002c045d14119492184101b02140ea003c1d0001882c2c0f030a110a410110392203054800010610f41c0582d03c0890340e614007802c41c580440c0c0c00002d04104038030716265200c414502c0401101c542d004c801481021894a106030780810a03560041e513486203510b64244451f003125a565540880300500142c05030f07440f43d40c0c2814079900b50040503004503003a5020092803070300342d0002e43e5408070b9101f0b180c180010021001001c0c0710a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 557671456 1250 557670206 557670209
    0x51917070b03071101110f030f10030512040312030e21090a0303020106050916080711010209130506130513060506060408070e0f090616140903060a0603140f1b0406 72
    0x1001e80310307202e00d08a80c020308083c80d400c2c1c00c4460355180c0078aa02c20101503400b91000d540300e00c21542d043d87d6074071101d101e036807801501c00207982c1101d000004c001202000f008400d249006d84441d140c500d94034103200e40401079072000041c10b041c10ba400f001c0d07000010703620040c001400b1403612031400d0748846403020700c00d9a0000c1d801071034540c004803d00da0150042c00880e2402da03585000b907681d0041d14003900d0900c07254034000403254001310705041c0c407502d100081110361000042c07806800c0000507495590701c030095000180ca510401c100d91520112003954000c400500313100c0c44c601502d1082c040191580d009000300da4070070210f141600d507081520040c0009100b00e6400c5503d50039901c99080c01280c5500c03042c091000080c02d08030340424222700800640100b41140c04204405607071003402c042c900d90f2044414490b94959650400100c2d0240c0c1c0711450008000d411810300d00d0fa0140c800444178820381c062141c41c1c180d2540056561060b8022041904140801a0010b406440d56 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 557672706 1250 557671456 557671469
    0x170c0403080c010e0d1e0f110604140706110c040903050c07080312060d0f260a110c040209031917071202010623010c060b03060103050d0905191707 65
    0x4511400c00b5401507009540341c014540032151140c0c0046422100359403005400075401d9a09616a002d4500a040050856141c0e00341580041c08590a8624059007114140c5001c121400101d081000c244154400f07071400c0e290420694071b00c0400c6a80d04d4907188015400b450b0707500c4081d41458401c409a92124113104240c03000b80ba82c0b131002c00d560b42c018020580d840300440b804a105480c16001d02001142d0202106802c0802a00d610300b4051009544a10000c146042c10408071030400c02008582c18903101c40c191007107403420780e42c44c00d20035006990099204211070481070f40c0010f0520025840040140103109103480e00e010751044a4030260107190380400c0c108100050302545402c000e00300d90080110940c1c4060f4070010480b022070b000700002c00300c0c2003c038207544200f917075045c000c1c028500400d880c00c40c6c0d8042807801a0980c401e0b50a50883c0791244015584a2600c1006010031104410141c0700501112007201140c441d481c00203c01140484964209008110003080d9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 557673956 1250 557672706 557672723
    0x3071e0210080916050a050402030415181104020a022518021209010c0e0f040e0a030c0c0e090d0e1311030108070b03090307020d03110703080703030e01050601170c0403 74
    0x34002d100b0076501c6800c03e00581070f0140e40c13210054004011208010070b1105154506001d0000951000c0c0095802801d01d0820106545550107039502c6840107115444115805040c1542c07804100203203207228030700401031500202e40c0015a90002140e4200140c2c801d003404009010344200c075030000021040c44112601c800303600b0f6000d000d1907580d42180c0c600580d1108801400c803200201c070300c0082803d480021045040c600684000c044000d800020a60300680e00e0915260801c40110009581234a0010400c03414502c0000281089100c890540c10a001100c0c0c4a20302c080b0b20508001f026440f004055694541003060340e04188810403481e000051440040c2d4024024042617210322000002c6166240003100d1280070a00d0256091143d01d50821000e080326000c03e41c10050300000c003018408040c048030000714891040107a0310300c400d10303020702507401400420790142d01d0002005040c2c0d0b00079280d84800c208196113440d142c0da41d0240c151440c00303136400142030002c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 557675206 1250 557673956 557673979
    0xc0904032006010b090103060819060b0604120f050c0306040f0f0c03080d05040606140607230724080103020f090c0c0a0303020d0e3009060a08070e030f03071e02 71
    0xc4c1c1140105100c680c01c1e0307000d12042d5201d80d0101c0e0781d4034020f003603128643c1c80c4d0070740007000c80c24030790018101d2040149002e01c0e16a03103060700d4132015824001510007a405407402403c2190400c4000700040c41075001d007030319140c580c582ca00ca002c0540c4014144c120742120001c108204d01c01854090b640c4032900c0c6031076101a001741001894115402c4030114507103000411550350340340c5201c6004000409141c5441d14603a1400002100036842e440d56400f008181c0f1011042070101c00094645001c1507580c0000c05949175040321900c00490342403200329801800941c841c000c2c01c10700328409456104030713900c5070380d04031030b00b4415121045264012842c0903c2050303410707001801444090700050100c601c01901181c0c0720020b110203040340c0c400c2c0c401042c264a03c014400d507031041782d01e9900343c2009807201c04200c0310703406000c42400007115902002021500041c151010401c15001041182d5501510300d60303d104030b80d03014044051100404130500000003082c07141c2540a000c6000c6032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 557676456 1250 557675206 557675219
    0x402030a0506031002040b0d02071a01060810150912111908060f0906040f14030d0f150b0a030e0c1302040f0e09070509041109090c0a06020c090403200601 68
    0x501d015503030300d48640210351000d500b01e15a070007130b82c00395020100700c0c52500c001d25600348001d6205500889000304050900c09a01608a0040d8000c01d41c0c4c0d00c0745e0034545400c400180841d01c054001a40e9040c480d40d40443c0203502c02e0b60b50301955540100c525200d803540c10241161200c43c00308a40c40170784501071340c2c140010342d20003100701d509510480701c5940f11105142d62804013290201d403982d0111001401003a144074039000c42da0701441c614014441e20b0100b060039640303c00701c01d00b0150744072001401c264503203205844044441920004140d8144030243d8920700c2505195010540c44001202d046007080c00035025030500202801d040042c41c51542019411902c66005e441d00c02d40400985001c110a99a20601f180009030080505001c20481490401f4000340d424402310341c0ba07003155485007910240075a100c04009d01401300c40c48204006142e0a4000004540108c0c0b4a04199111448007075000341c0e1501b045140181450554072020000d0344030003100d0701c500c01c00000d0b0f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 557677706 1250 557676456 557676461
    0x31603090c1401030e06040512070309231e030606040218041409010e0a0503030a02030c040b03091e120304080a0311030c1215010f120b060403111903120c03030b0402030a 75
    0x2c24000e0320706211040101401985881d012100a46a0f80081c02c0c1020342c8a071000052145c0c6100c0d04101c08150381303801ca0000c4c800c07101c0d45105a400d500504188032840c01c03a9021550600c0c0c0022001d0141c080c02c00f090711805c01410031801070360081680b042801d445c0401c0d491981c0b006e4010000d0350f01c40c0f005030f2002042614100c685501c0c110390a2500c5d071010031200c80c2c054000004519640310742c0b0724030f07009500c02403220364219418000440c401140e580110b010b003d54a00800000803459240c001e03503074580002e800b540e07010f0384003d505050640709480c1d100303411442e0036031902010542640500303206104001c0e980d60010800103032605c2c5c00b026060301001041034240ea0380e03606c2c4066503040e20b07106000e40071400c9401040525071043c66405005080c8200201e8a00b4010f4040380b0f4581150300104d0f030b004800210740417180dd24030130715104041c0400140410034555110799900049420740201006200c5241105060007031308883c141c80300103082150340345030141c00f5400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 557678956 1250 557677706 557677739
    0x20301020409180c0b191404030f08070204050c0a020a06020918041a070c031209020114030705040e060901032f0a0e06031e0c01030c1403090d1211031603090c 70
    0x1007032607800340c010901710414030603500d111444601241201c0504001a146d0311500d070f0300b000c0b4918080001000080004525003100343c030450445454180c030b0310410003030340c0c1c0041064003022420b1200041d85a400242550302c81d070002d400580d148511400304044002000407400f80306011414003041190100d09814050b000200e04905600c440000b12188080100090002000b080261000c03803101d50100c10030920504001409003a080202486600300721187c10200c4c0005c0f6082007a240588000c42e03114030200d400e00955070440d41d41c100b1001d042c01007861501141c00013084900316140915800c80001088140341d240d4070781401400e007001310744907130090160380c62049040740d920b000c16003000f00b5100900b8a040d6500011001008211440e02c00c002d40d4003840c2440408040040d401200000301034107840304070a0003c2c09512869140d00101440c040580c02007040f8001626001424003050301581c1c03411800031000303015141e00151540f5804071000440041c21a04420b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 557680206 1250 557678956 557678963
    0x140105070e011202070305090f2103132907080d050109020403140102070c090f0b041404020114040312140403050f010b0910030503030631060f0909150902030102040918 74
    0x1211114100c0c0c3c140c1c140c1c024603800901041c2c040c07006503400e00e81a0b5080b0700074140503240d13210852001e4100065240d5622040c134994000003080603a001c00015004094082c41c1a2a01341c00341103003011168001681221740868004900c07130041002d070604507085014006401d02032035858400c1d8600079032151104072500c10b58405080785009060080d90031058001200703040c003602c1c000c50700c0090310302078200d02041a52007a081c03810790760b80d1054a000f05407040754070382c4a1070a4030000d00007110452030842040fa01340800c100003040f41200d10300c61990f526002500c0c040e8071540e11514010350700000d00320300803801c92809031101540042d000f2882161660a15242d8201e0003542045901003d4403a070000c00c0000c0680c1403001140c1030b030000b140311555804000c1403064102d0502c0450300daa100c0d032907072810022003d8404000d805009000f501308500d401541e0780100107040c0488024402d600c07801c000301556401e40c10b85000701440407043c400401d41303a001c0c002c401400401107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 557681456 1250 557680206 557680217
    0x7050d020706021006050f21120c01151a070c17010203043003020702180c0301090b1906031d0f0309030601090e0607120f020f03010302030c010e090105010c140105070e01 75
    0x1013084628005c4008a036409010202c0b18405803040c481d03050954528040300a882a10144410004000e41512032000e41000c03601d4131610701c882c3d425541a00303c9100c0c2085081c40a0011000040e8044c0c1a41003440c00640d17580001d150620041645074800c039008650808042c40604041d00254811845809003402015200303050700c0314400810740a00321003110359a0034200501a03401014050300080030b85860b25080100e01284a00444459404240100c0100445a05d034000c0c031101c15002c0303450403040c071441071010503045c10511550040548a10404c1c8415003215605042d01001d9401d4806084048800d41d0b0380390710a0307404500903c120000040d441046104554000144101608107a00d84401c11994001e100071445055580c907160184044d2241c030040000d100201982901d0398510b004241c01c1c520300c201c8641c103010b26810103804076954841c2080c15030710242000240c1d400e0343d04011f4203181e940406016158a08018050500d8100106d01652a0242e860 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 557682706 1250 557681456 557681473
    0x4050d02010606050901030e07080307051c0503060f0405040305090d0615050a080d030b03030c07060201051527070c060515030d090810050c27151204061107050d02070602 75
    0x12402c07210342d44a00e00015905010103034103503120307401440d40da003140c004540c01580c4803103d960441c0e020010407a807680c44450150310210700c60910040740c2d0b0003814003500354030300700011034a100c1c0030b4078103544100c1c0c1d250000b60416004030b0645003180c001030300411030003206243c4400202a283c1951140318485540014030303152400304801925181c1029041f26450644254003030002905125810b010512070070400321820001d0300020001a400821030341011140600c100d490980e00d1802010010842405010390285040384042c4480703600c0100e03a12400c003181c0c082c01c0c00340010400b0341407405000700d81c60302e0442e403154400c08030155560090398250079a20001c0500c21940f290f04400b000c00128202c96201543c050442600d043c50505542004a100e02c0c0d1480d034102d10010038500701805040c2540a40c49200d107258085d4a04141c1211000c1c03004001807004001c5030b2208019044194001d0554090355440780855042ca51403030000b035121040d501987c801481003030311 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 557683956 1250 557682706 557682733
    0x311060109020a3219120203011202010e0f04020c240f0a180804081c020318090a06030203030a0203030f070306030209040206030406140c040501031b0e1c02040c03050405 75
    0xc0b0f5074500b03040e4907800400c1d1a25401120f11002a85050072282107501d070441000c004c4000034152100c0365188141307215116000540514903c2e04c0c12072116205100520030401c0c039440d0746e1603061702401d0030740540304110006a11a1042042d0b103401c03d0000c07404041084002415000311030315080b4000c800007811011551b1a44204e810a900c0620307680803503007110312580030074810f010340d848500e200141c130b80344c0c4811070748070364810440c0c0c1c0c0c0569031981c1031100c04065084040440d1000d94030b07004c44040148948001d2842441c032030080c01002c107900861784c1d4001402980d01400362900c1380101c80c000303500d0b03800440310a41400003240005152034441d100c1c1106403030303004081000c83d8039a07409000e8a038000410403500f8550b1910f040e806a801d503405144a0300307401c551240d13124104400101a1410034020712502000500444403140d0004440300215000b0383d11190892180070342c95440703580c0540d001c0d4005140078070f280121541600004e1180d030040f0304661903035a180c0e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 557685206 1250 557683956 557683961
    0xb040302040e06071b0f06050403090e090601051f02030c1605090c03041e1a04050c120604080d020c070f0f060305181b0402040e090a020109060915030c050c0a0311060109 75
    0x80d0351500080e907502812170715207035540e20f44840c58054041da4120070850343d15102104c3d41a2425030100e194000d04000f00314500d1200c640c0000d400c00a440c041d407410340481c44250180902140303e003001a00305018030310030400c0c3c3d0103e01d40b4030700b110200746500c41c00101403207040c02080d001d81407030000123000700c645804a9000319405031400c0185004401d0b2600245141e1004490944250095011401c020020140698040c0c0013601c0004010340402688200c11108648079800c80070800c400f1482110989441c04148a00540d45a42c032000b2607007400c0540d08209034010352840d000c00da0a05030440c0d58143ca455481c204859101d102c42c901c2c0007445281c00300842d82c0980108041105403003441003454901810140c1030685407002030140765801c8079041c0704c5610010364401035690041040c401000142080e040103410110011a008001204501403548070300c0180c3e0b0403841001141c43c80b1703650030700f43c4120141d1450000c2c48200c203007003001190300c61a03002044980d0300f403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 557686456 1250 557685206 557685211
    0x6091e0302030405040b0103110d06080c010c05071e15020105060102120f1c1107081801051e03040804170a0210020f101e110a020d020a03140c12040b040302040e06 72
    0x141c00540c205032400c0e080002801e800c2c100b590405031258518004989468064200c000c0090b002082503400d02042514184800c1c00042c1082001940311000c18070101c3c1c1d1105586104131a21b4202000002c0080d2081280d840800040f00018a43d104a541036110314003d0343d090b1300303442c011a01219030b44c42c0f40c09100c4c90301c0c2c40001c04100070035440a101940c0c8910314030300840862280d060448180d06500070f507409480301e40b000505282c0d01340d0390f41a00c060309e0342c00342000c81c2005c49400059100d009100744850f00400e002001c242802940402d59004105821126244400d00f004041d02d4240d04036049014514600d004403034603002090b001c90045124004140e5171010b40c41c01805003040300c0f040d148007030307801c6407040007249580078041c403d1030b1803030700c6a548125891000b407808160402000454001680180000780c1c011503507602000d0540e00e090712900500e815a0a0282d030342804441c401d40090009403140e1414050802c40b40201e500b00107100c4901001c0f91580800c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 557687706 1250 557686456 557686463
    0xe060f091804080c16031a06130f02071106041409070e0901091b08010b0306011215062a030c2d03020d02070b0f0322050601030305090f03031603110c060706091e 71
    0x22211001c0d5000fa407400e07d81d4007101c01881c2c030310039103920019001110441e0002084903a0000381c140c0074090b410001d80302d8403900b0303101580380c240303808803410303500b10f1481175103105908400200c2c580a04c035010130250408001c1c43c01c02e55507940c01d03040c0d005000f0034000300e6881090110441c40d40b40961110741c1210100c241a620715030320b15004440c03410702118251049a0f403400a00c05c5c00043e0344ca107078007800403903d0300d80e80d84440144c100081c1d8a00840000c9040380900040000b0b54854814501968882c0c40022001da0301c00103400000c40400321661840180640320303080c1039000442c4131500030340703800b036550321612010b1403001c80c881c8040c42c9514030004c001183c490340400840c045100305a09218426070056074038503003400303c01e078015000607601290041d024030700080c01e252001030441c0198a0007400c0c12403103400003455000035050182c2600300040300c41e4284a40800310f10010501076840c0034a2505e039000381000d800544601e0f808a0081c80070760b00d08401804240d40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 557688956 1250 557687706 557687723
    0x4030b0c070c1e0314150a06082505040c050d0504050c150702010801140301020c070b0306040c09061205041103070902070b070c0209180118210e060f091804080c1603 73
    0x640c5c661314501625903800600c176119400800030800081c6442500450110b1070200f4054605940780c1d28000890030203d140c45034201d820000072003500c00f00c800311801503602182c401d034065030585540c060321001f0b00d400c50500007040100180070848a0701c0300d01c2205c81e1178203054a200207040e1360040c008001d020486c80001482400d42610503c65400e400138005407600a15205150900101d030344050110b02c07012050000d5458180222290078805250001110f440c10741c0040c0716805152000c403240755030700c3c0814207004900c0d0718130502200103411140402e503102c551000a41c06003005640b0390780000c002c82c000a10480904090301d0300204202c1850700c40384e40d010740008000120603001d40d40c550122903011903d1b00300142140c000d0007074003080010741c200c601c3c1c0c2e14440391a00040010b9820480201d6892134151644124403243d040e449500440204446410120780d000d000d00b00b400c00c1008000600004140070300d11582950078050b00000700341055202404000d04008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 557690206 1250 557688956 557688959
    0x1113030b09062d150a08160501030507050d0905070531020405090106120e12121f12020d15240518070201090b040b0a0c020a080a050a0504030b0c070c1e 67
    0x140801119800c02c9402910554520136840043d03040d05540d801000340360812030206010780080c4405100400c8282010b01113464905001001ba200742c2c0003d4010640d1601c00105008041007580040c01f00508140c0100c0400c071710b140c80c03e200a0040c3c10b80076108852041a00c041802500c04841e0058460101030b42003050946045070600944032550360340700d46644e11300e01c0422880d0040c00744e50014564485001c404440362035002041c00c0490b0b00800407071500e961102000404489103048101d200b406544000b81119542e0403001e841c0c65002910006100d6040d03100c400f64030b50042d010188100d8180300c100a0740603e108640e44220b040c214020f03490034981021341c0c003c4240c40001480c01c1d5590302c015600d4800c1d903041e226004240300f04078290916215510701070000b80001e0514081660394105984203203622001045408a41841140d01440549001d5688804101302c90700c0d06041404154000c40310039a840301701600000350b80e40d840f99810300d10089400340800c030603 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 557691456 1250 557690206 557690281
    0x503062701051c0b07050304030e0306040512030a020d06171606020a0b0a021902100f1802130e0f1b04061833090c020d121113030b0906 60
    0x1d500040500202d1843c11070260b00003002203040e03911500380c50321501e4507410141002445465114910b5001e03502080078800031840000310034460040000c0c0255403a40c455031400060b000f840c4141c401d0600300140884c512400c07404048000d02458120f801104043c41c160025403281c2c85207a016801c52005800482c03211440d02d54855640780b0050318103143ea544940d415001e140341c050050f08580118889854a40500a5503140420080c46285e08402001450783d4201c40028814001488000002c1c0345980007210f444006a003900c80004402448648a207205a005070300901d1104c2140114a402c1c407640003926812440341c11003221100d0000f000b03000741c029031410442403041003001d808000003000d2228510301a0301e802686001c0320303a01a107000d000448190740226104050460303000d040d2002210110401140c400b0145054a50602c138203d8844c20301c00310083c001c414052842d09680c010044071048942a5482c20000c180d0504c221081d5284842d0f5096461000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 557692706 1250 557691456 557691469
    0x310090804061d0d081c020405031b040609140f0c0406091401021606030e0601080102030f0c030a060305030f0a08070305010f0605090a09061d0c09060403021e10050306270105 77
    0x11403034100f00c410120b41d000000401d15007803101c0440d404400080d0103441ca800740d40492034034042d204401d60034103080600003501c401424407140700702904038030450104c0c1d4a030303000007004042d200340800c00c0c185405140902c000c8201c034070078a001040b038045a0001d046c8001c403000c0701c04507591084c0041c103005418003006580a01d040c1140f08400e0480e128102d500c0360700004084a8400003441184071800f40c0c100401640590b9250344140200111420700c080c0c003d034083c00c41d14a0070307900d550b41044403004105c0760308007a20307521020551070803a521240041102007119203235002c0c03540c1c510104400740d4809001e051002d000326a0f0400c0034902900162484060050099840548951954048540642c003068410740e03503411400c0100035826010b9000110307245030030300d8281c0c0d81e804a1401c1c851444020b000f64002a165031840034860103a00401000a2017400c0190040b5001801030304282d81c064403510954481e079641e04681a58501c50540441400115030b18000070004c9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 557693956 1250 557692706 557692727
    0x4030f031e0e0918010e100b0a0b030601030b0d08030c0307030501054213060813030801030f020f04050a050106020d0203091311071202030a08010b12040f0201030e0d030b031009080406 81
    0x40702111340302440c00c0075080c02020405500140102045809483c0390800d1302c8a100c80140640c003e03040600102d540706040b241c0c0031100703080105001c1803a034013017030b1140c02000b0080c0030387c1e9000c0280090b20300000029800340303010765014407041c0d0301d8030104000072088040024008820500c2100e50301060102074a09051030b01c0e08071401c881030f015035496940000f9800d006001100d5082c040650402c40480d0055100d001031200952942d8000c1c254020602015200c6503403009140d0441d039840a088240e41800f520502a6040604c104030152400380907030b0015000c0c4112441500303200009846100c032005011176000100a20b613540144841c031586d1247c004100440d201050030240c40703120440381c1d40d0023903594000e88180102103103810380084451030380030400ba00384070401140142d0841c0e000043c1d1010f102481c40143c004080c40c5400740203d000c0c00040c0e046943d01948104d450400030f5040c0c0d11400c1694145504407812048005e040800600c010301940d44982211130 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 557695206 1250 557693956 557693971
    0x60f011d0f0f062106010e16360603231b03040f0c12060507260a1e0605011b120c172a0d05040909031404030f031e0e09 53
    0x307240000b890308001013040319400a81c0180c1c0610b004205502c2103001855003c1040500d031040262150402401c680c240b41c1507908100a40174804012003424044592100e075044140e903009640301c1024000c1d282c0c0c0c1132201c45182c02900c0c0ea8081c90940f00302c0c10b00c10301d05080c1e1030000001d098144a06500098001d0760360304c0c0210b60703190010341d8058170740010303152a1084050911861404409454005101104124030f400704d181d809511a66a040c0f0f102c00300806400079600c40c50208003c1c00f8440c20369403104c644407103000e01c16415504c04410350b142aa650384070742e440c0e003414a0b1b80040d9480001c100030304034591400c00c0d610901d541c2c1c0c03200340704110f008560355030140c507144913402007035081a0460100e100c01031100c80c40b032a0240c003458140007401c031000074044080c015001e64030072810080d8440c20042c0825116010f02c801e80301054250980f030b5600c0782000c2c940c1c08100d41c0c0441c0800e880301c041c03400300b40708441201c2507c0440e82d134074005030214005000c0d24400140000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 557696456 1250 557695206 557695219
    0x2c03032706150916080604020f0c0d0e0f09060d12050c01090c050a1202090c1b1902010e19060f0c060e0d080a060b04050402031008060f011d0f0f06 65
    0xc8040580912106006000032240312000c0001c10081111204002c0d1025030002d01202d14401082d411079000350b030000b4222401a02c0f6403085800c0700080c07048035841000d90045402c4928800d400850300c2da0507a0060f148202d1641004c400d000c42e1100944890368022002284180001e00b010360b86501c4143d1440c0590810704010051800c6d01c02d405021680940440028070140c2801c1d0100350040c0bc448000e031400301c1c01d5070081003400c9000390036140400d13800142c41c4110140b429118451003c441c0c205c8859400d0940307070f131101c4003505000324002020741010035081e240030404c1030203040841528240d00382c07421100380d03000d6810818102c140805c0c0900e06001c0345542c0329100a001900d030103844042c043d607500a00f4008020804403070f4910f405000d004d1401034030141d4096403000d80e40143d89072203054114034401c10a0f84041510b20070401040481080e02680c0c42c100c80cad00903900c0001d07500102d1400322455044501c070608011030300004d2005010600e1603500844080e290 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 557697706 1250 557696456 557696521
    0x409110708040e06130c080a0c09050a06091a03060310050709091b030e030c0d030b06040905181c0c061a03011d0606040509060106120e102c0303 64
    0x5081c295081640607100260001040194a04109600200f210103580f000c00c00d00d50f9540300504103c1000d841140d015603240c0000e4406405000640c004d4040100780d280e4166843c80c00914504190042c1e03c840c446001540d0743e4400030800380c074000c0b00001d0103400300f107042040007001040e00610003402c02001d1900095280400d128482c1d020800d49610607020200d1500502928141440b81c080e503402004030b041c6000000c541d00300d64000d540780210b0017007d0303100010b500d40165000251130615001c2882040c0d5140e40c0c10850f000c0002080e40c0e2886659114541840c00802050300418a030305403103400510a5071141c501403840809245400e00010082400c4540c940c1e00920760f100644a001c040c00020001d45612030421502070256141109695444040600c501020712100000005d201100f0340c005031400050402100c03d902004240300d0007030b003900401d44284503410307071104008a80005411044c2d800090003140345407500e0240e441c409407031382d01603400d8103030781c458 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 557698956 1250 557697706 557697713
    0xc070503040e0406020a390f060c0207030c120507060f1e0206071d03070308160b0901050417071101050a09080604080307031b080103120c0b07080f01090e0304091107 73
    0xd005000344c0c003415006845444004014002d4170307000c0702049520b601000c1881d05a140f0f681007c0950306143d82d01300101210f0700d4070105400030342d14000c01d910b0500b0381d4100481c2d4001030440449004541b036007003559132001c46807070141c0c40a902500640240000b40800c50050100204588952178240000d01c880103103104031542c20755103000160041c20501540300c0c1d001c2400c02510507000011b038116140c2200083d0fa40c1c075070b03100080480d2004181071400c030200c2292441d000e5040740c01d0700381903d0148403a90003000105c40440d503070201c4105410000350740b142911003a6070311119580503000043d0042d02c0c503400107958107041250052000c00c8804092203030500851150280070380302c0c100468090255401100b210b50364074401007598602c290b128180d80d0440390425072075502240807a404889070320400340d01078100e050707050602c50b0762548409541d104046018210200d40d1725a104c0c50241c5040c000c0581203640706000038403242c0b0660b071101d00d044a1082040b41380605540d03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 557700206 1250 557698956 557698979
    0x1090e0a05070c0b042a0f1403190c0f090504030e0f0307180b030607050a0903061e0207030e0415050a03080c01021e070c050a12150e120a12060602060c07050304 71
    0x90b400c0702c2200900014002c1c0396586007003805000c50801e41550700c5414014140441510f5216110554560701c44075801c86d201408a03585c11032b43c001080c1c0d800741c040d0404905450541c820805140b10600c0000b8200c1c1031442074038050ba503d55078180e20b03803203800d0070001400d02d1107616591500480314001401c1305428080702405070400b5022416030310f04401c15040c11030082509040c00701c00c101c44c0b82074a038846010f80580b40d00410000b45a074596801c1d40401400c0d031401d01e0071610004444052607045000002d5a81e03007150144a04480210741c0d0300c900d17155210382508540340e0042440058003110250010400c0f0138001401d03c054501c54041300700c250a1882c082400000c0e1050a0103079000280c0c0c064202560822000c0c3d01e801168440148618009440b03905000341d0400c1c40403180d00000040240c85085a4850b1302c0c0307015070380e6950b2110b4011800304083c0260200c6911180c0a103104944140d0003401c016911030380500c0c8070f60300044040f07585000c06c2202180c01c09408 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 557701456 1250 557700206 557700211
    0xb0901022b020105060607170d020702030d111b09070c0305070f1b081507030c0e1f030e010b0303030703331502010506030619020f1b060601090e0a05070c0b 69
    0xc0080c0c0c0c094030380300074000e4210b40000c1c00b1180600b104001b840007103040589450b4005005103503d541d1031580c003107041d0080c00754200080d45801011030350642507501000704020340f140c41e4107640080c0c07900c1030802d184c8102d49610a4000d84035200242801e4041e8103110b0081e4040d0038124500403581d5500d03c4002d00d14001250a030742c01d01810ba81e503500a02d0003101404a4800620102074080150b030f4014074002c022008154458000084640c420078011304030040103003e9001f690f4181820f11200031884c8138610020785030814032402000140244000701030b003d00a5890b584a084049000e001c5421500c0440010021a1304202295410080400964890b0209280d040c18080c1440b081140d849408583c1400140401680e001c2606600840b140c0100c0302144c3d580c00104d806400744281c40c0011020224901c0d40e42140044545440001c280560744503984030070041d14400120b015000344001d11400182201425078000781d0000c0e0705041c90b40744180c0a40e40c1e049126000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 557702706 1250 557701456 557701513
    0x1020f0d0f051f05090c0405090f0a1b091404151502060c0909180f030409050103050705040e070306050405070b03070c02040b0906030c04050c040801090311071409010b090102 77
    0x480c0072452031081107205154201c1c20340141190760603c072440038507010b0300d1801518400c013802c4000c00e000040c40401c0340c00825000c3e003010300d513251294000110314022101c155081c3d0500070784416180300c1490441c4c50140c643c440170891801c001e0440301d45008100c1043d00543d6880c1c1c200c4513204500d400c0ca001302203c4107042002d41c103141d8024248000a00b09555404050006000c69964603403101d0b40705403940c45400c5d0b08081074541ea032400c200c2c10109481341c000014040390800300358102e50705a0f80030300c040794027040d50b440501c0102c1c2e05000d07206080390001c5000b1300c00503200760083d9030880d0089048035480c03500c4013021081a4002e540f40801300711020324081c114101b0b409010940b06040724407091916106010136111141d0f00c0c00c4034400d59807034000401940e403010546000e030400318000c122500a80c540508114034044e060003951154120010344942c0e01c640803405c0300c0f4064140b80b1240d00e01000c074242134110510160542c010321902c615400b00310148620002c40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 557703956 1250 557702706 557702711
    0x106081504120e061c0914010c23030708070215070e01030b030a02010801050409050102160c0e0c0c030403060207020f090a02041d011202012f01020d05011212050c01020f0d 76
    0x146440d1140900e07a080085105000f03030700d602c0340c82075580d40d410713985c9803002000000c1e628100440b2100003484400001840c09940b02c1e18111200015404a14041000c9d181c901d080ca4503411100d66442c49061051184102000068035084c0700c0c8042035008507450045500b40190301d148140300d12400c03a5148002803483d01040203d41c0d250055452114081d0041e01c80c1c101c61350002480c2c18814001c59001c0e0b03445491000400c00709504554000400003001842000245814400005c4900c100f9020502d050080303043e200000341140e60703803010742d0011803a103071841c0c1e16800039402c266004d980c09030250041c018992101c0d030301144200d107403000c01a92079003892100172034800304031086001003905c1001404404042c2881550460b02401d040d40074220044000901ea43d180340c20400602c40034800d240380500540280101514041c03040c4282d80e00d4820030b030b00e1092000406400140044510706081340039100a000c20780c1c0c043c00242c98030303c0c601c141c903d0030b0340402c6890002c941e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 557705206 1250 557703956 557703961
    0xe070e0103050a1404260309060a050906251101050f0105150715110c030c0c10110a030c08091e13020f0409020d0f0e0d020705220e01060815 62
    0x180d251040560216460004125680640d22034031341d403e0740100300070040c4906034000030071382603181c0801c03000503a45c14000d503480c5860400640c580b0000d0781c2a41d0b80328102004201e458002240b40340c03003008015500300410318040c2440c2007400c44c1007440c2d0103120b2150301040280d031083c01540e00c42c081c0d050440119514150921100c80c00f810080c866101052180000062011607482c034200c005004c08250b404406280703001c0d03881031440d4010b540c4000900d00c0804500440c0900b1042c6040b207800c00c00601482d03050314514224400800d443c0c110340160000a406045c103480340da03024080319810040a1408101c2000b2811903640c01c0c61003003520413485150610000240d00d0304102c00350b00303041e83c10055559500403800740c1d041c81e41d0045020300c00d005065000c111034903034400c030521508901c5004075484034040e183d40401070150010110704d50030605500e0043c0032210746d56034003107600e10030500c0003000380e224030a1003952210400039012a0420548001d00f40401079402e060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 557706456 1250 557705206 557705209
    0x321120e0f060f07050909090c040c0804030806030607080c1c0e2113050d11060d0942090f080c06010e09030403140c040e010209030c040b0a090c090e070e 68
    0x1900241010f40c0103008008003d420b50340182903501e06181a5044044d80d2601c1d4411814a400c1c8419950464901290002503a40c0402014000d40c040d80b9000c085444a01c141038450344205c81174000700f03041b130000c105d20f81e40a80080c9081110b4110440001d8810544401a644945800401076009815500c00d445003002070044104080540a1070880c001001240c3c0c032140d841203921600380f0004035001c0c441003911a030204076009240c9540c903808000303c1401041030040984100c00b28003050fa0200da56034000c076400c50070b18050710201e2a881c0030000d01d10084012100a02a01d0f034030031b1030005910038006400b01e407043d0b11a98441c0180d00c56203103401c0d4140c3c80305e200321070882e040c4000b00da0080100d80651b038002c5c0f00b2501d003100e41084d0a2512040e1000d4940080c5804200501c104042d806080790744811404e0b02c112010a20030001030f14103400e825544080003400c00c10048881da0303c40c1030b03000030608002d08850380d95281740c00c1550044801d080414007030900c07954036 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 557707706 1250 557706456 557706463
    0x207060215010e0f060d0618060c02011a04050c0903030d0902010201140f01090c05090910031202010c050d0203060307030b0c12070f021c030e010c0309110a0321120e0f 74
    0x410603a100036001c55890700c0c280000f1034402505080907414190003040c4607032070b0007100400c4190040e80074042c80c0c80520511030048a80d92007551001e02d0840300c0c2011070b10602560151020003518001c0401d40241000000c041c050152213088004001d000b05640b0103201400c2c9015881a001541000c41e0001a0a490080c400e030003182018038100b0000040020610f130554881407000101118004030a5942d4400c84071620742c80f9a401c0c0421100b0140709004209981c443e00c04144000b05641c8140d00b07951861207041d000c5541809404910101340d806944d000c0c00003000c44012695907250500321450a03500c01130701c0080040e4005490f055005507942050983ca4440d446005009000f52034001c1c00301001161748640864845861180e0031021190700c140e4000c001c04940e407480030340200b140c600200d03a2a000c420449401d450080940007c60350003940641440c1c408090024081019500b10401e0003e56541800944501d2040c085240b020308010400c40c04000b203020b15 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 557708956 1250 557707706 557707723
    0xf0e0105090d0309051e060706111b1609150b21070507050607090b0d05070306030803010f09110c0d050c15040b040302101b03380108073e0d02070602 66
    0x10705143c24029a1b20545980e03040711a081e4222a00080c507074680d41c401c40f41440f0310300001030b20712464499101240c0c0c3c0400c009090707080d440410044075030b41d003000d0800d80d0301b0400c548012000124080200541c0b0b08024500d24805501100007003c018802150741c0340241c4003a0000b980100381041004820003045420142600b41085020701e08483d45255100d04010001015150f00100d141540a904005c01035980403808540325038541820794500ca03414070a0703420040c01c10240c0142502100c044400e0503109501130080708400003415141036106405946051098500340c600000601c01c44a02652254224850f11308160070b0003490200c004c03100540c501c1c03400c0e10780c403070b00084180810401a507506021400b40811000a40c5014103800180c4081800e49480d07c1c1c1034500300b00c8400c85a409880306041526051421165111030020407a1f802d071a140d50401e0907160b140503903040086581c240038103c01840c02450a140720040c0303550143e48005402d02400341c05105541 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 557710206 1250 557708956 557708989
    0x1508190302120c0a0c0e040c0b0c0a05010603060e0c0a050d030c15090305070605060405070806090c16080a030c02070f09110d0207060501050a09020c0a150e03120103050606090103030f0e0105090d030905 89
    0x46604003911222164506c0c0d00c14a09e040a00280c05001e0f4501448000c65a44d0000d00030880c2c581d407810f10a001d40341c0600205914000d0403403d684915010007450162140a08282c00d28070040e503054a0580301c03600b041d50084035221508400a0240c000d252615202e82e0350103465034000e142500c21389101908851182d400c110402c240b9550011000741e010008a981d500f4503221003200801c144101d07409400101d100400b480d0034030000100420103c0c01035941000305480d003040480c2c90303c90710b00a0b00710303800e0104401c000440a07138101c0158030310380c41c0c40d0915140c6100f4504080740e10810084a046843d0001003206140c14408a0010258002d00f540f1b800700101e942511071100a1004000c034034591000c94442d40c40d035004d0a4005440c10403203a541c860b90f02c1000b0491005d100032140c41c413803000040c05a042a1003038234102c03545a111104100c3c941d04041e2a42980710000a041100078844070005542c0d84008804490003a210038040e40e08040501502400c40c8a000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 557711456 1250 557710206 557710229
    0xb0607023c03031c02040f1706060315150a270c0201060b1b1203100906240806032d01050604020a020718060504060609050102011508190302120c0a0c 66
    0x74820792400300896031501341803244e41910820054140000b4000d0383c10503000c0780440800829980383d46007100c04400d0303103130044440b2a030f108020513a8030401c00300c0c0c01840c2d81c002030120701642c002c1c016140b01c100d40200020403207074960f400346010854044600c51100d2524010713600349009489829040d0b50184000d02040e41400034078895445084003a0640d401c0d59016078401d6501405400a08509128001c1d600d0600c5d038000c3c0c5400529000340b81020f844c1090001d4031015250038460034821996501c0804510100145c81084000341541d406004010000580350903009520640310300841000e00c40d0035000400c14210381004050700e0103107104101e1020ba040c1c000600c5421141c80a815501c1700c0c00c2148484007500803580007681250410750081503c9422100c2078059503003e80c000c020f800e024041140c41144c00c1d103e840e4181c0c1040100701c2d08003502c014030750125800f030700480306080c0e4264166001e91344054000c5500b604130200301420410184030510041800a016 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 557712706 1250 557711456 557711569
    0x901080711030a05070c0812070203070906060903020d030e12030316051e031f030b0a0f020304110f01141812060405101e05040f0b090a0b0a0b060702 66
    0x80982e02c0c454528a201805800310701c90741081450011040944140015903030347d000f040301261065046408128441d0103140804682c0c520180319400c00c5448a5481144540c41d68007404040159540250100b0901c0c441c00003050710381003c442120800312008540d0391408015030b10388610521075090070048100489040c06004d0074074407504441044015039a0348801441030492503610010210f040f480c400000248001c00b8007882c8030302c08420043c480300100403800030481c402140d000740781e02a140c1e000c01d01420425104806100c0606180070300400074a081001600024070004040010055003c428107003850000c0000300703000300400d601d00b401e641e06500c1c0c4010003103100e0b03420703986e5405124000d49521025041c50301c1034010003c5042509100300c4c2c5042c402821346940c80d2a90208030308d1040001e0032201545c00030712048071500c800381142c0140c4000b401441e80040288000405607941d58034849040c0a0b182007101c1040c4001880d0b01004c01c4003200c4201c0e074211969 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 557713956 1250 557712706 557712737
    0x2b06060c060203090c13050405010501060c02240d021614030906030a1a0a0b18030f0a11180106050c0615102102030a0c0219081b1c0509010807 63
    0x1024002194000310141e240c0c2d40d44400c0c1e030715210140304699400000d000f80480c144c04c041e4402401140949e000b805641c0c3c90351810350302c000f50083c0003034004160b416001354050100c192200a400500c0855241c842100301031000d0340c01c07080130303454030b0944103460008001006d403806401d0540301004d1814145a400003401c540001400600a1a00c50b030140040000e02d0700c000d10240700080ca14002c254540c201110150084104102c0c503080c4040302103031600e4000b5043c610016203500608410f4a46c1ea00d1045d1003074082d1800350080b2004182000b00c51500801901903c15a03440e152034442e000755841c82c180026100d840004002130404407103484038004400183d02c1820320030309041c0161403400660b514481c10b1900307141301005000701c40000d0b4000541e03091040e8200c98020710301c0e0603098a48091100018144074040006000f01e01913034841d4410001c24800b99000350700c101103401d4813001e090030f04000080d000035800e4210b60300240c0881c0c11040750315015100366003461 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 557715206 1250 557713956 557713967
    0x80114011d04050703081c0506030f06071404030c090903090605120402120a02030a23010203090309040b01050c07090903110118060209030717060106080f19020d0f022b0606 76
    0x209001400401c100000b028440c00b00260401141d100389000e070b0b500303000a0903c0c80f02e01100092611241001e012922a2400048189040c00040701401d405c1e2525401036541800007180c074a103a6109000000204098a02d001700502000c00c0109171580c091800170048521a0400d8017407000601900b8681c01c1101c2c0200d074800e0b41a1009003080303c024040301d00c0e00139102002035040c4213905080c2c040101903000c02142540350450308404020b4070a14600342d0004130b0301408654001d000791140c40c074194000620400060420500e0403007820f11107400d00d2a00d8000e20b6950740c5800400b410594064800b0500002d48002000a4a656018500c01a400f00005442290045010443d90703400b40700f0b0400a280c030384050360300d20541074500c6480d81c0d424402e610200740e04000003002442c60302c411521405250498007580310046010380000d40047c60f620100b0396407082d0024059080307100a244403243ca0050030040d4250f40c00013800074074090462541d503401c4c10350070001140c006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 557716456 1250 557715206 557715239
    0x5010b1602010f09090f0903021b090609041e0b0f0a06050108072f1c0206070215041b0605091905010c15020d0603030507141605190506031008011401 66
    0x2460716510380643c6110455800b001d03908010500340c5800c1383c6072110702890b13005111541c82030302610b11440e0b05925602c9005c80c0d0303400240c1c200a0710390006020f481c2801ea441c1d44544191100b08850401091084510400500803221408024107200e420840011100d9102c00c0350902401440e003003030002010410064142003e100c8641c201141401c20025000c0d02046400c07211190200e1005095540c2c2100030340704c80200118655518400d0720220f07440d4480d07503c82d00145001c4811a8812440100041007a04d4280d0080210411201c17407a1030040103240f540c0d181c0b6220515042049064880c0340b101a495000c0c8020030426070340c00c40400d43c403454020121000400c3c120b020f04000e4071409424070541da151030008010182c100b4058843d00d8003441c990305856990410141c1c0e58140b60400140d407104509040000c3c0c5000e08031038111140640c0e0810090f0340e00d202090391030304103503842c0c204072400c47c8007407020060074482d100106120322804034065141208000c07408189 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 557717706 1250 557716456 557716459
    0x110c1c0803060a150f1808030702280609050f0904120509180c040e010e01030b0a0b0d120e010210020f07060213150806120c01020d0e0a0506120103030305010b1602 72
    0x7100264099036031114460040010343c080e0840003810040c02811500d9840040000c0b88058808007a0907100300d51010030f07124018000c44c0740c502d4540802a1040c0e100750106014000000091408410030840c000123119030b8580c808070505003010040340303041505001c0c4c003400e03664040002103940d00010b004601c0c524209240e680c2440000315402694090f615001c10200005010760001d451b0010001c8a800740c9400c50b41d6600c4608110019900780301c05000340710390102240103070741903600502d10881e004004c4854002656901c59a201d1019100380124405101c6c25413103507010710054558001d9203008500d015884c0c68482e100d80500e41000d80b2042c4c1c042101c41240e10703100d00c0c0e0800f8144020300c4400803011080020203200c005c50380300340546004401604040c400144020401a0507005401d80c01c0b00503008507401c0d000c922403d9400a007151001903241c4541004084211440c0d0410503150704500b4003406a64041c0d1005240240030001c4502000003040d08104640e030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 557718956 1250 557717706 557717723
    0x624060815120c04060b0a02012702060310051201060e070504030c180608060901050a0b010504081b061b0f0c01020a050604030c06200a09050103051012060905030a110c1c 75
    0x215101e418602111103d84a07001032a1040103d03800181502800302001b146c0c1c004c5c00740290144804502c243c2c10680300042040d0041158018130b400c074055640400b51492249000f039a90000405400701c0d8206d0045a943d02e20092001c04c40000829034083ca06e41407071440d01e45136681e901c03401140c1d0f1003070701c099007180129aa02c110450b0011001007600d2801c0310030504001101ca4024282910313a080c005250140080f210350041c02914119007a040241c8000d0b00e03d0340141c4c1c031580300c00a0783d9a102c4410021080c0c00d0500054241801120304000d1800812040072540f509450b0b2002c0c50640d40034840c40b00c0007400000d00d20b41d01c140d0514001d00d1b118420710b80f02000d4410360442200f0348903c0c035460b00c82525140090034414900d40c2d5070454036640c81d0b00540c1103e40071f54088a01040c52442031041040b45800e20114604c02c0c50f0010346200e983c0c5825055411081d01003001403a100401081c40c17a00708003d0a00d15411904c0c0f0f00105840f800c104201100510700902924 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 557720206 1250 557718956 557718979
    0xb12070b09060702100228031409180109090b090c090105150403120e040f0c0e0111100c080f010b16020d44030606040308070f0624060815 61
    0x2120700e0152910564050604200029807880194880304551f081c4800310310000b10030810002104058059142c01d51502c40c0c0c80c101303e414003907440d0b00c021a595040202000314020b810b182e601024005c0c1074400e40016840d15600d0108560710000e07103100519440000d030420b9940e5404402030440f075084071044001341c0c81c1c034840c61290086500180c61300300300d80c100d08002900400b00b5802180101c508100910210ba402070498407600a8031002528072107204d030040d40164409164080343d50201c03401c07200052514000d80e5110103810b000030b000ea00502c468221440c415501404125a0701070400c03881011921907080b01c008042c1c0b02d00400c3c040340c8140a6881e5407004c0f00c05040d00300105803034549805034030028840c0d492088003a040c030141400c0c100c0110075a4081d100c003e00d940d18042c550780301c00d00700b900100420f0358003000d4000e01f034000036814443c0174200ba00001d650200b100c0c80812846801c440c0340d01c481d06000320001000750007001c5d40300600580d20100c44882010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 557721456 1250 557720206 557720209
    0xb040e13020a0305070e0708060d0c0608070201090c0f17061e10053f0a20090108011406040b181b0a080919030801060302090d02150a02010b12070b09 66
    0x142c5540c030143c6680103540010070306480c401c9081c1c1c81400c8a850324140e40c0c482105000f01d0482015000d0141c1c1c90840c000d0226611900d001c40d0400380343d10003c510307103030551980b0452040b01c3d40085c00050a440d42042039080a8040c0d5404d090b0280c0a49805d14041940c0801c07121041950408100d1500c0000c1c0207015107440e04014210243c0b51000b01c1b030111304c102c4802221401a1f14510b01e6100c817142500c103000070350f01384070702440000e441944d00e640e0f1485000301511990100b400d4285090307040b551540c00e40e0074000c103207010012034500002010f403604803034090303e0309001c0c904051944070380d034075404080112010741608216980e95800e03122140c18840301002403a044c000a0007071180f40d4040b1201340204849000d1380c814209103010f5072440e50000b14020046509440100304d000d001e5405420a02c201402105620001d58002450145201d45101440c074001c914080c0250342403080c482c4040082d180e841d03100803070290203a5108910700c69560b03125800078503203459 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 557722706 1250 557721456 557721469
    0xf070b030c120921131802040e10031202010b011b03090302090a09140c010c141c0507031e200a08071101231905130605130b040e1302 59
    0x100c460b6034040c05030b40e0800300c1c6050b03200c200c038400c03c0c07203140f4100d0880824515004111800420620194100c1519100c0d80002280340e81c04012040c0f5400d110029045404003400752042c010242089174990441c6000c0e50031181022030750013103a04d0280f005100380d0b00080c4c0c1e200090009240e0a11008043c50102c071070800540000790004076000078441411042c1e00304032440351044250030740c264a01d000c140c1c1d503580c0419940c2e002880c0300c081200403400c1118a070128040080580c2c3c0c00385c44401850000815803083e03000000c4000510300240b41e40103501030b203003100c4080421030005aa81c00280a0410840f40b00b0b4480d002c4014000b441c1001c2200720f0090b80d00507443c94584155040110088582d5440d55001c40c00c0c10455800c0054404000301514015101c403e0074604070320912120025815861020f0002c20007082d100c0c91000452603000f080c6035910340355111088405c04118071200d9000180e00402403000340300000c0c00e41d80245d400403540076140c00f0b140b09400021030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 557723956 1250 557722706 557722717
    0x10e041407080304150509030304050d0f210e01030c09030b0a18062a0c0b0403050918010906050604031a0a020f1201210f03230414120f070b030c 64
    0x400784180240010300c100c02001420482e5028035070003e05d2510f03040d081d5028803d1141e5141d168000304400d00c03041c900400302c1c100d07050040b00d6448103425966100d21407010300302c54801503e4800340c1c10298596200401418880303080c6000d0100311802d0070003a000d4066400020711600320b00000a44904175940b00e60484106d003c8507407246000c50134403e00501108509214450004d43d26254400844d104200181010380e01d4080c4c1320901d80700c01c04008800b0300100e0402504110a149569640b2140001c3e4810084052515403400c0e80c0d00341210002d40c049030180000f0300041001ca407070030101190114a16080c13003103c0d541c010003d402403140d407030303892410701020a0601020007a0100581a6010304404950800030f010000c4510311940b0f000502600c10303800c4000c0040c0c400c160854540503001d084450369100c4174075040341c41d00305401400c4082c041038004030f440d00d0429110f03410006c141000d03150949a401c1051344400d0103000303850b0001000004101c0b024903180c1100e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 557725206 1250 557723956 557723993
    0x504140f0a181104050708010501081b040e0a050603010506030d0c02060702120316030932010e1f0201050f04030804020d03110303010b030a0506030d0912060204030507080f190308010e04 82
    0x1404501031401c0040f50300360711240d81c001c9180c040004c0c601c0d4050040310f41620016120304406980303645540081201c10340400809c02020b000024900401d000010b0181035500c801103110700d4a00d09160031a08000c01140c400d030f0003007582000340354104940c039074080d80690b0038698809490012580c0c010504006034514440000d9951842407840c000c1c102c024404c1e80c070341c103100d95103240880e804282540035041e00866000c445c1c08030602d09056000901040c10054142c0201c280011902c0d080c0e1700b809100068140c011080e03490b82840703156070100d6400703026a45400c254a0050449000803c003e0061900741403407401d060003164481e410a400e08102c1c0d90301e60f100c0d5203131455600261f41413508203003001d011842914010401d000040c410750342d040012840c0144080c6140150b49080e81c21582c200000300c081201031000d44046d20660f0001c00e04060210300307030761a10b4500d6469040154420a41b0b40020303074842d01440c1110060342050181e902d44d401c10711580d152081090 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 557726456 1250 557725206 557725241
    0xb03040302010903120e070b0315090c211b250c031208090d080a0e010908090a06080c07020d0821070210020c100f06050d050c0a0504140f0a 62
    0x1040590542061003401d03c80d5481c01c0c0782c1d1440c0b00c60102030314401d440114458014410a01411402c80701031680400a81e1600c00324440e005d02103403080307004cc0c41d080381810380041e00ca516404c443e03588840d2500c20100d0075905140ca04c00e525001002c221850400d644001850020004450620000d264800360481004207452410201d90089d0b440308844804942d10120740d194040d540d22032240c0e40c0c0d40064100700c1313110001222803490060040d0790440c0d0321503140f801400d091040e003c1d50b034802d085043d0f460714181c00300020130030254003010401a09000304000c0742c120006450881d07a0580e0201030380411480c080717140c1c0c040c152800c031100100300820b0880070750715544240100455001d0b18150001075000034140c0c4102141c1501551000001c00d464981d9503001851619552500042070b03601c900c00036a500c1d60091041d1050307403007040144043d11742903090034010042214201310035480703a0451020080c000b000204d41c0c0955100040e160121030b008000000e4400e0f028 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 557727706 1250 557726456 557726461
    0x50609030405061c150f090507030c080f04020111070305010f1407020a0303020d09020909030a120b031b0a0b030106021b030a0308060415090203011d0a0905060105060c030d0501090605131b050904060b03 89
    0x800615071741500c96080d00c7ca0800380464110b41c02485180071182c03541c0d4880100740d40d00512500301002c0588100d04121550604001c01901030080f0300203180705500114203a1307616035a2205480c0c141d103000400c40d401209008079103800103a5602d42d80d500d1f040141e2294201030300d0000420482d00040e400495000c03c008041d50080002c1000400350b459411861404031111000c880901c1095505035001002861100f24540201300c0245c500030845103196486821111040d0420f030301c2100507a000420700094807404015031050000241d00801040f58540c074000d181100c00b5003c20702441d0703950300310180310312a81c00f100040c15030300c0360a55503075075074666000e411080d11004000c02c20f02200464481d0105004080f03405410800405c0c1c0c0341d0a20080165a521031500715040744410060400007109600903540240030441001601918100500c003060244140b0110464a000380301d580e11f80c006220f010003c11589480c0b5150030030000840c0003041d141d00a5128500c0200c01c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 557728956 1250 557727706 557727719
    0x7200306040c051306030c120228032003060708071107030b0a0f021927120b0606072f0904080d0b09190207020f100c050609030405061c15 61
    0x79644200c590503078145240f01c031150140022105d00303000003071244002450400c0500d000804204280d40014a0800030b51901c10511405801c1842c0c480980c0308040b5042090258000c035a10202520846100100e0341e0700340020b4940500400c840d0600c42d000c00440d0495204403440c1042601000c201c42001341c4038100760921210403075680540d1400c084071010360900e40c3c0291004490300030504645045250406d40311003c10141c0c480c6110401d121991884140300100300050021020000c00030340d82e4108100392110003420380b4041c250801c068000285100992854020340303030b50001e00d114403440b000c035102c50071503000c51b80101c1900034403051180d030030018010741001c50400c210f162403480900c150a001166040c1d0b0556102c2000741f0018041d070020a40503100a05e8090070985513000100d4141c521480000000c61210f6140100041044002c0e00001040f000b0343c200b51502c00060054421201c9014091048007a1030100318a04d8219501c1c07000440c0040300e10076140d21 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 557730206 1250 557728956 557728973
    0x412052b0510120f021201090b040f020a0e07021510080109060501150c03020303010b130b030118050a0b031b0a03050319030c0c0b0c181f02150c0720030604 69
    0x1203200301c64145a100000343c8031143d40d608a1441e40c4202501c0302410300d9002c00645ca14a20b209949a540700c0110100088240e02050301c244c0c0306540e4581040481c5c014005503030b800b270300001d2006146009101c0b18a40000d00042c5488a030148562290b840342c040390700b1030b04650710030066982000ca941c1d040100903085181a111407071005a104030103100300b20350b42880094043c000d80c00c01c000510081e01011b00600d50b0003101d81c5201c40069032401d1181c003a034400d074820800544c15003071051044801e4022580c120956180078012000540006610380c80c1009050325009000e855940d801c4e01c40980c0b1308011034010302541e48170525070b9801070460a4070003803a00020f140450301040036000310119600950082c2c544422561213150400c0e4035881803030300031b120501041d070303850303103036462a5841021901100e2020341c005150000a80b901100c1c2c1a4003d590f42100c0400030111180016280d20540081c0d00c03000c0800101d003e04500c80c46108840c0d098091401003005000148 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 557731456 1250 557730206 557730211
    0x1c060b03010f0b0909030307050301030b09030f04030807121106070c1112010504140a0b06010507020409140705191406091c03021c0206060109150203040e180c090412052b05 76
    0x3520505441c0d514160529107d2008688200101c0c1003480140080350102d044694004044800c41e442d020140030001110b070003591080b6100301740003840c0400c218009800b004814901d05004540d4803110351f0268960100601c244c0c1001640701545007070151904101500040140040421400082100c2e019103030460b0141e030901c034540700d400310a00c0006400c03400030b90031042406a03510340d40e00468251703020311410390b881500c6107480c44c003240610800c0680501000000c0c64000c0c07400d0280302e00e02546004015a0620000e000c210b030014400300c011802038126165a1742e454494000365507215130400900c00c02d4249079290040540001e2407062050307401d01c0300442500c02e41030880e0b070782d54110358180c00101c1282081081d00300012581d031083c40c03107005881c10706840d0340c15031514040c00c81e00707000100381c0c044988400000500010401180540e080c12035443c00c2c1c4c981725246030302e0340c600c0d10400c00c1c00100300ea50b041c15592030701d50815904c08042e003054020f444e00d0002d020f06 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 557732706 1250 557731456 557731459
    0x60902030a110304030f0e0a030206131a040513050a1103090d020606040c1b0501021b01052a030718090504230105070f05071703040507080705060301051c060b03010f0b 74
    0xb401d10401240c02070340c043e00e00c56580b5075070f00001c01802c02002c9408071103030300102d5040081000003100503602c00002d04180b4400c8191000c140b881c12907900c1e03918000c41c00300300301400200001c2c4034a840d030706141806817111a1000c0b032607403a44c0620000505400345041001036011050020008021400c0200c0800c10303802c41d0240c0c6c403890300b0401103440c40d24030040440d85004007281c0e61004244507100c9035001e00c00041c00c040c0035080058902680c50f6100c896a50b4030001c01c0402110400c510519801c00c0407030f040c9494501860021920001e045642132001c039081c0d6030806030205402c100a4200d4120900180c10b10f071401480304041c503449400700c000f10401000b1210b105104482c0701c0d46440e56034641c200201361090b109a44001c01c00c4c0c1d007007121f100f90740e070300c640001000b140201c1c404c2c002080c1e890b01d4030103001d04101d507903042944911410030040205680e17010030903840812441c44406d01c5400ca241180003060780e40e01098040d424903030101d00100d035941c03281120200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 557733812 1106 557732706 557732711
    0x90711010515031203220c031e111005041509080133051518031f0c0302041a03100e0c0a090b0901140c0c04060902030a 53
    0x900b00e450075107030000b825a206107030030100040da0301c95108040c41800c42c00c001d00440b1800310105050041d1245002c501014050600b404000070355210440f100038804100f44a07801c4544603c0c15140502e07030301c010b0340711400d01e201c11050b90a000c0e651a85018140b41001d5510002c40304001c0230064520310200c1c0c0300400f482448141603110340d07041c1c504103410001c541c802810482407094100c4030102000541c07a03400e07951100c0c102101c1c203030382c5610501d40300e03d078400502c810300c3c2d0b414450000c0005401c01d0311381d40d00c00c00c1c481c0208180040c0c40048402c2d0140d104d6403051320b81480c003071040482900100c00240d504104441c50860384a0399603010340003088026504c071404050005184030304141c02900702401826001615420b00c0403190019003071001c814403c058022000030700904201061140c0d008440b001442048501d44444650009401c1114402d04107032 = true := by decide +kernel

theorem cover : BRFrame.Cov 557553956 557733812 := by
  have h0 := BRFrame.cov_init 557553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 557553956 ≤ n) (h2 : n < 557733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
