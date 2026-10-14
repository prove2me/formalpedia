-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3774
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:37:58.27326+00:00
-- url     : https://prove2.me/submissions/1f6030db-6e8a-4c80-b399-894c193f2428

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 678597122 ≤ n < 678776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 678598372 1250 678597122 678597133
    0x1c0218040b100e031c1107081212070507150506090108010b0d0f02240424120b040e070602070905090c090115030e10050411030a0b060105090303090a080609060108 72
    0x45a01c440c010300a2207140b0f070510081c0ca554150109280c0103203220f4605c0d0880c1e105042c21950340e4400f034660940108081112005c6460785c01d0310f600c400d5126075594030b049081003082d00b01882a0314850703128899007003043c00e0980d940c461003080a00032080e0060302d41c1c2c0d041004206d00c2c00e2410140580401002089008010004201d040f0843c2d00d0240220344008d07001411907403100381e00022513800d00c0005420105080321440f171600309020326400700c4c11a034950114000e00200f484a1581c070b943c1c64681c0640000c800400610140d5041e5811a403034821110b040760301000040c008280550090000740c5c40c0100071001c5403c0500102526000a00c010009aa0716070845042d28030f42101e0280310302e40f607a0305500801400200381c289009400380c07a544031115511545c031460107007402200c1c60341140d0400d6110545010000d0040054801040c0c46500c40d00c00350501200c0501220300e400041000101071441984c00041c0c507600c928200480d070071042c08100c0c0100703680c000a00c07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 678599622 1250 678598372 678598391
    0xc1e030309051c06020c0a0302060903070201020615240307030c0804021305070210090308010312020d0f030509010e06091b0603090a080d020d0e060a24031104021c021804 75
    0x7040c50a007441090310400c5908022111601d1400503c03c400d640000304650341c000d00448103841d1401403400343c3c094021400000c826090100480da800c0c1e40c143d01a00c0303d03507200c00250b08002c914007078050700702d011b4580e4481204908010740c0c00e01440c1c00d90301e644030719280d070006080c1c3d0440d164410402600d107041c0030040e21200c1c2095100204004c0c042aa56a0392000300d16080070101c454200d2400d00b5120300078190030504441c141c90144154952180004c001669103015840040000500440d54503040601c80c0c3d11164002c2c1c41c00d40082110384260b100c0c107240c8a000d40e520340258108904080c02c0003071030140301c180c1c00e1098a00354110300d40180d0807a1640d11400000c0c003092000180450046107a60441c6c0302450542e80c100050940340b01d4803035854170203e8400e0035162500d0800240951802005d8111044a46401002c00d003580d0390550b4000c02550160b4016030284480401400044c850a848041c60580142c0720805441c0400416804089040c0118640320300003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 678600872 1250 678599622 678599627
    0x190207080403020607050a1b0302030c01050315010e1c0b06040f06031a0a1103040b07030b0a1223011d16060c080c1f0905160806010e0c040806040c1e0303 68
    0x201d040301d804413061030702c4840c1030400c00d00301258140b00400300780441d940c036000100b448070310006a034000c0d0100c545807058400107480610041d030f62a04001d0310340c415210709600c01c0d016001e800501a1510348a00da4180c61102d01c0000f0240031900b100c0000c0400c0300310309051107030441c4d0102106060145078516100c2c640102c81000301c07500e20662003000685040c07000d8000c3d594011000b80c01c05d03503e15160405500f1f1400c29140f40c4002420300108000340e00d40400c0c03000a603804c1208048100d01107a403043c0311660103810115500800c515408c2041d1400c0c882e2681c0003007407842031000c1c140c844081c6800c124880b41e514915402800080c444a0703030003001c00000d079a101500640c0d40f09400d940c20714000d000d05003101e801c0450b1800d00015030740ca41006000a10030400c507200c440d424050003480c44058004d0041a80c02400104251058000035903004030120101030301d45900e4444d0142003901c11501039507164415602008038200d0240061209070710341590b001d4850031603800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 678602122 1250 678600872 678600877
    0x9052d01050117090708030f270906011d0a15120e2802100201060513090206070201050313210f030c140912190203070b120c031302031519020708 64
    0x8440710503c200740003402c290340400100000d4400d1b24101c9403a00740850943c042a031100d5007586207210146c0e811400c0a680c015102540d40004258050a03550040110303455170b00c448100038078071109a60707101d44c1e890304c44081014000700111000c520f03980103030181c895550748c8101d200d810b03d8600800400540818002003d40d407188040822600c852001081c82c046588003a5100c114807004000303a1b60158420b000700d40c0180c03200c1c0000729007420f003039003110802c1d00d01135044103040200034011340c4268000d41d400b0340d410040004508032a1142180003c00b8803110b0364030744000c0a480c1c0c001c0d80007841a181951145800e2011003c001d000420a24214000d4070640c1e201092016050703881081c40105804890210f8245041502004810b40151030099000380203961010034415644805c80340c004000150701c980a85800e4800d1442c0d87c0300900091003403184000d45801650300740b20900369442d0813441152607040040c01284500308920322007294034410014500000c410106 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 678603372 1250 678602122 678602147
    0x6040203011b08061c02030d120c05070308010e100f151206270e0f0a150501060206070c0501090804060809010c0912080c011d1006050316030609030909052d010501 72
    0x1017001289407180720515a00710100c000a40c14040c008943e12510f91291203e000e070107035070b0b100744004040700034145e410f8400c162000d000590394100620034070441a207419001901e2070b030049915980c0d0034201134080032641200104010080c400702449a10811100b40c000c00700008000c1c540ca011020340600c00700140d00c0c4a0400c20641d03240700ca0500d039003c1c20540000310140c0380881c1d403c43c0c800b512200c240404a6161400c1030205aa11000e441366030b0503240300d07400410554071000010303035000380c84102c00c6401d507407034820b02c000003124a03014000626081c1c4030080c1c80c2c10300c5c85086003520000900302003001580c1604105942000740012500c80e041800c00780d5400c0c000140c1405050010071013490786034980010b000c0114005407003000a466210100241902e4400b01515070300e800b00d29400c944078011051002c80c882d0b41c00380b00c41d0307446410450116035407a40c146d81901c1d012607280030700054a80025085203060320604403000c8402544030035944c10b141c006401400543c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 678604622 1250 678603372 678603379
    0x424051f0804240b1228050a0503040906031104050c09010f17010806010e10150e04180b06030708120a05160b040b10060e0d080a12090506040203011b0806 68
    0x7008281446400922107200c40960905000c02503840d402c1030010f403c40616090080190140100140d103012030a0200394a082c0c4a5941400322855105002202c07040c00b52900c0c09000c2d030300030001d00d080000f0001000c4210001c01c81c2855810280070706440001d540340500c0c2043c04002c5544a100c0031598000b500742458104100a007004850b95031518020082406c80000007090301000021200c3c120f8020000c1c0000c15607801c0c61031900850305104070442d200b03d40c0f07032040c40355000f40e0404802e081c012344005002442c0098020b5140c101140a4400f0450001402520b06041c082c22001d00403141c0101940a0780f84c080c00c01500c10503281400f00280480d503280e0600100a01e021a0368100d801402a82054200b801400c10300f03640c11400541590710024007a03014106001070510000c00000990500e526010071650184000908101b070101d005042424a4030420304014050401428203107031620525007116500301d001d982e000844010803400b65440034085901503001e6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 678605872 1250 678604622 678604637
    0x13090b0d030e040c09170f2a090612031c15030b0604020f120411040f140718050d05010e0c04050f0a020a0909020a0512060f030709020c0c0424051f 65
    0xc01c1241c0038401900500c003011b100125410106d9000100740410340c204078181c4807030403078502241001c1d240c105c40008003071003014020103091500110351a404403001d0801d10440e0031104039603056510900e000d05248402c413480d081c00e08030510131090121032007405110b00504645900103005001171141d48950b8002502000d4801c03840151a10311040103800401c0d400e2500d42081d001000840701c5000310300d015624412820035000700442203411210119168468040480c2c0c04102041c104c00460008040003820f600c441da45080300900800000400c003141d46102c0341880604d402081c801c509010034445091000b20600d600283e403c1001aa989200401980c07205d003158401e038203041c4081101141c150b00000242005a9546100030156a8100402c01d0381c1281031081d40d05540404030511040a02e81d00516072048030b10102c454480c1d100c00058280c4180c0040c00c104121032450568401c114400f444000e010216000801d080700008042c2d100500340d9a80d80402919 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 678607122 1250 678605872 678605891
    0x10801180b0f03191703100b0a020109021f0206010b0901091514030c030a180503160f020d050115080109050c28140307050609130c120213090b0d030e04 67
    0x70102c0550815001034103a54908681c3c01c42e07100c480140440c02d0311562031192035288403001220850f0700c1010102614185503040161070451038100724001030545d941c59008001603541d90060105c01601001100c1008412070002414000d040c1c0c01800c46c01e0040c0400c0a4581e041a003c509646101105040d07003d04400b080701d5125200041d8541e0100010038801284442801548907081641c0217000200e00c8490f600410a004a4054410742003413024411004041084207207441c05004e401c02c0c0f41c40307240c000816560000c0c0044030160365514031032101c51a212403420040862400810503da441d0b180d1907143c4840c00d0030188560710241034062001c2c0406580c4070142c1d801e2808001e155221840200700700c100d049024400c3c030807440005254600f207012180356003400b504224800c0340181c5030700b0261807170316543c0040c00120000300b4160f0300d00b07202030310b80c0d804c2e07400030800310903d44011881140e100100e0640159071403404000801e400179140c0c3d100030003d0380d0001b07100f40f4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 678608372 1250 678607122 678607129
    0x3111005040807063203010302040b03030c0a0b0a0e010e0c01030b100c02010507061b030e0c041514060403050a03021005130515060f0a09050103060b0a050d03050d020d0e010e0606010801180b 84
    0x50b0913010345c02030b0203680703041040e8076203070241d41624400d031020006084000c0405590b4065040c44640a5104840c80e0000500418800e03821032000c10303011500c40360102185003901d100c240791041e10b07842540700b44003940e41809010100d1394203940d041c0b40c4030b90510009040070690314001e4144440019140304100c031a9212001d03081102883d00c140b4003140708020007420340c5540710a201d12a10380e55005a2405100750b10420030700c1917200400380d1070080000a4480e015402d9035200d10284070001c0411720034008031107a54400d501601d080101409610103d4034050f19082c200c20800303550710006440000c18050345115494908410f40d2a0750014428184243ca0641c1018080c20001503400c00303038100c035040c2c0307204241c244200311042c0140303e007144640c801c0590000b00880e00320301080c010300040211440d0303c140075182c031700700b01c01e804c3c02d94541d039a00034004c5e0741d81c2d000e84044100a00400360008824130b01000d2551505004500c001c0490315607203100383d5580380040d00d6a9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 678609622 1250 678608372 678608417
    0xa05070f030e0d050d0906020d0c02040f060902210703020a051b011b0302070308060d0807020d0516030c0608160906180302030601090c0f1b1e0605010311100504080706 74
    0x44000c1080c2d00c61102c0d45000d0b82c445041e01407500106e62080d0000c28001c1c00400c40c428a040c550b030740c07440020b1340b0783c00b0030010781070140c03100080b250340e4840851800300500050101a0b00100a4071001c451080052042d00e4014042410140306021203041d59900030202c401007030990760300d00c403c503d0402425006000d07185d002d40391040e0b82446d40d00116015005002c0080c042d0701c44c5400da5a5907001d210496540c202c0041001c14200041030040c80d20700c150503801c0e8020021600741c029498030026001e001a0803d82d080900700740100310040d80206800d600813104003020070550000d03800544442450f001d00401d00410326040da41c04d1090322944002550010112859541c2d03449645000b4104100e6680000d010300d104072444a00542c44000d40c00c09910701301d4110700352a141d00804c0d844203007000400c0035040000c2c0c1d01041e420302519029502031003440260400306010800380790003120141d020f11506000401000d0404101c1c0b000300d4009040c42c800a0030000380300300d10781 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 678610872 1250 678609622 678609647
    0x60109050919061a0d050a121101051e01091419181109100617330a1710091a010e0118062702041205100609020a05070f03 54
    0x40211060420074003040742c20440c04416400d03090504c1480040a000940340f40380c0c005807850f8003260405000a10b548014015014a490080b000c0c040050041d404e50b441540c40600005552a00d0380181005025043c010440c1a00030401c4480d070740d10030ba650a034010722001c60744111100640c21408290000c2480d4070b24501900c901c0840d503d4103c0d8544101002980103035110343c0062800c848611076081070f1380854440f980c4008d800ea6054540d04030040102249499442c4e03410460000d10307415450703505050030a00c02d895068001d20151500c039070300400c00394200411000f1a03c0c0041081038007450204008138003c20541001000c00c1c21106807004c140c19024000509004c9030702d030f818140c0300d001e5600d00392220b80c11189000c0c1c07003d60165403c0001c0011210804503001041c544000900200c091300745513a403e0001251034503548143c800c0d421051251440c072880d4482c3c08007600305810708604011300c1300300003066402100390080c03195038140c0002c0c0a260241d6009202c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 678612122 1250 678610872 678610903
    0x6040c0504090617010507020f1e150a0c0f08070e0111010b0603010305100f0207020604151e030b0114070f170702040c110d0c02010e0f130612230601090509 69
    0x3c00d5845405035070460403000c801249500e49070110310020700c003080c01128128107200401900c0b6030b13245440e600c500c566001c8852485400c83d47d84910300384044051081412110002d241380d48004007030182c0010b08103640030003030000101702555400641028451001707190024920300b804950354010720075005030540c483c00100002080080005e0745ea00d0803604075074144454500c0717141800603801500300c02540f00c1c0c1d00380018085450502c0d50b8081400c07403031401c4100300200100e4540b801001c842d041000130b032107080c184440d58006503030544074035041850381d18216050f21840eaa0210700d49000f0103c9514081e609a5020300c0d07826940c28540003001000841240400541000e100c078230034080380d00a07032010203003190080c0000b58045030180c444e0103801503100100040031211442e40d640c06030301100c80d03a00031b00c04c500c0f0710400b40c03e0f40002203a0416507400d0032002d010001d03c884d440100f01806541039050081012030440f0310105002c03c00e5142e90251318280416401038404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 678613372 1250 678612122 678612131
    0x7170f010207081b030f0d0c051e0a030c020a020a03060213080d0302130e0f0703050903070602180102121c09020409061b0905030d0503011509030507080723030606040c050409 77
    0x2407000880c024041c4c4040080000216411250020b880c2d001d03008802804142c14816101441c25a40091800f500703a450010715181107442c01c010071000551112012030800303d69003c06a405200da2801c460690000701b41e11034656001546290040c0001000160042149100513240700080c00140044c8010364801c1641070500070001e40156000c802c1070b0f181c0c2040000c03142d540b07240036800340300d1040e841c0940ea611721344150040e0601602d800045d1008104041c0801d00324405404080c0001401c2415040d00200083c6058418440c1030090041001200388552170900004560b00740401c01041c01309550001030000e00e010b41010301203509210315212803440c801e04491711041c10380c944d140000d407214203140d501c168212181010600400050015000298007075804500d030780f400e01380c072130344030350310a402c100780c0d0750055040b40e0000d0b109005c000c180c1e109448041000700c100403200034900000959515010703104030700569480c84507480051180d001c0b0f40180589000500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 678614622 1250 678613372 678613387
    0x70503040605130807020f28050a05011b260307030f06060311040e19020a0206010608090c0a05010c03090b0307020a02010e030c06120a0204150f030e010e07170f0102 73
    0x105168012101101d86a141c10700040c01000a140121040303504501540c0c1003c2030380e403e2000301c0302c071154043e610000003000c0d0b040080340c540c0309081082c1c0000600380301a2505043c0151a000c54010606000c914460f15240c0c05c111030591509540060f800c0742100a180070440c400e2240102c19002c11400100b0420181c2d05900250807100210008006842d500c040403411103d881404150020040104110b036010180781c058109403026203604c0b2480b01488903108903884000c0160250b04010b00401030340f0f030000b01d41c540c00488034000d040450f01e0000000c208000034010701e4180090160f1140a0510414429002d4072520349119543d0502840207540e88511035012400915600c010600324140490850f00c40d042c040c044d0f50400b0f16403403000044500c001c010b404900e5080c40000340b00c80e50003642030310014264441d4410b040580a0040c01c1c3e507920b5403400d00eaa030504144078a4450000b446070125000c2c104028003c0000d100d0761401d108160200c10745543c008038002c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 678615872 1250 678614622 678614627
    0xc0f031302090f162309060c0a030801050a060503100b0a030b04060303031d1c05030718060518030a0b060112090f11030114010608150f0d03120f020708031305011407 73
    0x14055a40c00e10a030f502c2c4136911380100c422041c08284035035000c07503a011200d440c05a0b4006080c401000800c50b03400c0260400c030003071400d00390140070780003d4000c50040000d403d014680320050007582c5490f924514180f00100e1859405100d80408a1030010f45000994825401041100802070050107260b075a418000c1c0a41600c20340984204402d01c2c0407040c90300f0000d204124150001410501800c40010544154100608040601c03502c81c0140e0000e54454925074058020754480c65190803078a004551a10303111401240a90300c804030150120303c1d800c205680c0468246000b26200860110301c002400000e840102050700e02c00309030342044142103015402d0403055008000450740c1ea03086485003c0284541000305a041c40071810007118282d018692040c0640340c090303c4003c1801040340d980302c0d40426400124508018a13520007140610b016552a20f4019030406c2c801c0e0701e0326100e610003c3c05103e2001e507900003180804c002900304c00124820314603111154a05200003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 678617122 1250 678615872 678615901
    0x403031409010c061a0f031f0509030912060f100806190609150302090907060f1b12020115050105030c160f0209040b0f070206100312030e010203070201020409060504050c0f03130209 80
    0x50600c00c1d041c540004001f81400070b4a0701c8420300750110341301d11103601c91182c0700a01000d0b0142e0040d002c02c00900003151510f04284030856007080042c285071410745041388180802414042c0425035040d410400354400084458000e5110000c0c220b03418000700a05009100d29800801114100180f0380054a1080c02c90001c507802603805c11046d50340c601c2c83d65200c140300d0240c0c5001c503030000d000049040c4121111500300000241c0b14480030061345800790341401c4c803185000140e4560310410507610810026400800c000e003462400d50608803040700382c030300074501c3d42d2400003070015580045c4a8240801e1500b1278000c4c0502c0b038941000e0a01840500007111904000c01c20000803441040c80010340911031417525111040913410340d60360210051144115500305a210044101d81410030b2009601882080e00010780c2d551074151940c05031031082c3d10551056280204000001900030201c40c12109200d80190750303030740ca00303034103806400040801941001c844400c006e80400401c11 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 678618372 1250 678617122 678617171
    0xc0509011205011508040501090f0b150a0305030a0e012a1b03080301170102090301061410140901030c051303080301050a090b010c020108100803220602030403031409010c06 76
    0x310312440560401c48807069450030321441c2e03482d2402859040003180301c0c1040e542c000d44100004202260a40c0720032403a26103818098402e480c0d40c409000039100c68140f403240c5860103aa41d59600c52441d1103803902c80c01010800024802695030a004aa105080c0031030b156107a014848140146080c07072000151070350004440b202075034903c2d0602c42c9110202241100d40c01040c0b240f0b0b6a00304041012484150039000b12259028094070509070740c01e0003440c1c050031803ea140c0310341c40700c52420403401c5009000d15409100c0001c00142036050901d003114a004409e09000c90006002a42120303c0d01c210307100240c07001d159001c0401000303e048002c42c1200c004881d680740031600c0c0c05824084071070391000540070510006046006500905d0400d80c84510840607003c4140c1d274800050940e0b0003460540c0120014002400303d0440100152001e018140b0056042500b16034003c2c040c0e08620403c400002800702c1c06541e56840360181041e0f0340e40c00181030140041e8006e0142d1f00b03280524 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 678619622 1250 678618372 678618377
    0x60e1801032d110a083f1603020606042a0504080d05030a0b060a05090d1e05010506122d1c020d0909110702090406021912060803040f090b01120c050901 67
    0x10b40000e08504000b500f24082d80306d4107404070418440e80d003500c11240c070440b903640103100c401203242802c050300c0010b42a06441000c0e00700c0e6001c640d180082c2483ca0041c103083c82945000083c141010361402000a051003000760a080100800c4080e44d1602803588510154840c1403043e030034440e40314001e1402a408c0700c2040c4120f42010040244a0041191043c0000e209002c035820519050002c266168080d0100c14150b14240c03240c803a0b607064a62080e40d4503074645007805060300740350700e00e82740045100d006828181000200b240c0224030f01c00c0c0803040e103a000b8a000c04150801c2c410140c07110303424828142d1002115002079240d640d910030b00741c0440d0030084005034040c001e000303140d100707280c180c80300745404240d50820100764005402030300c000b9401d01c0541d1101801908801680043e62178030707031840303020400390000d48140340c000729450742041c00100207540322445110191051808003149a0841c1700040300e00840501c104c204013414484044012600311005000a41e8280d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 678620872 1250 678619622 678619639
    0xf0f12090e190e06090a1401050f01051018031203140f0a09080715090b0106051903020a02010e0d0302190305090a0605190504050304060e1801032d11 66
    0x400545600c0114814105004503440014075500c0700401c0c00a10740007464000a960040c1210442c60035004403000100e0b40c3c00504a2024004941090301340c1b040200002d1000c1c2c94160540d444010040c4140c50284020201c4e40223070501904403150074168001e24001e40c0c60340e038188006e074902301300040c002081c0703403e620400c0b0b100e1104909124417011411426030b603c0e0b105000c0001d202c006019901c03181c09000c12000644000e1500120064612003c2400300031810035801541741070f4846d609100d400c0000141006040207480d400300064140181c40380c0092105038050025265031004ea80503080b440381030150560f018100308240e040843d0550505080b06400b1500b00342c0306c0c10f459a00c001000c2c400240c440c0c010303d501c01c0d2a05641c0b41d01e0800c3d2003035501642c40c140c0d0210b07540d0300081000d05c410f55200c040074488c0b0004650409070620803503040041e110040c00040e282c11101110110034210210311b0402c04180014040380c007000604003140140300b0410a40e1044401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 678622122 1250 678620872 678620903
    0x2010c1506052106010b1615020405040b03030c0a02041a21011b080f070318050703120f081b1b0c040506060702030709050901060f08010f062103050304050a0f0f 71
    0xf0380054820310039040140003990800d120b01c40c2a0f00a42050b0300035a801000c80400158914000c540700c0e1161480582c550f4104410130003500d075140c02e801c4c02075000740101960850700084040440d81c040d20000340420a03041001c4012444541c105e4000340850041358902e1404104440504402d0000300188c0e1074020301c6031100e5010040300e20010352540e0106255044004249070480298180014400700309402244c14035100e80b425211a0444a0708100b40403049109092381155454807150302d124014020340118000303043d00104244101c43c82001900f69000c4030302c400038070542d02c1d5146604c3d07005140d44001f40516140035900b044d002c00c04604150b003c1c1c9807640d5006002c1c020543c1091034100042c4030081c001601356407600c81c000390032014030740f04c0380c00780c5803140003c900f440440e444002610403580c01030440a08034400c400c0d02000c0c0602c040080303540342c039020f6500e03122800c0c4545000c00c0f2039030292208007205090020443c9500e043c0c044244070344200a1b86180 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 678623372 1250 678622122 678622159
    0x22806180312180206180a03080703140f0f0706090206130f150c03110703120302070614010303140a271d041e05100f0f061e0501080402010c150605 65
    0x281d0303081c1443c000d00c06150b00f80145016006000d90b49046200c6000c2203041000003807100e1810740c020f995508000501c072080c10780c03080d1100d084d5240400c24601e4441d14010f0f04003544240b10701c0d4901d141c404100c2a041102d07680014034410b4006000b02d0701c6045440b1888800c50840c41607820075001564001801e11180d41c090754064280c0e140d00b02482d0b4140c809032400d4025080c02c10b071501a801300400001e1140e00c100083d00d85503540142c86014901d400c0d021107549110054050b10103400410020754000c4012140788000f03902c89480d03800c0e8800a8411340c40300c01c5206c06100b80d80f01e101050441c0c42040808070b07003915584005000c10008240003252007694040e0000c1070900b0070b80844c600d884a5900c0d558441c8085643c1c109090011108841c0100c0c2d80d440d806458040702e01c0052024026200030300340006a0300e140c2014400d2414055040d403284505100c507031070004040da0700070701e81c40300495004501d070b041c0d200c0350b2011440100784a0107164801c024030003107000c0302d10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 678624622 1250 678623372 678623381
    0xf08040203060103021c0c090902011b0b0a020a03140405030c0c0105070816080d0212090d0918051308040b030a0f2f09040608011a060a022806180312 66
    0x3500034018141c1a4207580a00922007600e582e00d5403650480d05860b0001003801034403100514882400190b00b82d50341c4001400c940041a00110b001688564540814400718805800400c2e60400503a90025050280c001e01401d00010140f02003000401c4240580440100a0f542460040c0c0d02c688060f0001554640507000b8003510642c0306100e09507611215011054002c0e0050410741c0c10100b80340441416680084003507904131a803034051280001e4200102c20440d0954200701b1012400c00d00340403201c2c101c2c400d03004031640c5c0742c1e004a00380011100d07103c25090b4010758110341d00c5d42c9600c0a60010360003911455180b07483d0084014050f0340c2481451002d0b1720b0102901c000f2030f01101c2038420708080303003403008030f160081048140d071346c1c5c070f0340b04041c0100f051400228240c400d039040803000b015403010440c014001000b02c001d21607408200c1c456280403000c80303400300498014030003440c44a602c50043ca042e01e010064082e100c41d484c1c00682d031600c20307a1100c1c0c40c821103c0034002501d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 678625872 1250 678624622 678624631
    0x10615090b0703030b0d030302070b090f0c0402090a03050a080a08071805041a061911011109010f1e05090306280906020c0d0e0306070c0506010b0c150a0c0f08 70
    0x5200d200e001d01030030500d4401402c0c000c0c06440c001c03951102080015034101c440320070460200e64005850000c1020641403258000c488030064004080e108112680f0307036180d1854944a0307a40010412207aa48152410b0042e54122003169030007070a40c07400000307a41c0000340940c0130443c00782c000340f0300714400c10309070542d1841c0c0340341000c009140c0801d100251130748420350501031072252854142c40e211070f00074003010a140032105850041801001e010350610b402d48240d82d07414040f80d0b03c200c0300110110359602030286000301c54001140011100d00200c454900c4c8500c030048520822a44d00001030512000e085056841c9526100305000c860b56002c000180e10304a802050882d0a145c0c2e0300034030000d409460b000d417910021341c001908129442030380b00c02003000105481c0c0582070400015070300c0610f50801075030011003a02d0303035a44c40c1c2c1d0510861007800350024100c12032003401e1255a4003400c000c00c0d050340e64207010010078050140c5400c4800011901004800700328803d49106014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 678627122 1250 678625872 678625877
    0x20a022a090c0d09150b0411091219030c06061517090a0813080618030403060c1b3e10030b0a0e040611030105011205062b05010615 58
    0x38030380101840318a4500800c0d00008000c02c1c0103800c988009801035415842c4542c5100d0781603803c0d00f0405044845801c50b580c06146424040785103245140125002c44e034044179901901414501c0b581e161520407824076038030310307034192420301050303000b40051007014410380c03040c00240d03142c0b5800341140700d18401e01d03000150640c80c1481440b290003049a0003001031000d6501004140c0c03101d501c581d00640078210381c80086041002030f40c0090040070b80001d846c251405002c038000f201e680d624011804040d040a0741d407820403540030b0180c25140c20744600803d09203030002a90800d032142c2000348a05410341003518500f1400e1040240401c0c2c00315068500031085034082030b00b4055045000018101810760b0781910041c2c5940d200101402400341c0f091a21140c41e1900d00041581c44803014200e10301c00500040c40ec42c4e030000800d8005034078203600000c0550740d100c00514480000e5030b603d2110820a03e1700580000c00d03010513080e00740100020f21078195a21080d0100d00030081c4c90400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 678628372 1250 678627122 678627193
    0x203060f130b030a14012f0a090e0a050a06060e0303120408070b1006020c030a0b010608070c0b010609141f080c0f03130218060303030a020c010608060a020a02 70
    0x1418a00014911064200d601c800201c201007907000c00d24003000200c081d2010480c10040c00c0c8044000d0242003514a20084060f400905040118019114152007041009000704502ca0348034403407802c000040c40c100615226505003100604000d10040d10006c1c1c4003400c05401044040c00351070b04645000c000340040d490040c4520203c00c40010141080700e8400c410010407003c50b90038107046014401d102c800c81c5d0850325103100a403600e0b42c03489216002e81c01244101004c900c050301d81e107044942c6418180e00307984d5482001c0300c41084a132802402034100c0c500104d40d20358410130800541746200641e10700001c02c1c2040200c0b00307840381107a000e004a0f401000c44114440c0070500d40298420b8180c81c01d0150790f01c00810180c0044411403450520b41d545001503140c0840708a0000902c0410701c0c005040400101c6d4691000500c661032042e00001c4007040441c0c2540140b004185000c1a2446801e0406985029605c01d003c6078006200311020315600d02041c40b00304484921090b101d15 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 678629622 1250 678628372 678628399
    0x903021e0901090f1b090f0e01050a03230f07050307170616180306091104140a0e0a06060803090906060c0a17120403020a050607020c13091b030c1503020306 69
    0x600010000d45205039100e02c40c03105d64044c51101c0c40342e6072846445010003141003403a0304601c820180d200e41c0e1074204100040050303860720b103044030560343c00c103610203c03079100c50038030340450505416481d0301c0d80700394140c3c4440e4450124401040e1082181540c841c075550369100c641e403d502c40a14105d54008001085034041e050040c40b00005841c14800381207060813101c024854210b1b8800d44000392200c090908000c1040c41c040700c0010115000c010f0000003503460400e0280c02401c1c0b8609554401003200540410080e0181d080d03880348081c0005612504620b07226001109a280194940740c0070804521300082965500c0d482c0398000c1c030001040e13031200d0109602210380290038000801028515003e502ca00620070360003900100301c48007203894440e03e0100020400c1c41103421102d64283c0c81c0e510001c48003491040c0c2200455034004d00d04288424030164001150302c04400b190000c200004081178004444000300c01c00c03810a0701540c2036099102c11210343e60701101407003010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 678630872 1250 678629622 678629639
    0x914101d070b1821102c0f0d020f06010801090b04121e0519020106061b06020f03070c140105071403090a060f0902040f0b100c05120a0903021e0901 65
    0xd00300846100700c80d112945140012030b84494403440d0b26528003100c07104501c00d601c0e0800170ba01c4241e5031100f041140a141000c0c610380e40252141c11242c1c08414010101400400c204076141c40c009801654100f260010000c2c0d034509200310303180d0725030240200000b030119043c840c41c60303100d42000c3c0a28040d035440d911050307000d0210700f007101400907403d95084c5c00350303480c5511030561450b61200740c1d075117076180108903401c81c1d581c000c0c0341168100081031000580c008808003030302e02403c1454104014500e0b1520183c040c0d0340e001000040c0200800420a50100d10ba08105001c3c440e491107890131a000340d800c2c0c403400c82d90701000c1100e081c0b410101c0340300c036801507a0107400c040581d0403900c0c2594816040c0c80858040d102c4031500c0300184c1c019032400744500c10140820040c01c1054030305007400703c0d40d000f812a40e0001405001c0c102441070000074088001e921045412869488160490281210340d80b40016806005808241007501c1100c8805c1c40130003500a245045036031030b00412 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 678632122 1250 678630872 678630877
    0x81003020a1e0f32060d0902010e0907080709170d0e0d0204050c0919030c0b030705040f0e070f02010b030c040e030705070e1510080f07030914101d070b 67
    0x844915140349000240c203d0300e510900054401035410102c102c6070381507000c10412482c5000b681074540782d03505007804d580d0350046586078520094003080d441e01500050790700080301212190400c541c4e8003080354843d40440710a11820741e0382c8a4030703040c1d511400c3d140f41e405140c1003645465801b004080c00039900501030300602074001011084231031555408039003512000d4070326088000c1c0105800c3c04501e4540c8148804440030f12101090030300e9500d8100d14018544203040306030b0310020208640c54451421100540110080900c24036030300e030311820504c10100d130380c01c00254054aa003102e051060041c0913242200034000e00100b80c1d010700b003000400382121200418403003080b05200040d000e02c0b04a0081c030115140140c0703480c0c6410702c8200c0c0c18407443c04034440c40c0c0e4410000031035900043d030300d03410202c001304240d010b0317443e18001c2d001031010800240420103100c40c1840f0012001508040005005400780254608601d5030707480c00c040303201d000c072240c1c00c010f10901140ca8030101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 678633372 1250 678632122 678632159
    0x21030d0914030d0506010e010e0108010b0f0c070b0c12070b150103200c0f0a05060c030408040504090f02131112041b0f06030507090e0412020f10020a081003020a 71
    0x8403103a1406190480c51940c1d10601c009010f140d2203004208480d070704041c1907001c490b000e007000c040503144000000c14428050103608103440b80841c0d4036245200d032505035150584460104e070000b0f80c0350100441c09400a414001441c4216414029000b5411007514a982e600006205482d01c0311a05c9607400ba01001c1480d0401d0303a0f4075441d0a81401540701c013512110800c1d40c42c0e90710f520300400d450070001c6502401c03031260300c03544403440041c100145881d4440b654044079903c039120b41c9003200151096502041d40325052200b40814480b405415011092003224803503902c4c010031f0564000e0b01c1d034018081034540f909002c9441d0302405215160b0b4020310904c0001c0c0d200c200d9401d04580d1401d43c1c1c22406071100446402d00c403042d054813440e86c00211030300b002d007001464600002550f01c1c0c0107000a03e5100b08801440301c1900030420800f51200b46802d840a10780b8000d5404025000003142030009401030001c110000704081c0480c2c01d91380c0103080039040318141050041e59a10040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 678634622 1250 678633372 678633383
    0xe040201050a0c0c0f0f0b0c0705190312120b040507021c090905040b0f0702070810020c151f0902091f1e020d090b0306032e0203040c0521030d09 64
    0x401500203440c3d1586000030b0121000e141d20403071b080c41400300c6000166003207000790341c10810602200c150006910310482c1c030220b0300703400d440c07046e060441c2449007580d200a00c45c3c14070b84843c0c220b4a0308161080134a43c1075030b800708115804042000140c400a80341e44000d41c101c103840020f01c41298242c0c0400e4403190410381034860396824079404603503013160199220301c0300303c05000c004041003003600e8010300c1d00d100405080707040a19180d02c0381200322800e072965500140e22807520b5010b0088034642da03240c20000405140c070b09034030652041d6489840300348042c45100442c42030b02c0da10a650135a00c020f00350424a04810f45a0f24244e0a003603a01c0c1c0601c17900000340075407401162003075103040400d50301030b002511181001400b9200d15030422a000340061040001980b00005c2d80091344082d601c104003030010100c1950003600041c51001611400041000140070042c550103045503019501e074200d0030740480c10300c030b25144408090881742d001081403101c08034154000740c0045000d07a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 678635872 1250 678634622 678634637
    0xc0d030c170601030f2a1e1b02040f0c0e03100e07090213030807060e0105130b060108040c151d030303010b0f0304080f0307030e011d030f030a1d030409050c040e040201050a 76
    0x548002c0401b0003107944010360741421151040d03000b40b91198008400c085c041d0f07100002e80d40600210410018419003100f03d060600c190740e2190000040000c1540b0100107850151500401e4402052103040c028807e000f060001540035109501d40d1001d40d01c041e01a50781800f4010004e54491080c00c030300c62206202c0440810b101400924826100d00c1001071440005240f00d0300352040108080c1c411031101e1008004034100c41882540700c0c2d02460680340507502e0b842c0410f10100341c0d80101070784061000c00e1815641d0400d04040301d20545040d502800c10142080540e40c3c8801d00030200c8a0070709100c020440c041c284050b42d00035200b070090b1410580b040d628480e264204440d190006600ca4294900c52a020b108001c01220140300700154201510300e0203980340310b0304d24500300d0460000005681c42c00d841e400012114018065020405000c004090740d0b60064040c0780946483c00011500000b200c008442c00c4616050110005541c0c0f1380044d18190003041c2c548042c0842c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 678637122 1250 678635872 678635891
    0xd0e040b0f0a0e0a060909030f0f120606020a0c080303061518130b040e06060906120f0f0312090109031b230601060f020307020d060e120c0d030c170601030f 69
    0x2d5856610250504a031084818508400000213030303045540500012883c02201201180d4001454190114242890b041040803e0000c035800110491804030981c5840d5010030850707800320391b8a91541c0104109100243c131100607940742d2000396400e80d8080400b0307080c116003281c0b41000c2e2031000182d00880c40c9418842e004941500381460800d01c0d5982d94203412181845d051064906d405da41c10001c020600c2c10300042a1070760740280645200b1200c9201c422a1003c04101c055200c603120010b450400449a00c1203580b17405c0050180c180080032000514408414410301d041160540c0da401e504031464640c0c441081c00d07c54003130b01c04000084c440e0641c0b88800d0b00381c8402d0040000181443c0d8904480140002c0c1c3c40040d030000c6420810a5401607030710f0380c0d0f000841603081000000c4481c203140c403591401c00c440f2500d80031290040390810085401080c0c00c0000c14541e1810b10000d13181c0042101d41071800540e010700c11051a01080e801d5110f5445511144881712001448001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 678638372 1250 678637122 678637129
    0xa0e0907090e1c020c1e0d0807060c0f140301091a27060a030323040512030705011404051b280f09020306031e010b0909010504140d0e040b0f 62
    0x40d60700203028154000703615001a0860918107403943d40b0355101501508030144001070f00141030b0f48a03c40c0460400c00700340040c1d82c814245210309039200c0030a0390f03107079101d02c0e0200103001e244040c072020034400340800c40624050401c0404241d203900011740b45070300b481d80c800001c22120304419440300a81c111015140c40d5825610302e0001144030558107602d04840c101102c81c030040c500c13402001900400c00002c0c0d040021507403886101d40000420b80b1700d002408031280240d5005907880200f907822103884d00000f100071304030b05019900910041002d418081108801981c008004c1d900c4118403180626442d070070400641c030000e00c05501c03013400015000b41c1d1400c5890960821449404c100040d501c0c83c0703c01401015070341c8040d4114601040042d0311020501038a02d1501051044030f40001e1085d840103280303410007002c800f07c07802c0c0000f940d40200000c80d021200c804640c2c460345a903c400242c840300d5480550303948e41c0b85280c80001d100c0603224944c0715581003020030510304520355 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 678639622 1250 678638372 678638381
    0xf0f030a0605041802040e030903070b16050106240e06090918030d1a0a030201050901080405010902180a0e010b0319110d08031603060f121a010e09010b010305060a0e090709 76
    0x11520184d01c0f010034210700400086403449078011a1300d900400925590391004500c10048801d4150009c0c3c850045004012280341c0030b03200200b00b075103000e2003c241500001c520120001c0102542d80c04145d9402c1c00390740c903001900003107600030400d05c000029803a1500c0d48031340c0008843d2140702d20082c03814029107560031266075074131140d440321030070210428076115208007000101d5100c12b91501d5900080c000340304803181141041004e000140900038250081e0610035400b40000510919a840300c011403e020344040703c00364108154051039038014001c020301e004000f4058140a00c01e65004103041e40075890481d041071600d03501100c940e845c85001c0000601031910303545e403442c02c61585003154400c0306010301418075014080c800c60500404000c2650341c1c8003000b4040042c141418183c6680100049000c010f41d203001040342418451030314046c09021009000204280d00190143c640481c3c000c1d800a0032100704000c0c10100c013106a42050160055550380743d1100c640d4402c0d207 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 678640872 1250 678639622 678639641
    0x11a1810020f2b0305090715050a0e01020a0c1401030b090a06051216030305030a0209060a09061b0b190905031204150c200c0d0308011a0f0f030a060504 67
    0x580184924141d10032050200d0b8100542d61580c603800e29010a0003421034070f000c0c0714800c2c10140d85500040040000704486400742c610152103a00a8a40c0000140386612940c0b101c0c0c0094008219070074254000110906860361243c1d04820745800c0000e00013107c040c54076964101034070340b60048080e881d6800b0550040034110b1700402e8140c284824814410403c0e5425011340e130201c0f40202ca1107429900601c01c0c1c0340c0c1403070722a0b43d80c0c441010000107402207108560f40603000203030002e1f005802030035100880700103850343c2c107488002d0701c0000010340d1040b0001e094110414002540303903601c0d0840c41c0a5600c074075000180c88480d5250289160000c22882c0a200206000d01c4203100d040d1500400b40320f40c00784180800c0c420403a006180c400185c00801915280c0d03108140d0354101400040100c100103880011000c0d00c0b03050081842c0000c0c880c2d03080c41d0002e05110f58100a02c00111142d900d4009a01c8d49010744003002c40340194401045800c0d149d650344e2001c103284d0703100d00030140346 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 678642122 1250 678640872 678640877
    0x2c070603061809151e0e06010303050f131a0705010b0604080a02060c01020f130905010b0708070201031805162409030b07050f0d050411030a0c0b09040f060801020c0d08011a1810 78
    0x65401d5001044d00300c0d801c1e00300e86c100a0744040e0040000943c44022200c2c1c00a80307040300ca480d200003844a58400ca10760700400407418000c0385e280401c102c00c0b0701900c8950f00480c000c0c0680101001446840c1c4507030b00071a61540c1210007a813015042a200929074103c82070300061030300135008401e40d0b4a42088a603d00c20380707180d10f400c00c0302d03400b04d0080c1c80c003500d0000070315480e0003a03603038500d070b220302c00e9010090503d03407140c080c54194001b90031103030f8480350840b05469600c80c104910300d92038040703400b51020701c201c0d844107004200d40100400040d08025101c003544541940c47e10485090010018810441c040011040c600e5280303014203035112076880c001c9550b003480d1425010340418207040358020751081c20060701041e0300711036041c00c0300e12030b48449540d5104880030070044e201070000c56611074241100001c41041c15402442c8443ca60400d648044c2d0b0031030422215044207200b0010b00c1440024900320000b1041c4c002d0110540d00c0000c5080c2400f91000304481c0142050318602 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 678643372 1250 678642122 678642161
    0x606020a021912020405041110021c0e03060a0506120703030306030c090e060105100c2f01050304030e1903050616180605030112062c07060306180915 66
    0x1c50601c0e0300700303080d4a2602120b403030201d8102207090391006040100648242d8a40000c5010300000300200c94402c4005440c803003051a40100c003955403040019409080b00d420f1040c84462441012244181080107006c4d0a552b04c920107404064030000c5c2615621802511405c1d00c2000104200300007180702e0303100411503501d54180200c08140583c001102071303082c2400441c1800d800704485066a1085603d0a2400c200b4001121002c1e0990001400c00720fa06803020100c03820075101100c841c000b64404605407107070800440d82ca00007503400401007030b003069413602c0d05e00d091082604118003503400300d60401da50742c44051800d4004d0344d06c00c84110645a1402c103165012060040b1222aa2004100d880c070b0104010500c0c8014410000c00b0b040480c500d00401c0407641240e10f041d905640d600e5018070010322000301301100b280030b40c0c903070344980e1800050a6000b401903504842403c00d40d51407101c00700313800c5c01c09000800703800c03600351002405c4c40854801c18440c0c10409150100c0108 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 678644622 1250 678643372 678643393
    0x2090406060b030a1a0109050612070203090d0b01050f040209011b1a0123031b0120060106022b140702031501080304030204150e06120f030f0903011b140f0d060602 72
    0x110121404c0603a02d0405c4022a0144003079209c00c021903d82680c241c4003070459a40f0404100d0030740c01100784d182ea100a00882401c00e00c625107208030f06a410032118242c49510120400003207219101d4480d010684044842c51280088006251654001e0740344c000b4510140e4031000750107d090b003010120300260089144c105202c07020381104e201c8160002e10b00660602444d01004101422490400503200c403207915803807225007040700881e208000c6442e07550319803001a403105502400c4001d00d50641c40c61070581070450420400f4410035032960410203641c004044400e81c08483c1c2a070f01881109400045200310f82140d0340244140c0001c0d60b03d03941544104010b8920b144810b00403205805018080c0a00140c0016040581225180d03861100300000504020240c0c202d5078507800045041c01c4001d001c40c00030014031100314002c03c40c07595032280f03124600040170041800a00000c0354800d100720194001d040d015440100c2c0d81c2043c07072210300801a00c0340c0e6007000700160005081c04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 678645872 1250 678644622 678644651
    0x50d120903121d0d0201091514070807050d0311090103020d0e0601030b1603050405060a02091306080a0311150105010f020c0a15020d0801060e040b12061f08010e060402090406060b030a 81
    0x40000b0759013222413501915094000130540991805102643c0e00d4011b8010101805071044c00c108100c1800700c2d84c0c907192142440c0c40b95070070045080e0341c2c0b40641d030b03040c0c0d02c8503100e40700311803141035a000094100000440118000e41003803d58440070750b91214072179095181089114003c1d1f01c00c0341c100300c503460711032100d90300140400600d00c181070400052000048000c00ca40f503201413403800041e01c445070031001407078103110707807455218051402c0e07004034200d04045030111805010f500c1d51070440042e968a16a102c88030301c03403600c903000382c0801440340703600c9005c120114400a10454802c102041c0001c2c0e07070350741c40b42d0005800f20700652210300c8183c3c05020605100609003400200c640c5000b4000d449050805841e0744a03035542d44105490b60b03640d101d000240594141201e03258078010b018000300300022500d400b020388002c480091401c02c14000c58401424801c00f51045850b10b500b031010803200580101e5010752242000700ba1110950055446000140404620407400910a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 678647122 1250 678645872 678645917
    0x6040b161218031e0b0403030605100e311505030d0c0f0b100e070804150c0203070618050f2a0d0b090f1024050d12090312 54
    0x2220280251000542a00000a00b02104a0360005014400c408201e460b03480c19420450004011302140c40c2440b09256040e48050185c5d41d00755000c0100010941080c0e6aa0b100d0340c840580c0103800250013400100c81ca9002d0091300c110720020b4580d940c4041c0720006403414008003402040c4d030b08400b00f05916040100007401942d900345000020220348a0110311401d500c80984685021400329940c1c0310034041640052540199510740360800100091542c2400d450544840201c0e0b41001000d20191089001c95103542d0010b41c038088040e43d5001c081c4c07049400c54085190030541a402098003408914001460b040c041c001340302c0f01000c052048200402c50020303554110000c1409502da03d8100605031360403a401121540d1681204c919041c1c0c050302200c014001d461080b0030407001c80c8c00221031461801501d40450f186440c84a01c40307841e030711881c0e030f0250a000c200d0000c41e420343c0e0a5190840117284c03038024241c59031141017006540da5241000920a031010100f81d0030b42044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 678648372 1250 678647122 678647153
    0xa110c3105040803010509070c0804090c11010e0607030e01020f04060215130201050714030918010503010e030f04050f180705030105040c0503040f030305060d0507122105040303030b06040b16 84
    0x8041110b410103403030300d2046000c140102030083d00d00c134020170b00f00d6003c1e1000070001c0d684040d44507621307a201c990342000b07020b048900b000030505526080e60301c400f044c01140c10300010840180311941d91500220003800140d003000328103560810800d031460b0100c400a01c040c2003103800428a0814054490204e4200140789001040b070160381c00300140e030301c081100d10f45500252803455039840c0600050070342c070594648641c0304903050080003204104010460498204800030050410951200c9803680300707410b24070728619800c110510182c6400300c003240b00b0290103003220308501580b148604030350b80192084004a040132004024034a40303070081d0220150240350907411410240d94080309a101170000030141611407002a01985805410016940c0c000e01281c00d003580e02e10240030143d0000f40c0a4948240e40490034262100548141c480c0f00040e07500c41b40750a1458a0407001040ca414080d0f620800800000801015020103881510751080101d62441840c0c03400360483d00b8007a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 678649622 1250 678648372 678648469
    0x91501090b2b0615020c010315050102060415020717070c120b18190b10080601030215370e01020d1407060b03030a0207090b03060c0a110c 61
    0x71240e4010071481d4501401c52101041d00551502040b110041e080c80e0700000412180c4038029400c02da4000b0349800b80b842e0a0302d0030000300f11110300c956013001c224000c4c0d0340981d000c5070100780000e00b400c1c4c00030000e00d021040103040c03e003907545102030014818807488140308042000020301500c095410b0080103921845060720015644280882030700511441030003c1607207440d0039070902031003410b10030800260700c0e02010300640b42000c405d020a0310340040c0550700c0300010400010018116041c0c0390010070000810004c0082c11044e58440c0e92801894080d41135041030740301e0f1500000d004001e080010340c540e6560342e20300401004220f02503604561140e4094803a054001000d520703003a000021240d41c0f9481d80c01e00b00090100290503903014400020a40440d07a030201d41c80c0180c40b2450800d100480b10401010ba4482d020b0b00d13000440721003004485c41c0107000c1c50880c00061f032a2801d44810703142d0b13000050b1540f600007040e451002c000007140c02e91074842c05a000b58040f0201d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 678650872 1250 678649622 678649627
    0x1b060c050f06072a150c09051002030306060a2d030e210c031606022709070806030a051006060906031808030606120c070c090c02101505091501090b 65
    0xc60b0000d1480c4210a40d102c2041440203d162200c50404c80001d0b6007900001c14003044100b0051010050981c948082c0000e0410301c2d010445180c07260b4421070f041090b5004506580722001000026441a0300940c10b100c00e03200c4824401c03028658410091811030501c04980c0c3c0c3d8030f04040c080d0307894070031040c4a6401c00694012804504030380399604c0003115815540320034000e5041844c500c41d011540304641d917042c403004100907480d00140f0400b20445007014918240c80c82c1000000141d40a003a480703001c0c40300240c003980c0f0a0201d00c0e17121000504450200217661226420680d00d0801000302c1c1c2e8840d40240135260304982c0c2c0500801144c030f402c0100c500009140002a02e114000600c458400004030ba0a50380d0340041d40d020710641d0324410b11500b040d03102c40180c3d9004c684100e8103c0440c800004d107051a0f44a6800031080030780141030b04002441c00100142203484c10b4041b40ca981103800324864644480d142d21425403222002c040b00e42c03840026000c07440c03991007441640f104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 678652122 1250 678650872 678650881
    0xc030411010503040b07080601021e060103020103180f0f2d02100908060c0a0e0303030709050f01050708180411122e0b0d0605041e0605060408070308071b060c050f06 73
    0x1184085a01140607d4082060748860b00100d060100700407104442e1800d00c02440c11020001c44e2481c100d034401d807001c10013005443c03070654081041000241611002d0b190b55004128940e4010644510401011511805444001a4006c4c0310303188010a100705040020460403e006030f100300c40c5490a0100890b445c28548640e1840d000340383c119003004c0400d840440a01403540103d91800c01000d490300c91074905001049016244600c07841241c1810144016500480465049503008880b50346001c00501c0c0c62481050f04100845e00940d44002070034011940002901c130f03451089810800d2810701c0320112240000201c011500d02c4412500d1100442c1b41040300421503114103a00b42d00c42419006510052000e640840d4105040c00c0c14211058400f210307500c0e000800ca4010401c1c640c0360700c02c2c04a140030b02e0141c40d416600581050011411050292010910426a400e008d00d084a00510003000c264003440100300c0d400c0c43d010810005108404000d120300008080030b180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 678653372 1250 678652122 678652133
    0x110d060207151802060d0204032102061f0b0903150703150807120b070c050d08010305101a060d0b0a1401110a02030d200a20011706100c05060c03041101050304 70
    0xc1000e0f00a101e2580007480390b92481564040c1c43c000c540080341d503004500403d403031111041f0484109001070040200180c5260340b105c04102d10343c0d0180403407400030b5007415130515040e4040c500c45a49407041e02c1d10001c4040d41c00ba03000f8407a014643c3c001c00c0c2d0500d0051200035a41d443e030032a42480e0002901031000543c0c20759192402500512070407030f10b40340d02d80300b03075100354142c4800f411900803031801070040c80e00207100038101c921940071100b40d420b004045201725029400b8a0002c1d0020400601503860008080c1101444902c00084d10540c02c00009030740c107505170300201400d40300d0714140c281513800a20310f001c030341c20070805082100020790004ea141c0b20807064440034010551150b000c1000000c0a42c1e41c1e85d83d40c9811100c0c010510b0508034101004000c0c84504900103000e590800d511807001d0209500b0545265110303074076030300b04201100701d0203010340d8200070b5940f01000101d1400c2003041e008181c5110419034a051a051000d021604012114103010f400c02c140030000744e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 678654622 1250 678653372 678653411
    0x70320181c03030b1507031d0d020d0605070201060807090605090709060c06091505070c14120d18120e010201060b04080604022809050f060306190504110d06020715 72
    0x3a4140f8000541040d128000341c07845802c90b8250014a0010503540e04040d008a0829058400344c0348210400217148100329100a01030f0000f500001404502d00008405800c07068114605000100e221921400011300e468103a600c610b030903030f40b190020403d504010940f5904150545070951215040c58009060000c400100901d81030359107034a04284294040075054603004a14107100c241403240c03004181f040022415a56050182c0d140c401c2800d0020306404101e00401240d0704103c101d032403034002841c035005400201102012034600040340800301c0040c1e0021070300d0b60101c0071552400242164129004040740d1401040240100400046d4595116a04849805c0e9a420740401c201c01c0c5207414403500c2007000d0401e000f0a5011041c4c2005101c0c041e42d01c114900c82d55800201991110180c0300182039449160400324001516000164014001d8030391880600300c40002c140f02c1c1c4031817081a40c40c1c4d5400f040310410408450402c10002040410078086000a203400c56a0803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 678655872 1250 678654622 678654679
    0x110409111b070b161a130515071b02030a050d2606150901030b0603191103390d0e0f0d0e06090f0303030c0c10050112080307032018 58
    0x21811341d0802c21000f2595000ca00007408031075049810002c03841030120030030340350817100760083c01240803604c5038542d8101c1c4500d000b40d4034441d0312b98250031089074401900400b42d80501072800e900001c503604000c03112042000e6070f186000300b41d0110960040508145a00040654800512881743c0e1400e00440c40c0c02c3c011500c4a1b6100249001a0014882806015000031000c0304004604400d421407258003000c1c00014000d1202015039a0400d204c02c9410241c84ca40f003900b03039040b41c8488d15416184007400c041540c190448901d840134250404884060403076207450300030760640310511008441a003824014810300c5034440c070180207551408100f45c09000302140c1d9242c0b55030b03810025029480042c0580c2e6903400e19560b00071040c1c1c49104000940d200b030b400c1080f2083c40c2071240300c1c1261700d02c0988009184ca0b5a441040356400500785200705620b40d00341181104d048200c05982d00715a0300b5440e514a4081c0746000d04c41c803111252445100c44a441c1c0c48100318091855201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 678657122 1250 678655872 678655897
    0x10f090623120a0b040f020906071407030b09070f06080601270308040305010e060f04051023160908010c14070c03050601080c0108010b090d0204110409111b070b 71
    0x10500200c07030305090003820103403032128442500344a4402c80b103600011050609a80a2111540802c2e22505034440e03d0301c000c0e00107601700301c04004038444d9000d030f079007624100c0d054858155581d10340140000056030580582d07000783e1010801c40d0142c50070038004041604248800d403030840c0020301040100707200721101c4420850b05002380080d01004101869208410136100c54890508034000c200302d50070305540f485440045034030032504d420618070542d8010010b000d03011422050002a100030140808408604860421007108450700386204240c64001d004d5441c200301c10082c8117050660154096174504a510b80c29a540a1103c5d8112249803042e03030b0303552405282c824140c0e880c9510107417031342c000c02d40017003250000403481e440c004409a035208126600d4000540841c03207082d00a0b64845204600e0b803006040c181c22420300303004642e0946040542c0c811149040d42d418010800c100280092808800c00b014580c444844030100c00420400d0704007039a0003654032440b41c0c0040d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 678658372 1250 678657122 678657167
    0x180902040605060705010f06080c030a110303091c020310050705040e0c04052101060503070f0603091103120408120c151911190201090c050f121209010f0906 69
    0x55480d00c1c0c00c04001410054451561651582400d45c020304907440c400b43d44078205500000e113017400050741c85031458020003506e0100420b40e54005081070f680481a058081403003803151981d40d460340a0404d0345054081c8000c000d40d803040505103000f1491500045140c0010703c111107510200366810307035506d035058a4040d190280990300c18050380c1e120315400013034441c2213440c0301154520205001c4002009000b0107417103800b007503201c0f4442d0140c08101000b0740020019903101340c00100e00c042c0201d00303a03003c14030290046818503c60391000c2e00100000101001381c540c041117040711100003001013a003407042c049942500d0303100460b199200320301d070300c0c0c0031411402ea02880c3c00d000d10142141001000004e080444098001c2880d0111a19100d11030092050040c040d25005503440612045842c0c240020007803000e40004040d0b421058100c02017078036540c1003003580c00c0844078032050f5885448140005001500c4041c980d001c104440380204100380c1c00c0f001056006841d0050100c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 678659622 1250 678658372 678658391
    0x8041112031b0c09070801030510020f130603061509050307031106391b1005040e0408040f0f0f060807030905060f0403091406040b09010201060803070305190918 71
    0x5286001e090b4a580b19504501160400c0c0749001940c01032050080c1c54004003640c2c0c011064403840004d2101500a400501e941010510342c0c0c2e000f02200c0302903400160406a007410150504007840c0c100301c01003940d4038414030550341c1104510182c0c0071186411031b1b116041c800429207440191200801807940388101801540d285401c1e10700d030034a1424a4107030302c0d220452114060000c101840d8090032594a0040d620000bc940349801c101081c2c4c0c0d68003510004010301c04808906d80700c0c00208001030002081d540030250708540900e0040b60035075111400d140d5010401e21b5250311541e0030040c0b00700d041040c50100034070315080f80d2440c01e010301c29990302c20040c1c025209440f001446030040c442004084a05c15480c54001c80c020356503440007644544003442c0c0b0402c8080340a51004051004105641110f0010450350f01c043c0300125119a031070004a140d0b070050700042340402d02c00300755545018040f071f284902d005d00741d2620203007413403403c10500e00f0700d00000c44030354210f03840d00f0400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 678660872 1250 678659622 678659659
    0x50d150e0102040b131d060303090f130c0203120106030903120f0209180f07090609030f0c170609010b0409020a030f0f140a020a0f060503070819090c050907080411 72
    0x8070f000380f6650807103541d180080b1050f44080c140a00405101b0030500d04195104420204d129214100180095240c052686c080161070108050840d42c000d103003025031600c4a100d4001c1c00c1515400d0340045807203c1c2c00c5443c4009481d01604100101460f0800250100741c3c0200d400f030400c514181c0003d044013480103a800603110f0282d1039600114068800c00d840c91601003a1442110300d40300950107611804002c40d03981059128060000300090010b101083c602e1207205003280c070411184148a54030020004e00c80000390665113560030071800c0000b10b120038040c42e40d44007000c946c01c109401080e400504d50b4619400003800c40d00740607805404203d6900307081c42459400206207a4600300e9041010354800681004a0141e156510700250890b03e6070700320f0003901c0103521500d0440d41c40203c00c691000e0001c0100b072400e242c1c1a107554040001e8450300d6500703402400884205810300b8107001c0c0101014203070238100040c030004c12011030314032403601d1351010084800c503040446c2907008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 678662122 1250 678660872 678660877
    0xd081326070e0a0b040606090303030f050103120e03100504060506011b03120b0112050c09041103131e0f0515010b1314010509031006080c01021c030513210801050d150e0102 76
    0xc0c1d41c00c68074007840407d07680d81200e009000c60380710b951f090180c50a0748803000709036103081c1300045c890200c20342007110050140300700b0b0300ca0300c01c0a400c564403500b9141e02002a25070540c0c00380c038010703070fa80f061000c6940e000c00c0307000b00d201054460310041a826036000300f42a2040c1e068107401c5541d841c00c80340c643e1040c0146089840c6c80482031010303003480d5202500310742c01080c04034420384ca400c032001e00c2203503407400f03481c8100b48002801d00380701c0d580d45031110110042c8480b550344c2074000d0781c0074001840b00e0050000040c0114005e0250000034601014002c1d01a0440101200140314101c01850120030070f40583e42e1449012910510840c01681c207400f400c80c030a64580280b40d008100f501c56607000d5001c6644180845081c041d41c0c43c01642c50310001d486500140195840748107140d0f0103900456042550000188251a030f90b1f01d80c01c0100c103071410000c6051801056180d002d41d8040c102074058801142c400b0030325040c9680305940c0300d034003004051b034180d1122a09500f0f01400c1d0305 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 678663372 1250 678662122 678662141
    0x10c05191b020d0506010603151a160b0a05040b060d0203061303050c010f09050106050a05011d0d06020c01020901031409030403030309061116060f050705030f060d081326070e0a 78
    0x42e40700c0711240752138101c0d20303040d0900a080c00a850300b0300d9100078542405a1804403120041d11540f0782d20440703421086d940c0203242580b11807041c200d50900140c02c0100ba9441071042030400a103604082c83c186000d240c01038000c03407103a44070034154805680c01042d00c9820111510079205e00381154501035901e070054001c05c0c940d55203004481c60b09122142c04ca40703081c42c883e000800c83d8684030810041000e6142c040d050000f0b80040d204018a0183d0362411100240100401050400c2e95100400d13680011040c801594021403421480c0d40c1500031280b442d200012810302500d014400ca52343c81c05141300c00307010951200003800502030b150348522441c1e5024100107940b2080341500085e40c20100c41d0403a4060f02c1d020507502c0b184001c1c8513090065006654551543e1110b08141051480281800d179005100404590000303440c0340081150fa20241128841c45240040f0b14004440f0000c640e10804580394580b55080d40c0480c5e9075043d296001d05580c0540c85011801008211f0f440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 678664622 1250 678663372 678663379
    0x280216080c010c020c030714101b0606060e0306010e06010c030908061003051e06040f061506090f0603060b070f17040306150b0a020714010c060518010c05191b02 71
    0x1000007001c181034200800e103410503000c84481002034010305564140e80e204210020404002e114030030300d8126a030460444542c54403403140c0c2c04a0820302034080b00000704860f001e0303607010100685500003a12006881049025000c2503151141e03d09000c07200400342410041341c0b0070941c04160185141c600906418000c4404900d02802c13101d907001c440d800141d400d8403031604014040c070303405016204004c10b104040c1c086070715985c0d55108242652601140d0440c1c440070300720841c86010035800000c0507181e841d5035001c5d2402c5886020701e1016080f48041500b40441030003850b05001c1110441e952051180400340c1c000e040000b02c0814525450748800e40000e00042800980d4000c041c031607109400c0140c200d03944082840403849203800100150300300040030804801d42c0070001340c80d0314042c10044180002c42d5a00300c01c0f56011610486905070f40c40303d4110b4004244654900c040f4641000ca28001100c0b0342420340c0e20b07100c1c40c807004019500e803c284440070355807901c41445a015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 678665872 1250 678664622 678664627
    0xe0d0c0311030105160f050d020d020d1a060a02030f21010b0a0305070c0b0711010e0111070b060409020108010b0c010612030503070201110301180515030d0203040e28021608 76
    0x28603090288100841501d44a503003041c01103850042c680510716582c10494541105c000289007003a03070260820a4101000744c0d09100c0070340d515156000500c0c410074100700c001802d0400c0c0a049107410406d003842da00880c01407009550803030700041103507070390100c080384242c5528005000003041d05107241c041003000681000010804525406080034421300d4506020395030700d0711401c031080f20024001030070124180c0c001c03408050080200c03c1c181d0324008000b0074400a4080d5403401c0d10185401c0a4102d640010101c09202000804640081c4201c42c03d11841f000c1d80c0000f042c85d481800349103180c074000512002000c4003540000003c0c160a115605901c0c44c6080240c9a508121403070000765003400365510440074444101c0c0d041e95400c1000a002c42c03ca41c500c14020000101010b42c01241c0110711411581c0c20801c03180c02c81a0380d0300650707881d0f062400d11a00400058260141806103007142e08000280781803c0e01051000a40180c40e03030003046100344841003440000d890718100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 678667122 1250 678665872 678665879
    0xf0907090513050d021b09070807030906090203060709050406090b09070f02010f0f060513110d020c0a2a0b0307021c1b06020301080d0e03071401110d090509061207060e0d0c 76
    0x4900b02d0301d07400402c1c5205101e14503078400c7c803103580021201c1900050a210028500c94060fa00c100a0217004e1704d07001809400590200385414421ba074000e021505010742002940b0301406658040c004d081f01c18804c000301d2030041030212101070081018040c0c51220310441501c00d602c105410003014806200e030114a400580080c90b40e40a03150054188514500040242d40a88001001e514624629045003551500000e4002c8048400b50740100f0709900003140c00f64010747c02c2c200e084a03850344c445031840c50511401c0d00300c0c0d200600f06075090007005034258010904000294501140303208801030100304a549480301d12421601040c500104010f01000d9400303141681e800004943d1a01c14984054401103209080164580c0c4807000500c0743c007180d81183c00449206061900d881600c0c014450700382040008841c0014030608000c0000e0724056000641004081d184421903506551105803200010b0007500184503100705541860380b80c0c08040090b9139000703c00c012010f0745 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 678668372 1250 678667122 678667127
    0x7062d050717070213020d060e090c030705030a0803010501051b0d18051e0f0102010b10030203150a12121107081609020f04060e010e100f02060f0907090513050d 71
    0x300041c180e40c00454014060385049405040310038030b58000b001603604115009540001e907004440d00740000345c0b074200000e1b045040041441c000c02c2000b000c0c1c05102004000e161519205070320161103035000042d07680c04502c40c1c074100c07810750303000386049a611501d07850908030500b290394402c0755920491009100c010b41c0605c00d0001404004a681c9038a07a4940c104010304112074a40000c0e50401d141d8107200d4505181510004030041c0004110002c0307400008480d61207030014100070980010401000d07084250300c00116000c11120040e5923403d040005e180c455584000805964045100102d110b0180c9545100e684c107040031a0211521a05044e880e09111200064912a0b420000c50300c1c21031402618030752040700d410241068a0706c002240e4051100c0c240d079042c4130301d148100c80b0a032121040341642a0b100e88800d24403005040c0c00a2800100403c02b4100003525010700407042004241401117409251012610340c40d07601c140000395207180401441c500c185d00004030843e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 678669622 1250 678668372 678668377
    0xb0c15040f0212010c05181503180d020a120e0123070b060a14090a020d0f05040506091606111507080f100b0f160f030519090807062d05 60
    0x910940704450f115414100b428283e0b011aa0407002140c030a020400c401d009903401250106e000400b500140420490900313039550040e80d0141c61500c0c0307081e040c900880204951600204a403000300030b518059161110815079250b03001d000c105c942ca14000c20740c1e00c02d203801c00214018034449030700400c4070b4041c69255804800119240c00c2510000741d180c3c40d000c4151821078041b0140610320781000f2040140f036800081c111524907034240f105100e204850300c507200121200f0000050300303052605282e442c20b01c1c028024505688039500010288140c644e045003100d4813401d00030100c0c000350410908143c10491500c2c41c110784402004061a8014240c90040d02d041101411948402c026820a010700d4003a921640a08100344405c8000190040160240e4490a209401110369890302056480c000c240d000940c0415041032070030a80e199191005200d02380307101d103c3d181564441d12804035218035418090146500e12500304000b0b48250005040f13000098200c900342030180094 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 678670872 1250 678669622 678669653
    0x703020309011a06070605071101020706060501030b0603060120074208150409050f0c10091208070201030b190807050904051e10020c010902090a02070c0b0c1504 71
    0x2503080040c1140d03d080902e01041c0c0354000030301100c4c94541c0648422000d400c01402c0c002c00c002c90003001c6609010284058180c00e4400c3c140404c05500d0540010b046d41c0054a90701c0c843c9200704107100d020307a04000c4448020904084494910b5140003600d402c041140d4019684010070400803015000c89660f0085104d000b00380061183c0c144180099a0074040c00040d00440c28480210300001c00c40100f052480750f0050000c1b4692038103585003418140e034244000c005910a203102d400a245c00d03a21001018194641018858686136540c0c0614500e294003510a140c0040e0721401c1d6403081e0004040803002510762180032040c0b0700000340d088202c2c03080f0b28250040b000003050900c0c20301180f40c00b49030040010204074103151180d06000a0f01034003106588211550741c0d40c3c10981d40003030804c1046c030400000d0303100d02c94010700c60803a00c02005801c16030b1040041030f000610110f0381c1030a440000840a40314104135448614018409140c424841c80400c01c01003000108070140700c3c007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 678672122 1250 678670872 678670891
    0x6090c08120408160e0c2b0c02011d0a02090417041706130b04121814030601090e0d050d02090402041716030c17031b010c020f0705011d0409060507030203 68
    0x18206004c042c044039220a021740e400500c007071008a512441e04d00c002d040344003079014038802042542038100c8011206900c81d207408a4940b000b091156030281325640380c10300b01c000c0c003040480c014102d042e00c0d000d540c0002442004481d02140c18480b00354034220207001e1081314031740d845854840038102203650308a07001c26445424000703401c0180c0c0755144502e40e50311064455141e00d9541c4c844101c404208030200c10420f403032105010400511144a00604182c0c21021400708944103043c2060416008040365070304191018240481c001086140c40340c2903e4920349514228070f240e000780c0b007181c4115900c02c4c0082004200224504407015155445000f120340b418240e00d416400f800301c912001d402c02c5046201000860150540e103100700744110142e80c5030001403039801d584030b003550040303840c660341d1105500e56a94042008020030700c45a0010117800b407400700001c208025420314804140981c20b1751400d16200e0350130250005901c00e00a00461034041c20082c000d40044171721802 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 678673372 1250 678672122 678672133
    0x1501121a0316080f1f1e050412020106080321060102030c07090b100305060d02040e0c19061106240f0303030a090303110702090f2d100b030c0706090c08120408 70
    0x2400540000d2a040080d40c85c0c0644d0f0b00003925070200402456031501d07581d90084c03030b00c4481d4810511442014807403031083c003904030303000c0d02c821009013186c0c240c1c2c2040c0080d6104005400f0201910801a072420b0a81050368007150b80300c100403030440c040c031004c841e00c501c15102c012502e81e41a8111041070715090b9514000100811021001e80350291902d035000030540c401c01002d0b00700740c1c0041ca50000c00783d0031100528940030100b00081e045031585400322000310000e120079a446032164a9501c000e400070003960400000741000c0e0200d0240002040d401c02c1c40c1e02c0740d00c0d04e6448130001000e4008080d01d48925020340050080c10400c40708a00091a10303035100b007040321290a41c1c5070541c02070009001070f40c1d0324580721070500010381100d4000358044080d0000d0004402c002114000c03400e201c282a082940c0749526072843c541008103009810310400041420420960b1804c980142c1c010954980c0ca003020f004942480c2c10480c01800345024241002d07031010000c0046a141c03104448 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 678674622 1250 678673372 678673393
    0x21020102122b0c0e0111012007060606080c04120c120302030d0b01031b03021608210609040209130c0306110403031202070f03050706060b031305061501121a031608 72
    0x101250b420000850224080c81111090f81d403154030101c403180401b2000103801030003071042128514403081c002c440600001500c0f000c2081900581e8024486803c2c00541c904100800ca42c0c0341c001d902810160014007054001030000f4144003c00801105125240c0d401180c1002500c036800341940b401c225080800517011544203115800044950b0b20248100d029000c408a000c0d42c03000810300030b1a02c0006041d800700760313040000c090443c45c0c2c0320501c62041c003e294039507078240c0c003d02452145842108000158a400510980c040303404800c5510708052454000c01c102d0705034002070502c40c503212000010280c0403004005590003034071111602080c00840798241c1c40f5440004250305544140c410018dc0540b000c0c1402c0c0e071240341c5c081441703603c920f035580301c0f80c0045035803003d00464088003000f800428030a240d0000817001c40406c441c42c5560010780610380c05038510410698501c26800d440c1280f100c14002148000c09031101c0500b03000941c0d0024544c0d010f54181c5018079280301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 678675872 1250 678674622 678674707
    0x2a0501020f1203150402070c081c0512130f06050403020615092e0e070f0806040e06010b030a0e010e15011d04030c030302040b0a0809162102010212 65
    0x58800007a42c82d2240d156a40704090002451240620160015001d01c00400001d03c101c117040f004d030000340014100c1c0048410507180c034003601d0070041c0510804100380d4240e15401d5250603400b0b0b0726003640a140000f01c2c030301022040c0c100580681141e203020f050004042d070105000340a409015225041c43c1c44000c100010300c1002e454040880c00d52050f42e9513400f00c5c2c0005141d502c00e19201c10141d076039940450100704c0a0894000700014200900740116640091150f0b42002054038100108c003d082e8102c0d95540040c080c41607084408030018014075040d40207455045003600003448140c65181c1c0c459a122001181d040c042645100041440ca031b2150b10b502e1540e81d505400b00080d01e40e910243c507080c00e09a029810140c0811000c14100c43d810001c04940c0c840c0d40d200b00343c0d07180042032181800d0100200300ca0014184000700001d181e0085210384641000148100d440840d1006038a414041d0760b00c115000070120300c0100030409504204642e4014802060400c00440101c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 678677122 1250 678675872 678675883
    0x51e011502191a07081b090907030906150303031b03200c0319020f010e010c0c06050a0f0c1206140d0f0512030903090103141b03042a0501020f 63
    0xd44016480703100c1001c10b07100318521020038980552250080b03868906016200c44000320f076220080b8512006004070340d450f980320301100058452100d42801c500c00005800700c0c0c0e0140c41201015100c40130041441032680c815850f55510b4010702034007a540c2c1c68054090405102000c902020910802c0d1103d8001d000701540d0700116a8011079080c14005107040300e070041c001c5d43c0c0c9140b00a000441d1801680a01c209480b880c680040400e0129041180d007500d100c1203841920782d0500c010350491a40204020300c0241c0c0c45200418960b03941c0c3c8000b40103000d0044510088c0b42030100b8448100d40184011065a403080810b022190f10b41c07450383d03034698a080030b6540090300d0304109404070300301000318260300d442841500c081c6008010076000a40094501507800d07000040c40201a40e018441c8110105d2400520b915620b0409604d080f401c0c40010610715030000000020100708000410003400001c4070300401c140541c201c007803c88074009014582c050710603144915120400082c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 678678372 1250 678677122 678677159
    0x2b0203060d08070816111215010b1e21010828020f0a0803030a0f0e0c150d110d06141302220b0712080c040603021c051e01 54
    0x2020081ca410394400900e680003080541d60150248542c20310204501080e00f012801910300340902c1e4a041d0400c003415800c4400c41d41d2590154081032030818888449904485a1b8103181c5d4079a002045c04030384130310a4010440b0101c0e80010075440b0300c4000c0100d40b20034094018191096a240d030036450360340e64258403c95518142d03800003180115040701c614041840075142500880404008c40d0f142e4805401110aa800200402c00d040701c171449180744100b4101d5003801011400e00e240c03501c403d0b540b290603024a0014440c424480001c034103c0e505422482400c001c08160390701400440d402c03410742c0c080200d08003080060010325400040302d41704001810040b1180346120b07044025800000c805d880c0c1010320405142034620165172070000c046c40210300d59104801c3c50020820440380a201d0280580c800900000000704010354007901c03282e040c01681c3e01910240e030b1000700b402d03280780c1c0c48a50404c01000400d400d80860b66003d01404003804a442e6210a4030305c1050642e0701 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 678679622 1250 678678372 678678379
    0x300408060702120c19060b0d060f2712050c0706020619090302030d05040507120b15030f0d0305090106090606110f010c1d150c0d1e0906030209152b020306 68
    0xe60505c0c60341030340110b80108501c0390000080c21080d10b004074a110034802d800b0340d040e9076201d40c02e00f281505801a0654031b07204030350f5a8080203042c0410f8100800700707003002d00b00001c800c151004903405401141c3d140b03104282207640e1b450b52140000c0d95040208d9034511040108030400c19800014099002019459000b13141401c1012080100804c0001c4c02030b220351040510014100d404440d210f00079500400c8405a280780002003a00a00882007007140a40c0c0b02442203400c0c61004200f060280c030f03003442c0c08202d6813645075200d4054040394000000440c80c0c004006001b42e0040c16920150941c40d042d00c100a05d941000760888000300b60b14404200224000c546401c041c420b01c0105035001040c1040903122860302c1c0700f146e000b00750030b0501680301d429240d02c910342022141c03000c401125000104006030400080c10300c0a54400c4c0802e250300800c1d0624a0703aa000741a12118000e030b0302003a01e07544540705540702d4001c0c003005d402d00c080d140c1075400302008450007142e00c00e01c1f024 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 678680872 1250 678679622 678679633
    0x1211060a0e06070312020d0204030b0f0601090e10240815090a0f0905030406170f01152a0516050105070c0308130f14011d03300408060702120c 63
    0x2024440c242c1c0c40803a04a04010b04450f211602d41840d06c060612001100001170715541146044444800068090804030f05007804100c070f0307030381e2004d8800140d036803920301e01d9501e868150300b906010a00c0e8000c401c0000c102c1000842411910002400359101540d4000c1543c0312000c110007911002041c070740d002842c1e040003a03c00b130041d401000144882460001d200542c0741ca482d41035400c5504501c001030150610b00383d0801900340e1980d04140741c1740740c4800d20b52402d40c4142c2681d151400c400184800c45035084003070f500b500304c903408005c0c0d0700c242505c1001c5a0b180c05600d94030076601d40c8140c80440f800c0400c0c030354443c1c002da078011544030885499090454a82c1c414503003144c40e10800107044606c01092010602124800505211751140214004440054075015020b00e6150b140c2c241c90041018541d4002401702042003007840b010400019402c0951640190304084a0180400500001d90000000f5018401c0e18580d0076980d5414402105072414445c0020056165000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 678682122 1250 678680872 678680897
    0xb0703020318011d060a11060c0c2509092f13063c080307030e010c02011b020a0909080702030114010521010216080a0206060103110f180a1211060a 65
    0x40001b007100950303a05084000310300b1040c16524000049502180d02c9002041c65800c00008014405c80c1c040d5083c11b1010102407071518140b580c02c140b1582c1e01d015100d503800e005202c0705e9100e40c02800d00c082d8a014101d03016481d181c62030111060304900404202e40c204007110090321850013034408064481c100100c0a10700c4042c0d2801e203aa01c4100c3c0c020241c880d89218070742054403801894400081c5840b446141405000100c10966581c14803a086014100507a401440050201070f10401c3e43d01d07084032800880e6220103c0d400c0182c1061400741c0820034131580380c0182c880310784218001e001d84000201002a400820300c03c2c9134210034006125111001c5001c4447c0044186800042c05d10442000610803030710f40c0c0e07509584580d1b00007039489010b40d040c402554024800e08051000301c2100c4135005181c0f24502c880c4089d4400410940007580c40c1c40e10255100078020026480c183d1240c400f40d8405840f060704a80f01c4216051010003810480c0a0700c004001603114035101c040c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 678683372 1250 678682122 678682129
    0xa1401030509010e07030f06050c2b09060f150f0b030c0315131a030105101509050d0503270901090e10060e0603010b150304110a0b0703020318011d 65
    0x1000c2c102c44000c0d501d40049481c1c070101081140d0003540100745403008000c180c145201124006010030124031020030021815840307078102c2c0b036200629010b2680b152a00c140c3e0f004010010036800421290070031079980d092010540001503105000805260887e94a5440c84a600001d01c2081103941c020700010b4484107091001c0c5510020540e12807035030010703410000790052881c51143c1d00151f585c40a030401c441c80301c00c0c00001510305800800c51420f00b08001408420584110580241c07440700465505100c1c2c2500700c010f000c06040480c58082e51b141c0a40c60350403011030306501c4100c11181c40301544110040c40c034101c5d00a080481c06034200003001020b050703e01580a107600c03a010b0401102d800f1880b1744030080503894142d98050a18100305403e4403690300c810340c4249440b0070042e0340c5c01c410348226604190b02550081f80091110049100504943c1c8550305c0c0300c60104c0c2d820107158012004149a04400d200e100c4a080305600555202c404140c4200f10200284039412007400d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 678684622 1250 678683372 678683381
    0x5010311040504022b11040e3004081b0102071d040f0f06050403020f030708121f0803130608090319031b0c0212030705030a0e01031401120c050a140103 67
    0x5001034002d1641c0c0290404490f031a481080307281728600350780c02c0b4400901c030443c070028805581c126001e0123011000e60509940760309544810b140395000c01c0020302005030000c0f40c01c1e01203241100341a10343d43c1e68a4000c5d140c003091405c59011040072815015a0740c404200f88042d50940c11004450040c00d0201000307009000740212401c034074851841c0d000c0307012007603c2c6041600c0340340301040a10309842c00906103119504800b909600034444170b4001007218080d40d841598074042458150b50307521100000c044840b40c1241d11085070315011920070008001072562010f0f04240c505150341d105000c580442040701c1c101c015400900165244450410603c0f00000300713458040b0386940c3c29922188a000c40070303032070808903059455003400c500b050700e80b1a0381001544042c50410706591286600c910a45004c901000880086034039168040d0348458540300003014070030f06030f60711a000382c0401c049400007901d4903c014140059240342644455081e1035804550703006d40080e05005401a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 678685872 1250 678684622 678684631
    0x30b010207120b040c0f050d20062805070807081c020d0b040f091a0702070f090b0405100303020c1504080105070806010f030203010e06011407060e0309010f03050103110405 76
    0x1070040703003000280614641c800d003941e01d000308042c0c2100d0802d440d1440084800780e008036060340200d0b20800c00e940c1d912030b0a0051507004076840b01026940304460510f21004002d1a51024003c038600c08000c81c91002200c0001e00300c0e15107180711051400907615401010340003026950100525400544100b0242103c0b40c40130300c80042c400c02400d05413040c0d810050224030100e42d82c090028480c075043c0190304900c82491030801c0710b00b090781c0f1064540b044045001043c00d80e0040403402491007004050300800c0c02c280381c0008551281024000f070814000b03205d2040c0e040101007140313410700000c5001200d505400034445800d4140510401c4031401701070391502d040078040060be2060a014041c0b00340320f66070301e0b4511454040005040004040c000408040c8140300510100d85030a1a144c4c10100c08d00f085602d070320002c1d00c0d103403140c4200c0c40300806d11801c1c0324542490703000c0040034007a041e2090303d07250700c00b484181c0110111042484054203650504500716044d040590216401c0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 678687122 1250 678685872 678685877
    0x1b0603160509090c0a1706240f0309061602060601020604030e01031e0522080d0504021309050a0506091204170a1407092d1a0406030c030b070306080d030b01 69
    0x1046120400a0b600e800d003100c403480078004c0064404260360b4000c10100c0485408500e502c1981085004580101d19581c500b240e1100800102c3c0100310104080d98001c1100a4400395a860820540c0c0e44900040c2d07283c0480c000ca00c41154880c60003c2074842c841d0006134002c0220366510b8408403520120f014800703061569440c61070882c01d10b840b08480892405610201e51750501d504a030310900413441190301d61081e601883c0002074010301c102c80d00101503280225050304c460001403118a000e5101d400c400b85445490004c000002c652301400d14010429150517958254013280c40703000714184056541403c01051180c0d28005000c038043c840c1d00f408948454625660f42c05000080d44142c00c00ea034403d5004024101050184030130909000039255084842111082c40601004d51a54040b54442c0907407032681024540380c0200300340080051100982c0d030708000f148075172140400c0d648101d500002a02060003801a8022a503a600c000c18289030141c10071001061282c108031b04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 678688372 1250 678687122 678687127
    0x7090f140132060c03120a090206070b040516030b0402100819110706140a06090b0603160e0402030c0c010b0d050606120709020d06090b0f1e0a0f14031b06031605 71
    0x1100c0d00c0303d1004e0b2804074a100b004655a0008115a141600c001024000501d0812856000603250282550003c680c002025003050300c0d42d181060030180d030380e880400fa023018104000148811030201a01583c020399031000c0641102c082295584d40884400010380f448002d407600058007984615209007060b0340190915190b9a1030600f40c03040e5200140302140340e0741c10310100c42c407180f141c0f9009003d202410099220072002244640c040140b02c0b8046260401d601d086960041d007004118107001041107640b89480200c40401c1d8214440032100c944c6820002c40b1300b41800031180d0119a04100144020364668042101c1c65080c020781c1d40d158094400005a001c0d030300d00160210b8000342c1001702d5110b043c1880c003c00c481e14103141c60304c24001c00071281200e48411105208004825801440b02c040e20000702d8000512940a1081c0b14100d440000300e503464641184041507048043e01c001c24220452036952058110b4143d500040c100041010300c8030051501e41030540070f04101e0f0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 678689622 1250 678688372 678688469
    0x604081b10020c07080706020c240d0603050102031909020a141201020c0601031119090c02240a11271807020f0d0908030409090f0507090f1401 63
    0x40030398200f0001c4100d680c1c40720a041c4460354052103c04041c044e00d1005040600e00b800002e01c81808150042180d0031002200700c0c00c020040e4200d84c124800b11100740f2440355689000c80c000c2d401251030240c12482041140480c1841d4091a140b99400070304400041c0d04007451880304104911259a00c0b5501c04602e5006e140300303001411416074968083c013555171450610001200b05015003a100b200e90200c00c10a4141800003501505e0120348005001c40f44404181c1c40c00c0b141c0802000350a40c0c0d00128520409803001091050511200038801036032040b034100e03924028606050040c40c040d414201488658040718000c07001c3c001c11481d540d07000d000410341c0d452000e0b201c01005801c40034203000103140800c07141240307140034602294a40c0ca88440d5940b070340254080e1400030351710f4000c18801d2121008010f420f164100051b26049940c81c4240b034010414068001c01d154140340529440395000c01403207040f034111105900c0c003400500c01c8010800c03016103e900c5511040b11400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 678690872 1250 678689622 678689653
    0x80726030417060405011b0c0605180a0b09010f0c02030a0e061303150509031327020a0825081503011b0c02032b0c0507151706030604081b 61
    0x10100000802c014001508140c10100c4c00c3d44d0a00d45071010040b50151060100e50b13100000a85040d08007000040c07035281d044803161582100890321019201d0842031906210740030308481d02800c2d400000700046138040800038252806400b50801581060000500241c0622404140d032040100207070318040c1425103034125000c0641043d01c4c001c0c000c01c0c000100c000c46100f03694200030700100841c20407007001c04091002500340207001d100001e4000b4003100312400581c0700c2450201d91400d64a60803001c00c02422460121031032560381410340c00d190040c00316a041218454219940d440150303640000443c4d08034407661455401d590788104540a16402d40c02c82c0300c2c4041542d07542084000d150042518180b00e0404100112101584820000b0300340d14420700c0a010324184018000344505049003000020380c04100385440c03106104000e9540452082c040c2d1040c03450b610416280c15062550301c550465004100c40406c015503100e40e29401344c0d41c400354400008503640c2c01d10400c0c1d803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 678692122 1250 678690872 678690899
    0x7020a1704050303070818010c1203020705030c01051806070914090402010c02042c010513110a0806010f260a15060302040f0504050f030f092b1b0807260304 69
    0x1a1451307900803807d10402c100480c2642940078003468882400395150b10740c02c0d5142c039076030900d00030b160b8000303640010030405109483d003203803181d0003c122615080c101c3e408480300a44500b000790054400091000f801510b00800791800042c00c0050f400e1881e05200b42020f016005034184401d0500c44001645c0340e008082d80f00071080007440c122020180a80c130565001801603405904003820040f002115480003105aa00485076110314041840820040310302a04015606d0081070004544a09032201c00b00c21258400c40c400c4c6000707144d00d0707041c180001512107003160350890490140440c132449404180000c501c000003416a503070313500040071103044801c40d103d906e031a2030400c424404103200341503e030100d000180d0302d407103494084c401a521a0564462140480c0c400e045036690581c8000c462b200313410411000c2002890030800014120000200c18000c510740c00403610080224010048a4108110070000440140510542450456041d003217200a02000622000b00c0341d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 678693372 1250 678692122 678692137
    0x3180d0c0306052707050310020904091403091309031e030f0c0819050705030121080a17060109080d200115080d030c0834020c011707020a1704050303 66
    0xb41305140303020402114034002058404a1700000010841a10007081401e014120440e0050f5149007080c0010024140d118006e4480040b0b01d80443d2501800001032154290480b0792400e0356100b812040300f9500350600040000726100000e60520010f4000701d1407401441c1804200308000c02031450464500600160020b10780c481440254031413588450074055030204140000e150100c8094094031041c89083c6890083c80c1e10078402c14021a041c4582039480180f0940d01c1c451b401e0010902e0300d6800e0b10030305050000021815660146544508483e00d06000d04032148038403909940c0d52070b21002e0601031920703004444201003808c0c8a41010841d4611010142c00d04080926150601000c00f103010705207880842548541c00040c640c1c0c2c041d44c071a40454401410700d103152426411007014a40c901441c0c0d580300c6d0090f0700440c1c826155a800c1c4e07290034014009108449603004180d45020150b003050702c0342404141596604101c031140d1219081c80e06a450011900d554420380 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 678694622 1250 678693372 678693391
    0x1030b1003091104020301210f1208015010050406080703050106020c120c040603030e100905090c09010c1401050a0f051b0a12061503060803180d0c030605 68
    0x410340c2e04000000301d40843d28603044d2811400c41d8100040441c400d030100f00c00c3c11a034140f44010a0800240e66001002035238082848103206505404c00703004080207000d9045115008040c103009005041c6000302c0035004138481c484044070058840c2a080311040000c211042038079a140c0031070b202d580e00000020180c1c0e80d216070f2146001402080c1280141002003010b00340f0b4010000d150380018045100070003100c092002c02c81380e81c003003403508511403507080d007090404600206068102000c1c42d201031064404110360131529904850035100c0b8080e05620441c0325020031003151100d005000c6d00501030500d01000005900da01813004080e400300101c0740c0d15171040107003a01c802e000d903495280700d100052000e41080701e01003500500f100c40301c01034241e0208981203254800c03842640080c0707001c0c1e0701f0000c2d2506c4450803000c0d11480c1c104040401d091120001e055003000089400030908244056a0a0030300e50801c010300401880c01e07603180c4d4081c40003101281c290312030319000b041d036107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 678695872 1250 678694622 678694631
    0xe0a18030f141908090a1a06300c040c0203250b01180605010c12030515040f1a03120415140a050a03050f0c0406080603070b12100b1306030b01030b1003 67
    0x840300420113400103242d01040d820034480080065001d00b12010803110451012400c2e954507404501e00f0910540340041c03200401600c075a003c0c5c1c0d02001c42882c500c201007a034015015080c01c2c0025501c030040759200590080000d504c4070034065500d045c0d1a10300f0b095404010f41262110301c80b4000a070030842d444074811294401001c21482410024102030030180c81d8400a41c030341622800a07c0000802d1544640015a161a42d2295041c0c2c10238000d10030010300b038080d8804030050007840c00d85650640101c18184041c540042e000c117041c0100301d021450300303040c80c04403058041440801d606000b074a48414900e50f0400d070203000312508594419071a400e0003c0000e065800207440d00303c02910360380a0115190f02c0d40c1c2141c040c1d601700d090080742612040082480c3c591142d0081100c50f0000c14155840021030718405d020740c0007046052069511048086198403507402e841c11440701e041e004004241c000d402208081341d05041c0041c019404602056000130200030341c10009948 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 678697122 1250 678695872 678695917
    0x2903030408070e1801140f060a210b1005060f07051501092c030a0509031f15080601060507030c0501090b0a020d1d06060405040813060203040e0a18030f14 68
    0x304e140009020000f8420034400090011000030085c020f2140b0300703a8140050800d40340d03510b1030801003013176050040c00503041b080403484491000d5811641912a44003007a004000300d03039010152140144402d262100d004403168035a0b001c10390880c1c0074000c040c0e0626600d103000180c01e0091000c0200031a40c021103c94591910400541d0101d00a4404805c85000704000040d1a240440e40c03c00507910076150300000d01d802201c509040b1040303040e000ca0305140b0160340044488002c100e501500e500e44480c038841d1a00340034001c80740042c9007400400040780c800c3c440c106034203005800005da000e6441d00c40c1032103802c003141c3d21105260002440350900700140b050300c59000c3c4404a102c4c680040000550300c40f04041d1600c2e00c03a60f110400304041c001306008980c11018070440c612007666071303400065160340192040c05140242c442c0040e94142c024080c4198001912a040c0b4801031295010380b07110560800040802c03205034686000801c185004140c0c400c104411004000c12 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 678698372 1250 678697122 678697141
    0x70302040c0309050a140c212b0503250906020d2d1704060906140402060714010b060703050304050d0c15020a0302090612060901092903030408070e 65
    0x106000e40702018580004400071440100b1500c03a165400302420001d40f41c100025403600146000e030a6101400c3e8280b40c0034603c0c0e0550400c50040c00700f06454030844a00c8080c4031110700c201844445c00c00314054060580c3c4120001d582c0b02050210010807070945403400900c13036007801e00c84404180070034401c0c410f003501082020480d600034075203410342c19685580c2e0414444091810b0fa4899424403000c90100d0185a4000030490130a03440c210500e440e042c41d4014040309002500e1309460440c000c030345040e144007014842c42c0c014000c50b18006465446503012035160b5450b19003550384514100c02507603003070b00600300c05000342d803916100d041038209075003090f184001c10f105001206100000180b4604038049010485450058a40460300b0b8140e02910800380403c0d800100000e001c05660301481a0340d000369800c1d5002c20903680c07245456070272120008010030805101004c0b5189494002100b20102a00038054904107913032841002d15095039900240c40355800441081000704 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 678699622 1250 678698372 678698381
    0x303080f0109020f0405130f11030a0e06070507110409050304060f14040303021207080d02190807021b1c050a0b010515040b0d0f1d03041a180111100e07030204 70
    0x10b0075104520f0411112000b00700c07480b07180f04050103141c80b000001a5841564021041805403030400d02500c144440c1d01c0960768000c4032041d408030311308400c21558102c0042c601e4403e0082d03490303a500c1e198040c2c5498080500320042d0a40c8030b41c50b010902e000400500141c0010000c5840c1c54885800b8844007800d0707506c50110f0705461f030000303001c1000070079800140100c1180f030307444e800340d80d46840341003a0103c2c1c0300d141060010700340006054112801040c80c0030200e481c50350b4030f0a0007900d030740e5403c07a210f42c00c0d000d2a9851500c0e2807240d911b9854440e4100207449081e0a090b4015142a520f031030420f21405019104052040c004100d28106030a22407241d02002020f03501d8541002da4005040c020320a462181c27a80d555900b183c013480540c01017003410281c081c03036030b0300a40c0e42900e00c2e80ca40c0a40208c0420340b006440084c4042c0c40f2605460401900c10a11fa074002c1114004480d001c175010b00400c0c1c24400c2c02009000521a4490800175603c5040509900b80c1140148000d40d07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 678700872 1250 678699622 678699629
    0x30708010908030105210118141501051905091e0c040b0301210807050a060c03060b03040803071403070f0912080a0806040e1506090112051207020a0306060303080f01 73
    0xd9050a08440009401ea0201d80c1540c804031014407000107410707401000034104000c01e51244d8a4420300c401102445420490074521407054603042180c3d8503845500d0f46079620901c1d104405242c0140b01a02e000302850549602d001c0d1001c0700e4aa5400c00600030b43c4081d00d0840351510787c0c22301b0b42100e070348121180d640b0a10303040070645494609a800c0f0080c0c4014406c2052145040005c84c00c40d406213002e0b0301c1c0b00c0e034101c00c1013600c2e40170360b080141e19a181d2060072202c240c0361040c00521036009000c0d81003101d0701000428215503607520380014641c4010514401c00a8a010b03890300c07400194003950003000b19680d600140c4648183c0074102c420142c0000012118a010200005c1c2c3c09000b2140000c92528058003c3d440e2035011801038412a0340281c010301840c01c071091292098000c1900c101e0040f45c5d07929041c1d9075201d4042c0401c40700ca9000e0b24642050b11102c0d09081c01e18018485603101904041001da81c0e45c40f10800c543e840d400440000d900881400030710301c03e412110380503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 678702122 1250 678700872 678700889
    0x130c021f051008010e06040303151d16080105060a140d06030f1a0f070f110601081b06070507030b070c020405010f030254101707030308010504021605010903020102090307 75
    0x11700d0403291005a444a0044c40101090780720a03400c06400c040042e00c10003850007035041451400c4000440c208141c0c1280c1ca1034010800701c8898041a200b800a10b04031000504010f14080c031405086544100d03000109101c0481040412000001c0d48103500085000d050b248502004a15000008101c0e8080c000e003030f4000e8001f0f001040c030030800b016400003120b00304400a035103140b20548400e024182400d0300c80c0184000015114804a941070350701030600d1a410a0400000c00c2003030500a0301ca01070402d6120b09410700c0080c0140040740d80211403800c03c0494562141d00103400d0b1202600300c10150100c0c410b0800c11030070f0203901e04241c8050581d0b9880340f0055034641048490000d04101070b01e420000c0815401414180c6801448214070540c011f2480e00d507960003601227144c031a07662401001480c0802e0300c0808283d00040e82d0785aa14840181d18220412001e900480d22010190030402989000550300b44501ea8840d446600003588840c052010507041541a901c40d104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 678703372 1250 678702122 678702131
    0x13030918021c0b130b0409151d0a0804061107080703061401060e030c10120204090e0d02070e0708070e12150604060b1603021515090c09130c021f05100801 68
    0x507213540d03030160820b00c400310042c0001c0b040308200006015100120024100c01c0f4103804d80380c42c202042d08407019000c032002c412a0b1825821a007547d541210b5807000d000c8410600051040a1040003c030401c00584000c451556483e0b03015035082c607409600032039010784e403044241c01281138001158014440c0381840900da0b440d00c1d001c2070701c9404c42001e45103c4e007880d404c1c00000c14000c08981c001000003400c01c6458a80762a80031008008111440c891441002c0161800c5480002c85405441c50155401c880d6240d9020030f030740d031204c040c00000500c0341700740043c00e0310344410004082c0c20b0100402001c0c0c603000300002c80800c01c0003424640c042c0d81403500c24001903580004481020040e02175203040c5a0240c00e0407828003c210b25090031080c01041071000c0801544401702c22200202d40000441c1c4840c0c0f410318251081103245900040c4229090803c848103920503411035146005039200a00040c081850300105c0c1d50380844000e941e40c003030060040b4100314403400380080c00e00800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 678704622 1250 678703372 678703391
    0xc0e09060f2407050106050f030307020109170a20012c2701030506040605061c080903070b0d020c010f1802121c0309021801060813030918021c 63
    0x5168841403100c850181d48070303200c11401c0d2950701c120801414402d818003519001c2514040c0c1c040c0c1030b1071282034403403050784a00409a14010081760306140c2e05071a160845460141d00142c4c0c040481e159030800c4c0209a1848040f62182c03428511001018000c40780072032070640013614200d034070144900c0201a01415030322002c030b14103204085106c119035050241e50341d901000c03041100307081e020b241086020000020010300040c0705014621803581401180d4410092151010302d41c104d610400641e09a8080496503180041581c0580502a140f1894441c030440e0016030000c049010302503800942006102c0c030a116038ac0c3d1451218109010380420440280f0074074144100181c450821000d904101d400f003040302c1c510f0224014651a508100d40202070014585180180d003d0402c881d60694540c41070904079040e10216201c7d45065100d9528558030248174440031014400a4103000c10890705540e160568400d5a0b20003503070360041c00400000b10030711302c807035802c2c0c0720300300900b41e03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 678705872 1250 678704622 678704629
    0x7080d0c11061503030c01021306090909050304050d0311061f0e09030414010c06050a090308181b0118080703031e0206130206041d151509120f0d030c0e0906 69
    0x100c2d0880f1502110816100d00e02c0000303030075442240407034001580700080341c8203400059141e210442d04191a04500c1a5583c00001d003a41d14514000340f2940040209000500e4644142c502140c0a0700d4000302401460111929040d42500d04d14881c0d20003c060b111100c5584a010b40501407000400720b04e41010107943e6600d00880c040c841c40c00500040b41c4503030742d200e18102c0707860036040340c0140860b04040464100030a0100e02c10740c00148000001030603112202d907030051031800c45009000a1140d503d400540001001d2014104910041d1036000c00030825840c2c2c010300042c0b0003400c1d00341e185140207454001440c040003940d625034003402c0c0da140d4000c11600c1c0d02c10080c0301c58480140542c400940d051003140c203c0305500c60752450509028120620091042c800602018000200700c010042e892003181c03040f040300202000381e03034500c0c2040210a070601810900329442c007400301480c641803400242c26100060f1b40e44200040c0a079102d4002070f070782c1c2402c0d1480c4505041c880c010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 678707122 1250 678705872 678705883
    0x240503060a110409050402030309060f0c01060b072604090603061e0b33030c0d0b0f030a02042703120605010801140405070908010e030d0608191506050607080d0c11 72
    0x10aa01c2517030700e40001d0306644040c4100c0d406110000d09040d550520f08a0151403074001174802c01103503107803180101c0c41100342401c907014560400c0d0800c4400003401c46100c1c550042180488620b80107010004940c0418060080910b2207a0804200c2c400c00d0716000c100501d00400b100243c0d401c1c020080d1280d26001d550400f0b2185c1710340400c10800000c0380c402d18110844080c0b50760305a0000411074000b10340d4020b4442c2a180701d80a01000c050030082001001c21072402562641052400800600d01640051a51107120500c07400c02a40c402c00141c50f403103580c5087d0046101c40444201d2a80544180e03030140c10242010b1080d07504284001c05290388028080780620b80c1d80c80800d01540c010340080000703040540c0244a2000301c008101d0b201e030005a00c03170894034280300f80450340000116114a28900007112100200300035152850f14842d000d036080c0340560b54550200300e98462200414441c3d0151514030b13070f10000154660112100c51030b401c000c10410203160086000003265 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 678708372 1250 678707122 678707129
    0xa0302180903090d0c17070f0603180b07050304020108011a03010e0705072a08120f1312060204031103010207030807120635030415030f240503060a1104 67
    0x1403004980d511094150b1a51080b00c4a940d07001050b07410780c0080011219420003503600003a000481d07241c11000d183c2e510111400b41000b000c00c503460510a66210354010698006c145815988289041c5c80c1d07881c00c01002d03540350f0001000041000159600a5042801030031002100304100c504a0708504aa00060185155543e09080800d400074070030300654502980142c0c0800350040d1901034150032544214a003843c070204000c00160600c1c0104110340010103070409546002540030030080154071040f40f405502001000100e140403403501040c0000d441000016900c50030347c1800c40c0c0007085541e4143c40390b80100034000001354002c0116800905078240180840c040a281801a240d50742082250321300030f0404510b1071810100c601d8115020600703a040ca0700241c02d6a50700c1344114012024965100e95030400050300c0303a884810605c5901c903001406002d1114004070915400c1004c0c810743d1a84c50307081c400c0d842c007805090f402c00d5646604001203040c502444100740560b10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 678709622 1250 678708372 678708409
    0xe130506190605130c030b010201020a08011a07080301060f140405010509220212060a062a050102160807140607120e0309030f2b050301091815060501030b0a0302 71
    0x90340c070740e0550403900800b0151a0081582130020b29020140f00185015242400000c1c1409103810f0f955006100f00c444090f5159200041a03080401c40e0100380302030382c8001200700c02000f81d0000314448001031340c046c00791a80d4a0101c0a07a00c28010500e01e95a0100000e181080004010f942e0700001150b00c1c0103400d48005d0402d80444284c0180c0f4028250056107240c00001c0c50500041103e00c1c131841040d04580f80041300351154001c40d052401390581c403124220281d50700c0c5807510311040c0300104522550015103810340419901402e142c0c150000ca4602c1c0000c02c4000421258402d5424070702c80c1900200168030b402c042c0180b8103020305000709000c031343c0ca036100290890300f40101c0c2d10f00e0740c000d011034a07000191550b003a030381e8540b1041d400041c025002c511000003549107020840361956a40d940c156400c108000000f446188990620b68107038441090000d0341410300800c0d0300e0247d65002420303138a08000501921620100d4a20544041805200580d0b64044400c0840b2051 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 678710872 1250 678709622 678709651
    0xb1015050409050a150f030c080f060c0c010608120408010f0527030c01050c04080d0509031b041506050a0215100902030c0f0d020703030b03030702090f090a0b100e130506 75
    0x104c01d910010705885d02120754800c016040440c100300742d4451030046900c00c6100261496450a8060310340f080b03003c030601c00e504448049040511110040c00c100c10001d40001913165a0314681c601d4480e0f01320750218008400301302081110300c20701c100049100301c3d503801c0c00146070010560400200c29004440340d104441c100c54070300d50301001a10060290303c0020041170070280401001e40d0054441c2c01c000307102c0c02d00020380c8988941e0030780d281c208020b0010000420740d5014500184403029026400c6035503066408800d0075000c4425004201c02e0712156500c621741c0300300a040c00c0a0881698001040d0b030107018448d0741c0030020340c1c100e840407440180c0340c0c1c840811f805400e03c2501000074284001160111074a03070143d00400c0501e00ca6101082001003680616880e0300501c14081c1d8001204400520420001885c080d80140ad090a860301d000041d81d4403210481c0c00c0d28036507140c4088560500c0900b40410066411a6054140c25640044c035a03503141e403110700501c522602d070841c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 678712122 1250 678710872 678710881
    0x1208090109050601090614060f040b1810030e1903020a0b07170405030d052409090c031504050d020f0703120203160b1e130326040b101505040905 64
    0x2944440d081c0342d4030a043e5401c3e965100d640e000603009030300035048a00609403500d651482c0c00001c40b007141c00d004010900b030618040f1020040d421084160502035031005655850b80e890100c90900492a900c1c009042541086101d2405002c40c000302c0080c40e01c0d44210700441e0b000604501d01a074407000b1072219950b11502111307510151510062911216000d101c10420301001030840344070382d5070741041b040d5210510310400074400500304083c0032200c1d40200003810105000c90b8041c030400c0860f60249680c80200e4030f021004c0680d0465240404148410094140200c80100c401031006014080c442d221043d2100a2440000d1020842d805001c103070354028429650400c001848103450807270b0506102a04401c101d0700000d12015518002c1c5070542c0205e000713400b0304605a29401004c10555041d00c0792581c1e200c03c03000d540605a0b084100142404809200b44d20610010029090a17500e060b5031001d0f07a000001e40c000b0440b500b80415074008180d408503640381c036001c1426101e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 678713372 1250 678712122 678712141
    0xc120b040c02030f03040f06051006020105090105063303240d0b060d0309030c0e1501030510060f0903060e0a0209010614030f040807020307170c04020903070603050403050c1f0506030a1208 83
    0x400c08002c02060525080140e00e2b00504201e030129150341c1c00030300c03840e5074030160315003221070844915a00c20f801d40346454105200c120f11075000c07500c03240025140041c1c03150110321b6400864062a50b01400c03104031411801030419401882410303540151101015a6141305030300005114500075080b1901c0d1000b03041c400e1100200961300042c1c031b012a20b40b12580c040000400f220103041e040030b01c512400c000d500c248180c1d4401c00c6540d0038250340c0c0707040441c110740d070910449400040240d0040048085040d0784a580b00b5100408010001c8960902c1400403484059004400780070041000e0880c001c00e00e0212548800c3c03100c0070aa15543d146005101c5015058002c2e400d403007400004242c02c4001100b60044010200840380a042150104803c1c3c2c030510a8254042e00410410445603009400550b00588a07040075402d2102104400c0c0c0352000000b05144002d200c103ca20361408028811142c01c07071070030340c09825080c080f61603000d5410075410b030000c10030941000240e034040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 678714622 1250 678713372 678713393
    0xd170a150e04030327050c0103020d02040902040b0702090106020601140402030709150822020307230d030e0a17030307111606031409060f0a0207150c120b040c02030f0304 75
    0x801c01d2040514106400c004000f4803498201d041c101d16012641c07040341c424041600885907001c0001c0120010700001140690058224103528980900002c148075080307002800160402d1340f1290748a5009004009072120b040e441541903401c0381c0011b01075030518038007019127040306441c056a04d4454101c11140203855610416007014511040747c2c80d07aa0000455024000c0041042448500380c54682100c00d401c0300003c1d4554004101001f038007104070341001d0383d204480343d01c0b001c950078100030640078100440114000741490364003045a00d0070044603409012881140280001c00864895407031102412003020b02100100020054404000c8020500001074107584856038070500a0302614000100004c000b15138400200c9012000415078460108940c1e2901207449207030740f175070007540500400e449403001102c514441e03920078002c00314194101d690b0441e81c0a00c811604c1e044566062030b2600c40c509055104041503800400c1d6026055090b0142d5540d0301c0700e181012980 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 678715872 1250 678714622 678714629
    0x11090a06111f0902090f0601050a2d080106020105220b04060f1112010806131403090409150f090201050921010e0109030f0908120f0c07170d170a15 65
    0x1000c02220b0841020015004443c02e140f003984d40440c0707a01d94401c000306c68581220000d0020b1418051951218071502c0c0c200704000d01c035103ea410180e041c2401609010448010001040804004116141d4248070b92030b84501c100000c103070045001050100d00804026020340a015440041000d00c6810744c8036041c60400500c0070000d0080440300142d10382c10041f0310301d02c050a19800003131044404558188501000300c0034100003078455a82800d0356601032201d010f14401848102141d4942e48120f00c609400340108404201d04c5880c408241c3d040800c1390f0420b28204104040180d810100f0b0307644a1070115010a021146a8000c03820003111040075075031582814480b408964046d800340d298a4020390700d040c0d00c1c5020400660300c5094a200e0302030250b2048542c039902603a03500140401c0300401d00307098600303482c556000b0720700302e0035400c03517040c104075403c0e0ba0076014010455541c01c2c18141c10700d074061289800e45521010001020441080d03202d2801c44200c020f05240c0e60043c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 678717122 1250 678715872 678715903
    0x51611030616090906031707080c011404060b1f030e0c03070b0a0905060c1b041121280b01020a0506040c1d06131d0a03021011090a0611 60
    0xd614001c114a880c0320000003507000415204400803e00e04c5060186100b40c0b40c02090b031950840c421a1a410280d01910003900c2180c014030070100d0080c1c007070288602055500030240c1c404c0c02c1c582800804c6650300300c2441c3c400d204018200100091a038281c0d40300720840d080c001340d6141581507607418231001040072540341c000e550b0003040440c103000c09015512060368445040b261210700740300891040d2500310b917207030340405019400e101400390150b80108000e4404500300d030003074800c01c4494100c034205501d0031329850301258040340140c0d011544084480e20601c100018448250001c410100300848203985940c0c525500364002c1001800721a4440d0456140341303030034104650452a00c0c012104141001011520300c0200c0000d02801454020480141208180404001880407a0350144c035080a07045142044809001e8810158041d8024109402045041104840c00b44914a00120741408030300b44076102c4030b68450990f006406c0c1300b1901183d12841b1481c1c00401c4030305258 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 678718372 1250 678717122 678717133
    0x3150f011b08030a11040f172a09090d0c031b080301032f0105390a0203060f150d03050d0f1b020a121b021f0207060305060105161103 59
    0x100000c0380001c5104a051540810220748109000300d07181c840e5100306585485041d40500594070345e0848005180801e03400c80d01600500700021155914850000c11271039004d03904860785040c05084541d10001400184c09040444200a40080e40c001c001504000c6041411000c0c001e2910b80707944960b80000040b0b40701c0d030b524542603d4002c40d008030f24210100315920303020154104500c440e0b81900503103038681801c0f8a02c0680c5100c10344840b82101941401045904500e8403c0b4500710100a10b4050402c00c035040c01032500d407100243c28a03034070203c0d600c200480c6100c01e5054000c00e00d822620074002002c603003806ca401b4080c40ca01d2142e600d141114441d1300b4038950380000e05054803089285030f40340e440d9005984403007605102038143d50140044103041841023100a600e09445550000c1600715030300030a05100040c4011021002c68402203400f00d6010405a0010451850705001c04d1428a00080c9140140000c01b1604400301117260f0800070012182c450f030074405401c44a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 678719622 1250 678718372 678718427
    0x30206031503070e090a1403160302070918020f041805101d1b0103021e070507061701030f0f020f0910030c0807050a05100c240605040203150f01 64
    0x56019803907014180c881d1051580000320b1004070000548580107010281101d90325a448012405042000c074220354001080400308011603104448034041c0254010310340c46050100c00c100f142c1c802d20010450004850900e001a030f9851a1000030090680f40400c41842061180b03240c100b040d40000d0440c002c4000000105120364881c810b803031001d0b041032101c03a42e407401242d1103143c00d110705e4040c85181c6040d01201c7d4080d400402c1c2c0102d10741941d030440b884c0c0034115003003600003141c129076640000c1d8041210950000d5054071000d0b0b84072108045524607500e841d801240410001c2407100c60040120a40da5500482c01d88807101800c640700c00e01d01903040b030b194034110b07003c102c5251054820214012100080f4801610400303801d8604040c10700007004402916075103150300f04041c8942000c002280905031618010103a1102e17115511031103203100a0301c1c1d0a8101c940614030600c200400140007403100c02032018291010f40d0b4006103000100c902c5686403e80b0003041c0072009601 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 678720872 1250 678719622 678719641
    0x10030809132a1209020d02040b1f020102031008030909130f140a02040509190f080c010e0a031e0503071d0a120309090b030a03080c0d23060a1a1303020603 68
    0x4402c120055034032801d41401c4140b012044650082c00070f5008030b01000c0c0280182440d80c0030220700030009181000040f4946403440c0f904000d0b01c0d4140040c0d40200900090380d10300008540a40615000340d820602108041540028003c2103003101d0b044008400040c050701c11102004241c00c0030700c14204035a4003c000da65541b03c081300320f00071880c0000040081102040740007403103051158030a003045607610b65060250f044007054884c99001c2042d500d04080034410344212081d2400035020321203240c1805441506410a516003807031018480c01035059001741269440384150611805280c00500e01c0c0258a05450400303402c206072280200b04c001403060007440c10381c465070710381c0e01c880c0c1c991245105a40c1c2c0441c403260158029415480081d0240c00d586a00034403c81840c1d003010b00c00c0303605034141c902e003404254034039000301c0317405031188016000f441e403003001554086440340c07820342030405815010207818440c000200c1c02216455450303130190000d5400802c000e4403410000e030b00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 678722122 1250 678720872 678720941
    0x307030204181b09030c060324090e060f16031e050a0522050c01110f0604030e121506040f0e060a020408070608070807050a1b14061003080913 63
    0x100d00443c03e1103022a244600c00d04d442400c1d02ea11004580480345413480c00d8000c1e02c80c8540013201c02209104031084502800e007403100401d000000800c40782801101b003818913101900051140a0580402c00c8003800b01003c110040b007140750005440740e0745100e010010180407018a50076040c0418130040d048150080d82c025030400005280f000408000c80e00d61034010300000f005500401003e500c81e40c021301e0540da90203a0241600d25400070f14840c00e0602c0e004840840c00710352542c444c1041c81c20302101d98001c01210100902030711182912015402d000113003558803d90300c42d0722000d01c5140540120a042c0300d610100c900d141030007103110010790441d0003a0b040c140705560300052003a10610f2001d01640151b15540d4607074554010813200e940c0718001c1ca20a005400000001100030440c24908507402950180d405085456800b8103088000d0804c4011010500044c00030980080444112030b4088401030994031001002c8000341c2458002a0640860300344400c0050140281 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 678723372 1250 678722122 678722141
    0xc0f02090f0a0c0e0a0510030b0a0306091b060221040803040602010501090c022a030a1502090a05091618090507090305011113030b060409080c0a0204060e0f0c030703020418 76
    0x40501c58600903030001c070384c503401414405a00000d0f10710200283d00b0003440c4030328091240c0c070b0301241c20b140e00800b090103810154411605030303954081403000c0c800041250f21012034162941440c0a1412000030740d44d1034510b81c000c407040f0000d6060381c2404045000c40e0000c141c9c181c16a600e556650354068000c0c0824841c0440d0b550600c58098451032000c04c4d000a81d2032042451400140c468400c4044c403284056032680521484150501180c0d802e90381da224141c10440c0565580c11030700902682c0c5d80d2756442640589104810301c0305407811300028031241c0703203640f600f00d03855076134504410300b94052a407110300721a02d004107115a20390f00040080a590041000b801410341c0650320504502c55101d0405084500841c280009054803114a82105000b0800b042c45415038817006500e901c01c500520742c540c01700e28103500310b003003d000303000040100034907061a078030700314242c9100203000130099401440000001030100c3e0190341920042c00030800300701c00d04034290b03040100a020b02c14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 678724622 1250 678723372 678723391
    0x2010b01080c04030b072034060504381b0303060f0d03021c0518010804050a020913080f0304031106090a080c030913021908040f02010c0f02090f 64
    0xc0000c1c4800b1428030440c1d0440e136104141d602c040c0e94004c0b04462000b0100716513444035544007480d02941c20b04006285607440722955626110920001c4c0d80010030340c0a0480b00c4031120300e80f081100381d402c602900d0031190840c007a5036001107840c403400d83c0b150561485030400042c50b55001c45108082000c0e000101d07020001100d01d800e17512a190b581c0c001150903980c00240c1c07030305040881c100180d54901c1944a03004940c84409104280e582ca07070001c0800e940011004603821001c11000b042c14520070001b030030078541c40d04140c0c681035103a1540c2d10b03000c0d01a060740d00c04039503d031080192035002950010400343e1908010390380341c44642c0c0244d4003075000404200042d02c04407000704016019408074030003001c070340300c080d075400840d03401c00e4640700f0950200344413842c00c40d2155658011950a9080c0040c0d58018040c10b003100c0c54500456801009000010040060300d09944d090503180c090030700b0180342c040c07407030643d81c8009107100094200c4e600710184481c007510080c80034001c4a090 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 678725872 1250 678724622 678724637
    0x4061d01061d09060f0705161a060319050322050d03080a050a1a0405040c170109020a090213140303070807050c01020f0f0318030102040302040c180f05060702040f150602010b01 78
    0x242d21984d50303450113551843e08410944081403400e40a4002420b8040000100c84e0b0341407290303190386148102c201007500010600c142089554a0180300003a81101942c2180c1040341d669119999240503000060080c204000350410940096507044401450001c04513400c00700503240040000c00c050f40c410406c00d01f04808100c564510780540c40c031502200d10070782c20b00d504a50400c8007504c0007820556648100040c0401c900d60011941c0002841c02070011490644a20611810f0902540001c000f00c0c4184240c0e001c02c400e034000072007110000c1c0d030400d0141e229440040e046118640c0020708014000400108108000c66a003901490903002d0b41c00c00c4021481854441106014580c0550030800c250b02070303800c80700312003002802c000d000141020345903400300d800c56101c484483d011601c00c83d0400701c008180c2c1c50a0025001e10107d0f1011903113070501240d014001c1c254024826915010b82d0740d49001d0f181d00c0f604000c135131401d400c1003040d03403a04080d00070501980c209001030341c003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 678727122 1250 678725872 678725881
    0x4060e0702100e010207030e040914120c1e0715172401090612090609140f06010b0f041208120c040f0605070503040e0718060923030604061d01061d 65
    0x10b101b81c6a1032500368480d17007140340002e000c21004151296049883c4006807030880c844400810031840c60540700c003c41d580d282030200d1203a1500d03281d00100c04080203644903e0440ca0320109240c0c04540001101350454140407005a4141c1d550030514401407a4001c1081900c44130076089090080c0c406907200a50300c041c40045900c0042800750b80c0104130090480c20000116502441c81103004032800504480303181e58603601180c601c100e540160303110300c4603560740a0007400714a00404c803040d102c3e1314105443d00148402d000d2803103222080348448002c0b0043c0301207442180e84210360702030981c015250001d080c90603074000740159450b00103020b2001ca1128024821203041d01c0c1c01034019403c00c1e00e0241c031050403204c001c200d00200620303008110440104030030f041c8041c01f5240c891407a04e50070103080d0a2022524943d1480e08203440e403090949072004191a81c215402800110350000c1000000c5000d403100c5000807490b603c1c0c610001000421081c85249080f0108000c0702161079 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 678728372 1250 678727122 678727151
    0xa1a040f14100e130615110d090501050a0908060a0f0b041a0d03200f0c010906081902040b0f070b0105090c12060d060207050115090501140f04060e070210 68
    0x1001c00a10303810203200c0015450305405080c6041403100010190b01c0884903150000054801641c069840c20011803100c0505941082d030441c0c43c03980071801801e80c5450150000c0c070b4020140304841c140500040c00c0c10300c680c0b00f500310b0005810f141048612031704001403500003c08150000c9030350345191214400151030140141814902501140e0243e0b902c1030003000300705c00c14040d084052042099100549808007200100b0840350350300500750718404c4890507418995990010782c10071030100800c2c00141c2d00040030316009103a41308000000b07200302d4940303c028031a41d040458400004144240308a0300b001c002c100301449203001c910540d80c0c0300d0a00c4405441039501c10b030755420510103441000301482d5507561110008101f207030800f06d1a11608100c0c4c0c01044191343e965103800242c0311402003242d2050051030207e2040100303600d01510318007035103018010a8860010340180c0c54980d540e5800c618058101900015181e0038030081c00707540c481c44800252032060408414440c03070103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 678729622 1250 678728372 678728399
    0x9030803071e2705150c0f06010e010305071409040b0406110409020409060803070f1b030c1d06030a0309050f18070e01090803160312200a110a050a030e0a1a040f 71
    0x302d004d02207030801803540840c05010b8000c6c0c161924948180ca01c40898404100444e6008010900b4107007800d5041d410b05605081513500080d042d46039000000c0e0154403924501d07980070f80c2005108d031154031036140410290500d4005682c1c0c007500402c020901c400076600510403241c00756820006180d5440d0450b46070f01509901424a5038600744c580007041d509060424000307848003292000c0b603125030740e04920b22101e410500503450920100d0110620401e005900b000048000300100a2640c0d0024040103240c000d15004141840c10b121840e22040904c54041c02021000720061400000c02001070180c1641540024005c0c1030000790403038007000315038142d401003c441101c03001a84044d21090305101c841140d0035910b40c0064601140c1901200425903d100c22564904d2510b0740100082900100c419198201c2d22403040014000078041c80e44662606021644001c07450014400c16103560210b5500f41e0508031441a0688560003481030381c85142c1e215810b10740741c8030b036244040d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 678730872 1250 678729622 678729629
    0x1180c0801030b0a0903140c030414010e0901140f1f1b1713030807050d0e06090604031e050a060b09011d061221090a0902090109030803071e27 63
    0xc03a1054045684c3c80c5150300034026440c024141400c2c0701c0b4111400b41d03410b0340402c01840040d0400325007400740f800c5d03900ca078100e190003d10b880000030070300d80001240320006110362081c8041e90000180552601c104014400400030810a048010503010059060818141900140040081405285420354201181303500001054001c4d4a205022000c40d070200c04119541d50f5515400800199200c00900303a81d88168040e1840508038032015000004651480b0f2040c1024000c007055074940c0310a417412680c0003881728100d14484105a044a0f29449002d442d41c0100801c100038099a90422031030798900340d44000481e170342e0b81200802c040394080e6034030445911001050003482e1040c60303240300140c3c00342510303280c03070301c92120b08002c0c1c095550401c48490086403461751031600d207000e10001c2041b84000d41c6040e0344400002d183d046507010040c4101c2020011442c07441c41081c4542d80c0448040341e0161035003400300003401c22203030341ca00070321800381800f2a10401c011240c07004085 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 678732122 1250 678730872 678730883
    0xa18050a032103140408120a18020d0c03080f03070801080109030518010e131401090204121b09050a06031203061412012405010f02010501061704020409060501180c080103 75
    0x208a118a001d2002495440b18008041d2a2520340d0003800b00516501d010754400c14205580d4141d901600d425004006e21050340e080ca401030424050460600b03192280e64100c2c3d880c145800145004441210603410140070309c1c0010520180c5884840000c40c014012501c901c0c2c0030341c3c2c1e9161000d090321002031000780029000d2002c01964000055100240710050500400180e2508d0214080300c47d00495004426216000641036001152129024004942041d0b00c0d243c145200c0741c1640c10b44020040440200700000380354014821100005060408024040750601d450080043c01c103500094604010f040000d021181c043c2c031400084840464403d0a120326407002c1020280242078030500da95291a0407202c01c1581e40101c40000c041c11621080c2c06040500040c0078050031403801c07007568074104c01480b025820404940c071807036400c0b580f00000d0795140f01150142c040540c000740b40c40c2c10a40081046e46000090070302480e0705000402c410310b00301c103040724aa542071001414 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 678733372 1250 678732122 678732143
    0x100515030c040e040305090d0302280b041416030602090109051f0e0102010e070914010503150a020306010e03010e01060302130908071403040e09071a0903030a12110a18050a03 77
    0x280808440f40b20b54001d0007414000d0506002c040440e450340081c0104400680001050b4401c5c417580c0ca000701781c3e44400341051803080301540c2c0e810340640400350015240b54420103444035444c00c2006203680d560811107144440983d64130700000a500050b400030701190400c1004031b218240107a14420208100c203004c80e910481c100252000780400050364115500c0386489800d40070100031800052841301d400281c40706868a0310b046407401a00690b00c680c105000d000c681e1107040900c0d40d003201168000503038944840005079200c460a0103030a4065003032190200452006510680440c0d000743c500c6400180c481c11104201c4808590042020006014510100382d5180e00f00841002d500201e0f07140540300d2420705000c40f011504040d00358000c940c1400030320001c4000800d110076000015080c0810140000d4403030090032414420003c1600d41141d990300c05401000010140d40520b45c2d544d801200010b108985caaa99614140d405030000aa01c0c00c00d0114481101d410070719120 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 678734622 1250 678733372 678733379
    0xa0b191a010c0312090b15060703080403031e0e1011090a091109030f07180203061012140703022706040e130210210b010f030221100515030c04 63
    0x10b44880c4510300607010007000b0040c1c00031010702441810400790161103000100c1c5030480c09a040d04400004d40f50140e0b07400e20a110000fa04002e01c1e98026601d42808a4881c01c4420b240002e100304240c8043c05500f44041c0003085c0740302144907a010003411009001035880c0c50f60703135180c5210b000e148981240d0458010400c61042d40e00030410072446800080c40d048211000900d801182c0080e442650041e903c10006850b8401000d081c0c502407940c2175046181120000e058122702d0b00d0a10180301c4042d041002502031544100075081c141140140c175414544c0d030060003074002c8001c0b80d1252040c554524800c0d80540030780d1003040301c02450246001d007010800d41c142d010140c9070070001214450350800507551185442c0600700243d89800007200090641000c1d0000340703001009240c038207c80f9400c01d99000d03803005034400c818100541c0c2d80d150720710080741044004080e402810038240510100d901d81d0161001104c1d0200c0d001c07151700380314140403043c034030003a41c030340a480e41c0070481003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 678735872 1250 678734622 678734627
    0x1406150a060e0406030606170610080a021203071b1e15050903030f0406051c02030907060503150405091507210b010302040e04030c050d02030a2705030a0b191a01 71
    0x60070b04800c0a0070101d07965035240d5805090303518a80100c404031355560301162401000700300c1103130b2040107060707540151441c0c40f01c100c0e03c0d0b0740700c0400640907121848502c044083c041080b500c101d6400840d0a00740030141303645000d242c606020f07095502e42001c402d46561040001240d09889160409040500403000c084d42e550348000307541509030100780814a41002c803d0041c2005250544504c5d41e10307041c400710b0b050040c5540e9000000e1520501c144250148009584000e480050500b165070740c440381c1c070011108a0400c4055030190900e0100000003001040050051100394414016603c5456003910303900312100c0300c100b48060300c251282243c41e40341c000241214042c1001031030551200c56602c24900116020b078049151074200c4020884200f004000991035807001d14140440100020f02e280119400b11860b03908000300040c1040528040f2001440d0080031141030409078900042e12083c1112403001e19040c0ea503045001c0080c078010810710b0170105a00340142d42a5a005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 678737122 1250 678735872 678735887
    0x5070e04050a0209040b0604181e030315090b090606070201080c032703130f050d08030a0209030a21020106060c0b190510240918090f1406150a06 64
    0x5495a00c501c11001001d44c41c1c3d0790b40940618001d401c6e0031041d10b004420710042d0350303085945500003030321200480c2c045440240344007601d082540002d0131070050b42c02d0440141c110f0144501c10744d41f6041c00000c40c4d15959120a0b0203100c1510090340320364a00082040710700507402c4c00390118500b9400100045141c50040d6480210007074110b58800b040c61400084010900790a4425400058000b081401d01c4040c1802000e13030710310000760349003484089019241c00510080100d140840841c0d00c0d4550f5405a454040d0040e0803240303d8126410041000c0015040c13281d0310f07491000554414920601508080d21100c2d16000c0c0c241410741d65002c00190f0081c08240c50324032914180c420035038280a09400380c0f841c41c00748059503007440102040600640b40070440c07140d0604400c420a0340200134030003201c80781c0e42d540d68407080920b0b00d440940080c0c0c10017044110507001a01c00c010444000114042100003203036040e54614180001100c16020300c1e0381d03c145068010027400b0703c11582c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 678738372 1250 678737122 678737131
    0x40311120a0b01060c051623010c0f050706110c0a0501200d0809070b04081c050f0a170105180402040b0411070f0515100b0d061701050405060702030705070e 69
    0x100c85004220740c84180b8442003e80280d40002c103800300741030500c8001c100440508840050004603240340c900b00811001c0f010481c030380d4281d00c050303d18000342e002c0c03580060740036002400b041c4c1e020014900a91100c00c903004c0d040101d4a05150005651000584c5500240c0c1c060541d9101c942028015960090340a0302d09848142030024400b440c0024004482d200d103458941d000317181445a540d50800c00302e900b0213961070a00344403c10000c03000003140d50200d00c0601c40c40c0e56202c204541150f1901c5452213189a8100004421803c203605c4044001d07541e02400a14583d0b90300d80c010401c01e50002601c420400320010007080152030582d01040c00c0f00001800000d40d459811022441034000c24015641700d04082c0b401001c0c00310034460012448900c2c061001945040300107104c0d01082800382032081030300801c40e10510012540010040e003000c0801c4004400d05890241c040c0200700d90448031402070b20081050540004184e8006a61241c0900500d60a141350f1a250070b00040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 678739622 1250 678738372 678738409
    0x2090a0f020c2b14030603010e19110a06020c1e10020f0c010804030903030804050c040e010f0614060403080c10020a0804060c05030c030a0b0d081602010e06040311 72
    0x1103031000303420310501c010041060503002400c0c41c1c0380c0588038070703101d1100c940d0740b8110302240c04200450a40d00508640c500c00c2c05094450b12a250000801e00400c2d180c603000038544101081840c403c100c4008100f0858030800801900113440400d1010b45d01c00380c0b01e0000540e0258000136410f02c0d0100841d009882c2507419001d101c0b0042d00000e164480f40f0100c00c000d600074000b0440300d50340c00d00142c00c0086084c2451107550805560091200c42548000341c01c22002e040482d040002c140070350300a000008100344400c0c000b0408850082c1448031080c017629140034000508502030700e801e48a0100010007003810145503403140b026a0b440080d42740c10343e0184500c0011103144900c05002040e51070758501c1003600e041d00d40700084890440c58141400018020448400710070011240c0c818041c1801080c81108507005c502e007900d26000003070019102180040c4001c0710641200c92040c000d0307962104c60702c12481882050320072400060031024550700c0904c003506048554020301d050a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 678740872 1250 678739622 678739631
    0x1103010c0f0509193b010e0403020c1e01080a060501020d0302090a09020310030b07020715030f14160e0405161404031506060e03030309150903040503060109050105010f0f0c02090a 79
    0x581001c038a051185e00301c40c11300b64000d050b1002440c4120303940000c542d8605140a0451101e44011040b1041480740d6a49204001d0008080600c01e0005140c1808042d0621a06140c07440340b891584a140307a04a00064801c0c000030484d000380c2c001e12044030410f8000c2d1458040c0c0610072006035010f0001d480d04a446132030b0000b0440d600e40f000f940b0070341041d000118042c0c154648003950440c06890b10342198020201401004007280020742007065504000407004048100035020780f841c0011803d10200010400001c44140c00600100c2e1866641d80b12074904200208012a6800e136071105a00c0d895140c40303000325000b0006081024584941f003800e0954075594281316a1301c1501d82038009031a084100441c82d00b20001680a00d402c602131400d6190078000360741e48110041c6281c004103200d2010880c440400d02c221000740c03d003e01590465030710342d1441d2000c0c0c070b0288035243c00200d001b0b040a0b29140708000d200b084c91020340d5140709800a503000c1000c1a04040c1035582c049030788 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 678742122 1250 678740872 678740899
    0x2011d0f150408070e01050a050306150616080a2a08070b07210213320a051215070503040209010306050c04091d060a1b1422031103010c0f0509 63
    0x300030f0384e0700400c1c1424179201d6543c1810103124100405030b000354065400042400b0300c40340d1101281e4100310041c0c460b1601c8884010200d150100d85501c0500355007000600c4840c0d03260b10032207658141c00e40d401501f81c1c107007241d08441c200d41d01d240c0024000001c00d20075200010702c0d10b030426422801a1902004900307000c0418100c5016240c124041c15500180314012610300106080061400c203000303420b03010750300305090702e9021070351649400703000300d50716089507a640c039a8180e0141001506521091050405a03a514407280450100000a003800142c2c02c034880c0341101d12450b0301620120080c1d10310f0751414050680034180700032502c0305200110b100f9541c2d1140f41984034660400004280d070107007045081040203880d540d40c00782485c603421480341e090105144000841e141501c2003499015154070540181c100121000088480d00228040c00c03c2600b0305890040403210343d10861807007058200c40280f03038444042440000d8907101c407806280503200c200405003280401070310 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 678743372 1250 678742122 678742139
    0x7080105130b07053c0307120e0118020621100611071406070203010b12031c14132402030a0606030204050319030c12080402011d0f1504 60
    0x41111009149101140c0308014070100c20300054003e082801c10307910304010741310070b101d514a0307810b40c031208200d00c1010b4041c4800c60010000c100e00d180694203031a0b0412042c020b0480c442d6240d4080c0342420013403641e1b04d0741c1040c40341500880c0f28890078000d0724004d5091107a950010492200080e40d412060100b850b40c00002c18810100c00b040140c4041c02c210018003111180d4030b02d80166403100c182031101c009295021591824200c801546807501403000030b000d40350381d800c1982c02000e842802118100d0002c0540442c9030340c121044a004d03c16840b100844840d40c07142034450300390300c01142c8602d044981c081d410318040c0d0022103400a148058094009150700131502c1c1130303030001c01c2019107031083c4901c030007400c1d4074a0b09600d040e280c140001c2d9201c010b0609030390000c0450001c24100342c001c00100100940c007044a2940b400308203005407045204a030140e001c10704000d6600c401c070300d2030320b071140e05041e0084c100035001c4025400e2001c4085400c000c6d1034481410040803440c0700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 678744622 1250 678743372 678743381
    0x10142a060c0a26070302030a0b0a09200708090f04020c0d090f0f0612020d06051e031e10050402030f0304080c030f011103070f05040b0c2515050705070801 68
    0x1c0c0801e080365100042c20005102804002211980c0d0120064015059484000140e0404080e1402680740d031203c9600800030030218042a6120044440c0040e04c00d0054015080c1103803400c1c2d8180c080200042d580d041072040000c0200070520030095144c1d945020804004000d4000c0c00040c01c0c4016044034918146541301141e02080d9507040030080c0c408240c0004007e4040381c104c0001c010318007600604128000714070b0700102c070f4010403085480c403510b0f80403400901000b8101d507c440c0c5100b14101c101ea99808120b4024040e0502c20040807a1407941003e5541600b0001d0945c0b24004030490b008043c068400c070382c0350040c2031000c1d6100c20204007074009021408050140c45503241c04040c500300903a00b11b004503034104a0f410307400700000d009a9a0000980c01e041010440344c0e0012600c42c42280c0019038516400b14222140000019100f010071180600f60000b5002004031880345503000e1042c20b14000a600e100c416540c407070720103402c1d242c0c03054007250941178032081c41a0945c0e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 678745872 1250 678744622 678744631
    0x41407050a0e0907050402041d130f080d0e1c051e1305030c03010b010e10211b0215010506090a032319020f01080403120509030910142a06 61
    0x242c0480382841103500b002d106410043c14221411482c01c1d28003225408280007540c408808041844001012200b501040c0e1100719408040b680114201e407400d0205600070b900b20b81050751505940c404500310002d004070090f03d07502c1d070010b0400ba88900c10cd034036034860304040304842501c00b10f03161251138032009020f44010154854001078184410b0614107003108080b20300c00d81c1450542003440c1d802c45400e0155280958200d09130030452582620441c21450013000720b0b202034200c0480d0900703240d00c00304444491b04401d884010381824226550340781000c1c81001640305000412051600c1c43c010250b5480203030401e0720b2959241c6801030646580a4441500c485040305840c1181041c0300719110159032141010401403150049210500780c40d09803030600a10354007150606d07029204241039924001400d10503441c0100c400c580ba5009201924045c0c0d9804030043c500341e0044403806200d0609503400b074101031205008840d5020009804030604111004c002000b910a03c800343c800c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 678747122 1250 678745872 678745889
    0x4052209050c0f2b080412210804030906080a09081c0c05130308091810031e08121806041a0a05090a020f04020d1401090c0e09041407050a 61
    0x50b108401031003020300321040040e10541803800d501103e240020f03030740401000001d4019440300c400d450aa070321031046d900200c01c1c40d61401500000c004101c3c00d817403940d014401000b0380e24051460252400c0780c1c00e540040c0802c84e8900300384212482501000da02491490001c5080c50540d1545140d41d84025804046054070251040858105004003a9140906c0c80d0141c0307071405041d448800c0079458040101b80040c00036000c0b6035030362608140d60a652600c144002d003800d06107010071100c5520f00c021140745000000c144004002914190541a0003502452410325036012201103108000c0540b4003041251850801c5840e0422402d4400c41c0304401401d41d0a100c1442c07130540200040103060158103100403c88885d001240c0050031503030640f90400850716140004d030280c0035040c6c131010843e00d008441c0c035507203584028542c1240e181c894100710141030000c007111120048c1c0b5059400081ca5008500007a62650202d0400c1c40018140c07100a600e480000e910710f030095001d00c21 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 678748372 1250 678747122 678747133
    0x80112110a0b0a1106071419050f03090114010b03060109120c120b010e0a0902100507020109030204020a030204050f04050403140309070b030106080429061509060403140f010b060405220905 83
    0x2101300c41081106e401446909200c0003404108000503264420190b50085030b90760020f0b18182c2c1405042a1544c00420b280480d480386401d403109802040c882c002074201030500c13800080c01004070400c07240908010303075651440c6801e204510072040f580c40011210300d540c014000450115100c40c1e2204207100704001c0700654900700200e00c01c1600900118011440e040c01940140e8403102610900486420b145868261500042c0c0c3c02c1485580f000c0d40181c0000340d607104443d455401001946ca0803618081c04042180502003100c0341101d004012404513411200c0c110401c40195910400c90300469034410345500740170703a040e00700b0703803041003c034448134207100401090002d034140311125408035001500d0861034a40d940e501c090081805960245940b81414044408580106a001c1d0509680f26560b00d400d54100240121403403660158080303001444206000d5148103110080c00300b4205400c045c2040050f644c41c1306101201c8003400c032420040c0080c2c1c022854858001d801808 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 678749622 1250 678748372 678748397
    0x703020a091d010303200d0f0f03020c21070f03020c100201020309070b0c01060b120a05060d050c011d030a261314030102092d01080112110a0b0a 64
    0x140001c8254009004a0402c101994aa01142291241100d8041c582003501c0403e02c1c00c0c140c041c115103005003002c2c0c020985010242500102d0710560342450355900c1e940b152080f8421003c034002c41c5800300311078002d04400d1060b00c5000d04020b030900d0740240c0f03482c6000e00d6a80c0307100d981081820102c0250b00318555030303000380c0741180c82c2d0f209840d0107000a40c03035803415040450311040e140c0035031031100b040400e101c0403440d02540000050514040c101d81e94208481101840303990890f4083c007a64204000030b02d042c18103503101540e90341d1000c003d1020203180c00040d1130b0019201c1c80030829451134036000120380e070204202607199010b032504102c0c404a110003840c04000f1000c5000300008100803504280242e602c00d601258030b5220f01e1826000c0700000207019100310850150b01400640c180914508442840c1e042000c02c40428503901c00545c00654070944240b08154403800240410401304220034601ca030003803001003000d1412034481600210321b421060b210301c0002c035509440b4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 678750872 1250 678749622 678749627
    0x20706140903151911070305090405040302070b0c030d0b0a181a130b03010506120705010e0307030c06020d180b071b17010b1804171c060b0d0b01170a11120703020a 72
    0x1400c4803400301e03c551800001d0340300586280308020700f542c08ac5a480001400740340c07003804500041c00000134416130b20b0b0310054120b50b80c1e40151381c1c44172185203805241c07042c901e0413100d444115180c0c1200e14010303461225180000708154881181e040c3c14a1a000c00956a40c0e0000030900860510000f074806c1c0040a0600315200207060a00664156a082c407455600040c210300710f420902e404140040d010000c00d00300000d40d48002d02010241030301140c03480d0046011000810304e60344200c20940150305154100703005126110910108110f5075001c1000d11103003806181c10721441e01d82440e03a510200360807107044104203803107035543c80c070f00c47c2940b814101c0c0816207030030340300103908908043e21901034001501d83d41c0504410001650003541e49900c5039034989507240001040001e541c3d902c084043c0d4002c0c002103c581d4a4510301d0415980222402160085102d200d0384072660395295400050442c04c81028032a00240005d18480441131900ca200b100c1540c0d0140c1c4945414402 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 678752122 1250 678750872 678750881
    0xb0703030c030905030921190314042702070b0a020405130b1008060a0e0415111206130204210203070509040305092b030c0308070207061409031519 65
    0x240310815003000d900d2030100d840001a102d80c00011205005605800c001f098100356a21902c2102c07401800f05080340c8805090504c960a8040e494052070108480714071051440799000300c0310144000071040b0174002c810302e00c42c4901e24001c14010319107109601e0324107113100201c07010385a00d0340016050015081c4540a00001d9400480c207022070505e020000700081040e03031240007040004030001e0019a21045000000e00541d400c141c020304050412445607914028040106410008048a881c1406048403011400000c94402640b12901000089010031100c1c1e0340c580e800344004255106000c01c1450b802a4411603044122035902c14513041003004e900082c829a0550200b10119801c1801c540f03179007030200c40c1003003c0c0c10040c0c082940c1500314020365192402d01c101200825400c20100081d0078003a8644130781c1e944c2c5544040340e0320a000c0c010f000c005024003120109101d101c4000e041d07141001825542200c54194400021010481e03c011081c0303945982500001481e00c503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 678753372 1250 678752122 678752141
    0x2b0c1d16170a0b04060b0310050306250c170c0102070c060306051302030406061a07050c0405100e1e040f110a03020915040b03060a060905010e0609071101020d060b070303 75
    0x10440c101103654041d0000c003031801040c4000309902d0790200503113651107a2005000e899003d4a82d40c4a007000e5404205c5040320303025950081c441d040c041030f1070b014800200c10221561060034120b003008907c04840180944a04030743c44106580c0b910309040c40f81018040c6134000700001a11000c4505180c40f410407a42d108105061608005202c1502e40700818603800c01c05a50250341da886501c3c15070024480c641c0304613440c44c02c0404092400c9200d00c01017003042d005908481c03181034001d0400040701d105580d050251900110200800381c0314201c001e1340b00d0410400d88109401c1c48004440480302110201c0300c01e0b00360100142000301d40c0082146040050300e40f4442c7d2415640400c40081e400303001c080301401c6000095050399959000704844c40c0b00981a5075a41c00d144078184050041341c01084481800d140010400b5416041740e00d101c0d03080108894080e80700c1400540350f074026003283d800c195400300161188241140142001005200445541c40c001414000c046448107074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 678754622 1250 678753372 678753377
    0x120606020c0117160516080a0302071b05060915040306090302030304031e0503010b0702030327040c020a020d03030b0a0e01060f09080d020d0305070207031704050901052b0c1d16 78
    0x1800d1000780b02c02280d40801540c00c1d42801031b9a41da1100c0b40042030034420b1030041c860362000500c0781c0b440382d00d40c015100840c482c00d0340c4104000315500041e00040a070140c9500b1031414030046850f0b00c0c04032501801d14000300300031483c20b9140c3d1240001c0d5a103042003030300941c0c000018001055070280301c4129003500300e5101141c02e40f507008000c2092106106400d401640401c0400665809108607858503804580c01c10b51400074001112034040303004138140c411403401941444c03460000c9110842c0035070082100c00b01a125076000d4005000c0d103144203421200c1004d0100b0400015510340780030b0300d17880e1911030714180e08100c001c0101c50070f50019445070708106c101055440d000555040700c0c0c031540c1000710300c3ea66651000ca10303200722688081c2c0065100d40a10403210103c200038400e6540a0f04c075403095030788403410302c90001c500400c408944003041c021050f2a038841600201600e20440b10f030142903556025110700403030945da0403a00841d03200180400b0004002c540f003124080c90 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 678755872 1250 678754622 678754667
    0x318080a180f03020f061b1006050d020913060605060d050901062c0901020d0606030b1503130605090c211e03071e0c0b0316051c0903120606020c01 65
    0x1c0020662450743d00c0000d000d1030b501c1d00301895a80d00c130b1082e20b1078480d210140c0044455480c08240d0f48031005490811514038041c004036090400a102e0800300703030054003080b40f90b201e45021082c3c070180c1c260180c42c46a5914808111a0f40d90002040b50718003048010401d81412100d040c2100d007a58041c9414404010a6850b02c00541030200002151360200306c1e007a0752049034540c0644078013003888050620b0f100002c0b0b081900360f40b04a820754410f403600c01c401812609801047d00c425682d600c0400000e204400010f800b503045258808481415958402452008640041d194641c41c440355404c40581c003030701c0d400c03c00c404040262041d440000355071014003520b88910818001501c4c48044006031200ca0a105d008607289907440700f9030100a654854242000d0340043d5110326410100c040c0d52040d90f48240309954150a1144d17003d803030100071880c2c0200906105c5400c40901540440500c0c0380b6825200c0c2e440140140d40260140b840010001001030b0351501d4101c000e540c09 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 678757122 1250 678755872 678755879
    0x60605031e060901030813031407030507090c080115091a0912150c0901030b060c010c08090a0c210605040602130902070c060c030512010f0603050a0e100c0318080a18 73
    0x20486084d04482d040145a03954600c0030950700d2403014544c0015140b0039041c421311001d84800200c4004480c0108161000070b0388400c181001e9824200c80000043c5d02d4130010b010064200148088101981c2003403d020340e641d01c2c0410000020400c40c018144000c2030303002a501b8800740700b400700b400b01009400f00c40d62000c001160b90340301a024800c039550126540d100c1e0f0f4083d50240601c10802441c0c151104200041b1502070013164010b031001561682c0415107218001990708a86039000040340365550600388040c070f880c11000c0c04643d104c80705000c0320020800520076140140c0c02070f0340140c0d840d40b000c103141c00e00780640d5004c2e4003018030401c00780d008910003840e10015902e851030000d90101c2c1c241400c07100e902036640b501246619070b200000e1800200c60368a07040710720944040c0b0195903217a0180b41102c602c100c0d205025041184100f110a000740c2c04050f031150142000903489031401c107140e0801c00c0303100d001c07145007030300041200b80180c2002d1050040040341400000c410b05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 678758372 1250 678757122 678757129
    0xd030b180702120906040b2208060103030c0204050c090d1a010b1206120102071505040506130f23010e0601090f060510030f020f0a2024100306060605031e06 69
    0x40a003210f0400f4a8080b9250505a40d00401c89000f400c481245644903510b070007400b41c143d141400b044da04c040d04048006418440890991304890b0075841d505481d20040e009d01010b04801080401004c0c0d04000c60310259441030442c400403401809050100c0b88c032800d8810521106802590314108280503280003042c80f04401a8414000c1e9003641d44030210104c01400781c0039644000309005005400b0180d01c0c3d02c3d55001078030607800b80d004c071411034031408494501c0c803003ea440a0511407a0040520108150001900000d490b0032a16054408004512421601203c440007a19000340004000e042c07154080c0c030070100c22080c010002c1618140006a4010480c4005000e06451700144904401107905541c02e100c1c410384c0041d0f9850700d01c0d4009004001010007841203002d000309040f00d0710340001d05200c4c42c003560b0180c200340500d1910032201ca824000c1c115403070030f05030100110006d800350107400d0051403681c8526489003481070000d01034a5242481002040b030400402c0707195078 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 678759622 1250 678758372 678758383
    0xe0a3c060905060f120106030f0b19020703080705210705070b0105040c05040611030d05040b0406050a05090c010c080405030d0215012106110c06010f060e180411120d030b180702 78
    0x4c0c0850780361010314140140c5070301500265101078011651a50b0b0441800031804d022440b608040762541c1d0400071400c646d80482c0601366010740007448050000e110035000350010803240f040c501942d40103544200c0c0c81c15100784203c403054001007020642c0d6041018070700f18180545400c55050051460f1000005c11600031031041a040150715807015082d81310070720403221881c2c00cce410148214070b4103041047c2042c4064504035001490440000d851186902c20503015003504000341040003001d000448502115160a031200711040000050a60741041311400d080300710303000b804004481461f03a0180c07203070591107070b200d020070703107448a0109034010300070071000e507001c84001031210018901e0380c1c4034010290101c006214100000c40c584891206640484000b60350b180c0a107000340c01400b10000c51500d0741102e45a4020100340090000c48010b00c04244c0a040d840f00b8074550f40b501458000103800441c0469a210840d0143d0709043d11001001071040d2064442230900080003961203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 678760872 1250 678759622 678759649
    0x901081018080d02032505090901061704330510050a0b250501091109180312070c02061801080a05040305091003020f04081e070e0a3c06090506 63
    0x860b030000014a00703d140e2025142000640b0a40005a06c41b0803400b0308954010710315103110300e40c10300000a200e44034492480d0140c085611039003032034880d03a40b000403071805c1120003002108000f0903c058544078125851806550000c08202d50030201a40b00d44904035811060148048040a11146803008112100c030200c6103d00d201110058510300700442100c0c0c402802542041121020300107030010b00c0c214020f00b140d2a000c01d44655041010b0410300c2c04100f145d5400502c901200d804918030701c607070302008030300b003c101c40f9240742d0000700d5a90207201c00c001d2031908036030340b0344141d41d00c202141c1d8040012441004907040c00c2c0c83c040c1480c0511880c3d18030840c0e023100300c500c0c0648130b40c041e1480000e8414034161502e413103007003c81d2503404072000e82120030248003040702d05140002d4890300712030000c0c0010b4669110a003a0401030112805105170000d1036030050540c6150300e20164840400c40c1605100705070002450303405031155544202d0520307051509114059851200030407d9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 678762122 1250 678760872 678760897
    0x10b070519030e2701060504150804020609190306110a0c110112050703060504050907060516110d03170906090c0105130801060b1e04030b070e03010902090108101808 73
    0x200c1c01ca441c0c200c8501ca0340022403600461004102048442d60b905512544085180281c0e426a00c0e07400442d42030041d07101b00a0380310004401011610300407010309401070b0014122620b8104002c010817001200e40e00f40d2000008240410414040d6034401d4061500d40e548006280484408c4000c200f00789183c0054024209816540011313806040c2c017805d940041d12060001e40303020074010300100b55a101d0280141d003444006001103401082c24000e5070119112281402413604040e00b1362064031004132a40340000402c04421398406280c000c00f02d1090340c8401c008800411001517000c0d000c0c00746c5840e80c0c442400d00a5401010880b509000d90038a40b0720703103880b4190100081c19000c2c0c0d205400c95482c1c090b001c120f0412090041407030100909064041001c010710349090713840341d803001401000c0340d440803d06031b51052102030b120150040000c10b440801d0740025201030001e900032850f9600552004880300054083e211402000424808465015440d0908180b00f0541490712 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 678763372 1250 678762122 678762163
    0x7030915050304170d09050a030504050315060d080c030408071415031006030e0309180f01050910150c0209270f070b0c07080a081c02040b16080f1809010b0705 70
    0x200741721640c44440e413140c2020440d90f0307801c440d041c090410b602c42e01070b05009004e4017150741000e1080c810307501c0c0a404054008209644a40c403040c0b42d54100e85800382da14041000009018441080010007506c40c00204515025841040103016a044800d85145200a00812041d440701c0005134040b00e400c1d00b001315405499001c1141184100d034583c81c0c1c4a0f01d2034140c5040c0280022000c0d2180d9004110303404a41d8840003007060000003122046a0698440703400c2c80b01400c400030b00b00013880c1c2814582d03180ca0322940000c040c190f0854205c051001d035808040c520402115440c62660350700c10240485840c110b40d010303101d650070302903001d55140c001404202c1c11003c010701c5000703041000c1604d1340740300d017840d0030190f0b076014100d01d903640c01c8001041d031100110340c400c0b82c08441a00c03d8152401d0803180e42c100900d4070b161000d0312801c1c1e0500400c0c408950500040c14010240b14446c49003003132100800502c200d06811114010354280850800150005450007082001040c00131 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 678764622 1250 678763372 678763387
    0x1202011404120804080c0d0b04061509020a0201020909010915030227041a0601051809130516081005010503071707270506030c0121020f0703091505030417 68
    0x104948100e03402070014008502c00c210034408032034064000d84108600341e580c18a500d004118200d481e604024003008850300210740001c0c800d40c480161414140c0c1c131403103480c1d42d40502400b243c01240326100176075000100100c142c0f40c1424940d01410a08104003d041407459803588502030b1408000d01519492015505502041c0480000e9a061038013503a0140b0703040ca040c0380c40c1075003030880340002030036000895120740c0250207448442d5444040100c1036200c40302000f0309240043e00035042c1309510000d060208074180202c1d40303440c12281c007105180d0300d450146440e140e01107507000807141c5014014803030740e0340200d405001c030740304010b49030607030035038614078500f4188940d1041d64900030f41c00044486046080300500c0442c0802c8081200d591070b41305042d1151620013032305000074446114414030400c16906180c0380111218014180100740c902c02105912005041d008121740c420200401210703402080c81d921600e14000d400c1d4100b5989070124070750300d00008160711f4400324580303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 678765872 1250 678764622 678764657
    0xf0a020f16030903020a060c0506040b04021c0c1e080c0d02030f0712020a0b0a0206040201030c0516081b28020126062409060a021507051c0501120201 66
    0x5034229801c10306500102000d902e000391080d4240c1c8012802201840e800007440350140089054180c0c00070082d012540d6241e440300d002400c0140100d03404010a0041d48a0004c00481080e07a144a40c840001d0b60b410a10381c02c0084421460400e085c0f4807004040c080c401c0041034010344d480c4c041c1ca039403210500c0b0b480001d0402c014400030300c41c1d03481030300b000203500261110720308030319402503403410750071502d03030006060a100300344402e000f603403104001c40d0040d482544100c40310415868143d04010801d80000b207480c26030310701562146804070701d00f03101d4040540107420790141c080041102040005d01680e010b4046010300003484a91400e00b0305590042c2400c0320f02c0024070700c14000f00c9422225000900d00709882c03030b0740540700e400340ba40650545083c07440521061401e019040a0b607038410000b0382d9101901034070842c003032445290060b0100c41340240c0289883d450301a240c07100c140c0e00500d03a14a6201a500e100d0500c0010803c1803c54210101c0040c1c080c40d000700c2455012241 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 678767122 1250 678765872 678765877
    0x5100905090601050903030a030506041a06120c0f0406020a060506010905010f140d0501090504060b060a0903020d06091217060103050106090306090501061a0904050a0b0f06072f01080601080f0a020f 87
    0x85d50b054000021803104455055000740e211701400c6500304405100741d11030050981c0750342a6a1703040903041000300c02d510000d4020075403001d403000825103444c400f400400d102c0d400c07a03030080f40036901000881042000c2030196942c000740a04e07040c0039a81c030b4a4002046510000015000d11009403911002d1900001c12a0410b00d9560028843c55075100c0b100001004104c4060301c0c49803805007a0042464518100d9411000554801a0550440c1c0801ca1940b00c0d0090883d801c0d950360951000090440c402c0740014182511141a241e000980d2040002c0340203150504140c41d201c01800351355048442841544e0b04100c0003d108841442d2035801480c0c81c0c1c1203c3e016840302442c1d0148501103e000b005842400d03107090090f078580e01c0002c400e555903108010b0f03100604100c0c6003054280100545000b501030700d0040030000b1440300319000050700c4860001500100d8040207010350300566070307503002071007860517200500c0d165400c4104204081c28621041d6000900e120501405409 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 678768372 1250 678767122 678767137
    0x1d060d0b0f130c0f0519030309060e030c090108032502010f030f0207170901020d080c070f030903080d06051c0b040b100b0301090e120f04051903060906050906010510090509060105 79
    0x91640340c1075124100c841310180548140d0348640c1219800d020b008400b007001400b16645031316041c44d910b042c0f640645012600c2a40320341c1501c038071800000305640740780845001701000000382d03583e241c0e641e9440c8545501810b80d01100c4201c40e41c03070300041c1da101000d140b00030424540011402c1c5920710381000b0f40303e0b14802824001150320f2a42d400c000f0030f001040d800009808813051803250742000e4850480450b04044c5188007480700394041000f601e14080300300d1191078a80151501d03552020401e170840104000c115907150424005d41c20218080c10501c48a018000c101044941c0d9424408500a000a00068003440440c0c08440c004403102c024101c2c40101545942e10f61800303400030000e020b00c440041c45007002840c0d1005180701101c0800000c841010b141c6030400091207044a20080c0804c3c4e204d80320381c8000003080e002d10a100109104520200340c80c284145890714146040e082107115180c920080d036002a0031018000844a00703907074003800d541e40c0320010380b6140507240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 678769622 1250 678768372 678768383
    0x3010e071418030f0c01090312030608070e0105030d14031515070803250906050a140c0a0302011118040f1808210402060a110708071d060d0b0f13 64
    0x1c0340c400341e1203071440d03041c224041a8121003500c104d00080c69900c0703020b100a00d0208070315600920102e02104d040824151003418041030807551f03442d0301031401105602003c014401c80700140210315040c4040080001246003911491b0750306003950006200c060900c03140d032070b20281c04500b152030b074690391000035818201d900e4450b800c5051541d140d1f8011030b40f80c54244541c8080304e40b09100030828030301c0c494a503903450400c0303070400c0d0054030581e0003100d120081c4641d054144000c0ea603540c008151200000d40074080311042d5240c080c1c01e561301440200140e1005010740385012004007051143c0c0c410413100130901c04002c902c00002000e1111202c0c400c0c121110110042c04540401400c03182c4031050080a034050010400c40915016140250700560411070641800e1042c140140102e20144c181d41c40c440ea10030181c0e01e0846c50f0780c1f0030380c94042409440040440201405075001d0000d45031842017400d20b07902e400c8110001001c660028031018007080c03080b00890b0107480481c0e80b12 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 678770872 1250 678769622 678769627
    0xf010612020f09091503060c0a170c0f030a140c2a060a0c09090218031c082e030c1a09061b03070606240203130608090c0324060604030803010e0714 65
    0x101c148d900d039500c1088001c000c180c40e0011406030840c1060030341d20460f9918101800c10061a5844a4035400a44809200d507190010070590328070003050300c0e0103030180d03000840d580c46100c0d8045441010225803100d46d814061030080c504032001c201d80d40e004103d164005260003c0f08000d403800c060300c0e0841c42c9030750710100300000f0a0910302c0320700000340003c604413140446c0d001142c08800700c0c03515010340056140b202150a280c042100290845409030401c07041d40d5040c070240e1111510360780140c0c1d00100c040e104110f01086449041c0d40c006004440a152034400c07008207031030384035094484070303100070600c2402ca01e41d01c188244e9542d541d00c0700d014403007190760302d8000c20126810b0a040503070500d017400d0701d50003900000454448195042c60700070002e141100903200ca800042020049008110070100196030071311035003e050134404038110a01e500c900c41410000d00040442d4024142040184080754400040d203044a1540f054200550b460010071140d0007001c101001400301c02 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 678772122 1250 678770872 678770881
    0x4022a010e01060806250507080f1603030903030e0a020a0506070804180902090105010e011d0102011d01050103050f49030f0f0b0f04110903060f010612020f0909150306 74
    0x20075146d020700a080d0383d840001d43c0390490340054001450850001c210200106000142a20080d021210407000c8a60403d601440240c0042c072070b80c042100002d030786d0924401015014844c3c150b00028a1008020744101070340810300880650241d548a140c010030700c4020800803104480282c400d102c0300244d28000d12aa00000c0c00700150100c0c0308203103210010515500c0344000c082682c030141e5a0f1b021074420304201c1c400c2c4002501281c1c3c1155210305052046034070000e0b107050764524520000420758914200181420640050304909070070074004043e405000340000e000c107080d10340e40e0700f44912240f220580c900d0007034008809183c03892000b5201261b0076520404034983c6d82142801000303444107055080b00d409414460b0300c24640340002c4010704043d40403420070411400a03a140002030000207103040c00403550150b20b421a0401800b44070351202c405080d50642103419410004903007401c4030303c0d00440324140d00900e601000120f42d0004035071010110840542550f6042c00c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 678773372 1250 678772122 678772139
    0x6200301080106230103090c051e031b03030a0f0314040c080c040b0310020a020a020901091b020115140303120f060109050f030d05030613020a050409050604022a010e0106 75
    0x34455521070354a4201c1c00984103807000780c400b580c007212040c030001e522039540c010b4000f4070300501c081c2c1b04045c103200b000c0342685503072480400902e0300c2001000d5080c1102c04142c6003a25405401c0c44507140d0305000384079500c1c000180c0d145420035040c40d0300802c1c0130007002c80003012125101c1c05410010014801441007502e00c18059410a030190341c0401c07601d45c2840180e4000d15075441e0103620410520380740e443c05078042c00700c0c100345105032403090420303400140540a0a81054030b2a035640e15003a041e41e24030184905000500740001d20000c040007006d02000050752003601d030200700780c80300c100c030982c0c09100300d40c1e02580030090302016003003980b102101c1c143c00b220796902080d84880c01081514109030200407003100180117203121060300d8421200b54102800072074100d5099200301804c2103140c000f42c1491003041d60784549135440d160000f01503820240c03620b40564030401c1041200380030805000e030004000c0d0080000e143c0c00c8001c95004102800c0c0c954829440d00f0b9020480c240d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 678774622 1250 678773372 678773377
    0x1c05100504030e180f04023d03151d06060706021206010230130305030c030319090b060904020303090d0c150305091b060f030901051e0c090d0620 64
    0xd0203480000e8051204020100c21316810740784001c11031140400500113151034415010401c406806090a4002d451510801356582508001002103048441145c5030f41c0b6100d409004007840c5111401585028400f28082c00e105038030132480b40300040000c8841e04e8070021a80d5081c0c0c40034045503500c8405840881d03d01064690324014044c00700b010b200d44400d40003406160a0088039200120b050340d003c5c0c180c9501c0310501c02d424609000c000408604203002030304940035504051540c9107030900e101e0f40d8501d20086042051894841d0003000715000e45140ba038030140a40c1d0702c1d0056125400041d00e180595120345901002021130ad40800c068081136200301c3c2e404c0115018401d600072402c0d010b03100200c03441000c0d40c0c0688042601480c0401c0c510f4030182001c3d114070320303001903852485200c1e41b0071079442035903a448100b805415070341c0340700400585c62010880c00042c20040c221091502c5410485442140200032141c18058540e001c414518030484203042e01010070071080c201078 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 678775872 1250 678774622 678774647
    0x2120406020c07080726010902031f0c030c1202030403020732060c19080906040306061404060b04060e010909020c060403080a0506090f0703022b18021c0510050403 72
    0x20302400c00005a020800903141c400c1e141c040c0c85c2a035825a1b00c00c200d94245824921490351992180e8001d009a202805400ca4148104410720984088640e40d03c0c2695842103490301050300d44031a9580d010351002e10100c8505203020b01503030b02d0700d690408a00c2c1000c0c41c4c010a94043d070800c4010100d60803a40c2000c1c10680e80f100d400e40515071030f801c014145c003600d5545462900000400c0f00084414a071505103035124a400c04c3c1400410400306199800ca03800499149030f80c1c060502040300c0700070703111889100440d000e10440d8109102e0f41454022446a28203024101d00104101e83c01400c4682c040c0c00d468400f191641c0302244c8003030342c40105407016400304070f446012031000112406a82e100e1070011307105581c19290300359a001d01c80d4004180b00c040660a1203a12010031145c018103002c000000d4140110745800c00a602c00c8699805900e100700c051140c0c0640161541034034004035911960400b0101e00c0d007424030740d013803080f00c40c00740700c0f0249404c003007100f010341000154446 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 678776978 1106 678775872 678775897
    0xd23041106040902120a0501141f1b050a03180b0304031202090306070804020f061206121204030305180406030f060507030209030a0b061503060d080a030212040602 72
    0x4981100c5c2100c110b440f500010700408031064000e01c1c0c00340580c0200c9850915000e00040c0c0d5250108413000304407150703802d18138034030750207420314903805494044103000000240c901117803180249036044002c01e039422410b060140c4d15100000c10365076150703041c40c91510b6130389050b40c4022080000d40e500c070750200301800103030b142401101d000d501e00781c440d03a2840c14940b041140021a100005000d1982881640d40d010303441c6800c60303000350341a1404010341d402c0130641c50424620b141c3d8400050f9001400000300755110005044441840c0c004036615801c0f8001c101c1920700620010b040e4048820805010070b42d150f01140d006035107418010b25000400740881d04080c8125016603900b900c060402602d8105506000d90000162003d28074626103800080d19034a00407601824005000c2102c038241806a811107248007518200102c180ca020315221020b5031005006501 = true := by decide +kernel

theorem cover : BRFrame.Cov 678597122 678776978 := by
  have h0 := BRFrame.cov_init 678597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 678597122 ≤ n) (h2 : n < 678776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
