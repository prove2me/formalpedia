-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0393
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:35:08.702558+00:00
-- url     : https://prove2.me/submissions/7268967f-4ec7-45ac-a8a9-c94a366a5205

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 70503599 ≤ n < 70683455 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 70504849 1250 70503599 70503637
    0x801060b040b1315020703150e0d030902010203130306091502040303020a030c0c0f12170c100f060e0f16020105061018050901140321040b0d090203070303090905100303020d05 77
    0x101e016900c03198919451680030308845400c504092148000d0148032068603403504103e8003501002182a9004081601c0d00cc20b0b905c09032700040349940241c96140b60b507040c0b034010001c1000b216a1003500300758494142c1d00800c4c803000aa03c0c00300c0c0118403014015070032644e1004002441042e11810042c403400c5003035140c03902c584480e40b045210b5004003000c40c9043c413246081c41456544015000d03e01142030f80742c80c4501130469100e68910720031007122502e0300c00759250709000c2c0c0c01000241007506c0e40d8000d5440d0684050480e05816910310b04c01c130044003104808244180140c2d4843c01d4003402c1030342000a0820704032500c843c202da21003515801c05801084a035166105c0900070168845030039448000c0e1020142030021840346160301d200c203091004000f41c0a101903c04607070004000c55252020024040050105100c000b540344c011001e02100300364201c0000416107800036020003460fa1181d04504544000b40005070144c2d100c403489114081c4980e000b40805900c0c1c040316201 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 70506099 1250 70504849 70504859
    0xc030807030305061c050c040207081207020304060f020303060d0807020d02090702010e0d08040b07080c04030f080a0801054609091103152a03070906090801060b040b13 74
    0x39042a44201d001035150800d00200d860442d04c1c0e21142c14816031007012400b0a0740d9440e540c0c10300c0840040c000d03a000f040c0c0300c00340450181514003084014458000e9860815002921390348a401007201003a104910040b2075480001aa8416a80130b40000925030b0561200b4483c1d0308100c404030303880041541c00c0801070316050400c03030064446400215405141c030405608207840907240104003c1c810b400c10000c1148086115000886820082c0054440c203148015a01c03480e00003502c0a0ba404000d00304120300080240496800d80d900c20303400366221001c10486004840d074404048000340a0703401c2d5102d042c0076001000c5d0800e0b007003564848125100c080406d500780c0c013122425603100710351418407010048010014000703c0140c01c0808a440d000a4580300240c41c5440c1082d07020182c1078040e01a1a6040f0245445211303075440b458505001007241905002d40780004054403400141c09405020b1041500d4800d0a400d0516040404400c807503040203401c2e44c00403080f00c0d0b0010b9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 70507349 1250 70506099 70506113
    0xc06020f070317010803070b061306080304030b10060306060e0f0a230a060305040305040e1b0c030315060405060f0708090402070b07030510060806060c071a0a0e0f030a030c0c03 78
    0x1101da01c00c0c0c850381e00c12007804800035075032901680052116082001104002200c0200243d0701007022501c0750700005816220034010261900090074600c40010080240491124405d2143c620002080d0f80c031912420b04500781c400794410900440c03081a10465185001c480d12460000301070440b134603481d5501e01c01803010f0b1b0050341801d44040c420700078088a043c000c0e803c0000d003038682010301807403d080d40e00a00030f21030b5200f40b6076032514000100e10218445801c003910b9248122032207032608060074003252a6441a1245e1446104035006118035041203402c0c1c400711440185070b00d05008844041036403940c4185011102500c1c10050413200d136480784094859180244c120002520f4480c0001c0c0031110060400144c191000c0800c0004079407040d40c1a038401003d8801944407514021070710310b8010f09401243c0c500c0803981803170701490003520240018800304c2c2e42c6c0000d580902c4040c0310b44001000724194258004620aa004ca4000c410701d44916100b40e0303041048030303078a440e045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 70508599 1250 70507349 70507357
    0xa0b03060a15080114010e0a060302150901030b0108040b070f0915020a020102160305060606090402130e070e0d170f0c01050c040e0124081306090b04051e030a0c06020f 74
    0x210072556103120700e45101102c901d0038060400701001300403504400e00c904030300080521503141242d1600b0300085c148075841c0c0010000f0b65000d08505103c006d4046406900d800420007a4006460701110318281d41c4944c0030707580101e801130020350b16602c442400300c0360085c4804c03d1001748850707a02d0004510500c070007000028011a4042d1220350103074800241040840c020585544c00440070600101d0700104010380c110314103d590b503558808000103e000fa00a074000b2095641c10704a0001d44240d03c0c080c40c0e407158120780c0c3c5900d04203145a040000700c00728402c0291101024080d11001c0c81d100c0002003500170382d40c9496a042001c500c07140d0307080d81c0c4100d6001e0582c400c08a420420100900012409400505000e00c001640c2e00781d0380505440201001041119680120b00640f080034030f84144aa0015000d01606a141c00c02402e41901914116410303c02c0c1d4050114111011903814100c0305420082c42c84d203c4d03d40021a50700c100d250080d101241c1c00c03ca44241e03145030340010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 70509849 1250 70508599 70508611
    0x5130803030a020d1b0f0c032d09060309080702040e031b0102040806010605090102030d050a020c0a0317060d020a150513060c020307060807050d0218030609030706051e04020103050a0b0306 83
    0x15989081030000740c800d6414140e007400809500d140540e100f03a401441403070f5800147d18001321854190b0400303d4000240d450501100c8102c0002c00400014555109603482c04a403248003020342d44400440440b220898042c208540920070b00300186402d0300071071400e01c1d0120449040220650f19482d41400c0710a41c1242a0360005042041010501c000750042105080190400d2140d20010351240300d0305d018180090350700c030005070791110140d0680e000742c0b04140440300041154900500400c004006410201d00114001661440d00100401c0c070303070340d000e0310881c1824500400015090a00b03400d010a03c0070621071202c1845c0900c400d04002c0c002903a0b194410901401410709001c0300d070f088501001034481c1040342498225048130900c07142100300507601e442c0c00340d03e55101c1c60b403c3c000c0c80c2c2c18025101401140f00000028004050260340b04002c2074580d800c0351107422442c41c88840310095082d0001d0050342c000c2c5e003d10343c409011203021844210020029041000403070361 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 70511099 1250 70509849 70509851
    0x2060a11070b19030b030109061a151306120f020307080f0a050906012d080c01090b0705060a0e0c0301060b0d0c030e03071b031502090405090102160305130803030a 72
    0x20305106003004202010050889079a614035100480c481c0010801010715501c082c16181c0380e036466a40c400354004200e07150054400c01415071002090703040c185e400d10340075108d4440101d4441d01090041b044424099840d01d080035018540304084d296410810b190310102d03039071002850084011800158803610f04d40e6507410840c43c00c090a04050b11020740407040517442d00041200c8050002001030559030403840d038491200342010b01341e4800100c9402071304101294080020840b60000c0e55100008090301e40052854a6100c00c1c071003402604005080359100c0c40202e10217400c039500403089400c41c1c0040e01c030f040d83c05034042400e5031829846101c1c06440021280307004041031040e040c2e19031061505102e2a81100c001c2036580c024080060401c1c3d002812100c005240e40e490040210b5000506440c3c202140c06070340c000f50469605507004908000000d81c82d400c0600c22110124148035903a001d84c170040d102110980c12031070a44001d0a01288080f888010800242d032140d565548 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 70512349 1250 70511099 70511117
    0x10204030308180604140c190819151503060c0f0f02160e07021c0e041d1b0604090e0c0f01020d051219050901021b0d120207050a02060a 60
    0x1074000c0000000030400020441d0010f0210900d10300454803c0e00300f07420104a031100d0320208074890420252005070341e03000011000884000e88040707802c00444002105842c512600c0009440c01440403002c0280010300d00120302146100130b60194002124103d84900728645030741d12541151250000c16001c500d10140300040d9540c00b110030040c1d03800900c05030815000880e81425050315a009102d6405109000600c10303030f10811240c10100000461100d00700c0d400c050281903410380816075801a810403403540e040143c00500300c0c1620b5505002000181c000c01c03c030340d10651079810355079440181004009a119840d00031b443e040220304e40a07100100d10401040700062501c084241550091000d000f002504501544c0d080403a4003041485551011024a402c0c900e440d100510700c3c0c07600090060201d1305501a0550041d0042003070349071200e40100c1a87c070b0110803d040c0010385c0b10351070b085813111160060a03416205504865040001d9070002e000380e005601d00c0000145044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 70513599 1250 70512349 70512353
    0x4020c03091905061608070206030f0108060702070303050a0c05011d011a04060b090d06020d09080705060906091e340e07020303042d0303150902030105060702010807170901020403 79
    0x410940100342420340701102d5145480085800c0b4020384c41c200b440c05055041c85c02c2402480412107018642c0281150354070f02d41090b498a10500038061400340b845100300180407207000040303450079030b0781684940b810044044030880700380620f100100d80c0b0703548800c04201d400308004501c51410050200200b880c0441e0701c40007d842903401081d6118030b0a000f001c000d200c030480f00f2a1054032040c0c5881d44001240d080074400782c4150460280000c1c0b608221406100b540d4019100303103031242058503840e45400c114550323070b604107540540c003640010f6200c441c840c0d20f080c0885c440380401e0040c3e4154405080e07842d03079504685000400c01d40c0c600205030f0700c2c000b8080001d002030190760040f0701e200d06240c20029030340c2c0001000108401002006811080886007040c10b806c525500c55020955a82c44c0041c040c205500300c02c01b401a8030103000c12170202c039009480c1601e601030a85801c0044030b40045546002c00303005c40060004018000030200240f10300c451050780071400240c2e540d4518 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 70514849 1250 70513599 70513609
    0xb031903021c0c020906090612030301030506010513150b0a09091409120a080c090d020d11010e0102010e0a060c270302180105131d0d08150f2d04020c0309 68
    0x51560350100040a554200143d4030b4070126504103009035800040e540d5000302003400da15030124180027601c004000041005400600b141c10b9813000e940d908a006c80c100e40200988166440d005a84c120103682440308007001009000d610310b45140194080341e45100b040300300e070707000c00214101c41280420050341c4002003001040f900c0c28501042e20b0500740f0310004160b40c2016294460200000400d210039590750b9420b0b1800640007040c006041c0304a161a244201d62034809034085181003030302110940c01880f41e50f16221240c8041c00c422401d5030b035044024205d03a0045010701c10b0340301840d90500000d000c203950b000d0201c000e018100c0d080d80104901104021305200703442e40590014041d41c1c407003140f0081d0341091140301040031104041c4083c0b0441d002c0c15950801d200b18590403003940e500000c0e01f80140b0701143d04d221007045000910600910540025800c0b40001144581b151a05c18900400c8620000e90202c01c428080015040c0d0b480164000800d61000c640c0c10018642 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 70516099 1250 70514849 70514893
    0xf0a11210a030504020102030f0f071a01080a1e06060b0705100204050a03060b040e0d120b100c08071415070e01090326040f03050604030f0e01120b03190302 69
    0x2440c00d0540e030014002010416407140c0c00308a010162504007140469000302305440310a0b0b001c030840c07901e03800000800c8109030000842510200c465440104040c0106090a8103840210000d03180c041440e4480c1c04140503400301001c6080304510a00c4081605440b594026040f10100666602c001d810001d24200a10361a49681481084100440d5641d03682c0300d01120b50052010414201e48800203000b0301006503a10520302415141c03001035540701160320f00312500b09a0801c101142c48081c4041c0d8051300d075000012070700214002001c40e811101030000c003071203244030b030f2081480058610700303044082d903661100825800074010050b801c0b800b807104114082c030381811603134559220744141420700c40740d9110080148080d6842c80b03000c04202d40190801c0c105450050f6503034070f070441c0d456030b04880039400110b16014540506e403107000b01c0551b0203016950f00401031401210107000b08600c40c0c010750305100e50103901f404c2807080698030940c2800794010309082040038940c41d2417144 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 70517349 1250 70516099 70516123
    0xc0302090c04051c0201051c05061002030708030714040b120412110606272401140304120e04090507140f0604030b0a0204050a03050a120804020306040204110f0a11 72
    0x3402d01080c0300ca5203855038403030759414084129a03034000c0180010303251407081580d48144000c1c0306024403480c040300e4020b54014003045d201d401205c0c0410360300301d8990103403040041034204100046042648607a030440d26903201514540d01c0c3c140c2e520380e01c41c1180d0000395011135440300740c0704000c240300b02054a407003a440681060010603042e90000c3e600d5800050400f4842da480c03910035045030404801402122000344204a81c1d4100300116501c0881d111007032000482000c48110b80a5101e23019403031281c005c0c440c0041c2182c41c2c960700e072440c1c0c04e0708040e202c041001e8843c02817102d540381d000d4031041d6801032003d00000341c00c0030340d10404040d0101e40d00e8060081d821082c801a2142004c076021250000041c07200c42c0c1702d08480300081e2199a01c0203910408003078020060220208141c5403a611817034900700d140c001c1400c1942c8103103048030041d5060f0012000900517051a801080c0303144880c2d49000e00d00f0119140f511000d4000c40400c2c4002000e44d01c0506c8038001c100580c0031001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 70518599 1250 70517349 70517371
    0xa02040b070605090f010e0c0a08071203030f020904050f04060f020406020d0804020a030209070f090e0601090b07020f040509010b09010504020705061f0e04082706040504091b030c030209 82
    0x140c20000100d200344503940e0300034000d540d81c2d00018102c034401d2040d0364141d0740002c002d1010565225850f5501e500d03000c5d0740351150400210010f0203510001d02c0c40d04403217003404982d0b84207149450039001441074044980015070208004551b683d260b1042ca1310034601c0c20324070280750402d03041040444840e521041440d502c104001e110184e00059000403161191034070740c2869540740302242501c4100d6200039003184825090080d42c0d500841020410b170b01941e65a4201540d40e0345110f601c46003699400d0126500c1c400c01d0003242c107080e00030014640094911010a2040c8011408554088860f06541c0c3d40d06d2030602d011345001c1200301c1c010003040b00c2c15810066661105034440c68041d1500d00fa0300081d0084041c40070b28801400c0081901d164070222510300f6040107000b680c232403000c6c1903000001204054201114116407200781d04050320361801c00b810541800020000b494095030002c0c20320084a401200031201940038522855030140b0982c80c40c814403030940f5020f0138040c481c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 70519849 1250 70518599 70518607
    0x6031a0d0809060c010209060f070b070306180225060c020d021b09180607050a0e09190203060303070501090f02030706050337050a050f07050f0d0203040203070b04060e090a02 77
    0x4105000251440b0b090100d440c00c1e500c1075407040d2a4020702c2100881500b0080110340040f1044002001c0d00000d8040c10980025a458a00880c202c40031030003507d001c1e8118450f030364441401036002d401c00c400341f0308403400011140bc2d1601c41158548100700d4543c1d858600c0d8501c8686d040c014414000a03d0004010190350741c4112600305828141545c06105590000b40300c104802107041c95140c040d01c02e0f90054145900e00900f55400b28980401180c00d03040c8100c407070705001119038894880d48503440030802d542d200260196202400e441e602d440700b070103c080410800c0c490403c01d603100d0443c43d00f0a0086c2d105060402c1c50b01e40c8a201070200034030400800303801000c91070454000305134012a618107203100c8034444072005000c2402040c0f5100811030f900b40f04d42e02c13540c0205c5102c440744202d6a84c10b2800c5940d4414000750f02003104080c040d80e40f00e94903c3d009140c120f880182520b01c0251107500c54041600f056002400142c08202501d100e41844006540c0104500c00300394a4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 70521099 1250 70519849 70519853
    0x20310060b0405040e16060503061824120f0709060501020304050307150201110408010f060803030709090e0319020607080907030b07081803040602150a0b0d0308040303090c06031a0d 80
    0x1d40aa4403c050090383c88107070f00810014117001000c1d00d100d60b0035100c9030311900d42000520310b820488032a4001c0c1e01604041114841001c01c007403051210b1881038640032008485c0b91480c0b1600d02400d60005903140b08121461410702540002c5190364005200c0d552800c0e0165003520019482581507420801c030500c142d03280455580180c1b05c480305c400d220010345000c200d0050550200f000440c51001c0380100d10410190000c00e1030800c100014840c06448a1603103481380320a490341000301d03480200800c0804041d4001405030a450b8003038a043c43c402d01100812038228120320f0005810070700c02c010340d054002c140b4540028800c0c004000d00ea0460f40e60117404400500000d00348510040000c01d408982c9a038107901101404c1601d440703a580e8a000303942c804402416110b8010f04000103030030305c41180300d8203080f00c2005112546c4600c041d01e0a80c1c468401401c00d808164503510342002003140094030350003c103025540000e1401080a11625244060341c580b8841c881880e52440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 70522349 1250 70521099 70521119
    0x140402010e0904080d02071112010b01080a0c0908010e0307051c12270b0901060509060a141504140a06080702070e07020a020d0b070e060408190201030b040e0a02031006 74
    0x80080c0180c452800c16215030501500c11700451001c102403500000c0c4880030010600c1e940c00c2100c005503600d004840c01d084100e401c0e9407501c07100b00e000414001c00600f10000981080141e8092800c10490303240d182c2058500750b6003001038044035035200103410810000308100d151640380210041c50b880342c90450005080301000381400c40b80d940c440c030302c07016109031076040c00100402920a4168011f142e01d064021044115581000d07546071034400501410449401d41c4181d0300209848e907404d08150841002d0345154020503001600b5003840c80f0500d001a00034409003003000c4440c807503014207800704130721048540c00074010440300d04144070301941c0000d000400c0d01c60a50b40d4072402d54900701c08920b000c40d0442c0c041d50201c850402170017400305103080c03a80121001c0d44d5000316a0100c2c02403001e584254400c004650703114140c18100c1c1c2014040329404140305240c01b040701000d032030005040d6100c9070201800354105e00514421840c0c00c0003403078480059113000f4400d46241c241c0c402 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 70523599 1250 70522349 70522367
    0x11b1a0105011427180114060708340602030108010516020312042f0406050102031213110d05010c021005071b02191502070e0c0403021c0c170114040201 67
    0x5803464110307203014504e003083c2c0c1d28000c44d00201a0504600400c1c01c840403091341c0007803180300e404a829800185090034510220b41c1440e8001404524101040200f02d58014035070250100210008280c1c280100c11248102e00aa00a02000d0784075418041c546084a00140c0700407040b00d150071054295540200694440c1202c40b2184900d55031170b81450368001c0300b00850030000c840702032000700d88600e14428585070b4403001e560130030410381c07140c2c0107a0b668858034510b03d049000203000506420340c440e03a201001d600ca080c4071554003540c000400c0260944610849159440d001c98101d2254104030030300859a8260381400300d41808034020340800c0c07442103880d101080f004042000d40d2a104500d4000c1c0b0190340c803d54100c0d5441000480b0789001526038401400307014030001e9040310100b5214025140450000d1800e841c59080005809122204081080c078400540f00403072a00c0d01c8070401081c02480c40c800214281c107055085600c031107540c1248848100602000d40d90080b494 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 70524849 1250 70523599 70523617
    0x51e0913030e0a0609120c05030f010c0201060807030206120901090512040e06090c030601031d030d1d010905030f0d090c0b0a1704050c0d050a120504030201030f29011b1a01050114 79
    0x481c10381c06c014100303402450742c030341c12650b094411300030116070403401584070400c401060b038001c201e80760312070344015243c0b0001e200103075000c2420b0001e00e06111030010201e40242018000040030070303260392404d0500d079806442880303620010030100b164894040885a1100702103441c900145044466a03649002c0501714504141d42e1f070b802c0507070340602901400d4800c41020f0490780c031074203140d6091002c0e11704400c1c0005021300214011340034004c14041c1044017603014010303505018140310401610341203045101c01154a4080e020081181030b030070071000d03001c1d0400f5165520300304503026052810f242440b10308410084100302c089000492015800813040b20002041c6c542801d041d4507020446801420003c0024040c484603504280208100c1c8e2003030702c09103c0042b40103480781c1281c3d03881c0310304034a44010031407101c00400d00d002c1c000c4420b07005040608024481d00250011001d1104013100e04408803c4200c02c4c414000c0031241c018902480e202014030150b0742c1d0300c80780e8040c4c4101c1d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 70526099 1250 70524849 70524869
    0x90c030605070e04050c0a0221030123040516020609030a050304060c0512010b07021305011202010e040e01020d02030105031002070201050a05030604060e04060f150b04051e0913030e0a0609 83
    0x2080c0b019101d2901c60494410040c82401039082c61a01c801590780203002400252080a42ca850842014544a00250200307280e29007140e10340035114070718038000020342c1c140460341f000c08491503640f84141e902851440c0f0b0240b01451180c0300180c5041c2c0050020002a4000e00039441c3d0a0f9200085070340c03199010501264000c26082c0584240c01703805810a400081c0400110340418207002800a0364001c40e031485c8620114a122801c4a000307010b00d1a4803128400c0c22005035004865040d4040c8000c1c000195180c401d402950072078005000943c41d003500000100a245000c1003800c1c1d01c1341c856282145044400d5002074041d2081500c0c00b0280000400092800e50341e03079010307600910880300303e9071452500e40707000c80003090504100c200c40c0340b81c46081d030501c0410843c11804d48a00410091801d41083c08004070f00c580c1d00d20700011303c012001803410b680c442074081d6020350b9800c0c131141c0f0701860318500074001f045007081c050b0080d8005d03403007045156845540d900807100c1140c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 70527349 1250 70526099 70526101
    0xe060409020c0c03070b12060f0607080c0c0306010f0518090c011d0d0b010e0a0605010f141306050702090108030903070b09030c0301090c0812030115080907120803010315090c030605 80
    0x20009007400c0c3d40c0407003035506004d02c610020354840d0220040107086d0341d9001740801a075482c000c0050780c07141117598503000a418080d490025402c00c00800d00100b00300c04581e440710951000900c0c0420982201c021701700382e068100301d64103068841020407403540c100c15055181455090380c0e030380b05001440d81003000c40343c44004203d1201c0320303200c410080900140300200d094205004200000c0c8210500d4000030000079102c3e002c3c0344034090986005a54115010201c0002241c81070720302002c02070003074030800aa00056030281159002812107803100d60f11034203140100001c840050b4071544107a04100305448255034041501c005a40141c0c000c5601c82e400c41e40480c0c646070b250010507030150f117001085000d00c90306815078021202e107041100c1e941001805ea94010340404e200d0609402c44591140c050140602c0c459071303000d40380b607080711051652080d4040b03122280080903a0041c00020051060290b0703009132800c08c1c4031807201070106480e150b440c00c1d02e108030ba20014000a607244 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 70528599 1250 70527349 70527367
    0x1101050c25050a050c12010b010e060a03020f03010305010902150408060106140403061401030c060309030507020d050a02090408070201030f05091c0201020f0408011e06050a090507020703140d0305070e06040902 92
    0x24800900d442e04041150300040c0c240ca000b507078409041d81c00f940300c0c0b81c601807a2442072405025882050606944040401c0c0c0c8500621226411500348401815000d0055040d0702c842e05007d10b008501440010444440c00c0c0140086501300440880c0c000c0020001800300d40c00005003141161601e16101d0b980042c0000060107134012504001d0002d0f04212030070308000185101241130f2070045600030030007540c07441d054044400c0c050004022810501111001d850f01d491400110390182d026502d10048982c0040e0944000b02da044034034903004150074083d5641886005181c08000c0c108010303905103180003a0f5103501c01045110105918240e01400620179019035a00d00c100000c80e54981d40c07182c042c42d000c0c141c40c0c1c3c01114485c0d18803c000402800341d000ba030007207031009401905030600b851052406081d00034180d8041d4404c9800010004402040b0f081840303c400c1301409011007868002003d0b540050300c480b04001d07560b003410300c660782c621045500300c480c000c00042e5100710300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 70529849 1250 70528599 70528657
    0xb041415031603060c0e011d0105031009150603050c03070503010b070501150b0a140f09190806070815010206060105091003060e090601150c0507060e061308030a1101050c 75
    0xa5801c82d20110800c101c00400c004c07482c0c000f06039205003621030741440d0508500449090f0b10700b0030461680d0340111500300c1154014002142c1214031520a119540e85400e03840d41658146001603a440c0d01d90324081140d04d500d40306403908002c10420306491070801490052060006016000c80c41c840040c103102005025070004c2040c2c985100100e40850383d40c130402805412426280010505d9800c0b203102c0c5144007000c03104c904200c3c0704454140710004080c0070011101310140c1000b0542c00d0008075000c8810807401384152916920090640f91009107131a5640c042c40d03c0342c1c1554030150501c90240e03004015204015030503103445141c4454450118040c0074554055004219040140401c822000c42c10605840d4000c0b00f10750071034004030080ba071600701a907029084ad00411810701c0f00600c1540d140d086104003c1c0118202800092805440400d650005186500005039214000c0d001060001041c00303c1d00200928901185603450501c610121402500890b1083c01e08450321 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 70531099 1250 70529849 70529863
    0x106020d090b03071409041b030b0102030405090103140a080d0b0f0603130b060316082803020a020603070905031e06010603020a0e0d0201020f1b0f090105100f05090409060f0b04141503 81
    0x200240b00805401100c6103078942324040101c0001c3c03c04a03101d002d54000000c07a0700b12070000e445100301d40c1c6552101c0001065651042c4a1400781d940c44502080d60782d400350402c00e07844540014030511041c00c0210a000c894107042c00b80c5010310401032100800c1d940d032903000d50046985034050341d54100003400c280c0495074110040501c80c001081e40400090b9488420b5012964504841010710410440c00180b182c0200164080c803038000060a242000c0d507000625810000c14040c0c449000a0400507c00c0070b40c080d00d0030044a000883c1000c03c401030060049003011894101030700801403c540707409054600070000f2422820071a4400c20195181404035003d070390a40142c0c2c0a83c420b05828601418400c11202140510500c1e003401070504850300188214500204400140d842d100c060800800340201403018444d10b848901524045511a040018100785a41c003040112055011440e00603031601c140070780884100351503550003065460b641060050140006880e0147c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 70532349 1250 70531099 70531117
    0x10b060a0806091e070807090f06090509130b0c09041d1c0813023a0512030f070f03150602030706060b0a050a1125030308070201090803151212030106020d090b030714 73
    0x3072741c600003016540944c52800f9a401180c1590700b64407602440e150003021950064208100603001c02c806980301c4000b003044c0b07a000382c004103070340404d000c4660145014202c540710325000940211581c600c510f0b582203207480641400751043c14002c2c0808120010001c00a0007403428140c51400401c124980ba801d40400c40145032410101c90034420b120360681c10b003140c40c0c1c418a0b040987c0c2540c10000e59100c0d854654682c0c1a42e9604201114501449292042410b5031620b20004a0780101c7d4844081d00c03017500195a145040e185c0b017400c0b03034080da210148640050101400b8541d200017100ca03c007025241c003071042c9003000c2600381001d044c545804010041011980514880b903080300084130300984a8a0180d52070400903803d0b5401c0c0070005003041d00402c0020300c03a80c1382952102c07100c1c001805039070783c1d03d000c100f005242c0110900490100b1801200412a1550401002402c4581403034484519490607000348090b010103081c1d00248100d580b07051501608035015115408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 70533599 1250 70532349 70532369
    0x83603040b070203100902060906070206090a170c030a0c09020304030915021b010201090c0515070b09060402090c0703080a0203060d050a0606060e040902061902010b060a0806091e07080709 83
    0x96407595400300941c80790340228001e000720600901841010310031280c00540140ca901c2c600070071801085a02c0d440354004903031056040c02000c03402e4403181c100074003a11a55110704504a030440b2580d15001c80824000d11a81c070843d80000000c62181c482011213000100c056205c0c0c58520301a1951603558100585041c003034900242075580c00106c4a54803401e480242e101030310081c0049007602c450305405008821450f000304103605007401140000f508801480b030401d0260b81e1140c0703c0203000d5030b007286a0b900401c203000035840c08903c03c0c3e030400c1c10302c269245020748941d009801d20742c0041007500103941c08000140c840c0c880c5040006480d40c8401901c100e9441403a0080c006e101c14000ca00000e0400400e403142170030300744100070304986c0040c002e9003412501da5516050741d14070305824085540f501c44e5451162584409030a84025644400702180b40c40c806000310302030700820300c400d50060f00125002d2680806050307604400140f0742031509a03104481602d002803207500800d014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 70534849 1250 70533599 70533607
    0x140d0c080a230a120e060612030d09080c0105010b12130f08210106020d02100f0902310b0901030b04021207090f0b030106030519030908010c0504060f083603 69
    0x4040060010f0548034840c0d00c2d030461004024400314200d420003102c200741a849000450075070f240000401c1c0385802c40c1d2007103d180903210400c85080c1d40410358100d50031035011604c2d0442d103c0038002e03207000d003482e00305540c10040f0703070141d0b10b041a0003c0c103590180c1e800c10260402340310746808402c04d11078011182c15036800510000c0c7e1081e40c0d0903082c0704110000d900001c540c441c8041181140007180fa40100340031410001083c00902d500301503006015aa52075010040e03c0301070102e0340c1c02841c40fa01c540c030113083c00300310100011000c030700481d094030380626280c495482804890550760840424407180d950752011a1034070510a4440301c49101e000300000d800044c035000303e0740340b41801c0d80078445046a42c0c00d01d03090310300b00c0c040105150000000000350690344207010304c4450003450501000daa5805549003140c800880300380020300001010310005810884101d8030b1005460311102503d840e00001d03144041e5001c0300d00300302c0118204c41166002e02d030200c0b13aa0503818415241d803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 70536099 1250 70534849 70534907
    0x7031205060303041827050610060e04150e010605040503071a120a09020301050c030a0b09061305070c060228110c06031306051006140408030d0b150c0a140d0c080a 72
    0x12070207240384111f0786403042c400061005514a406641100c0c40c58036055000504001044080d01c40315a0480d20f81d02d44200020300061043c008034020822a10780c06d40d502c2c02c140504d402e00c46580c01254200303030607010000d220946242140d03011400724604a116488202e00c5401a240001010358550708000500c6504003807000110b00660f01080108000c001c00c00602800c2c007412291254000084c4c88280000c50094000b6a44100149440241600c550b900d40c0100c1e04030704d00203405032002c0703080c103030104203003101c1c01305051920305040704403465a40e580b640c0e0307509480c6002d0082c0e40110100e02442500c0740f444020650290040c04603240c60018281040b80c603110315000222a40100345090860004403015201100d014515261389a42204064000800140d8001104240e10150540716070b02a0000410f0302014081c0740e9018282030002c0c1814401c0182e00d40c0041880341c40380350b0401000c5005a510040f01c584820000b04280c2d803103208180e010104a650741c5880308 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 70537349 1250 70536099 70536161
    0xe040605010906081b060309010b09010e0f0a09080d0905010b040f0203090c0103020a02030301090e1903030b030105090705030a020103050c0d060e012c04081b1002070312050603030418 81
    0x7069a503500c0e0100040c99072560420380e192200341d400d02c501c59020080216074144030000b15400326460001050482c044004070741c482d2401d0780004106040b8a090010240742004c14a8101301b101409001840c8652680c0e0002d208501d01003160aa0764444201088000e4205000c080701c010030070044413840013032020196104880032150b900424900e942030b50302920030398040c80041d40c0203604681c201a0036030b0003444070b20601c0d02070380700d200a0740d030b5484151182d02660a12982e400715440000380203242c20f4440240011040ba045a80184142d4a0014001130610f0302460042040d48070300a2002c44c0740700300c44d124014503044c0003002c1940004850b50714103d8030826000b003a08401007880140c00d50139501c5011034040282e0110f008036010002901c40200007070100d210700201144c0c0c0910704450124504001600480c00030103054020340302031a510300c0d149041c415440c040e40000d89074070445c02840c00011210542002402483d841000518040804a001902c1144200c1c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 70538599 1250 70537349 70537351
    0x2041203120203040c1211061b010507111b0103020c0321011202090408210703060501090e01081905030412030305180a0b0a0b040902091005010f140a0f05040e040605 73
    0x103404900ca1480d001014003080c42102e100d40d4010704801980703410103650703440000d42420151440c159500130001d187e07403900d005000d00c1c010000d0400c03024050081132800e5540050040040c030011440c18403408101007095000c25a503a00008904081a00141c0090160181854a0b0321012030a030803449454a14800b1110300c02404030702c5c984ea295480b00c0340c1128006d0094008072504007040003e280c02015000040c2d07001c119003c4506a0910401d02070b50841d80840040e031105820010343d6003041c06503002c2e06280405212540c18203540a40c0c130301c10300044940b106a01200841071207818416036000c0d00704444d2020312818281002000b80005988901481d880c00c40404a5030340c1c0008ca0140d41e5612608000e4203a80d034001000040c0107282c1d00701e4000b170719034500800590301e23401345078030986104e0244800c1a08103000142480c065005100612683e45030440710700e0300c90300a9071a4200c00b803410707000c080107049013261580a540d100c4d4001001e00c400348810030007103410032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 70539849 1250 70538599 70538603
    0xb0703090b0a020c06011e050607022101061404180b0c0708070b0f07030b0906010e010e100201200304020d0b04020a09050a0f0b0109060509010302030405070e0708090c1e010c0c09020412 82
    0x60b1200c3c0d03220440c1d07c224031901c5c1c0d5040074880c1155000c00c25810700d41c1c041c052490008007020401d48000c08900c1600700ca0300c88401305030f5540d20003802101307584e982003d0000010389040204501000104080240c0c01074040e0040070716400066810592004981200d036022003855141e22151030207114818007610001d403010b601500140c0940d10900c5005444180203050704890f0701d544c3c00640b000108400003904000d005680c018141e210100081044100341d4000605420508070500c19004c105a407030748003000400900c00942d5502d035840f05441c0e0803006d0b907003481d120f520000720b000e552680f10386009410b000805c920114594411304812003003180500031034140e80011139122810703025080c0426018400021076510035805541e00900c01c0c01298038140e140c2401c0000c0d0038040300d0580026071002c0401504003c180940c804e0103078191003031565084850950003c48048055080c10440b040c050001403101c6034807014010f0000110455941da01d42020601c040020902 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 70541099 1250 70539849 70539853
    0x6050d030f03110f180103060b13050f0604030b0402060313060603030e01080901050c0a0e06130305030717070507060f0512040506161b0201030222180b030a02010c0b0703090b0a020c 80
    0x201c0b88528100b904507540961204d000303d25182144d040c0d222a14508003a00c0c1c10075944050200d9070b450303400010009104940d010449aa2070001001000b5110042850180c0c4051104000040141426a07003207541100c1c1aa00ca0ba140e1614580403050403030082c5c4058180180041815000200c0c1d1902407000e0381c51407860f954500c1c1c1d1500b659420b80382040c80705000c21a6030600c0b4843c100c154481040100400d03c0d1040520064128400b582c0042c1c0f02904002030940030058058645100402d00d95035890030010386880311500c0d07040703501c19001400300c40e000840a0034420400c41d20000f85400302540c0c14102814034590351b40d01190003020340352040c1501c10f40700307000342100141202003140d4203950b0b03801a401107010b900201091202490031808020440f0b020400c41c4d0058099455030010a04e406a6041c064070325040c1040d010f5040203003100c0251341d0001009002c950800c04180ca81d443c0e1900840c0203050000001d0010941c03c020710603504810f0300100010400041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 70542349 1250 70541099 70541111
    0x6180b030309100f1803060c03050105101202070804090509010f0b0303040302030601030f06060e0903030a140c0304030c0c05060d020c07080607020304030308091207120f0212090603060406050d030f03 88
    0x4245030380c0344503218620350b00c21140703d80c03420b40610070070f0602480c3c0700a14240b100d0f1040498141402d24003a0812103806444084030820070f5414400d06004003800ca0300d41034001c00c1e01c00b002d0b001540000700c540010383c0004071182400380500440d00208000c403410401440d103889903034001c0a4400b010080d6900780f030700c10700740d5141c00001e880070390340c004002d00343c1a4a141c1d200a00c403069110301711182030f10b8401c00200d000c0648440741c480c0d00e00a003d0340d038030320b04845850126450817040150700aa0b00c1c4c00c1c00600f091003411b8a5010394581001822410242010428404260f0149500c000d000903c039954820540152201c5441d0744102c0703a800d03854480194035800c00b115410010b030f2043c0300c10804288140080342d0840310100540700a50047d40d405001c0da441220141d0340d40801384c1a28109650001045044485e14409000114480103207003581e8070034024034a20480004c804210240e44692160000b004001d0481c0c003600d1091030040c242407208100100800c1c6044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 70543599 1250 70542349 70542371
    0x2060a0305041b1406030910050108071712180a080105090a0615062c0d0309081e070b0903010b10111501050607230607090f081b060307020a060618 65
    0x1100503c1914008020611060005014491075400040c00c4a2081c440d004001d005140c0711302ca0b0601178402e4401400c240344c1050b440080040c0e4187d0b01d00c400d98415001c00c907501ca6201e080c1d84443c0c58005184014100e143d0024249021b142c10615040d442c1205201c50b110000646550480c412a8240302981a003250505510a40c0c801c28004c6140c038011424101400c6030a40d020f04808454090f1922130380c00864001e804400c0d045012031140d210a000007201000340c020004003461180500c2c0b0080004a0b843c4c568500c9040b054990114111607140d03801c1d0000105104090401c5c20b541460b548010141c81d109107030700c0428060f01e080441c500301003400c0b81c1c0c186c610140800345000701c142e807809444440106500100c40814403102e1651308140100ca004815075590250031070b0501085400306109940809000d50100032900e44030003400c0143d20f00880100d0700b2075240d56a04106034104164004014002440c180000c103111400500b0710b4810007021070100031b0170080b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 70544849 1250 70543599 70543643
    0xf01051b07050a0303090c080102180906040b0117071205090a020f0a0305070b0f0702030d02010c0306051804080307021c0201090b0703050c09040903020c1804050f03040b030f0603030702060a030504 87
    0x44400501583c0100002c080400d0107a0072a804441c40340d640d00d8507050f0f4428400e822a0000340c80c90900758403820030200580390180802e0341001c800c9408014030454003001030020819046400c215504801c0001d002e40c0c001c2c0c0d40c1080061020b1414040c6150417080c981e12541c000c03401304c0c456145040b0344e03000d40c100030f0f00031401d072a444801050010300300b80140e00ba50300050112446400100202030058030305001a40081c4019000030035401e51307481c80038040d03030410b4120600840c9030401e40400900f07401c20700e5800907003040c00c459480d1600741080b03090480b0454a00301e19400c61049054196056000101040c0140c180740581c0d19102c204074103895007601c6401890340144500c0c40d01c3d1505500030524548640100c0703500f500f5100100d43d03910078240f40b0054207023401d010001844000d01c201550304014a01031444d0038180400c1c00000d0101600702400c843c00e800004006850400440c2c1e00103800405c0291280008040280906012074040b208400103004032807084040b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 70546099 1250 70544849 70544857
    0x120405100905060109050910020f090108090c03030a03020c03090a08071d1303030b0a151107080c01050307110106030519110d05070b0c01021c090c1508010905060f030f01051b 77
    0x1002c40a40802e03460180018041c110180c0b178124180900d51010044126a200a25409456074107903512a407205001509a510040c2907440c0da070452000c100141e6004012100030212508005841d0781010031424a140110700406822030403654001c01d88540c00203810080b243ea1030b000d03060110605808002400042c0c1d01c0f1452221014400000240a500000114080682035014160351022440c2c0750000120303000c0049181d030f0301100881001408405d0142c00341c2401444800181000245180710007030002e0104a080e14a00c60901000e40007400115005011034403403088403c121798011005d285c007110681d01b480e45417481800d29012080d171281d044400f500040d4501410346505522200340c0c1d104a5601300243c840d0800d60250703808044100ca0350028141c0c4084c9000080a000d40c4c00162046a0071202140314582c40f0404506440861001050035110301d00030440809081100b61750502072411000951001548072510904203503441003c28900403881c01c82c0d0f072203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 70547349 1250 70546099 70546103
    0x5040302011e02090a0626190606050403020a061103070606090c0e01020f0c01050c0f01020715051003081603030f0203040b0901060f05060301030b090a020d05010c08010608090c0405060f04021204051009 89
    0x656420401c060099070801c5000900c641f1000d9140000e4000c008460002c540c00001c02d000145003091410044c402e410103001541401880e02c1c2c21900000c10400032442814100700d102c4901c00c0b01134a0600c290340c20300b075000c1014007280b920783c11071601406101400100042a00d000120f0300e610000d540011000594080c0a042e1001e60045490790300c20070b040075091050a821441107042403000b0304000780038069440303c0186020b00001034480141440288414981d42403003c02c4c104411a1280001141a44180101c0307180c05d4000e01008060031303400620200c1084140a0340f45980d078410908070300200050394503480d01ca03c0c581a507019071074110710144018400144095441f5400200ba40b00300ea1802d02d15a00040302c0412080301260965150402880d11503041585140036144604040b43d0614003070000b0303a40c0c1c9140c2811240b00303d440304003081c03440c0c0340d0110401c2c4a00c0050015035903001c401c0f81a840200058408507540e10584036091028800c40c420800f24603 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 70548599 1250 70547349 70547359
    0x31003021504180905030c0d020601050901060f020706050d091e0b06090c1204050f0d0507061512020105071703010f080f03030403051b030408010204090e2104091e05040302011e0209 80
    0x50f511800010410010100d030284010000c001c44220304101401003c54903900030304140d03040c0703003d01c42d02c100107030b01c40c0e414824038928403000c554020410206445a5103440c41e01c2d0b0480b20701d2200540990100500303038441414010102c03164803c01158498040d9400039165225002848680e0604403204e403601ca006004522040082c42882c5070060300400440e0008105412050300705101c1c4004103002c628005400e600300b0105d400307590503140c1100c0310b200009140c410802c0c0382ca5007800000f4108100001ea84080202c024031008001880d8050241c503981c50b0000754a41d280d25000d289400c0c450710f840c80a094900100322449654550349550901801095049100e040011301104031702081c00301142c8250248060801880a00ca002c10f6403000e040040d0705081c0306418102595480001e900f50b500d110408940c212640d2700000980c42410580d200080c4800d100380d003512130f00384030074041455815004003001a09006042c40301520300d01d0100100d100304c410b003940007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 70549849 1250 70548599 70548629
    0x20f060402030c130e030307020c0a0608040201091206020d09080a02120301120b09070b0c011a1008070f0207081e0d0c0c060806011101050a0c091e0909020411031003021504 76
    0x604101c01c00440a5200301004100c5c26802e0105c181950022138170b1000503805105100c1d5903180503080c0034020070751410b08003a58100f50700024032441c000d016a50880003061144000c1041c0c40d81154000402808208100c40c1180f0704962036911100d0744030014822584c848107607038291002c82c0d04031034207581e42d281002880d58a001c80c190008240030040d0140d2840051550441d400900d50a040c00300001640d110505040240c5061030708100c0c014000c1100f080d55442c0c10550003500546a424500c40c003140c480012450060950040581c1d40a04a149000c41100084044a40220b401a503030300c2c0c0c0805a0840300f07807a980401070865100300300200183c0d03028815303082c1c2107141890128902900501d6450944006848500306141d8403031100d01c88981c00810200500003402103205420b44800003020340e11b11901a0040aa50350140c0d0340466540ea80308074807600b40550000e459240c09925515000c90510082e13016401d4182010044d0344054100d4050310615070a00b140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 70551099 1250 70549849 70549873
    0x21150c0a08130302070503060f0a1406010804060e010605060c033403030c0306030804240807020a0b1008010908040905061009030308070903020901290a0c1e08030c0a020f06040203 79
    0x341d00c4400e00a030f00b5409811400700f03542c2c400b40641c0d4440c0c40e030455402c5241c10182c0400381119018814a980042d4640a1007010381c1d201c08003542003600544081000c54404c8000f500420555200645c80480040d9000b8014404805000c4d12642c9180c040410300c00c0059a440443c940d506107000c200c9642840030000340a54454910041c641c80d000468940f41d0340c075803105034003a401103041c42d0442182409840e80250b10301400c0e940b82e01e01180769040c8194040e645030403051004140004960020b019410034130341401c001c00c0048000c2c400c44219042580640e840b0b4050400e4482c10003000458078100344080600c0c040f031075a695805a491038804507a0110054105c0c1c041040d0f9100c000003607507400c1540c41c040c203040315510451408030035100c00c41c13052283e082044a9400c2c4080d61403150080d0642c100300c2d4011002c2e04140607250385000c9004a00d42000709044004000c2c4030200c121074003c4d114001e00d80c0c0859a03e50300541c1015560501280c000350700d60701211500d20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 70552349 1250 70551099 70551121
    0x3010b030d0507080909180f011e0207031103130303020f0c060706020a05071704050301180c05060901120f0b0a05010809120f070506150103050c040b0406030b21150c0a08 75
    0x3d0043d0140046a041c00f101c800042d0406005031a0414006003a001141c6102c0c0706011a480c4500b58078020045043c001c424600d0b070b07246a4444c0c1d90800d07801308000c4149400b03000c003182180500c1069035a2843c0c0c2188644d0780d4080e5020640c014031845c03044111100c000908086441002082d4030b0030011907544100c06540800215002c0041c1881000001480d207048100e041c00403070109501c8609110034503007128042031640c0030203107d11a0b400c000c140d902e40f0000a441d03081c0c5075150340750703078000050700c2d0b960044c80c018400d41d02d0500404d8180d80607030b0210062803001c541502c03ca036034513001110310802c2600d00300416008107150f08010b0302c1f010010002c500c40104003600b4108240c44a03802c010048030708808000005151105941e81446030503848103541c0d00380f038240b500700f5000c15000d008078000d120074035a4600160f50a6602d060206601180c2000d44005107a2240d0394030703844003070002245075150003520120782501126419240c001c0802d644052050380c89101d862 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 70553599 1250 70552349 70552357
    0x408070201030e0a03030c0311040f030209060406030b240111030306010c032319170403050d02090603010803070b2406070609060501080d020c06040b04091e1802010e03010b030d05 79
    0x2810b00d036580d07101c441d9000c41031009601c414020780300003030b0742c2103218005000d46004c48142c01d85084100820311a0013010b00d4400c0503640c0690f0203415546e20200818001c00075a08054030b01070707641041000c002401032003005000d180740c1c1c0040301c014000c0c00640d03c960070281004040c0c0c10502c00a20154413585000d0750040c02440c005418103224a10300c042c00c4801106448c80e25400140704c0040440072802d019070702d24619150708801070010300380030000d81c064001001c0007800180d00e081c511568041d00d0300c0c1c2d4030040c503c6a903544d450b096655642d10070441191217a42d030b00c0008189800480504441030b11004010071483ca10030100f00e034940c00140c1c1103070559903404101000c5800c0c0d00c251806054000000c2c03009000c2403001074606044050200d100700f40800050129404040544040b1120400b001c00d403e07420701400c41c80c0000c1c80c4c4000c068649840c8468000824600c0c0c0056454004e80b074140d55080090140760a82d0302200343d00d9059070000421203602d6204070010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 70554849 1250 70553599 70553603
    0x605090402280c210504030311030d1104060f03050103050318150a03060f090204180e0a0b0408030601090906030c030f0206041505030103021302190e0102010b0d06050108010e0303040308040807 85
    0x1100d40320152103005518042c1600007880090340003c0d02c0c10400c02944002d01030300201e410001210300c400c402c01421031141e400014200703c080e090303110b4044010003d1b103007aa0b107200d0040c841130154255000403904280b007800001030345c4008083c44240244030b40341c1078070b40002c082c601d45a801c0c51401002149401e0540e044004a11370500008080002c6e16800000d40c0e0302040d00c901c0d04290b00d030f800d50541c01092003148100030070807254122000480c1c00c028440350200c0d000000c3d420383c4e030a2420a08020b001ea0103203504110421100400461145c40c098851405d60b80d220400f0300100c0b607a6000003041d0135480407040c0041510985100c3c0b03940d02c000d005600d0292142c0310480000f00c4486044017186000c0b0051007140f03000c046461501140c0d190850412003001c00c03c042070000c8020102c1440b07000200282564030030341164030550130142c128084c2004030725000e401803030244034108165191000041543c40c2c044100c80c081c903055a40da507072039104d48d2140700c80b80e4480142 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 70556099 1250 70554849 70554877
    0xd141509101d0f06090f060906060d020a020d020d23070c0302130504050d0309050c102703060b0105030402030a0b100911030f090601080d0804060e030c03041d010605090402 76
    0x3002890b039500c1c0310605007008120a0041c8642003480c002c0403448006080c807441105802c08006900c0f00303030050716501440031a0295803580b918404140644140851252524000665902c152b40c00191440900d500c40c0d0844540c140caa02c2c0840d40f05280c1103919002d140804440002040f50b840541800360003401c4030003000340d40368001600f40c40380001921685e9160b00400c82440814082c80c01c2c145524202403041045503929503889544d0b0747c4090f03200f03030020307010b02052601c00c4810380703641d01030170000720700742107030a021080c42100c00e00c021990642090341007034040d4801e0f030640c1d006540c050000d0049552a6443e1803820034002c150106004800800107640181c42c0524401c1014024005a8909110003507210502004201258562146c00108500d03000007440141016151601480f5074440d494128090300d40040000c05522000c260400b00107804401401201c61508408080680250200011050034410940820010310898615040a4004008200c0c1e21a9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 70557349 1250 70556099 70556131
    0x5070b0604060803130810090b07080a0902040c0c0b16050319020717070201120c020c0409060b120c01080106080601050a0c050c0a0e01140303040b070201050a0212030c0d141509 78
    0x400e1130340d08404141e000c22030070b0070001c000c800ea092007142402c61400e06d050222000075100c04500036800f80c020000c01400c4000519080020740c49a035100f40e0081c0144103500118000400101d02e040003036407040c0200002c158184420b1651034001102c0d41c03a03050866646030306241c202c8060080324030015070204184000140e4620b03954071180321040c503880c2c40748540c0c000184110041c140404942d45007014800500d500020b03c14281c3c1002c4501217070350216843c3c4100a003007070640c120b0f00b20851600d901404000401c9d004501030003a03881e003041d681e031a40c0c1220150703815118140031800801a541b07120b885400020b58450107079003203464014541c40440e00110b09641315864911002d401400013800e1404401803440c1c040740114200f50421041c05500d00c40c02400a040c00350005400440038028040200c00490440002d503d0b0b28005a019003140e02c8025917180d140d2812540c03004854410740b040e4002d5480040d1030740c00014030400c0c000310134030240c408030840040b16 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 70558599 1250 70557349 70557359
    0xc071a0c0102030c030a050c16020603070c0501150801051003110603250c110303040501120e0a0206030a0e010b0d152703020102071202060402130c0509060d0510140105070b060406 79
    0x1000030b5004441321003c0702d03901d24102c410701c1c086800240914011038010000044640410001c1c852001d030121460742e603c2d03c8104041d5013421070910000c116500b0a0505070640c445440c00208a6504100a05c0183c4e1030120184000c81071b0701000700703903540c1c04085108909140f005194040a003440c51448a48a000818864071002e807100002491200340c0340100030b040565009039001c103400550410b410400060201d09512641e9039405584d5081c50803034250801540030041d401030f029070741c1ca0600c196108050420351480c3c05e0f1070f41c24066224801c0c201f4071075a8040340d0708046440074129503028514041c0a5040c002401191240e072050304c01e80d01c2d40350500d0814071a400050b640d5129152000b107000301c1388034000554102e1803c00002d40c44551010703904008501002801c0c00e42c6400c03e448034003900d0910340d00400f003c140b030195008590700c0f49001e4441c4d403001a50a950703a2600042aa04242c001800100300703000c4480050013412059404c010010300220301d85841f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 70559849 1250 70558599 70558601
    0x10c020604081b040c171302090408040906051504030b060a080f0a1a0906010b220906031122020a11060c1c0203010605090f24130501050c071a0c01 65
    0x42e4100c20725a800014409042e00c01900e0024404801a94288184401104050002d800c424140480c2000c040300041c2d0b500e480c94800d400099000f450402141802e0a00f10200c2d08a8010500b44502d001d0010a15103800080d000c20074180e481c426280034110ba4510070012005403030303107411842445002c0350b00390b020311100e1940c84124004240001650614200d542e011600a42c030064181e41401f09420002c20382d28190b070748007500559502c055070200d003a034000326001003080803800d4201103442d039102d030024001c59001d81002243c41003003a081080b0803e0070000543c049803c008244101c1500350050107400404e41890390100040c0f207040c40c1060310403a00c240381410300040140380340b80c40c00c030680c13040a00e4500850640d810008083d002d8403617029a0f51140c02001c0c00c5030110382e2800040018544803012805160078440c0010a060b04000c8600503000d051301d10101e203030351050f002d998001e00380070018650039281620011074203404404188802400f049032040a40007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 70561099 1250 70559849 70559857
    0x7090c0e0d0302030d1104150c02120601081615080708100b0412030201060e010f230301290105070c050411071208010509070804080315040f0f0f1416030b010c0206 72
    0x65005180e403400240141400c86e6450700280c0d1106409000c18072140d550104031038050b04150a000044406900000344202c400340c282944501c91580045002c120200744004080c3c07000c400088855200c44820001061080c000380c0022080b01c00107914901c00e48140750012040100410090f031101a181c05643c4030b0f411400e80000000e64020070182c0c2403003000000d1004816040c0d8550425144800072820740c81600b00801005010070780c403406000c03c00b20a640005c0c02088001000b000f101080c0300004c500c1012030b03c681c000202994002c0b411186116406500f001702903090204120040281d01121182c104d4140840070000c1c01c1101c107036140b10f100340c031100e00d558905000c00103a08401003041007004089010b11000492000a0300d030054001c505000d0040581000f2900a04042c80028071003424441000c0d82c0025552145203c6079031004240100d07204111540021601070320848142c0150300c0e54640c8861082d880361115840504d0812003420f1903030002a92070308 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 70562349 1250 70561099 70561103
    0x220903030203010f0b03010303020604080702010e0a03030c02011202040605250501020f0c060112080304020d1a0a140a0506010c3801090e0d050910050c07030503090306150307090c0e0d 81
    0x1074004018400d25407041c04030802010b07855459441c560459070020348684001c0c0000f07102003008142842107a0003001d154101140c05441141c4482c0d90703040c000d0042000900681c08a284050f0245c64032909000300d405907a1981c882c4d914001e02c0110943c0101c4410710303010f05c5400086070310360005000b03000400080180c42407150b03c40c2d01e0f000e44036040c20810780c000050110119031441c00114a0781c107581e4050f40450f113141422040342403904a0414980380e030810540c4580c100098458107601c0ba606110020b00c1800b461754030700d2194801c4400c2039070594081407c1500c01000100700100300c004150041003603840020601c01c0c1205060520084001044404d20060020b001603100d2252403a4202c070003841c0d07080c6007580241040c400c00312154012860203207098490380c068002c403507074984000d003100c404695034200030307482e5004606900c4c445d010300008134180e00748807030508008950050103031170103d1400140800510411802d20280700c400e030b401c00c0d5240c0d00c2c4010000d030702d8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 70563599 1250 70562349 70562351
    0x4150e07050a03091707140714060d38040e2104180c08060f130c0c14030c01060b120c13080a050708060106051e03040201050c0303010f0e06010302030403020c22090303 74
    0x4006d524010320b408210050074480c1c3c0d802580c0c10001c81c84611240c20290105480d002d542c0c8411000d03060142950a0040000000c2070078111900101c001c903ca40149811340002d0440c0e919008000642c1d1801b054844c0b9640012408030300742441e800010751900d14151501d1900307580d01c0a4003c100683c03d080c42c0300ba55290030200000f03800c41c5040d035020400b141d0000b402507145000800d00814582c0c03003401d11ba9281d01c17030f445243c0144950084260880941c850b07074021181d005642e0760100c2800344095082c1600014540c02e201c0c20303102d0303000108a502a1035911418210103a810498030030382c005400780300000d0104424001070300e48500441c084c1401038241080f540c5821410780c00710041000800195107c100003405d44840c4407003003119030703689481d1800103c0c1c450003130850340441d41c00004000602520099982c05c2105c0801d1507140980e950100154201c2c0030403500600981c102c2035911105141403042c500c40aa2407120484d00408031401e0382c0b0445061590441c00300b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 70564849 1250 70563599 70563607
    0x507050c1c09091122080a080d11040303020a0323040605130e01063203010b0c060601020105060d0f0c030b01090b03010e07050102030906130302190504150e07050a030917 75
    0x7140d1184075903016000581d0f003031000514216a0121511a240508200d50300d0300c070082500070810751041004000d41011a030080d105410300d000a94407400b00442404d00c2c0c2029407000004001c01d460851750103070054959005140c405841e0000040c13280c85440c90080107500c940c44001001d00040c000070f03650301e602c0b07102030184107d45c2d0443d60404800313002d42030010000c503680802e281e52070765003850031441c02503d01c90a000355110089a03550295001100201c0c0f0b22500c07002904014103210115003031515000010390807501c055a0094001c0410031a810100b07603481d11100b11a4494000c001c98181d40b600da034004942c0070703000340700e0a035110840c646a5150034082c1c0303859084004083e0031004c0c90200040d54910501e80024020030000c2000c10b00e9000408502e801590040c0001d004403081c201c1200356401e690043c54801d6240824080300f10340c50340c0440040da4400010504180c40708030083c7c0365a0403420b4442c2c00c0603203031504140015181039058200740090b107005512 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 70566099 1250 70564849 70564903
    0x60d1104030f0204050901060b0f0a0216320901050d1110080612030906070b0705070501020d05061503090c0906030c0d0f0b2d040f0204090b07090f050a090507050c 72
    0x1992800703011021340341c0c10220188120380d0f840d4211403cac4654000b50a0391690085801e07814a02c406004184521010741e000500c582c0b844140c2d1414068600301c02c1c4012a04648a14500811720040d03410044880050005050130b0014102403030040d111148201040b000040084c101060758074001103a050500000d0b0030026201400070104001842c2800c808201240700350040d807001405c102d0400c00450f10641c0554221012a50400000c1d9030b1400382040b240090401031769524002c1c1404003409601c0300c01326003624080d240b840007403e0204c50220400041c1301000d085560f150140700311056040d079452040314444e83c0f107410403041402042c14160707010300c0002c04101d40c0000c0b8041200221071807003c407a66240081c180c690944d02c4900f0212401d00c0008002500585041002030a01c600e0904592141405ea46c640306104e8440c0d0001030003044900c03503640c01170300005090100e00b00d01d0f041954404210300d011410040e102403100c0c5081d8070308065070075000d040b81004103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 70567349 1250 70566099 70566101
    0x106050a0f050f1c0c020106030312020a03060305240c030601020307061e0222091407030527010b040c03020408030904021b0d09090c0806010819090c090e070e06010806060d1104030f0204 82
    0xc000c5d000c0d400204215440c0d600c002d81000e00611900c81d0195001456040d81400390380000003841d003002c21034a080b0402d1205940c044000400c0c0a005a041e400162000c034010301141d108400c180d010b0340c1400c00c00e0f079811001e8002c03092011a04040b00c0c510300340f02c10151000d07046035295111582c5030001c80540007203c1d044260050080d05083c10740381c4000903d40102c00350030101c6480c3c002003a99500e0300c1e0042e14010307503c1a503c1c0202002406403c071a05412085c0d419200300c4082141e1080520254224443d43c491f51466800034451404681f0b019809040e002d02c9040c1e56007500c0403c1039403203040150062410010034180f02d028440710310f00e8402e032051003109007001a07032818180000303010500000c040004084005a110507401165004200d040350f01c03201400034143c807150080040c0540585040b5540b040041c00610010b0b450f004c54010981a1100c5000b6220790b07083c09a00d80c0482003c0513003d45803401080c00344c8548009000942c020042d80e80c03011231600c1080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 70568599 1250 70567349 70567361
    0x204060801091406130906020a0504050108060d020127080d052203050604060b01020f012a140306010c020d0c0803030703050c0c06190b0409050a0611030106050a0f050f1c 75
    0x2c0c200038984201501c90546481c2d02507041a411034180d15045000340000d0041c00f00351400408060002c1142406c66401c030740908291482601c44000543c1e800003440b9541603109800703400150b4810381d488501c201c0c5c4000074200d81079506c01c0c2440c3e944500f0f04501e001181c121800000d10001681440c080e003800720710410b200d0f00301100300018a591901340c0da80340050f0005d0101691840c81c0c82c001d81c02084107880403098100240301039041140c1800340b13144d011a00000149001923a218440d21801b461420502404405419502c545004555130a60440101d2700044c0c0020380b200800c1c54152808020400310000315901d140c640c400409460307018004007c0c050301485270518605021a956501880c8580c910310404070500d60640909402444507811501d0f103a200801d1103008210009aa0302400092110401c134200c241c0e2288802d214680c00210140800207207644100318101e800c02c4145803c9050040c2c0318440c9404c0c0e8066803c1e080302c40e540c01414841f06407540196 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 70569849 1250 70568599 70568609
    0x605030f070501051809040f0209060102030a0c0605040c0e010905010602010606210903050d110304020f030a03092d0803030403090801050106120513050a03020a0b06100507260d0204060801 83
    0x40c2142011003000e039503440c2280d001d0141400400b05640820701400d12044821362401448010300b418035080c0200c0380d03064004141d0040380076000085495000204840c50305001740d413441c1c40e0301540e4903500e00914020384115900d0307060202c00600000300160460207420a4440016a5403400e9000380c01c4484136802807040c070040c019615082c89868441011007000c0354004200c40c901031804540f02d00c2040314401c031107841c01e40d00b559403003074190140d0b201701c1c4242c80806800c503e8500300365450034007a10090002d00320f90404e004000b43c10a901c2086010f802d00e070403468503042444580d5108030b4001941e19071020040005159028030414004c0c02808002c01c41541001d00003049020000300c410305007600d03200440d070310180000700c0703a840c2ca8102058845001951070000c1d2134003020942910710000b4000030a40c1c51502020007100c000b0241c9500340341a206596004170009440101c5400ca80b00004d05c01c3d56403c028024502a9681d45006070b0b05c90408502409030300041e000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 70571099 1250 70569849 70569853
    0x150c080709050d030f03150b0f0c1204121202010b0402030406052a0a050f040305060c0301171212090307120905040c0207050f1203190302040306050606030601020d081b120a060503 79
    0x1d850100e07800c001e1000c56030a840c500407c4107a40403000c002c0c151403c3d07010200440d80090000b81410300d000250580a18200075141031108854001c84070380528050a03080700e040d5504900054607810790504204580e0001007001c2401d03400080c2242c0040390103441c100d40301c2040095a1003070740540f4190f6511204006a4202ca00c02c00e0080e238003440c05c018040c480000b54500142c1d45110540f4010b50340b241c100c9040c0d1421100301c2c19142c100327104200811034080d03501c00b10844040f40100c0f8030b9111841050030070310000c4031820401d2014014040701d00040185001107580c82c4903421018415440e1070310000d01d402d003400200d40101e2901c0c803c5410105040c441540c540c8840a00c40400702c0d00350364042c40d140d48030303410752144448c0ca10f650222000c0e0090400d41580160040360701070641004259110800d01071248411138180340160040d80211035424002c91080780c12550300c400741e50b40c1450b000b0b41108140d0045999154205241d07040244d20f440d54040c1101030141500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 70572349 1250 70571099 70571119
    0x4060b10022104030209090309010e060705030d05070507080309010b12210901051207081006050c030912030c010c030e011503050703080a020c09150301240909150c08070905 76
    0x11000352601c1e05400b20710016421058000c19001161058034051600100721200c0340c10301c3c4507019540d07402680e40a0101c3d8040722035180b2864000181c4a0094008014501d403030008544c0900800004010b0414004103109100200d5031076000b4600c1000580700005151000c40c0c200002c1208162442d00c0ca0781c400c4500040d00c02280015140100d4003c04c0c0b1611003084100603100740c0640e48075490341c0d0918030308000f044c40d030004a55000d40000110100d43d03907141e1008858502c07900c0494082948200800003103410300c9040001d400c0b40210684c0d08004c0031521190950b00c0200140700000d440c1c1c2e1300c00c0380740792081c4510800070f004403180381c0c546465542c030f69803203050500c006402c6001c003065040701a4000d02c40300e03078a07220080c6400c0350303440d280203400400c2c2c00300c0400d180030f5840c200e41d4980454052404400103150074101d01603407440d106010700070304080c51084071121078074040d8103102d01481c0200c06228403a51a404840e240c607090041c02c1b104268071491181055913 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 70573599 1250 70572349 70572379
    0x120b06070803180d020604030801090507050414010201090203060a09031107050307050907020102040504060b1b0706080c09040b041a09100e040201080a091b0915030507050f0118080604060b 83
    0x1804941031241d01003a00c0351a07542e040000101e201410150791000d02403400003282c03040d80801c003107100394840c0d100c4000c144d80392000c102c01c444c0d0440706000451400c004c140041040380340b10000450051002050307020441d408a03042c072806496a01440d034596004400b00341d04400c106000c070006200509070b092030440002c1e035070412445458016912440841c0d43d042c400c1d011140908006007081c840e07960740d0075096001d45d0005a00750f5406500c64075040000d600490403e040f40e45d80c0d90f60412944518255100d20750181c40510b43c890703601c01d40c01181e0b0b103960191411140c092030036010b42c19810014801d191714000c0c0241c1081d14104014880d5075030103542150000d17020710f4468100d64920041000030410b240010740300a1101240f4510580110741100582e6a43d0606011007083e00240180c0000395003c01082a00000020301c850300340890394102483d814900159a41d04101550031552243d40102403075400c62004c010a00695000710b10344007c0a0b01c0962058440b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 70574849 1250 70573599 70573609
    0xd1b060e0901030f1502120403030b0904030e12030c1501090b01020703031209111e0406140a09090501060509010b040602150c0712020f1e06010806040503030c0a0210060303020d120b 80
    0x5010041110640813209024406603480e10074078003020040840d51000152100301520004850031000603081404060403070500002060090768541c50382c60780c10710300d0001c100d81c0740d058428505940c4814085240040d000300844025415808414070055052078801002d450f09007202038159806a603003000001e5100601001100391038000240304031041c43d215010a441d251407950247ca0802c1d90a500705029001080502e02210704102c8940e03070b10681c0302c007000b8210109501403404d10381084924443d41017442040e10881c000208141ca03200010864002a000034041c1880072600b031003c5601000380d98404032801070b1600003031910030200d5295220300c0c0c2c40145844860000420f08274006c100b031303520001d10f0000b43c582d000d000380c134402603245c080031501c00f039403042600000c0e0250740818018007070380d00310004e07500e9581c230030100c05407980c0500304941c00c500c99900310384d20f1400c40c0e01c2140046c40c800e5000e0422031413000300003420040030081c034103540f43c5003d151613030300d0f0b0315 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 70576099 1250 70574849 70574851
    0x30406050a0c021002030d1413080705010b10080403080106031401031511161505010311120c060d06080c0405071b02030304050a09020a020607080609060904020f0d1b060e09 76
    0xa94548280d03160404101268801038a00d03000707400001a0001402041e00407001d800005202401044030818a0f2400000d204003545d82c892005624038010000c41d01c1e000090940318080c6002043c003411840204d410300030010005c80009054400380000c140d805a8841e00501d00c601d010300c0100036007001d285a81c0c8041c840240403d0204030611404056038224141c03508490700340300d481c1c2d0350410050031680301005d811102103013800d03640041c0216510426060302e400c034602070480c82c00c9500b40712214041d170025040e18842c08440201c01d50750440100144400541d000c02c00714589954503140a8149442e148034034105004c2000240d40040380308804480545901015085400801c0c214400d0790451500710b01d40d071902064040281d0000c100c0700f80c035239003101c1090b900c49404030f0f40098180c43c0140d000b6060700c0424003610748020b2568000d80018508516029000001003203010083d1045510390040f1000d80f500000c0c420b91100140141d0410000c46000900000e44c4180 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 70577349 1250 70576099 70576109
    0x1106010807060507030c0c080c040b0a0f0b03041a0a0c03050105040b010c03030f0e0a0c031106070809090612061303020c01210c020a05030c06010f050423090102190c020f01050301080304 82
    0x3040d240d090601c06d502c1c0c22141d9422a10314558151588519501c030004030702e82501544c00c09028a4003402d01c9a90402250500c02d10300e81c0c42806c1c071187c0e5846501c09002a40c001c0c55403802449400305505c00d050080a00c0d1000166000500300040c040e40c0050b80003c0c0300364a4409403a416917041200d0040f41d035403500e0300007000c0780c029891000034808084c0118084c4034100f103c408210b4060311700420740b401802c403190800b10780402c01c00d241c8601d240007080c03880c084c009100d560400481c43c0e0b03001007008101c030000318146900280b4084007195698040840102c02c007080c59010f0204070100b40c0c0c28030b06120503100600e00c02e01c06c04545410201d0f03d50b990504040582c4c402d1021b003c0155000e426655541d01c4440741b66610042801041400705400c0000100c510386440b5540b007608030401440705842c050104d14030403010040c6a01002e540030000c0b030b100e4000701c0c4588206840e01d034039141c6464196005201c50130b8003522555060005c100014400d914001081d101161 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 70578599 1250 70577349 70577357
    0x50d080405010e0106060c05010e0f07091503060f0515030715050310030803160306080606100c02180916140a050d0503040807092708030712020702060f0406110601080706 75
    0x40c8903841d040340140b080103407143c255468500007060056100c1450f45540d0b02440007400f005284006041d22a0074040040c2030a0b4030a88042200726100e400c0881d08010b43e4044001c0b096480c0c80d10010380301e5a8018090684d503800402034005040891603c0c500b40c00d03001818403030704001e4061180607400711050188036002c070014410745404030380c0c0360265138882009901ca061844443c61106150038100000ca400c00ba40411842c40004900e4843c01d4000c0a0310035440d07808030141c80301961030320141d0300001e42c203417140d40900980c0c114901800100c0010300404441a801c28082e0720a40c210124000180f162140d80b035503000c0c5920160380040301d8482c07400389103150113481c40c400e66010003003600960b00e00140021190780180c42c2000c071158004a120f0303074030003007200c0010000c4004184d55002c0c40032a22551058503856445001420014604174081d000214140c000c0b80105990550003d8184803040e1b0100c001050051001c0040004d5410702103125198003403030003484100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 70579849 1250 70578599 70578601
    0x702120c061803070909050a1e03080105010c140a150b030712020909100c0e01031a0a030b19020409020c070609080d0302031e0f01050f010512010509040609050d0302130f03050d08 79
    0xb90f60521030500109210f21003080807100518190f0303140c40e54008182c2c1d0100c511800c072a440c8a1030017000c80f180f645a52289256800c0400644407032420003130548025003000b40703051070b21404100740e0101038000c41c010050f050f407003d44007054030700c1044820f0194100700000c002c03001b4154500300090743c0c1154070400701d5654041c0c491034540ca0182c890b03841c500749210002e440380c02640102030014283c2c2c082c40340d50b00c45425a00e451003450742050f04034000700b1080010441c20300d20700fa048810642c000100c0c01c01c0154801c1643c219402038085183d000880d5040050700b005000014030160619001043c80e11500985880d6150400400e142d0000b00107070001c001d0b48800c4004080d40ca00c54011070408104200c15081c0c2405140c1c002c0000c24a00540c940c02a01980c003204c1c2401042000d5a00308400d01c01074a1014204607011a268018180010340c1401451340300c1c161940c00586600442c0c042505160f8280d116104050b015007007400401c4010801c11024280da05200b011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 70581099 1250 70579849 70579897
    0x70e0703060f1206180b04050c011d0108060f03070f1403010506100305060a05120d0f020f030702010e0d2103060501030207030f0305070e0a08070e09031623070b0702120c06 76
    0xc2c017541000320702041c90404107802001700c060300141c0550b004600f101d209410940041d101911403042c2c24100900d002c3c4192481d600c2018815848000507142681d4000d0050101c1d02c1c18a42c0d070860341110105102c2480306c00d0705024580188a4120022312403800d00b08007003059080d26104400c10940c5803400100c0f00d850358000e8400030007018003007000ca800c003500318584486e251107400000409882d02c00103c240300080800703000300c0c8040a186082c450354015100c1140c1d14100c15041480c0310024408030703250540f040703850071980e01243c2492542080080854003640c101505052041c080c1d00301183d8841d0a503200003240f03041c0020603407198403055070f105480c1c0001d40e60180082c14007207140b007030108071001180e119040302802074940328040c070340764003032080243e84c021421050f900100f503040709102000e2081200761002e15440380141400d00c40c46070407181d20301070b000401c5407c60030110342214004200b00c1c041d0041d04090f8000813054810500d0b204c8151100c003007011030b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 70582349 1250 70581099 70581101
    0x708040f11130c030c0e0f0607020102070503060a0b1c15050c090a140415080c060f0d0501030f0b010801090b190b04020301031a090a0809010309030c020909070e0703060f1206 77
    0x589001c00520b80c814003191041050302402c92481c1030300c00641070018485d1305a016502c1e0001418005080b41c2041c82120144810307034000103030603811442410720020b105d4070b007803003a1400380108800c00b0400700c03e4030f41405a51000141c8091000c016181c01d000480ca504040405000c4480e030b0100300c6071121480290280244c88405a00810300e51001840c001826910700c1600340076070381445607060f0802d000481c1b9225214100c9560030205083c0b2103480e00e1001003082d4048142c02d6804e01d80f90403044000c0b200d00341c00844030400452660800d1050000800c1e004013000e2009000c80a4a0b40e500b071140017020300201068410507180c0f00d841c15142d08601190b41d40034100315101d603524103000c5400083c0f0100c1c6082444804003003906181c02280400502e60030086d81450711121200440081894580907003c00c07105c840301c0001a51004441030103808030720010a1464209600040d0040b000b0700007105052070b040d01007150760f850083c135404589006c144501442560b09246d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 70583599 1250 70582349 70582373
    0x1240c0201081308030f0906090705060d050709170105061819050c0c0d08150307080303040f110d0305031803090a2c07111b010503040609050106080607050d140708040f 74
    0x8016200200404c0002081041c18907c1404100119420750f1514060ba075101c5815016050304400c042000c800803041540107103070821000d00e08050541e0713603801811074a07164400581102d0351900d0034811145020080c034183c14001c0bd1103c00c0e9410304424403020541d64600c0d4056541d02e031030000348a4030324001500c024001031130a9031400840303560000c040d24000c84182035400b110440880c250700b0001040e03001e41e060040210705c0c50f162038403000c3d00d04c401a44100d401602000c0d81d0201c50b01d1341010382d03191078841d444041d141d0404904111403010010413010140e4001e1281d045a036850088540480e2545400c07101c112206040d2140d141c81807003c45034442540c681071020460740003110f5503e6191050940380c12011800c1440d20320105901007030f002610610110b03010811650106e514207109034000107207180c0d100750b0340742002d104507481b002040000c42c0c141c015401c0f81c0100c00c1c1014900801000a1810007005441c00380302030005082000508050410084c56442c1d072 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 70584849 1250 70583599 70583603
    0x409060b040e15010807081509032205182401030f0e0a03110102030c030c0d0905100b040b030f030307030c02071a07020109080105061003150506040e01240c02010813 73
    0xd00c100c920141c0c0305540ca07084880f2102d207074640e1400000f84000042040400c0c4c80845000c0d0508040c2254121510f15000d04034841d0360008202840c050041303006000c0d81c107400c010490a803145401c04001d4512805001411103a1192041240030b144179141c051022060b41d503901c03e42030200c0c00480081815608e1056850319003640c7d031600e40c40009116130581d1082d42c60b14191000d5104040c281c0c001550000c102d4070090001c291314808001c00340c40510341004000070441c03002d8485524140d1031041c007409c8140c1c1e17010b04000d40e0401e8040d000c034903141980209911168091615581e1000402c00401c065844648820040c800e0001000a184c01403c104450000c100800541d910601c1e00300c0c0403407001d82000400c00e406008061041200604442c40b1841750310054002d03109210301c002c402104480d001c90b1540e6042e0190018046000384c1100541c10019020003454160003034121404d50842600348032540078401d624141d60a10341802c203a140e030390a4a110040c40f01c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 70586099 1250 70584849 70584851
    0x415051503011a0c03030a0507050d0906060501020105010f120f030306080703050303150d020f0d03030e070b0702040c020a0c170c040204140306010609080c01031e050112030f030c0e0409060b04 85
    0x25408000880c01a41c1660b200d0181c000480142550710b00940c490144214404e40060000440840080d031041341d0012083c107084d468010b036101d070002200c0310a8411180c10303a0700c070030034001543c4c2481101d014158040141c2402e0b402e107511f02c0e032090780d081c000804610424034640c1c20140700c4d0b00150020030b0304100711810740c2e0326032424075120340080701d4039070801c5c0d640c0d600000c040c604410500b406da81c001d069110300300080820311017014417000080d02450741b00c0741c450000b400c0400070440144010b4032940c1e1643d41610410042e030301c004000d001154002108040480e40b1880b40c80115203420030302c003462120403e00282407843c180e41c000c4d881031010030001507181507000d080e00d1300903088050f52100c1c0c0e00c454098a1400c440e000b2000e1320740c4190041c20907940207034098181284001140c03507c4d4003100e14600e00390341d001d07049084100b81100c680004c06420040c03124079000d1904051010342c080c400000c010038500103032544500d484030030740703030602c500746e1b102014800020340 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 70587349 1250 70586099 70586119
    0x3080d0612050a030305060d1e03020c030d020d090b03100509130210050a030b1f0f0c02100f0206160210021c0c0513090603021e0312070515070c0c05041505 69
    0x1442e030307111507802905601007820301c00041e034a03203443c0b100d009102d5806140c00b00381c480804001501200c0ea240120154410540a030303186075802c01003010016183c0c1e004100c554018140140400003c1e0f124050346a000d0013405a0078420344601419503605961048542d900c5040755a4220005440030790410307088a4510703c80e591200c000e05002e80b03d5182800301d00c0d0f811040c44600c03d03071070305412000054000e4521035113114000c1c410480132079140031821801681c00242010743e648a48d0000b250500107400b14aa030148030a60b4448680d06810400740c03010700c0003a440e140e6210200445560000c0d8180003400c81d40b50320750000f52180d20400507000142d0001e4090303403000e00c0600000018800008220990740910b1003070742e0740030304a240016280d0038039800c02c1c500442c08a0b89802828920840003100002070300758140144010042081d20400c01800c0c00e2001c3c06d0503007080480600c01c8040344c1c01001100c00c0f0f0307105544c0013501d00245080d0510102003070304026800f5913142 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 70588599 1250 70587349 70587353
    0x160203030f1305010807050c0a030e060f0f0301090c0f0905090408040305060a060f1e1403030c0f16090509060415020415030e010501050402210402010507060203070c05060702030f0403080d0612 85
    0x35008001c3d41d038203894514850b22600015503c070f024103ca505010b0f4841c42042000912990341c00e0400030003e04003500b4101c1c0f000e03602e1401d03004070100050a5602200401030300c0030038000e043c00f1000c0c6041000d075031000c4420042c445021801b03003600035181403001c2801c0000c1102100d0086400109039a440d0410502c030001030491380c402e00403c001210400701d80700c42640c040355500c0014841d00015546480c1c01000100f08007071000741e0600050155081c0e04100340031803e078070707030a07540030304501d19120200800780030032030300b000d58054a80000c000d41d090f40092416003140e004110079440074101c101e1071020340310701c0c0c00030103010300e104400794021138064010290203648500240503aa80311428001240580c2e481511442c00403c04451109038840080381c00170300600d0300da4940500d54941a003668419140c0400081454069005000c81408a03d0300076440344095890034407006030310599402180400b8000c190005240100c94105501c09802071203002e080d50002c000c58 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 70589849 1250 70588599 70588627
    0x130603030c03120509032704020a0216140d030c06060801060b0d0516020604030f090e0f06100e03030d0c09050306041b1e0b0c03090405040803100801020c03160203030f 74
    0x2640040b40440c01540c8403896088550003070b60b11681c4144025402c7c50385907000781800400545410099145004005040b511207000904865001c1d400804581c0f5100602e4040040076502640d1001116800e101003940c84548d22080603070580b4017444015a14100342c4c00400fa69480301d0010761800c100000c01400e440b000d082e090410010400140e501d04800228a02800c2000c4006802000c00034000034090404015a034009280c450b0205840b800004011a0305540b0104c803405000200a014900054241242580d40c60804c030005034200110b82d4901500000003151741c0c840c00f05011403440f91444000902c801000c070b0f88181000d0809880701131415030044201d4000c04000f00b440d08010100036880040b10048100c1075240482115003608400300f5000c203400f0400c0000c000d80e03628000c0c14065406002200d60742c0c2400841c0b280c0746410f580c45115540d00522540300004030100580d090985141240350002c0c20510002c1d085205802c140820040089140f00d9010f8075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 70591099 1250 70589849 70589867
    0x902010e0a0f0611030309070509370614030a02120a020d080901081f03060f0204081c0801090c0c0809120a0c0e0601050304150b150a032c030f030613060303 69
    0x10580707580345001c00130b8454646901c03048400c19215406038804108a00b003a00e9856030080da04054a00d5a08071030940700d100d200c42400c58000c0d411001c2d890000c44246124100040c9148194120001c107088086170315114848000792042c02406007d0308200c2c0c09102810324030398000d20084c03030341c0405e181030005904807014082c0082c00c6180000c1c0d44605440703440121810000c0b80c2c100052860359541c000e05030300c1d80e0701701000e6000d10001074240010400c0c0a1819014260004c0c0c442620400808542c0168040b1300c4450900c249182c90070f80040c0000960360700301c00f21660704c0501e01c0118400d143d4680e00b44166104a03444203003400141c91410b4181c8000740c100b6034183d10360b00c0c0119003a01003039501400d5030040c0705000042500c194001c0c0801c040c06840b20703041e40c0c034100070580207800c088035100c0480d80b130340044084400400c0c1412364011005c0300520090042c0701ca01035a9020b08080760905450000110380035594051a00500090881052019580340d180003410482 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 70592349 1250 70591099 70591109
    0xa0e031303051506030102070b040816023304050d0312061a0c0105060406031109101e030b0604090c0608100f090b0f030609030a0e0111030c1507110601090902010e0a0f 74
    0x1001c0004c103600b0314042c0229038034a0303004040c0d5001504c03542c0740c0e50350b030743d021240e54031407000404814001610781c00070100f18103000108001ca2914009105840b8044884500c00a408200010b101d00d903100382008044541518018504511400d0340c900101036a0f00500c0170303124a1020301c2d0502080c00d00500e0701c511203000030303c15130b2070f000c043c8000d503070701400020040390003c1c1c0100b40c45d0070a000d450b035024032584c0100351403c2d62860240141244103d11070810354220000340f09110340f2440154119405403000c2000b190300380c807600d0b8903005034001c50040140310f00c04140d001102d90300140c040e11072034440000c11640e03031002c2c5009048500c0b145016603d00710118000740b8011521074440d03184134020b9813034080b040340215200c10790740a0b01810700003038440d50505d40c5c03420400750035103084100003400d8070441112000b907000001090b00c01000102280e407200351201003030b001c1c111030b0040000b2906840d035200607a609081c401f80d41e50230045840c4006280810306803000b044032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 70593599 1250 70592349 70592383
    0x82206090603090f03121404030206070f0809070603021308070f030c060320030903210a1404120f0908030703080f01060903021e0f0a0305010c140703080a0e03130305 73
    0x41c0d941e02003942503920816014195200032811080401e000300b482c15030351170241d04001030f6900c413009039a40c0c0d43c5044d5026401030340304004000344281c202200e0680160301e4103151542d86005c0391003940d1140d031070040e0810590042040b0076103621150203603001d4507091003540d00d800c0d15042d2000164606120076103680030714400000385140a8400c12212080b0410401021181d5094109081c1c0c4081e2140c0054441080000c00104004d02902d04020f0882440c2801d41041100304007034a128040716203048a5000910000801440b0044254601404c00408020038514140d41e1222136501259082c080010340c181090303807080740c8030710482254990f004070ba600c80104031003103802804001d40140c02c05d80c0c07480040c540c0388522240e107a4001c000c0b040c9040000e011804204003070380120303656911101149242900300300f119200c281c030401c81d64100416070b2001050700c0f0025110680b80e60780c60319043d2560400340122072442c100044031050086e80c074988241c0d604000340300a600c3d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 70594849 1250 70593599 70593617
    0x170f06040f03120b030307111c0c0e060f0105191701060f14030601020703060506040b06040f09050109090b13020109030c1d060604030503250c031109060a050108070c082206 76
    0x103c1d144295290000068011400c041141c1ea94072800b01e09000341c42c2c1c1c4131320107003120b500c404180803520140030b204031b06440105150505000d0781c90700240c4080d1007049110201c04050340d204050340c101c038854009c00030649103a5101511000c2140c207804000e2458440041a010703003200710072014035200d546e000e0380f0781d8529070381840c0c600003540c2d424010381218000b0004504990466904998010310000301080ca03c0c0029040703030b000c2d038000f001c0000c0c2c81f1010410f8107140e00c41c05005140001c404d001056080d0303540354400b00c000380386c4082185564004815a44201040400b0319132103200c146d21140c54000d200c0390f580554040c41140000301c0005a000e06003001501c049a611400550501000303140b03c10ba000000c003400040d6450400625000c50002c2c60804001c500802c18038248030110310a20650840081901e070082407034080c00c2213940da0051443d54065500e00c0c0600c40d4203003615140c0e0392803048100205100020b8000764605054062001c2c0459040352124002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 70596099 1250 70594849 70594877
    0x4030804050d090503060601030903090807080c180103170c151519080303041e080a030f050a022a030c010509010b240301120606080604051b03030c07170f06040f03 72
    0x11030b2298000c0e1500340e0010000301f42954003d4020b07004180c407904011800c2606d544106240c0f048960080303209501c00d0170840414180202c034103008564501d210181c170760440c0c68860300c1c100c08400d042c0410360005401c8800d8a000c3c0804400c040701c2411700c100700d06044044810f044400d00041d40310b00a05642c81c04120b1480030700000322649040075508541e10340e100c04480802071150314440b003010b030048000007080200141048481c94400160703c0c2c500e28041c20480d44000d02a940042c41040000e40ea9508052140c1c040c2d84107616980b0400d44400669086006125041c0c41d0382d800c110038403044060640241d00415004d5130720002021004003100780d01e20340760709e0502c0303000400c00061111880d9840164105400340d80d010078040e03918010503141c000c08840c182d411741c0111400082c401b00c0001c40a110802c105e0080d41810481c4103505e03240c0038144201108203441144a50742d50301d05000d02e8414901c0003007a00d406250a04044109689450080380002c200c400405c003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 70597349 1250 70596099 70596107
    0x50403080a0e0106031505090705060309010207030801050d051c200309030f010b13180c14030601060f14070f050303010303090603050a1b0c02030a06060602100f02090105030c0304060902060304030804050d 90
    0x41741d400180d407000c4020320840c800c004001c003510003d417a020704900403d580c1c0300d44000f140114400340005965074414100207082c09810f8001c54458070162600e000840c100041004500070641d50a11161504801c2070700c111420045507030070544006a4008080404000744c0704014003502910180203510401c1c80c00c9030a541d4117140d01c800c0c44511403604011540c4903102c00e146a80f042c0c44125100e4540d031100360102d500a0b003082c0c0d640341c1500d140c1e04040c441e4a0051945043ca502211014107014020b009000720388440814086080014001c20300b542d14022500901a26500d586901f00100181c42901441c008241000003040d41c24000d842100c502c1d01d4034940c1c0f0310006482d40c500710781d40d01640f003007642c7c9445148109808a146481070b1b80007090260005c0c5030082001c09820f064800c0c8405917401c180c410310941140780d8000c8112503102086900d21a501c2e43c1d1850801c00030204108013940050000c4108170400d40c10014450181c3c0c0140100e503001d1800402c219 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 70598599 1250 70597349 70597361
    0xa1202040509040b040602070f0b01060f02060420010201020d090605090607091401030903030221150901030c0603050403050d0903030906060905060d06020c010b041109040e030307020a08090105040504050403080a0e01 95
    0x10b40208840000401240381c2c818095081486203402500d00015900c88081c50210780005a40303440f0a400104080c07500801030402075111400508050300c2c20742c40c3d8640290480b4450342c902500f4582818081c7e10030340c1140d2510030f00c0403003001080c1090400e070b001841c084130302aa640c4511408169001d001360303100380480d1500b1124441c0064603030b00450107807902d074a0450074140c003072003050f0b00c84044091080e1050b0b82e502c3d00701c2162078003000e420f0b01ca00b440c50303500c0c0c001c044120040c404034004156a4090b60590b0501081c00d0f103440c41c0c22583c07482003203110070405141c52144810154075400541000b4040c9030244a4036407204069001c42d00c00b590392a60051035091039000050150300540031078100c1000000e1448034120100313042d40e08071409018400070020302c2a00c240361a20030210030f0902c03031004604601d0714000282d0780700315214015140003c0416800496885038084402070a4003030700c140240e04140c034004d08080b40650f00c020009040c20507890003036405210340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 70599849 1250 70598599 70598609
    0x601110309130618090c06110c10110307031d0103060510080604060b1c15060903031404090c08250215090304030b0f160212030414010605040f020a120204 68
    0x90351521440e6020880c10030300400e07030500860345596000901442800401c0602c0c0c16411021402a01c1c030701d000d04519850340c10100c18088040c10315038810400041d582e04622041d1610644002d52490584409042070345c0c1041610000494000300340d03001c0105c040c2012056807006180007140010340940360b0602450750841002c0f4100103446100d0201140c004a0140000402c10b403121b5200340560700140d410405552140814401e0700000c0c41030100c3c2c0303103e201007161190b09222005095101910024040198640511404031101000c44004202c0c8c0c0c0803c0040004451020308040030031103100c40410b0085225030b0303568080c2c0081c000c0c4401180e028280105170301100c0401240090141c2596100030700022000510348414103003d03001036400704000c2d141480c6132256203c800800002150841403030300c42c00c0102c10f01034030b8000ea40050003902454030390084900428003903000b80d9203e41480d00140124900b0790082c41691055030b501c0c0526500c00244405074820f0b132003a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 70601099 1250 70599849 70599853
    0xa0806180c13080d030e1207170304050111070309170f060604021303080309010902090a090c050103050402011101090809130b0603010501140705070b092d01111e0a050105060111 78
    0x80c00c44a401401007a9084050b00741da0340882d01d8140b090b10b800c548804410204e5903c611452945104101c02c1d40d060725824802482c0c01050b540d480d00240501c500303e0072184001c4003080c1045400e410403030000320a032503065280e04241c00c005201a580d885050050f501140034030300f1410001c0707010809031494000034011900d03210701f03010088d0700500406845008a99011000400e0076004600071482c44001113403810450042001d0740d0000351040000070303d80304c810760010744102c4000c41114401d00f8002a20787c1c172400141c3e8010500d81d031458155203003080c400100140400a0198850196145241094914502011a00442e040940c4060240010000b641c4281c003420003424140540d10308008290381c5440c5800280c0d0070030101c84001060136425414034050445034443d0800b801031200118036080140b40c086640074504016203582e80c0c01c2054020000f041d40030044d05104526001c140ca5241d80f102d001010132103441d420701c0082000b640c0324040213680040c0c4140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 70602349 1250 70601099 70601101
    0xa0806040f020907021906020a090501110a03120e0307032109050601170703081b19020d0f051204060201020c01050105100801060302031902070302010207020a09230a060314030a080618 81
    0x1c210307485000400130703000c5100b00d440460b0180e61440c6c15441c00c0e80300d07101c090b0f1902c90300c1001030020011038126504102003110441f101050005560380110303010304150f15401c4d4406090300140203075040b0021148000a40c400c01c05511020101d02c1d140c14041001c0d1202c0c040080c8000d88541e6039018140b58401001030008913000300c1d900441e003003103100326100207030307603954100060704070040446000481208036417182900f407154184118841c0c2502c00e100729107500117440c1d1003ca04014000801c201d03080800c104080040609102c0410f140d940c460b40e6988000b400b07035210a081400650030403000092600740415100c104515646071000143e00707040782140290801010f20008a45103003c840c4101000c0c4010f24040c0d000b030740050380d58600c90042c4415524283e0098000c207142c42010b80f01090711011524181001d160108641d07190704810038080c08241c0c102070644082848260104540000140345c1032649498426aa5841c07004201c055010050080d0a80e40414 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 70603599 1250 70602349 70602353
    0xc080903040509090f07121101080118020310050a081b040504080415050706061715010501020303060d020607051603020a0602060106020622050607020102030702010b1903110a03060203090304050a0806040f 90
    0x1a0544e8070100b558103da20307044100342150320b00034041c0e01c41c9003e40510203810b01440303403903541d10400074001e003444681c65241a5080c001d81800940e0020400c1d804000700e85003411b8140090010540104800704454035800c041c0c0d140c1004050050347c03050030a4440000341460b0151501c0703282c00112072030500d0725182c1c50f1038078400222a080204042004407100003480343c4151006498955011801100705020182c034010032404c0409582c0c20b02d000410203030fa400002c503644000141e621122101031231000c90907a00848070f0041507030040c4a12280040c13141200c040860b4002c550500404d643c614040e0f0310743c0c200780034010050b00448000303840b0740e090034020500002000d10f95070308401d49840e50390510406491850050b5000014084c0d4146e0900880e4085001180d46584448072070051900d45584c5110041000700321200c005080d41c0d070105000011500b00c6010b41d0f0300d142014041e9101d130b0050140c544200c0c40c1500c003003002400029002d00c160b50200e01308100c4103040d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 70604849 1250 70603599 70603609
    0xf0106150f0507151a0301020c0c010e0316080c010e0a0b0901080c070602030a090b010906050609040c0201060f0f03050706210e0f0115140108040201050a210606050309010c0809030405 81
    0x10300c0700307034040c800b04110030030006410014100c040811404005400700070102c40d004e0305180d042c3c07128841da005004020707040c2d4021528000004003402c1103d003540c2d40d03d01090624036503041a0302c044901c05400144640c0105081000c40002d0341c860100c95450700c00c10004041c103000b9403140060a114400c01c1c0d500078240d95030803a60001c001170508a035592040c099900484100b01115203e018900c2084140c014542c054490b1100170b00056049c403000c03d455000c1c0c2c20f07440d8030894445040c0c1781081d00071342c407000152150343c038540c140039142c0d01400c045007003d12003140c09100d14800040d840d40700e420303500b1040d03c1144484c000580e0210004010344007892100c83d2500901e41d1194100310241b044c811203510145a242c0e1661a081c410003c3c9001c4012050502800d030b010040146c1e2300a0894202c2041c034100000d8040e03c0150000c03015171090390600300306103003600c0800c01541104c0a18880c0c0050802400240141c850403902514181c0383d10000398402c0c00144041c1c80c2c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 70606099 1250 70604849 70604867
    0x4081b0301090602032e08030a0c020a120507030b0f0f070e041b090e060d0b060108040c030221010c09060909020a0e040203010b03040302060106020d120b0619030203090f010615 78
    0xa0011840b01c80e2500c41c00b0480c0d00680d4080c00382c03a2900302e0712205c07003a011090100080681a42d00b869071910108540300d10407400310004002d10780071140215a00c542080002d06052050142d441c44240303800782d030300c07000341c0800d6401d0f11256001800103c80c0c208520311072399040481e9125603d03014030a48024004002c1c03e82e203c0c1d1190a604620340710400344161560050366086011881c096900e0411600038040a025002c803000c0a00805c151aa1007034100b002031802a00540d07980c10000c54805140d0002075103d80e180021304c080d110303211441e81000c80e5900c02000303440c0480d003080e100da40103449450081000024100310117403860b400340081400030305000d401d4040600000d022a4030982100c0c0111201000348018598100201030142845000801501c0724010b4007a201441d040a0116030070749a007a010ba040d2181026251240030418600366488101c000150207504100c4088030184500000c2d20070030301c0140125801c688010060030b00d50b115086d4201c1396046 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 70607349 1250 70606099 70606153
    0xc070c06050a031409010506040e03090306070509030a0b0a14060f0108040210180b0c0c09010e010905040c050d03080604050615071202030f0c07180b030615120708060f0703020408 79
    0x19440c0400c4c01c91800012046110703803031007400054640b03024400c200c111500e4085040c0c0c0340d8810722503404991000205580c010b00b030390522585410440c0006480c0c0b0b404001d0040c0f081c0c1e40101400300c2c90329a40c100e030f040001112140c0381141c1d5014180440a542442c4c91030000e240103000c100942401640604040100d1805400000000d461841110004c1d88802c0c00410300269980354200144860411810101c821844951410352085030741d183c180030f0f03500013175900c2c004034080080b00d29a240003001c0c09003001da404a19414040e28450301141c4140c02603080500007001803504005500b00c01d40407903585030500805461350078514032426a1a01176120070000c0ea941240f14001920b81c45120900419115090881d55010b051060042c100c82c00e003400490101540c001c141c007544404200900f100d0311820900003120310f120300d070314003040b80100310011400d6a40480d055115000034800d1081a4917081c1b1308808074800c0d441003614541000702c1003480b12103040b54401c5901 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 70608599 1250 70607349 70607351
    0x1020a0b0901150311040608010c0c140c040f051006020303090d0c0c05120604121404030f0611031501020106050d050307030f021002030c120601020f06010b0702011b1a0c070c06050a03 81
    0x50510030a10300c1d030503d60b80060320404940344500540749064001c06000d058064000e109170078003c40d01400f0300600e20380051100a40162620700002d00b00110701d08031500410500c280c11221142c240280010789200d01c5402250354049011030001044a002d50003c1e80100215030083e2001c9031050b00d0908200c5041e6014440015660380307621490310855003c1025000e14100351410400c061502c2c020001030020101d0f048c1d011500700d2050320100ea80003d80600d0110b2686000801030003c44000040d0613004024000325038024854039040040c00c0c0c00802110b43c0f80e030104000101100700090081d407040042c0400039104040f00840e0754480d004480040c040d4440134421f0341c008680281a181010400701d103203068903929160050420700140001c89060b441040d102da00500650584240000700201103920030104e0049070700c420424450702e103003c4d242c503d00c0c40391510f654100003582840030420600d02002140c00b40766211000004042c541142a50325801c214040b500345 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 70609849 1250 70608599 70608611
    0x1404120c030804080d090f0f03061109030a05010204080705010c0c0308090a03050303191a1e01110313080d05280516030804020102120a12090809060d02030403140901020a0b0901 78
    0xb4a9640103840542504030103000c0024824100505184640d840920940034034038042084103070031030610042c5c80d0016804201c1035051200410284078030a1461303018850300e9051000d2000640c003500c00d8600101c1035603000e1703030b94034011104141d0045000c1d010003803582d001c00000306040020300c0c2d00340c00600011076165130781d140c5c1d9066401c01c0f19614101600a07180103c03244e498860000d010301154881161084800045001160021141404041c1c0003110182981c0113800b5040ca6800d49000c0741c0d664643d007c80b510040f032562048100c0c0f48540c035038441032036020350240c4948020104124507480c5200107c54014501031740745105000c1d00300b00e01d403182114407001c848405d00a490b1800c040c1014400240703058084c03604c603003007402c0900000c180c00d9071001550101b441082c00100b00c0d01c0040c14855041d00c6200304903a840303c000544210100c0264000d18415802900c800d02c0f07110286000e04900c0c416445100e005030030915040000a0001640e10f4100b030101d0300020390 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 70611099 1250 70609849 70609853
    0xd0902030303010308190804050c100e0a2603030c0a1b0b040803070f0815090618091f02040501090b07030e120c041b020d050d11040902030a0c1404120c03 68
    0x941e40b081e00f0942d510b02001809103461032402032140c000b5a8a031a084106241c1900c034903403a188c0e40b0004c00d10500c0b107a5103a0903428401e05128001d80c0000b481b06002995400b81c01e501e046140e9400c65400c1c850410540200e40040241d0348034128603000d0504d4039920007400c40d4403c41d010145007107040c01380b40c05404030b11b407222a81e00c40c9100e281904d40d01d042450028000340c2c2100e40650410855404000c1c04494910b00422161402d545640300c544492000503000400071501e170090032002c10400000c61400106400c0074030400c210ba20368400d290300ca00302644240c0c000c140c04100740c110300700007100000d0010003031980a440c0600e461a03110001a0968024030806d10280c3d1094100301000d280078480c410044103405a421224060702e503000e501d82d55082004802e00101080d4814094030a4201c0300801c12000040d42e40d554940d09000025002982d00d152100e00d08410714000500603012000c03500d0b10a5450303400c080c0351040724029900072080c2183c16045103500000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 70612349 1250 70611099 70611103
    0xf02030c030403120e03060106090504020d020f0f03041a010b1b0c0307080c100305090604030c0f0b042402030f010513090804080307020f060a120c0c0f0302060708100501090b0d090203 81
    0x4040d40c4030314600c000c4c1040c441401401503401c0604a84281c00203001040800e40120f40300c400c86505940140e110300601e03603401d0090064029800680c0000110b10065000c02001144950b03c21110640c40c4614030210b003030b01c4102401030500214040100c00d08100044003e0700544041d40210b8292143e0b6902282c18901c16512504c42a409412081944e2800342180d240220803460104081c2ca80041195510440a00040c05003c65150359400344040030500c0d508594118544003a282868035042d11800c0d41180c2d840d4a215007400f1030300400c4410300880e4080c1c91303080340161075a404e010802c2000294100c000070069991041880002c5596004d84020300d109800341d521036803180140985c00c07050b008018441c05040014a00c00d40c1c0000d00066030540d5944005039281c54104265456071000c00c0c081d0464420951900826a00242d03180c840c202a0340d602030507444a10303040c58404440d005190109059400a100c18011640070301134441c010344000c21a554a500824 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 70613599 1250 70612349 70612357
    0x80601080339100513020102030f070309030c0e0a05011202012c180a110403020312030403030227040e03090d11042c19030e040e120a030b01080a0603120f02030c03 72
    0x9002d500701007074601e40c820030f510485500600c4000311600c0713241030340d0000b07480348108402d5107200503002c142041490302c0303250080f000e10f611100e61048a610384620002c9400200c0d0503019003810003002152680c8451219a40c1c41d5040c0c503501e410460018039159000b00002c41984680d0400c10255015901c011207000e0790a05105035138500c1c2044101101551041d501180040c1810401040140c40000e01d04112084190940744c80341c450389400c9010b0700c25003a60740385444100d0460306103d11108042103239184122030401c49d0344610541591280500b440c01e5034800820704859012846801c0c0802985000030400104450400b545860398618103000303840c131101d810b01da01a900030030404009440082c8806100d1030007180e900800351070b450203516000d20784030001000c8601c010803200e1a0792203850320091300d4103000c0c003001b0001d00d0b00340c81d01800036001801045500005125075400c3c2c0303411003030031448580381d41e1055940501b120103600851004201501c0e141c00140054 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 70614849 1250 70613599 70613707
    0xc020d1e050313050a140a030b070909140906061e040b03030d0c0e0102120f03060d02032e0b040506090c0a0c0b01030305040611030c1e0a020a0f0905010806010803 72
    0x40000b1604100902c00000e600d600001c1d606c40c4400d00344141551462143da003240c2d4840340e0301b07503d070f590144110303207a500e19071002c440c050030100700200380b0000928052003070400c803044580640e204000c000c0801003a1001c0c90310402c40342c41002081c1082d13080b15403400c5010341201d20380345054502404454030400d0900005222803140301156031b0501000d000359540e03c4610b410801c0d60040c4003ca4880600282c4c41120520412021924280002104d020207403504101c1c0d084010404854400791004100c40c11703140038a404160701d00351240380c3c0603400117400348a1f9079070f903943c00ad019a8811700e181c0d000d1000070021080061401d40103940a58801e0341d62907203840c506000a0100d0303d07200c0c0301c0800d0343c00600601d0104500041d449950f803446582800b07100701c0114515040060841001c0d4002111b59000314651036403101c80c2e81154486c00c01001160f03a1404840c4e12140d0a0281c981300e03400030000d1400610706c0c07030194950306040b040030250401c00c1400e00c0d400b50140400c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 70616099 1250 70614849 70614877
    0x90a03080705011805191106030708010501110a0f12030902060304050a02130204060804020d020121020c15070c03050919080c120105010513050a0b09070507120c020d1e0503 76
    0x3540080000038010343c107065402032130500d01128a41d489680714081c4420150346803035501560810b00109100c0141180400350541d42d40c0e0406200c0108860808d0007460f01198281c1c0788070010035400a442c220654100750b5140040155640f0095140c0072411442c2c10141c44800c1200542d441c0720056010300c0c4250300804012400788188040b841c0d80c405010300395071041c07004000281d0040041035006904442c400c24030701c3d00b840140d401c10700c405d1304007180d054051003506072151964014201001190100e8600c00b01d504000c500641c0201d4070300c0c000400014003e00001e000318050840300400810301515480c0d1138008621230039070ba50048480b54000b04e9005050704101c802d84002c0c008250082c0440c0d0704140118150100c1c043c01842201d5071100028103808240e801614500c5001f0b00c9007105040c02c40004005030130451080d02c1e62038121000340000c80c000c2000e41e10140d409403600c1c14110890f11411654400301c5c0c0c1f01d041400001082c1000200180f00038003010b106021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 70617349 1250 70616099 70616107
    0x1d03120c070b090f0402030613151e03110607050703020907030207030314070509011103040503010c050a1d090105011b050105010f08071703030a0b120709090b060306070e040e03090a0308 82
    0x61041e01e81500c03603206a400c120700f0860443c240d12080c1d9942181507081da409696902c900e0f0100b8101e515100341088840d1904103ca58203511000c421400c4411444044c420648510125030b1071150a00c40184081002d11034482d05052000140801c2e078014000d4941450380c3e034001c03d02c5090110b0340340000960000c1d0100c201030701440781b0429110700540c1c0d00c2c118545446d006e000783c441c0300c8000341070145128103451240b000b00115409080094001c0c003400300d043c080917007190440e031500008901c4010703600100c550150740090041c00e0003010402964078100056911403480e009010007141e451510001250090003228020101e41506510451800340c1c0181410300759000004243d2440050038170a0000100b543e80001406500280da6503001e400140d184442d000365103445c1c06401000182030040398804090540038007031604c203c0d0fa50000f0541c9940c800c60740100854040c0072400510300f4247d000d031464400038001c40c2c0c50440061300241005040da88110b0304800006 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 70618599 1250 70617349 70617367
    0x5041e03020319030b0a0905060d08040806060108060108040c260115051507050c0f0d050d03050f01060e030627031803010e0c0d1214030403020a020f01050309030a1d0312 75
    0x482d5401c00c3c80d030602d004c0121680030300010324003002600c45d6003000e90700c0340c0c0810500e50710281d0005406a002d288903035119518080143c0703400d02103030782c14003061911000410a500956801e403103164070001f2101c1b080e04103500002400405031018050f039500900054103101c00f442402d02101d20000300c0030301245480c042042c007100c520313220600034800f8480c040004d10000307124118618100d0f25508018250710100381001105200540a4030841c62204400d0b41c040d031185001d140e409182c4011a0b0302c1d00340964441c41118030700d0f5050343c00500001c00c2c03400c102290f144408000c00c7c1c000e10f0709805c00c00c02851a0890141c030080c82010515903001850300b4403852035120300c1c3e1400351100c4e0400000140c4d42c240e010b03c0160070305800641584200c1c1c450070102102e03810307048905c4c3c2c41b4101400c00a550f8006460b04a000e0001491004c01541c02031060340c4c4903510000046250011403002285c490044890356162a0300d002111041c0c0e0703500307008014501d11014101c82c0c5603e004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 70619849 1250 70618599 70618627
    0x602071a060901080d1d04090204050705070308090d0c080903010f05010b1201080d0e010f0e041d0f060411060c0f0703050a0c150e010804021804060c1d0f010305041e030203 76
    0x10390110f40a0b80c004041460360503006008120300c0c46d035201052400e01c80d550085070140c504444025403184c40c0204101d809600300d4003400320980240d8521400303640d6601c0d140d55483c1700c0722840d400301c2c080c104404001480107004100205003c0c00108801c4404400740701554004c0e0400528002c000c0342d03d50180c040074041074010150900148006564084050041034142d50414100b1400010205030503000d58000340981d2000741c0700300002c1590917841050300d40c1225007190a80294070505c0665540081c80354040c0340c200c0401c1e00501c404104010a581c03103030f0407620280c0a010000c61a5490030f01101e00110701590282003011010f15007101c0541d041e800000c2402d0842102004c8a03030700c103407100e840801c2800c1401c0300b911140006210000109101031007201600100010011250003c9290340304944400c86802c00e9400c80135042c03040c158002c0d0704015000c050004640c420740115410900030582c1503600041158080807215500c2d10650140c0d00000d08400080c103c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 70621099 1250 70619849 70619851
    0xa080c0f011e050708040806131a040b0f0a060513021306080408040618090507320304060b011b050a02090c0918220c0305070e010506160602071a0609 66
    0x91a11642042c104000341d1404040d100c1035104102011070ba62081000c4581120003a1101008440640c03030711a00b03010074000700f80c10481e0709902528103005440000c400311800381d40c5c052001320880d41c680b509030517400f0000f04070402079500d5450024450300c80c640180c1d0b040007a1200903030345d0400c900d800007144000d603008804124400382084041500c240988040d101070345000c903040b1500e43c0244217030112a411040310649464184802550003030803541d94000c41d604088420030b0819030b40d03a216a00301301c24880740002000040c00140e544c0d8003216800303d050604503a4110181d40b01d00090791905421100e644c88601c500c0e055180143c5080d50000c4030b600c5031860494008049005000b1400096688000307400129003451381c061050308950000c48891000b1003041c3c00c00d0b1221548910061303030300c0c0c013030382034040f404074100042c00307041c0c0310b018080a141c254401d40c00b00b04600d00c81803e45030715500f03204c443c00003503078180c65083c402c1d604107080c2a2418088100480c00d04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 70622349 1250 70621099 70621129
    0x20309120304060804060b030102040f080f06090c010e13111b060f01030f0b0912130f050a0605070305130b1306110114131110030c120b01020303010302040902040b0a080c 75
    0x8000d01c0b00300581c560040d00180d1140d442200401c40d0400315001ca4060b02580d08040d54403242440046181d0000240100700100c8000484400713441c6c1020240d26607078407561003030004444140f1062241000704480b10300c44d09030351000030b0350070400502641c903810141840205005202034072108070400c018160300444030b000b050400b54507564803e03401500c00352000300031948000010304c01d6107051150070001408074600c150b1364621501418a4888a8080d14224483c01d06c80421079060652040003554181e0315120314081c0103440c02e80c2e8a80218025401404501d5008207800916074054045c481c08168602c105909054001d40b0411410030380700e84680c940540010405014a00d55405c8281e02c00340b986d10017898241070b0072300a031044060390000d0f52400280880342d8944c0c040c95410503150355941c13001c14100840c0c410703200c1c08426140160300600040c00546410b50000c2c0070544020400212031500074086624500c080e441070328160414140d08400b070030000441c030b0101d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 70623599 1250 70622349 70622353
    0x12030726090613050f060405010e070608090304050105030912070f030806100c110103020f0c03030115020718180609030201060807090209060403060e0a0807110117070e01030e03160302030912 84
    0x8030704070310226a2400e000f0100c81003d00b0b80c144007030501c402400302c0f007000d00040e001d403605840c060610501074020321588034001d10a6000c0000e865114040460290512501071840d00d480d290044034117400203400c0300454002c0030041d07071403e090000140715192050482411059480c10040c040301401004170b0b02900401b049500410b40c880012802a0341c80001c0f00110104000100c000303016071241e0403400741c00000d11032100b90700000518100c42c142c80c038907010042161000c81c0c81d6080d41c810050505180c4600d608811040e4010005d0224808809011034050303403515800e4644191003540940d55540060004507803d004020151030142c0f015480c020709203011801d148254840600b0b0a0750703d00d03181510000c140032a4a4054101100d01c0c0c51303805600700a441400c0e40643d07240820441e541c1c4c2c040000c143c45901d44104150307111030165062040c015005010641c254032824003042019450030034194050280250082d80103545504000d41413040e00c10f41340850481d26 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 70624849 1250 70623599 70623601
    0x60f0d141203151320090f010c020913110604060c0308010608091009020310050f01060f02010b010503070c110a0b0d0b18071805090f04230c1212030726 67
    0xc11801e001105900c40545801c40390507248194113000b00901040d5650300d0748402c9802403107021180290610003411906a810801014010f4414004000c4020f40001c0141e0000320404061403029140500039049038089002c810001040b40c2e02c180c00c00c001168a5200c80d1051550110b01c4074050806400d12280d181884d050b9142e07500101520002041d403a07226460840d10180f05202d80c414020b1414486030900f41e00c0b0381c0c1200400d002d0280007940b04a000000c040c414011b8242505040c0c40c0e031465900c40c441d080740d41c3c45244405031044920180c9a081030307160700003001300034080c525055455500c56400710701900c0406103600e2140058a02000030b42d001111015000b034a28248450115400c1c3c641e4510322406a00041d40491103004124240036051092807050707105912812003450107003250300f098049490018160350100400e69140d04000d4200c0d02da0128050807560800c0640c0d402c103003558030854000e00003440240300405030009150703001041c904440c20310a21 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 70626099 1250 70624849 70624861
    0xc0306021b1612080c01050103060b03120307140c0c10030209030120040b1b0102070303050103020a05011106010504050705090d210903050c13060909060c141e03060f0d141203 77
    0xc0215006911540800f610303804100046242129102d80307110000f44041d603580c0c2040002400800c2d0400d00900408032803448170b000c400101e84c441d01003529008144074101020203d541c100007004501407007450301da114140d550100200311070f200c0d5071b405613a4990304030a05007502c00480c203101d06c02c103183c086034081041c2c01301510240c5001d01c401c00e4aa9030341d00d116809081c1d61913092a0507520000c0c4540c1410383c5038208905aa00035221800501d96a43c01150006240340241509800140c010720403458160000e90700b20510303103072440c1050000d20006102c033403050401c40d0180341c0400d500d4450492122005203417003041c10501c0c0309071f00d50744405480d00005620188140c01101194103045100d034000703006001d00f0780007041484000e152040c000c000303942030302c000300c1e4002030500d10040360b44044803101e0003291410308800c42418000c0e16a6040600784583c42016244480b4254403050441c80000740140a120310040600c001203041820a50705003000720010801c11107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 70627349 1250 70626099 70626133
    0x60f270f1518090109090501050708061309020f0a080106140f060304030e1507030509011116050f15280503040f02010c030324180207020a1802070c0306021b 69
    0x104108101c14015665503942d00d19040c1e550700041501c0d44041498008540e281c103981c070402c281c0344181c008000c0f81c1c03100102500c4442d01129450ba106081c040f8110034280c5940116420130300c0901450f8914880b100095200e00c06500140820780d5900d02c104040e01d00041d103c000341600b0740c0e00c52003d070030070008540d0300d110081024051110f041d400d40340c0d50700c4100da40802c1c454841c1c20141c559140b407030001c01c10340c010000700d4005008480301d00250b101c046024001c00648101c000c42d0245410144800099030580007a0b00040f5100c42901d86e4428800600342402203500a0001c045104a00c0001d011172840c003004014041c0104400901c200d1040300c2c00d1502404c144104058a04c2c0460250000108a1014a00e1400e15400f0030800080007015510250303e580342240c107100320042240200b00c0c01a52201110408010100307180c0c51100b5010704c005400f42ca88403150315484080c9050744e2088603d540d00083c00000703000c40f080462000a000000380c0200c501c6501456 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 70628599 1250 70627349 70627369
    0x19121103040803040c0513020903010e070503030d0b040902040606020703031701030812092d0f0307051b0a0305010e100525030f140c03040501060e01060c0f02060f270f 74
    0x2414018004007040c203001700051020000c0078000c0040310904642046d140c041c1d003000c00030a00070760800c222a0143d540c00714404040c2c0b90017600850820b0007107140c100181900122a40d0016075610801003d62900d025100c041c2417650014100c040c03a5241c010601e17105a049820200c0701407005000040346071044800564070308442e040380307031500780f54681440038a031490b5401c41e424035580c0e4030030b50240000d401010043e10550f80b1b2074003087c201075145d12800c400181150410104101c40c03814080302c40c1000303807000c3e00c1c801d64940c0b25070f103c9007180e281410808940d44481c002c40508200c41c000d15070b02115415012003481141040d0350b01c0540400103840c18551607150760903800b0071603881200c02d901c400b96030051034103000203070b000345078815201030f5800d500308007001c10408420341c0c006040b00e0003556940c021059540b101306142c6070441049078040ca0801c0805410b001400180508220083c1b80302ca00c5188240003810b0700c1100d07007100b4005c2003002001301541c0e49801c0d9103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 70629849 1250 70628599 70628603
    0x3111c061a0402160203061f05120c130615030c0f0e131515030605090408031902120702070801061508040602040806010605070c0504060e190e031912110304 69
    0x205074000c102a046200240008000ea0401d101140c84004d003040c2070443d00300c0c68020f6003600d04644038244800321580208150442c0c0c3c45840004200c14140005c465466284075002c1c1c1d00280461800645102c1144045003020b58880d0f03814004e590625440505440190500b04010402084043c04811813003114006100f400b2507802010b44546417948090081804104901c1d1542e24103c44a007840d4080c10b840ea42000602282e070301c0c000d100c1e80c0140c0e0707030080a19659a995540e0003d180e48000c090686000c00862507452140702400030340031940110303905051304d14107600000d15000e001d600c40102c43e0b040a60802c00003c4001c0012007604d882c1c0f400c0c070241da85504008010b44182d9011048500c246000041d07041d0b4010301520001e4030810010408036079807000c00c800d840785401041c40c0c100d1410003260fa15100403850380526640000301290f942c1d20803c646007150004444020030040441d01c16040c6a070007800841e08083c8103004000f03000b0710000c880844d0100400c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 70631099 1250 70629849 70629851
    0x3031003060b040902060a12110304050703021507020901120213060f060c0c03050f010b1809062701060b0d06060212041502070b040f0509060607050c0112090b040b0103111c06 77
    0x10b440841d850b01e070032542c02c0e2030300640516600d6245d000000c1c00018044500c84400c1e00d0003c1442180c0c20304011680a140c1000c001d000075803c42e001c00640c180441c05440e40a4810003030100182c03100b030b000c14000e181000c038030700801d450350051241d500020030640040500d80308091141003d000404800e4603094a024014010545080050030455400c00341c010700ca00b0200c0c007000041500100c04400045e210340001c004142e60a40090314180d440a150703822803000294440c3c24040b1401922100c12144c80718020b5440c0d80c542140d100360456444000300050070703a01c0c140c1c1d500844000b8804c6100802c600c0c080d00b840c00b42c003400345000741d1609004800c150f1220030310801007800544000c44400f583c550380c075a1039808001e01803160501900860000030014a022010386070440e420030003410159902c00c00442c1d0800e00507031000700c416900c100e804042030b000c1806910461090200700602d50460901c040c882d10700da96407620480b4601c4022071007e50130b401780c2e42e4550f40300300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 70632349 1250 70631099 70631111
    0x1030f11010e0d0321110d060609030b0105091b0a08060103050612071a0f0a02010510090e0c0111030d2309070312050a09090926090105041802070519050f0303100306 73
    0x11706000703050f078081c80e88441d07641011201c2100ea103031080207104007078074440100203590b5140020b07a04d9542030b103c040c046101e9100100716504042002e66031203000c06500218824400b4075950603078000901d000005120001084095600b40c418103405c00e10480d2401141a20301c403070340d66114014012040341311252684c007001010f0b900c3c180c1da4103403903803070f0856164665080c00078000c2c541120791051105005100080b03102c030354403400c40ea6814100190a002d500c400c01903410000301d14060000f40b0080003100c0b0700350110f10800392130b004101e00c0fa110052512803049084040500805143c1c0c00c0400f0801c00503151002506400c0400d0901c2610340004000a441c0803680c0d90020103440e040035400b4080003203000340308a42d91240f4480401c102030345900d60762640211616540802c508100900010440c080604030b001d03004640540b400210741c0e0790b00d0501c103507450900e00140d00c0e00c1510b410041d0034006543c040746404002c504526042150400e0303000c452002420300c5942d08 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 70633599 1250 70632349 70632377
    0x618190e1002070f03091e150909060b070b09060705160f0b1302041a03060c070206090a031a0705072103090f0b010f05010207141203070b01030f11010e0d03 69
    0x44000040845403680c119200c0405080c284c01c9400444411800600352007408151092601000c4080100344e42070150800c6c02c06400441d400074000c2c4640500c550881c0000fa045c4c40ba00495029110301d841481d03c070602890043c500d02809042004250000e6040003030456105080d5460602440300790308681e915401e01026a40181c4005080542c294080128110719016010140c2c1d109440c200300b4190107034800c030303140c0e880c01d8040c50785078001c140071900320483c140c094a00306000400c902d1070001050005605c1c42a41d900c110f07803100c3c0f00780d85a41c1e400c0803640d40603070040107404c0107882c4c113001360380e22110a003a03206404015000080c7c0841428481c0c1d0245c007038194003d1180040b2100ca0400c0c440f94a0244103005e141014800c02080e02d51001c5118402c5801c51089010040c20b54010840100c42c22540181d95200911098001c114030b1100b0500071406242e51110303c10850070005550090b83c80014140b18000301850040d495840b00c00180580600c1d010400e03a880c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 70634849 1250 70633599 70633603
    0xc060608070f080a0b040231091208090a030819021602180c03011a16140105010504060803070f11060d060e060d030c020f37050d030f0503070210140618190e 69
    0x441c03904a07044003064007035260310f91980e00c0203140c54010ae504c0d803460621240100c0e00c2d12001c50340641c0f01d420480c4003100207401056002c0d0003800c41800000c0b0418800c06480407030704080c81020442a1a401110075406d0281c01f0701d2410400714802c2e40f192030441141c0c0f440b0700c17040c4a000841701c00d00324442c00e0540c9040a0702d4410700344082c580c00840c010b05004004510b01e125890719946800d00000b42407610744500c000303d030200809141094800c0c0c4609000019004041e12104075403c8a505655100001407900c820b0421001902506004908a100c08000c00d424080c000d030203040404250004451280c02d54120f46c1c103e82071a13a180400e400601ca841c41a05413505d001501403005a000406406d482c060841408180ea44101700800c81500d0803002d4041806001120b440c01c0c40740c0700030b50344455a80101d92503900040c0a10080b1810b66000c0007180c080c0070107010440c60003071001211804014414811810064a07000308240c020002d450901c0d42d5880300e0202244c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 70636099 1250 70634849 70634899
    0x30c02060c060a06050405060307030b13050601080304060306060906051803100f0207050c09010b07080315090c0c10050105030c01050d090804080601030209090d050703030902010c060608070f080a0b0402 89
    0x102520481d12060307048421a035a40c400c0d40c2e003810050a040020072542040c3c0b2074988030344c20040042c00e00302e140d625001c2207030401400c101e40200311000b185011500801c442d6009020702d40c010755445107006402402c03290b240e0040c1d01005079030203080001940c03010580e0450340c45e4020524040c2d5013000024905010005c168031414100b150110303145a155000d803036814000e2040d00c500103051020800d07003c00c24042e0009103803041c005940441d500d9800307513038024601c05606d50810742150004401d84012a200010740000140044000c18103209035004810301c5082440903504010020b43c50300580c586260410030040f403c03080168064201100e803d400520140ea2a625410565101e22090000341e0282c4007036000308040307403000141c4210b0000346a46082c240306440d0703070490260100c1141070741004070883d1301c00d0110b481445984010444007000308405403501c1c00100f081351040d4040003007a003015410f00d004c00c0e03200c0c10700c0354010703411140400f2404445010f8090210 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 70637349 1250 70636099 70636103
    0x10207030b0601210b030f1906181e1103010b0109051909060315050603071a07020a0509160f02070e040803060604030c03050307022d090604020c0a0b1e0c16030c 71
    0x6001000c031001004c0d03a200b001500340a42c1500c104800341c41d000b0b60398400044e003000c2120070155010001c1802da41c4801c6864803402c001c02501000307525564602c2000c514140103007540e11031100104950007801c80c803074200a5009016044a80c000a4001c12203417007954040e54204105400e451313484118900035004100c004c011080d00c0e410695a424808156092500e00e401c5c0854031a2030006850700480d5140100e10001060070340c5005010340101d001260000840c410100d907669070459218071400ca1501c5503003e00b04181703802020460015212004e64100b100c0511242110265660740300d03401c0039205070b40340c4500003c1283d500c503035880641021602c5c04040104207000c0020302005008440d00e0381443c80c8404501030494805054540700f1404803400c11460400712422a4440d02c020300050402034603040d00ca0924070f981004840840c290310420521003111030030f041c00208961011051454000084082840303203c03254000c00180081c0c42040602c01c4000f42c803015 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 70638599 1250 70637349 70637387
    0xf05010605120a121707050a1205010e04050705060c0c040e2103160306050a05040504060b30030a090e0c0f04171c020d0509060408031801080a020306010207030b0601 73
    0xb800c4941d5035510381001c5902110751210030310400c4407407880303444807641c0682107881c1c0104903141c0c000155126030007080313070400340700c00305a1101c0780ea01c243c41028000e085058400e24203151a142c04c504280c41e0303400c1180310380c030213001100700c0107400034a903813005100351400141305018081e050314100261814202140703041510b4460b003540c8078051806040a00c0454200040208041e01a200c2c50302507a80c01034a5040c081001d80350030703040725412a0140c800080c00795030460100301603070f042030140c82d442d80300118140e42c2003611584101900b10040080c40c01e010007288001c14205182c4941c4503544442e5001c20254840e180840780215140c141c644d956560f22000303003907043c1d95280080028020640c20255049a518050380c244159601400710a07406000a9031309800104101d0b8000f013040c4004922410100000c00c0c20340220300c1400c08629500000401610006120f000c0c0c15005109200c01641c0001d000fa003a02da00218548541d510000100ca280d01d03411503100d040317 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 70639849 1250 70638599 70638619
    0x11070501020a20011a0103050c12090c180408220e0915011403150a0e01090b0609130c0306110702060304060509160608061306030b0411010909050609040f05010605 72
    0x82034000441d12079502071400c510003c43c0304951200d080f1852103951195480112030038111941c403c0d0300c074070b03808400391034002d08041842c44801612202110011481d502a2803000d0807072a03c00240d104c01d414901c41100e16181a07030b0340030b07040c0c00381c00c8006820000308401900790149580300c0101801517862000f240e4a0302811056039074191031305020b0743c000031400229580f47c1d00960040d02e0103000d0003c0c5510081d00ea004424444003d00080e1603e03a21019581c6d000e0307080c040c08900500032000480ca90800800b0440710318009030441c244a01c0c0c803e10709000840c1d9952032401c498002d14001840642140c21040710710a1010081d8825030000800c001c1200382d600042c0240101f0007194010440c200c00605022000e00920300480c01100016025150050b5401c5454070360708404103c42d83d0740c0d518010b00e83d000f41da08076507004c14101d4200017075074010b58003c0205040d030420f02150500001182e800d04015001825414280d422202070000942209004082c06000079800c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 70641099 1250 70639849 70639867
    0x50303030a1401090225032016061b0602070203100603050f070504021809042102070608060a14100c05100c0e0307030c06080901091b031101031401091107050102 71
    0x1400503000444000c0c0e120000070540b10140d2007525440440350700041521104040c48400c0258036000450030844801c0c050548030a0303042c2840c010211400c002c04840200c1c1c4004278140c000c41d000705080055003107800042c80040000544030079005030006075540c00d14008a070408041404001410f4240b040020400c0707000201402101d24050990b0b10341070301d445c1084241c2c818080000500ca80c20076146810f46800810075422510568606240017004101c800c00c0181806000000d80c10884003000700c42c0c0c100060592114044070507a80c0301c0c0c109150f81d5120201d6821050284c030b450702c10001400e01641d48820071a8000c2d0071105801c100840b10006411003002d1600042d90311100f160031070030006810001ea070382c49225840ca89040000443e80920014955070041d0f40301d502c00360200710b85951541241c030550308402030081c158241030718800c0c68080c440d8100f5143c48040f41d28030800c220700c0c034191141c0d101c000c10016541d401c01e1007680035480008c2d00c594400501446 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 70642349 1250 70641099 70641101
    0x8040801110c150c1909080f030909100302090a0b040906060b04261903050d0203040f1a0f011509090608070302040608030a050a050a0c200109140d02040e07050303030a 74
    0x4071809419088803040c0d490a490000300c40420b0711940040801881120340740400170703079400501c403503078981142d003151341e548103a00d40300348410180031503000080c82c0d401500307000c402c559000301c1d484034170300c0603901e5513010400b5a00020b00ca050481d58603c03071103a803560f550300030104960300890184140340e200e44d00b2024690080c412134080c05400d25140c0304810300080f01d80304a000b0070000d000003102580c0e0906004005503011000c2010810609200f00d200d840610700550080360185003c1c2b03c285410383d6100426540d04e00220390b00c4041001044141c1c21040c15240c0d05007401c9090a070141040d00c1504041d0000e80d0410b08009001c91544000250502206e00844092020a40d00c4010741d45a115080b81c40000a00401400356a0740c02030004000304030303803494044800c6881d80c50b0600008188464a03520510080a0300e40960344001c81002070002a05141110703010340c1d0008003039180544000b4021a11001040900c0070709000e808014800a000d60303650349403900c0810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 70643599 1250 70642349 70642357
    0xc020118051809070504090309290304050105090d031a01030b120109031d1203070305030c04052115221406071215050d1e1e03030b090402011b0804080111 68
    0x40c1e107201340d40d8001013900e0240a00d400d0140c0549494910300d0400740b4500c2807071480b05110344030241840c60140c40021040007140f04a00903000013a9500b080302550b41420264003815040504104207020740302c0d080740b05100c40e07503000d080c0010060444008540030000d40e40d000880ca51915080c03d003411340002c44010f811070380f26a0f11150301080420040d0b0000140100c1c055944180400000240550001d50700b20800504880c181555032001886610180c031110207000030740e0b40303210703458241006881344070440c0d6030600c0111310385924603000c40e54603003c04400da1001e008050003400b840948a00900005c001a50281d1610b4040a04050303621140082410710b85049805421141a007400036a10300030710074054251203484d088011080c6080840310076409418020006603801c05001c80012001001075002643e0300300541144e41c1e8101c86402020503408220050303a120036154000d528000c48140d61195500b440081400b50740c000c08419841c0c21014261150303a50007034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 70644849 1250 70643599 70643611
    0x1b020d020f0d0c080d0618060608070c08090d02040b0a03033c12150806060a0503070506030402060313050a030c020a24030b0105130e0603011b0c0201180518 69
    0x22400c4222100c07080369210070703941401002483d0340c3d10640004240340010308205a03880c00c081580d948074000c1c82c04c41000410058042662183c0811030300303420040c500d9000c6168144200034100c25100c201c5540310b46103215108021004c4154110355655000c07100390b1201130400e070704181e213921700588000c0c0400c541114040038141d0940ca510203800c004031040f01c3c490240c0f0b0ba220980300064540024010741c800320349440d004e000d14030b146460316510040c00e40000600c0703a414841c060080300d52641d00310070f01903082884148001d840301c900322034000f40d054880030b90b20340c1d4800c944030240f218030b04020503070700a40740160f0900d036200710040300c42402220718807500da0742e030407014960001a80320281c00b5120100301411080c080c1d4426841d400f01814824a00300c500e074040450314240d9000000210180740511040e42024482c11001c03c8403829030441040382c411000e0000b0705840c00c028100000455250f48600c8031040d0b4000502015150041001005107016103201e0b040342c103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 70646099 1250 70644849 70644853
    0x60803130806040312090311011407080105010c0218061801030602041d01030f02280b0d0c0309020306011a04050d03030203091005010b12040c0b0301030c0e0901020f030c0304061b020d02 82
    0x80070595900104407207006036030686400450111715401440685071594080d01030005000082480f140b082c01500386070a0641d01c400f03004c1c81d01d00b01c09480e21606800042c10407444200703040068540b40308c1e91344018440c00021200d030b6103560016038a125034502d000904c1708850000420032440d42c0140055800c18800250140c0e124010301a502400340700150040c82071000000141c10203000140e02e08195080b40c0d13580406500b841ca60fa0000307a4000c544148001408062446240c81903c000c0040e500e007d00c8121629000aa95248180680d5840c100d00c604031194030454902114000e040c0549000c8400d10740c2d0034058029081103410300c1281c0a1940000a560094400d460507212100c11050600d03011a10329a40c940b001402120710344c90410b00490510580d4010314000c5109480c4914103d040048288200340040e04509190b030051000d0508100414140e80d4172100a030140340c2c40341d4031800c1c12030182c183c3c000020141706000f449203081d2036012945410151081d02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 70647349 1250 70646099 70646137
    0x90c02030d05071805010e03121b1204060f05030a060e01030f030813031d0102010608120403170306060a050d0f0f021312120e120f030a090e091002031009060803 71
    0x40c00b92481c0c8510135003c10146503d03201844207601404114031035100280c100d4030845846114220039500040b1040b155403503040d261244c400080240c285010b4240d40070508241c50408007900720380c40610000c040c08808000203039000c4071070380407000800c3c500c3c18030320340ea507520308280b02d031850080740a0740010321000c0001c0c9420588141c000e0035a52607945e14201c41001d500b84062000e83e0320340c03d0b045548892000aa15108100031045080d80308901a5100d10b546403044002c290f01007580050340f41031042044507030780c000580b400c0d8051414200d55030201e18121800406d1048a40300443c0c0c070348205518100c00f1036000d81207001d070700a0030001c0e00b9114100d26401c0b01c1803950003042c1e186ca403029011a90f03c12413200184a4029119030941000425020b080090110007000c8580c0045004c5080c0795101d05c080c401448510508081400c3c11000c80d911806201200c484d40c80d00003010501c2200c0d015144130043c00b040710100099138a41101ca604c80e44416280889525080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 70648599 1250 70647349 70647361
    0x1060518011818020c0313080c010206040519030c0b070804062417010b03030301060203030f01050d0b0402090c0d1d1c050d0c0905040c020307050d020706050a18090c02030d05 77
    0x60b09401940c80e0a1a9180b80b800c820550b1491a950410450300c0e000c3c0200350700010200007804141c03050b50000e94131075060159403807421740e074010024119031001d024800842c0d4041442c10303942510201d068a1500d4a0600f81c605038a0907400510318040c090421440591020503070340280d100d00c5041c490901e1081c1c04101da04010b242d440b00c0c00c0074203e41008540020204048008030501c008581e540389131002a0968000f6403144015030000401c0000c40d00038070018601400b030072500c61581c1e80382030321404104840180b00901408101000c2003001d11204140c800407a0200c8c41480500c0c60f240c0314644d00061070712111100d216445006a41d00c6c1e08416181d250040342d030741e250174494000c40e4200900f41d03207004581404100b0b4004940344e188c9009603010600c042d00115650710503490118546004d0404c42021900300c4142401800d5229080302c000046516045520b002c00b0600f80d44242000ea11281a40d403410110f046000c2e000301c090f0035460414a0100a03581c2d0b41c1c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 70649849 1250 70648599 70648607
    0x3030e0c040e070b13030203030f0417030a0e042c0a060e0c010e0607080706060b03060907030902010f0507021504080105180f03040612090b0c0315011404060305040206120106051801 80
    0x44208030b1854000200c203002000b070520181c80440140d404861045940350040790540c2d000d100c241004820010b0f05024a40045100301c58421100303000b0351030060884d0004000710b14901e40e09114079110680e400f92001801d88e0740c0940244580c080080003104140c1c9540c9441405007150b03480d0400d0329143c0c008401003581e00500d90180c5507103651455180400ad6994000d0fa400c40307001e0400d0005602184141c800d420140208024035aa02c0c10000700b0090008802008202003505001d650300050f64000e80b1243c00584901b031054031b0741017510002c2c82995500c52000708801d4040340002e961081500500d0182c04808942030104000d50141c649803032500c0c1c011a1641d00c1000b08004251103541c003180346045580d80092103000556411110800640e480c0c40380820220522900e0510b6103000800b510742402c1150054881c03040f03030003841c05a0b03c588003c0c03581c1d5000180554031581c0446203800b00d10b0700d01400d103685400014015810a58940d1303030710b91040c040c1c840c180d401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 70651099 1250 70649849 70649861
    0x1b03030301121403120702010c1706010903080d020409090609020a0602071523070c0e0105010c0b011205070b0c060405060606161205040807080606031b22150303030e0c04 75
    0x2c00d60682180e400541c580707042044421460503858807080004410818284541e01d008038040d50022038800d01c10503000300752021000b02002c0030400f55041c0540d907030b00840240101d0342d002c410140c0300c056102c241002030246600240c0c129017005c1ca1078041001c60b1f808642c106208850800b270351603e500c0200d039605a18003448a110b40143c07aa1511903008000c2071201c003880202c0b0f000c00e00122000a003060304020400c5070840c0c1d04035801c3c401c40301c1048000b40900400c0c681000d14050589400300000010302c16542c1c401e44410b214014068244141c1000d060005802c0707554000803403d03035603100c80444081d5854007800c0085096454071100f00c4203410150300d1a1840c00d403094aa41c02d4031005591050240328040000050196003840b24600503d0190017030b0506240041c10f00d824216844000110180d10100140180ea07a9981d481c200e14032000c0324602d01019000100f000306440ca60360451040c541200008042d4107070041e41048452100761920751000d48188001d841c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 70652349 1250 70651099 70651109
    0x702090c040e040f02030a020406031104050c0a1b08070c12150902130c031506050a02062d04030504051801030201200601140112020403030305060a150f0302090d02121b03030301 78
    0xe84900850041041440071350307907030b43c001401d64444d0080c50740090212030080d4401c55081e01600d08401e003034134141c400e181d800070b0141e2195247c00c0d40400014110b01c0051421212018070384040c0c002d0108040070f80b41940c3c0e0202c8408a03c981781d07006071001010b036000c210f48403000a00c61180b02074480c003501c1d024603406031041c0568501c00c1003030005022946440d00405640c2c8106011317800c00b415240000340a6900c0700f40e070700c054190009003848001401c00c04201800082d003200007000910a07a01c0080b0f000030001c19480b02d11702228644142ea009a41c0b04100740c442013115a0b2070151181228802d880f48182078000003c5041e4200040e0200d10442e00148010405443ca0f110440b94569051410300140003164031843c040381c0040d081900001d503140200042800c10718402e001601021030340e500d008050304c00c010304404c1d14010b4002010703000708060019440b82600401e0711640109101c5d005180c400382195100d5408520400c1c490b541c0d0844c445170309002c804c80303050f91 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 70653599 1250 70652349 70652369
    0x3120703050a0c15050c03090d03050903030610171513050403080109020c010f18021c0b0a0b04060815040b060f0a0b070203031b0109111215060406080a080702090c04 73
    0x956029080e59010041001a907075130f888200c1c0c014010b8954425240704601c00c00d041c0c0d48900b0f020404506c1d110030624044103051030001131140e10b03100041560760045088502640d24084510300701e074031403611980d5004a2000509000d08110042c15024124100340c6080c00c9405403210240296003040d06c020340414100703c018443c05c0c41c01d80080004103405030000c10340c0c001c40000402190904201a00000e991440c0441145030080d0009039140004840901140071a20b60901c002c0c4007a00001c2c0240d502c0f030707410328662220f0300004006c1c01103100b95402c5414010321243c00410407981100c1d15480d17880021640c1c81d040382401603245001c0c0003004840d08141c078203901644a5142640d243c4810f009080f80c0000b000700201c0c007900341d0400414440c03198502034134888414100c051080c1107a140b28041c2d840c0c006015a2840600386414046e80c451002060007070800d90801c0c1c02e20302805100c00c050211950091020038401d0760004c549541d255080490380c000d5004444540b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 70654849 1250 70653599 70653607
    0x201021c0507031805011b050c0d080301090605150d05040201090512010906050a0513080f040e090304080c01020109020d021009080106080d0801050a0e0403050d020408010903090801051509010b0c1e0c0312070305 93
    0x1091f110041c000520400c1100c0c03800c114080000c1c40d00c54820301c00c845092000006214000082c0500300040000343c030420070001c1a400c2640c2d90340611400a040710b980e500010301568441d0b0060b03070080402501901d151090140c10901070015280c082e1825404d09010035a14802c0b44180351082c1c072040b20f145002001c0d5544c07a540d5901549081340316520500010840c2c1c03021414440c01021002c004665442c030307048042e82040140d0f8030441c103691402c44070b100540c892210a00744560b04a403a544c51200c545000d0b55801c40ea504503194541c40e000e03004c103d810700050000c030340f03130704a807281d8009a07a900200320101d0003600480c0c110706c10840201e40024000d030302820010039884005810644c96025203800c4404405094002991716101007000f290207114541e004000ea10007406990404004281900700600c41c003010070000044c0c11001d101c1c24051003014003124a4040d132440c4e1807580303141d03481070910b111612902070f084100c20404070b800200c1c1c1f070060307068403010f0030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 70656099 1250 70654849 70654877
    0x30715030c20010e060705040506040902090d060507030c030b0f030a1704150c020109050103020309060123090f1803070c0501030b0609060304200d0308010e040201021c050703180501 80
    0x40c01c20129150706004071002e0158024000d00c0e0844403401c20384000042d1110144103482c07801201410010a02208010034442c0c0e407a42d400f114180c4da602e07840941d0302d03002c0201043c4035800894000c0d22051806041c02601e070f5043d0800c56007511703950303010300000008c0c1081001d5882c4903446180d156022100301c200143c8584a01e0a0400c6a00641418160341d039602ca4005071540001c035000807250300c0000115030708400d4507800340800f03180131401d5103000c8001ea50f481c2c0d4180a55604808003985005070f5007880d030f03a40709a40d04082c004100b5410044001030a403402555010342d1210414054403102c0d0300042910651600803242d00c42480ca088010b40003014600086500441c1c204482e1481c1d4913040000c0d401284945071200c0720380300c4540c649090500810300e1a2003035040b10280e60209a0000c080c505640100700c0c40e10064446100507440d1602440028a14034019941c440c62140c008000d0f0a42500030744a06c40f100400311844194082140100f50108038021500c3e20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 70657349 1250 70656099 70656101
    0x30a050a09080301080d0305010e040807021e1806100302070507090908270a05010504050109061d1005030103050c0301140f040507090510032006031308091003050a0b03071503 77
    0x18114031828800200700500e501c8819082e0b00980011034140d1280700c00c805002d6061107081d00405c0022203180c0e0310704160341d0b4070055218101d0003900c103507500c58a03050500401a040fa140c08802086a2100c101e85100c6032011801154180d125040111003400400c0c001c0c0200c03024107500002030002507061010010042090381000c0c0d4007140144003480585600c148400d851408403c040301c1c041d8404010040e140d071094002d03504120060104212998200340c2040549441e401c0c00100780340c04030903080050460564481d4042049000f08042503003080c0218140c0e4001d8095501c0c0c0d1801205050030381c4d01c2c3c030305121a99109003002425000081c00c2c11340d04603214000f920350f80769580c07a00105030f90094803109074650304543c1c10000c020140140c1ca80c5001e10310075507210340200d200015054040140090f6415507070140390400c0160700000c03100814002412044190f0380100c008000346000c844a09d800c91070400034606501e400200013048420480c6000b0415051001c00c034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 70658599 1250 70657349 70657351
    0xd0e0607030c0b0c0423010909020f0c010204060509180c0304021002031b071409040506070804020d0b040c060801090b0a060e010c1e0201170907030f020a0b2704020c03030a05 77
    0x3404006a0020120003d202920b03598052070840040685850403d014020201d000d01034085116910b03005041d680e0743c2021450040311030f507920058a440d07c001d071000640c400e036851050594800a03002c2211a00f00000d008101016100440202c5515403101d8071840700707a42c2082c622205000140041c5000e00d286200300d00c907881920b0030103034284450b0001c00c1403054410501c1e0440b00b018000704401c01107100129408441004542c03c2c90340f106502c1e100040c09135000c10207801e00103410354646046001056030700c240100d00b1460a0f007031810b0124080c0c05400001403c00c070002030700c6807440c091800c02c541c00a00201182e403610074261410307020201810f05008445443c600403400017034000c0c1780c901c0c1c2c035071804100d412284001010040030795141c00ca040004800d0007000e40c0000f61210903a84e102011922540842c0000380c0c1440b480d6000c0b190002c40014800d6195170311401d6107a2011524613004a031100e0f070001c10069000d81c00d08201942c0c81800003c02c070251a812413 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 70659849 1250 70658599 70658603
    0x60403081912050a0603060b01030b0d02040507051c060905180303130c05060403050f0609210c070b03011202120c03030d150911031f030c05010305070e0301020a0306030302010b030d0e0607 83
    0x3091203401c0180040c000c1c0d03001203800d088245c0d40d0308402c00a004460140b003810040034601000340403800303000200d1054555a01034000c0f540d80b0002961107004008071504c002140d125814400300b404100b8000d00014001c6058142c10321012070880c3d84484410100321610318055401d40e5181c1200b82d1100891721401c0d0f81d00c50165400042c80e45903c3c00400285010710f000d0003e040071030900c1441c044000d0084a40c992214080000d0000c0c1c149859aa07070710031128540d550b0001c0c2000604d0301040e038106640304400040000f641034a00c68803044854402c4c0c2d02d00c41d501c11101d01041d100c2680d49115600364104201c0d081100515610140e102088403211036030958a610101d070444104c01d98680c001007000080c00070032500c00c131000c0d0140b011080c0008401d411552840100201d81c40f601c0e044c5515800801c45071405142d01d0b06101002900854590b0380d0704100802501315403000750050352a15076020300504010070114241d412688540713a410004009001d42075101c3d07081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 70661099 1250 70659849 70659857
    0x708180705060c010609150308030105090c0d060603050708090a030e0f0d0c06020606090f090712020f040c0e0a06030212011a19080109060b1606021b03040f060e0604030819 76
    0x49442e6841c40082c0620a031510000603403c0c6c01e212841040742d80c4006407030b0714001c0d03030b081c05c00009a204040f40e0540310b003603407038406903210310011580c58021500e52800701401c100300801c03144d130b00d944070f2489250580e441000b1500c4400307880e0b80341e6031500c0b13018001601d0600c40e40482e0400302c0c0007414804020f424945612840c0d29001801e044580001d001a00904188141440c106040b01e8000c0380205502031300b803d04940c1640d890070540f050303620001c0c140d81c141c425559804001483c200000d0010301020f554410020700d981c03215968640b2880340c113440031485070303ca803081c3e82140d540349040300003590a101108030f1039064125500000c0e14200400071a501050022104000040d160840e0755410b2132100e0043c0c440b00c1e04504003100b41031000842154804103280c0c2c45030b821441c016039a1226185181850aa8000c2e41d1b000344800070340000e40380003000460088501603034451a000030000100714031032240340b00180000c00b042c1301d10030740040d0178280404101c842d405c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 70662349 1250 70661099 70661113
    0x40b090402031510120809030c01051c0c030209040c030b01080901021611060418020703020705040c080f090f01061202040f140c0c0c1f0212090114090a080f0708070806070818 77
    0x7201020820000006c603000000030811780e1482c10100f041c0b8012840034204107081904500440607540d040c00c0c0a08409034032140c3c1491194000c0d81150f01514020f0010701030650800310160141642c03280700c0f0300040d42e40303000445481061094484000507440d01400d84c080756102c11001060105030250322401c108800580b0721141d038a0101811200040941c541d009806c3c0642440c03859881107000341d0070001807401c03459000360000c3e488030000401410b50780b156104c0300c0c64600c8100e8649195803030008080380d031001d41030190303613142c1c401c850070b01000500c0c0e80300760152604145090001c007001c00120380d00131510006480b0705040041201c040f910003e0000360903043d0503c866103d600c08500340b19680341d05208444106011040c03082c07500b452440000e0141c02c0d03164445440c8400400d00041907543e6180d40002042c29808071101d0141a085280e103400041c41000380301c0c411035600040c080070201c0e40c40d1040019844081d510754883c94001e440500782c02c0808801c2c040c0030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 70663599 1250 70662349 70662359
    0x30f07061401030b071806200a0503040b0409050a060f1a0910090303022a06090301020705010501060314010e011d06030c0901030309090c1b03050a2c040b090402031510 74
    0x44a914021406056101e105050803170300548041e10400d1803900207003c82406210182c0c214000310340032000004800060b00c45c1c100308505240e001900144a03000c0010002180d62001014000703545165000300320645809948504642641c4100f0b11038804045081112101c0d5050303c0510701c440715000b610301040300002030342038400755040c000451282d02c014814503504201c1080703842d144407000b051500d07007800648880b022003100248035000006072640d070303920290181e07108207901c00700034011035842d81009005005403420381440081c888000090540d0300c460201d048500d18030301d0b003a2400c81d01607816044440100b429415104085024100740c0390096a10700941c02a0703581800300781000801ca0540e100b0320800d0007044810f558183e2105c822507001c40556034107041003030350341070207140a1300ca15616402000740482c1031541d90007a11043c109007488010308031410002d4000c01340411907042c006543c044c2d0513911005807486610900b1007215003254904020241007a035070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 70664849 1250 70663599 70663631
    0xa0b0f061906200607080103080a12020f1e0304170d0204350f06060d05010b03030a0201090b070302120604050703180501020c1b0603070503100306061e05040b03030f0706 75
    0x16520410016200d90f01e5007070541078030b44503205002903540c060400b038103262500602c0e085041c000a01280e100280302a01d181c0999418440400c00c81000c2d9102c140e2081100d03a10f8000568440e039140d4440141c030590540f0b00100ca200340d912000b554201c00e4100043c2c807044c0c00c0a016044106da003040041107003800a80310150300e1080540011519091a61590480d00b400700400f85562140d1140b000200c00410002c3c0e00c40401c0c0c03036801d6202001e0810a0240c0f4000d04a5901801300040c0041d929606420501d0311501a201d03050721610b034582c0440c00c0344101807020b4400910040842d0192526420054020000c0d2070041240405242500040c0e00401000c8030035070350005074200704035000c5c80140c10f6452502c140409465090000c00c00901c00141100204000040050070490f151441c900c0a160004400c00081351504541001441411b40000d0480174070600042c4524050103002004100500a18242031440980c03085a0b0800d81c000c0b13031015120303400c1d403105440f4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 70666099 1250 70664849 70664899
    0x4030c0315060e0601020a14012c010510120807020d05060c130801090308042d0803150301110a0e010c0618120c080403020d05031611030c030a0b0f06 66
    0x1080d8000359041c0403810036084070308035402040f031030718018100005a0f0b008030740d83d41e1168110701e01084407521140010b006242805180703011140c0310020215181c50544c101401544003002001146c0390b01443c00500403282c45888100c440d45007000e0002551000505841071025040b07880741407541e500d00741800c0044132003005000780800c26000c40030b01001a00e00418107000204910500ea4400802c01000144082c1807462b4007203094a8590791f40d801c10001100d03503408101c02c001c0300d02e070401c483d5106945d415041c04031060151420715040c480c10300b036100301d080c00a15050125805407509201100c100741480045041c04010a01a00501c90784c03054070000101c4190b030714a03100e52803904ca07158100c2040b2700b984514000071215400c5a00350703501140c0c0000040790900c1c3c56461441050503440070056002c990400300101b5407410061440308805503221411260181995102404006045400d550011504c5400340303903140703500f09001915403106100ca02c017004490400b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 70667349 1250 70666099 70666103
    0x5060a0201020d050c09030d11030729040605040308090606010923030f0312010f0e0105040908041203030b0a050319110301180309090b0a271d06060f0402070503040b0c0304030c03 79
    0x30006c4c1c421a00c0c82c0500080340340352407508007007543c105140003450b5a4050604000c0a00b511030000340c24040b002e8250b0142003000c207209403041d2030140351a4000d4101500c0850100c0d0012002c0344140a011440c507100740c0d0103941d00140c09240485081c051003021070680101018500345440d543c50501c611081030b10040011a9602c540705602441a50f0581c0444018004d2801c24480125110340c66411503030115008a002004c50910340580e1056900c00b10a00c00d034004440105038140d0401010701d40100d072036007803650f0b43e8400d240d12450242c0072001c0c1c1e8004081c1410001c0e41c1c0b40010442c4200c00750000550b40c08034890100034410090068007c1031000e80d041004000c280104d1808036002d440491400d45080010100c2c0c02d00d036180c01544200100b451420040203600011510348040c0300da820030441000300580f6034a00307139150707401544c3c0b103105641d45040600071903040320352000080d40342514180f69001c00707800480d000c80302c1c1c0c0020080000851501c0420202840c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 70668599 1250 70667349 70667371
    0x151502060405070807050a03030e06040b03040317070306050f0108130b0103050601030c0501140d1a090115090837060f0b0f01030b090a0c05040e090105010314010501030c05060a0201020d05 83
    0x20a141c2022403410295074410304e440d9000b10760600054403030b00f0100c0216503142c20241043d01041c400581c0c980220f030850450a14040f00300014140e2000b40c0d0800c400e0058841d1002e61901c1804030191083c038020250000c0001c3c01001d03165124201c038039400b015800c4d01d030f0241c01c0310fa6907c000c5154280d0003500c4c1c3e94031041c018818800c80d5070040001f440d007428a80d086401c0d070f15103c51907000d03140d01015201d0361440d0210008031000c42e1482030480080c00f11040b581c40c9c495040f002c00e240c5007904002550700d140801c1099001840201d0040b001da1000c2c03c90b44c0340c0250541c081c6003010044958403007030712040000b60042c051214040f51003e00419004601c0c0300303000c038854000881c1d604050504540d906c00f52151842035030042c00b07042c404680180306020a4801e4412a4001d02c4c2c1d40c50843c0c204980c841e410361116040e684240042c460400c42401e4290a070f420a00002d00703614490034013040903240000c0100012140b6000150030440050041c0003101e0003190180504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 70669849 1250 70668599 70668601
    0x9130b010f020c030d03020703110727050606041a0418140f1006030b0d0530070b1302120a05010903090602030a0e09040309030f080a1403010b0d15150206 68
    0x20360300319190401c0d080703051005000102035040004da0701d910310207207501030542c005400f0041c9841500c441917142c0f501411a50055541c4000010b034100d050007403c15004d11209000350385100b40561800760350002c0846040a040c101c9540104000f40b66122042d08104400103403a456200c038a10201c00340031000078441c0d0300f0685601034090040094124175940700412140ca1100c4040c841541d46c81d117400120600300780c010070303103043d9a0600540144550031581106d41c800c402200b82d040f03282c07523207400e0014032202d14007001e004040d00141490072400c0018114140d41141c054810700081115120740400c408c200c0c1020074541c02610281d44403903601c8140742d0081800b0008001600c0110714016400900404903000142900e1081881a000c5400e061040c0d10180285070050340c0c40d0307850b035024506000c1580c001c0d420080800c821444103000240d490702540e040b1000c1003076003441d00c442e60402000500702c04581c400d0780c0307007242c03070120701c001c010710040c2c50b1014240c00401c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 70671099 1250 70669849 70669871
    0xe070903150207020907030c020c0616170703051c0902040905010b0103141303031d030a1107060c0c090c090b030c0408060906010302030717031e1c0606020d050c030913 74
    0x11014003000d940000c42c01000144016100c00b04840e600215500c0c0009042d00310303880c201d05080e00b10740307196440380740403900080041e40e50b043c0040c442d00c1400802c41541d061b190382c0e10703140036990010340462401e00c0707c02c8100d034841350001c0d640001017100081c04929640020700f102d802813025200b0340c0d50340f1402c3c20103503054401c81d00001c141c005851440d1804641007041580b44001c02410161114480315030300c1c2160f1500c001002d410f0095a07102c03542200300400c0ca104a501041003803103000c0c0b000820500a1088030001900072058030307a01401d0210100191240d02d031104100400444c0004040341040061030081001340c09441cfd646141003a03580c94490003500c00b1141e504520700400059a0016140c011100c2c8e0b0030409108481c2c900c0070500f14040d00200c1e03100c14180240c10344809510740d0050401e00d061090384481d60910300110011101d15004034409640b03c01440003040d8012005012900d28244c120780c03400344540040381040c5040904075107056126100c0017a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 70672349 1250 70671099 70671113
    0x11090103051f05041e020d200a091a16140d080603030304020f010c0606081516020d110a020a0803030105090f0c0406050a0c02091302040509030a05040312090e070903 73
    0x14000c1c15014a120b990842c00800da400c00034a44111807080d030385ca0815002c0d00010603030300c0c0740c2500c0c01c40085450345441442c0380701400201c400701001c400351840035aa40010a000e07101c003185260b440503081414038652107045089851010f0500700c00707001103160140302c007042903030722840783d0082d0390030b8001711110614000103206214144014201081b2041d20000252940903404445800641003282d0040c0c46294004801400580c2084004600102d00003841c0240300c0407059400c0c49543c40710310386400740119415810058021845500c0401d00c60f503000b5a400000790b01f502c0307110505500180210b04070368001d008175000800100894544091040da114040300b0f0201d0b00313890b00c90201d021078031650050000740000402c0318040c507031003149080e201a5024102c0191402c040c0c1e010603445a00e075400301d104600303000c000345101c80048151843c00c0c0441d100d4a003450708650300c401840300d580c1012030410481400c000390044085040318041c3c403058403420252402c50038085 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 70673599 1250 70672349 70672351
    0x5070905030607020a0b060406061d0117041103060105092505040503032101060302071203020f040b0c0a02030c011d010c02060c0706080a06080312070c050c030f030a09051903020d080c011109010305 87
    0x1031308c82d62078484104940b941050700d103640f4040b4a004528202d40c0200141d50078109596290740d07403000c5008210411080d03c3c3c4a040f0408218211034890ba80ca200300300c10b1003001c55528038400c02246100307000c14418500145403204d5402c0003030905881e9400b080c40d5400100300c81302440510460b02c5e00c26100800d001340940264a800e51a18125844502c1142003201045040550006243c40fa090245040d54003804099a03820b076100340c56803116549501202040c0e00c203000b0b00115042a42c007403001e02c6003070040c08101e5113103400c04200658941e0b601c400180c2e0400800c11a0252490703043c00300c040039208603101c13101d07507041600621040320025006000035a1041207556180c400c41c0b079a070f60303106a0901d001c0000400398a05541007500613109140c02d0b2064518100c007a010100142c4110300d000d507900841c90f503030360303003001007100769110307490312040300400144050705101100ca05110f01665210b864007076600022030841e140a4030f0550960004210180c3d5580d041c00b580d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 70674849 1250 70673599 70673611
    0x501050a05060403080a140708030402031e0c010c03020f010207030f180b0f0702030f0601151202030c040902090d0c06050a1103090a090e0a060513020f06040b030a05070905030607020a0b 82
    0x2800d45820070300840e0039440789000141802c0c00108070008010f02c40d02031000202601002541c0b43e008a2074103100c20313001524220703c40c1c051a0344c0360000d51009640308000c0c82100000388039442c05107006603031000f25403505400314016800c07240030350701c030134002000302e10320a548485420150102c01448034071641c104c800302c200890820800d040f03030b120581d0028014880030a54510302032001900d0500c40350301e000e00c107000b5140005910500840c116800b051291a913204000314560107a00720303c002c58500043c01c03030038081409082001c6c0d020700000d20026120481c0303504a83c8884406044036400340002800000d0101c402590086140d01a140300d40001c45c104080d89000440301440d502402c5900c80c0d4034205120141001c000418266420200401c52130800000850170303120300304c4003607000344615a0f40c00c4150400f00e04807030032a4800b0107041d046071500c0c1d5176440500400fa185104000c09400d0110b4140d809004250181c5055001841e910060740ba00c9038600000400c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 70676099 1250 70674849 70674859
    0x5010513091104050904030801090c09080a170715050105030118020d0b0c041505041403060103050d180905070806040605090108030405060c160807080f0303040201090b030403020a06050901020d050105 88
    0x8050000c1440c5032110190756900c0c2021403010264076185003503002e030f0b600055100c94150b00380000d00d0340090665040e68a881d40920107400e816400f030f40e01c02c01e40c2c811445130394071400d82039000c20202c8868428620018605a00c3c2041a80302c60046e101c0300c0002d420200d90310b9004018600d82482445060103016011640104040d00050051f003081d0030098010b00c0b0650020b401001c0f04001c4602400640c0100425107822030001030003070b08a8020060600d007004400c45140c500018070904884e07020f0014041d480c442d9070112040302ca81745078032a05040480000c10711036900e004691280c0c542d503640110514260080105840f0207511440c002c0c074020006015442010040300c003551302c1035604030f98a001c030340502450031181d810076103409448442e020412181c0401c15204031211401151400522201104d07102e00c420780f1b000740071403c200000c0010700900400307568024001d0041d10302c92201526030400ba80e0003102d0810180e5800900c0e481415094400da5000d0705007518 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 70677349 1250 70676099 70676107
    0xf06030902130c030e16051908060c0a0c050703060c08060d1e0f0f0f03020607090b07060c02151510050c0c040506030a0c060302120a1a0111030f0705030a0801050105 73
    0x8180c1c9181d146110b00300796a1540707082400d003802a08000341c1d9074000412a40f412401c605004000300c01801101d202e4142141818281c4030741081c0c0d88190b0360b00c031000d4109a169203504400503800704000c0002e000400d00700d6008100e05114101c002c0d400303100b0100741000e41700f200510410005004c0d51064158552400200e850a121405043c0403004a00207010050600d0b2140b4600942c0040c05900c403030040030204400f080d02c8002040c480e400702ea0660f00e80c01c02c00d44881e200790041c410f000600303010300390101c3d042d900503620f09082401501c098441c0700c04c8085904404680710072000c280383c0c200c0c0c0840c1c10502049003544189152490070003080c44102e03502e591085803920b01c02c3c2e840320041101a44d09204518030715600246001c1e40e03075a114806030194110030300b00d41403541804001401e842d01ca0161641c0541541030380c4440c071031114010740d112440f03100d0b0000b0720b110600590307118046410040c00310034041e40045803501c4038900007e01205050304058100701c0180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 70678599 1250 70677349 70677353
    0x615020601051c060e0307060c08130b040c031208070207090b0102070504050a11040303080a0605010e0d020112060f091d0109080301030f170d05040308090309010f120204120c0f060309 81
    0x1040d050306403001201c09a0000b0104910354401601250740a800980b0b170441c00c030b0358000c002004010305032040718107011243d00a03005a541c200220b9503103d40c1d0045c00d01c4040000c0700c400645602901c03a8598600c00380d241e8403030035440561401c0b81c0020481c80c0b0b041c80f010039010403880005204182003440000407400c0000d48904c1d90784200c1e4040c507110404500058055000b03501c1500d91101c004d40c0b16544c0703040003803c0c00b8081c0c4000303003001e180240100e0340394800d203030700a41140d01400151301448107900444a145e0751415a0b41c0c21540c0341d0700882e900b902c4524607002460b20034030108100305000e0141410740706c1ca100d03031802a071410040900241d0620305036811a038000c1d00040308582c00d0304018403103030001009201107901c005440c900c455170700d501607070040380039540c0d8204030743d5501800707652031046c440c41c07030f01013040c5460503290107200c0c1c201016035801080d409070034165290f0700240c045905080031100e01d03428017414410109544203090040840e0300c0c0c107001400141d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 70679849 1250 70678599 70678603
    0x7080d0c0908010218010e0f03030c0a03080f0c090d050c09070906021c02060705220303050301090506010f0e0f0d0c030c0e0f0403170405010b090408210c03131b0905010504061502 79
    0x20b640c10b100e1f140314004015a103510b242c031001900607041d03075a107d031501007407503d800c1d1104045011540b864041104050001686c5100e245801d00c0701e49001f200104110011019030811501c52003030196150b40c039125084003c0c0203d21549441200e42c2c107000000c3d042282d18015411704480444130564280e90028406402051a00b015a501c544040c5200c1c2600d0590218040321403070148000708040e0311600030750403198003500802c11512800011240c0c080c41140190002d00f000d0000491403030155038140448000602c00e42403e0702564840302510300b80e500640300b15440280412181440500540d800381c04418618114681598040c128006101c900e17000d03031000f20009800c02400354007221020200030400b060a141903d88940654070004030100145c006c00d003c3ca1007a0a001300b098000d80302e1511084c11640c0c2c589080261880e001d4041c0c403d514510007100d00b040c041c010a401618213501d006ca0070b5070402c0144400c1da0420b900503580c0007201d42010605a80c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 70681099 1250 70679849 70679887
    0x150e0706020d020a050a02101403090c010f051e031503010509011d070b0a0f110a05010e0c03010908090603060d0b0a0603020312040305031812070603061508190e0307080d0c09080102 80
    0x1045441061088d45a00215144c03a800e003d2014001c0001081c0100004000344100424400341d0300c030100300b01e40c0e1904896a0095418200d103c140e6608052840c800340005945c1c0012450b83c10100072101030000703800d641c410341e08040580d55501d0500180102202c00c40d1859444400a041062501d685d4039014810008034000f0441d1040384420403620030051000103180010880360700040e5820300c1c80c000d10f40301e40b50b200e481c412044007030124281800f5460401d604802d441c0e040c5540300050060300d80c0024801d40d48207090b4903041001408140305203014081c0000b000030f40302c0c10b6106040c58900c20a9203417070760100501c800c10004d103000080f160004c200502568140c9029030228012a00c11501424540120304000c9640c0d030381f43d130210080300c42030301904825184241d01581c0d4400c1c142c5410003240c140c11030340400e81c051038011030a44100d01c400c40b40391503074503203030900103401181c1c405072000c0c2c40d0362003482c4d0720f98480b400001a000c0100210700d8054804904455150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 70682349 1250 70681099 70681103
    0x11152202030d141201170d021b060c0c0301060b0c01060605090d120c02090c1309020301031208090307060204150806030c01120c050c060a1b020309010503010302010507150e0706020d020a050a 84
    0x14441050700e1542c0c3c2c02c43c0a594003500900e0980c01e855840e140d011140c6203101922200c1e03440381154031495103100249410340031515070300030861141d502c4180b08456201403a401c01600c0307030011100c4203442c01d1064a00405051852135110424040c01c43c0c29504241d022400f001000d010f46140c83c0c7d03c1001151040f82e01c110802e40614820303a081d2030a07a21040701a62014480c0d00b08070522444d00c1c0140390304e0425603800d6028544031614801280003c0c00090b0010680c0c400d13904001f4041c1204a130045450740c1182c0c1401865074800043ea8005d82118403428410915550326036044002c0680040301240a85800e44940c80024800420f004100c0c401c1a00c4040111820f0301501c1107c00d034038244802d130f9069103016003006015242d44030703540c2151070380c1d045507203101c900c040141c40403110160b40784c910707503481c503001158141c00040d410b484c0c20400d84149401c00c5254410b6000e02804a0040c14101c0d04d4040081d0812184018440c00e540110b00e01c00300160000c81e40040140d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 70683455 1106 70682349 70682357
    0x90a0b130e0708070b04051005040b0c0c0f010813080306010903140703050f030307141315030501030606061106191506020105061f020607030b0111152202030d 70
    0x4603c52045c100340320000e0000380401c4c5410440c40b0101e04107443c0c40784c00d05407038076040c51710760380600385100b042c0e401016403040508101d80b04580d40e043c00d00f800d281a24000a00c00d403441e000007001010020004000303030f003681c081e09414000d917401007001c0400740c48580120b41e94010b103000940c0e091140046030782c1a00000402c90748228040e4ae0b841180d00c502070621026500440100e8000c29441c41020811b4001c5241e21882c401c541d41c0d0118a82d495405c02c01c04030303003490700300008000e00e000d0a85501c0c1c40010b140742d000313800440314100040004c0c0408000f0f200e101c011040d200001440014080d03415001540078210490b40806202c60007c032608500004d001c0380c00150300302500140940d0b00075445900d8200c0107040c220607082020105c0c40c140101c04441c0c5201c010700c801071240780046400344403003404180344182ca100f00c9940029a45041c0d0200d20341c200 = true := by decide +kernel

theorem cover : BRFrame.Cov 70503599 70683455 := by
  have h0 := BRFrame.cov_init 70503599
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70503599 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 70503599 ≤ n) (h2 : n < 70683455) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
