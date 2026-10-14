-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0489
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:04:15.442322+00:00
-- url     : https://prove2.me/submissions/73a232ad-ece2-4886-a08e-a01733fe4b72

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 87769785 ≤ n < 87949641 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 87771035 1250 87769785 87769811
    0x4031109131505060906030c0123190f1b020609010c060f0e060702010b03010e120708040b1c0f2906040302090a05060f01140a0305060d0204091b060e0f04050406 71
    0x602c1d00100300d4020000c0c441c01d01ca41030000c0c2c440c00418090080d8030803403c98201d030780c0000c0d400c003580780e0800380c0c40d805940c203060000e190700480c500d10800d070180340ca4613107856406c443c0d00c884d103c0c41561410164550451110f4001003215406900031900300400c0a40c2d5114803080406940100070110340e17220f6400c5828201c4580029007031850308075806000480b0703428054048254801c4000380f0044600c150800c0d10b4170320125640003452400110442004810000d0360300400464908948640134405182440c4421146081301c0c5844c0070f0302003091003100d02c100381c1521145c0e20100815100c00c0580030502800c2039840e84d00c484107000000041e590303490000d21640300700780007041030300b00b64040c026000500e001c000c1c148604100b03602040b0003140700b0744014000342c0c9004115625410007203032407a0285480079411500b88203014042c0b10b800d40d66172076219001c00c420540240d4a1030300f00c030300d010405a5254007401c07201404c4900d250a8010a800500500001842d01c45070f2074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 87772285 1250 87771035 87771053
    0x4030503030702010506010e0a03020a09021308120304061d0a060c0207180608010c08070c031b02060f0307020705040b060d0b0406090e0a06060b0f04050d0f02061c05060301020403110913 82
    0x1140b60040c0e460b0020412107581c02050300381c0d100801c1c4c400002280c11540010b80a00e00350250b50001075001c40c00c0c2001d6094030500900030141141034528514508414012316441101c00b0381d00241031034070604c038040340441d841441c0c40d00500034250f180c6091741c40750054420041068218840d902d0089105c01c4011300704a064000680000f410514080c160360a40b041c80c0c5020080c482075600300606240c100001c08000b5a0620b048034061300740e0001804042c0001d600a500100049a900048102e510040d400703000c0c0e640840d1066590396040009640c1e030240e010390410000c0c04814007061450304241c4c02c50900406c081b440503121a00141100c00440384a0380360f80c05006441e0612100c0d100d468064400b02c1c0b010740c41c0100f49040c0c008944614402e050048006030389142c113000110903000c8200394000e144523914942041c180f5810000d40009545041c0341c44003040f020f24052007250101e03980030b01b0b2079901150303100c00c201c0741c07040081042d080c1c1a00501c0046c0001d070110 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 87773535 1250 87772285 87772291
    0x90f01020d0c030e0d0203070222060b030a051005030c010f030e0a050a0b0a0203040b04021002100e01020a0924030c02070f0602010603290606030a0b060c0a020f01090f05150403050303 81
    0x7440c0000d10b401c0e404001410788400000294441d081405480c4c0c1c079a03400b200301c0308099019119518003103541c100410000882c01510061240b07032000120b15544044000c40c058285d0642c00c1c891929612840c4045184521404e075140d403100c89620065402035010f1030a0448609001407000da00306100c1e41482c0c030642044030035411100c088410803600514240d000452407030110f09603c0e10b41d44810000d5130141020740303d0500d150600c1501c500c03c000c0384442401c00c000600c403941030682c03801e001c0e4021040100100d0302558003c0361100044000003c00c2c1c0c2c8d400e03c03c85900e1401d250940050031001c400204501030300c1e00100e031a83e1004984002801f046c2e00028190b443c41c1007403501180b240020300c00008045058048070680c82d2080c0d0b4001c88102c0d040c5980c2e803228a12440100000d25619800c090003052007a20b003031000c517400700c50900a0350b030180700c04c214400449025001c0d002e0302c0d41605020b007003805103090284445640f00119064186001d80742e89820b45960021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 87774785 1250 87773535 87773557
    0x3010302030105010f081b04020408010906050114010f02030f1308060702030c060a0e0c0f01051c02070b1302060d0b0102070e01140a06140a03020d09020d0c030b09030909060108090f0102 82
    0x100118202481003500421962810b180390314104031116440f001d01700050030003e2041e030b03078107074140d41d86504840090111324001c0048480324640b07940540024400c201c0d00c40c016a1070b440325540102c03980e4007014142d9010310300d8802901c0180031a50003050144012054841c008036030b1107020132000b80150301e5500195114982c001c1080c3c0f50960080401c0c082c030b0b0a01c0f0711840078007030004402450f5082218107421420442c001241d0500071662002600003440d0a481d80c1c401d21913004110850280c0d03d10201079941c0d1145010002103200004e420070400c0001d1000c0b0445a84543d904110500c15140203965030380da075581c0c1442c00e030041d00c51818180400c0b00145840f0700450001c2c1001d00746480d10307001840c40c00c8100c1c0901a0f0050900d50000380d0301313020700c226500041c04141d0007008074141d11240d0030501184140740c00f0450305000550085000c00c80b001041d0740364030900414020290703032588011220070710060490000342c1324105c6800c00c03090302800a45000514 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 87776035 1250 87774785 87774787
    0x1611010f05040807111e060a03140a0902010210110301030f1a0f0105031608060a0f0f0e0708060a0506060306060a1b03020606130204030b0a0b060f03070309210f030e0c090c 76
    0x1414044202100c048030a403144141c603040083c22505101c086c08040c85c101e500c2d07902c944440c40700b40c0107040003110f810740c00d01c14401000902125070f4411080c850003030f800c80300d06c07000c0c4058030401c9413074000340008190418030041001601001d10904003a101c0d941c0214900b039003c000e410f10110968050300c403094190014070140c101007200f0410756900e07a0108010902d0241c545448040c0a40100c4820741c507858540d000c00c0321074020a03110110070500b00081e940440455494083d5030046038018022030340440d54001050203013a014030001402d0a01d9910790f00100889580882ea8041c107104180028000030481c21150305516406a0050a414507018003000b00607003001114510880c41804180003003224001c00b81c0e03000c2c2c10030307000041d0300614600048980c020500b0804201500208001003180d15401c48504584031ba11065070450800c4210344515030700800039000200c1d82014044c02e58030a400c084013621142082c1c80c01c031280000403919501d0111880300308a10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 87777285 1250 87776035 87776047
    0x29010e01050907030c0c0201120b0604090504030f0809101e020c0c01020f0d0c0605070c17040816030b15010e030706111e150c1207020d020c091611010f050408 70
    0xb0b0440415900c14907620f4100510030540402416020446c10042c3c100305945008401001c1a584603004035080108210349441c1c0d0b43c441c4030302420303081383e0460000e0240780d0503e0820740120b2409016414100186c0024014000c05c00c1c020035816030162202128102c00d044401c03014401000104e95950140c901c1100060003e46441103524004c0e21580c4200c820314a075640c050440c440301640a00003140e01e80f50b46108454040d002c1c038015000ca412480641c000d82180030080c400c4400d40c00c10b43e10114240082c1c400c55141c04d1202a01c24900c0314001030900020400000d201c001c141009007040e00b001e00443d107001100e030804004521603503500c6c11403039810081403496020031032103000364400304034480c0d464030002c170303660780c200111103000c120492805019151400602e183c40003042c80d01003030003036540244510900140c0505c03840c510b100d0800110040c071488a001e1500500c2c1e0a150085968040e51110300b4030b207541c1d036a5003100400c000d0203124051800b81507103a485070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 87778535 1250 87777285 87777289
    0x1803060213060f2c0603070203040303180302090c030702010f0204090c08010b0702060417010219081501020703200d08121008010b0a14130908040602070e060a0329010e0105 76
    0x100ea00000c0902103c201c0041c07102c1e81c8240f9503804040d0b0003000b116000801c4600814210a44440e258042408010041c0c0d080e0f002025100f2640039a543c58070a154901c6c0c4064003032142d00003c0d410803e07403400105103054910085070003200760700c0005105903407a043c0c1001c03030300150010210070b80c41d01140409c59a2210030700780540b40c91002d10345000c401c2c0d0300180161141d0b00c40d02442c0c4e04d2010b001ca0f80c20350b084d810748800e805880680d0b1410681c00c2c80061441c81d08030364840070f50000011848465100240590560340d00c0400340c41036210f046025008101000070703440e8004000f00b00200001e40403000380001c00141c484041050805210080a00c0700c540c1085100707a02d80100d51010f80d4488581e001100c040360b140c40c084c5000342c400300d22020b541600711000c00381448802070401c050400107004460b440e500b030300c40403078460f41a0700e0444001d6810b0b6034011039428003800419103107003054079000c210482d519500498100c000000300c809034012100400c440c00104079034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 87779785 1250 87778535 87778567
    0x2030a0b01050408030909061c060f06060e01080402150c01021315020f0c1e030a140c01030902090402090c0c0d050316030603030203180a0503010603051b030a08071218030602 77
    0x1030302090802d14180340c02c0c000d440e5070328014480340c0c500c2103200300c0c00b14038103413105082c104030401102608040e69009041850182c62072445480c0001e03d48100000e503240b180c030b43d040c0e0f2924140e4070011542c0390b68017009110115130000e0b20040008000d40d29440b2401d100034000340310f4510341110034030329002564a0743c524980c421425504802c5030741807030340c902160410301c03074070304569030f10840c201c0048110f80c3c85441035030950140f0072080c070b403400d0040100e50001440852401c4401c4c0d60704450045003035589405002390040040383c041001450007094241d03000c503103154035500340280300e80344916040000d8540000307e02c000041c40f506134518802865000ba5904050040900e550f800940e0391040c1020f100c40384041880b40090b9540d1214400300500000f8000c0c040d803600c03810000d84410802c2c00c0d421160407000d00c0c00d0b100e4140814820419a000414241001c0d000d031203119402c00351008810030098580b440b088010140694403011718080d200050b228003031076440d2808 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 87781035 1250 87779785 87779801
    0x510020c0f1503070807020a0804090b1011120309030f040e010f050a0b12040302010e01020d0204140a05150d0e0703140f070e160302070203070603140c0406020a02211002030a 77
    0x19044000e840b500041c1003400c803608110b041c80e1404443c0d4601c101241403103030f807a13030013401c1100004d4000748503150390f0024070820350304644076400c800d0030440035036001e1040b9131300e0165600143c8080c182c00385d08402035540309503103005803440d02d041ca442c418080e502a4010403605401d010046c070071101d80301e00d100041c14041d510303504024180364500a0300e00038034418071502c00310100000c08161003900040040e8041000030f6440d1a42e50940c0c0700070f0b41050082c000003007114050600e1500d040c6541c98110748015103016402c0031040c00140c8980c2c4540300b207100c0541c56568840d00840c040040e0001580210855005040c0404009052545c0704181702000ea01c9101d043c4214400d02444680144000d6100309010700000003c0d070190062000181d4140544000000e140390141c0000c10608200201400d055589010a002c6405503014500040c1d1110f50a0f500600b000003500d020071144042c454400c03104614480d02d444080c054004c00503401000f40041e0382000e02031045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 87782285 1250 87781035 87781039
    0x706140c0a110309010c0210050d0920030a0c06030203130c060e01030e0d0e13091e11030604050307060207170c0a0507080a080d09080c100c0e06121602070510020c0f 73
    0x8036041413103000803e03081c03107000c0180c420565802d00950701400f400c2200c80c0c1c541c2c050824004d000c403c1c00c2001c44980d240c0303090000c00950b140001103910780820200030017644010744100c0142048000c80c02034000421070401002e01119510110310f0280d1000c0041109a5901000b807100303400040584242a1a240c542d503c191800100c95030002d0301c4a0010b03001f80c0303100003040300c05e004040c080c1040d420b000c0d00210b14400d240300c460000c40103081001c0e00418a0481c00154601450303961502200d02400c0c50b00280074000020320983c00030510140a03c920010301f114004510b030651303102d5000c5048540c0041000360810000340b20030001005000301800b070160544d01d032504503209802d5158244c942c1e13003400b10b041004950664204030005000c849120003207440582c020700251301a00301042046640381c07918684501140c0c2c0c024100b200740c41403526042c0081d20400440920081075000b210000304050315080060010304c0802e90041074960494018051a0910f00c00070ba4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 87783535 1250 87782285 87782287
    0x120c03061206021e0715050402130e150618190209100302030f010b041508090f0604030f021c0c0602130e070c0204060905070f0f1103040902030f1f06050706140c0a1103 74
    0x2170042410644000d0b00d4807210840400c540d0741c2c92002906000c4501041610705103040c08144a0319000220102e10a81101d07600d800b0b030725884200444442c0c028107103d6080c4200d00020035200b149800c411151625840250801054200080f00900011400300c0081d071301004001e03403814074801c00e038010038207000300c07074034190921508240c044440402c0606004261000c80c201a42c00c1082e0000680322000340d034202d080520300103003c107c0e2141d0030740061080c80d21400940303841d0100040207240540300c14201940564904c0045e400103401801c0a66000d9800541e99a55400580c81a00b00e0350b62500d0703071700503031042000300c0e43d1580001c10b0b807501d0041001035240d0454418101c16000781051401101151021100400c0e2041518524040864002655982c80d00a140121b4100b1a070101c5551003243e601086407881c454000d94003180001004418001c400510b003850180d2004200f88101d490030708500e480503986444210740000340c0010742d60f4410010018101c005000d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 87784785 1250 87783535 87783547
    0x31e1c110d230901050f04060201020a0f03020a0c12020a2a060c080d021e0403061d01180204020307020309040207120e09070c0803060f030f0106031b06120c03061206021e 75
    0x19815614004100e00701d0841c0c001001090f43c0c0c015026a0b91003140c05c4543d0356116215140240030350848031603100414a210003008140d4000d009a034181100e5550b00c1220714480d440b44c1c2c080302903582100013503001c1c2c0350b20300c8013103040700341d03502588141c8a007030b0844000f48000700721419226a00c00340c100100c240f250320005203180308480c5006043c84002d40c0315040703c0e441c80d16840d00480211038070140000c000003000040c2d04009607185049418105580c0ba241d1142c1c203071202007542009a15001c441c4a0043c80d0070760243d608a0b080348100c0f0304081c0c00c8404039041341c1c0b207410142c50320400200c0e078082442e0320044100400c10250b940034003d04019502134020301e050b21001b0070040001c000542c0035101c00400788800310006041b501c1c01c409011240f4020720940c0001e03a000d00b0a0800c4d1009800400244000c5450650382c0ca02c84068004407000100302c4c01c1c400008064445400148080905070030407685d070300072000143c0e284603503102c1304d88202c080300006840480611407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 87786035 1250 87784785 87784817
    0xa06050112060308120405191208060a0501080f040309090905070314010b0303041208190e03060a06050d020d110a0e010e010f0f0302060a0903080c0a060b040b031e1c110d 75
    0x5c1d10b101d04800103a85105807a40e203030103411720080448520725412202647c105102240d445142001c2ca10303100c0014645443c0300784031450301d0300e001c3c4e42c0c04a00b1b03103804242016440070a1070380c8140245040705d0300c03d86a150240595603551000d54040d88041003c4c0240040b61000d080ca00e00c1c000000c002d80200c0002080c0c5a008a1040e03071041d00e0a500350500b880801c408545808a00d400d004034101180c00c0081d04c0000c2c440c04c51400783c4036840000345111000d00c01ca1050b0b94006041310383e6180607030701304451784020541c116000f0710082c03e6010740313884848614002d084169001c01e106d40c1050901074a64030164070850111141ca03030b0420071181c0031a103510a803034041d2001990f0f8002c0300429944a0303510740c00103202c0100090034a0004030003280781ea040c2da11078202031025a900301c0400c4191a2034600b01640360f004503481084030ba04246e60944645115010f40d030303c0b46441044401d205c07440082c035101003480300e441e00c01111814001000d0407039160500034052035082030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 87787285 1250 87786035 87786037
    0x9120a02010c02090703020c1509010f0c020c041e0603080316020a020108131e05030901030e0304180b0a08100203012414090f0d06060302030d1409010302030604020906030a06050112060308 83
    0xb8042c1c0a143d8070303000b04a425100b078045030024540340f021192000140310f00240c1c0c200c011100c0e40225483e100c1041041e9107640100c00c080069039000f4a883c4c01d4900401c40142489840b50100b401c408040ca00780008078040c070402103010301c81c90780d10b074a0a050f104250420a042400c01c64110403035050050b078003d0002c980007141d41c0191140c205092610245524605240b030507000d6600e0b04007020040000000c0011000a0741c082c03084103504c0b08200c0c2d480c006d50180300c084020b610001030080c0305551041c0450b0400600025a1568454645042490728074440c1c180e5170700040180180345a0000090f400540503051881942a0402c0240a880b07151802c030201a4005000c50940c7d41d008280300c03008200401c4040b22481c18a0290300510700c6220481c000d00075148409000d50040000240c4458002000c0345007440e1180110001d50004103520b0b030080d403d0004032213546400000d07520428114a002903000e060000160a24100c0d503440d2001c18241981800080c0042d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 87788535 1250 87787285 87787307
    0x3010303080a0603050a0c090c0e2103160309080c060c0303070305092e14040507030b040501020d090b04020f04021602010c15020c03030f070f090b0304020d0b01080309120a0201 78
    0x11810407a180c40d006940030140c00c00e64400f60442c4601c8040708107118030600600708660700780b0742c100844601c4100586556441c0307070240e80e02c4001300d0707145845243e9584101c40440c5441d01680d241500d109102140015240016400501d0402062144600030004070f68445800c90314141040c0701130484c69503a00c40184042c00301506c2d00082800c060040050b15030980703491070711038400700c01c9045200018903196a038040081c00c0000d00700d20700e203892203151700032504032000c1d00245056880c0c42403019800381003203940799402c10050241480e079100d040c04483c440c0c00300d846241418010000c44901030144288101d10410400b210400020560a150303542800c0550403140d041c21f02c0c0241749101d0001c502c40b20300006190b0004c103404001180f05520040d4001569200c00c0c404865400a034a070700780c086050742805112440c4032801031a130007840100140e5911034240d07540c0780c1040c8283c1c081c801c5648046100e6805140581222401801d04401048585040e80000307110282c21 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 87789785 1250 87788535 87788537
    0x30213020702030a120e0306010f0b0304020607141009022805040f0209100203091203040521030c0a080a120506030a02060705030c06012c0906070302090105090406150e030d020303010303 82
    0x1c014045403400d0240385a142d41080300c4014840b0702c0364002c2e11200195000034424042e51f0000310708005200040710a90f80d019058604540ea968240145580300c41e038241d03043c8480c5402e590300c82d403040041d01c0050124610104903c0124410f204070807903030049040341d40300d002c108420340174160408001154811600413490180c584950402807003074604258101c5000c0e20320724a0310360000020a402d000c16104014196100c2101c0e41e00c4e401540641079006401c09c3d541000300c0d5840300e4161211003107900342c0e0b1400301c074180040e2405a541078201c80f108008a48840d180b60031001360840386007202414045880c04000080d180c240f120030003071241e44003080710780500c002081a00d260a10000c2180d045585482e91040c503c0441c441060504445a0600d80c2c07000c5580500c602a0144c44010015034031011000d030040c0d08040c451504105080c810071516980c0e81c02103000800140c07010810222444c00002c240e4103111042a009901c1080311002c000d40c000200d90440e605 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 87791035 1250 87789785 87789787
    0x30a03030f0b04060e0609010803030c0a03091712011403010e031e120f06100c080a0305041b0b0301080607020d08010e0703060f08011a01091a031305010e060a06050a03021302 77
    0x6610700314010004a030300c00e0382143c9055804107008000c0c03150076004090444252080b80e0780c6101c8259207110440d4a600f42480c10321451910a009402c115442d51040c008a11250808032003d016904a00e220841441c4440010003080070038a200c83c1090000703400900284144a089907501d00c505500d5014100615110340100c01d200000d8400540002241c1c400900b082320080e000310b102601e480384550304100803842554065603281e1100303540680d01c54107140040c4000e400a00e00240207072110841100c60064030035401c0c0001c000b07040e0f1540e407035860303506064032103160010040405040d54003e01c0e8a446040c0c00065040c112a80031442071400e5440801c11000707820a5400b020f400c0d006000e011036072940640143d65082908440581e000c1454801190401024442c80110190010864981d5522038005603804045e012001d460030106071341d946d084902c2501c070305103250046014807100015a010740303c0104400c032013205003541581c0000d100b840c0c04020700c6003e168 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 87792285 1250 87791035 87791051
    0x102040e041a010905092515120e0712110d1506090e340b0406030605010f0e100c03020a08070506040302100504050d030b030f06040305040f211b08070602100501060e030a0303 77
    0x710030f44214003808050100380070108c003019001d080b000701c040c0030451280c148614050300100004101040301c6502404411102d200c8e00c03144209500805100e412031040b0304547c021500105030014400341844000448600d13000f04401203640d20690360703032035070812001d0042d0a80c0880c45610055002d070900441c0d21490b026840130b200c0147d012a24240021800084032a01680490b003140e00c2038076840307c224039410044403490f100f07070465544844000714a0704540e1090700701006103446401115405562901c803d0100c0c0c0120000721210f6200404220030942d0512208502c20f013620810312070f40c1429524280c071020149600c50030982c1c0e940c50510a680e04102440f890810384054440301c0c02e0509006284d50301a01401540700558200011015a545603201842900319000204802c3c1d40c0e41e5601030008000700c81030661820030700411181d5041c003410300104102d4004010188480c005039041d0b410590101050146a408103d1030703032004075485540300e501d480c2c0019804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 87793535 1250 87792285 87792343
    0xb04081501030f0809180903120a15060806010302070c081c05031005010f0c0803040311010b0105070503180103020c06010f090f1a0909011113051206090312090102040e041a01090509 80
    0x6c48001084204066503400384688200080010304100040010340d103c00e94411300e5250540380d40d91208507004051501c200300740c2e4810031800390800303414034015140110640303070482015602c2e00102c800d0341003c14002001000132140c070000d2082820000d04501d050320340f54030031508034070400341803000c0c803907841c001548138078040b095107507004a12645034145420f00410300c40d22b044039000f20b5868184a200b4540c010000e0782c080b2a03024005501c0d28075060403851802c013006071560b061503024044814680401d1141c207020344076040b0b06009142c501082002954901310300310051310f28225010320140306030800055040c1c0c0aa42480c2c80d510f8105440f8010542c83d81d0410717141c0c00201d444c2030f094070f035690110211402101c1500b080307554440540d45600301030311440c2c5c0c2980100f01501d055040f418510364003610301d1000504280d44c903085824130540454003100c0403204500c043d2810725141800030301500e41a01c04200310314100070035660b144020380404024004402d8002801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 87794785 1250 87793535 87793549
    0x80607090326070501020a270b0f0d06080d0201050604091e020d051c090b120105091918031206030206030105060913090302030903100209060703050a02030706060b04081501030f0809 80
    0x700300140314096031041e083c00e0845c000d402c0150f080c1e00180025005502c2680124041c041c10440c00d12582c2c0d60700d00c1d088194a03036a00103401c250590905110110042c2074520440004013288000b03070008002c1208004e08483c401044030384076528020bc40c002158034640b0703443e0304100b01e003070003c8001d00c18000a001ca403c50580144940b15401850750040c229100f101c0050040d030b00ca81c0d45d02d54860103080101c0c041d015002112040c241c004000500c1c005c01c03034070740050001100d144981203440007481070fa190729801d202280d0b40c60075413104240d4456900c0204d0210088201700071425640010300324401803103400c0c424440820340f0f020554422008080f1a070844c1c404100e003044501d0083c3d01c0341c1020200602c20b005452501220380e400d0700881c3c5818034010000f03854600c2e035580035145a00700600501c21031100b40f02e50400500c2901c50080503048825001e038075149071030041c5141c840c85e08110b0302c1b00801c4400400000301d61001e602c644641c04081651a40c04031070100d151 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 87796035 1250 87794785 87794843
    0x60e010303110d091a0f1606020a030b01211503060c02010219020d0804110a05060309010506090c0408070b0703110316020a0801060509010e0402040b0a031209090c08070c0c12060b09010806070903 86
    0x101f1307214824800b00b0001154020315419141d91014841140701000543d04909041c250480c018070105503c022101640c1c0845807611111281202194480c0c0f2101d003240d074260b50f4070000d41e40c00a8900c5500048044109086165100401801d1001400200542c0380504003c1c14140030b075810165aa440c94580c01c00743c40090002600ca180c1291400e02a16042e0b4001d406003030300c40003048551015030103d40640d5504001050582e10700340b44182c003039100c403205400b00910041d50218130002800108200600682c1c21a50740095004201c5c401420b5800068542c1c17408004000c952102540741d41180c1e9659811500b80d0b4850001c82c002c0e06016582c2948488401e4012080250002c24411529059607030f07481c50980301e5403540c1c1194140401c0b4000300704ca000000d01d1283c1700324120240d15100d19082c2c095540d689060891440c1610000c82e50240c84007520006d5040005103107004018040c024580350030518000b40c84103003640000340241405c410071070b044021002c041c0d10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 87797285 1250 87796035 87796057
    0x30720180a0e0a08070c0e10030308130f030c020f1f0c11040e030417060103020919061a0702010810060e0d080403150f0f05040302031903060e010303110d091a0f 71
    0x982c4402d0f43ca0000b00690140c58111008031141402207405500b4038515803103200310801c1d0342182400d54801f510300e094014000107100000748840c1e40024060503108200510984900e403621000c0c2c41002075004000c5a0709003d20302090410303330100c0c0784000481c0103611508044007803402505240c0d0b03500f03000e56074450b00305080515490b080c840010082c000c80388094803100040c054480340680313070b03002840040e600c8003240c008a0200e004100c86002c0c00c403500600000c0403030342c0d420550707106400f07041d18a007072100c003284050955805ca192558441c0040100649050a051020b0914014a12040e0041410407152010080868202d5020f503030022182c6215403210038214001d890704001c18004541000c481c902c0f010000e0092902560b415006103080c8070f081e01044480c03540c9040304008042d241c003000a80b03070840b450030502a500a64819601c1d000e0544064588a1003510105c00c2250b003140820211410b4582d404145c480740c80820760b9003215089018243c0180044c0c16 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 87798535 1250 87797285 87797293
    0x51009080a03090503060a0b03072c270606090c0304050f06010e01090f020a0806060d1e05060102012304020d080405040f060302031009170903031b030720180a0e 71
    0xc1c0c24140c0191510782240c90482c1181c99036a5054144401d40d2107002081d82c0685c003140081c00b06604c001000700d002ea551040700c02c440c10803038041043c8240700780c640c1e410009071002c07480400720f42078101f0602c2c007414200822481c249039006ca0410000148100000c3e0000300c00700e408c0100c2403045c1000507000390221005561101000f6400150a21a03407584915080750680048504d00941c0d00b080820b44880c0d02350359441c414841103a00445038440810b507074404a11400d00e00740c0c0d00c2207200030b00301400038840c0740c07003000a821600702114a040e00c13518000c4442203103400e02c0700184d1166040da8045041841494000c0c09406107400003640701c1d080c607102c902c50b00c00359801042124000c83c01c80d102c29014407104012987d403100c2c00303003156580184080c00c41c28900e0040c251203901608403031504d2060184048503034540511100c482e0030000c4d450060010300c0d440700c192040c901f0001c1c54451506000100e581580e11500e8402959200c0000d81d00041640020b40382c1140c10103403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 87799785 1250 87798535 87798553
    0xc0a030206030a02161a160f0509010c0201021906150911040303030e031e0c070f06020a0611070501140a060b250501060305071d0a0b06041a130f0501031406060405100908 75
    0x13451200c1d0781147c6001c041495641302080c074500c40d40c8407058072000c0d611401d240008802c01158514040e0100b641544501030501081d00303000c10305406060b014410005400c0c0181c80f250003034400b603074000400f00e17060090841b0100012000c81e422a0b6160400160360640615910b045000c3c906074050070ba4a410703001c4600403a0040241b11545060f010340d4003560b1213440200c44d0701404d010f4100140c6c0405082d000081041d80105006040c558500b0304010300ca941d0182540c926103001080304030114280f040941060090783c0c05808807045c61810210b001c0400c04042140429031611110340200320000d1200c00e501c444007541c1c111043d42d031500d4030368900000d103a0f11710441111008410300041e00f04401c51051040c039010007000a4a000d240a40c541c003940441400100031403420404c2d0460301410149072401000340d5000521440e28200c0003408458003c202c11614010420400800340e80d118119420748404450042401c0c1548900700c2d08a09250000d117064030400001d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 87801035 1250 87799785 87799823
    0x20c190e01090e0d021506130f020301080102090a0905010506030c07021804051c0903080f0310081b040c021b060a0c06020711150f03010e07120207060e0c0a030206030a0216 76
    0x140907800c415030120781c107140d43c1303c130304a03952016903c0d213103101203000001c40c0c01854101c5021415020484000c01c2111455803a40e080340e2080e4041540390703500080603a000d041c4001400002e25010700b04100301d40c5000086031072840000c0c003075080f0301000140c41085503034140f00075103540c0046041541910b46031900942d1504084008460705070b001c01380040240c81a2191416a40c0c400003050600c0c0000c00b00c03c18540014000c0441c01130b4604011903d41e0f410015a5000c81c000c408a90500201b40103000403600d520780780e107045420400a05000c50781e02011520300e040c0944820350759078200d040403200c0140c1007400074142e600014003481407061035140c8003a4058101d81c210340d2400000c016030f4403403203080d9484800314018001040852054166154000034a0420240e09042d50381c0c6441240d1180c07200701c0d09035a86a414a2140b1000c018000107104181e8006d5401400c40c1c00103441c5e80001810301108039000540c4800510046001207046580f2400c2031800c9410803a13 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 87802285 1250 87801035 87801041
    0x2071406090106061b0519060902180a0606030b030c0f0103060503010f14010e0103121211040801021b0313050609030a06110c010b030307080a200f01021e0703020c190e0109 76
    0xc40e80002170148807004113101e98440480c4611030744000208602c0e0345444a02c0804005400c06907a0281d4481c1c1850158580203600046103010000e030319410324066243d030003100d400d60080e000301880c00c0d58600c03480d180010800c2c0500e908a440002c206140c500482c0902507542140390194201fa41100c81c041440e00003000d920201070580404d80e803107803010340e080c020900c40a0418602d0300c04d1284818040d40959210400f2603001250455005444503450b5000d503010b000560b41c0007952031811440c180018076814414009103140c00c1c04520858581d00990080501c10f160000704030070155400c01564280360380c040b40a010145050503140790681084a48854a5080100304045440e004c0116069580c0c000729107030030070301124806c42ea4400b450a84186952044952240030b0b041008020f0740c0081d80d90025a682e00700050b80c0002400d610b1810011041c14012400001d4010504190240b400d85641190300b12000507000102c28641c0002000c1458000105518240d50 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 87803535 1250 87802285 87802289
    0x403110312460615050909090102040806041202061608190b030109060c1409010818030c1e0d09050303040603050c040b0a020303010608060607150e0c0402040f05010816090902071406090106 83
    0x807041005543d40c408080c000e08071030711504c0015604100704022440c0001c2156080809040018113158503030380020302d4810705403015036031034406c864868142a81003140700d601c848108600701d100340c00c0c0040904144030151113241c40601d0b040c110484107035150702859034504000e009200c103040908019008040b410103000025001040840010920304100d94001c401039603014203d039100c1500540c00302c5c1401786260240010455113909210402c849004030a03400700001d00c014000b86030740d103840000810442406a929400c01c440d503400b10030b98040303e12a00703011920360354860202640e03210b1030304070341c0c3d56500100e6a20000d0b58000301079416502540c03900c01032620f943c01040900d010304400203100701300d02010841c3c990001e401002c88140040122544e11103080001000d07a0419040040501c500d000e00f0892507a10100e07294000d880c400d0241d625165080004003108030b41c3c000d0944c502c0d00010031504000c84001e1007581d85c104030050300ca1a0402598041c081c00e018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 87804785 1250 87803535 87803671
    0x120405010f0801080a0f0c05090a0e0d020d020c0f01030905030a0302120601031b120605040207110f060712110a06020705060f070f0e13060812030403110312 69
    0x1c115411003860084082c241a00c10b0b000041802c0813080c4e072500c84440c1e070f10380100e52440280c0d20004160b11180c9405000715078100010445544640040e03103003180002c01d0804540c000424030300c81a030040b48200c070389130083c0c0e070a20750302c000c3d5001031b405404441030052482c440090994089503060b030281400500e5003040040350380307a820044050703600503210361984040c03c4400300480750180d001603541078011100072804130303910f00014040f600b1101081c1e86d101c01d00622008a4500f440f8445016041201c00074141509070316290f04000c0e03d4140b101c00d1184115115019641c104070285050740d000c0c109560322856490125140c9070300f070303a40d00e42100010020031f2813540641030308809040f0310368981512818610030041c0456212400401d101e076120404a920101072100c00c4581010007a016980e0504d4500144100d4100070601010382080c090700c3c09007908862405c2d0407000c4603203c42c1e282074041c80440910001805994000040c0e828400d60400301540420016500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 87806035 1250 87804785 87804797
    0x80d0206010f0b0d0c18120b01080105040809100c0609030e0910053016030209010e0103020d02040c020c040c0905180c0d050c07050a0602030105040509031201140f0312040501 77
    0x285981e602200a114002d03003e07403030700900484036814015440004040c1e0245404844613040c21340c0c0214203050340d00003074905c03050409520240600c8402d03860043c00e01070020055071034292100250390040c10038040c803a190000b803403540c0c244902d5070003082c1c9800000810035048030745800361160400c400701c54000c00002c0000b8a40380f081c500d0180860390003410000c2c0e80c20b0f650104900c00c0081061016140c11208410b251201c1b0401c85003175600321905c5484401c0d402d40c01000348040701640403080d5003103004018801629000500c581a641c1a540411164040c2600343d08112010071455001468040300503010b80e84014110102c810030780c0d43d51224001c103500200b240900300c3c1d5180400504100c0e814800513140c0c4240c0d40198421282c13800c000c0c65030b0303d250601f2001358003610341e15004030050009191030311030305c0d410912800080d860107030701c1c2210100c520014410103030307500d01c007401c0700c40356803a214441030380c140009007902c02204480d044d00c099a04039000e102d0000304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 87807285 1250 87806035 87806039
    0x605070b070807140322080a021204030c09050705040e040c05040b0409030206041707080403050c0405060604050d03140f120414010b01021b012a060f021303020d0602090a080d020601 80
    0x40100032031400380c2942c0c4c1e500d2040000b40b05642000c0d50000d80f0101c4541c1c0304840704501c080000080a62062007034022960310411300200916040920446c0300c41140700700b10400001e81001f840c8801c0343c500c40c1c0c0110f12540c43c2d52040d00d0310700699001021080c1c0d2002040200903280107801d081c0e40d800c65040001d4100c420501c0100c903110300000740075a20142c0482c01103104642c10484072230f201340c0103034601285696585e403241c00940c000c0700d0743c0d0300c0040140f07441d1520303000e03841d4084000d840340d5050500e8a000170b0540030b00300341c019041c000814508071100448c081103d43c40c0b400c000b490f6540d44070701000b101204100711000d84107c50310304660048030006015034400200160700524880815030742100c00c0000e140586410700c003845644010072160585400546c111800100030070303d845080600958200c1821000201e01c100110103180e040d0100f500c0c2038a070107031180c42c80c0030802c2c60400002d200e01d022865016a208800186154000540101c5154980d0a136541a6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 87808535 1250 87807285 87807287
    0x908010c05040506030612150f0f04032001090606061d0607050c060a171305160605040b0f0903010f020301050a09060f05041a09090c0a060921020d0503040605070b07 73
    0x60354564626000907020082000745207000d101075034020304000c0c500c0300310700700798803000e03191000c2e20f0020710250709808204002c1081302c51007664170204c42038035101c00b86001e1390b0062800b001c01000a0022040e545003060985c0254810041140c0c0b1007401c0110f1502c0741c00c0603108041c43c141036004010040b031011101c2c204003080d20500ca9014000b45048440074080100079000070501400b000f04203050421000c1c09204e08500132901d80c5641301c84104203080450408205000f00c0780700c803040307860400130190b1240031202120380180d00f06444085080a640035846580b22065045d82414914818013560b42c3c0154103c407411115a540e499a6440120a0303c4e0700d44102100484100c600f0070050400d5008451004110034010750b008142038006550310900b5224000d556000795192501402d000a4520141005007410200e4600d05800c08819580910343c9081498040e81d00c6001c54542140304e184955100d02030b251035644400300146241c0000c0d0080d40c1c0020300c207000c0b0341c5903 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 87809785 1250 87808535 87808541
    0x325020d0308091b0d020f01050d11070b010518180c06040f14030d0206160c05030a030b130614060c1203010608070201062c0402030309040c0e03070509010b1c200703090801 76
    0x184d40c015220000b41041a020000804401d10314141440410042c42c0c4041000e403051948040485668a854040c141007002d034403031050304428041d80c601c05540081d40b46544140c0e80c41005404419600543d0307080c07450820500d803070402d0f0000c101040c089560064120030740c003580c8414203514a8100e0100405541e1030b0550003400160b001403011030707041d03c00008013200f0300300e060620310328590382955480d2071948980c2030f100000f40c0d242400c40161428001e541d1121b1038540080c000d10342069000e80000614103001d5208020000304982c06003030520445071180103281b061916580e40e900003500d2282d007164000015484c00e00c0101d44110383c038440703002c80c45803800114000c10115022441c41c00020f030050382d00d0720080c80780c0e511030350700c034002c20b1041312070b66940e041c0c070104510902d03240c03000503048540324580c104010700024591400340d5078082500400590701c01b0940070560001c0500c80181294007888184107491291810b00030590350344640c0d2411400e40d5a20050b0b801c07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 87811035 1250 87809785 87809833
    0x60f09061003030503060307180f0c0305010f0b090d05070608010303020c04060308090d030201110a0e04060503060402031207060609050c030103120201050606030604020f0405040f06080d0c050325020d030809 91
    0x200741c0c00704000d00c0403a100c1c02c09903034001c00107402c131000542c441113802c0360701c990302c50030140c0c1903202d84140e05076a90303c1c007907091048004d050034015035050441c80440c0c1113813805841c80440e0040380d40021a555400e2404280340c005040d50030b010b460721001400c06034240000e6000d0711456505500031b091034803403802201c5d00801094100741d090b8003000014203620f24258115925040c2802d9501c45010060551402e030b9118584008210010f2109442075030340800c1c0300e9000201040051789004c00c0d6200465244000e9590701c0b20030749001801440644c0081c18028a080c0800004218650007141a24010812211000e103d02000c0f130030780e030007207441035000913080c070100d1010b00b8903401400240d0558038400f41003035120004102203e000c020300c461308544807002000003a60030702013003140201c0b82c54021613074400c58a42035600d06c01c07408074103244000c0282c1b180718040c4000c1c003003d400354006c06416044034a410007e051b02000d648600d06401107030441002240c4101d51902 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 87812285 1250 87811035 87811051
    0x90c08030a050a08270d200304210506040b01142d03070306050a09030e0a08070e06040e03120f060a0503060402040207081614100603030c120207090e060f0906 70
    0x120f803c000107421031380c00301c018013401c08068803a54040e074140d4052140c800556114001841000240c03040200b2030315030444c0c05068450b01444001802d00040301715401e46480c0102002d031031362014800144281c5107480a011806050180800c200480360180d040b03c4105004041c4541550200032030000800d080816443c6184500d010f03c9840300c0b040f0315004801816161019a42d48505080d540200c0e00c2e24400f03580c58061208050f08850f01c0c551100065401201603401c100140380d40b66581d00a8080714410300c00040c04a80e2180c024903800713100380050701c2d110079024070075184010060f01d180c2c4001300c59500103100d504222010310121032008000b006a500c56409100007580250b20698185401b00036840d10051741000f14103881c0d11401c2042074038107a00c2c08060804030542c5540b14142d040400800c0440e03403011044034210b0304a5035034642809000740507468240c95074807140700d46040020183d0003810200d201131041c000f842ea526103540c3c6183ca102c2d240c0c001215241 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 87813535 1250 87812285 87812287
    0xf0e090a0212010e01020c0a050607021501090902041d0307020f060f040b0f16030908010e1203010b13090501170106080a0218072f010e0601230303090a0801090c08030a05 75
    0x250152820b18007141d090082100002403c1d046010014203907400101e0401c0158024001681041400c000755944081c0341d20241000c500031020705040c81c030040c8101d5440d5605c030448882599242d0f8401c0305103d41c0d01c00121001c0a6510159842e5004250b09038865840281840b0036810708d10111040d16001103e15840c140c01c080820203030760003001c0c0b400d9203d402400f0b400d013103c1c4400c0004240f00c0c002d03185c1c125103074500b22149080d01c0600c11000041e402502c800000c0c2c81c101c00540b41503a200300d25803511a500700b200310300360801550002c84080d0800c400010000d60313041124010417103103c020700c030741ea0310381e41120381d960481c0400941010104489015051044020301e8000b22685000c8544160b84007018070f041121303e105180c10001084460425142403264005144c040c45c05031009603d8405125000c00e02505020700d10103042c0101c031010382d0300780101c1340402c1c001803040300526102c00c1c4050003404400d00c00c681d50818028081841880001600c4820711965115 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 87814785 1250 87813535 87813553
    0x5030c0a05150a120f0203090f0f1b0301150b0903010b0f06070f1401140a06090e0606130b03010e070302010201051b0306040b040e010504050a02040b010c030915020717070f0e09 78
    0x103103819078071154a0204004a50402c0410304045001e85c5154503240a80580c0301d0814410503130501d41c1445c0c2111540e482107088a804d61004602144803150481070300c4080d4010902107405411240701840751000101008070b0290500ca0291480702c606130002c0054100c1d800921a18a8032803241d103034800d000340a041e000403800c00700f408980d0320558244400b55400c003074441c291002e0f0207039402c09004410401c11864414400c080040200600511803400400700c1243c4608020381240d001e80c181110b00c04000341c00c1d8000b060200e0014008000250b20312090b40d44944550108071f0040d428200411000c4e036400900140b520100303681c10b031171a143e10341008020003203603e800d500b040d00c2c4c107103112002e0000e01c110b42c4158095400340904c80391600c10042110b0b00c14810314103111140f1500c0c4003183d4400c00050550b030b090503141ca5802c10b0001d0036850005a940700301c0c0801d0207600e00d480d101d680403038048119840040c40c441d006480d40a0120a02401c80e00400c140d8850168 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 87816035 1250 87814785 87814819
    0xc06160c020303270d1509030e03150405070e01240c0b0c030406050a05150603090111030403090306060501020307030c0b06301507090302120c04050f0105030c0a05 72
    0x2000000a15605091580100507408282180c100030020440342c01d80c0c03002c890254901800303604582400305c1c0d654441c0d10856503511540c03103000d10240305055543c1111000c05004001045219400900f01c603d241445540303440b95604c11101101c1c24000c20301d00003001c3c031f4000c041d241a03501011900c89005800e814203a0000001000d4504108100f00031301c2c0840c6240c10820300940d1248100b03a03880c0b0301410800262013001d4400110303070b032420303080110480700989a0425504e00300c40656403500e03800007040c050803404103104a07045000040c0020550001601c504503441158103016044e901c01c01640c481c002c02c100078002c1352101c10a140020319807103110707500000c02450f2042c4d004080046000030109148210440750501c0191580040304108807400402d0107260210140740284006064a0161000074024800305010b03058a410070300c01c01c0c501c884054010051890074aa4940b5003100a2180a01074091984008043e040815142054480c003400000030902d604079 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 87817285 1250 87816035 87816061
    0xb1e0301060c0f0f060c03020a110c010e04090501022701021005010b040506030702160b1314060d05041e060f0b0102031603050c0f100902030106050607150b04020f03040605040b0702030c06 83
    0x1011a0100c512102e9080028200e00c06da18420005607030050b1210f0324000081c02e086c9111400702031a50002c802c003003036603900c0b10601100303110544001c100d5100307501c2d021380a0300407046243d1350f400c01e00100401409582e64617400c0203909a080b510345151001c2c621040310000e00032000c4941c0200800c3c4000d0400800443c2c01c4044d52048841d14000e14020701001d040c284c002400c0c00a000440d01220150341100b400504169020440e000d0501e40010701540f2502d01c0208086480300001801d000500e8058250701d00c82c0d02031180c11040c0c0c0e242000c01031100078441800c580c40c04001500d035520000c161410031003400344104070200360303883c252400e8008481c044030344d100d800003114190405000c0242c100c8500040415801010720402d42500d01036000540182c0b0207028040c0443c410341304882081c011443c0000c1c40101e1000400d020784184c08071145240e00004c1071104001d042d034440c510072030082017041556216920102e0b101e11903003061000e260702600101c1c0645081300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 87818535 1250 87817285 87817313
    0xc0306060703051b0715140313080906070c050a09090206030414010b1c0605130201120903090504050906070320220806010b13090b060d02090a050a0b1e0301060c 71
    0x200301203050200c0c03500e85a08419581c400029076030071412040143e80c0c6d00d05500c2070341c0f180c01e09120a40d203a601404546c9070100504030302c10403000b074074020140140c1c0740c00c9070075503580584150f0b1b4030480740c02c208000415038806d180c000e0140d01c2e00066515041d201d090007542c0d005000710300d9070700c81e03864000000500400001c059503a401c200a001d45e655040f929842e01c1d140003200401c01d5030305203030782190801010300e51080c280180f2003005070307072000034102814214000046e041b02e02d42400c0b50361010a801503600325151000f4085418400165107200b0030720f07550b081c410009910b01d5070300c8508600012600b600310521403003841d0f40c45201d45026440082e0041d4a04036900c0708440c0ca407040aa2140c03400000000c1c0c442100d412a02081026040c03081c010300c244950318010603003602c128440d21426039808114541c0d00e030307254603002004010041c40741d0801e64842c030700c04840d40c3c000221070145165582d0003240f18011501a01e040310601d0302d030f1340c2d2003440648424071402411 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 87819785 1250 87818535 87818537
    0x6181e09050901060f06020a0201020c09090c0111150703020d150608060d06020d110903071205030322060f0b040f0e150603030d0203040c05090a0e07060509150c01020a170c0306060703 81
    0x50b00c01003105e0900c0e004100c000d0101c0d5000f0200348403140006400e0942c0a14518020041c0c8803c0003d0030000081ca140411000e1034070340c1038201e100680f2410950100c85c2404902003850511000707a915801500c2000d802c103d0401074180e400000041489551244d1404198094005242c500d459440010014082d24000d03280006d4692081d00300d0b0400f40064144080100341442c050408005c070700054138900001031900310464032074550301e010091440714040510940360708444800042c0040107540a40184555001e02214601600740c040609000da481c069090300705103020b0040000c1d03c00d18501a0148440d944615008068000c00c0290540700402291565016510003144a00d01a0792810314043c28041007040b40384000d0070380f10329039085c2503400f0180417000c1900022100642041aa03542c0000b010034410034040400c0d021824001c107050300450419001800701c01c829668484401342c1e85800d40305076407810f5459403c3c18100b407001510504001c07005001142c02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 87821035 1250 87819785 87819791
    0x120a18050601030c0e01050604030b0c09010e060c0f0610140f040b0d0f0309060305041109091c0306090f060b0a08070905060a0c061a030a030503040609080406181e09050901 76
    0x154444a10745242a071080b501e0080c860313002c0150340006000503001d000d04482003880c20349561150141c200018100d028240703000940510581e0207103141c032503a0079014000503200c118044052351034001c9550045214040d03500040d440400e1301d5500c40a403030108070344004150740350042c04420f401c408011034000b50b07594801001551138424020485100300000d503d0f10807680b4004003004503681c0894285401c08003480000f480b200380f401d01900d826128103c0320f40c2d03459225031034512054100304500d070031400441441981908440291070043c501031100007814030081c070071558140b15a010030202840100c06051180c0c1c030894211400340361001034507484d07000190780ca500c04030380800410070f921201c508021460040f01c82040c0005506000c04d01e54a000c2511512a0f0000a041040010010b0304003d410f610484403140c1203035886494548031040600000110302604011060070140002c07414180b6103900400300320819411070705072500b0300c2c20303000d0100038208404c1c95407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 87822285 1250 87821035 87821081
    0x9051f03050c040b030c21040f11030c040509030c06250503150a0b1c0603120f0309060e0d08090d09050906120d020304140303090f1c140d080a02120a 66
    0x1320040295000388103c404196480c40041e68048102028940c00003141a03124100004107040000000ea42a00125164a10500c03600042d050254100c0d405134010301e0001031110030000040134003080072031101151017585500c140480300c0c0122a604071010040c0f182c5d060006d03884740300955005074142942d00229103203040040c40e640c541350045c0c02d09240104030f50010888060350001104c003c5a000c2050702d00f580c45041c0d68810400d0303421306005405200f644180e220303620000c03203660001c80400c000c4010038205070b280e000c00580840001c801034003190b14400c0c045030704a203400168480d480b54034500002c0c0403840e1002410390340d0260004900c0302480c02c0c24010f001002c64230f40c0c09184e60f41e0034940320412421500711150b001c0d41c070501890045e91512954000c0004c8111201030802544225031051f101074240e00800c1e80482801d240c26240700000c18010041c0103849454190f0745243c0d1000480c010484910042c044283c041110a000d603404911264640120600982 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 87823535 1250 87822285 87822299
    0x31807080303040609060c0305040201020709020307170112110910030b0615180312070c09020f070f0305250b0403081f060203071a01060f030f0617030a09051f03050c04 74
    0x14108a038103036072103500e4130541020401c1b6071203005240422400d0401c90307810a500003e5464109024011074030b1303800400309179102c0c020ba11003038042c04030100b18275a03507864620030208040c080c2011a00854503002c8a00145010f0031814400e5104000c641080ba28545480c100d180004d403041740c01008070302e018202254200028660005001802086c1007804001c3c14505902031181003075030441405100c000403000710701c00301107410010000d80c84000981c2011900d2203113100c02804014400090360030550000007401609025070380001841c1c00e801c0c54542c172032081600080c0038055210000d40000d010b2101c10340c00407444c2f21401c40c8500314205540c444000c40c0c1200c805607002141c1e09041082c0b03000e030307241c000d141100420f550f035151610192080324503001d0350342816100c40c0841d40e0b5108543c04000200290b1228109007244500d009841c0d62102044e000001e59860011509007000b004c00b5203600308600700b40e40240e40d641c404400030400544400c01c154810800040d5603 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 87824785 1250 87823535 87823537
    0x3020409020a0206060f101403060f040204120b0708010b0712171e01090204080715050919030b180601170f07062007050d030c020111060103060614040b03030318070803 74
    0x10b245500100824200f0000700620390080702800e5101c0d00300d0300b01e1080030700d0f4042c601c0071160100c5044241c81b900c640d00040c0024505034051600544045000103032860316465081c29980204211034098486000407188140e00b402000c40030881002034a001401001116801004034502003000c520b0400b40f5421640c415201401c3da04040b4070301220400e0115180d80c010550781d4402c40c6054601014140c890006105031003202c851410209001809501200d8070b01c400104540c1138010b1881581010f04442d00094a45105a100007001c2d421412000c42c068040c81c4010009a0302c3d008034460340c0d1240107020352407030051f42c0d10083e0b21007041181d2009400c40741c80f03480580e000c0d0180003c2e550840750031050103a000c000c00300003e869240c008142c85402d441c001c42e203000130b40010b8410401d086000c00b95403050754000418008a42e12007070a91b164400403d048005030b50801098031421280c070b80e40750f003082020402401034000c02400c5989094180c0e05103a580740d200d5811 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 87826035 1250 87824785 87824797
    0xa24050105040e0910050c040812070b06010e06131d070309020f04050a020d060803040312091202060304140d0f0212070302150618010303082512090606150905040b0105040506030a020a0302040902 86
    0x11f40d15011400340110041030081c0440b9254090519040c03400c00c0c0c1315650140340141806040c44642c003480112034994008440328007455111642da0169240c80d0801604504204090505251004139800341e00c21301900f03001c16001402c0f911030240b0803007003000400014001d4540e00358200840d01540d5600c2c02140c0092a01101840d1201d10b141449000407085181c00000c10041490510518000114229503160160b464076100c1c1c0e5280307480341c040000c0e82a04000e0b8411294130714061603008444031503a61042d402c1c0c41c3e6051391030032218014015541d0090250300210807240b006003a500c0c030282d0100000b0040200304e09414000140352400780c20903070002e4562000c10421482d094418044400c0c01621030b520404c003104000c22105015000c4004aa1640020401d20500f500010007a0100300960a11a201c00c44060503180140c42034500803818002c0d4241c5940c00703003056408488025280702c1c034658810601c00025481106001c00345a802e1001155124007480503000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 87827285 1250 87826035 87826051
    0xf1e02010e0a0506010503010c051201030f02010201110403060b010905190509040206090a120c0e01030b07270602070501030e010b090103080703021246031508060a24050105040e091005 81
    0x4c042e5040c00f00349425140745080f007a050040400012140550044072541143c0d00400c21041001c078500c0101e01400d81268210362103607010401109202040d4404841c60509807107400105560b007090066046202400c4142108095010821740c2070445440b54050310003022036140071038200c0021005400703a04003104008040f1a07540800c040052090007504403400f9250456240da51015050a0018284810071410031000c001428201102c4078034090600014610503464850082d9100c406101d09400a42007100e0900074180611914802d0340c0040c0001c404e907800e503240c12005034031644007182107200e000140076000c0f402c04003070244040340e421210070b020040c1240c00304445e1588190320103071400300f841c095096040745034102144500d05020030b00c0c0d54200140e0010503140e074049600c9018840400c540c40980d036100b0400386903c01040b541d0bc0440c01d207403204040c0c0d1f0b802001e011520801040c0204e4482c244400c1c0d001520004803034000d400291440e09a51050368845 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 87828535 1250 87827285 87827293
    0x90203060102070f080705060f211909170f0d0e010c0f02010e070303030b0406030b010b070501060f0311010c0c0504020703020115050612010506030a14070c030806010f1e02010e0a05 80
    0x10866a040c01540700800132410141000c90400c504c894481009105051090000142000080d03c104090310180000c103240020700d00e8078110003c1c0c611104032803059418010b54200710101c003c5200c1d4090b03403a00b040150702d038198561442c5031554040c0085000c603800500c00c400450360b4900a0030100b801b41d20010076081c00c640700151100340404589810359040507442c2080100c00600001100c0e01361801003289041440401c004004079040686144c00c184008255403c2a1009141841c826002041072a5a64104400b13080d82404010312a100c80d005604d12507204040040080b070003030945058550b550400501203904c044000ca001d80d455a00c3d05030403158112400c1300400d1300790342881c90450b4100d85078600500502440c2c0c800c88000c00864814059980b00710f00c0c61013070100b0034809080030b24001d0443c03022400304500007031102000414551082400071082a41c0c2d45a0144e140e40c2d03610040c1c42e4184c0c1003445411076503255880c18203900208404917009002e440a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 87829785 1250 87828535 87828541
    0x316090e12071a100f0e060f0a0513050a18030c0b0703060503070302040e03070501020a0804111c03030504060912050c1501050307030b1e0a050a2904090219090203 72
    0x3030074850440780354400340e1014800a000308802c1c14454000c1c40030100c200082d5070741e003c44140f10308a0354000c5140301c0105a00410040005103000d03015803004c07a01e4102c41c1714201d003040000c0703446000d103540041841d0001210414280c10183c0c001304c5410000c1a02c21000382d038020320700c00c07850f8190000b88604c444182441890002c141e0050520325041c0806800c1c83c000c80eaa900a520001340916554400306500390380520956807043e5003c8029980d4694a0350700600501c025903055804145100c0c100d1170a160580c4035048203990100d060010908a890580042000030810740d291500c8080e03440c00038681c02c4000c243c4e880644c591986502441340302501d46908409002d07081224080188070548e80010210112603108800d640143e840c0c1102e00c0c0c40840080560609504c42000c1c001d64410a4101d5807007076100d031404002c101942540e04803404c44880200c9200403200a0b103460500341600320b0f0340c10340c0c0050f00d8001070409214000808656a03840036000b16804418 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 87831035 1250 87829785 87829811
    0x12020a0917010c08010b0a05040b0a11070801020306090106080405030904050117070509040c050d0302031608040501080c0913050714031e010b0a05030f06010e040207060516090803030a050402031609 87
    0x1c580041c9404000c0000300c2100300c019080e101e060041550600021507102c61a910030022500070342894110540c50345080540904400c4113040e440010b4003800304003265420051094901c203c0c1e0052601c0700c141d190a400380e0b414040900251500e000800c4078559030386450203038a00814441e0301256000041e004c08604003081c0b41c0010384144000d00900002c544507843e404192903003100c00d10030b000501d180c1a0f155108500b04c4402400182c0f644409001c20000500121982a214251b947e034488889150702d116102d03500c0c1e80030313061000d0409034800e6640215400141800d1126404024a400b2407160b001101c40d1144980c03201d21115aa145c4c082070b550045c0642e180841c00d004d040305001c2d099010040580503014040b50009005038441c00d02e6502c1504003034021940c0708800d082500c003905080701e4003d12841c04404041c0c2942c440c400203400c544602c00074605640f200c14004018010141c020b980c144210491110300c0710019200200130314000100003028283d000d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 87832285 1250 87831035 87831059
    0xf070204110c2a0a05130605030703050a02240d0c2303041403070302030f0c010b0a121709030307080d06030209161403152205090c01030e01060812030712020a09 71
    0x880429940c816402c00a554071400c5248040d038400b01c070020040031b13089440c5001081c0c02d520456240c455010000b003800701c04940c0c020101c2c0241d40b4104046000740c80150391b184071000380800031204015200e5102040d50083c00c02c0320040c40c00c0981d40314498800e000001010500f00c40000c0c00205000403c50b80c041070b490304e4542d440155090800a07240a0b4803409a450031465810001030004041c18082d4080c00114500400302c66071b450b22803442d0740b10242c5a603012507110b41000f100800c600c01d0507003a1914218014000c0d45130203d01e136620f000a820a100035884203485220110050307a500d506c103886410340310912404204403e400401900d010b4030441c603100400c0007030045000b48070316103185a9800703843c2e8021200b1051001d8100303140490912a24602c2c080074882d0345840841d0125404c0000d030f8080c4100b0030404856800c81d2000d110707110283e402540d42030b603903604010107141d1007281420b00761404400c40e8482800d036070209528100260304542c0074856505011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 87833535 1250 87832285 87832333
    0x120f0106051306030b06150405030a030507260405130f0f140112030c060c02031e09011d0607030f0909020f25050a020103050c07080403060e12070302030f070204110c 73
    0x40705000d042d01c4c0d6102c03074070364904c080c086501441e0300c101100f05071118842100d000740030140880741101200c5c240100180c100b014226624000380510701c0400380115100c03480c80d800180f413185028030380381c100504241d402c0c5035201215104c3c0c007003803180c91040c403c00803060f201c10b00110b030140c042c005050103550160040c4002c1da10340010180031950103040382c400a0b901500014100c9103d0030241d01d94018510107401c606200190000a00045030187c0180042a00d41e610156400d41c81c0350440403130011034a80122007480301c01c01107449058580f9103000e85041503840183c9403021901641d1003030310b4001143c0800101112401c10310011820407a900d0820942c4001607603589036100c1340c1c218006410580c84201250085101e48120341c1c030164007041e410343e1a80d03039180110180540348500d240e10f0050380112240d8035580d8040319592039041d070255190004c00b100d0641c4c6500030200598006603100e940801d0701c440600102140c00b0030310010110003e10403e013401d086202 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 87834785 1250 87833535 87833569
    0x306040c0501030e120d09110d03030608060a020f27090709060801050d0f0201030b010516060b1e0d060c020c06030c03100b0c0c01030908071e0b1f03030509120f010605 74
    0x900c031841da101c00c081d0545030046c0000801007100d030150300b40251000401d622095100680c2140003080541561111003240d001c5400e8a4150b6200c002d41000c0b800b4031031500c40b007801c040103100a54111650041e0710171a80c000c84900d0b101d00b400200340a100110f034800301040e0096804d12846401c403040301d005004c00c803084140944941d941014121041398000d050503140c4500040b160b0007502500d81001710900c10240e0000306041c600c0140400c80c10141c040c6428141c0072801c03681d003280303400502e000503011100204580d034404008080854400046014103e8841d41c81c0d83e13428015400781c070007600c8081e03ea0601d00614030880d070755a8441c12480604020707012081b48041014804000242030018007200b2605000e0100d1080640003400d0343d0415000000c0000c0c00c00031091483c0c090501c0d240c1961303034848010030000510f070203070b0300c4818907a07800c200091040008010400d009070060307890401c0501c216103400d600d04a502c0311a5140e0009100a0a0100b090410f400c6a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 87836035 1250 87834785 87834793
    0x80702011802011e0e03100c0306080c09040206030705040801090305071101022116052e060503280606230306040819090305030a120605090906060f0102010b0306040c0501030e 77
    0x1940d00290098001940c04c45034a00c0340600e000145000710041c8450301d2025040c0e50942c42101d5214004040010320240440c3c42e005010500d80000507010404a1000c6c19144c55a2a15001c01c80c00381c0005021000f0001d08000118561000f8010010024071a40315951034004502d402e10200d031168500c241103620120400c880303540e002013803003843d489022140795035002c0000040301041210402500a102c1ca859041d000d0990549103000d44030000d610b9209510045026020341d440c51054941c035a00212495510701c0c3e02501c2a48039450300e405201c00045259142001d607005030303010012100550b5040b03850b40c503194030700030041c100c200d02400d6680b40c19561060b46000c0e0400c100c40c810500ca008008103801400520095034200c411130361520b550000080400c0d821610062205092503000100c9007405200d00340550034040113442d03503070b8400060141211f031540d50141199211084036401d83ca0a02c14a4069801540500034043c100000901030343d250740c1d005125540 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 87837285 1250 87836035 87836081
    0x40506040209132403051005060102030a0c1b0e04230109230304031407150f3c0503040b0609101701020f030108060a0c051603030b130c08070201 64
    0x5141c03d818018000350100c0007500c400c107184054106044280c0d80000b080e4401c0d401701c02d101c80024400000b0440081c21b002e181d60b880300480e20b902901c61410045442c020f500d40c00141251800d041e61041002485020381d0f4404010102c03540588043d00e00d110006508440d2400d00d0344e80502d030320504402800b1528055a60f00f02d05240000c03a02595020b20145010403013062044500860f0400c1076000010f1940023759261040e500c1900000e00f14000b290a9107405507444904441203504e911100303407248501650700c0c02e0a810410b0044018448082060300c0c1e0344011300c441381d11a60740580301e1a1515250b11044c00c090704407446002944100543c3c110b0709907080701038600f030104500d0020324060a1034060f00804500344d11a0001000114050000081040c452614501d043c00300c1060440c2c01e90329845aa43c05021131360142841202290003034000c4a0340385009092984100000b0078043c0484c3c0d589110320700042d105200b844441542402010f459518401042e84090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 87838535 1250 87837285 87837289
    0x203010b09040b0f180702010c08060d0b0a0b0406080f0105010e0c071502070b010905061c0302370303090308090106060c030806010201020910050c0d020312010603091b0f05040506040209 82
    0x70080079001440390740c9030704414103152510003c09440100141c200d0b22035051003000303401a2401114036000540c60300d080244030034407520b481030161001a2000038486999211860103078401071030304500e6610f51144a209449a04ca020f000346500005000c3c6403621008080c255036040e4071500008107044180407040d90030742d00715000580e11110f04a118815142d0150290245001c0504400d0700d0a00000ea450201d800031441140221603a0341940f581c1e00e10581c0c0034440c1a03003c1c0042c1c0c0b04148030750310b095000700c03100343c060414145102e075503a00111401207000c584d4800c40000761144030391030130543c07c50b144030780142144000340415800d04100426403880f45401808009160020841c1c590003907044450703420700940312025030300d00340300013802992004428000c5845400c10120410f840881a156001035a0010f40c40c264608002180507041c00701c02514000c00141c00c142c01c20030340b0304d94a0018100c80c0a69604c051404080004841c8020035040c051401003002c49030a07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 87839785 1250 87838535 87838537
    0x50307050613030606180c020d02060f10050d0501020a03061d040b0406020c0105040506011410090e0403020f07080601090606050403021003050c0d06030f060b040b03030703030e2107050606040203010b 88
    0xa22030076545541c40d901c0d40d50000080099503400078140518103640445c9100c2910030010400d01c46c18410b000100784900c3c1282d030380702003400000045c1c03c04c0c0c002c60f4001d60600c13001d58020030b003414914a0755444a00003111300c8424130b41110180c2d40040c400803426010300400d00203042100d5501400c03c0890100e420070040180000c040b041e203600050100000b0f075041e00c00c0014850020080b0b444e29181041d5101020b019904040c603407404c0341202032030101000c1600c0002d0303503500401e2a1811111000901d80500f0071429402024606038483c83c0c200543c100501c40e0b40700804441d49460702e09411254290808400c1090801c81400541c940c20b1602c80e1020b110302d0000390a0380c0741003000d2028024441d9407803000c2e0509000100340101000401c120034003a4070200320f810b450703500f00011a00c600e4081c9030160420701107040403a000b40c3c8041c0b2105a4007054512220015001a00110848104140304480880c04405001003000b840340c1c0240c0c2a2421442c40d41011403150341 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 87841035 1250 87839785 87839789
    0xe01090b03070201110c010b0a1a04050d150e060106080105030601060503061002070e01080307020f03012c0106091107060f1505061c020307080103150501030308060103020c151915050307 82
    0x845040040480c55140c801d40c0719a890035509135001d41c03a106040d84080c060441a04560321956613850700ac0b4042d01d1450b0209820f042e00c01c41545442e24100074007841c0c207000603055031718841107000d1071340d501c119018900195803190090f212940c100f1401030100001a0095070180d800030005104482d00402260f4001d4400c403000e403000b0414150803481c002442c0c202c9116281550000180072500101905141d4802c0364951814640309013030500321000340e80c11074440c031114000c40002c00030042102200b03222031030002ca01c2903240c80007003043d503041c21440c00306410002660801e020300d520400498428000082c024824a420f112030310318290b000361031181030001b44c80c14411511300c4000c4100001e080d8195200e00d40108041d04403070007440305807000c0804021100c0c0100d650303c1050f05a80e4907813100c40286d20340c5001100250071030f510b440d10710700c60040000090940f40c038489101301010904a00d189540c40401400d54070400480c1034003c0d554541480700b65404248041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 87842285 1250 87841035 87841049
    0x80307031812020607030e0f10110f031510020307020a0e070507051002070501060501140d110f07050c121504060f0b0a090c0201110405011205091c020115060e0109 72
    0x503080400a20301440006035690081090410b102051491074001ca041d601c619200d46041040c1076204000540b2109102c56244c0300e90071510030300300300c5003155104201d1080300d42c030f0240c140007030900c0100702a4416200c84500031000500d903201031826440e96410000d040c80035500303041c0f441d40451002c8100340224442400c5407000201e009100b03000351042907811074101c6500c801d04040b080300030f511401d000e032119400c014001c07420f54065200300e080046035558040c070700400c80e40044010000034007240da00c207004100a4200c001c040c00a000c5c51b90154003e007444a90020030070140c0720400302a024281c12084c040304400c00c1c1c0c4014107900079048600071a915908980c401c00611a01e00e211f64003641a50340840c81d080c01d03030302c03401507242e4540017000070025442802070503005900c00c83d8000340c802580c90075032100c81e400140e0803071211012070b00300e000700e566041c1803041c06424190050b99610a0090448a4040942c0040c049810641c0482c5002c500080c0403c080740a000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 87843535 1250 87842285 87842291
    0xe03030d0b0103180c1d070f030908070c030302300f160f0506160201060e011203090305010c111204080303070c0c0308030705071112030915090a030506040b010602030708030703 78
    0x160569001342c2120028002c40079001e03502581034904030034043c503e40a000d842407070800d4030001c0100c0b188500d6026000d55190003160b840b189000b18090050980d0031074080701d0a015010006101d028248041d46c4241c01402800002c2c0d002c4a9400d00001c03034060051014a04428085034050100d40007209980610b80d40c2e080d200544826980c44608002e00800d50780c000001801400f0030202d010301c0d04041c20105444c03150108a0a8951500844048403100340041200390121a60310711024420f0500e580840d55a480322421200f10b8142100418802c4c1600100c24009210204000010184581c06c16003041c2c00e050303407400020b0035281071040481c00c410a110800d04401c0007158013030195a940d2800c03410060064101e40350441e84002000d41c0e40e040c80c5030880010312802000e0000350b060441d400e00304a03015190114800851600b08000d0f020342c2c0341d0240010140d8054801001203007070a1400f0f40f061038050307010f00119002030208400145007082107035000241440c0c04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 87844785 1250 87843535 87843551
    0x3031e0306150e040b100201020405120c03061513050a0506010314010f061404031203090b090a050a02061c1508060c0a05030c0d0f0c0306090608030f0706050c0c0f01020c0c010e03030d 81
    0x40f600030040d98402c031b948031000d8020301880650540080c02614025116881c040700016032903a85c13880040551070340758104c00001129605c43d000d01640e1540c008024840440400001e90b0440308207031790481c3c42d151104100320055030980140e161504503908495015854140910038407078072401030b00204070001d00409031a03c680700903a009140c104484800b042d107100805402001e090310704031151540c000c00100a480045803500b000743e00000035000079807070340e07082015a511603030041d040340494092070315590a4912503011001e0b10800420708072824288442d103003030402003505641003410003000c0e126a51000039a41c002d103580d9030b007a84801006150038094468090304010044c54841201e0500d50315412280840300a14000c01040c0c1e214040c01d622445145103044d070300c800410036440080c0a6502540d840040703450360b107003000000c0c0f02c44d0b17041208030060311185a401159034100351205000420380340c6000d09010a10184100209449014402c10010b005543e0162 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 87846035 1250 87844785 87844789
    0x62d0703090206030901020d0b1e0f01020f01141009020412110103021903090b0a0e0c0d260c0705010912151d1614010c1709090103031e0306150e 64
    0x1041c151190700804940d10303440c014032118001d42103210a02c0b9140d0621003802d80a003400c0c03002100500034aa2503c02c0d41062400f03004510010079004c0c3e0440c481d50007058001c8100f881400301007808a100c0200c1c600f801481c1c081c044466800100e0240d20403c41007003001c4420360151105c41e0312110321300725402030390300680c000d0040410134480003140c82c60260802e94150310072603d07544600202d0a19803203c5205a080310b042c40c02c200e0484d801a0368007211881c3c8081c83c00555440b81c003042100038865689402d0320304550303024602c0f5882c00300c0c110b1078982061200001400c000c0c64145800c6140052283c816001744801411191829500003001032071500100e2980c11511051030900100c0c0040aa440201e032402e214403000311a00030403500c4121404841142c0c05941d44503d4110030f4891251088011081050801c0b0410520b6065100c41d61054000c1d4002e46482c001c40c580740c0c41e407180100070584144101441d0000034041c01d041c604540e00b090f05145000b80b400095140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 87847285 1250 87846035 87846041
    0x12030603020f06090a1517130210030522021908010b1008040302060a020f0909041103070602010203060612100e070c02090108060f0a0b0a080703050303012c010506031308031503062d0703 82
    0xd80c80c001296a0800c20600c4481540c00e840c54601c26184641c81c0c1d8003842b0103d049450594240c40b015401c2c0070b41c0304c02d810312184880e503490b000074842040900c42404101410f01280e1182c1001d035190028000d082c600313140c03014400b0381c160620521515041d50001d443d0300005000312500c0e5030129840d00346200043c1a47d0885501500706091818241032501e20a1a0f240445100344903030308000c14041d1041c001c0d24003c14010f8986801c2c980c02d01d0b00040703e440000d22050441c04030010001d11015001d40c4140950902c0c1ca070403009180c1401404a5450142c01c07480c41b5910081c10301a81505118030f481d40106e8207000060402e03030700380c0001d011204560000000e4400c215020040c0300700800118100c500c00d2001d0040301c1355907c080c880e10580e074250000e551207510010000790400d0001161b010041d0b039449030380c2c4800b40e991004250815644004594904140b500031824100b001980001012a4540c8900c80030002c5004007008003040000c1503000001050019010750 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 87848535 1250 87847285 87847307
    0xa150902090f090601080f07140f0604030303020d1505181506070c08060a1107060207020a03020402041e05030f030d090f05062503061404021612030603020f06090a15 73
    0x10040ca00750b0600c05803444001c0420755009490707000b0030740001060782000070107840d05081d03400038000240c501001c01032024516140107821592048894556584000051014502c2138500680707079121020701c50201c3d003000e82d0500002d101207a05004a41c0c1d00041c4081c84488804200202d6460442c0454021480010707207412a4001c00c254040003604101030003518403078822102c05545150b444000e840301c04c650407000c214104014404505aa00144289400584007500007a41c0350301140032a072080c0c0c0980078100f18020310301799164041081c0002000100d005000c3e041150100c5502d0380b1070058588035542e07450b04c0100421142c05803540c3c4894111042e117155103030105484a000c41101522404c5050008181841c50b002e0700c030b001e0565003008040780a2070b4244080c04000c7d4080310f00c00c48945640c00c50000080d50044410750040c1c09582c01050240c55881844030b1a800181c80d948074420a00c0110079a4030b50021140807070748100600c2d4900405a0b1080e00c24801c41 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 87849785 1250 87848535 87848539
    0x201020406080a020c070e0702250302090705030406140115110607080a0209030705040f021e03010305060a0b04020c1c141606020307050c0a11010f02061e060a0b0c1513050a150902 79
    0x11f002000b403c40d8002c94005101e042207140308902805040c0018813011440c040258400c28610218500358880d0001e1940544140310000da2010f0414003034034480c100342c0c04203103c4071600c001c6100302030f40002c5900d4001207140c0240180c0c208140b015101c6040140302240099003c29403031100d07034003000000003c0c54043c10800c01d04c240c02e00380300c029502c50f5100c10250b400320f0311004181035407141240d040b80e42110162285031100f80580d0064100c80041d02d82c4a41c0902001400107420300c0304c40d44c00b298030b0074407600340741148202524800e400d010310750310410b041c1300302c801c2880c01c0c071100d540300e50b0700040040e41d035a282e20b42500c06003c1d00d000c00c1840d116071003844e400c000000d48c0f0046a03800980700d10f111030840c01c000700c2c2e580ca4101c0c8c82e1103450a40f0401d0f90f90b00d80c45910019004100100400e02050300c030813596006d0781200300c00e9012a8848440080d000c4001c1d012103411050f0002000d0001c90303251a800c1c0d50f40c014000091440e142450804803d207056803041c8112580 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 87851035 1250 87849785 87849809
    0x2403080306040507020714010e040e0d080103030e040b0102030f2214030105181c020c03010c030b04200703081302091509070201020301080c0616240c0201020406080a020c07 76
    0x12810400280c0d002190740501a5241c0710104d01010b00004040c0102c1d41c50354420b407a41c00049004413403503641062201d80080c1c03596075030040990244070702d400c0b4440a54030302c00a507142d41801840d1041c0a96002e025038600411090183d07804400c68080d40142c000e5107a690300498542c2c0741024004000150200352140081441c3c640240d20010049084000348040e848400601030031042c0e0908035021f5900101c05208101c580010b10380f4900c2c843d0041c0d8818801080100b030943e0501000c4a00103990380e00c40000d14506440703042000020303100c01d040424031043c83d42c0724900c06c22101400b0700074544001544c0910003021f100d00554080c000f00d525080c03800011034036070852180c080c45100e403000010007440c4140300380c078104c40074080240103103585001400b200c1c0d0700910503843c0c16403110500001140b04100e00444015a1a250924503410019418100c0d60800024011a4010001040f645034031155813a0001d9404070016555852800c4461402e240e661280074040d038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 87852285 1250 87851035 87851039
    0x212130e040309091406010903060e07030501050709170303010602071a040f060c03031812140c01020301030b0709080d05040e0603010e010c03060501091d0c0a0203070609080304031d010903020424 86
    0x98010780f62811501c0d2190b081c020000f4034400c111309070300101e48032400a84c940c4420404520582c115039428400c1c1d03400d54080503240c1c1c03160360035030f0703c100d4a9101040c0c5522040151011080c603141403590307150061415541403250083d290440c5204522020b80f84110102040720554100c400030b01d0200d9160880c03584d144409006001090410303000700345441200790745a8103068041c160307141e01c00042070162805100599921900c104034601e0010240040d00b0200024802107020b14081c0449001e070740b41414000700380c1e0130b0f1600419070a030042003004110503001800d40d03040d02e116614038032103950b40340082401400d00c021200c04540c00e041d007031020b00d078156001805884083e0f9a0000c00c035105c002080500101104460034412003070005480444013078080c12000765580b06070f91030200140c030b5100c16217901480070b03203118030000284001c258104040340c2445171444045c0503c2c07900400060801e0382c0d944000b03070086844140b240154030380365400c00800324002c207510080316 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 87853535 1250 87852285 87852287
    0x1803040303260412120b04020c031213030e010c03051c050106080105012109060207020303040b0307031401030b15011e02030306120f100207080f0a030902090f070212130e0403 77
    0x2501801084451001082150310b1182444058900c80c036005502104605602c403411242c88030040781015041e6a50207004d1070a40d2203000030808000b0007402552928201d400b4018100000744c607502141220140c0c07000001d0708501c07101403c00342420803540d010407a040070381d8984240e0b50004c0303a841d045910094411035642c40a4180c8140d80ea588c40240c0c3c035800152044a40c0090110407141d0f10440c0c0214102d05411160501d4800c00025041c400d0700e501203443d540180e008030140c00004410840d1107545440f401c0c0040b980c00044030036a51640e00c5c1c200d01c0c400094900710300d0007481c089402c07169006002e00000311050540040c0300c1194540002d483e1f4005a450a1092400c41c00c078945410b0002042207400c100f1401420300c2d844d1000c0341230001c0d4001d80040710100740500040c05007062035006005801d080e0746000c602c4c80100c0c4104000076100500700726015440100380000298001030807610781c01030080c1c25a44c2c4001d180358070108400c03a4012201401e0040401c0105 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 87854785 1250 87853535 87853547
    0x1b0d05040b0405250306050c0f16031d0a09020a030e030a0e01092306032505120a0501060504051002030705010603080408060c0a0e060702041e0b131a04051803040303 73
    0x2180110240c0351825000b0400c11910100c40e8004c403944403001d00c0500c041042640416002600122404d1901044240a0700d10350017840303600c0201820310f080d5000345a0420700c007600740d9250fa000d0b40c03038007822100056029207860041c4000c042d400300d01c00c0c80c1c2c50300036130000c4c420901c858212a11111140401800500e80200e89400601e12001c00160083c400d580111078003202c402c070902c9040c40c8401d202e0031350001008072107850200f00c03012000f0440110050b01400055550f2591194000e024810060000d0515403541e40380c4001000101e0b8410700380c90030786004880940c000b0b10496002c910718014140c001e80603502c3c0400002c20400304c0c0009000b2a6085030645036190b0f03074107031008041d00843d92401d01141800715100d0303261410b240107040c8030b480280b0028004004400c0000003043c2c144805030b10503a0741c140a1460701d06942440c1500f00c191a00f445034102c401451030300c6030030034100c013405140c07507002064451110a21391320f44d038212442101d48035642e03814024a4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 87856035 1250 87854785 87854791
    0x2100f0615020f0304090c1803030810081b041104090f050402150408070b03101d24030c150c060c030403030f0504030c0b10050301020d060f0b040e1b0d05040b 70
    0x70449408403603098290020801ca81c904030101c021394105444c14004101414003041000c0800003a2042990300c0070550410070003a40c000c1e41d904005190034800c071140035030740b0b401c80b4800d03030300202d041c80020104240002118005980125802c2201d0305101814081c03500b00305840c80c10700035241c2c01e281301d46d4801c61090303008071400311410800c0c0d4a4103d5903c120701842c14103400194080c00081d4084006540180700403040b01c00413a611150120820200100642030b5220503003405038500f40c0d07250044001d6004290824031203000350010307a946a10110103806500c501792040800c0d0035040a0364607901c0400b0a4035903501d4210141d01581d84104c0d0100c010903c1c101d1002c0c41100e1034800c0d03910855040c0c55045840f00180c030f50b2503468200412003680d90104881c045000d80b000c0c00501000021540b0100701c0706c5c04c1540342c00045606030000e0302c4821050004202e0f850b940240940c200d000a40c0c002c2c0216180c2450003824455a031512950b941808144000c00401c1c082c1c01d44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 87857285 1250 87856035 87856049
    0x3030403050a150203091504230d0f05040602070614090d0516080601050f0103090f060e030a03060e0c160501150f090b0907020619090b07031407090503030d05060102100f06 76
    0x311940c006500040b4001625400c1c0386d03603c80c214042001c0030700d44240d504640a07412411048000141005024007280d483d00d8298211400d900c0700581c1002c84485405814209503090038240740000790b42c0c00240c413803442049215130051a80c0d40005045440002000c1d0418088645c1070a209039103e80d4030b200700307005020304a8009490580402c2040c140d40f4000c000741c00f5505410700441c068401841c06840c1e400c0d04511500000340a4481d0900f045040740140d40c441141c41401740440d602640000032905541c030410003d4510801220040442c000d41c0b12034510080c142a40100781000d191880106d0114020481000e04400c502c1201d1080d035060004c081340354103001024809842035405a441400440c80c0c2c41010303116030505d5410300d03100092207443e540f0b40e02c005082c180c4070080440d55a81042c4400c208042245a0203400f030300304403011030301d000c010030b40d40d118012100d500e1030703511004a4016882031025031380800701c10400744403222001c040f410040c03440c0d115100f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 87858535 1250 87857285 87857303
    0x9020105042313060f14010e040915270b0c190503010f08031608030604020c030d0207050f070b0319020408060403110d03060302090a090206040e07020319050f07030e0f03030403050a 80
    0x41e00c078607181c01004c090711241c860070003149207010200d000d4661012412070500000040c43e0106407201d11411114600614280000c0e8000c950803904446600b0800d001042492020528039002e0030b46006805500c4107040c0342d1a664642d4040c014001c00d1a2120101c4603000081c0e8444c1c2d101c805541030710381da604120203280d0785010b070070341da8840c5000c280c1d82c110350192468042100c20002c5d40e40f24501900c094a0324150f150b10904607030001c42c1010800ba800f20b5502c007402000c01c026000300d001c1c04000d0508909203000fa11003800700034171200c1204182c2200c2402109941c05803001046110115607507400c2500e40942661401c12001c0528401e100703408460324400c1c09442c00b140c2c1c0180c041189610f89040e0341c00988070087d02a1307000304040100040003901105080e104131401c0d40a940c44041101d84035200c80750003414501003080610040d01e03110092002c41e01c0b1651706003000c44880700340310089055050010442030b414000490000700b401000f00305007040034400c60080d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 87859785 1250 87858535 87858559
    0xd05150a0509160e0609060102120c010f36050106031a07020d030b06071e05030319050f040206090909010b031204060809031306080406090204150303110a080d090201050423 76
    0x1514507000e01c542c03404da100d18008604181051a495030f040308044c41611054005480078004c1c1b64090360580700700d0381d95510b800a07018050703c14209494004003c0c03202040c6071686914403411003c003003070303e500c0ca90340424041001c00d500100c011540120900014506040f8040c1d5882040350400094069102c0c4c180d0300c84d00c40d1107a08803400004007507d044c40e4441e00c400544404001d41c000101d4066a082800b1800400241d4031a00305203841c0c60541ca0082e00010903030384080d28a4900d0b01100c8140310059444c2800ea40650400b500c280d02c0640d04c070358036680580100155142c15018100240480d500c0000007481035442c1e03a1544000c40d00d50400c2a0ba80f80f0070a01c456801c1c00c403100d802c2c0702452050311a160001c1c000c9501042e0050707581c00141c100c134142030b00b400b0b4010248a041041581002a0400098804026103d03001807034541c84035511803d104440c0d11a559514001161700503019100600b008004c03142540c110064002c80300504540584d1081007403100d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 87861035 1250 87859785 87859813
    0x310050610020c0a060c050a140a050708010501140402030c070b01060f0e01110c0d1b080a110319110301020f0d02090906060c100b12010c0c060f110301050d05150a0509 74
    0x40c03203c1d8500980203400f076600d011710840c0c140c24184022141c41c050b0a00c40408501c40c1501d404000c1e03451009042036103041c1c40d2141c03501c0c0442d8002440d0f641400c004000c040340140c0c80300149042507601682d80c0da00e19403000c14603c12150020f100524420000c03800d1a0702c00f03441540c0c1c0700161190070a40c4d60040054896400800340640550711140e56040c8604200107003100c2c5a210386149581820320700e40c4c5003000c88258010f61380ea0783c00313800b81a00b4001e01c3c5041c08910030080d07010b400218034144400c000c10300040000f50000c0f640c0c001407003403920f007541181d50300c2540034138064407505441201c0b0040c6d031040001c00e2040001e0b80100c1c0b02071600c0d07022280310050810092428003040e10b1176002511160030320543c4183c41801d203503c0300700c0c20300802003002e00d1039070b4945940301180381030800c6808151604c00c940780340261071074446011804070307410f4030800c1711030310100c0c1c9252812600d4680001c01c0d5208103058030b420300030104c0c85038002350701604c009029501c5105000781d03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 87862285 1250 87861035 87861043
    0x30f0f05010e1e04120e030a1202070f08060403030c090812040305010c030b0306071b02090108010c0801140607080c010f020f0a0e03012318161a04030c0303140702031005061002 78
    0x3c003030341c00d2004503000301d000240040701c44031001034035044c0710900404480019040905486007550f14041011b290300f9219030620140c000b80c47d0b5048580c05d010b041181da40d84d0380000510060516542d8039a042c402402003580350020b02c2e0410454410f05c541c480f1516880d005031004862942c00c2030040056103000e80030340402080090028540c59490820884e03104075907000581400107802c00010141c2c8a1403500c5000e0b20101c4004107400d4000700e0300400501050b4060b08807514864180301e0345907107600c100d60800360000301c11a15009440300c0c003801171042040c9818407902c0000c0f43c0c40d01800c540302900000510380c8031074581c0d200820605003a1410b07200e007a2040a07a2407400c00c81a08104105a0000e900b0231520020681d070442d040d281000300c00c018a00400c40000030800094685500b11515402c200703805d041c5031070341d96460802e0203540070050600a4007140c40e401d00b02c2d1001540d000700d070003c080310f150704074003c042c00091200340c075501e003e4041801031010640c0006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 87863535 1250 87862285 87862321
    0x80708031e040b0304021909020d0c0216030804150909051003020306010b0f043507080c01020c0d0803090f0a0b0106031802100f020c0307030b18210a030f0f05010e 72
    0x43c01a26540d030303036802c0000722001200c460010130a50003001c5020081440644041d0310145400681203109202c080e2503e01c417002450b10f5004403400901c000345000c0b081e40d04442c1d02040907119002508410b0360b042445400440016142c1010880780307010000505e030480340280c0c01d80e15144d88079254a0790502c00d6440310300e00c0a82c01c00c400c0200d2643c0c60301000b210410200250f01858890350220203400b00c3c0420014154803800c0103101c801c42c14407110000420900050002031545404950354640c0c000020f17010b80c10200c0010140c207410b01c1101ca030360410400303441007580705180200300352000303001c0e0303030000307072030102102d0002c01c0c4440c1c408515a0000c2a104d4501c40088040350140c0603e1070b014114040c5104404003038900300319290203135218444001041c6449050349042c825008000c1e0a141d1005a40540000080413a803a00003061801d60380d0301c3d07800d65404d80c00740181d84084020186481400000800542c1c80903043e41d02400b0b0014041c2c5642d020304880d04418 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 87864785 1250 87863535 87863549
    0x405010e1005010c0201030b03030310090507030c0c1214072d050309090a1e0617160905130c080c011206080c060304020f0d050a0605070c030804020d0309080708031e04 74
    0x703034106001a41c040c20b605000c00e481450080344607140390f80400d003581c00503220b01003c503d04e40c0e410f011340c80311130041640c4108280b50410024841803001416594a02000780811092036501e00324540300b80050102c00320600704081d620300003403901c404141d000881d41c0e2203080524505207a14104101d110a480f50054011801c20419104100c0c540c200600720030500c542d24404060001a94002c40000154800000401c2071502414083c00100762010100c00d402240213581c20898004a903000d650740e9520000f03135941c401145443c010005000a801100602c17000500742100040442840c002a41c952026143e01c1000c0d0040d80c00d80d02a0361065045800151101d003000340107550700034001820b28003413070440d201240c08404110010b42d104e8111040c00414498140103140e0802c0c010307d030600c85071b0002d80700101007250240c0000d104503501d0045105040c03091410a010301105020b4589050b601c8280d20341e2507002003546420450b42050181448441d001030790304075560 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 87866035 1250 87864785 87864811
    0x20105070f0c02060d0e061003150b01140d02070614090c0108010b0f09012f0d18050906031501080c010f0306031101030b03030c06040506060a120c0b0a090509150405010e 75
    0x2d43c2007082a0b00890302031941165114030045000d2010050741e806503403281800d83c0580d040d07080001812031400000b404984c00c2c020440d049983c40900f844a0724548a1a144c0390343c040f13052070340a407085260180880e42884602ca28150441c50030034007815500c4200c0b074400b90741d0f50041d02e0b001d0302441410182501444090001c169a9000745030f040014900464680c604045039002500d0464911b107c9544200c0700d42c00d280c00400842481011504007032003d4595038460041d480801d0140c42e00801d0140042141130b20100061808000900c486840315130b1100c1405560784421a0038500268820049020117402886070a0a03240c21003010900c0520b040015000342500541c89a09444100036101900740240300281c000c501c03400141c0b4507801e00404005c0da41203690442c0c51440d05100113480060b10035004a0100c9000c40c42d99a1103e114040c162040f00b5945e01c840d4011110340304100c840700002c0c403c4806003030f0444040203030f0b036200c21941d08d41038012140890340d460 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 87867285 1250 87866035 87866057
    0x30206060f0a0e010e0a0509121603030b0618010210090218071403011707062c0a120501050405060c0a020613061e05040c06140f0f090604060f020105070f 68
    0x106405181c0784460050700301600c4035610440743e0a209803d900541d2140303110b0003880030103000340c020700781c118822100805c40145448102c003007521550302d0355181541c03510481d000b094007a4110700c0f06c0c070000030a007030345854400201c4e850700448100094014002d0041364005401140f040790302040e0007501181030b1501e002d190307a09500b0040c040805000409003101c880d061118015400b0f1711040c0a10389480142c1c2c02d91501d002c0c03003030b0006420700ca016035034144c0c0012004051009070359150300710007040020f18007144121100e40c0240390860300620116052110541102c0c3c0110301c2141152a1030f83c80c50034400e094061030118000507081030307002c200215109c04180030114003036840083c04600c4040c091180c074125144240c029a1034404106c14405000203100090120b41091828110002208041880b82c86c42d641400c0d5404501c0300030000c0c1d00f4064035110b882c003426040c0d84580b10f2001800100a4190800c0150700340310000359071501c110404034004409880f4240c6900b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 87868535 1250 87867285 87867289
    0x9150c09090f150f030c090c13060f0503070e360a050603030703110c1314060103060602190c09110301031b03080a110309030106031103071a07030f020f01021c06060c03020606 77
    0x41c200e1000b170341c18030a044280e003c1d60b480e02007440c010b800c58007845035254640c412620320400194059800d0204203105c6240c0c0981002c1141d90050f603501c0e00241182005000403500f04010aa88000c4c170b080052171006d440c90100c084e08c914111800484259440803011000e858040390b0080d00354109000140000b4011425070b40b614107800252022038506002103410490740c4001410308940358a501e4540d107001301c510942155083c40d051000a0500c00003940c1d0386100600c0004800010000c0300c24401c80750150390140c00424024480759000c210303100001d420a01054582ca00e001c80744141154030301100c0c0d811264442e59460910300610000e50790070000e8049850540000c00a859890380c0a00c01c0c00091882188200340c0b0a01103001d2500e84a000d07000b032140c849400b21107500112454007562450765040c034020030000c805c440120b05044411800560641c00402e142c104040a06100c4656200b18041040300784e640302c01c102e460040601000e40540c0041d4003181c414 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 87869785 1250 87868535 87868549
    0x90b030705030d0f02030412050105060a0824060303091302300109050a020d09061a10090e070203190903020112020702060a08040606120602030906010609030210030509150c09090f15 80
    0x109804c1d0040d00e00b13095480c1030f09201c00a1000045851380d544008001c60f0f40b4089c80d0082c090400c0c500284081c01e0704250040b0039520070900444055581030000b1021754017042103c04505028084105403003147c0340d20006500000b001c90340040c078400003c00c041c0348452084418510340044007910b40d01e8000b40c04018200a4400c0b8941c80e02000310700c92009007405815961031048000107002c008201480c1245600400c00c18400c4000311004038501d60f01c24886000e448406200b201e4a48880005900c0c42c42410000a07844461030300401e032854000c1c0c91041124002c0c2c0341d50305510300c480c0e0070408030710a1500083d030051007800000b4105200c0c42c0c0f1160711078442c0c0b800103511030b01c81365220044100b0140803111103800200b003204821040c00f030140145041d0401c440c0060555002030300151114a2501c2019600d200049650740101310f0500b420501c3c224198440c02c061030403000b680d1103106020f020f407070540f000c42c0b5041440c0c006140b090010440c0000951307080b03c01c0242d2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 87871035 1250 87869785 87869807
    0x503030c1e0102071a0f01140a0306020903030d060e0709081f0504030c0503030c040306060506030103170708120403120e0606061e0405030706080603060c0f0a0503040501090f060501090b030705030d 87
    0x240d0b41d400c0c0403900004948107501d500b207100342d24041c0300c41d2030181d40701c0e07014010581011102c0004002154400c2e1500b220340401d50742e100c500980c48440d0b01c00460f01e14011090400380e01c0e0b0402e940000c07100689050280100182d07900c011403191500482551a1010000b1061a5140240e10304920000b0390090b03401034440d141118200240361500d5184da0000c0d50f40070b4074a40700040800400180707100e03010050105a17503060540d850f42c2c8072001068515000401007038000155001041054412920b5600048403230341c03602d0919040c000c010382c118044440b4000e00d85680e00c10590000203509100310001443c2e2450802107e48441c1e001c0305141c1807045d003000600011442d982c0078440600900b2071aa2540020310f414003c02d0702d0014007400c42c0b0440d000401810212911120441c0c130705d640f103402c0c40c555948480c42e1241c010059400003402d40342c1354407202810000300d5001a03049035144801404080924010561207400c1072142c0b40c0d0580c081035803030560074080e03050424 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 87872285 1250 87871035 87871093
    0x61706121603030801050f040902060702040209010908010c12050f0609041202010603050601081c0f0c0305250302010e0f160306050a0605100207030204060e010518040510021309060503030c 83
    0x85401c0c8056a20310440d4180c1e001140840d0b2124014401070500c020a00c886e100c04540600220140e90089000c522440001038000c1d60000344065480e401010380d1001072404500800800e81002c0340201048500d403030380380f503650805002c00ca0080404290380d0140000504110f460344680da504071200041c4201141907541314400040031070303014401540202040005081c03504683e010000020507406442c50a0085056400c004540e11807468056550705007402655440b5480c0c4181d0441001c60300c2c2864050010a51410594190440903640d01400110745a9001003036030192150302c212420b2003a0303044001d081012512542140e50040d040301800030300396483c0c102041e50604052030500250344451810001c50601d403207042c00828944100d09510b506150001c0c07000078001003405c80d01d480d0900820203109044c4015207a14070081c5085550390121041184c40407050300c20b4466030f6180400024190401000310b405401002000d07010b01c00c600203160650b0005075200403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 87873535 1250 87872285 87872293
    0x7080a0b040f09020a05090106050406180e010602010902011106060315040219030503071b05060405011107080d11012304030507050c03060a0203041101090b0f0d02070206030c120106170612 83
    0x4415038607588511030b1000e0344081d0109501c50b2a0041c085080b000d45d1040e4000d0b20b009004205136036210082d1015160a481d210303410306000300d2440c007900840d0b00300d06955119031000150854055104541c00f41c800e0300c484042e2000d81c0d40203911040215161341d0550810700655107003006106c1103c0e409480200b00d846560a003080c03039005120550400c40e802c0c5d00000c1e031481805403002410020740946480003501c00e042c00c0109401d03000310322805050000c07000c28595008414072005025002400c11503003a141e003108000c0800c0c2c1703444030700c1c082946400b44141c4158505500c603202031100750f40020468840381e03008c81c1c1a5109803070503215070041035a00d58a9540c20310405003d020725040142c1c6a0a083c102802c11404801d81d5038140600001c0410010304920f007540c403083c10300c9060544445210004401900c00c83c5002075000c01c0000800a10004030001703882038030600040300245a0300e810040e950340c0c0b52401c5240808000d500000d10514190481c0c0c2c42050b407002c151 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 87874785 1250 87873535 87873551
    0xd0f0219021f03090c030f14010501120b060111010e0d120501050607141e010f05010501020a020109052101090501090b01080a0b011e1809020103150501050d0203060102070510020c03010f020f0307080a 88
    0x1d0041c280e0f0811941000e0600900003440402582340c2003514404000300242e516042056030303c1a01d2070380082ca0300c1c842e100010300c560f0041c500c8602030380754000203008900390784440c1034a9524640c0e040c00131a500f8000c209001c41305e4820300c0d050f258040d00c1246000a9170301e5004000c0054010030303001e4414000035481010140d021800301e460520b00100d880030860420600342c444c160055411035014501c1800507030303131040c0f0305003c690003074500e820717121100c0381c1c0240000340e10074171249290f08007811882080340540c8014003039405802c158a05da41c851040300e4580c0b48003980544558129401480310200d1401106442545840c0100d0300079036907150b04020310440d000314070100d940d41419200350358150140e852200300c1503c80e04585402c040c00078000d4042c0d11603507803c06901000054099000700481d0002d060b0003000e000603008507600007075842d1850340c1c20314003d5003003010007008000c0f01c0c001d41f648841c5030100d032030031686c61010854181c0c0d402442e0301c1070107480c1c00385 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 87876035 1250 87874785 87874793
    0x11091003081602131406040509010f061d070e06030c0a0201020409050a0906060b040b16300906050301030c2106060b0901020c1002031204030905030d0f0219021f0309 73
    0x10500550440e07601800340100f401001500c0f28810f00b84240d0300c0c20155001e034403480700c0d07109540c001012500041c090b1601300c501801880c240d00344c202010714080c0c0c0842d20725061480c444030340c0305000c100c03140d41e03603a4581202c41540c20b8400d40e400c140203002190fa024041e03009000101d089100060900c2c0c0e43c0c0c950030041e54801d0301d000e045181d8a210b0002400340310701a4101416403000f40c1ca240a280505020f15232081080140b44040da0807501001c201398182940d200f100a0355903544a208118108a40890f400000f680452500038002904601a2081e40d0499820440c00c289041c40e15003c1e030200c8201403050490380540c0c1e801b00c0c001800d00d10a290260402d40d0401e921503044c0303800603280c041c007401c0c01c40c400c0d09480380f80b84041c1c0c0d00000b00c3d40d4091131042070700b160f602c461078241c42c2c1d6074940d00050340c140a98401d22070902da205400050b0307107150b5821204d030001c4440320001c540302c0d4401c0c003035000f003007004250398a410940389000e007640c0c540c50000ba5085050715 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 87877285 1250 87876035 87876037
    0x712110a051813050d090503010e060c1b01090204050a0209011101090302030a0c1a04061a01090f0b160501020c0c040b100804030f020703060e0102030a060605041508130f05070515071109100308 85
    0x40c08003007a821b91060001d818244107410041e1504030050030075040c29a000500790285610092440b103600c941c4c040d15007003c2d0800c9141990141080c0003906044030040041c0d00b26900403400980d03020400005080140184060300b90990003852801710071050880d8000c1c40a00213680701c0c0788070225401c440000440c8a40304c0d070b004000000e0300d148290300c038100140c8140c420704d0401540d03032001c0c4182c0350070302041c100311030361030400d5540d4040b040213480104841c204050055480030a8100c07070301c0c001003807485504008a400704058451782c02002107a00305404040c00050f04400042c001030300420914014035064012955040d940c0c1d515601543c02c8004900071594010041c820221a40e0082c540980114248581030130b060042d88001c140c450114602000f403144c0119183c05100d0007002d54041d0400f041d11104801400e00507074900c1a80b01c3c0502800340581800c0c0e508124005032003015600010226400c0304407010800c110001800b0703003a41c280c803c0000800114000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 87878535 1250 87877285 87877303
    0x2803110d09050102010f1103010b07030e06120402100c03020303040210030e0a050a0c0801051902090a0306020408031b030a050a1409040c020f06010801090804030308070e030712110a05181305 84
    0x561001d41240c1004002420b452000c000210001d050507400340040130f20806403410744000340c1d0159241e0718203040807590034802c00700745030704120000303070704441d100d90941c41c0c502c554025152000c00c00e5070302604440c4001d0400c7c0260042c4c100388042001807400207144100e0072014580890800481184142858414002106c0c00d91104e0507550802c641240200c00501120001700501d02d00b6034001c4070b09201969800c106030f50300040079602555140c1042e400f55411100841d241c64546001c15500c1c1c0c090080310300ca031074084c602695070800010071a22000500e507612400e000c60f481c020755032040400b00740724a000080c004160261a103101d2503010040c40e6004040c44a851207040d0b0910300c0607080303c91203034100310f144408074800340102d5013201e50600d0212000e40d90100c0846d54040c40b0030109505020f0342200056106a0743d001d0304072540143e00c0042c00740c10700820041603044e9441201c0d002818009510224481c618019901000081c0c8401400e8490355442d401c020402d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 87879785 1250 87878535 87878537
    0x9050705040f0e150103020a0303121b05040302010e2416300c21031d0f15010807091e020406021507050304050705060a0c050613142803110d 62
    0x12100c071900207100f00a4104c5000e91000784540e80c1d415a000310b0700812650101a00340310f2140340d500078202482d88074040828090000391100e140742c02c0014100d03030003480203a000444807080700c8403d1601410503000143d030f0039489200c00400d804444450f8000418107000d403005861320340b0128906440280315100303580d002d034105000d0180003420f04c0030098408001c01210001e4000050886620107540070540340a40030001540a0301310040c1000710441100402c0b001041c8805150014044032103000b030102b9a2013031a40082580c0c4000c20034401c5080907880326908010060302c550103048405901d92442001e89c40c2549500c3c143d0f0301075801070005920810303150140106101ea03064108101d450905d18504094680c0c40d607841440c050684981c0001601c60020380c001c89a885c9101d500606a8503c0d107000044810200c040310b4050f1408065802d0202003a8004182e070504844100c600005015a2008031000c1d0381200e1021010700032085030b14040400104443e484c040c0031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 87881035 1250 87879785 87879791
    0x1203011202100f020d120b13090b240d020a1d0106030b09060102030d0b060d0e010b040e0f0a080708070f0807050111030105012307060204060f0e0603010b030103030309050705040f 79
    0x1e10600c0b030004140800d400401c54070341c6140e200258003060701c100e00300c0640b801d034051000360b0f1002c100404d4404191507224400030740036000032400d6001070000600401902c0034a64541c0c4420448040071403200541140800b891021480c12000c0c100c030301030005e861004403540b201941c0d0300d0781c441441c1007001209240010003070141c0c5030140a0300c8801c00d581c0102e15041440010b50350b4042c0071171083d1540c1c2c0341c0544035040d0f111501030700c1032071130800d0081c0081e80c0450140c41c028031f01494130500031424a090036800d00b4002807021078080d1520020400441d554079400d45c240c002c480121032011007000303d0350105c0c1c200c66282c00f03000e02564845a94804a103055821500010b0070440503540510040005030707000702d0b40e10b034002250706061402d0b402d03000c084401e80c442c41000821440c0b001c81c0109560b548180c0e0b4040c0d082040d00c0c1c0a0242180d1000c1107003900091081c415048000c0006000007446030300a400114402c604840030a03888030300140c10b07141003518481c00c1e199 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 87882285 1250 87881035 87881069
    0x17010e0a05030d0e01090809040902181302120a03082703040e16031109100e0901030b07090f030b1311040609290603071416080a030e03131403120301 66
    0x2c043c404c10000200100003042603104550340e5581a000d840f410f248512340d01c0540d9400d54499915441c04590014108511441d00075040f56059031802d0381a8010180b00d400c07101c035642c00140c886610350309a15004a250f0710140c1d0003610781841c94080c5e80294000300d000307004042c200080e20140c410070074191350b1881d00503800ca5440c086240368a080500700403924001c100e0b00c2046441c001001d86103c40030490707000050720115280c190316070b001034064000000740a406810b490107983c2968440c0f420b00d035665016030390341440b0f0001615190220b400300b0702c4852040b84400075a8400d041c611180f246110020303080342d80980c014004252a2050007a50b40c80e08000c1510046d1a2034440c0c10702e506090208585000c000d05040c02d00003040b503411256211281a1000155440340c040308005240c5080c1a080e0401034031140400d007009440c150840c0007005552156481c114425500340c5032806402c2035110300c280f0f95805000d811604a000c0b50140000c43c041c00d0000a074a4801c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 87883535 1250 87882285 87882307
    0xa0804091a040510060e0a170a03020c150d15150206090d0516020609011e0201020c06070e030c090c0c12040807090b0105040b030606120a1409010b0a17010e0a0503 72
    0x1e0454100d1841240382c03404000d040200c203c102e42c01c0e01d400b850120000b12840c004030b0300d45846608005142200c0e03a1409500312400142c042c40684264250b07044501500706018181d5002c8110f200150400c1c00081c0c00e100c06a88010000230300d00d00d20544295852052500751201304c6a1280141c21030360421000d03031001c00c076074960b00032140f07400d51030000c0d1030000f00780985030840300a21036000018458416031040e0a03072411062082d04803020024030742c201038006e6204100780800d0b40035140c00542c0700d5004e450000400d145c0900035181c1402c4660400014810040071040c20038010300060140036006c05c206910f000360140c0150f5114140740c1014030781030340c0f03601480c00d0a04143c1e06a5890741d0210542e421542505000d03916512040001001800303401c0d600f98030f80404904111441c0840d80101992641039200a03650341c59a40c003045c00e90707018800407600501307604004c20004200c1018414120255400050750b62200652075080c02d00d120380696007a031003c9414007000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 87884785 1250 87883535 87883571
    0x303180302150c090303040e0c041707030515060607080702011403010f14030105040305041e18050f060f031b0102010e06010609031407060207060f0e030a080309070e04080313050a080409 82
    0x5811207030161305100b10741c800240d0b03d01c118080d10004181d0800401c02c002400800e880c0503010101d404803584031030040d0a075440d04075201c103660500c18080041a501810348030280610b001400d0786140034940d0310781880580c44403d0490410195030285a8000079010145001c2c004844800f5a40b03460045104190023500480c18400c3e4903000601c000250000210f0301111408181485082480d0b0313847c00e5111000d80c03100c403a50003180007025906540790f101030b2141d041d1200703004581e01d55909200c1c81203800c030041c640550103080103070524100718180300c440c050148000300b5518480c000c0305051031020380c0030710042115a5414000c1042d41090100d580c009071000344000751804600950b1a0304030310440c07090250840c980c0940603c114144021400040d08440458a0310316140410382e10444080c98640681c40012501070b50419000d800b868201c148141503841d4050b0300c0c02420001c9000301e909105a0710140001440d00300038200400e24000009244000c60401da404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 87886035 1250 87884785 87884791
    0x501090b03130f020a031a1009090b010504110c1203040317100509180102120105010e010306030203060402060c07030c1203030f0b060a0f11030d0906060603021201090504030318030215 81
    0xc1503051003000b42070800807800984880c2c000410b01d041e2807050022810021003500040c040d0601c000540c07660070390303a909050150b0f8110412200203940c40d041d000c11a000d950b002064005040f004010750305c1d0a42003504145d0038124280e00d4440c00c020300314a000c0320001c0c004412240072003000281600300441074098502c44404171058544400740b54411301c000d003d0036208022040200d5118611089201e4010092400031075480862040c02006401d0910910380051501514000954400d0007030b00216035015004005680703c0368204078a6030015100040c451242d84000008030744c0d01070200d80284050250941410314505004095448101c610b081242c240310100c500350f2136040480da120101c41c0f60440441d01140d00445483d00c00c10f561a2091102280d0224031001c1075000304c541620075a01000b0f0317107940300300540990080340c203126031444003440101f0001481c0d8208540c00351080c035000855000d4448040005402c402090740168041d10900041012101e90700750 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 87887285 1250 87886035 87886049
    0xc01050613090b04030f2015060102120d050408130f1805070c0206071115040807090b01141608070303140a0b06090f0f090c030907090b0a050d0f020409060501050109 73
    0x1100b905450307440400341d01500c01020480341c94040c0010500c50241002c0c502c2044800d031000e004480302580e500c204100315803168206da400812003a600000e03994501008218282e130800035000d120f1001820010f20540b031056040013035036019a0199581c1c40500301ca00e40e0300f20100e08100303249055550144041e6503480c500001d000016801601100d4141d034112031140d075400e518500904481340b0007031825046002c00044c510140748040103442600c4455084410301c50780ca244440a907050a0314080c0030405004e400315040c20220000c1401c000c0c1040ca0ba1022246545e402040303034032910085e40040d0303aa2030041c00b0030f1003400e15141c0110036031105108281c04c1c8000030780148038913000c1764441c0140b143d000d0700c0764407031180007413050000821040b090f1a101400200c01e40c4100c500310441e0042040105031440c492056100420004d403104082904100900c41c2c202c03949901600ea40000d05415001a901c0703008800007140f140402150b15403500001601005003904049 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 87888535 1250 87887285 87887291
    0x6010e1005090a05070e130518030304120c05030c031309110a120e0703050f0c18040b010902030406020405030307150c050405060702040b0a0812030108120306092701020c01050613 79
    0x100555501d030020350003c00704000003802d0345440d101035400103045181c01e81c02510080305801940095401544a2120303140710040b03001480101c0341d01c0b031004035002021440b4114030009010720950103060518801c10485e460626021403440c5190450300000c144005e08280a120b104003074020020303110000b00e216418810541400f4080451415045094956030014806030701c008000c100d00840d0440d090b03610308010740002d6601c034214058000d01403012a01025214030110003194410b580044944d8040d90030440b051010f0f500c086c00c19103520303800b40000304142d941800102000d91059680306400c42c90219010300380c5040c1d4a98006100b800c0c001005035864010403507651941c104d400040079502e10001805940d01500214018803501510b0303016150344000442c140c0305101c0403500c0c81140f851040040744800c891154000290718040b0340c2c0b24205041d011410302987e0030050003608020300c454220703000b408400070107070346070000d024041c20300f0000540f250039014000c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 87889785 1250 87888535 87888539
    0x50103090308060d030216030303051f03020a12060605040c020d080a0203010b09040f0f0629070305090d05010e030a1d04020c0a0803090a02061201060e040e061303050909010806010e10 81
    0x40c005120007410b83e4012000d06460b4410540700380031480003031440d81580091680c903804d0080007048200c406900d510301e00d4215200045842e0310800c1101da00800c52090315081040c2d0724454036100701d0840d100c079115007020071140d9131401100a080c0c82c641c0100100342142000034146d0f0700180422440f10b20400040c04250741031802c1790300a000c203840204000c0b1242600f00010008403800b004038518007200401e010740c00e4a004d0b04510407080340a40d648000d210070319001e202d0343c44010003050081040e9104c80c240026001010703400740b400065806076651050382140d1256a86400042801083c02042401180c0d40c0d20040001d80b0300b181006900e808c4d5903a81d13802414064031075540480040c01d41103041003100e00403580a40b1040d00d95030f128501510065082c040d80000ca9005d03c5150710740c0c10701d842031100000140006040c0c548034940360381a00d1721409016410007030100042c0c100d94032650807250091030400010001503140030300383c100b0102b028000e0b80c8800c20981d01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 87891035 1250 87889785 87889787
    0x1003030801120212070618090c08010e0a0b0a060e03010606110307060222060323070c110a0b03100501080108030f0f0901050c160e28020c031317070501030903 70
    0x30090644402e0191500e5810441c0001070309a080d90020310441d200c3d580c400700300140d1142c80402e50600c80c01e850300d840d0b91900c201c0002e8a0361003000d01d00040c0004010000358911500080e04010f04041c00146108001d002c0b5003180465040040403900c00180b03840181024441c03100100f84502d070001650703071010041510391141d22400b402e801e80101d20180700c0d403844000d040e01c040320600b0311400a552800040e028050341c1c0c1c01054a4801c004e00f00403a900f0180b80548140c5140d5100d150344101030750b0b180700c2103c5c20000c0f940c000442035000b082040130940294042c0c8110740300e0001083c684000100301d00c1c0c5c160000c0640d40c0050115044112030401640e442501d07918480e03071607600010048a2034003c08005c0d40c0b84e48646180d2800e11500b01403e0403e890b0b042d40100043d541d158138041224030b0301d400390446558944e640e40c80c0c0ca965035020b000700c010705100f581e107010302601c035800e40000360b40c00c140c1d00e111640321861034110081080d90700804081c00d05201d84401a14 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 87892285 1250 87891035 87891047
    0x60a050301031205041706090709110a030f0b1e04051003050a080d0b10050d0b03060105010c06020304080909010314070501030c170702070302060307030b030705040207050a032003070b0a05100303 86
    0x40020622075001c981d44042c5030190741590b018291b000c5803c00107849603202295540da00f550144a18012641c000c503032417416008004030881c0300e500c0d680c60624680000c03001810019062141259a003c8072025a501c08041282c101d1180310049000741040d410007040303500c042c200192440041d1020000500c4c04078cd0f51016a802802260f00c880702010b2a4014080a80c5200e86c044017503440b10b0711894122019162155130036800300600140c140c1410380c0c400d400e0051030b01103807604414070002030654005641c820b100b006124104980030b80451110348017a08211031300d01442162400c030b00030070484030000b05400d01e41442080b5404402800b00c1e25516403500c05940150001040c0c01d00800c90a40110340c003030002d0350340b0714091400400505034610050701c24042c170400002c3c646810b000b070382c10700e540100140c08003013101e83d026220350683c0c0088004a604001b000f2102d0340060016001d10740c080c089016492600c00104001c54900402403020f850b5500010b0000c03a50080c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 87893535 1250 87892285 87892289
    0x307080601050a120c090c05220303023003010603020405032107020f03010b09040b15030a0c09150308040807050109061d04020a020c04021303030e010809100c0504030f0b07080105060a050301 84
    0x182c540c4550b801800d00d5100348407560054041b0314205003a034002164082d00414144400181e0920191801034200142040511002e80140e201c41d18102d4030040803210400c403814540401044440c070042102c041d0b03002603000c6000309902060410071401c040c407015564081c540501181d0540c40328100c0024014a08040c2c040c0d10300d1740c07911480e903d00750b10003012414000e0036000c080c81d10380745c800320401c8111407400d000102240d00c6c2c501c90500054002115900c920458405070a1912a80c004c11400c1007030004203800c4280040455141002000170707048140c0504540c1d4246000949002c199a100004003ca0701800d65200d4032607000d64410200c01321303809a82c600045c041249014000c040301d540c8a440010b09164060861018a00300ca00ca52503d080b10141200150783c44017040754442503a8000c01d09150301c00440d0350005014501030b0500c01c0c00c141d1203480b41c0d006101c03450000c940d098020001c0c0041c00350001403107801407004594003485c260070424001d09901040c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 87894785 1250 87893535 87893549
    0x445060902060409090b04050f0c03120a1e0302130e040807030e0112020d1409030a09060f05070b070203030711030906040306020706090b160809013c0e010207020307080601050a 78
    0x24040400c11561944100d42c020201840706000c052918100710701040819502115944240a60003404686c046040f04803050000c000c0d200004040480c000594003520302c40f0104102000f0181a65951111014a2003240da500586860042d2807420012105402c4048122401010000041d400c4400c031600d003075051030010414440400140d8400910100001d07400b07002040c0d1030361107038555205016525204130000c001e034461141994892041d0030481c00003c501420900666015034104203800d180e5250a510309005510342000b605800d035011001a0000814031000e0750340607007406d04805943d000b0314a025a0000020814030913840001c05558010840c5000c0c80510340c02002d0107034000b0106030003440c00504404102503100d421101090690020071842c502c148117a5804a0b4081404140522504580d0340707400c60004407031081d45012210f035034410665001d008056814030b000580c6800300c2d84101800d0445c2500011b2140c0d02c6600104526078a6036807800441e205 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 87896035 1250 87894785 87894791
    0xc02060f13090e010b13140103020d050a1b030b0601080601081909050f060402010f09080c060c0f010c020d12110d0228081009020309101505044506 65
    0x14400104401d0a0794401e0307011502d407000300110610190001000315404555003e0800071003011101200d40e0100010b05922048005100509005600001d02401001180d0b004d108079070300c005440950300c00c014030300d0108000820030082007024082d009002420044643d18007840000e09801000304207130b800c1034141040070703420740290f480040d040b81c0000655035040d41d40d98074140d07104030940e4100d000401c1d48005c21401740c0b05d29601d10079110020054003003110048100311650300524058803a038081c000e91030742c0c2e980c0d00740300341d184118241d0003508030b43c46003503000741c84c0602100708460428109812031101090841c200c41b42503216000c0182c55070428000611400720075102c51411299540e000c01186800c00c0030540b00d140c081e03ca40340c0d82030b1652403403000e07800161003051682e446150400f00c261119009a11a04446d240513125590780d0780000c1e00703442c0c0203245120700d000402c400340e510504400c58014141080f01004510072440d41104030040d21118010342010b503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 87897285 1250 87896035 87896047
    0xe030604290109140f01030302030405040515120604060507030903021515030604030e040c0306080303040b0712020d020306040f050405120901051314010210060609060c080910020312070c02060f 85
    0x39041050000e1400106101c0059078440b01c0780c0d401000101c0f50960340e800e0620010700d00d04103e0383c10a0590741e02d83d01a60920f03242c0000c1c400540342c05080d20380381940e48100755000b03031949901c480a40ca0601d005003042d08090411000311880075124a0400d400c2c08402030101e03400084247c400c1d06011951481c541c0c90703082078078121603180701d01903250040c4e600303000070f0503401603007080c1803d0100e404100304d045022090741126414415042590001e000180c0886d143d1401d142d4030440c10b00380f2208040703209c25034030f0032a40801070f443c140c16404014042d503801c0c203110b180720b4440011002c00ca1424244c5840c0d658409180220303510725000924a40641d01ca0360640303d0140148503400c03955503c40c07082c80d01150341d184885005201e14040000e07203905034007541080f1031154683d640c0303050414200303c5401e41c2c41072085d50304c01c0c0104034605142c2c8601301c0d0446a40c06960103181c0f1410321041000c00703030b40702500301d5081005140400002d41c4d90281200c0300030300132a4802e13070740d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 87898535 1250 87897285 87897323
    0x603070305061305010b0f010f050901110304090221131203090227091606120204082d07030b0105010804140106030b091203100b210106050909070e030604 68
    0x41a604014600d024140520842821402c1d0039045503200798020710801d50503c0502000183c121560b900162000c5243c6001e030f406140240001c80e818034090200a1812056914681c0035900031f66080741d001400d0049400c410040743c07071b6a2a5038969030214103102c0204440c114901601621010042c00c96030100c5010b54002c0e44032036170152080d10b5005600c10803420503e4241c184032804003001000826000011a0004000c111192424281800c00200f11650560b000900c50803603820040824203050401102d85100029401d101c1030b100d401c01e8064803250140160340095201650600002e5801410319054400c28689462140d441d400d00c00c21160780125075801c65440c050011060080700d0b81814170940e00345045602050710120042c2d6148021240303503000000b001e4003071015160341c1008009658401003407a00c048541c95030040710101c281d20802c003040000402c1002030908058035a40a0124103054080a0364200420f458a4004100810100490001700149 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 87899785 1250 87898535 87898543
    0x90f010c0203030103050c280b030403030e15270f030307180b0d0906060b2d160209060111031204020f1806041517010e011a031207030e10030b010305010801020a090e0603 75
    0x23038111382a00080c655941c6c0b078064115070080d03d003540028144207401000f600001409403220815031425403076980d41c2c075984a480766a215544038010104a00c8440180d405c01c407296440540030007039643d0341440400074280c2e419160003580304480424003080007a4111060b1002c0518240001c0380c015038a180c440020030280c1c05c1490003040c0414031050300495130802c0c40c9a1000700e13241d048012451418074015000d1f5406250340e0400708088500141800d4110607005101030420b289a8001e10300740c9400c58018461075410640090300300000d5152646014052800a468080350000c40c1c021160803d94002d01c05800f95844850044410b090b00c21080b0061030250108100e4810042c0d080d40a4624001031918075800c0c14410035200741032104441300034000400500403081440c1da440200e400c905000e13414003510346022042502d6980541c0c1c00c541e400c0d40d000070300002c10301c000b40450300127800c0001c140e80305010400b101a00401c0c95816036102038131030001c2da921180060320b4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 87901035 1250 87899785 87899839
    0x90307020a0b18010306050a0302120f0a050d090911250b0106030906060e07050a0c0f020a0e010509090d0f0e030a060906090b01140105070b060d0b090f010c0203030103050c 76
    0x81d01c105400035181141c1d8001d400c0f01d44000075007420101d00d00004505940c85401103950041e00c0312420001803a05100c40b414840d680d400b0b8a13180c2d115100c110b810252490300550f100d8000c540c10781300d62503000b051003014140d200ca040060003180400425207000d01030307405541c2130000309407202c1d0a91944406c0645079020126a03d40d41e1a030000402070503500c80c0480b03c3d1030038404045a50a0b80c0c1424078420b450564407981800c04000045845920394142900c44400d0b4801d814003580315840340c0005030100004a8031355503d00740a010749003400a04406198000c15400354140383e00203d400e082050a1420b42c40b01148800024100201c440c2c0007401d1700d10380007a0004101d202e4000000c80c1d800752400b21541d81e2703660711440c66030b0380030099a80080e108206030780c00910300000c1c0a80080700600400c402c00b0b510780c0d9110382120243c650841c1e95109582d4010a0309007409010440d6180340701660455155944030396035080c6080c0745a100311800c08841c0000f9119003a9008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 87902285 1250 87901035 87901039
    0x2100e03041502031b1c02030708090d290f090c030a0b0a060b0c0a03030e030a08060114090d03120b100e04090602090a12120c0f020409051c03020417061e09030702 72
    0x801c0300400d41c00c0a540306c09000c184200140007192001c07000f4004000e9440d401d401140d82d80c079040301d000800001d00408101180c04004c0001e00390003420640301c03180203d01d4858402245c509020350040e40c061801040031607d076001803d003500c030f500d012404542d4240d02122100c0d05865030400100500010f8002c41c034804c10214030760115403070010f00703100c0e2240207840400c02900232428541d00c0340300358211000405c03154030204680707500c600742818000d140c00361134034108510300e4005a081c5013580c0080e400a04882010b4081d2141446095407107181100d0144602c24428405001450429485c43c4110f907200100828020541c0440c0c0c21010000d017081091074a41c600800210f01e82281503400d0010140b02c003260b0b0b8020340303004110701d80101e0b01040201203542004054107044004403824080c0b4201d200311401e42200840d91000706403030150725941003034614140400c20341c1c0d000d143c5501c07000511040e03524522150f81c04042210b4040e045603502c0303203400d19612812000075 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 87903535 1250 87902285 87902317
    0xf060f0c0604110a0803040618030209040510050a1a040513050105010e070807020d0504030f0501060b1b0c0303040e0f28050f06090121020109030602041502100e0304150203 76
    0xd0100040480d1092090740701c2c0303030403265852056040c404011410701884000c4d6004020521250b1b015422a85022200038111306041c0c0e00c99001c83d101000c1030324100d8140d0300c101c40740f005501c4140a1503501000504040161400c031300002e1842700341000c0024001c0e46da48000c200ba52182000086000350404000d02595a481200109030b007003c54040000980c1c810100b00c025101181e03208100c02543d440500385402c507201e002c2155800300d4125440c0d0360310b444c0022041a40c0300035083c0c0715461016100e00303484d034003802420305542e102d02030310030b0700100024044805071080c82c0d0340010040f40b90baa0650390b00c1101d02d8845006061048610310720044c07403106401c26420240c8a0040c920840c02143c546100784944102c00703008100b03040c5100c9200344006c43d04411814501401403400c06411580ca455401c101c1c2d000740c004141c12041e640c800c040381901042010a94100c80c14101b0000303541003400c0d0744a019030f020700a440c1240052005c641d0340300f00305851503080851100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 87904785 1250 87903535 87903547
    0x1401020a050406081f1211190e0702070806010b03090a0b070302040f0914041b03140303041103010e06010303050d060905041b0501050301030804050f0d0812011707030803040b07142106060c0c0f060f 87
    0x908d13804407203114082c80fa003906800a4140c40c40403e0450031074a409004001690030300502c086c0b0303504002e14684641c401c140f440da01040402549600440494500503602c50401c0600d2000007110b40242c26880c0c1000c2602c42d04031064040700c0d41c0103420983c10008040b45115415030040e195001a0901000315140d1207500000300065006a22410b0120220040c520606003650803041918010750045001040030034003540040001c4043e4180001d603861701c501c03180d412203000b0355054039601e8561451800d0010810004400f401e403d0904500395851596405510310680c00b80e60301038882c160b09101e603a01c0d00320306208e031140d2004802e030f1540020400e00f00690300921404050800c0c0b0508200180300200391241640c1d0844039182c51a55191260b82c1c4544000d042c4000300910f0f0036640c1e0843c1034182c00303400d0325401248100259100291101d864a50240444d0b2013131008004040c100071300000c001c00b22202c03e80303521424410368400900076000302c0305260302e000c50025003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 87906035 1250 87904785 87904819
    0x105041107080403110406090e030d0b01020106120f1403120a0b0102190602030f0604050c0d0207020f03060403080708070503060109060e1302040b09090a02160f1401020a050406081f1211 82
    0x8145c1c1c85840a0b1001c104c015a070748800c81c03d46201c00000a00380d0010401c1d01c6000305542c00a10048a0600010034160340d41c05103076640e030000761000d84104840f0103c0c181041b8042600c02000b41c510781c0154207080650745070080c100c07005005140c036943e441030b10040700c4c1d00a10800101e100154960607402c0e00c1c034148140a0f61045503c182020004400250a07140a1061034043c00c41d001000d801d0444014584000398801d10f400d84c0d1158101000c900b90b60f0302004064400c44c030035039a03480c1605106901600300703003000d4081001e10106004203c110b0340c2c0540601d04803200c40c81d000c2e01964007403010030013030084004003091761400000c02003407070200080201805d800a580c0203142d6929140080124080e0380e40c0000204101410440407545000d291500140100c0380001c05a03d40c81000e422a880740813400701256010808004061304282c00c0740d0300c0240b004000c8000c445103240240c803c103242c0954041d8107482c48144044c0305100304a02c500c03401c094901d2611a5004a03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 87907285 1250 87906035 87906053
    0xf1b05130b01020c0d0606091407020d09030506010504200f07050706140d240f08070603020301050d060507050c10050a0507080609040813170a051e0307020d150510050f0312030105041107080403 85
    0x141d940d015210350710710010242d04c6010dd51003100d410201400702a42032a040001509014813088014640d80846640c03442c000c8004015000c00c4051a50744c82c00307180b91803400d207181c5030b0281040c0300c0020100301d18014900c00301e80d030305507240c14000740c060340c15401c0701c3e2481c600c1600012404a0180007061149034071680c402560943c01c04c0741c0d0020b54501003102a0f210900500b60840200103000002500c950005d540100c4942400d904240710502d102e0300d070105220120501d0381c0c49100384411450907215941c0c001d500c904d8804407902d00f640100d940007002a10081c0b584c07030005080868000c3c01d415410103002d0849144140c01c0411825982d19440307000705940318065955011510540511403060040f20701d0043d6040c402141c0801104483d119025580c0d150960013134003451000d03200d03142c440c1c41c2e00e0995424040c1003005018401c103e0300751a60081c1e119448460804003403100f502e04640c411100070941042115041c051805088002000e00c200030502008104101d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 87908535 1250 87907285 87907291
    0x103020712090e01090e101515050301031e0f020f031c021e0106180b03070f09051e0c04090b030a0b101a0702060a03090f1b05130b01020c0d06060914 66
    0xf1140300d00d03662070350600300850b14081489181603215002c0032180c141c094224980c800e136101486084581d40f0200911810f04103008900000c00020061007000498079241180070208a12003030110266900d404c0d990203c0f00f4003030701c6000d40c1d80010080e541c080006020b0b10409000c50860801c0300c00020713545070000e14119404103114103d8000311101441240110b0301902404084041c03611803200c010402048190b03010300a20202003900d03a140c004c10002040e292070000390a25004841101190a4000c29480c4144400512680c1554040de481c00d0b68011701c0c0000d0740008074000240382c1103410b10000d28411070f1408020307403095018100c10032141e007250130703038220038040842c00494419004000c0d8401000e020048030148240d104905003489502e414596480c191501c1c003044a20104804604204840620007800d200c40c0581810700454014003608030040d0000c0d454480c855021130040c200343c05200300384540c54000c0380c001d0016910800040392f90300070f01d58101e43d0803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 87909785 1250 87908535 87908549
    0x60d0b01021e032209050411090601090509011502010603020d0b0105090108030903030a0305150a030602190908030405091902030405010501170609100c0215010f0e1003080d0b010302071209 83
    0x45408042c2822041694400706039054015501d8120f12200703600261407800314000202c550900301040d500080e10529000b603004400c4080c440c3e40842c10010340e041c004201c6410031045460420860b01c0b032510144c1504c008200036190f50746503c004900404042d4400303940000302441410030f101000da0114143c1d41c09441910381c2d42e0721a4082c5903248103000005406500400848580030f00c2548129003085c50101403510768001c03040000c0780b03041d9580081d500c2d07950003d0301817180815140c031032815500e80d0070300d01d005929141d915606c900a601c6420701800d050070001ea24040c0300c43d01100c1c00308504604640f0f90030503050150003000d0174050301079001500d1014a240100000700350784a40201801403403c032507070b54203000143c80c180c2c2517141948200440c038036241c8403056070540608040d15408100d1441c1a8030310800700000b41101e052070725189024804075414004540700c0c082004004110201e54500480091180c2c0c5c5014000380c895001840005601c18800411030700c003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 87911035 1250 87909785 87909793
    0x12010b090909120304020906040905030c1c030608070302060304061e1b08040b0a09170a08060f060405010c030c110a03060b180907050f2b060c1803020f0a05060d0b0102 74
    0x20280725a079603c0e410b200641e030f03112061002400515048140741c0d03000c84040c1c00861000019a80c552035034100c86120078041e000b208040d43c2402c10104680c024800e14074051005510f000985503e0f089940000f9010340c60000005d010b1201c2070708030841d40c6d0031300200e12125507139003083c0703000410380c3d80f14190380610340308144200c05100d80c911500943c7c2090071120140c0391440f1038401014041e104861103400c0052041030300d10441c000c0c00c0c51500640310303000d452034541c1c03c018280300c040b012684a40e40074001809540d03409440c005415a03d0b0801841d0884981844012a07880580c140da1254940b84c000c1300300a46600040c0352224243d60400340c4400c00340e603144a001c0704964450081c0d002100802007031510252000381c1d8000500342040c01e02d000b041418100b84410040003003441680e413080100a4244904480c100c0e10380340252a0382d400a22144084c529844003034861440780035000030b03c5d501d0b4901c1074010140104225911400d100c040070103400040302e41400b5020b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 87912285 1250 87911035 87911041
    0x509010b0a08030a0212071e03030f020c0102040302040e0601060906050c0f010c0309020102010f050108030307121803090e01080f030d0506030f2505120c06070f050111070204061d0403030c030212010b0909 90
    0x20031b0310300392210f05e580440398810040c512403003180000d140342d0081c0c0400da00c500308100042050b100401040443c02d001582c2c890441c0107000613103501c60701d2000c445d8000d4004010f040e60080303090b8155449840d00947d42c2c000c5041c4580303001c0300e11040d61465403821001403c825015401205407e100785c009010300d0305d03c0c585840841d89c1c00d20500c0c11a4008200051301c040c07048540d03c56150701d0340c100043d002d902e42c10002d01c169441c04100c0c08a114403009000d141f017540c080034010900e041c01041981e4030a1645900c03802005460381e511a11500070540c17581d01400307013040c40c40c0315404460015440e4071007005c7d190b00411100810441d00c0001044130f04010f54091002ca000c00e0081052202e8541031010650200c4816240140d207101d001c4006031003801041c020812030206d06803110789031700411044900c00c0e4004181000490b00b082c1c0011441b00348580d020703030035043c005451000044294064441c202c0b0084d59489040004175124280350050320702000300307881e206d459079 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 87913535 1250 87912285 87912313
    0xd02012016110a090908030403090b180103201903050a060506180414010602010515010804030c0308100807180b0108060303120603010b090702010507021c120509010b0a08030a02 78
    0x2100d5605007290300c1020741d6140011030b40020880210700307805002e40c10b9070341e61002c92030211101440300f01d0b8009000028001450342c8800f0f800081d060707288005140490043c0076980c00d81002000506064484255138101141c40541c102446000356600790b440304848d0340c100013900f4411000d004030b0b20704030106050103064401c039410342e06c1c0070b0800303403400e140320818409000401d216180e01c1522042d06840d8a4000700ca03540c002e02c00e0ba0004219418070000c0c6c00b9104401960305410400c9642c10440032950106c0b40d07d10a44e05030401d49203079100c1140e200ca40c000150000c0c4120305c5049800a0034002360044034104805103501044100201070045031820010744150703a0503070050010590040d4040129038002200800000b03038902140c020600180d42101c030100941d41d40c03020800303a01d07018020f24441410580210034880b000348400f80941d84c000440109151782d900c002001190258045455a50000c01d95030b1403e59850626540743e2182e00c0380001402850142d000340 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 87914785 1250 87913535 87913537
    0x9150a05100504092a1206020f0403050d05030f010902090a0e0612010c0c03110304141905030106030b0114030a05061902040f03120906090501080705070816150605031b0609120d020120 81
    0x20306e071001c0b0200700d910050380383d000c041e40143d0f503c41e000c500b0402c00000010410044140300103030544400d0f0301d0740740c48007841c2c540b0310f0140d000d0040c0074010408403031556102820b40f0280c621489080c4070743d41390000031030a16030780f090300c1c003401750310b805d058002242d08070100980880c800c3c0e071401040f40314040003e45900543c42071800c00e0900c1c000300c900d00e03e820700c859600740f80b0b1040c48140c541e80d41e10000342520344d140e105a65035040440180240344c5104801029a0000d500404801099684540e40c03000003c0c6074210120040d40c0081150b84944c0442e801810b40b40155140e440e142d08005400710910102c000c04541c2011700001e007240103800007004c03200d0503141c0130001d50710a14280e5255208001c200d940c04020000b40c040ca4041d64508002c4500030713a54140c0000085078010222441e40c0c004910a90021025010100210980c400c00000503503141d621040000c02083c0e500300540356072061801a9030550800660541c0400000c007440e1030100302441c0c4e01c58648480d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 87916035 1250 87914785 87914789
    0x406080309130b0102030c011e18030e060f0904140f091501030b0709080d09180605030303012309162343050609150a05100504092a 58
    0x301c030300c80051a20002c0c403030f070000c1401001030042d00e29001c0301784626030031500e226007107800c0d0104405452032548050312509519003032040703a51400701c2103510050507489034181218030407000080c0304001d054440d4117480320540e0107003007030001030b005401060700c0c0a01103c009401d607110320b000646100c800a0a907021005070500e036485079003951190781580800800704018800c0341140041c803140104804a042806651031848183c10196201c0c0c80144c0d18092000b40e03030524400340020355011044a04480303404080340400f4016282c041003140380ca48a440d88081030308104502c00d0790590005c84400042e81e40c80340445141600440401d0341c18050805101042c0f1990401210142a40380168000d0103011400701041c1c402044070a0816254410314a0025402d0200b2104100d841c1d002440c0f0340180511445403841c600c0392100041c601340c03000e0b4842c000300315400e81c0e00c03648101a15000d48107005052041c00c241070800c0c030020401d0f181040e83e0b0080001030201c0250801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 87917285 1250 87916035 87916039
    0x306090a090b01090e011d1615050a0c021816090509010e011716060c060f1812050f0a030914010506090a0c0e0a031202060a09080f0703020c090a0203060406080309 72
    0x1840b40d007040082c0b801481c40b1038441c0b20303665a0300b1460a0510841840d461f4404400b0001c115004007a000041194119407082c0c0c400c1440d0740c1c25070342031904941511500c00c4a4605902c0b01305450001807400b0200b08030311510140e0120078040500503100c0a8607440e20640c640c5400389950b5014842e01c0e41003441900744010001005000720050080031241101c00041241d0580c861112019460540c1d0751011011401d0b0426aa08008007400744050101007041c041043c1d154400e4080d800000c060401003514203041450300400c4d0168040d686489403072103100352100c4003050058000c10b2a0641500c031540c08139030101c00b40c00d05004e07603032043c9030242104065845081c0400094401000310400340001c03855408c5880d2100c0f02080c0065001d03200d450340b01e4440c0d1301d0103418000b01401140550f410800e217240880e0b803140071216481030011049075502d0f8103003022420001400c40159018440c0030900c100854540c014601940b011201000038641e11200c503966071003203e50241d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 87918535 1250 87917285 87917303
    0x8061c02010f031a030f0f250b0702010203040f0b0307031103090705010509040f020d091b06022a1903020a050102010207030801050d230a050105070f120b0102100609020306090a09 79
    0x14203583e1080d006011144203039107aa265800e5000d0000e401d00e004003419164551200c48182c3c9004410481120b40c44099240009034201c0c0c1c040d07080b5140994092000c405c1400154201164404c10450700105070342e01190101e15155a180c00f12a48159040d4000038109556001c0a001c00b4007141e01030790000c0300900c8010f29180065506403c00300311564881d588454142d4464402c3c0000c04202c54010000902c84041e450400840c05020600d0852003800500611400d500011901c041c10031500701c1060200d280b8040d000400e511640b4150000707078113865030429041e83c00d094000d0304d00c01c564222900c0d1704c42004908031f020f943e00160000351404010401414404000d1054a01805106003005002c00e000600d400310401a12502d82c441503501d0207110083c8101a00328480d4600401e1030f011484d4000c09080000040022841c1d607a40d9559060b030082140c02852030040b2010b0208643d22000c000094004440090040d1030020004034038a8052003490031099103c5120 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 87919785 1250 87918535 87918557
    0x114010806030c030d0c061d07030f0203010b102c010f050c100c080901050c03010b030402012601080d0e03060103020109030b0a0609020409050106110c130b0d0c0608061c0201 77
    0x4403540300e0080c14641d0903000708662040591014440c00040d4a4107484150a6142e0b03480d02e082100e204204a51400003007559000c4802c0b03003c80c000084a410220b691040d004900001740100319416480740e102da042c1d0b010240e2540c00c619005c00351101e0b07008081025514080349160f000003501c5107030025122095000722a8001c070003410314144094202c50304030714030210000803a901341c1e00101c04280c820b020024261000d01820780d006a060219500b154940f1a51080303138000944000c2c14400550409030040c180c0c9581440c0441d1034170220303081c65a40d01480d507201c091246126001845008507641e09080004800e41202c1c0c0c103964828420780340da1500b0011100181c42408040c0e01c581d0001280d42d81400548040c00708032200003065494040040d00400901c120314030a03402080a100c0540d507400d04850404680345404141d840c940030010340c842e4035404004000701e048150205501382d0080400c0c1c420001602c0c0c0c5841040c1b214101c1e4484114080020700040c0400300c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 87921035 1250 87919785 87919787
    0x507030b010e0d030212041e0b0702030c04180510050718050603010608090f0f030d0b01081e070207030609080705010e070b1e0903030a080f061207030b090a0b01030b0403080f011401 80
    0x3c11000c180c002d10581d00c464251080c5030520381d00c103a2142c44460070308005804920347d110f40c8a00140644110700c0d00e000c0e103643c003107a00d0355208c0d801148110703030f504030124000721801003107034402e40d04c0b006071004540006040700c0280410360b06d490005a2007142000c09031540c00500b002d40d0f2004080c1070460f844c00c80115014100280740d9074060045510741c2c02c0a10b020000310240510400103580c503038003051842e5007119400c0030201e04100c3c048080c80480310b11070442c04d034103403070403081c01100d9564446e05a00c2c0011030ba0000f844986065801c02c1030001c1d510141c401244108028056020041e8140b6a9148a80034416088504020542c01c91440039032801d042c0446124641c01c3c4150100000d0035a0000341c400340104486c40b0030400c0000c0140c035001d40c09601103c41f0400721170f860300885e64810315400000c140500050100340700600c200b000c802071990000850a0940e16880c2c80400000c0998044011500d41404941c00a10101416041e19800c2140c20109500f01d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 87922285 1250 87921035 87921049
    0x13090b0301020408160503100c0c02010c030908070905060a060305010e0f09070e0c0c07240503040606050a120c06050a171b0a03022205090f0a1103040c03060507030b010e 75
    0x14859041d0741c00c0100080701031042c0036107849400c0074003c02d03140c6403400044c181054240004038034480d103810442c8440d075800c07810008240f902840c107004509114a0140ea4808130b41d0040038a0348070341e50001400c030419802207803040d0030a0303031010baa0729902d64042d02903510030b010b5040c00a0060000901e00b580c0000c0e040d51092280c000c5a401d40d80d00c90316100c00706026101c801d2000800a864241c0460800501004007407821014150301308115021078090242c3c8860020000c0000106003440000d4003c580038010040c100c2c4240390381c03900801d51141c00700310102c80800c1c3d2288001016405282914440201e603115003e07009010910000380e10380083c05404000b101c600d440448022150140c0400341c02914016907842d42c140498500c10345441c0c1b00003044c0c100c91024091a180c0301003036908401e0000fa0300c0408c4e200d140c642006000031045220075000040200001d00480f040b8200481c0d00a5000300840d85801000710103958500741641c2c04500d6845030001ca50130200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 87923535 1250 87922285 87922301
    0xf0c01020d080c0706090b09011508030d09060b0306090f0712020a050d020301090506090c01020c03060408041e090e0d030f2016051902011b030906051606020c100b04021309 76
    0x1803e0f14000b8240c1c2c0d518129035012000b91202e942050401c20220381c24451101800c2e42c0c0302200a00f285080c0c1c0c2c4a9070303886828469810300352642c0c02001001701a42000127000c3c5c004003600c10600e8108803040e1ba950112040e8982c511420400241144515041e1040550040c1c401e0f10142e08100030b10540003902c0070101c0c5c26642e11080040495000c0c40301d64002c80d03c5802512289000074002032524480e202c21310b10940101c024000000c88400446080303d105038030101c919032076202040380c4082d5a90298002c42d0400d032545d02c05c0c43e0007045103c07009405803400c21101c0d00040b08002180c800326041164a030f110030804a503080284090402403980c400c031490011281e590307080c1017400c9266045c14826520b41442c04640c0c100054072060300b00d03110680340071801c40c0c81c018003000380381c40713914180400046d1902e04070500030701b541900f07500880700790340d1049021200340d0350b0f000402140158a240454494540c5018021901202481003d04040b60305001030f120043c4518 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 87924785 1250 87923535 87923551
    0x702060a090314070309030c0b04081513020a0915060309030c0f050106050a180e010c0903031d0d050313140604050609060405030f0d0e0a1211040e0610080f0c01020d08 74
    0x710b149043d50400304001441c40f144603a407100601461890122120030381d6802c82d0040c8901400b080c40740c0000058040c80000ca240170040c0f0715181c50b452040303040e400310006034024203041c401080301e00da06d1b0403038031681185010381d280e000e6440310b00b10101c0c0c50b43d1000900050b401c1da00100421202d16403464010702580000071500c1d920300000b02c4040542d0700510b01e1880031441c1078001100e610a103036203d11894001e00480d00c5850001300103442c3c40c0001014407010401c2d009004480b10740201c090b0382d000d03100408949035400d0566407604250450348440190f140e003c900700341c50300440e41c403054015103810b0506080c14100180d58004080703071600028140000196a54100310948010724031501070000340000c660010018404030275641e014508840c010000e0042c5507101e9034506411480d0b10603070450480005025240440108045110701014040400b4110820071704a8034104100c1e041000710100c1d654980d446901d965001d80c0002c0d00b0805000e01400d4001c0e817110310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 87926035 1250 87924785 87924797
    0x40c08040201030f140106030b030f010606080606130317121b1b030c0d050c060f150402030c070b01081c03050c040509060a1503090303050c03040f110105070f0803060411030702060a0903 82
    0xe170890107880d80b026070011000984401040e840f0742014001500300c0e0003203000030b0200324101000a4400280a0480e501070070740000c0c0d01071802c20348420381000e19441214580d00c0e41d648110303006a60400c0c3c2c4064500b10a0001003410070081c0110100845102002e190402c810183c4100c07464140500d071411314001084600b400480c184408520003810f034541701e07115540d0903203c0b0302c0c01c0300c0280998202400c07107003401200c0340001ca00c0c200d203c0c4200c0d00940c0e41c0d51003e54031186070140500c000c1c44030344150008030302d645000c00c1014606010718000c40c400400a4000c4040c1c6005942101d0904020031084c0050f042c290b0700c0540c40600a00747c845115642e004211020034a030700c0c01c20008c0c0d981d1003407004055050152640101640300094150700f860307100c00c0e0810140c44c00080811407605130514969000f04107580b140c80d04015008041c2d407050810038080c0e481212807034416460100c20441c5e00f2001000d60f401004254000c0810f42c0d9050311540040c00d00f100c0a03414003038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 87927285 1250 87926035 87926051
    0x3030e12070c030b01050607030518060409051005120d1b08040b040b12010b0c0c0d150213030506060301061203050901021006260106120f020a0503070303021506040c08040201030f 79
    0x40300008100381c510600112042914608041c4003200703044c0c0160b44038800400160f00440d900409540c050203003070800c0100180780c030340010b149109590200050504000c02c007e0540d40d071024000131104140c0c9c3e0b0500b03070a5015a00303904c0d47c011121110204491503c406840325003030042800340751060803401e243c0f903240d41402030950400c4c0e104102c1c60100281e2020314401c0d640783d0f6401404000402d83c18074804801e541d8440003c10720550007004500451400c0c01040c44000d4840304010500b1981c0c0c00180c03e002004019900081e501d80c402c4401040f1035060510440049902c040300740f8404460710751701121264802c9071910704500c078018528004031a0b91103a80000c101190f600c4817000780d490024119928081c01c0ba03803c591400004000c039602c089441110641d1008146800b8440d0388001032054800f5000030f03806214804002c010180c0010340348149a008640001c0150341d064100400c2d521414100c0000401c3c484c0440c0055000c0c0d04000c6000d1502d00700070030114 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 87928535 1250 87927285 87927313
    0xa0b0306060d05090706021501031211011d0307062007120203070b100315060311060c01091406071b0f031b0f0b10060905100507020a090203010308130602011803030e 73
    0x2d0f010788400c004c58021003000c12800f42c041000d18000d04402d500070f1750540c51515840c503254654041d040a10181c813602d1003a0503020340c0f1501e141070b240900202e0031030200f50f1301940c0350440c05c02118828038000101c00c160030090080381c80500a002581c0c0741c03145640c0c40c0c140e800440094003082d44070034015100024a203000035031043c01e208110100003803550030000f40d44000310220b11185890003605101044c1c2d00e05002c4e107094429100c103a9144c0040c031002d80109001c1c1c002802d2490341e80c07030444c844103001c200a8011b00440d96805d141e004145221242c00442200040031002405404000a0b00035407000042680082801006410940705c0e01d9000c0c0780910125207000c0180208020400515810303409031000e03143c8040003604100110720802d022460038001d201e40400c2400840d580d1014801c09030000340425901ca5a4034504004503400c0304136042c00000605001280c914414030518802640c01383c240e1040225a031000d50042c85034a0390388901c3d0081d841080051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 87929785 1250 87928535 87928541
    0x102100504060b011b03090509060609040e01020c06280c050c01020307030b010219031b060912030f0b04020f030a0908161a01080106030309030b0703060f09020903010b030105060a0b0306060d 84
    0x141c1c0a140d001c54414110343c0014001c21240300d440d100c03080d40c86000d0000c130b54044c640f0b105641c03042d182081039407103d0001420354080c4031400350f40300e42841d40302002150103402603d40e0300152011101240c690208241c6e5500c070b8210102e4079a030383d44400700c038569010f4014200718081802c0082c54080d01155160990f40308596840229440d69001211541e0400010011522103150029424032035a401815101c044520060003001000081c0a01440744e000950a40d070044860f1242902d100010f806020040c9481905501d00502600e0701d003824022580301007091000b071803459a80645400060484641c00d5403205d01c181b1802d119660781c000112202030048036101032081600e02100800380058101501c26418840f0800000360404051029658800d407050960f13500c0007000c80c0102110307401a80c2002c0031200000b060f03510ba500405580c00e00b50024001801504145404d88005a8089420000030f901c204512080b0360040d5130010b0300208080d14000f5000c1441d0300b6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 87931035 1250 87929785 87929791
    0x300406020d0806090105030a150209030f070825120606050301180c080a08070320150a0510051c0302030f03040b180d12020304031e020d0906080112020d0201021005 72
    0x903900901d03440e81c680e0b420800300c030707800901200d001000c2c0d810000469100c1e10050700041820f48101c1070007080d1000c580543e2481c100103001c440407585050076103562485030f803040c4050790107802000c1448140b150720740315020800b1100c40d49c103d80b030f0828990424172018019a0199602e0001052954081c0144250308800803201d0120038414105030f40c46070801d43c8000040c1d030004041800003400d0302d044e10452901410150103404c00c5080c0c940d010003015903001003502840c800c804051006803885409014000c408101c25640c00d96420702410560203000c0d80560b220045071000f85260040d803401e94800c0c4152410404031407400c42080d0015982103481009110401400c4224420a188641d6006004080b0850000809800340c184160300c1c0c41c1a0350004005410300d4016407014011600b00017664071054072101000b511000002500300000c3c07048000007405d00e22a4004074141c50304d15000c506d01092603400c0020f074103410441281540200707401e0f41e424040a22800344 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 87932285 1250 87931035 87931037
    0x4110d0b0f06040c0302040e1f0305010507030501031a060a0506033102120607141602060705060a05010609050109052103030c0703030c030c0e040506030f0109080d0b060408300406 79
    0x10794100301c2e04101c15103002016100030540305020400806914015494000c95803000d401050344688448180404a0b41c102078074541c01d2000707101003240e0560115041740c3c0644580580c0c5c402c03030304485007110000d8520700e92001c03c4500c18407a40c80c04100a51700300b5500070019a24400480c45c00d004118080c1c0d0320b400c10a0200340d00429401c01d80046040202010041c000c985000c4101520340c400b100070200001102041806500c002c00100d00d0101d03800411031a26480186040350b50b44c2c10480f1035210650528000280d068013540c0f440742602c1050f154500f440381001c062000c510201022224001540110014440c20500085004d0188030b00036554076803d504000e000d441d1003c41e90303020146003100c03079800d855103d8660790351401c007102d002c15140c489a0000380741012051004415500c0c041d220b600b08030142c40100b8450080d4001440f542d054103003004464051481034161a801c0003c468030010f24107103c82288038005504e08000d182e18040814040c5c102d42c200c0d00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 87933535 1250 87932285 87932311
    0x6040e06041109121e0a03050f031005040509030306011d010e010c020d021c0308070f0504210b0c0909061503040209040c030804121b03080d0906020708030a0617120304110d0b 77
    0x142070b12400c5445a540098110020030039111b43ea0350080c65440380d1904405401004004148070042c400d06030300040800500901150414154964a0783d02c1a00c40f01e0100307001c0c00080107080f01034442c140a030700c016141c0c203071600d4841c030040d1009001900201c0e48592030800610050342c8401502c540c440c00700810202c4000145406448080d000d40150280030440321036138a01036001c0d04890954803140c0e40038190400c01416501040c4c0500c0e4002c003ca144c0300c080003103000c0060050301142c0c10840302d0502c0b54071100e0034024070600300128040c00301c10410004000d030901c3e2250640207845641400890703030f541d0711038407080c0e08160003284e0040d5901c1e62641c00c0c03104045142c0300c100d0801e40c128204078a1035680802c0c503c968462034880355141c22108050080c240d0680707241541150401d5a00d15008280304010a40f60142d00c4901c174040400014240700080c1c0c0c0c4c0d601d0a2449901459078880d5252045403412040308194403c03e000c0c60310001580d4451194003c5601171441 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 87934785 1250 87933535 87933553
    0x203060102120412110402070b16020d0305090607080c040e0a09020f10091502070503030721051806031012030903031b0f0b070c0c0e0105030c06040e0604110912 71
    0x9003826214803010b81a02c80500090216007800905213211030b50044181c0d6129202a011030068080c0b4400a40103041c00b0341008100200c0c8034200c01182040d900780c2c3d5051900100540c215807007a24540e006500c85c0d00015981c0d030058801d290001e140710500c41c241644c4598100760100d0850b420065991a40d1602c011403c02628001380540f049810000f2141c85810003048405e0500c02c080c01c9021161031914040d00921a14026210160a03079550f4032082c1807076120700510a408007600360240b4114401c139071180c010742d01c0503080c00011000d0426410704001c1c00fa04040c1142d08001071050001400c040000080700074684a03446450f1058030b14200a0407120001400324040c6400c401100e001843c1030320185241c44d0320550500054491a208071100c43e074500001784000054000403070900c40c0030311564100c0e0401c40032685031885000501c25640924403071120020f01d2038010400b80e20f8590000c0c51403510781c000c00c900f007410302c0740014008010705606081d290400815 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 87936035 1250 87934785 87934787
    0x2040504050f01080a110a05030706021c0203160f170301030312060501110c04020c0111030108160f1401050d0b1905011205071b1a07050c0606040e1c090801090602030601 75
    0xc0a5028415a000948940c1340c00001c585a8400602c0200600c0f42008441440d039a00d050b12805400d0103000c0718004c0c0c1d00c1d11400ba540c4e1160880c43d400320b10903a1030f544d96040c400000c54000e0000d28100b450290155560f800322540d00b02000c5480d02100101149901e10001c041d60095002c1d40c0e800111440320f030607000c04c403001c5400460400c00010380d100c80d5a000000d98400c03550060304c0042eaa00071a0f18001e0040c850380340821b80b0300f14000000100d50400140381821104c10300d80000ba5030b83d0712003400e040405c251080340700f02c80c01035100c41a43c0d800348010f4008041120000314400901c200015a810840b138030301c208824846000b4011964003044040c130340c00c00e443c8108411300300301c280035101b00d1102d4114521002045005d0042010003140041d00c0c091000d0184c84c40e0504a10281180d0451001c1c0007242c45aa00040c0d003d1405008513918140c030030001c2c050640c0c081a20304031045440220b00700744402030704005502c0f1024494401c14a00a1600507124107140740 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 87937285 1250 87936035 87936041
    0x3010617010501080606090d0203032206020a12030c050d0c020706030c02010212010e1314150606090a060f03020705070e01060207120b0601121b020105040510020705030f03090c0d0602040504 84
    0x280140c85105000103100c541d030020b6007550411811165262034103d0200080c0103154100303002034042c000810a040c12400a02041d490242414054010140c44d26030803a602c0e0010760b8050490643d040d0003600c1d19009a0129550245614005160132558141c040a4854801e280f1006920141c0100103c2c0d6140c865811203095502c02580b4208982c241d00030010410f008a12510603a000030807030305050400d540780c449912802d40c8580315900300c1c400e40c032015141c0c1010f0032103d003c07000406928103002100d9045030b0052140c0a00703070070710a08440102e100d41401050590030011b400109a0402c0004002d020103d4000525810507000071f0407c5415481800c000b49644d4070f210000c0c21964070b44c1d034425030a18103211000311616180001c1d100c002000000800300c0c1c10b040411a6064015078480d0307026500326044a141c00704020100c0c42031500103002c50300140104005012541c00464001561034202d900030582e450000d250b61f84035040c11a911607001604100a040c81c3c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 87938535 1250 87937285 87937307
    0xe1507030e0c03060a0b0109032a09060b07030c060608070915060f021207020609130906050f070c0212031e04060e030703110409060f0e0a0501110304021804031112030106 75
    0x4800380c07070104142c401095503520041d06030240c0c5911403903400000d03407180020400658020700d207003a403100d820483e514010728010080b1280080b801e03010403c003010303008400464440d4660103143c10b00f01d880403641c9089100c0121411501c806002800420811010300a495401d00c005040901000d03999070640c1e546d4000000e0155500e00da026094000c02e10100a0080400d503036600c940e148000b0f0003901c2112041c680c80300030740d40bc02001031501d501c40c000c0c40c0c0c40b82c0070811043c0c8502401c40a4000304842880026100e10032030720050501708004030021800408072414010300703040303e22030f205d41c01c04601800b5002180c00c00841383d201e01051940f000030b0380070f8818203003191208416401e0551146001d5522580c1c0201040220740c04440c503000b1041c003c1040c1030b58a086513440c0d110800b03080d02c0560825000e0107804045108032805140e0040c101d0902c034104c54100e000105004001354144124441d8038203003480107000000c5605201038603541d9039030410a0150000c4410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 87939785 1250 87938535 87938561
    0x90b040b0a06020d05030709080616030c02070f150908060702030901090f0b040b16050a0303020d0606091d04030c080406020604140f12090a0909080343030e150703 72
    0x200c10400c0940214080c2c040d004c8a292456481e0381b01d8509071000328043d8021141440b6540803c050781305484540481010300d541d051040f4076459100301c1c0d44110301d0154a600b0405c103002004111011034030310400c1d51041c20940c0440c1d5481481078201001142c0c40c5026070000191500f6a603802110380340038110f0148c58246243c10f181c9030418a0083d4081c03500000780004616550b000030700c106480c4c80d0740c004101c800780f40785890020044c0d002282d81c11003607400d212011a86c14007920a481c103607140b0252480c1c200c0b5442006020301c00307000e40151f00b40706920351568041054a0024005482c5a400410050400c0d1405156651910400302003541100d8040f11100070081092004802407182d130b65110b00440b0001002e41c40030354803501041e403401c4d01c00800c0001046c003841c402c2c119404081c000540e9071072100300000302d50407800c02c944c00b4441580c7c0a12014103040e2005465031800080078451001030516000740b1a5401840d00501c10811003250381c1800b6040703c0b1114 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 87941035 1250 87939785 87939799
    0xe0106050109030b0f040204090506090d08060f1c06090804030b09060601030221090f01141501030915090606090f0f0c02030a0e06091807090815011206021b0106090b040b 75
    0xc0c54070307070613020540a0101d109441c240008582559181d4020408490300007050b90b8041c00e04100299607440c10340d2059011421250008140d840c0c200c030488240c00e0083c00d403401d00c151300c4021080c010041340d0f0465103e5511400c80c03005c141c0c00d20141024610584091585041842c0410303d0503800816250415004001c694003001c101a580c6010808043c102402e9441d0308240c681461420007a904456207030803203105003069001f40d201e004007034003d404150802034034011030036500142000303070481040c0c290201308004a5800448290300418000504c0e584400241090b61040840c4002c00c940710040f611070240c46124103102040300d400211304d840c00e0b550020344101070105880f032244001048203005621842000394211401d40742540c0603140049006d0180710300d50042008603c100e000c0e000506050400c894180c03802e40300a800c2e90200c82c2d8500002c0c2d88100b00c90203400d99800c0840c0b00c444000d0060001400b4400d00102e594404d12061008031507150f05d240c5d1103002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 87942285 1250 87941035 87941039
    0x2003160c06030e1b10030605040c050706060b0702090708070c05010f1b11060c16060204032a0f090902042a030f0209060301060c031107122a05040f0e0a060e0106050109 74
    0x1c0c040704091201025101c5114017030313170101706500030591544100d8015041c0b20030740120591040c01080c1c400d206100402009441e41c4440350507004041009400c50001381c0880e01480c000c075070156000030145820510480181e40313481c03c0d6091140a90383c01502d0704011400f1a411490310024030300740749001320708448803000040c0d4604002c1c03d0480c034900c00080090320f00c543c0c4401c911415402c1b4200703540e103e9072450900c4034014954610a8411407040000540d0903007124480708952000c0801d40300f09040503c1000140000300c0201d80c403503a5000050f200c0204581040c04c0c0308080202d130060262051000341c26104000c0460012520400c200e280aa89420640b81510260b1602550200062906480507820000401c86a12403018005804040310380300c003420502c90a003004c280c001c500c50420107506a103080010882c0c08036801e21480c00c06ea0310001e80c2003001d403008145007204210480c01d210f49070b242500c41c03c0d02d40e40c002c1c402c034009003d4070004003000e1800028040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 87943535 1250 87942285 87942313
    0x3030e010e0a0302060f04050904080301090c080f07030b13091109010b04080a12110601080a060f0504030c02090601140a050c070605040501090e0912030c0a17072003160c06030e 78
    0x1005800f00920822020600040709070380034055501910b00034001715000c0c1082c0c14030710102e40091147c000454103040860318079502c50506140a030005010b207000585682c3c00642c00381200c0008290001010011407480303001d10300401d45454014020132030750712200c0040c0102403030142c1002e2182141007008208032500004c2000d129504402400100341c3c8190701250706684091100d00644540400403403c0800450300c2031340035100f80010000660040003820a0385e104680180101c0c220403409009414092451940124145052201e06a007100e4648280e0091a840f10024202048a00104d401040400050505801d207181012302d00000203104d00f03c9805100c1c004c29030500841c076440700410804044514a40c2c0e665260725001c1e07803240c0c00c0d4001e011101c0c00a182c000c800c0700451540c10404d0b0040980d0750300e4401065800001c0003011030f07262803281c400d00c0200000c60020f00010018542c0c9442150411082450060020141e5103650704400d03841d048103440340419 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 87944785 1250 87943535 87943549
    0x70e061603050c07050d03050c010522060209010212030a0c110106150c0501020405041407121b0c110a08030309060703110702151204030905030d0512040809030a050706020703030e010e 81
    0xc691600d44199107402d03490707401d42002580d80c0300c243c00520022103041010303005000740028401d094000c01a5599100b01000060108a8040184a140d1001601103502500200300c40c4e201030048172519980240d03410070b0b5a00444480c940b46a0368500400440d034401ca00b0b8601c3c1264100a220042c1040e851001c074060204101c020301c90580061000c00100390155030045c1030092040101559401880c100800f08035285400a000000300c0c3d1b680e80711a12800f81c204c3d241c8103ca5104005c3e038402911501c441c03410580311032468204850440d40d481c1401300140401d00c0207941c5030704103154a2454410701426120616042180841985007110103407018142c0481d40b03c080340940b10043c80241c0f03ea460040b100c40c1407582008141904071164a00300c0d80194203d510f9086060030480d014080c811800100e8009980801c004c05c00302c40150403421001000d44034078044541e034551416999500603000f50700580b10801c141030b0031110950a222080c01e040300482c0d009000141c103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 87946035 1250 87944785 87944827
    0xc01030b0105030610080415020403081201120c0303030b010c0206031806090d0e0d02010909050a0504051908030a0207020609030a030e030c042f040b0706060509011508010e15040203040803070e06 86
    0x41160000010382070200140c2c40c41100c43c3c8e060400c558540c1c0702d0404003410783c04034024551b1222000d0001403840308941568030941e40040181c0802d07400c0d82c0c0d00310054030002c2d140c24104100c0c6501000583d0384e0348025401040e8100181c840a1015411141400da00525000fa20b800c40801c040711190070600c1003104130f10449001481010520058954110320b4020004851500d0100400340b1a2944014003650043d0304486119050046c049040ca2000000400380001030001c69429041a0054007110f480202154103088100303000c42d2400c614244244c0000701f0b001c48020b0070341001d024114a9070020360f0280301060201032081602c1c400041c0041e03402051081444d01502208180c0303002d07180100c0c8007580d807129414600050030840c0a800e01c03130b03c020000003462264032142920a01103a803541c1042c0d80c60542c0a03000888010014940f00364074a0201303985a550f880110b100e40c1c0300d100015100d08008000610782c00703101484d00d000742000c00100003401e003202c1c070900c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 87947285 1250 87946035 87946037
    0x303070e010228020a05090714030a090503070f060501050405040206040b072111011b0c030c030c231005010e150f131d010912050c0115080c01030b0105030610 70
    0x1040c140c400403880c00e83d41c5801c081c5204a00f42d011040c45807880d0b14180740074000c0754410481a04c4070104050058151442c01c04610010501d1a00310340d42c130083c40d880030002e140064151182d0b01c446d42103a014402c2207800100007030303400040001030700c00c240c050402a981000241341c1680410003070b01c03807401050720003c4046541c108009052100114410703544021281c20111004080c0c61101c002c0220700c100e5080c241d000c40460b00a10031000c40d00400e69500211000503101680c10601c520030a600308441c1490000c08545500190910307850681e04900307101801c02c10305c07400d00c1480302400b004642014010040561004039031a0000c034102184090f07510103100140d28031a10610f210b0f041001c8140c210010322550740118883c0c1c04002e071441268840f100d5550895104882c01400d140c80360081e00d540c144500b01501c8c00340206000002c1c8136100c41c0780c02c440c20000e54040d01c0654482803036170030703e540c2c140103120011a080c01c281b42181003031400202800c03400a0840 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 87948535 1250 87947285 87947297
    0x1110406050304060b0301060905310807030513060e181308030a0b0a030510150315110912010b12161a09090a06030308070f0824040c031517030307 65
    0x340134005103603c02c082600e4014000c0140c9035560095102070882241e034203d071000030640c40540d1840500402049100803141c80759410055501c0c0c441d2500400000e0741040340078482c0441e0071240c0c2d20000d01610301074031004540ba80d044104032507000c21211194184950500380114460100e684140042d0312000c00d40d101d548104200c40240a5955590340c800000b040010a101010400c0c3d2042d400c203580034011000080c203080d11071180d41c40002c1a44403aa203900264400c40e51016810f458200380f0039282c40c00e980c1c0000c00c8079201f07040d0820700380d55980942c01c007440d2141142400c1d00201014144554112041c0140c5511501c1039801c411510120f2100301e001140441d410403200426410741c90624116180041c030080c003085010807410800308000c507000d102400c20746d841c0c03039958914642c0c0d221605102d410380c1c4100c110741084894585400340e9168083c041d88100c4a40e000100051103800c0c0c28440401540b00f410810701d1401e00c484400d10200c2102c0c4e2001c0750341811 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 87949641 1106 87948535 87948541
    0x15090804091b0f08040606030609050303180607090303030e15070801080607020102250f1403070b060901050303070210020a06060f03030807170117071805011502011104060503 77
    0x20102e804980c00c0440141308409082d8418482c410120b540c80c0d6a03511a0b0645499030b0b411907690708044208201d4008880c00303000380d04c40d5a1300915040c148601c0141480c6c00c940030150400d6101c3c950350b85034000c00c00180c10101000c050168840c5450b010082040200b07001e00c1c0c00d28050301d004110901c0c030500a9844c17212007100710b42e0740300b45129202e251030001240200d030410660307401c00c0082040d01101c030710701c1e03240300d0041c5070350706541c4c5003100301883c00800d80d51003489588018031141e180001580c0b4130b568143c4003c003040f080008181e03c0d0200382403009114904181010940e030710105580011a031280d1120982c58540000543d00b848a03001002295601040104074a0460750060a2a000440c040c1c850050310b400300c0602c52084040301081e019161401040120850100042c0241091000700aa03240084544000d44500e118503c03c1140c04008 = true := by decide +kernel

theorem cover : BRFrame.Cov 87769785 87949641 := by
  have h0 := BRFrame.cov_init 87769785
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87769785 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 87769785 ≤ n) (h2 : n < 87949641) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
