-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1184
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:39:07.024595+00:00
-- url     : https://prove2.me/submissions/280c4101-cb24-4b06-9bd7-bf53b3f88aa2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 212769784 ≤ n < 212949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 212771034 1250 212769784 212769797
    0xf030509060c150708060406030507090b040e030d021809090d0c0c1d0105030708010b0306011202030a121e03020316050c0a0c06090623040b090102010f020f0a020f030702100807 78
    0x1c00c2c0850f282614a4078607841c02c1c6900e00a20009540c048030646d04041c04071401d000e8942180c9403a502c601140c811164860f6a84041d070000d40c032580c000c0b0402080b40c00030390303480c1e001d13041102c030103540800800349540c81c00740700550442c6003415085000d241e02078010030203e60304c0d22041d0f40c100b000350340c04c1c2c40121042c100060002112408034100c8003c61a0701c01495241006052034200ca9805c90041641450100031450b100001d11a044a001d4240c07018800410700110f82424140311020304181c035420500e0510507005028034542c0090000811b030007102d0884201c0c1203000640740001424074042d01c80300107501c2440074103840034200782076503400718866484105d141d0f9154007410224451140c00c0080c20303007003400c5d007150f0000c8562500c40803480306030101c45c0b07101d54001c5042c4441c0104810041d80d01c03d5014462028451008660f00c8009100707081d01c50b004804840014480c040f85580c892002005455603180c0c05030038001d90b4425940c0680b444007004015a00700101c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 212772284 1250 212771034 212771047
    0x30b0d050d020705010e04090f0209180303070816030b010918150e0f01090e070608090f2d0c4203010f0510081f0308040f090c08040f03050906 63
    0x14280a008145030890b001000194501303000501032600c40c0c200148101d1800c1041070202e0300820311042419411561181e0030b540b1012008030307038141c14140d10702d20b00c0048108180260042405402026009a42c0c4010a504803084080c0d40b03040e008507000500ca5030702003040c0050031861100802401c0c0c2c000c212103202440100040394958030400f0248407004c240a03512100400841c09011841e01c144514801c0c090f4050761040c03240700d42c0041099280c0000d01c840340c2404a180e01800d058203072030110200d6038010411038210380b849012a0860340c0858140100094020001c80010701044e1a05020700e0210503888603103034200c64031030729451070b00040620244503100b2081c240d00b030268603541040340780419240390b40c02540c028516100c003501c480e9001100c040e03005041c103094001d0990024082c81c01182c580d440205001008030300441d54800407440e2006407a010b000401038800c07090f00484000c201958050210f04141c182c7d400464882c4004001c05500035104515010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 212773534 1250 212772284 212772293
    0x2030615070606050108010b07050c010e040605094f030e06040303030501091512110102071205070801180c06050a0203160807030f080c2b0203180609030703050a030b0d 74
    0x740591411114140d8904041c0180d6070000007440c058031910a8140c1400217030350310303c0e565901103d4040c3c148802444409859030307940c0c001001800b000ba0046405042c404824a00f41d04d0202610302c2032240340c0c0504015645a900c4111584599400f00c8000110030071014600350b1484019020080080c0c5a184d5548400000704000c51090754001010740c0340607000d208031160f801c4003800c0c03801c0041041190405041e444a000ca0b081010300400c0e00b0340d8030051749042411b920403c80c09030f05082080610001107104021918181e00030702c40c085207003114003070800524030010818041c44005005651180d405041c6201d11801102e28219148a40b40b581146000c42291031820003d8941c0400d03620044031110002c1d00e080c940c04500b008500c03402640680014500101400707000407005000c0342040751146407009034115a00d06001c03a4203880080d09005514861240001280004600004681c103003600350341c0b25414101c040c0303012000303003601e010b0321680682540039140105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 212774784 1250 212773534 212773537
    0x4121d240c030a030b030c06090f0307180b0a0e07050403080703170a0c0219020a1a0f0c0706020f03070f080c4312030c0f0f030804020109050603160302030615 70
    0x1241c0308021610780e03d40c144001c0980b00300e50901406500200e2403960303640c82d01300903186413100440b20404d5072041c0c9000b00e881d010480e8080313400c0c10008070002c44454110b82c009050701d10103458400d04191102e901c0301c2500d10030380eaa00e00241c0c04100c100041403400e000341026600c249000c2c044c41e07118491070004040299500482a541c070081801c0b0b841d0108421100200844040141111140c0005104031201d100307510b81900111000324941c84c5500c21a40948044c030b4070151110710844000d5551301e000e008541c003502c140d0820b03131217062001040c2d84c0426400400401329412903901c08405411980d41c00d81203104060f89400c07800c0262107007a0401441100081640362030600104450b0762407151803a01c41191002401585101801410040d4043c201804d011175280784c460250752a400002c1c0c0300070b040c00885001c044e4094aa140034900036619640300c03584440070042d0318481920640d4484074a102860038090094018590040000740b41074030b80c206850301d40701035 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 212776034 1250 212774784 212774797
    0x303150613030b060a1d040201050c1f0501080609071206091703070206160e150a05040e0f0109200720150c1006060c08160c090504121d24 61
    0x3080c403c004001312820b01009000c01403055180e518005100b0000041c0046406080a8100800003920601410082061790000c090541c140b001902a8a1500004060a0003000c40754021000440d4006000089600588aa802004a84541a5403654000c114050048407140d16904440d96035030f0304007020314071400c0142c002c2c2c034203032409402d0317040480c41d404040d0061045100342015692125080d400c800750a110038982d54449484058840d070103035074040d50381d92184508015900354407441050407910100c10030b014840c1145210240644a040c10044a0105001c1000402e0818010701c48500c000211101c00303640000218100d007000c5d4217080348a4000050390000c1e000200558049d80340341100812443d2f0508600801031610000c001d0000c41c008035501400d090b054044070543d0350301c4024988907554668103003004d88812602524504524100517440030f0003071010340103400c0e600c10880a8440c1400401c1080302940c8885072850090075210394242c203840005086 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 212777284 1250 212776034 212776043
    0xb0f0a08011b0f0c020108040606080102030c0705010509011e020901030b060c07080c030a02150a030209031504030810151b0c06020601032f010309081201030c140d05030315061303 79
    0x242640c00e26072081c581d044a0242d5010401c120b858071903465405005001940d6091030608505e07203d42c02e2040c0a081d0076084144c140d44004244a908900e8000420655101e440244680d58514180c03c0c01c85000150500c100c480b0055800d50300600b0703034010a5508414100003401204100216023503800023980c40702c042d440210140308105080000252820307044006054080865012601c89505140200c00d441c501040c1c4200d00742c0030380c045e64000f02c000790031280784690349a111181c1190649080c0c010500d200040782600b140c000101e0103882c03040000c2c0b0140e03c0740e4070381140c5074180700708c681140e4410440d0101c0018103a01c4503074001d0800c1c1c1e0040c0304550550901040c00d407019075442c0854241c1281041c00140e400801c484295170900740022100100c6c10045d03070511461721150045561503002000304489040f200081c0c0b180c0400b4102c81310041c0061003100c03020048090301550007440020200c958114448000803000fa1009041c42c0e1002d80c0e90030504c600f5041181d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 212778534 1250 212777284 212777291
    0x516150e060408090a0b0f0a050304050a1202070905060916050307120612060e0f0a0f0c0b0c010501060906050c07030b0c04081c0305070503132a09020408010f15090b0f0a0801 77
    0x88107480c05d0185032000d40f4200c0415450400d0280f4403601c640b08004902d41402804400501485001c3c020120000d4010040d245001c5640000a40310b004030b008510305e851a180201d0386500703141c0c80003480ba540011610504880c43d01d4255640d803c0200001c003007242c0c003503d0010511041c0a0080104958003148104030890b2030b01d2011340d44140c0303014489500c6584021404c040003e8207a2001d07400c030801071000452400c0180b0390265980220150200000350609107500550000303040324010355034800080c0c1c541504840c60f01c111502031095501c401c1c024004103e03003864903030f00020800d0041c0e140623540c942d1a420484002e0118141707118182c0f280729080d801d07000c3c2d103a01a6032450200c3c6036141501100884d079504210103030020400051442600074207691107140c03944042d6121080503a95145c2034040c1d8080e0198400e01d5013000214140d07043c550050b100d80c44214940c6a2040d814a05684001d00902c180769510030f0b03403040101000c0d00d8842c001c1014013902e50010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 212779784 1250 212778534 212778547
    0x2011d10031a06030408070b040f0210020c04061a0a0e0d0615031a040c12030c0501020c01150504051b030702010204090204030b18060c03061e03070b0310060516150e060408 76
    0x2c5a80821100c10b0144204104002c002010709048031a0541c3c8041c0302d2000b6141c40c20b1150190400c054025000405100703000d1605400241c41030510108640c14001039446450411f4654034070603484844000c1400a094082c0c050b01d80e01640342c0c00508902e2403260240c40d02820f440c4a03240d2403038441000c90060041c401c1c9101c8940f00c14580042103c3c44d81030994400c0c1c0c201560b40310729241e0718210b03807030003081601c190602000203402c07000a6440e1419114030500806100440c2200c903116900c001486082601500c1d04c9150440c0c95a03001c84c5207010074a007a0341c0020802011550b007044086561115071001d00f0145010744030200c0c091409550042c40704401c101025120360114040284001b426400c8030340c004001e0f280e550401ca013110ba4840300d18031540c0c4a0794140241d2034045401031510000d10702c02e100d94126807502668412040d88c8511031b08a01a510400c46c000c14000720301d20748c81d41c02101e0000540010184021402d00e42022820f8504031040000020030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 212781034 1250 212779784 212779811
    0x13062a081510030506030a1406100812030109050402010203040e040305252109050604080114060a080703110d050d090f05060901080a111b010504020907030c0c02011d1003 75
    0x3181d480292103503900300c0905840002001c03102459041410551210005141620244210a40f00358040120003080703460070409030702c0d05070454a141c050007500100003a0040000707001d01c403111014640ca86164200510280a480d00400990552100b08400180700400d0840345110340c1c080d540c0d8517144d51000d140c00c4050340713244042c992500e488c00b54000200341304c0745200021818100006018146441080d03605003047d030b111903800030011030006240401074100e14442d6060382d0f00c2010541c0e2351002c200100d05640100041c1d60322002040c4001411003200201c00030340140504d81c080143d90782c46141c5490500c40d10001814490100002020081448041d21049400f1f900340010000024425070740180b8400703803591a40c280e0003940c210b0004942196891800c81030f0709a4891441c0350107050256012030041d2802c078001203010b4400c1c41854a042c105030348081c2c480b4516001111644a4640034402403100c0b0f2401c80581d551b50311540300002100c0e14003003400000d00f00e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 212782284 1250 212781034 212781047
    0xc0f03050309060112080d0c03200910052a030d0218012d030f0e03030103290606030c070213050925050a030f051c09080d020f0613062a 60
    0x70480c40317440108580020b200d410540e000c17030342c00301000a64210306032070440107080b294080c5910950f040024109070303900c7e40014504001c0030345100488040c1490100c1c1c092244150810300503078030603446030501c40000c00d40c0c640340914204603800c040918041c6000ca92040c0100d6208c1065031414103001c0d42c0041c001940000208004150300c10700000051118085215280070599500c44101411403e58460448078800030201d9441e503840b40f5007441d280007444a5042c13642d811044803083e140c14184114400c210242019096449451542c0c1181d04402022640700440c09066400c0b50214820781c0c0c41018280010803170084d684c6140c240070b034811100200840074142007071103161541e01c403c0c81142d50100b01f01c5040c07889030500038101019400d0f041b00c28250414402e401c2e03070b440705514003038480315020380d10321404190082c0c0c1d40d51440e501d41032058000d000082c00c00c002096400d09954045c0c200441c040c5000c4000c01d5017800070154110720340c000d48061140b0640c1c03150703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 212783534 1250 212782284 212782289
    0xf070f060f020304050a090615020f030d09030c1437020108060409020d0c090c020109170901020a0507090501031103010b10030213030602040e0906010608040f02191e1a04120209070c0f030503090601 87
    0x68031010801201c0e041e10f901c00d100e00782515a07200c4ec0d0180401d882202d2682d03109400c4540425101d05200200361600541c0d000703c601140c2040800d00d5030860111510380d80e840314065002100c50f168010b50700400020425075006941340c00f19000358603042502d08032944641814007080d41440302e41800c41d100e607404d074000c581c5405201c400190170390090703c040b01188041207072a4241d400040307240c013940c400000c00754040e0030000144416950005c6059034828515166001d500400741800c840f022049540e00001455030b040001703020303130b0080c80803450504600300015225156501030368482c0d408442e810390130300c0410200c000180000743c0540001c0c544180b450410b612a528044040c0902034450301c00030307405a041e0340040001d0401001e0021400300007200020594561000740d2051501c2c00752a035042410807103803001141c09031400c243e1002181809a020300a0700760004207a02c00384440814035070081000009041c09281c460358407990390340b82000c0e18900345501030303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 212784784 1250 212783534 212783537
    0x20709020f03010902090316080f3f090a080a110d02061806070c030f0201020f030f07060f020d020f030a0c0912030804030309020901080d020f070f060f020304050a090615 75
    0x140301842400e881e05003102d0450310415405a01c0341d0070b190000b42421400c01030500c030110034440c006201c04010440c03005002c1c598003070f55040d03c500300290380800d030300c030800c5080f00f00b422804c199440d041e4411400003402640c0d850742409203000125060b0a00c1d074001041c158001d820550400c40c4c00c2628080344074003928620300b515040d50200e8614041d4420202070a1104011400c032602c6070019180d1990300a081e03038a049030742c2d0a01030b00302c203004801079005008404041a101000204580702c80d0081a140d074644216911060020080102d001c4c042319001c1000142d01c8805002500c00044007210290307490800c40300301c030110390a541100c0280300561804000d010b4160040c81551509414a08542da680e450110001d203070f4200d00a5002e000c100010132100d000096400701c01c0c0f515002c40b502d040c416420165612094400c08403200a50070040c441c0501c21100c3c001002900c0c01264241521880001c2071043e49810030041959507981c2000000b00c0340c49100f07540c241c02d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 212786034 1250 212784784 212784787
    0x7080d0801050603151005091c050714010c0602040b04050315191e11031905060f040c200d030c0503040b04020f01090308030901050103060507260c0702031c02070902 73
    0x48000905400c2051180d10b114102c04000100301010300301d100d401d10400140441401c850416015255030001900c25001d803241c950707442c4c520b1076031444000d0110380080080c01368501e080e411123501c2448541490400840710400c9e000915103002420192800c0000543c45505000505242c20840f00ea41c00a4101d44414403a04030000516551081c2040c08007040300400050902c0b0050241008044540e152072000741c103040f084000303940030302c030072000e83c509018001c4a10421341744195030840e80106102c1c2c001c5214942544a0408080d0300d040442c03505c101c40c0d00500101c0842d821486064109006c1d604003035078144160000b070b069030b00b4030070304505161310317106440c502c0240020b024100782042c07040a6805110071a00443d07200f0a4107940b032802c2da805a010b00820310045420364200030110b1605030003026410b41300c01c2c018000240005041a00d07032000c0c0c0d00a80020900b0034101b22000160301c0c2440351140005400391a0086440e242c1d40007890600140c1c82248110310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 212787284 1250 212786034 212786053
    0x3030a05030c03060103090f0609020a12031706030f0f0a0b0c0301062c0402070f060507020d050f0d200a0e04180303050405010b120703050706050307050702010c0515010f05030708 79
    0x41100941e50410301102006840340d481d040180c00074005081d028110711941e10f080f03010009a6040366616071b209a80e200119542c8540d00c031040a20f5180080206030248003410b09004901d000c1f85c0c0c8100d0040c11140c0c0721249222890800213900c501c44829080425050305000c21a80314507080781c481100945150315000340104207003c461000d8034203125002084c6003040c644058a0081000100110350f40d82c42841c0c8a07510106111003142d0789030611000882490000c140c08007803403610b8440a15005d4031142000349640042d11021140d0381d5036844038540800034200b506003c140c0e0b0800c6550b55081c10028181c40f0715003c14030310850400c440001d2009450b1000307000250306003804290740e1102d1800300e001d811688180b5811480c031600383c80e0940000180c02003164000d1040d01d10711a00d5800485c1c0a20046075400d006c94070410002c4015441018039107030460280c0e05032224400d0203083d20400703170000c0e0703c16840d10721501824001803600313000240080006400030441c0c41c6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 212788534 1250 212787284 212787287
    0x12111c12020904053d0e1305030c030c15040203030307050313050d0c02031501060519020c10020c01080f0c04050d1103250b041a0903030c120d05280209030309060c010603050c03030a 80
    0x912a0040a035080100703401f25081500d000c00e5056170542c440192a142c0f25a456555540d80119411180d0f910a00440c00c0075843c4c1c84003c0d40c0903d8001d00a1465980c07008800d548a9101820151040700d49045110100303c003800340e14462003003507031421203241090040602d020610310420b200702610300010802e4903001411604030014880d000c60000e111584242d00b86005024078540103050803941180c2c0f00d6011800341586502621601c0c134070346999215000b13444040b02c500c1d260403020030003440103242c00d60500c02841d100b001c03140750400110012030704004004500c10b0900018601ca110440101c0c00400d0150403180c41140c10a40340c480581d641c1c00c58092000c0e540600050034912544040c82154405092481150080c000d070840d08003ca0b0f10040c46800414075190116031010400c6182c2c8160401180488459601c10074140c4001e602880ea1507505120801c00b54400f41c59600207442e111402030300005650340345040c45c905141515984512070b410800100390b019 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 212789784 1250 212788534 212788651
    0x60504050a0b01020a0b060415030804260d05070f0503180f06070503031906150f030605010e031510120b041e0203060703150306060312111c1202090405 67
    0x13a81042003101b490b207441c0c01160081c00809003446080c04400f00100512510768001c20880c0c0c8558200c2c500b40041c87d04650030503213500c441a140d60051640b503c145403080d000343c1800d900415405c0c000c4403556458a241d0b5000050410b40c5400307017486203c003813400300d841004071403041d100b180c500112941c0b6241c4a110081c40348004210301d00d021032007640594002d201034123800d000102c0040344140083d03d100b403052000c1000906001000c15194416240309580e00401390092000915103c3c0003c04018020a810340800303000b0000922401070418180d651806080d018805041500741240300c03501303000042800000c0c818140006071030000703815600100902d000114100100045090504143d00c09042c0328185031010003400403404000c0311608447d210b680107140c00154950311f82c84810343c02c10001c02038480d82c911b01c0740125503082000410020042c0b5080c1c2400000b0200c403400e6400582824202d14101030300046449684040b00211909225807680780f0300140e030705c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 212791034 1250 212789784 212789803
    0xb0315040218030a0b150d030806010302070318091406100c170c1209041b052517040e0109060b03010302220501030b09150c031f03080c01060504050a0b0102 69
    0x11580002d101850164058480402c1d003001401c2c4d42c00e596203410411128001130329540c89040901c4482d030000e14088000d091001e83c15103d030146a69201c0c0194003d401180c015070600180c001070301c0390182c4040103400900034850002070311203070b01d10003108182e00c020541c41c011b801000103003007000c3d000b101328541305a01c41030982140100d64203004840c024900704503060b00c90581c204c00c89411240280281007010707034042260008100f12031b80201c0c04094040e0100d002001042203000001c4c010701443e020000f0154104000c503551280244244050500c0b89034011505114054080c0007250040c0700420083c44903a0400015441030301c0103105c000d100d002d101078404201c411604102c1088a030061040046603074070308203060995030807600340c1401e00034114140c21821422081030300910140c01d00e82d0469440342d41c2c464001c2d00c00019415500e001000c0000007511840040c80100a604004100380d850034003800240e6202426800380c03a8105805900582d07130014401c1d44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 212792284 1250 212791034 212791039
    0x906020312011403031e120a020a1d010311120a150b0a1206030b1801060812041502070b18041a0d0f021c0308060f0103060f17150f100b0315 62
    0x104440f040080e00e9845031150000074030104850300d01714001824081d00c1540141280001c045e510154241c04a12a141082c008180c070300d040d401d0348001001c21011000018100000d08078060b40d54030031203802070b000282c04410420104040c0d03a155005000d4540241143c1140403410042401814003c148000307040105103498000c421160703403c01402160003107038607041c41c203210418010400c605c00c0b4049403503007030010000c2c482c500050070108940c00d9103803041c28542805030082c1c0c03240b500c0c80742504600c074846012070600303100c80043c0110b2070343c004581c00c03c090441c24041900c6034421640c0890400140310f10840c0c45400360318140b5a070104640540b0b103800c0c400100300468118680751a100801581010140c22010103400740000702c5141c18115244401102564418007030f40400d60120a01005421591300c020030640030a001682d1070014007024801e5844400c48070002d18841c00b4090140c0204060702c050064010382c0b44480c618640707031042e0404003150264450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 212793534 1250 212792284 212792309
    0x1009061b11120a09050d0f05070e0709050d050123070305010e07090605030703061503090203060c0414061809040b011404200a0504080106060203030f09070303080c070203010e01051006090602031201 87
    0x4902d1440340c80c204d400b812008010549036151030800414010b007060086034540300714280030810b503514840c814403941032613480221023410b1034240001040c10b10f20490f003175074030340303c03840000d0742910301c20595801c01098050403490880c40041c19110107901c1500c80e58070b0103041c41584c0342d20010020989055080080d92a114101d080380103150982c80350340c0d0035a00070207030607540da410f800401c90140210b0440e404c5440d4481002d0701c81c811f43c441c800c006002401b141901c3c0c00e0850280c407045403550b1b400d1110018071408103206034411601110000001720040c00060000107a10444035000c0d04c0400c061034003030400900f4050300c1a050b8036400d03408a09128400d120380100d8000d070134580d009100b0241c1d81c510182d541d80041e50451026580980041c030302c420b00003503071422a60140e90309041502c82802c2e500180d485180240d826548078145000d20b81300900070076000e003602c081500c61040c509100200340c450310360407440864004201c214101c3c50050740301c50550348000c100c2c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 212794784 1250 212793534 212793547
    0x50402030c030607080a060501090f122303030415050f010501030b0f04020c010c030c050f0708090109080a050703110402091e0402041703030106090504020a0c03111009061b1112 78
    0x3440c08085141c40340e454030520782008061540300d05084e0207941141c1041c0700c000d80758801074442400ca40604003071170712005010007019120341d000402403405451030f50040340111642e24806a10200002160392000040c0410410709580c884d1403c1c6030007100704100d0400005101c4500c10610942e810540c46c2c0e4003207100e81d42c0d0b400b1541c0c4c07510303002402156905c42c483c4c1001d021742661840703400440e19024481400c1c03402001100c2c074041507012800d160a5041c0c1e107a6203942c02090b1000d0402c41c0d0640086100042040321803c100e0041c6c0c028940365103107251a8011248412040f40a0382c01131141310007d88540703d440704000d607a04030295060074000d0210f4024026640090b0009031074030b040070341c0c08001100440c1a1410f40d2390b03900c0440d8448051000780d1003421401c0e0005661002d158012030302c1081d4401407030006e5000c0c2c801d0201c000d00c852040d0707140c0241c1554a01c1d62901e502190b10070003404c040c4400c103070381440100185081c0c916500c1c0c085c1003001d820443c4001811 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 212796034 1250 212794784 212794789
    0x70f080604090303022101170609030d0e0c120604060b01030e0a060b0d021c03080609010b0a0e21070512060c0a05071a0717072d050702060406030b1005070201020a06050402 76
    0x40d240714042102c0c0311000da181b03900081d40c07100000c1c40395001100502001100d00c00c3c010442c580319080b190003c600d0802030f0250f100081071414240c15160254810011181c1d48149400c030300002100012300c1c2d18207160900b10101d039218485c06042c5032500d880e8008002011a11000481e00840d000601030550000320700e445039101d00081d44001c8940d28182c054000c130b5459032800380203643d0500386558150078040410000e001e1084038450521122546610806084d02217210290500107201e207241ca991f1300d0386540920340b1805402000f0144024204041344815010901005101c0c03810071140c0b02d41c1d580b140400c031030104034000615000348201c004520608229503c104889403604079402060020a4480e5030300703100614003c034230010311403d0b6401120044091610707514250610034080e54a0740c0a640041c800f0502010000d60ba031200070b40b00170b003003503100841c9504600f0200860804100c14407030620009021710000350b640020501000342d44110f00003144d480d123000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 212797284 1250 212796034 212796037
    0x1e060305120d0212010e010e0906040827030706111605090402010e0105120412030e010b0108070513030b0901020a03060501021b09061c03110f010c1209060e060c040608070f08060409030302 83
    0x4e03100100107404000160a42415040c1e412141102c420340c0c0141c40303441000e6104d80090740e001d0103001060244e505418240b0b005d090904814404001c021501200840d0401d5040d500060102d9408103000e20703d10401e01c0601082e0142480f00c500160810f00000d03c0405c01400c040c0c108034004c016402d490b405002207601030380c0c1c0d11916481c00e00d421b18040081c0c0d00075800520003e4109105250b00318014047e042081405844003d500c4e0f4500e00300700c0e0321340c101c4003040e440c5209201000021425204200740200250740000d655400c0121018042d135a59601c42411903201c2414185040381e4490b0001040c1c2040311b0140c641d0700d60000042c2040c0000b407840c2000c03400e001740c2600b0160030030820142036400c02c0541d8a0b103c070501602d4201c1e1035241480740864070440b182e2504e1000781e801050704620400d4000350b2400c01c0c8030744901c3c1400485030f034030b61400d00040c01c3c800c03540c00c405466804805840c0c104681d200d1004000d1950340040d01c3d840c002c603102c108a00c00c2500940 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 212798534 1250 212797284 212797297
    0x70c033020070609050d03020c0c01030915090f050d080106090e04020d06050f070e030706121d0d081e15040b030c1504090e06010803070b04050c0604091e060305120d02 74
    0x110039a80b50042410900d000300340c024000c99191140c1d5425000541c007900039100704c409030802030304c20b0181c90001900a0154a0812103181020440201c204441c41c81004040c9001d40e540c000720003c0307803a09c0c616000c400d0550790300340141c0400401840d0303440200385003a01d8290100d83e1003512355101051702c076050710800a03c001c0c00d0200b0046104a50b00c0414440c803042d65401c40300750300f0394041c10784a0b000c900410f400203020340806050010181c0107401e0038102a040e00110500d9940c8150505410078203480005681c1414445082002401440b05800f072512584450408900001d10350b00c24842440c02035845001040031950305200300100c010020b0141d00802c3c0000c0340452a81d030150149450300303441c0405c18503001130700285081c11381c0d064200561403c00745440308010040000d100b00e403684100c10341008591200d030301810081c00420000300346103c1d110411014900084c498050040c0342c03900803c003150002428a0054044484940c0d44140e0380004002900c44d10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 212799784 1250 212798534 212798591
    0x60d080f0712121e021e12041a090606280b0408070603090c0512241501020f070306020f0c0604141c08040602090a0e070c0330 56
    0x20550406201c14182841400540343c0c0d1248181e500e00c034020f004640c09900030700c02d103624000c000000040740703600401d6070b81d400c81d403001500d070044140d20000d640f0442c106c0118500300d40600003040890780c08800e144507005800c0b10a464007001d0141e40300d10050009100f0302c2c8400c1307810201800c07801018691142d01940b000b2451715465a110f0651051050700c481e88543c02c000202944a881415516030f480022000518642820003402403610360110201d400b8150106140c0d44084c4a21440c49224404080042c504580c3e050101e141888616055400c01d090441c80014040788090549038000001030301c98051000b044c0749400b4841901c2d03c0f602c110b000b40010b001526806a040c0e25400d02102e030090858800d90b003040c511007051601054031000824001501c40d00900195040a0301080100341d07100041d40950700150356070008500100100000d050b401102ca02880c1c81294034000142185d40545c0d0300704a6550181000d03507039420b28500007801c140c0003ea00000e60 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 212801034 1250 212799784 212799787
    0x503041131050402100c050c090703151215060506030601080a0e1f061509030305180603070809120315062104030518030606010e09061306090603020f040203060603060d080f 76
    0x2030039032800240742c00d903000d920401000b05008561441504424141607000b4094140c1c8a9010140689644041c24685c10305072902c0c80c80f490b2440083d400d100800200982c100181e0040c1020384000d64007604240c2c030141070602c184055121441100d804c03036070a00e8001c045603200411400102180b203900740c030300c0c020039100c0b0902000c1e40041543c00201c1c04800c0142c0341d5038010907044250011400c3e0701055411000f00040390140c80079000d407001445030b000c498019540095402c1e80101e403840c000c1900203041c4a4000f60410904102c0c414103110036155007030403070a10f01c0414540c0e0b840c030710440000a0f0b0301d2140040c2c902c1c8041540e160944410a41007500d0f01034010b030880400180c0340a580b0399540c40d18600020b00364003584060b1101c2000c40b0707402041c40400c280080c905500b0038000d0740c1403208200117215220090010700c1d0005030031030440c41000400c2c016005502e11850050041c001175035205012250040c104442e50350a40009240070314540c0100023a50702e14010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 212802284 1250 212801034 212801119
    0x51e040b041e0b160b150d02061303060216030e0901051315080d0503090f0c010c080a1e0e0415030206030109020c0a060f06060e1816051308010905060705030411 71
    0x72030740504c400075104110030740d40c5640b0117510318803900e040c1c032004c1da0080380706800c1c1c80903003010402448d8040684000020094682d00d42800760381c4400620413100f0302030500c0000349680f106440c880f0003403c42c1c022019524023000103082000c1480c4400c24280e403801400c00d0003078a0848580208007080646100d540210307000380c40c542048407088294001c4443c0d4000c58a000300380d031100c480050f150350444040303584aa0300241c02110a080501440c80101d6a0b10244419804a80d25841e40c0d014444001541840103840d031b1141417654000440030103000503652101524191401004011780f40c01604403164601b071210f84001e462940f03481c01442246440d81c00190559869840d880c0340c41020714140303d4800056104000840412000305865000440f0003852400443c0317019400c1c0000c4044910041005610070300203070395511007101c01c2040521000c0d5110149080490a601e4251914030208404001541c880d028410017940a540000100780c1034201c070400344040c904 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 212803534 1250 212802284 212802307
    0xd060f0e0103020415030812070e1e2706100302070c180c090302010c021207050303120a051f030b0601021009080c070b0f0403110d020301020a051e040b041e0b 70
    0x1030a000a070300490820f03100204c49000b11545070110781d80141e46a140c1040c1280d010000140503007150300b000700d2191480070035074881d070b42c0108900c00e8241c3c06544000a404101c03203030039007504440909509542d0b81013022505a50700340d2200064400d1111042001011002032007010b40c004d100014030b076801b2070148454114062504144881040140b402c220281d40103004ca00c0028009174140d0036131001400c000c10780a000c0e0041c002220102511400000c0c00c5400440c82c2d152420184400c010026405010700c40d0081d07000080c4080080c91160361580480e070394040903182c07107000d00100c1e400340d02c00c124150009001c401c0c1046100340724604651550700c05c80b01c0780150300c00c81034086040d410903000c0b81d81c1c04159007040d030325052450361009240c0c2596500e0607848a0228000d0015840030700041030401c40950b9255501d483e1200e4501200404003282e0303101d00c000b804203002c7c00400b641202d00b40d816040341c01290315000007515080340309035082110402030200d81161440d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 212804784 1250 212803534 212803559
    0x91207020d0501060806090d02031206220515041503020607020111030d05010312121a0f0d0b040309081207020a14030a0614070f0509151e0c0c0f01020f060a020d060f 73
    0x2847d0160548a51040490040780c1d41d005942c001c10100c064480800c40b40d1400811318074265540301d08804420004002c00811201c0031140c054050590425250303c5241520130f84a0340e0300841201818541140c001c29642c1c00780707150003418000d03100d250101d6007c4c00c0040da0700b80e194504007400150784034600913000050340402d45010800010b240c1c280049940a0f08640d001c86009442c0210780000c1007150704210900819041412000000302141c42c080c556032065010b922101e0f140c61a0007001480c111095520642008080c080719005a8808030103c1c100c49065200c18091076006000a0918402c41030041c600c5183c00350b401d648184c0b1100c2c49106611325140c00c0d141810080d02035030300d403041d400081c0d48000380b003a41015100401d4054011a04d1070510400b0007070b40c80d000c004407644980d80d40c0303046900051100945150103544008441e0084c805400c001c104c0d0b0007560b0755158040d024003141070300425550342d0210f035540f02c2001040c1010318543c500d969075849035000b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 212806034 1250 212804784 212804791
    0x18150207030b010b030714090409290c0a0f08061f0917030c10090c05120a060b0d0302100b011b0c0e1b030f040303021308010b0414091207020d0501060806 68
    0x40c02c1510000908040c1c001c041ea403040d80c03640c40e000c0341c4201000c0d8501496014803840c6601a64070428600030584400c0340140000d10701c0c0d92804007240c0000c416041400c010300102401d0300810001c00c00c0340c0d2010700414072100324240304885459500010302200c110040740000c0c2e07850348400c050104e40c0001c2030402c40d1240380e5402460303103501d0382e0a03443e44513441d50a081c603485542490750412603a400180d445000312041009180c9440014a0751162805d0640c0c80e0351041098109015540c400c080052800301e071003185142c540c4c1d80c043d40f0b8082171842c64103103568802500000da40542003604000f69000c6c0c1c4e00360400f1041ca0451480d0301c6501407d5920480c410005228054220030b00d081e03081e94080180c04d61b03031100420081101e000304124101602440210204040380400c9409002c8181c0003180c904140014003003120071100c0758002d040582d1013032140421000c0303050404501155101b517940c07100350000c02c18074002104002d08039803070540001450400443d21602 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 212807284 1250 212806034 212806043
    0x402030403020c18130807150e0313080c01120515061603080606030106140a030204030c0306061e0e07110c1201050103050f030301080d030c030e011a0a050406151815020703 76
    0xd03440035044d00b429001c0c00c845211884c03406904242c0440c00100c050051a84102c42034a07054182e20303400d07011358801241440f510392002c600c01e1000c0c42d410741024058003000d40101030b45448203000924144030b0741c8800d003119560314007040b4074803018a80010720b483c0141200399a028a00b4420407000d0f000e05042c2c001420443c0840d0140ca4400c084030304842c05542e540b400ca1103805100407480c0e2002c40301c01d083c181d01300300001c0010111100000110702030200010b407680b6200c603900380c500c0040c0b0740f03410302c0c41c03801018460001a0618190004030a10f4114001c000c080205441e10110700c003030a600c0402c000a00300501302c15000f69060341d100780183c0f107024040683c900d581307000038040e0f090035820103003401005030310942c48282410207520b00807840001250100f42101c03c080c290182405d2440071020442c14001d030307401300400c0c0554040003458500030285002c000160140c20030804041c01d01503010325074242c20300c0603044400d034542081e05418406980c0340141c1c481243c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 212808534 1250 212807284 212807299
    0xc050903010b151213140604030f030c020a061509060b070201020d0c110f0d0605100e1305070308131a070b06010c0b070c1704060225030201050a050304050106050402030403020c 78
    0x8910b08220b0712440c80d06903e110342d0340c00c0c50b60460114035912402440c960410401d801220080b0b008501d9119100f507045001d0040ba040500f802064044d40009150905080c41c8070503100c40d90000310041d203190800c000140f6442c0b0500800010016580b03c1203105007015000f1480b421202c00034410345200740c00b1034604030340808054443c40c207501c1c000391242c1264583d02c0c801f42800c103614002458028040707618100c5680e035400843d10190b42405c2803410411060ec0f841022092050700511400840419603d41d940d640da0f9440e2580001082c2e91404914401c41d00760f00041c84001d48a94000c51919898548a00d085900500c00640e0200c0750000405c0c3c3c154040c01b02141c006411048005503a600c0b42d205031449040000219800c07a812020303107402e440980301500107041283d0240403908001d03049144170031174800b807400c2d403c10898400c100607a00442203408a186a0802c00d44030340c1c40c3e080c0740740141020351000342c205000008000c02c01da40820f000e43c420400f11280c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 212809784 1250 212808534 212808551
    0x10605030115031b0b03040f11010207080a031413080a0c0b09090105100e040c030c09051005042303030a03050f16020709020708090312030708010801110d020a0507060c05090301 78
    0x90300782c429038095121001800041031010071203007140000002002090f6080c0e40e9130701d218070511036004440640300044c14401200811410900c400b150580034402000621705290a09459040e2804000c0c284a0420030024203c10400c0c1503c000c0b2495138641c04041c0d0746c2d0749015440d10059101224203060303000c400302c0c1c0c144000e001e40c0c064100c09480181c0356070801081c056240e2403507030010284150400c2221066a481c000d001c940d6110350350200f10b652003141c0140001503150000c41c03248081c460048402640328007510b0480d20000441041c03d803041c07003500740f50710800342c0341905400300207107140f540e580613040303e030081d0414004446035690b0800030595030203040d0b16480c0140c0045800304240d07040c82d00030b40800c9019040d030502d08448a00007c0c5021001401145500d60120400a840b6084a403032401415144020300442054a030300000c2481494107000440d94042029801d0038856019290710036440407042090500b045005461904540304070fa209601f4078595 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 212811034 1250 212809784 212809789
    0x1008010e0906011a2a0d030b030a020609210102030c0a0f050703140a0e1f0e0324270106050f0402090312070503211608010b070b0a020d09080c010605 66
    0x882c0d0485000d00c40e030a180741c0383d4044500465100d074a03683c1d4640d0a01d500d5420450003541c1e280340a000c080020502e04d0345c185005001da41d50406050310a070030248928000da00c8410854042c0c001c11500c0111000e1400c4042c00440100001c1d074000e984040108103079000c1100c010506004543c6840d00f07902c0450790210303900d124000008001030507590403081ca408100015080005050510080c01c03511000425120130b00d1403480c042041c0f0500c80404e003280c01c051070039003010040d0041c111100031700f10103501c1600c1801080000d1289000080c2c142c02e040f11a00140c062407440c0c100c1714091013444507020f00840c0c0103240c840d80135080f0030805481c0a108803507c050010340039183d6100200003040c855004010f00ba00c035030104000080d0306103a21030514400190703001c4805071904151002000602e1104441d5040c046540b0040c4044000c40060743c0b04c4540c40f401e540c1c90f070b50700c50604501a00402c00d8a0280704d05207580d81e4104110140a0030213a11048002c001241ea80c104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 212812284 1250 212811034 212811043
    0xf07020a1223030405030d020c13060b3001291305041109060408060103031202090d02040e070f0807030209090106060503062701030c090b0901081b0a03021008010e09 73
    0xc024420320b648042e000c440d04044040e010b00b60806000d690402d42e0701c03004641402110720381d440040c0c114a1104000c0e1800122201500d9071500042000354100070406007140700b8941142048414664401000c01641c1d00003801482903211420795035035240d0038180403c0b000081c15218103210300f492600c0c080031409481410584062403680c50749000c040c400100302c41c070000c0307080500801c4260701e541c40f6030000748020078085008003110340c55402d00401c5213003400003d00d06035004100313100c100c1d0388011b941001036804480002d141d40a0500c59484e00c01e02ea8088044c8841c0f540c0700052103140460300004a81c001c0c0c64240c22551803050207403ca03a0240540e0f4003054040c004a540c506101c01c042070f0307081c0c0c040c0000150700303203207805220644402d90080b14614009041404460310500030fa5903010025508034046504006c042d94032880e680303d80c407002007441030941760503aa90003c0c4000540d0043c240590103010101c000740713000d4090141c004058041c00c0440c0f420303280001c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 212813534 1250 212812284 212812319
    0x2040e1503031e1207080118110304060b1f02330c1b15060a09020c0c06090301061206050a0e07150818010c02010f0b010f0e040509030705030f07020a 66
    0x70081c0d0329007420b001d200c6251a20030300d441c0d414400f0502c0482c9190003c900d09500680c2192a650f4440d0b2501d8404030f517120150807003c24140c14141e10442e0002c03d181940d800a41c0294080381ea0a5510013290000c08070402c0d61440d40e40007080c0404698010076804c01d01d6040081c2560f0030b01401c3c0c1010800c2191401128174004014005001015071304060000b03240314000316295102c5911700d291403c10301441c5111054450030a000c000d1504049040052071321079405c3d400c10f615060034a40301e074505403550b4065000001d00410b244d8003035000390b01074400d00401c9115100c03103090a5004140c01c66904110360701e0b045040e0105000040c4050840320450f0340c10b11012842a003c0724130a80182002c4c0355103248083c5003034026828050460840100c6d400000d11401071907010041d6108424141d060200c0d142c442804107502401e10201000144d401241c00c1e140c0401840c9036100310310006d022070102252890781c4035580c80040900070f0081b140e2074007407525108030013829070155 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 212814784 1250 212813534 212813539
    0x220609050d0c170705031306030e1c05030f09010e0d03021305040b0603010909030e0904050a030f050f09040e0307170d0506011d0907031509060603180f02010507050c040f02040e15 79
    0x900c1c0c540f51403003d00e4002c00d882072148043e24248042c04242d040f402c0318035080348010035128540b036514040c0400510308032001010030609080940c20b8041d140d48005011a101861504e00007030301080c007504103a0040f100401103074002c0c0b50454004000b504582c0c42c0320300c6506403220014407840c06000302604200000d0146103964a4203000f0401014020412400d20603240b25007405507403000e200901c03860083e0050b00809040b440e00900c40d004a10701101404018030030003510011040558591580c19500041c0c03002860040c0381c554000c443c4c00500400a209071055055610005040b085000081c00e00c82ca8444600545449560510915200c036503c2c1c0c90754041e1800d900c1c1c030354001045050008228040d0a0201c202d0b001f9074114502060300d8130420001103078076101d402e10121401e8180031031400603035501c103803525080101904108010400c1c1d82407200034440c968904400400400c5900f8040300c40001079045072091a4220ba201d600298050f0400c100c02210007100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 212816034 1250 212814784 212814803
    0x50c031e0105090d3219110d1b05010e070603060302030d091406070f0209010b03060f09010302090a0e07090204030f0309080a1a0c04090f1a01020d090e220609050d0c 73
    0x40030302e4111141c84215000c02100c1c1010704e083c1109a0f00c00130414506c0c0710030398034a40c1000c9180540303411141c4e11801103035404400505c10031a4000c950088c2041ca4040498443d00c481c249207000d002d680d400074005001d12003000030a02c0d0140d0111044a109906031405803121600a50324944640324001300d05002901303030011450494010022a849640144a9000c2d1343d00803619000f402d03000082c58000c00410301140d80743c203081d030301219101110030000560540d404114951030280036014114b4982e0303003000040106015007006405c2200c0708540311942c07820b02c4e004845401c2d205a0100b00504004900c0c1c17500854801503094000107184c4800310312a18155030180c004100e001e0a12080c0400700700a0205d014110b64812020408641e0301d1010000200c2807607040c5806041d544224002034401c0d810010490864240b003000c11082e5840342c010384403c0c080008005a084036401c090000c01130346500484106020347c2c03c440b000403400d44141e5210907c000c3c003901c110780 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 212817284 1250 212816034 212816057
    0x1120c061404090c020a0c080d0903020d06140c03060a060503010506070210030b030709090507080c09070c030201150312080705030606090f040f151404091e050c031e0105090d 77
    0x180000310791142401080c07441c0c030f595034100b1030132651021000380041c0c21108580e0140043c2130b19141c06882d140303028000300c1d003006401800038040ca00c4020701902a40c0d96180902400741c3c007401c01120781c00b09107101032500e0010300b901c03580110b440920802c0c9000300842d00600ca070041d02d0603110060301851414100344c00b007005005c602d0f202201010b0f100c5913000c8a5440501404008041c1c00901185039071207407420781d0a0000a80101d0308650200404103a00c3c0d4072802d00316002506030402025603425404c0c01c90140242030181038180801040000400460254007a903564055980225035102c20204541358030054030315640c07000043c0601041744c5080300c09840740800c000d20005001c030141d400c130b4007036801da65940180686134030010040348604841034010aa0b0840f410040c0c0030041ea181501441da540d1001c4000c001e80c0d070035204002042207034039441c54005003240e50303005108418880844000303841160035420140403412004000605c2200c01002c0d0721080304045 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 212818534 1250 212817284 212817287
    0x1c032a0f08030406090503040612060b03100e0a09020d0b0702100c09171e1507080705030408030604021b0d11060108070e0705070807030f4a04050f060901120c06 71
    0x2c00141060b11407179503c240c84000140c003000140f004120b15111105420340071701d4050b003100d4040d030040007071043c10020041b84451151050054800b074840c940e03101e031182c14840d001002c182070006e40003400d0124103418029030300d00c3e080c400d889581c01c50b20901c205080c031030700b5504080029004608030101c14041b40000200c4044c541e20204125419000b515503c461881403d41d0080341c40e8000c5852282404500043c10340d01c12007504180c056418045d600034064440107001801441e00440450311950b41d0760100c402d40c1d02403200145003407013000f5419403500c00f4150281c0202c0c07241100f950445402140b807c1c100c45030f11010381031451521013852045900104410100001005207100041d410406040c62074000d46c1c1d500d005001c2d040d07015111802c01c0030130b14441c8c54586c0070350340800958401ea5403002105034a6001001590003410040d01c0008030040d441420324080080b1000e418030414410902299544041d07640c4240d44c462802c044100a040b00c0d1441009000da107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 212819784 1250 212818534 212818537
    0x140a03060f090c020a080f1e04060f02070f090b0d1211011a01050306100311070c030b060406030f1403160b090d0810140d080a1d060901050403111c032a0f08 69
    0xc0c245070f0400c0c4c8c036000c4000c50800c11140400c0100084180201c1d007805016480451110b4810303a1740020115141000c24a0048055038403419400a80f210801581d40e1240003a10084030352160354014070b400c20540c05810707100d0039a00c0400c99841c0070841c2003811031800c01c140c8121010384440d807031529005c040c41008050711541c1406d040d210207070b00c0c0c41e032010300c40205031240c041d6280228450071441d0004558101500003449507051010078008030701c0d0360045e40100b5a1210044a5841c01c411686003107000d21081400001c840108040030f0104034036103a8416080ba0381560211401c4c50320903a42c00c0b00540e610005083c040c0d41c00d0104901203203030040032200c01801400c49941d03e40d60401181c0c4035003859000600042e980c0c0e03403a440050040340305010100e81507030800d00c40b41c000030028020341c840070382001701808040d02d0300e481e03080c41d41c2c203002514241080c41c41e80c242400f03008080b0780703540f04003212000c2c0c142c40c1e070282d8050003000c5181c0d80043ca40600314807584802805 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 212821034 1250 212819784 212819797
    0x901050f0f0708030f040311060f0a0c020f10020a110109030503011703160602090907080f07030f020906040303090302010216080d030b1801060207062d030507140a03060f090c020a08 80
    0x90510810404001c503c032400030314401c0c100c144c0807460500d05850020000700d04c5000f4250183e1005c41403246034074000c0c0c0182c0e40b02a000c6000620303800038000407864003040840400007800f41d41e496022550341038000341000741864880d0010310640e2507401e401c82e042000301400280080c0010700c1003460b10082c42400054060403241090310404a0000441074910102c0740b07e03030300040c54981d40c00d04440c40c0b0743c41402d509080c3d000d4600748020000c0c203140149003000301030707490190502c0040c02d0350555003103010292986460315101d16003d050720803503020580c054070030405240211720009002a05543e100c4020b00b0103100440b00507400790071122007440d445a98841c030f55668000a00c6460300804441d030040460750300d0508050103030001c00290825507090780244c01182c0c0e4403d07007548940c1c0524070300000c0c01d0381d13114002c440714500c0c0301020b202c400c0c002654600c00c0380e00d03401480c01c1e10010702c808201e0300d070741d500104201d0704160b290602503000f65441c24080394944014001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 212822284 1250 212821034 212821057
    0x901020a0812010e07170a050601031103090303010f170714060418051008010902030a022e050c0105060607150c11070603021b0105101710060e04030210020901050f 72
    0x4034201e80e918107164100584890320440800010456100740450407074003c0010b003007900441e15550020074004200030640402c803902e1f036000c103106911079800004e00511038000981c4030300700001030b1a180d0b802071180803c00310051001150520380c0c41c9641140c1c400703503c0200441c2e407610398002c1030318450f41001ca038000307001c2c480000c01c011000d22864034901c54200c0052035181108400003400d18507000904141c2c9000c030104016240022000800e540441c0e003064102d040b0b00b020200c640c090345202c0c1d0800c0600011102e40ea402001404110b801c0300c1c028000c41d0780e0501404280d00500f40080c1900c004010380d441c0c5003000b94003e50342900585010489900c0c4441c07102e1800c6010b41c02000001c0d4000380985811028024129001d04000004d1240b410540e40c1095584024020044008802501940209002c0207078443e41364021074180009552007400002d4107004a501f5805030081e80030420b201c3d6410b1085034011201610341c281041080034212002c2c0c1c0200c0818203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 212823534 1250 212822284 212822293
    0x80c0604091509060b1908010617060303090409050f0d0c030c031b02040e10050a060b042706091d010603171303020301060f24020a02061810020f0f030c07030602090102 74
    0x3030884464080c02014110400e0820341e603e0411600400d020b1441b0600c0040282d10342c018481181c2c803445000506004110b160030549403c1d000900f98070489110303e510500d010000c0d4100007001c5009128041ca640c161380da50841c050081c2c07040212820300030000ba01588071800041d01400c401420400c0c1040000f140300354030b60215084a103da010b840319a4400004c0542640c8207000740f651140c4004805c2c031030145000308080303040c0203d005180380540c11440550310b0100100c0c251046504c00c00f41031100341da032180380c8001013500c4107140c020709c0c03c0001d03202c15040050081c0c108607a4000518955228000350b8000d16402110241039000003580000000d03036024016100641008500c2901c40c1e458070240300030712202c8a03941c901c104036806019128a8002c80e0350350300a41c040e10001d0f030300c05448250300456a28114481e034071403100c1686202450f0f0000e0b0164080701c1c4002182c0d103842c90a4220780e175a000e1a0b01900050344100020300008100e0f401a0014100600445 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 212824784 1250 212823534 212823539
    0x30d02160b01080304181e0b1804060207060c02030702010c060c0e150a0905010c0b0703090f08030a0603060c050403212109060b010e0303120903090a120606080c06040915 75
    0x10710a038582a446100594400b103014003a808113000601a48460444108030011000381c103103030701d81f1004445000d03103030341c84e030750f041c075a49440e02c01c4050104104072048251604c0e190481c020341006e04151440c0d4503100070010035500000480c1c1c40650140c40703070100c04640741e490700b020308034031002c035010008010303000003075030321802c04d000881180f241c9100d403102e4002800810b0005658810b904000321a005003000c200b031800000c0d0421400c4c50081800726081c1481010f41c50b40b8070b4018036a850000c2006071100360b9034403171002d0320312404043c021030000090071102c90285010140400c01011600100b000c0444030641b40140542080c83c100c44a000c1a542d1404036010003080c05500c41c5c4203a0204280d9101d4a0014042402c283d55152240c1011a1762805028407011300b000c9018040f6920700703c104160384c0800c1c40246a5003405403070f922410240340416804841540c01c0203c0800c03140390210707500c40c07000d1010309050b050030f00d410b19640c054004110451111203800c41e01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 212826034 1250 212824784 212824793
    0xd050405120708092701170703080a0509010e090603070e09010f060611070e04030f05130506040902091302191d09070503190e0c1003062d0602010b03030d0216 70
    0x5400e482c2d0181d00080e40701e0459034280400c101104041c829a04020745202e07408601c0074685c6415252500c5840d81107203c000260f031301d09011038101920800d40440c0b00c60119a0040049c2030029081c1e072803a28111030300003442071010b000e8843d280d041e08000000e0021048070b52026034442d11000c00803407140310304d00c40001103989c02c3e000040040c1015500101c07600041245000034042000340c2c070107a142c282c400400b041c0804c896242000340c0042c41d0804640d001e90000003030000109490f039103a540d00d00d43c20080d844205ca49000300e4440c00c1c008102c0c00584203990030003e03501c00300d804005107050b04a40340165207041c1c9440301c13103003d40000651902580d0500c207240c2901c0ea01c1d0b6a0810280121140c2d84e0091110b599904041754000c00510215580d0f65910741540c2c0c5403520100c1c1d0006801070320003600701c1c110212055801100643d012511030742c01c202c0c1841c44420041d02c40c00c08034240e440d003c0c00766405920030415000100d1403507000702000d484d4a040b03034140d18610ba44 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 212827284 1250 212826034 212826037
    0x1020f250315050601020706051303030e01020a060606050903010c020c1e0109090f091403090f0f0112021c1104060e150d020c060601030e0f15101502071d0105060d05040512 76
    0x950300002c1c2d503075200700a010b580420070100a000a82400c81c1448020021480c01e1141d6002c010200070a1140c00c4400380d000300902003589900c864240b0034181c884000900c1600000b000138070960810303461200c03490020a00d40602d500180180014074442c0050341401e8040c00d06440c100b00d102000040c58010074442e010060380901c40100e00d04540e42080040240851310008940c1c204102c000021354509070340f4100c008040d075080d4000d0740a800162040e4a0303000440030240d000058241c01c140c004001c160789e45c0e07440e239400c0201d50890301c00b950307150003113001d41004203070700a01b807407054079060491403034503200ca447d41880c00d6001d10000050360004800d04000b070344110140043c9682602560300100200c4000305180b945000711143c0c1e40701002124045081c0a0300460148a1203015a0002e4400802d034018405003400c8029900d446c80d22030301036120a05c0c6454003024281410950403141700a0000f8205000c0b04000c1d0010000900112554895200341c0b0720765030078650 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 212828534 1250 212827284 212827313
    0x6010e010527030d020102030603010b181b0c070821120c0708040308070f0303110f09130e0105090d03050f0609011503060312171317070f020303040909050c01020f2503 74
    0x140007523202c2c1040c006141c2035030010f0704618480d090120007a850703024100802c0d6400140604502c5104060741107080352441a40090b800301c0c000d024010599200001e900c1d440c04540140d4003148544510684205000701c0c000700500c0b00d200c3c001b064690700c20b50083c0c06014080c80e001460a60b5a507202166a03101a504031111180a07a01c20705058040c4031b9000010003910000303250900c140c0001d155071007006801c070300c5045000302c00c480040c801d0b2320501d0320b001c0002c020003c80c00e14100c2a9510840c0455000020b410b080004103141000c4080c0f44c020800a0022040d0f40d00344144c0210141d40142030070304055071048000045204c00ca11a5040c200c00e80b6004059001070705041050340c0010046081002e9640d0b035107000445814104a1044006000c0b90701c9a055282c0741d41c55120384100650305100202e00854003001617803007403000c0c621070400c844032401518016625000c98074118803044c0c014000f04064840340801001003080400c200c11100340c3c8036600c1c01403051a95 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 212829784 1250 212828534 212828537
    0xb040b18151b031c0c020f010606091806050d08030103051b031203130b0f190e0d03020705120f090405130f02041d0601031110080103110d0c090e010b01030506010e010527030d 77
    0x54045c1c0307038400c0d0180803801d5030a00c044d0091044908005024103001c13514802c0314101c4d08046480c01540400d54000130140c44010100121525941010016034201f8001500c0500450f440c038005820048200e03080020080d016002030b00452103c040310750401095050400c5104c01b41d00b0001d803005601d14440c0c02d01c0e040b0041e070b03030802440c180b2030010100e00096440d0301d46100c0741c008100000c0c04614030340031880c0161303a40d0220300d0214108001481c40c610910004103c002103088000080c100e03240c41507034200403075910310f0b00e8840222001c00020742964442c900180150074941c1251801114802c0c080c2c2400100001040c0303000790907802030b1030301200f03284040340d076282641c10008181c105140020342c0c3d5046440c1c4552604800103064814080800c4440401a02c0c940010040200e81c130300300005492644500d010784030020315240020700d0000001c01560144822240e41c560680d00d4600b40820203866003605014102055980d6800b01c6417000160f03020403003984c048005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 212831034 1250 212829784 212829791
    0xc0d0207030c1502210403020315010e0604020a080a090602040f03080c01150f060f03140114030c010203190e0f090405030c151506130b040b18151b031c 67
    0x56040120a0710a01e0700840b925032a03066004280f16400180d603a1444000c44840e1140c8075050a21a01031156600c02074250160111a80c0780302003100b44a4100c81c62070710441500d40e14101000100e100d1b81d079480f800f288000c13001c6613030f0303000542c030483c052449840018079003a210305a4074000310580e80121030320b40c070003d04041c981c0028050100f003680702441440d00c0c5414061141004c481078080c180c00c03c80d9904585440074840d8200d440b04103c040456031240d61a408803600500206200c0c42c0688500500303008a5480002110b41107820103803003052100500e1022680c070b00c810300400f9842001d0250031403440c3d4520047ca40501d100380011590307003070201c43d1075080020105000b00b5295240042240c41d0034001d02c43c1c1c11084045030ba2543d15150400c02c01071000503500000b005250108021419403820b6004018070542c8820a035032944512040044000e459180b20400d1841803114a0070a007404810942820025059904040d403441003805248140d1541440c10b648 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 212832284 1250 212831034 212831039
    0x1803010f0c021b09010509042f040b030d0827061f120206030711030c06010f1a0304080421080c010606030b0102060403020d0f02030412050601030b071706060306060c0d0207 76
    0x40400c01c0e0f940742185a8801141441c0c2c000024941c1c081c1445824025075507a80002c003003001001c8001c5c641c111140c0c0c1c107140481050300d2000c45001c03110031a4003807440c140c4a00c0d001c0ca40000c6500204100750703189001c550310000c1041e0819400001440c7c400c07004801701542c1d05092181c07510070301035103500744c0b00300302c00304014400d9841e10780c00584d031200034254400260f1155000c681d4481e03114101180c0c43e80c03c030003140d40345204052240005018020011400741003440a07030044035600b69a19841c5d50032184030441d01c3c03006550007425104204030800403c41d2034100325421205d400c4819a000c40c942d214040d0b2607101d04120882a5500d8605100c0c40350944201c1c2c000100a20051140b4079140d41c001c2d40e165107a0a0280c14051641b469100c940d100300100d801400101004179100700483c83c1440e900c52080c08221000020344001500e01340c800c40c00340304020f8903261604050384034a4103200c003560010340b480d60081c508004030400301008000303d05003a041b95005009141c0f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 212833534 1250 212832284 212832287
    0x311040f120c050d08070303020304140105071110020a080411150301120b011d0628030b09070e040302030f0903030714031801180e150409140d020a02060a051803010f0c 74
    0x8405400c5248034101c0c04c4a040701141d60b80e026180300710f603d030a0059691311503090a8a0301c440c0c00c211240c3c99800d003c200658554401500b5a2002c1103508544502d07940501e008181e003ea414507000282c081000070307020400900707007807402e0301d00075101409210303081141c80c0031640242c100c6d800301c1c103007088620200724880901600500131501c3c2c42d1140025660b220601c540b02a15140c0b0600f00c44055402c401805000f0055151003002204c0c00780b5604d18080c81c40c0e0703000702d8030060701d0302a0752400900096140d586c50f104650503400345142105c1e984420b4041d40024048139094441406580002100310321440940b0303c00301c008548440c040a5a892205a121003003810005200407191000c49000981415545501a01d0034640d465040e080b80da6880208110350040c1000088014091890301001c8480c0e151403d030307095800f00d240700780c0e650b61505074000d404c01d008100341d807452403113100a04800040b007465103d8001916000038295600b0003030102a0703981c0e404408401c10b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 212834784 1250 212833534 212833553
    0x7020715020c0d020103051b0a171501050703080903041e080f0111030109020c0f060708061c0203030a050d0e150907050d0506010b030702032107090902030f06010311040f12 76
    0x91103184014409900c821003c18000e9070400b50003414181c03a17a0104460f07c0079100a2008404188600c0d41c581001000090600640c440c012015201c403c0120389059600c00954011036010303180c452908c103507560100d44168005160f035815002c14132000c98100150074480099080005c0850859410085607500781a09a100c24905070301d1700f40c0c200300c04001001079034115401c9103801612104134010082c00c0200c8002900154010b07a0104607005800450a500800b8103803107000c5400410054410300c4483c80030083d600da40b041c010801001e1181005190a404110300881d21105049070310740750a50385101000c03806800002c110350070008003c008010170044aa180007000e003500c501c4d84a18043c01007003450b000002c0054801402041100d58000848178140d042194000d000101074034156014800980711060004030301e06a4000d0b2402841c110740004455180c250055000305881040c98040340d1080c480050800341c04400040207080c00a484c8031900381d80e14140140713 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 212836034 1250 212834784 212834819
    0x10e010b091c0305190806030d0e0d0524090303011202040903030b06030412030b0d02210a080c070905070f0f03050603070902040e160201021201030f06090b0a020c060a0501050117061305070207 85
    0x30451070001f0480c89940001e076840103c22181055010b0001000206280e04240300b0090400d214589050803107482105541701000c246401d05903081e1242440107071203100c288900c6030502e4082c2404400761425600c1040181d1003802d0005550a044001c10030342e820484003a280c4494030a502008280c06024032050f40750119114020201142e0006503c0c4150380d4850040349604242c49410341e008010721549650004803807901e410303003018007655075030080c007030b02e0b00326410800400d081d0741c00f4080105840d2003544910240c160540300890080000406c901e601d8841c180c0002443c2c00244014406480703540a02a1640b0309240d0002012080c0c00d01641160f2040005000711011401030a0540c0d9003e081c1b0f0b1070040c0e190030b001000d012202809411983d22605014083c441a40109172040000b4142d030944d03a45c01302014105d0328244140c601191020481c88400c0701103803080c50780180f00070301c0340d65045a40c0103110f0484400b02d83c2200540e0014405100c5c0e905000c007540e80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 212837284 1250 212836034 212836037
    0x3020606090610120b0418030e04232a0c060903040501171003021903120c150c1808010b1305010b04060c0303020912010b1503010e010b091c030519 65
    0x162410300c80041810200d0b0b20100b50b0030051814500c0582c18843c0d04100105e0400074030600c10f030000b503110040106084007081b03010030180b1200d0f118500780f500440074404106a0800c14440c040100200c5180000b0300501d09918100c0003408080b090301c1402c3c103200400c1c1e03510758440396507000d0309280103c00b0304968603541c01804104641e031303481005007541c1413803080d420754642c81d120002051481c9541000f175101c0e042c00e09440e20300724003e0681c0126800703500e040e44143c81d8114160b655100c00d078406800d03000c004445d200c01c429980c114004058207450a01d10b05e02c510b04503240420003a0300280d0380d60f5110020000746141900f840003241d148000104010b5140809840311840f85200d4a8103000b4028110004c4c140603505903040c1503400b80403001c1404911920798002d280d5001c04500c20340781d46800d1100d20090205803816950580d036000c26607420310540711801d8000800c215481040386180081a15100030340b1441207100b900d07069142e4204a51074403800507110710000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 212838534 1250 212837284 212837299
    0x5010819080d27060207030324030b100302150409110307080403140c0d0905030738040816050301050703050402010c030c060f021b010c0207030c1a0706050f0403020606 74
    0x8001c03400348800c40308031541c0803070001a401480c448104407030a00c441d40c03d0021040541c10010710015400920f0100d200c3c1d642040440040d00c00c0c03071541a0311034284c0200c2003e5000910005d2207106a05402504500214004544c1ca40c0000c2241c0d40302000e0543c0f0004c04501005215440d0141f0380704903442c0c840641c218506940300800c0050000e00281c100045002804400c9846804942c0940240007c6d585c140d00e803154098003812851007828020301c40c0200028164003061032410403c02c90108030a000324201510840406202824255400e420403001510b40400c01450132114400e42c0e03200c03100341c6010201421039a0042405090604203000c1000503030384078031000080d50303140c00e01d80012030260504a00030030000035043d640a1000958400c20303803040c0300a40303516442c0310003071200f0085001c00300c1e16555a40b10040c01c41504000c10b0143d090b0011200c4181400075030300c2414080702e600ca8005480f000c5da210224001000140014140d0500805134403038020703501c0b0b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 212839784 1250 212838534 212838583
    0x1303060f0c0503192d020c0601060503010b041404111b0601051c1e02100c051e03090108090c0312071103010c35091f0b09070c06140a050108 62
    0x41c220340400d40d0a00610b9944851880221070310700d41700540900c0f00c40f0901503561350b030320b12070340298040501c4c001030b440380c00c0000440510480840303044c1e03a400071b440341c10b0074030f8440820403044c1552794450703010751100c80b802010001d0202800d440a000180b18298076214906070b0b0038a6010f070441c60003440c0e01c62a0300014070480401c4034070709500c11684011401c1100d103005500020480096000c1d1041380c180c1c0c1c60301d41c4840008802c0c0d0103001507440c402902c0f0142c0c840700202c040807961079001841240815800384412540c041044025034103002a40000242008a0451600400103000c01e06c12300b4022103048480381b03540260b0003042125241007016140380049840b8081c9450003a4800c84030001603001e070407040d103d050303121000b428440c01454982c1c1e88604002802e008816401c2c528001c6402038034140400507210800d20f80314140c0484018114410039118142c0361903000c041c4801e00c0c60000e01c07618942d840041d482d41808103480c02c0c0410207a1010540c0c2c10010341 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 212841034 1250 212839784 212839801
    0xc1a04050a02060d0b090f06010306090203060d030f0c0507080102030a0e030c0601090c0c0c0905160c0b0112061409060115020111030c1e0c0c01022a12031303060f0c0503 75
    0x1240c40c007580407101d00d0b445844560740788015103089504c4d56000410041408014520741c20b00c180100400d88050000d030740c0361071000c412170004039000750340200c2c1440c0410100c1d010b40d495808014981c03400d0007c2120548403680b03400d1441c0d1045030f01b60341c00010085111414458040119007440c007841c900b0045650156403044107020307108200d41d461441008060144802d044029480024000039643d5943c0b610020082101d458520528900d45070380100c4c070030360441d103e043e0301c280070001690030178041a03e0542c040308202c401c43e070395076070311380b90ac40c203103203040e03125460701c1c00240303032030f40c100f4160000d1810300004080a42e8105620800500b1000303040d2940580805009138854030410f00683c4100248074424010001c00510307074803c0c007000b04281d000d11600b80c00b00d58200025003155010390b42900002604500000d45102c00c0c0d182c410b0405c40703840b40d03220031a030030100400103400d602003c0c2c0c0c0c003c035049603a0715184100f00885001b880902c4906003483d80c19850711400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 212842284 1250 212841034 212841043
    0x151306050f0d0c021f0f050a090b01090504020d080c061009051e040501150602030a03061e03060207050c100c050f0d020d110709110c100b030c0103020903010b100c1a0405 75
    0x2410380c101601c5840c0821003130710030080918402c5010b03074181609042500c041c03006100d00400d403200e29060030000341441600e401007110562b44510106030300d030f1804000c18002c000290089038040c0340502a5008640c4110107440d24820310b00c0903051904015015210b5150142d219120345400e01080080e42c90070000c408640007802c01061000340d5440c502a8014807010407540004031040304040783e0b003940080500885012510104401c81c0c58400c90800044001e008940d052049081400014520340140c510369200c0c0c0110b0f010311181d9130001e400744021005000000d010b90100d5400e000c0100100751a01c0d00044c00b5002488960100a44030340e001d00320802801455191404680e90812402e030080220400412581c40101e01e03005150b0302070340c50550f85100e1208030583c06155440b5000e00d1b088010001c2c01600c5203c0c0054000c1d411805003140d040d583c6e400c4144594440c1c0c00080007d1441eaa200b0052052031f141010350040e000ca80c1c500008554400c000001c0c80025 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 212843534 1250 212842284 212842297
    0x806031b06090612160e030d0e06070f0b1f030b16090b04090b0a14031b04020d09060509010c0f0503010e04141603121b11030a02151306050f 62
    0x100c4034480490500c02141d075610481c0e0426030401d8001800c0d0b0200884007402c41d0080883c0760030b00402404090007128801070709089550f240d0403408000403c140580c0d41c8420039180902424105000d41d01c2e402c2c40291081015030300c11038218200070400d12945403030380ca6002440c040170001d030f08517298103407446801054010f0b0590040c9c2d440a015004500d800001e1164000f40c0f59201d4a806164002e000c031940c03907a0003240352078004602c0100d007003401d01010360050014100101c0d90701e074412001c9096408240c00940c00c02010204500742d02800c844136006110200381824504a0745085849051903a410041011700c00c8013981d5000c2c04a0341141d02040c03000c0391640302ea05066843e2040490a0380b1248aa4901039040040d079000b00c1084034005c000c008006543c541d02601c0d0003880c0e03034211403525401c003030a4000807016048600ca02ca070140459a01d61840c0e4049100d13010889412f01075900003282c2c0c0c90302c00341c4020181003c0d00c882d24005041000e0040f42c100b46000c0c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 212844784 1250 212843534 212843563
    0x10807052a1e0106050f01050c0d140c010e0325080301090902010e180403080a020a0504030206160501090317060f1003050a090803070c060b06131e03081216080603 72
    0x503859000000410031020081c66015007108101082e5400307518000c2110348299402013a10460910440d8050410b80d90b0f078421500103000c4050b0401011036800e0861241c490400205201c0c0040d80b0200f407181008802201c0011076880401354a11052101002803400740e8007804002c60700000e00203800c1e681141c090769400b29000d01d0314401a02d11210304180310381c0014001da5101030b0036202000007030189000381c40b600c1003074494800d60b41c00e13485828001000b04100300410401821700308010000f055030f41d81c15000e01e4a0b940e8546094440b461029000240503018840071000785004040d00541c0856858074400417040115007030040c40c1c18200149a55403000641d042c2c007503005880103039807000880d40d4906d8916070240c13811000e5002900c1312480c1101d824414205181121031400b510101020301c3c0380340c16030a244c0d242c800220210301d400065800400109880042c0c0820698181c1d00d01c006e207040003607004140b401c81181410421600144291034030b021807141d0f0b02d007140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 212846034 1250 212844784 212844847
    0x310060822171e040603050f0f06120102040f08030c0709050103020d020405060d05060a02181503011502030d020307021f1401030813080307060902010807080906190f0c0c0201080705 80
    0x40c505400072801410480c1558402ea003012440f4840b26038003c0c000c0c0d0310662020025602e50b408901c21911044a41f014040c03007140c04140c0c18549529110079014034071001524103030b15410704d4508401140d005400507800840e003044052414010034010300000c4004000562550300000e0070f0011414010740aa03686902040b0796850340010900d0054104c000c45109041a4404100950045405d1241460b80f01131480b220724103881049070107001c0e08000303415a401c1520400c18441305100b20341c00d5100c100800030031396981d4005180300310f14540141185244d01c2503070300c2d00c19407116400d00c46c6a00d0000c02c01c1d002c5161600b21810360707401c1540350b9120411040c0d09180840780b078002030710340c0c800861080100300d0a5007042007111b03c03c0e66100b01070344a00c40d041c1e07080d07401500c0d03400f119001200025001103800340940702e000705005001c02d403c0c5400513003004980521020400180a00e0030203025560480907068000d05507141081ca0514801e2141288031411680c1c070510452 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 212847284 1250 212846034 212846063
    0xc031506010f200a0c05030f0303150a031a0604150510031a06070b01170109031704020307030c080d17101404140c1306050a0e0418080310060822 64
    0x4624a2214078040c02032100c0b015101207100140d0b01c14244d801280c00312210707080032980b4100441c2c2120b030714500600440c1107882e05154104007404440c1c506410190480c0004013090800c49401281e1103046024080d9040030810710083d20311445210116a2948501f00a10303140c496200c4624a558680007540288800da0100728400160110342d10120200b43c640510090a680754100e0b034a2800419880d0340a55104d07080c1e622441000d80410031010320651042401c07500194083d02c02000e0b120f0881e200da5030b28040a0035074210a110340e01c1440c140701d40d590000f124a0500e91480d040320103d01e800801c045d60110f880c0070321002502e0401c0c1d4600b00e92502d402070b4100c12021111030981d0311342100407690b25049000625021000500d000800d180201e0480311a01d1450751032280c158004010701000d060700140080d0600f400036000004119144c0185024031191210414054030b07224000b800341c9006014000c000109518520310702c007145020303030314072035002103401d00115 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 212848534 1250 212847284 212847287
    0x702210c0301020717221e08010902010905090a020c0303070c0209130c0621091b0e0c0d0b1c050d0f1103190513030f12050309070302010503060409230c031506010f 72
    0x51001000d0346c5001041c20200e00c10302c0b03d40005e42d80095150101d28410f035505185400e8072140540680491292202400181848204c055000c07081d2080949805070381b20b56245903602c00c5904200140c141d400080c11440c0c500e4940350041d441001003405911903442c0c0307030342a022034420303001480403244800c0000d0000c65a4080780210480017004406c0d071505240c188020500c4810910074034a080210765055040c91250203500c9a0b0503080c24003001550850003400c0c0180c11541c04038911100d9681c114405c103480e20311620400c05004c0b1002c5240c00548551818001c203003e0081010200c50614400801c0c2c80700c0041180f441d601c82e04240c18191654407840403804110206c01e6808014403421040a071049032003850985104804210101c070785010035a180980340d0810001000550301c01c001960704050300800001e20b1000542c0c4800341c1510303c02d41c2068003910b040c0c3c0d085058800f070060403507040040d405071040280002d0001030043d00101114140203081c501e9202d803d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 212849784 1250 212848534 212848567
    0x2c04110a05220c110708061e0106021f0612200a06120207020d08030a05010614030103050d030b0109091505090601110a0b04030509060703110628110702210c0301020717 74
    0x4c0d200103040d03a200503140c40000c0e0310b550048880030071031079021700d210702e4600c0c0c600c0c25681250025400b400d5200c00b10001c1c025501402c4614888203510f030b010100d07804d041801000320203840f442c144203907442c0b8401205141201e041d070035440b41701c40c0d003010040c981e0051212038541e0004440103a54074510b10029041030306100e00501102c0d0007104020801649612a6040e07850340e403502103080e05183c00321031161100f40801403580d0031080020030501d000c0d8200c0031600c14141008202c41c0d0302d48841c0422222052444040132101c4c501c100a5030078800c2c00150042000c0c40c1c1000c91110501c0500e90380c0d60544002054002948006030030702d40b28030141d500411009010b9a50f134105418000d04429003103004011a000f500c0c003203240000d65107140b5900000c181c4c201d0022441c0c400003d80200708601d45180e080404004240040c1d07506030003510b82e031100280c1d2458141001c403401e844c0c800036040d4940a68410402000811414018040070002541c2c54076680d40416292404c80d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 212851034 1250 212849784 212849807
    0x30c050421150c021e010b150c1507020a02190b090d0303020705010c030525020715030603080f3123040e0c01020c04090c2c04110a05220c 61
    0x401c0e00d004420520780b5404507081c00d13042008404c1c003a5a580a0050a01f02e0f400c681c6200d6100e40020071207103016011a0280249400110548101040345c0207060030014003118100c006030410090700c400c6250602c241110f040d1850011140242040488040b51186447c0c0c0c500c5440740a01c0e42003018803c0c0c045891040d8400b009000d104d140e800c000d0080d103420f554074860210f01c0c840f500c02c401c005c0c1c0d242106480455001708207440c5071000203500c165a95a117101055101c0e08080003048581005050144006600d65030b110307050f0090051014070040303020484854501070031044440d245070308094030f91000b1119855085020410311514031b07000301d00e4001c0e0034841001c0350f080000c51020803041081c0c003034440681c02c40c001c08c0200d61004000400d480240c0405004095901c0070400882104d40350b24000c901402402c9801003608440880f5505040c0c02031444900307042d2989001860280c814485040101241041c800d10350007000c400196103e002c611414441ca911910 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 212852284 1250 212851034 212851073
    0x3030c16050a08071b050301090215030916170610030819050912010b0103061409040b0411120303060406091806050619060e030606180714070b01060e01030c050421 72
    0x81d10b02c241c0c504179aa900041c0c0d2100583c1da401743c80042c0d2400c0c180507026055130b00a09504070310724900c049000e9500080c224100324424441804070700c00040b1036040241c07201800380e02c500645c3c203d80510f0110014050320070150718400400c002000002a5101b5403038001d407808070140614811901c5000c0d400083c2e61040c03448a000c076081c3da066002a000e43d03000e80e401d0103000d132580b0004840c03882500d4450340040d090400200070516000c4680d401910034400f0061040c0d008000844c0c054980e83c401104da0000418005186000e01c0f40f1401000c5500c001d02240260768051054802d00001c09007000c2e23210000108540d6070001080300020700d402184c031019448280c0140801811920503000e0311403200072031030600e0070170423070300d02c60051464a501a9031000b00880324075494890395980c2c400c0c1480441d000464100701c940c0030300b205558662854403604001015584400701102c00d0200401041c407908011441d07e40e4a02c0b02103503070040e03d40161031701a284500c0c44e1482c60 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 212853534 1250 212852284 212852287
    0x3061a040203160e06030106090e090c0d0305040602070807030f0305090307090e07090f180807080d021605150103052d01050a050f1e01050d110d0302030901090803030c16050a08 78
    0x595981c41041c071010103880d9881e0b04d603003480e0b0428050365200a00030480441c01c00c1004200c0307140c814174104d5000d1040802e8650302d6191001007510000c06040440110301c011030203202c9140c5c1000040000c045100040c40483d2540e11038a0b4007601080c3c01074200107001030808240c2c0c0302040720000507c24144104000c42c10f00b041151500a40e00074412000d08084c00300c0403d580d2400345c0d00301215074a0401002413607640d6444110350080504603071550045c030184030024a1440581b2000c100110910400700c0245090b9003448140800145803001200040c000718a0004480b913094403600341c2d06554001c01ca80030f500c80c0e02c5a0203140a29030a0000b00a011078030b6400c5140100a000a014141c0c0c9030f030f881d07092000c132004000340c5827a600e81c401040300b8604a400a200386000f9a007940445032940c0119604503001d40e81900983d000007a025015648000d0380c2008180c4d6401441c1035090034140c04010340b048407003609407000685585c01c24800c050101ca06182e0f030000b0801d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 212854784 1250 212853534 212853541
    0x31b060e01030b281401050403020a05090907031707060509030a08011502030f0f0a090f0b0313030e100801030b1302010207030b040515010e100b030103030c0f0c1a03090705120703061a040203 84
    0x3664a890356004040f0750300000c00c603070700030365000d80d003648d0a40707600401c81010541001c1c00d005100c13030010080455441580c3c00040400c0b08103205080011050742380690720109801c0c050240d40f0040c2485130f017513008100701c1c41500e501c0400340b0305488420780d02e0900c1d460f010400724030b58061801408811040050312103601c0031007400914160f40b0300c0c3c9610072866514401c0e40060325082c8030310109220200005070b554120a86c4841c41c0768864184620382c04050004100d640c04040a5080414803000c018818452030b18086035110030f8080c4e5003010311507a07600003034407070606200080042002601040c00c00c80140007041c2038498100580c0310710b40c0c0d240044118500b040d105900d07600501900400c0c802030600469059030342603111910081c010b552840f0204440441c10342c1c4c11900a0400b041c0642d481c001078000c8011880c00700d0300c3e81400f51440381421625031081d4403c60b620011114903090100b02c8004913074204a001644103444405850089201032241c3e40c0280b000042 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 212856034 1250 212854784 212854849
    0x30409020c031201060206060105071e1406100e1b030a0209030d081f14060d0608030d020d06050f0108061203090d0804030b09070b03150409020d0309031b060e01030b 73
    0x5080c1140c1c3d188842c1e0a240d0740c6a0041e80c46150541e0590300060b002c1290310b0200e030f148100d8404010351a28400b4a52006072a0040240804804a8015040318003880207052030803502078003810380c10086c2181303800d00040507490326007a100300c82c2c210003001c00054409a90785d415a0b80c00d82001e03050740c8108110f048001c20340c020440d403443e440310f4402030b50b4201d0010304141754103031038154200c0c0002c1d2500004100a40d0006002c42030007503100d440c0440c17880e10510140012001c030003005078039103d4145102c0241d400582003640940381c2c60308014440d0703078001900c40c0c2020080d00c402d09481d02c6c3c410316508611076209019086040b40b60a50100800f0f900100101ca00401c1083c640d61500c0490365151280391095802c204c8040c00030480790203000c6c00000d6882401440055401c1085c3e0114011450041c801d40200310f140004006001a40c02464880008030131400700450030807002421810b400b2164a04156487e0300203403881c0c0f0399000072040d210b80c0d00320040301d0121071044d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 212857284 1250 212856034 212856037
    0x415090306180309090507020a17130e0a0b030f031219020301060e1003090f020f03100509030301030c050a0303050a03180b24030d0905120c090a09050601060c0b06040e030409020c03 80
    0x4201e00040d0744d0040000e41c4c80b42e07889218003860055011740b10b079800d2600c0d10110500754501c21000703036504000034070008659000700c00040c80381000a003c6490704c0c025a10884509035401d60283c2c004440459040301e01100301c1720700d60003114072001240c8a4801100108810034900484a0700c00000883c1d00c40c1c000103015600301c02100d4070030804070100303400ca0603215050390003070000e051400341d8001450404035017020b604014084888003841c10f00084141c9070f041c1c502c000175820001c014130500803d4604403000d40029940c0406070391455600620510498984070109a43c810360145004621034601c2001504003001d0a01c605244440d40c51020169456503d203020350301d4012190306012130746218120803074076440c070214600024084804141685100c49028440680b00070740d81d40343c0501e02a041e14040040d00c1e42d001c0c542039151043c103801c0b0304140401051402c1c00680840000b03a03000c8c0b01030382e01140d503c55411a40d440c40c0241e401c28415903001096881000c0300000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 212858534 1250 212857284 212857331
    0x170a060b0a0c0c060c330f0617030307090b18040c030506010905040e03040611100e070305071d04081804020409020c100204050904030804050a020d03170a050c0415090306 75
    0x41943c1c6101c0e9110016201840a00d8004014411580c852020156030300490b1111401303140c803040c0311149000d40c03601180c03010420500300585d00c803401e021200c0303900b903e05404a1000f004500d1400e1955000c1c080040c2441902c09032440082d050702d11041085101c03003050000b5009000340110100081c2c05840100c07600f42c00102d0009002540781340c203001d200004e0442002861400c2d003404402c03a10702400f803550ba400340c815607041c0300400c005440389200081034100500340d95400c40c07808a040101982c403960201c800703501c5035080550031010700c03604991b10022659580408804404500d42456070440d4003d20126001603911015002000040d2441d000d55420300240690070381280154004daa400071300d04400500040e004082040d0010f00035011286080001d600003070307050303090700c2044000802d50300c1c01c0200c40c8003051545400605021003808640b5094005400364022841900c10035800b002c848a0076501600c10000a1074000300140904804500341d40c200e00320b0300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 212859784 1250 212858534 212858543
    0x20405040507021209150712030905060f010509070c0f12020c0a1a07062301030f060507020d0c12030608030706060333020d0209040e0d110c01170a060b0a0c 69
    0xa000400e00b52000c02d0780c03a00c20030075032882401d003035000e01400b0386411250b51000c0006410042ca0010035043d1014560f030311019036011441071500d00c0c1213410010044e00806004039800300600c121b41e546c00407e80e00820900d81801d00c0c40304ca042644100c100c00002400724180c1918444060380d0205a090000005442c20070071103a448507c10407414000d2020030700740c00c05000340b000082d17075500b207c807100d010000d100b0708800741000383c10007840b000e80c0f048a2020130844c20204102c1c1d00d00500c0c7c4c0c88800382c0090300792007500080107001003000c210000c00c40c200d031540c5c401c280b601a0b44024080c0c2000d0307003220303201d28031840c2640c020022800705591050700c02d5030400c4041e074200780b00003000c20b90481d04104010f47c2c501d207101942083c0318064040340c0074841c1680f60b44441c4076129280340c044004201d14144004090102c94201d03495828641045030211081e0740c102480c04a94440030280c41c28650b20601d2000007020650016501500f001403001811940607404a200e02c2c0078 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 212861034 1250 212859784 212859791
    0xb060a021507020f06160c1a040c091e090c0f1e140619170403080411030106140105070501060b220602010c1b05072c01140105270d0602040504 63
    0x1e80c24140d13503030301000b00091940c1e404100060582c4840b201c807410b81015074103000102c1c5031603507200c000441c400a400c80700340d0056420071041c030012003080c0d0000d2041e0407082003006a40308601940c0741c280f495450325241ca80325200308000c444a4081c0050080e00107221085440702d004024544001e2404558107200f202c0c0490b021011001c03004000e0b03001891030f4030381144004030f420140c0c4000942001d01410101c94610700c0500030301184190f209076101c0d01c681c503203454412100d8445840c0740b030290303142076030501c0207688410b90441082000d0078059255490380c60000e01506454212210b0f5400225039041c2101215100154094000030005031141e21500700f2400c807801d282c242800503c0c59425955031004081c1405940b0340181d040c2d5409586070020000751180c0e03030a090020b28001c7c2c40c450b00b00901d1032040d030702500e00c80c2c00203414081c403140005c10302e02400b1050990904010441c51800085400315124140c0203481e200c00741c400c6081c91350007074000740300d5a40901d04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 212862284 1250 212861034 212861041
    0x2120d0c02280e040501060305030a030207120c11060714011b021c080604110d06080d0e040915051e0c0a080108061003031103040519032f01120b060a0215 68
    0x8804500c200d5040b1100a6650340d1074a607441c1d00104014006641556849401002148052004051039481520056035407803075445c0841503119060170701d10410914885020001e40b5080305144001e808880c040e80b10041410603203401d04002c42c0c241c000b5842e0503040c10f59607603114064440c2c58420740a981405a0091314080c454420f15080c5002540c8080064007034034160303100303044c030440a110f4141450000140340040300e019800881035a400401410b562686c054807194a64005503002e003e100002c0c1d032068140102080107500c000c0e128400224040801c2c0305110441d0026001c103041410045200d243d00da10080d00100040e4408001199003400000d10340d019120208182504502c0e584044802060140108103240420440050955150700c00117654030310b138406983c1c01918600d010f4640e00d0800829601caa82d19042001215072043c040c000400001e0901c030b860000d04650a8006040b8084840c4c0e014030082101c00546600040007111041020980d280c20b86 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 212863534 1250 212862284 212862319
    0x207080709140606030f0106080705091008060405150607020d0201140a030905070b03160f11030403060f0e060c0d0c0315180c030e0a17190215060a0e06090402120d0c02 74
    0x11085840d5106c041c0f140e00100840c074400c254482c0e00c840645051410420110001a4146050540d010001d0044400c3c071a4900d481d115064002d0146600250ba0810b0080814000e029012000e0310510100b01544196401950100440c140311480c072982c41e1140200540100240da00641761489080342c049104d4060804503800f41c1050300c0040d88060215400b1030308138000549603410003201070003a01041c1000c2025101541c41400b002c102481300e128500100c40400c0d0300c0c0c42d099400728080c488081502401c540c0901802c8001007140e5502c0da005078041c00c0250208500050f03a40d000041c94019014811080c42d50f20b030042c02072095100d0114192155035407100441c0d000042e801000a80d40300d01d101d145204040c0090900c25020489031914120040e5031025800c24034171a0b400ca409242807952014044554040d0581001803d140b0b2038801401c20b801142c02c0c0380820700b50f40d13521203820035101c0c1c11812540d46100c0b0b400c00a11881140701c0032805011948a04044103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 212864784 1250 212863534 212863537
    0x43b01360b0406050604060b0c030a120c0f1812030f030c0306050108010506070c0b070803060a08030c030a1103070501110c0706081302040b0105160b04020a0b0a0e100207080709140606 81
    0x5600003900641580b25603c5a5004140140c6900d42c050f548480004403910144007030400c00c887c041c082c503114003d03c00050302c1d281810104001d1103192241030700354117070000d114240f00f40d41071405060143d680d001e03051800c165a007000c601300b0194100d040405520094299509425603401d01080400034000d80070b5810318041c031408241290014050b5090035409441e03211f021340240300c083c9944034800b040641c400c5000b07440302100002080b203035050032803141004040240003580307401281f680312522801140e0441081040140081046010400558842c19080b5008020010000322400500c1d40500d108451500440100080550141c040c09105418480d00c07007004004503030811000701005c0b21098140102405040d000d00c00d04018042d180e841034030011240e003441e004109004680d80e1112090807810000010305640c80484105030200a50b40f61301d038002c00010603800d12265821002042c40786110004910000b5007088803085480e000b403c05e191a28420712100307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 212866034 1250 212864784 212864891
    0x170408091f0f030c030f02130f120f02040f061e170106081e190f05010b04020702010f2a05060f06030309060a050a0314010b09030c043b01 61
    0x22a1118903295030b00d40c007940200160040c5450b001452150201c1000300300d0b0803044a190480c01a038000b8406085080b84060180c0070000c00c10840001c00ea90701480c0c4422001d000740603d482d64085860243c260b04420060103040141c41d244e0300c0213038400d412900043c0309400d00503c0800104e4800d8034184250030655541c0300c090100416030290044503a1800c007440b100c01e21428825204a12184210400035407107000c0850511206040080c00c2d118003024503813103944104080300c0181c0c2c0240000c500d002d00d5080c90302e0381540380c08140060309025103440c1004d60b1082c919404001000c900948107a07000d0007005100d80f10241415070760f00136241c89540000e0304000044c9454010000f8100260f410b283c0824075125045088807800000c1c1d00840d00500085841e0716103240512081c0e0414800303480030000014006181c1407040c91a2000c54512280400c01c020038a000e190040c42c2c4000e40710080c000c8500c19541c40251208081c88070f8506040211100344940c29418003440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 212867284 1250 212866034 212866037
    0x3120a0608030f0c0c150705010501061404051e09070908070b030105150d060504063209150118080a03080906040515071b060b0f0a050a0b030403170408091f 69
    0x34910b00d1240100594001100404130b0b10654020303801d9a51120241550741c0c4280088685030030061810700c0c06c2d654107030440024050480e2001469001050954045850803500141c480c0c6614201c200c420320300c1c00e440c54000740d2070010441c000780c105400e44100c40e031910440399610303601c10501040d808207010396544246c00300d60b05010384081c10090241124059000240d60b591540001c040f40e41c1d5078030004000c4150b881130050781110000ca00703036400001000c540101c6540b00007880009000340f0042171100000d07218000340e4407078116804030710010b6540810458a40c00100d40d5410026421000141d0803030024180c2440458800c0c020b0b03134810020100c8106000000c064140000d1000041100c0c0d1900c030410070b83d00000d40760540740200c0303001400001784003d00607680d1592803900d00808030580c082010307454640f0300340112a5800502038480d00c0da0f1400301c82d50780300e0844039248032903554140800e100d00f1100400300b10310f0888002c00151180000e00c0d801c41d041e00350410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 212868534 1250 212867284 212867287
    0x61b020c1005070c1814070302130608070c02040501030c0509070f080103021e060316080105010309050705040c03090b04300e0108100f1211010819020f0706020c03120a060803 77
    0x3850280520b01924207144104100401c1a84414038030761031149070b80705250142c0e01d500500072041d00b2540706542000c894038081d40341481401d040030300c401481c4108000c2103048400205420721900c600000150300400500041d6960f080a200c442c04074062640310b41110404201c1c1140200417801b8060740c1a160203c01307070310f1502040b061501207405540c6a1500071541d00704c03551100b0081d48504042c070340c035441d004650440240543e00503000706050501d440301182c041400041d440c0103e078801c0714003003266490320204030f010b4092010010008201e081c144004c0114585004100c1d41c82d98003074044d402d01c20608a01c1e540104442134010840401c1d10b00040e521a9866550282c80861001c8603da070300c00300091548541d5014602000f00611054100103c103030140c4540c2c0001d28107070180c2d00f00045416400c5d52014041d2803407641c0000c00001000141003a50768094102e4011034450150400d40c40d00e941c804940012503841c0800012507403282c40c860b541c10390718514002c4d07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 212869784 1250 212868534 212868559
    0xc01090f090f1d0607031505150f070f1a0604200a110f01060e0a0203091911090708060f03011b0507020a0f060215010f060c03051b0a061b020c 63
    0x1100601c402d0000c0070100c1d031180c0c0f010902c1070100c1c0d16040c00c014040000d0180b0b191085005085a245140c101e450f000300d400e041080d82d6401c07a0449950408540e0b8a03507419104c0c1c04c080081c070480303000074000c42c00c00c2c2c0c4100c2800302e81000044100701c030002580040c1da81204001c100d9001c6072941c50a5510680d80c507c00301e011801402e060b070310703038104116070400c0070058525002c3d40d42ca00420b181e460700c43c14000b80f4145601290040d00c07000055045040107201c0b41d49410741000f58051000c01034900340c0c1404140f40300842c4036070018003102d269040080c0000e029040440314a0300805408602d020786040510a280e2400007080461042c07080a03002100c555104e00d0007640d203d00b0560000c2000e41c0d80c027074050001c2000d81c0043c075100c000c0042806254505a000240c46c41019800f040480d81003000300c42040e07414a4015555142a070400714400e00000800119220b801072010401156500c4221403000011030340c6481941d8800403079036070415043c004e400012401c1217 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 212871034 1250 212869784 212869799
    0xc03010303020a0b0613050103081e07081e0403080a02101a09060405060a08030309010606030b191202010507080310030501060b0408031b070b0c15130302061603021e0702030c01090f 80
    0x10180c020740e0051040c0740aa03503132043c5000f030302d0027a04151041400001c2c0100304016000e41411001107024640d41040d506851350a41c1e4001c050b404812500e02a440c02c0300400d48004440c003569105540a440d1142c0c403000030360346c011031401c0480e02c91601c202d2504504c4900050522079100401602d025550b07a010311010b804045d100c10340001400700e001c5264242440914030035441e600000a440d454500024192404000100c0c0580d01010850754042884004802175618201e042c841e10100c071310040300c07948260380b00505011404424803140c113100b69111700850740168024445552100c90380c210a10440c030451115600400c0b15407090052140b00100800c7c034002a50f038a1a507521010510313500001c1c41d030400d900301c0c1000d90700c40051f419091343c1042032128040c00491595030f001e50717528030150080b00c00c0030b850001ca01c0c440d88250101d03865611001c24007003041d6612156100740760001e0100300c5c480c1c010046441141c1d4401c2043c441202d00600902103018540307800e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 212872284 1250 212871034 212871053
    0x60509130b1518030705090c0a05070f0f05012a1b05030f041e0e010b090616210201050a0b061603050904052e06020c101b050304030b0c03010303020a 66
    0x40560410652030a0040100071540a000c40d1031100d40c0c64240d4004050800d81840402e4019611a080d1802805107041c00a001da9001104908055950f1007203800d001c4480380b50404010810391500c494dd40810030103420061410402658040c41c0480c1c0301440f0800750394040c160000688404c10546d104141802140311803801601940c0c0b030030114090700303043c5074000e80106200f01c1e14440c011070090080402d81000b40001440002c281d4180a070119851051403100c0b4410030001c01c2069540c00c3c207001c2102c600b607101410200d2400361800000d0b01c1c00703201800c10b015500e03000015403408220300035a03004c850000c0041e450101000307072070500e44180100643c2002800e0010030b5550b101c3d80b2409002e101c0c821018500592010070504904c001c259401e0181d4141420810a00c1c0c0c0003d20b0009105085600e80b90080e605182212610084180410032643c446058410701c91b011000f00180c90050400c5140307a5180040908544001e01c80240181e00140045000c500c1210 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 212873534 1250 212872284 212872301
    0x30a150c050409060b0a080901060302030a240f0509011a0916020f0105090703140102070c0603110d0911010201060807030c030303150806040507060e04090804050909011b0e040606050913 82
    0x14510b003001c1c1c40307440003400c90f401d0b50003804544000080c1001c170380750402003c41d40b02400c007000b4441c15086502083e00c0d054282402040c4814a01d00400325104006600400f0400e2903c204012260b41c031049000c1c1500b503451102c25407800c407501c2d8101c009102c02c55441c10021788620440d0b1240d0741704c1070b5040c00d6030401d00114040e101080900300e07401e024040c00b48a61300010b080d06411400e0411038080032020325510b5030f00c10020f01c000201586c1002044986a04000400d13079070f03c03440d0521610038070b60180c000341d140c01c020704e0403c81c1e00039281000a1080c3d000304041d5841d0304d400b559990150101928904115004000003072294121003050480d801d42201c00603078914400749809410b43c0c048403d80c01c0b14006112a90b0322103140e129110003101c061012a1864940f51010301c20340c0101400349248400090401c0c00075000490400b4142340b9040480001312170080540b8480030341d2a01c26810300d0b0000543c144244240d801265000704a003281c00c41d45440003000341b0120 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 212874784 1250 212873534 212873537
    0x72409050723031c0e01050a17061c06090b090a051b0103150b0a0f0509010c0201120905120d151802090d120504030302060a0608031903060302061b010506030a150c 72
    0x308510b03040d5201440304100411006242c0928405101d002900300e04a10f240a41080402d000000502c0d9102c00740d1540950f516210744e07280d48070440481d61150408a1089184074110701500c10082c0f03640c440442c40d40151540303099034544415040e2140001c1c000607100da0b000346c9007040c51a1008520b802c401005050025021306865480d00907001c440d80146c40303900c1c011900f00292a040303a82049904958500645085040780002c0c080c00100f500281c10001c0041c4092090310465000e1410b4507000003c45600f9081c0740007076039640d80006000407090b41407c41140c1d84110310503440303041c3d03900d0803001c1e1130020300400c41030300a40041c0c100b1903002030444154004944544072000000482c0d542d8180d4560035410302a1500c040a003013030742400c1c0303414000c01540c2804401c0d02c154031658440d100080c20051000c40143c45150400b81d8060b00024034040b108031500c002c0310300700e42054000d010a6035410105910350301d1022001d005070340c440541c0e01c030005c115401001e294585 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 212876034 1250 212874784 212874839
    0x60d020d060909020118030302060115200303010513060803030f090c2806080903030103080a141810030c0e090604060914060f0d050307080a030609020724090507 71
    0x4890044055900076441907140c160f96031011029940d00140700d20440f10016003010b80b051850382c000359610380500c0760340c880c18546440b0940700c1c2d10034040c0848080400c40708a403050102c210241d1698000e11070203114442d02100e0408242080c0035100072112480c02075811542c8001e0801007081c0300034040c01e01d074058049812600d40e5440840094140603991000101c04009000308250741175800c41070601000000b0840c0000002007100c0c1543c0c0d002e40c100d0384903402034006950505542815560fa98000715070610324004202d950404104122400300c8412a000c0c0180c00b25047c0042100004c1c80c0f036054a0102d0510380c10f00b640000026000095003541c410440f401c454070081740d41d02c1c10403580180607403898190380c440d0a0300c00803142d86040e50041d940b655079920926000401c1d4510114600707000d2030007640400010131441c5001e650361115484d00e4840b4101b405404159004041186501da44440c0305189032554000c000b0b09030141032490710320410704c0d101000341c2d03503100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 212877284 1250 212876034 212876047
    0x6090f0b1308030a021005010b0c0604060c022b02070b190c1502070602040503010c09180b04092406140609010c02040617030d05011208030a0c020a0605240d080405060d02 75
    0x8080009080d0213141e58040d00d03000071900320010980d241039110402d214824455020080c40215a0076000703030340940c00294445203070034281e04142040750152008c0640c0710300b42807820114402c030907101c00540e0a07207480365100c0b0b09502c1c450045c03a11641c01703180ac05802c1410780d40190b81d54007081c1e000c0d5184231312503808080040260307401400111113a64010408000508090080c80f03000c18050401c900b07000d051200010082502d07080580400e504c4008141440c2c807994041507043e500038002c20407144960300c0032044203103c0c103482d250300c034901040003480d508181c840c0800100010041c600d8807040d14011950410004010b90384240e503140f0003c0e101220141503c22035080030b020f0b68490700309032104412980305038004049a00328144540c0012894400c40b0342c0024a00400584c4901c0300030304a00e00601c000380100001c0ca410140f00e14922070a070500600881e40400c038402200003000d000b40c80b405040020070302c0c0e105100078021031610101030006d01402c0b0400505040d07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 212878534 1250 212877284 212877299
    0x100801030803040615080109031103091503130b0f1602060705030c0c0c060d0b0a0608070504090903030207050f030c010e0c030726030d150b0309061b070209040c05010906090f0b13 79
    0x16080e40305a1b0160354600d504810541c104021410003201c0d11b001d94249024200460000800b0455030002d4107000000203080c1010b003c100310603590440e545c1c042c140b80107003001030b0780351040d201c3e051502c010000d912070041c40011144d110b40c4455a4450440c0c403004000802900182410980d5000c0d101440c000c544526018211248066030007040e104190002d103d0348040c16007120b410014880104509160002c08032822500452400541c2110908044000b0b0091603c001c0181c00741d00d26440c0818000005032402c1c80061000b040103076a11402070303a40d94280c9600300d425070080d0008000f01e0345180c3c182014130508220400b40d420b051500c09003140e01454805180580e11b001d064603240e0b5405010000e00300403003406203581015412280c0e03800c0e0080c0b40e0314680031190b00e40311300c13070141c3c02c00c1e2803186901030a0700b95a410036250040119038607015142c00502300c01400a4210710030785510040765142c00540001030b05141104045a20180b02c03815001c4001d1300c00126107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 212879784 1250 212878534 212878571
    0x9240911091503010905100c081b0d0209060a0801050a09200d0603050f0105040308061c0b041104090507050916051605160b03061e031f06050406030b0403030b1008010308030406 78
    0x54890b1002e443c024422a14000071503e903442360000300020a400c10200d04040c1400d4244072500308450b54032245101038210292142010843d0003000c04a0311076103540d00062481c0c10790f1421640c0c00d440c141c803521002d04440f00612001c0c038011444c8403c19854140304c0082000850591020030416100d4071490320345003910226507804d030340d60010031062607408000b0304c2d044002181c004510032807449480304e0090b002000600400d83c02c0c008601040040c2c1840c00d2a01c1d0042c005101c0404c4da0706203251944454400c1310302500000340050b1481d500d40107030401c80f074050384030315003403548104002c030248145000488141c0715544904c0001c286c030b081d0f01401460411442035980c80e0039018000070203185103203e4000024950001115500800c981000001400f10f950f40e03461a1381c1c0d07190291009611964120b46005408401c2c403400c0845144a1fa001e514240b0030321980d102803008043d40c0b06490340001d80c68000610002e202d1000442c1c0160040401044031012150300c800c64 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 212881034 1250 212879784 212879801
    0xf0301060c0b070806010804201e0a080a02060f0d1404060207121e030c05090a0816062109020d0b150f06031014030f010924091109150301 61
    0x401c0c0c20182410030801c00880b626031000103843d05003018245840003810100000d000203104e42e20140d1800001c9410f42c04507590000001c142402d5801002c10801441c0081001240500d44200e0007040c01080007a03445a441d60151016142100101e0020826041014056050b40c1c0343e0a181001c030040c11425401039014000050380e070b102c2032a0800110b05660081c100340304e401020710968800a400300700d4000403a007004560540c00030380c12146442006070071584018482c501151002c1c001515640c0c42d54280e90f40520f01340c0300e840c162400807508009485152001011042d440c5558000d60900c43c8007810181c42c01d916a070328007402e4401207415a0340081c500c0c0c00495035140c06000202000003c1e81c0403855400c1c004480e4045000c1406a95400070400c8141500f5807410005a2174444100000f00485403517450260440220034198150140361021048403014991289004040e0b01ca0101c0f4450084041440814403004004003108440f2622040d481c0d02c0070300071720300d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 212882284 1250 212881034 212881037
    0x50613120809040c02010e06040206030a110309030a0e0607050d1803060509060907060309020f040e0703020a090f0c03061809080f0a0302030f09010b010818030409020c010207151a060903030f030106 87
    0x12a5040b00301403000b21801d50348424110380c10304281c610751540104038250403e4040d9a40c40c0c0e2592200200f001800c40c002c15011210000401c00c112400e020015201945148c2c0c0c0c0d608c030136040700f010020140915031010f0082e8000102c08405540601400140d541d10015008401d950381c0d02c2e84411208103c8d41e10307009805c01307000c00038241010b10461000d4404e45c141040220885e40104003214071070b1202c54040e5969880388200701e042080480e00540d8002e0010b0241c0e03031a600300b94090003401d02c9440390745003018207800829010780a5541a02e00c00e49680f00000007044c908000f605c9100020755010404010000f039031b05180008050262803a1805640d07400d11034200c0702502401020b00c4000e91400021004076a403003001640c1008041440210807a140040b041c11031041c2e901c03441c01c080c400200310501806c1074000d81801030141c42c1b000140b020150300d42e030503103030380980202e40d1111b40a071044091401401600030481d010702280c0c01c044036003661400c598006c0e0031100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 212883534 1250 212882284 212882287
    0x2601061a0a08060303031e2e03050c0904120302030a06030602040b040509060a080303061005160b0103110d080a11030c100b15090303070308060d0218010603060b0408070506131208 79
    0x1001d80000c001c5403c400709800440c55032030141c0b02d84600300d01c2e84110106100420010810052150300340745850914590200f400046001000840a0051008840c1801340004480c0c0c585412140c562203141c114080001280c10b060b4102c000f0350000b0201003c460341c0d040003201140492010340054001200440d40c0c0c3c50030b010406c290340070028030705881180c004e2414811403d020017941d41005041d00c0e200c52000040900356524040d01482c42e2004900c11851001c0c8600c01d0403042c100c80c0030b542038108240410040c0703d022081080c0142c48005d041000002d1148201c6005801881c0c160941c0e0030000c80640d502c3c180420304400440d00c1c2d448000261251078040c600300d007140c0d8242d134071914094080b00483d0700d03402060390160602c250302c40014195101c014605060640c0208100d0340100130000650062500b8060036002924020011036030480c9001140c06441c540001004014500310403c240f07507100d05800c1580f8980e20a000482c3d10022184400306803103410410b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 212884784 1250 212883534 212883547
    0x30201021e07170705070b0d1a01020102090307360b01020705010c0c0b07020402210118060f12080c1209030c0907081314030d02070605090105012601061a 68
    0x20940881008485401c007401003100000150350149419614201019419110801c0d03081041c1051000c1e48103075402080011000a0000d0b95401990550600f1a20055a209401c01203080b03010b1070b4401134150f40001c00900030440840c0212000c51050050f0502c06511081c158a8440020030f10261031525090400d60643c0c0600c0401c0140c4820b10349540709500c2c9861f1032116107040c0c0300303005801e41c0c00a135103010f5440710303011121104440300444001c80c030000c0c40004001424030a2009801c810010f010103d040c46c06070408a5020300101d1851b641030448600e04100402001c40e0410310411200020748803d201c40d100351103690b080c141d1500b041070241820840081200b0f441008418204182150810700041d04505041c940449811940c41c2a05806114031400074441c400404e1036412215150000c1504510505c001d0116480701c0007001d0030f9600070302603881c00c0d4840190b503411004800e0400d00d4001403c2002084c4d560703581203449000e8003080620380c2c650b000000c40c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 212886034 1250 212884784 212884807
    0x60b03151e03031209012003010e0613180302010f02090a0902032d011e030b0705031509010f0306140403050316050403020405150108090c0a060c02040e10020309060f0c0a2a03020102 80
    0x208041040740070301d85c50081c00141c1d907144088c48140501c5101c0d6481d10b011501d00e448014001c000340b0010b80c000c00c03070f1600003c01c600700e4841c2000d0440c015804d201d0402401d488a00a45d00c00000241180f880d40c4d040c0058540a500011309100c5045421040308101d0312009120b11904a00c034000c21001d94184015100c0700448141b1101945644000800018100b40707042644480b08d0310b01036444ea2681041a03c15000d4041c0710341d030100c07042001146070a8407482ca070003101e20405003000003c0f5000d28001d4171440480300540030400034400901400c0002000810741d00031490058602a280e900007070480b00140e4203441e003a01c01d0b80d014083da50300081c2054100003d04010452603e80c2d1000038038481240c080c0404001000e8040d101315200c0fa007100e6520303550b520503a040c511088058800a41081f9202d6080e445210080759007241081c3c0e4041c011b1a6a01035640740c40d5098106490004020303000d2040c911074120b02c520400d202c62119103c02c0d02c44c0c1d0000d6070342c0343d54490 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 212887284 1250 212886034 212886041
    0x3020703050d020301141c020105070308040201120c02010213050307030c0608040c15030501030b070804050a0206090307091b020d0c0c060e0a0e040615060e0f0d0302161206060b03151e0303120901 86
    0x1039071300ca145500c87c4880940e8000e810b58104560600d000304039503075a8030040f5100030851461203d16400e1070300345010260190098203510141000f0008640e645508041d600d00302840b02502000c1c105c07005224661103810030f158854001d00b0010402540c50500b56003040301e00a0100000303a0362001032041100740c0d0701a0381c200c4000d10b8907980c0342c1407075201c45840d08003001c0000e124000c0040c042c4582d03142444101c0c004c2c03c0040d0b003041031400030118210341c03a40c80c105810050041450344916980141401b1442c150483c3c0401202c07030900009441c0520b44602840d40840b0314500003900100340e60b0342e680714174400e1801141c15000b030501400c0d01d14450300140207100c81031284070380da1303200e401c0040d824140465403031840382181d05090741040340320004480501c268400101304030040070300040405104400400c0980c0c2e072070618035064003094a80310042c0742200d01e800d1381d41c50006205503542404001c0403e04141d0f500000f40345a00404a00e001d40803083d0421041d41c0c0d0a20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 212888534 1250 212887284 212887309
    0x1908010902190f1b05150106090b030a0c0903060c030207030e120a0308130c080f0d18050409170315040e01050105030c130612080304110a0f0603020703050d02030114 73
    0x1105500700381c56522200d000c950000b0b142c604001240407820340481c82110f0400d1064040307182c1a040c2610350624645a60515404200f0014401c1c00020110b1244400000b1184041e44043c15510b03800d141c40040d0071840b079407004101140c003022010a5062164000c11015600c005907103112500d00581607080c5608030303d1050030341611494041c040421006010360f45803904417001e56500180001001c06058003034a03040101401281d81c500005013100411070810440d0000d44040d2022119400c4c841c0c42c0c008001c0e080c02c07040100381402e4010001451080c01c425018503205080c800381508101c440c6500e4008444c1c1348509400d081c411144080e0101000380f00c0c070760620003c40d9076412207280d8240148e41c001c0a1603000009940840044c3c20100341c140c411541c1030400a0345a0401d031010b0b150100c2d1046500e002e171030b01c250080c0031121740000e8130b002a03141640943c002e4001140a40a0000070003d04800c41502d00c001d6001e0845920320440c00d07400d01c82840207184844 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 212889784 1250 212888534 212888549
    0x1c3009050f04060e060d02040e0a0308090f010606020705090403111c18031a0613050108012304031e020309030f030a020c1e041e0207151b050304081608190801 70
    0x90000130740c049541644100151620071103554184040307802012103928070251401088614400c0642c0005500e01842100c803c5400b0300310b13220206c508861461155001590100d0380420480c01c1c40544141d1142c00307400d040b83e091003180049410090314192100d4000b12040d1001c081d0f5410a107000c94003050060008407460556840c40c060383c80e02c3c903a25100207074020001f5159610074186224819102c10180040c0d69110500360181508150445455541041100c075900c0310001a910850b050354611440340304a0404d1120301d45144020740450004004031f00441e2810403001c0c0000f241c03500195500d210303125000b800e01003844201442140c01090401c49148401140d00c280a41210002545001200401c9620216000004c46140003140b080203000090602d4684c600e004101800860780010710801114660030108010803824000300780030402c1c08024020511142c02c01d00c4100d030080e2101e0245402c69048000214400303c181444294494030090051640 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 212891034 1250 212889784 212889791
    0x3030b272205060606070501110a0503040b0a05150112020c07080a021201050f0c130302090705030f160c0305070609022107090c05040e0712020f04050f1c3009050f04 73
    0x156840546603d00905014032505001c0b4003603091110030340c0013510500d81c0d480826903070715007a08064140e4008803401d40d040d6a24100041c40700710300f0b0060034443d8000050070641900000c3c01521141d520b10142100554240540daa4a4404020f400051302d82c000040c40701c00310070300c104205000e80c0c02e5840f803164141010b06c40000e4081840d00d4019140c001095200c034031034100104059110b07400a0741c0f005000d800d0001b000d030800300a5004044c21140111282da40d54141500c040e130b91940c28000890140c601400f0a104a018103540b52180c5e9020908080ca81c000076454044031002408451064910014203102001071034028600c00314180901120041c2c0a401d0380102d2186000c4041c1c600001403e1a00c10b4884035010b202c1c11004540310282414002c007150442d001d000d006130001024039000c0d142c041581500c0c0002641455034559080d503850904841d1032030802025140404202002c0150040682c04010340e561812001031a00b42003000034481564501e000301e14 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 212892284 1250 212891034 212891101
    0x9040b030c0114070302030c0715021504030206070c0807020402030403020f0f060402091b090405090c0f010203030105090a180f050606010905060306030d0e01020703020a09061e1203030b27 83
    0xc0050044440010000f8030340d40b01c80050900303909500c24402458a02d019101300803400940c0300c0e070410240540c9508454000740040c040c550112820b075405000750b8852000211a1885a1586032502e44030700a1141000101d0740480e0a0340c0041c2e400301d000da0000301028a0995040204c2080040e101006102c2030610707402180e0b0b1500041e10300200c4603500144074801401420840300520000780c401c01407458030100c032a845155120310248654580002042c0562000054078180d6000601402c8251201c4207414000d055031504130400340003e10308075000c540b4a8140e664001d024502820543c0341000005041a6154104c20700c500030510601449880018071020f100002d03040c404240d0307100350700607840c00e48145e000a5100e0104100420030f80c405810844c11218450041c50011034101c0040780b0b05101400743d480728081c8005070202103032090704464240c41010b00300c2d40342414089907081c544030342d42c0501d00c880449041485212040c00812440c108030200055001c000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 212893534 1250 212892284 212892287
    0xf1d0708060d140a03080901110c070b07051c030203010806010f032109120609110301090201050f09060d050103050f0f010c12050408130e010602010e01020a120c0e120309040b030c01 80
    0x4050050350250500d00c42003020801e0140032009580400c904603a40c04c51145401460104202c0c0c1003c025420134295580100051058981d6060000090a06107040507039140043e00656015039131032081c40414079210440c0d10703000c1f0322100345660150f5650704200515242040c181d1006024414640301080461004151015030204104101c00305400100003110907544541024810609081401c1c0c03c00003076610045085120307000d00d00c40842e40e00101130072141c01c084040e000c607000b000300c072030039460401c010300190b00e000305010300b0440d4030039480701203d400f43c02c1252942e0015401c1d14440e0b000b0001107070440301e0407000741300c0c56103001070003004507410032861185e00d03489001081c1000a041d0503202c103c0d03040029844400e6403504c205502200a2041c00003551a111288a02c584103008030b4510180688500c2140703441c0e0700d07010b8018804916400c1c2040105010354810380d0f5a40076007100c1030a42001541c80e8aa0340c010001150004100c0038402e600141007030170640d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 212894784 1250 212893534 212893547
    0x1080c0d1109090106171b0909060423060103030306090e0a02010509100302070f0605062b110f030f0106180204050d020103020702060f0a0c1205181c0602040f1d07 72
    0x400703040e198210306445400c005409424241c00075158250881060800c0080000307400c08074000241100b03c03001c001906200b803e003400e80f91044660402800100400d03401c00c0c0300c0c7e10300200c00c0c003a241c0759068420324508041003a08200d000a0300c41c0010400380c22580102020400d9a00c00303400380c44504d50028081d48281c0d440107014a05468010b00d510f0700aa06580500790030089800fa070001c02d203407882c0140000c46e5401d100715a01c05110304031100300030f0700d1040ea021411900d401014543c5455001e1501454610b511218607017155070703140c030140404400300d84d4000012030704c0d034108004407950312a808407282c250352040c0302c100074a035519510750204680a0a0069440c50b040c008550780c0e100c0c034090100c81c02c40000c0c00c2c0025603880f0351100c281c1405228206c805981e1f0341011280340c46518044841c0c3da17000d20310322a8514005d141e031010301900c0a280c200d0408242e0340c550580c1c0095103c0c0c1001000c030303c010030403c060030030b940c2c0a407586d40d810b0010f40d2400c084060071740e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 212896034 1250 212894784 212894813
    0x20307201011101a1e0a0806010b03070e0d02030d0801030b06011107152607030b040905031206010e040c0216090c050315010c08030f1b0a0905011103070b010e01080c0d 74
    0xc0369160201c1c0100b11150b0060907811000203071030140b40c00c8a0b0b01c104858041750103031550145a400c4400034180300007280e4181038454002a140c0f42d6200e418085800c005001c485a501028810040005960401100c441002241c5815006c0c4d8994140410340078001404141404400000a4120304c7c02050700c109030b400c0c40a00d0320340700707003020005c40e400c107005e882c3c5101581800710041003d180f112070f028403522041d941070084100c40f00602c0159101007030700401544c003e0003d1a15510038078101c0f94040d2041c034181c004942520000703070668061000200160b08418126044151200d1010010309982c01050020712888403004002d4400200035007042525a480192543e1040341c1b0398400b035401c100700a4403030808503800001003000307030381d000c0d550064010000d84a08055040e955101c40700d48500e0845450302005652942c07030401184400c0c002000920005220705d45242e02a107250850b907605581803012081c0b43c956040c6d880751040310900e1703103040018148a16101b1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 212897284 1250 212896034 212896063
    0x216031101182a03050307050f01111602031c0c0501050610020304150306030c090621110d031b050c0901062102090d0606030b0613020301150c03020307201011 70
    0x4000042441091600806204000c0c0305030f515a00005204000010f01121402401a00c1819070380050060880e410030344105040c010a10510000341000c00e25a0780311400070341520965030701c0c9000e4130031102d101d491041c04140080ca921007404000d10880307074006801d0b1200c800000349500017a680b07024600c0f840c20100042181c1401c802d1007a08504002c1da4010300d0080382c650dc540410015008a02420004400b5041c100230300f2008403c1c5c003024690030445c0804151074040c103100c4440e0301c2c8031055082c0190189840481130301c51801001560080340038000b00700c04842001401e003010390049040100752940c0b40c1d108071000301701d060443c02c412001a60b80342890b0102d5141040701201800031850024004180419074803c648250030444e00d005540c840c005010f0202e00080c0600c68a114140004580c031078000d1100e81f404030701a0046a0801581c4c2c0c0e00c03c001621502401c1841c2003440810140303078100191a104510054146409205040c5c000903994084d640915130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 212898534 1250 212897284 212897303
    0xb0f030307060b031c050d0b0f100503060102010204120503070201020d11102d0c120c08010302131d0a0516030b130c17060610030204051309020310021603110118 71
    0x180340e40c2002064812108617540096580001c1070280642c2c0080011114481c2003008201183ca00060707481540f07100240526080d0044802c00ca4a82e000106254107543d400c01c408111384a184685101f0705104d4001107980b461144002401d042541c1910b405001c058240c81e0b0004402007802041c900c29104001151001c41e143c00c01c5280e0084140b5010015552200c2107160f01c42d0011039840d18107440d502212100342140c6401c69842c40b1081d00046c1300d1900502c0107241103400c0c0c20100320185008a05403004d11018810000a040651901d0b4498502d2070100b00e01031103420240c1103040c84080469141d5100c00c0c00b06c16006101001412112810600308000c0d03903540f00207891061448001a440f0280003a0303143d005441c10741c419a16000050041d620a008603000da82e0044d0007078030f1400411130401c01609400600f280c4c9401003220a54040d56580301a004801007400070011042c086d00b4054081005441e00600d580d040154110641600d40150400180d0205002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 212899784 1250 212898534 212898551
    0x1050402090a230403050304060c020309010f03020c031b0601140406030c03030c0609080a0c05060a0504240b15040905090105090318030708010e0309030f0105072a0c0e09010b0f03030706 82
    0x4812000520f07204030b40c039002d00703060200703140d8030071301840c8101e200e104100104140050242d82ea4000e0520a40c005602c08003251a000e00c40d4025208485a003401c4a0074032140514503040022800c0b450b840c141c0c018801000341c42c840e4681caa4080c102039408000e03150954569100c60440c601010303091000c0c5c0031b642001c21115038070110065820901791a21030001d010014900e0400301c100395000c1c03103800042503241e14988038990085501c0b1803442c161040c0c003071904400710f641d41d000c003000540c0c0700010181600c80034540c0c06070580c0040015544e03070900494800b00c600140c1411800d0785803900304041d02c1070001c120f07008200822030001c803c8400e500020715244081d000880c1035400c0806103064030034008054400c0700c10840554060000b00c900c202e003290740c111900380004001c0901041002e031a01e01c03120800301808200800c1a409403036840c030410310f941c00750303500c105c00d007041111145080c03003024400c1e2412107204558071108800280c0d640280350300541030320741d620360f038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 212901034 1250 212899784 212899811
    0x2418072d05090f0d060e0709020f0339090901080115031b0f0b0309010c1d130207050d0f11010216080306030c03060406020309100b01170c090a0b04030c0801050402090a 74
    0x40c0d00e0000c00013030030303c04010424901440640a2a01d112207280b00742036020800712107038020341e00c00a003c030310014155916081c6400c1440c01c0034448420103850b0140b9485240500c6502c07040000c58100c0440e51140c500c8248031743c90300d05074400b03085a454a4488230042c8084140401280d03000a904905821000382d0800c9903555507022040313241c0080b5002030340c118020041c502c035401c0200200440f041120087da040700c14402aa040030307100c3d011070f1070075280032804c042e0280e850704001800c00350140c3e5410f00c0e0850311904ca40200d027604035070303c0f8201d0784011409190905040298200328080a10031010704030900000e200304000701c00554583c404101114180c0002411201107051509104d030082d402603407500303c22b00407450020440c1805003e13861205070103079240d42003148a905160721880c00541813101c20031080162118070340d00d0005020240c01e00300c403910b03603651540c43c002c01c001c1c10a9001500d980d05000810005d0799400105c10790080120360045103101c0b0600303c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 212902284 1250 212901034 212901049
    0x1101030605031005040507050105030c0a081504090f05071e0b0c0f0a030906030509030319050415060f0e0a05070807050703030207050304030606080c0a0e2418072d0509 74
    0x8000d4061160f045007030042d1030030380c0215014900480a0b14180c81c1c0b140300440c0d40f440102c0e0300120901c4100103003d0100d206520050740b180102d0030324070f401402a0001015102c000000780d903010045008071742400024842d603002050504040d61b642110b404569154030828880c0d00008400400c150350302ea2028041203c0154203202036030b005042c07038500544500c2e414010b00000a00d0b100c00140903160000c2120b010780d0401c200c204c40d49030700c0380584c005840003c0040ba808101e410324a0110000b40c06608098140c10385892551420008440b80d1510014a583c0d03800e4106030500180380e40200d0182d03005050f51030b020740c2da00c50710304060300070344a1500010018400000c0c000140106648040c094070905426a90000103034010804103d21500030012a5038040020644c0030907500020402e00d0000300301d0100034900f00d000a901c00da208640c0088856942c4200702015500c80d04034066118003200e18400c0151200076400b41c034050444000500000082c442c115a54410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 212903534 1250 212902284 212902289
    0x50c0d0f0b01151202120c0318060f07030e010504020f010503060a0e010803070c0504021201180f060e041110050405130f0e010605040b010507020f1306150216150c11010306 76
    0x2a0001280d5960b002100e00154049008100149060000441c41e07800317402140c0801d440c2d241c101d0300c544c82c0c4405c2e80795661b1000d023510207000c4c40c40c10032070034602d0103002e13252207041c07402500c801602e400c903005030607200d4440c80d007142a40741c8000c010043c0c0d1243c4039400f90368170078078100b51203a4800c0301184a0141a130441c80510302000700000740182d000000340045803084030001d46281d92030003804107078001d85c1d00c47c1d100c03006854010f00c466240b4007001c0c0d0120803030001c081000986062010101c03165074126103400e0038504104014001c201d004443c40d0442521464411388102000904c0d5004500460f80300d002030034510308500b0ba00b41c00c0401f21241d0304200700850714031882014001c0c13405200301c60123207081299484041d8081c5003034905241c2c0181a41072a070a08000700141000144210402c0d0390340c43d400030403880d2851040c903001d182290010300320680415416802e40500c0c2c0d001c05c0d880400b04442405076503000b2444819541c1c0015620020003030388005802410142c2c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 212904784 1250 212903534 212903543
    0x1817090d0c0e04050d1106060f13180b060a0303230403060c0203070209010f06050901050d09080412200f1c020303030a1d0601060507030c03020111040e07030513050c0d0f 75
    0x224004070b903004005504038040ca1003001140c40d0303926561426100072101d00c81e032078110340040c000110385050468600e410508010a038010346c41032a00303810203c803422504615840e0318940290200004550305c942c0140c0216114003a070752655400400d40803c480c14081c4155596150b08a0100900d050302c0140d507004001f400080c1d420390300255240c10081042c0c7c40f40a00400000304403c1058000042d00d60b06c0c0e441300c2c90521804010b40d1503a128181003800c0300d540b0308a10300425010340180000e040d2100c000c0300d400ca85800c5c0303200080c048100030f0030401c03d862440c80c51950741010350158840181c0b85501400c0140e1480e800d5039041c200081d406000000401a02040da0b52102c95003102d0a01c200700c1103601c80b40c01a9603014240542c0f00030500401c03801c03020900070001a002c0d18400d00c000b080903a0721040120700b9030070a90050b0ba020400800380003686405004440d0b014050110490340c400700c640300c86945400c80c0316141d025100450740e100500c10100301095940f50070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 212906034 1250 212904784 212904803
    0xc0703090e150102010f0c021c11030301121502090a03140f071502150613020318070b0403020901060f14180909060a06050306071d0a120b07031817090d 67
    0x40d8049101c00b0000c80321107401546025071900c458003080c03090000c20001a4001c2a8800611107e50b014992041c05602030044041210b030911400700b0003103000c0c000700e00a440e108451440c0590305c3c40e1140100103440b50040c404400140ca403141004200c036001107507511010303c00071b02d06041ca840000d56035000e010311040030030540d180e100b03900c0d4411038031b46c00c4410002d400b07540c4460200040d569540c1c8150b4408461161001a8025540040916044001e41da0341103000a00d00161a0700c51941e03031501180c00c05c15494614000c030b004145504007040410b120010082c40c0444100c9614040714021a00303641d0504100300b001c002d4807000e032503884c4500b8900034241c4d44120072240c01c0000c1d82400383c00b10b60b03410007041d06401200c2546500c4015081e00803030800300c600f14812a03410a0244100064900074203010035480d502410401c0c843d41403442004040d544203010016050285110b030b04d00140c04001000c0111801001c550703204c036034280009441c29460303800074040551 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 212907284 1250 212906034 212906041
    0x306140601120b0105030a05100f0f0501020d0306140d050c060715051003050a031d130507081f1e05060c0303090129010e030c04021902120c060c0703090e 68
    0x2598a5140103850980707800384035001c071900312410b0314140410107000542c1800413501c68a12a00441d0f04442010800a8003a80700c0c096004a090305034000d90714485114030402055805000c40100482c55103000c0c005941820740300000003100d40c640314001d68421807801d0a0107406d0010036000e0740c008007036903074a0016062408a201c090060140858640b41c00705855200c00d118405c01c07a54440042e2000000580f801e54094006400502d040c1c240d1490854044c3e0390305c14039101d261030403200001c3d281401400201074000046c02d0340001040b501840705442d212141c130b903080b40e4894880c062540d44c0d590000f8580c030450b5002e43c2d080000490066803020380030019620581c00b800081010303d4018824582d20f19500300191501c144043c0240e5142d489060214048400038046440407580c00000c1030480e8070090550810310000000312400d2075050040007900c0c035040450908282042e03620369140d0002501640560034001180000c00d0f02601d079480040c00b007040d60903001c1c0b5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 212908534 1250 212907284 212907311
    0xc15020109052505060705060615070c060512070306030c05040917160311011802090901290102150103050303010e0718080606040b041b030c0e06130e071103030601180306 75
    0x1940f10714480c3c00100781000c070b074138140b41080e1408070341c00100034141c0d6210f8a080c0a41e01080c002e00300b8008204000506c08140d6500c104402400b850703440e00e07519009640c040710002d40280164003094200103042002c10300307001c0c0b058240c4600711400a000c1010b480c0450313030421000c0404a64000200e00e070201c0c58201300000c2c0e0034030b001b81ca42500c07000e49007403480d088410440346032036403000c002c410102500f440544542d018030301d0f0000044012016443c1078165001e0200c000701103074005042202c659041c02100715550510001c490203504581e82e282d124001409208484a40c040001e55481d2103240c409e0660031114111804403a200d80007030340c4039401280c40e0b81c0501c2c242042d00c1c03c1414240700307140001d448401c40d00e40100340400c046019003a280c807103c0400c4203041c0c020800c2e903503030801080f50915008401000303d00d00020100c40d602c0045c003c4040c803880e115240d1422038080103d980c40b000901e402d0090044130180f07591040c3e850b4002400062030f0007081c00f000b8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 212909784 1250 212908534 212908573
    0x603150c04170610090c03020702041523090c0c01090f060603050d080606160201020313090207061a240d0204060503090f0f0a110d050609030403061401030c1502010905 74
    0x120080101020480007200280340d64031030591380c040101805150030400380b0f000341c0c4030f02e50800b0307280f80251803c0030f26000202603038212906140c50f26202d00c800c000d43c1c01c08010740740902c91a042d1010701e00320300e4000202040001850346400b00c4d000074a04c10300d01c0342075001c1143c1e15440000200c001c01c560510100070100e0b0300007150b0070700c41e410501040b2401040c0280c46640c5c0206264500701d140720170301251000700c0d58101c0c15031000303000b155400082c140480014120601300180c80d0059820035006882e007200042501c660f103e40f00d101241c441d83c4120749212440e00e0844108132004140c160644240b10b15150348030b00c00316010031569440002940504410b41c111281b1403600946152599400c140c00303003603a4015442c140c0003583c2d0301d4401c41d981c640104104c00b18481030301e4103400c141e41101c0c42c044a03000041e0038410003216204440d03007420402d00c0c580781c96066695550b0051040e0251030744009011401c00d00e541c1c400d40010580aa003c01610b006552600b41041c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 212911034 1250 212909784 212909789
    0x4020406170f0105100b03010b0a0e06041707140d02220203040605010311030609071503060306020f0c0d050304020f01080a0b120105010f081b06090a0e070210050112020102060403080603150c04 85
    0x95500f0100030885c203ca032501503409440303100618500c1c40c0d2902d20003080700d074400b108020500101000c1c03105250303980001b51004118220b460f40d141c491225640d0b0a2080c5504601084803880201441d141c82d44074485c06140e5050b0344d00b0308105c14580604805ea482082c4601607140000200010002d60780c21090480f403141c0303100c4420b1101113082544540d4229404940781e80071110401644a116004150b82d101c64100001e00c00e880e500d60009a82c00320b25038200440b00040e0001e0900800c000103e0b45036402d260244c2903040c2540018007540c2820700080c1001000c0001c615007400543c40804202c600034422885185403a0007180270700024480d11085510021000803a0240800e03a046942104e490a5900c00d0b002c000300706142d0880c98000da0081042e13000410130311920425180582001d80003003002030700300074410b0165101600214084984200e0a20050742c002512580082e41070802606c0c0340d40e158003081c5484441c0032155001e415101c2440300d00d440d800020000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 212912284 1250 212911034 212911063
    0x6050f0c010609021b0309011202130b0f03090705060a090e0402062710020118060e12040e011401031e0f020f0a0306080c03070e040312110d020306180702030a03050402040617 77
    0x9001782c074500b00c0d07200e02698007a035012a4098860780308254091b40145600321420000030034031621010600700541084580c080c0905001084c08034082c0100824402030004550720f610f0940290782c01401102c00707200304010200b5140120302103540300d106542c07001820303d4541d43c1c0c0042c0c0101c145000351112500c42d000c0c4184101d01c880b03041c41801003254240c0101d031501a001c8665891500a00241040c840f442c014104580c28085030b5800070300c010565030070804000c0d414009010301c036941d44032215051515281c00e008592011004140b804819120300242942c103203030b15640648030f81d448451901000084245810703030994400c030203482c3c002e0304440c50301240c04203041d0388034458011070b080d1035102c40001e80000d100703002c022410a80c440d00400d1055100d0549440d580011500c0a001d5801004001c0507080c1f40c00c20069883c0c1d0494411414101500007948a1103054038420402da203500c00103083d9140c94101c84000c02e140ca51400462104240b030546465120aa545 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 212913534 1250 212912284 212912317
    0x30717011e1e0c0e0d08070828020705090103060209030c040e1b090108031b0309060a0305160c0b1303050702090f010303080907140405090f01111b070f06050f0c01060902 75
    0x11107035600b0f1088003461040e545406001034424020000001c03054881110f149008010010008020f00080c01c0032020f4015040020410703150a818020b00c0c1c010030f101190f10a400c1080301d0b944081559045030f4206000680c0d0303075826800300f420580ea03090100e41007420885001c0e05190b00145600032582c40c480d006601c01d00f901c0401c0105c0c842813290b003072540e01c01e200002100010281051508901c1d0b001c49141103203042c08219160010740c00304020a94503000c111301424402c05580401c01c181c030b44414a940159135881700d0340c5000e40b0440500885115030702c01c00d4040c070100c03982507030000d0841030380d464400d5040d04185400d0008800003100840404c441d200c0000364201907411040c81038400c5038406c0144002044010040d15091080d007200498070032003880b80b54645c2c100071081c1030b03540050000801c07403440c00d07500c800001e9009503010480240e94900380d0007038820310300e8560b60700d2091002d1002035005d0003807004800c0d4a0040c0003e11010164020f21341400102d406d40e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 212914784 1250 212913534 212913581
    0x12090506010305160609050a0e1e0108070504050901140103110f09010e07020c0d0f0602030411060c011a010203040503120706091b051801030f03080c0409020c060a0501090b030717011e 81
    0x8403903018441c85080e070800703001103050000046920f200c03580940c1c0390310381003c0003104ac4050f02c030f00c400c03e0307000c1242e80d0054802401a07043c075020f00d940c80981c1800a001000420032400409001403001074600308003803400b40da072603444201e030102d1600002d0400b400d55071501001d8882200a41e448405481030340c400c1c0c0014200500502807060f0400821200003103691680d20103540010403c03120724018555031840caa80e59030140170001007200000075100d251100700c464800c1c20f6282d40741998401e000402c441d50300094031280000e505400182c462031a4030b49403010307014107079006048505011100c542c1c15200460340048500885004040c001c041ca03681800390030a000c05410030054901d96004240542ca11a403c861140302c15460580d0b41e500c20800c03600312114000560b0041c0007032140c1002c0902826004d01129170ac00c00c0700c011008002582c7e040d0a204104c0300003050b90780a14020001e500142c0030340349011001c6810344c0072000e48070003040c2d070a40709000c03110f695100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 212916034 1250 212914784 212914787
    0x6060e06030a0b07050c01090c14010806040b0d0f050f070305060f010e010609090504030e09100302040e061006120b0907080105030d020c01141e1b0f06090d120905060103051606 78
    0x40c42c0c1c035006000c042c51512458400c840c1d039401901c900c4071642d05d510100000807011500741c030003810485000e5101d4411440014250500540403500c00ca040680030162036583c1004024443d500041e110440e1405261882c10072031145020a55802282e10001c1441804500340380b19035421601070301280e8803660740e4004102c082c0a10400644000e50a20030515583d100f203070802d00078200300580103000030002e80721050880e0040c030144e00300d0108200314100340c0501c21844c0121000740a051415480440c2100d00030b219540030400c0b050034402184805511903003a00c0c070040e05901c16443c1944e00030f03004900a20810340030b03100d044000310501b88040381a105096050b501c0285200008401c242ca1303800413030b51003031400c801d4944200c1c40c148481c01841a81e480c04541b031740001c40001c0341800c0450300403500c03030242c100d401000342c8101c01040c514a0003055080555071100203014580c0200107124005013184150400442070240016074948c4000c0f584481c40001034540e01c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 212917284 1250 212916034 212916043
    0x7120c0501110102030f0a18060e0d030e070503031603140d0506010e060c0d0e12160f08190308040f02061c0501120b0c0a020f0a0602070506061e130e030706060e0603 73
    0x1041e0110402446c041811107410360808411180300e212444040d02041d10303a082110494005000d540c0d02c40801c1224171071b014082c00203829210000351072a689404042610f83c403448000304180310041004004240c041c012429000301442801504c4c1c04506da581002042c040d00c04501054450b504500d0324074040080701e40c06001400607103407082407030320107460203204c0c244a20b40c00240440b19000150b41040000c2061240000c1e2080140c42c1c50800c181c08080750300007100c1c0d600319140c0c003684205101d03108000c696040c07408484c25910344c2001c007190310b80b07207500a51002c0005284682c062000203203410504941204110707503661098004101c0104610040c10b0600c40300010745503814a60291560490070700541d40a503080d10003071341c24040d19541c1128003990105074601400020040d85501c0101500c15000ca502803903150080745c1007d000c118401d095100c41506814140d030085201d20400d9030450341c48840780c1c600704014002034024448414001c6001440f10314000a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 212918534 1250 212917284 212917291
    0xa090c060e010822060e0c04090303060f050901030819050f03161e0e0904020301090512030417041a0d1104060504090b03030f090d061b0f02010506030d1202090307120c050111010203 80
    0x411010b0f001c110b945c0300006030285034a40d01c9580621400401c840d00e4501800c0702c0d0911030f43d80000c03003504241d800600c280c096080315015a8660700140001000b00084804486a05160203e01c200055040342d00384070389622460898030200520030341d070050000a1800002d603440c0c0c06541c00e03021101002c06403a11603070f0360002d040018041400d007010b80446812030b00181c00414040b03955183c25182a00800c41b5030b0309140004100000c1c0b10000340082d08050400104504d85481e0031706040c03c1d0210001c03c1c0021260020300c00c0e041c004298080820016038a2402c4d8403140c1d07855000c0e01c40d412034030400111030300302103135850149400710859035049190200707942813468902c140900102c414030211000d595a5403101810200101d10603000445903403010030030108000001d003520720242000e8001e520950b8170403009074000c14041c0c40c85d01021001600e4504120019140c5000c0d1784c0420302c01e8035505500414005104115000c1d26401c0e22000700c001d0704180d0030750803440204c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 212919784 1250 212918534 212918581
    0x60501021c05180112020408030a080c040302010915050705060a0509160302180903071505100e0708042a080102090103050f0f0c030a09020603071106090307020d08030a090c060e0108 80
    0x3048140d000c1e8a0f0100c19441c1140c0616001400c82800c000740402c81c0e0042d0412030745a407000c0764042c2080e501c581113650000405a00314200303440d503400a050541e042c002c000d0182c0854801400c418400d405440d0030342d402074200c030707403074280f046180340201000e807200f810710300454030b040081d04852075032181160750161090540b845104032650501c5405480c0c1e0b100343c00100140070210300b4048400c055424040c10009840c1410302c400410000d05034042d801003442c5000b00301e01d5507084040c555005400401e103003580b081039014000031035450051490702c3d01a0440200341200d0541c0545000c81081e03d00300550786595600d00c2c4107800484480c00038419020004444500716006140c0007084000041080581ca600065854000702c03501e40c00200d441c01e1125400b1420002c2d0750300300d4000000395290040a4001c40d001c07612020028006110002c042341e2481d0301507009010254000d0420300d10345840740d900030066010190010300141c1040046a03c00c0401c02c609960117108 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 212921034 1250 212919784 212919787
    0x21c0311120d020d11220e0702030702101e210212010306200f0c060c09100c1407080d030608070b07060f060e0a060602060a090201080105010c080906040603060501021c05 75
    0x348204a020394801c0c549285140d441e200c4c0000580b1401c8083d0002540c00b5400803018500c042140411b6038155211000400800007480142600402116800c54060310b82111010000105980d0f2854104441510300103200304604090340c040d85540307401004400e00e00001c030303100c00c0e02c0b02a8000e8680389104034440c030b4010000a84c00d50b00002040c41041d4000b0190020307031038000303c282c0208038241c2e807184000400c50060340051003565402404d030000f640c00c02c42900089403109140c034010b0414410210901024010b4030104100044401400c641403030340c030756104607103808483c481312000c00d0500e40d01203008940800c01c00d003500e030301c0001d03503050071501e80b10900a80160940d900810f541d40c00c1c04100e045880c1402c910940c125a40030465900e0450003d10b00040103040c06132441c94001e040c00103070384c002d050701e0460702c1c00d00e003030782000320a4100400710744145010345600c402c00180000d085078140d004641291000d0b02a03c1070013078801301d40442c00e140003030700d0400600b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 212922284 1250 212921034 212921047
    0xb1002070501050a030e03031005120f030d0b130e0a022d131503050c01020f010204120807050f01020c0105061206040203060103060203070504050a090b100908030f0304030c021c031112 81
    0x4103030081c0c07881101500d008540d15a51b02e10304d40c00c41d401922681e000981000c0b0611481c108441449000040c0c240107080c41c280c0c0812858480c0a0f84a800c4119510380080c24050340d00c041005991a0b8070341d00c20080f6080c444e2001d9502c02000704124000d0010702010705e078035000b01058007082c01d1002078188001c1410740c20001740e1000100ca00d8115035a403982900c291411400701b902a601c00c1004004203a000e0740064980011031046040a0303004103c24084a038501141e40521a4041c0203982c860305079281c250b05140042030758140c80d40c0302241c8180a224150030850094006039501c1c91000d200c042c0341511514120b40c0a0341541c46a00100f0020300039a00460b070240141c81d200341000d4440c000500c1800e900e6009a00040d00d8002c100c20790b01e020b00d0307040f0210320f0740c0c10001480c610f0005113548a0003a20b82c5560701001c084009002e050050b80340d000e000707500500c1103046030f009100100c68a0000d403000d9000a220b00408803124000160044404d00010249030401c403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 212923534 1250 212922284 212922287
    0x70806010309211710050a0306020f040503030d05041b060e0904050c0d0f0b010b1614070f0b1201060305270c09160f03110406030f0b220b1002070501 66
    0x15003070904841d08880c40e80300b5000a54100100d50391203c180c0c0e5a0f4800c60a8501c1e2540d030640040c00040740e1250110301048107035a420402011281d00c01c5000d81c0b035101540c5034070068011580803d816010024020300100800d41c0240c1c41180b14494080c561405008082e83d1b42a4034040c840220b403a10541c1800d42ca02011410303803286c840c0e0201c59200300102c02140d0070120a500460392065401d00c02000c110807007030214058600c50f008070f03040c01d8100c608905204030b6408c01600d00407544008009800e424041c0c40d011f071000440b8865010313a248030201c5c596110440506205041000100d4220b10900805004000441c141900c01c50703401e844040100d400c202c05591031250350380e880841d8860311111442968101607070034080010040140c102c030034507508141010303e0154055109084003094505031b03401490300180141048102c0d00040580321f802c01d0b4482040c220000750007500c0b50024010140404c411301a80202074148050080c41d070380f0801c0983c003d61000d00403175 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 212924784 1250 212923534 212923541
    0x703050901030515060c030702030f0c030d110102041a0a030e0a0201200708010f1401140a140d05102903190203030f030106020705010e030d091503090b0123090708060103 75
    0x1d010100c00303c1049084c1d4001616a4405005a442500b0100301442589400e022101310055410050301c484151000000e480790b0140b0f280c40305100a500a4480d84d960960555010f0006660480c3c560b644143d019902e0347c00c0b113805480060b0906400c40b40800c0c0c04100400020350603142c01c004000034080c680070004d42640400d0b440d204210002807030794000d0040c46103003041c0c40c500042902200f02e0350328002078142c00030300404032201040350661300c40384200c40455020100c41008021100000351114419140282c4640324280c10510030484070381c40034813822408a46004002c4036200c0c034903a04030304002c1d480da058001e0500110582118240c1c03004240c0b0084c00d0764902030002511007051740003a000f400060f4040b020038016940c21000c6140358440407030040c038440c0c01c4482c0c014a8812107001d00c5603c2007020200e2540c080c000d8201044003544500c1c01d161941e12404a041d140c01c92000c1c07600d40c0000d07021070104608020702446d000d082aa560b41000b50b80d5140150b028 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 212926034 1250 212924784 212924791
    0xa080c0918040818120a08031e180601050a05030304051504031a150108150f011202040303080a0615020a030e0a09060602010f05060301051018020d050106050c011107030509010305 79
    0x3203020034801c1c42009a090320002c0c862031107140010b0316600030400003220015100c0d102030003150300c040d0310880c0d0341c030003c0c1010010b91b100804030365a603180480c8556008051034920380c090075880501203a418a0b6803107100083c00b1404490302c9030790390002c000390169544949070301500200300901403030500f02080c0c2404a107400240389003959958440b0702a45d9940c0d08000d501c0d04803c00e10000d8240d0041c440c0d400c0100746000e2400b4200103005290107002d002d200c0c0c0c03040b414844172034000e134040c8404800e84000c8500842d21680d5906014100100442c1d819500340e24204001c900311714020305203030000d002940240109903103aa01541c1c001c201400710b45d4494042d100010785001d8601501010b41483c4d400494880403450f50281030740c1c40a4101d40c031a9042104100c4441c602961640803180701c41c41c000c50040c56101c0b007900a1081d548000302c1c185c14000003042c02600400200440c21100d402007085038108140101c040c0500a40140010300c104040d0000f90b02c80d070000b0b600f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 212927284 1250 212926034 212926039
    0x7200901090c030c0e0604290c0a0605060312030f04061e0209031c020703123b012d0c120e011701030b0a022a010c030e0703050a030c0c0906081e030a080c09 69
    0x180074108d6801669410805400d1603540c00036514408220b524040c154000b0b1082d002881144e0704489911303128000281004601398680b4001000d00c000d0760051001a00d08000f401070200c40181064040d500038044a4000e200c1d103814201c84602442d0004c800120300e038003401129087d55240088a14100d40c036800300180c0c10900d0685011010000e03001440003122007101910034104c0311402c0e400f800351103040c0706580c035141030300c134201c880d0854000c1c5c5020f082c4010120700c06419244c0e191410300c05080850180440d11405402800b2010032800c00d803a4046040d07c004000710004d603003400020120034444002c640d80b11a190080c00e41010306c1d40e550301c1018441c10b0000420114ad500400a6a4481406410003a0180b01d84030140c1d0000b0094a0f0180c01d6880d06030348c54100d004028204003241a400f014000c02c0801c080140000b407100340403045e5641407050340c0312080e0f401d2002008403107241800a40d400421518484401d0b1507071003c0c4e42e034021010a282d001300d0b41254 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 212928534 1250 212927284 212927339
    0x9081e18060702120708030304060b040207020f1201020d1d060127050408070510060f05030706020615040b1003060312050406081314191502070807200901090c030c0e0604 75
    0x104e525010300640c00070b0800c0ea001592a8507145c01d080003650741c80024a4040d1f031040081c4009030b200c10108040d001c0f001e495401903c0001c08500e4024441e03070309000b040d185020340c3c5c00d4400400000c400946802d8208a4607aa600d1b00788a1007051086e5284010681c50603084207801c20050304095486801000c00f1402c0008035100e240c184850742c076814050795500c24040c80300c101c80403003035005081d06900520f2090f0912401a43d0303000060603128400e070786151440179603502c5c3c0d0090500c8003000b41501004903280400076015201c6400103c40e40c00c400001070080c01d00c03d10a4504a0b00c040d52a542e042d1600000d44c3e00d0074441402c2035900c0b50707a01e0301e09506113004220b05599110302c02e01240c0070349120700303040c6500c1c0c030f4207030f2107101e92801006400003080d000c005481c9900d03044002102a8148180c0b22507800c0d44c0e00c1c103c1d5401100300000001c0c800d14a17440380c0358061040c1c40912840e0180d00e0202c9500e0307509104140c1c410000d0009000b5031119000208001c1c5004d030800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 212929784 1250 212928534 212928559
    0x50712091502030c1e03040e13020a0f0603060b07021e1302040f03020918070e07020c10030f1a0303030a020a022505031c0804020d020d0609081e18060702 68
    0x10285500710940c0c0d201503400007411440d440c00411105012140c1d01002c08021440b500d40e641d101d224611401e8015400d03c0c0100340c24102070008802200e43c02002c42c00e080345c1d1003464448685680c07241402023071030300c1400244070005d10220b6081c6d0307900500072510300c040c1d6200c140b410110300e03400c950408007010140070308510520040c0b0152138402161000240f551040011024008040303100d81640703002195403003071000688005403503500c0c51002d401d40d81d001e822480e00c6110f401d45030380561003020b01c40e281501944912000000030300700f4080c0d01e8041a881c0c0d03105102038031840d016401000003c0300d8194a81c094040d0718103e205640014480303840b103c60709000440043e146d441c6483d4108203e1604000141300012500139544807440d2450004c2c140d250024800fa016980d48048401150b035001e81d600b00c400d42c805030820100c44281400d031056040082048030b01201c410030085585800b00646901e03c00401c18071a04000d00743c24032405030440b00040760451508003c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 212931034 1250 212929784 212929799
    0x10020c010b0d080d0c030e0d0c020303071203050a0f0b0a0306020a0e040906050603061305150c12130309050105090319021c05061e0f06010c0309120302011e050705071209 75
    0x40ca100302d03000b94041d83d120307400d8a015004071a0640c034142c003071520388440c140c9546008201c00580303d1190505c04090003560000c0390561140301c1000f0408000b0000003c2c07075a4043c0d00c42401601800c20810500048140800403100c004040c241e00c05644c0d0001c100003041e41c0c005110781c841500e0040e000701145400724042d5628054203ea016031586c0800c162400c041003180d52112903040f1709140311205850700e5494422007404240001c1c0d09200180303109503c0c5080302c03258800314109550078640203050190140004a0440000b03641520000b00c5611440a4407000c81009020b0040c802e00441c0ca129541d5900314102d8000c0c8207450b440b034204010700041d122440c040d50140515251404460003104a0304101500f01a507440a01130780c0f180c50100705034050800c0c00c0000a01d07006090654003891503600041040812560040c201503041d004800350308644400b18071455140e200740c4065032401c81c0c2040000d001441410041411482d5818590030f0508012800d951500e48 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 212932284 1250 212931034 212931049
    0x28050a0608091908070f0f0b0702061509010810050405100507120501050618040f09020909030904060b04060f050f0f04091b020105060f010e01140313121110020c010b 73
    0xd80003091180c0c0800c05290410f00211620500c00d0078010080c10350b41c0d840c500d8a0260400280082004c09032210402289008410f0590b0300700041c68054900400e00030754403141182d100d241c10030043e0742d40c0c4003070410200c0c00d4185c0f00c0c004068050041c400354954000e15004000fa142441052a444035904440c45181e004006c07564801000503031907090241916410780c410390080b4003c00182040380c3c13103203600c61440d220131640421202c80d4903000c50060940000d010354002054420301900c030a002004000742181074405001c0c4076a00c00305248940560f10424000c9012056088107440c420002804078030b218007034a82c03c000c08050032614680082e00081042540c85100740b9400c00404050482c00d665407009000614120000c04c0044051111683c10700405081120075a8050204608012125030035140c83e03141421004248032991442903403807803141480d003191144689610491a441240208049004c1b00a901c000b54001c400c403036003a569070034401d8291396a01d84d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 212933534 1250 212932284 212932289
    0x409020102070518070f050a080f072c0f1f0e03070f06050403030e03160303030e030c0a05161a091011030a02070f1d0f04030302070b0c040905130228050a 68
    0x5222040c0c42c50502006000180406c10b40f4081c0a4140005000241d02820490380301d1040462554542c5485405880c8403c43e03280640c50080a58141820412402400a0010b038204e036100c260480300c005214102800c0103017040d42d0320300100042071240c01607640c5201140302804451100765120000010000c0030b4200300700007000002d0400c180b552090f042404010200c010300b100b8240f0a042510140203840024241601c454005000b00f20600569003441c91903070a8480e06a25071030701e00c1c5c5071403540c4904409411074950108103003841e40d00002407a0380508619103050344200400000095070802d80041040f901b902807a59030050002d00300445050300100201428651402031742c1031a90401c0750004600f1000016580c210395416070486100858001d0940300c0d814214040d200d0321101034100001d050900c00825021401042120030740d2504120a03100c54114105107401c842c0c001c4d50111034a20704085c107803101c11501c0f001c407913a601c00d0304031686d548010071010040d55 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 212934784 1250 212933534 212933569
    0x52d0c0a03020f07090e1c120c0207230307031103160315050108030a050f0904020702151c060b091917150c0304120809030706090b0712110904090201020705 69
    0x14840f8a0048108034903809080c0300c80c0309004030181541c10b540d95007801224034142e10141600d0003212070140d10701c2c10754210140300c14001d601000001a65511040c490484a102007030300100d04010841451025040014050003100d451030305d90040c404050440c11307a040c00384c07105645042501d20b06001c019441000408103040039146150101e941c16400541c1e560410800203002030391280886030035001202205880d005060045402030060810081d005003160f040071611403880d0000d00744101ea21941501c510308440c1c80d410540f0494420311a02d54020701c00600d283c64003c8201c0920f20f141085504516680d482154020381c1440d603001c1960454481c0130049070142c02d00356403210070301c50818910704243c0c0e1110062006200f18000300400200822510b01041c800c03036040d250000b2041c0b220000e0703810401030400303040e100b140c04550351544c0d0804c11000e500034907543c04640120f5500701100d4405000103848130800480c114000e04101203115680c80c00402810940e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 212936034 1250 212934784 212934793
    0x6030501081603030e1309050303010603090c0801060b030103020411130303031a010c0804060311041205030414030a0b0a0c03020d1107230a060f0b04020c0a030305010501052d0c0a0302 81
    0x5007030003181840042201e20301da140c0180400c1c404640c00c002c41071410507003540d48029107449404007200070481600000c145000010001a404d60705030001d103001d5000e4146010b0b4240e0b1880360341c6c01c82e2a14072401d08461010310040000d450607501000307941200c0040c0354a0300b019078071032098045172500220042035440801842c24042421202c1c0c1c003540c28240200800705c2034840c00a03502942c49030404041d00e900c4400074100d1440d054800a21042c0c0345000d251400e07150054a035086401058a20150321756610034600c1d001503c1c002d040d420124107150b0361215100240908800c01c0e0800903d5020484541e02100750f2140c1c19800c002c48a00e05c2d2070f9105403a1810001c0800803402c05490815180141044030102d095200d140d407061b00050018650030042c40901301040145510a01c08110704810075004942c61108501c0380c0d9040046a881c2c40054030726000f452441701004c14100d0606130880341070406120b91031500c0ca07001d42070001440c20503140015200b030880041c0c11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 212937284 1250 212936034 212936039
    0x315151c1a010306050a06120803040f120e040f0c08180c130e060901020a02030a0503040c150c1203020c0a02040e0a060513110d08030f100e0106020102090f060f031b0f030106030501 80
    0x1c01d00c00c1c940c1003c40780c6c000303100c03084c580740c182d020022021001511040700000881c0401040c40c4008000c0d682c4518014013000310000c000c0c0c50300388103010440c01a42440c0c500d9001c1c0c0d55034401e041d40100c00d0346500603e601d410b080f40305107003800c1481c2c0c4018810011003001954179640d468580c0360890102003441d0200549441c10084040c3c2550980d81c0140840c2d40225008025202c05490b246010364896441c1d00b8810450000c5503c0040c50030b0030440c00c044c4007507020012005050162650180443d0f082d5422000ca02c00c00c031441c0801c0c5c22003411400103117850741202001013000006c654502c0100c0d01d40f442202c42c02e580c0c100e1454000120401000445070030104520011a401888040707542c96040c03045c44000d000a091100c00800907400c90461041d1002074075503103500a60f0b660310341030f02a0003580001c2d852441000075040d000c03000c2c9442e100329005096115029829a118018a901c81001c16500402c1c0c2d903101b4460701c604004000095402401c0b15a804030740d552 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 212938534 1250 212937284 212937293
    0x80c01240303031505030304051c02090c0705010b0102060411041a04020a030e1203071409030a0b070e0102070519060e01050f070305030709090504020307180f09060501050315151c1a0103 82
    0xea5280b404413120300314050801c410307640441030710103d400035500a0b80e0120344041205c01c0c03441c8598000d602403400030620808110b110f000d00016032080f4000c02000c640030005998034407046400500308400c0d040d49603101d080540000501c0115000342011055801001074283d0300b28070003480000740d45440b0505008410403802014070203801ca0545103040140d402440d4001c021620703107921000050b804129102007242402032900000c0705407031420040e00081010311044101da005208418001ca440c0ca049150034603040c041003002103805250507410307a0344180000115043c01818440c00c3c1808183c44001c003103061003031791081da9a2400d4040a400c0b48e2194104101141ca031504100040e20001200001d03a00c0c02e58188084d5900010004090450b101d104184181000c038147d04001068010364184c0300c0450a40340c00b40311000c001540608110360b0303040071803100540022141071140503c29074a4110340011a2480580c950814042042c0d40b0b141c24a1000c100400610 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 212939784 1250 212938534 212938541
    0x513211a0f010603090206090d03030b09070e0d021903050d080709060329040f1107050106060e090a0c14040305030d2f090607170706180f080c0124030303 68
    0x41049a0000c845030629180c003000074841402014185556044003c0c25541c0b03103815250446401810b5a8210b03c052a009000e03003a0192030f5030180f072000003c96141801400180e8a1103409080d81c1b800d404580c00300500c24089248070100040d1a07040031010400500c4a003004040b03e40712241d150521a00040120049034000400c040c500b00e27035080c19182c41180701c0d2802c50007034100001804e101c0002001000c000307418200d038038500881c080a50700024094943c40740110001c1083c5c0365600e40699100da1541c4010b03030303c803041000141031028941e000c115912054a41208200a641803030140740c0e0103600140c0f020743c004500e111912100340541003604a00c000c0414070800c40d070074804118844039a410511400114085482d501c03030300d003940d851640002c168920151080d00140d5185e01c04101a107000f03003446400144007403056581c941c600d92150540c034000609494031034030307500456982413403552124907100c404c030021102c0d041c440d45081c519840c0d040ca503207000b6088 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 212941034 1250 212939784 212939813
    0x605180d0201080601050a020c19180b0a05090a09060c200f0318060c1c020d0507150b040f06081e010603110f0a09090302060117011407051321 63
    0x1124004010300050340e02c820869040390342802c0458075608510400d9051000d1103e40d103400030161420011100c0d4203440000464001107000c0e03450b4010540300030143d038070b5140100d4001c03030640c40c104580d040201e0000e40c040017049000406480355640ca606458002c01540b0020703001c42c81c107a41400c24921020301009034038004004940d068040f0340c0d181d0113042e881d10000b0380020074a4440d61280012200d50003414815200e54a80c800c16452541d00e0010080005101d441046207516018800b00c0c5c80f040e8105c00301c0e003040e5000b02616005003400748102d40d000b51719103006411500ea00d01805000e04800c2000e8403403a044607000e0300d5070b40600892000705a04202040021451000880102160903502d0b0001d140c03405004c5121501d065001d8400c092400b81010241070340402c000d4182e502c0402240c0840001180303041c02c2c2e43c50743d401946654080000b1540090261300140341600d40c2815802005a403880d0300f100c0c084219044c08003006440c08240700300880d00340401c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 212942284 1250 212941034 212941039
    0x203010b0301030b0105120a03030c0903020628050309030904090309030b040510360302030c030c0c09100b0313021c030816020303101203021501140111010c0c06020906090a060518 79
    0x45045810351f80c99520080010050141991240c0b181c00013881800130b42c000c2d5801401041c4d441010720346c104180060501c0030b440c0100e15459140c0c66071b2081c4116801a0840c2c00218100280f010400c80144900d4034102d06001b00d06000000140c1c0b140b034020f00c100e015001504c3c010080c4141e80043c1c0340c81e51210b0300b61810069010b0402020706085c8450540071a4403c1c1244d80145000d030701d98801d01201c004244130108800442c90000500d012507800196401e005d103482c0c81040c800880f40c6030291100281050000070000c00d10380b1030501341c1d81e0000300110030040303c124103081c0c8451a40000d0f27000840d40307410000401403025056422400510046281d07107801d85800351140c1c4c1c01d0041941d00c070f02c1c680c0740200f890b1007041111542020705110074500d5031746000c4030315002845181c0c1400705080c500d61503801d9031706100700140c01103141c031000040381041e607412009603c03003102d066000a080c0200710458a820348080003078003141c2c035216135840c0100c60071486c4403010741c20140b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 212943534 1250 212942284 212942299
    0x1306020d0801081618111605210304030302280207050108010e040f0201110a060f0b09060a08190602040902030103030216120309090513060921090b03040f150203010b0301030b0105 79
    0x40e08840b0031a44e0402c0b40d41701940d00c035a603044000c15401a200c2c001403000200e0300415418840491800d8405c0220312510071074014607901e07004c0b241c4c44621209074202c001002d01c0080c2c04a80660020408001c28030154500320403001c41b00b418014020380c16200581c00101d052215503000702c0c0c9180035049424140070b05140c41d03a43d00f8850940484003e04116400002c080044410003003801c115601074400d11034003020078901030007003880d12844e610418103031000c1451402e000300c0000940d0807540152030782d100a07030345c040b05503043d00e00216491030307081200180c410b0750b6202860186129901a151002101e90300400f41c541070340049400c08c444000400000340c2100303a4204072084500b02040701c3d55040c04540f6842420f01e0081c0580342082080001c01c1a2668030145926050362074041129118600301c031418624050544000c00400101f40440c0091030303c070300d00314403441703c1409118900007424160303002a4407500c94200040014820818100c0c00b0502428003a501341 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 212944784 1250 212943534 212943553
    0xb0a0e04020c0705101701090f05072c0613030c05030601050a060e0d02060c0f0a0303180b0c1b0708060105010e01080f06040e0c040c02160f0b0a0f03021306020d080108 74
    0x154445406201d40ca10a04200001105c0d10380165040d89410310400350300105903965618500161030904504100c0c030f450000090301c640c1c0254080c030350a070790300714084484000e401c40001c00c80c4a0780c0c842c580e128004cc840e44500201440c1d1810107144507130f00350b0107020300d000141458140e040c3c1013544228080c40e024800c0a43c400301c1038912180850b10783c07004050900201e00c0368812100c84061600600035405d40c0e00c0303800145210080c1c1303e07680400c0b150345040d00c99074004070080390060034a141040810b1007968a2400760070010240380c0c14840c0c908103c0881441c207901c1e5400441340d0341000300108100e68101182c0c5101000a00340300c0440d14103000300365280003008001d50f1080b645e075004195120400c102c0c503001040068000c100d0b2141c00c82000c0c0d910490b84540c0c502c90844586c011403a0b01d0007255501c100ca040d2170889040c080c3c1040c01380c40c0d206048454104043e401d0014802098202c10a00e00821041d006004000c024403801090200141c0100136142d1068116 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 212946034 1250 212944784 212944807
    0x608061009320603070f050d0902060d090b0705130909170307090608010503010c050d0e0f010f141003020307051002150112050607140d0c110a0c05090f1501050c0f070b0a0e0402 78
    0x4186c040034074900320340d42d01490381d02000200803012001c1e40005c80801c000e600070060b907000c504818040c40c2d21280e50303990345104841601c6a803413580d558800c070510400c031450440e0890b48c04144140d0b80d04c004500e0303000c5000095002252540002213050f0401c200c240d801401103805084143c00a0000040303500c0058103038031920034405c00c0e25940301521101c0c01e02c284201d10b08040c80d000280140d45211111401806c0c545809000d0340d044580401e0b580d1415403401700440c1c0e400f4000d8030003a4070748001c004441242c1c541780c0c0154000c160f004480a0b0965950b680070345500d41081901c5102da0419034506200181800248550b0001c0307075003500f050070144ca550002c4248042200010072500300c891424492408500d442058200380411095030402d00941e01c2c1540d480c0b8199540c443d42d00300d0000243d490381c514140020075560b0552142001b803003540002d4080756000840c4040c2585454881d0380000720700e80d00072400690550b4081f03100005071208071402e6090071202e811 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 212947284 1250 212946034 212946047
    0x5030301050a060201290315012706030f030e010917060f071112030702030f040902030a1103010609030809040e060a05061f0e060a031d010e010b010801060806100932060307 76
    0x4200d5400c10554103406203550b801c1064030030714040c6640c0301119581d11510a4012482d4844022b0003404c04201600021400e1080c1c90803a90000200305141d400c0d51003ea43e04241d1800050400c134141d6004100ba1041d40594605200103000400640c9800188101d2182d40070f03041d03408120b1707000304003a03103650006140c00810340203142c0305640e07884180003640345100319000c040398403001003030000b6501e000f94055441866555000d0081d810070040140036032109000b41408181000300610110303048401a00305840e0140001034aa0a030442e41450200120b0311650700782d48030000c10a850409924a82e4403c02055404600002d914009000810440d00f01d50080c000402c140c291039100e90008d040c503104009101d480842140107040c0a418003030f0420a8a600306000c1403d1941f0661240e81242d0140d628100306445074000c0101800305404124200100520f010132540021800c0000280010740720951443c441001ca0030b000703420744580c0788904014020041215002038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 212948534 1250 212947284 212947331
    0x6020d0804020f04050613090f05100e0706051c0501231014090d020d030c05061501081f030203030a03020706060503030c0a022b080406081501020c01050f0403080705030301050a060201 81
    0x3907001c00c4030303034820700447c00307449403c0c07200d110540c1010101c0d0140b02d007408480384042d001d442918110011400b591050b104000450f0749150b0260108200320b500c10005400e10903820030040002141018003181600c03402c0c1c102d0302d101411100c41c014282503500311401c81100031340e900c921115030b049000c1c0842c0048414181022000180701c051582c90210340d0700701d140e0040115480e00c4032424020602c2d8102e103c1100e0703034410300f40410b1000010520b640c0c1c451005a690301565030750b200c890b00f0f0142e65120018030300e60720303988040016a8144060640c6003d240d800603100c01960810300306a50b41540158001d42003000000050724001c05c541c00c0907a01a01e1030180c0c0c2c0c0744200c000035001c41200d01c2a60640003080c0d020200041c50700104210343d00755945950700d0b11072003210920141510f06841c090ba110300b2281721954003d4020303000e91070000d25040c4c18140d0320f484101907039001100854454000000600c060302d41707103804002500907031008004045d030a8220705001c01285 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 212949640 1106 212948534 212948539
    0x91d1603090f020d0203010207150506040c050705060a0e030408060f04030f02010c2003040e041518080f0702040b030307060603170c120a110a030906020d0804020f 72
    0x340070361110150800200003001003180c1c01c02540c0c0e122144200e80654007440f00c0e40104141c90b40061110540b000c0219662038040308110480b84082224030a0140600ca1880841c100040b00c03584030795051310010743c0c1c8411008a9186000c2c0e0b600011192190600308241c208020f11000e000d2031003a12070ba981103005490a07130a0315460524003000907413480c0818100c2020014807a81e030140b100640380344c0368440e0b02074089500c00715016580068001800d20400c4070b54820180088120040d40d020181c090399001c00e50300c10348100301c00060021542d60309558403030f8080303480050f0080889a07911401d01c1c020780500258802030320b043d90303000e11020480040c81e0440e000004520041d090702403210042007440e800080181042000301241c0241c000780402c0900c2105000b6111079441c249040c00080ca07080c0c8c81c0f03500504005400003400016291800c580110071000c = true := by decide +kernel

theorem cover : BRFrame.Cov 212769784 212949640 := by
  have h0 := BRFrame.cov_init 212769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 212769784 ≤ n) (h2 : n < 212949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
