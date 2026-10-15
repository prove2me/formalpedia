-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4050
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:25:42.193704+00:00
-- url     : https://prove2.me/submissions/7a6fdab1-a951-4850-abb2-944e955ab3a4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 728237410 ≤ n < 728417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 728238660 1250 728237410 728237417
    0x503090904020d05160512031806090109050301050f060a1205060c0f0c0609060402240318010603020a17060609010311040902010e100c051606120b030c0909010c2304060e061306 78
    0x3040c031447c10111385003c3da03007555500852400c2c845140480c9880b02d041d04152080c034001a6240c801c1e403141480c0c2005202c00b500034001800c3c40d900c2c219840804031400790003140008030018220b0301d80051249560380000c0030b420303541c86802d4540000c2c2d000b0755140d1207004080040090004080002512803984400502040d017414810404101c0304502d00d1042c0c500c4075204034022000304c400b107907040042c071440990b0035048056100d02519070f641c0f0107580551030550024400b105460400c0c5112128419696035540e100c0820042003020301020300150204240501281400e0303108500860050400e03151200c181c00004060b4035000c1015000101801030240410404105140c05031030040c0305d00320308a0500d10300501815894541e032030349585800004505840c113001900c081000a000a4650700e801d01306a800781400003900f10000b1340c084801d10003a0320b8044070050311100500c1207441c081c60802c04a98080d902c440c41e6a00803400c01007960b4804014100d980100720303d89 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 728239910 1250 728238660 728238703
    0x6051e160b1608010503120306150c2b0c03050702040f0c03090c0e1501120f0c0518030601030213021b0f010e0607021504060203180a2d0503090904020d05 68
    0x90541c40d080708400c90715428003c0c2c0000510096801040030024042142d000903105e56415000130b00c0c0944c1c0080d80720300b200d40010a00ca40400210b0312444085d003403003115540800c00c030700b0b03814084040f01200e800522048660000607115000070648980010b10200c0c9010340d0161807401c90750390b0038018020a5854030040c4c20080103c003d94002c18503200d41c0c13810703886c0500c0b80800720810448143d0400c030035203030100410440c640c803240d28100300c8d030020001c5000f0b035600a0201d40c001c01c0411413404002052820b1b500c2c001030514140c0354041d207444030040c20071708201c01a4028241840805006101c0c3c80c01d60003080005d1a2a440c2aa00115566a04013029810010060811411904004d000d00100d581605400e50001d03804000140c5d25510600c10016241400c21038020a0080d416018244152100d00d6500f03556444240b8181c101980d0445003040c4004070000e02035001402050350301e16141d907002c1d80c0240091324400340594241d42d25810181851a0b0551154400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 728241160 1250 728239910 728239921
    0xd031a131d0a0b04020f01090806010b0304020916090504110c300a050a20030c1501080f072c010b070c0905060d11060f13090b040606051e160b 63
    0x100e040810720180e00d000707400508019114403004080c01440a402144260513425071070748100c80303500003840000143c0d251940c40302c03c01e0010394019507050388501030a2010405401184451001e0a10a43c840c0c0300400d29180c248009840340c0a20610300e0502404080f09542042c0100d840b0490480c5813032400d01900c84070688103003051000e81105042c00c0c0250203104c1e40000c01c83da003203a00c0703041c074200118080040038414040549650f40a0002007500e240495000030a12030414440d145207082c0c1e03886203110b995030099902000115809a00c04018010000884c1070042d40c80940000030700c000707420111903458082c1c5c42622007003400241340c02800007048103c00a007221070380c2030145081c81c2e800034001000361500135009400d19802c001055481004907400b824600008680b0352000c411000c181e54007600c6070039540b0382000f14441041c5010300c00d04040d0740303064580c18100508254100b07d0050701018445500c0002c10521815086401e8800e0039907100c0c4c5070321659880d11 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 728242410 1250 728241160 728241191
    0x90b0a0806030d0302120a0b040f06060c060c02010b010210020c0f01090804060f0e09010b0a020f0613170f040e09030f040e0105042f0711040f090210050304050d031a13 74
    0x10b0003c08410503106100050360120000c000e02d07000030002d0300c007003442064000007034001c100c1c0741843c00c02c0524001c80042c92540200c1000c00c054003c10040001100b0042c082e4240d4002c40c41182c0182c00c0111461001400c5a0141200c001c81c001240c1f40a4010001c20742150005003050310204401f1404102955210b12045450145c900d85041405400c0c4040307803000d601800341b451104004a03900c0041d42c802c10100701e205120b08101c40103410169800c0d003800203080420303648031072081410000c1c0722407101114104540d046441c0d19103032420701c0c049a000c20182502035507000402c61094078500150282c0050400151040c6141d4942010001150000740c82c400c6000442c104550507032818181e0403c6040c0c00c05c4215959206a140419114042d642420346c42841c100c08091030400d15400040300b180701f038034080803d0610200c241d5290000b00c0b03001313081c0d86c00180050380c40c6100ba00800010101014001d081c01414400101552801e002c00820960755606007100f1110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 728243660 1250 728242410 728242423
    0x30204260f010b0328021908070503070b07080702011103040e251e050d1b020f0616030b01050405040c021b0f030a0b0403050403080403140c060306030a0f03090b0a080603 75
    0x4201c0020000000d204010030780310050041034001400180d0700000012515542048a032a4020250300d20700d0318240702e1940700ca02c41d003e14451791080c8000440d403410001680c0b01521485c0265070b05150b440d54a05906612000d0b080381081101712208044420802c090300140a29912001e054901b12100f401ea030300c407503804040080f04076014500d00c43d8010381d103540141254110305004030001d000c1034079148201c50310348110310324010310300310124007000c00c400b01200765030b00380e40d41d24101e4040180e403a2010340d01d6040d4481240e5195400502951060300a1700c03042c1000c03400d00da5151300080c115400d640031000980c0000d07040b1140140300503074549903860f003100c00354107018002000c26170300c00380f0340c0c00288081c411101041c1854025000c2d900115030102d0a0381d5115224541906840d40041d00d011003803103040000c0c606e43c40d0103010380c1c0c0b05000c00b900400720801c1a49030203080040c05030b81901804041180421101d40f070308002c00001c241c0703441d81100740c10705031300345454500e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 728244910 1250 728243660 728243683
    0x100b0a080a110f0a06050913320106030207030503160c12021c1b0803090a0606061101050708041a041b08070513050103230c091509090109050303061003020426 70
    0xb440b04d001d201540e0000b0640d01c00d400f094403580014041c6800030340040034520078020845540341283d41c900921450081d54a01d5001c01100450b66592815010b82c0110b000041c0440c5040c40000c4101901c0303111106107140364901500408016140c1410300340c01018544016000100050500c19540249407480903803032901e04880d521000640b1118003000400074a180030001c0402c0e20002c1c10010740180039045030f0204800c0d650741034040c0040000b403405411079400c190001d20304601954006124903007100401180d8108841402103021004104a80e00d00e55009420042e5903014206000f0385003000c0144003c40c00c1c4003c010000e8056900f051081d803c0c040144005800140e9080400588044c0c4020b80300828449608282501b68941d41020350351040003003a103030840001702c0700c0304144c07614001c0307403240d840103400d070b50700c14070054036540c400c201013082410050386010801d80d10b4a401800c158403041ca40d8519140410304441c0c04a801d4207007200880140450010350 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 728246160 1250 728244910 728244919
    0x121e0b10120c021204301214130e07020c06160605092b08092b05090301050906150d0c0501230c0106090c03020c100b0a080a110f 57
    0x1001800303005151150a24045070700640b200407101e8110f000700058140005000a1030b6112600c03013070144214001d0039000000d000c940f040007001a805010f00e00b140135001049202e1704140400192410102007405141c4400100107444010360200c0d0110050704405c00c0c808020f0030f140b90001e02d890442c0304001d21480041000541c0f4074918020301100a5001c80041001c1d951008086c2c01d00e441030840004160180400d51000d40c8041c0418880030300e181c44282a039110550156500c161407250b035807440c440e07104e945480c51304850152171040070510304585000180b9003c02d007034420903130340355460f80d0004d0140034002600c0c0c0c40f21906800c0507140c80841084584500d003003002c907841802d05009903825242d0f50680e0500d10018412080d9000315035a0402503400780c024112403007015102031130582608030303503446402180d24142d0b451004289592202240900403c5120092940040c1502000980010600203402030601442080841c60543c02c00d0009001400c00e186229 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 728247410 1250 728246160 728246179
    0x9060c02031602090403111e070e091f0b1e09070e0d0b04050c090f04030f0801060f1d100f030f020f0d0b04060305300c120a121e0b 58
    0xc480c0c04051907144980441380704030181c580341001d503420955030f035048041d0b029070501c01c801c180090000b119600440000c68400594500040c482c070881a6141e1041d50030a02c01d152065140240204c20302c42a81d80001702e00e50900006003024990300c040c0104249030030000d000514040f44c140e60321283d9420329900c2c04200400089242a000d100100140740d504c002c03c0c18800104100a00c58501a01443d0f45042c0078010350501c040882e0220005070124a944264600c191511b50480b01280c031980c1c060680850191080d1068800b030380c40d10303a074207410400650345510391030740442d50f681c4416514504580004041c0e94002451500c06401001102ca1119058084039040e403054034000a207140c841e0000303009018142c3c40a000f5120b41c50005c41503064000320a01c01844c01c00e0300c10342d6031103103107031144d1036000381c803c201c0f8150080004d1074020014a0003c00342101145040030402e4501e0803414110b4085885603401c001803009060502c20b5184078820140c00100c0b20f0b01c19 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 728248660 1250 728247410 728247427
    0x503060112080c0a021504080c0f01020303070327060b150a020718020c0609031c0b0a0b070f05030d02041815051c15020a080106080f0f0709050405040609060c0203 72
    0x120719801e00c40041903440c0c0080c00805040d800c1c00354040d9554010b00041d01041d03495103c18050b0028040da021500404080040741c4c41c004205254070041030b0061800c42c0d0b200c290035002816440403070f00c0030042c21424009010120702c205504648560800900155130b1024170004150080982c01802400c100c0800c90359000030300d06045914041c03145c0420180302c490f080280c0680d81b12501c8920442d8203200c0300d00404000342031900280360003c150300c02c0c500303500000e80c0c9210b4021070300803203d90b2050000c0b1218000030700301e550082e142d801809401c4e41d1590710f15881030305000f40305540428107004182d1001d5030344806908200c02440741c80388a068403d02601103200c0c05109000300007190040d000c02032949036583c0c0e000001400d081522551800c0a9884030801500044913100041240ea0140c91164090700b00007020303440a58548000909452014010b8814086e0600c800140c56031540285841948a00350200b008071a0340343c554191005079050b0815500240070025 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 728249910 1250 728248660 728248679
    0xf0c11160905061c03030c030f140f0c0708120912071e0312020d020306090606031612060e0403020a1b1a0f09090f040b0105041a1917011505030601 65
    0x68820200000070b0700c1d02c65000160700403403110140d001d0700c800001e82400b8550142c2c400014000313aa00c050010035040e500d03038802c50303007202e0108400c04c40c481c010460103800d10020b558003840c540c00c02d52405445031910302c03041e00450240c007800342e007000030042c122606000035204180c00001c0d99003458129942d91181655008010b8545c0c0e01280204081c0b501c1030610301f0201c40340301c0c000c55070f0300344036134500c00654821201107024210307000101d60903007441c41c200d0384540015100348005100946080b20030305076030380305050002d440700d01c0400c2801203140e4150203136129400805484403d86441008004c400244070a4045a50f204110741c201013501c102e0f13001e5654102a07a100304002008a06009a10080b50410600070403c2780c948d07220f2a041c0d0003540200d021000e00e0383d0301c80410050700e00324509244101001c20406155003000c204248110543c40100f4001a0b2224800308030703160010003046090391a60405120000d908841c3c6002d0801070f03001d0501981028101c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 728251160 1250 728249910 728249953
    0xf0921040509100902030910150e16110d03050103050d080105010e01050714060c0a1103180d02030c040e16060908120721090f060206060a031112010f0c11 68
    0x181d000c0c82c12107000810400000701040098100140115203a003410a0b844c2d50b00c40700c240c21140b0883c81c09041d00340c0202d2480c0b2000031100c022840c0c0b61107035140c180c3c010014003030b005c82d8000e0140c130b261020300b50381090010440450781c81e03400181c0c0790f24606103a0b15203d600603c11041c0702001005000c0d99901c40c021007807007103080c200f490303464031946001003048684002042c51400380b1030600c400c4400380f0004145c0e001c0c15503176a10781e003403a2020440d00d1740b00f4890151258890b00190b0720340341c1004c0502901c483e0000b4181c909141d585008102550480d6031000358640001d032503c1200c85251841101074191464448041805e00007165910601106204214000842d140c2b0030071100c180341e001c5c0b071400c50220b40000c0e960100302824003442c501800c20700c20786d181c1c0003058203440010142d204a2000742100785003444c0d501d80c81103074014015025001407d0180d16549101d003402094182c10102d600041c1d0340304010300040c00310181200c195843d40205601411405408591 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 728252410 1250 728251160 728251169
    0x20f041e050c0c01150501020c011814010e1807080a02040501090918021507150b1e0301231f0815091903030905161d04050a06050f092104 61
    0x14240c1c50b00084011a4090082291400d40c00c001c0e10141400790340400c5000c44e1030070b8080ba05a10f001900640d5100301c84d941286a0080d100170400c01e00144075010715450406051046084a4500102b42034244a4612652aa00c041d0502c100143e0004000350b201c0744002d0114101810640002c01014051050120075034458007121203252001403960200c40e801051095002d404c11504212608004410b0314000c001d40e80e00b1125684501401c0078000000382000d18a194512807000160f80320302d01d0581543da1044002c0034462014880812940b4001c54002c0c14504051442e8101401181d5140201c8840e007041003403c500045040d0006038ac01c00f200e499944889540c0d280650700f07030380f00b64035024680381401410b8050f40f2604a00b40500c0c25120064104141551401082c0c403500c0e000340e15036034007407034900c1c400481141c005105209641c035416064075844c0c280c5500340c40a107883c407010411700014050402500c0c101c80c810001c0c59096070300000f000b06007805184075 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 728253660 1250 728252410 728252471
    0xb0a0303080402120607020d08060603010f180608030412060e0d02150417070303090201031d0303010911040806010311010207062c0301020d1a0a0506120c0a200109020f04 75
    0x1040444d614140f0607446030000804403011440c00c440000d5454503041c0c03498002c1040d010204001e8204201143c0c1620383c4002d15010b017520304586e20841c4ca07002c805070f00c0b0441ea2138a01182c0c144091004000900e12000461400300c51801e0480c01c442070403010001a0388904036500e04250040ba4500c000d034425001d004640d61a0b040044046641203090907080c0d000080c54410150190703c1000c085000b03a03020040300d0f41c110103040d01480e40d0f91002409501c01e03c010000c1044d03d40100584140e00001d00f070038a84d03034844451400900383c00403260010a041d82c0125540e041001c400207201e10700d84202e1029611042d82043d07843d601c110002c0c0c3c04032142c0c0144c252000d4045640e0018850410490001c0e68047d82c50850b400e050101c0c03003265031800028041c80c107201a2141d01580100182103500e85078001c2d03500741d00071056581489a04640200800358038245240d50503448400481c0781d21f81c1384100800381e01024001032285181013600740f804c501d803c9079254810211407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 728254910 1250 728253660 728253677
    0x402070c1502070b03041514040b0c21090607030c092411061f090915020c0f0703030507060c0807020a02150d0f020405100f080417040e0106180501030b0a0303 70
    0x120072410414941c2007021045030000c02e02080212000071700300316404040080006400303462340a400c0082c00d8070054841410324020580714404d01004040c0c2820210410150b051240c10050540b81d0450345d180f100d4004c04100700311640c0500410742d5000e25803601d10007481c2010050100410503646218022500040d10408507004142c8800110303000402c98038603142c088201d1020922120304040712000000c2c000620705420b014029040d0750041200710203440c0100850001e400400c0155600c0c4100c1d40d40c1c0400001c180200030245000f682c1d41d583c1c42c200350600341c0944c0c14400e003013405c000b4800100040c03d58003080c0440240d6046995100c680844500414140500150040014600039014103071604550060042b1081650401d0520180040540349031800c000c000d004501d4100000780012040d91008100c01040203100c0d0500342c84800030080168240c1100c404585413280152203030200040080c0201000d1a0600c01203005102080300c966262000400707004401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 728256160 1250 728254910 728254949
    0xc0c01080405070303080415050109020d060b091c26070c0602070b091009090e010903080a090807080706022808161409040e0307060203011508091b040222140402070c 73
    0x11041c0507400d240c000c8c10302031561100c01a1000754400e214070300b002460402c0c0010104045007c3c2c4034500001005545290541c2c0c444540c0c000c441c003000c40301c84502c80307400700d51801700700a0032074030740340b024003440e00c0d01414504003404103100d130401d00a540c44a0810885405844200e550034075041c0d600e051b880001c8403003661200b000c0c1d00b0a1800c941040e046004600b015400702606900030382e9406000d40351510030204a804105000d00039000400070340010900810050030528421f8000604c0c180000144802e0400740901c0a5456900740c1407115940d607000c150a50840d0300c1c003030300f00e00c4100200e070701401c010b102072661260b44001195500165549a010b50100107200c01a2503481c841840c00d10003e5009025002d851b075200d49445900c1e5106402080c0b00d8060900180005410110b203c4c1e20850b04241d420fa00680030009000d084804c0c0d030401c40e401d05407414280c002d0f803c3c04024050340c0823040030980113500c1030100c903001c107041d00d2440080b683c03c0d5405141c260406e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 728257410 1250 728256160 728256173
    0x609040b030c04050f1605031504270b180105060d0201030b1c05030a031125020f1e0f03150a090c05060406091404020414011409030706050c0c010804050703030804 72
    0x8030b00303801da4000d250404200c299200802554412910240e60b0080000380c45c07001d036040d02040d205009403c10107080c0808030300340f5500c0001e0f0907000405081c40c00b509d60110210b414081c0d80d0032205004110300f0311020116007407500c0b00c545688002800680f600c10041815020b5106001c0c3c10142c850103424182e8882121408110fa140e2071010f00034005404c000342c1d01d81c010030a110000e840c2c00203500c5182c01c018242d860b414248020310390b0296000240d09500240e04c4016a8405603407080c00c0507685d80c203005010345199844894410741c2c0708008001d2003114045240e80281c12040e44481c1c01c00f11402d0142c0c0c00503083e1000507100398282020010b40225810a03a04281d00040101d0042e4200c00c0a0049031004400b42d02c01265190a02c8107901440c803c922540811540300e0b584c541c05400121003c03010284010300302030071400003a1402c00d16520141c0420f0001859800b5100284841d030380030b030780a0034600d0440c10719039106a51a040c80c48003400704101e000c0420100801e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 728258660 1250 728257410 728257423
    0x314090604030302030c072408040618050c040c0503070c0b04051509030c010e0d0c0605060d05010218010311040e18010207020901170d020d020616020c03010e060403090906050609040b03 82
    0x1000380195480c0d03516850042c0d9607a020110005a03442420000200c881e05500307116001c9040f890604001300d00c00b902a2010b45e000350041320000e449820242d691501003000307140880c022001800d40c03a444e08203010445941404880400c001002000403554001c118050899400110300d804c5503642d00f806410440107407214000405000c05110322035400001600f03034002004000c2004a1900f49003954880344002000c0106030010718400105000e50b004540c000400703414521081007075610182207901c030061210700016465001c4404e542e0503c9415400c200e0360580d545401d0401d0280400940018854996010402c0700e082001a080d0181d505c160f5001d481e2124a5841d161044030340d502000c10b1404030301c0364140340483e0600c0001c910b28104881d40203032442d0b032203200e026031403030b003504800d03100394890020440d149490034401d120b000f10a0402402290070907280007840303003007035074002944141403002c180441d0b5550700032540200811140000e007c104040824207041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 728259910 1250 728258660 728258677
    0x1205010e0a140f0304120206030405010e06090304080c03060114150f0c06060117130b070507020d05010f051b220b131a120105150c2a100c0314 63
    0x980d4044010400761081d108055007442c016510401d241107411581e03030090707105203e4001240c00c00f0f4400350410600558105001c0d50012600300794158074a40381070340542e0741d5209503000050800411105120030a16502c0c11800b4111551400c41201054628034240b24419500c0d400344110000d40401151800c0d400e60503001d4480c00d0100485441d407108440942c00309001004001d4151001e0000502c6003414002000c1052000d898506131407500400c0c4c0b03414041e042003090b0241c0c1d54000b40ca00700d01c0c443c00c000f150590f0645e00c1082510400f40907898401140c20110071403012040079500307101103401160703003002101d800d2142e03d44e035542e11610204a0024003410351030b015182040a890790869201c41c460b42d004500c0000e0706c0380750a1002da00084100610040ca46440d2000c1101400d024213400d2180080f003075402e0141580e01940c112608002c2648070740201e41c010350103048202c6968009000490307000e01140f42500c1c0050421458501401d00140b81c0d0342540c2c00b02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 728261160 1250 728259910 728259913
    0x601120903080a112701030c030204030b2811180102070302030304090c020a170c1213050913020622050414070509030718060e130503070b0c160f23071205010e 70
    0x2104030b2100c086100489091140000d0401d007203880235902a000b04d03002c8a07842041000c903541d402170000c42c203100c42403418041302c410004000003907260f80558a40780050840140c0e8540c5c14941d504078180d91000b1003419074210f50810805a0f07008010384044502401001c1040720780c2c22800c0b405d02d148400000c20410b158448100111107001c054a01d14803190b0490b07481d82400c0e0706013180d502440481a800341c0c00c040c0240494100000e40039009072018110b040d0010441c0d0014105410103103400081d84000200e03410341300f030082c19400040c4000d0f0740400200c42002092000108000d01c0541488400200001c4944082240340010f1081442030031a60000044840c0903003228803424500b5061180840e00b00c41580d03024901d1141d100c4010b626004140c0c1c1c404102003401814220340c003400b03000c03c62603400c008030203250b901d100b1070240d000000c1c503140081961168212006665a416008080c0300c500040d460301503c0c03008030640c500000700c0c6489405045405250001c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 728262410 1250 728261160 728261197
    0x60e04080307091805151203040506070201020313030f05060f060f100216060206060a140307050d15050c1215240f0c060105030705100203030c070602090d0b0601120903080a11 77
    0x95200c5944498060b0b46c03000000b400d0b41b12041d0821058464920703984040c1e4004200400c15840c141005118492040c015070b81041c0f00340d001420412155801a038842200789142420041c2c24454564800d9100624807014200403010440b90ae0030701401c40d004409041d1003801a500810001401c0e043c845c194035201380e1111002900c40c1e500703562850003080c2d0703100041449200c207030302c0440079403016000700000c0e4075100401845918118054800b19540780313049d00303169024007502d48035010412180c0d5403411030490500601c80e005000c12860030b0718440a01b015036442070781c2c0c800c44000e000204120803030500c401e40d09214100040e18208400034411030042d101150242c101c95040701580c660039034810611031244411b0b031401d001070f0403c2000030007200c0c40f00058003e080c000e0b04010300f001c030003402060301310303141880950300b211001e0100422581e0107443c01d101c1e04460700081c41006101c1e44c0c081c0c01c3c00d0018000400c1140c990740c0000300c4034034400a130303600d106168110006 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 728263660 1250 728262410 728262449
    0x30307080405041d240907050112020a0306120803040b010e1e040203030c0d03050415050c04092a03050402090c0406050d0b1305070503090d02060709090b040902040501060302040810060e0408030709 87
    0x5102c158117030900400449503001907511400841d00c2c008072001a12010103990742c2c400c2490082d40301c90444424165140000304940b901002c03075000c9903101d08805580c9082506180250000c140c3c00301391200c0481e4104041c5440c1010700c0c0d0a620f00c01c4a5281c03141e280ca2002a0440c01017090003031a80c0310380f0001d810826499089980101e000b800d09041c1c0116803c145030039240211050114a20200310820007400c980c1d00c00c007640224800000100c0141c020941031046608900e04002500e030001d104c158a0003a401c242c1118103c1509443c2c5440c0c854040d10900409140000c0342e91b5880da5183c03103803038800646840101084c010401c500d0002c0e00504940c200b500c08019500c40c0701104a8030a00002d8110302440c00d645401d0805481c00d2804405404040421a0050349500c0388000685940c000d03d4060944d68501584450400c00c000d4600042e00c04040c100c241814802c2143e140c40c0e21a0581040c0c009202568960380c4030340c255000340c5035500084a40c0d03050700c0b101c007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 728264910 1250 728263660 728263693
    0x703020c04052a0c03091905030a06020a031a0108070509040b0a0b0307080a0204050102060117030c060a0c030f05060918030c0a1203050f0f2d0123030307080405041d 73
    0x81a86090a181d0003003000150000011301070340100e08000c1c0e00410040e086485c06030f800054140101c07044650f81c540f200c01280c241020301c1c204403540390b004520080015094040d20b616039107020748922900c203410000a0865402170030403c1441000100d00d1010b40302c6030010780c0c2051014000904607a82e60050b02c1d10340d401264103074001181d04000c1404c903019070088030111001640101216402c00f0001c20203c00165818409448100300c0d00070200401c0c031031244a2290b06000140d1410f07100405003c0d1240503840d0030500f4545010841c8640d90311705080c0e003018102d180c4640340c501c0d03030300002c0c0b941c4240455038a40b2b108100d0031004104c5541d50f400101000307582c0070b020f59101c0c10100c842c0104191034154103207112000042c0d1051b0080024800070700b100c0003e107000d030070f0307030b103244070010f6080e045070804820142d101d60320481030000d0110155402d600031464022a92501c010a000720300441d417040f5101c0300b40024011010b200c5401081c0414103030b07264545c0c40da100c007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 728266160 1250 728264910 728264941
    0x12050910091505010b0414040525030e0f01061a0306030f060a051902040308070f050309280e06010c151b05030612010c0e040207020a03050627060114060703020c0405 73
    0x3280003e040c031001103000790841d0b054808494005581c031000510301c00c04c0002400c002003501286500d00a50001c40b040c2400d0009402ea500b92000a4400840420142007074034001140815a041c00820800c0003801c140e0003008506c1c03000150340f2500c070740380001d0038441e42c2c000e50703455841042c00b072003030b90b10b11a803109000c1c4640703092074044070003880c07407d600b40d028a00c00030708405004d114510210b80c403506400016482402a40d02d031034101e038000b62040c1c44c07051411401406840002d04c3e0003200c401035a0240848814a68990bd82400000d115108100004251804110403495940c0305c42c0c1160b180c2c1c0c0b000034050240d21404010003041c64104075130261180400d0395103035001d00c40600c10b100283d40360350b5840750289400000d110180d0f0244508171f070807480800000012480c14084207009080d4912400d04940050380c600c2c5600007240085000c540052004010103000e509940e070000d1410382e0300c0c40d110191800c040e800e103000c0300011a0030900348401c0203a60303001000309 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 728267410 1250 728266160 728266193
    0x80403080c0d0915050708090a0302040204091e15031704150c021c260c0f0f15060109030f08090409110112061409180a060b010f0f1205091009 63
    0x11014038913921045205800e2080701d20b40e0104208200240210b1104001000c3d07030030014005c81d1350141d503540490102c0e4420b9210340c006680c1c4250507007941c00b00c209100d659803034407001407006d900c1c00d050141c034160b0a480014031018500741000c64030650481514000c204007604d4042c8114081c0000c0d11204145070200e06c50103000103441d9214134a0400e000c3c100c0d8014074110010110414481001c04c520310210f620081c7c217002503468500200921050b0401103c0a4140e26000341341403490b00c81d42458506241171107608000059a0110010040702d80020340001c500603d4140f0040510403401c016800034242a408018404000001a6403131001e98848042e40403410b41c0308111100b500030303c100c40d60025502d08280ca0200062a045440c035806101038070280d4011070701d003040700b240488c0c0300c035251229520b043d82c0200200122042c2801e00084c40d000d20383c8024040080a1548101d131541c60010845499042114100c10412920200303d0702104c4d041c500f4000d030700700c0345 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 728268660 1250 728267410 728267417
    0x90f0709023f4209070905041a1c031407030c152405010f020706050304121115040c09060e040f03032409050105062109101a01090e22080403080c0d 65
    0x804200300d007880545584194070b15940c903d84035040c00100005001d280e610240e60401036a401f000d2a92612602d00b200414882b00c010015414130303018115000c02c10010b440460184014404603400201d4400c216274802d081c20b40d9103000743d004c000108000d03c1401c000b401b00b00c995032a4020b03440080d0080e10001d8940269074600801d0482c3e844400340140d10000e01d042c80801c0c0000d0841c00b03943d004e041c043c101404418030b403a00843c60140e160180a55510103441480144098451944042c10641c4030a224007800c2c00d444a1000e040500300400040c0b4179040002850310a0713010100c1090320f800351403c0c40b0024140c00300c0c800700354000c006071240b03006d0001a00381390210450f41c0140c201089041402880c6609e00341600d0010014009401400010140d25909214012502c0d0360300c80180d414400020004054102c184c10802404420201f4401d411400c050401030000d001207041840449901d8400311a0203103601c000c00c2080c0c00b08810400040124004040d81e03441e54 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 728269910 1250 728268660 728268781
    0x209040e0303060a17030d05130c060c0b0f0910050a02071a060d03050c0f0102210a090209060409020604080f030405030f06010e070503090f0709023f 66
    0x3010039141d2009031080da40c0500c0c161810031484800280380745d81c1e1145c400c2034904003c0044201c030240d0b44104d45420403000c20031241001c03c039401e1800405402e441c9030059029400d562080301c081005030660030204140c0c030000d030f5140700c03c01880d0442030750b1141c00c0c07100d41005144030020b5009110125203d142d6918140320580d204100107104e800f00800c0070907204500d4500383c4440d484469824018018520080c109580900003040280040051030009805087c95000c2c1c1003000b4046503030150030600150017517694000400c0d04260f0440380080c1d019600c1c80080d9880c800c6334480d50641c00f900242860180020010b0000c030b0f5019401d40304103070850f03214036032a001309016000c2140c140300089046207129801666010315454200c0d100b0300c5050490520b021407035032205200d03075000224800d00111008006220007051480c011041c2c003920b90390711a00c41002c07a580c10581c0c0030b0000581001125080c0351400c03281082c400f0480c0c20034406c00082c212081c0410307030046582c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 728271160 1250 728269910 728269931
    0x190207090b0316061115070e040c030b0a0501110a020409140c0904150203041a040c06030c1b1103010b09040f051b0d060b01021c1e14030a020f04090e01020904 70
    0x329000798119940c607003d16070745003003903000c0e602030f415408048814403804850407103039026040f0250003521561601116807000500704415908180410820903090940146858480c0e01021054031404d00705a0b500e242015012840c00c03a0400029602c541050700d004140205a10041200c007001800d95001a040c00301b4062088420384004100100501849200400a40c0515000703480342141169009104400314560300e000c0d5015140e40c82c900c1e004000003609441446d0400146042c50b0360300c2405150201c15020409601905050210f85a81d1050ba030a52003920002c030011302d6891a4181420501d900c0c26554004507102d1280b407084481c2003d01d040c0c0902101070081425032000e4175541c070132001c0c00325118100c0c198030400d84c0c1e0101c2c900302080790b04841c01d16903640c00e40d00c001007421007403018881071100741400a014000c3c1000038819048030740c000c4103a80d02680d00c0c10b6104825080d840350b603018244042c41c100701010b031050190020040070400b1501400543c110 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 728272410 1250 728271160 728271163
    0x15041707080a020303070f020a1503020a0e03070b09040917031003060b0612060418051f180c060f120227090f0730090b0a0509030901080903190207090b03 68
    0x6001029505500030701c070460001f1510350300d0503541d600c01790181413641d696940d0302d49a0340c00340d000c80c800701c1c0c0c01050b01448541d0180300f001c103100040f030082019601c0e0449104481c810ba1560601458855203203a051156061820f0031180b403040a40350f4a1a109110070214145800100c42071420084200340e03520f404416503000702804900c0c1e0703044e034444908110042a101e0300090710045208040408a8818032108410110310840105402c94070201e80040710355203007800140400841c441c0011900c60f410300016541c86d0f041000d403501070300038142c50030303031208400d00800c5000240c0c00703c40c100c00c400d100218443d03103070081000d070031401d0403c01a400b00320765001501e4424000528901d100302980c3c00c0c25910250894107000d856207180c5410001c80b6900b41007107460341003d00030000740400042d03018500c60402c0003107041000d0318503200d2190085541c1000b070b49201240340f0f1a01801100c0c2d420700c812180c442c1c000086003010707490310443d10491130030034030304403e44126040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 728273660 1250 728272410 728272423
    0x32d051e0f0d050d020a020a021909150b070807020a0b04080a0b01060309020d020105031f0b04030308130c050d030e090f060411040311130902100e09070c110f1504170708 75
    0x20b440d25114100400120b07080c0081d042020900218030a01c035809015845521100b98851940c04806003003a082034184c40940d000074400d0b00808000c050308100340d0000d00b00303940c0b2056204801e40d40e03800c4c4034000100000901c0c1c000c540c0b01c1000040029081d00c00042d140c0b01184907100b0714580341ea890b0000d5040b241d0342030700603401803503003494100158403c100959010f45804000c0c1c1d5608402108080811031603080380c404400300050500030b040e0070550507540440400c400440700e00f201d944000001001d4804c4a0003103520141c000101406541c01056110700540007114034603010350804a03032401607400300e014600d401c0c45000c034040140c0840b402da03500041900c0301c6045501c213201c800c00c001c020b0740b01030540e612045001030791020028141e41d81e0540c2c07140c0c0109010006c0007060803010702031a06003d904034841d00010f000700100c0243d44003c503040ca02d01381c0e42d0404a4862202c4040582c2021b00c0007034040ba40340c0d0020361151820081034200d65080381c64208840c4d031003a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 728274910 1250 728273660 728273683
    0x3110d08030f0618160315090c09031406070504140d1a040611031003110f03011d010506090112141c0903050c060a17181005150901032d051e0f 63
    0x11001039150302514087d0700b000207094015116100032a541d4900390003200d6507000c60000054000360304209000b0700404c10f8a204111501600070340c00c2102026116100d00c2c4100f80e40402c000c80140c900356180040400855042201252180b07014215001c1950702203074220b445a2500c00548144100a81075a01c20f445955442d48401d00719196080c4102d80d0010103039021421101704c40c140c2d1801c2c0681922441c41798000700349242c00072103c0742074500041c4900e02444a640040060f422000605500c041e00490701d00c81c01c91901704a58281040702501d02aa101d003c050070409075400889003044901981c2560526425801040700d40d10402c01e030100020014100c416802c6026003495400c5444148654001c10041c40c444d1d06050155480c0c060362a43c800030070568850702070f50b0b002c40c881c0031078480c07400d581150380702902e500810420190365541a02c0b1400c0c0c809030080f04210094110048414200d100d0580403004d090080c01985540507013a40024450740000d008240d04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 728276160 1250 728274910 728274931
    0xa03230106080712090515040c0e13020d0f0b090303150102061e2710060626060a09020304060203070e0102031327020a200f0703110d08030f0618 64
    0x94881c000b0486604d02030302081054030f5994041d00d00000c00400600903084449118205030346410300f003010004025a00880420560904204130b200d40c3c9026100c4259044800b0182c0c2c0d1200c3c1440c407500404200000d002c1400c42040c440101000030145102b010354180a01c44180c4c85401241c80302e20a9075902c0c0d0140340d0b0b5200c42e2400200c556899442500d445a205002e103142c00b15182202100308403c0c8543c03c0712035204200c0c502400b84030080d01303082c00d00440d80c0440340300d203012040405120f0221500c4080120301a0307070340c4d45809001001150701c03e548034201400c0141c000c5d030042e1400720100d07001507003600d5194004400c0d261445041d03807030032581c02d103031100101038064140d03100c51070f2000c0700b048401d1403011803001d0012178400d65101030010300040c11000b885803005140c00d00036442540148821080024843c050766880000c0c011100016070105003444541d1100130b050300b10120400c440d80b10026880c0e40708210803179a00258040d012941004a5001c0c0e138180070740d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 728277410 1250 728276160 728276177
    0x40b0a030b061e0d061512081e090a030c1809051b03030702040615020d02032b09050105010b0310050d03092601050c071a070905190b0a03230106 64
    0x5903c0c01d4900390502102400411420440380307400142c00603444001105c495036104034207403410100e0084400684002800310000d8003107515a41c80341e010f8484410469582c108030078a40740c01c51000d5a40840c0b000c1d1035210050b4480c607114802000c80d00495401e8a0380c190302208007201c40c002c010700c40c1c1e0080090b110101e08008000342009808880e0341d0944010010500180c94034810030000f01010078510074a00e1000704002d081c103420a00b40f40071940240710960811090b000342e50300315913141c55510301d020055080c0a000d07000c81e86001d4010351a2400000c0c0d41205403000358032540c01c00f03d10100040e103071006c12030740d00d60310340015000400d00d00c018402030942411121411113128401054a079204500500b52801100c2070f0607901c001250301000c0011640714402c5445515900313408034600f0303010003045290f003407040320b1007403030002c1c15000300307090711f4200f1405807a0040e000c540d41c0405140144c00303050700341c0c5054050a0700711281040c0041e102050b905030b030f6a82ea9150341 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 728278660 1250 728277410 728277421
    0xb06130501080a0209060d09110117072a0c0509070f080c07022107062015100b040e07170622060b040e10080d3e0a02040b0a030b 57
    0x110540010a031030703861130b400c10001d10140da03410041e024682c0d0300700022490101c82d181500c01aa00543c1d5207050008600c0c040c040d040300d4004c03040d4402510700d01505680150103946007a1401c3d115410300c8448620b080c41c050100105003401a900142c40c1224640c458031812034032003000204420010b01c025000c1100340d90014000c064042c002040307171b241c02e8102030b00c403207000e40c1a0600610307d90000340200000b80c2c2203003561916480e0035100201541c0b00049103034a40c0404d4030580100c08206001a144040d4840401c0c054501c00740015112901c0340064104bc80703050340e622011500020340c52280b03461824145120342400380c42c0091324000020301189441503401840c41480c0c42d100003080140181c2c0c0904001c248004941e502c43c14104444001d0000a410081e0703543c01903850b40882c6508203180e00c10001000210305600c11840d40c1c2400c210f40d052240300300c2d6020310924070421440c0010001d28640c021181004640c4480040191054841c8801420b0a816400041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 728279910 1250 728278660 728278667
    0xb1806070f0504180b03210906030a14092404030e04050a061805181c081504060816140d06020d060f0e0103060509010203190209010315080a03030b06130501 69
    0x2421001d2034140603060984841d01020f000810344250386100390b0360b10b104051480c0410010780c5952000d90851940406084c0c8001584140c010880c02034070008041482c40380503a0007001c1140c41301d601000d00342409581140c40e041d90406541c1c13041d80010b500c5402a001490007070080f036040c0c503000002c2d0528020300010303043c02400d4140442d50340b4800100d18609407200c2c980ca48ae2001c0020340b44c40c00e0b00001c032441914510142c45a032209000744520740cbc1c9004600f03454002c41c246a2a10b99074047c519010740001d02210350801d003400340000e4032140005020948003241c65240905d95210202140303030400041200b035100c00f0b070240c09000704da807a034010030700d01c000e6550115416403a465907982c50b2856034044130514840f03100406c248903207881000c2d00440c00303200a520f94103040815160b05000032042c2e00e4480c1d4002051103846e8025400000d500c1902c04406070019074400b802038440d854800b058000c2400c0800440a40c5041c2080782d0040030740c06400040c1d981480e0044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 728281160 1250 728279910 728279927
    0x6020d021609091103030307050c210405090a020405031603050f0a0308010b2d190e01080c03090114010603020a0e190b030c0c1b0a1e091a19030b180607 67
    0x1a64a2441c480310103666417410f0006500c10050350b1220303a078500390b103030301185840e030411456012020380b0300c8080fa54010310740c204c4080b0b540c21035201c039442d01c4160b06000244a20741c041c56151040b0b4490001864007500800c0440b4000c800307071114800e8203a00c080e00c03001c5a050003000100300c1c01c018003001c001900030301030b4178081c1031089031001c0c018080304603502d070102c50031020b950010414182da6a82c80302c401124110324074118185003007050010340890405410710f02c0b4028080001030460100350700071406000a508804660350307607100080c0c0258040031085001810741e440007001410440000c80111103460342549025241485100ea990409404074014827000c212041c58038030304204410200811392507070311921142c0070801c0340c404060740c000c00c001310b840b1824401d84801513540c641256000b000216680e40c1540680b01a19541000f0551002000c50f424512658a403000026244650900015510b0345140c428464011000e114280c1e0311840008068906c201c064 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 728282410 1250 728281160 728281163
    0xe061305011b1401090b01300204020d090309061808030714030702100f080a06052112041202090a020c06040809150d2f0d1e0e03030106020d02160909 66
    0x380b0340c140065600e52400790700164154409079114814503051000454181c1e00409001d60240001c11404044211410103407014607290b8050300384003000c0d5126901250141050620100180750440c0341c0039010311214041e80c000206d2035070083c0b44110403603482c8815540400c00842c1000c000c0e503511442481c0089009010780014030029006803108441440030240c2500c40745855090350000a000c9100100009200d9003012000c005544541d0310003510248040c4551521444048001c1d1802800d02c840e200c040f500000c0000b000303581906d60488080c402c80f07247d0f1081c1c891040034401ea0141c482d140c1d50b180c010401140000f40c40c00c00800308803602800c414000d00c00c4030749000f010303008003d0301107106403950350454980840c00400444d071003076140fa0305d440036105545018103000340301c00c035a100c030781c3d4410041c01240180801c160240c034004040c03121a21548c6102d459801c00c0c0b1402e0f016200da40070a0282500101e40b81c1004d2410025916a40d8a4501e5110140030384200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 728283660 1250 728282410 728282447
    0x1f18020f0f030109051027060e070e03010608070305030405091008010546110d06030f030212071511190809120c030a0e0319120e06130501 61
    0x12001541408007505519810361900c60700ca40c03410703815900380c50f00200700c101d0b80c03104000306200d0180103d00c3ca03007040c550386040440700c61159419400502c030607000507400080620420113500d5000416482040b000d170001d021141d501c0c15903955800716400700400541083c0300500081c01e104045640c46107110601c280c40d40d9603240003070b0840b0000c2c0c1d0030403004094900040350a020f03510180d00d00e90700040300b0070007441e84010662032404107a914008a81d840f00c4070404003009840a441018182030700c01c0107048e1383e80c94007003048a1500c20481c0580509031211064144920688484c81d4112600704880a0040f030880001c007444040300c445c06c1400d00880000280f4007001c2100c003110354035041d000b4200b400c800b6151030b00c45406480358581c00c014446080c0c80200958241070b60f241014481080044000303802d18041e60030b5510000b042c81d032258240012041142c5041d201516081503040d100020300545110745603a10640c0700c2010410000c0e0b5104031010b4208040500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 728284910 1250 728283660 728283667
    0x25051207090207050105040b13020f04020c03071403030a0509070b070615080a0f050705030318090402210d030f020405011d030c0a0308030a0b0f0d0b0705120405010c081f1802 77
    0xa16000b01e070000041a21030341e66075400c0000b0041c0c0c0000c0b15800494140703ea81d0f4040003940014441c40066111900030307900403405005120080040e01d50143e440110380e0000001464226584c0d0021601c0300c694500384408070b8411840460b0301c0050b1050300c4010303850702d030680d00e4203000740422280c0000c00051104000680400074444000d00900c506d100c06006201d9060451811041d80c2003580302e5041002418002040440f801075a054240e074400c0090341c480c000926540101d050259002c0c96462008444002c04644210940e80b9030300c04214464040a940b01280618041d15001c59600e4440d09044280421004480e0074020308070313001c040076200800d100c8607040c1e204070b46040004c0148140d142060245286d41d90302a40c0c0c0c1c840110092000401000344036a000d419a0100004151050f108000300c410840383e5507050010307030610380742290003401541126030003d5040c45c04111010582c0501c54071400c1c2e403001c0c0100450504204075404c001e044c42e00c14010340c2c01c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 728286160 1250 728284910 728284919
    0xf0702190f060501181d1b0f030708100c0207050d020409210504080f06061525030e03150708011a190c0b070512070c0f02130c0225051207 61
    0xc3c0201400b0b0880f44422014401e1900e00e00c0c02551010103000314004000120301c4000314000410301c2c2d0010240003079954406e000e01c00701d9218034036440f400c0c0e01805540c0c0c010030680700c0012640d4507061a6030301000351032040d9104984ed490b0900039190700821510260300586415000461210b0141c0d0712030764480c0c021031031980c01401e2900031802148012074104032001c010303c09a82200c130754001034180303403400b200001d402400d0341480d0100c1c0076000c20030294800c0304440d0b580448a000785207000a010906010f01503140c90040340d8841c3c45400814030b13141840b82c94a40c090082c980b40c6010136400d00c20304190522610079211200c003421f110303505960103020386583c0c0c07500329501e070702802c4401400c20280c003c000074005001d02c4810400d84040c00d5a07400c0c0c0e10750100403490b1400d18242c80d4948100b031000742840c0a0360180408801d83c0003050036500c4440b480045401f1a0042040c02400c000e01825507060342c25144038806081045041c80f0f8068400100c440c41a10301a5448 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 728287410 1250 728286160 728286173
    0x30506040f0603120f18030222020f07020f0f150a030908070606080f0d02120a03060308031f050d0224071401062c07121b12050f0702190f 61
    0x5503005561500380b00c07001c50440d64018a600f005c60001780b402e07100c110b000c20001d8500c1465844000d008420b03c110f1418400d808001c034009030344a200d8151740d10564044030707101c25000b1480503403080c1e05a281400c00b034540789503034540721400640303030002d1510840400031998000e0011002810f446241d0400007401850003403010a2296400007052814000d1003440e01c1c102c42113045059000605e48404c2c9a00040c800520701c0288031407607580e1840304000c030068080e81d400200b003010040300340b10201001c40c84d03402e00c5441031032007402103c0d0360f00204849544510b1002e50003001c00500b208004d2a07481446c0106c0c0e1401c56201e1500340705680350344040b02e0600300140079954801003441340868000302854a101c4c81c4810b41810384040317400491b16800074180500380300f07280a04500016550700038804007c1e003809407103152055520301411518840810860303851600d4000b940700c007051500140510750703945c014100003034032007076000304040c0040c1c003918840071440054000415 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 728288660 1250 728287410 728287421
    0x1504060603090c09060501050f0325030b010f2c060712090f080c0a0e1506301b07030e030601030f1a010e190f02030c03010330030506040f 61
    0x36190340c0025290180e0034508002d050582100c2c0c4510b041a00c1003000c3c1ea4444291102e034450b108540344d803038440014140e40c000725602405003440c0110f8590101941550041d00030070020f03228099004400b8104840580e071481e10b0f034035661402d10108501c03c103a405150108000500150310b45881c80d10f500c0e00300c86106020a00061900800307000366041d15901c0300c014028200103090100017071001500000d0f040c0903d0042e40c00880000d8400c0011001b00d6500c001e01502aa80da07107001100114400880380040ea10b00812000ca00d40020341c3c410998440c600710140c400690b40c02c0025041c00394403c00d400da00b0050000c01c0c0d41550390341031111500a600c42e161400c02e8190358a81034014155404030200503954400040000c02c01600c600c079440001c0380f440c40100c00c00d03000d2110041c444036818000051010003040245207142000714180ca01645d80c89810f20448258208a244031006480941c00070545400301d260013900031540080780180003080303091011400c2e00441d038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 728289910 1250 728288660 728288669
    0x30a0f0e2104054f0203070c020901230d0c030f0f06050108010c1106190c12020c1608030c0718021b10050a0b0d0807030504030c17010f0b18150406 65
    0x70035401301d0340050034049640d0200705401d03040304000c1e0402c004440010300000040804550000002900140700b0801010003a03030040190340701e5619850721094640680007401c0f0ba40c203526141d103200d480e2508600c20800c3d0b000521189003070950352054a1243c40034811942c1d0300b440c10b5801c00107445401894060310408000240110241400400d400c00700040b820017600641c0c14064180e812034001002490504030100700c814011f4422130703a034007140c86410425440442c20b0004641c000c62014159110722200d40401920382072025200e00c58101001d41c1c66000c0c050401504031140d4021040041c2c11000505002c0303814040c80c00071904010f104a00e8000e080c032007480540d00d110702600860142c408002d003004000c00308440e403031203500107005d1035808626541054407075407c4070080e6500001c0480690303504d0742c80072058042020201c03415400c000c020078031802d46200e5202d00800c0201b2032070079440100085004480c000c0d007420a25141c0007402041a11280203420040c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 728291160 1250 728289910 728289949
    0x90303050a09050303060607060b1e0f010306030f061d0a0605090c0a050307031209050604080f0d08060d110607020607210f0512040201020106031205090405010e0609270111030a0f0e210405 83
    0x100e88103400c00006516074150cd42c10f1519004050003c1a003825006c84c83d5a031186001030301410040325021810801c51442000303204035200c0c82d0411095400060148462900303c0300460b50398810055520203030300a45415078800c04041012030011020900410f0080c106940113544940100d0f21036400342c0c01100d640e0b400100c28000d00c0e00f04001d01034410b20710b4a0000f14605006000440100722842c0c0541541c11000d08044684d4400c01255540c0b540240303003076911001881c00e8034810594558406410300645440c04200f8003940c0c010040405950f9407a00e4101c6040d21800d5400025200340d046642e00c00010000428a44d0304018482d4244c9031180c90b09401000c02050b110160811000c1000341024400251543c0d00d05030740025489030b030000041030100d000d450440044802408030740c00c1c084d9001c1001003500c0114020003064006101030b02031400103505654541840350295840302980031024080b40380100e4501048130681071070255503500003180c02040d402c85c2c0060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 728292410 1250 728291160 728291209
    0xd030507080a0507020c13020909040c030c0e06240c0a150c0504180c140304030807031a0a1707080f0706020d08040b06150d0f090303050a09050303060607060b 70
    0x42078006455079401124080240210b15120780025100d4460740c240070b02071004500503101c2c1c0b201c01d406032a050503000e0040e038118076041c00c0240d424015440180e50300d64a051011600c441c4071130b070807442103a029018121810004820104862100114030083c55042c080404001390910074080175500a0401401d800011583c134030889090035045d03814000104420055a080b0001c0d035106420803800000e87c1c80d10040341900d030030707410050300034410342c0000400041540140320240a82501c1e90104929403601003141003c402000e0a40c2d40f007540c0b04000c00420154071904440780c0e420000741c40c81e203030345c030301d09a480c04081000d140e03400e80003030100344281a810055515242c1040c90312200a08040c0c0342d50300301030005000310740258034035501c4d00c221021a804940d88090751060412403106404000740c0200001a0103c00190030000410072400355805400040d540101c0914a19103a80081015641c0154400c0364040c2d243ca02404040d82c8494650000c05002e6a00070035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 728293660 1250 728292410 728292421
    0x1425021c11040b190b0a0c021206010810050c03060d020f040608150601050f16020607020919060801020c030a0c020a170601030c09021206060a030b03012c0118230d0305 74
    0x43d41e00340020580681e030340d514600031410500c60440c0883e0f220a0b502a51900200d80482d030a8030a00c2e4062340109000c401460b40e0f0390002461812100a0015100c0c4045030240140a0712015200d10071480418800f04a151519100b8a10002d10051007810f41c400551701140503640ba81d840840e05400c0030a40c011a03c03c24100941e0001091074800d24000300102400100d02900c504820000e001c1e01c451411500d070101115403180c0c004010201c0e52511002c500c141005001151950600301070700051404814001c0c0c0c2e104890070005141018520300044800d0380441c03005a0b440320078404001044c000d00d05448074400c15a2000d880c056042d401d06100507001a40b044150390303c10050100007a0004060a42060f4101d40f15503407031009890450240026040307165040d4600f00542c21540c2c86581c80180d00f4446016124225141207411802c80e805030342c9800010441000120000360f540c4c0f202e911150303100400d990080842a0b03083e15141fa0901c0d440c000c00c1d0f880041c0311 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 728294910 1250 728293660 728293669
    0x16021c060e0a020135040816150b030a020307060f03060306060f17060105010e01110a1709030d030603020a1202060c060708063615030a06020a1425021c11 68
    0x41c0c01da09205000701100003c074107042921550202c0c85c84521590100302001035890460390b4030b1191042113a005002402c0100e00003040107407100e011131074805d280c130300c50401003218041d503600140a05807280c500300041e10310001003c0c1c010f0406a8400d0084001001c501c500790241c08078000045000d8102900384070f001100c00781204143c0e20030001048075a0348510744140200023840d2a070f41d2003410003480d40c5000403003100100460509004020780251450141c04445011401c4446500340d42a0650841341d1038003010750441d10240d0107100b02c074040654001d030a032025045a2074007401c1da20250404100395842000211039400b804058039185003422005038443c01c9262002d01140d03446291282e41c10200030407200620005031007980d0241c180c0a0b420005020f47c1ca0aa0581c98040700a5022120304004108118890f20844030300509a03019840302c9000c008402074140c07412001318000761000c0760310042c1080c10064074200402c40c040d4051040e03000c107440e26425030800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 728296160 1250 728294910 728294927
    0xa120503090f060421020d14060402011e02031e13090204060e04020306060d050a0b15031617070c050a06020f03061813260a09080706020316021c060e0a0201 69
    0x3540300f21420300c0184021107240007a40c0d500c00c07500a0540c0455914400310b01141a0300350003070403407241482010f500c682c3c0459024401c42c400d0361088540c003484200c04e00000038132020007005a00034403810624a1000c01210008140e4105031400c06220b004160300440071034126500c413a4001c80c2c10061a80c10056031a030720102114194210315006000c14464010616201c5549072500c0c0801e003000ca56a000310300117440940180d8030000150690a0642d00c00c0e101a84000c0300c084078600d0f0144a880201828002d5202c9804192546030303003101c180c0b4a0110540e05800b40c4940703d00011294070080c10340c041408200d41d20307450602c082240d401d612000032a0001d00750b40c00c0011b4040c5468030301641ca640300c0484502c0f07070525406541142c048241481d140c4c080000d407800c0543d00840c00c60b08031481001101d480545030b000490302d0f40505071009400102845080f00145007080100d039004555070500003000c042911581c003540c1d4411084150b0340c2241c070f2010155603006101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 728297410 1250 728296160 728296189
    0x1f2304091104021b0601060f1b03080708040c081c0f0e031002130f09090c08120f0705030c120c19020a1e0902030a1d0f070b03060a12050309 62
    0x104030322800e503110380804107000190940301c0d650000315100c0b1034280e003100c50900d501440840c0c2c0c481da12024050214010b500703449000c1400410084c01c0ca01d0301c2c62480141d540d0603a1004003580b41c400d4151500c18014000700d40c4040030701e04c0440c41c84802c10000000c1442c0300d03080c940341c045040f000342180070611844400c00c1516054915180c03000522801c1404404000503a51a00140c0c401c40c00004d43e0000000b40003c803100085010f2160003100344a0300507070082c080340c3d90340c411899a0348030481c1744052001c01400000144040070b005030484d03a005000381e918010301003110501f08080c1c1e040c0364260542c049551010300c1c100304a00d0780c0400d1038a041d60b41c0d400207a000101040651304c0b8010b034010410401c0d00703100d0100012000242a0120155241d05001e800d0b00060500e003e003a29007946a42041116140000341c034000d104c003c5409001d000d4144104900705a2000784425085418484005403070729507040d400a5a50048001d0341d02d070403403041000b040071404d08a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 728298660 1250 728297410 728297419
    0x1020705010621030e060c0a0f080a26041104060509091f0e120f2106031507050304110f1503011d101202040618050709060311070b1f23 60
    0x480700000380e0010a172a002c5c0104940013929007840c01c1d820341c504030503000f00900340301c410740b8507104124410019044101c55512450300e4001032001e0101280266214003615241c0100420042080001441e10f514005800410480d840d10701103802003000f680c00c18495442940010142c0080c012a880742800740401840f450300440030b82951a8550080441484000206003500d1038807030381100ea0b65090b4058a5110788c8868901001f00d0500300ca5075406400b84140030100f442d03031070400520940d5a62500340c10342d201d80c1c0b05c00e84556041078002e80c1100c06502c0300c0d0000d41d0348010141c0107401c4208107560360740c10050340304501041180c501c07800c80e010005100302425407104a1042d550310401d1103072041c0d0540000f038080c00350b560007450b0f10440e43e0205401d84c0d1094000502c542059107515621030768401c411000c075181200e04124401c4203000540c00030b508000502d8005600441448a4501929007080b02c03004981c0b10341c0c0300316400c01c000c118010900c4405d008a01c2c00300c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 728299910 1250 728298660 728298719
    0x60504050c04050c18060f0415050d06090516182409080d020d1110020304030e0415230105090402030c120702060108071701020d060f0515030630010207050106 70
    0x540c0c0170715000344c00c01041c030621012640340c184407810010b550040c2180e0007885003200c102503007d41f596100344d840b002000d0a0500100c0c4041c01406481d010320884800041c6040c2030034011640020140c0c03c80d09460351a40002406400034215a5641c0140d10402c1c810744c0e0210b00054078020b1154031619044c0c019442400625402040401c1d10384044d04107580c0d0410025606400c1c000c0c4040710390442d51022052006056100002c10a0020141c40400500c418008903804604091040300c9122410400006107a10041b135044021038060414038102828500090181c0c1c008035484640e010300469814034504105c1c11281d00303c0414000f516141d41064002501d50f1243e01900c1c1c54604041c031110240c0109504680b24001c80f150b04020103500d41c11051044a0140b00740c500c56400c0b14150942a0181c070b044a0103050004c040703003441900c0310211301555050700c2d10201c812074000701d450b1000b8001e000a051140c421400055050b090194011405100006c40300c0115244c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 728301160 1250 728299910 728299927
    0x302070f08160605130e07210b03060118090c0b030901150e071b0b07020f0c0f0f04050403050f0f0715090305070609080408010606051c110403030e040207060504050c04050c 76
    0x30b2001034140c5015162541d9182c00210b01d19080d8080741e4402c1c03c140c10f00f81d0070003000315488410b0356001d0340441c42c00000100360a02e00e00a40b0300e2081070540c560811001003244041d00904001c0201c0304000110316045070380c95146a60071198010521420000304022542100b03108003076000c10760316081e003a00390904103502c5010030000c0c41401401001c00325580148540388028010542c0141c0e0303000c40d4500905d00a4462501ca058501d00b031251055400f01c2d0314103812400c802c0c11000c0c02c1e0383d00c038650341c000304405030070080c00c15010300c0f0b400c00882c1d05100d001c000905528228100960b40c400305460008400440520400c22580c58a5100340020750300c41c0403119115008040810b0864070303400c0911040c031690f4000710507980381100000f80b094000002c0c182800a9904143e004901c1841c0703801511008803e42d404032008101c10300c0001d010719085426000c01520041c1800504c1e660322040f02c070103840a69169008004103180381c9002c0c0500703540920005403103130402095 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 728302410 1250 728301160 728301193
    0xa0216080d080c0702130c030207121b06051801110a0e040507120b0a0b1909120209180111040f03020f12030307030216020d0311120f0406050c010209040501030302070f08 75
    0x24103c84003002c40000d4042c10b6541c0d10020301c10780361071010104074071802520003034025071012004a4107100b0400107422054021054410008440e40c800c00c003103141c542e2908004c190040900ca9100303055045039842c4c4609226101140f003403424550b540d51904000945022421052a4426410321040048440d400040d4484c900c10510022404030b041c10001450301c08103130400b00b800320003c00d0080d000d51440114601211581e1035002300c568686115006003030650b04040c3d00074100201240d2403807061224412401c1e40c0c5000028154840a03181945a10942c05020600300c0c05070207000350301d080c5000e80c4140700100d9080c06400bc0c0710304003075100d01000b000031040c1540825081d101d6900302816240c0d00c1c0c1c2c02042e15031003040e00e14002e010f00c0c42c41c4c4281e82c694443d1409511245c440003088441004105072903900b05031400d48115081c4d0b01c0340911988954080c40f6810700e80e1502d0060b540030314845d4000e40324207800d118070b066203824503905c40310440d4001030400c5040f101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 728303660 1250 728302410 728302427
    0xf0303090a0f0206190305010f09060503150403020a0f080a090501020607200106210b010501110705220203040b010501030b0307031502280c06050f01030506060d030201110a0216080d 80
    0x5220b4105840b02ca00c900001d4131030702031164036104d1024511200306000b42e0552103c0d040c3ca007a00c889282040d112810107080b038a60380a080d8055010b00c00c0039000303842503824941d02900c01d10440c2c40202c031aa4403c928440003407401c0340c8110b804a200d40420f074100100302c0182c4428070081c2440d180c69180180588a0350790000e810012220244c640c6200a420050180c00c92240140303141d03600b08081440e40c03044d10000d0311800c114800103d8698410070300160030610031001000c144d4104000c0080740c0d6030b004000d90031001e50000140c0030041c10300185104a0194520000c9503250030005015102e042e81d44510a4015103024000a488030b51140001c039030700c0c040162110b0700f468004036510b5400484c41158900015050160341d0304c031165801641c480d8005210b90303140d2004440740f9074000c0c00300400346d40000000481605010321040000b60091001044045159454007519031003505140e0040e004034440050605030481e01ca0010000c10000300038074104868014242ea4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 728304910 1250 728303660 728303663
    0x20307020904030e0409111f05180f0d0b160216030b0c0d020403050604110405010e01230a2603030708060108070507080f0306010e04050106050301090f090b100303020f0303090a 78
    0x3074205000c1000d1501c00d4004888485000c0c2081180e0343c0d9a09082c0d001c00850480e0034841c20440b1496400d4031800010401a2026625402d06000c0a031010085442903104042d401070002140040307690307524100007074242d000350401144d80c20240d11040d001100c0078550015544078036801c0f542680b81c2024601103d0304040c1002042c1c850142907a05440b030076120007021400442c011062000224007c0d004900c01d00318a03003034000300307000d20095a0b400d20442d0070a09186004114400ba890310064061404040400001e085000020100300706500601402500c145c0543e410003815103070110b850314294011400c619203084000c24034200148414100900f00010580f00380c040c100307407107600380d201100640380c02c00518001f0150b002207c440f80040c0c14446841d0b102c0c100391140c04e041c4d074900c0e82c441c4d103560300b0f21002102a284010003195096a620782c0782d00400d9034144401d00850031548500e02c66032440c2802450040c07414510007598104106100403107600051081d000da = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 728306160 1250 728304910 728304919
    0x10203151e100c0204142e06051e1605101404050a021c060c0f08150d030e0d0b01031109090d210f0c0827060105061b070602010516080702030702 64
    0x20f007840e1001c10040c2c03420941042c40301440805100c0700e40105094800c0c20b0383d00c95594030300c813141151096402d40301c600c02c10012480c100030784081d41800d04480d40c031914202450500e01402048011001100c0d003070241c2e01c0380c1005c138800c4000c0310140a00140648460a44441c07403c040d29400c1d102e00010704001e2090703070800321550f40310b90291042c6050b29080101040401d40e4580d0240032603101201c0040005c44030400a404990340c00d62280c450318004d000350521202c9507a056626540f802d580a6211115415480c002a03007109080d000e1803081c20b9101390310050206016112001801142c0a60451a1042e8170f0303030307070000c0e4011001120812841e124020130121100910f00350318a030756200d0500c0000c23100d26401c0345001d030003448810a416450010b090710509002400d100090f00c9410000040090386001805440080c5100180c0c1151602113613826140c00c5a0354014009030351240d040002030000c2c441c48040340c00391030a003145203282c1190000d4981c403034020000d114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 728307410 1250 728306160 728306177
    0x610080c07030201060512010c3b060405041104030203010507030e0a0303020a050f03011502120a0906120e030304050a06050f130305161b050a0918030c14010203151e10 74
    0x5152003500170100a14000d040781809141440c52a0301030700340440f240c0302003620400595802c04201c9005480c0100031030001c1d403007039021105108404507400d280c96120b2014440801c01d44d039140b040b591300804420203d995103280d0700c145803e4600c000e14010501d072609000c00c0c40d004010441e00b420690505e0010303916002c0e014103440e94001c28881c0c940201c4080f00109960706000d40498080c02e080d0215070204c2c001a51940c524030592a04400107402c0d00030400509006034041031410700511000305a80c044086910b143d600215001d88040c0d01403900401030202a00c550f503080038105038080307824a0301a02c030401900c11428001d00f00034000410700c01c07001e86007000c5e80032994403c0300c0401046003035078000c02c501c007180651880351410fa200080d4084485c1f00f18040700e540102100c407084c049490641e0443e011042c16106000061102c98281a081c40111710412800e001036440d91042c0c1c05101107620016509010390040d4100ca003000c0c1d59002070b40c4c20300041c03460201c94 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 728308660 1250 728307410 728307413
    0x21050f0c1f05070c0902091e100e030703080a02030a0f090501090308071b0605180102010603110f22060f06170a0e160308030405060603151f0b0c01090b0610080c07 72
    0x4241c0f144410103040d00072018030103d1509070b9600241412403048690403905100003900707000501400000e0756202401340a40401180285402501094010700307407801640c1e030782c03140340d02540007001d0000182c01c00201d240050f5005600e0b40310200c003514020a01508290000e05000414000500448000700e50a000c21808100203070a0300c04a0349800802640c41c0e13000352590300501101c080980d102c4070b51039481c1d4414868142100d8100c403103404844080d00a00144400c20014079401c41c0003115070901c407aa20200412103000c0c0c000001a2403460039024000c400c040340c00000410100e4074586e030080b41c800f05d01640109840c07071700140a07403c00b003e8918003039500210f1458403448060000510041c14003852040d806501640c802e5a00d120405890710b5820b01040b100c3d40c1100003140981c1c0c41031210540c41e902c00400c0e1280307a500c9aaaa1801c2d4010540384020f40c2c5d1208500740c02c0043c0340a2203a0000340507500c14841d4014600003518601c00207101e20340c0010082410340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 728309910 1250 728308660 728308667
    0x507320d020105150d02090c0d1103010e0103030e090124090f0b070b06060a23090d0f0302010c020f0703020402250f05010c050406050d051021050f0c1f 67
    0x41529002000c4a2a460940101901a1104664035134421544000c031a500d400c0549010440c25801000720b04540da42c3c80b088003280e000700000c45031041c0d95000e11055107030010001c501801a02c001c4507010f624600c0c005248039500303030265001e41042c03001001220341441d00600311011070228001500e4070418100c460214962140140310f6001c540028001c0418009001e103034011040303250720f40e44000070303c070f564805e0032078100004580f51a1071410320000084880b0841d403d00c006480c0541920008200c203841d07002c2980d507a010f00094104040d0240b090602aa40c14005011403424280235940c580700c00780b2001c0d0051382c00158802082c001e0000d1701c42c100e80382e01c4950121030041d003041e501464812030b00300c0389586010814142c00c0c0c06641628101d0303907190f03545c034600030941c000c850250201a1907448151851140400e9881e03941e0302c007520701809900711204465043c00d005290024000090b0541d404c4001a0417481d1a40b071106038001940d284142c0340d80c4109007044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 728311160 1250 728309910 728309993
    0x150103020f161a0a060f080102090609100509061b150721090b250e0603270106030501020901020c090f181f150b0313110616080403050106060507 64
    0x90483c0c1070301e020403082d031080364054001c0c0d5014a454416007600c8007949800c134400d6034985580451300744500348151600300f50200640200345021400c080742c140100d1800d4100e15294860401d00598188060f0410002c080824007501c0c0140c0550800e684081e240380754108080c0c000200d0403030321001241d6290007000085506c003050490500d8100740031400466880e2a00c100280c181c200c16a403248101c0a800360098020030061071501d86540c1c4660415100c9074810302c00c820320425a0402c4020701c20103008500440015070303a21891800241001c0b04085a0361044a05100340300c0c086c0c030f642400380e0780682e0120364070006000c10070f24686440300d440b10b018920228445d150800040a80004038a164124501c00c4600e40700c14400c0140d000440c0d04601c10080852800081808d0840a1441c05005807000340b511802004000c9d200180880030b4800c1c030340010301002008001d1041c20002c060714505917042102c1c82c0d0b624403803500d0300304040800c41d007132443d0920644110030f0403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 728312410 1250 728311160 728311193
    0x103140a0e030f0c01060519031203020304020411130f1703070b0c090d1109010906151d0310020705070503010603021f18120c15021509030904090803150103020f16 72
    0x40b0b40c44440c0c40241394040c10396405028015150302c8501c50440c00d61541c40001e69902425100740110900c00441c02500000c106980c03042c0c07a448030030852080c0c4c0e0010032114556004680381641080b50b060010300c5542d20401003414514a9503020354008000d40d41c50a80c03114103104191107024042c02c00380243c00240740e115122005030010030403111000030103a2801d43d14214a42e90b202404401c0f18220b00c0307146101a51284135440300c51280d48546d010111411a0303141b85a07140b8040b07898074004854031141d29034009044024400104491001044128000d1110909642c0400c110446501d1140c11040d1101552010680103000d450307140504076000d00380060b56142c0740742244c6220f24042e902c50340d16190100d15200d01d00244180104141c004125129441000801618004000036850300040c020b2a5030342e078981c00307641c40d0540a1040c06442e41003516080300300562800c04603040c144100700760340100d250741050320704041003043c00251031106420b121501e080000c80 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 728313660 1250 728312410 728312437
    0xf0a180906020a05070308330310060b0901030605030706090506070501020904140f1515071707030302040810020412060513061104140d0b0f09071706150103140a0e03 73
    0x807a03c030640c2e400405403441a0180e40c0d02281d94440161a100344021892400510304103141c02005004811507908030008020f4100d81c130380603186400034100c071884c1e04100405600010100f01e40e6915000700d40141c10118041c165581c80d04801a0501140d4452240103540101d81c50092142c2035041d203041d24405003080c400c00c0c035040316580b03520758100c412905000400d40810032044040c018465031800c007070a071030303081403203002c0c221100c0d00030304000c80f250301100a0008800c01090007812080384662005a100d6003400308042c01c120100302200c0c00e075881804200001c4901c0080d0700c501e075800c413000080e00d440301004c03210102d821810240285080a0b50b40c0300700c0b0810001001120f0003d1446054120390500308903002c241600042c08149013600800d120501c0542c075190040c000e40115042e0315a1000c03455605155010042d00d641c0103001041004070141c4580c80301410309203001c11080c580c09030b10155070308020700040410b030360300d1a84a0b20354100700100c840d030590b40c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 728314910 1250 728313660 728313667
    0xa060504030c0303050901091106090303040306060e1e150607080904020a080103060c0e1f0e10080106020c0a08150c0f0403051c0e01020709320a0b0f0a18090602 71
    0x1406040c2c50b52141003100000d21700300016140c500c061141240c10359000e050400001101e004100550704804412a450f0004000001c0080e00900c24140240035030030320380b0440e16100040d401d404032500c03824a0480840c2c01000303102c0d04200c9182400302011103240752100ba00707040580c0c80740510b240c1c09070820302c00030303041c11020b4200c0d11241c12a4030480050056400c99601180e0309510f2286054004481c4075405203000c0703903007401018040c118034040c00309a801000060421000c494400301040c40b42005004565051000003d940026114410074a10f01804d25039903a18200e105aa0407001d64042100401c4103001c807034031b000c10000c042c0c0d225900e034101191a44440c04111210614144079203501e1400b03031940c0c4101c000ccc141c0150590a1910303c0c1c0d00c01074203280f00341c50812040c1d600d10300b40b0720058400071a50f080003000d511a0034640f000e291803c44062541c0d007441460440b4a2f580c440d5502c054201c01d1b102d0708088076242c0f94811161002410521400420701070010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 728316160 1250 728314910 728314913
    0x12050109060c0309051002090d0201030f0f0203011d090c06030414070e0901060906050a120b0405030705061608070806150c0c0a090203040b0a061a03041a090106080f060c040608090a060504 83
    0x103420011655005d001915940f50f01c0103100f10480c030440c02c11941018180c04408090741c0254020081501ca102d0045461044035103003004030ba000340c10444005148648041c80b0420103201968082e03203030030080000c01d1124000461034080140010a0303101d110fa2a0303c01c001d014001c01e0010100300320142c0c4030703090640441d4081d01140c02203238203071480c0c56400602072505c424203908039140307007a0281c0040c0403600c0d20004035500078400d4902c0d200c00c0086000040c001c0044900c00c021820f40300c0d01100c200c4400800c4404080d11540030000704000f4000316a031029110754060046005060703889103855181c07420503064610b0345034400404100041c00605a070021807055100f41c441030ba00703649034001d8004403241400b604803824030082d441103402d28040015500107006901003111440c0c00407030300c00810750071142c1150607515a601000040010010244000903040c0545070034a01001d000e260350080d0302c80c01d0200b118070720220340e8201060201007030054111906118a103003e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 728317410 1250 728316160 728316167
    0xa030309091116030e06130906140402030402010f050d0b0306010b0d0513050706080a0207021c030e04021216110a12020709020f030714040807030506090d1812050109060c 75
    0x2510610041500b41010521508104021110011584000c910004101d510304032064000d5060454100300c0400c41001e04c0c0c09181c1c0803000906203088045842030408001a048200703520744280503034018000d200050703030400d1080e00c0707040d094030700652198440c0c00104068492580040c0e01b40c0698800400c140100c08000c020840130341405010030388490402e007250002d10702c0702a106d80c000d110148030700c5208041043e00711048236009424101c80c0c1d00081c0301e4107400c24812451581c0716240c45c08258005c501c180110a0441d03003141000712902c15100c51242c0103246105905034900b6200c3d1040c001d0501c4403000016008a07240540c403031a284c580004155400e10140c4078007040061020200d000700c61280321141d8100b0308544480c401075642e1380141c445003884080600010038460401c1140d40002c5000d0307001080303d41082135205092040c004144010000035841403401c1c0d0602242040441d04400903c81c0c0d10070746801c2143c010500f401d03006103075a0401c1c030a8003070143d2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 728318660 1250 728317410 728317427
    0x203030411041d0a1a1e0703060905131103010513020d0609080f2809090e07081906060b0f070b040302010e0102070b073e1c0f18050d080307020c0a0303 67
    0x3084841c03508103400400300305040700040380c6e50b070314a120081ca01013183d4148440d1940000301814086249a11a20300707100fa50b0045440a1581062a15030340c1445100b140c4020307042010760082100c1d0400380b00c5403202c01309480000e4080d8021420355410001541e01c0505201d0b044a1810f440340750b4281d26810036480000342a007a600903400780c1245c13803410500d110740340e51240c0303804d0701c1c003490301c20701d030000e40303401240c401c458001c4001c001456001403120341c5540c00d4860303202020a013030707241030b400b11b59a40d007020401030310500051000e0303003120701141c0f85c2d80e0304003140070072a583d41c3ca0124007400390100d0a10b1745500101b40e41d400c00200411342070040b485600c4501c804c031501d2001c42d003c0c44802c101018000740c0c10340c031010080850341c901401c1c80d5541007135401001c51521030810504201c0d100500040a0b45c00d200301d141e40c000c50300000040040303030300c01c501c03032074900092440d01500c0710260440340c00001080368240204032800c80c00c1409410442c90710b0b900e04015181c00d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 728319910 1250 728318660 728318663
    0x40c0807021b3d0807050d0f14040605100603020f09011103070c0806100509150405071701080705041d07060e011b140f0d140c120c01090203010b0f010203030411041d0a 74
    0x140030f1001260890302560b00584618803a90341c00e1700b8044680c2d00f103409000d104004503403807652480c00071002c891203102e06202d140524004a164100501c1041551015a020303500300351042c4a0400090f4500c4100c0f200f074602480e09040c041d500000481c2503104256005290041a04c0002030359000030075054840c000d4400c0210000360380728103004141400303c0c0e444200000300541078075140341c00e03404150001c40c140f821007001c0e542099101c84c1035a0030b82140c6415800003908106602e0603004982492030009542ea603020000c13052155280c5250191390184214940b000e04a6407154103017a0340312000313000520383c3c6905400c1c0314204081240440307800d4050b04c2d9501c1c0b01c000001403001150001980c03058046040c0b6103002d5410780004480380340902034035140f10150510080179191078a17520000007004145031040600712500c61041e00d010b5140201140d207141c0e00130060740d81c800c0e08141c1001d0f440101074001002411071082541812159050030b0000d461300203043e44d81039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 728321160 1250 728319910 728320009
    0xc02030d030b0112270b01050307270c030906020708070209011a0a050d150303021c080115050313080301080102090111010b09010b0c0f120702040c0807021b 69
    0x300068404074107980039500410301041c8412101c1a05640700d50213220600b40c400100e6410741303000341c9090f00c45207030b103942500c40511442c01440f1901d020321094000305444901c21004080d45907490880c40d44075074003145495940c84122503018046e800c40c01c0c00c83c2c0e0240086507102c00b24135114207070b46c00c030040903801401c07690004992416a940554101030a04030380300c0c103041124004585a40c008140015841c0d12006040320625100003a070f40554440d40180c4100582c0300011400c102c030307040ba2103040001d07440c0104642051407241051142e081e1408ca80c1d40d584a1405c2602c102c10610010f10591000000240780c910660103400c07244401d80c1c0d40c40c0d02c29050a855820785003800b080300c0d4803070f101100401042c002c01c8000c0c5140b03a140d4040c0c41c0e02d2400400301e2030412049800c02400c1e9440001c0b41070031403a04e41700c0d202401e0705c03505241703001d424000707c005e42e1100200600f05000d202e6120202c2c041e80e41d400c84002444403000d0b4080000c80081c2400140d481854580c980d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 728322410 1250 728321160 728321173
    0x306210c061c1a0a0504020d18050304211a0916080d09050114030f1b1222051e1018050d020604030c0b0c090424050f0604090c020c030303070c0203 65
    0xb40307200c00c0404903c002d0018846068103040c81c003007000a502c400d2503c0011565517104c1e440340c0141c4104d035120540600701441d1558903161000300d21041910411071000700a800341d500003030440d04a243c0424000c000c070881e1b9034612200628080100758070a103076014058000945640010313041c8180f03004c0d59280c2c100c150340e1701300544910454040d10816840d0502c00100f180c000c8105d201d038800403c100200054207030b100c00c64481e034800e00380c0d20494281d40c001c000d106400741d400340c03140d09c005104d414041480c0352106600d40003c02a1841540b45402c50780380812400c11482c610411946070400081402100e40400d10010301c10885450242640604c5402e002140284c030a075055140c00ba90911030340d480ba08802c400820324031101a051000d41219266440350082030100d404010414000c00030090440207400e6109074400c43c1030718501e805a4403444141c1d800c403400585d010032020301078502a03050001020106070544004410400203552008095110500907011f5804 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 728323660 1250 728322410 728322431
    0x8010b0303070b0a151e05040c1d040b0301150e0114010201020a081503031e070b01170706110102040305060f010e1506030619050301020a050d110306210c061c 70
    0x1c990044030406440502500f0014814600c690012418801744090280507640c82d81c00583d030250b080d5165200f0110a03000c240000d050601c5800103000040c00c0c80c907218412000c0c510820004409814015611a80343c2011600e09400281528030703c2d08089545980381c000b4046404001d100e0701121342408814480f055006100310303171074041a5a507500c040c0e0380b500c03011552170a241d030b0f52030f4040c482000b88d4000c00f1105a514120150200061591005903050905103100180c0000140c00383c0b400980384c83e60701c0015100c04030382e00d505080280b8100000c0e024024069544040c015001c2d800c10066002a8015103905030365400719014401d484105200d00c080c0000c245250f0050810004900c2d43c1c5040da0448584071503030b15082d007000340c0350404079082e03070800c1d800f8102149000c903007042e0201003400350403031020300028010704518041c4005100c04141a8401c61282002030400e201c3d83d8003408001504c21f40600700c959504c09003000c518134040c0390020b210109181800004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 728324910 1250 728323660 728323663
    0xa02130905060d031b080403060605010305091c0f050405180f07020c010c17070611130e040203151b1801030b1f080c0c0703080d0b09010308071203180b0108010b03 72
    0x1d00852003e030121107580c40e542e0301640ca050121145c44e008021412206001a065500600181d8482c54010690760700d000d0016065079005000804070790061910300e0284400804e0406001d03071a4070b48003c420b059aa01038865204175007141e03401c000f1003211850000b1200c40342c03d019005000f254030749030b40e40d117100b00c0e1200709160b00680003807503805201d0041000c40d000c01150f2450210178629001c060b64aa90441d40d14902e907001104001c11f08100091301e90202c40014029039808401e285865400a40c40746088141c05105004a20204003585000e010655800c185d90b80b06650b60054119805150680d442050340000d09101140303d0b075040403d040860007455544441d0b0700c0182d06015550510f006240c41e4180e10203001c040000102000078000030b41c01400102e82d1160f8001030002518801110030707014650560040000880e404100d07100c0a80141701012280e0440000301e024001c40105440d0b000d6149950105228044106504840c52103000300400800a02410f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 728326160 1250 728324910 728324921
    0x18010f0609120305091305130506010b0705030306060f0c0a03030b15070302060711010e0d080f070201050106080403030b0112060311040b091501030914030406020a050607050910030c170a021309 85
    0x410161410100d2000081c0c0030b0313030144c2020b81c4014a00c0070b9030200011000104d0300b049032481c0e82003d0740c90700c541c2070103000c0c495503014000c010300c075500e001200d454040c1e8070310014200c1c038014100003c02c500001d2402c0280c448105401e030541c0c4483d052400c00501910003842c91600c91202c090050680503020720465621503415000741c641552118403e560724131b00308600c95a555214140d0203482c540500220400200540b00c0f03e0b010300709070800940c1c03040014070284c1036a24100040c84460b402180311507020383d041c503020074804019030040340d0461100020105207410900003004000c10105031280c0b420043d00d042107144801c0342006010102515000c095450003904007480394881e802088050380140380002c0d9009084940c246542d02540c4a4001600030050103020840309200171074101507185880d90131712148100080c0e00b040c4241070102030540c2c90307400001d11806040340c1c512850b4900300c4810300307252240d41400a0b500c2500045001f0022200c045800c100c01e2140703 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 728327410 1250 728326160 728326169
    0x9100605010c020603040c1502010c11030a0903020d08070b01090504140106050609190e0103030201050402030607020114011502010f0504051e072d150302182d0d0218010f0609 77
    0x50690b400c1c2981c080c480154070251003503c59044e0303420b000c5101802c42404040c1c0384000c1d80009040c0301c105800411011b0040056580c41d041000782480e440d600c4202c81d015640c0488841603e01f02e40c1c82d01c24250301c611074008011a406800010300300c1c2155020500c16805010f4a080a40b03d4090450803107081c1e000f2a5407200702030040518a04080c0014038100c8510a0722001c20b40e26a482400400402d81c070803070050f9118000c000860030b060002541051442c00240109800d41c00ba80242c0303001409080c2070107440720700c4003440a200350000f000140e400c40381003100b41004d080c46d41e02d0304000c07607803c240180e000040b42d10a0000207108401c488180c46c4001a4204011000403400300f4660301c51601d280300d80c80401e01030112425000c02d805140c500503503038800c04090620701030070b11015510841c200c2c00c50400c1040c1004c1e0081e0903842d50361700503044580d010006071841e80c0b105c5000c0d4010300d1009055081500031403d040c180c0d41e0514119242c01d076103a80c111a50001c5028 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 728328660 1250 728327410 728327417
    0x120e0a11041b030506030c041b14040e0c030c04090e210f070602130b0d0e1c0e3a1e05070b030403021e101a1e0d06140910060501 57
    0x2080300e0781d0303c00c1e40825000180241a0b0707929108050001d001e86140001190031095a00c01040c80c1e26000b030120348013605040d09213801e04e880e05c00f51107a4017200405c450490030002000413030030003442c4212000350028080401400a0055450b65584e048032403424800c0b40c1e81b03010345003c04644060354078042c1d042c10304618000c400d549202c041e4001060b01161302510f014041143d07884200546041c1a0135480050806620814280b81055520029070034083c1c41030341c0d1441d140d000d0034a51001c2d0058078a00f114032151003011800080a500d94030900c80051121140010030fa02031074041780c000c00301000000c2c01005050b81104060f14010304582c480f1404015001410f80078561140c00b90054501440803841a88820640c40303910107090b40141c040f030b0300000f03aa0f1049241c00e207003c000c1540400181c001103004000e140c0710440f1844000e06040c05aa901e202602102c10380c400c078284107180c0202e40307020070351a050394042e0032801140702038240c5916074441c1c0c2c012540140e4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 728329910 1250 728328660 728328701
    0x170306031902030708300310030b060f091e06030706020604120e09070f020f010506010e13020904240b0f070b0712061811040321120e0a1104 62
    0x1e2201003100540400c9805001d10100092548030500559080c441088094024945041e0398000910288140103e402c0c00520a001c419a00d861010084d01e510000011468458000090219000000441c4d1149003001040310601182d40034084810000100c2c200340d40b195020103880e881c1a0107071700d006034050303c00100802c0104289014205e0030781000c0760301109040105038456402c543c0000403d540c80030383c0c0c088135030402c05401d41e147d103000200b04074140f010000306410342c032014462146100300200700203211294100d0b110060000c2c000c000c0e0b08540700791104c0101c17904501d0008840c42d11000a011070511b002c65400003440c1c244c2619007a0b00790b482d8541c004020301600c04014180d0440f00c070100d42403091401420f41c038128100720031123560314a401d48110460b0011510b005000400c0000c0400451171206a802c581e14007030a000c04004588950141c10f012603090b0900441e5007801070003184a42d6080c4c040c0d8004080c0340701c1d030307010b1009880001303045510700c0d130740103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 728331160 1250 728329910 728329933
    0x2a0f1306120621020918010c021e0c0d1b0504060f0302040b01050a080604270c150905060412021c062a0503060f150705010506130c050a03020f04090204080a17030603 73
    0xb051117552007840155140c181540f50b00742c80f0f00b100c1002580e10007680c0101e07100780807500c2c1204100d0442c4070940040c0a140503480100c2d4031a40c3c071110091180e07500c4080d45807603d20bd000b16501822007d441001019a00c1103951001081440240d0241e4079100c690a500e510036012108005e480352a980b11945461082c00010420001027249a040303040c800c42c5129201441891620b010f00d000c060028203000140c01c072354548080030412b100d9040020085074803000c0554080b00c40f8000380d100e02500c0303070000c1001c0f9200051000301e0310754a885c04008105540d44885c541940131481307025052040c040810095884d09402c0d0082281030000464619020210074803012000c0c2075020725040000b601085074200400c220b4040e5160020004941840d20b855401003140f15400d0100c0c09040b140903000340704d03401d551000c0607000a43d0390000c0c0c10346421140280f185d808219034699403200c109840d408200021650b20071000389016036036070600103070307805118003c02421030311615 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 728332410 1250 728331160 728331169
    0x70c05040902064e0105120d0c06180305120108061909030c0602130e060315010612090507030c050f04050402030d1101150e0f2a0f130612062102 64
    0xc1c4d401040080d164841c2d480d900602540e0544044031301850505460300a00101c4150313070f40507000140240c2411b8007084100b03000046640e01406141410508076100b400d00d5405030198841d08500d5141c1d98518608040e032120040610502085d280c0c605030342c9a04d10030340ca5810946001e0700b00c01c504e8400303e402c2065a0320801d8014428280003d10f1810342d51050700f40e800842d0703000358244140c0b20412035818064805544440100c1c0980700e64540c00c5004100302c00103004e100c0401c0b03800c202c584183c1e070890b400810125081000c0307903a0f031913603460002c100e419240074a070b0141c00490448441410203005083c082d07036004000d41070320518107104a13401c04030454021240c8d901d8000423114602d04080c0f13400500380714000d010180ca0001d40302c2443e444040c0c19000014074400d0041c8480064030250114540c4e10418a07a03950200e91b40c0c055a40180c24401c214552600000141c96421001000f6403d0b02140184101927035a42c242000e408042040011160451200703030043c0340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 728333660 1250 728332410 728332447
    0x1107120e01020f0c030c10180b030603300702010903150c1b03020d051305041407110f061303120c0f02010e07140411070803040c0503010b06091e0406090f02070c0504090206 76
    0x22a10323081d04264002d40d000c100080d01680301d002c40b41000402c5c8040d5007010720003444813000700f00a001c14070a4508e603500030b4001e007014201e10440c001c42c0c0340c02107a11a0007114020341d00b0102250100c40503e1180c00140100c0f00c0c103d010407800d04900500d080100c114411054064000c2c001e480040c020607100c5900140c04010420080540031401e542c50307226100e1128240503800c42140f602c1c0102800918000c403480700f60360b1004610303903070003900000e65a50104810b4902450050f507440c003a03c0500000c800e40f4001400d10b0008648aa030068001010a00a60082c0005206d4000103610380209004003040c04e068a00c03550520f04050b00451000c442c1c1128552a00b191354560010703581068904884003140d44001704503501c0c0900075284010030403034000c0d00e00900030002500040f00c0031702040c07203003001e00310711804e6aa40b54030084c001c0440040520018582c00e900900a40c840c1000300e130503200c09100880c460a291150f40c03903695024104034a840100d500c0d2980040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 728334910 1250 728333660 728333689
    0x209071e020c0405060604030c15020c090c0a02011b091a0928061d010c0f05010c02010b150705060f09011b0903020429041107120e01020f0c030c 64
    0x15036861500504858015240004421540a030840201110401c400d8a2029000b80c1c440e040a120a0011900281083c0c00b21101c0500070307129402c1c40300041e41003d41411029500c40030380d80800000b003a0901c01850f68240d198000c110040910819044801c540030b05407000540080c0280584000c003000340c0c0c0b1001c001c1080c6820125108006240d04000c901d10302c2d040d00c240c02d807003030007a0f10500e20000039205905094203d404c000c44a070001d07039100010360781001040301c0c40c0014805130301510140c09402400900c02c0d00881d0001038064042c0507055800350030420010401142d80f101507803003440d030050103000561940b903882808030b500903242012270355885001d0440b008105032458a112a1502c81e50140d510350300400c01281c01241034a1440010903e268180e00604003030501408400c44001400c494203442099030360041d8103005120310005000c0440710b0340c1094a4000c000c400360300b202c403100c0c4103124072074803014521092500b550060491481c60701c0e094683d6507122 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 728336160 1250 728334910 728334917
    0x1c05070606030c120c090218041a120102190503040503030a05070207080f100501120f0818090c040509372405030c0411090904020d020915041b0c020907 67
    0x41c1d0b169180c0150300030440e84107010800d22002c8440030880c80045400092521075001c50801c540b0031005d8203003101d1014458031450355011030821310031300191181005070317014091014420038551854000e501140b00300d80d03155800c8241c624070511480c01c03a80315941c020301450654940000b208043c040103402c02055005070100800c404100f04044076952034200c0017440d0100d100c0d1080c1d402c455040e0000c2c290b8050150700700020407407108060030a0b591144040d80d45400b0340c041840014040e4030441c0d403090b03040c0244800d182c82d11010300140c030b401b1a8050481d13281d825a642e5201131030085c0c0303881d6010305101010001d4514035420b00390400b13400041071668031480d01241040600b40720541121004105000c142810044061420420342e400c0000a0024501c88924005e0b0700825200b50320100004d0b0441d1240c00c800c0ca5120b9000e4034510303460030140000034154040f03480c0384e0301a80c1342c9040a011401250341c280c04800300c43d120480c0402d410340901002000080c102c6060 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 728337410 1250 728336160 728336171
    0x412080327161d190b04090302060406050609041203091106071202160f0e10032f060a17042d14030406050f1b0a03201c050706 56
    0x11001068505092107804098803408080540d5010910001d4004005540074640d0f5107540210b1100e015410a1218107140c1007030f406180c050b00500f40800c9940d0308a4201405601091f400003150780c02144501760900c0b49a0351203051120283c0b01316400f9042c1e01d4102002c202d0203020341d00c580b5000d40104100d400300d1050704003080d01a4802a030855880710b07854492a06103071705100c1c030500c0840d009004105246010008190203a050203114844000040804c01018406403510001c6034040008040d81040b80d42103400c03d80c85881c040d031040c1030450034040302d14001c0120342c2043d203d903e5009942680c0440079021213001402203d40c00c4040d081c0c4154000b0003039080e101084034a032110341500c454509042650101100d462160748244814000c46400c00180c600d4200c0c5403c42c951617450100c44640c6138000050f0b0483c0078042c242109c018190b2160740c814000000b9125508500d4501c17240d150f070380c581045c031001020122051310b03001510071801844200d00403140804c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 728338660 1250 728337410 728337451
    0x1b0f0f09050d0c0e0601210c02070f0326090307031e1a071403040b06013606030e030a0e040e0a02040f050603060610080103063803070b04120803 64
    0x30b0b8800b408015261074007401c2c400c1190312480c002e210742c4079200380f03440c01962200440c41d4914101845480900e19140c40c2c08d070b0716041c03081114400800c0d907940d2054055541c0e042090f103070022a0b0728a603c1e420900c940f0345050481104603000150f002e0001e10306249184c5440ca0880c08640b452989184c56055000100f500655a40c0d4098a100341410b128184460041c0142e0511941c982d0403500a00400c004264066485a0311240a0808a1000d082400701c40b200f07000603a550403102c5c3c1040d0242c00d49020f6921103805030b0b0941c0e10108101401608165540c0c0134030f08080c8005100c1d140e03041b8060501e500841500200401114540030312a4001000d42c2c2c559020041c0c0305940e04101301d414a800c00006401040580e800c000e9004018401840d80e401400f019200c40d032100011401c0a82034540608a00d40031000c840111180103940c4161a210700c3c0714034403d110300310b80130500a0f8880c0071101103d244160f1f13070310006450b640d68812a040100b04e0203d0321419001e201 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 728339910 1250 728338660 728338669
    0x4090f090609030806190503060a090302010e100506010e01090e16020304270f0608031e0d090b060102010501090608030403020d0c08060103030908010c02122d0a090602011b0f0f0905 80
    0x200319034440d48500c00c240c178025040c4400c0c6041c01060b001100c503005003c0000c0c1c1c801040c1550000c1c606240803031041103504090b4094041000100168400c0b495418551000703903104034001d0000741c0c5c0b001401c0c072401004484038034a5010300036088500c103001c90180c0381c822400014109460040d68105907842120380a100038000c0708070605d58454180c624916110700c69240d1701083c000c8100041420b000c40c0964901540b210840142c4c0071035108007a84002c2c03801d481405044403c14020580c075860000281001620914059804c10700007051412140c012041950441401035040134071355001c01c465a81101e4040d68188485040400c075400c090120038083d40c02900c50050061505282d00d0848400310100e0045412600c4101201d4070071100b11140000107170740015250000c0c00740d0707a0040000c00c0401d814107200003102140181c0102240c0b08a41d1590000c03c50031401840616249440c01c0504002a6507600c01d802680e00605d01303100490154074040f8142c54030307200800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 728341160 1250 728339910 728339921
    0x21801060201020a09091401030813080607050909090604022b0c090203101212080603010b0d030e100228140304120b0105030c09010308031e0a240b04090f0906 70
    0xc0c80180d40014000318569000036a5400070309058000f0040700d1007446c20803404040c10b001c014072404002410500424a0440a20240480b242034a81905100001a0181d48034426440c000e461000001d500100040303040fa01c43c0d034002d4039030341e09019926041c8041659403170054208804190308a800f0400e4009400d02420038100f006949007810350009240104591002085001210f44031000840c00107180c02c0c0d030b12a41c01c2c03d002d91b0315240c0000e400362006484564000d010403801d0b009040c0d011810000e0040196001844c0804940089880d0300b0341b013060314503001501c0c0c200e1180c0408020b050240e0303405403013105a80c001380182caa046030f00c544c0c000341c444804d03016040240b0010881184c0100021402011509000c001007004044144005000c0350b00103c0000e24800f0f080201027100305900030401518a03200a00c44020014070840c00815001c10154981141c481c6020b070003070700c94803100d89040904d018449409080306806401816403581e032204000717103d90180e03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 728342410 1250 728341160 728341169
    0x906160507080c09090d050a0e1f140403110d29040515060f0d06020c0703080310050406030b04060b1f0804030e150f0702210f06090115060309021801 66
    0x984181d03490901640d10344401c02d4002841408120b0601c2039000c000201646441c1e140e00381a40c81d8020314000b50f0f03030540113030004d41e049910304040d031291140a42e490031006c03400b5200e42400b014148900c1006020b1404014480301c400700004540f49409200015a64440d0303040c00321025404c0300714111801200700140c0070800d4481803004002007030200c1200003c04407102581d503d46000010071462080e040710f40204e24040900c400d0040b15011540c0d8a05094100c4000e6603980c6031803400d50b1300480c0e5420401c001403030081014646806980c0451350032603942040b81d2074985440006021100300d40d5400402207080d080303a2200440a0708804145460b94080740c40c1504001d0014009180340e21f126041150b9906c028001140650300401076203030003940c0310103413440451020000101081c04200003492560211040000c8280c140c0e03454006130f581036100d03200c1440c00d0f101c81c180f520401035850381c010711200781f00358000110035000920f4000701c2100140302f054903180c00e811 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 728343660 1250 728342410 728342413
    0x51819050a06090305240f1b0408071701050c0318030d050c031801110a11070513150b09010507020906010c0b0720070513020c030c030d06030624060509061605 70
    0x8104203005060242e11030380c00d03c0e454080c4808924961054460306d004110700441072210f000f0480d844110403421030360102c404181640c4648480103c2c2c0da4160038411001c400c00c48050000030440f06000b454080e030416035186040da240c800b04860143c012400202c801d20082c02114a0b2210a000b0b0354000c00d010b035860b5076a030a00c44c41d10901d00555a40413962a81413801c05484007000b1411034212400ca481c242020303210f0310903aa400c1100742d0b40312079840f00404107032034101c400c25808600c1c414a0a18003501c82d076542c040021050140142a5012a905109240c05828040c407002c2c3d0114052410709070109065444007400074087d5060000122034024120a000032200c0040302d08078800700810709180352034005030b04040d10a010581711500891f041131600b00800a980903549050207480d221290010030200801080c8810b88580c3c0c2018500c030300103002205801e030312002c0b40c1100501242809000e5502c0d40c850021260001010400880d0007090074031542d642c40e10800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 728344910 1250 728343660 728343677
    0x1b0f04090506010c0f030521070f05091c05060a061a0a031104030f031e030b06160f0c030515010e06210705060c0708010c03050f040f0203150c0910051819050a06 71
    0x8003001408c41c1680748606000d040074180b254a6821510b2100a8003c41c64210b83c0c07207168501049410000701300c00c1c100d1104a81121080143c0810b54a00c01d500502c0c080120380d13610411100781c0d07e04903505800c4090100200d90600d071007a00030914180d07000700000c1ca071550320ba960760080b1508400a400180016850358440c10700b804120000c02c02c646000d111826444002510078400c030340203002200c036004201d0080201201e50526415000b6400c10325043ea00e081140d21640c5c1c0b24080610b03506100000304031505494903d60003a440540f180361149142c504240c402403e51031880030354401c601d40028269a1140189001c00401000c0d104252500780c0d51800d490320036074100c09140c248030400440481885441d64043e410070300104074141c00d4000300341000013204407210303500002801c1081d010201001095042d1003a140c0d11011022500f08070790074007d9214041c88007070751540e00b401a2a00f0800a0007407250343c044001707125a81c40004840c81e900e54008004074100382c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 728346160 1250 728344910 728344927
    0x50a02150711070f1505071a041406060102161215060b0d0b101407030e0409061b020a02100e0312070323070b0406091401060e1b0f04090506010c0f0305 67
    0x10f001080c0149800750402500c00e040c421002c1101d018030314480100003020414400b40a4540f0a84541d01102c2c195880c2d50304140c1450f071410342c10101284080d01c1841c02140165200151820480074800d81c04100c1c00c0c01c08542483d000c988410a81d90b42200d1001c08121402e1417007000002e00032114042e580750000c41492042d1607046003030348d00c50a080c8200c500c02c0c50308001c0100c814114608003030790b20f2109150070740c0e0103080b051401e900540f40040940801c81568000b40e0210b845855010380340646040803a80c0b2141128000c0d082284229a01500c0b40030716400c1960280040980e10091400d800c602c50f0ba82060600742c0c001070101d103464680c0711411110712840621101c1040c80d10b080fa40341c2c03440d001806400280b00640c1d41140e0820702441c0442e490150b09030000070b208031550344909500070102526004468917040d100c816240840400b12203540800b66206420036180400b0b01e0000c0bc1c00402d040c0c14415450841c01c001030002035202004c5100e502d4050700d42120 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 728347410 1250 728346160 728346163
    0x15010b0a030608070b0919031703060a12030e06030703060e040503070b22110607060510061e0e04090206120f070f0c0f15060503010e010504020f0619050a02150711 72
    0x30381e0106040d41c100b244c041c0419071419046039030b40c54003130310302400c41414081c0200154240707900c09482603010340c0e00618840f00d050b00a50241d041142c1c000c1c44152580c00c07070300c07641045400007808502e103000004a5404c110014543c0403031142030000b030880d42d078080c503c0c410030100e404032465080050803504011105505541000b242100c40181d410b03014a040d2803061f0080b0064180c6651081d02d6005580308000c4800c0700354044000d20281c1030019078644d00f40c1d00c0340107010101d003903203200584030080300c41030b6840010240d9071f171061400104103100041c0680c0034166044101008600980c000c080e00881c001d0300d00d128444424948404020005d03803210709800e04108811300101c01081078a40341a15954101036401046210208100e000303140c01d03803017079400d5401c001490b10000810f612036445030b0300a40703c18603064805420002c162040012800545241c1c9101c0225503220b032019181d03c10207401240e814100c00d0403078054001c3d040303070310303000145a111302081c0c1c600c1d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 728348660 1250 728347410 728347421
    0xe040605010f0b040b0c1f0e0606090709090522030f1b02062b0f09030206011a0a301e090804060f02070302090115110a0c060507030215010b0a03 64
    0x424000b1032400c1800d00c0000342241c46503208000300700401150311900c03071000b881010704807020f40031215940e284d004503a0b07000d4035008810003986d000b075100090940c1012002c891140032243c4e80c1000040c01d09480c07400a00d00070700540e401070845402c16076032141e082d10b2400c000340251105884c11480700301c01400c905582b81160707004600d40c0000340c010f0f164441541c0da500802d80e007031304d04014110300c1034055910001c1d4240f070704c0741003041d003a0b400c40c5103500c0b00000500990940300c150b81c0315800b4681110040c140f100100070200400d8400a02c6012040f21014a5102c103907903284003800f180214070300d02001050001c1e9594a0380c200503843d01610000315500c00414401e448039911900c882d8012031113a00140b01c441610550660710038030814000d140e0052000540e540c5617000300040e010118000b0740030132079500d60500032940009940035919807060381c403000e46084c40340480d8560480d01e003c03025480ba04160441c01c806041050340a0020b00c1c081507107401244400905884 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 728349910 1250 728348660 728348669
    0x30e120913090515060d050d051321060e03070b16090801140a0506240309280204111c05090c0f01022107170306131b14130e04060501 59
    0x3460060014000703000450309051109103000300e04c0143e03441d01c0101e0302000c1904001407444c052000c01000454112000d04440d46150410410041c0c45400140c07041d500e014035184507500510003800002c06a401c1100440100425a0309106c005d0b1342d041c00b015010b40e18070550041b402c1c140220740740d100740000c1c01042024024001151410011280e04102402c040c4015031141d00061503034580c0c01c100c0d80075a113816203034400c1345554040c1140030340090320400312900400125128410389a416880c0b002c840d0344049260280c2542088018982c3e5038420250442c1807019580ca06d851048480740d50300303010404980c92402e6101c0da800c0035801c03a88235115400150181d00d05d40d900240e03240c4280c0100780c2d64840c11f00240784c034000b14041c0c0d540003070060b0310800c0c48603064040780300654000d09094409040c0046a910540300751011098080c4040611980c0000064400d01c0106841041c0e0911113180109009003000d03000180d070000e51308008030301c0900c400c20903148985070042 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 728351160 1250 728349910 728349949
    0x20706020114070c020d021f0806180103021516060204170d11071a090a031a010803040b09060913020f0403021305070f0c050f1e060a05090616030e1209 67
    0x903e41100082c01c0d0103010710019000e0350184803010304540700c5030007080c0808080a003c2000300340b41c9000520000342112045c0c0601d042050010041c0501411281a030358014000328140445070341c402c040b500110001c43d0803c0c2031140881c0442e505100401c080d0500e203c403840051001e984c680e2411640c0c00f200400c010540000c262114804a01c3d0005d4580d0200381c28001c19801f070b49012349008410809620450f0040d00004008030705e207610384d84080800750380b602130b81c0e5007005a40700d01883c840c124a0350000c2160304020b1900034001e0a00d00b9004240007250005910024101d8001e2206646034400004042c425880c142e18640c9011015080502a501d04004003c0020400340b68070030a0100e44140ca004008080c03000d205464a040100d41d0365040d00d0003012028402070046c640e00d40158000705844000502425200da80c41c84000c00640d00c5401844403405201d0300c4801c200340da12541e01001d1113003800300401403e0001101d54641000d0410000b80c45038090303401009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 728352410 1250 728351160 728351201
    0x91a0901060516020a0314032109030430060b030c0301020903030a08190f020a0f021516140f07030f1b0204090c0b0a0804110409050604080d020f0a0207060201 70
    0x126440b80c00c4900c8201101e01c80c541418075480818a14245030708011300c1d41640d500c02c04804d0300d0010107080c48590300403200b03410a0004a01c3c04100c8801da8414101e900200424801c0241d42c0d140c0c00041d1341400e1600540010301c2d116100c04842c1b1906c00c1399004e032030301514043c0b442c0c10070642d4921181140214a01707110360002907074030301c9000d48a00c00c0c0491200042e404003114068408000c1c5184020f000c1c201013001941c00030740c04540303441c0229204000003581684000b48540d504801ea82c0c1d40850ba4580148180d401d0350001800001c002c2240c1a0707110742946900605680d4104030615526201c3c42d00e4090140102e081014080010241c06015403400703d0301c1c0c2d52a0603805490000740060740c1c0c282031110038140d4205141c41c2c80001055003885900405080c810340c014811400040c110030204003d480703140901511540c0110003240c00b00c1c0c5204000c00c0b070503881003401441c00c035004440c120300e500003c509801581125404010141d0280100702011283e120368501 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 728353660 1250 728352410 728352419
    0x2300106140a061d1507080a0311091c1401061d0c0a12020a35090606010203070308180706051b060115050702010201140a06030212150f0718091a0901 66
    0x4041c50741084007007061038000b0013510a44401c1c0035043d8091a64070100c0d6600342c3c509280c40941c1c498114080040d28010768650690110300a89120f5a0011b20308110945581e040d01c9084541c3c0c43e0aa844041707841708040e9a42c0244641713001040a6000345050b00c0c040c642d655031443d00240540c403082003c01c07030207850b0790703002c00c40d84d1071002420001a1030302030006086410140d00c0c40c0c4c0e41020254a8080700359444a40034048080c0703050040c0800d183d03180c082c00780c0c50740815035409005d84e00038001080000c0c002c14103a60710815440070f0740e807690402498036161190991001c0003261002590158024400c0c90b060340c4a0074802c014480e651420761800b84403901c4400c02e40c00c01030080b80c100b04582c401c0d003000e01c1c00642d05d00d040700c041c00c00403507040082c00c180c0300072807082c4901080c03440e8498002c80c0a081204000740590000c0c2e403808490505420000e19150412808a0b540d010400040103220003400c11100000380485a84140036103081000d5211481460780000421 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 728354910 1250 728353660 728353667
    0x91a0d030e010f02100603150e010c020d0c02120102120412020703050c0f060c011b0f020609121b0102070b071b020907030c1107031a071b02300106140a06 68
    0xc01c24401c0c0303485560405425012400c1c0002040c00c07052143c1400c40004c207202000c2c40402c44400500c1d03007000100703540d80c1258200c60f500003001c405a003055030b2011010b4001c04203100650b0000d0b0032100050008110242268000401c44041e03904078030511007071082040290641c0342c0fa0740000c189850940d11056501d0455240f55441030048402c0c04417143c50307400c1a65240021340380284184200e140384140c4041c406a920030004201400c901641c070720004403540100e10240140080c140d440030054603540c860402c828800c9070aa000050341d0100b40300800b146ca0003103a00d60360b64100340350010301364620381901029035110680c04030056680c03480e010350010360904000030104807402c3d0545180004c8001d05140c1d0090420010602c440411004d8820040040c000380c130b5036035007030203481400c10345900da04094186201c0c5801401e100d904085000100c0401d50001140142c000c4088400c0c040d82e044d0a944414081003441c9118404c000d101c0f40403a140680c02d0300301403009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 728356160 1250 728354910 728354927
    0x40306270f021e030303240d0b0a0903030b0d050d09090207052a0307060804050d02012d14013305090603061f0203030f010501030911010c061401091a0d03 68
    0x180c81185102100320a50000e0303a503083c0384840c06401e0320b440b850700741d07601c125445031981004900c1c0662141c02e60146040520359005650000c000c02040d281c2c80b030002d004000d81c5100700d040c140e841d18a40076665602003100002031054004100f0080d110344001c00346c110707592003010418010301140b00000d0740882d17180c0c0301c94480500802841040f080700060305150002d5290035008006001c2a81341e0f00019281c401e9008108035851607604107004c82c22641c1824400b0315048ca4409818003c108118803a15201002600441c1d10401210a0481e00c80c0a80c40700800f503001640c0080c2178140648241c000340300000340b044044910b02000340032071040d01c081502c605c0d4000005140d0390b440d0658000103989074034011341c60640b5008043d60702e910544285801a00c5180001201e40c030902407602883d034071413500c25108601340010348214a4680e402c40d40325845103c40700f0383c500d26502c0c06000b49120407006c0742003201d0101084400403190405401800c400681ca004241c119041d07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 728357410 1250 728356160 728356163
    0x4060507120c06110a140a090521060f0412020f100b0d08030a0b240a0804031b06061701090c0b1c09060f0e0c180606090402040306270f 60
    0x81d9a0780e01c061000803684100b0071800101960700d8680b03580c0e02e9600b07101c080c0c00140400e0f2554080080815000c4c1010300409000d540040c2c0940d000384114200058001c0800340100b018001b2400540a44ca0419004480c0e0781ca44070501003c02c020700040160781902c0e2080d0b030002d42224451409405d03161002c210111038516243c41c1000b0031900e8510404804139040140503441c0e04203040188080c0c00300c00f078601c0c4600b6040362264041d60300b441e0750205103004214a81d01e0126100700a44001100610650a00c40100c0c038045a41c0514131501001e10703c1050005101420402a03030f400e0bc002d60030a0751160300d0300c1410400594440380d050141d5048100031034442d08000380449030740841040d600400d0742401401c401700f0a00c1d80120404140144050090001d141346542d40c500b00c0c02d0b080c5501182c0d48101e01e005c001080c41071900484040d0a003031400440e2004a0141c0e44035500071106d482d078510b4500c16024903030503801001e542200e10700c6c44503012921000c0504003610340 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 728358660 1250 728357410 728357423
    0x20d0e09102105010207050106090605100207050f0a030b090705040f021204151806050f13020105160c08030c0609070510091a280809030c0a1415190c0504060507 71
    0x486142c203400c1801d60301c0406034028000e5540d480689445806060603116162010782801c2020a05c0d2614040c04880013580740e000301000b44c60f120400080100020416030810a400380200200d110032014605c44e204034001003007007901d884180821100036400100c01300348140311800181d410b4010311500643c01a020700c40b03145148990710020a051002c044c034011008421000304000c98010070720032545c43e100c4000e10755a82d40c071102500700055000380060f5040281d0800318601e8074158050b54028842082d5140d00c6890040c030f1a40801c40d0158103900141c10482c070301804004a1000e808207a0310b185220b00800d0020308160305602074038035900c21041c0e9044825410409403450071444003004800400d0a00c007003881c07404001d007a140020198000100803500001c1150723015102c02000702101b802503121501205070108056050f0b000d031480300036040b54407041300380c05072107150444081034640701850720865250504030406d011040c8820071070300e0303004025610f24540280 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 728359910 1250 728358660 728358689
    0x9060301050919051c0f030b0a0509010b1e030903091306030c05060307021c03020403060c02010911100c02120706020f0d02120c03190801050a0b040311060c03070f03020d0e0910 78
    0x103071907070411102a001c00070000c0b6003d070040300241c3c0b08000324802041b540341000400007101c01d10982d141756001d00c1d40c118050000400c10618400000d00c0504446101c075580005a02c000341a994000d40b160781c030300c4e40301040a030a145040e58600c04054440700781000304c1442c6542c0c40089103090300c2010310076040800020522030080c4140e042070140c0c03c0b28075000380301303a29014009401c44c2c04142d030f0344c40c50011a80742545c0140b04110714540c101d903041100030382c00e80800050001c644100740800104840403c016290301214a200c10318440250003080c0c10b00718001d18040716000b5051141d40300440c200055070300070032031006400500f0603440d507403104421804d00e188910045580b030146400000201d140e404440213040c0c5404035180b05110780e48981d0384a6500440c0000f80941103085903000713851070414000c24030403c401080e0f030b007401030300c0d241d060000103000c000f900960041e0707156591050388a02d040a11601c115040c07901d50a040d609402018000d0103041040d00c00702 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 728361160 1250 728359910 728359913
    0x30411150409050915010b090108041203150905090105160816030b030303101401021b040b010903021c05101b030509072303070b0c060a02090402070f0303090209060301050919 77
    0x12084a0150401482c2807000c0d08001d00e9a540e219440f410081c06125108000b180007903015045501500b0143c2d034000c490f0311180c03165902035800d41c2141040c1030341c401c0d48081c01c1c901140340c0c1c0c0080c080da460020711032070000042800d640b4010300da86e20030310b81d03c44602111a00088540d40085000300f5440d0b0300000320209400070700c1e54008580d414070000c001c01c182c00c09a62020800d42d0301703040003460704a540a00580e55044000d0b0980803000c0364404001c0a400d1550004024031014948001c41d25a20f070007245840300204002400314540188001c107201e81081480b0700c1c5600e24030b0030130180c00074900d0750b80e0002030341102030101510b030004200c19100c00c000c1400039021000540c04440b8113202d00b86400012101285d019001d41c0e44001490300301d1000766801c254a0300003612a41e030310030680b10025400300d480c40368042c4e801c1c007071800401c0b061100302c081148640c50001c1c510001c0c6c010803402440041c44944640c0c100810860044004035800002e2501c001d0110011442c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 728362410 1250 728361160 728361199
    0x141f090c17100b1912020a170705060706110c030c06010605090a030609050708030f04061b0503030f0703150303030f39030e060a0903090806010b190203070b0f010911030411 76
    0x224031340c00d90070720009000820043c1030385030301900d034502c01c031030030b0a9091380d4051358419007042c81034180054000140400130340c03d2800080c800b5512681d03000030301c01401c0060b002c1e41e070024201400740d039001140400c182c5e0400c100940c058100c03800c0c003d04028025000031701c030f82907600000f0031761070b100c00320281002010016400903154082c140e9465154551715240075420621401c0006142009174494565061500c400322a03004030245185560350422880c0880000d42000c0801d580c40001d80da10401440060001c1c6119650100308250565141c0065440e40b0003200b00880712001d40e18031182007c0303645403208140c8001c4002d591102581600100207411420805000e410100a14080d080c4c0c0802c106038030075110084416143e0710b007107954500900500e06901010008c44449005104c0d00300d400304030b548120781ca040d042c3d59651607044030569651184000280c018406101203001d0300500c42c81c040c004509601d41a15011f0602c0050302c40c480c0541e0050614403440c541 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 728363660 1250 728362410 728362429
    0x2406070303420b03060310020309070e07050403031d0d0201120b0a030b180303040c0e1003061401151d0f0f0d0308070f0903050a141f090c17100b 64
    0x44031440341000b44084150528500b01180c0000d1681280c0001003524041c01c0192801031402800508001d00303c04aa400250300c050110b0f20144607040d400991090405089031003003606a030383d5900c8500c4c51501415403404c0c258080c0c0802e00128855007980c132000b030300c003200c0c6409181c25004d441c5a003201c800146500f4103255044410160080248902d000401d40180802183c001c6641405011140c07680030070354009000d07a003410402c028140f41c0314892900515800021802c881d40d80d950181207404900108032242c104000402c5114403407071a5103d03140aa0900041100c0d40041145e020314102000c02e204a00410407442551038071107613170001c01c0c8040c04000e114245406d01170600001224102c0026814450040e202441651248205e951010050000901300d6961000c0e0b00c0320350743c2c01c12061181d51050508042d00c2d8003541c10401d01d400000032203145604007000080d25a80000307202d0980c80c0703a0303601c0800002030a01103080074100000f48000340203000881c80b00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 728364910 1250 728363660 728363711
    0xd12110306130e0307030c021503071e02010b040504050a0c08070f170304090e0f0c010e0d02010f0c0605071125060c05030c1c1d0a090b010e030a0b2406070303 70
    0x220101e502c07030070117401c08221403280380200d82200c1c01d00410410302c0c0141c4001c4600d01d0005248c11080090610740340c0c8003a1032004cc07400003140c031540e0700c0c0103d01114412201940d5952040e003a04050000f85820034001d4480c40c8007900c06641002c12080300c44405104491840b85440b803036460100c020700075140a4004c8280c28411603000500840d03484070400c086221500a42590100a6000c1c010818100902500c0d0042901e155001954401d03032601da08824054a0405030b40000e44621609104606580b05c80340e41a1004c1d418901d0700601c080000391101400d10040041c068480b1108121049483c00085090240c60000d0950051140c905a144601904010310022200c21440c40b0304880d40c580d0394480ca6000e940071344411510720640c00800600c003d105124403604845440034043c100f4a48400040f0302191034520742c40b50035103000400c4003d01888506c403403a601d02d15011590740c01500a241030000300144101000242810780d14001d010800355200000d0700d914 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 728366160 1250 728364910 728364913
    0x1406190b092e081b1305010806031005180d03090804120f060207210f090902091903080904050f0f1f09020c06060a05120714040212090d12110306130e 66
    0x80d071903420b000c0e0010b041034591600046562928260a000784410f0f5441c0c0b05c0c1c403000b01c8403000c1c6400d005550a400181069405016006040c403269801d4010345004440c240342001c0440352648109041c080c0c02c4450342d08050800d1600e00119078200156420f503241c0c40c059241072038881c5400c0b1450b00480000801c4203001041e42818000d03101200e00c43c8076034031516161901c0c81c004040b01e0001481501d48041170420b00305120012884c0d010f0000f481c0090000000d1403103e40010040b000a58400c5410320070000300c505160619002d0680c0040010740791103050708200e030240501500c0185000c0380c3e1406882407008020318039661400030716021804654030110500800e803144d6049980031f02902c0c52100002d107a0030701a102d00115050040580001410014441002c2d54242883d0358441d40a0003d840d0008807655000d004c0d008080040034000e80446014010900003841e5a941034070b0130407608032090100d0300b241e6000c9802c490340f134001460503000788014130321f41c1703c684201d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 728367410 1250 728366160 728366239
    0x9030c0609010905060117031206030c041104330f020c210f0d21020f0c071701050403050f070f05010608030409063f0203011406190b09 60
    0x7481419401229824028425100181e0304c80010302c0e601507000190f902c01d980200300c0700484404050807550841030080c1521002461070300010b054174100340c0f0a106502c400101044000c0003c000d6484042e240040c5241808811140d0198401081b00200074003802041c918415882885281d4041c44024940542c05504400340c600251000c003400c007451040f810844811800020102c140310016901c90b080007060905030340e8038545803c61160307802c1e0240000720003907415902424440e00805c0c02006c0c11460f000018070136030141b0302e01400d564500300c1031002080e485401c640041c0a0800e16580d0f030301091603d5800004403540141841d464601c0100341e0900210040088840744c503000e000d090b031643c3c0740b4618200b22901801215942d800101c200010640c0f0820980c103103031001d000005056000b0900751000c014000c0a690100c604021044c07030000002c01029002a0590503640c3c204416076607180300e81c62109114142c1c00c0103401c59145845220301190b002003421060 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 728368660 1250 728367410 728367421
    0x30a1b050d0b0702010f0e061f0302030a1101020d0e090a0207030c210f02010204050a121401060b0d110901021b042d050f0408090402030a020c0d0c0611090d0b09030c06 74
    0x1d440400b070f02c160340194201011801591510702500c04407542d070b04041c02035030321801000341031004040c84500200a01400000259405005926040740214040343c070b0300d180907000a0810381c0e0031242c00c00b4048401003404054550030141079000b8445107005a40364070900342034444880206c401407080c03118600c042c0d85001d01d00c54241042a01351105200c5400e800e00580c280d008500400f81c1140c400300040010100380c01c80080e015014048942ca64244a0b00150965403141c02500c0c4203e4002894400c02d1441e129052101290800c014203050000000030348504a003050300e00200039498805100da52654801251480c411503040d0000034560010340125101100396480e0034689400210300441c1740c0c2d01070b4072485d80568254500200b0200300300007500094401444180d003071245a0400c0d900300400e400716286901c2c1c021000c000c40c5040020780710814464808100c007403140314030300c0c0c9032001147c101560003e040b89075940c9049200b41381d4002c407000328015103c1c0c0d5080c0f06 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 728369910 1250 728368660 728368673
    0x31703060628080a060305100b0609100905010e010f02150606040b12040b06030c1503040804091d061803040302150d0603140d030b0603040807110306010902120f0105030a1b050d 78
    0xd000302d12601c0d034102e03595440e10f1520449009200c09411a003099500a0487c031680d484038589401c01004170381040841c002050312500328880c6c443c0415503249007403000d981c001081582130303542441e00008100715414002e480e00310a41c0048144c0701403101040c242e0f039409080c0c0e00031f0700c3c0b4801c1c11502c413240c8468003001404c0a40d0140c5803072120070003044050a01041000c0c21050241010410555900750310406600c001d000b603940380814440400e01d91514003075071004003461b40760401c2030030b17280140d1820044050019078243c00c116070301c0d1071520700220646040f00d8040f20b52585816510329454010310450b00b08002c0c103860218040208141d801500d4001500203086036203c1030284819400c03550025009a8407901c203000140c0000c9040780180361080c4500221190580d41e00e003c64035102d800e07005040320b150042554500341e200a140940d0091401c0000080c551504c00401d44400c8420405002d041c0c200c90003504041da080c01385401005c0c003901071b040369481c900b001c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 728371160 1250 728369910 728369977
    0x120e0102040e0105030d02060c070f0f06050a0e0c011d04020d020412030f0f17041e060f0b0d0f08070516080a17130504050901060b07060903180317030606 68
    0x840b460641c02001044d24100020008030440080e0000c041985a13205c03001450313044074400300c4074920083e000d0000a4903c0c90f000c4046440358070042a141480f141100580d01d00e044043c00940c00500c4e090100d0380c0c461011a10340c01c2c05005408007841490209010348100002c0ba80314500010b40001d915140c0c03010300d502c5c42d010b42e07255040004042c004403449418401100d0001d908410540c40c12096003064682143c41034440306c4100c080310326519840001c0302020b80e4065030700c4100d5a442506801200d028000032164403040390026600c802d81c0d03d039401005800313032101054550030050100001e10310041d0900040322003d50310b08000d40c1c1c481c04240b00f140c12080c0c0e80c2c0060b0907003800005175000703401002d4a00d80b00300d0a01c024003004180080240c05590748504001840520380d4008004840c050603011a03400a1820041c00c5202d503003024054104034a0000c202041291442c1c000f445d02c810107595407600c9010028900b80514102500c2c42c91110b183d0b400e4041d55080301 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 728372410 1250 728371160 728371169
    0x150309020409140606010504032013050f1902040305030d110c06090304050301060b0a05070201030b06160f11011b1401230a0f110703030b06040b030c040f05030a02100807120e010204 80
    0x1221130540da03113401140d0b10301443c80020803501d0440704401d0040b02118180134054000b901c9140c2c1c40300007417400c80a80d402690b24030b0b2024450700030322000048120b03106d80b0788018100c05510341850f61703540350b0703a900c0388005000e0f860380d54a405110244102c422220b5488e1180215240c5003084444c9039180d03803082c0b040c244030b58603040e80081e8031440039080d50f1a050154880a0512005800560203032200b503080c3e650052003001707403100c401100c10205c0d407d40d0246081c1124502c46150040000f060110107a060200c0714100c0074208107d400760280490780f110701e4000c150608107040303001d040085801d14a0440204001401c5000481d9840c4100052001800030101e140c00313600480349024400c00c280c03034003040300e039000c070f8001c2e08018003124024101c01e15140e82e9499515442e007003558030365013405c40000c0802045c1c200700c0d000c9001d400d046025101c0401607a0001b145281100d0504003441286070004401314007a039040304030700e00c50303d00a0080c0c11490800c0c900130f500a004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 728373660 1250 728372410 728372413
    0xc120506040603120c0201020703060501060e1206040519080906030c07030e0d03080610020f010e01060e0115080a1a030604030905031908181c1209120203060115030902040914 77
    0x40c2141c90140100b60860b07811500c1144245964001100e664100001c02d0341548507002c0004009402440740d58020b040d0382e40c03044480714440c4104903c6045440c1e503000f40f41d01000601010980104510f64640c0100244286003a414540301020340107641c1e405c2d50120020040202c581c2101005100c884d01c0f9a84081e61003ca8000b004440c7c40d1146001d000510020002010f80c101080381c0c910046450044079155160124850b09686144500390b0040e5120602000521949a0000d0140c215040c00c14014231035440000e0020f40010140f102090b10f070310050b6042d6110081c3c25800c101c0140035215189080d00300a4080e00311482041c0c0a44144441052001c2d02e01045ca4101e9a1210310700d440c18121000034144150ba100c095a0b00039111209039010980d44103070361841d140b2505241900e03a460000142148245070300c407003090209186504010327600030030080c5c1961900710700b0508030542100220003e0a071000000d41151505c4001820b001d014030303010f00c00502600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 728374910 1250 728373660 728373671
    0xa060504050a1a060d0e060108071d09120f0f030f040b090c01020c060a09181b030c021c020c180906130b0a052d09070f060903061e0c12 60
    0x110410840b411045826001002c240c4505030310704d04200200f42e4040100e0380030a4100f42d08681500744002a0f20105080e403200c1c40410900c020303a8600a845550100320f0f80f0603142500d00c20751208070446860f500003000184503000402d1940c16601244140500305460b0314003a242308005c0f0b00151020b0719444c14203000240001c500044010001906034041d050040014007840807d8200032104828001074078004507601408013110200442100d01c041a4080c03075903014848840308a00800415080a0003144482d0b0005100380c0022280c030b5114101c40207800d800c90a00095200e45644140c0c45002d03860810724140041d40510214800d80b840d03a00c612189103140c10515100420603c207003800502813001c00d82c00705e82d01c402c61111946403031054006680d5203c1009164441040c03401041c42038071a810801c1d0405016900c0860007141d04056010f03140444902c8024901d5032a54815079001182c2c18802880d0301c1c003202e080c002040c0c0218050310300301c030005052408602c2d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 728376160 1250 728374910 728374921
    0x90d14120d0b1518010804020a03020d0f1203060605072310060f0503070f18020403081303140718020a140408060118180201030e16152003090f15030a06050405 70
    0x35000c84039000484031300202034811100054440301002041680c0c404840c0b100040540c607980d50500f8094440c007500002e143d41840c2c05201d00c0040c510301400c15140100911000340c00c001180d500701e4012001e100f529880d45c5050008580501440625000d0a02c041292421540108060362800e815500e0b0303958550082c5903075a00e5a100781041403040d003104200144042280c2402d000c2c40c100f002d4a000d840e40c4074010b031032340540000420305040180410a1044103410300e10040101c030054980c80d4540513041100400303a1740c2c0004103039400140450014040c0940290310082020582e895566402c003d90711004248100701110b00d00c81602e103004c0d0024451280c4000c0304240407044602c00790011802003500080c00c1c18180f0454483c0080341070010203240090800c2d001f20325000e01c522100420014006080d4140c90b2000090522012004403d450030360350240c4800310340c10071712400242000101c0180c14500030000080c000d588183e900030209030740090702d050040c0c2e200c0e03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 728377410 1250 728376160 728376199
    0xd0914010f0212070f090b0f03060405061e100e12010501090e03070c090f24030203010e0102090a17070b0d1506090b16060e01060b0d0b06090d14120d0b 67
    0x2100c2c594060f045a09001911484c040c140154018680749440c002d10380c1c88400e0190343c0d038441071000c850000c0100401c0081d00e060300071190300c002d00f900c40c000c0009221481c118110f0200c150203101d1641c42211088861144244a85180303004104105091100304034900800d020b0082911035401d26a50800701480002200e400755444001e1030390003407030040c03200d00400f00169610566911002c80161310210b130449407a040e0384500c102c9034828518810903007121201d90320704001e64018015283c4030356440c4030190403600c0c0741040103103003000128014140f804a81000040c10404254007110450f03962007030011007001c094420080d0388544081d50000c00c107101d40d900b0050100080c880c40c81807914a24000b512a80e4082101030b25144114251005c0ea0000140307400081001c6980042074001c0d0303002c226050341d20914101c40382010420100060001030140000f8117048659640200a11008003107010000c5445002d42d08001d4041d0a05602240c49041c0603281c11303031040300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 728378660 1250 728377410 728377417
    0xb10120c03110a0320070302010f0c02060c18030c06270603100b09010309120f08060d1a040807050a03090501231603230a1107060905010e060d0914010f02 68
    0x40002480d42054289102100a0905420450030345d030704400f14030400d49201400b0705045413090f0000302d0b032a4001d040d040304480c900f145441c1154855020f0004000100044400c8600e041c40ba55589034001c902181c034042c141c4a00075041000011107c031504d1191102107040c04070306803007038540a5000e080101c03e0106032107161100d500c0680030000004560002c140340a010304011408404648510710854440a014804211582a10507544c8d0b40024040e9110004542030441c1000d0b54440b44c0c40356100800943c140305400c0080380902054405494000d44c0c8681100c81c401000e184c010107000080c4101e03404070314412216081c00200180c040ca410011240345402d12150f0f42001c1d405014802c070560034071030f412034001500040c4000300911415189851070f60742a90460040003a00c45020205890b0003d0a0501c29103a00511140460710240703005000c4401c880c0c000340700d600c00c0f003041c0029585420a02820081c00c004402140c0524600130007030749150b0000802a4031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 728379910 1250 728378660 728378681
    0x506010203090f01030e060405010204180e1c1b080702040c0203121f090645050a02040902130503061317031e0108010516051603120b10120c03 63
    0x3001404200b10a007080000c284941c20705141c0812048084040c49040c50340070381c0e09903003e9400142c1880039141c01026003101c10b101350820030a106508541c1070b140c444041d4154454a142c0d12241c0c8550b01c14500c007900140071070911030799003900d464117400550110300c01302c1c0901d04000f881d1000301d001109480c0301c40681d20200315999540754451034620030b4110305031552444518003080c600010320841024100a0080004011070f1841d4102d442c02158000020f0880c208402101145003440206042c0700c0d851021071b043c1c81e081c01c07110281c010350308040b607001d201084034a950184c01d541c0c0c204131001030342a920f142d2144014030707407158114003015141003036001031100340301e120a004541c0700c1e00c40040504141448182032101c2c0310282e1200c0b42c6691200b00348803840c030884000d100c00c14001e0400b00d103001002021036040120580c0041c052018000861900c130755960011b03140c440b070040c0b440c650360b13842c0b1101921419003100001d4815240400c03404899000b0b1117001a400f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 728381160 1250 728379910 728379913
    0x111903020c0a0e130620040f0e060105120c09040c02011e060b042102120a05102028020102270a03080c01091a1914070c050718150905060102 62
    0x281d440207811410000c190804842c0c05540d038114140c4591b1661003040482809a0310725500da2510441d124080c0c4c0681200c21032195903c14010241c2e080012500700041440c44170607950342c1d981c07042c1802d00513509010b030854106024000200e6040d07101d400203403181d03091003110310600701075642111903c0c010003078041e00821040c440340420b1000b01c0003100d0042200c2801ca200c07a070109400c8803d11446a60540c072558007a420400180f28140b0f2282c4018020482540d401d50802d42c0075090030410300e40c1e48000551800407404028902c45200080f075140d045200311000001d0007503001800304c40304903c03d160aa405c8402c0c41b414152209801444800e01d00d0442c0c9070386200350f20852209116640c0c2c1e40c90702e00003901c000380702404140b502c29038035024a0029041207442d100b0b0700c00140803a01d810108a001001990025008941854041c02400c104c0c6403035403501c8055000441022100300580030a000039800c188192001003412850050b80c500c408016074070b0507182280035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 728382410 1250 728381160 728381189
    0x150804020102300d05190e0d0807020a1407050a05010e0303073c0201030b0909071a0f0408100b06120103030507111003090308090d050d0903111903020c0a 68
    0x8103d400302168484010003415880200b0100d2210000c941c4003d0000054640b10b10410880000401c208060342c1804407060140301c0d100c6c50400c1e2225100f5240d038040c042036601040381c442c420440c04507401c2d8440d24010404404501c903950700e03011480f07018810100103801056551198044084804000e001141000c3c0b8554030148010300c000708600085050003ca980d1034414980001e00205042c0c01212144105000040989440d441850701503d07040f020f01c0301c28040029a44104e441c81e0002c83e0a41900c008c1034102403089030303810b07881454080390206060401040144230001e42a80410410901c5005c2c4501d40c01050400701590b120b080c01080800d00031001060200d02c0345e98001f048201030000142c81c20124038003c4000380d40c07000707054101f580041e82c09801c165154003c000d2005051401003541c40f844003400112070711804541c04060040e4030301501c004120041d02c0c0351040070000200165031900099005200e921414481814180740100a495921034034030308 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 728383660 1250 728382410 728382433
    0x81914041a1006050d0c030b03070603090203010506040608190201031b0216080703050d050d060902120a060902131a07020d051c03020f0417120301060e190803160309050d0606150804020102 83
    0x10818050304c1d1047c551220920780302a60144007003805040d06440018502280f401410708482c0010401400749180460900400c0300005207010090700740082d04085882c1c5100403009004042c0d901d060500711040080b050540224402c0310344070540c40842000f039541c014480da10702d0319110103070458011103c0061070a10403801401c0411701d04d1030205100d981c480b01417040340c4c0090603000c004102c02c070510400b00d40710300404000b0600e031013041d0b0a0115010340704030304900301d100b100c3c18444240e220f40002000c08056841e0550000c051414102d032a0406c1512007041104083c00e44a8544803408040d00a09c00d4640d641c0c0c0301042282094181800c1c4000c9141081200c11320344100c40c1a80069003011000310b0107030aa69403080740c500400d006016241300c024003096001d80c0305040a0200ca400042911682500320b20800d070551518102034880000a410094101150901c01000e005107038100310211801240317000010308426a085607040e02c1564003d005801c045400311 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 728384910 1250 728383660 728383687
    0x10e0615010810081c1e080705070314031e250c060207050709150501080c070f1a010b030f15030a020909100222060c03081914041a100605 61
    0x5a10001140d03510f0511500c40b00035074030f0a0070443c501400321a89030034050406600038030800c001d0a0503100140c840164190140580000414000c10464007060070402e06204584c07105403841c000c408145e03039090201c20b00030701d1400c1d400003902152614004c10050303141c0303c542c003101140710300c2070101c1c1c003940c44801c4075117030071002c010744003141c007030219001060041c025800100f19090001508402c040040780c9070702d0403075224906104050082050401d9000111100594840580001d1aa09180000103c0d80c80181d1714102c4400d40300124405918400640c000d5042c0c184d090303015078507940d19824826025000303503015000748ac0c2220060903d400e40582096495064684c2c20444a101d1802c0741c0183c040321681d00e0156140d01c14500680c40f8a0003d4012441c2c6106807000d542c0300900110009004c0a810720f000301580706a40d41d0b41d60104d0036400b41c0e550003060a00301070401a0704070315403000d240c8400e0201c4012845100c104d0500404607100c94441505240d00c0c013066a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 728386160 1250 728384910 728384927
    0xa03020d141c09050313240905190b0a0822050c121c09180e0a110a05040501060c051501122d05060403080114061605151602010e061501 60
    0x10070700750b40c0f01c01516002841c20300240c800c84402c0c052001d4480e00c0c010a81480b43c00071a030607850300704081c240b010b0203a403002000741030703440030f40e403107a031295100091510300b810700ea1000c00b0090b804941c52003490b510800350350040040300100d00c44200c100e4145401012111801070042e03003c15104900ca007404809074602080314800c1e03175141480c21120382c02e0304400d00d403014005a2a0601881342c0300e0102c0d8503003001c24050310300300402c0952400c2c0b1075840e421a84050800300710b0220407046035907082c80000107000040c00c00c1c000795039201d0020b411488400700440e028021041c8810380f8500054165040b03c040b0181e500c40c4c0031603901e652107030900c8941c2c56000020130403105070405802961084116101d0320083c100e078034140c01c005110f2030040c1c0042c101d44100c600040d449542c0c0006440340c2c00303001f0483c8488108580342403842c0041c023508440d18808640704100c8269014101c507840271204e84c0003440020788a410850b1280b84c100c500d07011000707a03035032010b40075481403650 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 728387410 1250 728386160 728386207
    0xb04060f0e060d23100608090c0108061302071203020304060b090408030712020705010c11150105060a12150303030c03180f0f032601030c0602060f070302030c0f07050a03020d14 78
    0x4205107107207a0b402d54149001321408190001100410014568803d00442c8d1103400d60010b0240d88014800007411003d0150502d446140c01145a901e503005560403146d6075a130004200e003514082070400780180d0000c0701d055441a14040042c0300d141040d810681c4100c1e40301250714038640ea026401ea80440f10b44210010640c0c2c24021600016000d00c13034000000d07200c1e02c80b020a070303904c09030461810406001c1901c2540070034004200c1c40e100c0400740e8140083da801c2c18007d80d00c0801002c0d00910a41d010851401c4040b9800400d00d86c1690003548640c0081e90706104d44200b8800c031004241e2603640041c80d140308244ca01001c41c80001c1e840c0d084a100b46008011804042c2482038aa42c0042c1c3c042c41c1910a1350040042004103110403000303000e2800030700414a0098061001e0483c01083c48041c0b5800200158604419004440000500d10001c83d00d0b91340c14248143d8442152404601500c00c04d01c0060516006601c0603c1900041c054540b40400c03000c0708282c4034812140c4c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 728388660 1250 728387410 728387441
    0x40c020705030102030f01090b031c0309110904031e0f090b09190e0f100e15030f0d1110022d0d050405010c08061906140909010b04060f0e060d 63
    0x1001c22540c0d82800154001c19208000704010350518980e10100c07059034801920a9105a003802c1d041040342208106d440640d0070000b8807040c480c10000422110544415803080b035441c100000c154000c2c1c510360980300510141c413030261081c0410f58075a00e88074800c20204000540c10801c0d101a00d00801000401503c1c0740f012043c455004000c0c0d05494100c0501906044100003100c5106080c1c983e0020403a60410030705843d10703400c85907050000e0150918030b8100400750000344c808110002c0c0000120040310f022404007440240115500042100507000e10288103101c0c0c0c2c2d00c0c0c000c0c4c4200c400c603004130460244200c0728002411584118480300072009024111409081d4802c0e40e114500501c000f040450348120001c00f1104014481c62003881464003100321801e40030610340503505113045c4685401c02c0a080d4a0650240ea040541d120607100000b0402c0714040307001e0022140f41c1d17200e07506840d04280090366031030100b410301908208148002041c151168100314100641c120 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 728389910 1250 728388660 728388673
    0x30507090e1e070906180b120a060302061903060e061c110406090222360207030e011b0818060c070f05010e040209030a0803040305161a090f0705040c02 67
    0x204a0b1004049840c1c0d40442d100042c10812035400014218500301141c2d2040d00d07a0381049070500440c003410100798024512480040e0010176240e01c21005503400514079074403410305022031040740a8040701c1000080c108940082d816031205103050141c4001401c80014400303844204a005203980f00c1500d60294403140490a500c071449160094440e0b4080941d99003802c00b900d041c4030001202d2081f92100c0c8003410030102044181c02c0241000072040910300342114501c095403000d00740f404204680c40060018109a0043d44441c0f407450284c840c282c20100c642d40c1e60146180460000d444004200500c4150344402020501801401040b9a040206040d01c0034945010303a00102c8045120400500403982c03c0500d22001e4074084600b0740c901020030020039240e121043d40105074290100201f010140640b0507150030903041c2030014509139860522824030b0306a80490221010824007080c2112008a90600c00103520b40041a84502e8030091000030694000200110301921 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 728391160 1250 728389910 728389951
    0x80405030d0e0a0c0803180f060d02130302031e030a03020d060305031605011b050d020d1107300206151203040e060307052d0f04020304031e030507090e 67
    0x2849403184441034030000300601140d40c0ba00001c0f44c0c020350002c0025600911a20340d05403c103072414250740c24262503400c08154400c01181c12401803819885a041c00402c0091800c0305000842c002c03640220120fa0106881c202c083d40c0f6103842d50218031460308100104c5207124003d400500908030075400004407945d5a480b210b04641005540910140c3ca0510a0040c41000d0103442100d801205018960802240b0060901d00c42c1c0184100c080e90040348900300310340b80783e00110142d1130451034230ba611100ba240516120062402038100c1001d802400144962507003818072007a40d0980042010b500c2d1840d10144c0c581124540e00d501c4804c4446842c031044003803014200030300e80050300c5001401c02204040c10002c0e00c5e0044d6002d402d000764030b40d1210b000d0100c001001050b2201c1d003041194141c011075803141500c1d03903030f40d04180000305000c1016442103101882c010910103090314480b060404800f40d90b03041d00c450300000c5040d0018040c6121070340e10150031120003a605440700710705 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 728392410 1250 728391160 728391187
    0xc050901080c0927060f1c02040509010b09010f03030f020c01140325031a0f09070f03020903010c2703150f021603030608061e070503150a0b030a1802030c0108040503 73
    0x4004da145030b460201014403d0b00c1c00d0002422043c0030040b206408102010304060841d20b42c070b40c001034880c546030b84c0030030321034002035001c03842c0b07514058840003d640c0c50741c0007004d4440c2e07c1c0c8001c900145410304100d000e91300c041100303c418841650303112011529030303040884542004d051006509207d04484111f03291001320302c01d01e980240c50119188084004610307204070b44402007070141d556038022131425a40e01c00107940c051083c1c00c045000c0030404030200d0080c0500603000750503600e451000030b050f0341c100c54022811884000105039000301c8000c80c0c140d2041c0780c4802403009840003c0702d40d241110b9044900c03101d02503840182802412400a009a40004002d4005ca941d5180074032002400348074032035011707480c15141c0c0044185015034098032600104001c04005010011a03030b40020610711540600c002001d40f842d540e100c242041e041c3c0d10503124646070307034a002100425117410701c21441940f41c000700039144c0b80519000644552400a004882500040000045000700c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 728393660 1250 728392410 728392459
    0x70809130e1204151b0b0f010f2103030e150a0603061407091221020f010e0f030418060302060304030203031b16030c0303020c030c01020c010c050901080c09 69
    0x9140320200d60004110582801c01c407074940b1003039203604200401e101c8040342d40c00000c04d0352518a0803626200c08041c0740481c5403c0e510004102c042c0321300901600070304202c5a281642c5a030440207515642c0e5a550691006a542254000e00705006030480801d021364480c0d149003900809803802c0016840200b44002d100710b034030800d1142d95280038014030000f44034080040c4001d107040d10a07414461400342104815100d0b8a9204c5045031844081000c0401c105251080103540480d59113002071001c0d40707911080f141312000350310786000f01a2002001851000c2548000d01540c0360500300100b84040d46d0300703104400043c075107032080000181c4581c2c000318072490180d070255440b400d08014205890b01c110f0886141400248400d18407000d101c44243c100903498100042c0c81c003045c0c603051340030303000310241c07607105000204038142800d506400800e010388161000f0065181e0460707080da03460048200720380c0064101000212034800e5400200000310001b048840c45600c0440041d400c40c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 728394910 1250 728393660 728393689
    0x20d051c11010506040b15030a02070609060f150521010207080708030f01050a05180702010f180c090e0601121e0c1d0402060f070c090c050306190b040506070809 71
    0x412110881c00c052034284030f42504804112018044a821000041e05003900000e9540304040008081640340308158115500e00707512804c00d012060440c03c020008080c103002030031a0a0400d40c5044003908070b0840541076510080c60b0b02596902d02c452048003004c0d08858060a40d82040f540011883c0f56000d02a05032168503840e60302d180c001229188020180e009a0282c481d4203010b2085076104a645000350700c1c044030703281903991904412405001e0390070107a4001e0303140007401c0f682d10069041000340030740264103950300240d4680ca0751040360b60304020412035412403001405247c82582604070708038000c4038078011091070190741c08101203400d00100e403800b9003d0010050051031002a440c10000d60064405e00d2800f5004140c992080b0b04030010b10aa00007500b000304a010218040a4000c040b01004840f0740000c014007542e0050301c541d44100000c0b0040c1007003850981448041c0c0d40d240402505003441c1100b8444a5000000112a43c0700b080c00203040b2030f26000141e15040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 728396160 1250 728394910 728394917
    0xb041e0e0105062d06040f0f09060b040308030c09130b120307080301090b060c030a08060906060a230c0a060501060e0603090a020105090d0b0f10080703170c01060b040905060102060112050a020d051c 87
    0x90323251030040710502680b940442c001906081c0104500e01c0003c080d1030440e0b4000850741d1741c5ea0342e5070004007814815620680c1e0300211a04203400304c00c103e41e0244201900c1942c0202014501001080da03e00038803400030400002000140004089504860030f08100900241d040c41c521301074541c1560010203940001401e21000c015080c5007000060b07800c83d40c19103419250180044008000c00101071026854081e2801400c02030f4200e4012512107185000549071045244d26094000d01028800c200020b00e04070070f4600345280190459004071600401010008200d42c0103481540209407001d5003c8801c050070008103507141000780c803035001150706508030710303105121481c4e100c421342150b402ca500034002880011480c003200359421400c40d94940e01c0760501040140076000e240c001c82d5108901041c0000c03d0aaa600440e001d07070002d03001c1d0b030056a22003507944104000ca440c0a00720f5031202d2203000142c2820149407034440e02581c15544e243d030403041d145088980807000140007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 728397410 1250 728396160 728396189
    0x2805060f0703021e061501090504060602010b040b041506030c030f0e0606210d0c020a0302030708070e01270c02071703070501051006021e010b041e0e0105062d0604 72
    0x101607042c0500ca81003524071381410b0f0500c40100901360365090003005075001906004401036160701540715000200b0b03004105000440c0c030740c40003d0190014810060007541001c4080240e4a4a4001d5400d502d00c0444018082d5181c04821405819001c860000303140c0c1d500071125070714084c1c0c000c021112440d0700c000d050701d090440c00d03c1a884103402031b070240c03c41441c0801c264041c0220f1001e0105542d4640a04056403d0000440c8240107500081d450700c180600001c425001250a200300c9549004001d40f607a07031444105041c0e5001c40c80c05c2241e050782d142000906007940e1103141c0c015551b2044a006031b48410001e8507540180d04254511f03440410341d84200a0309009840c0d104801251080700e070303842c01a0195440008602d00f228001c5085c1b9400d014550951001c18608002441803000035044a550b24000100b0030f1048811401e100398401d101e90140115070140310b01610141241c082204082412600d040c10188081e00000b42042c080e0b0b50003000e00060a900c5500002c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 728398660 1250 728397410 728397413
    0xf0f0d0605090601020f19030e0d26040303020601030305072303041503020c060c031e07030504021008071d0612090c0306011d01030f060b060d060e0108010b2805060f07 74
    0xb11088000e007107504561264400c644148008034801000001041454019004900d01564290890038410341c1120642c80c0348010300005004041d482c2c00441645c0b80b003d01e41e0b8094800512842c08041d0150b4819401040000c1c4200004d014483c080c052030058040f007650003170f070380d150000242000c950020506000608401902c4186015681001c518114441141e02e03110107008000800740e4801100003001c003568000344000c1080c40f800d03803d209d4545100044c0c020720f0b0584059005d50301d01007240108d2401140458094003c985504840703042c0d0220a00c6c070310260740d482541204c000c0c0b01411080c0d03114600e1a0041c0c0501000e0700110010200b031503d0041c0513400141020405246260703041d0004004c1410340b80c1003e20110300807001e09011000c2c00c20684050341062000502a61903800c5a00c184161240d5541c0020f01da6680d800550030784014924540e440031034450001803038030b20041c10214900c0540306038000740c1c0c0e4803000292240c121905000441000084260 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 728399910 1250 728398660 728398669
    0xe0d0207030b1e0a05070318050715050421080f040602011a091e060604030c06080711010e0c01030b041b0801080f062503090b0118050a1a060f0f0d0605 67
    0x581c40340c8845070009070020783c1d030a40ea40341400504100c0009554801103850740d4480e030003032514a050342000e4000e5030880d241c2a03517500e6040c498004656036110f141c1c40114440c108a504a60542141e038803035201180241c0c1b54020100d400720b43c418410848154820012005000240130300c0e00000380000c1c0f02054504240c282880a51150306030108010904940c10f900c04481c040e04c1510390016507608000c1903642c800d0b500041c005000140c4006080342d8040d424030300c180401d50324100500200c0030860700347c582e0044402c000e50080c040f54a020752007503204014644004002003000b24040440d14905081d003418003001170340038030041c0a05807041000c100b13104c0c05500141180d150882d90f50703c441c48100d01000780d081e4401002c0310554070980043d0340302c50f0804101040c40d6510050010400b0780b02134901000c5040800181c2d060307809109240003541d5140e14981481e04407801c20000d6400581003611011090024068103c2110040c000e1891000400103541d4100000c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 728401160 1250 728399910 728399933
    0x50717010b071707150504061a030a0b131506060309050d09080303061c2001180806130305121e0a150504020a0e04050f040b0702070602031c0e0d020703 67
    0x180740c8a0002c2100b6400100c82c0342c01c00400c801d00441e0503899a050f0b01c2c20307418046074444591420f070706003414801440b08540c04134402490343d115200b0481985828940c0307500c82290050400e0b10004001000020f1140140303d1041c8140c46201d0301030203036203451013120180e40011001903910085074007000410081c558038040c65040250440d0300c2d00c0540341e82c0b44002403156000704040848110300c180005000010742e94080c03031445803500381100901c0d050316500301c0c0a000406070070002c11110030b0b010035003094400080150070280c3d204d018804828001810440400c1020051010b01d00340c0c8000030390007040514080086034003106a0124603480241032003c040b86040c0c540540c4040f0301e078800e03013190002c1d50301584401220b0030503a810740c40d40d600d140c2c01c1401d2800700441d05421140030f03482540f09020110107503d44003c120303510801070050b4400f5900030400e1400505400000f40303240d041c441404645244404070240c244a81c02e5106405030784070010078001c20083c00c014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 728402410 1250 728401160 728401169
    0x7021e07031b2709141015060c0803090c1002030a0311030106020606040b1309080301050306180619090f050f060127020924030a1a18150405071701 65
    0x4640141d081a112104036200c1e0781d07024240044195240d4140300140d00401051600004070401003440300e405c0c59124584100300d513403c1c81c84c084401d1009010704a05009458245e540c4400c102501e40e030300c40b01d40d880581a20b001348a0900f481c1d0f4036644100006200d4030480e80995203981440d103014003503075240784420040400a100512845a00044032030344000304031400315211a40001090108141c0c03500d4903045070404075120b003030056400095040740d80c20b4044031202c0d80c132440900d030503c906103280300c17094100702d001c1240340480c01c6100ca0711801030b000001c0c01d610280d403940e0b01c20152100c111040d8000c1d0312002e070382c00420f100880c014001800e103802c00401e8884030920040342841490441035020030881c43c584c0711600e100d040d21860a003082411645103c0c000115003040b112003161034180250344001040c0d0003800c84000c0e00241c851084101c0aa01c11010320a0041203e03001290042d83c030b100c160303914000c49001d4491034941010b01003900c0040700003054140c10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 728403660 1250 728402410 728402453
    0x8090105071b03091703220317030a15060e210d0c08161b06230a0c0b0c031f080d0e01050d0204090b091e0c0307021e0703 54
    0xc000e00305800c02c20229502000c032141c01002c002c180390540b02d00304550040381c41441c00c0340008900001c004000c180713101d100310104841043c500825400025030340401800745040760712181c020f5600b90301071a0041465000420706017544410309440001e590301501c00600b2506041d5074604040c400340240b1448117940c4140c012402240d195208180001007041180c104010307801d0060340003c0d144c198022001c400717030030071860416415000c0000d004a0f000321640c0da00040c00d500607441c401100d201c0e500c0d030486520621301441c0007030308005001000d1000c00740f0700400242c4100b80b014410720707400340c403281c41f41407280f09059214141700740c124081c400c121041c4402c0b1000120203002c98141e1601c001414079201c0100d54500803512035000f524004280422400e40d260005a001c003415100ca140c03964649803541c03800304000d14107030500b07480a0007080907a0380300001940e21403024012544404810140d004048115180030781c1c00343c200340c600b401000500f07120700c4442880000b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 728404910 1250 728403660 728403671
    0x60112090c30060519051b0a170c0901020f0d0207140f03060f0a0b0402040612020904090203071217040b0a1202041e050a06021c112a13020c030d09020609041b080901 73
    0x84114008032041c80f081500205d02043c0c50421500c10900d140c9402740304101c4040c41e0a280c099120180c000f2045240036001d001c0001a0b900ca0004d1201302d0501c0960003442907515083d0130303002400e0f4040b001d9400c601310300c60410301503c04104240c050740108020f031620f8500400c015045070002a2480d0ac07441c01000200704003a0b00c03000a9211441c0960016a6510031000007030040c210b100009415005594000072222068018090047d000f2842ca000d040401c1081b4803003031085000e48001c152041c0003c0c04100e10a08141d03001a074100070061502d0303150200c60040e40c0300e600b02906044030ba0702060200d400c080c04240010a205e000a0901c081d00c4c00500c000da030084100d04040006030100c45008240c00c0150080030601200e03c85082540151041008560381d1141070013100108030410320400f82d4804c07070b0117095a04000d142091114140c49010340f64503513043c0c0c0d10210034002401315170746038810700f6134a82d1035031f0941c4080500d4040c0039042c401c000305010304692506 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 728406160 1250 728404910 728404921
    0x106080c0d02062109032820010e011a040b03010c14030c070f030305161806110c0604060c0318050303041406160308060112090c3006051905 62
    0x180c6001500c0c590480b00d071610740704c440b44a801201940003550410409440520104400200003404095070903840109160f200c40660501c401c0d0b104c50907400a0008402e034140c1200803020541980700070030001c10903030b00401c1c0031821741e4010943c5d180403001c6d050604c40c103884c141c13140d4134132004250000c0c440345007204070141a0203000300401c1043c2e08004002092420f006c42103580c09540045070008109103801d000300140b104840007002e594144441414550098070066156a01c0306402d6544034202a4200c6001c014203441107503600c1203111191140d6a508058000780056580d81403081880b424000e042c124a545184400c6050a40501494901100b00c9055503032003840c0c4165698018045003062050101101c0c2212500400a04141d80103582c6800b9003030036a40c0507600345e85c002880040712115100101820038890007003180402e80c900340c903104105041c5c02c00c0c0f29841c40403448024402c000084420907960003c114080495000030112120010020002840e00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 728407410 1250 728406160 728406169
    0x606180609070509010903080a17090a020d031211300108070308161b05040b030f0312180601030b0603060c0a020c22020406090305120307020d0e13060e0601020106080c 74
    0x900b5a80802000055010b142d9000350920002507038810000c03580d072044c80d1070040c580301048445502d41a41b10006c2003440d40c001448000740c1d40c006184001020340c559054a21401c0402115400c82c0c56425060103001040007604845020200350a50303005010708001010303000031300c08501300060030014400d0140c0060300c0b00a50303038000303202c40d9580c881d00b244444098100f403008202400b840c0503000001ca03d022042c0860354144c40a0104512402c01c0541f101a5106c104265074014010054501d10340801c82c1e800840400280040c032114140032070910500341c10980d4251241c1d0240019800c0402c0002d0340807012903041801c02211440c02502c0e0504900c0d014403800c041d0707030945408203d040a50031000c5503000c2c03c650343c907a11706010308800201d100c2074401340982c000e445036a1003400110381c0b08104540c05000b500714607140a60b03440c07401c2282c1c59008204400000c400c0c0c01d20703100d603901a04400203002040d15002000900755030698000c096079402c0140560045d40340d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 728408660 1250 728407410 728407429
    0xc09060e010905040c1a1e090f0d0602070b0403021c1b030503070e120d1b050c1c02031e1c2c030a111c03020a02010804110d0506061806 60
    0x1010b51021645440d10f003003040c07080501e81c01044800c1c0c003410250f86403001d4030000707114a0040410001d00aa0504c94100d918028890699000110320314400543d00e8100d0326442ca082c41004014102500d03900e420b42c41580c02c86049015034407a200740400f081541041054040e400d02c0c102d803429001c070301116a0081007400040c2800340c00300c04100c2d114004c45050300c030400e002c1c000048060034185d83c0d541d98200c50b108880030402403c200d03040c145070008034107583c0707400100520451a1500030303c265030400820850403850752000a00050764288202118003540c3c846285045134820b60b858280f000c8050f40400411030127120040c65038101788071280c0950010308000303032881c28181c5444008112071a40b6418041c0000398000c11161541c00d111059045d560706120080500400c08964000b22014015034403282100c00158440c00165034081d1148404410345503250010541e540a413101c202c031203030042c1d4104240c5c0d0030b10240341e00c150384810940f00003030300f4543c002c20502c54 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 728409910 1250 728408660 728408669
    0xa050402013e251d19060923160815150c01150e01140d050a0c06020f01020a091e0b0313030906052b0f02070f0c09060e01 54
    0x418800c00e511204161503120351841e481e07403288200b00e0b0b041c074507070301da15210b05101c40281c0c440348400c44082c40d400240c002e540030340d41c410540d41003420701112034500c000d10f00c01000e40d00d03a02c0c01e154400f41d1700a82008218404010441d160040c840400e10f01c241c821340004800c00c80c0c10000b1480b0030f004a500c0040590500d101e240d110420b02414028281c1040341d00041c0c50b0694101801100006041000e51103001704400800f808004409000c07603c10340c00224403020050008a0f034250b00c120140f80020f01c10890b82d1508e90387c050911080070340a440c11000c100c000c10060342c05011146a8801d81c4000310719000e461400039100d111980100d1422101031344551103898000000365020b46140001c2c19200d00d4803070b0410401108500088001509929000035102d000e441512034618540102d14201d4250310140c2a11041d06442000010340740c560f4610030f400144001e01c04035000d607030004024009030074900e011007000d900080c005840c040042188058198a01c1d0655 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 728411160 1250 728409910 728409947
    0x111908090f0a170a020a0605030705031f1505120c210a1d07031a010b0901080403030609020d0213080f030307050d02040e15100806060f0c190305040e0a05040201 71
    0x109880082510042e454009040544002ca0082d02440c0c1c0010075840c4039108640725200c1d15200c0204075090300060f10070101041050000c03c840d070407416000b002e18490040c0f2004195030340d2481008a61201e840300002c28000119561074012100c0001d0b807080003001c41130300e805400817501040780e415410f0882402600c0002c18684034440d00000c4425502c1104107903c4048906502e0b180e07401c81c4801c480003002c03070a00da40503c0c1c0080e00d4134100e4000d2402c1605141030080192400e4100400840805503903480104100c0c4041c4007906008480c07100041c1c54011240b104504180306421002c129402100803d014034000411070794805510301d0090307110f6401384440c2c0c0c00381c001e0750094400e0900c01c0701003100b80c50300e20180b250031482c100c41e2400301780da4144055134403c4060321840d4101c1010000c0c0c4e00c0a001c1c400051402c0401141110107a02400498a00b00e07180c90340708174001500010100325100100038020382000d44c030030040020f810640d00103080b0080008600949 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 728412410 1250 728411160 728411179
    0x1b0b03091903022e050a0c0207080a080d05040201021e030301140a05030712140105010602010f0f020c0a1e0b010b0711010206010e0402040f0605060c0c011b0b06060d0605060a11190809 81
    0x3202e03480d4a1005101304405010311080c142502080090300c2483c1c1410010700c40c103000080d4000f80050b206000f02e4000f070841c0c1c0341118030444031018000040042e41507110b48030181031440c11440789100c2c0421400003664403541440d10150f2050518004a40f01d0042038601b484159404070398081102c2e0203001c201011076251401d000c9082003011411441d5103000000940250107420030414100f80b5401000b400d500c40c0f0a1500700e00450020f00c450f6840703e0000c81c0028518a02e00900c400c212684800041c3c3e180d940700400d5400b41c02884000802042c000304000c2e150000381310088007400501595810064100914800100b01911039511040c0c0806500c01c0759001002602000d00340c03550322094064081d565084120075a8001400045116501c200c00c102400e03070184e01c00c8400c030440d1100420054660400f0020302030165071000c000650390b58040040800e2400c07900d07070050202c140c503101c1c0e0070820710310090582c03504412042e00005088100722400250101e824040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 728413660 1250 728412410 728412463
    0x60a0b030c030a0803090c012a0602090d060902100206220f08030703020a0809010605240405041b0f080705030103032106060c14120f03041b0b0309190302 68
    0x252020308501c03550103024070000002400328035401580304040c494110b070040c900d03035801101c004400180c011023100e80c4809801c442e01ca481c201d2400b8a001c0ca1000d030030401990006078844c619031004442099840302c0140450030110510610f104060001c0c090b9850901e0660b0504c842c00c0301c0c01c841c03c030003c40314181002054603c42148c00e0f04020559181d11b08002c000d8000d6005202600200b4a120001011514140150340070348034058206030701d284004480d09840500399014041402c414000410f45131502e2040c0c0009105189800540030b906c4180542100380f4550f144003002030307020421415a4001003201d044943c1352814036030201c00590154019001c200d00e0b07142c01c5003003050000342030ba07214114203800d600541ea030a0003086402012365030340c540d1034103901030302c0400d01800141d515008040c65106005040d81d840440d00014410700700c40403500708d5600410040b041c404984400c0000504001403060b40030058000c540380a551080400f418100b810410103400740f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 728414910 1250 728413660 728413663
    0x51f02122107120207080301090b030a121803080c0601051206010e040809040905070807060e01020601150810030501090510061403070902130801050a0c080c1e09010c2a0512060a0b03 80
    0x148007404103c0031512452a4580007016074801e00ca9964001d0805003800b00034900071851120f20390780445606150400d01109031402024141360380780d42c041e403090000100b88190010650200c510000c0d01c6291305001c2004000707150810f11005079070006005101007000d4124454216801c103003415100c90400d030003d000f81c41034210040142c06017201c002409100003600900ba6803090301d88208851140c80120307504d2030b0034422801401000040b03246010f0040f1903030354000190850a003903c1e9120f40b00c203401d45004c400112100e50010900001c00c110f5445404041c208000750040360783c1c0048002680c0340784500076501040da00103110f500c0840389003400001080484024860351134100310420003080889914130100f01110700003450340020904440603070810341449025040f192080c0c02060300201c81c105d050005115a44022500c4841c1201003410144540081c841607591801d2180c084d070380c001c074080e002201c0b040d41202d0300810300d284d100440c038000091200000001a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 728416160 1250 728414910 728414927
    0x140d05130f060509060603030703090e060d050f0c011209080a0e040e0a05030409110c07150905280807080a020f03071d09010b100507020613051f02122107 68
    0x3001110780c088000d08106003034002a01c14071851040d540c0c0c0c0c0d5102c00074503841e0700c40e448004000400c04141848907140080c40250040405450310000310010ba898034a0500401d107400c0c1c09a20412001d0415030b4040000b0300e0382e898508041c04400481d550f5068a402049043c00a00c02c081d101c2c000d01d9281d07a0b000e159400d007a507080f2080c1c56018146a5101d03800307400b5481c2540e08250300d9805202d00001100e002e4255140140f03001890088840700300b0348081114030400141c18000100d90b50ba03d40045403c1d41c220300e40903281c130f425501c04641112998400c0d40c0b03a80119204112071880403522601c1290180c131202240400701c800242021443c0d0411842001081d0381000101c01d502c803000e1007055881d00070409060044104952a0008401040080e504012500c01414010040e12940041500c1c52017142d85440004074000203c05c1c1c4007105080c500412441ca9074104004100e802c1d41c510f10901d042c000e00803c14007000786044c3d8100b1404880041410140300340b061 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 728417266 1106 728416160 728416163
    0x23111070302070b0a05040e010b090321091201020c010608010b0a060e0a092406023403060203060607080c010501030c05011814120f1c140d0513 64
    0xb98684d0b50700062030701041040503c03002030030105180100b0301800719521041d03100c01d0458189483d10750459200340d40112510310740c1880c2c08200084815409041d9200c05662500d070302d199001e4800e001c080031080d8600000000c50340d10650000300c0403a01110005485595403000b2100030300c00e80451030344540022820060709400768404030240152066900d20f1414607648400c4210040d0301c4200540c00200c0d90388000c080c0d0148040302c0365082d041290352a1024032007041981103601004085960000105585695103c02d85981507408402c0a903035011020000780648400c0c401203491110051002c5810741c015910103c074600c2010200c1c003d03901d02401600c895001071003c0c1c0c2c0000c0550a070514000040c8501d030b61060b0550010090200c803170340a0800324444c0d07201c0c0f10402a0f8550195440e0070064119090028140004150346e1610140300c2c5107000003020 = true := by decide +kernel

theorem cover : BRFrame.Cov 728237410 728417266 := by
  have h0 := BRFrame.cov_init 728237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 728237410 ≤ n) (h2 : n < 728417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
