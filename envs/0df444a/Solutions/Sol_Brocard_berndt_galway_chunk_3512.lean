-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3512
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:52:51.643979+00:00
-- url     : https://prove2.me/submissions/3d39935f-77d7-4590-a9b5-0126459f71cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 631474820 ≤ n < 631654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 631476070 1250 631474820 631474829
    0xa0804081b010504090b0a1526060108070825030c031406011b02130f0b090717060f0609040c0302091903020906240301030c03210c1b0905100f 63
    0x10700540701520030b80c2d02406a80c00c2e0b4901840c0000d01c650104000b070314072080e9500c030224030580201c20340b0150741c00408404803810034071140b61412803034000034031030b40c41f040380d20501142d4844041003442c0d10824815610000e07100b6a4000a401110f40b16070031151018000c00180e202c045401c3c86982c1406020400d5140001d24603103810800006410541940c031744000055581140605554031000101402c2c406c1ca80b00700130181413000340201a084000b0480c2c0900c1c0d044000c5407902d88130302c3d4078140f4041022074901c05504c0303d00801c041494880300c4070750321007400d011101c0c0517907852040ca41c80180f030b030702c006a4030140102807008602c403822210107001400c603c1080075850702481c09074000f000320f88100e0300d000d6a000a0300102040c3da0a42100200440040304010159240f8810b46c0d00440c0d602d50403500210354407000c00183c1d01c4500008000d2028100019812000d400c020209641c5e03582c4001e445414401c00c0360005c0391210304500c6140e404001c40740d4040408009032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 631477320 1250 631476070 631476103
    0x90f172104051e030906040f03060b100c0204020711090a09110a0b0708160807030504080106050409150b01050d0c0207260d0509041416030b03010204060f050f04080a080408 76
    0x1468951207580c1c40d10345545640f02c08904a40c10100446800d004a0f602510010a0725840300d448110480509141c4e02003100c900d881c0a441e92030901d070403510059151256a00e011960905034280000394004040440b07481c0c04039800e004403913654009142c4a600188000280002c3e6030800c850080c01f5042d600d401281240414060100640704072407441da041100c0303550f1035071080d40101c8881d0050001608001020aa10040542c072200410848a24100070310886498204000803118458030040408418501c95a101c40a5800107641890141400d034108000519004207582290104600582000c4070034801d240030702841111801400980b1904000d203c1324590755820441c2c4034406202d004121a2001ea80e2900455820310680c1812242130030484951169042050030900c00f080c10050007180d60b08051094170f00300c0740d0503a81d416106446c104151803075408158102c50949040001042c1940b04011080641d846640444d98440c90400e115080454040354940352 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 631478570 1250 631477320 631477387
    0xc0503061306180e120c07030c05031b010309050109080f0d0e010c08060108130218070e0414131502030c0702030f0105010807030b1305070e060f010302091003090f17 73
    0x400c0210010400b4240d4018000803030745450729806240c10300e05d04d80010280000034884042800100d010350440f817060f10308403001a202d104050302c1e1034090000210017217027855504200d603c44e0b000405054080e03c000185400c40391075100240d0721238500541000c40002310007450708154031a618083c2c03407200c000c1000642c0d95600404e2400b010386810704010460b4003040001e200c80c0d031000341d800da0003001c0c00e040c00003617000040c4208084440f080880c681e0315803441941440c3c01001418000000c1c01c200594032214030202e800321181041d80e03810004200e0b0100d1003a544020f60062072200c8a0f99220226481010302c1c084081c4151a050b9040600400c1310000010320002500e501c101c84203810f030f5840d004408000c43d04032001d4214426000000740c80030f1031342c850601410080da00040082d42e090010340907440f40b10a8590070407013140c1000d000c01d00c00d0740600b408500c2140d4080c0245d01d152030303449400125841c3c0120a03680010b003070710480d604079142d4521007251200b9044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 631479820 1250 631478570 631478579
    0x2042d090221070f0f180e0a0209030f010608120f12180d0f09120b0c03090c1002010203060a05090103020102030313061b12142502030d0c0503061306 66
    0x2160052240d900441d401244040201e280e10011188403080141105001c0c505040020100c084076a141d0011613620344c01030b08094030440c40304a0701d40710500c2c1da01a0f5864a60250515480104190300d44d03a800d03c40b500c81c42d41c040c4510700703564040e00001300d86907040000050510ba60b130a080081d20508000031821101d016064454444500503945200c2d51070042e0200980a81e4040c0300040c040e02104540d00d581016105005140702d07a0341d0300206440e103844a07040c031400304028011064440003e16510007000007154005074040c241e0f40041104000314512a078650f2510026035008400c000d1b46003050307056000101400c464000d819455a00087c2d26444043c3c6000c5803907145184039024015185c21071500140c40c00200c01d441d030390140000b400c030002c8003c0889110f0900d01e0819452840460490003402c402d00421004400300c288854851000d1459405602080c4245007410000d4030a11840001a440b6141d80c0d10b485400c0002400548801c4000c251a120080c070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 631481070 1250 631479820 631479899
    0x8042a03060e03160b0a060521010506012105100803040320011704020d1704060e03010b060403110d051c0c020f0d03020601120c0e010801021b010912050d0b10030204 73
    0x60042c0c0d004400170a01c2e40b204c000c3c10000c0d000a41001d60004904c0c1500c44041c0b00216480c070700c04c1c01100081006445103401100c2c0d140c103040d5440c0d03801000000c0201d241c46103922054101214143d0f203901a9990382070703035042d42c0040c2d109440651696034103400044000c0d1404018034030900e00344208100c040280b04900c9800342c00a40109600070310700c402c0004541c0d020717101941581003162220b40c1d64900600c1f11041d81b10b600d000707500b03202d54002d0320b003402d800395019030f54004001c04c02001c4071024003040c0d034a100790a40d89482400703070340e0324682c2c40102035401741c0d1841c0e40d42192650160040c003e000c080c1045242c0250030355030b41200441c0d40443c5003815039a05000b45103c0345002d0412401c81521038100308420301c50740000150810055008080344031011343d10041070b8008000e940e081362440d94001d02010200aa14400e552090005059800c41068000b03a40821500443c03001142c2031b0700400400e034009001d00420304181291301081c83e0340100e980d51a100590a030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 631482320 1250 631481070 631481107
    0x50d1803120809010905070803030a060603180b0c1308060106110307230f030f070c0f1202221e05150303180409020603100e060f01080708042a03060e03 67
    0x28000c0111203000b094402d2821740040c0c040d0b50b0080102c0d02e2080e06e0f100381c0c9403240e1040d555040b82c0351810200143e2603000b80504c43c040311000f4100c0d080d0424580350f5540803100200174400d0042d041000ea00118584d02441c0082d080d40d500034070181d81000c0001d420701016003d0f20a030f540c81403040c500003030a01c680100242c01c42541c03d0251800c041900c0f40f84c0388840d50fa400b56404049005d40000e0040800f4110303050240000103001d035a20b036651a1001d9290244da40b18101c024000360140c207040b4060302e0071515010307a030152841041d000c070048070514694081c00345140d00c000b60000225000b0150411301c1094000008514200000d9891041040e81d0f0190700b1070402051041d034960b40034032891900504000d95a2800407003030502c1c9440c0c1e0143e52076a640f0100418110300b40311b81001910300041c0c560000e9a141e0318416611504024811139001031008445081030300040d121603450040c00102952190551519000b40e500210f090038044d48180000c44849510742c400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 631483570 1250 631482320 631482353
    0x3060b270402041109041e050c040f06181a07030806090727080d0207180504020603040201050309070306060816120515041a041112010b0105030105130603050a050d1803 74
    0x9440380c1402030301c0e4003600992a40691051030185a40140181f500c5e50852002d18500d00b00b00c1c0b0360750405003c03c14040c0c2d00603104042d02c04903040c061035006aa50b8448401c8d20407500c950340350b80e04240c5100820a40400005500100e50802010741100181c0e400100031103003000d0604d8082e000900c160b154128400f0a01e405113203881c4100c9041030000040c101c01400c2c0d0304600302d0004065520f00d01072240403038110040a00708100c40c85803103950300550b401000749203552640e400448280d00040d01d0903640380100e5034000009620b07446000010000328000d0030384c0040b04889800308080c29441082000c8040300c1000010f00003150044140400c07c4407219680c9031810020000e52070340030200080c200c4d500c18801030200904910000c90021100702c4200407005401609031a040460180810410300051042d0700d000d1a42880342c2e00c3d800000143c050b0b59859241c948542d090301554541c219192000d600c542c402c41e510741001d4100380f081c07805840c0d6503614405883d01c242 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 631484820 1250 631483570 631483579
    0x21c0b0411160303090b09150a050906060d030210060905010f05030309031009150c18061e0f1205010b070506090a12030c1b03030c08010503241f03060b270402 70
    0x240b020540a40d0141d000706070426000840f80c40d055603896900c548010000001c0c0720f41d0000611904064040c581c85000c40c140613200d11f4460805202d07580e13400c004210194002c2c11170b00100b541e0144611001003100d00b6022906500d0221905500522904071a010307800412082c10700e6100010400c1045000000c0001c0c08065401c00000d480c40411140752880d040070064030100707911465480c4004400b4016049859032a1016240d004401e22588201c58911045810711806403250001c2d00d00303582882e100e034600d02c20080e0201c510036044101c0d141d2000c102c0406002e42001401c1d4054101c3c4000c141800b45a10341400b5050403010f07100416899002c2c1c000c9140c070540c900d0382e0428088c400b20801144915029002d801143c80f00f0001480d220000644e9160000341820075039080e025401028a10b0703116103108a60041800c143c1c0840d18034640d42412448050400a5004141c00544035003035608000303203c05a0001c089070180882c0b10922150581a50140c20650444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 631486070 1250 631484820 631484857
    0x60f06022112070c02030c0a080c12011b11010c08010501020a0b1b03130b0f190e070521010c02070f0e040302070503060703060521060103080a030f021c0b0411 70
    0x4a05100c81c401d031005820601e075400203001500b500019809001340c821030a0700c82001c840024821000036a2280b24650744c810000e40c8494180034071400c045e1000c21002044007010b500c1ca1405030a0010014000100941e07c2c4041d026000e10071b51400e05c0d03580c501a00c60354074100c0000d40e40d8080000c081d05608111000c258105010843c41100d0680c0c0c0c04910303141e1610134100d0880e000b140c08251441011f080020301e0250500d01200c0c452465031560001001202c0494401004101401e918503c2125000310b0159500d110f00d41e9090303080d00e000910004c40038096801e54004d02c450405640c00114140404880c18841d007041d242c03e620004d5007983c41e03003422460f20240b0f510150b014003e181c103016110358190401d105a400c256220509808407480115040c11b014400c0316803034001d0b00c01440012142002017469205900d00401e0076401858035004903882504446258440400c50301c06c4080c0c98094070011040c110b03820070582c07417400410040c0c2d101d0200d40b89203502014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 631487320 1250 631486070 631486123
    0x2c0a031e050405040504080a12050408030c0708670f0c0504140a0806060f01020a05070902130e040c15051b0601091103090c0f0a0b0a030f060f0602 65
    0x90090b40c008100c000c10034416410b1070b0a003038205170720012944c070025401210249500049004503800b0f160700620840c555504c1c8010400d40d0b401401003182d03004010070510f07444180c1142c0c01d2170064001000b10b00800c1d21035100000034010300800180382c0c410400800c414035588920348a00302d04400455400c4490940080010420071890309402d48c90902000c140ca90304c400a03005aa820701d1002040b0386404007000500720b581d124501c80c503440103000940e1400c00c1203003c80203c0043c0116089005256507043c10000160800e51703402d40e001c150300c4604419030808100800100d0042080b501b001d454032000d448140c05212180e18a07540d13200c01042c429000c888003696000d816601d400d90b81c602480c0c6500d420303c18580340b20b0400003040011080c000860303005219540041180ba4030103014884807001c0146c450341d0080c000313500029182c07203650062070f0503d0240d40004840c00310303264200c1211038940120301000d020300d0041c018690005aa4501c20300500503644006004e03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 631488570 1250 631487320 631487327
    0xc0102060f150f0409141b030f060114060408070e04051509031e1c0f05010902271f0c0309080f0a08030c0c010c09061706090103110f03012c0a031e 65
    0x40805c02840f15161850404122a01041e440300a403030151204500da039844041594590400d2030000e0f040d0082300041010300040c0d107041d1009007028241e18117003543c45034202e0404107140c0c01001d0900212040004110040c0400c032040560b049500f01a41002800d00b652801100d0306d04040c164103582c904980161982658071514842c02d080c07a2010190300000d02412000e10b000e1075072030804002180c810268001e840d00c0390b42c0801c0410413032030507940c0403c29030741401e0a540c000c0d66107038661030b82035041812040f40001c141c44060340d054580c03034020003018680e8003240c501e41050786a411280004500c0054180c0c10490103500c03601c540e48210030500c10040c0c2c07041c007580f07400441d8090b1a00003071000100d9405480c1d64007d030f001000201c40c039a004889080d403101d40c500c018000a4a1000c141c3c0d140c00001c1c000200058018020034215085d2041502d203410003420388240c0b595505500c80007a0780403002030000c0c1c08060f40d0280c402c0a07001e0340c01c2c445d00040f81c2034071100341c417 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 631489820 1250 631488570 631488581
    0x30703270f02031515090a0204141e0603010306061503050601050a0f090b030906100f050d0b07180906091d07141201050f0a05010b0c0d0327050c0102060f150f04 71
    0x80c0384030f001013142450315004d80300c0040501000c1c05658050b0004440004900c00d95046680b0b00c4460444c0c40080c01c00c0082030364414208aa4109020401403040c1d1194009113001e035104075000200c0609207100e800c0409a184c0b004801c26007800100061030364400c3c240c500d0071040b800e101c0394403071110505440400b00c540140390400000310410500c2200029014020b4280715a440b40341501e07540d00e400140c100e0701a030350704545080710321000101840c000c4c0d50701c06898509003080d03454400803201c041040b6070000c80724549940040c401400341d845621029000f14188011a44024100c5600c1f04200d118200d40e000d12402e0500c0c85444804026008100c4d010003000340303180444940c4a1588162812100e00d49060f0020641e04102c07000c6860201500c00206446001c402003200907007030151b03540240055007000040052421012641120b2240d000b40c044030ba010b1000a103400707001001c1e0005103c010040c000c001d4a03214007140b20350019070f451407422045d100407034041c14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 631491070 1250 631489820 631489843
    0x50c0a02060d090309050d08030103020603041127060102010b1815090405010906060b04050904060f1107081c061d0603120307032c0d030e150705030703270f0203 71
    0x40c0000c504060b0401d6903c0781800d14400d413142d4010584440071b001100c031040c0c600038080b8804100520241c9008000f956000c2d00c21890401061284400b0130104545812412a11046e000c5907050394035810081560042003807008001001f00c11000940003040d08080304064940c00001c59610710320134040a80c0c24402801c24000e03030403d440d02c2802031503680d60595030f407840c1450118410101c10110340c11604002c00d150002d03121612044000c018200c50762400560762100e8482c020020301c0508085030041c9481c1e5221543c00240e4074602468407050281946003c206000104144c0c043c1c0c04a0300380050041001d5580801092600d10214850f0f15800408010066001e0b0301da002001d10b44100b0a49140d100100b031512524400c0c003003041d81c15030704041d0104203464840e41c0310300426420101181c01212800c00d81000190007551038100044001040003030890301401002c00c0d180c10300d140c0f0031101d16040d00009501c4001000100326141d8a6180303410755034200b080403a6032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 631492320 1250 631491070 631491079
    0x20a2703021012050a050f07050306120616080f1b0d060e010e0403110a03050301090b0d020402040620070501140d0e060906160525050a0b070c03030b100906050c0a02 73
    0x40002c01400740000918600420315582000001051039185000d26402001c4d42040500507441e140c0c01070b28190401800c16070001c590300072140d0703007840801c8a140200740c00b541d18032000b4146200100040d100404040762945d500040c000540001c014070b05551900009083c0c491405044000c06000c4c1d5500c04203680c1401e2002113040340b420280140118803076150b0500c80500c1d400c1c1e154441c210200c0c09000b240c81480104178046080d00542c039003140050180041c03805d1540050200c0c0c0054001c400002c90794010643c0388010141c1102c000040302d8010400a403824000809a401c0c608030042c00c58070104800b1007885290300021813078118a401d64000d40791000600d41c1d41c50044030607503562801c09003165852402141101e90990704442602e14600303110b100400b03175040112007100d5510500a40c8404181c1404443c0c0c000e10140c1d86003c40c01030b0604008044c0c5009a40e21485800742000519055400540c800102c900782d08280d074503000c507640c01307600b000350390500070703410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 631493570 1250 631492320 631492339
    0x3070303060510020c011403062403070201050709030819110d080601020c010e03100e0a0f0f050c18060d03090f26060601020a080f09151c020a270302 66
    0x101038140d040101a40c03000c0e40c02c540c030071800d00c000700ea0f95142e00f600180400e85036805028240751981c019580500003900c0c141203054509452044448003c03040251120080103000c0f002e1b5083c01000d41100c03041c80c204080a09540742c0000910500d000c9500c01c4409003a0100098050340071f0b0004c415046007a20204002554054054403044594900501481505081a44c080d03109180e010364090002d142c400c00c42004072000388034120009042d4400e1100c24000070b11128090159070740b0071a0500c401440d03915080d450305100581d40d5100d031600800c46101c40b22080c1c005644803904658038201c180e0181010f603180401b9401810002d048040003056406402100e00c051a40749208101080c04c1c2040c544d0303c0710340594010340107800009040c8045034511001c0c0c1440d135003444840d0b24107100900000c01403280c041c0451010040030030b11002001c078150321265410b0114006625205d4003140003020369100e040c80e107490035201380ca990f2441e80410000005035034003400c80c240 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 631494820 1250 631493570 631493573
    0x20d090c0b0a03060b43150501050103021810090503062a0c0c22021201060305070e10050c100e1e1b010c1401090b10060801080c040509030c0307 64
    0xca5500c002c44510100c1d0826800280c0300100e00211155810f580504000805030442d6561240305071482441808408010420b0521660082c554166110f01d109a030b20a241488010640784168425414140b040c05001041c11806401010207042161359410b030340500b01081d6069500ea8002c181c040c8070fa5010062507444640040b0540501c42c4107403c17400020065501c4c59100b2070103242c0307040c3c00454000c220303410041044011100c484d101440c880c4024000c8400b21703001000c8105150320300d8001000055058451700b60030661524000100d080344d0404595561105201c035001c1003000a070341d80051506002d40f460800c055041130025004203c00d00d0360700c842224070a03402111840080c1030004000a061500254480e00342203a907144000569a4200c0c100d400c1d9201c1c02c071228a4110000203115402010703201d41d4102c1c507a0300b0f0ac000b64030070031082c541141c02805144401032000c140001990f0b101c14004443c089801d1352000f00315411070245080ca900c41d440302080380320 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 631496070 1250 631494820 631494839
    0x80f100b0c2e0e06061f052101140405090705060a050d0e0f1c0909020f121e130308060405040206160f061b0507020d11100c201003020d090c 62
    0x2d2806203968040c416421602e0300c8945458080d109035074801c10025402401010304500f5425200700e500b4424189101c03c0d480400300c6000c0420360281d866103000520a03620000c02428141c241a902040540303040c441c400e0380e800080c080c2078411040401d400b00014130480407122041400c1c02e0500210803080c0d116139640961850000139401030541e032407511201400c1b1854032550a030b6071201c40600e010f120303000940c8021541900c08004000d10781101a0f400c100c14050916103101c6540b108548041e901042000707049106c83e40c4101190001095102440341c1d040700013114002080e4445100081552003801202001140740482c0c1d08103200b10407060003906801414144440d0b10490000594002008030782004102d091003030001505202d200b80d96481e12035004030705060f0741c2c080080c549450b58800000040e481000300e01c2004030300c02e1544092055042c4c42c1c0380b403a94070703030000c1c10030b440b41c01c854404c0541c00b14441001028036000b60300c00d56044281d4411098072441ca15 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 631497320 1250 631496070 631496143
    0x9170c011b080420010905121c0e0d1e140f010c0c0b041220030702010201200f070602090402070b070f0c03020c10030b061603080f100b0c 61
    0x34000c40041621649594000c0803100e108640c026241403a5003580140155844c00304100981002140d91011603a61140340e980c0031220b0008009103038042800124202403801e0401e180100060030998182c6611510390144a179648060702102e07540e502924010580e01075003018105150101e1900c0b005c0d4008140074100e040d14000901c2004130641081c2d800d050300d03480050442054100060114559210192481c4064901460903042c8501001a0900707000c403102a0354000003800307400c642c0c09100380d1081d004070444182c420400d08020720968051855010b0307035440b001a400f410084523034102c403100c00004000b107403100024145003080d584100e45080200da010503820840a01480c06c003500181e05500800001c4006402c0c0013102015601f1441456207450b001ca01c66a24900070f4045c0c401440010118404281402440404c018107000940e845020a00c0b030f5503401ca2652105540072000c0140e964241a880da5140c04e084100300502c014000ca04c0d0103140c41c000190 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 631498570 1250 631497320 631497341
    0x10b030724050415030207061b02060117071d13120c06050109140403030b010e0904081909060c2d03080103051b0d1101090806043c0609170c01 63
    0x441400c0307200e04000795802c0c400d83c01036901d40303802d404801c04101c2c401d40003001c000d481200007040343e9104886000c2100c1c0040e80650250300b007000103105102c5c161400e5142160360800400c1001d25004080900440c0c00b00c8890728404924009581c9515801c601360340158045d80030703100c1044819008101d2005500103caa06003040000a41c80c1c0c198000c0c00800e01d0f00c1d1509894944890b07400fa0700a01c004c1e14120305124048105582587c2d400070260700c502e01030030301c3c1c0d0f0307442c035101c051700a803001d0851060044c010411800c6c0701c4980d04c5210102074541c444460700c400081035078086982d49885c10a10b14810301c6a181c1010540e00400a904070f0344103004644903600380d4142003811003001c01302150802e842240e041c001c11001c15980154000605080324010f8480300703602d040407000c880688019220034000000000480e20502408110b0600041e50f40007401013400d20000d0404083c18045d1119041d50074042c070714000b0446000d8003203c130355840702021450345c00b034241c1128 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 631499820 1250 631498570 631498619
    0x1b09041202070f15120207030807030f150e01081203041a04150e030a111b0d0206040806010b0a020706020c01050a03020a2705120303060622030b0a0902040c1e11010b0307 75
    0x103800178404070600035601c0080e8140c80d0100b1641e22801c04500801c1d200013040c040751b88074501d0000b00e20358501341d140903080c801107000666040590303507031414a500d01002140d200800410000c114103084110131b50b4a0206161540d44803802c0014044440010324642c80e8905800300112a0340040141a03107000d40d21800c041008400c0c003961a02c1ea800d240d221101e00311080310841e841d01d441004460751006003034606141d1651461450b00702e03341c202065900000500b4866190108404001041c01c0e100401c0c0070300c0300000080c0203001d8103541d041850b40104100c80324078080d40720143d1001081c92070720380800c2c07941d100801c211090711503a8001e0f0021492440c03d0303030010049030b214000c0601590b02d01500303116078254841c03038501119090343d07d002c80071000510f803403035645c0103080309440410400780f140108012610306448074400e010507100e21540c501c0d184003004282d84c103103051a802c6c3d05051120180949203902403580d240c0207941000c1074030318424010070f501001608 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 631501070 1250 631499820 631499837
    0x603020f01180501121803020a17031003150e0f0303060132130b040e0604110a02060a020a0c080d06090c020303010f0b0a09051e01021b09041202070f15 67
    0x542e0a252540450b09902128180c10b002650003078016000b1003401c20700000d40324030111007500894652110440041e0803104480040c04400c41d181c2940c0801420b005145041042141012000603c002841c9004848003020f00002035844100c40d10f00c55004c0d40c40340d0412a840d15220f50045aa003804640405c40c540b10400428102000c0280d804003400c5844200b0f60f40007406800507542c040d56000000c1c804a058031980b409440280805c18410340113052940c1000255000d02c6d0001c441a0070a0080030740310b030703800650141c204c201c0c41d200507a01e100c00744080340c500c903036020060841b40e030000c1d002c0020030030396010b4001c0f69820b210821a001c080c0c0002c80e2644028410313404218940481440044801c200410300082c06040103024240d03603101240314600003c49920075141d0350048407045507014810701c40004020300ea102804001040024004000035002801030303103405202a0300d55000700115006030506c00328000b0415a581c4025610070380190441d0000380001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 631502320 1250 631501070 631501099
    0x405010e070f12020a08070e0a0c08041a04020616140616080403080a020405131e06060c0816050f070305010c09180506150f2a0a150e0d03060302 64
    0x214001c8140e4000080c9041814a40300d03981e503811030705079020303680000308000c0040d90840812403c0028041079010412929118816001711805e042c2081c0500040d5001c200002c0c40741c03144000d49011800c5200b059840d00d002241a5000724010004c042e405030a003041070054a004c0703a00c000e0904030440e0703920344e100c08001c46c55248060070701c4086104480860f000a0080c01d10f2035100d41c0500340181440d40c2c8000003241d00e10042000440b590b81c2d4101040b80d61130106561031100d000b98418842c2c0f51424900030328164036844064507414012400d01d0034000340c0c0c145e85003607507003210441d169034890715482515500c02c0d22003110590302e000641d07050540504070b800c04680340d0054050b05240f4110350803010703080042695a010414480c0004c03513002071005040c0c000101d800c3c45840d0304203805981160301c010341240ca150142400410840740e00001c20f4600c2d16400200c001e0141d403003000140c040d20481d00b42c69068001c2c2000020b0381ea906902010881340211380710310501a40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 631503570 1250 631502320 631502323
    0x5130b01020c060703050909100315060803041e084603081312090f0501080408070825120e010e0904060b0f0607052b0503010e04030311030406050405010e 68
    0x2220002805608214103403200d910700040501151802800c086191035601000100105030031600e100c0c00c10180c480600600c04103c840c2c4403c0d54255000708042428905103c3d50b030b000b2071144042003018120139a902000d0b50000d1402002c500c000c40f1048010210f1010400c942c20f039818003948401c880d440003510610030352100d515040c0d40040044505c9807411905107400038265a41c1c04888001c2d000000c680d001c0703840c1c0001155940311006401c0c00700c5a030350702040354400e0341002000303000d100c04202c1f10b201b290756176603000a10781d5843d00c1e00c2e490112901150501e601c0000070701c1a1000034000c60303036014002003240b075940804200b0700d04010350340d01d40003c410f90342040c040000200090400e40c0101402c080040c40b0440d500c1e022000242c1680c40a9401c0703c894101080003001c4003000c1c2c912000c850403c030390744038a2100c030901c0200306010506c11203203016825030129080c94041e61115900031480002c0598074a02420030342e001e17080c00e0b50204c0340c075842d080899503040320 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 631504820 1250 631503570 631503581
    0x30a140f01140a0f0902030c040312110f07030503120a0b1201060807050604120f02040f0207030e030f06060102030703080712110304030e0405010b09041a04050708180a12080403110111040513 84
    0x764028200551401e140d035145c001c4d08000c1030107922943c00c202c0132020452101200014800c5540c9000131f9030be01d80052403c00c0341070700b1606552303480f442c0f0900010b0001f2056810310079045d10503030002d9a5140911002d4440c0b84049a0090300d07904070a1400c800641102c019515100c003195041f503550b00178042c1511942c42240390854a40740000005030240d80c8c0a07150360700082000c20b10100c4141380008a0b03000b02401c03400300d04400c02c46415410701344071480200e45200041c100c1441c1c00c00000c2e40382d1044d210700230204030b84100025800b0b40906800c1703100842c002c078104102e03503900c00c400e6041d40c01564103030042a070120300044a89004e015080c181c9200e1900241070116100034000940480401410841e03001121005540c5a40c401c0741e03c940840da4030003901d03084c40d101035200011318503c01116608203c3d4880c02058860780d030328a08161034503001100e07030b8881c10122190000c042d6000c80325402d1102140c0c59450850281040d034000f100e40b40040f8a20040803000c468 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 631506070 1250 631504820 631504829
    0xe221823010c2c01030603060f02040e0a0504050c0d0611120103050f0c0a0504020c0c090a0b01081b07020d0201021f0e01061d0a050601120c080a0b06031b030a140f01140a 75
    0x340041c40700000744581d60300000c203c002c103050100d4060340b2036480c40250742110b45007030200c9034046010030402d04062003003500048948010442d9041070340740da680f2504101e11141c003500507411064104080d652047c000e403803003c071145403140c1041700507880b840c1e8284800d450714820036a00010041c0046070b5000d1440e0003c2403401c0c0c4e05d2421003848080c0d0010700081d007040c05013078064401d0391280c00700342e8860100e2420010341e600004001526102c07020b403544101c8a4030385044446103a003442224442c0c1c0d0112413a039100105440101d00e00786400600380d0b03480c07042040d0380311070000303076000300302101040e4009020164891080c80500c490321400740e65444030030b10110320350a50913440907804c0340061620001011f05224920240c90303c054140000a04020401c4014141c61141c140854401c4505ca880c509118840001c1c1d03103a220b007039510101000000c640741c48041c0c2d00059220b904003e40f0103071071602142d941d240340030034420310350f405106078840310003843e0030389601c0183c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 631507320 1250 631506070 631506107
    0x201111506040509010b0a140102060f01180b0f03030c06060f01140f1605030c0a030906050c1506061b0a0b07030203100603020f0f030405010c0e221823010c 69
    0x240d581d0020040038140141425200f55615000d44400b902c400610744081d21814080c5804d41c3e110100084c60400020102ca07001d001d610014803080e034248034108504030003d180880c04018080009440d624003650b40e50f45440700003011102c1c02008501a880351608071104100000a100151030380425140c2004100d401000071007071160424001e06140d6611801500c0c0c40141542e40c00d2441d03001c0505458a58050241c00082690104a1038080c00c142d280c1036040aa400c2e0300940e070340d06652100d000c190008000648140c0f07072041901c06a480c000003c010140c8041032503501c850b8440029190010440001a0054000d0003100c0c0100890440904003920b043c00032002500f104100d8990b460003000f0482a8000d9800503500640c01080000345034000000c004c3c241000742e03004d00f0702444090161105200812100720582d140c0e00030302060381c4200340901c80c00c0d001d94490080465268140c0368a10800707010395450760000203002005250342141e0705a59004101861613040c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 631508570 1250 631507320 631507363
    0x60f0102030c030d050a320108030415030e1002040f03050c0f060714030d0204060504090515064005010f02010b2b050d1e0309150207021903050a020111 67
    0x1390045074000750b448404803000284410400d955a1850503a4000c054032001000560700508a0104400c50040a02e24010751800c1c0c80c1080f00d82c2c40030081c070300010502d9602c2102c112412414010240c1c004010182150b40e151a802441c100580078001a1103038882c51003480b0803414550b0700b03401e541100801a50610340141e0b6680310814620b14481c5407404240142038000a0600180000d0000368a403262598200480d0f401100d46c01040c91042c0c03688044505401d03150310080301c880c6607000100240114a00000d0755050b5400c60340c40843e6404e8410030131400d16143c14001c2aa0f509aa50703900060301c001c03040b800d90724104589507202c0d00239400d101c2c02ca54914000698100e500c1603460040f841a19001c1c00c101001e05580c000c244898101003103141c042c0d0000d00524910300b420440b6070f20b607449003802a81c21040c0e0741d0340c13280d00003901401e640c0c134810388001d1804003040724000300e43c40b89846521954200e200300d0200702d01e104c800c8109a004210f0800301d4481c460340c03041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 631509820 1250 631508570 631508587
    0x6030c070f0201020708060a1a0603190203060402090607060b04181124070f11060a0e130207020603010b0702010923041d01111306111c02190b060f0102030c03 70
    0x102074072000803419845040c60000d0a9142402454807e000010002803c02d40080d1403a1100303481c80c04c610b220b03810030010850200c3d14100604a0742070740c40b00041c0c0f60b6940c0d0010030020710800444030b034804808941c003410411250804040c1754001e4034140700302254140503c00c4131160000003000840362074005191400c100348100c09102c0c0c1c814070352900d40462402c1e01d100d039103c10820313203909113000002c0080c440d6140c04200780d180155403040c80c0040e280c0f0010000205d0b02041c4e4881e41d080304801c40d20400c290152a13032903400a040542c0e07542d4601a640e0f50751700c4408200d000c00c4041c0c400203018445a4404010122140c00020090a0140401c0014070703400781c3c0401d903100c1c5544c80603500003091040103000401d020307040e40d8485504454400e1420981d01c0310f0204007000c0e44201c001d0502043c15005110001d2403441d55a210000a07402c244841903181c450500d840c4048081c084900031280c0202c10603110140d0354403606004913102e1140c00702900c6071b603008000d030a6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 631511070 1250 631509820 631509833
    0x80403060c09030807050c0a0b1801030e070807061206091802090a0f05090309010e060c0a0f171603110f1b0a0305010f02070c06020f0606100e040c09060e06030c07 72
    0x14110542c0c07402010b826200d94665100d81c00032913003a0f4807a404000710001700d040100c0c440000d00351101d040e40c2080b04095010248014005074141003540781d03881290140307800c0081e0710140c1190303410344d6101c03516000001d1042803402030826000703080c4000090000003600c00c51520001d8003042140340c8403981c00788481044041c100c819225070300d40240011050301c2c85501d0007550184091603803114005c0c001420f030400c0140840c4203c0080150000b02d031000681c9a0140d544400c00d26400c0c81e0328140b206000c1221030150340401000582d6051105900c030145070028480d40360b010074418031400d0349545400698200d8441d50100c180c40c3d14003070030001d0904010034010860f03087d0540381c1e80c40c5c90a4454106260342510303008503141e401c0040e06204c2d40c3c0640005e00c01488d40311107034208190764400c0901103d009070a905103000e02240315404080740f203032000d0007d00904040e03010003400300d022889030400260600350258100d1501004490154104200780360900d0855154035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 631512320 1250 631511070 631511081
    0x705070b07110307060f050610050f07060b0d1b0315140106180801020f120108150c090f03061008060c0a0203030c0a030e0601030c0e010605090108130230010c030908040306 76
    0x20161105100c130800148140c0202c46080b0310806011070315040603030a00c1b19664440a441003400020b1010600c80715504055443e16a04030002180c0040d07010007150126000c143d000d89030705000c1109404240c5001c804c2c40440e0300c64040c02c400000a205404201d8202010300c141a487c1d800040011340d04ca04640070400c0000c8148400d040c0c2d40700c0002e4220b170f01490fa140800040819244103505c0b044030f0745401070000c0406090860411a50144101c5004058148003140802c0021440d21160000540b0080140440d900303414a070440d0801d11240340700d0b00004e40b041000040d070300051071054500040700c5400a40c1551586611803000f07400c4854400c040503030b45c06151a0b0540200030160085000d05050004181455403072549100142c00c62410720208004442c12039074407940700c691100140060841d000200d200240c0c1060b1002079030401800c0051b502c03001e001c418120805d0b240404002000a0242400e0980a5525a2002500401041c0300400105904e40c010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 631513570 1250 631512320 631512347
    0xa0303392409051507140c150601020d050f16080304061406060a090e0915160e2b0204140a0b01030501050d050d050304060e03030103030f02010506040501030b0c070302010204080307060e060705070b07 88
    0xc1688000c400840e00e0b4560032847c00125a60f109903810040300f244c66025940144081c0b0103031080c04441007001d0200c4c8107000d000c1c118000000350381c44140e5240840192031a0340007002ca035403802e040c20180d010b007040b0314117010f181c1c0181000c02c54903d80300c4110341504403183c880740c450501d00b00511516050003080342d5110300820044c0e0295000c0f03903016038410740114190400c20700f9078003002041c0d4600107611078000d107440c2d103140b801c80340521440d500451459900038054402c62001c41c01800c805271501d2590003c91090164008a9401511005c0c03000e0b6010055a8fe0f281e00304a04000c0d45000540160441e04c074030980c01d80304000a551042c02400003041c005081d072501c5286a000340e00c00e40014900044542c0c600758203000d0250403010482e000d000c00d5040d03482c0d0900440b4050560340d9101000200807040600079010f44000700b01e00400c2d03e44400c220b0038064040c00212070155031074043d150005091f075000b00309032420a5004150300125595040d030a07190003504010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 631514820 1250 631513570 631513577
    0xc0203010b03031b100603151a040e0705010e0603010b0a050a0c0b1e0a02091f021005010906031101020d050f1e0c010608010b0a0303392409051507 65
    0x4081e505501c041008100038100f070f40c025840707028040c0c005824024441c440c091082d0a144042002c6044040c41c034070124031440c1c0015115071444000042c503c6d12488030341c0c0243c2040c0000074850400301c4e1000841c0c1c4207072103da0300c0c2c003641010004148024050014070020502003043c009100d840500b00c216032508005a16215035100c20346030444c125070300440d045500814501d00e554040075140c0140b10008103505001400780003860300c40c1801e50300780c40701d0142002401050300c02c104030320000e00c840c401000745586880c80030014001c240001e907049030451061100951001690450aa1451356854141444a008590a03074000c080012600c550b40811940c2c0c101d41000034603010801d0000020740600d010a0035013501d42c6a030407030b0310030350441c0c46c01c2021903005084481d25070105800e000400c09041c144401007031000800c030507940a00360000b420841c804490007c1c14820b0010744000d48580c0030144240c440840009015422400f03030002d006070304403400d5410025508 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 631516070 1250 631514820 631514831
    0x804110d02130203010303030b0406240504090606051801050c060103110d02060c0f0708010e070b13120f150903140702010903150218150708031003080a080105091806070c020301 78
    0x1000110303046195280b606015a0000042080582504c030303403401144c040d038081c0451454405100c803403401e099500c540280300d812001040ca4030400458001e0041c0f450108405070701c3d650b00802c0c9410440d18101144850041c190b81980141d06903401a0003000003085242c0c00d5550300c445e0241107010403900900b072000c2440c0140c0d14200034003080c00c0c1400080c10415004040b02e40b91003500c2d8072500d1329034035103054005281808510441528240074001d84c0e40c5c828000c05c0e041c003844d964022500c0405064000003005036046091140d6400f81804150b01d010b07030540c0d50111031048034000d0200705244c0d1403000c41c0080e4000f42410f540141030030f01005503240c031090414042c41204907441540010748101c0030b500c90700b00c080800c4050b00c00c401a0b030482c0002c002d0911422101400d484008170020b080100708412003006144d0207504543c848650703140141c01c0010a02605104101803070000798070350b00b04002584010344401c020320840e00c132840240d1756190f021505076050754a45 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 631517320 1250 631516070 631516073
    0x30605130504031d0604060e0f0a030507030c0803030709090c020a330522021519080606070507031412180a060f09090c111005060108010909030804110d 67
    0x440ca481114000da2401180500d400c3c90010030803041100780c00800c0c1c200300c40003141c80c1c990200b61002e80b00d0a00304102c014404a00280d00b03085030b1b181d0b0b903600610500b0044100b010105848085074820613030004081d8503464007540f2400b048985800240343c103082000540c00981010442c2d400340e006a42d207500050f190074201000030942c5a0103001e1120319880785040c091980d06000c0d0040000b003000f030801c140b00d40fa02c40703100702211015141f444100700655803916810000000d1912600f40d03960403682c5807041e000c4081103800c0208240a00107861820208200c400b500e6111001e41185030550f0b983c82b500c140794107030710f0586201d9004074040040c00744008005070b143d1180410382c0d01d0004007c11000200e650401820000c2e00c030700032014190003003001c9042d1031605002141c02c2c00d244500b00c50125003000c0d803848500c40c000116180c42d01c603502c564051070084e0fa44414580c0c9812424080c1e500c0420005c6c0001c0140000601203043c10b6281a040c003c010700000503d070700c0307 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 631518570 1250 631517320 631517329
    0xe06010f081b12101a090d30020c010e0405010311100509060406200d08130510051e0f01061d0307030204060f1d040f020f04150f030320030a0c03030605 67
    0xc8604d0040c9115070030051000a4035131001211881d480304041d0324000130400854400700c5020350017080c402864804001341e0034611a003994050080003003610200f41c06400079510f8680304002400716840900048a03424113000302030603a40c00000c011004030340d41c000d1104014016400504102060020152503616200100014100da586003800409600340743c80c0e08284000080301e20307074081520007500070b400040c103580c0300c0d040d01400d87c02000141400f03802d1905440c48c0d9107203246801c04000c0c0c50030503460302207420b003c000f040b42c8560f0359059546842d9807083c01500042040c2900021b8540c608940c50701c0c1891014060b94542c550700e60204064a03416008200c8001c1c03070a45c1801445810700940c3c42c00c100b00c1e421030105003015110382080c0844014007a009250f03200800642e511503412000c10b03070704036000c041d0300b0030b03a102d0704a04860204e00003140003c241240c00e410720000c3d05070031440110040041c42c5801303132943c070036640d1a524900403418180c40d0303500014250744c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 631519820 1250 631518570 631518607
    0x201110c0910032001090510090b070312050708071209050717010204080d0207050a050402090d0b09031308010b0a05040b03100c08161e03020f0c06010b040e06010f081b 74
    0x1040500e204110341186131083c40c26605100f040001c4480c401903814680e4848070a0080b00d100341c0c1c69010314170305020210b07520842034100d078400141c0014510101507000000b0215807403040c40812554480c1a801c075107403981510700000161200c01d6041c0d88040682c89010460700c20804c03100380710390728020300b080c0d09010700d8400296527021a042002680c05d10844101c50705601c040c040780b508200016081d19028000c03240120303800b0a1070500d58460202c0d00501982109406040b403a081c424280e4a07842088a03410800c0030315000110f040050003800150311303004100020441c01e000c02e1000401d056102c90341e051003449c1203042c2c0042a0b00c5a181c511500c1e0381d0702402ea18150310714809411901540d042000300702c0440a10700a10029007000c1d1014138603015a94241911600c10b8502900c0c1c2401d05a0080c0000080c403407814000410803141074540340001642c49800540d414030135099070360082524400010100c45841d41014012070340e070300e4413500348203c100e0044a03004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 631521070 1250 631519820 631519831
    0x40203100e01091e1101140406081801090528020d0f050a1b0f0b0a021b031606030501052b0b090a0c140f0a08030d0e030f0f040905060d0f0201110c09 66
    0x103111010703820178403c0c82203c580c240307102070030000c2c441850040308401030f00c81d41c0310328020010310502080e0070070101c0d400403c190381140b009010459031424443d85501c000c4082495101c001d0514101c2004200c8070719500a030001c0c624401d041c03440c0c88102a01000d51821a4180140300c0c0541c00541000d060629607100c0140070155281043c18243c00b00b080c1c0d030401c0b40400d600b8050184050b1f80002c1c4480000103000c10030f2501080b00300464a4200903c120040b00030180f10086800c641c1030f4031040c121401140c003503101000c0600d00c41003c0d4407070f00000045400420360035000c40d0700211440d404c820204100e034807584103038a8200188107690404090740c0d4510703039503541605e00004606c146034000ca070340e042810b15202925035240b04840e0a08921500c4084036100d4100a0042c2c0e2504942c01c0d102aa03501030641c1c8048555003d401b80c00361142c078001c0414100e0412100f0a6416079200c12842c1c208049500150761900100411140607caa050380c6120340e11540642d50041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 631522320 1250 631521070 631521113
    0xb0d031101022b0b091504020d06030510020a020709090206070f050a02040203190b121b061209030306031603150f0b0a030506091905061b040e010f1409040203100e0109 74
    0x2042c26800e000c0c296420b410743c4a05c0342c1c98110901080f4034450030320344804203040340d005a0703401c4401b0b03891003d460b180d030010305a80182d042101c00084c254000b071080c50340f00d83c00e44440984441850b0704a450342c0c24080d4101c4011301c1184002564032003400c02d480e000f501201c07002411940007805a92007101c60850081c5109031559038943c5a01404148400032207407041200e245d62241940c9242c11501c104a2644e0603001206507200e040c101d850201100300c510840b46030101003981d4960003540c103940244684202d51803054219082c800a0301c1e84a40103807032001c250040000900100c0700009120b03551000381d800c081d502c0722000d10046208001a1403540390410342d060902d48100c1c0b034071008490103158580060404164150b20100c080c40064a203440081c080455000e540c000c0b12504051100125500381c49a801c0002c0707076101020004124440ea0602c5114901547c0c000d405920805080440c003009800c043c100400710310001400d038503980c86280c42c10340802c2500044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 631523570 1250 631522320 631522387
    0x3070203091804030e04021c0f0507020705060a120203150409030c020a05061608071109180c0a030b060405060613060306030b0c040308121317090a090b0d03110102 72
    0x9030806460a120040e42e61121014528064402038007004200820511075a40002c0849400091080460221003501010003581c0c02140b80200200420346441d030261013041d4001500349840011200f040c8038a42d202540e40316075072105000b075000642650080b070150001e00c10291218031039940001d0080da01c1020289590041c003142c071700d8640141e40036140801c501c1a440f1040c044104000758041482a5a5070050411b0b0006100c0c0024041d407010b60601881241500c880d000d01070f6905900030780d41c4101005003000303c9601c0e01e1200174010342c4e150000440c00d2416a00040d8000030207055145009510300800410f107c05400003008a40d48500a1060007611036443e44d00200f0100494585408e5442c0e40301c00340610b01ea001848441e001c001403503107a00c000041d40341c0d079100a400d00a0701c0c01e51034083e8142c000c030740c0c01030041a070740b0000a07580c2802e009103c0c076980d000e4009400740c01c03551812500301040c1564902503640070030510607104041384141c460541c10b402d05510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 631524820 1250 631523570 631523587
    0xc010908160b0606040f03030c0602040306020f041406090108011e0801020a11070b090d0206070c08071403010b0109210f150606230f09030f1516020133080303070203 73
    0xb441c00b006440b0600a0000f48410f1002110f0340280c0c00980341c0600b003030814104289403540c013902c940e80004200340c1c00480c40c80c6559034204050000c2e500101c0030005408042001d000e0740d40260000d40380051079010040008504c1520030b00180c00030060148002038a400c00035083e40c4c460070307220300080d04004250050303036414807034180501034071407800e4903040194000860112015802a2040c2800138068041003e1240306000510051040d900c290356138101d100c0444801180d5140030394241812282c141d8891040c820540c0c3c4c0f0b070581c3c1c0d0001692403003048801c600c80c0360219940110320084001249010401d03009240004d0008200e640c03c00030011700c28000d0304030300800b440390210300040300c07208070342914020207000c0c0c00161102c40c9800020701c5e01039420741d07082850007001d40303591600d07541d00c508500c510b4501045502410803482e01b20f08842e140c0362000340100380781100211001d180c80307015100102d142c03580d01c4803c2e16000545c0c15644161180800750340000740049 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 631526070 1250 631524820 631524833
    0xe011716031104030c0e040c05040e1507020c13270302030909060d2108090f060c0f070218010801110901052a120d0608210c01090816 59
    0x28408022098100854188815108180e0306000140c806054071008003030304103002001030f18015034001610f2803001c0c0c0d40d500003144540c0c05440c242c40b20181c001010030f840c14640607560b040c4518030010500785017003490000000c4005010714045000f000300c03801c400d5842c001c10034611000e0035000594032040340070464041103400e10a810391180104c100b00882e40200c1640d5200c80e042c0e0b0070114550b2030320002400c81045800051a89403056119680a403184620800404c00350f2140b050799221140c40a684d0200c1a140030100c2d480710740015889a12200548501c0d00071031002c0d07041c00410f9000421601940b0700c60184461104010842640240100425010b102107920300d402440e00000700300d4800c50311248110244080708044a200c0c40f0881e00a4041c40c030141d0b842c1c040080100407556020160440b4040d04081c00403902400200e101c0321250b00c4200368900d42070030011221004d8000007410800c41d540e45180002042410b0000e01c6203040443c801102c0a50500d80103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 631527320 1250 631526070 631526087
    0x50f0414041815110909040308060405100510030b060706050103030c03020c190e0907180614030f0325020d0803160801080c060706150f0f06051602040b0102010e06070e01 75
    0xc0d02c2081003096a03000b00e80c0c0441203448082000c4030104001136003000b031803994458404001c1d00070307500000b048149540110644e015800c2103405108640b200d001e40c01d074182d01d600030654441000c030b00740075905011758030040c00d81c40064601400d000f000d8682e942107500c01da0054000c9000c40503140101641402003030228031017283e241c9400e400b80e002c81030801e00c10380980001d11211034003145000e1000c00c281c400410715020f600a0100302c0644103006403038144103400006444640015040c41c001c00c0145810300c40400030350a1207080d01400b400512022480c5caa150302c10816840942c4500e088511103a001e540b1b000d54905061942c00c50900110703520108111b03408006103d0f01c00d001c542c0d02c04a41e0100c0707000c0d440e8011030424800034055003950004005000c0c000240221802000c2400c07200b10722043d0005c0c95984806a94074842c01340140540a1808950401490300754001444054180300001d01403616205451401e0010303249030002c41e1602d00d243c01207680c0242c60 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 631528570 1250 631527320 631527341
    0x20c100e031c05040807060e0102090a0807061206080c1009090f090b161e0e09090d26160909050a0905010b010f12090303240f12080712050f041404 65
    0x3c0019141075140d80009015401d00103021580720040200e0b04c2d20250190382580400400403524243e84441c2a5640c0020b8412a4003003409100c04951030207a9105600841d20800d0242040b032800408200d1142c8009803242e05000c40b1075400b0415281c0f501c98405040c8090380c0c006206444c0e410520911035004042c0a07070f01900882a400700742d4080600704221a9030812401c81c00300d990401c0e6000c4410f011007542040313004040104e03040c80060451800100e03501d560314441c0e082c00410039546c18001210514520030004550900640080b041c0b070000d5614044c910313144c68248150507620145c0d00c04d44941d49614002e003e200082c411220080800d0070060310120710300e103024010104410b50b084615995881030424503021b038010304090782052840005c224440302d41e071603000b9400e002d0720300008010b0f40042160650000c030b0700e98140c0c111a130103081803440c1e41c54042202051900c0c804200091100000710842000640040d101501c1030701c20140080c410302045420000b10b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 631529820 1250 631528570 631528627
    0xa0b040804322b080909070201050402010c080d09200f0a060207141521010609030b010e090715020102070203012910210c02010b0a1503020c100e03 65
    0x4180d200b58907280a560040d8409407410f5410a004041400c450000000081007034400c800348202080700e104014441440221500c20250300d40c01401c03401c0314012600240428519000b4001287c42100640b10038850a0400b0482c0602c0e41d40b80c008100e040c118120b040102d240c44403840c0d152000210071588419101656a42c0c41c0140003541c540d01407080810103212a8490b910503221100420344000002d00c0e0b02c1d90311141c242400344811208590300c0120b00e40b5a0000c5600751240c2210011240c2040000a49034203005142001c088042c04c1d01c0114030540d000020352039462203641341c07099000e03000142c4883d440e00600d420b442c1003034185c000c00714080c080103640c02c11164140103001001d80d068404034043d601c0587d0403210f45882004904460b0f9030b00e0b42c4500c0942c2000c400425180c2c0244641905041404000d04442c0160b10001c0c013004405c500e4a072003a4080c02081e40e4403c22506907028215968044580c01e81080080b60000a0b4290301007000e41d00201d8007020092 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 631531070 1250 631529820 631529879
    0x6010e09040b0c0d0605030601030803061c0206090105210705040801150f060e1c081b060402131a0a030501050708010515040905190e06042f040e0a0b040804 69
    0x180c2c1e030310050381e00410709005043c0c049031110000c1c00a40c0300102400000d8200d0760296101d0500b61015001190410300c111f040241c2250000c40444810109550140c81281041d0454005440ca90070a0100307000303143c490b41802c2f50483c030700102c041c000d06c181d413a07440c1d50304c0c205000b47d400c0d42d0f4a502d007500a545002d404000130f0321040c40745e00c2218504c0c504545030240c054001084214141c64071100b90f8030307001c03001c000e101c80e60009280b0403052504c10003040c01d022504030703100d000456001e580800c0782d00700091440c1e86500601000644441451542e5680700c00203808039180e83c01c2905e02d60b40d20310800821070303081410741c1e0142c02c4c2140c1411b9004c03e10021407076240b050b40206a501c030b4581c5c001c506a111001400e084501940d4410f200324102e282c181969083c1c12282958540302d1445028021399100c007525120a000810b50034011400b8014403003d0160400e2500551040c010600080b807031044e41c041c091803140d03003010358413403801400358182001680101c181042e00c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 631532320 1250 631531070 631531073
    0xf0b030d020c0d0501020c070b030108190210080402190801090605010e04020a060c03020309101211030601120b180f01030308010803030c03160306050a0803070620042102031506010e0904 82
    0x1504925500040310341c60b569024034031300300f8068011106100524420b102c000304100881101a42c180d5680704215152002d14107030302064480100c0010303410048050607000707014802d4941c80c0c0c0c010b001800c04901c001c0714220490000007142d0001080342d5445a02d00200049800b403c0c0c0100300380051120642400d400160703003007589104450030f00141c0c41d4480b04060080c0300b0b588001c0001003641410540044015016544d01040884d08501c4d107645a490b402d45941a02c0c0a514181d5801c020800000350000007407511404803a03210031150700320a043d07040c800110b4400d405801804409516514015005001c1030f04820341070340081c810400c140c000002641e07400707002441d0b0740801c0d80c1900810b0f801000603130040f42d0008280b00010130401e0f0000020910305109078020800328020071109003078441060a030400c0d100d001c000400c45520031854800d2024600c1c000b282e003256507680068501102d00c0345903600640d45a08104e919070700405c0600c8047c0040d11184003070300c3c0070b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 631533570 1250 631532320 631532323
    0x270509010209180901060302100908010f1505060d020c0a1a0907060206072706020102180a121217100510030c080103022103120a0b010f0c061e0f0f0b030d02 69
    0x11101404560f14510001c0c0f9288000d400c48001945c0180c60407031003e0b92280c0c01040c001e024055000290b082881d803202074190f40c0705800e05082d42410140c3c00f141000100b0425034005080b109030103800340040080643d043c0006c0340114854482c1d001080501549915810002020030120307801c00841009840c0c2c005c901d095200d141c500d007440500070171f01d04003004805040280e0207494210800030a50310340560080c04540e02c01d4061119890340c1c0020851350100e5401400fa003041d402010360001082d11a162082680c54100181140e41003603442c01f19141c229500544115024401c20042c102400c0021400081f49001d101c0c81100b298080e107441010b201c024000e030341030b82c030800740d81240624107080c000c07626040e00d903030308980900310406110036584015101e240400980f980d40c0107401241400d68907844a65181c1480e0315808c005149500515243c2e486150301542e41c9841c91062181c04401c241c0300241801050900804940c211000e0900907131280700c0210b0011340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 631534820 1250 631533570 631533589
    0x90a05070b04080a0b060409080d090b15060405040c0329010806101b031b290105030d050a2610210b0a0209100f0f02060c0f090109270509010209 64
    0x4105c1503183c11910351030b011400030b200000700034200c486e012038440d4050381c0315004140c1107406180c2e1031103280c5409604458641000d000c1550192040004002500f81030b040310142c04054100061a51205141c65103040090b01c140c0d141c80b501d03070860700019a00710310241d41114041e100360421450741940503000421492140d01911910a01d04c41014030481c0080c000e07105c0c0840407104c00b01940303412000381e030101d0540e5650b6184c0505100c0d807102c80c2007089040b10310080c0241001890200c1c185c80580c4164090000c00125115040c511003000762070070005030039549280ca003460140102440e0b4110b5400000e00300c03010b40300481c4080121304105500c56045403986d00c40392130311400385000340300e00000d040c0c2012890382c842e4805074002c44001412001515160b0848840300c1c0200c2e2203960460b400003801200f40300703064517074203000060507050304181040340d68140c590381d202d80d030100e420461030bc0502d101e10013542100007500900383c0048259000f0360600b441000010034104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 631536070 1250 631534820 631534823
    0x6050105041e210c082806060e040b0106110a0302030a120b04140417090918151f0f21030c0b04060209090c070f02060906070b090a05070b04080a 64
    0x1500d00340c400d10403040c1c2c42030070300c01411083e600d41d0740d07038110141d40a00340c0048201542c1c80c01054a0028039803d000c85d0700c0300040808a1000004444000112001c403a21103042e50020303034601c00070401500c042074480c003036030040070740b480d040d80352240c010071070481207941010940003540d50600080d0000107a0b88000390328242170b12483c420400c01001008004001e903841410304507017030040b44214080070302450103412200140700102060703c1c61440740782003141d0000c4207107001481428031400c80c8010207840703178144c400c50454030b1074404054030700f605d50505114440700c182c60400041d01030400104508074440800c1e07850460030a02c8084649642600d03c0e64044040d01018801d078a02c01c00264011280c191500f0107003021002500404074003030040c242007012a8880d03044400381c0710566800520104441c010741d00740030094000200454005505200700f10000301a0382e0918440d6035403030018040c1c110300d81420762802c1c1c42075120b0009281c041009002c5500003049402009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 631537320 1250 631536070 631536089
    0x1c0b010c1110020f1204091b0804020f0a0905070f180e0a020306030a080a030501030b0117100c050c0106060e0f0a0320150d05190c0e0d05150c1c0605010504 69
    0x2182d407803000b83c1c1030403404521501540102e21601d0400001ca00c0544161058140c040103588100c8010003a00350001c120070b40411001e400080042c07400101c02c0b107151001400d520302d55955007803914266642a14040040342c0000c0c120907d03190321003500203803442c00e545084410352030030180541100300a007104455580000020313001d61800c0251442c180c0d800450b483c0d030b946258100400502c4203010031940c10b079030398000090529113807520904285604001c2e00400d01190040402440390294010a02505002141c2400e200b807003884018a215100c030742d0004040400c1000d00004000303240e00c07442c5901c44c20b00200f42030600344c808104050203500d031040c807030000250b92480400340105504500251043c504401c640196010b141d81d0f0b1140d070a00c9803140320003000d0303c407105003040000d402c0740150700c0703503280c03041e400c01c400343c01101941c000c501d84100031040c80b10100d07407118400f20300040540e00030240d2403c0148200c0c00600800005040000003807451040d44103c1030303030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 631538570 1250 631537320 631537339
    0x2090f012109170a120e061021020616020306090f0d080705120117010507020f0d050906280810120809060c100b0a09050402130e0708031c0b010c11 65
    0x3001103450349043c8504001c0c6a1580320000d5540003855441c070340d45001c070344c00d0803c03820228005000030440c1c003400304041d0030400d0504045500c0c1c2071132101220220798880d005102070141e04c4803c0186500031440755140118165401407624014010384401c540e984800d4150421910200300440081580d2038a0758941e00c6941e0304039480d0150040302981e4001610000640b0b010402c10808280c00f004001c5c0266910484141c2c1c94030450482800a600981d10404669229200a2259060041c034250800d081c42e424050881001e120003035440f10040f599144441d00140025030107000a0000784401c5c0c01c0044041a5003001b6000500c0d01e1400304400034580d83d0f5005444407441400d00f120300050101c200c050281c4543c00002d03000e03801440002c1200700305070080c140314a80280581900c010b03459400c40c000d0460f04201c000901644c3e40c085403080301400100117110b002a15404181090780e00c3d103044031440c00185044c0316089540b0800114200c03562019560101d458009 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 631539820 1250 631538570 631538573
    0xf0414010915030c030b010503041709060f0c060105190b0a030207030c020303180a05101b0804030f111504050f0d020406090e070f09060f090b180a02090f012109 71
    0x107100031542c018541004400001e45082681640070110315061070ba8140301a89107100155014402074a000c2e200b2250385d03050f0801c400300e101c0203041c0200041c08040c41c106100c5a045407039000000122519001000100094600803481c6400d81001c500200003003071500300910041d210380c14819003070503008502801854084c02284c1d03043e81c0c0107001d6030f41c1c44000e24502d10201200d20714003440784038419000f02d1541068041c5041c1400141c80d82509088401c2604030075103981c030001c81d04050108000f00000302a40314906425200b003421480d15001101000041001d020202c24010380521041041d6548c000d0f1440b50300c43e00b5148102800084c0c0003060150125070004502c01c0e05107403c4406441002074264104c0e001840c2910580d612428102c068400601c5070184221070041d0900c08808151301c6003285e00001004031080754242014219040400c031070350280c0a90114800c803503400d2114081c5064442480e00728003d03a40c5451206d0412000002c00010743d9451343d0060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 631541070 1250 631539820 631539827
    0xb190f05040b0c06070207090c0207050d02030f0d020304090b010c080f031e07170604020a090506030a0e100b0112140c0904060504050a0506190f030b04030519020d03060b0f041401 79
    0x700501907034070384280e0722148440807543c1c0d14400d03540c85006101e0508000f0394204140f25103a0b41d10300030f42c043c01020785460100401c3d960f20401c240d13414080c41c5c120042c0d2007010030560140e11942c0d005980c5a628114010048440c5a14014180315880340403000141c501c0003100c00c1c101c00d105910352a0789856182044008840d40403041c804012400d01c104039421402407034440c0d5610004842ea5524030041c84140e000341c02400000c43c01c0d294090110f0b02d0040003945e800360300d0480010700041042207080c941205c0311240b482a650f10b20700f20340d503568045003941e542d01e0000000c1c0504c1e10080e074045040316000782012240400030806203111360741d5411880051000810038080b60034182695002480d051300c603540f10352076200c61807032010000c80d40803080702d20701510400c6041c03542d10760042880d4014811002c11608110720b500d001c4407009060b02d0740c80e103a40241034009280310b024084504a0700040c03081d2005004503111024030204176819100140c5210f000c80700f0703a50068 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 631542320 1250 631541070 631541077
    0x10f08090c0d0803101e0302010509131505090708070f0e0f09100501030b1c300e04061e0302060c0115030b040515090a020405061908030c06010b190f05 67
    0x29031091151100000b804110383c013030b41c00780310604000d030009940d40c04401c2c41c21801c0041d5215051140c0000c0000d907004001030300455601800c030040700c48900b050281111052940000a0040c05005000e1807d00304145a070001c0681880300715403c00c40303c0075120328541d4031800204200316038900c000c0c5d180c001d10f1040d0148094500c9405003010580b0a02c480118080c544c00079143c01c100c0d04852034203190441318400701009040240039180c640034941c1c0d00d05420b48044140171042501e0f14000307a84820f012505d10303034494443c102405c003084282d642c41e910548500a00c241c02040368a541c000050840750b049881658410070141c0705405002220410810702400f02d900105000022a410b4891840b51090320340380c1640d641000d40d40e21090310410110f9110603040c00042c2410707484540c1020340103018800040344004820821041c0c0c0e0010720350b541010487d001480800c2081901410f64240d0450800040019258002000420314400c000d44480300c0307103440d40100304a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 631543570 1250 631542320 631542343
    0xf09031205040c051e040e030f07030c060603021320130b0306040e120d06050d031b111c03091205120d0e12070b0f01180e1c09030c0b09010f0809 64
    0x74202001c070140f5a172803400e0040841c0d03005500f041842c2c07007180f00120880b49440070b02041507080c00b10302d4901701c4148114807411035640780c1d50f607408009a079500c0ca074400b400d08001d1010544140c2d00050003010301081c0782c0e00040f61000c0c03200c90400b0031034070360302400d5030b10700255580c80c1d5441100240c040c002401c08401c540c001c643c02040d900302c2048c0100020603c012041c4160b940e501c1c2881442c44402a0140008281c1d51006041d2130720305a40399801030045643d5400030312810001a021010342290459188115016030105504203070300c480100742203e8500440340b425110700b0f4441034040040401840002202c44896041d540103802801850702201c1e0048649501012540d202c95020399009031650002405a049041c5d010b040e5400c18803043c01074442e2401c4040906080b80810007a40034100c440340c0d00701c8101060999501c815550007a0142c55800c046075004e52980211669181c10443c140c0903036000341083c040c002480c68203840300d9951610480c18414030071076 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 631544820 1250 631543570 631543579
    0x10815120c0d030c03180608011205030d110a030b09010b0d050711010905060a0509010209010c0809030c1302030105040b01020d1425051506030c0f06070c05220f09031205040c05 78
    0x2c03040c181584444c03c546400d00c41d4551100c00c00780e80b5a1840c0a0300d852107402e0000d003482d40140f2200c50301f403a0740040244200120303420149804040800d40d004a040e0242602d004159401690b82c14007904d51000e2054402001079410085a13007018814010b242d43d50703039118000300d10198803501e890402c00005800800c000800c602e442c5440790703804e642054100b800d01000c54060300c01031085800c0c4013416110021446d5850399200c0b000d4000d42a540c0d89802070b441c0b1090181c469850954407050b85142c0143d81c0c2d8100740c1084101c1760300c200c0d05811540003000c80d04a4580005008441076100c180642c0c81e42c0c44036007041e600382d040b100243c1c07610001c04450302c01c000e00002c104d06105c044404a94495889070f0a055582006144280e03004074500220345260410340010140180622070004009448038003040580c1500342840d80030215124007010382c1500d521803c1d07031103603018000384681c4803142c800800c008900c08101101d59a188013280401c0354071188040240405403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 631546070 1250 631544820 631544839
    0x10e1002030307021e0d0f03020d0f050405010e01020c190204060b041205010e0c0a0b0c030c0601060c1104090215031e270f0d050c031303061a010815120c 68
    0x620094890300b0640d40314003d07104151090442e82608464480a00001801020241101c400032684011038044200515600f0081540910814017072918031220a9070041a541090303d441383c21142e01c1e074030300f0880d6481441618840311b07000c03039200520460218011002c4029000190081c1a243e1015a400c0302c001400a107000e01c80ba10025440c3c01040200000f4650301c00c01622800062400d540c0901c0d100001e100e0b10f040440a01a240c4801d000c4a062022080582e458a102030300314002007412080603500b00100c500f405001503a00340c50034004032032030f5030124603545c885505086c02140c010001951a00c41c2103580d500c072003c0032450030b180f82480c0201c280351074200039125000c11400d250b01d1654140000d032130341040c001c0c44020300c2046c2007968119440c0d00014a07598060200300107d03d21135100816200c003840c00f4480009a4502255070743c101e0850240382241808080003c00c414039480d8208085205029150b40c94007001c505049800d059030000c3c01a4880c0f10f42 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 631547320 1250 631546070 631546099
    0xa0e01020304150f110f0a0c0606080c09010605120402060a18060e0a0e0402061218060103080a1205040c090f02070206040f0e090f061f0b0705250f0306020702010e 72
    0x410310821404039403000c01c0200d1305202d5032415102600d20803c00384038200294034100243c10020007041e00c4518000807140040e949400544e602d50703000c44402da0003940886000e240490b40ca81c010245420924070780282c42e120745441c0c0740300600188c8607980c042a850b0095001e0b450340e40e8540c01f032545030000c05850340c1015105450a0846501403440c9100115985030124071a501403500100b80c2e80c1040a00005420785c003000602c2c2d07000320030441c056851050400c000140c00b1390b200d142c0e030320344032034152000921404000509088042c10041480003040100c142d00d000c0d1a1064804940546454901e101a00c01d40c3d400031340102001600190407202400c8403400d940000d01d040d4100e4440c1c0d1310171982c90f03c1d58090071034581c0008010a0b1b0007541905d145140003440d801d50488555a114400304a4115210948090b00954000c1c206c5030840034864012b02180c0c00500c40e0f450800d8043c0d0080130850100a044660018429081d6801150704d845d4915004000c030644003080c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 631548570 1250 631547320 631547333
    0x20f1503070f0f110c090414030703020c1c030f080a061206020702090901090308010e1005120a02012a060b061605030c12070f080d11030907032102150a0e01020304 72
    0xe0b50000502031081e02c0400501c10003080010019140060100002010130064030710b0016104035041c00d028103100342c0081d4140b010f003d195009401400300d4042e104140100e0306034020004031b050740000350740400203800c00e1400c0c002d00d9651030502c285035030320403990f00240785a4001c1001d051110508001304103c6400a00c0200c3c800d03501904541c076143d0145c0d00362000814020013152000b00180024943d0003055603001200c1c91824015950f90004500c08030820092400582c010021203c25560009140d09150004a054803020f00400c080030405240d6407900030202a114408580745d59070362025111003400001340840c4109551a00c2a561ba11005400c03009001d29050441c0341796115098501c01038002840d040f007540300e41d0f528521644241894041103036140600004d1441e003801640c414056207004261903821420300c402e44440c019148418080908856240b496002c10220340411496428904a40381d001600002e4411048014036545c408410802445034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 631549820 1250 631548570 631548587
    0x3070303110316050705030708040b041d090d1107051c030f030209031506041812020c2e05040806250302090a05010f0905191505030103050a020f150307 67
    0x1003034500700100054407240c0141400110f41d104002c29148140c1c84401303002c1da004203112071050302500d04e01440c0c2e9540d8502c58000d03820030a000d020100742030062800020317004c1c030303103014001c1480c40a250055400c0c3c5c1e92801d540000d410080c052000100402042000001920000703080303089030300e80340b01e510503400004007080e0001102078030b429801038040c0c030890320f202c000a0082c2c44196005590a00903d80240c039143d00310307a0301c0000d0500400080c40c01843c0a10469010512030803903040240360400700000540f20301c801d0421002582011204000420344c50030860b401c0d46001e03101610140034540c4501c0305130242104010b031591000f03c0800203540080a00f00c19172070300b00c100310128007401c01c81035042221080b040c0059801044840000c10103803418070081074403a03021840f00f04232440100d181001c154420300200103000c619000044207483c0c113509540c55915040e680d82a00c00c0c0c0a80910b20700030100b400c0e622005503141e580711981c08455070781c3c2003040e0001c01800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 631551070 1250 631549820 631549823
    0x801020a02071e030b0c0c030703211a040f020408030d0c0201060b09060a210f090b060d020a0e13120c021206011401050309160b0a030b040c0c060506210307 69
    0x10003401240c403021200203904041000030260204500f140c5d100110250040c050030380c07101041c014408841010001802030601c2a5a0308203141c0441c0800d00491b455403440030151400d2040324410b00b45401d41c1c2c0c0d02d604d5012200890882c03e110380d00d00081c46190003010241c0000071340c0b050441d40940041825003c564000c00015a86204004042c0645030b60b00354009000c1042c1042d680c4122812110315601803070040d800b00104190f07008440c4180d0001c0381c02510b500140342440003440c015540400180ca003d82000c00e185e000400500c0f050194245002030380020a40000900062498503036100304101200059082c025000e2107120030101c1c400d804800fa0310201d2000458024100d41c0084132041e40701c1e19080040d203d9410042c14021280b00da00d6040d0741d5215081c1e800001040703a203900d0342c0d03111001080201511249520f2a00542c1403180d40d119041d480380701c184074103400441c00523040d00e9160001d02c44401445280c0303029145224180c1c03e07084040f00501c60b09 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 631552320 1250 631551070 631551073
    0x60305160e010f140103020a0e061605121303080a0e0a030605010509160e0d030e1908060702030f0405090421030608010c0e030d1b080f0702010f020f06060f190801020a02 75
    0xd81c3e80d000701c0f01e02c0b500e06001e440406100d0f1103941c011940a42c01500da0b03166181051225013048501080840c1c01c07162890036002c404e40100418890180b02960780c011003c0d112928011b1003140c0010003079601d200081c86102f000403240007652280c1c58100c110355004000611050fa2418040c010b08030a004003031040c3c50702000b0458030250300690404080f11611840720001d0002c0401000b0010100150288046103c5007131a959a050072040c90b4004124801d81840c2455142482d202c00289964255402045582a003080c0b0400b51001c0f0352003190081d2180e6164584207e81c007004002059215504910000030550160001419120030a000b00070500790680b0803030340c1600031412580c141e00700145d4007154511500c4140d0018040d0200102040084d40c1c44240a521003441c0351078030407021500c00c04669001c01031410351041c0744014403089445140315500d0700c601424980c4200908050f044040e160300b02074070310711520162500009030717039405800c5c040e40c01910f00c074006 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 631553570 1250 631552320 631552349
    0xb01050102061509070c0b0a090b280c090305010c0309031b0c230603150a060306080607030506120a081c1103010902130e070210060b030712090606030516 68
    0x9501c00901544154007007030780c039001031141030280220b0040240407441049601a07031440402e0069100d1230141c21581c03000102c40c0c0306070500301c4c1445009448080000c4145007038140d10703034001c000c40803190410680061061052041034490a101e0791006001d9400c00142d028442e42681c040000140a07494007100d400c41040300c00300c201c602420041c40e401002e0350600490400410710785041c4521040c00786440546800980b103600100d40c040740301410625900000c2c140a01c0880c020f09031401c0c00c3c06850b081c001590b88850f0010412400c04da1340d41e00140c0d15030740342031000e1900c100800954100c0360752414041c2e21039021600d047d42e60300300c14040003140c1d0001d21500080888007aa080d042d44d00703180f4654042c1d40b0003c3d0000050040c003002184925204034440d0199126070005d016542c290103c4105407056944441c0d902d48044c4200150160007000d400d09140c201200003c00071004c1c41d14400400ba190030282c0240300f60701107644880d003400110344c20303900b214148520 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 631554820 1250 631553570 631553579
    0x4091502120c041a22080a0c080a03080a0c0c02090a060f050f0604030b2a03160201090c060f030f020c0604021905060d0f0b0d060209010905031209010c03020f0f0a0b01 74
    0x156101d54402c0c4110300341c004659078510010769000e01420140c14043c5c85680c40c150031039802c202c4d980d800405258220803141410071403503058100060959601030102005141c43c040c103818001005521816121448210450f1280781d80c4512107030b0050104219040903005140100124000c0001c2c2021411000c1401d217400d0003e0900000001e04030380c645801c41d95980420f402c003030881c2021100c0c00d0094a481d240000590b0700c4104410072164030380c40c01a80300041610008902d1041d6454183c6071340100704215a41016610142405205240d140c50300318001c0480700b807212086131001c2000c440710080450f259004074002c59980b06a0524072007107007074516181c0329040c0c0c00101004003240030212600076020701200c5140029200719100b01107480844001d4041341d0a0f64006078a0000c3d45c4c1000500300940000d03401840200c1380206100c1e0759128242e8494180b04840e8002d0040610030401c1c0210071690b40142c03120003441c2c0c00c0c4d595079070300e0340b01c01103516181b42d200200c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 631556070 1250 631554820 631554841
    0x11410140612040318030807062c07151205010e070807051305010c1416050a080703150e01200406140c0c0f120d2703120e0409150212 59
    0x14400b200312102034042e51140e5030700f5114149003240324104503041d03003000004580040003400b506400b5a40220355000c90003c0f40390500300307a1403d003050000e0301703600c60744480e000140c20099a4400344a1008403030b001c04155000c1c18034040200d070b40c0f4101000840d00e0071100501c1401603480e40c0b5814003540790031006944a00030035500f000306001c02c0e80e0030030540d03206400070b03884c442c00323040201020803400c0542401c0c0340c02a02d240507490803d04040180e03041480d41000103100900c098010326056658000c1080886c207807140020b0b89401c040203411400b03502030001c0c01c20300c401a80800a92900c604800d0704140709620220300300f60b1143c00030311b0281003182c0700704401c40d020380101059070701000550240349003e00e070812480e0381a0340030041c0811020380ea058483c0c40740780660100009880d950560b4406014484000910400000751038174401101c800302400c1c540b810131500f0022074000c0a20890190142143c1030170400620764075802401080d2103040c1c1c04a0561711100d1381c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 631557320 1250 631556070 631556077
    0xf0c0c0206030a150512030c16081b13022802010501050d1b09020d022d0a1128030e030601210311010c02070509070801050d0803090114101406 63
    0x394100358100000740f1500c40301e501080c0400300030002c1020f9282c8400205003d94210202c0080c00e80c0009222140e48500300070081a00d0b401404200781c190400c1210b82e2202e043c001d00c42c144601074800e40c0080e40e80c401c0c07228280300c002d000031901c503040c41e031624640c00440034203109950a1011443e1007644180546416107801130580365685019503900c40b111740b01407039015008000b000c40495504441e00042c603404040c4100545c0b00c0e000c1c40c0c0d2126014100b0410390801e881151495411001683e083c0d85000c1d0301c074280405500403003501e0310f007000018040f54129015100308400c0c0031180324007050f070086c0a596594209540401410307605e42b130038000c0e48010945042500d43d01ca4004000300d00d820300c640b605046030156140380500791440014150f02582101206001500381f200c0c8041d07000746580391450103545400042200f058034088013400043d1300200085a412007500a2000e10241c0001c1304950b20b422601a00d124a59008003068505400e02224461a009065 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 631558570 1250 631557320 631557323
    0x51504030b1005030a15180302011b11120307020a08070326060a0905130c18050f1317070209041a0709080613050c030703051605120a02041116060f0c0c 67
    0x140301700300082e128181556a43c40b10000419201c05e031413034081411150710030076540300e82c0003c034400c0f039a070f206c03100302d5510740000508202d030b2840b4021031145c000560200c5510f094034000c1c0e8035282d8850803800c1000c0d2031000392414000003000d508140d03200544161001c2c0403078135588903400741030003095603074800e0f07c10340c0e8020207200f000c0c82440429803081c1c0d009603040d0030381d5903d21030a6842d10f04807080d80d88680d80c6101e1240101c043c00b070703941c05402c6d4440140844101c041c42c0000c88100050078280f0094207a1034040d0101340c0f240c81030401c4032005900100320304924030741480c4c150380082002c00ca1050b1480c40c40003007001070313014034416015079130008007906407a628401405d03000f000c002c5040e10301c0c0c421921071042d42c0d1014041c00002d0350050700600241c03200e0006914010009a200074000c543c0b00503011094400818a001c0d100d504407000b15817141641da8030001d6001785040d040710341d2203842a050400003140e02c4442c0e212400181440900d02004094403030380000f040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 631559820 1250 631558570 631558573
    0x30c03040e0c0a0c3c06050c0909010b03070c1e0501060902040f030303020310090e0312060102150c22060e030c1804170706230f010f0b13051504030b100503 69
    0x8104c00012001d0000038041100c5524004002e00c40d90108074542d4070b0a1401c0c1d68102d100d0030b180c0d003440030714040c00364040d00c41c12a06103450304620104114410500c0780080500010010400b110310500f20041265045000585000007070904c800c0b52185010080303800d90700c1d008001850301020700a80b81100c1c9115604250980f960f10160044e5000034044610028040c0002c80c1c4504141320f00c01c08003d09500030354650b95042d841000501c0b01038061419540040748400405086610090348100e02e055090303115403100b0070910141d0700004c201c1d600079a20034404602c0c145e0094401981407030480480d00d6031080b00341807084481b003582c000b501c01c1e40d0344c1e40040c0210b01c50001480c0a0042e244690f441d2204648401007200e43d0303011310000700b00803000851015020208040e4001c141ca43d010507030355160462080300e2403254442c03641c0c8600046519000e2042401c1a13100a00000e880080c0d808903803d03080140354014001241c1c000030322000718408840544115040d180041d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 631561070 1250 631559820 631559837
    0x6070207090b0f03010c030914010203090c0418050609030306041104140103230123030d0c021309020a0b0406020106080a0c0501080627010603050105010212040e07050903030c03040e0c0a 82
    0x600d00000e0030203040c2c580e4104994030b10400e0203450034072400c1d46c42c020a9400190010240c908121040344c00c2205100320b038014020700c20301c1c540200e100306001a08950000d040032094807000d2044a910b00090000d006620070050355480100013140b081d0b00407201040164aa0600c401403801039004130102d04000300b00501440d40290f001c00c485100144100c002051400720a1041880036009220881e0030213841c011290a0300300f0580d1040012405000d080800d01001400d1500344140039101744100364103c1800c0505510152003aa00178144410044c0ca50312034480c10f6000d4030a640056180580003e0b00810120703440c003085500c40c01071162a0725003401100c2c00c0380c0c0540019413203040520758900c2030004d201f24126603400c40c808410709605d0900050b085441c16032090703040d5044030000c000e0b0913600a013250b080c0c60f101c440d021555110264208e4040c002c1a01e1290540708c006004c4030100d1002015108540c0141a04501c84d81c030780611240a00480303941201240450 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 631562320 1250 631561070 631561079
    0xf020106120f0302070e0a02190804050a0f02040609021206102607050d02180f03011802150417060f010b161101020a05011509051b0306091305011b020c010206070207 73
    0x81c1d03021480030300900c1285c65141d100c0300c0d2681e4100d0140c44810301d550780000c1d5580c02c1034441c0e1104150500508040034185059182c5945520880304000d151070100e002520865880341e22090240c621000115111082000405404101503c0b004d120709050603903884130a00c250ba0710045640b01c02c0344502c07070200070b01d4144040807014048505002c01401800c0d4449401e02c090314141942c04510800c052500041c2325800c00844007483c080d03410422001e900b070f220700c0004254968181c4840e800140d854602802e1401150010030b05503002c0c03104010707884800a1101e001c0d036034490000c5003a9984070b000070300350b10480780c074190298095040040402e490380c103a0b6400c1941801611110306540c1d880500712071840c601c2e003000d452464414416040300744941ca41c0203050704000f18843e4450550300000380002070600d8171860a501c000398811170003582e160301080e4010000d1048061070700100300200c610b403403075100500c1809500c800c90341c4000f45450284407550042c040c4103041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 631563570 1250 631562320 631562333
    0x3041208070b072c09070c030203040b13030b1602120307020c032e051e04020a170304240804020f0f03101a0d03120911120d0f02010612 60
    0x810005603000310080c0305100c0891641c030b04043c030400166a07800c4461008041c00d0388140280f00c4500c211002d070f0041d40031541c030354028107504801c044c2001150b4485600d0103d196109941021485480100b80040c29036801f40c401c00a90340b09508600300755503130117420000510354800040040e80100701c480e24900045008682124861054612545459002c20301c0c1444004448c010840718645042d0103000ea26000410103d0b0075409102c6410030f41501c000602c0d42144014012a880c4003103011903844020480080c949402034007808841c3d190b9440c4c40e50010f02c2411000005202c08070036038851401c0d5100c05504948405840d91503a40074460381128001c49260015411290803803107640c108010640d1040c011804103003508042d98000403200e80c22070150003000003004c00c0c0b000030340210f0b844600034915000001c18040c14101952241001a6400d070406d268401d031082030b1101041c840340850440e1103104001801c840120b0807281e6078480c803040412a4510b10000414 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 631564820 1250 631563570 631563599
    0x90102250e04020a170607080a090506190e060405100f02030631020f0d060803040303020d0e0f040f091101110a08071a0702060702060109140109150806090102040609080a050304 78
    0xb8081303200d200e03214205a45000c501c9030803004a60f000d00204134095521000701e50b4000000d8130103001142c41d0b42d03a0f84da643c02003d0607018280d08840302211045010394000c50202c2c400900712800f904007400e015840b0303038050a804203a50705002c0034007038615460086a025040c00307440c0c4114030800e80b0141c20310543e11518001040000b140c6a800b664250010703040d0701d980f0300109561140044500c2089840c2948455003a403c00c0c0030800200341c010a00ca1404205c50074462402046840001c80710201e100b5103a500526010f41000034002c180c3c800a05980700340e0703166002d1490300d03005480e03950400d200141c8640c040c013600000a50050701400304984030748404168190342400c140c0a046044942c3c0340107034058810051401e60412080e8010b00035800c3c00c00408840f034410989100050050355240d540b00d500055240c549850000002c0c0340c56000d80318903003850b410641c040d5201d88580c000048284201160580011131264105a0302100842c6000d140c607580c14001503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 631566070 1250 631564820 631564823
    0x8091504150f020a0e24090603040318060903050c011e1b06050a0b09010b0f0703032315100e1c0305160f060c08090a02060904090c0b090102250e04 65
    0xc2e165520038400000500203022a46a642c0324112540302d0582070094891902000000701d55100c0c40c8820062803030380c12150011400d80b05c20340e40342d40342c0c01c00303a41000d82c64043d100e5108101d4400030380749502c41641020f0300e20034070590751840c81c10401143c40d00060384100c0480040407130f5138004640904144a0444251141008541240c0d181c410440f00308072240000140c4512400700c04c1e01d405151240948000d902c100e0034000c002e98164414015a0b1004041c140e44140c101d08040304a404903003240840800c5442528220319980300107269410014013450004c41c51425a40c0144503024a02002030a0044040048030481c501c0b03243d840f13070036400d10008001c02d1030405006049a41c4281c0200024458031a661070404212010002203030204064003080c06040710b0b001c2110209150100d0780c2640b5140d681c1d00003401030015000041040042020000701c03030390800050030212000b60291a043c0410000861111103032011811140703e9440040c4090681c1c00c6a458100d07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 631567320 1250 631566070 631566113
    0x1809050910020d14060a0315021606091406060a0b031506040b0c0703030215090a06051b040603061508040317151503180d1b2d0308091504 61
    0x30540e080035604a0f03020a5000b02e420ba220b402c8003104802000b45960000816506010300c10b1640d140c2d02450741400074014030b00c43e00024800b034003080d08070000d842e454100408010b0034001d860329100c0c01c0d5031405145018002ca100042c000e00d00f00d080d24080b1920070588505e03594075480c00d00c00b80c87c038801499500410a20020468141d108007905008010b43c000389555400e50a0182c501008074080d544240000c1e42006180c800c040b135410380300c55000c1c00100b1641c803070b10100e041100c12140540703682600884d001400340e5141d0040000c0703842c50501400e0350a04100100c0700b20104840150108e1400888070095402d00804517a001d00740c40c1c0481c040040c2c1000103441d042542410b100b00c0b6501105101110b0141082030302c850840b40010b1150800710315000e041c0404860781d0040d00a41608003105004a40a80ca010341e2040d03901450360a080390b0030401c00251060741a000104000001106024001105892290203501114480d40d0b281d80f40071080c2c02c40741040444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 631568570 1250 631567320 631567333
    0xf061c06060b07050607080a0c05090f150f0d0e031602150c030d0b030d170721050403020604031e0c110102010e0111180603040b010311120f061618090509 68
    0x29050018050310b2a84e1007070b8040e04490030000c40c01000c17000050300d802d01581c43c2231103007001c1603002011580b00c03201c180c070b00320391041d030030301c000340c210740f11940034101c2d1400004c0d100c0050342c09c40c40204030048030007004103e514501e9529a64034080d0500703520480004000c031030090301d0104d0540b01d6560b9800307243c40c40c0c50301072884281590071844081070a140c0b00c0540c00440d241c1803000201c000403501e0b00b4a0041c229846644424a01508110600003c40b404c42c800000f0140e14601c40000f0307060900a40c1040d140c000c0d92400e00700c40c25000200e1210082900d40d08510201801100958407901207012544a9480d000000e184850640d03507500d540100c50502801000c1c003000101c043d4680b40c04c230743c100c0390f04a0309148881c2e61051000700200000a2008a00d4a05480c0c1120642d900c40e400700020940d2004200c8902a0038415080254500140003500340e1042640781038400d00c000c0300c09405d03112075404c20042290f50900e05802d1148542e00d61207a42c0c04120320084804 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 631569820 1250 631568570 631568579
    0xe060f0408160f1a010510140d0603060603050c03010c05160204022505150c041a03040f1e17070308040b0c160506090708160b090a18020904050f061c0606 68
    0x820003001c401141c5144c1e040c540003515200e45100e50b8018401940c0c01c08408a044d03400600d13040c00010016449040819100d554000315400340d809941d01040402c0815143d051460750303a10311010300c0748290300340304081c581e040c8500c0982c0e0128200c503265181c004c60703507800c110181d00444942c04d0401e03000c0e400100e2040d002121050407a005034050314401e8191a1000c0340c01c5001000c3c080e1010f0b0402007009290106400d400301c410980d14120303113903180c2d8507110080b83ca40c001c001c1c00342c0348210f80c120b0a0a004440d020780440c42045c00610f1400140003042950003410800b801040c2c42c1030001d0b01103118502d034940d00000d0645298607005031a224410554400c14054800e980804200324a8540400c20740c0094049840101445030f49010010f8000c0c15034000c607050043e01003202d803419200d164540019200c0a0310380102403404031200f1000750030100202d1300c503508140c00305001c090309240050140a0203480c142e100d20017604136501d00c3e103440c1412900c15598100026 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 631571070 1250 631569820 631569833
    0x5060303040f09020c100f0507030b010206130303150b0304080c2103040305031008011b0e040e280b250305040206091c080a0c0302150c30010f06030e060f040816 71
    0x24440687c03031400205414150801400c540400091342e040d540300703005100308030640e0304000c14240e615280110751040c1050310140d00758600c0e8017000125001206000c204410003000e010604000400c68502c00b1030465480d5841c883e048550114100030804640840d200b00010342e03001500f044028011680c94100c542116090801d041c1a5072910401b46140c942c449401940b80c03808860902941c8580c6c907045890346011000703281c010035400045c10500c051801c2c20494250400040b0803149403191130700b001d011100c0400d603440c401144078820041d0107849440d00480d006010a07090500c0c00f402d003c960b801c581e10701c03101002c1c0343d5114400150448000c041314826aa12260201c00c02e150281c60310462441e8080103203109000c1081109031a81501c10001503142c0091110b004e050b000711032540f402081c2c50410305282d00100c1c62401015140040345e02564042022048144019407a80020b4403000311205141c000b04020031a030074003800002c0c0d094840c1c0d054207942c503550103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 631572320 1250 631571070 631571081
    0xa140c0a090c050c1501080d0504030b06010302031801020403031e0807021218030f0a1a15100e0904030206010305070603020a12110921010f09082a030c010f05060303040f09020c10 79
    0x2005c0030400840140305500040c80b282030800d0709402c01c90309080c115170760f580f41303064000c000301d041543c04000100c0c950380044803e10101d084d00021541d42c0c1e00c03030900522001c07104d04141c1c8007014441808102911a40a10b481980300341d0141901c20102280a80c80f94441d40181d44e0001011510740282d80d01440340b0700007000000c1c0280440a6686000318141c0c21a14202540c108240201718007510400c00c15560054102d4100b110244428000d89500a0004442e41c01440d0f04080004150f000110300e8140ea014400320f90889030b940c1022001e07031280c03075005d40c0080c3c48600750b58061040768001c0c04213940307840c0c000390620b4514130104405503841d00c0071101941c0350a81c081c101d60400e00c51080f1308180c0042c14003000b0841e46500c2c4484c4103144d85d6100050000c0d541607c0c0000360a00206003522201c26a5680c55440f422180a01000c4c0d4068080c03626103400301c0c1051030000119402ca821407241c203600b8a28041c03862000390881c00017030040d4020030611211281461062 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 631573570 1250 631572320 631572343
    0x180f0209101a030a1a030a0312020706090f0614070e120139021504031b05010606050d0e15010e04111005041e03081b03070b04050a140c0a090c050c 65
    0xb042d00c0c0c2c680140324805440d000d5200f1090321200c10000a603036140445c00510382501410b0902d108120740c8a140d00078814140042d203460320f00300c15001041003081440c0ca0080c09801c051020300490007516a03000c0c410b032038400101d1061041070b01c19003813007990000620020070000410740c4141d6010006c0c07050f404400350460984442152104040710503100d541c0090788010240c40c4003001e40c814902c80041e001034240094410009580c1580120300e040d0180e00c00c0c001e1162039039034140a04640c000b80c051070400303030800d245003010441c00100101c100c41c4910a403111039180950100741d12102601c2600d1400812264001685482c0d5105425502d96902c01d941c43e0724101082298004080088015200c14282000030074a40300940e680c117031412039003c40c0c115022070014a54454800001d000b050030f401007000348080070804030b48280c081d0302d07902c0481240c0340100c1e8481c08001b804507441000382009008060380b6602101d000c40c040e040062901381106140ba15002c01c0c01e00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 631574820 1250 631573570 631573619
    0xb030312090c100906050414060c010c030f0b041a15070b0f010e0106030b0a0506160b10030212030f0a120908031f05030a020f06090406030b0f0a180f020910 69
    0xa1110b203003041403040045005038a05680c0381800c00c1c100418510440c0715140080f0300405210050707550318000c582c1128032880003000015180b00014018116120000c1881443d09d10011083e040038001d01070f00c10242490079403040a204200104281408a00030083c14140480e40000c1e55403950140100d10382c81c101d10f803541c58210359a0346914140c1201040504007165080c0d0350701e400e150781d02034901c21030340d844e161603100c18507035000c0324404000740414503050140a41051480450400e0701c0c001c1d5400c0048400a44c5803650300e11071390701d210300c414000b00040ba03c0300e44103105240c0e88416048010a0b110884d49400d4029002a605801e698079018641ca10720100c0e00003240003031200f500541001c0c80942c000591089501213024041d0308005281c005694850b8401c0001d0340d404962210541020203c00c2076004084070110303149031902203020310103c030740040d6460702580041c000001112550a002c2d100700007078580487c0030f104210100e03160612071602041c00c00c80d603d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 631576070 1250 631574820 631574833
    0xc06120e0c190e0c04081612121116050406090506031e1207050c01020616020a081309050106050a08090307082706160507120804151b0f0303050a0614040b03031209 72
    0x201c41a0401009000400d1130090b06182003007451aa81d1003000f10a400c0b0341180140020b150092b24071703074090501041d0070700603407000b4100180c000c207503041541c10685007001840d40340c000c00012100240c0c1c0069060f4020302d01d16440340715089081e5115014002a54078500404a0710700ca180c200800c100d9a0340c0103242c800090356410001c0b10f82c000d4034840d1440e860303080048003944415290303034080e100c00300020718500c141549504d00c80003020128000c101c00e41c1d55403002010740d0041041000050088408105840030000a07104d8681c1c1107004140b501d0707a0301807071219031001020460b070b2180c44498511100d41e01c280180c200300022740002e00c480840c40c9000350a080c881d41003032030f0a514002400c0c0104103044142d030141c40b400118040d000c0010b030001d4816804e0000703031030909403807640e440003000702800614242034840d48090095071101030305042660658017584410442e074101b05001c3d480d00f9040b1600c400001f41c1624504070032074039403206101b000c1f51092070ba41d0000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 631577320 1250 631576070 631576079
    0x111201110301180e0705130b011e02161707060c020d06060308030603150c0d0b030a050d0207090c030e0d030c17040803010510050304030c0f110d0c06120e0c190e0c04 73
    0xa01490155206a1001c5c0c14180d0030680021040300c0d003044400c90555484074005c056900441201380185645055003202680f02c84009548429098400e0303411a4280000141c00c400c420144150a4490014010307050406074100c8084c1c40414090b64080260380b00c21010980900c2000091801016032a5983c80c010007818a0300320040c4022841030744900c01c00441e000c007a403ea42c452034101c0c1020800322208000249046a50540070301940610f10602c090180c0000d01d031021100c022109001c1c48001d100c081d402c644a10321010101d400000002d00360610990001d915440142001003051410b064180e080b00300403942152580310000050045140c01c0c00300440400072460321a2441c81d0940d002042d400d50440000d2084400d114500b0400508500404030304401034003161070409281000c0d031000bc0c851065402056100c80001c80c2e900c01703402951007150040c0028665420389001348a503040c2d81e01c5076031410035400c041c086003900c4503501d281d0003405500c03c4181c40d5800c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 631578570 1250 631577320 631577369
    0x180901140616140c01142a120f07060606030606020618010e160305011128021507020313050102120f1e0a090906060512010b0304020d0c1e080a111201110301 69
    0x949440030384224240510407481c8480311f46a500500302c0c108607800c62000c420b185140a6041000c42503a4101041c1008545400805084a18007520061080035a60b40c01501180c51900540b001078100c0c9000036580002d04054183c450040c0340005032000f82c03640a1810800c0ba1480c211042c00580e0041007409003d003d03402c0e44a070307c0c4151034940750000c1d03040d140000a8000c2e1244424164030540d810038000d0200800c1c280c0e091800c0d20240c5004c50000b5100d034003894100c51203509140e404550743d4070005400c0d280c202d09180261a180b454015581e060300160440c460604010740c203003503036000c440d01400c2a04144c0d180e00d082c0604010700402580c2e144e40050b401c019040c000004203424810300d03281103a0001c1c05055407902c450012822101030310740060181c0e010f40c24002106000d00c0c402c0207102030040c00c400ca200f505c41d488680c40b01840d000240070415000840c459500c0c000c1e89200054084100010309241001100701040e002640507401e88551203100f40984c150 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 631579820 1250 631578570 631578587
    0x40504060308070b281503122102090a17030d0212042003030a05090d0206040b0304052109121e0c0a060333090606020610080a15050a0b0607050102180901140616140c01 74
    0x1c459400cad410103940b040800c45520701440741b4680d809050b607800720860000d0040f036404102d520804d541d80c002d1848004103100303095504a8103100c42250f038842d903071000100a0325202009001c1d510388a4251805c41d0541c000c64007140d0b2001081c040100142d46002c010300c004e0000c1c00701c640e1070f4502402c01d1410000c2c0100c180b102c1c94181c00c04004446400b00c202c0e400d00d80c0448060256800c5007003420314050450013410000340d0300c44101d400f051030004c1c080b2405001154081000f68840c10100e05039261000003040d213008134400c1174201d80702085254251100f4003600d41c1160390b5143d10505480710796002201503041907041c820400803540c0d410015004800040130000490741c1c95581400c2c00e0103c04185940c1e0f02c02268680e80070b030304902005e0200400060701c0f1006030070018000d51107401910162103440031441480d0528441c442c2c100c0c2e4034050800902c0891000340b107002e5211004030b1040b81d54000340c3c0c10000e0506103072204080a41c0005056861010002401d03915 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 631581070 1250 631579820 631579877
    0x305060111070e04060e01050a06090c020705010e060c0c0d0303021312050616020f0a0503090405011e03170d020c01050906071805060f040504060308070b28150312 72
    0x8050500300d1611600010b61904440b0301070b050004030303600ca040c810010311561550310f44175401c010034080e101c84c4a40202041d00d8280703800300a29020f440302a80c3e00e80380c5229280c041840445880c0d00c43c07030004040c0000d42a10b01c06d940c0b0031401071001501c030040802c403c6010a502045500003010030b54803080140554900c00424071203540c4074145c0c1c5480040002850344000c0440803156442800405011801d200480304601e105140181c0c0341d400040005002e18944000010301c14200500300b009031114080c061402400c58449030300c42003040708068007000d01040382c4545541648010002480710030000103040c01c02c11126030400c4c0f0043c2500c4102301d00c1d401e014001c1000c0400c0c030002c850003151010307513500c4402440c51035070207558022a8003074946500002800b4490f8000c04480d0b2144468146072ba961104031807480804200500044041425020101915600c18074251084a543c0034082ea926075a4128810000c1c04080c00144040d00518010402507010150325 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 631582320 1250 631581070 631581077
    0x1e0b010206070e0925050a020c090c160c0515070308091f0c12060b030702070f080c1c0f06020405100201021905030c0f040909020111030a0801031713031203050601 72
    0x1800e100400909410024112903c0340d80d02a0205405d0070140b400c160040303001c0e107400c1c0c410030b40b060009807032a0062401301c4054080c2d08141c404601c1c040c1013291040c071030305440307508000c0d6814441011098110040325105102030010502d0f0b030350b250501c0754411000c2411030b40d5100c1c0e480c00900341b100103042c0040650004000c5241e45003500440c2c0600041018001000180160210f484032001170700080300724a49200030800c1017240700214803998660702103030300060703a54009070258900791141c41c016400c0b441490355240b825039241c148030603244a000720140c1d20350711111038400601004450290740080c00300058200351600b2001a4200d000840c1041e4100b104a85410503010100040100003c0085d01181118003510070603c0740c421516140d40c0c580b1801030040010b44000d0b400300d000007204001c1d07290300000319146008250b580502c01d920b1a07650482c62201c1c0543d00c1c03412036081c0303d15114500000322200055000d000100351501001e08040d08843c3c015040c1e5041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 631583570 1250 631582320 631582333
    0x50a2f0f0d1802043c09080331080307050d02071b030309050a030b0c07021f0309020333060f0d05030405130b010918061211010f1b060f0f1e0b0102 65
    0x2515260001130310703d00e000f09400d5a040c0c2d0710000a0000d00006c100181072503070200c24407111940303105841107800d0046110780d103110045204004410000031000300252402c000140304a88164042c0503000c42001015040c01c039260740305c0300e4280c3d04000c841494081c0c80300c10404c1c9076000180e0b400400d000c3d10108590b50840d2074007a048000185070000c80440050745404640b5115440103629582050007041d40e92000001009008050382c260320138800c1506c803032800342e000680c00d40c956074035540c141c002d54600070a02600240041c401507210100448a0401c1c0d22503180d9618454850700282d580c803810142004200c905249144240d07610300b1000c039840d640c11074041c1c01540d00c5040c00800d4400c003280c140c40900b110b5003200c48003001040b84071003003000200030740d20908e5090321001c858205000c0d00300d4a030300714024052904000c003a0380c18040b40740c0c1d50260b5284182c1c85070100d0113500f698210001c3e2002503070385828081341c0b00381c04984a03101e0b100b50b0031002e20901c05482c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 631584820 1250 631583570 631583621
    0x1e09010c06150e040b04061a01080f041b140301050a0606020309060d021908071e080c21010b0403031805060708090d020310050a2f0f0d180204 63
    0x489148240c02480c0741d5a90100d0050303040b00c800c0b140001d0241803400031092403d0b140940c1a14000d40e000c0328880e0500c10522000486c0c503034440c40c80e01e01a03440e1105030341c4505030b828841c140a40160340e24501884c10400d1b19110300680707005420000c952507141c010b098249400c40c1e80050440c40d0044c6054000d200042c0d010046030040d01301298215112190b101d05c1e00300a02c601e5032251034408000001440141c3c010408500c551190f4440d02004451145200c0d900e41d40e450940000072687c9000500900c6404040c111011105101d10421080342d00c0440440000b07801a002c04840032070104100f41e808000162070380b5403804000701081c985000b181c1c185c09a048000d21005000c0b411500300d4070b529a00c1090710783c000381140d1084031860b420400038401911084216403d005040b01c000040b911030320340c000c02401c1d11088400c046502034001e600b003c40000b4409038100101c640607015800380400070b4900000d5410ba0700402d1040100b1a003d501c03200030f84c007115130001d21 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 631586070 1250 631584820 631584827
    0x1509030403061d01020c07031505060310050c130f0e060a03050303070507140a350403120207031211060a0b0603070c02010201020415030204080f070e070c0c050d081e0901 75
    0x2011a0342c00240801c10038080c05804151240d0302e41c0b01545507202044260038078400003034540403039000d689400e6101c03d404021340f054820845001e82c05034094801515448a0b95001650020a01000606103981e03041d03d842042c0d032a0740b10004450a0340780a000512080250a40189044170b0031b9100c0d910b1560340e241c03a804028000400d104001c6550340500078817a40483d40340203100152a40d40100b8a01803d8080300070041050100d10784d2030420a00b040b2051113045a01401d6019003414030b19034030b140800083c04003c0e02103008e0400c0020001c0c44483c40c0495450b25910f40344000c901a090162a101c402090070203113a06000074114191204802c69422514034601031025011030300060380a0301c5103078000302120010750034074841c50b603241e03000c0c10946001006503000d03007040315121695045d040c007503800c8100031318000c1044d26001b45c404054241c41110081c08a6a03110700180c01143d01c00303400c2c0e400364400502c0c07036283e042000e600c102658120500d90f050030128800207 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 631587320 1250 631586070 631586077
    0x801050705071a130b04080c0606060a050d0f06050406030f110301021813140702010902180f010627031505130302060105121c031d0303071e110d05090102150903 71
    0x607051000214003044d20804000b948158007500409100300c50300b01071400902544c02000880d00310301406012501502d0900101c0e034000419940b0141050110140c110044c02107800f0179400982c1d400300000e1a03200c0b0f0240d1001140542c0b81410345420500300081580c4803142410700c00d900c104900311458010031100781507010103980b0410444808840c0300c000340082001040061290410040d801d68150458081c20b403080d00c0002c404440d4180d0240e19582c180e40f02c0419182000c01402260710038600d03003580a0701110740040c01320300c45031b0300c901c0c1001503041038031130611010010006180d0b50081a8100245010020400080e5180291541010300605202d450302e52140c04004c1410010281f0b091481c2e10004154022030b40d01500900c0482d11125480710307100841c2101100c042305480c805c0b8143e40320265103004020000d03140343c20b0041d203034041c02a00c2c501d2119540e01000320800001c40ea0321110350380c401440003e880c0c1110032008126241d554805c00055400100a6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 631588570 1250 631587320 631587353
    0x60b0109121a040305130f080f011112270d0e0d0c060f02030c01050c0c010e030c030d09080408061807050604062001110a0801060816050a08040309050a030c080105070507 75
    0x740b1000e444a00c0c0891340c0d80304002c40611a030303208010114500c13244807001c00c103e515880454400320f40302a201801d841100b200803000c400e0521002103c0c01d8408101c0d0780c80b05900c040302140b000c00114007a0000351103c0c001d084c4c0c0c5d214070082e1010f036401c036080490101c0d0841e0213805c0d2520503510300803000340358000c100070070644910f8280030754000c200356041240301c0402403246144c142d440d50000d4005401c00d245030f41c24101240021507011040710441001d0034043c0d841e14007885a5440681600c40c0d045800290800c0001034608090140a005926508481cae61141194140e1843e0442c0c0d90410340c8141400c00041040c581c1040c125001814809503a12841140e041c00074010700c8418100310300c01d01e000444042c241d03840700441e8142d81c03007501c4541d0141c0350403904007001513241502401140e8100044c2c881140250192a446031084c9800d0394860385417004130349034002a078022624000d08036400c3c801c42c1c10078000c5d694004103130314050b81017490503162050502c404d0500f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 631589820 1250 631588570 631588613
    0x19030b0411150f03040b0a020c060c070206070b0702010b0a08010204050a061412040308161e03021b010f15080a020d0f110415060f0906080a0f06050409060b010912 72
    0x10745031950b4859400e4801e011108601054a440b0000c5200300640e00440e0b003200c8004510000420301072140c420744540c100c452008040039612440d00c048540c0c091442607030f0000c1d082c010a40001d4800c0d030403034440c1d180396001046200704107040c49407102c12a002403c031359005110510042d2145411441290403929091404036000111901e151090329440788440300a0010001410f4000c3c210a0088001c208101060030300070a0880300401c1d16800c80b018240385241d2a039038203100750041e04a402e50600c070a180c9441c0c0098507802c5652a4020740c0300d0a4491400001040400d484880180f010b94042c10146001e0742c000760b02180c1c0101d00410045200810710b040c80980c024083c0a03020140c020052a14040d4948900100a200308800190000c020000052081c540c4d00115605c5859000d9246c541007802c1c0007030611607400c015140d503112800134241ea651301411001c43c0c0264400101280d50340001440342056401034401d014031100407000103903003c07280140c80001d041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 631591070 1250 631589820 631589843
    0x60c120614040b0f03010c030b281203050c01090b01051005131710060b0d0b0409152004030b10060206090a0305130e0f091e0c040902010c0507090b19030b04 69
    0x70742d080c40800b1381c641c1c0641c80c00d0b640e07000d02601503011400700030040b40d100740140301d43c454002c84012903404018900302400f02c00c0020480b001042c0341030b98441c1c104941062024000300d401c549000d082600c040807107400400c40c03400c01d041a9604840740c0d103030403031806804841140e5603080d86d20a00301c102c1c051487d01c00c3c0b40c9200784405840645040002d00000b82d0720150b081454009aa80032007251030004002028a031a114409890364441600740c011a403480002c0c00a080440b80c0144100781c0c0d10401c0c00e030000e000010320145101e030f14410301a0400011141007517900d0380003007040d5404001400b5900c54001060b000300b40d45450141d07613604e00c01b04604d24500e1b0326030050240540381e1050050030980c52180f54031640c0a0703000c4680316550b0144110007517400480c9030806400c4034910341001c0c01c3c2070308142c8509006050420130705205544692812480390300042e480395075103030103003000c0c030b082003000c03174501d9082101c0303240c01d411915000d803144005440240341e030343e810 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 631592320 1250 631591070 631591091
    0x209030c091008030a020115211103010e010f1a100816140c0c04140c0927190c14040b0a0e1201090506130b040201080703090203030403060c12061404 66
    0xc042c00026004020980c0d403103001400d8080c3c00f07131003251444041043ca10703034003207141c4003400703050b0080121b0001c0c40c90088042d91a482400141c000701c1355055503c910b0100c1180c4000d000e1110f07911440c600c0000e0108102d0880d03900400d078800381911400341c2c1e8601c114415132000020360020781403501d4469003a01c404041c0c2c0c06202c0420400c032000004908840420000324080903104020354051001560804a00000c0c2d07004580c1040b10301c4092081d180b1904110b104d221851840310138030310740708003035022044044a0480760403070000c032080854501810b150050381e000d4501400d0521150303002c0321800d102c9006500480619500100b01607501900c80c5448015410001d0040d19180100004c4280a02030790312080d1014840d00c1c001c600285280c1d001420f4064000504400540b502e40c0116a2081e010301302c00c04054a0360107100150350203000a1001394800d070000514404040009040702c0e00700100300d02c00074034058042007080950380400c02000002c4a000412030301c20b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 631593570 1250 631592320 631592341
    0xf0a140c07030c170f071e120b160503010e040209040201030b0a030309060e0307030c090c02070902030c07140c0f10020f1024080304090b0a0305010c020d0f030209030c09 75
    0x3400d04a9100c0d2094180010a0200d4034031103c00742d42c1c414509801001c14619034a9403007580030303070385001c59101404c10031061100a00b565005102d68198800e40d036500c010b00d00012410320400d0300d401c1c00403000d004140803900050542c00043d03091080c11507240105400e0f03400d40c014000303400b070789844001a045a200760b00a2012001c000c187d50350140c0c50382401489002c41340920000310b07044d040e00390301625001408070100c80d41305044001c0e840c20130807410050320a440303100701513115003140814110800e0010b10700c51101c010b0015103800541c1441440034002410340d0700140c0260580103503903100d5010040d249a0150b4044101203810a0202d1600c001c000c034040c054000d01c800d0303a191300d415401211303410201021040030904402d8411002c101c2d54894400c0381d0748200410400b240c11900f01e00140c4100801c1c208065640381c4405013510010203d010058200c820b801000d16042800401401c9042c913085052440350302c0840c0d500c100082d5041e120702032000001d00c10101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 631594820 1250 631593570 631593577
    0x180506040e01020d0e19080403020d05070b1b010507090e0f090316030903060e0304080303011703040510020d02060c1e03091c0c150c0807030c02160b0715020f0a14 72
    0x220500840d44d5108007040480240500402d1041c907000c0d052602d05554420b042c8044119004000c0a2410307146508001c450b910300901120103009048000030700031b585001904000c15205070307441704200006042c608440c4001d041500344103290b40c05012040e800828240e1027692100c2800c502c1d00c640f03240c1407550103503c0d840c482180b4140301c51400c140c0c0c400329003811248101c80901c40031540e41e800580343d0107030b405003000aa0040c00100b140c445424800c005d2805040c083d05c0c82c298903034010648405548100c10056404190602c0c3c0055040101c141c1c0107013022402030070803464140030194180c10080920740f407180803020646d8480d051100c40c590800d020440a01c00601680250803031190440036960380c1c3d020000f080043c2c0541c06000303540c1c0b910765a0246c00c0e542e0311074203a00406840031f000c1e0840c07140c095210312a00c095244200541200c1c0000307a1940715525040d603031465032058420085005000c00200304449106442c2c14549600700000001041c0400044900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 631596070 1250 631594820 631594841
    0x31c0b0a050a09090c0801050f130c050310140f06060d0c030222030309080c10080c0702030d030e0106091406060703121811040912300203060307080718050604 70
    0x40c0b0304600054107070161382c0004e80e0280708400840b121680c17440001e00700c550803038500805150040001e0224400112040402031048203201031690b2644082858800000508608903560300d0b602e1040000714102e155104800055500c99481e101c2c01045040c010715088149050300c54284d02e1082e406078056901e110b1521500c0d140740304254061000700040b80c4400d8020490140b8086100c04e004103800d05c2c00039000d420441c4102c1c5003c4100c52604000f0041448048148203110041e80c00784942604030669a4000c280e00d01000c420702d084036041c0e8070400d0064a051107100920b541036141030f81c003001c11540c0c2620340245050689106800800c8265501d01c1e10880fa01c1c151420014040454061050340c2030750005041448111040020041c010060003008071011a1080c00020911922004001f50000007002c2042c0e10104d1b03105d6081001d0b402200b04820750030200030760030041402070000c0070440c0c5130030154000365000b101000c2c0031949690025005841d6a0008565107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 631597320 1250 631596070 631596079
    0x30c060c090905090c09060109140d02120a031707091a030a0e0307060f1406030307020904060f0e0601050321040608040f080408160b0c1504050c04060e0a0608031c0b0a05 75
    0x71314100103030f41d84448410744028481c899400100d112544900e2819040e10807078101001c5401c0c0f13250801480c5064840102e80c172003409456407034028018080804814031a88529403070751030030344c0028186000140749504200395854108600800e80101c2030812000c1210260303a03464604510340038041100c9026200d01c800103a070400c00c03c00b41e1001c90b0801582e41d04020040004409408081d07060b9007103541517009000c0c41d409880d00b00c3e5040d80081c0300c0d0310000b810b400403c40d000705903006c02ca40100d241e08000700410080c1020301098551a5500000c1c2011520b40342104089000b0341c0500410000d40800140420484a41400c0300c150402c140c644c80ba9503504a15681c0d54404482c40503010310403100040f0400180706036904001d40030042d2a90845000d54940e0641000f00709a03102d2141c1c1000480ea81c40f28807900018040c0c0e03000c2c4c0b0040d8a0028240c0c0c040c1d4240360b1180c0180c0c1d02c10048030100038058904441642e021b44400320721420124001b40000f8156003120740d11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 631598570 1250 631597320 631597331
    0x12011413051b0a11010515010e040b011223090c06071205040b0d050108010f09050607030908120f04050d0c112e020706020c03030c0d110a0f032109030c060c0909 71
    0x903004013032003540c140300c040280300ca80d889814039100d00c13a5610341580070810940e1000f0087c50181c1080851001c185815034800007412506001e6030004100c140d00340313494960f405529070481e1042984580010020a4184014070101f01503100d030b840003070011402580b00102d01c1c0d100d20100e074002d11281411302e4a400205240b540180003e110390303410340d840d02625000c1003019004400d5801e0f0403a0203000907690300c140c15009007030310b640c1c202d0b100b8034100084005918000c2c01180140d0343e10302c0e460039600c0d141c80d04a103040c240b4800407090001e0703580700000169002d03400c80030000042d5005054071084182ea051850f0300201285100e688110382d000f100d079030000b84034003101c8541d82114a8895040180340d01c0384285000e034220354100e101e040100300e020f45814814440f03c40200c4090429640300c3c0360600d03109180403000940791059503204240b4030030441115484403081002001060b650240502540040081c080c2d5240c03280d244180340110203020003410b071103100f40301 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 631599820 1250 631598570 631598587
    0x270519050903090418021302180324061507020d140a05010b19080c06091203030406020901030f06080319090825140901090b1f0512011413051b 63
    0x11650460a000b9008629080c000080442c171011642c860365006407100c401c003600208014040e502440002c800340c001c4600032401da0b10100202503075010034001c800f000b070b01c90f80d45540e003082000e8000b030301c100030060074420340782050303021940d95030790484541d0401012441c5c45032130f00101c1c2c0711710581801407405240034003e040d0000c07040d00340200c5070402c07540140e81c3d4101015049000d40074096002041d02803c40c1494401800044030082040d40c44690300c3c0aa9855a4030444d812a000c0c0d401148000c15945c05006a00c05149090300c01e0011508004c021075690088080c0da00340c010350ba440d40c00303201c0d0080a1140241041d007068411603c8806c1d445068050001726070807107003000000014500c40300c404600c5100a006040d08620303403a0203040c0740544500310b00c1d02d500c44a076100600001c8a0850001c0712000240c80e040d48a5003865840c2c07034040d070160301100b07080c600485150556901d43e1034a05445201a800141c680c594a40d9000c1c1030444e0300342841000f400140d81032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 631601070 1250 631599820 631599823
    0xc010f020d2a09090504020a05060c0f070b210a0609020c0c010206130201020733110f060108100207060608030c03090a1e050603070203090916092705190509 69
    0x4500c40b45808040d400d100480c040200c0d008551030054000416100c01403021112a8210540040c0020001c80d001926600080d45a40c8201e51500461307201003009043d03030b14140700d500000d00101c0c0c040c0d03041c200d2911000c1d0b042401000c00ca460b450440c80041c84c030f0710095004001622a9090454440909002c01c0d691000301806490151050000203403004900c0311240c482140d0690103001403d10701440d80f034180200503800b0000c920011700480540b00240303c008881030446ea659100300e46e9480e07102e0b040c0030620036904090382080c40117001c42075002810400d80c800d568801070341c2c5d2046040907001041950425506d13030200060644501e036000002d420780d11012507007004a030303640300c8150302e14080508403c811032040c00030030421450b000c4040d6a204907a8015289881041c000061100500b21624004502da814201c00f145601c00c02010150096804008822035601030110a6000381582014020344510014280d403800d41540c0d4a4484482010b10407410405840c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 631602320 1250 631601070 631601081
    0x9030b060111070b180d021c031b03020106140d051f091b05090121060209010309061e1b0504050d1a0c190f0e30070e060f01050f0c010f020d 62
    0xc012403503a0307020b207170309916088400048090740149004100d4050145001141c09140030990900100c00515442c1003121035003180f001d44250300010340b4500b40388034142c03174585499800340245910b8a1140c0020000100c0145042460441c1e03440901c02e8074815000d07152058001303118140d00500c0d010750400c00e18111003907490450301c40d0f0b90f0743c1c1c8952039500102c404241070707500182c402e145200402d515a00414101e9818500810300c1c0000b9100c0005031010f4000c10041140086210751100c0090b01c100c14103d4940180c441860f8400d0034010728034087c50180d28429540c1503444820841d03020400031404540f003441e4200e614160310208016008020a42098010283d641d441548542440d0a00c10b540d80c4861490280c50400e00400070801d00595946030300d0301c0e811820107019034803141503682d4440014002d26051001d04034200c0710103000240240300d10601d100c200c0c0c1c0c00900b43c1c1c1520001d141003580f90185560070601501101c50001506403001404903d54201038014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 631603570 1250 631602320 631602337
    0x1d010608060109050603030f0703030207150501030b1b09280305120a020c01260603010b030f0a150605090112050304150e01020d14040b0f07050d020f1c09030b060111070b 75
    0x7040313196a0002895142d104140081780394107400c000d0301000030300a074050281c090140313a003002001d81101c00501141e0080e0030a0741c410280f0810000c03070507030419200100c0b8003403801c00d50510032101c010406001000403842c10303860302c802070340350400ea000c4000402550408113348100040c4c4040054070384c8268a80c60044c0994401626a94059080c108008080d0004072a003e03c41e0f01507103007042806050703076030b01d03549038040c4002550702004210310020402000d800303560803a1401c5040c0509400e0210813560500e107080000e03580300800d0341d04684e00000c0743c40ea40d07034851510741d003980701e40e030032540c07440d42c05220300c0c030507151308c101001440007081e002c4540d6515422401d8849101190b4a8070410300200000c1c4551800031000d40100d009900074141400425a52141068202c0340e0140c0180d1008a00e4041410708002c16142c1801d2000788220889481c90300614415203070002604410710740b0041861a403240071554021208101a101c1c100e0715200d510302180d0001a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 631604820 1250 631603570 631603589
    0xd020a0306061502010608030a0e0d06090804060e0405160c050a050a0c0504061d0402040c03023708040f0f02010e06070b16030e0a0605150910081203191d0106080601 73
    0x40383c3c0d0040d0300510804041e110140019410046101d8040f208142101402504840402e0036100010742600448808034402c003500364a403030520f14006c2c10790b20400c040c10700c96414003040c00411543c00c102e10140203254a0312144156841c1000d0b80742c1030106100800b188201d8003000140301c1401903d406507141180c1c28801c46960314905d141005041c60400d501c14030740b801080042c68240d103c10080b482e1820003609080e00b5841c0700e04071361940a82109590761000140c160300340801c00b440054480d0b41040d000900f07068540c14818004408020958100610507009580c003d04600504840040020350780301070f54030b0070712071301c0d402610828169110b18011010f16402070080400d4403000301e0081012502c0764407000c010b043c1c090486498105c0544104140d80c440041503481380d6014002010b10510f0180717010b10344050f4070301500302c0680500c144440c10007009208031510032144404140ca04008404400c4c084502c044207070b0a40c40c0c5a4002207001001ca2194120385400707a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 631606070 1250 631604820 631604849
    0x70e1c0201020d031a0d020112020a030e1c0c060b0f060304060e0705030f0a0b0c12180f031303150b03011b0e0907092304091406250e0d020a030606 65
    0x24040d8140c0b00000d0200c843d9035049040000c150400c6c070540c0200c4c5005240542c107940340480014200e81c03100c1203517070000303803105078600300c003a020418428103d509980b000b41403914080c0c0189580c2034028000d0a03162100745454081c0d444018010f243c0c03400404444d40d0f4200340c85c2039401411449505e6095015584001036280307000700d081c107330100400c4060902d4140c5541d510135104001040009840d50500031117400000fa510b40c2c600c83e0003410b094040d41440d02481502c3c0050918042c0c50a83c030800c6804003007070035a20311004030395001009075410600486400c1c0604121910036070190f181a0000b000c8004480e000403074140c0585607481c82c8810041801141081140c845d03000c281c80c5241000100c8a280c1000230018621100866130b88001700002c065885558082d81c5920040101d543d8030b26080c0042030b00411210b50105002c41d12041040c0308034414101c20f07003801070f0502c81556549035902c064070070650050254aa158892030948007c0c541e82c041c0710500200c2d034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 631607320 1250 631606070 631606093
    0xb041701050405061906120804060207090c02030f07030c02090c03062d0d020a0819140c030a0201120212040c030c06020f06160c05030a09090b060f070803070e1c020102 74
    0x6100c0c00b402642c2000c041c1041e95a204200d01a0506483c901e010311603031840006205050f8125211005224980703950340c861070700d0340091a0400039000f074098540f0340380e410a40b4503000021501042c082041841d195001c9080070742e090451048069003000060080080700300400c03006600c591012510101c1c0e0000c4e0660302c18440954001800040c43c1d03180b2010f00910344031f81c06001d581c1c4014491010603465450b82c07818814224811075401c01707a401e0300342c200003210404030300780f42e046002401c42004020019946891072600a030500c010a080f030300702052650101d8200c0d08401c3c510510a0420f0b2034803c0c0000244d110686208044240102c0d40701e00c0860007000c4514910000d1019844560701d8064801c03481c0007420038001903103090400100140040e00a0314502c2e160062004d281102010940e00b9007014148141c0c010080c400c4031460000c159200260841d109580300d5540d480709646103100c0ca0f10465002c0d4030070220b5948190442c5c180149c4501c00e0f4203072800441e51 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 631608570 1250 631607320 631607323
    0xa12120e0d0f0306230328060b010e030a12030204080a030e0306092a0301020d0f050906060901150806130617010f0b09011211042c0a08040b0f040f0b0417 68
    0x11303070040b080946413150803450324249a00038100d000720010b00350355120103103016001c00351000c562680c259040c004226030504c0072902c100380c004071080c00d01d00000541007001944540203641c000304880690a043d014240c4aa41603401601042007100c070103000340d08015104400c101e0003c3c0c071920440c40002c8000e035010078031950980d41504400102050000d00070820456046101c0d0159400e1004004d000c1040c05007181581030690006040c1c244006500d042040060030180191816001000030000b41ca01415545030540342c494100d0b2504000509030f005480da405080908084010984070349015a201308401030b103000300150500290002d098441000400c1d6000c0303031600041000c00c15203140c12010078840c034150300415002c0d00000f0200d0b0310306983c4100e00c10400c91070a01d410000300805400e00110001801400c4a6030f8800c0308901c91070107400f40005020503080da601046106035400350055420559149445007000c114640081c4201d040c190030804800c508a00b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 631609820 1250 631608570 631608581
    0x60908060135010902211005070503070e0301060509070512090604050a020f040f1a01022b0f05070c09140c16020f1233090a12120e0d0f03 61
    0x40c00d00c100034000d20303140035102c2c012070103480e00740365480d001c099005030b460750803d41c6186144581c14021001c2459654945055410302112075884c00042c001444d40000135203921000900e0500326010300103010901400940e8841c0d5000300c4d0043c00d01103010f8002c0003402008441c50140401503540c2c1e510503a8890040d64043c0141e00103080d201d016050600b0b0a0168040140c004142083c1101c0b412040b5821220195018144034030880015070b814801d1701d8582d800400c0c07101c1c0c04001b80f060240c0340c40c0c0c004103180c140588440c640e10381e80d0041c415070344526006452941040d586241e000003801c65a400c00c403401c411200000c210307020f41d405980002c0030041081000600f19400c1c0240c401d914100ca681c44202601e050301240c1d0108911800c040116030b4034812140d40111740440101100c1c4200f81004a64080250504000505071704180c0c02c250003030003903150603406030b456100031424114200e08080f20a203440400240034603c0390038681c3c586c14107842d50700d022000c552 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 631611070 1250 631609820 631609859
    0xa020a090b12070f0e040606080f0a03090807050a0e0a0b03062e0303081902090a0f0509010501030e0d0e06070804080d110f0c09310b0a09020a030f15060609080601 72
    0x107100b030301748004150201034543c0179206080009249440303490340384c6480e420f4210031002d98000d6005004040d8002840303c018841c0030020010641050300003030741d900090041c07007512610100001c031104016002112848800f80070750b403e9003003090610b0340c40112044c10380c001200c0c0b6440d54002070351410f000c0b4122505580c502280d40ca452600801342c0b000c0c0c44442c048030b80c0910001e41d00c3c0d900d8141c141c0042c0b014008a0412620744014040d4030181640701c9410305140c41d0000000b000d01046000c00e0800c28942000300c60112030004d040380c043d0550160002e100418045200540001d076403000440603120350443e4000241813581d1821100380810b40c40c0c12113043c0e4603550801c1c0380400d410410300e500d0a4084150b01542900450044002b0740421038440d10b203500f403003444d652941e0400b204040a004540464020520b42d0700c032448010640b802c42d201d0101403000215011000701451030301486143d41d0390034020000051405502c0c020700461000154009a03541e40602c01c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 631612320 1250 631611070 631611089
    0xf090c080c0a0b090402180a0801020a0e06090a0b0c070b07080703080916140307031a061c11060a03020d090302010b0f0f03060c1c021201180e070b0c0a020a090b1207 73
    0x10402a00303200c0030303402c07e0070304558000460ba0494515500c00e4608005800c84038001a00e807502d141c030040c801d0400c909128003400c02046801c01c1070f280c14240d4000c0c0c07000f80580c2c6039100c20744d02e0402d103400d031503500c178589488001c512013007040305601c018001d2038082d945101c00c58440700e105e0354850002c8030004141c0003148100300301c40c0d030f40c2042184031080014265145507550341c8461a02511102080c01084140703002c00901d8a00303008002c2a84201609410000c21282d48000104280c0501c842c82010301094010b52035200707804584640410020902180d1a2854040d002e4840e0311728042c82001a00c4ca0920342c6c0c03c2c44100c07500c600c68000c0c0101031a44071002d2802c42030340050459105084000031602c80e08207170f40001d0001101c5a128620a50b00d401c1c40c0c3c104a50804291440345400c1601c0d005032080000341078429503140180c00d03940c0d203540080300d5141c400c0e00c14000703411841030040001c0c07078039140c1e00c40000c010041c0c1d41c403602ca90041040710f854a0060269808a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 631613570 1250 631612320 631612327
    0x71104180b13050105190509120a081017010c1b020f09041e0f031e1d041b020a1a071b11040504050303091516120f090c080c0a0b 57
    0x1244008407010703041002d40180380e000d1421a1240d03404d41e0380840f80040c104000b0305000708202418400c940c0d01c802104050070071100c1001500d00380d4410300c1a60401c0084505c0401c150340004100300004240603001c0107514200c00701540d0103400d0261085003c540803004104100c0305000788009110b83c02031445d854010f103101001100da5018109490844140355450381c1c100c46c0d01d00951116000e4640200546164034000f050f0440034103802d519500203104521019800c0207144443c4111403500644080d000e1001c540100001c4010409001070061220785498021a11400c118090b0a240243e580358154140f040758003511501c0015609448140c1c07a441c6207a0101ca9052042c00180b0090a1202c009016580c0c00d480a0750907410000030f120398860200001d120101703503d1000046403510400715640a5440c0443d01300303002c03c151041c3e10289455001c0794000144500422030021141056440d070312290080c011103100f400384c02441860710301c40c400704465540c0483d500c1c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 631614820 1250 631613570 631613573
    0x50a0c08100b1614160b0f04050f0d080406030c111c081b03010608160c05120703110303090706140f0403032106080313120807062d0207110418 63
    0x150b584242c0d46040e240f080301c4030040c0050f80700f044401c01e102006008144000144c0c807500c00b020726950111081c06006c2089041c0d20725490181d4045030f000701c8950791161125401301e804649080e2000f041070300c0c002004100550141d1282038000b074180e41d0f51100c4400d0b05489a510000c418242070340c0d200409645111500c10a4035551183d4100480c0a000c01880007048250300b00307801c4200440c50403002c020420409603102d0340b414a05140c40c19129111381c5076103440d26844042c08403030500000d590070616014a0341e411843c1d03049400ca80d41c0e0700e8280401501c400441c0a5100020b031014840740c10540000700344c40000b003500b80c526280c14510b0754162200307140c0803240001c0c1440c18010903003100e8284140d100078990349000d142d550ba40400c4c0c8107500c00c2c66400c2441c0b20251140c2d01c001084000302503d5285610100008603095604080b5030204101104150000340b807140c1c200340400d0b0360f0054034100d4030807900c4000c240e0505040106644040034a501e44040c11200d500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 631616070 1250 631614820 631614839
    0xf1207020d08090303040f090f0f02070b0103060b1216030b06030604031b060f0f0b01090801110304021009150f0906031107060c1211040302130204060206070e1804030201050a0c0810 80
    0x5001d00010100c86c5010b85c0d44202c01c00000a640c01080d1199840000e8015806980140303001d51305692021407900d90a235984c88400340c0c0c10301002d041c1c08d958010030003081d1107016141815042e40760882c1d0844594855154480d005800202d4192180f2008070718542800989180a2903154032082e105923452501061070304281142070f5002502c03182c900005103114030506158401420021071210f4a00d400036000b41401d602020150703250441409140341c0e0002505d4200340e044400e42e086801c021000c8503600b04a400c0f600c0d1031544800444e05268005802811680b0f0b252500e0490340e42d264000e808407680c000c0c07005540001042504005074141e80802041922400c00c030842c05010341c00b40c0102c03240303005448503d550010301801035150101090060000010f8190314190401400940b45c0c100580300300c041c010380f21600c607083e82e5025404100d080024901042030b02d0719080080c040c0a00740d50f8115118030f001a1044003510400c0c01500c0f0708010700c80047e00a19090b05003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 631617320 1250 631616070 631616077
    0x503040311060405060a1722030318140d0845030307020a03030b030c150706061d0a0b0f0a06140d06141203031012020301021b0f1207020d08 62
    0x1a0b00c400104000709103940c680c400390003084000c1e6100c0b420085e450b842d891440344040d00031602c9212007400c610b02c0a03000d20101151039414500440d034045011388244030102030601c0103100c80e0417550b00111121002582d2600148140c1d9200d035141c0780c5826429200b40840d81f80500c5101c0c169071070701524400b042c0848025035a03904800c484600c2e041007421500260342c0700c00181c0084490105269140c003c00d072800404801034074007052900d00080c0340c1c00480c01075101045001c03408905100c0d03564000b500a1445086d8510200a0070407001d01c0710004982d403503e400e10f00800c86003a1305024001d00920200a40f40035060f509100703040c1c070002000e0152048640341000040d0b4049010b004100040006002c0c284607500c0140400c41e0240c42041c8800700e990051081003158140d64203100c0489980015800d0b8040b02400882e019110342884103c1c0c8140b03982040101030b00c0054440c16000c008403d903191051400d074400082d108465003c0e511a1a0626220210f503104004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 631618570 1250 631617320 631617353
    0x30703080c031210080709051e06120601060c0c09020702030c061b0a0506070201111306030c0903120806030f011a040c20010213050103050c070312021c06080c040905030403 76
    0x480f0305020000d441d00c4a51442210203521240880c58200449102009510060310102d1002c2c0102e15143d2903a195402c1c0a1204520032003085003c28040e40b500034608040c9002842501d65540c1c441c80003409540746501c0440740207420f50000110300c1c00c58426149540c3d030080c0584028801407081184075045402c942e1030b003c646c1451042c0b07010b01003000c50049442880904907500d045200a03085401d580b0507042c0e440c00030000c4001c5086003000c1c003001d0b900c1303506002480c800c40b050210b81d6820160401422a189500881001a00546080e104510031030403100c80b81da07815016800c1c0c0da55103165540c0341d02c0072203580003145066000b80d503a1203820700d8600d44a0807112411604000350519030300c40390350300145003213000072984842000b0301800c1c01e061000c1c4c141016008220322508002800304802103805580c08403003901140c0003002d0f0900384000c600102c002c040020400303441201c410f80b080d2003d01c0c109040600035080d10340d8000300035608140c03440d2a010781e2211034449 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 631619820 1250 631618570 631618573
    0x102060a09030e0d03030b041103040309063b03010b041e05040206070b010308121005060d09060609110417010614151207030c081b04140301110c01020306130b030703080c 75
    0x520358070f903448803281d40440c1030095030003003803c208140070301084035140900e1140300e460401c10400401e4000302008121202440d008044444001110400c000d10070002080d004910106d1846544210004030f005d00013103000300007208510081001b145d4001170011100b410a00384044001e1040c0d02042c1e21a002804541c03602c0302541c3c81c8607100d00c00b600100c45407100412140c1d1510300e02d94809038000138031515000e6076418130001032a1805990540030b83c55446803480c1c010089150042002803401100521001400d6410048950440d01802d0400c2c500c0c4501c00200d81c2d0305008840c2140c50716607005291000c2c0c0401d02180990148248a400c0e1040020305070700b0070241d022901c501890340e070000d820398443c00700030701020015080d81e204800d0417031003103516080e050417a41111541c140f0185001d01c0240400e015006004503840601c0000c10200c0002c04190021845400100d600b00e40e400d2006c0444000c0f5011401030b2501a44907100510008401c10700030990303d03412a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 631621070 1250 631619820 631619837
    0x40b030c0402030c070308010b030702070302211506030d09050a0302010507140604060f051513020d23090706020d051813021c05180c0904021c08040f0f03020102060a0903 75
    0x203000c0760980e8802d0390740c1000e141001880c4014186e000310442c0c00f40581c1c45d1028614185010001c0d50b9a0b407078040a072091124204c12141e080030032150040b4030055205503548000304800e507111003281203c240e802030050001c81c00e84a48909003130005c0c0d42008084862650850b001140c1540040d40b040324000d0415140150f0001e0800115129500c00c42c400b040000e41d0031700305000d584003d44110300c1c02c518041c075460603648544840d042164031040c0143c0316400b03603a03560047e06c018881e003180c0c200c0c0410103000f84c4207100c0c0c28520890036502218255a03980704100d965100500901c000600c0a10549004904a04803030021800007401e00f0f2490703983c041c03084226844040601d00a50003010709224190541c010540d1046000d450500300f802500311a64455680400c41da10403054000002c0840d80c803101c0703142103030803014040c0c2e10904a524003040300c1d82c402e01400c941c800d40c00a000900d0484003001000740ca5040c1e0140c4016102e505101c000b070b0158100807011b03c920306 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 631622320 1250 631621070 631621093
    0x15060303170703271a042a050a18060f0e07050307120203090c0306060108010605160213050f0703140c220504230606031312020a0203100501180e0606040b03 69
    0x1640388a006090641140b11610742c905008a507002d13820103072a25005200b004081407000f0f407c889000d1589811154404030301c802c1c44c4100d00c01e608484e6000188010205170030001c0d8541620940303035010204411620b60101640384010340c03003013074140d000042c00030325003d01c1000036580046a42c1421954131032000d00c560283d0b0001c0750b1506c199482910b1070500345c682001a242c12503000c2c01d0001440d414808010010b215070640e50340c918048000d0f00e0110740740d5402c600070300d4031030420400503820604544030302c103402516403a0001e410006805510400c41d8883e901407820954240e14002403000d07003074480c101071209489160303019000065503890700e002d881420100f00c60008600b11540c028401d4940c000380c0901d0003004280208015899035480c6030740d540381c00500481e403070005000c0491820307105030070082d014002c4a1a882102c901c941040341a6403180044401e81d8211107004c00484221814840c0030381d0224020440178285644002c07420303079014042e1031008040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 631623570 1250 631622320 631622351
    0x60f0b031b0a0210110909251b05010507091e15031a0a0801020a1101020403080a050c03071505160206040209061207052d1806040b0a03060f0915060303170703 70
    0x200788429034481c400100d003040c516041c43c0322940302c80c4c807011000c607000003407011544016030b4503030903402d000003c6e09e03402c014402540c28900c5140d1042c0240034519100e440184038918620448010404840b061803c03410f01c12800c038141c41051a0618141140e800120060310355041421601094501c1d03c07005a1034141d1444003600207400096a60421860000c02e10b4a40424180c0d07131340d01c14807081c00040c1840c0e04643c582c9900c0d20b0a0394464480312003650a5110b20b9800801d08802040042c542003190340240c1d200700110f00410410407003512080c0e0f22000d04850080d0720030052800540f40303141c07400082241092541c00c84400e0f50312100031400701ca064a24006454552000d03d501e150b80001003000c4a480650300140c07080301e02c001e004c2c1120780280c80c1e02c4c82180c84180e0140d40d42c0780c0c9160300d001150000028044180f11600c1d2030000c00700c4031400c1d181304a02070300d0500210b145020707400441703615036510140c00121800303298a000d40582880101030300d0741c92030100d1589 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 631624820 1250 631623570 631623581
    0x614090c01090518061311030a09060c090b090907020f03070b06030c0a050d1403070804031109060406050a0909080f030117060601140318070803040603060f0b031b0a0210 75
    0x5900005240405980c0c001506022955101a10803680740d800c1c1d02c0241421081550481c0c01901c0071403a0074840000e03039024281c86c010300c00c1002c1001c0200700b8001d07900c0c0c01035130183e0f01400041242040c00c15088422009c580240f810680042004882e5420300711003d650080e2144180c03098500241603050860780b03c0c0509071444990b030014405507241c240291100194202d5030510003500d000085202c40300d02050150a222403030301501207815003401151743001903015008560b02c80e180d28001c03000d44603000b00d45000fa600800000d40d541130038803510b01034813001440900480c0c0b0b08a006800f8210f00c003000c590b0980c0c2070251495241d0641d0103107020707202d0342c4c907150681c1e00400c482c0c500d03182c0c00410781410022518440040da240b020200d94205000390b00926058102c0d0034a10b16004c01613000000500c030004001a50641c9030b072005055400103074640410315035999004a843c0030548801001601e9151290003c0c135503c0000c041242c0c860059a490007083d0300c0c1d0404546 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 631626070 1250 631624820 631624831
    0x50a180909110d050606130e06130519050c0d0804050409080406080915040b1513020d0f06030809310609141509090f0105090f120c06130614 62
    0xa84940100042200341d54600b022100c0540d000000c0f036141e6100c05a40f00700c0030b00814001c0301b00c612802000c5005800005101403805c013115241d080004914500d01c10000098030140140c40200741400b010341015410690040c00800d10102d0010070001100d20b04001210300300000c102c000b0703080d20b0754029510240c0c041c0d503003207485514003240548039031402025000d081e000880d80f03105c0c14010110054010f508150001c4441d5a41c0005e40750301c52604240607031081120785005842080b94000b4002c110004a05002025858080c2ca040e40c01034007006084035000c3c840303400305051070f40071802d1170805103140d4500310030707038003445200c8409103d088481c039130b1a00b109009040c45030003070b4004c504031541c0c07040382803030200180c1c0c2c000074519010347d104228000109466100410040705c4080c80d0600070845814500d00d000d550781102c412050301c50041d14400b04401c0705400c01d58281c1f07072240303016103e40d50b10803403031541e5454000021100e0a98030041a1801900c60011a00c00c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 631627320 1250 631626070 631626089
    0x504051009091103121303060b011205040609060b03150f07020102090d0503030417031e1b0a030e0712031b0507030b070c141b0f040b0405090a12030212040201050a18 73
    0x100f90741014942452101c003601c2403600e0041117246c04200c594051003003200d420803c00101250b0440040301e0082400000c494160704200a22040c006250b01c07030100107110312810840e41080758140b6403500001e101e403c1d40506c080c0300180e01c801107000081da001400d440018682510a80040d4500d080c145003541c03254008400c02c4104503210740c1648076952700e043c61500310f01e0803007456822208220202500c0b0100748020035088800749081c01114602010703242d0704c1e030381081c1d002001450074851a0710b05e8441c1541c005018901035000300d14a60f0540d13200c9407800200e441c1c001aa4407440300031500ca1248030000404504040d000c3c501510260351080413408040c100400815220401d601068015204445020240c100701e1244c4d15416210710b0030010360140000c0040030401840c0e500181480704005c030034040401c2a41c0140c1c4610f80203601c0c42c0103e00210201d0086071904070540c034002012501541c005c8000d400301146500c0c04d1010144141a200000e484550020f07400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 631628570 1250 631627320 631627343
    0x50d231008010506010914040209191503050a0c020309100c05010c110c01030b011e03060902070804030302061509040f08071401020408010b040203190e030415020c01090e060109050405100909 84
    0x1100e083c05881d82108013441c1c030518145c1030008041008194404542c0300310b60004003422252642461000d021903080401d03c1c48c41e540318500b14000c0003103010000020b14010001b01d5604032445440300d80c00c403035402181403800280500903007000d0350455509100030503100c80c000840074054145c0200c07a998403020701c170200d004800e10b0910101641030501d4103145105100b648e10000b40c01107403400220b4140c1a00007401d05070024801e035000341801c14000174190081c464454010811207100c0e908680d43c82e92139500008400b0700e092042c0f1350000d440f40104001c204641d0003030610030700966a9a14101456440c60f07580d40404601c29141d9401150400c8004070030b108410205809590039031035407518290100c1915542c0030540001940c1d60b0076078100310820029540909260409446d042802d8171010b99222481102d01d8001015614081591b04455000e14000c10040c1c5403080854184000c1102400c1c0082c240354045002d379000080320b078114058884000e0091080601 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 631629820 1250 631628570 631628579
    0x40e030403080a02030a0801061e14041a0414191203051c09020901060903030504090f090b070e04051b1209100c05031e0c2502060f0d06080d050d2310 66
    0x140d011f050380030100340941d0b042c02d07504040002a500382c40070410701c0c2c004070b0300d540b9140d0701c0700c6401543c11012814000074600348083c91850000c0050700e20545404001c0c1845404110312000c1c001078603482048409810841900110300a200c8980b290030f00787c0c14401e0809816801c40b4011100307040700c0d03466844c00f0301582010140a80036004514000c02d0450a42e10b01910500c16445582412941d400081034407c8440d880401c5c400d9015000c0da0311401c05030002020f44015034181845036141001040e0310510503400d041c0304103003006500b401c0941d1401c00540c04038001b480d40f5100d00800d048416943d01a201324034441015440d5a5128241002036842040e0000e15003540744c6041c009010b02243e00700d081d503644031100b0f4403900040c0c038425074820300e070780c20414000d40042000c10340800300d50f2110003030300001c404c000e010480c10755030342d18441d90b404e4065400c401240c420401200301c1240354000210300c0032904c00301e106c003000e500c000702c6588000f1178101c044c20009190071301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 631631070 1250 631629820 631629827
    0xa150b0a0b090307060e030a0c150f0201020412060507030e031908060306070804021512010909050f0111030a0e01020c0d05030f0106020a0c05010809160b0d0b031b040e030403080a02030a 82
    0x58030807164028240349507440400c0d5181c440b40920010b00c83c0480a001c1c16070b130208481d10015034048a41050711f641d035030b41e40307001d4070040b05643c010904124204034854414820f80b41101c4480525000d0315466444000041101400341410142c0320070300e00c1440182003000705a4401400411000a04101c03001040d175100684050304c00e401410510401680c0524980d41041d0111401c010a04070032780c80301d1461041200c0d11840403604000060084a02d5001113019401030054a4a12690442807400c1321070300e50b080030001a0038400b0a410072541d0307000c0d2140c5a0788100062510304092500f13850211110b0881000404c000200081e405c04030881900401070781c0000c040c003520741d85e500c0108020318010f0324104038501d0b0024814000c2002440c0400721082c0d01c03904007e848250b1440c4640c01500c14541043c10801c1c1c02046003400603144c8600810200d142e529500b0103000c1102504290910b855203100c10b2001002140b682401050300e41e000ea001142e4822070041e024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 631632320 1250 631631070 631631089
    0x60f142a0303060a050a0308030a0c1206030317090d0f0f17010920040602071a121e0c0405060706110906211b030609071b060f1407050a030506030a150b 67
    0x9004620399070082000230303110015280c006254a9020803500c0000c90110340076600311426106a80c10700d2400000c1c10382007000348520b8480c440000000c3e0352280c000ea507440c09112190710004400c48251200305110b00d4480300108018078015001000944141c03503104000e03080b1900305aa24004480000c800c0c4a5542189860404041c10301d0300d840c101a4880d0254480c1081218401000445134142c80c421103c0d0000f00c01003c50803810070405e080100101200341c044184420004118400c1d0101c040c0c40c111100100708a01c1c14030a6941c1c0e102601140714100c505a400380990040c0d99500d40c083c3c02030b1035211b2f1000300d240d40c031441080c1d64298051f10450b0a800c500c1c0d400114001c0d09000c4a034842001d0390b06a040d920b500303404503040e0a47c031705280400e00c1c810042504000f0b0540210800d01000c09041c048507800e04042158144296402c0c00403d10800c00300d0044c0303000b034201c1d40d441030000301550001002601d031500d0b200c100c60491807006994054425540c580128403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 631633570 1250 631632320 631632329
    0x201020318070f0b130f03060f0507090807060e1206090a1b0506040b0304020d080406050705010b0a0609052403070905100f1b11040f090c060f142a0303060a 69
    0xb0b0035007a10f491180090300c0e42d280202c510001000078242c8120420040340e0004100c0b48000400443c1d0f02d0801c04000c0c40000380042d9101c1c00d160108145500c212104803d44410b03001425043c2d00d0450141d8010188081560f04582000080084881d003801801d220b124428064840306030700345080d401d0402c0c0e0b046806503403003041c0e10a21041d203802064030300740c0301e107a0101540c0303840c1c60000541c40d44e403088000305800400500401e038240d105c40500400c0d07100d00700a2168505100c20005812024003c00000662400c420045ca01d0a4608241c3c44107030041002c142100b55800c0c4040c070390040341c603400440c1020400304840c1c10054914030000c401403a040000c1040c04900602d2407004581c40641e41c5800c2002900340280480d00100c02000140104041d911001da48006803245460a0b05ca50070140030019141c0e018a10520568203640d0342d0000e660124001e148850304000d104100102030901d10100d1140d81d05940c0194418500003542c99240c02410070100140765000b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 631634820 1250 631633570 631633573
    0x1090f0c06080c0a0309060e06090115091a01180906030c030c090510060320040e0414060103050d050d0b13060e1302060702060306010c201f1b11100201020318 70
    0x20008040f01410a42d02c48411515010907000d5140c00c242000d005840d00b035a0203402901d0034440d08400542c0210441c0350400d00645805564822500c120f45000400c9165400314100c01103a82d88905511800d90001c81044101903485403d910100d5034160000c0b1a2171803003038801d0092051b02d210020040160381014801032525000302035042070740d8440d000606d615060b07500d60a514151620701c000d00306104164039159078511152a0355001d51702542d242d0344450740030401c44004103015058a410034000e108001030200c00700c840d940620500da02603a0340300c072001490391740c0c11416043c0302c1c2c0000d80459021300b007102c440b2036110301130100081612800c014400589500c0291803910f901124032527180d58038000140c5116018200041a0014040124084003094181c000d01103c0590383c3c5d16030f0b43e552891f1540b00c4c0c80c00701c400b107003c104c3c070340d001c000703003502028610000a214800420b00ea07040c580210f00c00e20f0b500706901001d82d4011041200b42200b800d802d1404410250 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 631636070 1250 631634820 631634837
    0x303081e06030a02090601052209200a0507081306200615040213172802010507150608100917120f090106030213020406020c0d020604060509030f01090f0c06 69
    0x140060f9603590310050080c00ba415a4002611607805001501c0b04126412100c485a10080c0071030080300d00c050240c445c2403450201000f02a00300351030030350190203442d11000e14129041f0010b4480d504900402c840030312041200c1648401d440c0c0306800140895126254103035241040384030340c4426211b00f034095902c54810002ca070203955144241c1e00b40251001a0390b001010b619251407903403508100b0002442400b10201c1c18000102c0019448440403062050440212040300e0104542c02c081d00180c801d02010001c100881e103070100460081100142c03855980c54440c0c20105081b200041c02d0703550760346880a00c841e108040c0240c820708102c2038501140e00d0b07003141c88090082c042c003080e6a10b10300001c9600000b54004000355400030710070007004032007081d1100a98440d0140c6801400380e00d8080d84c070390034150309000c002a070045c8160700381381c207022003100d00307801c003550095151060b00e03000c0b045000288200050240240300003030600d64a803d11052200c2c441d4080001c00c01081c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 631637320 1250 631636070 631636081
    0x40213090305040501110307140f0609070503031e090a0906091109060a03150f08010c1223070c0602120f0c070309030b100806070e0a0803040506090f010c05070303081e 74
    0x102c101d4044d14003d081440d0300c0700d080c049092460107425402040c2c4580400d0082c0004000100d40c0c0070646c0ba001180c2c8103a881550a0340c0303840d03051143c907030141e0007403004002c05000d03003000b1280149299800d0b8144031b07181c0c0001e140d540003507020880d0141d607403006000b9005540143c2c10850100b030750240c0340400d0300010030201c2c0315010141041580c0c4d03940d01200b09800190200c000c4c00d6a08001d160b0a031104003141c020170315101d01390007080440300d40310b0181844d401240c3c6080120824542800b28040d002e004585005016504201c401d0480c600080d01c203101414406c8560f6400c910340d403805444010f00c034ad00c044c0207042000030a1109500003070b885504001a030340d010051400b6904c03141d43d480083e0340203801035000c501480c010800041e90200e0480200c403c02c540c2056400d6941ca415501e0303100303901643d500100100a410b500f411320340d240800c0b054040c0760a0f0302e541c245440e620300f84050350700102d0026100c1c0e0240a501e525822202d50814503404000c0e0090500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 631638570 1250 631637320 631637327
    0x80a0f0c18080115090e031306020102130603060803072003030a0210060b030408032d0c0307080c0306031b0f03070e07030506090f0a0b0d060615020f01110f031306020a05030402130903 81
    0x40c0d110b050144d03911011405000c0c0c6c802d1003942e5800303078904100d801c1c95071a00c4010303001c2d420041d1342d25407000e4213100c00141075100380541021a04410091840c1062035104c00e200943c80d0100490304060b40590418640ca04100411503683caa40c06000304960801d03d070745c241c42180d400340140e0401801800013245065084a81041444614840c200c1000c02c544d1201a2003181d80d0700030b2940c40c02045400c0a01c8002984100b50550300c050f581c0e69060301415240c00141e030208c1e019801201c454081c4c540300b809401c895980180004814001d08000038074001568000381e0382d03c01c400c810301090320b40500400741c011038101d42180c10362030034001c40742d074140009000d180c4091304c4851001003601c554103180c40d00d540112007404015110000b200002000340c9100e401440707103415001030084180b107010482100c05d44160314220a000c1c1d10b0300280c0000e010700e885820700340c0340c044c005410352000380384a0f4195244c2580303e180030700400c40080240074860b07059074188280a00000e60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 631639820 1250 631638570 631638611
    0x31f060b03010b03130510020328060e060609040b0628030203090d030c05091e01020f0604020f010e1201060801050f070509011202300912130303080a0f0c180801 71
    0x144082ca11405d115103081052030070b0282090030040c2da200005011300f02c002e078240c44040c100c0558421419080345580d41080303c080c3c0c429045188883d1004c1107241c80c00c100280304040c40200b012610149100000c2c140303501c64810102007142880700360040c0c00d042c4400f9600c44900d42811401d40c41d00c0d09000713403540c143d411503804040d0f072112050303587c602a2051300c4c021003010385502001c03105044909030109070f854443c2d02512030754010b21708180b40015500c3c4a1a8043d20740851142e400c401902c4455040c0c0c6204d85c085180c04002940c00024810351008020203c0007282d0390a018282e4880e00c44003030000341c1000b404112802e140e0740c0281e5582100000110010783e03642c14540c036030b80032405070601c0792203548418a0171303007820800d0b8622502440014080d134143c504070b544454110b00c40d4015455a1400600c030030004240141c1543c1c4c0c2c40f05000e140401c1409580f0b02400444182901c01008642010104510f4042c03240c541c00113450203000821904481903103485003a00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 631641070 1250 631639820 631639831
    0x50601021903120207170706060801050c0a050d02090d021002030304111f12061706010e012103051c060e180106060509060c0a12020615090423010605031f060b03010b03 74
    0x90300021700c00c3c1080354256022099040c0e00c56650b0b10342c001447d00c17034041c0c2098812060782d07600f441c0c08540c02c503070000c040b50b0703450a142c0c88040c5081c00203101c11000e9080f644500d40d020340002c00ca50013589503800ca00d0a49241640603580e24134040c0382c2220382c590907444183c0074043c0f280c102c00700c59102042d45062691241412100c02030b201d4410406025580c101e080d049410b404d500d02541300018219058800d11010048a03a03211038a072194120100d194440b44281c40c04140b02090003040100103d111001c010881015000c5449003600c5603640004886103070381c2c041010034613550042c02d4516090030000c1c0701c01d5107059070080a038001c0e00c0c07080c1e200307400000f00c0e040182e0080080458644d803060000c0350400c98031a003e52600411620042e402c64500c01030105031a00300c680350301c2154801c0015400e81d00c2400b40b43c0070b820500004000541d44c40c54049501c1d502080f8a1000d40000d50601180d50704080340c0c8c0c41656003039803004010182c14001131103c445060260707039005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 631642320 1250 631641070 631641107
    0x4061d220308060f03120a0e0603040203030f030a1517010b2d01170106020c210d0c020d020d0c05040e0712030503250e0a05030f070302010305090c13050601021903 72
    0xfa201c20001401451240502603070601c03c401a900c2e03010315100107085004402c1c0c545000050201c818056540301c103d400940c5a00100907260a014a180245410006c5a0400660013040800360005807030960424408010183c4886c107500009001c0c41000900c2950707200300c840d0b154004a440c1842d40700050b0a0000b142c1720384000c0380d00c11f2140303041603035003280c0640c40795940b05406500d41c2c40d841301030750140d01d0303001c07084003101441c400070501454614024240390289500480701751148030000c030313807104102203500c0c0503a980802c5441e030180103041001d191454002000220741039000c8011250b080031400f0007090704461900b25a46800d400d000750f803a42d480c4d144203d882c0c0510010080389c821809400403040e4014122040700105956144442e81c4503010169070f07507040f0b045031056500c8900107000551184d0030164024240c001210b655042d050700141c100d640700705016078030315030b80c0041000c0740d82d0411a56841c801c07079200c004010031b41d5840007032802d4078102c442e1441 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 631643570 1250 631642320 631642337
    0x41802070c1502101401051203070b0411010e1305060901120b01030206070f080c0f0d05071e1407120c091e050903160f12020c0a03030e040b04061d2203 67
    0x2154002e2112401004200500b007045d4211040d1404150300c007801040d0080280780d4002d9a860000000c4a041903001070106065948540d02d02c0c2c40000364a1b002e6041040401c15a00644c03130380c1052143d80ca911100101d40c5190010170311a0b01c1005a20141d424200c0566590210385e04e007403141d0540307405851559031601c640c140782411003031100006060100014503981d8008011449600604030901641c00c031000501003204e5078040c021016183c1ca00005580f4560780020b820ba0143c94407078039105108840c10000b080c20480e480d030200488000c800c0d0b03410704000b044000c4c2806440011400c01070007900d0036110664000c50f001220b03800d541e68001c0307049100300b0425248040b12120404003501c00501c0c040341c0d000c0e0035090444414100254101340751380040303810300000c203014046204c041e1560301c003120000004202d217a00590395000c0743e0441c0c0c07654015040584810800b00900d0480414101b0341e10380d004140b2034441081000080c1e0314282e03812958407a84e007624242c0344 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 631644820 1250 631643570 631643609
    0x9090207060b09010b18040c080a0507120c020705010210060819210f0e010215060f04060306060e340509300f0622031202030705041802070c 62
    0x402d031100400b548215040000240c010070034005080c010300c481030000a1240200074401564031440058021400100000304e41c480d80784d000030b40c0309449140002004640042d01c004458088084000507004203c050009503010824490b203050506030800c070700d514112502c1d4691414800c91501d28080401143c00e0241c1c0c2188562501420541d00031b04460f40507001d040c43c100401e502000c50140600c0450729800402c000e85042003099070240696158000c00640b08030141c11264401d03a0303803001002250161107400050807041c0d140e0b50700d0382403004945042411741c10b2446000c080404803001c5180b02e1421071010014581080c03a2039410b80300018424101905420030224903244422011804c5a0240c07400c01080d40d05803403070444641d038003986418040344c510b8080c00d8403162100d46c0a000e044490b005034080c1c03070161f420150381074251090303034020349612000444c0450305004150405044c140760342c8003c0320441c80c1001070307682c00344448003a106140c00070044841084 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 631646070 1250 631644820 631644833
    0x3120f0403080c0a120804050601090b0301020f0d150e041e080f0d0b0103051f171603050a0b0f13060b0a050a170d050307120c02010b0901060c030216050109090207 72
    0x502031a44641403c0d1204560000640d82d080c05010030b0754110500301d20510213500944201c0e00850300200540b040f0713800c2480c1c034406494070102058040d1f50130000c20701c4056464000e03042c40d2224034004a03002d00c1400a41251030811340084c0601c002880620001a003171100920309030200030621107803c3c1c4241010b1410f40117041070800071510000300130301000d90715446260409000d032004c200d96101d8120f60591440084255110203504010a1107000090310000804004080840e48141c00801122600a41d5a401210240c0c0165614420400100996076000c04050001121403511003c551803040201d5005041156610111105a00c8108141000d0000500445035441d03449030f0844543c200100d200300d541c010301c0513410046120343c0882c2d0061030250703202d00d001145000050b00a0a52496a03010340d9a40d051440304c9459400c8518020301c06620b4000100d46075003000b07414000000c0110303118071004a42840f6a03a00184188180c4031a03400060301c0700306514020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 631647320 1250 631646070 631646077
    0x51180b18120a0624080c041b090909020622170319050703120c020c1302130315060504051510080105030d110f030f07050d081923090102180f03120f 65
    0x1513070385580450124603007000107007100c043d40c02030b05c003007000200341140030109641c00124000010000310080014003420b80200e000580000c1c01b6a03c0c000484255681d1607081c1c45080d02d40411a040030051302541c94481c0c01d420300c1d0200511b107000d0300c0c002d40c2304084403110104814440041041401d05204500c080c2d030492513554100300f5070b0320280c2d010f035171141d2003054280318070a0245800071200f076900076507080200c183c00b112442ea04560741d01443d4000c2014201d0041d40d54030340014966601e014050207152000c4010000c4910319003803200300c5680c40c1105042c0004800108110713240082c2496000800340b415070016176200e6807090804070710002481192101145c5c842510001800030b00d2000c0c4540115038507554000307001d03a00820200d43c4007108084504000541c010190030031300713410340d12403840f68001060845600203990107880501d4680e41c003207242800003201d60b00c6050400e10841c0c40d070780700904040000b40c3d1043c440002c00100c1d01c0c00329603514120004c4041c2c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 631648570 1250 631647320 631647371
    0x30902011206150528080628050405041502130603050108150a0e10061401111f1508060a050405010b0409021302070c030c51180b18120a06 61
    0x1e0300c4d402d4800140050035040c094407d54401e4034400c031141c1440260002c503000d420300c0c54250071113035490201000300515005000380d501c141d420703210000408440c802450103c070310301e000165182c2001e4005088410580042c0010b6000302c0702c0141803040ca94405034046400d28000c1408004942c005003002c3c0005030450041d82048404101e40d42d4a070100283d00c402030361421010064404860303a21202e02001d0f50101400407400701030900c0982002d000b01141d903001140c1160307a00740444c50840100d9100b00340e1542e601c28001048400c0c0240803125504603000d10401c0010380016540c07c1c0d000300341507041507001a030341c4200080140d084008641010311822400d594404c201e540380302000c02170f044c109065005100e900c07000c1c8860815083c0380741000c000e240005521041d0109500c400c40140007200b603110b11992012100c1d2405032402c0c100c101d807140b918030980031008001011180c03092000340d070440d81d4090b00281054203980c0003003002c40c1e0162031041410407400c82108 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 631649820 1250 631648570 631648627
    0x61706190204050a0f1403070e07050f04170604050d0333030501020a02100524061305040609090308100b0f300711060423031303030309020112061505 66
    0x20009000b0039001d411408461100c6e2280c1544080b66003010349500c894040d10800301441c001040c45640305401a00300511581f502a1070140c5900003c00700c0118a42c040000764800d40c200030410000b4040000c030603199040038068120305206588004001c80d000b00507142c4803000644041050840c240019070700700008554800700284001e4450307030840d00f540300a90031314000c5641001c004000c03c41c1103054290450782d04448808020315503001c401c1011a410f40080081081d80d01c5205403070052103501d5000031200c00501d4064100751004000014465944500b04201e001800840d241c075844200456515101e0403000c110150101c01e030240341034940501d850108811440550003040340d0b03107441144907801e5581c070341d484404a4000b010510058503011101a0b904000580c0c046481c0550382401c40300309440340410030640c010380001c0e4407115241c0c10340d6080b841c00b44000d8425401400600d080454025000c21003051000800000080c03030b000d000704498890341c0b84c041c80035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 631651070 1250 631649820 631649839
    0x1309060609050f010f0303090b070204090b1504140f040303020c030403060606080f0a05090c0f03010e0a05011407020a21171006030e0307020310091403040b0c0106170619020405 78
    0x40344400184000c507018200350582d04008981031700b204450b10100c0b541940c40c510000e00300b800c10085034001c260200d80081e11596051f0019580c83e03101481140724000424544131440f0400003038401a0f0540309918460f0004d02c140907107142c120562103501400c02680d00d2007080b5205145125035803000c0c0c0740c41e18200d000705515078002c0d401400389071480c10000c050f841e04001e0604692060303c2100140c0c2c407414182920b4140515140d0880b20f0060000500001811405080a501075400c07034960355520040c0405a0710050320303540100003071000b080030422550300c2d8480851010380300442196480c25118480c0c0c0308038140032100c101100840cd00b42030518030b0714007102c0c1c240558008a802c040c0030341b42000001050303d95190700203000b0803454106035007610080031600001e45040c4507550442c080303644108002c0c0001e06121180690701c00d5030210582c00c4074610382000c45004007002c2468880000054826040f1b0b5010420700d5030021070124140c02031003079900031a0820b2006 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 631652320 1250 631651070 631651079
    0x60a03050313050f01050c0a170c0f0123060307030f05010f0204030f0c080c0d08090d1e030305010b0a09060f0e030f01061802091813061803120908030613090606 71
    0x107919507001c0759020b4134030007901c4c8902e0005440601403101d01844c1a0310070000e039800700c0c1e1848081c0c40a0012140003034500070064039120705042c803140381040169140c00300031031703c28040c10003042d00d8495681001010300f040390000b600e801d01444054034118003070500d402440429805a81240308240701103507a69503a00d030141d05446a024150348800308442e0000317500b00c0102e807840422900400d00580f03040c0958070400d580c2c0298030721542221002c03d043c80020410301401607042c54096070790707030032912601d0020141c81058106002d000010b00c440981a6001108082501c0e40c071b060282d822114032004980e07080d001509268103100340381c2100e0941006521010aa805600a58000000d002c04101c10791241e101055080b94817a000d0044442d4100c2580b600840d0480001c61485420745410050b688180076240702e000c50f40c2594030405400c000c804614100d60b01c01805441c00e0741d10b03006094040100711074024000d4851101ea2103041c1d51000c0007d0354071502c20003e00e41c0300e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 631653570 1250 631652320 631652347
    0x41e1a040c03031e14070609050102070b1006020714400c11100c0516080301090c02150f0c0c03040b04050307051207180e0604150c0c02010215060a030503 68
    0x1244030680115403000d0081404c00901080b80601d400e403919001450000050030070203035404800e00303031802a0345940413400554280014441d03280606c002200504190041c3c2c85c28501a0344030400390b5000341c500300929841d4880905112008641105080e42c0f07240364100006130180451100c032940f6100407426860080200720b0308000f607201040b00c803c0c01c14081d51200c2e00f13000e00c0701d82503200d6020b203407500f00c00c0d4115002201c0103241550a1585180c3d00340c404540c50182103603d10004030051001d25070510411220041510061070000d0010240554540c80134080581000141d00000e03c111040403c84403510804000c0700c1d90380356503c64a48107034005024540c824002c80c4070000d604c1c82c1071200341035426904009400750301c0ca0541c1340e0b41d00d07100704009160701c1a01d58a0707140501e03c0a00425220380c0c0140c010892921041d07014504a480d00600c0c40240200401d056000d41d03400101d00f000c50f03d03070031000c0440d900e581d00043c1d281e640d00e510003071180c4400609128030210 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 631654676 1106 631653570 631653593
    0x6030706080a020a1e021f061827200f010206180a140c01120203090c091503191403041d060117070203041409041e1a04 53
    0x582005840d941c00c005c1c003410000d60022401031000d903043d07142079082a0405030301085420f0400c0d218441c8000e6040010144682d07031240800740320002265401e034003060340703c011480a807c2c5450071091400c20a00000d1040d880c0d0144142e0504060001b0944c1058004d000d059840b000800800c1d20a20328041841c840c0b600c8140200e03042ca041180358103e04809000c40d80700c2c0070005130124200b042c000690034410020400c40d4100840c1c40d030400c4204568003003c076101c10310940c04c0c0085102d112a450300440d02c5074150b0245991142d2120362268035952200a50b6080160f00c0f40240e101c2c0e106000d4a00c54404000c000320001c0039401031050611004404180d07115441d004021503d030005680005018000d0072214540382034200c608407220007551415681d80400c008e4a090307040702c1603148448160070409084482003810900500408551805083c91080c800 = true := by decide +kernel

theorem cover : BRFrame.Cov 631474820 631654676 := by
  have h0 := BRFrame.cov_init 631474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 631474820 ≤ n) (h2 : n < 631654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
