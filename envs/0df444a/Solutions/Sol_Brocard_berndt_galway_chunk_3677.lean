-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3677
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:21:28.978837+00:00
-- url     : https://prove2.me/submissions/63f7b8d1-7554-45e8-80c9-600f7edea46f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 661151079 ≤ n < 661330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 661152329 1250 661151079 661151081
    0x30f020123040f061701031110050702030d1707020307050d080a0b0310020a0207050d0b040807080d022a0d02071401170a0902090f10030803060f033a0e0d02010201 72
    0x10a1001c0a070740020801049500a00300f61008031290fa9032600701d0110022120324180c2c20070f10004251030b01e105030010b00c0d420031001704000c2e40e9040c100242004110f0f0007080c240000e00c0750110001e4100c0e00344240104511044a4104072644021424500643d807000d41c0d446103140e02d28240141c1d400018a08503864100ca0402500901903641d500f000c0603400e00030303405c11a0190054020400e022405060030500c000040f41c01c0901c08a040c0c845846103941c2e035020a40a486106c030170883c4014049590000700301040300d40940b1111000c5400d900e0080007980c02d038403142900710710f0360401c0b9140e000509206480a58414070002c038046d0300140e4400e616112009500d0b10100100406c4060030341c80040345600035122142240d0300da0503136440541c0c4c2100c00c901c04104011043c4045070b00c020296900060260480100c1100316000038644541044d00c01441c1c00d200704401403640301665605940d001619080080300144440500604200740165000c0c500f5440040c0c10740e803003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 661153579 1250 661152329 661152377
    0x90703080d0b0a081501060f11071217160203070902390f01020903010e0c03071512050910110a0905190902040b220b0405120c060c030d05060a030f0201 67
    0x2441003143d05c184150440d04003001800d10501000c103c02095201c10140210f068280032035204c0d0190851b1820300000030700010030b141d0150b444c80b52010420380e500c0030326401455490458584d003140015103104243c54500359821540796103005104072560300001c0303515440a021921580c1d14140d5403203244000c00007243c52081280d00c01d0304020f5103000b0042d40141500310054000b8000d018071404d030113590b00c8039148500d030560320a000403c6049844604400b030000300d4902002c024080450804c00c0d19001d50f0208a940c01501407003a00c0500c522400d200ca01d941c4c0f240700d040100c07018014200d25413522802d805120300c0b02e004001038440da400b620280c0782a100c119100d6440b05444140b82c4c000e8040070b1440b00c4125420100b82c107d080310fa504403066a1442c91402d420721061101a10450011061a11541c0160202c680e100000341c02c0c61101c03031300296243e4030051282c00903075201802c0310380610340004040c0082401103202c03009494081c200024803a480c0410fa41103144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 661154829 1250 661153579 661153589
    0xe070e060d0c030e030a1e0e060708120f0f0a0b06070609140f010204030809060a0507051b0f06031b030903040305060f0a0f050603250f0f030605090703080d0b0a 71
    0x400003510400718146500122940000c2d0703400304443c40c02a000e482e0750744201d00c901801304d1035403071101d410034085c010400c540c00100e240694410032a00c0100c0d800390003981c4100d60100c1c0100d4004c5520b010340d1400796211000003d001801c1c00c285948042d003c40c064100c0b14042d85400c960680c641342c01003101d49482c0c3c407000030007181809080410f0305240320711a442d4280200400c0001c840310500a031015079401c00c640c541b4000d0702d003040160f1548004440c0d02440410b10844000c03034800c1c000c81c140445400350b9800103400d04401c01680c0e1224814a43c0316440900902602440c83c481004184d0740070604166a9114802010b00c0c40c000c580c4000c20034860344003005407400301003a40d00d000b908000014401c80f1142d099001c191070088030780380e0301030744008001c14074121090148200050f07180714003000d550712071141e0346014007150031101d4614250303c020801c12005101e11980405544040d1032038900b1607a40c01003d00c00c14040712091034640e840b2144076581d0740803900042c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 661156079 1250 661154829 661154839
    0x1806030c0c060105182a03090114100e0402060a09051c0515040b070f031e051009020405031e1507020c03151006080c040e0711010e030a05040e070e 65
    0x1260840080c0003a5001a91000c118012500001118206400d603500e8400048071151101d0f52800748980d0343c1507146200040107614080540e822010304030065000f152a00c001080d840e202903000c82001c40041c04005031300900e600200103460f04607001ea43c000e41e0448005030b8504480c1400c07116041c0580143d41e03c00035003408103403285a4800030364009441030003560f07480300c50303405070400240e402c40e0081c01c0400003000240d0707614403407401d0a5460b65075043c00135002e4620b6240540c41903003884903005403541d50341400400601111660700911b5070304025840c050500c00429180c0c180781100440181406146400702c44d414003029982c84101140405a403403d400003d50b51a8400407850003401180c40c0d00303084a140c024154441d01910680b01c15561400808440441c4000d04520480d1f106020100d00716071010b49150240c002692042504003648101c242101d0300442003100710b40c4200134640c40d094200c0141c400321841041c0c4406c030f5a5515800352001c075140003c042d401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 661157329 1250 661156079 661156081
    0x51b10140601321204060515060d180c120c080d021e03160f0209100303080105010c11030105010b031006020316030c050f010903031b0206060303030a091416180c0e0105180603 77
    0x510004007249100d58010103040c0803c0e00e234507092400440002d0b070a1038003c0c40410408400c610399800c881004802052100c090010540383c6841560380c6402202c0c42c403810031854010701510492550241032084054401c00d8540035020707568121440c20015201561056042016000d0040d1068510540800b0402030b4403482d241c80c0341c0304000012807240e6020710101d001c6040a8003884143d96250311a01556400e10b001901c400300700c0c1c042114905440b80c20000380707850030700450b402403e4440300d058803404c140000c2e07200240d0359000401150300520201d8002820058449401074050501c0c98000c0ca031410080e090002144010361190b080204007020560b142c2e100d00a80d6030030f1546400100030f0f8510480c1c4030b600546e0717103aa055005001203203040490303511800155106414001a0a01080c68a410000506601440000b5100d8108846650b070212213a0b241c1e400320080080241441014007010501c032005810400d0229200720408000580361a51000042c04a612 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 661158579 1250 661157329 661157347
    0xe090c070f03091e090f09050a1707050102071a090a03020a0803060a08010c09060e19090f0902090703140115080708090c060f091305040c0b0703051b1014060132 71
    0x18404ca114940c101c40c6420074541c2071760006c1c460b0b80315517a030000c0a000c0e001c080f81c4030f40c4003203c058107201d03101c81d50801200000030740034070040c8003151003140607003071314111000c44000804000700300840942081c0800400282d000c104106502d5105284507100c0e115000070480941468210045641c680108410351513007142d400021030b08255240c41c110181c0c901405003184111580c00707612101c4000034440800c41d0b07000301c0303034488001320009503503112a000140080b1042c1c070044046580c450306071808940600055000d4807140c01c60f00840002190000c1001800905030400c0040d03184c085400300f041445540307502c0d90300400003030700c88010006a1800c0d5100c6400301d44a80b50300f4181010720b0550780034041c49260004240480e075464001a41c40d60b5015030b50403410080c0030451800f001c10f40000e00c00105407107400424205a08142c06030407a018803034156202641d503400c025450381c0c04207010074141c3d900a80350030802c43c0d580c80c101107000300c228140c0c001c01010400c001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 661159829 1250 661158579 661158629
    0xd0911060301260d020312091615090f060c030503091005011e08010624020c06120910050f13020301060302120102030f010b25030219080a0e090c070f0309 68
    0x802104440c0f040780d05180420708103590b078a40409200c003d070700140040d000442c2c0304e4003030f941d00c505840b094590816031184806005281600f02d03100018a814030403e80980c03180075400a400181c504031340c0c42c0e00780600500710409154000b001c0080020010344845024041008841c0311804c0601107540c4440044c42c4003100549140c5007660710b4240051182c605029680c11100f005c4504840e002c502402c1001002c800a41141980704149034020b01e07440c0c0100805408040e105680141d080012240f03060240f03003400f60300d07080d05181c117020039811641c0350180c000c04204003480446410f0310209015000c0760340043d500031407440701100c900f9010740085106281d441d2038881e29030303241c12001a40c0c1c040c01c4020070f00c049001c6040c40e0701d51007404403007012a01900480d0b030b5035a00d00c11418809414000106e501c5800440d0341700c4081e820060002c44044103e0f0000310901d00000c40403801d0081d41c0b000b406004180046106240c00f90304014060450820001c0e003040c40d00d08415 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 661161079 1250 661159829 661159859
    0x80f1c060308030a0c0203090901050603090312091c02150a0b04110c01020703081803030c13050904062007111521071812031805030f1005070e060d0911060301 70
    0x10450ba411704156090107440442100c80c3c2d41e0303000f4100710b403076400c1c130061090941005211071000d1000b00f22a540c10016000450302c1030704120014510031031200d03541d68410f00b09580304001d40d0310910040a08407145400c0b43d03030000c00404001180b102d8000000d020b8554035007008012403001441c96110a410740003890b006001e0340b550f140b1521744008001c15000003146c221456001400030404c0051041d0080007190b0303403560103071305181d15000013990440c000d540131150940d03502d020304190210194200240c40f01c424556083c8a41902c40781d5074004000e50032031280c3c0d2510303042200c404035281603138620440344101e04021040c200b5008a15801a290540405c1e1503190024030310010308010030a543c507610070140d000d403041e40c003610310407003000d003462105040d6000030030940c0f000c0200100c2c440c1210000c04604580d1070000e003c491002d04481c2c100b115210340b9038810303107880d0112002c0344180400012a480241007010040c24070028042c1d01c400004000902510380710840 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 661162329 1250 661161079 661161091
    0x61b160809120601060203040b162003060906061005091503040b09060f1311180a061d040c180b30010b10230408070608090a080f1c06030803 62
    0x40c0800c00c1c1c2d041a90ba980304824860703400141c0c030070401031005c044418041c001c0c80340000e002e950102c5c003613542c0040c860b50b00000f42c64408850008098149030801c006034108503550050a02410800080740340102d21060b010203000e000100100c85490310009415002d54204d41c16480c1e04280c903001200e000151016601803144902241080841412982c0901415503426030030401560b15064450124842c99034484c04c075601c6406a0511012442c2c494020100d000602c503003044600c41003049040da54041d6110840100000640c0003400070050700c440380741d4512035901a0b500c0401900c48010310701d0304482110b042c444c548107841460726081c110183c240000c1490450702d6803c03603402e00d81003a4061014441000424040c101c580f4440072000f00358142040149500881c0e903019a01c0241c4c150b020303280c02c001040d401010181c00070030120141005003e542c5400c80ba50062242c8612140d2000401030400301c1c0c0c45035004081e0b41091420b01015550f07085c412101d400840e00c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 661163579 1250 661162329 661162339
    0xf06020a020a0e010b12040f0204090602091e132a0e0f09060d060c050c010504050304150507120e0402091c06060609080613240b0102070b0705061b160809 68
    0x482d01450050f50035050300c1c03d181c00070b802c0001c804003462507000f0150044d50400d0f1005425000743e212405100d40c10ba0098201503540c01c0c03040e0922000021440c4400b140c5d640c4c0759210883d0750307107024901135903071030307424004c144a584080741d014594000c0068925003282e054102da0809c1e0002c9404002520850344c0c1ca40c200b9038602406102e6a003101c0c0a40c0c0314407603003503807400560164417407410040a85441824402c00c81e08031400c44c0d109850a40780da90010408000803005080a105c446070700c0d2801500780811a590301d501807010780ca0701414020400e20141c9030b912281d0665591a41c000c100040802440307100c0c00003042410019904603040602c04074040e1f0140e86220b08a400403070040150780c1d02c042680310030b003108860480d01c00f000045501c0c22052840701072001d05668000002e8428080d00019241010f19070200150f00703821301c400e80c01f1800216a40e9880096403c2c9440b0031801d24002c10014441e080498101d0740c007000c030300e01c00d224210018003a0a10242c0b2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 661164829 1250 661163579 661163599
    0x4020306070912030f020304090f060e07020a0f110f0607120e100c06051e0108030a1211070b041a0a021e07080307050703030e101b030606080c130f06020a02 69
    0x40c02c980520203805008100b5030210401c0f8000781c410f5200e00315074000d500c10341342002e0f220340c064001c1d103081200303c070450303904c411013400096403c13010b09802c503c85000502c0d140d1080c1e0b1f14103040c3c0b02a180050240d01c0300102d005107907100c916409189c200c004042d00d50ba100580b52450b64141c058000350f000a08141c0309110f41c1c10f14281440c011303800d81d100c404000400d41c0d504409082c0c002c0c0605202102c01e20301d4408180060b0441f8043c00d40b55000c0c40d00c0b8040f204000703014509a000e1800018240849808403841002c2200d0040c0c0d0000316480c0309c2d40d9181081c601d03101c1d000642c8400c044400d020011000301c1507000d092100c150402d8000c1c1121143c150340c00d2805800c801619022040010031103090003a0020034507188a810080740894590400c1810052134481201c01c2948810840c003c03428144040b6403842c1d02c0b42010400d490604000501c4030303600400f031819451000400e5403440380d000300948000c0c2601070104a2140d00e0390300c02502d58524000490040e042c1c02 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 661166079 1250 661164829 661164841
    0x150a02041206141003051009031106151f120902120d02070f240e0307120303020301062c0405060f1c05060f070e01050a0e0d0506041b0f050f06091804020306 69
    0x144d11101120340141c0100a05090744100306e00031704030310108500b80107030041017601d007140078400305200e415080c2d20101c02141010034484007080e0380a5400000116081c18000142c100304800743c001c4640d1030004205985101080c03100d00b51207155016441581c502241259000881005641c1240142e801040d0340d11140302c0f2070114602140c1c40c1c0d6181441d1000708502c074183c00b0013585001011034440c50b5460810641c4820076190036000a50000014410250000e05034820200300c03044410b080030f00c00305e00c1d1881121f4a040c561089469801055243d51000e082440100008102c4103002400c440d211601ca1740c0040111114002e14001842c00c90030700d00f41a100d0f403210b440d00342030809200c2c01115560310482040c0c092114000030283c450300c520441003882c521800c001c100c14241400c2c01440c940c00d02c0d000d14250050142c041c42076103c0031081408a6005840c1034140c1d004080c0082d400d8010880e19940102e14601404802c1c8542c1c41400e00980c0260283c0d20b49450b60 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 661167329 1250 661166079 661166101
    0x80706050105040c090b0f130e0a0c0807091d07030b220b0105070816170c0c01031b0e04090c033f0927020c0703030306050f0102150a0204120614 64
    0x81c41103032a030703600502c5000c203180187e200400b108540141c940d14840d4072601d0650740c0e1001a41c0c0803100c140c1d118101020990407a9220740c00c0003540c140240c038a442e1001400d502e903c240c80510480b00c490000c159214084e411103c0c050300000c6c004148800f205c44428440300011340082410b03410904000015405007044079103668005c2070b81e518028030040711b51581184002c044543c0381c441a01c80e5005244100a0101c981603a03002e0007601e00b000c00010255054805247c3d800050a050305a4003034000701c489007141c4061b503010500302c00c07a0400500c0740c003050744050301920030540351040781004a1003111501d01e4040e40e401100450106e00c0030881d4000144c50045800c0c4e55041c000340c030700d0361019610038202903001144107807003056100998000300c04051343d5500c100b806208168042c0261000303450306030307030a0b141c800410740000d54903009550005192194000801d5920342103030111030243c0781c0b505800c240580d0341d00e07002c3e004090300c602c121044041e90300419885000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 661168579 1250 661167329 661167347
    0x207030905042f04032301200301090b0105190305010e0f1e04110a1502100905060619080f0d0e100c030509030a0204091b0b13031e080706050105040c 66
    0x20000142e074601d80c850314185584841d40c1406403049405000000c0003921a603000881c40b00700002046c0418022440d5500751018a00b0800076661003010401d45c0d04128026241100c0044a000c1400301c10100140c6241c0f09007200001c507001c1107080303102c1103909600450704071021483c040130a07030740724071081d00040e006480303036140600741884102a801c0100a082d4201d8042d00100e44036918400c0002c040c10419800b0108058818003181040341d010310404c0c0350704110540500c0791100a80da001d407503240023001d40c2e101d01c00002c802c040008078140081e001d403004408441041800100141e554413920035110001512401c5407185410281c3c4050305040d91600d071f90130701a11680c0e0656a070741081c50700c582c0600c0b0b40308051000d40d0b12400341c00e00c0079000307002c0c181d04810801c640c10000a4240c1141d040b00391b0401c109080e500d61008894210f07a005280e44001d038034420755940e076514507418040e060100129210041c40035542c805812200c0844041001c19024101669801a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 661169829 1250 661168579 661168601
    0x2070309080d0906081005040e0c0906030f0703020d0c0b071406010501050a0f030c1107030303090519050d050f0708030a0b101e26070809010506090f061e13020703090504 75
    0x710719003013000b585020300c000700e421049010481841c1900c410200301100c112400e0002140d01550061a6908010707800030b030040710540c007403c00320381c01c0c2650541e19281844001c0c047e4000c0c0b600f03501800136409e142800b403c5407141c07460390b82041d030400038200c44540f406100c0074000c5500002c0c1d250f00a13030844041000503202c041910700f000e0340680007820030002100510a00304005420410188886c2001c1c500c40d84000400c0c0401d810018544004220300c090b07400313522042400416800100408802c4c441d00d0050340e1190300c1041c0031603074011040020310450001c0306114600d1081d802403490608282c0d0f001107001c0c00c25034120b5a0031100b0491014207582c41d1703151843c070340c0702d50101051385100005005428680d41d07411803a08408030780110000e42d010060040150003805100c0d00322800315801c0c00300d07003444a18450b10400140403280b01d0701d245402c590600320401030030440054000c100f101640c50020110000c2d6111280480014007030105c0450146052710402d58048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 661171079 1250 661169829 661169837
    0x6040605070c030807050c01110a02070f0b030103021804050c04050f370f110c0a02130203070e04050a0905120d061706040f020a030503040308090f1804030f03150902070309080d 78
    0x1317101c80f101600e056021608540d00c030754a03616408000390f003407001080d10301d4142d0b00600d0304502d031000640c0441c0c5250000d06211038200010405640d9662156008140c2c0e028001b400e6111490403d2800d003151084641003414881002000d2400c01c01c0b0a10038440c2d13245540880b2040303888010501c0102002090004a08542c1020410240d01070001d081041741c000400b0850744201001503007103403006808a612450320401141407054119101c01f0b0380000c1503045050100024121386a04540c8501481c0c0e12000a100c4182a4116078507080d0001e00f0b5600005180d0500f124a034050740c02000d0306401c144001070166090040c034041c0800302e80180c01d05403034503504c031240c1101105080c0d900c20507400c00071010803070504c000e10085200e40e1590b030b175a031460414005181441d1a40034407801c10310841c10800e4202000c060b61103a03261411403840c0d00002410f4008000c40080c41c40c070082c80b0301020604054035402080c25500035164400c2d40340d95524141e684043c0300444c00005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 661172329 1250 661171079 661171081
    0x207030b0603100608030d0b1e0103051003080d0c020f1b06030c070b010f150908030a0c02030304090906050402040509070f1503020f030a15080c151605010c0206040605070c0308 78
    0x104440800150308075100806895500102d6101c4400f42c035899085041541c20018001d0100c0000d84a401c900100c29142c2c501c0760380d0314229080500205a1b40b4a06250b04c90000400c904400e0909a001e0b41d44055007549603048604200c00914150222002510440211a16595000907619054004840610f40c082502428441030360000780c5034000300304041c0184800601301c2c14015020b8604452a48075845c500520304032809080303030705e81c000e00004c10818418401c2c084121842c803c1d007400c0511413600644040b13444c600c01c648c40042e84500d848000000c000840d0440d42c01140200c40500c8103031584003c5c2d1b03403204100e1084030700820f07001c8000c1140d000c0c01c06180e141240d490800606041003011945546d900840f489540c5594030307071459240035910503140002e000014000c0c405006410081002c0d44192031840b2849580071a1401181500c0e05a8400490b03003d0001c1c0b000c40326018000e591000c0c00d80d001c9484604040010765520f100740b03400708805415175900341003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 661173579 1250 661172329 661172333
    0x81f06050702150a080f060d0b011e03060c0e090a060b04060c060626160509010b0d020c1905070e1e15090106090f05030309130e070906080c0a15020703 67
    0x941d50045004a810071540c2c0320103100c0c1500b0401510f0b0031001038a07180d00902e0a03e9041c0f0240340000c04282c42400302e9030081012400e2503800e0760646600c8201f2165040d08543c1d12100c40c00c0d5540014445800c000d038401e61217078804441440240203a48501282e200d002c01070b01075a4a5000d011202441031204000242c03282e19031080283c06280c000401c03680f6400c0c0c0ca8020311140d0b003034440300101010411420f02042205400d11807001d220410854100700003e0740d94001032007907149418020591480600d8558101d582c440100e0301100d00600c4040f0b00810100074084050700c560082400010380400d448414a210784031010b03050607030071207410ba07901c405480a421031104580d003a40b80c8a40e41c4942c01d4603070103460552111001d507440e01c88504107030b542c07540201b8001e80060010320169201c1c0b0f800d800c0316840c5000d0104003410f145505610300442c0d68043c40c0a2400c01a0004a01d07001180342100c052007903d440e651103450708080c2c6402e403880924100181e01c0340c601040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 661174829 1250 661173579 661173587
    0x30a0201140f0a091401030c0f0e01090e0f070201060b03070503040219120f060b0307080730140111071a10270e06010305030f0c0a02060705010507081f06 68
    0x8200c0901024403410302102e1401c00c00503411080003500404c00028091141e0b109940d46980000c81c00d19080c1311507002c150780140040c00800d40017041c8415010003d01c5a8040c02c1d8403000b4080d607001e071402c40d14103460318011001c07090360a20059480c0c03081c04140894400c0c00c803485944940c84551464031346500b8407164040748180e100014001e6503020444103e01802055401c1c09500040a4804e060510504403501c2c51855482540149020030036070030b0108403034040325000c40c0c0e0810030314001c0c001481c0199010075040340d000c140e4540c0004000780d103c0d5614840c07222100810944c04a4000c0034910f105414020b02001c80d0014111154a250341c0c04503407040910b161aa5000e03600c000c00c0c44911069030004410708082c01010f0381c0030300c1900c42c140f00f0b0030300b030001081d90f0752554652036260300c00d20745026400040050704003e003034000c0041d8012150301520403036542150341001c41c0200801d81e0704400148001e00030400c15007014440d5054102070410103850030303290590541d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 661176079 1250 661174829 661174847
    0x2c06072003160f0311030405100c060f0c090e0a27020f0406060302070b0604050106141b1f0b01091a0c1e1c02010c050301050f03030c06090318030c030a0201 69
    0x303181403004000324600705610154001406220381404601c05000d4500680000e00341c0040300b1a660041c0f01c1041503545034400d075605c1e43c0b614180754100054508004018049041c101c805040c10710f05800748140e1b000440004444002040e46000e498411405058901008404441e01c070001c40d00da8044200c031034903c150503c01010b091040c003800000c01c050b01d0742c0368841e10100381d022442200b40b09201c00141e40c80b2800710750070840c0c3d41c1001c1000d0b040c07000140b032020f10740c080454007480d5010a00540c80e01c00d00c0138000c03070b1100c0c69449856541c0d441d500a0706200c803800c0c85c04124841d4042c0c20143c0c03d881109018101168100400a000340c0000c00070510074480c034800c040810003003d001e40390103903154011305803402245022050b0034054811403011a0324104034918590b0388582501d0540b8002c8079a48a0950020000303440c6004040803160140a8003041c060011800001404415a4001c4484100132018109070311800d4240c10b02d90150003400d61800150b1103a0020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 661177329 1250 661176079 661176137
    0x6010806330105070510150e0906010605210118061401020c040507020102090d080a02010c021b041505060d14150d140a120e09010506090d02040c030b03012c0607 71
    0x2505040c55a01c07054035050341450002c0800c0c3e031303400d1f120390422981422400034000c02000ca02e0036080a885450b603e9005201e180c0170030001140d41201f508120034035000f50309000100c90034070358650800b00b4400b0440b9551030310640c0b83c83d400003814a00f800c414241c864058001d002c80b5a40c060600c406000000c0c585001c43d542044150201e41c1c03012011030380c2d04d01601440b074403110041d60183c2100d007c000ea0320150b600904c032000220088152401c8050700558010414109445549050241c0c42d04015444a00421010a250384507840000080c0302e42c0f0402d41e482d1102e04070344c15840401e17144690096401454070000c0f568420021000c024200221100d9590380e8131079040544540501800180101032200d420b0300c1e0441040c0e000d80f400b242e00c50b151009090001d40c002074074040c024065512403072030030500350003603112249000d0054000d1021060f40c1e41c12503081c050a40d00e05080801c1d01d1010403800c0000074010b8800c880a8840c0c1c0c08600c20403820040034101000d034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 661178579 1250 661177329 661177337
    0x616113c1c03090e0703061a0a05040b070305090f010e010509040e0a02030d080106030f0c1b0204110301180501080c030304030f0f060606030209015309060108063301 73
    0x800c0944141000000619500941d02d02a10508103110703074203044000361030282018100b0388144010b07402c0c0c00d408c180c2c08032140700c0700e9919049040103070340c5400345600044c040d0b000402d400c02071580004c018103800d04100c8464200e00c2c840030040d00c101d01c500203e00d0008806001d003103032600382a0b20030005956050304580d000c04d000d42c0020728103510076044000140c848001041490340502502c0c014960180e4103011100310030a0081c40744207c410300c0c540c280203603001c010654981d54007005092900020f0156250707101e2402e00322201c80d42d140505800d00d84400020108004181c0141904004004d107203864519190486050340300e00c41900c403600701207a80c10000300d842c85113500401d06501e000d40c490b040000050b01c21034840400030b44038107400c010600450590135a2900310740c01021410300402518144450403c10120700011003524071042c81000b102c00510507040340d1418085400302d075610750f05803243d1820180404549a034090342444800c0e005400560070507010302d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 661179829 1250 661178579 661178599
    0x30102070210031d0109020f0603070513062613080705120d0902042d0203070912050a05120c0a0206070f05060a05070e010c03050d09020616113c 64
    0x800a141d01042c0310b02003540ca496a802c0d0901c1c203c07820608020000007000080c05a03004200031500300f241c558440c5e2070001c005207020b8040d0003036500034070b2800c1c80306007255259580500144001d0324091154400399400405003000c044485101d4016480540001d5840742e17100519a01321120840750b070701031585000080c0386084080d10002030001000f15682d0981c0c0180310407200b400021940147e4120307180082140460101020b0000206005a40b80d07110723481107414030400e800107884100d461030400f05002000a01c03081c1e090042d002c1d41d501010741203040c4001d110b40500f0b900b15170001c1c80208098940b050203020303d14001c2e1074030030a4541b03560b5040c2c1030040031200d14450f80d540e08280030708a030b400103a0680c091000e081c41040c280d520340b0301510a000b02c21089540586030822102151035820503181c9040351401c0300c8001400900d040300d419400d0282080c00f402030710080c042030b1a002006c01a000404200f0324044228041714080b050141034207160b0400341d003072 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 661181079 1250 661179829 661179833
    0xc0f140d171606150b090f030118050102070c05101209020d17031506031519030807051f02090a03060903030902060f0d0509030a021531150504051b03010207 69
    0x8000c0000282c44161880711001900d010012030b00d1483c04215514407001003402824030410403144c1c24001244d00a07a0305040710006409800012200c0071400a020140400c011054001e031140b5071240a004201540f00c0040c0500c2c400300c44202c3d00000d80e40c0e440042c110500b9070050045600242601c0c003035015944442d81a2440e0b0a803005040750008100300c02c156511400240c44602181c09600e07605100707000e4883c1c1416400c2241c8030301e1407110703200ca00c1c03800402c0301001154011102501d4940c0c40c2040f5844032105805190b031201210b00b624090010703803088652164008002154060550300c0c1c3d180248030b0107008070241945e50a0348005070382d500d0080c1204030010313400e1590b507070034003803030314043d542c0c0941070301c150f44d10034020150155000b06107000219449904070506648a0b000f250740441c2c0c00001e586e0440f40c071000e0120240c0328080500845014a407400f100030711b83e01c401800c480c01102c002d800713600403d55003c00c0049880800b040300c44001c0000d03043c07035099 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 661182329 1250 661181079 661181123
    0xf07050909042d120f0909020c010f1401051c050703081b16080c04020306130504030c0804060f08010e041211160b09180709050402030406091406040c0f140d 69
    0x14440340300c4422640d005000300032040c120304d840401646050100c0b2182040080c000d00303154011403c02940200740002d42400940c801c0c5c0100018890070301c0180c0d204400280362810a00420340104070390704668490842044501c0101e0707a0020040c81030518580f11949142c020f03080c03000c0e51182c0790040800c0d51408011108004a00348814112145859a201e2601d51000f4942e0300450050042180950301c8290351007a0100304440401c0b2035882c1d26048488001b5168014083c020105002c100300d54868000700d140c480d941c403452000d0362100d10a50841030110760007043c44508000c4005005d2040000004a464040440715800d459861104500d078040d0000ca56103640410a8a19840c1030600c00d86441d00b40101d201050400e480000d0416096001c1d06001c0d5400201040c100956580140c0486030000303440788208502422407503c2e050242d409071050170420700041407901c84c1c4220b1b4401c40c2c0c051280550901039002c28400441d072812416030715210101207458544c020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 661183579 1250 661182329 661182383
    0x21303080309010c02102717030414102f21150d12031a04020403030c03110607091412030f04081014060103020930060f0705090904 58
    0x7584004208000000002482e103001d000b410381e05e507424060300b45203040404041403811141c070a1541080491402d061261987c0c607034104200100000c01c000500041240316514bd1f185407041c3c0b103a4071041391048059411840c1459100c000e502d103001c8140040b0b00000b8000642020308038106400d040f003811f00ba640c030580740034044840d44100a081c004072102c0c4441d49000301d55400540c0115226424900c00324071208082c942d803003481e008600200c10a07442050802401950740d281c40b442e00a107410010001100403c003079000f2441090000325540340310390350a96501c20b4880c6810b2440072050901640560055109039107100c040805000601100f2aa8909160340b02d02e85010b0520b00b46051382c2e4004801e1500300580c3c03054a0050341140c20080c2480c025884d9410710000030070a003406500d5584115500c40c02d4428000c84907010030b286400d500640c0c025595680c01c03d840c00804881c60000104100719100180c58102c030714a8120780694031400b4010404140080782440c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 661184829 1250 661183579 661183591
    0x50c0607080423101215240507050a03050a0f090e072001020706090212030c19050f100606090f050307170f150a0f15090e030f042c090607030213030803 67
    0x104c0c103141d10004034840c0c007403101d5508001c6c0504084626240040d001e501192000101103802d451304088194840c0d4280c6840c4e40c2c0013001c0d02d080045901e4040c0050f80040c1c0d0310804900c00c1c03000b6507070b803c0c010022031045500100e01c2e42d00303d507a101d6085662910341c40300c01c022168100d044041015091000d40700c418840c440005d205585401080a0650750301c4845403654001c002c43c00d40f01c500400c030b00c07a02100010040c041290340c0e1400c2400c0c004c85101503007030361050b0400d60329100c3e126000502112201d0701c45800c110b4551220f4024541c1500501da003503449107408101450402c00400c40c45400c103802c1d2407040309400b081034100035171484080c03c0c0c0b8241400344003078512144903051040c44501810481d1a8103424416548011489842c0340280c0c2d51900e040c10700b40a0040712403203544c1405159541e0b4854400303216851a10090f60004507507400c03180314820001c0b002c2c03400386240c0d074000c10b0242e40f0380300c0c11000b940c01860001c0c40b5540b04d80340000010702c24000783d80600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 661186079 1250 661184829 661184837
    0x3040314030307170717040f06020d0501050f0301060b04030b06150307050309101413060608100227030703080702060d09140d0f0f08100806090a050c060708042310 72
    0x400c00a4004001086012515060304406002d0004039908104c0700f0b014001846c0490f80290b903582040c2d4142c100e0b00c44050091400058081a00390156024906803003003103402091107a00e0b0000e0500300c070800c1c0107412510300204424404a007016955aa0010008191000d400034191864000341c109852840120300c1c04401e20045901c14402c1100101030150200a030009008501e0f11540000d080250b88030b0b8111071450030700010f83c2142000d0030701c183c112040c5404e00c140c0b010007540305a41e00d180e580307003800410f450020300b8905404907110003001002401d003162502c4440741c0c4903000c103e170310540800800905142034010038003014003d0b084c1d080e42c03421101203182800e844150003401c10500718485204107410801501c044010761810044a07541d4511100c08407055030040b10540c0705e120200440107c000442d03000d414410010340309591080030901c8003900540d4130090040900340004e00030907403500840241b03440e9a00d0054001e14410000c07030b410082105a8070005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 661187329 1250 661186079 661186081
    0x417010e01060321081006030221130b09010c1709031303060c1107050109090b03160b03060a0b040e0c0904240816150c0203070833040c030b0702030403140303 70
    0x307104c0202d010030290400b4203081d041171911070030100c40030b17400b40204800c0c568003084080300010740d0904004a2a07445480341b0050801032100900c18910100407160100420009422039406014800d0f5580c12504e9001c60f91080043c88480b406000b00255054803081c0b04101000603c1c411010003140941000201030141e4a8000d240794600501c1403850b80c004941001642d900072050340481d1030030080020344a011100003414500c44081c80403c08100308408207404907014029030082004503103240100c0d907183c040ca840c80c0100c0c890100d010305040d000030001164034000301403081000b000002c90500108010a07600c0b2881c62000e90f1000c528005e1080660400c0400c02c140c0c0060b01e001c0503c1e02e881240182c51100c3c0c0d050340c080101e04001502151010450513020f4170300102544c801c01a051282d13190284207422080c20006d40c2d007032800080f5443e906450055420a61010500c0e04503103628040100103094182103200801000002c0b0f416903008242941452020f9540c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 661188579 1250 661187329 661187363
    0x501020a080714091e040207020d060e150421050d02130f0b09060f0d06082406090c0313080d060b0d0b010f05071203091a0406200417010e010603 64
    0x10240c000c9041050120404c10006140c0ea04407004a43e1400849040240c1e20050f0108003c0e000c1d003030b0001d400c0088140c0300001c10009812448081807404200e4a000030140c1c1080582d40703060300e000e0008803a58a803104042c18003c80c48000d84480c0c20301c1444c08400404550483c3d11815207022240c503021820700203c071032800c2581c010b000c0750242c00e04000303400000512501c982c00b2031010030900003a0201c01c803c02c64020a00038600070040d11201a59038001e184a403440c185a1500c84490308002140d07442d01c241c075140580080c08080c0d05650380d88000b490022a650000d447c405400d00402d10703280071901442000e8000d48180342c5c2c69121800882c1d003a40c0398a00c4076811301941c698071a1403245d10505407480540c200088103034024903c1c1c0c0540c01007129050181c0f80701549000f41c00c2c0302d851485018080c61092808101d02c244c492000150302c034012071404060384082100300306501e0b0728403082180c44810030001481c280e0130080e982c03c41d21194422104d0180003021204 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 661189829 1250 661188579 661188587
    0x2105120a0e090106050c10021309060f060806041e0f0605040e030a2604030f03060905040803010815040b0610090503031201150e060f0a0e040608030c010f0216021c0501020a0807 78
    0xf0050100b070800500380b606492080791174628402200d01030304d07030101f100316951034a01740c040c1c0140710310207040061984903c8113018003035560103039001080301e24002c10030314105442200480d6294504420840e25281034007405000b0b01180240c000761034650201d60340d6220311414100740c59501c0110ba075006501c0025000800402d10516085816414040c2c8079180c9060203600a5052502c0341c55814074080c1a0001e106a42010411600d4081000100001c2c00d00450607201040110380030b215007441071400c003840444004040c0c810502c00b1401c2414110920365201c00d041c00d00009007a22800820700e19000940960060001ca1004000700805203a00e02044415442d00e048600403400c00b00d0b8161145402c4900503031400200703020b8403482150044040040200b0030f12210350f0342c00415aaa400450030a60700b940780c4004011900d00b031f8401c82e003903648008410040210b003502005200c100c40d40010401418003101032000901c20710092200202c55110441706051000c0014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 661191079 1250 661189829 661189831
    0xd050a0b03100216080a020a0b0a021b19060b06042103091d0c030417071410021c0207050f060403090906140102060a0c030b03070303120b0603012105120a0e09 70
    0x38019407042010440880c190702c04030071303100c1e00b0140350740d9600c001c09000c81c64440c00c2c40c400b505a940180c00d02181090301c0e0003e00c50304600001c40d03041580303410b480070740f503118800d28084d0700b21715a41c0300c4002800c5a0464403609400901c102e04055a504450522181d1011b00680006501020908050304490030102810560000b03402d401c001401c843c01c4120040d200142d214800700000d410032040540303841107581c0d42c1c141c2580311042c9281050a042c04184c400045014030800304560881601c01d503071101051241601c04c01040040020095114031402d5516000e0601e01c903c40090411466015a01c40d40c0c400300110324104543c4115000d5401c40c411030700c88070045d645180c1c1e00055041d00f11501010018480c14050010380041c540410100d4140c09020b4002052640101c0141d14a054030320040c8138284c1d115040082600c07090050b10f403004203442d1107590482e01000001103051048046549006a036001d8000c580c000e01c0c0c1110000c0c1205d1007602c0c030b5061215170070f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 661192329 1250 661191079 661191103
    0xc0c010e1014010518040609021507060c0305070c02190f030c17120906160b130308060d02100c0501091a042901060e03070f090509061510140d050a0b03 67
    0x18401c50f5042c80d000030041e5451040c1c04005189120124061107030540c07003001040d5000b801207030307a00e1850000744441d400180055902500d807845590010740240103083c0f103600300da600c6410048160b803c002644405c020101c000e2151400041907550003000b90790701450182d0a200c4b103c6141c8a5441c2c034154481c600403074283c0010044031000d00001c0240c59240320202d92130b503160044040c09590f50329200e000a4180000c80d0284403480c60b00811060b0268040e948080d0740340e43d100d0a2003109410b8040003074108144842040700144568861800c19106400101d02c0100640300c80410050380c0e000500100d070f00c82c05000400c81c5910501105600d04282c070f0140d0469142000480072051040c5014408125681d02283ea404d21007480640303000314480c80343e251254004001440c0450f50003040e4420311011032101c501d01c08800415000c0203001840c1100340c11b1044031004403010079210b4051007489544415249401020b00c2200d6944000450f170000384d0801d490202c4040306 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 661193579 1250 661192329 661192361
    0xb070e0a210f06060e2a0a03020c24161706060a0917010b040e06060a090b0f0d06090b01080a05030315010c120c020910050d020d0201051201030b01080c100f080c0c010e10 75
    0x100301c0c041b15850300760b4100d01075508005880390440d00ca00c40c1070101e801010203824500e40d5080000b14000262503004050001004144013112001074410100718540f6001c0e807004200081d48071703d8004018107003d400b03407901005041d030711070300e1003980b1004008540f0180d446008904403801e00f03205a07440790151034001c081d00c0c10306901241c0041005c0c051217000035195001115a84c45100100d44a0301004d483d058070040d803401c02000416009070111a2003c1040002901e443c00042d440b0142c0e4110f03015500d1910340c1040e0250341031070a112036041c41030007400e01c0b0106500c0b5000c001200195142e90a49420610400c0111900140301004240215200340003135114600201000e55043e0340660f010070160005803003d0003918038102c00680f11a00100c10032000a40c114120713582d4000b19080380ba1240c0401c92046a109005400141d4501c03e20b21024482c4102642000902c5402c918120329168001e00351390600180025581c8a000f80341d4140d0303428403c1d80c56110000e01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 661194829 1250 661193579 661193641
    0x130f08070e0708060603071404050d0303061d09461506150e030a0c03050708010f09150c140a180b040609030b040305040b070b070e0a210f06060e 64
    0xc0005c1c1240000340c40e20003000300b4415a181e21324134079811140907201c010041c0e0061501860024082c4c04240140012140c00554994030380118406282c010441f02e0301400715980d500320407d980e0190307462028074061009842c0c925003038500c0390104c03c40740c149410041c403c1c03103030a1800c8118803200c001240180b52440030001c0d4900815108191801440e016490000500000b4a0000052005006d00030014400020040e0000700c1100f00c81c450b000034007000925007104c03c01c80301410390280680c4850208607107684519407082010503024248002c1d0140e0b45032401000d0707000302317a007031012071707501d5002c40214511644880024a0b018000031b203450b0038000024a910030504c0024884200c6001181c2098020170030703500604001c020642c1c81d402d443c1002d1900a009840c40340c04610400b80d2004c4c03d0401540c404c1c04d444004500709511203043c0e00e103071801101c03180240d0f0450103104101c80040c13614081d00008000c00c25410324a8140780c0692465103128008015140d04810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 661196079 1250 661194829 661194841
    0x90103020109061103040e090d020f01110315040e060702060604060e1b0a0903060c02011a04051e09030c0304030b09070605030103031d062101030b0c0f0f130f08070e0708 75
    0x180d454810343d0360a2070482c001200340441c89142d809960407030302c240d118071000c0200014000038000503207180d076400c43d020312003030360031090896091070401282d00300d003000003404005140700b0a8410290140000070018100c2c40d2060034103d0a035207400050704030006101551600d0300541011384030101c6550315034288903961440303483c0280e0424054200100c0c08406a6015000b030000031500170405001004140380c5c001d0081000c0980c00d044240c0d00c00e000d50b8107003014802d0300d02c106004007080d05145420a0015680d40d00106501d0861004200681c0964400c0c07024100445c411481110340781800d00740d503801c1c8002c0740c110504014050004001080c0d004260240e00a005541200704841c0c0401046643c410340700920cd11049520034444840302d5002d0301c81c1200c5c082d6102020325103c100001d0054801c28401d01c001034030500450100310041d4005181303d00ca1a82000d6020b945c0e050036290000055201c0607154101220802c00c000c104a0754662094a514150381685001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 661197329 1250 661196079 661196087
    0x4050105010b0c0a06050414060a0e1501120b04050709150918030504092307050c0c15040614040906080a031101020712050d060b0c030a2303240a0e0f060901030201 72
    0x13080700641102e0702d03140860188080039845808608681c020740c0e501e482c01e0b481c008058000101d0785030b41c0740710380071a0b200680104042c09059035281088500d1002907078075421404400604141c4203800340c1a40090081c5040c800e03807100d40c55950341d09070050302d40090b031411103034040c2455400700503a950440c00640d000c1d040b00d0507a0061000002e6210b92041c004224400c0d01d89043e441d944000f0034072a08a42000c081c0071440241c03001c460080b10f031003042c4003c04148064201380380c0c2d020300051054038012110030401d01d0b0302c0c41d0f429041c2030b17542c24004191001c1d40c0c00000c0390f411000800c014181c0c00201d0301c403a501d06200030b618000c1070b5611640d032201d030340035007108000c404a0004142e07551500140002c0c9020640681c81c1c41b83c00f40203d0300c903070298442c2408200d8907904a08802030007000d1000071100526100c1c00c640d203503584207441800220580307900e407000030300d141d4142d580c1004113030180404070600704652502c50003201a5503c0942001d1055a41c2801000141c0e40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 661198579 1250 661197329 661197343
    0x204050a030807060603150212100b0417010f02130614040317030c0d0e01060f09050906010e060d0803100e090a021311070b0c07051c0507030e0f03100504050105010b0c 74
    0x1010907035556070849810204d0091071a034100030039001c001c13241c014017078140d900500320b614100c88545d50561607030700c505601c09141d40b00d01c8030303502c4042c0400c0003100187d107210660b0000610011914040110f224403c0307a00502c40034041007642c0f001401803550115050090303907031281040f443c050541c6ca54014040d80c0303103282d65196200000207003191400d00b00340d41c40001c403004d080c80800c3c00000b00c03d02030503142c0140f64002403040e100040814442c0103290013064250050403069003000e03407200d2480401050300d600000500d100e0780000d48003100451185090300b1580038851f0408085510190000e0040003044d40954800e002607540c80b22812034020360b06200042c481c40101151001c0e01490300c015182105c247c08000224840c0001803014a1051090302c00c103030a004542050b2107588520140002c406000e03000009005400100d140700d4000d1400131100201c1001034a03052060071a8006103031030320140010072000740101809420b00f11100d40c1810001c0c0005030f61048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 661199829 1250 661198579 661198583
    0x120318160506091302031e061c0b040305070f0501050a05070507050319030609060b070501050702210f070606081b0109061416020d080703080601170c0a0905062a010204050a03 77
    0x600015440c45581e1002248240307100a0801551a49013507102c40101c141d1881102031105442c0d0005105460030084442414803514a01d1002295030b41755642b840d500100708038140101002010041510fa0803501700c114441d500100d1a0b20b03221031f0001c00c2c0da038007800e00c0c414800284071620000e000402510140320040e6800140342204800c110050a50350b84002c0503185002c2020400003082c0c1c0041c0b80040c0954000d00550f11030207800c076540c41500103a401208003506c0980920111340000300118a0312402e01401e20543c0c3d2a614102d82c0f640d806480c995002d0000700f0b26005a07440064041302d02401c061148610300003001d84050b00d0031481d051038107000078100102070302c11a00e40c903403250042e1030709280d552a860510788030350103008190f010840d241c000030100e62041c003805036005403800700800340b600c5080050320350360089101c0b4814007a007a000812507894640c0900080c00c40c50880041d40351030205140c11100000034459441e900402051215440d030816150480c0d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 661201079 1250 661199829 661199839
    0x241203050a180504110a140c0c01050304150c0804020906030703032f03071208010803030103080702011d0d051f1503020d0218010e04020a0501020d020a0204050a0e1203181605 77
    0x30305030040b1104061000d070840c952080c50001c1c80784001600070040e0110700b9454840c0480c00d080c42e0301030380142c0520a02080a68000d032420a9079500c40e50181d50002d101c7c0042c40114141545400b090348c0d04110301800040706903041005501c0c11a551a401c80e40c25405480c07080d06580740205a50440b00000b41e41600c180d00400703021404038081102c0361a070b80242e0340c0b40d4626146c000c4407401804c40c480e000450210021a1805021040302c0c101c1c3c0d40000b4182c6050710503801074415080315248485411803601d54901c49481d00020700809a118030043c04401f524030028001c10124a000d0748400c6182080c1c824529080603903840640381c04955400d00c0183c0d0348001100e15488602c55000c40c200300300000f50450071065114001d9100701c4980c0c0480c0d03100c43c012039403048088101001030b44019000005820554806a00981918000304c0c2c2d50356045e010780d24001181a140c8144c0400008210f21500b40500400003488903501501007040d1034110007402c6011405014419 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 661202329 1250 661201079 661201097
    0x121005090a0b010f0e0105010f08011206020f1b0f1605090603010e0d08060319120c14030403140105150306240a120201031b17040204020904241203050a 67
    0x81101c4050107602502d51030032903840d401e541000b4402071041080d41d84032100042525802000742072030804140d540e10b42907070310b064903904082c06250700645480d0f40c204503080500200b90b00504010140200b000501c94803078031030500d0121040035503002074200b18031140c40010900d09620071107000b00c44e1615540ca03000700180c01000b406101d1302981c42013542491045400c590340c980300f20310880642e14900c500c2100210304a92008000b0710200c2c0c603800304084540119018070310b0501450302614070a1021058070b1031a4030540064822101e84998109544424054076501c10b080301900c45980003200003203555020041d0850045a01401507041e45240000140147e858024901200c1568403030079441c2c0004004016030000c3d08100c4120103401340d048441e800c90300c3c00c1d074a20032040c1c41c090542d4000300c006001243c0c482e03000c02401550b45d03181e008102020350072203607000b601d03441c0409603a451265030380034950f40700750b40d8200703c0829001402da8491100d03905140450b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 661203579 1250 661202329 661202341
    0x3200a0809061614070f060504050108090a0213020702040b0a12022e090501020f0c03060610031e051f080a021003200309160f0519091811121005 64
    0x40390040060034100d203a83c805121050100c6540244000e095a00a80c1c209944803021203903000e8083c001d07940401c40c1048100200c4d40318a040940c0075900c40c003598500718040d40024860015180c04400864021a20304154940307440391603000070701105c44603500341c906105208080000703000a03205100d1181880140d0080b60300107005c600444580b5042c81824407005014000e050095900602c9149060b0003440c40014a25840c450000c2c000c01c4d066a500341000301c0c102c2c501a2560405407a0a810020045480c5c4c00986079494040085440c0c940284040c0318501d021a08000c1c80c3c0b0600010804050082600c0c05220723010b65258520100e4008194040c00001704400410314400903d100b0480454010b1400344c2e82e0581a00c940d101501040351030200680101a02404403800030041854010000458445130084200182d5580c04544086454411080a03031400a9011208205442000148022088501c00c030b0800c62061100d940300f2102c0d164045496448020841c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 661204829 1250 661203579 661203589
    0x12006010905190504080a030e01200307021f0203070e09191a10030902040e150a050403020c1009050108010f030812091906200702150d020906040e0403200a0809 71
    0x1050b044010041c4130f07a040505c2d101a045d0b10917804400080c0c0340411502079034106001d0745400b00c0e003074121400d080310b40030a5070400f17610281480c01544200a84501d000d803000303007003590420004100607220720f003007003000d0311691002100703030711500149080040c1400007400e14001040f02070b400084c1d0400e0328242d01b80403041401c809a2000802691401e1a42d05402c91018540b0a840600481e07a1181296503103201c00102c80004110000008880c4030441d0300450f0300c54001d104842410030014041022a0300254100c800100e51404c288102e50f0002e0180707004000c0041424a4985103071120b44d00b5001d44060484200300010101e0781850301001062010078940100901d4841c0358a050002840b001c47c91028041400c40300b0390001600000f0b42e05e041d0740180c010700e4030f070541588034240e50748403a00c2025415400c1c0006056503c800b80544041c09182c0c1e105c100900309401e02038001c04812400c1c1d100e00c10550440c20401c4004111800050f50060015403601c440000040c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 661206079 1250 661204829 661204861
    0x40e040309050604080c01090503010b1305150d0b040b0709123003060f05030703081c0608031b19081c090f080a1106090a290f06012006010905 63
    0x90f80250040350114030000b0100b1400c141c41001d032100c2d441170fa5518181400d071007031102e0310740d070240c1c04400d21030154606401150f4403a50640c04070703922204002c001100c1c0110544103940510170003040001b08030b015140260400014108014006c0c9484100f00c41651917100042003182280c0c003507501c403420320f0508043c0c29060080a40b032000300d24802002441103204092a504440100103000c3c180802c0d0402070700d40001d481468001c002101e42e20720b000c2105400340142e42d0395800141d81c0014005800c04c04c60740d40c0039104860350300c03404610700a0058001c503902a41d0812020000e200013045031115030007000780c0c0075a8903540308100000c0501010180c07a83c84007403400070801a45400902d41c2d0921605c85c10902800c0d613030001d90b13800081395850001e03030041c55404085060701c0d0740e290050280b0b2410740d080d903812040c104c240803020ba44040000e03000c8424010a90703004010f031600340ca4022800651700c0d601ea84241e65680c4103205000e4043d9440d000300b248020380407114 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 661207329 1250 661206079 661206089
    0xe06011103070b0108030d11070203071a16030e010806010f0e0909070506030a060306050c0a05180619020d09060e010c0b07030e0307050a05010c03090807020f0418050703150e03040e040309 83
    0x10030f00d150307036079884152260f0014032a4000d040c80c0030088841194924207841d4801d030043d00801c6241d05140c0c112100d850540b2160000000510a440070045440b003511160f9210b651400e850000810000d011040c0150240d0f0500120000154466920445000710300da411500c8041d5030f01e0f44000182800700c2904800c1e00b1100000800c095509150007801c1103d1140c9400c20042d503988107004024010b0001d030a001901c00c00c4960440d50b08021041c0181c0801010240341c0201e100700d440c3d00107035000203100583c1101d044405000d0708a0a010010a03d07818011000040c120009041c9005c9039001000614000049883c0c14030940c0440b0340e070320003001102d0741c94050b0708056548420706001160b0035030030450442d9001c4d1080c000d645115a0002c141c5041984c25800c11841840f40b6485030381007070b510f0a0105409664025900c02d4038000d001412203030742582800c42d9081d004052030444c140c00c00d42c49022180c03000044800b2159000b004c0102c68070b032131404071045107642d844 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 661208579 1250 661207329 661207343
    0x30b0402191e0e010906030e011404060b040b011407030c06230a18030906050a03140a0c0905151e0702060417010e0d0f14070b13051203010e0601110307 67
    0x10a81040d4002c0a4a80c0d6150340001140c556100c0d000c040303030884000a11540004c501c03c004010301c42c02600000200001c0d50300125500800560708072101c0346c200d07010b0f9202078a8201c60002e509092150b40701c4514286427620701c9a2108108400a10039a10028100314a5483c464188551580305800d4101403603182c0100310a0003e148004560aa034084841403522411860940b800310070030b60744590544821800c1071400307800b51a0340d00003180490a05031035800040c90003049500451081041c42000103401c08290070040140c6285c4c0c01c01c50207124038422400c003240c0c840041e150581c00005088001c0c43e0001c8142940d4091900000d402650100d4003044a090106a203180105500020056598801499980c62110f450460040380ba8805e561003441d1155901300405a000140c0e00d1400f01683e466a20205044410301405030121440303a04110f0240034078000c00950403409070071941414101c1c0d00c0314074050120f5060047d140014141c400f028404d842c845500192 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 661209829 1250 661208579 661208617
    0xf05030a0e010f02060103050706110c04060b1803032a07080a0f0218060a03060b0d020a0b0408070e01081f09140a1b0b09040504030c05060a1a0406060f030b0402 71
    0x40103040c40c260201c006000ca103414200004092001403c14101e0303410800a105151130038805803001d4003190841040382c060544412843e403298000c501c0104a444070305942c4001e01061180300206070a000c038400d0300b00300311403107000500704115054041010b603165901504000c04525085441e0b01c511014003e0003a25000e11001900c010b9841d4001c2c1d844030103420310807514032481c50049a85690003982900c0900110341a0f070300000b12441e0150220b82d0140213a0001201141c0690140d5126103002038280070118003446042d00800100848107425410000b005031507800400703040310220109100c0111600440d041494440e8016640c90b4400303034221320080d1207c484500c16507558001324020812081c000e21003c044071350107041c40c3e04000e10a400c00c03001d8800038005a081146103c90b040201d0420b00c45c00d07004580c0314a0000d608030380f26041c111b04164149000d40b040d86070407801c0085940002503030150060600e4001595101d14002800a02a400011039100242c42c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 661211079 1250 661209829 661209847
    0xf060b09310f0b0103060e04110423040c1403030f0a031509020306030d180905060d170c0706180b13090e0c03100b150309070b1818060a0b070f0503 65
    0x2e4044045494036001c14000c07452044015401c4c0d4000348520b0f403000318604002408176904560140f5068802840860090b040034074840c0e641002409100303d220072441032004200480c007114000b0300c0b02c80801c01b002c600080c0026120301440c040b030354560b0070000d4032251040c800d0f0700034400301d080350401c11040390300c0d10910802504201d074000e0203171203001c88400d4040e010340c01c20701440443c0d1066050b0f041c1400100c2002e4003000d0412074010300152440720006007221607240700c01d01c241401503151460b120303140b4a895940d601950600c0661541c44240301c60744507100003074070940c02915036265240c80b030003130070841140c0c444c40e40306d4030b4404050381e505d9011402c80e221110031402c80d42e2000c05001800204d44040f00034a074400d40000300f800240e032030600034550020f83c0f407051b1000135a41e944011026400850031040700d405e44490f00a807444c0500030000083c01c003802c041c2051629102282440c20380303016110720b0342c001040300760401c103405942101507680070040c0d9850b03507649 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 661212329 1250 661211079 661211081
    0x40302011409131409010623030c0607060b0108070c020d140a170d140907060c02150a0801171b0603090c040e0a0204111204080a0e041d010f060b0931 66
    0x3144c5505504099403012a110307400c140903203410f0f03c101075070413500d41c070154808100094001500c00c1c1c142c040d203540600380b6a21a006441c185004040101c2c100c00c060000501c20f08005107004144080325400d10056103a04100780c28582e132008904088415640403180b40010407500180200c0100c0003046019041802404483c041000c0500079010403246030b80724560100c0d11012554005a01004001d01c1201b60050603030024000200c42a4200b040fa0b0040c0d01000311000031802110040119010380454560000300000203410a0f8083c01c01e685011000c8100d2580310b0000800412900d02c070a00042601c924002d00c01c004401c800b8100f6901c80b0349155080c2c2c451307460050b00c1c0441c9076003002114208c0316890702811a030382d102d6550310b00d10703000000b1000c03c000c07200d00701c29200d8843e846060007243c03030303040240f00392041c1401143c00c1d40c0520364000b00d1241000d80030080c04100b0000c2e1808031074215103c3c0f010342984003080100e030481d846541c01c90080720b0140c171452852 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 661213579 1250 661212329 661212341
    0x11060712030b0a061e1b0c031709031507050910110601080a03050307120b13050f0903090a1a191e0302190c05151608100b04030201140913 61
    0x10640301400890104070410100100c02d200b120046241624060005c200050b440741400e0494208135800104012102c0881140e0040489150002c2d403414000d000c14501d10f05802d0b0b00b025034162800411201107500d510080d0340380322440000300086000c99008900fa540084400307842e86680082070702000b02440f65445180b8401e02031880089402d00001c2100c1030ba41d030301511441c5ca582c070780074001c50340b20407001c856040e01c55484420050603524040c0c554031050301590040b50034100f160240030560030283c1444d000f0f0b8400c20024980c2d407240c107094011200590150100000d01601c502894032401021b01d1030600030790050486142c010301158105007494000c50503100c81d81100750b00b00e00c038844c07a40b02e100c405010b88401c950320404090401c14403034015200c591108140070303544903a040d10782e5002c80c00e4000404211980c015642d0754800030300084c01914030700d001204041c0380320750700010381006005150307082000d103c2c40c101d900000028055054043c4003840190040803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 661214829 1250 661213579 661213613
    0x9030f03140f07213006030303060302010e010810121a070206010612110306060d1b020c010e1504050909031603170a02030906010b090103060f0b0c010c05030f070c110607 75
    0x22502131807803990400c1c054900990022620b07007096031640d4500103142009030418000321210501e413400f40c02d07805801118011403090720702041040c25440050142c0b074074202040e040240100400001d50300c04200d1030101c452807102d00d00c4d101018200200d2042e0110220080e4058041c20b12071071355400650395048a4040c1d4501810a242c8000b9005907500c00d02501080310084c40400c10a240100050281008201000912031041580c200c1c10480804821016800102410700d080d41c0242602d0305c406001c4a40e40c01e00b02c10081c0610003070055004280c01076151134001842500b0800c1210300c04103d001e15650105514a00200060600b10310b0092000300c0d01e0104044200e1802075034000c0441c04040d0003180e0030044824200e802204625042503100c01001441001d254942005811928440b079034560f2605c1c2c0c12425100c00c030326440304001d400c10420a00c820034031b60303c0e03404c19aa4640f200f002d51030b03410881c059941c90624245c1c4810001413403420014803104508a0f49 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 661216079 1250 661214829 661214843
    0x20c152b06060206040f06181209050102100212041101300b0d052e020a110d08070912021504090e0c12120c0f0a1203140709030f03140f07 61
    0xe07031500b50072600c811003501c008040905480d034200008140e42c01030b42d03803c3d115000c4984840210349a105030641d02008403804a22000d500740100c0d6030500200d800c0c020b500740107500c0c281e5128940c40c00c0d0b000040001d0030031240c1c803200740f003141e01c1041c0d0a13001403240c1700030031100b06c00001291441101b8408142d103041c40c0416013045070501c00f4550f21960707005000ba0001c8042600300120008020400910400804d403485c9484c1c40c4a1002e4021800955070b5590340110303581a441ca00071a00c8094018040036804104405a01007103560036a20401018030085140d840410005103840321600c005513000320340803c0031042d541c4003040c9a40d0100c100d540c045240800d1001130300321601c0c1407046401220403c0010004040100800f5191404842188401440300c40c1003450710001103c15a100141e03070a0500c0c0e06008640030b968030740410800034145284068100e107582c0c84021b102d03a02c00342c0c00c00c0c00d040c02820740600442e0f859001c20303503e03102450040130b26800480106c0f030306 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 661217329 1250 661216079 661216091
    0x13061e080606180103090506090a03111b1003020c060f06041503050601210512090a09020f03040f020d0501050c1e163309060b010c0201020c152b 64
    0x912640300d050003000d014142030f151843c0e41100184a5000c00d007000c0c181519205d0800c0000d10400500c1e00c5142c02038003904044000d45401002004070046460503507200703030601801940c10320322424282e0030485da92045103042c820140d01a01454400c40014012101040342c190500c0d0720080c0b0441e4211000c11018014040092032071105000152082d4080740040c01403000c21541c600400300310405802c015211a6102c3c1e240082284501c14981000b16840343c8900700001c001024100b14501981811103603000603100f804000e00c007420380403100c00568103540358607104407001c5130000300030b000038030f41261511000c0d071103085039401010a0040b8801960541825140b580c00900010b5403441c1d81c6840d100019081c0100311104d00d107010b6181c4104015401d540454040d0f115800700d0a0041400c1020071986060079071070600981040c4a00143c1e0301184050f010101103038252094603c0c9100c041c268003c0c500071003c84070038a102c0d10301c0c40501442c24807038100c850006201e8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 661218579 1250 661217329 661217387
    0x5070c0501060b1b0316121202071401111204030e0604150806191a03091f0b04051005090f1801062304150b031308120906060604050604030303020c01021306 69
    0x17492007a031704100c596411201e100c400091009851080c0e80070549404c80b6666158140a01280e1002d103080701c818038981d15180600d2000e002c3d1080c5004004001414203410150b940410440280018100726aa69030b0038000e03568007040c1c0e00a00000300c1440c00c4020880c030043e02030041501c000d4402c007524026041c4100600740403205031082c40e4416403a189420345151450341014003003250a0140d000743c01306124464030107a08030b1030000c0c030121714a008a01400100c2d00b02420341c2c0c0307000fa031051050001d0349540000365003003040345955140641d12800d40b070070103a410711412080740d4240000003418104070315080c1b40b0f6142c0600303803800d00c0d20820100404c07222010803054011150340c40812207558580b0285500c00744c41092070050a6840c0c0d9003160360381c0000a0025180302c220244550584200452580703c0c02c29680310b0f162500b05000113225005501c0b000b82016000107440701005400e4042da240303042c0c50643e46040c00d441c4c0c003010b4600307203210500041c40808480310280d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 661219829 1250 661218579 661218583
    0x70c030e03160e04141515090c0906031e010f06080a200a11070e0f060103050603100e01090203070609150e0609040903030216060218010203030f06010305070c0501060b1b 75
    0xc01500c03008101801454039a903d032602d00010416158010b0303101c0c3c2442404814402000f140180712031200081c540030044080703d480385401d00d400f0780c032100d00700302c00c0c0410b100c1107500c03030a0100c880c9a2241c0d640c0da4031540306190249501242807071f41d800014140e210503c14020348074a0b44a415141ea1004441c1e0700703e4005500d9801849203030140380c0c02c000200c0c2d00404049000c0c0ca040c017107a40501401500d404038643c005c4050f11069420041a0b90b102042607420580034601070125017042000640c0d60144003080c8902c0e203540724210b8944030003d6100220056024080e10401c1c0e6a404001d80b01030319610401c1080d044004541c8080f038803a1413950940340e0024500713400c00e0044001d01000f08581c501c120141a420000c0301950003000d030f10b000c3c150384100d101581e240101c581a042d000020b906403415948180140000510002c40040c0e12070005c0c60002295943d00c1000c80758a110414050041c0d464400081030143c2210003d03c00301d40403c1151a000c0e540c003042d16 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 661221079 1250 661219829 661219843
    0x81b04020d02160c0801270f03140f1e090a0512100f02070317190911030a05010603120f080a05090a0f03170708060603071d04150f21060f0212070c030e03 68
    0x2401d15521407c0d0040094808025815a40d001f840c1107400c2e42c6910041c400190703c14503408403500400725103c800300f42e841d0400c0c1c15552001440c2da003019850404546800660300400d0b114085511550b40e551808103c00c610600031400c0c244410095034003500001e42c0100304c20b030000b46100d245070000303801c2100303281e02900c0e041340d14601442810800c2002400c40000486e40341c1040c65006c40340d0b81e4104084030103c0d000b10300000b0902e00d140380510344d082c420320342c20f07050003401581c1d1194241c110001c650f22509006002c036059440910290821440810017084100c004103804c0502d44c0c0305105407921000070444007120384070704200361615041102d1940d40040b04000250103540f080c4182c81c03000c00301c000214440800d100c0043d00f0b80b504401510b11114401c1c2c000c0102d284030502903001001d0300030030030709030074902c021070302c3d07401c40d4130710050b20701505d900b284083c0d480150b040381e100f480c0e00780a510b0b00303040401c1d00038410046030a040d0001880020903010b01e28012400c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 661222329 1250 661221079 661221131
    0x61a0405030703080307031d060703062114030919080d17060118051011100e19050703020402120105040e0d020d0e1f0f09081b04020d02160c0801 64
    0x1001c2d07062544c0d480001c81c0d03000400540c20592110760035502c0b180c82540543c9141e47c00c001401c0c0780d14001710020101d5006910002100e4048aa03102028859001603000ba0741c11000901c00000e070000c00c6491840340078aa103400003a00b0701c44e01800d8521500ea0703425128000309951031130b8030060088030344480c210036024844144501044e15980a0300c03c51010200d1b2040c050146542da40000725554103802002c0d010464460b0000148802401401440201143c0c20428140700c1c08407242c1da46101004110010341c000c8a41051000c10000c0400441d8014005d5540c0e5070340150f00a21010f007031080034003540c104055061040c0e404910810040701590041003024540d00040320611303034002031140c01800041c54000d01c0d000e0651010100f0302141c031404651068401e00030f00700c1c1050352000300642c100808605239032030310f1030b4a02090340d0210380150b20341400d40f900800030304c03850580084000c038694490b0200000c0f1040030b0301b1511181c0003003260039440003000c0702d01c4484e01c5e00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 661223579 1250 661222329 661222333
    0xf0305010e060d1a0a1a0a0e0117071509141c06020f07141b1c1b080d02300d110c0d2d050d0506030c03010f061a040503 53
    0x7009810700112140e0f0741070103030b4801e100284800c54801120302c2c003500c20040403504d4411700034041e0000d0a450708180400d070b07100c40f69580b6000301c100e001b62042c0601c01250200c0c901c0c09440e0441040680c0103000b071001d4070500c450384030707030050162071941c45902d03002510341c01000d14602e021082581c261050415551340202c0b5691224000e522800c10070010740001d0118201159044000c5600005400000c140d000892034004a402240b480c189104504400c0c0d0b0082c80325040c4846485954000c40c0d05104404019070756035030030300540001a192103407203542e5a01990019000f62485410568902c030300d01d100c0052004000501d54142a00c0d00170400720a81c101e465010390301003002c0b00440350800c456008441d041c4010100004002983c40c4082030310b41c0d4102000700c060902540304000100c213030035001f41c141c0c01b85040040c1c1c507031b5a9000251b442d1700d040c441c601d15030100400030882e4604001c080c00041030a8002e400ca5092004c104901b800002d00c2250152000180 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 661224829 1250 661223579 661223581
    0x10f0503241504061d0a1a011b0c0b0c031209010209030a0f060908040b07050607080709290307031a0303070203060c0f130303050712021b1306030b011202010f0305010e 74
    0x9000b03a60052102400d5400c103a4032200010141481c541c41540070101c1740c116009802e00a680c0030a840d100341001d0f0380c10242c048250141e80e0000c410f40380e10f5014950310101c81c3c4990a00c545e015000e40c3c095486144001030080c01e40c080800100300710f18103112000d25684070038441601701d0180c40c945a4050740102c203c4c00105a061422040180c4100702c04541560f00b680c54520340d410503403200484502c08103020301001401c3c0219035118017170b80382c1880d03103103080310005209140d076200703161070f212218080fa0030f12440c0202000460350a5010140c0d40d0800c2c50340200142841d01d00c401c101d08811900c0100e5260103c111244e840d0000c004041c241c0301c140c60b440d0641d201d08410000c42400303b06c071640c8001d41804c0300d0015400383e12101d44443c131509040358094162031207042150492980040401c05034011103811400030703030340d044540f00103404010041040e9003003d0300c13106680c030000480d6022062141035891003a0b9840d48003031644603060707007501c0c0b0a004101c12880c0f50700c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 661226079 1250 661224829 661224841
    0x40302010f11040b18060705030a2a0209060303070614060f0607120305060a080a061509021e0a050d06231e01030209210114010f030302060103120512010f050324 71
    0x13074003a051800103480301c102130214101c00552207600094086403643c00c04140a51348540103643c24051a8042c9003240000440564840b004410820000d109012030408108292401c00070b84024940c020020801c0b18046003a82410581c11034180d88952840342281c50b140c1041802e071154598002a10b1a42c15051142600a07003c01000c0c1e94220050b02400100d65208000048006009070000a28501d0145842c032680050360080340700700d401000380c84003e120314186140c4030103e8110103501c40c41c6180d421601c0d441043c0f44d107446141494408160141000020601e000327a11612124543c1da50b0144450440031854100d802c2c0c200c0c1f10703039600650080d0000c09070501e000300141d80780c0814881c6404c105116480150303071b9030344d5881e002c0d07842c1c0076001805001d8008806030000051450340c0c029621001404000c1c00d05c0348040100c100f2074080e00680b028071400580215042d038550000e8cc000324414403a41d4032a12407400f151000000c1940440d00c0c15540c26403042aa0740c0320 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 661227329 1250 661226079 661226099
    0xc1621080603070b27010228120503090d0f0504051306091a100e031207030302030f060a14060d021e1917070c05070e09010e0c0f220e0a0b040302010f1104 68
    0x2c499480c11f5004200c031a05524600f074200500720300c005103c00c55021001d0400d00c41c9058800c8540007440700800600208c5500010f01c0f076506222840c00c0380100c000e0540895084c019075104e03940010144500c0420380c0303000d40240081c3d91910000308500c1000c1a01d0b8840280d50441e00c0340c00c0400e413040141914031840c05823420b4031026003100e40c00c2d40c000d0303519241e65010301c4040c0d002075070110901003150340701404150820b004407442400700d803c14445801c0311b1503c05c130492040c800041d40341c40303280310798041d1000488040400307007102001d0612003e8a600c900c1800001160b8034542280f1307240580c07003c02408614180381640e56803141000d0f02e0313a8001160941e420320504a00140c0c1c18000720020741710f0300800d400031550b1a400b1100920301188034000720b10400703400315102d106488841d50041307000d2580c118201c85006e890380f000300070030702d4910100c0c440c000c000e0240300340500600c150b4041e038805d83c0200081e421041401c4111410072403004001c1200300b104000ca4260 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 661228579 1250 661227329 661227397
    0x120c0903080a090e040f050c090405030421060606020102120a0203040c05130b030109060c1202030c03060108040c0b07060207020109050402070c0302091f08060702150c1621080603070b 81
    0x207141015078030700c4d44400042e0342561048800b102e01c82151300e02d80007045811b002802c4400300a9070b07072400ca0b050558034180c4902890240c0218205415218000000400c842215161700400100240354503002c0080c003075404038030500f250161040c0452030080c56842281e104941004001400a061104101510300100101d240c12074844991406a5078203100c5c25208902c9804000344001c140000038003583c40c1e8490031202e01e4030600421000c1c0e0241003c481c0e001c4804d10780000c0aa44602d883c501400c01c5d074110303035400240030400500704030f41a40186040c0d03001341c84420741c0715612820002a441400700c010047c80b000700c810001800c0506c111078001e42d4509400c3e011f0106d00500c14814a42036108400c01d5002c1414440e202c0d4040c86540d1402030141055a09440c021004116a1141c070700c41e200282c005000010611070050140f441c0e00f00300b01504151200f407440003d20040d01070b600b4a129008840c40010840510b40840d10142035885185554441c010170419070864 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 661229829 1250 661228579 661228597
    0x302010c0611120f090c01050403110315040302160b04060e04110c0f06010504050609040b0f0c0d02040603020a110f100908090a03050d0206091506040e070e09030a120c090308 77
    0x1d1074001541c1c1c1c0510303030009010108014442c01d41d8510f00b116a132a050310000d0404c05841d081110b5019081e68071070300b01e60543c1e4000000c400044a640c012a143c103003c2ca51641100800b01d051108059010806003503045039241d050701e045d500c8110100325441140301e01000310308900d91180003820550461001c040440703140386d0500c1d10188041c0d08000700b00c68415010342000005000c0f52605110340c94011a0076038058001c0e1410307a50750700030104060591075250200200050900c0c5600c0c013128841c400e266402e641382c55031008054041e410a070520004142c0180c00443c90b01d00020384014007a403258000c0c03d003583c0819100000700002c29081d640c1d820304104034921760f121103428000440c821402060440516a4001d0400d41d01403c04007032130700729000c1c118044a0008981e500804202c2d4002000c008807080c3e42e26000c88c1e0340c082d01d0021001810407000302004800b80502c040180c9400740b68a64040c00c41d0202e407603543c090750201e0741514051020030886400b500f005c0d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 661231079 1250 661229829 661229831
    0x130507090801180b1311060c0a08160b07020a080301140102010b090108030a1d1008180a0b07030c0e1f0908120d0c050909240a030b09070b0309070302010c06 69
    0x141e2586002425528440c58a03d140150340f50000100103c0c00e140c42d50003c03124500f01c0d4052890b43d0740120006a14003c24410349000c036510300b0390310081c04481c0b105907000c1e80556450002440c0b224000c0c100c46415680f80c00070700000b4004a00100d50403600030f500c40e101524503030900c00001c0700769040e07914450440d0750703510300203001c0c1d210594403030301a0a5180046d40c64900d140c8005101031405000c07280c250783c0c01c1d00700400d43e4031a4a0351030800b5409083c0394204c0e0f6251078140440e407510090a041c81e100e014801414020302401b518045d000e40e0341d090103513071031091081d10420a40e500c2d0507000301103021035800702c000c0d414405015000c50b10307003a80f82550302d414981c0383c50400d01c3e0030103845000084410481d04284075400801c00c2d141849410300f44800c0016400110040c240103080c44050b1109d6184c1310403400c1c4075404000286407118454807414005441402110111058440c0c04001304216002d042981c2c40340b505500100072450440c4c1c01129145d4030200112146 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 661232329 1250 661231079 661231097
    0xf0a170601051806013204030c090506060a020d0f0512040b1909170f0705071710090203060a050a0e0d0215090f122b0c03050f1b090f06030907030c050102030306130507 74
    0xc0d004c6c000b00f00550060b1601400c1a00b04118038044500207885140b0880e02001440d030040c0d00030234165006203981c102030b1240c1c042a80140c13114414416003c07082c2c10035908100030001d03556111030040024420241c03d121454445030102c4443d180f026081850071800200e4001e1000010007031880540521402c0248075598a0b142002036001844403410700442001807031010418070114800c1e0341001c4c010b144180d00070940b251750183c5003107007903500c640010300700007030680015802041c0d12003180d4420b040440d000b900c1d180103202480400701d0a4001c00c44034500040c1c4422404008005404001070b8011030143e183c1c060400781841582c000394507140c001d000703202e2a50b6544140c2010680440c0309100404070f5030000c182c440c22202603814802c6440c410032181308110110a003e81c4e480806c94000340e011a46201c4c0a9885103000042011003000419800110391042107d007441d03949071401644c9074082200c0054000b45000220205499550040341c2c0181103802c0580c18 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 661233579 1250 661232329 661232417
    0x10606030b0a090b2b0b0603010c1d15040f0e2d0a0b180a1b0e0114070605010306020403021f170a0b0a03051612080403020f0a17060105180601 63
    0x400074401010045e030100c1d0a4450240043c003488241d000324120000c00505015800c0940030300040f0425240108501c0413411458641d0248921400c011803010340e01c07240d56411014074211180140e1403100030400110f1400c00c81c500301c6084048180d840000710369011160110b00350001010000c89580380c40a110060300c943d51111104640307540c500680c0c0c40e00555a00c141c0d94a0b003008140321040341120307482264000c4c20f120b011300003480d000c2186114010b940700b0740d018900c8081c01701468500004108082c6600400c2181d2081d960701d90008004030b460707100389295694800c040303808849030f811301c0025291881c5d840078070b203030000510000d20000304481803043d070401c07901e95010307800086904400001100050080300403544c407043c2035a65035a4117005522000740a2011410505070503640d4105a101506544030030904020045075890b640e110b080c400c0700d0140703d49810f105100090401c0151040106071201512398070040304a003001848151203a84100b0f1010541038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 661234829 1250 661233579 661233619
    0x6070227070206042001081f03080c0703022e0c0218090d031512060207082b0b0108010e130201050d020a020f120702100509040902041b02010606030b0a090b 69
    0xc001c0e5080d60040c1601c0c90540307800c48034440c11490005100e802100581a03982e84421369a41c0440f01c01341d071304040140001d410307d0150140c0c00c018a41c0310f000c41d051020300b800250440440b802140c6044c00044400109000c005e02d85151094100d22000c1c060042402138100301007a078800341c4a5006611504e150004101e019200b6400039080f03101103660184d414042c8000e669a11043c521000389014a0142c0d4401c7c2480c00600e010340100b2203c1c00e02040c0010b88592002c4800d248040c8101911380a81c84803100313020604061030490b034030240b03521800d02c1505a46ca240c81445032511000745100c081c201c4014100d04108040200e03610110301030026000c001c403076800800c90000c1c1201c0301c0e802c0c00c2c0c007061401d6007490309025a20245c0e40d0800404070082041c24882c1c0d43e9420318000c02c020702424080030707401a0614403490410030b10460200c140990341d900800482c0e0712140200d080d2064544002d500610b420030074030606580d40e003c001620342c0105529913000341404280 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 661236079 1250 661234829 661234831
    0x9060c0f12020604020f0316030201110c10050406081e04020609030a05120705150f040209090a0b040305070615061e0309140303091506030d11102901050906070227 72
    0x203070041c0c00c140107110031030800104040c540c0701d04901030008290390402d81d6403103050b244006410420b00000240e036494090051285280010b40401c480e00d55011024181d5809272140c0c0002441120003c2c804002080040c0380800c1039a041000341d032120b80801c5115044440d00300e0745400384140500001d40100117074500781c0d1040340c0c80f50703c3d511641080d6041c00400704201c0c038418411030030050705111040c1080c1d40b107a4101d80310784080d103030b03440c906140160200d401400341c42560300348414541c0003400351040c1031003400c09010070420b072502c4c0c4e11100043c0c403515022034070041d440d6002140c2001c030410044942c1c5400a02ca8038075403101e10400400d4120015250000424810002030920040c030307005030040388070580760408002090740c42c205580000c2c03c00080b040c4049404c10180003640b040e002146c818031403d440c15203003404071003000711840340d040c4048020081c154024804c0c1c0c0d0300003100402c001d080101507000c1c007071790f0348000c0d40c0000c41510154078524071140346a211 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 661237329 1250 661236079 661236113
    0x91c050f061f0b120a0525170109090b0601050a020f01090f12020d050d0207021f11190c0b030a02090d0b040c090515040e0c030f160509010609060c0f 66
    0x10805101d0003541070b1084850780c108600c954000c10150500b00c00c40d540458000e8507900c0c2c009055a01d2a032214224400b0841c032058010140c820744400d1588402c14945003294501040d0160743e030742030b0320030403990601001030403080c0c0300c40000c5140d0b0141c0040d115540150041c0da201c0182014407900f101d40d411022902d64001c0d08040081c040c0c448109503144500d40000d2107480d9050b107000d005401a05000c00180d0f0b00010380c3c40854440d580c0c01150640148040360300c000396450007500440700c0800c255080e218114040d131070141440405c000084e08000301c422441d051440300b500340c5e4402001e100c0810b0f000c12002815171581071146001d20b0103030b0074110031802e0a2814101860f495401a40c1c014280b80500c20080320404607001042e030100c400044010001811605102c0d280003a00e40c14000c03003076001c2c2a91f074003285550200c44010000c031065a00c1c0c800700a0701d44002e00072000040c040e4401807141b94040c00d60360b48214012a82c034000b0300419038440c04145008140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 661238579 1250 661237329 661237351
    0xa031103070f0e1c150c02010605060d021602101d0609010e04020714070b0c07060302031e07201f090c060c0309030c09140a0c120b0604050303070609030212091c050f06 74
    0x8070800520244900340e00e1b15818070027481424500390000d2814002c248000241d564002040c0c6002e01e01c05aa4101c500ea02810401480410b00006010807603e0408004000b04003829441580f403c00112154504141c4903842c8580481d8240402500055000c40e008510b581545100a0302003103484010110142c07040d07034840111031070b0b40c1000d117140e22240c02c1c140140203020700c08080e04d5891a40034003050328900380703035200101100c840d580c012647d006c07020700009c4c054601201081c0b444041105821900030407500c40da680c0111241d43c00b0160868081070402d0201324442c28050a0050180c60108005c1c1c5e240e44500e00300c054503610a100032030b03441051001e01480c8030301e1103601242280c01040801c1c00c1c9140601403401c84000c140c200c9a441c01a58000c1c0d6446d03007640c0c0030300070241c100c0c1c2e120a410b281c1a0001c10201c50160050320940020740e5180c18840211100560050510712801c0c80000803804e9902e01140100c4850044c0582e1070f0003580200070b036070710400001c0c1d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 661239829 1250 661238579 661238603
    0x2070c0b071202010504261306050c0129090c0d020a02030315062109030c07030b01051c0c09021606090b0610110705100201110a03020a031103070f0e1c 67
    0x203400802c07078010354958025641414104404542030b03540c421004001400e094510450280c1030703031854400c400540c3c1219890990201c4c101c0d41c404083d00700600800300810602000414904401c0107030790762543c2105090407060101c0c1080900f058101c0b0840b41c52508000a801d09041681c10011024005a0020040004154031a9031802c1e1418081e11841d2514658509959403084100c2401c10b14101141c0450000f500820890320308560040076100156101d00c0c00f80c2c1d0401d070030b00c500c0f031041105103c115005580055040c280546c8400921055854100690041e4000c0032034240d02c05402940400400c450703000c2c0b1110a4400e440070f00b124a40f00c01040101d03c000494881001044070f10301e40c4400c0005041e82c00e40b002107806111121503010228003401d40c500c011030707010178046100441c40d5050703009070841401c6a1014804900c0200840c2603d0004444500001d0f004800f41541e090045441e10701120b03002e080050f1382c1940c9001038500d0492110100d414190b604 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 661241079 1250 661239829 661239833
    0x70828170d05061903020d1112030d0f060906060f0e06091c0b150604061803020d0b0106080903091c1a010609051c020906011b0606060804110a03030504061202070c0b07 74
    0x404c1440d440a280d002d02c1070581c2540c010516590030341c1401040f54420015450041d504c0303d801080101261044035960b1401100b1070000d0140f00e42035101d264100100440c80300d02a00426041e80c003550303245030003c0868001252800107001a164000c0710410020380140ca80b02201801c40c2c081100308052900b49140500b041140201303a140e2621240a030702010b0355559044400312703015403420160f240102c041d100c40c6100c0581c80254818a83d800d001d08100021024604880103525203031929940d0b2a01d15480784600c0c07800561103400340340c088454102e048824010b15018009201c5c55404007805002100740070382040021800e243e004011b10314041c1c06558024045660910030040e9990205881f80405001113051060b00c11020b01e8039005940c83c00a00c50b0411028420141d840b1009000414290781c1954000c060801d0342c00c0b0b505050002d00103da5050384c0e454039240c90803070102c0e100d5a00c00b180c4100c6540030045074010904480c03d0070702070300f29070318104d80c2c0b00320394 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 661242329 1250 661241079 661241089
    0x50903061e130606080a030221070302212b0b0f03150705070f110a080607020d050c0705041a0f0a06090b1804050f09070828170d0506 59
    0xc040328031003a860307014030307103030007800041150010941d0090140290007490880094405500103500314420b1551400070705500082501104030001d242c02144540e400015555205d151030290142e405001c0c103509030408683e0482c2c070f9603142c00b0124100350400701c00c807002d140843c8a8000c00420404000290700e418816034680510403070760b1b82104001007021a070ac88030180b01d400f07152078104001881241c00707403040341c101e2648100440d40e80c480c0342c50000c01613011301c61058005c40d013408001c07807951000500c5500a4810340c0003080c0407164400103c81503805010708581c0d034094000d0000d01500e4500588480d842c0c84035840141c6a620703001c0c07100c0d0844a4402c13a100708856281000036582240b2148180d41d2038010980ea1920301002110701d41d40d00311501a0445c1c03800041120140103002414052120001501c1c030580d40e41c4c1d602d50b5180076044031200c0e0380c1052449031220202000320200d2151181105003040d5950b40701e0100300e034103c1321034485059252400c0026610309 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 661243579 1250 661242329 661242331
    0x6030605030703021305060406030206120103170c032205271003030903030509061309051f051008100e07111903170402030f190606051c0305030415020a05090306 71
    0xc01d070020401c292664001403420000c1da15071511603503484000c540ca9458a42041015540281a142e42c1300d5007940c480305954400d1009680303030b2040300c4103403042e000030808445044001c54003d50400302d28204507081c0c01c441d215004c09400c28500e00041584071b181450341031440d002420700b00302500070303051030001c0c000800d1141c0a440c60241440000e81080d50034059a0f098501141c4a9591030003265051103200700b0501004451500001c0880c00303600524800e080070100101580f0700c01c5d207000d0349684240201940040e00c40f8180076100d1003072440640c4010b45014601c01180d81d011805040d00c8192034000c0003a00c4032010000907002000000c842d09504449180711184d1520000e0035082e01c01e0704d000300298540c02107000d5580802103070034089100c9091303400d203940c0101c901c1c0140d980020100c480b20b00702140040da03894100e041100340d403100d5101d141508810380d0700b22031551006208a42c5003403a003640c4442504c262025281307401c119215079035100c10000815243c840 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 661244829 1250 661243579 661243589
    0x801065706050612060106200a060b010e01030908030a020705010b090a060807080d090611011e0c12020304050601050d03050c070b040303080121030f030209180414070312050d0e0f07060306 83
    0x4104130002004800008032181110302600c1c0003d4650246014010300840c5079400c0b000622803a181581806240c0c4d0084052000036220030725100413000c019007c0da40449409030aa080500001d43c1c112002e4008055441c440c0b00002482503ca0000400c800c509480320040256940b00510900100300a220054110b60008081e484824030f4000c01042990040c50200000d60401c0c00132184250000c0b5243c3d546048000140300c082d9004000a06401e041180058648542102d482c81c0b50b20071280902e410001811a90382407105114140c4075510084013002401c0100d0500801c0c24407075803000c3e10303802036016030300c07403843c10300504601040c0c00c401d4034100c01c2440041c010070b0990700015156070504000008030202c503002e400078018402080c2c4c102500b6146444800b100d05001481035110748070262222004510340c1c0c0d40d03101c10303020081030a0700b116810003000703004201500c0c1168150030b002c1121501038280380d061a0425080b0203840d48441000e00c41c041d010f0080801901c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 661246079 1250 661244829 661244839
    0x80a05012d090309090e15070e0102070b0a1704060219090602211306050705150126120406080402130b010c08030a0e010e0a0308010657060506 63
    0x31a80d00a0285281c011007005088070703035803165801058003641448004201402042050078480c4070515100d80c2141500d51191108000207140b080c040c0d40c00741c0170f1a00690040c04024146940903104c0c0e400164250107000c58010108690302400807900c3c8240d21401d00561568000340c5800c1310141100344543c148450810188009540080d520200003c401c40028034030007810307042c0c950b602c41d500d421040c20042e5180230800b00c0e042801040030910036801c41d038000260b01c0034908030940c00e010b202c00120140741c10000742d20202c4e601902070603508040e20a49040d010070f01002d54055400304021a17201c0c2e0402041d45000500813903000a02e039810b00504a46c540000c008401d20304008009405c04400f1074a0400030794403110b03006640701c008001c044c2c4190100c55590b40c2140c021800500d098002150007440ba04200b00100308000903042c007070907207160485da40003004240c968031140c565090680180184211a203207140025207600801076403d10805851009141c64046c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 661247329 1250 661246079 661246121
    0x50304030515040b0f040219060e030c0a06050406081005030a230a03050316110604031707050c0601030809030309040914011a09040605100b0c01062d03060b060d020301080a0501 78
    0xc2000700c000c05034440b1181d10303c0c170166501c0d480007441000e0b00c2241c500194040e0751020461076003002074982e10440c100c0460b1180c040d40343c108482c48800e401002d00242d0188000c00c200e07401522990340017124000c900350a25241c0010a1030040074400540c1c0c060701c1e003900000d581c0c020545c00c20181e03201b00c000d03107983c0d0060384000d0074612005d00720201200c0c0c0800c130307102481d114162074440322079800300b514040e04103410000c160615184001e802e06000034086032410740180100c504407000000036060503861a128031000d0b40045824a400d40410031070700c100c0351380798420310808520406050b400748244040c05801c5074040c04078000d480000e10300c9016260340301600c0320b91043d030001001c1881d5a4020243e41c6000c403951110307460301e01c085502c60b161201904440d0030340d00300d0f00281c0c149804000d405024400508205020f0030700d400014004555160004c10040c40080c140302e2030946d0101349401242e100b64004001034003c40404030402c4001c6c00b0f11503244e240388070300e0080c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 661248579 1250 661247329 661247333
    0x1090602091f14090a080609070305060610090e060d0b09160506040e010e0901090215300f0403031b0215010b03060a15090e0a05060a0e0912031f0305030403051504 72
    0x1000411800310f000300603011030044480c1d52628198800b80c109941960540e0800000c169a59800c9001c12141030107100b00048842c103004d1407640b8a081155540d4550614050302c00012401c042e1011740c114042402080100d4510300d9140d01a4440100800e907042d000c0510020020150b005148904010082004884265400c0f241900c8283d040c0306a039032180c0ba03a06006244c481e00080d04803110860680c4100e00303c1010b081c0c00a40505e030104001300f5407007000c01148140a2004c0041c1282010a04000340018210f500a101c3d043c001003115000c0d40071100b413010f907400c507401680101d103158400f4084501c50360040c029440d40c5410350418400099007003c060240c0143c505d50301907040b00c40782c4540c01d50030003411080b4007581c26041812106002d41f0701110414004c0050280008104c8114215580b0422203900a0a207400a070075413010305031700241400410504981585c00c0040241ca2a0340003180310710700560350307585946403403401d00000407948002c4502e103104001c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 661249829 1250 661248579 661248587
    0x80708100612050a0209030118110924180c0a11030a0504150314011d07020607210b18011d2203050d05040b06010201061208090411070501090602091f 66
    0x890807034040c0c00030441350f580c1c01c0c45100a00481a00680c15820304400c1e103214550a45501c00c60b078000c18144019004a41c14420706034000c4d1665550b4103400426862488250011600c0c503000081080c4084102e0656075424a0320541e00d80c416103000003042103c640c1c00040d00c42c000840d00d00034504003080400301904900030307440343c59820350b40c0d41c00f80700c041c5219520051a0540c02c03031040e41203503101c0c0000c2031641d1090341c0d20b5400c03a04107404078a820b0300000d00c4d98802c42c8a0f5071256450082d80c0108900142c0c0000398a201c01d4a9130702c03ca5a179620f000e82c4141c9100b141d18805415071501489005c40300070340c00580700143c100c00a002a0408030049d41d103412414400226850f2020b240c2203400380b040d80741d90003c06240c102070208001c0d0202c0881d00900e0264004e120709500da41d07041d00d1403010030a0052181d80100701c60003072410950802e040c01c0080315051030070f020a0351605070075168410811105160b001a14156500d070592004102c20004081c03550300c1d403030f8090701074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 661251079 1250 661249829 661249847
    0x30c01050a2106050f06090307050105090f030a1505011211010507110d111002030f0706090f02090a0b010215070807121b05130b0c0604060b010c120807081006 70
    0x141080340024038000310340c0c010502000358450010441100c019030400c408000c00441c01050710130282210154072500e480400e03542c050b40d000b0060710189280500549041e4403018000c1e40000400c0d00c486640e40d010700a5403002409001043c0b61120105015000c07180c050304502c80d95181000b48401003407455294001c1d01e002820810b80d80d0000c1c0c01c1c58480c3d10101801c01e64131602c45004001001107401c9440818141554002400d03c036580050382c5034021009220710256080c0f0a03140403440c203422000010303000300c030301c208000340d0341c2c010803044241100d6080c1c11030340340c0c900d101c00c030750b41040000c0131070184034003a40c1c160500c01d00040400001070042c104000f40044881c8048032286d10200241c1241685482450010729003c2d240350090010503a90300013610001031554519802c54a4002d16207025101c1690746580309402000085c1c5103c0c108148031a40d0703000034186030031039144a1495190074044c1d2070700000081a0217001440760341a9080c080041186a811000030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 661252329 1250 661251079 661251103
    0x30703020606090a06033c11040e070b070618050102160b10060507061508030d0f05010b04080c0d1a01180b010215131718090c0a0207030308060607020306040c1d0603 73
    0x100b9036481d90104807410b08005002031a480002c007414150806c80c20b804481d01d403400270f035400d1000808280344d180d02c48002d0710405011003420484080001c0c0c06a005804000e0441d451f001005000c0e10f0741400c9800c0b04443c00c2c421004048903106211000070b00a50144013803400d54038803418140000c080d4081d2410081c443c0b0b450309550061065101046800b403e221b4045946805002081c07001400e0140c01c030803900c600e043c0011800b10100c0c8101d07404d03036250600425400f4003560a2020318040607074155500740001e151000c8a01c4e031502a40d008044d1681962120040d0ba0b81032400c48503d0060309041d9401610700039165800e1503c090361002690b400074504000e02d0505500c0c001c00c84500c1d40c1d02c1c003c00144490415618104002e25030401c1c2c17aa0366031a541d00408100d5441303246c107064056441407800b00300291250551a62080018119604000c2a6400300c1e107011026a011203010b80d1061050116604100321000e40705403aa01215507030a080010985880c0c0300356079 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 661253579 1250 661252329 661252373
    0x512040f0b030c0721110601050303071407090603060f050a05040b011a070503030c0a2303010b16050f060610090e010e0403050714060601090905040b0f0711030703020606090a0603 79
    0xf280b0500080070384040340d0300700c0e14800c1d09190b250b074803143e0700d84008242c00c0030898112a811080754001000b46c181c1d40081e0086242900c6900c1d4800800c0b41c0943e45e02d40c0d4494000c020400003428051280118843c4101261040e5080603140990f00010a02e079116440c000401021403420146035044a080c0d061b0080380c505076503420301c624890403801801501c000030610540085480042000402d543d480d007442030b00c028019000140c41c4001110848001c0c030040c0483e011040080c900250b010307640300890760007691210309100040050038480c0d04200304128060070408100141d4151070314050080a040903051203e980c010b000b0034514221540003d003c16000d2400c071050380d50001415910f198020fa20190385e00320442c1c003180000e165110001c1c5640c103070700a0714011644010502c055542d0790302c500b800020001c04850800c4141c0480b4890307980b00340300070982d4600990150a181c94103100b4050103000217060021224649501000810b00c2c5500007100d5001c0401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 661254829 1250 661253579 661253581
    0x102031911011d1204080a03050d140a02130501020609280204090b091005040c060c0f12090603060506070c150e03070f080c0111120c01140a090512040f0b03 69
    0x1101c0341c24100d55422060342c030b0300c0c0a680c020507104180310380400f1428212031802d1164000038840d4080d6224030345507030f88001c1e00a000a03002d40060a007520f0f2000000a5400e820a070382452020140d0b03c503d6095800101d031260b542010615102800080c0010212409c04081c5140d4071708009004620071803401b100e02180039400c0d891200880d40081060000904d2404c0c2116202025a080c0300c01e4466010f0200058025009852040c1c1d08203405960340b42ca005810789000050003070071207441c8580302040c000a8080032902c1400c0f01c003941c5040750f6500302500030381258100e030001403207120140460800a16541036603c1564030707050210f540d6044a10301560440031040c405c2c0d506000d02c0c0030100c0d64683d242c2c0c2403002c4440c0103080b103001001010040d2915032182d101e1070504e820010380c01104d0701a0070000d0000704800000000c080701442d000d9503030f00c04140c5800d80056116503004c2c0501c0f5003003202c61080c040619a403072030180707080c41013038070f00388148102c180e812800b01c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 661256079 1250 661254829 661254877
    0x13051f1422050c040e0313060305190f1d010f0608030412300f120911010807170a0905070f0e010e0c0412050709060b09061b0304080f061e06010203 65
    0x2c4180020f00c1d0010344280081e5089001c03007034a942028100381103982c1c9400c0c1c0054100c0c4030340502c0d4029043c14050100442d100c403c45805001035001c0451915250368015004940d4821503146004a120002070380c02800e044460580b1070a40c041c41c2641c1c020311041c800303030342045054007502d03620480c155615890500c814001d07400f20307000c80070154151074120200036000010a05030b44019038403e0400c0e000b01d501c80081b0b0307110510241010403445850140d0354011038840381c0000b01e5041003503140c46001c01102880104035140c840740390b1075012103c20010b08000003405018404203101c185030801c68108040f9805114042c50007480c0e0300824820440c442c00c54018111071070308101480002c4c2042c65850301584034100750149841c42c00240a8031010550b54400c60040c4014600007008048007003140c2101503048641c0010400040c50920811808180d0040741d8040c021900c0c0c56141c01ca0811440d2005201652034072080103156030740402110240d01c0d1000126201c11002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 661257329 1250 661256079 661256083
    0xc0302041a010e06180909010203010f061b02040c05041806051c2f04020c061519060305041505070f030e0105040b010323070b090f0607020d020913051f142205 70
    0x901721140c4c0040e411030500c001c40506400440c1170701c5e40069200100ca0366903500326030400d49800b907840c484603a102c0b19401480c1c1030300481004d4030b10340b40540c01c094407a5001c140d10401c214080c0d07403440c0c0d41d28003005282040420a8401041200060403116080d1561900ca9805009078000e09058007444107e22004410708042c1b000f001d0310031516107030641d121541e941c0c3c00380e400b0448003e24a0600409282c0f1500844a00000c840801c690a01d800c0040d0082c1c4000b0303008550350111801c00c0602d8251500c6081d104800302d0f91360f040f400c0ea5040c0058111000c42080e10072a904000170003010030414400141100d50004022110301c85c80b840100c5501d4002e4a4040c4c9400361a00010710b0303903400405404903e8040319038a0780840702d442001600d124039100250408a03110a14016103024005160b01c40300c444412503524502d503a03464100040d5004d4029a40c03449003102d4180c400b036115010034241c10a03c28445030520075000c1203908440c0d141285480c0341008030074104003007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 661258579 1250 661257329 661257367
    0x61d010b070b130807030926030d0c0908100903120218010e0112050414070506130e130807031d0402070c03080901030f090b07032003070c1109040c0302041a010e06 72
    0x13004e6420780301c490b2440c00800720b1f0303c2c0c1d102c0c04040c1d47c018850003020040550440d101a180c0200452508130740c466850081d001480703005042c41207804002405000500110030505112140003030120a54038014040400384151260402e205001070b400000c80c40c00c0e80e1714003540900380415100c4c40030300101c49022540510381c80c45800d00c4144010848092543d90324a00000c043e5480952103000744015030140040070343c4980d620020400c0038002144105400452801907210800c5903130312512002d42c060401100040d1030020050309500740700f000b100300c1481c00c840c15858480e9a07201c401e1320f00d0b07540c00003810540000550802d942e00991041c500d42c00f074504144008110b605024800b40012144c1c000424200a041c010b00090700c850a0b498482040356a41152a2001d0407141010a008115111a88502030701d20650300d02e0450b030320480c400e00d0440384050551041c0000c0e91548480c04141e141701c40200c04280c1e8012080710200101a503003d0345a503480401c120301001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 661259829 1250 661258579 661258583
    0x2070315020721030f021216050405060c100605040903080a2c03041404091e020a030b090f0c0604060207090e0a1e12020c0d080d0b0402040801061d010b070b13 70
    0x907403443e03810200340912143ea041e149a1420091341c803154661130107034131400c0c0c42142c040180c5030000e225003042c001c52040e0050503181160400351101d000c59003079030119500c49416800310f9001d41c1504020f0142d100038200564040c84002c200b981d0180c00824085c003c003a40503144d0004100401d0011404690800000512502407512440300b03502d95119004280085801038021041402e11307010340032400e40c0c1700780701e03000a090444116140604d403403000c036071020100500202180c40c41c540e0900680d41d400180a40700c2542c151640340030318000c02c4a000d0b0400740400c100c4c094000c0744060483d4031007000469034032601d034141820165240d00040c4601500407a41040c00c0304403254a0380390384100c0c000d42105900003020b07640c50400340f03040ca41c00b1207900e5a2400046900c4047c1840c000901030100b0200d41000c0043c00340d0300f158001e6200c036907440c0c00c00c0140b12003041140d0f024590a070511811941440301c1c1461500c50424007800100101020030320fa007810f00111b011040e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 661261079 1250 661259829 661259843
    0x1e0315040f0903080f0405072d030606050907091406160501051314070e040602180306010314101b030b031006090b0a06030b010e090601030902060d0c09060f020703150207 75
    0x40000012004100402c4107900050309880018680280003075924040c9030040c005151480c0b514807400120060261400140c1e141d10f03d0b86042403800c0203424014500c10203000c549241800305200e04c07024018000f80821040c81310800844501c070120003031a24041c0c4e03403190b403884544190703034000d00d2080006110358038120030031201d41004101031400c07911844480d1440050700b50015a140481e000d2174043d40312070404503000600b0380e4000c010351000c4804036100072020b140000e040207400d9005076284001c1984c408503100f4180400c0591149400c820030a54941c21a06034040300c00801d01c000b0705544910348415540c0800450780342c1e07103200d402031111035216405070f4040c02d909060319010340d07a205400300d01980039010b40220700a0680d15070044404800030042d11000141285050507a0351360307130340e0241c3c64500090103007203440700300801e001355084401802054240c0c1300d142041403003d501c050151307020841c0c0d0110780d00060700c6524518603030b03e400024400d104000b8424 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 661262329 1250 661261079 661261091
    0x103020f0d020324101d040218070f020f030a0e1c1b06031514010c0c0f09020c0c0307030f030807050f0301030501090215090a090e010b03010e211e031504 68
    0x5a40d19860300156180600d032481d8551240b0b001c01701c0250203801400002c0045e541d034140406207100c1e8455020b80020403002408a50140e580c0801c1000d990560010b4000c01240d11800c0c0c04001c2d03d44031003100f01c0294905140d107034000300516001021103110306d6908d040340e64907000c03282c6c2070b000b601c0e0000841c00340560500c0801c410215284030311000700707040007805040020714480e56411550007003050218000c00b14011600c1210300041250310103180440414249040c440c01e0014002c00302c0010380d0303428240d0031540380202c44d4103001d00c80e500130a001d00000340c801c20100d10440d81402d0500c002d49a208040c0c0b8940102603241664039404400002480015004451b495000791000c240c0410a80e045100078441c0c02440c0303810402c2003008200c055410303402140700c18244030002814003000b0300040c2c255003564540001552003c1e21400060500098001d841440c03075078801d00e0000070307009907604002e42c840d81d1034000001000044007102c001880e00c0c29038500610400c44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 661263579 1250 661262329 661262353
    0x51c05010b03012904110913090c0807060e0901081903030b100503040b15150903030903060f01150905090c0702030f0607180806060d1421030412170103020f0d0203 72
    0x800402c150868804140501c4e0a50641024824582c0c0050340064542c98100c2d5401402401d5007000b0860000c2030342d580c04400450105003001e409002140043d008440c60b01c1e00007086003200e1420907200303080c5100100000301c000101494002a903140c08030044059040c250010810460300e00c0d00301e0707125501400078684c884011841207201d4040c03111240c5400040001c61040d6a55480d0000b5101612134300c11441c00c40034240c07c140090880340b074400f000c00400d082c004160f0310021051000001440402030041000764190b419141078076205190000158008130040c00c03070154140e000541c4030540d1800c1c000815046100001c441d0507060400300107050f40b107a000e007001d015130300e01000f00d0030795000701c1c0d03082c0640c500916400940318a5210048140d000b061315007000d2050b07405142007412100d580350214a9084412a01d030715042c20441c0d03244020803074030401c0200503180c030720707030b00401da4019415243c05640c41801124450007080100b03451b070038040d505208141460303003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 661264829 1250 661263579 661263611
    0x604030813060813122f011a060703050409051009020a0e010e0a35060a0b10031e0509030c0a0803010312090e010b0c0a0c060809060709051c05010b0301 67
    0x40b90150f5451104680e41c1d10b800100c5010039503401044580304403031444104e84600c08152580c0c3c14226000b188001d0000007134134100c0e0500b942503141c2d44a440f01f100b002088088800061410f4030035034074050003650010041d1181c2c5c000c00014075034500c00700301c441801c0e41925010340320900b0304540d51050303400007800d2080e8501000c0d0002d00074032030318a207504000e80500e04680100b0304443c00004a00c44c182413014052180c01da0390382d00164491086001007056030b000b80480c1d140007c40000a00500100e4404a003282c801d0505001e40b020041042281c140301d000711000c0d00141949404110b141544941d2a02d070703e552023002c6107030b42800703503c1000714100c80c030480405480038540c07041507031901c5c11880340c980b4401c5190010410194884001c0020710369160507610a10f1107940c13003c4611455400420005584078104694040200320b82e5410542508000d015985401d0014545500c2c800a0154140b0156165410010b09401c04014624014001d00004002d0380c0412 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 661266079 1250 661264829 661264867
    0x80711040e071805060d06150f060509010f050d060503070f0e0a0c0215070207050307060f200c0103020c0c041109010f050c070e061309050609100b06071106040308 72
    0x40c4654505508801001c070300160450403241c0014004001161080c0c03014003c1c28000c1c802c2d074101c0303802d0449a0009840348614429041c0c400714807082ea0703040c5844017140d00c1c20b94105d1800e100c020010040c4582e00480303805807024507031402580d50800010114064242c5501444e0184540c010100d0f403180c0540641050340d4190010f0909980d8100045003030b160ac07100c1340d0025130401da142c00580000400883e5102c2e0b054011203403140d6840d00842c1c644041070340018001341040301040782d495171101c101f0840d4504e1038001c0b03a07404a40307499203440c1c80c200c01225040c11b500003010b1101420500501411040040003040303410a0500b900701e45038031554070760340040c0700c170780d001001103000700181d8444800d08402400250304000c0845040400a0160f91703000c0b030291040442c1c6165400741c40304c070703e100b0800381c01d107410213658141c0351061014070003640758140840301030389840b81000e903400702c0c1d00b125800709001c00d00c0011902511807600054003285001424208581040d072000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 661267329 1250 661266079 661266113
    0xc0a021e0d030e0303010e0408071410050a06360608010204030606080c061c020d0b042301052403060406030c030807112d030f160e0a0504080d050703090807 69
    0x10700002c03e4143c2c1c020b44130f1009000d201c05803003078080400d000c0341c10369000d015000c0c803d00d030340442c2ca410300c0c442c0382c42d04031401511014103485d18100442c007482809880001d02d14060320941c88000c0344000302c840c0da41c0b203804240300c091000e204115500150040d80041908100071540c907030b16400c180d805400c3d035014080e480c2c8030312a00307034125050200444155101018481550a40c02d107001d5000c0e60101f00c20a04054852001d903596541e540304604070021400902d4035005030180758442c42400c1640320510461901c02c1030f4060401074085d103c980b0086025440c0d82e42c0e078100004000340781982000c1c10a04503004048108a8060010003480703006840c01e40025401601b0440c0800342c4042d00c60700c82a0058071a288200315031550444058000d0540d02060420381d200c0c1c2c64030600500000c0c803403451074420040d0314100500c413a0854aa1070741440b1600d041e0700c2d148040d100e40c00440d0311155841c2c0010340030354402c1c1d010100c0c01d0307481000d1980ea44c0c2141048000b1034140b6083d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 661268579 1250 661267329 661267331
    0x31b02011b080310080d12110d02160b0703050c0a050309071509140409020f0906030c2701081b09090f1b01081509160c1703010e1e0c0a021e0d03 64
    0x5c80d00b07040015039503401c29056516144609030f038040c09006081307614515040c0340002d01250200810900190030036008522483d80c543e001030800c144100005070018051515100c18000a4002802111606045400d01681d40e48860400314605500c2c1d92203d8402051384c00301e011401c0d0b1001140d0300b1038050003614113440e08007104002c200c07480710000950240d460b2402c164142049100b1302e91245005081e03800f070701c0d141c5004c141d010385101c4019135128403100d00c4600e192200c141203405851144010300400150003100000e050300e60803000e105d0b400c0d503800960f041e01e08001c2c0c1c504441003e01600c1d103032100b44403030468205e00b100707515010448440c0095043d401d01d0041c1d4003c5c0c84000d10740d41c071039111464040070810740c50790b80f8400c004e030342e0b24544042002c4040e0b106242d04111903582d5650b1520b03070302c0000080040c0c801202d00503034071102d00100328424042a00440001040c075901c0790f030040240d01e000021040b1107124224280304c40083c0c203022500c546034641d9900c2c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 661269829 1250 661268579 661268611
    0x4061e030e10050c120403121802060f070c0b071b140a0b0f1b0a0c1a040605031305010c0f020f0a1a0901020f04080102091c031b02011b0803 62
    0x10058056404001c140710881d8409000e1400100e000e03080306401040455041d883c1000b0341c16000403d5038100e40c2030b8007150390b418403081480e10701e10541b9050124414a040310780c0701d907400134500d842003c030f1203402410301251240c10b000d620810000100241940796641701c0d07003880c0250b0400345481a901c100c1e41d0f101030001e00f081c040590321412082c02400c2340006420009420026000079100c481c030b100c001d004c000100d01c0c11a808200c0160b1400091242c2d000d2464211503141e8180c009208100029444480742502c16090301c0036030750b41c2d0901c40d449544d001800341d0480c46107003011b002e543c20000601e001c9a0859000f68950308035500703a541c07110a0010066891201003001080301d003200081c014007191541c04541c100000384005483d0400aa4a041040c3c0042d00080d4450f580001c107950303549800520040195045d1103107820024441c0c50203042e4424941d00710a1401540042c2011a8030a030343d0102e11040c9240c1d000f58159107801d06c3e0100e90002c95061880380b14001c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 661271079 1250 661269829 661269887
    0x1b0c0c0b0a020a2a08060a11090d030c03030b090103080d0506010503091009080d050405030a0f03110d1a091603051021050307050601180c0c020102100b0303040b0406 73
    0x40441d406070000c2d070020b0146024903070740c805400048000706540c01e40d21034035039081103015824000040034650b00420007424400468000c5030a46119800c08030010480c6911a866401a04104c4d94160038201c21901e078509040d805401d1214881d64404109000442005134480c003a06806c03d18510810440d40c4090040d10548019600745209a0004464405031110354114400703040c491154181800440c001c42d20580e84159400c4500343c0000c80d0b4000d01c642d201600700c10400040c0340502c50b11614100c080054861440342609060f2201c0c40305155012140092004850140c0304089524010002c0500907c183d8210303c0000d06184c00b00d084008944111416591021208603001031110411280c0210a0a003107801d400300307000d0031000c100e06001003030003000f4800025030100250003000049511944802c01407050740115100580d0303000400c5c501e40c51503003c00203041c80380f00b00001d2550090790b20100c1d4a9800043c041040b0303a1112000512400824841202c1c0301c1d09 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 661272329 1250 661271079 661271099
    0x280617060402010905061b030a020c0909030301150e04020c1006090c030615030c0c050f010c080f040c091109040501080c04180f11130516091d0115031b0c0c 69
    0x1e44010340000d00421050200b4903050340203104c101310050442d055034051143d410f00795008000200301603040b186003914103040400c1550761141c8244080c500e55814030240449030030f030000300d4070304010309a0305002d220744490341200c3ca0302c0c4801c0c0031070b0218280f4054850141c0040d0091494850802c90341c45061400b03401400241c6482124004001e11082c804600030144a1081410820424035850104406020406460203400004104804a0a4064410080500702440c00c404000407c40400c0d103a170310f40d02c185c90412401184102e41c18201d16258060300340f60f140d04c1071508000140c80d40d000100000d40030010b860900c51000d0720000d04208004034000078000003403402d8083d0014102c030b9002d030900540105003400710342010008a046820031180c101c00c1c111000110368420fa0004480d0008102102140c0302112120300c02142c45501071044402100801c141060070600a40081c0703801212114144070701401c0c03640c0106031940c0c907001914000c03840b9802140110030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 661273579 1250 661272329 661272331
    0x6150602010c0507080708040f0b04031e0519020f060a0302040f0603020f030c0913020703030903110102131415191b08032d0a020c070905071728061706 67
    0x40303443d00c0b030130258991214442e40e404404111240c031020080460b1a01028a0310405401400c003600d803182d040d443d00d1440340141444210f00c075080ba40d55040090790015000305048a40947e0f80c0441d0030034400b0a510610380d0580b81e0703001001240d43c0068550590241044584004010180603a500425400c070b200300401c9080325581000015403982e0741030010907080c04050314a012126241552504982040d9000c400180c0c490410b2018560300440301044e0407145802107181c00503000c113001c0c6403602c91240d141304080c3e914441e2040c1d500d0412400c00301c45030700c442070740d100d80b4071002c11161401c8101c24004125070000d4420700035640d03c8842e810960020401d0726603181c00b000403101c1c00110001d100881240303508140d00010400445004850f030410140c2c44030600c4180c1820701704141c01c034503d000c0c58441082503d81d40040f4800d0740045902c02421540c407441300d80c04444601c3c20103035110100c001c0013a004400c280d4401000c40d084040301c840f078449074503481603c50070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 661274829 1250 661273579 661273601
    0xb0a030e190b0424090602031e061f050c070305070f06050f0f0c0c0d03050a140726160b1008010b03060604020c070f030b0906060307080a12090806040615060201 71
    0x18020b00058001440007001c0d81503000c1c8403100020740300180c4014802d90b25a1481201c3c500d8020040c003080d0306403c294a101aa004038414049240103401302d0f09100101c071248035008c0d0300310104240b950058007111001c440c060140c4585a0b00d81c101250303070300310500c15812409220100010001e00c500243c1e20210f0003c21024900440000c20106a402c249400513030750182c820b02c4030259458103840c0840c00c1c800e13200c1c2038a400c0c1c010005402e501280810042c002e40070400c20000904c1408540091441819072189c4001c1c07028010040d401100c0301903a02c1c1e1407003d00e080610030440320980c8645090b1040381815902c546913142665110002c95815610210100e8510f140a801811400f890903049030485650345218440d50302299100341e901450303007021f11018040178488240d200c130003540104141498895031a40d00e24101a010381000740300d1102840d482d100d02002001454a07904547c40ca0811342024001409a4110200d5900040000180003401800ba0030b0803070b4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 661276079 1250 661274829 661274843
    0x203030c0702042d1409030c061303031404050c03060606250201140f09030c04060305060411060405090a050a0e1603031409120f0709020906041e0b0a030e19 69
    0x1d25a9800d000240c03060115000000c40800180340d500c412080c090ba0f020076201d2404240804030a00c0b05012440150400800c0d420030840c1030030484000860541105180d1b85100311070708030b820110010040300c9901240901c81005100c18440d00180e80541004124292103840d1240e000304a0548070395001403d082c12401249a1081e410b400380b06010784c0181400050344414200241c0c0c6c544c070181c9841c04111000c2203811071070034100000c840d20030059504000c1141583c558a0760741800402c0104804440d6045845a4030b4070f1054400030100034005103a2030400c0a90440a40000c50b400030907140b400560904103940001d200d00c2d00d091580000460303038107540b0102c803c0f069504002400800c03c0110240710785130088080a0118000e02800100c0b1902d2001d900781402d50b4418400540140401005540c510b03040741d0407150b015406400c150411107007100303102c13000c1e40404404800450003001440d05070300300d50070400600d03003035400300b03000c484090340c10b01d8481d50003030522 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 661277329 1250 661276079 661276087
    0x8032b091709010e130c0e041505060703050708040e01090e0105060619030b15131403060112110307030321110d0209120f0d0906020c030c0913020406170705010203030c 74
    0x1240c180003001800c00c1890b080c000c80130324030301254440450b04d0110480e00d03514074100c084c1a130300656029081104643c14003034007100213501000150380d0300a00d4400d83d40028203000300741c0204221218940c2c4000000d4031185c0d921504d405254091140350344990030a01188000e96043c410070b441404010240c0e800c110300d604402d00640301c41c003c0308050658401150781503a54461006186407211b500c003d40c2c640803c41c0e40f000c40d06082d40140c100d10307850340040c0707450340d40458030038190703241189402000540703410070301e84030114030860135014083e018010040c10703444000c401c19110507641025064107032800744411900301106e1000c00040601464040c088150002c00b8865402030611b04540d10f210241420042842040d1030117600c194406806150009000c1c0003c11041c00608030300b800a501090702c0c1c0c0034081c551840355506030005101040300048848130701c0d0b00500104203464644e0034640e0341000c0c008a02d4041d21500200103595880001180d101d505031071206401c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 661278579 1250 661277329 661277363
    0x50a080a0507110313051206070903020d060912020a020307140609040203060301060806160215070c0b07090b0408010b18040314130504020a121a01200708032b09 71
    0x288070140000040080904407461041001c10140c40001c1d030b008030f11542c40d4038100400002c1020082095800d030003174406c0040072500117250204076501030700e101d50515154500741c0d004042540000388440f8017041400f0489500041c50070443c3c0c400d404540c0310507240c090b00840301d02c2c01041d06511000400c43c104e07840c14180c01460308104050b00225146403070b40881c5041002c111a0201ca0b030f1031010f08640000e034100448408000c001000d03440c00c1c145000000c1c01c1d2690018054100030700700010800c800d00c6010410002c200c4072020a807156218607100e0301806464101d07130301c9280700382401c80d40082d41c2c0c0c00c400d0040707602d9100e00794110b09a01d0000b02d02c0d0072104035944454880c1500003480d8030f0b82d000400d14030340e59a4604000c00420650501240c0c525108500203c603000340c2c00c00145d07003000500502401c40380303d400755107401c3c40c911071604501d9004603540d404003240300f18406403400700800c545000c0c090210744210705041090300f21049543c000d40891601140000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 661279829 1250 661278579 661278581
    0x10303031506050f0418020f3606040302010e130608030d4709010f0315090b18120a02010e0607020109051c0c0c140312030c040302220608060f010501050a080a 70
    0x6201c5081b40005400c080280a400103103070040c0d036083c05604d09080c0c4600c5281080e0382180c82182803a1680101310f003000d804540e0301c0c05107020081c1442684500b41903195501024407800300341c0c800b402e00c6603903115200d80b510f07904132142d0b00030036904040d0084480c00b905040c0d00c180701055401414130400c1d05400c0c4015007903401d9506440715042c4012000d584805540b40c0c0a06030b414000c500b52450340c5098021102800e07403004182e4030740360042d00000c1c203254819405c001082d01010212000d010010704210707204000d500314600009400c04001e0b01034110411a0040b40240c51440d81d80c00800e900341c8090034001030540e04462501407440c102d40885501715120342c98151000c4249544400d2017030000e410210602c9102d510042c07851034108003000703003644103460b024207604012048004074011400024843c280965000800301c0200c0d110114a4000c508284259951585401e8440c501554840140c8412000201e415409081121103e00e61079960700000d50343c540d4850 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 661281079 1250 661279829 661279859
    0x7110d03110601080d120c0e040b03010608010204080d030b030d080115120507170705090112050402041803030603031d091b0c10020c06151804110603010303031506050f04 75
    0x101400968101c05805090820165002c2c0c0b6804c80282400702500b08041c0c0602c3c4401c0c0d403c1000d900381080c2d0b02c03015900c005c0c0c0c0f01100318251008102c141030303000081d003d4003582d08840b00e6507201050015207108000740709c1070003900c1c589007000b81025041c00e1545448403e022400451039000040004000703200c5002c41c60803a9292000c1c12184000d14207040e1402030b5001000650100c0a034000302d18880d170081c0d005000d9040c240d01d01050800084d1290354201d420701c640d541c0e5440081c2c00d640f41c0d900301000c18503c40b0b90a02001c1c15519000c2c005064a0000740d0000d0b20401c100300303c0c840b41032131120800a008040408565581002400d080e44840300c2100390f4405000d21140045e0400016030116590400036855042c1201807903c2e01d24010242c10108100719100d003100e0300c41386030f08201600c0700072005d03440741d0359810001160328094042540122001000006259050b4401251442001641e50406548204c211243d0042034070017460540700b04400c01ca0b44010300244 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 661282329 1250 661281079 661281083
    0x5150408060117150c28140c15070815030c010c06020705070b0a17060603060109060c030201090f06020d14060127050a03060507110706021f0222050102100207110d 72
    0x440c0c5050214041c1e601c64013068410a8403064003050b44200189621004000091000182c90841901040c0103050302c030074418055402d03000081210940e04148110b8950050040d800d030201e081c0000000c00d0290226075010b4400f1181c0244c4001e80f43c085004685240c0507980c003400b01c205611a02c0096118003800c6071980314031880014120701440240400e40502e0320b0f0040c000c034140f110703504552001031800e44102c1c1c00f0002c12110fa85c102d40600151840c82c40c001c805140d1b2440d041c1c1c0140345484014140d11103403003413035041000d66001080c40c6641d011052044544415010f01494000d40750b00340403c2d0802201c008045000148900041c00c001c50b01460030f076201e020030b451100704d4006840345610f80781000850303a00002c0124648a45000500100e07103020740094607103d040c6026880803483c280c8418108010350141e450601c10151217140361146500c0e0384004030824072a0318054042c0d5880c10980d003059100362024560003001812a01c44d00c0000c01004403401c40302 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 661283579 1250 661282329 661282333
    0x318010f1b141e06220807030302071e0606090e0d0c110f040504200a121e051c0806040902090105120102162604080309040e0705030a03080105150408060117 69
    0x1141da400b00400c089070b0080603140000d420b440c200808440000d00c5c480c2a007081c00e1882d41e0400700050401ea084550107034041c9401070b217652041c644003100982054502c41c00c5000c907000d41060040960009045038440b070b004202003606440d070a07032282414046480403c000040c90342c0891341c1c0789036009140e0402007441420041c4c40c800941283c1c01524103440049442006506586034000150800d00d0101c1300381440510f0261113440344a44448001e091070000300300d0032443d01b210743d46c09000e81d0f40310059070440082c40521186114a41e003109001484d4080454001d0030030f445194030a030b8001e0301c1c00d541a23081c201440410740b0003500e01e1090390760030400000007560304a081d0000c1c51180a82404600d59400b40341034000fa081402c201340c3e801008104503504000040b41c0c1c0750b280a90300821079a104e500f00c0350805506a00440d0140500d103585810580c0c024031031030507220100c0d4a8089415041c00c90202405640120701d01580000d00500414913220b4908a0110700307081 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 661284829 1250 661283579 661283593
    0x80a09060905060712050f0d0917120c0a09030b0f040506010605030714030c07020603040507180c0806190807090c1206030209040213020c0a060207060e1606050a02010603050318010f1b14 82
    0x4000e81a951008d041c41210340e60f640c1c03c00c402c100008a030344003d021000c24860500307002d2072070000c40301e0024004c03100c40c1c40001072548410340100102d4004581006400c07070180703402c44442880c48011074040300c860003140c0010070140d00640a03607010f540d555442d0080030310074010034190b56002030314042d807498080c02410016580d6000a5109520550190515514040ca000c109050103036055441c0c50504ca0400080d580c080c040d154050b40444500110075021101001c50441541003104140202a00466140b0003608004c584200c140e9860502e845111390005c112140b5000083d80050418045009031a0410190b6148050fa82005140c900b1100b492440d011702e0100c00c80e0702c01d4012440c401445224841e040d5110710310805004c0309801d480209010001d035004180c140000402c020131140e100758002400346030300c0b0741220317030b80c5160454160551102803683c034001001d2180c2041500d1041c0100813000c3c02104003441d02501640e1b84500196240e411140c1601c9600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 661286079 1250 661284829 661284847
    0x1b07031206030c18020301050f0f060712030204081b090406110c010204090605090106080f0103080307050f0d1a0d050c0d21090e1b070f0c03050703080a0906090506071205 75
    0x4032581c1c004600c211600c14006280119062032194030240004846105100422a0340c494624185040d08100d0380258003c001000142190040c3c50015102e031203c014401c04650b050b5000f00b00b2790329944201c81907220400d040c1c8064030500243c2d01e4201c01218045030010781e058021100000007040d80d58100000f01440f182240c0055101c0e4042e07540b245810081c508010b2009409009940351100e002d14003400f1102501606201c000c2c51100000009030280d8894026205070492070b281c103030369039449005036102174130499081c1307c14440207030000c0c00d031807401c0b540703d040c140c6d0b1003000342082e204401c00300a0341c045c400303609485002c00804036203403061109100e0b0580180741c1c0c42c0c2d1000c46003010003852104070002c014108400c101c0c1c500c0016a511001920340342c9500218404c02040145400f440041d07080c5d1000b0130611880c2d0004c0100008103001d0480e08807155501000a507942c00200d402043e181b0400b50400010014000800e4202181d0005d2115a0515600d890005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 661287329 1250 661286079 661286081
    0x3a08030403022103280b060c1b01030902010c031b080d050702010b011803150e010e15070504030314220b1b150105060d09120c02040b091b070312 64
    0x4540460058000219400000d07081003020240102070090b40c50031842d02c0a545840311710b1a0b0325044c003c071081c44940c0c085442940100d00a1140545142e844100c00320000c0c2ea50b20308020311899400c0120200605944244901d521190f0140e40f0140100155107058690091004032403641490554015021640400081c84689904080018145001c140090031207504004040c10009002402d031660700451280300140d98012810340c1641184106040c010900c800000000b035003007030100c00e000d1001040b440c20804062059152559401070700700c80508c1140802400704103131800f60049100408042d184000440001c0c2c000c544615038811015400c1da400702c480241c000800e61250900303001802007100c460702c02024072a60f0820384503000981406854002c0001007004100007125401c07800200d07420028003801c1400c400c02c0145200241030050b03014500305860b1074050b040c01e031555441a1050180c0582420001d0000040362344850743c10f504101409800c401013120b5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 661288579 1250 661287329 661287331
    0x140604150b0108071d22050910020702061c090b010312180e071103070614010504271205120906100e01120f140d17063a0803 55
    0x50452500d541002224481550380c0501c1e020b040200c05410b0280282d004084040622290000e050480c240840411000c00c070180b51171500d103200008465115081e60311160080e50080f066030901c4034840f0800c02030380f050b0000203400020070417880031001d8824194101d0000318032000700d00f240903511214a0404207130000e4640304030020351070b1031041d003102c00c00c102102c4a01c6550700d002d207056a60500450001c103c5014000030306036820311084c0c140200d030251548030b10108840c40b21448601e04074035007402018091482d0a030040d210304542c0c54004144094104401466100c2d9074440e02045019003400c001d001d024040490841c08480d030b8140305452101c024222458120b44d0070103200170a038020fa05050703480005000c80f00d12180b18071001e54207c03240b01542d5142d86880c90650340030441e285820300030b2082c0d40c164150f0003641010768020000341031680307031105400c0002a0003504400300310000350740354042c1c0030483c2802c148511410301300c07070b9215401c05480308190740d80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 661289829 1250 661288579 661288583
    0x504030f060c1b030801090513021302040501030b0607260f0406020a17070c063510060e0a030b0408070503160501180b01050409060b0301110d181e140604 68
    0x740b114005102c2503030040c038100100404215650b03150107103880180450714103009165030b02d07451b440080c0c030150048117440c43c10381d4040d240c40b0349510740710281e000a41050246a0010b4208a100078080c54407405a03490140c119644200d0400440b40560700d483d06444040e0891905200c4416881040f42c0540010500303500a030000188070700d410000010303000d008949640c4c040c04818081201c0b180d00d01c0a0300c0450504015024032800800c41140d4040c11011480030189100850f840c40d141b5070b14050102004440e03c143d4403458181d42495062018507008611b2036820400300e5140e1340c400e41c0281c06100320b03904d0141c0d2a00d032103055a20100e038100d1413028500a07002004000d00c101e00450b08032144403444206280e4a802c1140010310809201d69100c2200000780949603016002011006000700500ba60300348540c00309400000782c0d80316031860501d0034485803080c484203030783d61030380b0018003036203502c401d0340726007445039030b2031060710300a0361403515641c841c0c410819103000c2c074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 661291079 1250 661289829 661289831
    0x240a1e171b0a090e010e010b070803181902090601020f03250c12031409030a080703020f011a03010e01050c0409020a022401210b0a050a0905070b07030206010b040b04090203070504030f06 82
    0x1403d00e60800001d01c01039001c44900055070004022359034000080e03841996102124030703a80c0c0c9a4441c45c1008056802c0034081c94012280038803441c1c0c0c61a4000303404140300740c6025801e5525000161388801106420400c0b54008000e02554030075804804242c0d41400c0301c001852035285c0c4c0300c400e00d514a41d00044408022050004249900032901da403146a20550746803402c58583c1c00b103512002ca60000501c140c5011484008144c000d200c0480394200190081002e0344001e003038909a50b4100308130b180079510f4006d142d200258180600d502c0b54103020b2500d0702c1e1030f14201901c8025172210b40302c10700318082c907134903e00c01400c08054030540024020101080354180709814602011100c0d041c212030490103500000210350f845290760020010740d000510b551159003072400340240b500e0061103400750306004602151010042c0c00010b002c5e030301311041c50f030300d03144501e0003031045d806941d40018092100f040a040990000c50f442006843c080e41420780da955015501030b0521021a071007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 661292329 1250 661291079 661291097
    0x1a070b04230a050316060605041b0e0d0b06090403050708030a0b1e010f080a0e0f150a06030f0b0a0209090a021224040209240a1e171b0a 60
    0x480034400301c0c818503900070806444402e000c0c0d81c6166072486004030f031110340d010311030320102031041c5076000308002d18015005004a40c6000701410792604e086030a480458a200b511408c3c904010100203012035112000700c0860b22007104000c0202c5004100f201009001c002200005440002035400782000410100b800440d820400030212800500405200c403c6800310400d44ea00c059041101c208a0070917070241d48820110b500504203443d04600e052160000c1c50031800c0000403644244d1985000c210720f01e85602100c01d050341c1040c8409030540d80c0307142144022891110700107422050114005160010704d00100c0c0800c24119007089040e80c0c003103800206100d6030548154070801d8001c41c0880704a280340314101590003644240e0003254040b44000b86030b12814501c541400c80e24010b6000042c080c050b00c0050b80c84560400002810040d0000d40e02c400344481c503202d401980c0744c00e071560464204129608000518031342031003080d1580b1003509240240101140f0710240d544240f0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 661293579 1250 661292329 661292363
    0x310020309010b18100503031e161403041d090303281e1b02031602130204030c36050603190b100618140105071e060606050703091a070b04 61
    0x2071790307102d640214006d8104001d0301c040c803907100e8509404c80c800b980d011900c1d1007000d101d0a00b41e031003a00b40200382060034070440303880300d00000c054800c403030001481314482104e10241c04a411004d5844012560050001c6411036042042d8a1750304045030180000c40c100281801b01624040c0410014074560405141305841c06801070032500074a03201d100d02c101c101128000d68038800d10081c8084079040f080107104650343c0e4403101d904400c40300c20640d2501c0c0c40e42010321070501d40c0c1c41078805188028030b0326000c003241c8400d0f2200c0389140200d0256808413803403a076006464001e20003036040c0901419441e602901440d00c0d41d81c1e9005480c04810b52038a480c501ca8907031079540110b8280701031036000c00460301c182d41041c0141c500d640391400025903000b006850301e014801d8002c1858410b035011110100d01103c03000d1a4600810080c41959a40c0d401076441d442122400b400140d1460401e000e11824581da034007108803c4000036241074119101c4286050f0191021166403c0c89064104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 661294829 1250 661293579 661293601
    0x80f0f0a1e020c0901170a051e160b0a050310081b01030b040608101d0a03030902040b0103020f030f062404081612150204120303050603011a0310020309010b18 70
    0x401c1219000030640c50f00210001000d0603414402c009400f15039820048241300188022206250b000e001c864400c030381c45a19580800d0314038076600240c42907440300480b0208080206003140c03240f00303040d840c2000f040c400301e840d6030009100940400c084640000c0703007103040000c2d02c0380f180514001c0d510b007070702e860005042ea407411100d58170032820700c0742c14003103600c010804c00c0440e101d40c040064208200384014504404480d260340e00c80c098184001c040c5500f680028007040e1003140c007000541446401501240603050b2100c40142c41400007504000302003096940080d0000c19000c1202c0e07400034400c41c2510141c03401c1030706000200e41001800c004120038954100103039012291142000c0600c00f61400d03840016003001c0924441090114040d81120060f04e0b030010900020682d9040145c0941070030b1310180c3c020340c40c000038002054010002e6410783e42005018101c1540010b00e1320010350005001c13007003503550b41d1508691503a12081d00010f100b03968500c031240380c681480840 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 661296079 1250 661294829 661294877
    0x20f010c0b2d041a0c09060406120e010501030b070f030c05090618030d180b030105030309060a110316050f1b01270e0f010905040807021210090b10140d080f0f0a 71
    0x1481170030050050f1101c0e41d540d032041d039043c0d4049103001e0420711140510782020b030250920440541d40781600200522103040c80091145031a40c40e88004000c0018040b4100c510040c0c5100c0022810304c0b91203064541b02e00106440c032801002440c1030580200002e00f0b00811282140105003d01c60402e0300408800064005040d5920110300310b41c5004040f0340c80c2d10500b00218403c21002401400d0b01c0e014500042c880288441240d855036080550000813050040c01511140300f142c0c014440c3c414000345034156581310b204a5107242c565040151030801c403241d008811000a5440c040e41680000c408200400020000e0750403410300e1000c1a103284010f81007820450708000411021552803021940b00c15816180c17030040c0000c424007039042410801c049a510b0b82050500400d00c42d0000c2068010b0b1000c1700c10014140d510920000082d14880381c00342c02180a1410402295500015081c2d03490b051782d09914100320080c2c9102c0c01c2e44401100400308121142e00c00c9800c0c01800d001c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 661297329 1250 661296079 661296091
    0x9161503060f1a091201180b240103020a090b07060b100f050702090402210c030c0d032a2418020915121504020f010c0b2d041a 56
    0x45202e40781015442101d880c504030180300e0102000900707a0040d2143c003030001142c2603a0000308050110340740104140c08803150b09441000441000c43c440d01108403c01e1700c0d44c06500e6210b4050031002c001540a90440310401c4d00740802c0d0400001c0c6424490002c0c250944240b00020b0b0f04d00e031380402c00c0700410b4070390205000c00c0201605030a100b904070b011240c0071501144da04c8216940c510000e43e0140300404030b24240c04404c202c83e00346050001d12a083c140044041e00c0d030b059601c400348074081e102e0017400390015010340605401d44299844902c600d90381501c41e43e000789829158115a080c480301151303030080d0520782142e2600d0741e07403186c6204c02c05c82001c1e0801c42406030f00010001d05000c1c0140380b071004654001c5038166900f540b00010200085c0603150101d40702c403034400340d441c8100e078140d000d070301b010b0201c080940c499041c03201c04d6540000c19900e65107a104061820084014010a961500b194480c800c0b0054082881c4512320621216050201c40019582242c4000d054 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 661298579 1250 661297329 661297349
    0x3011703030c0a230d2a0e0d0f0f050601080105100f060e030106360c0504030b0405030f0721170601050913020a0e01080c040515030916150306 63
    0x140320440e9206000c440d945800d51030602c4d85a038040b4151090000e1602000b4000c140024200c404540d850b080b540d10050740c030f64040054a9004030820501005156040020b080012040714925000301000300440c059800c1041ca0111544c54a400d40b408440965055006500400941000f40500780d070019161080319009c52a1400c4201841600d0280340140020120b81d658907440950007140109241d10600d00d012500e08046400180e1403a13418088050804000340121564052800000c185903511483c0600e940c41d0340e44c0119000c3c02c01c460b50700007004801e6039046030300b020f8a842c60007400905c421001031905051b0822400b00680c0a04c8220032424840700200003005611a0f001e00301980d03242002e40001c1d4000b0400b40c1d400ca4070b20310118401c0c48d481e038001e42d0860075550a072200c1d103254540b05900110344c0281e102d803d9012540c2da20f11520300c02c895010b180c11031883c0b801c0b603181407121500400d462401d50440003100c00503031800002c2540c1802400001c2401080c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 661299829 1250 661298579 661298581
    0x11090a110304060c021c0e13060b0f07080408062526100506041d070c1106070204180308100f180507020304030816170c0a0b040606050301110301170303 67
    0x11100c0c400d400300820107000340307540b81064401240248540f00800204a040d01d03680c1c1c03e107000c003804410003003844900540c110079000c3d441c91a58820354041d034080311410741c20440410f2a4401c01e6204440860322958140301c001281003003009800e010761040345104c0411200c0c0c520490500d006040310700100409821482c207414112107564104502ca40e0031182c3c4d1755650f0719038000d07111041e44429000100020005402443c161202050400940c40d1480700d8880280c00c03502c100400b203015002c494140510080c6203080001803d0251000d8004035041203d403408801881e1005401e4011807040c1041055142c036030010103010b8403003125004891400c1500754055000e031001e035481b020fa5600b02007a86d51b4020819100216444001e4560b1782c254416a000b42c94482041207541288003a49014001c80e10420ba07446885903400a190003402c9032581d03aa070200c05031056031426610100842c2d142ca081c003a040030084181d10456503940340000c03601c0c40a001181c17a04039500180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 661301079 1250 661299829 661299851
    0x5030c07020405040c08030a0519020c010909020304020312030a1d010231030204110d050c0406080a2d0b130c02070519090513140a0c06111002040311090a 68
    0x6855030300d60181c400190981e5586010700c250600740c0c01c44041c40c4008940c030310347c5a6004c1300030b0100b030407040e40d501d010810a110599030341c145030040a000c02c1d52010b082c00382d1305041d8061a400390005007180c0b9041200110b4070030961054a841c01c0e13060b1101d042804006e500c150b561103082c50070000314503081e050a203402554100781c01d040019904003084808024000340d0719800755800500400000303030420b40b659101c1e48032003801c1c80c01a00b0800010345241901041e01c0840301c076030f2a180718540e80c20030b40b10010544a02501004041c0025000070760724550000e0b0241e804858000032500c00030000c00c8402e10203000420400c604152002c2c42055010600808485096601d1100d10703480c3c091864800d8415002915500c1c40c2a0400c42003642c1070203e82c0f07030540104d45803441d40b003808510a849504070a0080c4c01013002d288100202441115406444c1e0004019a0780194240e060b10099038040d900a65011452140e4031409103003140081d60400603504080144406030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 661302329 1250 661301079 661301101
    0x1e1b0c130903091a04060801140a0306022d0d0b060405030703020f0619020601050a05030610150c0b16080906010e0c032707060201060b13121103030313120503 70
    0x600540002161a81d0340c040405005056031000743c0303207501c0e034940140c44060700003003950000d200c1d10001900341c0e40001000d030030340700c1d038800c0b1020080c0410038610b06585480d400703035220440008000b019000c5403640340f004850b01c000c8090305204801e540b550f01489004c10b544116002a11032032042104100c29507000030031800300c907415110604070640c1080040c1890042103180c0300300b4044518400005030340420214140c5800300c40700101ca075103030fa05255450740b048ad03048907031482100040c445030041d18040c80420640345404600d118665403058070611041d100805506071024000c9a0140c01100281e131140c44030740180380941c549550003001e041c0103001c4081d101c40c0040030544862080c140802051808a0003c084940700340643e0782d141620301c075030380040d46001d0004c100701b9503ca0480302030f64641c03814000e0076030403d07061a111a032602421900e01c040c990010020741c80c1880907604c01c032802e000000304e1402c1402e201c03203200b42054405017005810001c0040180314 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 661303579 1250 661302329 661302349
    0x5030c031c05041703030f07080403020c0d020a12060209040c14041514180301050901150b0d0e3403030c060f0b090c070507120201020d0f02031e1b0c 66
    0x7002084407a00001030303064400e071040e03030481c00004242002040d0106070000086002d8a120b403a00c0d121680d980d94201c0f0700010580e0300500682010228800c1ca161845002485500085c800300c40241c0e609100c1c201e403050000c044503003035004100811030789003900c06c13105904050308010302401a10841044644918000d01802d0040701ca03000402502c42c0c840d40b0100210606c00c16a00c0742000a039280000c0304001480c413075070070100014004481030080b0500310280c005038541c0942840c945160541005a820284554854840d10303400002c0010145140e50700a1a04501172251455000240c2599019071141080130741000000d43c0b240310000159080800020f403052580039003130141c64040c9100d5880562079041c040070144410091080a100d4021211007954031003020b890302e0395501000c0c1c0940c2200494011b40d6000e990418412109481039074544046403041c4841d00f0103001002554110201d40c2c6a560310030368100c2c0c0c0321404410002c22201711600c1c001501c4800b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 661304829 1250 661303579 661303603
    0x209011e0612061d010e0601030b030309150c0709090512040303120b040f050403030501061205060d110a09090305040312210b03030d0504110414040809042007060e060105030c03 78
    0x4000c510040b21441594044000b5048240280c502400301c099111112142801000d500801004c080780b0658000d11500348000400b50155090078091410407400d016244d0400d50010020001030f805400140220406010680c0d00011460b40604040307180252580c2c40c108062400c01c401c0c408a078000c4e8a0418040310008042425400e100104002e02050101280814104824801015096000030f4103030740144e0344000300000d02400f50000e6907000d8a0740d030b07007240392564424080b442415500e54504000780890070103d0b40c2e00d5002d82140c04080c400d40000d0b8010409104000002c81c01c541c112a80785880c1162000c0c0c4209a580008565411051141d5a541c00034050b141072050300c0c5040c203600c00410140c07825007480f020b04581c10000c030b0321542c60010450300400e06401e60341e0280c0d41040c041401c0c03070000001e0200030402c071406240000243c452030143c1441c4600103202c810711a04010234100248003040d0710701041a001284a500003039040c0c44141c0b000282d080500c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 661306079 1250 661304829 661304837
    0xd0c0f1707050408060f010519062c0a03050318040506030606010c1b09021c02070b0f040c030209070201020702040b0913020103020711030304030311060a0b010c110a210209011e06 79
    0x501c9401050307a4a00c940d50148050740142c00070012900314a2600074100c0b0001c1d00c1c501c044081d514a101c000034a00d002d0600400d9400b80701a5510004400c150751601e607900c010750748040c0c2c02001070341d008440c0e1b100b280c0a034030021383d021262085240443c00c0210030b07a01404030b401c00300002510303030400038102d0f81040103000e079100034021000d4015850700700c0a071a040407240c80e00f60520180d400304101c20509540359501010000061017124031854000d00042580e803184101600113860281040d076018003500c42c007102507607030302840d240200e400781c00041e9031301001d2050000f07a44600507850300c140420300811080c90f500d403490810721682480e006945031454035003880000b5001080a0309488041400700c00c05400011500d032a008210841c2d40302d40d1507281e060103440c010340610740055007880078a80018500b200c1c020405500810300e2580c5500c03034288445042042009000e0304248090507070544c100700207214090034211500e003240d02c588480c0b5941024203841408100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 661307329 1250 661306079 661306081
    0xb03180109080a020109021f051e0403150209130b0307090e01020d0509070515030c160503091302041e0e04020909120304062306010207031b0504050a020d0c0f17 71
    0x5400a51291140300d500442103610f407036a01d94001c2c02411100802c80c01404500d03c20300300503603000710203500e0701000ea036164a00b520502003541c0e024141a084101500709002c003000054402800c2c999110b12420010703207528400c070401044006030555a00424500130603408282c6000c07400d902520755003000410b81000c0c19903054020305c40c0d454221001d034500000d203c1d000e1008a1454201d92048815018440c7d00d454080c00318070042d10380c4010000108040410f2a00042d80e655100340243d0690342130015075400305070000d0050807401c140a50010b07003404050b0b01c031085000305615000905580c241807041040b065200600081e108450750000508e8022013084450081d40060750596124101840d1a030090142400b0303003281c6590704202c041c946855000c0ea01e00c6500c050380204401031841e1101c10032400f8403060440c11241058003c1007135100d500900d4041d8161000c016501c41c0701c62010300488104006840400660300072000c9400e61050801c0b5a00020959580c19 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 661308579 1250 661307329 661307371
    0x14010603020310081b030c2d04091b03033207050f0f0d09060f1b051222150c08030a180f0512030c04060e0f0a0b1903060b03 55
    0x10006035001460500c0b584180c40c014184601407918000020341c11200007004940230130140d04c919021085110440c5080c081e031038003144401c1000400003500001d003400c101e4a400041070040a80d09079000c0002108000b0964401c548541c0c40302240200704050341c08038001214581200310351500c070700012982c1c0c000c1c040c0078400d44240f00c05210480d00c0c0f100204d04519110603542c03000c800800c0b03c0303510000c0e045000385200039034240c040da11030180380c105481118100d00c0380401903c0d18490381c01c05010f0341861000510000c00c0211602080c01c140d10305103400362140b50044c01c40060505070103a651508000301d018510781c460744842e1245c0c0c0d0928007038000c03e0701d6401918110304040000302400010040d003ca801d00400650304544034040c07800c061880199402c0d03000d503004100401c611803090045004c26140241144003102982000606514468200c1c02039508005868441e030710901d40700340d459141508092019518081005045000c0200043d5100c0210040e51072 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 661309829 1250 661308579 661308601
    0x31005040906020f190311040303080106030e0a052509020a0f1b0b0a14060904050d030b0a0510020102190c051911192120010516061e140106030203 65
    0x103500e984c44402591070f16600350f40070b04040c00b44052900030900e84131240d40200c0181d400c0301c040d6901501c03003600356407a04070200c0c003d0601844218403401000c00307d000007034003488901c80c0301c0400101c41400140380c100b0007502c1080c85d0700c66001c451040101d520316a4115404201d504c040e801d0140b002c0040114003100800d400032700030302c0d1803c01e9003000004c402c80e500104c610b509900c0800065030f0381000340000301c1015100641558800248241070600c2500b2804490001505c5401a10b5072800071510f4a41d50b580080d005d40d4002c29171020001d50f1148001c141c00c028a80441d03503280310744032140c54910b011100002c540b04800e0400034000bc0c007040000c4204040d0140200503000c80d00c4144408450041800040c0b003401050f501e00340c2003081c1012560000c01040d081c5504594804000317008404090500c807081c0080300110049400400116004a90120f443e040c8200140b80140d80c3c0c01107140028900924044410240b26009054404a060050344e030340319408448 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 661311079 1250 661309829 661309837
    0xd1a070c060e21090f0405060310180b160e130e030c0d02060106092103031803020a060605060316080604060b181302030105091302041112180303100504090602 70
    0x1a05080c02c0441c1c4010301140040c80920000000ea00341820311007000304a1aa40700e400e2000c0d60000b11455024924a0b2a41c0310a4100200800f100c4a851101000a00352003040310720243c43c0c4800c544200c2840f0084c03014540c4440006410340c28944100d001402c0200201075030790041a5003c52300b0050069036000d408101241c004036a01d0307200102e83c0782d81e154407418605005000b01c00c00002c40030b004005120580f006000701101d00003204c201b41c4a220881d000650425031140410800e400e2082d81c03100d02607020703a0181c20a01083d0612030103507503243d4003a5002c2c0008104102d0018141011241e08800c10300c1c11041039210080081c020b4000d40d04454482040003800f203107e400900c180700d01562050341c55101d150017141c01c10089000900c103594000000000103000326944021081d0140d1006000040f1716100c50312001d00c64000300d80b401c00c00e03070050061204181d1403400d56120030061300000c51031403905118600709420280b0845003d5612592001c040102c03680540b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 661312329 1250 661311079 661311083
    0x13090203090a020a03052104050a1e0b130e06030a0f03030c03140705040609080a020a120602041206050915091902030307050312060a08010b09061c120e030c0d1a070c 73
    0x203130030305849080c141d440e03640e00d031448030110250890000204d0090310543d0704031800100014080c0d4544070641000300c0c051840481d00002090f030103d9005030f0040a011050003c20300c00090710304101e24554001000703460140320740d001c0101c1a000030312007004000700c15418a40800c80b09000c00094001e80310140c40d884081c210303c81040401d40d800b40c00781c001c451155840e400c840b50380e00c9050343c88600701003010b90020301d0f5500a00851380311803003908105114507401460140d40da10300b02c40d0002c41c10011502e0640342c0d07003030044403841000a08484e2081103c1c140141c1170503800d95030303601c0f03500012624141500300340c40d095540610a440746180c01c01305903660b03601c030400c0190b4120b40031203100d48a050741c4000400c0c0d040c1d05100d030004800e0080c0c6400203640351501000700e840c0c00f060620308400611680c20f03001680c015007080388070701c3d1070b11030843c0c50b2410030405040031903804055010311010301580c1c01140e2080c60710f03e03500055000c100c1b083d4440341002c0303035412064000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 661313579 1250 661312329 661312339
    0xc320706090606060f020705090c120c0d110405120606211203090618190b10050d0b0703051503060a0209012a0302100908120901230a0605040213090203090a02 70
    0xf0001d0165088402c5c2c4008010740e40c280c2d040e483e16072081042c092003e41d400250b091050000c4c680d074959402805410191860004c2c0c2011030302103041d1700303643d0282e0510180d00e20100c0c040010741030000300e002d40f500743c034400341c80c0b54a0410041440310f04180606c120b0141c0244001c1080801070044480c50100c8150702552450640e4200c1c0d9210004c0e41c26810210713500c0748030124080080741c030342203204090300540c010074021388411700c7c10b0001500318116181d00ca03c0000396603a440c10800041c034811100c40e01540b5240d50081e0403034400409104804000ca01c0e500e040355004a0342a03482a5040d0005881d04598401221021640100d030703400c0c1c0c07030020106038262a4640c0b00941c0e4902c00e508558000c4c0c603580c1028292103008400070043d01060040304c00d030070b02c00d000070365000f0b515000000380842521101003c4101543c01d1030509200300c424480c2401007805803401808043da401d5103056803601c2803030303107083d5140304031701d18240e02101180300d9080034418000201d8000300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 661314829 1250 661313579 661313591
    0x6120c05090a0f081204060212130e181209060d110f040b0315040c200f03030a06050f04060302060306010f090320100906140705030f0a02010c3207060906 68
    0x51a40b0701030740c1e28000c1282170f1051038490703004040a0b03800ca5098900a901030444100b407404c060031160815402030703046003040380020070600040e003a000c0c4184203624020180b81d02070b000513800c0c4045e054407100001d0040254070403035181d450456209a04420000074806144110b8144c0c0740180064080440f01c0001d0020710038110344003443c020b1031102000e007580d008400801044445000c0720201060449040814003101c10b00c2c040c203441244c0080d42c0001488a070040d040d41e1040b00c0154113181d460000b44002e0400011f42003406a0035641044031302d0031a00001d4403400001c000c9410040781b1303065440342a1045035035000a50f480480030440303900038581050b050802d02c0c89540144c203091101d00c05544070755450030449000d0307203940083d60405c0310003100f1a844030005a42a12040000710804035a00d801010b21058680c000540700719401c00051034445101c040300c030400180c0c00b08000d50a510300400c1d0343c0c20400e540b590703603a02040c508803002d0540c040d40a4070540c5814 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 661316079 1250 661314829 661314839
    0x106121407090501030b04021e0910060905180115110d08010603050c071212090209010e010815071d18040f1416170a020a0b04081606120c05090a 64
    0x15288120180203109565495807038042140403603009100180086070007601007009414640900d00840440c140101003401c030250114102010540d242819018061010890260b200703400360b0207070004907500550881c50100d42c3c9140c0c00c040c0a6040d840c01103588112000c4c2c0a0074210103d802c0700000c1d54042c1c8805c2c032021300f04144c24440c0e0302c0800d007030000013008602c200b0b0844625980c0f0400c00340c1607003209001219090207500701054040c0d0348045240150b80e807065000e0090403080007090300d0358100880581401800c0502c0e14070340040f00c042c810215007000845075003c100030028807405881100040d1003102184440320500d1031a01480103203c180c2d80100301c03003402130382400d401030642c1c481c0c162740711600b1604c600c00c0d1003494401d12000b0760300d58030507503460038100898100034282c1d00000c41481c803a43c0441002680081d007005400b80901c04040c2060862151180c4145130980c060300660300c0152090000b6500e41401b10386501680503079071041130141c03140220648032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 661317329 1250 661316079 661316093
    0x50d1802031e01050a020304030c14120408100f0902060717040e0106081f15120f1407080702030403020114090a0801060b180301091e050a080f1209010902100c05010612 74
    0x480d002c00100e50038000040c0254400e402128012941035039842c441c5c848540703070355528482c0100b0350000340c020400a0114011000060800313440c942c4060f00b5440c40716201b01c010ac5080c40c0040f8100e506102e8090091703070701c04094500850304042002610341405520031240e110b550410000491001c00101d02194441c4030703d0701c141a21004140c8805000c82800c40800080c803401ca000b903100060381055030700c985000f9078207d01c2950f000c9500180c144805099070b004010b504040003007202040314540d4040c00c86c603003000e0140043c514203420750300000c000030045010442d52000000b043e034510b03281c041351400186040c20081120300e40310f04855159501c4200c82a0302e0282c0314807091518a010b200e0003c6043c1d00024000c800321480307840048141c2a030805503100d01580c4040c2e4080380d40c1074000c10210310078425055482e101c000342c0344c04400b8060030709841d980c90090010016110001300b07045980680c01c0c0715010419603e4054090103041d040000300c0e05e48c055080c000c010030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 661318579 1250 661317329 661317373
    0x30c0102070804082e0b03070503010905010e1005190207290610171518070207030212010209030a0602030a0f1a09071d01030b010c06180204060504020703050d180203 73
    0x1d0796041d10090b81e405031415012580d000301c00c1c0d81076a42840380f281c180e5403540c4880700c86c810240690f80807039074400000303085408407001a209651110003110440ba030900480d20603c068540c2042542403400d40401510004c0070f004075001d83c0043e01109000080600c808a50b082400d02040ac8900c00e803180c51900e8146e0740b0740e000b19400340c2040740305401292140301252503260010705c26a14903840c000d200801ca04401e03080350240803003003409010426070901c503501c50380003820241d146206128503c07211071740d84001a48184080840380d40c02203010b00445802200c05030b00c035203e107208400280040324070707040b20701e250808040410000c80b070490505803007182d02ea035403a0f84140781130b15111a0001001001688405a03240d60340c0254480e85038400c061400075903462856031000c0460300601c802c43d0113114007803498011440c01f40581e8015280a0760150705100c0c040da0040c01e28080c1c4500c90240d90b03241c502c08400041c1802c1c03440134040d0005c040b150302a13440200c40f5443c1103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 661319829 1250 661318579 661318589
    0x905100c1410060503030711100905090a0516050f03040b04060b100306090e0606010804150908030f0a0c180302090901270b010602060c0f18040213091b0c020603040302030c0102070804 81
    0xc20000c000031301d0314001c4180e444c400e800c10740c00d005180c4000b04010001070700703041da60140541c0034000700315626040f45080c41034040500018050504440140a82140306010b104014041103a010701003210010f890b042a404184040710340c0303545c540000034001c14120540c01000c1c900c1959152581900040d08407500c0a100304841201030020319103c50080300d400e0301084880011034001a9041c100b4002c16454101c0007031000c201c0d0b659001c4940c800d035000c800d005250300030b20405441c940f00d055160180703030a0414010f1444001d5543c040c1040c4400f0b40b040c01941d0008074442000c1d04241203500c0c006032601400c41c407541c0840d440d0415400c0550704294604c0001c02c000d030000031901d00650321040120300b0304410400c007003181e89c081403070301090001113407451983d525140058060120300f01a45080c0c0342c1440a1107040318070b162000100c0311000c002a809041d000850303d40030680558540b5602d83d00c41c00c00b41d20b10f10800210003483d41c03000a045081c4118800600242c2e1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 661321079 1250 661319829 661319831
    0x7140c0411120a091e060902100e120a050714030106050301240b1312080c0d080612011103010623031014030609120315120115050109060905100c1410 66
    0x3d1107940f08001100d106540040124442615185201504140704a800b6204903130219401980307501182e0fa00290000b00c001055003a00c00041616065000500030414140148103c0100341c40b11a942e01251145c06880d840c100b2040240b070320290409009800007034000d20821511110801c90409078403c2c00015081495020032030241040440d00c40c3d603c0c4815110890f800c201551080c8040c80d80201c1e070b009030800000003880c009002003152100315407034086281c5000300c2488000480c02da610002649081e0034440703400395100540703055a070580350240d03118962002c024030f101101056140107080100800210a007002500750580b608408180416543c1d0001e00d03076626010b441a0005403c180384080100f4003c0001e56400303034a41c00490a40c000207804140e41c0c031b81e084483e00740d0340d443d500b1040465092042440c01818280313003500e01c0d180382200050800601d401514800c07c4070340001c4099034810a400c04c1e102c1e070403020700c00340282102d540c40d0f50b075028400011481 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 661322329 1250 661321079 661321081
    0xf13260f130501020f070e010303030c0c1a0108160509040f0503041706010801060e0906130c1208030a0e0606031203040507050604090b0a05010212071e060908030916030807140c041112 81
    0x10100800d03203208a83e0751f240e0041041c0d0035990184e01030700b11514450104004900c0040125492011f814520904140c00035900c2d41003954041c2032060b00e01c2c9000f51198848030801854450b41d6000350710641001c440c004c000c3e02880d0403030943c03140d0b0344541e03a0504c92100c0001c0640740415000d0480719980f008026065540043c2445c859041b41c142c0d88a070400b000040c4903800b02800c501c0180d00c038400f03140101e92500460b4003030600d0803005a03003182c00881086007061940c4501010241c49100810161920344002070781d640078550781585000000c80890b04000d8200000005400024001c50b101d9403a500014020500c10411034800e042022001680307500100d442c40304a2000b81609140254030f84a2014084500710f2540c080e03445580c0120101d2014807400d01110312440310030b917503420841216803820703894100c1441d80b01090b80003080050816000c0340d94407640b14a00c0507201b615121164205404280783d07135005820001d8200c5a0b1942900820f1940310a400000d69 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 661323579 1250 661322329 661322353
    0xa051606032705010603060f02121302031f09020d030809160f0b07080405060f281706120a05010501080d080c0a050f13030b0f13260f13050102 63
    0xd545120a42c40c51503060628240e040403100440d108555028a0002c80c110b42d6036940c0f0303400c07900014001307000a5408511000e000c90711031ba0b2560400800d03842018620120b07000680c03103141906034052003001c0400002c014403515004048010340040400d40c0000c0c0a06000d0522030044802c0e1130640542c0100010403c000300c08101079034401518034039a141089804985640510000d880c0300c6424000000c6071358444004040900b11101c0c499250004e401075030f620400c0d84c11071005082c0e5220100c940b01c6c1c0d1300a1181c1025010142003030b01544039400030401085000d441c052107801400c4980041c080150092070480e48450112040402c140e03070115180c0c0000e84501001e4176041045580c1e29114101500e1408030040b103032031503d00111360340141c800d256071040751a80041d00170804107510501181d84e0050300d44040704140000780d41e400d140810348001e04038046185901c2c00f48845101011340f650540540010b95aa01c4803e6250018038150302c40e40e8010312940d500707000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 661324829 1250 661323579 661323581
    0x6060f030e06011403011d2d0606151603080906070c02010507200a120b01090902090f0a060510050403021915030f02070c15170105131107050a05160603 67
    0x9455503000000d002d46908012026490140c0c44440a90540d207451420071741c2221000210340850b04100140601d4241402050501070b10743c0030101d00c0f08007a0074202c8100004201242c2c8400101e600c0c10b905003401074680105c4c0141200e000025211f50341c03841c1096004040c0c00e0190307034850110340c11580e030311074101d4400300c2815000340022418007100c1c1c0042e5125a00c0100d071501c040c210b08101e00c1c0c510200d42940070301d0b88049064504681c0c240c0c240300d4007070103050262600e4581401260001d8010400c0b2002c003502c096289a4120001072081c046a88000d004e044010401e8075091a440f03002804c0d60028081a4425905201d2804144034000040300c1240d100e03803044099080810300c05d030000c0503c001100c20355a000c004040c0062043c1400c40040c0513031992140f080f51040d1001009203041c5001d403844000c03648014045503071542c11034202e20a44001c0810504414501000c60707015154008103140b007844142c00400c0130105861708100f6258580007070142d60703010f00b20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 661326079 1250 661324829 661324841
    0x1205150f0402030105060a0302031806040f0c14090610030902040f060e061f050c12040605041403070f0902180d06091e0201080105300105010f080f0c01030b15040906060f03 76
    0x607400707003081041c5d084403230094001d16442034990900741c4141044080050030a10215011030b00c1c1045003280104000c0240d150201400840341c92800541400c0c000c500d454401600c1c07580318030609000310406500c80d03001031411a42c0908244000c8681c18001005400180102161011560002081c6080ca12a09d8031400700440d102011014515810b450607442000d24426030b01912121242c107004040c001d00080a581e0f0b00c1540d558608602c01400f030512011241c400d40050104201e480d6001c20840306a4501103c0182d03250302500d2000c904150b00e1181e50b41040d1884401c905002c1680e1020380414025030003000302d0350f03a02e611030141002c2d0500080c04102c0e03003c0184440d080040c05101d49800c0340303000c0703c01c000c00050b00b5100c1800e040d1007104142e44400060000600c0e00e9240d02c001d0101100501e81c980102e0401c2da1103010944035541056a20000c803c1682d5034a01c102c44044042241150788a4942c4c120700c0203007409000301800306a42110f1400c035503100c2e01c521 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 661327329 1250 661326079 661326089
    0xf05040807080f0d020c030304140627100f02070c0608190b01030e1501050102120c0a080a0e060712022b030f1b02070512030a120c1205150f04020301 66
    0x30928003000e503550b48075560060a280c88500301c00f0701101c4840340f843c0c402001510124001103460b881c1c680381c61010380804001005058000c442849034003039054480c0005e9022891300004001002a1128039021071440071070241405d02c5040205d10348941d004081d000d02a03005450110745481094803240070039145428000c00d01c495010740d045a41d4800d02a0718014500840c0310440c0c150301502c2c20452248a40c10443e081d00104650340c3c04001c010600c62041d03404a0804084201581c2c40380f400c030001520741030000401e8521710344184281c00303c1550092901d030f1079540701d06100c5a0504042c00ca2005031240389100482003080040300720149140490040c1d46841c2014210302815441c0b84100c02ca0f6140c51032090280c030400030442d441c102981c01400c0c000e2422080101c81a0700820b4120701c0d8108000d40b035038aa41c0000c181c46410b00e00b80c400309805008213000c075100d0041090b08011186070000f030004151200500300c043e484101c82c20b0703810600c98010041280320038410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 661328579 1250 661327329 661327343
    0xa060503071503021309051005150a0309050705060301030506091005010b07240516140903030412050a02040c050910030c0e131404060902010f08011a0f07060e0c040f0504 75
    0x420003034030a84244018420440f4903015050a80741ca4030010402100d4015151480d2200100040244100c04000041500301c5a00c001024500428412489112500c4041540300d601407010302504200c600014003000c0c1407150f40b5a5a030902c02e0b11003006a503244c000b03001c2c10203504504907140c000c541c184c0e015480720b0f0340307050b1450b5184a2180d10000c94030038081031003c0c060640300010f204040c4161004070000841500801005201800d001800f012500c3c0610420f08551400400d50f400d07a084a9501c10801e00c0c1814110f00c7d090122400a40c031505101c4041c00d0581d0210203440402e0060752240c1d48200400b1064042e68103003083c510000301e88851540d4146050b1003106a040214080042c0f400f80b04504000308041c225820b44042e40c03124a1b00086582c400e02c12451114203142054403541440780200000810f1103500841c50000f00781007403015000d104460300281d21040030448501c010007560b813210501c0f0344c2c16106910b4410804000c10860050364811075120f09 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 661329829 1250 661328579 661328593
    0x20108060607030318031806030203040c030f02060c3306150a110a05150f010308030103240f05151e09180d030920240d11120a060503 59
    0x401e1001c16048100164105511951100d403900e104042d1003c2c600e001e5034070b60069400010703244140c0d811590051042520400411000c109a0740b100c0d81901c3e413107601715925241c00d000044090041200007003550040035010300c1c08400f289195540301d003914160020740f1519001d540000396084036082d0b00300c5180040d10300c1c0b88800600600318000c00781058503410f00e050004600d480c0c1440c0d0111225485510941c00c8011282c6d14154000407006030070f0025819950340d59154081880010807000384130f6603030440e0a00c540448512200071980c2000640280744c50000540400e0310702086c0c25402800717500c51070602d05144003070785804440207000d9503081d5090081740704005002068400b234650031810306134070038028441071341d1440c1d501003884c1d0316a040c420461881540d030041014669111248980c139622019180503107010004040002810103110051152420302140d40e03103004041101403031008007520055440040620903a0761310160203040320b00900a095142c6c2c010300d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 661330935 1106 661329829 661329841
    0xd08090712081917041211010b030304060e0303070501060f090c091d07030e0607120b03010608060117011407030b04141b090a032109060c020108 64
    0x104040d0048507050342c408009101d0080712081c43e11000c00740e281002d000341c0f03030b0000c8040d40039005101d034605072610503445031844102c030001c10802c03080c0f20416807051140b0820150003a004500e000d00740103040d200b1100c20500c8590600c001c004050024600780203901c02081d068840394041820130901c3d0065540d401504010485001c50420081d5030610890441254041041c00d003500c6040044000d05908a1402001e105550611072040c1e80112240607085210608203d0b05500380704240c2600c1c02445070300141d41c80701c00148042102c030122004440c008500004500990f001e0b00410400d0850713a4401003a0b0f1060554540d05240c0515a030291104000700c186103040c0a840016a00c0d441d80340c1101c00012415403226140d15540074083c0d60080ba044040581e003405540b0009078201030b1740005401e50304000340d041c0c015080c0e02c0c03280f075050f110005107a43e4a = true := by decide +kernel

theorem cover : BRFrame.Cov 661151079 661330935 := by
  have h0 := BRFrame.cov_init 661151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 661151079 ≤ n) (h2 : n < 661330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
