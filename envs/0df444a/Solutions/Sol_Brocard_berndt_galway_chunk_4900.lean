-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4900
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:05:52.820983+00:00
-- url     : https://prove2.me/submissions/fd35433f-706b-4251-8990-a7fdf31c9ce0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 881115107 ≤ n < 881294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 881116357 1250 881115107 881115143
    0x1306023d0650151b01150b0f09040e0f060910060312200708010603020f19061d0a1d09030a1202030a020c01060b0714120910030f020a0e0906060a0509060c0109 70
    0x2131024200c0c040e0b100207020709039a10904000c0c141c000e2040d44042082448206103402a810103800c00007009000024600042c4d00c00e180381c0424ad603441500364200100f070084524051000e01814204010284442d510b1582c1d0450790000d120350300400c00ca08660007481e0410708000c0c0c075482081c0801212035249c1c981900718000c2c040d9100480c400d040840040e00f5a040c14044a8412801140018942e40c64038005548009901b4034082c10400c1c1c04100540d1075486a0440b0060f140401d16002540a5204403604000014000401607802032101740102e1fa807001c044404a800742c2e4005da00c2c0d89450640d000a40110711009038254204100410000300602c003605546002c0c980a26840f40002e41c2c0f07170703101c0441e42c090a0304048100a440180d040503001e451030b0300d450b032800295251581c00100102d030021082c100000c2d01c080c01c10084d070301e0459403041c2c03c40d500316925446d020b0b0141e0082c0c280d2017803282041c019040840c0c0c08202880030f5200c0070301075030800e0a81e515080d00d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 881117607 1250 881116357 881116387
    0x61606050c1312020904140a080a1d01031e090c0f06020322050d11030f06010806010f14060d0e0a0b04081306023d065015 54
    0x1650048250140c0b01002070700403106000a40b1068000e007982c03119450355180c111035807680c9140510039204da00400c00c0001d001302c00914621401d96560070500300441c1900100c140320000250406081103001d201c001c01c56441c0b1036007444040380020b602c581c03034078024040706403a0744541c4903940c1060002031055008401012441d81100c1c2040004144104048071515640030b81508409d01c5207800c000031307114281c014108080181140d61600d8800ca98910b4051700f604400c82c0c81d0000001000b0245120311402c0180410a41158600420001147d007038029400c0e000c55694582c00b03480d00800c02804241106034102e88481b90700d180909204140d0b074004200d4801840c0e02e1000000e0f0a4408111070045640500031600504040c011000404286184000140c044207038416001140c80c4103002c001e2002203e108203030358400041940c00b08803d804c2d60844040020400d00c000083c0b804050b03058001042c40c13503010b40d0071001c140e01584100030100002c800241e4405040c0c031903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 881118857 1250 881117607 881117617
    0x5010e060711060609060607060c1e050721180303050306010801170c0d0623060a0902130b0d141905090123040f02090408040303030c0e0a05061606050c 67
    0x400456055840741041103071203801040381140b00303400480c04280185400c40040307420890082c0707814103003402601c807001200c41c15103513000032840c10b05a1308003c0070350550a00403c86a400e00c203080000701d0312010038180c3e4010300720081100c030fa4115400d8500a254006109141e0311130403800b5a02d0749405440c0758400d0301c409000c40c204030000039403100c210742029012007540c4080d201c2100a1014004070402c80e0b0700c1250300a8441207a940010700324616020b11a90462104015041000038000180a01d80102100c0e5004100303110b61034685c0780c003460840d401100800d03611442e03013524000400e402d06d00c1b0440c4044540903c8a4503840300d12458060203540010010382d2100d001c5c0f00d0803070f400c081300d907103802800604030710040000c41c0650f50710900078842d40c04a000980c1c0040c0900c0c00840d0121164a030118040c401e1617818410342440f800d090508c944074141500005510000b64421140303e1100011140c0c2d140066000700d03219140c1c01402481581407481e40540f140d00a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 881120107 1250 881118857 881118881
    0x3310b160f02130204260a030c020f01140d0b04050f04020d020d03031e0203071814060f12010b2709010e09011d0304050f0105040e0a02031312080106110c030601180e03070501 77
    0x10a8001c3d54841b040420158502c0c0d03450f8075810180003945e82409000b008002029041c00103011211007100d0700c2c84024410108a0303040050714442c042c040008a500180038000a510101c0400005840c0c2c241800401a01125041034800c2c0c1803800700c004e001011780d0b50700301c8004041c1e1407407403034441d030099070084409440302540074986c560313184442c21440c480c0d800441128003004845003401c2008025680b0b40f001c03001d20388803488080e5024000c080c3d1150102610000303143c807940000c444513041445007100c080c400040d201c00082c4140e44103000e0034800304051000b00b144c4800941c081001c60300481e01c0a02100010340c1103035200d411510580780038142c40f1121020541c851412101956610481c00b03600380c45040d41d05000707400c010105043c6110411112010401554211031003458940d100c542701c0d81042e00081203107194004600c0700d0360080041c01080d54000c41c03001c0c15100590211056503220540010107403000d100d2030400e90100140700828000190018110101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 881121357 1250 881120107 881120159
    0x3040816090203091f0929090f0d2006040302151509011a1e04031b050603040605040203010b10120c020a1a04020303310b160f02130204 60
    0x80d4604030801a48021640c4c581c1c40e4205812000070b030701c040600700c1340321000e41000091b0941a66030386031102151031b408141c0000c0003440c601d1149070107040564081c13224405000c0c1640c810b140c04c0d680f00d181e44c1c4094203100e048401e050484140840303403200007449030112205401e0605020b901d0751040a0074001d151200c100040b250101001421080d00d80500b540c10765a2030201d988400e14030a00a99040d10b504004041080c0051044000400c0d0004400365480740707540b03080302c803510315100c460402410210042100303580303100c10741e50310581088000c14940e5403440001e0041c80c1007c200303907105c4101070640c02902d40c8401d5a04002c02c1d50701c4100016955200166a26815034100034924401c0f200c10814800c111002c15400034800380c2102e0812850704a810b0009106c080d2002440c01c034000702d64080681c44220b01c009041c4240502d04d4100c00001e54500812049000b40454a09074120720854880c054071003c25201e00c0411903c032502c0303212055036160031900b4188003017 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 881122607 1250 881121357 881121359
    0xf02090603011b270b0d060905010308300108030d050f0c042315070b0a050402010806040b12030705030a0216050306011802130608090709090b060d1403040816 70
    0x810705200d075602e031081a0008400c40c4243c404119080d0001d07420a49544584500b4030380e1310715092500038003625400380b499445000790400c40c0c04a0320303258022034030349023820010404101100c0440301400108403403c0700c0085842c02541d100994040c019044281d0b9900000c1e86d200f0201c0603000c18011510240140d49420341f4109001d10142c0380b41c084210100000c016003046400701e110003400042c0003a55054405e80001e81c0804907000e007080c00c0c0740000fa000e00f00045003041640c00700e204030b0704026030f0a00b07030002411240002c18580c02150f941200501c2030f41d0b4400c48909107015034003101d80d5502d0500d8115200d4024510000c0584541a11801c407040454558001d40c0c401400421060b8030f4685080401d0390503009201402d5800c0201c802005140980280030f0001c41e2103140d41c03420001d40007454840c0c681e01100101d0720380501d090016507035800b01c540240b0110b89800488072503080103414071002c6015403907144800680020b0303d507404143c4203000c1b440580c0954220b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 881123857 1250 881122607 881122609
    0x7050706080a0b2b0218040b01060306170604021e030105011701140708060103151508071e050403060b2b030f08040803061509060d05010e07020a02030d080c160f020906 74
    0x142c41c400e50070200000b004112148482501040388031318500007011030303013241502c2c503181002c80f509890039900c2090136001407091640601400000385400400003a044801c1151940c56000203071000b44a00407803201880018551070a451385004020020004d650303680540f00140000011044905c0d400c0c1903a20720422180c800051003026030b515007400076564100110b000b0861201c000a400c0290440812510b03030050b52200c00b085943c44d0781540f8105010042c014624800c46000c00e0050402016901a8030100f9a01101e80c4040081084000e400004074600b0348410200081c141640c23102110761101c03501c2c15407042c002c1e200d502c0d071411680d10490b1030b800c040b200a420602c0800104403141011110b1248fc3e0086011103828403d42d00c000a6090f806054a05c41880c1c9400051000340304070f91040750007404600081c6020300c0580c1c040ba465207145450402030150076000603001030198000c9502c0d034180c40c1140e215402c42858a0b6210a007803c001740e0041c0c000030001415 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 881125107 1250 881123857 881123869
    0xd0c05040608040b041e080306040e060903040306020c2e150f050907020c1201020912070e0f09030403020d0305041514030117031204350406080c07050706080a0b 71
    0x1e5411555a00905644945031815404000f800480e44140780b1341440045002c10741d19446200d04c40c0656a9803420198104000e0307505841c80c1c0441508a1010300050301070000403101166800b41001d80c5030250100d01e0307401e20703207042284520a907213411140c0c41e450303410010300f1151100c003500b080741e07160742a0410300c50343c61401946903000c01304100340502d00d0070740a0b680d880303d07891040b42c03001800d4038045204072010031481100c9a4012943d4106860215503410214402500402500303240150044c0e1441c0c0250581038039540c20b0020880e0034a0500131600030b1a0040c10300b01400340c1e50310740200542d029105190028400c039a0b9000400e10400686c3c02015007034440c1c81c110390034080e602e1040e41000980c5001e6200c204401c0380308019407140a8899405030030101c062010810026030901e080806e1202154036000c885081395030000255002c0e10040d14000c2c070a9620b4020080c4c15102e140030240c000e11645000080045c0e001651920480403d0401d00c422040c070024041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 881126357 1250 881125107 881125109
    0x23120301030303020c100f0b0a0905060612060117040507090f051308031026120a1704110904050f012909040c03021009060e01053c0f0d0c0504 63
    0x10001040004201091294000d8044a4194401c1d524120b403241061070469420b0101d10f1003043e00e800340400d061030501e40c103400504018a00748100d250420014235070344070b06c0c101e091050000002080d1541d2084103011140380c1d074020444440d00307003801d00c0c1b555040c4600c0380e40c84450038410100c60300c01250050b40d02540e0310381002080000320380d07070740c0e000b81d0002840b400100c50805000542080018107c1c22214082240000040c0802d13000c58142441c8804041d500e030801c004192085a0200e40039901d03003080c1c1c3c03268015480b189001e0b1608440b00c10000d0380038190360184020b12002244030f04044500703c008014034800003d08240382c2c2c0301c030010460340c20b400020000310340c03c0c0000a00e6200c0c2c03150103985207003500d90307000450800880050000041c29503000b800303040d0700300d000a21603005c01d0901d2030071305514a4022410104103962022101c50002c140c0c0d20114101685030200c0144900761525007030f001107200103d03001980900001402d000302d0003101e0340200111b41c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 881127607 1250 881126357 881126383
    0x5010c140901030905030d0c0e030c010e0109150318060b011e1713050d0f080606040e060618031c0206060405090d140c100b010e181b07020d23 63
    0x607041078003940c0194002c00c00b203882543c003070000f00140940e01e6154494461105c017113485051060340c01c3c0007414038260304a01554188a883d0428590716a00030005000301c0f02e42c01ca041c0540d29011101328042d2111a0320100000c50000c0c00310100241600009000ca0082c1d8542035500c00c204517481c00c811500e401c91011a030300c020300c400e114100b0000d882d8040114450002d00e05280d07514a4540040d45c030582d00020404408011644c0c0e02001c250341000b001c450543c00e06040c080610010200035000354460800000e08405030418500841100320001342038034282000c00c848250340d00010100400180150000102d480c5020300c0b4650003100c00340010400340d914480309a44103022402e43c0c0410b10010b10000c0900d000030040e43d0803428526501003400f001400016040c170441c03450b400d1017120211a44202c40b1001810180e11000c54540040c40c1d034072040e242c085038400c034403001e50807150a101480a0000340d000400d84001f00d0300660346d1080e040455203403240c065203810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 881128857 1250 881127607 881127647
    0xf0613060b093c130501060b0301060c1a19020c0a02040e01020405010f0314061203040b0c010c08062e0903050109050c1005040305070e06040e030c0a0302011b0221190c05010c 77
    0x118040a551441d5040d81350f01c035030000120a502c0c0c1c4044144d41e0000d83c8003400040b6101910801c00c460804c2144054841c0b298a100d6030030b006c22401011494a030303040604550100303402803280010040005070030b4010f80104941106c96405a020303504c2405100d010400c4182c0c0903440b035209110f04032000344881c2c0f05001e0382d1945010820f021a10b6020f1000c18401800701064442850006000014150b0000220a140c80741c020300350400080c9024400c502c40c4d1494072499130000040c400c0c0809500e49149012107028080d2002d011a0300301030050342c40c00c032401040050008010b0840c1c00d00f2141000c5a00f0954000c84051095020041c580d030000d9004100d4482c40500c065000000144046078000300641c400386540c0194030000d1041d4440e4890702c040c1134080c81814001e00101000d5825620402400781d070b01d0600154162030b01c03002c480d441c2407450380e90081c0c444280708017686090403600700e03400502d80b03400030205a03101e510301a10403295031b00841411200306005140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 881130107 1250 881128857 881128861
    0xf0d0e09060a03020613050a150804060b030304090f05060906220218040c020a0c062f01020f070803100b030411090612061608090f0613060b093c 64
    0x40c80a90280900314a0b0403545094020005076103000242c0030018040c0d0603028011b2a01e410826040d10310790049103210ba00260201c0c0060740881c10341c4c0e005402400110b0b01a48010200786144110783c0303d045030b1850482c03036259a8040342c1006000b04400c40340c401c1c0319192802004050040c80316440d014554246040c100404980c010301001d1300ca00030080030010040380840e060700c0c81c0080900c0140c00451103c000c109510004038040c002c60310b00b41e44030001003030031250400403040c0125504002800c10401c002030940440d8145e41c03500180316100c01d080d02c2c1c801050b070416a490130914070540800320704100b00e5015648943c1d08500c6c0e01011100500074400b840e500540b80680041c0808405284024104440303401088807070011284426003c000800040001d8001e140503045015916100000015100d40000641116044690652074100028030765224101d822a112000b0042c2c888444010300c98288a1214940802140b16a12003140c08030062050030701c02a07440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 881131357 1250 881130107 881130109
    0x30c18080712030e1f1215090b1306061110020a021902011b11030c03190311031c09020a080d0909020309160b070c0806010e04031d0d0f050f0d0e 64
    0x6202d550341802400c201805015560108010028054205401041c04d08010051507400500030f90209000319041101130b00f04601501030b046240308607801a0b882d018038500607136070742000324504400402e040204694405002c0e0002c101d03c80f034001c0718016007880c00080701d02c0d4001c035841c40d001c9902912500c00040301e20f1b946d140c00e18400342c0c1004030703492f0000820b843d400d1142c0b00280c000c00810b002805800105880e007102a03080078000e8102c09002401c041c1c01003001802c0340d606081c600218480703880254694003480c0340c998181100713140000c1072086946e121500e110b00135145401107035100c120b09540c0d40b4898050301e0024031a40c008101131030315a07000c2c580114040003a0b446481c110038041c04500e8858210042c0b01c1c00c00038510301000402a0000c0003404940081c210039898411100e0a0050041001e0305100e165009800c070001541c0f44141c01c558014034041500d4002d050040001041e560111864030585000043c0520005181a0700d00c3d107590b51680d440000c94 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 881132607 1250 881131357 881131379
    0xc07060c0309151e060503060609070c0c060809060606071a060f040f0b18010f0b0f120106020a12030b0307051201020408011d010c0e0603151807030c180807 69
    0x406000c242c1c0c0c9034045000a80e21511115011034008800300e450300610f5120180a0010000d89880740c1c501300c02002243c40215201e0ba201c101141c12500ca07690b003050645030381014040c0280310550b00c1d04c01140d2640c010490314055183d28085410316034880060100c24814984e01400c60846070344000c05203541c0b030741610303030010028000480a03040040450156043e110f141030b84152503180558031401c1c0100f40da002d65170703000a110361551420403c0f0909802c24000d200e496880058040c901c10441001c0b203000c03043d405007a5030745694540d0000e4a07508880320480d0108009410040c800e03100340a00078040780d00030080c1030210700e020100800340c010411030b041155000c0c04000b90781c81080c42007841e029050ba402d810025000c0020a0843c0c02d49044101404052145140c01d500c444082e6075002081000b20104901180001152100c1e03038480c480c0e40c1e48512b0200b2401940c1500702e040020100d441d0007055540742d1480100240c1d00d8041d500040d4001101040382c08821 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 881133857 1250 881132607 881132621
    0xc05040b0a08120c0105100308160804030209011d100608010501050d0f1b0909090803061c150209040c090e0403030908120106020309120102031e0901060b07110108010602060c0706 79
    0x4140c0350201d5510194a07007402c0422101e03014042001c912503c0c89042070017266031022a03c2c5850034628155515091a405001d01c404a1201290000b504100c185c908a901a640003448400c1c150303550b0030241203901c00c10600b9103030820075a02040b54501f910403074800b60798882d11400c03000c0e8244801190640c20400c084250382d03440d92420131010405119013000e59900a40f1500c00c200403150103040d50000d54040074106240030042000f1030000400c0e43c0c0c02140440d001c0c0d9810070003025000c04009011005011805401e40a0008200c1c55001b0b00e010001a54180304141d0f048105980e25903880c85030400c218030719400140040d10a50005000c0b034070451500303040c84001c1000100c1a10b0036001413001d07a0001039408081e1510604902c0034446420080d4510700c0c0119011185200c05540c284202c01c103100801d0083c03c0a40103800a00f0420300c4490700c42c2d405041c01c025841a28840303030b02081e4468004038240d8400706903036120362481802240b40a81d40d0351114020805 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 881135107 1250 881133857 881133859
    0x4180201050c120c0a0b0601052506110a0917010b0f04020a020a05060414100501181a041109120705100f02010b210105060603070903020d0615121403070c05040b 71
    0x2a45a00300c81d40c10403502401d41c03150500005c1c8542c15240c58424090b510290800f4148881400031a00100744404400c03222920f03034058030300c0c1c1415842c11801a06208000310030054011840d1000785034042c074400700f00c618139071580345402d81030900b46081b900d0f4506401e400490783c104850160809800400d0304180b1441150005881c070380303a441c20b12100b614112103c0c009008850941d050805c07034104c0710280198100f2140d403402003502d203d0981c4d444c00b5000a0385640304060b5000081d0302d903d86009000e00140300014128540c6210799102e5440c4c90b00c19111800790100041000407008140c81014040804082e50040c007903988400025801045640310606c60190741c69180b45a080710b040344010151542c0b0142c0c0c11401d44d81c00401c003e0040340144108a402a40881440704880d0169001c2003c07010034180607003d890007e20a140c0014070002c0043c9040304100c40c0059280140c0080100070900e40c1030170385a104191001d040e280048005024a2925620000c10301e20 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 881136357 1250 881135107 881135113
    0x1050708031b070b04051c17040624091118150403081803010b0405040203120706060e09070608070801060c02060d0e060907081e060103031803080d02090f04180201050c 74
    0x1000507580b015900c200c108496054825080c4001c20404021540c907a00391003c2038400300c0386801005021400b038240f201800c103050400700d02403100715400100b003030b0401d01c00f045000a40d02c80c156110003040c461810032038a486c6003152846c1d00041a40d1000c0401d1080780c43d14580074040203080d244c07107280c281003040104000000940410028900c3c980950014580c02c1e505008240c2146d1680103094004e600b400d04003c0180e030302080310200f14009403201034540c542800d20ba0010300c4180c00071401c000c2101c00f441414200042c0a00c100d41865940084036a54000112142442845540702080f01c03448501c005103031002c0601000c5501b8800000c8007000c5c200c507a07103002d41c00c1c1d40840301078200e1407040c0612203052002104540344d00001c901c0d08230f20b02c2e09483d0744200521019017003003000c03481c1d8203080c211017400c10010340e040803000751114234462680c0b00030b40c441c00c60703944280c210114101960801d401240802107902d07c0f111161500ea400549860340480c0615590340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 881137607 1250 881136357 881136391
    0x70b03010b03250e011101020703080a111611031218061c020307120f11121305060103050105070e0f0f0d030e1201020d0b09131202030403023c0105070803 68
    0x14645a00355110f4582603555203201485803001400304940c00901603850303401000088042500b11214581140307994000007401c87c0b101420501c6405042a20a04021580e00c40c00034070030040341414080301700720305440c03580d1044c807201e600d14400c1d60213040b0b452070004008409441d040c006049020108074940164141c005070f01d600301d9008446c28400306144800d030b10000e4000380310f08400d41005000c100040710030040880010300039100030004142001c0006a200300c0504142c01c0000d41c403d00b25001561240f800764041c10084a59100040c180c590788689480d009862100c00080989140e20341d200d244180122100310210540a0000d44420f180ca50303207500085514a20550700016150861441c4003015103d01400071031203100c081d000d100f48401c4600b455880c0d15445080c007402400c94000c140d0450145501c060b5100f101c2900100040f0a802003405100e805c41c4003c260249031100610861445620080d000860a2040384000b0350716800a680045114104d101c0b55 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 881138857 1250 881137607 881137651
    0x60c150a06150f090816050d0602090d081809010b040b0304030905060a0903061103040b180709050a06060806010206041203110c0d02030403020102070608040b040602030619032003070b03010b03 85
    0x30919800b254800521882d0003100116800202c800140002901400248400340d8030340040d442680526407040c0c0c085008502040349a90460702105409070070740c04800005e09040c44c658015019170881d400c10074028510038500f00400c41d0603070b80c1000741c1c282894144032080109820050003101800850000401ca95030ba401c040e00714070b0b00a9070313810329140c19480c00350140c8100d000300c0d0200b604103100703020000d84807400e50b9038002004003100402241d84107105190000c036130f00548865192034188002c03122950058004d403011519485403e44840004a079078400844010740290040320b88150074610903001701551034180300c140c60801c0120640c660030615900701210140c1d000050410843d41c0501c6154000e14903410464070f03a1405494540c00c00740c0042005101640c00800200c03da0341c4c4500c0c035070101c050000f0646000381c60346451840880b20411070804415401207013489482c00090f10b80c240e4045555007819a40392105500c02c64001038480c04144056294121300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 881140107 1250 881138857 881138879
    0x414040b090f2a04031217130209090607080402090a0b06130303030b030703050d050a031404050c040f1e1517030405010f030606020d0c02060f040605040305010506060c150a06 77
    0x40014100800c2c4605012020080d51a038014481c90243c500411150f002402c51003510102c030b4102020300e1807082041d104480b00c44600755404500c1080000b03000d20200c9010f0312103602482a1146410364464038a450383e0340e141251070f1000903c0600001c6c1c0141441c050407074201d001c019000c50b40104446c002880c54101441d0b07402491039507141001415414050700040e0341d81540a000c0003820354440c02e807071340d0013040c01009011002505840031071080c0d001c03007507012b00c4007031111150805141c89034495103082d0b11b052045040203422010314038144078040d220320f0b04e412200d118640b4800201d01810350a580300301000411b00780003610070a44900e0308080c900034005543e07985d06040000d131010309099104001c240c90694240321581e00000c0c109161b11050403c1018078003244000b801901c1180ca080e50790340004075000a10a80001c0980180c83c0305e4002071006940c4d06040c425140110100342c08158880200211040112900340707811400c80403011030060748404036005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 881141357 1250 881140107 881140111
    0xe2202090a0909110916050304170c160602010510030f26300403030e010b120a0512070c0510020f150402010f0f1409040906060e01180507050414040b09 67
    0x108192a81141d9040121041919019010441d40d2103580d0038081002e90f49855055021000e1010008c0850140110924441e507104c10503403c55982d2030602024903120400a18051001c3e80048008101240107006082c41648183c40e9484114956101c00c00b0f5011804c805a466006000c00100220f0860041b228040d0038080700c2d9a03983c0200040b907598040c3c0060a804c5110340288142036441550b03210b40d0071940510b0013203560720101c2441d03030041c000c22001c0343d40031702d06004100d0601e0780400c4d014002c0f4050400d032007807807165600781c480f1403081000003070140400110500182c80c0001100380004030600c100c840a0344014402c501d045070080202c0c002c035901c0810442150303404541480d5103400c0746420055a00340e20009071150300d49415612031a400840c0841084d2595800041216003100b02441825640c1c240150341c20000c0c06561403c003402d03140c084118043e40541400746025650745444c1501c5c0103128030318600406202644946c89020a003290351b0f032045218 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 881142607 1250 881141357 881141369
    0x2a080a0b090c1b0d1806030b0607060b1206040321060f150215040c03021f080106260a06050102121204020108060402091e030610060e12031905070c060e2202090a 71
    0x41c541c90000192003081240304c6d44074004040c14800c01c0300c40354a8101c2903e200716401600891002c80310710000e4501014610094203074402c1034104824194000070780b0f098405000300115500e03190140283c2980c1d40c50003940c4145070340c018100240321603a400000a540584169440d1405089a48a41e000700b5141070316a802611024001e43c5000d407903003100c041040031412881e4000180103080c201c01441400c00f4030001e54041400072000a42c61100c0304056411901c00d4603051600000030885400b0b480d006100ba252040e241011300000c0702c800a150701c5044100b03554560046503c410018480d9800507001e102015498803948034010b111501d03010a0b81c00c07100d01c401403503c0c000d8007e01840040555070710400029070080d0341d116219400341e0307039a501c0000d031238440c41c650300c00d0b500f10302098440f8490724454141d00c80c020f003004c14030a03809180120342e14201200c6d13490f84042101c4d844030b012071030700c150400004031410803480b00c10b00141c00c001c1e10304005040085964011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 881143857 1250 881142607 881142617
    0x90a03060b13091a09190317150109030b0601020c0d0f02010f26040f050f0d020d1d060703021e070501030509070602031c2a080a0b090c1b0d 62
    0x81c8480d46030048040c81d441c188803008110380e00c21900e80c04c1d8203424a40b1800341c040303146000b180c2100030900100240101160113541c140415180c010000c1080898012294050901007614400c048250040904059641c05122410f5842d940100c0c04090071072815440303190040f00b81e945549200b00015801404403844040b2580005003092101c14112030420080310b050861100c400300050460a107a0101070955549510309428030300282035010f403482c030600d0072821750150001142c0d0b03410807256082d40e00c1a0448082960402c3c0303202081c0d0b01070440030400d80468146a03010b040004e0091045a200700d489480c0c0740c6007242200c00890141d0060032040c081960180a5a904401d00b00018040c03146030080c002d4407400f076a0600102d000700043d02110781d024603041502000c01e80d0035812010300182000400480c2c0610b030325400314920000182e0701e0540d61044d141c220b00c0240c010341d00b03a5a800e10030302081c0e011598805900980200e0f100845800708074000c6490319540320 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 881145107 1250 881143857 881143871
    0x1f060e0a020c06280e030d050c250f02010804240203150109080c0603060a090516200a08030910021617040f051908060703050411040b0604030b0c090a0306 68
    0x21604103070008009642d8442c80c0c40e000751110090080e2a0915061254000b03100e0b4045c0f00000c1c11442101c400c12080f9080c4400e00c4000b884010003011400600c1252000a801e43c5031442d407114803d00300030b429400036802050140d4052501158028891204000040001c42d10340c0041c800c842c00482c2400d6000c010030103401e120b10887c0b1280341c7c090808e52502490300c0a040c1e6200040200c2c030303010b400084040307229500c3d1660b4160251403481018481450280681001520051617581c00154102c1a440d6000c0e550080703640880202d2000d000549000e485410349540301600b0b012581c030580041165404451000d421240c10304158105124180e0a0100110032940342990901400300400c022105075040507174201c034016180e500302c54022052041d450071980d0301100e501d02600d000c011500754554449031007107200d901c0c1c030714a00c0c1c3c00d02c080c4000c5589040085400c070404110074070105401101c695401044989414a441e410308040f079685d126a6104642c2240c485032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 881146357 1250 881145107 881145127
    0x3080c1608030408060103080903010605030d0221030919081908010f0f0f06080a1409011d160603050406150612060602161202030a0501060b09030f0a03021f060e0a02 73
    0xe21004150500042d401c3c14200880f280e1103410603c0018401c18001450711507580f03003074004100a010044c280c4404540c1c4c410b0184d110031610124504c07000804080d414144400d1058900503443c290052054000002002c90109030b458000e60b000c401c2404248401100072120381d1458240b0b903a40d2040d54035125600c03801010a8000c282c49501daa0810b2141440d4903141034100c498a1501660329202d0204000082030808650b401010502c420419504015009064206e54035800b84015210492420382c40d00b111803110360380d080b54510200034181c4a600000c0d0460b001d0032000840132990f2410690110b00c5500138404a1601c00c408400301c01c40e0701c5014024400c6001400e1413482c02d65059101b02c0480c0192190b80200c14513000554504100383c1190651220003080403907100c481340401c5400842000384680309403d40380214440109242001591580081c05441305403040304e00c9000301081c010140304e5840c400018046003c0c01c02a0095502c00001659010300c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 881147607 1250 881146357 881146393
    0x10030804091505090708071d03030a111e03090f04060503010c02061b0c1903110601061806020c09060f0d0c0b09100e0a090e03040503010207080406080105090c03040602031003080c 79
    0x54400d0f4460808135040000d4290440c1d590f07a1f1202d05480e0180320290740e00b03801d4002981d4000c0c0f058062002103003000c251904400652a0303070400b10100c0e042c000c1c1c0d050a140001081c02d24240a91b00184518031860402044810201c2001000407500c40d850f10040f84c211411146848016031182c824810212501240c0074015a40310b20221b00d1319442016155036510080d220714507002034134019030306052298107a161184217a8003a581e4959641c4402050789444001500b40941c80c0f01000650500014100280e200050502c0b6130a0740c5200401c90300422a0707050a07000043d941660300000c84988218020f0070001442c1da8940c00d140d0107020504003404003800038828040b03d81400756036000208012200809004a9100c0015070f000e41103004035030140d605580041106c00c00c002803003001e0700550f03806034dca1161583e62031040141040c015584ea01c0b0100c403c0002c1008280a41c00865101c1f4225180300023445e520341e600e40d526405201c0b0030350036400910b03c1e0400c4291a07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 881148857 1250 881147607 881147609
    0x30312070905242a010c0e0a29070209010801020304031b020f09040312060e1602150c070302071203030b040c02010c0f050306031501080f120a05040e100308040915 72
    0x180d59409000310083c5031001e9071100c10342c400500e81c80200700132036140c5082c0d8a803c400a0588810190900c2c0c031103001d03010703008005429011514151030414207042c1041c3c7c6070200d50446c0a40c00d1400300d055115410f0014000103105689000c002c0c5801503114500028020304600d000103075a45801d08000701558080844403541e9950f0002500250b0340d0803040c0c8407094000c9130b48020f00e45403441c0617a14581d10000f841c094600b0400b0018844500702100e0b44035490541d000d050204078440100d03152840030505c0f0700000055800f1818031134190025000c6644240100e4070301c141c554914010f07807542c5110440019440c1c00b188031403800c15000f041c1c80041c0c24002841a080c00440140400d14000b030f440302000300200000d0195a010803418910140c2031245a10361358407100000d0f200c0010070907001580c418819410001510710b02207409c40b584603540d15007070604022164041d507001820490303051401d6103020001c9a050001400284030315200001c1c911a2035070382c40c01c840380e5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 881150107 1250 881148857 881148859
    0x110601060e010f120b030105012d030209131a0c0a030f0c0f0e030705041103041a06210115060906022104120c081606110d0f030c02010209030312070905 67
    0x1081c04118a0b6041124082c044203c2d09102c001643e00a40b1040107102e41d1000300c0e815800c160001514007103000030005030307040c0302c982004009000726103000400740d1848001d402204450008103c401c6c0458000c4650b880340c0d1825443d00d44a14200186040a0340c09442c0488000782c907580c295050700c03a80c200c041e03400384144a0f140c2154006040092004005030620040c4c00c184115913900740320308000313040300900420000700640c0d401b050a802c1101c00716030003008000b00f2000c01c054070115901c50301c0014000380d060340c0080410340804006080b030140700c5d0b49500150a0b445000050800900803541d1a130300c030640390480080c5006c070b51100b070802e890015201c00d1040d07050130b811541511460959015207520030302d400410000107602c8003ca80c018a05c02c01002c105440e1044100ca61540e2007012a403400003203e916031071005003403000301d11540941001d44d4000d8203c04140e1a546c0001401e08440f81c001c2400e40d842008080d03034a10490042012086d0400c0c0b40d45e0140c80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 881151357 1250 881150107 881150117
    0xb0708010f081b01030f1107060212130c090207030504031a1b040501090b0c030403150516080601022a220c0c02010504030803310204060b1c1e02040611060106 70
    0xb400500c03040190340c0c510f11410151111440410741d2210f401c50703204a540100b9542da943c0450802c800250002c14824095116441c04a1034004d20351072000d4210b0b40118041461a1521a2003002940900c200300c0500205102c0007020500f0140c0c0c101041148010014591070005c0121301001c0c071070b00101c00800306c203000a05c100d903481000c00e001d1f201d00e2600555203031844a2018514055548001d0545889001c20700b0f1085158010a0044c0c445000208041400e100300752421ba90072182c980c0103078030080301548418208400e01e0548003004442481e900e001802140164000300302205258000120381e030b000401600ca5500c0b582d0452504a0301d289a03070340000d1480c4980e1001828550003c401304038100030010385070040c040c0e07442d1600c1c4900da12482e07410301112961426803265150178800200b20900720308584503880c0340c490b1040406800303a000320041c801d2105607007425801210860702c441d55440148007512582d102c50718040e6070302c4051490148140c000c601005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 881152607 1250 881151357 881151373
    0x705010c11160b030604090c060f020c2704150e0a0c0e1308030c1909050414100504020a090816150f021002030c0903100c031107080409050903070b0708010f08 70
    0x80303010042541510f0001c02c0300c5a40351200c000140103000300c0780307010341540c20311900026690342160340c0c2035040b00c20f502500e03940e00202081204000c0880c42d110301c0055002d000014050050102d903920600c034074282203519440e40181c03411140d080c07804007400d5001d240c445080c440a5404a4000d12441d01c01d4421803030100307031980c03600706050002090004007101003030702da01d2071006445e58800800380c40800224014401884045184901c6005900d400c0708a42410743d04660706200c1d4178805c1d400c00d480c1c1c0c502000c2c0002036000c183d081e000c00c52400d10202d85c0720414082c1e41d1407400c461740301c081402e0810310684c4e00740426a0510b010722403400030414410713402160025415600c54030040c0c0700d540b1171044c41ca0314840c00010365418003a6011014014106034400010880c1a580811100075200740805442c41804805032102c20140020420400745030031081d4860101c10a076824584141d80c0c51030070301c605a070b0300c50200f10f440c4010301110010750501d000401d14580209288 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 881153857 1250 881152607 881152633
    0x30a1104050f0909030d050405071502030a23070204230c04120201030b120d020a05072c09150a0207020f06030f130206090303040810061d0a0911060705010c11 70
    0x114607105405480c80d83d00140d18018240305596560401078800c0c040c0c0d280c07500d03000f0307151072860141ca118401c0d403406109840340f00200b5901045800d40b50a00c1d400300d4054840b1140c4d20740440015041c80c200403003030058540b07010390143e5030758031221a230321740d40f15000020003400018903a4080038814403082050300c421007940c055031354080c00d0009241c5602004a4a200540c020090315485590b0016400740d60004080c0c42c43c1e4010010340e030f40c182e154040200c2400d0b12455009440100242c1c0c0f0010b0501080c1c820b420800f80003c95001100406122840840842d200d0300320640c0411400194200349403000b040c1c5000b103036100e28602e4002d2603001c421402911500c6003071100002d400454844400321540698000c00702c2c2e4550b030741c90600540e07810340744d403011130b034035040c0440000e01341e074031915501e101861260420b01aa640b6500c0800401410710180d0b442d082e030f6017000003070b922403600804030300d40140300204841a8000c40030b8990189050b519810394814014040c007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 881155107 1250 881153857 881153869
    0x100b0415030809030307060203090d0e04061d0c1e0a0810050a030609060902031b03011404210c08040e091504080910110102030a0e0601091505061b01090503030a110405 74
    0x980364048602d5495240500200c3d00e18054140020b000500c00000e105029000040002800b840c55a039800ea2401803802c0c0f1003075803014414001160035a00b200420204502d040030b42c071980d4042a2410808100300083e520704141d0100552001c00117041070855601c406115440220720315030980d6a0b00d0400820846450b510010700b5459450240c2c40400015420429070160001d0444190b00c44241219201401a440b614401c0d0310b03100300a1413007802c1b154158456a040b48240b4000d0307511040c100040682c0b51003c00400c42000c20240001399000060000341400c4404071a8910380500c0042c40c203080704603511407007807042c02000005001d4038100c1b03241002c02c1d6001085041c008a00b0346a108030400c030000c9650021040120900c854ad202e101e0742c456800454803180d0780c940c90f5204494980350310a13501c040791701c028481070410900800540e108802d030040321421481d0000d0840b00104022941c0b40c000005100034010540a840001502d84400f140741070310300780c0083c20f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 881156357 1250 881155107 881155109
    0x9061101051b0f120703050105030d0224061203031e0901020c0c040c0e2706010c0c05010f210c11030f0301031101110d0509011821140d02100b0415 65
    0x801c0c0400041c0390f04142c0f0903101a40c04103101100d141e505814040380c0900075040074021035009100302c1c01d1b001d14882c400100c441490448101441c40b00b950840580e440d034200410302c0d500680303d600c00c2c0501400420003103101b055119460304030107a0103003d00c6400702029007100400e0b0b005001c07140c404100402e4201900e2000c40b40000d0704204c0395020349a0322020344c045644050032103184d072040008821006041d41004e40d034412650750318401510000038100d40a45041e00f0180c080c0303c194020340715001e94000b581494116001543c481416a840312406035400e142c442d5002400c4542148401e801c5042410185042c00e2200380340004074001440050200b100b600b48440c080d034000c8210700a050600c2e0103a440d030b07091070b810240486e4130481c3d44034005011246a4005c40545000f4001915620412901c070180401981010000310701000e07510003026001580b0128810000303010380c1c0426801406004030081d01c0c1c101298402a40036014600b411811081401e0000403d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 881157607 1250 881156357 881156401
    0xa1e0e2a090a060f090f0b0a06050f030c070609081809010b071b09020f0406170124030b100f0e0301050708070c050f060f1f03050706050d0207120906110105 69
    0x35010750b40c9442ca107000e052960f204c2d02d40c41410b2a0b02040d00480d0fa007060481c000380e5030b014002c00c0b0740032081c00701154140c403c0100061050198901c804031400c015a044440d4a2189052065036103800044800c110720071110800006082408035040800803124503200320b400c079000d9172418003103004504c00c40c40d004145105c0d038100e0741c100c110001d609001600703640e041103490351404858070a07998498003840b000f0418004038103500c0c501d1518128165203080c05180c244d0300c00510300b40c968074030308412101819211403180d880781d284c55107211581f182a94802c0e4460308100c0303029210340d54050fa01030003a41050104850203030803180c01070f00040a403a0a026460b502e00313019040c0700c40c4008558442c006d420611404003a0310100e03d001d1205800b0036000030f0440e100309140040704d44002041900700c1c11081048900030405455030300078000740035261000c550703181c140b032401c3c401f090300c08130340b0070301c410300440390b1180e031884100100350020031482c24003034045003008030045406 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 881158857 1250 881157607 881157619
    0x114160f080a1d1006080f0d121817030703060819030f020a050321011205250905040503030901050f040b060d060617010c0f020714090a1e0e2a 63
    0xf54021121403044068003480203026141903680025110025000b9441070304100c2c402c51000256108011036240034800d400e813a03841c1c0100c04030140ca0050300f1585029201d4030016100032001c58082c4004075055110b16011950702d2608882c080d0484806420215160344041c080e0400600200c100c0640c413078150920303200c6204c81941c00c070302c4d001c2c51510040250001141e810362041d40d2012218000100e001000311f5a80c179041618061201400054a10303403200a141c204c100380070106c2000b01400c812003100c1c9a481d122201c0680d10195021242640b000003003108035842031140075040000e050340510303241401d0b11a94a61003010301403034030454400203001e0402c291540494014407018525102903c460814580244052460080860030340514001003034408911a8142e83c2c40350702100c6100216802c1c0b081caa0030080c90b4101941d40c60404000412018905010781c0070543e0000c0b451407040078000341400e5600a10401c1c1c1608203403490b9062840d005c8090341c1c0303941034070a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 881160107 1250 881158857 881158871
    0x9091e080702030f030408013e040803040810111303140109060f1d0f0d03020d150f0306060803030709030b09011b0f0215060d02060a110114160f080a 66
    0x103814070a01d1402949445800320200706408088040c004a54600d03000f00310280a00c007210b115803622046c080200c11080a2000c0c1c41e0b20b5850030310081c5007008401c0c40c10700351151903a42c0f455004da0055141a0f009a510800840380c0c0d00a50315643c0c1e45104d601e0820f40240708180e0344071244e010042c940740c200301c1402c0406800f507100200480e0008424460b030366001c0e1100b001401c0014004041c071218003440e602c001c1001030074401441c40940201600c40c0111070450080d04102c02c60300241d61100d1103103040f24a0007038007001030080b4003045042030740785142060446d041580500941d820038401c00100c00e40101c03900003140d4000e4110811387d6107081000c2e005047d41c101410540c149040421207941e80301c111a104810290200c07164000d65040c80071403444200c0700070303602c080c0b440c040070014104003010707103d100c07410708180d000c400e0700b02c040509590310716032480c203070004035406c2103041d0350500005200c8403428180030524108149004002341270080040d9509074903504 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 881161357 1250 881160107 881160113
    0x204050d080705190b09101127130605030d0c0302070509070309051c1202180d05211c0e280204141005011b1212091b09091e 55
    0x1188a0321241032005103c1d00d807913146000310003d0015502541a846103d8503600c503041b0303d20a0880c9003019110726401e100c1d4070340c20440c840350003800003810a4096846c8201580b41c8000241907003080c0f00300868101d080c10f0a161402c031090300083c0c1004030700a00ea101198010a90009030358060781c0d140c000baa500c59090f0080c00720703004020440d01c10030f1070006044002c410390f808100d8543c3e44070803100540403002826070096503401c11401e070228040c95141e1030980404210144181c3c15500e501c2c0c1080c05502e01c1802d00004142c01070300c005906a14514030814070030700a401c082e003c000200401c82c08981e10a8000080b40c42c00038003a44210558075441709011030b0540c018010301010700c103040309880e050320a03542000720600a0801058540c001e410000c400c0d1490b00300c1c4000341c5100e071508081084d2481c2d07404140010300581103d085803900440703200d45e006904800803c642c40c0c00702895030890340e0006403294900102140060003500c1c0130611400c05001104020300c05e41 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 881162607 1250 881161357 881161363
    0x61201230d0b04020918033001080708191101030e10020a020a060b040c0f031104090509030304120806010e010e031006120506130b0c072316090204050d080705 70
    0x94034035500050002516040203004503405100350310980c0c0f001c4058880034890500c1490040589120350010f01111121108510040c07002000074400b101c1c2d0a496004010703885102a0842d07007a0360054034041c041c0c100b041014428854151100851012080e101c401d00340031210401410113403030785241d03030840c4c0c0f08004092000c10181001c650301d40c2d40c00720181d592f486012040f02d40c603040000800789440c0504c03501c034104d0210b0300d44804040c401c62044004203186180140b58610034000847e800c10b82d4820f5902ca48201d0340115a070b8101030030400b210b200c842080c02c007048519420803559982c8068580c4400c403007828160112110380300080c2c1080e00304c802428440c0d207040e0703001400003460403615032005c0c043d03001d84815071940d440100000c00341ba9400340c4900981000724900d042200c00902d60031780980080303030300113943d944d40300555881503012800652158203000b250180302100c2c1d400509801e607003145018900401b251b0091030120300541400c00100303564090142c24 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 881163857 1250 881162607 881162669
    0xe041109090c030f0d140c4c0b09090d0513080303090105010303090e0f0106050306030f01110904180c151413090b0f18190911040506061201 62
    0xa06035040c0d44c1d0b80624141d078500c981942d460001d10701207010101030f1840300841d09210f01c4000501f5192121881100d10310b903004070660224500e5141e00c3c0300020301e005801c0d80219400e850311004100e4110140c00366020415420312841c900410f20845100014044902440c0760a09a4a07034445030000c580421045c1c0c40f9600c00c1c0400820084451810750020303060700e1081d11213040d0036803640343c10000001c045804c031011992100050009a0150025582c40880141140c03d6036520304a55403d4900d20b8020b14440038001c0f503034103480c2ca0a400388605201d4030403a4120000b1503503c0e21000c54265114071080d00345040186101240300d00c1d508000c00d4212060305980306034495403070412040307a00c5102c071510b25001207101c1a14000c40e08981d1458010301b042c042404d420000f20000c0c0380900124089041071203089269050390190741502030103030b21038041c10441d160501c41540c80044c00503200e202d08104060203800350b51b91443c155480f00c0c035a110442122403e00300e0328402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 881165107 1250 881163857 881163859
    0xf060c0f0d14030f0708280f050a020a020a1205041203021c090e06100e0312030a0507080405030f0304030216090912081b0d2003010306060e041109090c 67
    0x6154140c8040c1500088110050145594070300505005140301c000a01083c1d074070704041c0e207242c004500464800c81201d0740001c9400849455046481c18041003141040009100c65465201030418440300c0d2088035031140921000b03500d001d104990094442c00015002070403000940307080c09800388940240c2e4080c140f140401c0f00c00d101d40c3d080c040d54846955181c51084403200311400c40c0b0502c11100300d4100d6007076485089060304c6031401c0003400600c02e00e0000402c00048082ca405030b13010880d000912801c0040640d980c1051014207084e203100070020400e0040c00030074000041c4001080302c92144184403070b1900d07604c0b146000c90a0414149030728004201ea0900820103460543c08005201c3c8500002e485580c0c06200540c1c0d541422108200820b05000c0b0710800c800c002d50040c2510f869801000403456102441e410070300046501c841c0c520507000c401801041703014030402d8054242590303002420b140035541c00040d514107824050144500308041050740b03408000520b00860 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 881166357 1250 881165107 881165113
    0x30f0c131e051018140c0a2c010909050c0406081801060e0f0a0c02030a180909061407020a0b150d0506040b0603070e0118050c21010e0f10050f060c 65
    0x50890710030b902603071540204a02d1051803000e0000c4c10300140304d03640c03101007101049042076030742080d00d9450b40c0000340000d05020f00600709401070005410400361035031005900e1340b410103a00d000101112850b41245000e1850301c014005255959000c0d1001c0310302518103201641c0e1503c501c0050784107441c03c1c0c0c41156003414030200300f070303405031200f40c0c0b16060f64100caaa5603580c9030158000c0d0f4085084020158004002c007002c140d200d40e1a01c02d0840ca10b02d810002c136540d9400700021900003102c1910443e0382c03060000201035940014541010745840101742c400300a480b80b07400c41388081d1a0030951107001c61204100d84800d49035800c2e080d003002c1601c1e100e103403a0800341142e00084414510034011040081482e94182d00d01505903004024840caa071303501c02500d600100805040c00b04490018000b1000340700f40d502c1258405000021080c040f549000030054112710301503d890000000b440030050501c2c80140d610049940480320000d2441200300031800f50700ca5050440c044e40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 881167607 1250 881166357 881166361
    0x70b01080106091a010903030813020909060109151a13081e0105061804060c090f060207030b010b031504051005150408250905150a090b030f0c131e05 66
    0x8a410b40c440350864010800a124203103440c04007541081c00c01c0c4201d80400c1880c0b5091011074800e04040d584400500c81050102e580c5400041d50400d085800b207640754800390043c400361440b405600070419110a2010109081a0350700c2100008a440c0c410f65550200e0054048090204040f006104c0042036600d0b81c0c0e900052554140108400b1407242c0d8204408246241881e255076920f0007007650100e031240c2c0b0786640e05000390250202540400003c1c0c4404510903040c145550010001600109040352441c0b0b0407503041e5205a12102c0544400e108001540c20520650041c1040803240044e00d9600c8141c818042c5a15800c10340d080b50154550320020f83e1404001d0080e039038200d007113500041a0f800d04080e01240c0f00e0042c0c240158000003085558410f400148c0c2104000c60644841d002c2034011500184440d446040b6064482951211a04041c01000090440c0d48040d110f10b4100380d0203d0f40701500600d0340d5410b90b0b52144040c10f1001e001101402204458070188024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 881168857 1250 881167607 881167619
    0x30c06051f050a0b0a12091a0a06090b0906010f0306091b080f130b040804090f0c0e0a06020d210603030507050706030504170f090406090c0e090f011505070b01 70
    0x5001c00c00e00644011800070700c0400c007803400c2c510900456016680c081e281881c40141164030b50083d44a40000c0b079120381e031b0000020000010304041200341c03c00508903141c840031702c8054801990101254502d000104141901c074000c11aa10034401c0c20090600c134a0280114002c0c80f0b550310420781146804a492030300729103c0e994007048611aa1036420a07161a600340301004001c1d109881529811603c0300001840103860b40e0703019018031205410103681c9c42016040e103d48000d14414155030b0702401592070741100c2501100303501900e1143d2550b0401102030364458030f9482001c1808034644c01c0400c84228240c106000c050003003001e03c101f43d600e00c0c1c090b04507000002c3c00c031401c7c040c2900100b034180c428400d5078403c036000a43d082c084040d0392005d00c8683d000307081000c860075081102c0121ba4486000344002080d00c03442c0081c405c052000020102c0f544010410710501049051088081050b1080c505507804854146042c941a050a54140c41051001080c0d082000000109 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 881170107 1250 881168857 881168881
    0x1080705120c10030902060d020a050403060f02071a13050708010207060606020f0312151804050f011817070c0308040501080a06050d061d34050a060c030c0605 70
    0x494605907280380541114880482e01c1ea104210b01581081240c0e4075203070f842e80b003600302010b024005002e07185441d076035080d88403d82c2d01495061000c00c400003010020002e091240c1c44541c0e0b0307013000c21401d1061039903400700088514841c403a2450002d6022a07800c1c0181100440b00562000848840c0d9540e4050b66010350041c080540359a031030b003140094440d00103c1c2c1181500210f1002c0e600c0c24200151403c5640d20160500e4000444404000b110351a0201c4030a8003681201501e602c3d032802e8a0400c1c03501e200b072251104564184000c51032607117407240409454541c00704515098501c0410021481d008031440903105504010001050000940092050b83c1c400c1e82ca0500d41c4d07803103000880694a5520843c1d8002c050014402c011810b2039120440d04491201c9020405d01c42581051a213550900c060045003100c0405403004480c1012680c0151101040010050301d4500082d01ca11858448d9609000c1d200107008201840f0b01810010154414020070590a00d0001c50103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 881171357 1250 881170107 881170109
    0xa020c12011104080604110102120301090f0b040e0109050d09051c0519030c030e0102070b0304140a08040603020d150f0e091906051e0903030705070c080102070f0b0c0c0a0201140909010807 83
    0x81c041f07000c0c4590103c1394800704002d110070303a200b0802b6195034030344071000004000c20035110b14616900d1041d00f51682d500d0160f010480030400010402c1d0f4071606206040405030a10142441180b180800c0b0303e484a07002c065850402011a0303c601006007051401c0c00d030841c0501101060207031002c0105504102580540c0703000b51b5801c401c81d28a8401682d5604280c001c0c151415014000030340000c0121820402e0f0078410707020f0712030445441da00e05000d90490303001038011030340200304c9290451042c070409110f207840c045c010486500d0701c44030f80d000e01640d0003440c001102c81e00006a0345401001790074400a007070414021440000d00302007000b8041502c1400042c04100d0980080c141f040d04468000c4070b410303028524584a40c4000c0d42c00703070b0005008503148014032034001034551082c4064940140107450200c01c502003454410010b0000405003852604107025142c1c14003400901c0038640d41d820308050b00b01c03050607005148140a0802c0c61640241800300100d443c0340301181e030030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 881172607 1250 881171357 881171363
    0x1060812030f010611030f16050d02100f060510050c03160819050a02070e150a1d1810051b03040f210e090414030316140a020c12011104080604 63
    0x2c07001d03625401c0840b035222000401d82010341c81805100e9060b19417000074400449030f000c810078040300c0c541d206800c0480102c2ca0401581010310074000486d424001d44c2801a04880100f04071824207001a07120010f9102400402c400802d07103c00c0c480c02001100e008150360f40c03404014800e20319207100070741e114034178845121490104c400003450148040e5920b251044d000341005c0750a01c030031103e40741d10040004071801c82003900881161229a41c2d45d0241280303005881c0920f240d101c1c00700f88000003800201140c2100304070f004903040046070721400e070802100e0105003a200c40b00000c02c0f4054494103030600e500300005100400c0030703502840517018400c0c140040c0b59090b0b455088003445c1c07510304410100b6414100c040161920080c0d103a40b091040e506c144d4072400754400c40b403544e00101d4510f0104460f0803a80c11003541c00415102e261540c01c00c0281c80c240070404020745554175100c401c0d0003040020b00c1090304550a400090304043c110704036544075640d644c141e665614081c1c0d015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 881173857 1250 881172607 881172631
    0x1020109051011040e04060c0906080402010e220e01060e06060a0906030c0309020a0b03072a02090c07060c090e010f0f050f0d0210020304030b0603010203090a1502071209030212010b0109170106081203 88
    0xac1c01601969010380302c0c2d50141c4540d50400e010000780504a600841407007004000c20454003404059842840801200ca00c0000384080c14081403418910b006003801348034a4040c0040c0491940c40000b003001c0e510340d032501090342c40c1169404c0d0080c0000c4d1710000d43c03004086c1c0001c58401c8042010b180b04401507a81c80803240203603800d1145100c400c0100d1a505900110034801604000f00700c503030001460039051b0700c1c0ca5015242d04044801e020a982c0000d054040c040140c000000b620358058054600141c00081c5000e1855443c1642031144e60301440c665660340e80c6a95595901000d5150003505010040c98003800094496005000840744010311f240410728508051081d24412a055402000a0301c03540e140c0f203503021a500400d055060302040b540c00040c100c0c40c0c081e100c1c0e0310581c80f1001080c1c1140704109030065400310306945030303140c92000b902d541e078031190fa00221007000007501816511503e00c00c1c00341403290040d40c1e203441303410b2014020b0060100114070445060b132207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 881175107 1250 881173857 881173859
    0x30c050c040b010f03092d0c091811060913020c070807080a0f210314060603090604110a03080f130f08030304060f0608100c02070501020109051011040e04060c09 71
    0x4001c00c03203000000d8a4000b03070340c04841c000f119010b503112030400c0740616004508503100c0c59012100f042d0b0440d01c1401849040340500130001400b00c023002514a0784400e1100904c02400c45801074803180018084070194405051640c61b0b041c00c9a0404d0b0b030180912502c0c41100c4d5a8401a510855990f1100c0c4200c00740041d04c0240030440354107540d0140c000d800c907901aa11943c2101d4001d0406960728078405c0400c2443c580155210941c0d640c85460100b1203c41d416140e803907402c4001d20142c000d5008208100c01010b010400c25803003544842410f18a40324600415031100b143c0e0401000c4110000e06a00801600409400355084940d54507070a145c84507a40b46070301907213105004180d031052000c2000203190b40c11568090709914000103240743d55000d001e1a20303030041d56280c64195030310101803140348c2c180408c0b00a404d085c002400444000d81d903290740e44c0c0d00c01091100155641c09140f949401200403200100140e524140d50303400c01e0704110008041c0038a4a5021640c1301c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 881176357 1250 881175107 881175109
    0x30708040b0924270a1b0305030a0c05190309180608030a050307030207020406290f041806080607050a0305090d051c060f09230c0906070c03080304030c050c 69
    0x20980592464181000301c16034280000c20b641e400c01520043c4084c03072004401144255042010300154543d000914010480f414030030440c00c0302e15070074600ca1a03086001d01c0820030001c121a5001c0803031a250405425a040075424800000c0320038041500814440091503804070540050760940c040426803243d144042c94200ca60364424131707003cbc0c2c00c00d0180860003402040039662104280c00c0140c03170702d106540002c04903009508600006c2413803442080c800403107075002c1040e068401d8525840d003900320b90030302030b5402036120700d42c4507231f485c907004c0078170410b141d00202c001b00b140381c0885044d0300341010040e20b5034101010100000b85030500190031000005414441404140c03151031500301c0c0103003070380056916610000f001c60303242d21002500c0490390445400911001c3d07000686881c025078142058031400d094032400007103005c240041460ba050896803000401c0b6982d90b40c44400385441c2990b0003e60b4000740070064080200814544c1003004031524a1250381030340c0035882e20070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 881177607 1250 881176357 881176363
    0x1501080109021f05130303030e0c04060302060d1a0d0b180703020108150442050603070c0f14011413033f020406110303130b1b030708040b09 62
    0x140040d5010000f50022140303e440490011440069807034154074001c0b0403116286081850b600460000c1d90b0b0f810360820500080c407075202c0003441204c060120b64656000900c1602403045030181480e6500b020b81e0060710300100c6210b07001c101412005158915043c901100c000413610300c092030f6031040c2004503002010130004145c0354140c40b4007155865088200000a891038401030308241d0f035096800b00c5640c44600f000071200d441006903000b211648008052102a0700c1c0c2c40070701c01818400b400142ea0784001e4a5005c942c40ca0107480018040c280044a0400d03804044d02113041500c009251030010340140b041d007080042009100c1c0c1310321089405909408a02500007080002d4898a58450a03882c50001d40000c1810068602c02c1c96006488004005400d82c1e890340000c0412800390809d204855980d03113030010394110718015900d1202d104c0110401403006032000d000405940211a034000c40070501d03c1ca8a49a18044101509940094600b52034400c844000114100000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 881178857 1250 881177607 881177621
    0xa0608010932120a0e040914370206090a0b0901080c0c34080303010305160503030403151b030905061503100f09050f0a0615150c03140c15010801 64
    0x90001807803003e240360383d1103d440d0810600c1c0000c01c580c02c08152415500e0b4014115071902500a68a40b48542c0c02400c3c5007514444440040810200354032000c80f001140303800c846601c803111040c43d8951407000509511411700e2041d4082094100405d0340400c2e10064500a0401e0301c0c0d60015480e407400740480d0340118541c01703225034018400144203140101003140301130341c400c2804001002c502d91440d0803905503000526141c0c00400100706021b010440214403101060720840414188000b0130b03164421800050103a510203404040380422592180d6100c52080c071065009c6884140d001b00544041d207401c2e909071054401041d100412809408183c000080040011300b4920704440b0140801c1c42445011990710303034610000c10018420030f0407139543c44001d0002e6803158035000040311035501008005005645080c8004c20303170002424043c05e00c0341041c0407079540620701103030700344d41c8000515401040030949113426030b000150022a40540034031850320741e80741c42400b030032a558 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 881180107 1250 881178857 881178953
    0x9230601090e041b03060c0e0f0f0a151115070f0e011d13090f1b030203070506031504060306020c10050c04052b03052814030a06080109 60
    0x2c8020800040704209426840385580350300f4048a0343e261203410803a0804d00e05c4002080403c00d18203042d240019101d509c0c0e42c811600b08544800c0d0f0b802207441c6142034012a0000b07500c61000881240c080c4c07072514030001c018002c4480444000e0058050040141d840c8804030761540307a15004c46000309240007407800d041e95401780c42800300c40a41046c1140780e41c0d0f03d80005000e00701c822006414018017144078010521400b1410161034400902c20710052200c000c0b9060420078401640d0101d2002c0c12924126041902ca841c1ca4002640348030700c5405d01ca40c06440e01b40000304001c070703c1e009000d0a07000341003680d00c030800d560918410340f042190513114640c400c100c240400d20b0050300080e84400d01c940c42c1c0e5607048640002c0000d4600b035000a4000ca000420150345010041040c0d10352000d03841c0a40e100304907815400350221800c2208440860b9011001404040e202e500c07480003030049000070310040325103045c02d06051005c0c0c0442c4070110b45103c004294802c0f6000003440c0090 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 881181357 1250 881180107 881180129
    0x70f050c0a092009041107060b120f03030109050a1b0f09060306080304030f061107030306032009060904060e030f04290403060c020a080d05060102070510050703180923060109 77
    0x80d078008500341c84d5200070611a4015552150b903909140194013801700035200d0140001e551041c44100a0501c81e0b0003180401c9074447d00780201841d02c04003da070b04651200a0100c0c4035140e0080030300141c003040700440c514072064894011030076480140e003020403d20351184210592513101c03c40955586026a030040e5001700803c1001520090100d0305c114000c0c2e40000303a401c0105418000d9a111400030f400082e2218010b01c2440304050f450202482010b854030090882040414a011402032519100f119000c00180501819070010407029920307c080c2c9640f044402c1644615807c81d0160b9000401d04003210380b803602003500a41101c00480142504041c5145d03078400281010405030720442c000c1e540483c0001d4200e501800021050900119003442e001c1c000a00d4200e09501142c801e100d102c0161440c60f802404444400c0d401d40b420095147c402200d40e8040c2d80c0a5201c1e528645c40c04c16807010714124019035006900032032200c503405481e40d100441d1204110b0140f048680 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 881182607 1250 881181357 881181401
    0xb06040c260402060d060f0801060603050403080f090c09011e080706020c060a1404030809040b0f0f06070201030b10021606020304230d140c04060b04031e0503070f050c0a09 76
    0x110714103019030252004104a25290014621000741d40c4135900500c0b5018003801c00303101da00f20038000c0d480903206501c0c0c10031540c509514014564140034003c00842c12001000c920404000e001c0d40380b42040191880c1100c0d69910718501440724035008400c8059561100130aa805000c03602d0011240c0d41d900401c04000e8503400c00102d588908680e805000d420041044040002d1000d00025800340e00c0c49922031001c00280030981d0600c580c41d40c450316082185c0d140d02d0b030f2201001c400e81e0f0003c1d222035881d1400d030700c0140c0023000d5812000e42e2000642d03072005001c950002e01058032002d002c03c1016003640d2076030180ea1b41c0c0940e00031091448840303250402402c40c1080ba103825800010031506000d17a20351a5442e40d00c80303942c80503501e42c220030302583c0c050409000d08002004800f40d05840d2600e1510b6845110703101c40503198072201648002401d00078104280d54409800040140350718505151581d911001385c406203000c0c0e4050800040c03510518071402c1002c840200540183d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 881183857 1250 881182607 881182667
    0x61202040509070e011214030a2114040b01030c061d010845070614030702150c030f0109022805130e0105030712021c0f06090b06040c 59
    0x50500244011428825444001815429041454000e200984010112041500f007031144a0300c2c205a000440d40104120340c0d055074482c000781442807032b092880b460041c4400101001d040c42c0080050841050414481404451003865040b28450104040400c0d580c4400791009010814141000900315020030110350050503c03130382c00303580a203805d42045140182906406011741101c10300a8848089403826502d00740c04600c20844030700100440d61514100408020f9005644026141c0110114401c1c9008020440d210004481200c84515200c9949000c0da001181e04880c0d0801f0080005200f525034400c6a080c40c0409084a01c0035501d0015a449000581960000c0200c00c0202c100d40045010b00640034059414580c5910b525080c100b41c60251281c112200c0904284001c000583e202d000055814030480f03290646144a403c141c1c0d0720030058140503202c1d0741094409410080c074045900d101d5101110304019803400c4420484120001d0121051005030f100185085 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 881185107 1250 881183857 881183861
    0x3030f020f030403050c0601050f060a0c1704180b040b0f100e09070c060509061e18010204120201030c09080c01030e0a0c0f03050601080610060e0409020a08100b030106120204 77
    0x2515112080946410310204a210955000300d50a40026a0209801590300e600303000140c0100400c4070316400c00c130b910340d0005060744201c6503031100340440404800c003000103026514121001c40c021a944132f907604c0da13640040c03001c10910143c0c013034a8814600200e2800c0e1155001e840005400c0306078003549a81400344042007072003507009000c81440802155074038045424425050b40d611a0303030310041490508207446001c0d11030500c54128000f000060301c0301130111860001410b580c820161624454086141a200783c0c48400d540002804941707032180342d0300c5030384880c401ea07401c00890300c42590441d6031204500410178640c1207807804d00241d61094010012190310002035490b450410fa8404051000b180c0c840d0840d495804070410034008244031480c010030400001c0d01c2c0754942a4040701524100d030140c3c800307004c3c54100c074817995100c56001e08150340e07001d0544040307070343ca801041da9115204103800d1800d0b42031410090b09030806028210480d42224007804440039a0303820080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 881186357 1250 881185107 881185121
    0x1212180f050f060a0b030709060513090311030406033c020a12060e0103060509030f0304120e030619050702010608070b160b1315091e08040b0a0e1e09040303 69
    0x900c2d215a4034a0020444240811030282000c3c81d00040c00002c108103160402c0d0b940d610100c0400c1c0391034000c111300d4454100c108003004000380d0006014007107140684200111001c2506184400300e000f01d00c40d034042d4004d05010b00a02c40d41c500c1110078024440c040301201c030002d69141480000841c044501d50040d0542e03401c203040c42100c0d6440180900101c80c0f01da4000c05890f40c00c80010000d10003944115504600040301552401c50b13070f508007444038440904014660021500340300a15413080301d9058405070010180c0740c2d00d00701b084103001603400b40300c01c3c45c0c00e0f2468540482c1000d801481758600b10b0300300501400700d1514040680d1169088086581e0f0004690264900040c6a99520612404e00404030340c15003100d50924940c00d5070382810003820a450540c4c01004120310381b80390090801105403403850843c45180c621000c0c00303540e00201c0241004691460480d402400c007407007080d4183c0b08003500c3c010240c07007200144990b0312140d4100d0407000128001c640f00ba00220 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 881187607 1250 881186357 881186363
    0xe1f030906020f070818090f0f09030904110a020c01080601091428180b06091c0b070c140114060616050304062105190b0112091212180f 60
    0x14207143d80c1c4031603020194061001281c2003030001076440ca40b0407503420840c40106081d2030303d01c02c52408113101411010081c14608081c1c07420b4001840d1403004208a50a003c4040c009011007001400c80805d5074000c40658805802002441c00c0e82c0e500c501c0b1200d1140c0c1050707441c0a00c6c1440c141125010708020f0562a42080c8400d000c2207070031070320b1802d2001d200301212a00040070b02d410900a018403c05144031502400c11114910740c0c1e50b01402e443e0f1402048a014103581c402d1b031a00c0103522151600204800212420802503a802441040e215801810142e1004185543c054221403501c1071032004415450082021820b201024081e0b01000306030b1581781c51906d0720b5551444e080b6501c2540040c06d81928202c42d01e080740d00c04040e0b030324888000d10603818070401c1c00b03090300c0d082450f00e60f4140c0d403803140007120b0b031003260303600c03603488401c40b0800901c5100c0c204090802080ca1b1a0350105901048811000b2841d205440c1c4205d01080e0a550403602a602d00d40b0300c0300345050503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 881188857 1250 881187607 881187611
    0x302010b030a03200313060f0203090a0833180307140d0e1c020402160609080403062a05070c0e07032913050615120402010e1f030906 59
    0x500d6a403010030180c9581070083d100c44200d02001c00d05808004e100780c00d40046904203014200192046501c148142c5889050650b00e04d10495812031840c0201504968084031601c07002800c20000b082c0382d1100c0d1140d0f24801361070440400f955140c0481850400303810b101b440b00050301038014150084c0741c81d40c0681620700d000519107c08c0e000c01d03c2403e80d140244c12584031207a01603000240c0114262054541070300407400c000c503c1ca503900c010340e0b0280c001d0340c0000c0c0b508280c540700344c3d0294601d0384c031840030800a003640c00e0484454103d030008558861900c01155500c485003080885200282c01c8010b85010b055081196140c000000c11140c42070f0600011884510185009128245982d0700145c0720500c620382100b480000c200b1018107a00c0c2c4581044513031039420f22a0708128030900c010455498200c007007200c01411040810b10200c011500907080d1260588540c001c074003da8424070502d03d48400c21044424070218064907084881000c0075040c001e801000300b460040b100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 881190107 1250 881188857 881188871
    0x3061e0e04171903020405031b01051804060f0308030417071509030c02060d090c05060a27030b01080303040b10120615170304050a080c0607030c06090611180f1c030201 74
    0x1076107005541920f40c0c000800d401040074002414200705400d83e0020510348014040c11442c0081d04c541b14a6003500f15542e0ba03e10141c80a44031604003400800755802c45545990743c0f41001d0b40107401c01d0b60111103581029069001201a4400343c6030701c56001030303000000240c0c180601c3c0081100c00700840034000c0b05c29202e005651200c0281c864503601007800305805150f407810f0700200c20960803040c0704032030510810712016800585203d1550720103102c01d86a03c50070140d1040342c442e6500040c1400505400800c005d9008006140074a200d0100302c216a1503001070700c607080c4914007510b80a581c10605107030208030f01e50880100c21031000c00916120751101d19503100201e60b10182e828aa10010307007002039052911a03c00185a04070207009110300318000690703103214040d0040c0030840d85000c1e0105002e2a40c0c001c0350303510740c010410800c09011094185a540010502074500d150900400f80d580c2041c4108043c1e52000410300c0316200048200490700b0201c1d00019000c565950702 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 881191357 1250 881190107 881190127
    0x80d020d051819140411181c03020c030d05040e160c0b040809010e01050c0a0212100606020d09170606041d070b190c050a0f0311030a03061e0e0417 65
    0x80e0014010100c540f805600700050180168805050f05008a20b401035010090b1810405e581c1c4100307183e103c1c0998a021000001c9882924a9401c40340060f0400c8443c209600081c444508103001e400b81c0d88007020743d000c2a2014003844c1300713002183c0c288500003901120003000c904929411800d01100d0110340e80c40c2d00d40080b034110380848440c01d00264003001076802ca41600100b2909180c800e20b001402c1c080300c0d0b10380500700c800034001c1804000c800e01070700c2c0c1841203070f04120511004024030b56445c0d400a603590301041d102408503048107804554030448070b411082c480c0540c40100603d440f070b4020300c00200140594040d51580008020340303004410300a2400900310004c669440e1300790600e00a007400b01031384010003841050407607400081c00100d10380e06140d822141c80014441c0c1e85c02c0981e00641e003505003000070f0000245080701a50140e100d1020b913809100c403068010f2411140c070030500c029005500301c11800c0c4d000103000445481901c0300c0c1c245020b01d801d0400002d46 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 881192607 1250 881191357 881191369
    0x2040c020304290f0a08100504090c1503240f0905041a060609040c030f140709031205041d04150506150c030702040603140609010506060a0309030201110a120501080d020d0518 77
    0x1142c2e60b00088a0b0007d2024402c0c0d910300c02405454100e50400c0440100c1d640d41c030075060b40c0e1003001d40c291114940050030f14042c0d402118109454101451202c002d09001c140b0b40e0704500a4114511001780f0124400140d482040c0c460f0f940704407140c103444d490402014070940028800303984048100100801da481c1d5024503284010303140c0707001c200c400a01c0300d02402c0e40c3c848076540c04041903603000c1082455001c0d45c424101d9070061440031300d551180c1012a414440d0342c00c042190fa240203d41c02c2441740b9030107840c2c8154080c0c41c80003204405000104203581c0e040c0c8000d0790103105111805100381a400060200c41c1524080b05d01c6c2c403000d40d000c80c042e0b40c4594801e44480d041807500304040071061207441c0c2d200036680001c000724500500000d4840c0540d10340724040690703882c602d804050003503215000c86030011020b5507c6260080000306800c1d001c40703080d8606030420000160748039001410005121264010740010200c0740d004a5054004000d4440841c5114180410301d80710b00b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 881193857 1250 881192607 881192617
    0xc020f0a060e04180201051204060902040204140907020d081512060c090102100603020105180607050a111002060105180c04170d08091b0405130212060402040c020304290f 75
    0x140ca402c09414940c004000890b03607000400c08001d0400141000140ea100007103030841001c1c00c00c62040381c2c6680c148140103000821000b90460b10009e8080b80c0707507460810405070f040382190100400d544085c400c903203542d1350001c0c3d00c0100e441c90000c038040b070a04417503624003c04060710851031342c00d58005651504405940281c40c072880002e4000d010350341880950707103604070800c0c14805145141d0000701284618446050b0744800340070904569511841244d101c10b80090489140c24a03a003031051030803114002032485143c8048070002c40b04e001081403412108001c000c10018141281c1003a140c400090048c204120300300804101109006000d0312a0074420303004124844407000e026001c1c0d100600501e409078040e20510580f44030a1101a0350100c2c1074a0118071521000c0c103840d11044684e000039406040226402e0300d441c400650548254000c45003404000044201a0b880c1e00c03542c01001c010840c40d000806400c0706007103c1c444d060252036000d03031138155600d0000129400c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 881195107 1250 881193857 881193869
    0x21011100501030c05090907091e020c0601060801080d12050402010903052e0624121e15080a0f170c0d0806030d0e2206080604050601060f09060c020f0a 67
    0x1d640d0050080c4904440b200b0060181a2510307209810700c040d03c1591504588a0581c0d156103401041414440944011010320047e0b20709545400d18100ca450700d0351024000c800004082500010303581d080054103914141e8140c88070000b51030480d0542025002c001d00c180e060008903031f00000054410440e80020289160403010940804a81c90f02e07412030b0240c05861490070080140306c483c030300341e07100d5003004403180000301c42c0d00c0d030510195000c0c0c0c40c55200384000c904c0c00c414041e51001c09203401491075041c41d4100505520380440030203045003400b408243d9402040c404000510400d05001c64901400c075036000003040d12840d680c0c940c080b48055200d078002c4186000c8150708005400c2d0010400c4014000c2c00c00b1034600240850049030049100d0f803007400809050102c0c07152080d108038030030701c1d0500800d03440e0380b0650350341c0c482942c04546511451000055030380c481c8010800f41942c50782e4180c900c0c9c0c85c128080745c040000780004d17a40152900110b400664507400103200030f000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 881196357 1250 881195107 881195111
    0x40b0304060c03061a0903120a050a020c030118030c0602090d03030e060a060510030c0e0a0311010f08100b090102030c1f0c0804050d110304080a03051309020c0a02101110 75
    0x19103494070400b6500284007110074142003041c24414103a80251004100790481c1480da121501036000921300709841c2c00c2122a100700051142c000c0354084010710001844d034080f1030740f040d011010b0608a8040c03181c4031864035a0704000c000081d101d12030545203280110300140c140034407030300091201401204100c1c007107981c861051810300030901102d0b43c080c8484070200b111616000100303841800b041d8441040580d180508001c140c00b07805003244003400640000c1c000b0b900c0349424034a00d04114480c501107800f50300e4101940e44030741c3d0701e240706548007030915130910718015401d601c40c0c01001c440307410760006000ba4290070350704010940790710f25030101d064030039140002d05508545100c440001005114420440454000640f501d0500c1043ca0069501d012140c100780c05c41c02550030419040c01010340c00828190302001a01200081800c1c4205c1039641d050900124030800380301e4030082e003056031580c0151806035a40303c54203a1a04000071540d00040800d03003080c416040c04c1c50096 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 881197607 1250 881196357 881196361
    0x110609010216300b0601050d060e040b0417040609090b04090203011410060203090114030a06050904050d0e22090204200316181e030b0103030809121602060d02070206040b03 76
    0x108428611030104074044511090402513101d15400c444001c0c40281070000003c0c20a190b0003451344814000d00d440c0001031003d01300b52038030804408040c0e41c246e8146034408180c2001410a1045608940b05600e4215986252084030300151801101c41d90380180d40d604c0c0d12000d6203080c01500b200096050503010145400203c040820013550030031001c540c000e01076000c03a40d03089001100a090a00c1c0782603201c0c0d80c1c009420029000075005550030142c0c0200780402c00c280020711480c900070715100d89106100090502280e0700c00710070503860214010a91501c08001680f01c000c80da40041c001041c02c0f515013080c00350f5051446940800c2607800810070240d031000244a1f400040c580ca04010010104141c024040c03440c0d0003000030070818685032645a4400f01c04040c01540d02c82140303602c81d03941c0d0801900780e00040358000484e002d4050b840c7c2d504581d04040f00c240e200030580c2030112807100e80901c003050704000d00800f9419030820212016a84d450090070007025840304955881c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 881198857 1250 881197607 881197649
    0x102040b0a0c03140903030412151e1a0d060504060e160501080c040605040e0c0403050d03050702010b030d08181e010c14180114130f080d0507110609010216 69
    0x8801300c40d05142d00d00740715042032035402208075000c40d2080d95404090703014a0500325140c140a504030301541340b07410032060b500c03541140c0c650f0181708100801c0005025150030200d0300c050440c0034541c00754881c60141d0001e0000e620103600a405080002080101500740360b00c0c0c0700e29400340005140310758404105941c7d2110182d60b10089a44402e810545008000307081030096004111006402c100010900782180341503500440c0c10904495071007521290240080c5030640d0244015400d00c1d19148450a000400a02d05140c5544503042c1d030742d0b03101d9079120b40a480c89030301c0d40701d0140801000002051102e20b01d145d194100c00011400c1c8007030ba0207017810818854520b10120f05010081102c1c29400c00c1c100102020309001c502207500c9544c8581700c0c0308007840c6804080100d0341c042104240681c1c00c00503214000110b60141d01180c0301552a8001c1c03070b40082000b03c262024004038140a000380042e0341d0b040c01110b00b18011001c814000d61015089840c03400b01d200701040034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 881200107 1250 881198857 881198867
    0x21060c03070315180c021507140c030d0207020a080f0d0e0d1b3b07031410060f0e0604050f06120403110106090c0f1d06070506090606060c07170102040b0a0c03 70
    0x400191b000901d07520740201e2500300c030104000c190005000c82e405001c55085d0513030702143c801521600681c2d0b0b840f4480752040000307401845099000c1c040b8818040f920030740000c1c441455041e030704003c050350048100c045030242d507607210031070700f05040798100320000e001c1403500702c41c02c52082032241c000e5017070007003118018107281e48014510801c0a031000b040599070030141b6010f00800c500c0601940d9217041a4050505100000b141c170740498200700400b240d95140340151040b607581d501800f100030600b260740c00822522590710140401c002c010510701080c08165940300500034904000500c0941200181e00301c8040d030206510b0204040d0f605002c1c421030000d030801c080c041007010a4658000c00b803401c0000d01c5410312840b0b600c12450400445002001004020040360b51440f65203000c0d40c4916090705d03100c1403446001e0100340d0603d0304c2e03800e44242c00c410724000c01c4150302e40f90841c00048017540e07032a11595800c0001040000d02c240080c400c07c01c4640312030244800500d0002c03c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 881201357 1250 881200107 881200121
    0x91e050604051006060f1107150302070c050301061404020c0c030a050f0c061c0f0b06310308160f0218090d0306080601140103110301060306030221060c0307031518 72
    0x600f0919050702403180e039402090034104000545884d142c11480744e280146025a10340002c48400142d28001498550680080841c644540c42d1040446d603a00107140c240c9103d0302030404100740c0301807000c0850519502134002107039200100c03000f41100c4c0002c03e0a140d50781c4400e480903089000140b08501d002c20281403000b1080d60900c0c81d080194003c10401e82c880342c0c0840b10709464080c07040c80e00c1c807240c01403210001d00602244d03449441c90081114145464101d0380540030003c0940759180d43c1060942c1240d8009203030519207420319810700000c2164000c11100601e90650000141c2c44040b0065880e9005901c41070490814003400341c502042d81485208041c00d2040c00e119048002c40c45d281198090760b984a04030100c0401a4050064440005400040170000081e0140d0641003c82141d0090ba1045200305c9940e4009079040e19040304200a0ba11030004904840d090320015503000c46c051400240321265110b00c0b072002d001030351145200c2c0707203079213040c4099456521400d5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 881202607 1250 881201357 881201383
    0xf130303020f1b1203160e121c031a060706050c130902131502101e02030a1d0d080613091505062815111c230d091e05060405 55
    0x1170035464841c2e1030000321703100100714074104807280910001e15283c84801d032001e00032000980c2c2d10401c50b10400203002c144500307e81d0000b800c2c8116285080c0051060980842d03003d04a14640002506d440703018003c05003940626035401c001c0403040c1a03041001c10080d001000c000b60b600d0841a0342480200ca0a4010024200310031010080c07054000a011a07070841c17484c400309900b074400301b55600014100f82e000c40f00900020800606400550044104e00c0d00300c19403585c0800c84111255031400502d05850104015001040d13031482e20000c4030807400307014200860308000d1030b6200344a401c4081c1200c0107454403a414800c0e0751800c1c0020031b1b800918140c03032804140a18003032040c51855880b8012020720b5104551400e5449035852803100f407901e81c11a05070b0075083c05102c420a9a4401c450000390842031300804207150303074002041c55078030003003260f042c0000e210881e0020505202c04540d611030842d200400c00c0d50201c1a05102c0307024401601c0c01e031820b800c0076428a50005654 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 881203857 1250 881202607 881202643
    0x26100f0306021c1a19080a0c030605070206042004020405061c05071e030b0f06032a0f040501030e0c0405070201091106030f07050a020114011215050f130303020f1b 72
    0x44d0214190005843d200d24000c0b180c2c003045400066a880c1d401c9511742150f141c6015005041e418040e102d01e01302d00b180d106480401540d9141c41c01240c85a1040c0d8008002000c402804c0c0c0038602c07103604c81040050000d00040c501a6180000396040e404511807204001184d06170441c00b4455114440d400880c5003040340301c0c40340c282c0c04060040c0380c4d06822414195100d03440c041644840be0f0b0381e040154083e04042d03503030821441030b0404540904000f20030982007d9210302e255480c1040d10803c0703030b040d03035031504180c20310006501405a2007004c12040c030541070444400d81c2e440c01010301514482e000042d20f003240e42840c0407080b109a40c154001d660410500c034441d070f0031040b00f980c0042c1602e803854503800201c9089014245020116100312803400005c580481c0c040301154065100d443e0490907030403010813800507510100c5010000c3c004a000080010041d11b4141580030310034500103140a070404080403450b0440803558a21401403c10b903a811003040050300d43c090303002088 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 881205107 1250 881203857 881203871
    0x702121f050f0a110901030e0307060905011e020702010206040209180d050910020f0a03051605030301030602191803170f0315100804051207061b080f060126100f0306021c 75
    0x136000051081401303450400d5954890520304010038421303205a0350b4401414024800c0c41d04160b8081c200102240c0754881c0344061108070401c99108a40c0a2541a00900415038a40d020080d00140043ca03100414502c060070420f90b84051203810283c0103e526580d88800412040c40084111091058191741c84850400016040000c0c000d529692600d480fa0b40c42c802c0360030011030600c1400e8010b00500c0040008010880960050322004d03545c240700300b0502014800032180d04d249507a03610340b1017546103014008206035016241d0030b02c032000c25252030542250500d00d11a44200c410910704e5070b15a074902617500d0483c0700100042000d282200d01400c01c1e445032600c0e001019080303030650000040d04410810f250300100c24290340c441c1c098849812154014011480c1160044841c286000005e00c1c20b600a01e10b8044213121180c01c220200c00070b05c4421b405840c098048030107105014000150800040c01e854091403064a005d03842d2941740000d901c0c1d41da6240c407200c21440c1400300d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 881206357 1250 881205107 881205131
    0x501060504080303011412070e0405190807020f0402090a290a17060f040e0d08091903050c012004060207082b0903201807050702121f050f0a 62
    0x1a241981c0306401b000c42c0d0b200c2000d00041d00800317900301b10f01280c0164500001c40ea00741288480c8982e005400f50340004070380380d203030f01a0a1003185c0d0013807010100740144005410f1100718150320200c003400040c9840c1070080004d10b505210b50004102c800b2840082c0e01c982c89165800c100600c6604041d4105100b00b80050600004401c1c03014010904000050460355021034250044034040e00400c0740304407000e40f01d41c1f00c0c250300408802040c40364002c561041400111a866a07800c488052901c0e401903400b192035600100c00741c1e44031b64903410410f000b03d81c0c841880c184000e50160b440e07a120300c4c154003e0f0030800554040032140d0070401f102c1e02035800142180100d21090b40c0e8543d141e1914100503101d803400340e00040d11040a050b0442c0e04031044500350510480125621404082292071602c0290320440d109000500d050011032f005080042d07030083d52641c40d1043d52840704d900c0c0343c502100d204020614090fa925803080c05100710211a14a400040f441014051040f201c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 881207607 1250 881206357 881206363
    0x7031803021e240405220f020301080f0f0705010507060209040c020a1401051509062403010f1a0f090a03121d092a0d020d0b03061e040807082b050106050408 69
    0x111580d4010141c16080102039006d451040342440f48507441000304010186800c00203400901504101d0310482015040c40c000c00a43c062115404000414500f810030004454a4200540c1150f0340c94007400012560ba0380c900810001d1150b0390300414040c503540c01c0c0340d4031015040b001508079924080030302150026135246004a42c0050f00c061009495281c041348a501d403600402d040340381c0c50150b040074802c0410081d07048580302c0000012480d141c0e041311460041e03c50f00f04900c4070042084510812280000e4103549100520f80886e10350382c0c1d2581d8038680941e41ca0400003985100007904103680109098017171100559141c00d142c0b40c080406000305041d004880c00c41d0400310741c101040356140c0c00b101c40310802d4410a40d2106504905800544100c0315078901ca405074000040c8002c04000032040528805109200aa2103d840d103c0f600d07800301a041d1962030041011104003141e01028108421080c68880c0d602810311825104a134810381051042040400003045045000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 881208857 1250 881207607 881207609
    0x3040b0411011209030801060f031401090f02040b1603031503050c0906130606020c1002010509060403180906060c0b060916110106050a0602030310081207031803021e2404 75
    0x22901c400010003030307401690481c01c0140c20100301ca040050b08002c0582c03040049040703601c2d45c0c441c0740d0402c2c0c0901c0c059040da44440c0300f06000540d008010458100c2d141c10125030440701e034000510346a00c4000d0003d003a40010b2803036012399607210903076007003550600c1510540e000d191417900300f10381540c0c0c0d40c5807901d10409034588962082004a42c056803a5942c40d403038180c03801d07000c00c80140d07103031030103502c98404034032583c0700b008042c12000d840c078010b0103418030910000028100c99607503540d00b81d84540d20348204c04503440780c6800102d040c400c0b81c403503c405400a41c0b502c90380070b81545480340388440010000e5004041072002c0c00380c0010b0810b1004801c0006090640c3c102c8480002c90303004003081d9000550212091078009a855000300080d40945140da072103403001c5454582e21039030f401d409d00d00b96101040400c030b8400883e01c204039414001e400f5882c0d0082003a80c0f900040d410180c4101d010000c00310f009655500c0345040080000d413411101500642d00003c0c084d400014026 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 881210107 1250 881208857 881208863
    0x10f1409010620060703142217120106030e1c0504060c020d150b09250c06021204150b0307030b1605070605090106030c083903010e030702031203040b04 67
    0x480c00041d8078109426484100c9000f8403c840e028508802c2c024040c0c00100701c1180c41d030003664003040071318001c081e80800404042c0c08141d00101596110088400c14001e4165101c0d0140240140c03a60052591402017841d9900821070544c0c10302e40c030f82402c0540c1080700c01111800d0b1090003054103e0141c0741180e89070300345842040194004103120740030395500140480351011090080c15025407065040d54010740d00c2e030300d00f5a208421520300c5800750648e654104521020000c04a106c1d000500725184583c1c409410110710310100c0c50070351400d071011240d8040700000b0383c4140c4868800c078511500201c0060680030702c1d40e110380212000203001c1c00142a105015031041a0054080346c40741603200000308510324040244a00a0000e4001110b0555016500140c042400a4002d0b040d0280c810b8100e41951880c070a50b5028410482c80b0140b408c16280c480411741c1d0030712461801e10112005180c0d1803502c0d03c100b50030041d00d210b270700004501c1842400b010849040505504c194 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 881211357 1250 881210107 881210117
    0xe010c2d0503060a030c090c180b040b0310030506070906021606090b0a0201090b040b0f06060f030a0504060b0315180307051218040617010606030b0607110a0e040308010f14090106 79
    0x440c0c3c03000c1460b2200c1c60300098031040380c45200041d03d6074181d05c40184c0a08507502d610f00341000c946001e044000a00c1130340140082844140151000b80008640000c1c14883d5840210341e203580d000d050101c21241813003c1581040108400d0780c05012540c200881c5200c07486e07140c0e05041c0040e050085e03e000302e00140b00302040170500c0c14000d60002032401d420482e21031052034545812400400211109405021080301140450801d00151070482d03405140c5941140e071840c8100c0c005090050060755070343d032605e9030f0480c42d48090080b4080001104120404ca00d07280148003075100c003c40c124241503104200c207401040e80818081d0528844041c010340c0c4800d00040e8070162030781c401d4655070062520030001548040c01d544075111590040090000c1560342c14140c2c201c82c1d1400321240c00140c05c0040400007540b94800308601e132001400421125180c90b003c2e5036062080300c02301e001c2841400180800d95500c03190728010103130740003601a400c1220000c107206500c11320442082c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 881212607 1250 881211357 881211361
    0x91d01053607180f02030f0105012609030d0b0d02010507020d060f020d06061101201c02030a02270310050c0c010e0c0f1c0201050304150e010c2d0503 66
    0x41c5540001c4041100c203601141d100e00d496620f005911407660900b800b500b803034085940004886070090700c3c4540f44000014900ea881d207401910ba84081c070301d4a805440e4100c842400076400e00000350f01410400300216151908603a280c0f00319000841114451418900d903000183e034000f0464050f19070554603000a149a440e091f005030100070b00c01c4041d00e002003005200e103c0c0c60f9000c44202d40496485114403011a00032608031554154032004071400ca0340ca0302c80c0c0d9001d050041c00810b420340c0501c0182400000b00784c1c102d80050719500005500010206100040749481d0500540d07285004a542420180003e6a5000c0c40000c10b60054a440000d84e5002d4160306403000003029000074080c080042c0e000941340c1c0c0f05001d0f000d00c50003156242004a003802c0311203a281c0310440308024190300558006441c40d800081c000c582e0700000c4011051809258011201081044000400e001a843c68040c0603480f10903154400c11500000c060600d003144d4000c0140c4881c0d50910595075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 881213857 1250 881212607 881212681
    0x60406032f030a1112011a090910140a1d10120f0b010b070f0f020f06041706150607170409020c0705030106081501090b011206091d0105 60
    0x300090200d4940e03180d0304580d1241c0301c0d0901c000e5100e92280c10080080c28103000c01500540181030000b0343c8401c1d03040040c4030070741c150208041101880d146c1c081c1081d40384000a00180d404498414140c5804a0100000b81c00300e4180b040f140f100712003141c3c4942c20804500f038500700301035210b0ba0300001000884c41d00c5030905c041d540907000a1880852250207420000114007041c0303011141892060000100008404156181c2070740c030030480000c400503516984000c40031501d060380d12200d001c4a000856983c0801080204060300d0211110304a809185041100081001501040e42c041145180c0d4a02080712042d41e44130054203e480714094100710303903018030740007000c0c0d0b14400a000b491400f07000460404582c003c40c024000740e1b41700d0800c0c5440e48030044d440d024801190005205c503030510303002005103102c180360592050b146021001e00782c801c036603c04040300c0d40ea01615804c50004034407201a140c901d00c000d100300d003842c00b4500d898891903850102c1d52100c2c40c40714041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 881215107 1250 881213857 881213891
    0x191802180609040f0c240f0e151c020a0f0201050114011b061e020408120a0f0f02010f060f030b072c0d02090f1f0303050301090e0c03010510210206040603 68
    0x1b9101101040c14140300d540d24240d524295903e0000c081822050b80f0704a1900c10f92401981c8040680070014030507141c0900c0c4001e811180d0516034030310400414010340c45035031026100055190381c4908c01e00f44050704c081c0c00c507241038100e20025040000d45400720f9801024641ca01d200081d0300c0342500003507040c4080103204180801ca42c0e4030001d50746014441c2160042d105550080b019a85414654141e039400351285580c1c0e000400c141084000605000785610800005e07540000708204010b0304080c0300b00c5010fa08654070200da02c45061081c0540d0010340c941c4140d090500000c090454121b001a05801c061029010080200b0445841c0c8503048440c0074954094040d4217181807544107500306090458118903654140500c51000e60b001da842d1034100c079015201c551860b402c0000348000f801e11215062894460701441c0c8841f92000d22a0030b20400c1c442c01c0040f8500d080c0701c801d02d41c01c5103220070304076802c40091241d80566038100858084481a040c00a40c0101c503949500d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 881216357 1250 881215107 881215109
    0x1120f0f0b01060e04060518060f0307120308012103020c06030c13080105040210020a030507031b0b090705040c0203040e0f0a06030804030303020c060f070e09191802180609040f0c 79
    0x2001800c900000f082504030700d09020f08101150300b8840e240c0c903102407190101407603804018804103040420710908100412a00b0030300c0180a03a01c02031788940010402d01c03000c240071000100c02c403004100c0c07043c40200700d4030b00103007041007149619001e4900039928008413220741d00c25000007011504035920031007118403816081c180c070a00c20307664500c0c290081104813801e0f40940c101e214110b058038408a000201c031030381170f1122402e02d2450f4170700301d419514000c00e208400000c860f58202140c0c0c040a0107124000d05c000628485041005000540d184185450107550003400f0034404d1140a80400307a101035032611000071503489d1208030014204d035a1000d002841e00080110034144e0580041c141c3c175110307100f160b055490381e003e9414010412513244c0000b030714018404d80d091820150072500242511842202c90305070307164060898540e1100058040c1ca1150b1040850030408084030440414003501e008174038043c004104000401403009020748118221b1034100070400c10480 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 881217607 1250 881216357 881216363
    0x201140408010e0f0d030207021c030e040e100b0105090d170702060f1207091a070f020a080f060610020c10270608060301050105060a030c020c1005070b0702030301120f0f 75
    0x120400581c8403e0503210b14040956100c240a1180c1801c4224024001c4a640c554084e1207071000c2d085c1a2000b24021801480840400100c1c4440b03113490b5580707000e0958188036031405419003c40995000e8215511214983d042c84000d02c841d500507965140307001601500308201c0403000907240001020b610541c1d000079400240440c03021060320021010342182c0c0100d40060f05a030f100c00c0f005407609403180c4180d1500d5481300012007149500c030300180c03000034420307143c1c80c02e10185580016440107150700400056440002030180c608070410240d504050182c440c0342c0035804c82407000b0345901130188018003d002e6101640e4800d841120300c181ca10400c1007003e841070450100041190003584074000005d03895001082941c5011301c1018100d9100078107161511a0011042c2c02030b00328511880190302601c5c50400160301da0092522541c5000d07550300d0355411080c941103001d0a809014a4210b5000f88014030044003c0407030864229046140000c08012910b04980601d422890003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 881218857 1250 881217607 881217611
    0xf0708062115010f060504050a18090c031101030609020313031107090f0510080102090a090b130e06180d02070620030a090501120c17131403030604140105030a020114040801 76
    0x402c54040541d48505950080c842c0c0b032a8a650b5450440300c038007890082035403143c00c0c200200040300c10742104030480344400b900880d0480440c2c8521044644542c8141d8200d1a012955202ca6905210310350242c89440c400718110b080550038084c820202030401011301a21818144007013004000e108000c0c00c0002c428001242540462800f0785820f40312108030014800c0f022a0205041c0203440e0701c01c4024003c1e803403e52070001c4803009800744404c125002038000003040302c8600b05009209410404100421040c1091700c02c800a0600341d943c0c0d046a600100311055942c1d1b408106d440440300d0a10781188201151011a03071902c542001c412920f02c40001e40a2800c0d82107241001211401d0303e0340401c050445480100b0740e059a181c24000500600c8000f44255610300c02c1900040b01c0001ca512103801c40e0b80707081c540c2c4010890031071075a2002c020400c01e03241a015400c02020700d13030700050085d450f00b1701003950340e405040000e041c805040403404408207102c0948005080200003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 881220107 1250 881218857 881218873
    0x41e05040507171b06211f0314060a150306110f0414010e010201020c1207050a02030d02030315060f030403030f09061104081b0a030201180e1503060f07080621 70
    0x501d42e50b44000712038989506004c01c840d18494034001c01940e001c0880750f0005034003d0134045032030a100000601d01021012092018041d2440b0700c0015030166101e84c002d02c0e501d0818594183c50b11034000e140640e01420452040304815411598108030380e0f21203c0032a00c0a400b41802d80f59001e19018201c080c4004200003030052120064002c66450070780301c031134581c04040f004900380e2290f4502011030f80c3c41880700001d80c024040c0180700c0c15008100b07442c0c010429500182c100b2005800c104016840481070090340300d000240b24038070301412a041c6240c10400081044240001000035003416610701d83c100e81002c0030380208000e0390b4050b0040220f40c4501d1010300c1300ba0001c1c02603822034420244515800b40700c0d4034419a00c480001e042044203842d5034011102d03c42490780224003201450300003d80c141e001c41280e8000c9a807001304c02c0c1c0c541480401c0c54a841c000501502c5005001402c0c0900705d50044105604490300382e03101400411a0280008412041c0074244414070880301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 881221357 1250 881220107 881220149
    0x12060203040605090c010801060f050408032d090f09041109042004050f0f040201021507020a0312140c21090105060906011e051305042306041e05040507 67
    0x100440c45240300b031404106036142c88040c03503600d66000d01450301190000006201007401007840c1080050390b85005403038291910301c0a810364000c1e50325904a900b0220280d020b00e403503008600d000d000e0410206003041c0e4454009442032500c2c4214078010744658001c60f051000700c401e01c5400035005450000103051500d0b00179007150000d100c540d040c50050030100e07110314281c002c0a0045079801481d074190303151510300034021440030700b08074103600c00d550038400c050101c920264450760182d006001250658200030380002d6060a0050101d4908044004a03484681c0020703041400c507000c05d50ad0b10720313210440004490103009450040040360401c4025041500030510854003545d2018994941100540c2c00d041c91441400020082480c050803052007440601151070b07840e14102e0800c3c0c1d8400124080703500940b258010500030014000340507101089590300800190703401c100d102c22007c450f64000f40d0742030f86c4500441c0c40700d0100c1e040c04000c02980e00501071040807802d02d101111 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 881222607 1250 881221357 881221361
    0x70602031009141014030a060b0d0506040b1006110d08060112020c0c130510060e19060c05061609030204020f040305120301090e070605030c0c0a0503030c04080717030901050f041206 80
    0x340c2d4928400600c0700c0c041400c0001900c0702181c808007400410151302c044c6d80b490f000d27200d40c410882e000a44040000b02141c0100700d000d018500400e10b036a20340c11300101030201204541c2050003072144000000448042c00690310959110500e40802070b43ca46074012a0400744240d5064040d5001161300c080c4444003003680c2d690385c041240d030413050041034100f01059480495190b40c9020710072404015441c0607100e4603080c00001007124081d28204000ca0300c0e0100242c0012000555100c094000c1101c100b11154000510291702e041800081e0001041d02c152804028003840d000b00300400070380d11030300c00e4030061584030040c0d035000c407240c40428003c0c0d0400d00c58000c2c0e02c0d0411520110b5580c0124282c41540d01d0340c0d070f1f0030f441c50f03a81d07400144607079122032103400d110312418245070045202840514051aa40d0340301594481c07414130061302c0c082143d0460600462401c240f105101c06c000202c030071400d0b003800d2440c0c45100703000701003219004a9008040800c014007404013080103c0e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 881223857 1250 881222607 881222611
    0x503060a0204140a060207031209080a030e09090c03060106050f1201090203100b04050a05040515041416021c08071b06090605070513030602160f0819110307060203100914 75
    0x40c0410b00360009184100011312100d8414880581c006103005d2010980100755208552080d0070110300c0c0c19a1101d88c5460200c001400b503000403000501900326182002020313410035a400e004207403038185c900001e40c55101c1031041da01800000903c100e1000654820340f04c60054906506d081980d40d40540b0002e5401111512a0720b0440407010818418a4040d981030f594054845035a00b03003040300784001050701604104041040c84202c4007150b4446c0100000b01038a88540c1400d41001082d6071201350b200303080c1000b550002c5a001800000c2c4e610640ca001c840c03860400103603212400c2c281c84545150300504120b948540d9071006000480d0400f07201d0a100394000c0020740d6403507004540c1402000d18052524138055030800100c4d9075a00941031103403014251411141c026a60301c20083c210520031500008040360300d10000044d00032001105500e41804103608040701c280980b688549440200781c258040301081034101e1615080000d413100180800441c021942d031180710801c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 881225107 1250 881223857 881223869
    0x20904110f01050f0d02130308130519030305160807020909150a02090f010c0804051e090a0b0d0305130f06020a060509070524360102030a05030f100503060a0204 71
    0x41180707030500551081c0201c030301c0e54103865082802e01c030301c18010f10041c2d40410b01c0c421902e0850340010000c070701914011306054a003980c01c24642840d0206010f1600382e4500c40400c2844140c0c020004a42c214040b5840301694148075506002d880c0b40030349280c0035104c4081d40003400751041090421002407a2500a050341c0b90040c5c0c65600e43c80d948007640300e99001650400100014490154003402002c01c1880c4604c0581e0309094503840882e810496a84624113030f0b00029000e1415400c000034003a400460342502481100100c0300403a0b42c8511102c00141040300024005424812210054020300a035104041026075956030087d41c800340d40784180d400d546400e001c038101c40c0001030900102d0348060311400c80c542c0740401c8500668919414070f072240d02d0030800c4210700568500030f0440c1d016100800c40d01c1106100310304501c1c285201313029040d98008c0211400032500700d41507a034401405c44000780035940d0f56014032a1840d040d8405501072041e2014421080f41c0741d0080c1c400d4901d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 881226357 1250 881225107 881225119
    0x412030f0204060f0e03070b180109090b0108010b0d0605040207060902040507080f011505040b030925030b15010320030601020c0d083a0c14031b0c010902090411 71
    0x80480c02100c00c9110354414000402c0d210f00b6030b18a10b0340112005110410020306a446040d540c24042250741c0c0722840c0341483c3c5401d81004c5101d0b68100354440b02901c1300090400c1084824000a4000b46060041c00481c103001b05001100301856001a0098140500159110300d014038041d800780c03040c1c5404038841ea051500141000d8428400070b4800e03041c41002d082c159182c200900340108200029034200803081002084018052005500901c0440010719011484100607548555100c02e03800f42682900c0003000442c40700410b458000c041284c40390007460380c000041c0c0040050307010000095000c18030ba0840c41220101035881010207030203a03522280c1440400c52100e402210090900310144010b140082d5044559400c801105050442d203070382d5030780c5802c02400005408800f1a446101151800b54003004880c1701c015540a01400c606024034405048542e08004028904000c01e1554000d0030035045501415009071140074542054208681918045500a0b0080e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 881227607 1250 881226357 881226371
    0x30c15180a050a210f081302150301240e040c030f0903110c030d020a080a0c140a060b04020304150c0210060f0305010507050c07090e070f06110c04061401080a060e041203 75
    0x13004112083e2044221940c4104e000308289000b0307551640c000d06000c1480308007000340001612041102e81c401200d45454949942c54503207406480c040954005000d028030448030008140c10500f0b15003066000c82e0041200e0040301c00072401031a070750000304210380c201540f00c42810780168058071400e112030261181d020b030340c505042da03603018240f514005a11121055002c5a04403000d05040e00c0c4500d010040203000d034480c0004040c3c280d204211540148004408010340c9100316841c5d0303141a10150700358905510f800042d01d03c5510f04051036501c40000c00760003842880070910820003404108050b0b610340d14441c0700c8190f030f030204844035840c18011413100b5004500783c45a006815006240311401c01c0241402b43c102c1d500d6080340c603c0f51000110300a450211510040c01d00365949030000324503001a585003c942c040d205008030b103815400e0044400401030400501028240b0009035140d44124a00034041c560152003003402c280c09020030003200942c014884c40459505024003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 881228857 1250 881227607 881227643
    0x18030106080106060207063f0629030405070b0d021201090204050d1b09050f0915310f03030209010207061416030c020a091d030c15180a050a 62
    0x2206a400303242c01507404031500300002ca00c5620723101d0060030f42604041d080d1004564202030b203039031801403403890121040590070447c400d00c1110020501c2441c2401e0b0703034842d030400880603901900100c099600010000f020711004004240041003041282a07407841c0300b04400d0700079085000408014900800001105595402958207882000b0700340782006080d5550f0a0101c0740c000e00c1d00100c02011170f80050072014a202c3c2c18854203205030300b000c8034030789001d6644c00c1c221402c00003a05001908280480c6501d880c1d410011800300c0340c4402d8003140c2c110720003040074821340d0700204100300c00e0080004241d8940c0203003080e44402e0b001c840041d505c1e1501034403070f43d00c42e4074100c84803101401b0010445011b84d6107080228024100160031140301d07000700f441c00c05581c004a05080c3c86040006141d0080c0c048020707610f1020020b18100070b05900602e80714518a04c00c21040d46c580d10101c0d0000341903928900040c8401011a46150998038003c0d46409061a05660b4400861000888 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 881230107 1250 881228857 881228861
    0x30b010c0b09030c0f0f061819030320072d0c1518061e09050d0605190b06120903040509040b090105070903080a120e010c030b1903020a0b091302180301060801 70
    0x38651b144018080550b60310170030092558444203828403074420740921411105402c400c3c07030300a500a0b540490005000740d021031182070a0301e00104510000c00c542d4021441b4000b0400e224092039850b11300102c3d942c0680c100301c015582014008050f2004005140034020180d0102400692070b0112342c40c05035100c10000a82c030740303c2d08002c51180760504190880030301c00040820960708104100c10f4845c0049144600c030701c0320469031155070700c0c20700040604050030803495000394a002c0c00030002e6400451010700421004543c0301f40c024011580c081c400380240c402905000d13211941d240f0740340c10498002201500c1c02e412075440c1001040070310741f04024020942c0c0d00150140d190080c3d000c02200e0042031152001a09907070b56000e000002800c1c0901e45c24165565008541d41d400c040411508128000c0074590042c0c021310100016161b4034900821141e403220701c2501c81e0000d1001c600d00d1001e0003115502148001036500815045000030b18800b20242c0082010f2078607295500c0c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 881231357 1250 881230107 881230123
    0x8030a030e0105070e1302030705040f08010b0f031b0d0203070306020a080708010506030402060a050c250303030b0d050703241b02060f0f130303060503070905011a031006030b010c0b09030c0f 84
    0x14104203200c11b4441c40d03241c203030001c1d6001021850070307a1906903190b00017502c84c080386c0c100034402d035180c54080b4424946031070780c04d05840048001e406d80f070315101d0b6407006401c041d0506500502c50040c210f810340d40e00340450801107800c42000d640c2c40f148403400500b0b1071401c41d0a2004182c00300f0004c0380a080802c00e8a10450b4050542d81c5450704000c800c0e034040e00302c89a1420a8420191000c10b0070701800c0850051402440c1040009c1e401c40c034014080d20b80c066090360265581c12004004580009120030031290480c00e68002c400c2000d03110340703a000c08040503206a80c1050100381d0300e8080c1d200c2c502d684018583c2660144e8a50310101c2448241c269040d4000c1c1c00843d02140c18030f1900d00c0100100c500c641400140c50340d881003c6030500d0455030203807a12940d40c1d8010051a036100b5032100340c146170714001c40c2c60351400180d41c00070303a112400b070380b1304041c4c1e111861407160740509090900c06410000e040c0592500300086070f503a44c000306442c00113000300c0911410401c5d000079000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 881232607 1250 881231357 881231359
    0xf040203030d020d0e070e0702012004121a0f0f0f0402090a050606040f0f0e090a08180103020f030f4f080a091d0606121008030a030e0105070e 63
    0x25180c601c0c2a02e654000e5000680b4283e8416645d820b00744010004004040003403681804003484c514261001a00310b69105c200700040328548900520b04c140c0c0c92044500780c2e601c0e03070070045000490342810b00e078100c100d030071802da184001c1c41400145486203000d00e1203801c05003600c0c000f580e0b80c030826121700401610000d400038054804110070300c0b401e41125500100161070142401d0b524074200c800030a150b4000e00e0010040c0a043c0300c42640380360342582c850700c0d0318020050002c1a5803064868030603003141004c564000c0001c46401ea01c640c040b0ba491b291311050b50368803410069980300c0028410303a520088110a40c05a060049400704459000b007a0020440e51110780c90464581410032466107159556034615004001481c400213050008444d548e01081e03d8208003000500c01020007204c0000d1240e941040090707560070b412034541c064404ea000b500d507241c40c0d40781c500c03c0d00c058100814a00000c117105950950582c04907102e02d1a103402401162034102055030140e4082c0c10711 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 881233857 1250 881232607 881232613
    0x6060e04240603273f03090b070503070504090f0b0402190f030e07090b030f070305060f10032a170a0b0f0610050711030a150e16060e041e140f040203 66
    0x40e450740705c0110100c410b900d52400c60f000e6440c4249007056070854501c000100f580c60850b40103101e2040074080d4001c00a00f805451801c3c102405071a0f8082c9110f025101c5450f900001107030038507a0040e01c203012010300159126511544e44c00d868201d9000c189000801c82d64814800b2480b03401200480400d26002d08082030a048010001d45103001480390944200c11700003100c7d55041108400071401200603208074200818213441d0440003810b03140024420003800c3c00810180040310015400d891076000c000202207235203207000c1c0a203134821489032964140c12100020040303a1000035030300c56181d49a091790341c03c02e488111242501c100e6000540720031a48661405030006100c00790040c3c0000c002c007162000001e140180980040b01d403444120420704006180d8010b0240c2420b660b000b901c10803420900300348a4402901c50b03203041007a04405903100340c45030783c00030881c0080f800000c600503840c4003034800034021400e0f10f00d0220a1032070010700e142d6100302d0b1590241da070060107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 881235107 1250 881233857 881233883
    0x2a0d020c100b060a111f090b010b0307050d0903020f0a120e03011104030b040f1b140616080906040810060617090a0605191a1306060e0424060327 64
    0x2180d0785c440300070920860317101c0c07802100c0c0c12407a1410b256140b0101c4080228103102c0916141c002040c040c0e02145520070180f040c40281e80d0428180d903041e40300c00c48002110940350400700d250203118a1101014000d0403040302c14000c0f00448c041e143c1c00e017502ca41c1c0214860301c0c14182203400452480c184040203002c1480001c201c0348026420074080c1c414260404925200c04121901403480c0401e20601d500f000c115001090581c0f411180b0204c44140c200302004000409060807010014454100040e0741100341e941c1d2010307034006d050380300110b50b8401500f20b41000100384d41d005030000f01c0d84c000b20401e4440898079285115003e09406825190036030341c0c0d4400038010181400c1c0381c0c3c2c0d900c0c008400300d41400e403064100803d02d9900004540d00388505201038410000c60307410059003019800d0100c241c0000c2c00b002900c030706a40c0007400c02040301c4140c2d000000806648148414a240019020b074560062840001007071a1040c1501c028031004040d0202c511008152601e031401c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 881236357 1250 881235107 881235127
    0x3050303162003031e0603030306150f130305120c070e07020114040308040c05030c01020a0308090106030c030506160201140705070507030b0a090b090f062a0d020c100b06 75
    0x580048510300c0c28a085a0400b8181c82035100e02c15001e5a0301c0c0b5440401084001d070b00c030551a8090310345940700ca91076401c040300465100c0c80000e10b414000c7d105001480207070030801d0115421030300e02007074494a614148a105440701c55600c016295807245d80209101d050b242412160b000150100610100e40340002511014100804103400d6540c1c90840368050300501a0042c8a680f0035038030782038207162a14058000c0003058009030702075808041c030780e14207076000120340b000d4035058200b102885d40c0c0c1c81c07019400762901d07810080241000d140d000042000005185024141c1c12462228034480007034200e0880380d64040c41000c101341a404200301d10701540041c85040e011384152007200b40c907a20f0b0b030396240205a030110304581e59544103105000d0030020396600b204e40720b0064140080c460301c910355a504042d1940b010b2002061010010748055001c6070307800c07103600e04801e4030340000c484c40000a4210102c01042405880386086901c0c810b0300c552080d085d0f00610041c00e040200d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 881237607 1250 881236357 881236381
    0x1813051608040f02040603110102011b02030406030216301d06071b0608060102100207050a0212030d06090b090708061305091e0304030215040e01030f08040512151003050303 76
    0x2810544500f1a10091071015890f28003410029502407056802107140640009007110413412030f0004100008a0b85d01d0982d60120444003107965914000d80c64100100b0549070402c9c018400403c114400c00e211070f0a4103c0c50a04202104a40d00b022032031000c0f410b0a481d131010882c02c114880e401510040c0e591700d058409440300344d01405000f480c040c490071104043c52920741140340403070b0317005040040d19a03040051214050031101e0550406103243d4569980b6001c44000070710501403e09403118082080050703400901c1c3d1018203018403641c4104040040140c03030383e0745005032501000540d1031400781c8650350180c44042e144108001d00d450300c0c1801031201a001c202103004203410000081c552144001755000c902000e1b50b0744914501c1000549190320903905081c41c0140300400400c401f200016044a4000203000d07004c86503440d100c95203101d15044285c2c04000c1e14401d20310040005429400d8140c0c99061a00c50780742e81c1040400a0000d10004004e540200001201d4080311 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 881238857 1250 881237607 881237611
    0x60c121b27030314070b0709030210050f09040c05070c060e0103060504140f070504230307081906021c140a05090708031804060b0a050a020601060810051c06021813051608 75
    0x130036050341c1014001e07a00e00844500503140c0e9000140b90090600a51518a071616140d42250a22034500400e01c1080740440c0504503072903100740e03607821254907903e00030000c039030510398030401111540e515604060046010000b07042c0c00280303004008030b1103040a108429101102042c46407040d03480c20503040c20309178020445401c01606210002d6820a480300340b08002c54400147c4402030040c07001c0c189050b100c0d910083c1140d011681c900104041000212013142d04070f60090b030350390301c1c00750f01001420000d1004a44c0300d207082004031b80e0b503425802d00c034091183c46c9800d201a4031a4030b41c80b40d48207070a004242035900104080c0151101010940342045805000480d4455a030007000035503812020211000c154009600503405505004c0c0c61302500c2d042c100b14105042080074103860041a008080c015009640b000540d81201c222003504103900500555a81e600b0965884018000e415454052411502482e0800c07125000c1c6034800e150b00394014241c448201c00880d044100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 881240107 1250 881238857 881238887
    0x11e1d04110409021302120906040b040b101a1c151e0504020c0607120507080c070809090c22030f4d0616060c121b270303 54
    0x10b10783c03c00740183c0702d5180d45142c0900000300162540401805c01400510090000386c10b50404410400021414005c0d290803d80185e044544c0d9654408104425810780e084a0b213041044d0b011a450310304180000c00c402495151a840032681b110710346002e4500e448801e06880941440078400740450792542c08114110101d82e05405554002141c1282e02224569610f50402c4042211380780d00140310501e0304000c01401c00c481d260041c001082928064240d00011000040349414400b011058a518040050140501e81440350361045a5401900d1241c81c540c11400107d60b5414104030303030750440750854914803243d10740c0d9031121268100007c178143c241e42080d40e112400c11401d84d851100c01d074034152440028010390414002c00030700c80740d41486200208903413080c030001f082c41d040f0003541c0b140d00418100c1a5038002e90300b251025200c1c444041c0791600710111407000103440d41c0ca440858460458079601d000c40200400103140000d4480020104100000b0340309506840c58401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 881241357 1250 881240107 881240111
    0x1300b01020a0c080303150a300210080601020f03040b07110604080703030c05150613200f120105040b21210c0f0c030d0e1503011e1d041104 62
    0x4040c2c1d103d803d40240c1d500a1000340c0d0020007003260b071040c0c180301c0390302c100c104a5400f071340680b0b0701c141454801c017054000c8141e40c0000c030081081400c11420032100b69030040021444ca4070004000b801050308588050040c4540100d01d007590701c020044500742e0300c0e0304c40c90b580b030102e8648542c0a01c02c00c03192016040b07802080002140c01050000002461003907a4080003564241482d03403400f809030820200105010043c00030f60b5450b8001d61101510f518004100080409041c6550034501a80b4002800300095107000d04414580108660714090032403000c0c9076240d0040c001280c1391100903e40040c407211360040e02081c200301c01003004030340004a80c13491303010441185003004404840d516004000c542000740f000140700341446c091003440184a011110000a681c074049800700e1020320441c0f008030141c5888207460340384009040304500e0390720750759081c0781d04081881a288015140c09240701050280f088100302c828514401036102480d1110b45500c00794208884400e07038803c0d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 881242607 1250 881241357 881241373
    0x20c120f04090c02030d0b0621060409060c0f030e0c0a0b0c03090409121719020702010512041a150904031b1b060201061707030609051005010e040201300b0102 70
    0x401c2c0d030300440c0501e80c62540a991a2124104a4030990304001c458620810b001c2c04034088040c0c1d12006006402e001706020002620b0318008240104104035002e085213050030403401c032442d0000480820152140da0400a2030941408140c039480c6000d51300e580180440c4041000880c80000b5110f40400e502c150780c0b03845101c000203011101d6851084880b903641d4003251140681005c1e64903074000c16101c440300c1915000e0351030b40017078079503000c0d0703e844035808103c0c14156481070042d2544403030303c040b00244908103810300034450800280009000b002140000d109490024041c01c8040c03030107842e4105c191610f60782907074600382d004642801207040c1d486c0c210210717440d0801a080c00401f41c0680307580500b071410007420354806401c05d00d580d42c400025003d65805c00a14030302201d40108002502d0151450030500702200380104404580c1800004101c410511030361501891003600c448100c040c403090403004050010042c40c0c1c4101c03103001e800711b92207410781005115600500c181c03403441c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 881243857 1250 881242607 881242619
    0x819020111012f16081c090606080d0903050d26040b10060203040b07061a060c030c10050702060f15040213090f0207020d0f0305070f080a080604020c120f04 69
    0x4034120401c41e520580f58510001001803400d00b941041e00011901c40d24100c09041000030003e8038600041101600040400000400c3e4022440c0c000200070280b000607a40d05200014203035030b0250042501480d00702c01c0c00c072805101c0d42c0b0200e0f54000060035000b54041429100380303210300485500c0320003131280a410b030100341d440131b803013280319002001036030912a001c07100d442030582000b029580f04001c00c2c0880c11304e88060b151001e91098003c1a01411000501a900c02024840c2d0b048600403c0d4401c07400310100241917948950812104c500500c2c07144981640c40603100e520250b0810008070b44c22030030329040194000324029080000112901c04102260700c04204010b0f1003900c11000d10940c1007900984510b0002e2410079414854241c0000b11a08452a0000c00a00b2421340c40c008140c0208141d9011981000c8441c180a01c58100401396034000d80030000040c01c68000504903180c2032003503c0e03018810307600402075181c0a040f028400e51082e074040d480420203200010350303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 881245107 1250 881243857 881243861
    0x170d05010806071e0903150b2110050c070605090a150603061d070e091f02071505040b0613110309010606180608280504051605040501081902011101 65
    0x20070201004010a00e06038000910340b0070308400ea03c480c4007100c0d4180c90856440403000c402e0303035000440714400b0880e803011100140400540d0b1600400d505a10540b0b4071403400d01c00003e50b50000035542c540d494200c20804071501290f03506000c40042c4a0400440c01c964002d5a0250200c4102c4809e020a5100c056090b20421020080140c81c0d202c14401c20013103008404107400c040040105403040c021000341c0b11801406546042200200000d591031420810070041900c07500d0483c0d200b2146c1640200a03501c029800d495110320081d00b4115402c592248603c81c3d500040f031307884d56450344010428203100b0310300c00001131500d6030380ca20421003900c3d0045005e40e02a1000242461400c0d8000c0c20b0800038220401d85900c08407410042550484895940100880c8101d4000c60900c7c82d04041d1002201100444034608004c12013007110000f8601c0d4030700c2c011049050003554440800080c1c40003406050340c5c64211401c0c28101c541002145502d080c41418824017064040b045c00d07007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 881246357 1250 881245107 881245109
    0x20102091801360e07031704031a04230705120f0c0114030a15030807030306090e12040902070204021c06061b1a1819050c01030c0c170d0501 62
    0x486036554010441400c80302030700303402c90a82c450a40d90410340c000680b0b56101c60b586a4108080e280c00c80c240c84c8080500001c400341d540030b1820b41e1503160300041c04a854005000441f19408100405d44010010302d174100e206a901c00d0741c0c040d417105050982c4800c078004441e81200c0344200c202c00300c1e40f40d40d580701e122000380d00c4100074103010049040451800031a501802c0c140000340300464400015002207a6003d00400740100f0190a8440fa0b0034880d240c0d45c5c4042c0032100c011411004065141d0081b00485507a44020b0240d80f182242c00340e01c0d50900ca000294055042001708140e11851f0054030096000a00c0181004103040c0c000d07803000c8580b02c2048805603941010b001158100e9010b10281d040007200c4544641103950f40140c841032001d406c1c00312082140050351008018800742200c1c488107044d2440562140080b000b181c01089044400b030240b40706405155102c0d100d021042506c940c0da40e0004003103512098451105108000c02c580c40411080e546030905004142c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 881247607 1250 881246357 881246389
    0x60302030a15180f1e0206030c09010e06070501050a061406040311060d02040f0f090216020111120d1e110306060d090b0c0a0e030105010503060c0d02090409120f02191202010209 78
    0x49222285040c603000e0780480d100d605901c207a51001790258881c41c0550740c2c00600191801d503034003c203c1c0142d070101d041a00240e030150000078424200201908140e004540d81e9074144a2141c90303025541440c043c10540a400c11400c0c4030403c045088003207008039840019064901e86048403a0715000c1c1d80c03242e0060021242041010004450708168010003011281001c604080c0307460022030802e207031020042d040007502400720329070b01001d110080d150b441001203a566038001401250207424040c02444c0500c525407240020540d80380a00050079001c10a02407031650f40c00c0400040340c01c0607941810490b901c0001100003004a2009030280008608180d160816990002c3c0424a003054180c00390341844010042c0780c40c0026015006081151015140c0d050001114020300400725500e500c02c0c201000c1c40305126580c10020107940f05962249100c20b400342c4241e81d540d105004851a41003401d0381e1030701141510384030840071041032001601e00701c00f24001a042c003132240490 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 881248857 1250 881247607 881247623
    0xc2c061e03120a091505070f080d0906150e100e0903190302120a1802100c1e0614070206070e1f03050901150b031503030405090a02091003060302030a1518 68
    0xf032010700b9041910b440c02400d80b180140601c4d013036040000d00740c0c011011b0082030155080300103820020014140c0d154207174580b40410008016041c104040c10744121100700350041e0020100f107500c00c2c2041944180b00c98000d2100b01031400705402d0b41150001d090202c02d0006120720502c1e4480b0b201d042d0210051950701603124841c0d4428211a54400307000b55243c94500004680c00e110f8400790f110310300d60100e443c161810300c200307401d0300c004c0158240248044c1c02200398000c50004510041d02d0b0324060841040042c1e0000c0c10009441d10595668016a110380c4c0080e80b083d1145003010211315004e07050500007403210b080c0ca00c5400416030341c038002c6601c41040213080d0409202d0046001c8580e2002c030f0690b46005a4880700303100103000314100c046541c07001d14090b1404c104640c0240f101600b2441c9614007610500001d40000c3c0c0314a00c1002c8200120701d03031600c17a010b00c4003540d8009000d06103800407a540e15150380030701140000d450340c0314000c807100041c141110f00c131264052a09 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 881250107 1250 881248857 881248867
    0x90803130905010f15031a0a0f030c0b030405060420090f04140d1704020a1e18110d150512030909090303010605040b07050a0506040c2c061e0312 64
    0x40d40042d520140c100030401c110620082041070070380300811016006034140040c1c1141c08034215910307031521024464208016400000d40704142001090849020320361b2540c030191107221030030061005440103001680142c021401040c107141580e0341c0340d1411345248012540e801c1c08030381548021101200c0002201d000c020070b211124a01c05103040d03100d406068110f0f440c4c140035107244c00c4120010454032040c800100ac6454501c0024080c0c0603410401000d039107a580f400030180c0c140d0180c0201c2e1100905903241d000400d01543c01101c0c1c40340c0c00035041c50030303044280d00140b030b034401209000159a5000103485d1244000780c0c0b950380802d009180d4a405480c148080910094601c105035402003004125a50b805000c2c0d4040e02d065501c0241d45424a0425910b024180040940140507010a00c8104045602c20f03070225552490800c0249202c6041020702e032881e00aa00403860800001624030b1911040400401c8840724204055611402c0401e2400039002501d55000c0c0c80022 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 881251357 1250 881250107 881250119
    0x809010b180103031b05031927080d0e130b04090b0405010e1e0604020f2716020a050606221b02160f090207152d020f120709080313 58
    0x10100d03405d002c00303054140301d55515940c0d05e42d41e11030458060301010b820307400905090720522202040c041030291130120600704100c10113404c21144501d0a05108660491560501541c4480b01c0c3c002c0c020200001512906030003800b520307803859219401655078003881c0000b040800260300541c064000050300c2c50741d500d0150301d002924036155907004a00000c0e40d901d240000f42850384258180c691801160b074100105501d04400890585490321440340e0b00800f034000c00d15a840340110580c100c08443d08140c00343e880d440340410107005a041800000d540e8280b48007410f90400c00010440c6110503d2009441100c2e40c040301b0707501480c452003110140380c0c0d040005102d00300b000d804a40d041864484101d4642d20b0520a07410f40a40103c7c1c4103080c0715410b0000260040039880c10700000d6001800000d022004540d041d02c3ca0482e0803100c0ca061001e4030a40b10f1801021000c0c500d011089528015020310091503e400c100c00c5850111b41c11b40e060000c0c142c15502c2ca40411286410f0036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 881252607 1250 881251357 881251367
    0x181805251e030e03090d0302010e0307060b030c01030e0c1002030913061d061c1118040203060f011a0f0403060c0512060904080d0b0a03020307230913030809010b18010303 75
    0x502040101410028404100c0c00f02201301d4524000c11500030b004205245070983c0900000d25034540103010100340d05090110075003002a80010440517504840701d50f1005400701c07400c003105841c81d94448080700240f4204814050703554002c0b80112800d0141c41d40000324410f0f10040c00c1030403251a0282004064007a0411429001d03080d000c060081c40d2000100d104502c880c6480141e28480a400784103104a80743c244056842c050440c4003800000c101900b00004d082c0e038124000e10130700000a034000220030381da5041e81c800030141e403140000d015070310f01c0030b4001c001c0707030030b030030441004000001249885400000034141d1103d50300c81d82074000403003854400404142c01110403508010000f02d00f00122410b42204e204005100b44081000c10481d0900381c000035058480c841c0049552401c0660503200c807400266015000051002400703900d440a40d04002480800c0000500007030040c442c85611614010000602c03030030f00c9001402c0750b002c04400445140b0394400600925503c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 881253857 1250 881252607 881252657
    0x807022701230f15030709030c06171003111201020f0c16080c0a050402071104050703020c010b150703110f100207110405150603060414090d18180525 66
    0x445001d11102c03c000003007141041450038141003d20008009564140120750880245030000c0c0d02c50f005e00d490341c1003e05060494100c0400040fa10400609403071060000c0302c0640f54400314003255000f00509110141010b40148003d95400340f00601203942401c02426101c0e03a601c000344104030a00a59200204058000c240b45400402010034951501e518000486400b0b840050b80c1c3c403418182541210151100594818248400e00c00f5040e81034001d818400340000080101e40b0300c40d4100a04969003d681301d01e803a60034400d00d00440d001e161140b1001c9149400d0392400400e801d0517038108041d040b0320b600700f143d011408a050191b60700b9007010401e01590200302a042c400e0302c900b02002081480380c1308540001c0040d4440d11141c0100c401014400c4a040e182d0521103092507d07107400600c40d2001030044445909140820049082250028030803410110f4003075180c0d0000c0e00c0020049102240c0b443c5043c1411400d02c08403030002022980c07020340c02075144401107200f1140b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 881255107 1250 881253857 881253859
    0xc0c050a051c0809070b210a14060d0f0206030a1b020f15010b0706110412030302030105040c080103030c0f020a260f0c0a0b1606061215020304080702270123 69
    0xc030b2030400880404c0028a42c056600340104140c8440c4031000b44d0101c00b83c0302613400040d180c0d030800e000c4100400c0d0012000d0030308088030b081880e070f0303980c0911059044100020f0f003104841038105025007080c0d402075420048a441c00320f07180201d8181104600c801e0310320880180d000701c3c049103000409110180c001c0c004030a071442654945030070403800d8015000c0c00350601c3e68071404402005460004c8400501d00b1305401001c8a400e4140600250801d202e4280514181024400329512400b641c5050702c3c0d00d6258586440e299460703030700b0a841d05c01400c0ba0454015100400c1c02520040c0d005080c80c80d0319040b160f106109a40c050030480c2013500484140e00c040d29041301a91006003072000e5560790b480050711440c1c0641403000c0ca045501e4082e044903d458000300d8410400d02100c10607501401c0341e40349214040c0425422480201e801170300c10401405001c0042c94030000f904021442e4408144405120101c600210300082e8801c04031006100040200383d85040b449c40c140c220 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 881256357 1250 881255107 881255117
    0x110c03070521162306070f031d0d050d02070c12020319080a0c030201060e040c08060f060f100c150501090e0307120503060a09020a0f03050121060c0c050a051c 70
    0x18400100581d40c0d503e03024018582e03000b115150304119010446501c049818000712007003400c00c220054140c000402001e8002400c010200b056a1b9000030b402400c20a00740081030785050004045441c1d410803012049055002c2240c0c0000c111841202e101900c0c05400c2100c0c281040e1041624108041c02d415101c4804aa880408500ca0000782c40070f1080504081000622914007240104025000341e24044045800d2005001d5203c0208054821030411105962100394a12071038100840d01c1d00d500a590520005d41402d00c800c10501c0703840207003030100e820300b2182e5401e00320f0303103c20b680407140655a00041201b004203009540300a0100400746103024100d45558001c41000c04002050150000c0440d01d0703074494004140c001d041c0b901c07046413102903176030000701080300a00c10400000d04041c000300d50700410521039404011600314620051005585100280040c031303c40754140095810b0704008210b05204100ea850300c17803005002d5116100c03c48054000d600f45401c82040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 881257607 1250 881256357 881256367
    0x1e04300b1603020915040302040c050408100c0e030a030c15090305091207030c08010606090b0f0a0e0f040e070305100c020a140c040212072709110c03070521 69
    0x5000000c03140e4202880d03451480ea14840d000c0141e02034807a540c0115002036076140b040c0c800f010420040c00c140d920889042c0100925010210381310b000d02d008000403604581c40c0c84a4000181e880420708103881d003440140f901002d000281403864490b01038020034030340c0754003404202c0407905004d0340e8010f2000070040070311181c50060450044004060180c00c9200d0803404c80e42040000f80d00540d03201030081c608503191203509020707085510954011a82c4030402055800019050360342080ac170111950400594200450300c41000b4040780b6001300c1403805d407084070f4460703000d0140090208001400d08031b1951400619290705484c0103801a4174069134021f505034041490740c070351504004100d9503050740d00d50036801c1414003010340340c1c0584002184070140d04c0340e6100e103200b51080e495010044800d80c010b108510b00c40f0061003c0810112010f100c80e0400e0341c0000610700040041a0400588291180c035541c4220f000b03540c80d85c0202a01c0304200a403007070741d840b4106000c2c4894202 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 881258857 1250 881257607 881257613
    0x702070e07050a0503060d0f030c110f1305100902040f080c0a0f0513020415090e060d03080a1a0a1409010b0906180f0306010f08121e1e0430 62
    0xc1d0203a00f81c05400c1103000004520b45903120311010007090b401820000b01c88407946006001a150b55808039582c020300c2602c070205203840d98544c200c1c10f0380602400d01030112241103000515004090f42c0410740105800300b40e040b510310282003e040782c60144850103041070042450106081d02e014810303180908203202e50b0500821080413a50142d88107403034001c050b0318080c0039001340d0700000b0140e00251404051103a005c16070000321100c68064140a0b01c1d01e2081c00140000060050b0110b0900d101040c036503241640400302e40c0381e608211203c0f118808002031100e021aa020f1500351100440603500740c50701074601c0740180b6110301003e01c0c003034442012810a0141c4c140301032039502510b8001040340c94004090ba4100c0c001020780300190b868084903d1150441e0003100d04512070030801c0d68244210f80d040351002e40c4a2802c3c130042c922510752062069205c1c104258404502135015502081f504000c0c0c0064100000003d984078801c102c040002c184004041ca074000200200c1004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 881260107 1250 881258857 881258867
    0x11418011a0607150507030b10030e06041b03080c0f0f0307050706050904090f060903020c030c031905070b030c0c0c01050a080403030914030d0e0c040507080f190c0302030702070e07 80
    0x381c10255041c50701c0c0d42c0caa040c50003044807604d000760240ea05107020030007055455406030070000d00c1220f00640a1041d00000c404882c1c1160759890164409030110300440c03d004064840200f40e0300c080d000300c40e21307a601c010068002c03480e40c480c0c0343d0000307803c1200d03407100340241c060b0b040c041e40040d030600382e00b500c613540d843ca80c42c0b1401041c80700c006460565900c0b82c0d0800802076801181802d1035500d40e1919000411400b00158018014007510b58041c0c98007080403850204028014482d0002ca410410010003512000302c4892091050000d11030400101a5200701410b03074a058135001d50303401c0c050812404001403410441d04101035001b103030b04400459009a0107140000301e416140c40d1901d466a051222aa0036120101c0e8440c082d4003560442030301400314009035141d9a0040080c8800c0d40c406503101000320711081c002940302e100c08035951b40e01030b4004411010300204114510100c450342c400220000390000f0410603a1901007120000400791050f40501c18a00498000c01c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 881261357 1250 881260107 881260151
    0x50108010b09131109070c020f01030507050f090f12030a02070b03101e08010204080d1205012103020109080304231c030213031a1f0807090903050c01141801 69
    0x10540d4000350500501140b0b00b1460442d0130060f000c2c0c40141005000508011802c81e012407048000d042081103551207401076034020002901d503d0700b01503280d08800500d8000d801e00540024161040040f80d0b81e488201e40d10035681c4401440e81d407050110000c1c00c1200940103441c600038100f013804084400514a00100e40d82c202d000c0c154000c2c0003603141d000d140207030302030280340d070020038040341c2b0000120703504562110750b4548030390468040d035401e0180c51007403144d41c54420f845190300081981041012005c20322038400000c407520640d48802198000340c5041d101c50a10410a000303602d0b8032004068251031040003010020001d40300040307540c8542d0040c0040517000f01d401040d030094601000059070380454852110701d07103c81e40d05070704d080454260303400d5030814000d15499101295100150748000002c0c00500d41801c05400203000425401c40400c1000c0000c2d0441030401c9c0b044900190f01a81008146d00701f1a2248a221300e00380c007565010703454455050300e03d50701003030288 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 881262607 1250 881261357 881261371
    0x2130b0102011806021b0f070303050304050709050a0902040b010e030d030e070b0408030c21030601030c090e040f030206090c0f0913150209100c15051f0801020d050108010b09 77
    0x12424214200040380500440f48410441c400841da0308410403020340c000e0000c0482c280305e040802c0340003185c0590f0f52020003443c17040c2504061001d1010034421001160300c24090412100015501c1038002e040b80c1c3e0464111118070381c0c5114000442c42e00707015504a0040c2468455105070940b00020b071103c101c40020000d040e92044210001c000034403601c80100095a080d40d19180d6403d2059102d0740440c058440d54002e4810000348008000702c0d00600140c00c0300340c241560b80342d400650080029081010520040d088005100880d90a0b00e40c4280e115484060305002c0d10316020b8580325015003403094a0300000c04001c1241c0301c2506011000c07500322603101c1a0380714150b0701d05c0380151800010b08484401c07440340c410306907950000c00c14294242d90702c0d44c00380c1c5230500459980c102040000c00a00124049641042d404d410480d00000c0c10f540f041401c60705001080300c1580f0340d500240b801d9401003100c6440c62803600c41c0da4010500d14000f0f01052840400003034074284024808 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 881263857 1250 881262607 881262611
    0xf070509101b0302070905070903050a0303050a1b0f0810081f09050f06010e09060c0d02031801061e0f060c031809050c0d2901030b1c0c0f0b03040213 66
    0x400c18284030b051995a0b00d004050095640003450400a4858105000b80e400e83c0b4103200200e40c040384907031f2060341129004806400512100c0d41c0031000b404028088214040e203649903401c2103c0d000b008800c900d403140e00e9034007043e16904405010b80c08018240102086415010081c0d5640426402e030042c0c400520107400417048007181c0010080f2a00c040c101d8800d04440112030080050136505a600da40008252030381c1d98002d03182d0701c0c0c1c0d0407103400c2c00484081c08600509000390300030310f40215401c0f4030030901080c800103007401c4a900340d0007078100c8005420140054460307030384004040c0c20010041c0c0c4680b41400300180c003201060300018100052803907906081d0070500b848070060303c1c0b04c1106005604003840a1303101c0e42c000e025a11602c03480d208207403803840b8a00c0d503140c500c80396008001d0030300f03a01400150028826001510380020403010a030b1044503900f20740c0b403015031180710300e84204c6080c8914951300102980041e0b0411208205001c050703075411213141c007246450800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 881265107 1250 881263857 881263879
    0x19060c140d020c07090203040501020306120303070215090a050d120f02180f0607080a0207050f030a110112230106031401080c0d020609090a0504060b0a050f041a0a0602010c080f070509 81
    0x180f9150901c1a403001080600c0881071108111041d0000d5004400445c0c001c44041d501c802003a881344015200f100140c2d104488904c0c2187c00c110b24130741e1200c141340581c0d01c84510f6846090a010a2000c0700001550322801940e00c45198860400115200348046061495101819040c0c510009038907100f00060b001d646800e9075440e04030342c0506d9202062030f0301d4070b803000c03406562907966000b2240310313001c0d541c0202e00c9400c002600020340d540085d01c160111306100300540d401051041c0e58004070340c80d2008103041003480d01d594020030300717084240449503261510003022540e940114502800c02580100b29510002840e110341c4001220000d0082d00684001080c601c5003440c09070b08800040200140391010742c0c030452249019000c2480903813900d10400400748890702407640d2018141c034110ba121301b480d0f80403103118481c10f0303003c241240304000011031000f060360111700183c1d15039032204030555028400720740103040340400d40c0c114280410060200d004801c1807a00410030159 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 881266357 1250 881265107 881265127
    0x1080a0b03160e0402270414120711090604060b0301090e03040f06021b0303160b31060c0311041502100203010b070519020102030f0a020f19060c140d02 67
    0x540402d11014200700068603685221400001c0c0003218268461040c104003151034070460711444074900021589000f040e40d641e910842d030380184402c02e012a00c5244601b10700c1d00d68440007000c040740a00d852048100c81c031420055281c1005203054011810608108004c085000a69056440c1548c0c0030600e0a480e905581c030390f02590380846202c60741c0000000f801c907000b15512078129a024500c030314202e070001c24146ea9202e5060000c24014803500300710041000840501d41043c00e00454202c00100e01c400d411843d41d106d080b400415402d5000c0d1002c0240601ca8202d8070703d103038202070000c0c6003803042000c254003551150790600c4000d2030750080188d01c2400824001c141c424800c40d1207507120044182c1c66041f486044606105004101b0f9502e206d08600e014a182e059008600e07121f2088044605604020212000c0d440380307500c801c41d5440305000402c4000898940d001e0456810300f070001c1600c0c1019419028014190500d40c6018603200c100c45030304034201405a03a91450304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 881267607 1250 881266357 881266363
    0xa09062423070506160e19060f0c140312090a02030d050a11010f0b03101e090c080303150a090c0804080c0708061f0e070504090f0f09050c03120901080a0b03 69
    0x198010928010b00c02000b09908284528a110f00000c2d1740c6c0500c11900442030040304410114101000020310b00b042002c540720b6403a40c0f025844510741aa0408810350344c2044040b03042c180717540641c1010a11001c1055904d600706d9005450340000e21a42c116900440c0c0c49005c924400d40030088002001007030355002e001d14034182040032008001c5050340c2c801042c020514030000c42d100303000751032a49012003400c0c001c10254a94084440c06e60a900d807000f00002e2843d98011201d5440c40240001c3c090700c1407000e0b5100b010300c091105d038000444810800207040c141c00c031400760b610300243c0c0c44031183c2c00f1040c140d0156110102c650b8840340002002e1824185500611061081c54104200b0340c0701c40800c00c06045049268050103601e030440304420203800c07503040000543c240010445a000d80d0080780c210070760342000240701d140d42c00341e24041c0da450010586a0340d2003082a00c000d402c1c10410020341c00c3c0100c2003207040c90b5600000034119600509610000d60300e401a40035907a4040c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 881268857 1250 881267607 881267617
    0x601180603091119081009030e090a091713090501080a020922031709120f0706020706240906061205040c0b070f031404140118050a09062423 62
    0x2090301c00c400701c050128051190085c002c0030214052a031000700d000d03000d802a15609035050300d0343c0a501c0303c0c00003401103c903c0104403604194868001c40007103281542596040c40d2089542659000810180c1c40f140c00703d035000050082c5044d004000056002ca111a0358603411a004035950b2100c10300c030055250b9050031003807500115902c000416070008903034440e11000e5410881c0e1036440a84140e00c90503000b6490751081010003d40d100d420b901001414400c2c45484c00606082c07094660340111840554507090b1425a4403c22103030b09c6403900150024001b821040c4040b6081a0005255075100c0881e800d02c00e40f0740c40440e00f04003d511001c80507009880d10b1903124000d50501e8083c4045030f420a90216500b203540c10a06609082181c007524804007100510500d0b031001120300f01e0441d1010740303101c0940a07012405135030322802e5800510340408081007050810004448501c028a09001e4915003c1d001c40c0d8200d800081303800404007082490517a0503400c000c035024500c61 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 881270107 1250 881268857 881268859
    0x504021801060f0806030303040b011701020c070f0311030a0210050702044a030a0c03170a0e010b010c021503090312090607090b072001031811010806011806030911 72
    0x40400420030343c1d807014203088001e01c0e6540c2c1080540301c0305c0034140c0340d100c10340300030b071546001a0061000c655200614008000448001440c0001c0d80310440e041500d140c102503c034804942c0200240003050fa002d82940c0307411000360451801d198005490403c580300c2038010b204000c60103005558460348a0079481214003000301c1d2235940030442001c81302c80241c0641c02c0e000901e0801c903c1c18807001184191b8001c0000031440c10841e500c1c01e80b0709945e064012000c00c29499801c0b5240e00d184060b40b402045410170104901400e031000b24251f4500c15462810080b9a2849601580da032030607a400d8500c4201e95156a9100e80d250795082d80318207075003403d07280b40010030b02115003c00076045100e4180f540ea00c4410903282e510043c2540708511003d03104258030500040401141d841d850010001410005103050015a41017466003207220180c2c1c486071003c201d5541d40d42c104412940c031020918011500c00ca01c01f031994001e0400340154030425a94800003010464514441446124 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 881271357 1250 881270107 881270149
    0x1050c01090c0306060b0c0a0f0f120c150c1b1412030a27020f120717100507020a0b0703090c0305060a0e0c031e070306060f0f050d15050402 62
    0x105608203051028400c3c80102ca44a00d4074900050140c10389040d01c05028450000d8010041130703898100a04601103000e90303642032104004d400060406000089191031522503010003011801c01000c40f19810005842007803d101d0404400c0d81e01000070038404a40c409403600c24440350522481e400814007500c0200d1054502c2e10990381081c0b400f840c420440300405028454078100250a0007032103440122302c1c103c4004005005207452290500d0100700640002140712810a55a18040441d0f12501080d60382c11340701d0410b29014007021012401c0604240141d0600c008029696540d0707071800380016203c0b0020030080f51003074004450494020401c541050b489003000d80d198a025124864010314100301914112070201c0d20704032050b0010041e1980c64035030b65440369544403000e00c40002e401a8000407002526510860b0301030712515003441c04080c1854a809800c084a0300304c148145268030141c40019042e11f0783c051801c11300b0b80041102c1e266480410850702c03184400300c07540d80c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 881272607 1250 881271357 881271371
    0x2210c010203090303040c09091106073909090803010b030a141005030105070c02060919090516081b1c090f1103101b032013060e060a081501050c01 65
    0xc6000001c5c5010320301480c1c9520303c00d039599030a4811203204000c020120000d602009070145028070281055501803040858501b5031821260174040c4038012149000700b003c0e90010307030105c1207585032001d400300800403c4880800d486500316400140f04545201c000000003890021080e0442c07440002c5145600840781070a02c00c009912000d8001c2d42d01a61a000018072498490b4241c415080c0d0050002d6203000d10b0407051000d181c2c5254108031310701010500025845100d441201e206102c020115042952004001030880c50f0190108842050741c5503002e5509184900f22140044642003c0c003100c00c1d4040098050034080c0c0c0040c0004040c0034418061100c0c446503820303001c1e1b0890503920309802071650001114500030a180351111001d84c0c84810310b000364031030741c110890680b0501130102d0f8044908140d6211401000952070012020816150001e482c0c0000f150221003032402c2c2505075800402c881801810311400600d516040a601e0b401101140e0011000b000240140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 881273857 1250 881272607 881272621
    0xd06030305040509280b0a0e010b090a0b070308060103051503030c0106030501050a02040f0b160f050a0606050d08030402041e0e012406080c07020f220e010c02210c010203 75
    0x20b90081c0c0304080c0035405920001d0340120b000782034920b100c640c3e11140f4401d400002d150310010200d82d0f40c0b294008541c5803003c14207442c4410b100d0b00828800100075501c500034420b2000902182c4d000203007030b4505101200003c3d410140b411381c0303e0b50170300e00040c0ca507852641c400440b41113521a55051f000010391082c6420041d04000c0c1942e010304020b0080381c44901d10902240b18900c1142a0b5401d00d039804d01405900170000c04e451901c455000024524a446640001e0f190080031220355020040c514204001805504000c00080301c50103000c1c64543c440000521004000034451a550a4101c030070000385088000810b01001041007440701c4405418000d0100f805428141c85000c483c080a02541445401c00e0303968958544604d516000701c2d01846400c4140126070081da5008841c0341512615052840703107094000e1500d4110000201208462a01c058031401c0c0c0d04082d030519031150005400340d41283c101c00c1160040c0345283d10081d40e0f0154050004165000000780410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 881275107 1250 881273857 881273867
    0x20417060403031a060d15082b0801050d0f050a060509030d0e0d1718011e0b090417070302030c01020a030c080a15170c130f0b09060a05040c050d060303 67
    0x4200d100b52000c100e0b0024140801c0284c5803240d81103035000700c04018000d4401080d42020040d01c4020480c1e8443d50340f904003580c00c1000200c20a59200501c2c10030003040000c036141c01901c00301030b0034155419414000440c0070004042409408a50a4084041048010482d48806603000841004107040c8440c1d413940329840401d0180e28903080042a10781c047c404102089003d500303031203002880d0610241058082c00c010284aa4090600d50407260040300b80540103000b0104405a01d5000d40c01c40041e044400c03010403075000304060020800000c00c0030041c0322036011954040d80e11000d103460100e14520030304614280744c0d40040750039689640c040e041010310b02c5868540601e01e40d15000c0e848111400744030032600701202d100702003000c0003001042c120410b4040080d102080c808101083c190110940d9000b801c6681e02540c1440c40c1451092660f900703000c9908610500380200007a1024601d400b90034481e50f40c2e0a190243c0314026000c0b201d45c9c207502c0e402030103015030f41c1c180030384 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 881276357 1250 881275107 881275111
    0x614010c0807020a0f1401140316020a0b07020601060909091203180f06020310150905100c1a06090a150506091f02010e0d050702241e04080d0203040803030c070602041706 75
    0x58110041030f035445181d801207000703409a423032501c078503400e5170386441c010141c1c915a00225000d42c001c0b29140c0c804180303000b202510680064004140340d501d060802400c003421640502010362601d141400051040c0c545104405001c2c600400c10040410008c07100c1000d90800800d070481107501e4804014154002d94132440341d000c20820b00c40d0f0f40c1d800e043c19170a400281c880008112450502103032411151108025003107107442103119031247c0e0307582441c1031111400300c00c0401c0e40013080a40d290549095034480e1070641c06201900d07084108054011580c05590300c50133000c503180ca025281d2001028844c1c61074400076900c80d002d120f010b4024080707038003a40d9540c040c0e200d140c180c86002c1c03012944c00640c0078041c4003144000a014000690589120301c40c0d914040004034258400c583c030b2482800c4400304800d0b0740c0c520b03000501e890111291302e00703002d64100348020013050001000ba60b90010100d0021507031040740e480c05200910883e0800c0140d1986105100c107160f50019102d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 881277607 1250 881276357 881276369
    0x9030e0a080f19030c060c050d02070b271e2e11090d140c0603090d020613080405060c01020c030a050706051003110411090a03030807120614010c0807020a0f 69
    0x4000c241d444910003c1908542d0002d00440c1c100b6102c03000241d05035011111207951440d0140c01d2044100910081e68840b11003a6406c800d030b0000c0c00b09822210400741180854492000203100000007055140d22880c200c0040383e0700c201040420760081800b08058018041d50407003491032154880301494655240c805407820300e85001700e4041c0e81c0600440700c4034440102a0390100d000d55540300e0700c41c4120540c3c000e03680159104100503440d03030b401071801501020081c0264100700200203141c9080180318002c0341c030582c94101d02103050442243c0035204207450f1a1740c0c1d00340c0080020302900c0755000315000d0780f02c001890254198840e001c0d00f00944a070009200d161074038101104e1601d2035001c064207034401a551710340d0602d40f0790f002c084409005040310f81840340080c0096400714041c0e0040d004200c1c07038020001c00650043d440e04031201215030400c006e506048512500da20703196004d505008035100b1903014025900103440c049540144030f80c41240d01c5110340d204483c07551140c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 881278857 1250 881277607 881277613
    0x50912060601080a2307030618050408120c270f010503041e1b0306050609090c09010b0d0b06042301020f0601060818030318010b0d08030615130306141602030a0309030e0a080f 77
    0xc039003c0712a01030a0700540d00208090300740700703371141808500c281c041d0800720013400c00c21000900b4600241c0d20007942c50002820320040d81c42109004428510140f02030420004000b0032002916504400f031188180c2c498104543c2c680e850048030886240d0305404c0c26a0700040c001041081d680c11043c8035290540e16400c068455140d441d41e01e00c08803c0d0703258801058401842400141b101604808085030004200b4810b54030103d03240d0b600c65080300300882d10441000140c802a48501083d04000f8070051072620300c2d0005058481406000e1201000380c0c480c00325101d041c000c1c01254410b440c0a00740c03a5681850720f9007001c02c40b8080180340b000c0d400c05d00000702d0351900c503241000c165000f1403a285141e45110801859a00030201c01141c0701d02807284070092001d01c480040a0752013500c00080000108a40380401e082c010b0079095010102032900c45440d5000c810754210004074200030980c1c5c4084e107425906c0f0048000207130380113000c0c0e5500007808000003030381c00c48060012003a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 881280107 1250 881278857 881278889
    0x60c04081603030203030f100902070305220803040b090d0c090b0909061b0f0f0307022a130914010c050d141b07060603080307050912060601080a23070306 68
    0xc403a240c8110b8031024025030800d0001400303100040030302c10380c003011800380e400c41140c4494040041381c2010f8800d0703001407004600121142c0d2588840340d071040d0140e1844000902d4900399982d80d104e28042c00d002200b0101390400c0d9511071500b00003100d54822408940540c4039034a00700203010b60280300d0b109110480104a4003503022440340d008943c103003041c18080009003505036065103d02d0320104004010015840000345520240d8007490342a4043c102c09400a5a000201085900311032421188120302f00780944c0c51003a0f403405034900110104001085013002e40d0f06507801e04010380709500f005480b482056022008248a00c018041041041140d542d04c06680804840e0201246400301001e0f0f0001620b40140c00d50910800021a65944940d80c03107880760001d450040c0822008140102d040c54207003da00c007040b032403034002d005510701040001c0c00da0380d010740682d085036682c4880d1000882411481d51594a000440141c5801c15020040041440c3d00c00c522850b811350320 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 881281357 1250 881280107 881280133
    0x61a0a03060e0a0e0c0f010203190e0306160f14032205060f1801050610082e0f06020309030d030b130e030d150f0905071b03030f150e010e06030a05060c0408 69
    0x200c46c01c200101a40150f0502d09049411050450700c05032900511800600c0d18201d43e8003000305c5403148002400803950003a00c020302070640302320500030009000c80c00d03078a0040b4100810580e50b2000484400c05524542412180030864074540080d00a0003010200070100c105a204e4270f0240c050f1400c280b00301c416a01c0e400b4201e40781582d506034480c1e1103030050322000e403040c540d50350880710341144c10201c00c40e4103440d04100310500810b2121440e030840208842030404101d0402010240040c0d0319041820b00007a40700d9050750610414596224800d80d00b0f502c0d12401d0038000140703508200b00301181030030b45030b13130b80d40120900c02c1c5810305003944d100020600c00000021078000c0d00c0020b1219040c0741d6404040d0100900c0c1e0f10030801040e18140074202010103880c0307042c1c001d46000500441007240d04054a81400b55426440c1d00078070708001c2c40340c24045440c115421015200ca4903100d04001908241c00c0000141c014401c040500c1300a985050007803045929920854403c500304007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 881282607 1250 881281357 881281369
    0x21070903020901030b1b0c0610060f0e090901060b0711040509010b0d08070305280801080106050a05040b03010219051c11030712061521061a0a03060e0a0e0c 69
    0x20000039046001c04004100080315101800e03084984001c415003449505614406c003034102071480c05040e0300840500c0440c00d0703030080c800c018069500d0000380f00c0c0900c24002c0c00e021500328803580109c41000c0010b8081e1004c1d070203040900200e80d4503ea46d042c0794208000030b801c6114006100e54600000324101a1051003042c52084c0064064030783d541300c6864a00ba181c01030401901400402c010395541041400c0413200d00f45d44c502c040742500034403074a008003003002c1600400c009031314065082c00345030f035800d0340798003240c00071038000c1040d0300c04101282c0a0300a40c0030442d00765076684032800300c43c0d130000040d2050000d241e00485040002d0407285007a074448822150a90008002183c01c4a109040c100c58a110304507001c10314036550540c00450b1803949125600003007034082d00343c044281c1e02030f05019080000740700744030032030034502020300086078031300c0c2e0103000c00001400300038050290300701d50001d05082c210b4403160701c1c11740100740c0a801780c88005c000500454800240500d025 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 881283857 1250 881282607 881282609
    0x102070b04080a0b04152306010305011415040306050106110d02030406091a120106020303180708060f0403020708100b04110a0e12190c0503190503181203210709 71
    0x10307004028104444d110425000b80c09801a101c0484031405a01d408296002d5400b0800c100000440321303000803250302c008594094030990402d4100001000030090320041d100c0d0008049580d00e41c401c007003240c48009881250320017042c1505100000803030a170010075000d02c0c1c40c256015201866803902c01261a48118041d102c0400c0d0045018404039201d00000b510f903510009010745000382e040c02c07401c41554268082c2c030044c0e00c00000c000c94603101801c000d201d180980010b2076642c0c10009540c1d10b40038000d050149050170000082e0501d80b003086210010715920041d40c5581d003041c4107160181040c2d2a40900460070010084c110105440894001d00f02580d10090584c9a80307007040848000350108223200d1042c07038100c011009000300b09025041c8a5080d0540045c0f0f03000506040c000da8118003100d0355204200203006ca40e01100302c80e0b10f1035540c01d2120400c5002070020301080380f1019240803500c40441c0c1300b03002c00d0031070900007881754008046614540c1e900700116160046 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 881285107 1250 881283857 881283869
    0x109050a02272806081003020301051f0b040e040b270703050715081305012301090b0a03030f0f021204030b0f06030f0c1e06130e011401050304020d020a03080d0b0102070b04 76
    0x85120420104d44104403003900035014446440c0700642e0ba400007400e50340c0c00d441f094070722744a0034119001d140d075410300d600003050300381c000714246450103140301d20104008002034954010000041c0d04a254a002c3da0070395400302800f0601d000a254100341c0d41c8032240001c88091140c0c0300003103442030305000e18194002007540e900119a440841c10354549183c281c0c01c4500d0340d00e91000c5044d034030b90030070b0081c594080103072103400a61400c420301d800d039030b045040603010300f03403100084c00800c0e8821400614029942011a400074208108a00d040086d002c01d03891001c02080100c01c0000c103601050240030b02140f0503103035444080804d5110700c440340d22410317250b215070340c2a0050b08000d803c8981c6d88202d1200750150880c10340118241e98041500c0c8200940d8441c81401860340d4a40b1860140040740c3c00049544c1c1306600107829440090320291141000240c0402195551141400174561244159864041070441071014240e17140c2c1d070a0160044580100751551102c0c1541c0813140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 881286357 1250 881285107 881285179
    0x8060f0f0f01120c0f060e01021203060622030209182407180e1302010207120f0206090d02030f0106091805120f04080f061512060109050a0227 63
    0x110b0540f12165402c1500003c4829185050000a96420003004c0d1001400302e611024002c13001d4100083c18448501043c80c0c50718414428000c00e91290b42c1581d01e03c6d100850f44141a4118000001a004075540000d51088105040004e1900c10070214820316200c43d04030782410300303d4500d4a520300d25100c0c200421500c41c0d4009442644910014040d1400040810358082d0701c07446d900007400c5040b14251409031506071500c0855904026201c0100020b0411030032400301c40e92504012482c246019101d0980840c007a219981c90001d2001d0b1180d0040449600d2120491514060100b40c420030300d5291a0202d000b20f15103410700c281581c164004094410306800c0404040f0301d0300400b00914049109100100d1020030030440b203400300c0303c07000c01082580390229104079682c1c440e02ca49801003000c054104101600020a20305481c442d00010800f96111b000401c002e00039004e0b0986036800c0d030ba00442e4104002c1c450900c4e000380a5620403400c40d80c094800510381001100b6a400c0c038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 881287607 1250 881286357 881286359
    0x2a030d0e0a2f0406081e07060e0103020a050d0f05011403032a120703031a01030204061227060207020a1202100f181e0501030b0f09040204020702030708060f0f0f01 72
    0x41d021806011010481e949404180110b4a0105040ba84030b80c0150100780c0c000ca000b0403401081c085050003000d070000040140b503051003c004d140d84008041507062580209800c80d141e070041007a510781c818140c00030000490104001c41c0548020f1160044444010b280a186800c1c0071084031440c486c0000948003503003145600316800c40116005604a009148000d0200780c110b40040040324041c0e500414a10045240b070445841c4890307115051508c1000304002d1140c0102d5294ac501e8203176440090b038103000081c0b800b101c043c0d91400d00e95992941031403c041081ca50b0182103410f0083d10800065500ca110030012046c445030065804070000d80400600c903c540e580d00550b0030223103070240b800410740f0070409210304945c1140403800750010030700c2c4610183d1a1802c0091500b40307070921859043d503001c125003420713002d4402d0049a8040c0041c055480c1c540440d04074641c00340851300d005070303200241c60312200d06880c0e0100d0060701c00c2c042007134a482c42807010b00820740c2d6a6180c48507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 881288857 1250 881287607 881287643
    0x150608070504030f2d140c1309060b0901090c08060301060b120c0903030a110c0f13020d020717040816140d110432011a2a030d0e0a 58
    0x200c04904111664642c2281070400350310f1509190a00c04074200c222404c1c0005886e1402d02002140c50626107548201040c1400303507950003041c0c10140d1503010001e511143d90a0038009000388224064101700c036500009106001913210305400747c800da9650300161500d0040501703940440c414004c54000c103001c8004a84075003a50181c012809a20883ca008500c2002c2400c603044200484045000580c408840d082c0600c20030403d40c0301114401d140c2010140013885131240c107281d05d05882e07404504244203280e00e034101d038502c0380c01618180d0080e840e01e1180c1e03081c0e40540510060307800707044e0341040e10001100c80c917016030b4180b40104a40030303810303400d100c1c200542d000140c51107000d444840741652190300c1113599800700c45060f4540340c20000005400e0a402c0d800d00004040520010824a00812045200b540e0003200244c2d90304442c4e030740c21410708039042d0b841030643c21200090212450000042101a0801500b4841c0c81403001d50070b9142c0b6450040900240b030f091401e80c5036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 881290107 1250 881288857 881288873
    0xb040308091e0a120219030e04051302011d0a0e0a050411060a0507020609010e061b2e0c18080c010e1e010c02040e010906021c05010302010c0f030c060f15060807050403 74
    0xd00c9520b4411200011803600420b801441b41500035004034000c145444c080d07003018000c040e40002c85030210419840540e0008040e80c0e00c032820313106011190f50000c401a621032016000500e15090000c0240c1071084868000302400e8500b200c40100d0410548903504100342510303407440003911032505101075074080c82516448508014100020b0452910840e0748041c050300311140142e41c0b02024401c140b800390300c0d00720405c051122880e00741310103610a0200011f0041c41e400020804251034407800341c01d0351047e0300c45082d80c900380101180420584400210164181800d0343e950f03030410907070814014100d640280c0c503180f94031040301c1324909500486155000500c05000016621440300d070107400c40348106070441d60181c00040c0e100b4266a2001000810100d41d10104415499940086c11a1010800040050122441c40070600d4091a162030b5501c3d0090001d104030000c01114a0080040c107034041e20020030020701052a611850106200e0b586a84a40385881d0541d124140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 881291357 1250 881290107 881290133
    0x150b0102190314120103030302070c080c0a12050c0d0b09070e0f0c03060d140c0f0603010806131a0f0601120c02071703130803040512011518090b040308091e0a 70
    0x1008401c200b00640e07004c00b500d04228000c6010b13640c0141c503030441d80f816644603c034030340c031007546a803041040303401550341ea580e12802c9132038048804003140098600302c0d040c440c4040610758004180c01d52981449610780c401881000d1510903a00f00545030b48030090320f0141038550007440c2895600003240b903800b00c2c00440e0000d00c0100380c000d01c00910f0703440808681e03110005041607000782d60707800910f051010b100b444004040315028115030620406590340c440041900000280d00c031002c00034040408a140810800300d00302d007070a0305d0406103590180d101030311028000341554043d0403522109101c0c4032850741460703001d000d4407840c020500321003111004510741e2a0204014200c05c0ca805407403030314000c02c140d40103503403920300d0300c420803400800b4840292116410100d02e40b0072140f011a6070402e03105450310141f0000b50000100e40100410080100001350010500c4240340d04000e14510801e141400c40d0782a03031302d017030603400c10503050600f115082d4420340030500050b50307403800740b1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 881292607 1250 881291357 881291387
    0x181d06090606010c2627060d2c06060901050303090906040b060d0213140a060c1203060506030711010506010512150301110307390b060319150b01021903 67
    0x5500140c42c2c0101c600c04617160416411540c0010f40900c030b0f05100381c0c11600220f000d003006859120700c58003041051082203010303800c1c15541c0000001c000c03000d80021921603400c0880c8952000d01d040d0a0355034603030545000d0301c69082000002142e140000440d006404040c1861030143c542006000c09882e1034195a94841d0041c4200314000780d00e4405058016025a50040103900c3d02482e050b0001c07400d038215000740400d4605006058011449000c11544040c14640010b818501180186030b0741d04516072042c400000e000e20907074403944841d03584480c00020400341e1113800041d0303079a02c038403410712290360191800101d8501000c07003d00b407601006070010079a45a26081020f1503481200c50b4408500b110159060304c80c1120301c410a406050000c81c9006041e00030420002c00c02020001c0c550b10142d0006901a2028800300350403c10b034100703441a0909900c0d12490150420b0007043c2c4007440c6c000c802c1c1d401c0d840000c4903120880d02c80000210301c400741d01c086490300e01d842404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 881293857 1250 881292607 881292623
    0x1112072c010516020a051c170708040605030a061503050702070b04050d02061b240901110910120c03021b0a031403040606121109090c01020d18181d06090606010c 71
    0xc2c950307d400c5158482128800000080401186400e800303002e031000c1c02e51b105800c14401103000541480843c0c06076101400c105407aa5104004000602541d8104801040308200740850302030f05a0042801600340c0e40030b450b4219201d82208038540030301c0c4909680000c400c1600700c007600f850801015100c40001039210041d120483e10f40c5400b06139002d040241e8038080003111078800c8200c0558124002c00024040c25042c10f010288500071124042e06c51103048800301c008501039040304c20811240041030202d802d45000250080d089441226403901e00800c1440400e840864952020750741625504405418043d0ba0303500303a000244101e946035500c09c00818a5a420ba50502107503208800354008441031800307025012602a0a41c44180d2002d14610174680e00172905698030341c0e451800d04000900c0d051307120526801ca9002c0c010701140403882c181e1410443e04982e0724501c2001d40b10724840525500075907210002c0360b80102303d07080340002c9600c5611401c0d49181442c06482c0c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 881294964 1107 881293857 881293859
    0x110405120c0109030308060f090a02091311161401090803070e01020a05060f0c040f0e06041b080c130905130201091e091112072c010516020a 62
    0x1421b000b4110f0000c1c0140d04c98000700312076204000c1075000c0b40e003090306034000298003a048580c01542c6841001c0980000c42c020307851840040c66440d490080c0400264103010000c1d041183d005410000d60303e80d05c002402080c0720706005080c07550746d9080203e0060801c0c401d200c03034241503400c2a01064081500401c4650f0b0104aa14184200e6580e80c41c41c40a40d00c00c0743c00101c00e02007007003404961420180041446004141d404012020034410105540030100c1e071880300103445800002c5503401e07850041c1c81440c20702c0c00204007032500d80700c010b03003916000c0382d0303620990002c19008415907a0100c0340303100802c0c104203400c03051f841c0d4a50030b0103840c1c054005c060003641c96256010380524400d084030361141c08400f0081d52802e0031100200b00041003016140700380f0010b12400003000402003074416481e016103a40d844c243c80c04421800c0300c030b211801aa400380c1c030104 = true := by decide +kernel

theorem cover : BRFrame.Cov 881115107 881294964 := by
  have h0 := BRFrame.cov_init 881115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 881115107 ≤ n) (h2 : n < 881294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
