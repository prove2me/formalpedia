-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0596
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:39:02.254036+00:00
-- url     : https://prove2.me/submissions/9a5fa032-1f4e-42e3-b86c-fe5e6c6f5942

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 107014388 ≤ n < 107194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 107015638 1250 107014388 107014393
    0x7021f0b03011515170604020702040b030d081906031e050a06090c061101090b04060e030408070602030414010509010807051e040e090610030b0c0a141909051c0f02060408 75
    0x43c40300c190840441d28a00544401001c148180d40300984985a058000440120b0000b07482c0c0341c182c180402907002010503030f0400e0316a501c5a2403900d003004440729403a0103542e55041403500c1c0390394444a50459031113600c00350071300a040000c500006800403480300c01958840e010070342407030018a064091c210080c08141400c902c20144101c0742030174002c8a274151503a00040042a403410300300c401011004003c071240c140401c02180040c0d0194400c000003204403481e05444040280c68094a607015a0040c4d10015040c01640d84024884240c4102820460309004c0720100103020044000d02d220100701002c01d185c0040695004010904000c0301d50642d9202d40b15148e80c84240c4c000c454101c001d00c0f900010444000b4110344000441e41c01c10b61500030394031803030040095035011030140010886803242d21850307070304050010050703001036441c0c21141482080d00580035445a42c0302ca44608543c02c203071042c40c410b0169041c04c4640c014805c04450403a0320004100703024a800000151 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 107016888 1250 107015638 107015651
    0x7020d030515130b010e0613140d1a010807150503042004090605040b07080c030c031506040602010902090702030c07061101060f0303260606040303050d06051005040608010b0307021f0b0301 83
    0x4811513006584101e000e9039801c00c050119402d1002d10b110b070704540c401d40346058604000300b010800007504044002094080d120340c450b16645090031401d420700101820050041254035010050900204010712611400003182d850141c040d00000340041c1050000100020b407c6407549404000710800070300802160006040c00c4c030083c8401c4404850480c0810040b03003440b4080c1c240342d44a8514104001d1441e07075405290842500040c1c00d41d00720084040b078184a554401000c2c0001c1d00c80c6500000d1900312900400403110005801002036401c10070445403805000300c0c006007954424100029000c14081115004103490750040350310f1150a00040704060784084180395000c400c0305141d007031190300c103181200d02b40142e45c9683d2240c0c00b00800c00c00640540e01810b40d40100400005904c0e5a60b40820b0071041c0329030100300012000503041c000b46420100345070251010301c0301e1074207500d4002d6020390b8448403420100751860001140310b05441d0a500818049803000e0001d1029 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 107018138 1250 107016888 107016919
    0x6051f08060a0b0f070506150f01050a030605220507030902030c01030c0908010504081b0309090103021003090f051c0302070c030f14070803041508060102060601080a3305030607020d030515 83
    0x83d4009400c115540e01887c80402c0c81e04400451780c20180600514800444000b640192016840311041005140d16588001003603030b00c0d101403074481c00c000c0e0340b1481100c11071000081110300007401c002c2454600400c49005d40c900041800c0018002c0c2400140031110b0182543d0040541d80910402d6003403100304400c12822202030700030079002d1901118150180414141c4a008070918640c020441000410140c68203002c80002c07044030381070020703102206484840e2280d00c0001306640640c418140f07115141c002200c425a60300507850118140045603071090a54080b510010b8088035680fa40e040034400d2036850641300d106c0e4a422685907607500c803102034a030f801900c5a4104090003d4203611030314020550b0758490001640503107191b59614005407203140c009403003941403c1d0340310ba0030580244050400180c19a006104040c0030360501844604a009a04540d0080e000401801903403a0000742c0008411170b1420045415610340d205501c1e03465500003940d50140491585485 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 107019388 1250 107018138 107018167
    0x30605040207080706060b070302210d0c17010506070f0807050f0304030302070e0a1b0c050c040f050103110406060c08030402010e040504080901110610030f05071a0d06051f08060a0b 80
    0xa4403509060264981c0c1c7c9030802918000d9000140158205158680b08100440300c1074030071007541c080c15414401c41c01c2d01d40c800c862000c075900010480c00d030712408030700c03241101d020b00401d4200c1e5801d141484d00d60f100343d091900c208004010000105480c400c02009020f54003034a0b411b0801c80b6111a503c0c01c0c020b55501092048901d040d00b0303100459a80d170418014504903880000c840464030115950841d80b0038412041941e1501800e030350445241e440e80184495640780c0c4c00d02181035411418180301e810403c410481c49030340340c810104402600403000c04a4190030411040c1c8944c0c9500040e03c02c2c650f03a03600ba6038090301d408200b0041086a40c042e1200c1c03002070343c41d03140c0103040e94401c980e1a0002c0c0c900803251140241700b00b000803983c1c0c0c02446054030400980f0b03034a80d41c2d40422040c00490080e544010240402c001206041601c100c1c4010700040300e0205282880021018600450a41e108100404040061501c0c1c0b01d10b40c40704014800e072844155940264504040d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 107020638 1250 107019388 107019397
    0xa1e0905160e0102010902010507020f010903080310170d080403050708040504020307030509010b010305070917100c09031208010506030703020f1b01020c1501050603161701121205130b030703060504020708 90
    0x40c041501540e0b440415441441007243d06036041c3c42d41c0c2d191410716020060790f001c26140e040d04011070300b800400003424850285021345460340c201440e49040c070500c11384018800d10b060040368402003030724040592110410b41c20540504190340e0301c160307508207002e2070f102c0c41d04210340140c00002030200841c1d0540c4011300c1441004003c12200e041e4078011015110180d5400b80082c0e503d002c240f181d07040030180381007089150000c5400c041d00d514070075015a51149a400b01050a01d5000c0042c070804001e07121008a4501e00002e143d07042c140000e10500002d8540c038201940810700c2034803495003c007154a20800b900c0c51004040842078010f010754414031629aa80c082d4108028214945408281c161100144418219603a080f0724030a220000050381003001004039009410010202c80e0602034401c1c03141e06429040e180c240800e00c604500500303020080200440c054103034126103070704142c0d2134a00d0160b540c0d40b2000c0d0110302919040d01710700c0e0310900c00124201000345180040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 107021888 1250 107020638 107020681
    0x4030b04170c070e0a090b0f06030706020706090603020304020d06021303020a0b210604090c1706100b03040f02040b18060405070c0201080c0d060e0916050a050a1e0905 74
    0xc0c1c6801c01c0700d5507800e81d8020481a6141940a00d0041c01102840504294444c1140c180003c1c803d100d500e4449801c03500769804d00c00d440d154420b101c0385090500009000c3c1c2210700060100300d18000b4000c0c00700040b48168400c05074040085411580c0c1c00c19900f2049401000641d11644011000d00c0d000c1070f01d1104078414881001c0004d83c40300e1b01d10030b442d5902e40080e101e800702d40408640c5c512060000f0541a40503541d140b010b4009201c22078000003801000010020096040d00e40c14031303003480945135001c3c80054007420003c0c00061021603034440c1c0c1c0515010904450342c80803901910f151600c0c1030340900301c003003018035620704403403964030620040760140029154a942510400c030381001c040e0004480c0c400040c49160464001d080760901c8510010f541660f4100a01c4540300581382803100c0d030800f482c4900c2540550444001a2100301d92104a280c90000069008945403086c1c900e14041c03100315504c181d1280d50101d0080c900a9010302c098604030751040b20701c10300e0a461 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 107023138 1250 107021888 107021903
    0x4230307060e0d020405040c0f03033615030608100c17060d1e0507030b0a050f060109052103070c050a09051504021b0a26030903040b0c0a0804030b04 66
    0x10328034403030070ba09110380314003422649642d01c3c60b03000c0c0070140c00010001d40305600e280c0700000327031300d4241602d10303000350700a0303441d24402c400d00c80f02140f00d00d802c000141010f200850700e40114070304c0900e10400311043c00c0039100b5500381001c1c6c144c01910059200500c180100c907074540006c0075036000145000e42c2e6565603482c0310700c00102d030210a541601c880d03801040740c000940004610001401c84010b488643d020b0342a510b035141890064135400440341c1750f08083c18044400428092190004019116280c091030b00c40c00082ca42081885030307610801c1c1454460076125260f100c4070100606081c2a82d0340c851003810300004642d01031217814090042d1a0000900e40081e1080034040c0c44601162014000310390300b048080d410926a00c0c80030b00f080c008155480b02d0400c8885201071081c1e44151002034000a2800800c0080100006502007002000300490700842101c003075490403d881c030740f64861108503038608540c0c180000c008010000740030080c8191069041e11440c8500d08 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 107024388 1250 107023138 107023153
    0x403031d07170a0c05010c0510050907050f10020d030c090e010f051002030a14090a0806131101020a02010c120903050a080711040b030a150b040906020d060527060105042303 76
    0x2c00b5956803440c1c54003030807000c05003100344000e40c41402c02d411036a02801c11030301c03042c0542e00c2003c00c6540c1600d00410550142c0e50800171410941c107080c00074101101c010061781804100a5140c01881c0303007101c1010b94032694074003840d00601c0b10342c0142c610b2003900a40340d80c5a10b808401441e9a0103600e10505600d50b109060902c0001162180900380d95010b00c03440012803928481e0300030f00c41c41075000d0303400040450700300000c000d03051040c0700c8680060100215420120700702e00780a40c1803411900b2500070403000d42d030070034105200c0f00d40c0a1040030401100107803c550061480e04000c100307016261210040c030035640c014090190203241320b92640e600341800c01003140c1004175140d8140e0040340f141c4010901a01c0780f003e03000081c0101241000004002400300c400d0304604640d40341c0e0104100070762580e1131140d10040c0005450280814050203a0201151050000600940c80c03200002e0300c240d106000b80c400409000805512501d00e4228400b0307420541101c443c02441206d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 107025638 1250 107024388 107024429
    0xb030606030c0120011103091e030a02030a05210c0a0e0d021309050f0105010b0d050f010b030408030901060b0a08060102061510050d0908040e04051e03120403031d07 73
    0x342e069040070058407481100740b4184903032100381c0e0004811003074556803074180c4185110441d00440c40f49808601811041200301010a010341c502142140c0f258000d100f00380c1c68580020840b207162441d4100b880c1c544100505100151115103d0075005070403e409000ba491920380c041c1c4990720203920b499031807000d2901804160000014065880201504090f1004109600c4054528045e9003517821002c0905415801c0d200b0a0780701407075406000459680d641920b02c170302d40c4c00643d400c0120000c2d500d05076841e5014000548098610320380000400d181d41e409510000092035500c05054440b0f0303c05102925004007200da55000d401844001041c8081c0c1d14031480d00800005c01410311460092406c840d0f0350004010841101d40d07904040d40400c00d800058030041c0180742c1c01440a00c1c0500d0810b043c0004010003010003050008091654203010040d6602d401c0d080d41c817100741c1d99840c2802c8010300700f140f9480b032400d040d14000900c0c1d103401043d220140d8084290054150300c050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 107026888 1250 107025638 107025643
    0x30c12020a020a060908091f030606031118031c0e041b0c060209030f07030b0103051203090c010507230105010f1d040b040302030f040807080106050d0809010c020604090903030b03060603 82
    0xd0341e1400c0181c00041842d000110300c0d030320107948203028100031418500881c02040301c1000030500412010100366010b0843c0340e06004000141402c5c0c60b040c440c00b03030006540c4465004a070340d81030501000010403859514100311010341c01383c038610f07040e905074690b840242c15405a4140103000c3c80c284403031141d94100c240c004030090410b507039400501c15501e4603000e0003500018841a41401001c0421084500802008010354044c10704070806d54910300d480f6241c206112903054081209204001c40c0d03600200e48125610707401e0030940c0e030ba000300e0700d05450790b0100781d00c2c0400d052031505240750030900154051810b944020303421000c603507241e160404070702880d05420014200c031003000a00103100d101d01c050300309204e40100c07420006013000c0441103800030b81203001c0c00e910500d0100107803102401218010720050740c07812954182c544130701086228010040341030021400c08903003107488001c121002080e0b208010820410a441c0081c09000c1050304030f032007407048801184461401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 107028138 1250 107026888 107026897
    0x450201020318120d2006090706030903030b090108030d0c050f1606090203150718050607030f120f060306060905010f0e0703020d050f19090507050609041b030c1202 72
    0x5030000e504000c0d5990038600307401044901d098100d1258030840312000310401040000801c203454809100c0e10807020b4108016011528040303641c060014013000d0200801c401003504e4552401040110300c1d42419405032007014605500400c200300000741c0401c0100c09081c003020341d41000e1001d40462400bc81c0c3d980103c40c810546003030304101d8000c24150344403140e0586c074800e4401041d0309000c1d80000f4104a5405001d10136580040e04100c00158403002c0c40c03020a011111a0744c1d86828000885e00714095910000c0902030000700030b0b040315024403401c03002c0c0599140c00f0b01040c00c400400c400900018442140c0083c10300360089803000b034502400b4142c80c520010004000d2a102012a5400d07006d08100140343d8204408031500c01180251440703402003120b0300c60a1f080c0060304408000f6070340d070904580c5140a140c0000120049048000c6400443d21903880e00c0000c0e00080003040d480100070001015000d400c2c1c60355826800c42c040b03507115074450300842c1a10582c00804d81c0718 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 107029388 1250 107028138 107028143
    0x30c061e0216050f0f0406030309170f030901030b190602010c030e010b2404030b040503090a050306060d120908060907080105011203020a0204050705041203030e01050a2a020145 78
    0x1450181407000341008510f541d940400200003c2d54401445c010504860950300140c0008800e03400034840401c0c46440c0c1e080003070310400108080c40d101c12621b9182c0c0030b880221410580c840700b04200a40c2c0d116248044110014007154080d40d0303c085c040d000f095100480300c042070601c034000d02800c9040c4203070100d001c0007034031121000d201d50b440003007618524050741840030001e100120110304408403091140348120000e50f50b130411142080050700196010700e11a6004c0c2d41004080d0b2074040c2000e6a0720b501c80d003c0c2030700300c2031030f401074030000d81d00d410407040392088008001540340e0005207201102c400b08003c0080f41d03201c08456001e0011440060096800003891400504169120541c030415030321303156080603108c2e6040b60004e41000003e9002944448200c5c910b410213108450300011701d11020448810203048200040c0c0000d029901d105003528070018075035000790403074600b8444000c040c401d4020007110000d072a0310400d0036841001c4482401008890000b0003a595130354 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 107030638 1250 107029388 107029423
    0x3190210181205040e090109060516270b070c031a070801060e01030f020d050402010f0815010302090f0306041209060521060f090c070b13020603160306030c061e02 72
    0x42440e11007a8081240702503100c2004010040040c5e034084840724540280059170000c20130b400203080c000213440c0c000d00a4056580b0202c1c01407001d5400c1440c211002c280403a400d94000d03140020070303091074003640c8030203100d400014411041000320840c03a01078034401c500401c84450044564012110704441c4d25001c50880d42c01807120901802070701d524160305150114030760038110756a5040c0c2e080700c1480d000a944171828032003150b80090341c501022001e0300c0d11840900e45040794500340d00440419034149540051221000d031502c6892804c1c41902078101c81113400d0500e03240c03862101d10181c0800041900700701140b11031180d421102c0b038039202004010318000320b0005000b006405001c0316032001030000140b030f02d900da40078943e10a6070101845600c50f481801c2040661000801c08a000d0762103103517040041c0e4400040e69007040d40c1c1c074541c1030300b56611f2409800400c01500301404031844828000399840e4070000407a241d01c5002e030144134242c0790b11400da80d138003d800906a001d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 107031888 1250 107030638 107030681
    0x30702010c141515031219030f09120f0503070210180501050712060f0803120612010216150203070c0213020d06080304170a1a1803190210 61
    0x1988160304445509000b04208034100020003000303840d107440072880401801c0001c00304009401450264130b440700055000d0b000001c09402c5801551141c0180c0c251000c080c00040e80d08248170750300165502c0300100b4104071801941c00d005450040c0008c0030f400080a0080c1c1000c4103100ea41581d00403c3d064004004900c400000b0703c0107012078904c905130900d409000607010501c01d004103802040e0350789500104012130400380007a1280c41e080603540720740e82d10f01000007010010480d00005507409004036140c0b40c41000403565100b0001c950700341c2d0300100d1840d900540c15034250403802d11a149460198450310703c118180c2c04100c4110001c10001100540581029001c62845600805006281030401c00107803003100d0f001d400400c0164000305040c1b01c0c0101c504103221301080b00c08000c0c81800030030ba98094840385aa20302c0d00e90a60300390003288a01c0440700f0126860b1001800f07403900c0d5100c1100199070002c007480d44500520403c482114030ba400b034810860211080101050314 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 107033138 1250 107031888 107031893
    0x807030c090c0e040f0501060e0d030c06021317070816030506060f03030910030b030c240d020403081204020112050907050607020f040c09031b050d060c020106030203030d0b090a0e0307 81
    0x800c0b00c0b926020030301004650b405002e075528400e100e00d41880c8800010207505000d0010a0064240c0c121406007209007105008684c0001e0a00c0700d9541c00080543d44111000788101040c12a034840d44c0c14070140c40816880a0300424202c060365074002c1250403103007107100e00b10800c0e0018400030f00755400010200e05a410b1118a4030307204240981124074041680d40800c850f111340c01070a01c00203a07a055540305030302d81404624030100d4129034290301d149140e961503248a1100f2001c090071003001845a402e15103c0d01075800031034100088988810f4211011200d400c801c40701280040c40c0825074605121540c480c1038001c0300c1003001041001d0800c0140700095111410a9070b0150f0802c81005880d52240222411605250b5420703094620394504854805103106080d007405c03000c00803d01854070b40036910100250400030214034440c4440c8282e006080e1900007940502001076484102c0c0580d8001840a410590384943c00da51741222080031074505074244841a0000c0041002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 107034388 1250 107033138 107033141
    0x6010608061e3d03060b0309030a0c110a06030605211903030209130e060a091703130b0f090f010603020f01140d022107020f070303110309190e010807030c09 69
    0x2c0000a000e040300246100d1400081da8420001080b0000302c26030942034010f40c0d041c010080113201c40c001c418150b007011480680c9031301898103440c04200041d40d00d4801d201088040300100d1102501069800d5140c03440100540706500130305005100c02c3e03120b00d0007603061a13407071981742e940c070400703002c03603405c003480107441110241815030403d5003e100d00006651240821041c40800100004001243c03038222401c10900506004109291420032004075418100243c9120280a0107d58903611382d000031412a0944d200070303004c40c808508015104102c0203a182c005c606090444a628034141c02d281d01342e510f5400000d400c131032510000400b65002d001d070340d032414074140165030901550700396405c1240c010321002106030207203240c200d8000b0303040d04c04c591308402144040d0801021f6040110ba99508520000f402c10042c1e4001e000101030502c165032141da001040c0316007000d0000711190313028039240151654005081c0c00012030f080001460402c403503111024611140c80c1910110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 107035638 1250 107034388 107034409
    0x6030203060312040807060f08100323010e25180c051204050303060a150e0907020316110306090d0c0305090102070b0706090b0a0c020a1415010806010608061e 70
    0x68141c0300311000c600000b0780307010203040681801c0004040d81d511f0010300038200e4542e6400403044c00101d030184203210b042500604166a0400c10304120001300d002c1c01d2095107a541502740d015441c0520101e0100404240751610146040b0501040d0300091144442600148150391240d200c20199001900c280e0304440b81c440080c0c1071250810810b40c080d10103a10040b2001c89042d000002004464030300341f8000005421800d504403052481c20001601c0c001ca1811700c580b00d032100c2400aa0558420003c44101c0100340c0d1200b84104850f150155118407646000c91180c02100001410034800003070a0a01401c03658810380d120345592400d481c264083d055442c1107010390100400c0c0301d41044000c20318203104100014052406081400032980d01030400c1520358285500300800c7c0d40e00149101d143d0b90049100c14024840e07100451618004401d0300c05106500400014000d4011036280e0403100c55407100c0d16141d0740e0000f0010f80342918105401c2d10060f811071013015003020810354 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 107036888 1250 107035638 107035651
    0x303041a0601021011070206070503030718030206030a1808160b24012105011205010b040606050f0f120406020306090a0b0a09020f0c06310b010302060c070308070309210b0106030203 80
    0xa403400d1b546401180050340f0000301a0f4a9602c008140f240d6654046503080305441c14048009980d403c0d0f50000300644401380c072080009460f022040d52141480071801080c6038084513455580c121110a84600f015007007050b1685102c0000183d03005440d4030310070300a001d01c8058081307a6054240150340388030b4080907940040c102820343d91801c0080e03100f0b075406094220044c0318003800d02e1030319500359440e0440c594041c0d41055410455039801100381c44214501c550265159910711840c941c05000c0c2c00407151041c1c480e441400103000c055801103010301001d481c440c003169111748602051340d0014034680e801141f50002000b11040507030280c800c004107030701c54a1808022410306450700c4016513521100c54045000c24141004080c03000d040c418502c6489240c00c10740b82c41b80380da81c4d1320510000c0d000303410009245500e5031040c0480005182c0c07102585496a450303040040100405000308800003801503000d5410300000d02600e2a500c0c2c1c00300c0c0b03560346a130030310504070701a41010342003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 107038138 1250 107036888 107036921
    0x1b0210050f0c010501032a09050903090303070b040308060625060f1d060709050108010312051606090203060a020702090a0b0301201306180e04080d05090303041a06010210 75
    0x601500c030031800300401003080100b0001c1207a5046040240c0e260440e0594104d55200c1e807000d028101500c45120012103030303042c02c00101740d92030302001410342c071516407081d45c1800b00255800402004855150150b4003943da008203d950320000d000d424490b91070b41c0c106591681d040000c03610001480b84031128405c000100d04142621445425181200c00390001d02c0b40141980c5031240c801c20115501c8070312460078258140c644000030304018010b010103004000c04a480c1c2c4d0490340110216801030728003501a03046242142041c000504021008901ca8000c11022480d41c420300c0c02900d2080f500240304200a4403100c1001d8001c00156a0107038242d5225a403030b4640182003500812001190880c0036502c3c00e01029140c030000719600600c061290048005180c84851541d00040d501488030f080c007240c65500304040c19024085c0366208060400d802c1203a00c1c10044042c601483c03040d512807003100140000d260024130100c54a50043c0d1144881c0c19a51103a50090500050032191 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 107039388 1250 107038138 107038147
    0x301090906060e071d04021e03040c080303070f17072a020307060e130522151b1101050601081f03020409030e121207110609120610061b021005 63
    0x2502c040d80f60100c40300f00c0801c070754103107146400f01440400d680b00344040f24114a0410641c4600c8100e4009203801c070074030701021001908001e0b140304060b001d0007d000450303403245000d00c0010101041a201c07040000d80d0356410303880f203042c641c0781e85000b0301003510b5400c40b10507242c43c0c00750408541070701c25000ca10941d4842c00542c41c1404682c004d4541569110391007803180c800d0000c3c166003101d4a0705082e2810040000c1c0d114200c0d0501d80d500000d00d42480d00d0109400d02d19094658020b0307440e00d03a071a10500f8034030280c3e0900d0082d0050f04988902d03080d550f0030b00b0b0003403c070383c0304503000e901140038000041c0301c505078a22405079044070044152401912070b008503040b180c000303030100c0c040391001d682c80d501842c1c0401040f202c00600401840f41c06140c0c0e1002c2c5050056903402021165511280744181eaa0131081d1140188083c26103680f040324a40e1056641805403846000000524004100c50b84101c442c80b501040c40c1c102e03202004040c0d802e0005142c00c42c00340f00c080103c240b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 107040638 1250 107039388 107039399
    0x9080f03190e0414010f0f050d060b210a020109080d08190915020903010b09070c080901110d12050a020a0203041202040b190e06300f0f1605010f05030109090606 71
    0x209245103080c00c1c1d10740d400e132503060901095640445400c06443d090511000f04403581e141da00e109061940460040386030030030580487c0354010070440c0b07038039240e00340b840c5403014140004540207814000d0783d910039507070f50314540d45171100c48525100c0001822000024013a80402c40342d885584c00100c00090501d0705038807a511402410719513115070b650005004038044c903090040e590700c500c0486804c441424506ca0140c015500c6100c000c10024020a15031101c1e80925850760041403490151282803807a494001c0c070001c1c110b0816a0a50f1130302000c107601010520903650100d400d82c00031403034141040401048401202d038120380c4940c44002021454a5401001701042c0005031070881440c00c10300d0080380e0b00401800c03c4c0c004d4910000c580702e00d40003180c0000d1150380f41d400080010034100d0300c003401c01448480c10a280e1003001da8074450040001480100e01460024041d00705403035000444110900391000e500182d0144014084083e080d1f1240d443ea0b03118010000300c0c10745c0d44 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 107041888 1250 107040638 107040641
    0x1030b07230c07090609020a0f03090804090f0207060f05162f1e01050609060402070501110310050f03030a0c14030c1501060e0d12050a03090206041509080f03190e04 73
    0x101440c10b51074000c403804002c0c5000f9070040c40c0c0600000b100550400b580090000d146581d280058402c150700c0c0ca941d0000c1c84510011140a0140110305020401c50303984410040d620849040750724524140d40729501c1170307452041c03602480c18081c1c0810b050800720000c0f40d9420f051080c024451076940040c0381c40c2c0c3c0d0001031001c203480581700542741004c0401d100c0d500320080089101643e90511041003e581d40d40d01e01c0e141d010300c0444005840f03076040c0c14243d00408111008101140300002070051921400300130781c00300d9404a9402d5000240c84061686a0059170440b0010450f0102440300003680004040c0042d150307001284e090980742c00105181802c40131031080080301440050100c9580000c0303040c0155015141a400080590303154401c207448070343d01c0d604208000c50a440580d1180e00560030302500200400c1e00c3d0398031844608100f20241c81d05d9070204940c0000001c2000340814525220b062900155007407025072403003441c01840d00e050749810442450361700c95103545c1e907 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 107043138 1250 107041888 107041897
    0x1f0210060303090e0708100b070609020406090203010906050a0806060105031803030403030f0c030e12210916120302060115090b030405070f0828061b020a02010206070801030b0723 79
    0x207a40e5183c5601d00c0c1c4410024071000103852101000b40b6081081100c0c0d240c3d40c035090884404004041c0d07510903034144207006141e6008000c0d48113051900003e80301030240c01450580341c005004120490765441000155202d901c204100c9402070f00008020398041d07806141c1c840c1d469400404134a20341c56102d41035074000c4404502103641c6500d101c100c040144030341000d0300c01a003810404031000001c4903a0f5001d103644c066082400029010500e58148010481d85100e0400446824100385552640f1005084042229074410480020380c64108190b0407181d6034054015080d20703400c100442850a003060420014444503100010700c034071407240110321442c0210007034020b460030007064126078074440d0300c07040d03861b0701202c201441d40107d070008074103d2001c403000c60480280c514241000d00002d0980307800c2c0e880b12420303000340c258000c250318005030b200b40e007078031465605c1040a0303032808020700014003030716901c40002c2c407541e00074185a08a081c1100103242840e0500303032400b016610 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 107044388 1250 107043138 107043143
    0x3020a030303020d0c0801080c131508030909060303070309170309131a191404090503040e0a0506011803020f01021501060c0213050903030c1c05040c030b060f1f02100603 75
    0x3d0008042500111a200d003821500c464600130841d54036101c0c0c0b0070b80d51003403070072154451100f500c034040c1705a0700c0ea444011010800107031050603a80d5003c40300c0d2642c00c40650309001c1c10041001a000380f602100b103c0c2403c5c0d0584448400a0030142071118070284109100c0709c0388010400c6044541e500c488001d0780140c49c001c007140800100484034510341039601e04500403e00049200400c1c81c041050a05580704034400e2042184802e001030040c1220340400340c21404001404611710314082c0505100c0d80c807400b030502c050f44480c0c00440745528800c8542416040c031400900040c0b40c1120b118a140c2e0307052044413041e010b520301c13a2104150170790141000c68194400c21086040200502c5071811184034100040d01e003501c0120b4980c8002000c4601c2d0900c00690840030041c01c058031503924203401b50412491426203400c4d180407206000a4a40440c110001505494110040081c202c4041c02441822403490021174004400340d80351000d500441d1600003819040d403041c10025030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 107045638 1250 107044388 107044391
    0x12030f0313331401140d0201030618150f0602030403080d140109020c120c0a03300506010e030a0c050415030206030408190816080c0c060a0504050118030212090a03020a030303 77
    0x180c030035122a04a800c070014403c081ea60000040000356115403a50300c0508058600e00201c48452004030000e00303441c0c00c20003c8004a0040d100f8515a035881302e0040c440c00d2200078a42c40c1c580c803800200140038428000142d00402c0207100040e88030001d8a00702c202240c2c0840c1d64550380d100c00d2070b01388d8241c10160540f070b80440c5048680c1010006010300c0600009000c0c0340c410000401512440000c4d40035040c00f000007a00091411003800050051042e15641d025a004442032240604000d83e44140004c0c51440c1d52402440c0c0860b10742401d642c010843c40030203150a05120103406c00400039040751030982000805030300c980c0000c51049116201e003a81e914030b0720f030070b10312001100d410f4201008030b10010407200303404000300b03202403090a0420509598864240c03210360b1140324031544042c0a01810b203c1540b40e270f500301c6401a40f040000307112101028035243c0d14202ea0500150040c2c0c022121501c10344a044014a000000640080e51003030b10380c0c01140b56100c19900440029 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 107046888 1250 107045638 107045723
    0x2180d060b040c03021206040e030f0304060b180f040b06061308060603010f05040203060103060b13060303030e0d0f0e06090d02060309100501090c09090209010e0301061412030f0313 80
    0xb8a45445000704007010303800d086080100c0101d0f15131110800811a43c056607132241c41043d08038081003503540742c00f48071484554910305032428002a16070006414021015258842c20480d1900740d128415100d44901c0400c650303450b1264894000c01400c09600002e00f04080c140400304c00321f80b60086d10094000341401d05110051608403503d80c0f034038030360241c5004244801a41c0200c1d0440c112604081c011484441e650005005685407400c40d041240c60b0001c00400c040d0140c0001c40b99105441c190307a4289000002514590711480b0341c034000a081411100140c500f0b0405031100c41c40113060880c0042107903000c03d800d41d00c1a1a0003005500001340409400014010680581007000043c4005014914060320105171070060202c541c0d008200c892050340f2400002c295018000d000340401556008404640e6521a940f40c2c010340903c0600b9016140020407954002c44000c441c1340745588629002100d425803100885031205001e500303003c06040d80308040c240303441c2c1130f0000344030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 107048138 1250 107046888 107046911
    0x3050327190302010809030f070c03030e0904150e03040503030c01020433050d0b0301050c030601020c09060f0d0311010c0801150305090706110304091406030c0108100902180d06 78
    0x2520002103054072404840d44000d1006a01960348030440e542805c2011050300c80466540c1035001e59a000712058401246c084240075404a103042200d009450b14424a40b0140c14040c1d8520111000303004144074004003102600e059104402e00c0404400362814183c4640000f42981e015000800840e900490188400c0803048810305006001c420308010840c11300c0312082407040d542c5103400c10b210000c54060a60800e58200084802c0000c00130400340c500b6080d0720310703507401c165031050051240e5904290a0f003017522405010f0000141400d0306a5801000c01a011a410f00210b0070080c0840c2100d0310001c003406001ca240001e510360704100c3d0305203520f1003205080000170b001014180818840c48031400320b0024103840386444c5c5540103401000c0064034520a6900540c5858a0004100100c07010910300500546c02101510080c1401d80011110340e1416101e500b141e250b0040200b001500b035500400962210703060000b81030010a0024564404011303003a01d00640340ca0b411100e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 107049388 1250 107048138 107048197
    0xe0102030403090501090e0109050a020705032d041d070318120e010f08070309050102300c030105061b010914100e12160f0204051014040c0c1506030503 67
    0x14013030038a003403000b00c0d240001500d040c060601c03405014944d114041207403030b0303482d40444891300d03000340480c0d41c1c480f6204103008040d040401d80e211342610100c40d006a0300c1c034600864040300d000c201c002c04607000703c403030001e000003025081e0300038035946006081d068050318584080843c081e500085030902c58042c0a0f0007410135154407410000d02e2640082c45640010801c1c0d000010ad290000b1144203d14010780280b140d50b800c030142c4c1c80c1640300d1300d01ca800d2004040c403402c4003010940e102512070302099402400280100b85e0700c01003d2104030f02c00f104080e006c01c40d0414400c004261403d890b154990000741d104003580c01a0441c440c4520321805600614000e280300600900000c81003c043c4e141d1401a4140403000c040d01e4803801d0144020202b41d00d81c0290003c204006604203400d000c9400c0384640700d40c00207440910744012503403505100c0c1c110503141d6915441d08000041d03170382038400c07400c4803483d81c3c0362996a84040301041040015220b41c2d84e40080c09904892624040c0c2c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 107050638 1250 107049388 107049407
    0x1e030f020a1a09070509010b0a020705030109020906100302040e0403030507080f061c0c0315090203161503050406020c1b04060906080d0c0309080a080901110a11220e0102030403 78
    0x805651000c00d032000041c1c1d0201c514040e0000d01c103500791480c1c8a1908103401c00c5003943c010707a40311090100205034120010000c0032125000e400b1121120342e00d0307051501342d624a41000e0750001c8080001003441c100303095841ca00c05c01602e07005240513122001c030700d4003c100741c0d13054001071358800c00c00141319000344a00343c111251644024442c0b40c4140024450503001d10402d03c6890014000c0081040d8812510003840c1e102100c0c4500039507986004000f00000c00e41680301e4814400c000883c40700c601c64080c11f90f0b40600ca18001c2c12041001500500400351088400d140d080050f452041010f201c0c079a01e62080c00c08184240d10810200020348030032b03070400700c180c0d45485020020900c0010301c05107056003600b4a00c841042c18141036407042d040c0c0d40240381501916801104128108009081d0b440003603c8518403902c010590555031802400d0090159140100c01d000c50300d0142120500c2000f10580307464000100c084010540d50b0520035640e45a4001c018041015045030070340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 107051888 1250 107050638 107050667
    0x20703060b06090a060302090102011404050a1205030f0601031505040903030504110f1327123f0227040509030f07060e010605120f010c050c0705010e0d1e03 69
    0x542410b5400f4000340308442c8610070f0409056000480b00a00d074000c0d00b0010304461481400c50080c5000d040440e00c40c41c0520040322044d200a1800c088980500d054900402000b01005442d90340e070001500202654581d8118603007200000242503550350242e55502403080d03601181a0030245800003c00100924941c410a00a040078003a80c44002c040b0070356110740c607404508001d114200c04403e0004c249950020386010101106100c805410000314540c10359481d0540e810b1030902004c0b10310510700c050304c9820404600e031400b840c0f15841420100034240c0040c0f07040744042100c000350881306420058041e480c10b5010251905100d1181d101c031000014500d08607a100891210f446080f5005000556844100d032070210250710040203080050720b80f00c90070314140000740c0d1321382c0310310300e141c070079600780b62400040314440d4042ea610910182c00504099041c41c0066404140d003a040903048140005608041090320b1440c5076443d00d408645010034210b82401441030b078410201 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 107053138 1250 107051888 107051899
    0x302180a05220917030117010213120302251706150111120f03040204151a0a0e06040b0c0f030f09151204060203010519080a120903080a020703060b 65
    0x2040030752581588080602d4540d5400781c45a90201c0c040c00c010300e5a0700c0b003c0c01009100840884000070400254160f8010754100180b07800d019000364241e21864512080101091100f0080e00e101038044030035441c1700c7d005442002e600c0071a4035114106e000b0781441000030910040002280c590005509541d0340400380001d85012408559422940580351781000b0b40b00c80c99820503582484244103268036131100076503410305128541100e4100707903800e0f80300e50b15254407800ea40025418540442f103042d03c1045882d200c18803440340725001140e0081c1031000f80359030b03a1102c0d035031040184040c280e08103844d5242c25803c400d0f68540504c800420348168000c100701d44141503020142c528554046030108800d840c524901c0c0020302980c18801609402d80e8180801c001da0340d00994161a401c0c1c0c0c403180045a40e1050f0300c0688024030400006400140c00072012554000c0e40000d03000013070400010481d070340d0761114030f00d03072190b03d1090040e080400117008112550042141e601400c440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 107054388 1250 107053138 107053159
    0x10b01091211060f0408010e03030703050a0209010c020603060406030b040c030303150e060f06040b03040b04050d020a0b3702130f051e012303010e0108060408040311150406030218 79
    0x44404401196220700d611502e03000c80c1504d000d840501c11240544031030382c000d02009411031001d80c1e690b04256020400310b418a40001c600110780e100b5101e03000016581c6d0380f029503031074080c000c89a00182085400079107504020002c1015080743d540164401c4d0481c02110b0320354100101250701d10b0020f6420b50f02c40281c02c0110101d11070120303810210480d2b13403078a08a00e1000180452045511040301e02d10040100401e100f200a01d59215a00074402d0b182d000e40589402c0740c59800c40f1100505540c0200081500202560039182800b80d4801081001c8600d0400c2c1c10500c10074a1205c50341a50005121a543c40f02e200707007000189201c00d2003205c260308240004082c1a0f425804a0692100c103120320105d070310071115180d548045003d002c5c47c10410720103440c0070380e109001e414444074890700000bc10040001d0f1640c0301b01d4000030003908082c159940c80155401c004480f40d402003085400f91801d415001c0180000c1c100742d2001a580d082d1150344002e90039280b000740d840b0f50f55a44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 107055638 1250 107054388 107054393
    0x1090e0307020d08092209030306081c05030603070815040317040305070b250c141b0d05030f190f02070e1816030605010501090e0105061e090d05010b010912 69
    0x1c070007024284d10000a5440b5080d04022078086e02d40c100d900c80700000c440b660112038504a902c06680103000f03030741c00e1020903180d1541c0d40d501d4001e4030501c809841c0c050010006948103a01541c0c005a006040d01c0071640d440881c24602611314080e012404800001d1104041e0850386041480c400c11031a0300c007030326003a100036011303014400000e00141c45160000301c000c3c08007a00e9140e034145c501ca4041b10a085c11000a004a0101e030040711401a803a90207080d0141c0080c420100764039488048003581c02400501c40000c100032400c079203e20041c0210dc0a00400c0c0003d031040c50036100c08044120043c80009003100d05100c4c4e40d10a41d0460034052040c1207802030302c5a800000720754151803000c1100c0c1c40031b203421032032150020211172200000c820460340341c000c181201c0090361030808103600c0d5a440c081b040028814582c1c8440c0801c04041c0c8408000c0b045401c4440444120b4109141140400c074055448001140d090355581048001c9680000701d07000503001030001102e681100b41e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 107056888 1250 107055638 107055649
    0x3050a090e040807120c0b04050f010c030e0601030813090203010b031012020312031b030c040603060e090d0f0e0d150c0f0504051509060c0d080a020712030b0f0409030801090e030702 80
    0x9000500301d000c0e5240da445c8414010740a000300f907a40030540420a1074681411921160004041480c6500707001d50480e515100740200b120f400c40941c040e080c186d21b15075440616500075981c078554804e010700006042d10303852010310300801c00903c0301c070350f0780c500500005d0301c1406982007200b0000c4c400c654007000d03880000d01c407003804e68000b0720195203882d44021a62407504140350340243c035000204020f16244480d010380201c0e400c98406010721516410b0381400c400040f6004680c0358000350007a200390f48141c40740141c00105e810b0082500c4a080042040c05400550a48185229441401e84010207204401014803540380011a504c0280c03802030480c40345109041c840d0700c0c480c820740c510301c4460b0115516030f10001d1070a80d03129100d2100c276480300c08846171200401c0c095800201d090300e80d402218600340e40004a46507140b181d045c02d0f002069104202070300071280c2c0817101e44c40c0d00c50344034400800340242c0b00d000040d03240006a4040c0c0c2c08001d410000381d001032007c800140c644 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 107058138 1250 107056888 107056897
    0x161e050d120c14010204080c090115021009151a0111010227130c0c0302010c140a051c0e010207020906040e15090f01020304030e10030501030803180c060703050a090e0408 75
    0xa600d0700b804280481c1c01c11503806034008500b0b020a51001400049207a80000c0140b40c074481a581040d59070ba075005107880c11496030154001582080d603c0c083c0b140100e5100b02645c070f21802640c01c0610b003021a00007103c1c445420380102c03404680a0a0866810070259902011058001d40c9880350701650608505140380c1050001040d00b01e440c50680c0c0c0d282201c1c0c10091120100300400038194200810b086080d103426000f65180a104004261146a50012429441002074a08401914103c44a074002e4503080c182e14540c000d0320b2240040f50251001d4603e80400250700c0e1003071801001001100500560310035458400d050050385008201c001c89500c2d14040c6c1803550355501ca0150a00003041c00108540d440002000308040d00980000c9402c1401c1d2286180c008480100340c080700c1d820301002d031590906000042c0c600040c5d481801880710110701b03503101001014003003851600000402c6010a001061041c0704940c80300d070000090010041c12203445c28240c5950718140304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 107059388 1250 107058138 107058173
    0x5010501020d1209080d05010f0b030105090412020f1e070e0603070b0a02070b072012100507020a0204060f09051b1204170d0b040b03030c06010b07020102161e050d 72
    0x50380304030200618115071040b5180360300305162569507440f0740031b104010032003409550000700c40b011011032862400005e03241a150054840b01080c2c1320b944414815085240717403581188600c284e0142e5174401130021141c02000b178150760001142d980312840c100051078100e1f00c60a0106c000304641c981d000a0308900712100300164036680c03a000c0c98100c0c28040690488103c003100080c3c024200011102451501401c150700030111030300c060100f0090140c84102e0800300c1d402245040320142d120380c0000d80001039801240c03402c1550ba8041416035816600102e8942440f0f10100f144640d03a002d05903000c82d450303c0803a1a44594140d1785024000c40c3c146032905800700d40041c0802c80c601a203170400a400b4454a511910400803410151402c0d650244c000c2d820074181c1c411a06000050318403203401e90700684420317800c0084980007500088000c0e41107200f554550388001c40440300c000050401c2000c0141803044d10758a110005116500c03841c0524090a40036000c9070000c4682880041d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 107060638 1250 107059388 107059397
    0x30604050702070b030106050a08070c0206090f1f0507060c0c050604080307090515031006090f0b03130f050601031a1608060112061e0b070b0c160506010b0d0f05010501020d 76
    0x1241c68100703d14180441c0c01400c0c068100100103c1c1c03054205001d810905003540d520380d22b59689181c00c45184c540e5510081d0840b0040c07009040b9458005e000c417000d42da01800c0f82c2107090000c50660b01c90780f00700b103038140032800004000c424043c00f4000c0c02a03582c10f034144100c10360200c0d510140c1d035410040014042c2000800414400e030710424031040140001010285101c624140c2d807400c07603205441d050020a0355410006281e030013200358204551000240e00790507883c0c1100100c0651004104d80306040002482c00009492401212030302400341000f0301c1258114a0b280d1414140400c5c1d205141c42503d082248607218880c0c4030205010302d2500c0005a02c40341c00584004500343c1045034450304003480480c410368101a4403500001c080b0100e07008582e603001c00200340c85920390261190740c1000000d40000d8500c0024003056140322500562800300d2348803d803e02000380c0140240910004880101c88110700441490100d03041c0c04002651400d07001075540d902c2c0200800520 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 107061888 1250 107060638 107060641
    0x30807020c0901030b070225050f030304090e0c1003050c0714190b060f0a0b0703050715051003120216030209060102150c091804030f050711060c060402040501120803060405 76
    0x244280402030054001510b20325041d6103a2420383d00d03503941120804014440d003114980c444412042c041020f4201d544d200e0591400e040600c04061060384240e83c061004010024045205d80315075090049500040c7c00b481003101d0070071a4030862155038100301401c000502007048485011119050b50210b041174484071420f40c0f00d030500e90702c10b440e140300c1041c0341440000e006451001605ca1102103ca04000740c102004000b040c504502401078082030511101000030f014200400545000e00e105c1000842c0741ca552000340c43c1704450781705803d841c0400410400c120983d40d00011101030001e030000c1075609844a6005640e0301c00070344140d07040307008104564028008030121442000c9041c082d1300d001406080660b20120f46180514440d010020341e1044503100107009990550303480800300740d100401c4030260400307401551001c034a0107a01d02603075210340040640e001d00b00054000d0785041e004100440e03070168030004820030415041d40004042404a95101c5400c86000409 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 107063138 1250 107061888 107061901
    0xd03050313020d08130312050403030504030b060d020d120315050915040b060a03060807091b051e0c01050403090510020d210c0507050f030901050405060703030b03100b040e0f0a0308 80
    0x50103000700507000190000da000107203200d10505c0320550f0b00600395811642e900040403541885a8070014000620a000610001e107015034021b402150040007500501c0d06500042c8150301452800c0b10081c80c0d500780301c3c0c0510f40500403030700b0100381c00440b0b4503040e1400d00400c02240c0010300400ea4041920781080b15030b6202d61202c020190041c000944a540611024000380041d0182c809944600d0a000407003040354084d0144403055080c1e00c80b9070301500305041e201d940200e50049581c078946e17040d400e01100b801010f003640d03113070003400031409041c141000f5008908941200740595403001060b010142c00048d50000d0700400d141040c0940d5085901a419184031001f00c101c02c1d0410002030700059000303002d0200a4002c001b43e8841d43c4a225071280d40740714404070785010480c00d000401542c600302000c0e117000c600a00300854003090140020f400e1040015032181110b030394000000720340c2007078407503d1070750403180006040141e989506140e40d080c0d5158020b04212076903000540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 107064388 1250 107063138 107063149
    0x7030c050703150f0605090403020705011d03100615090b090f0f0618031204030308040f080705062a03010e0609040f1e03030b041e020c0c03030c0106050405060d0305031302 76
    0x150f401c1601200900000d100c01d20180c0440380800021074280f01000c01c1c3d030720b840203140780945e5254000702900352604e00107440043e9120342c400004c0e20f202180c04103646051041072a040704034100050b180e0f0501480406a80338600c2d11410404007000a11103a41e1500c104d441a01007110b1356100c944010000800d20200c000450f0b421501c08118800041c9060116030801c46049007507072502030701001d610140e80128031018002030340c450042804070755103510b910200388c000c1001a00d005401d4880e180b8141058580d030301420780100003141d007070024150010101401580803442c552405800c902150005403820f03104005070400b1600304040c07880c2c071459a6038080c0580340d19280443c290a00810201002d40100341401c03e103a405107820721881e0590300c0c900410a0700c80124042540017904445002040703032140d8100c01045540c04c0000d01a80040b101c00030400314145800e02041d90000351441c2c0c0a0b0703000082e104002038111095a03070180b0303040245620060203000150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 107065638 1250 107064388 107064403
    0xb070312051005030118050705180109090602070602070516050a0b0904020306030a021302091813060902030c031519020f070f0c050a03030305040c0503030c0c0f21150702070b07030c05 81
    0x9500d50f103000d14a641b800718800301c855025000e002503c1c900e903036890510103003081100c11541880b1104005105541e00790303002c000c000b0300a40c401809c0090070f0b620b04040341d02104003034540c0c0c0d0000c044140f580e030001c0603840240000341d40b000005460f085004a050203000c9540d4415500480000d140340c6042041e003039155001054424454580d44d00786000358003405606015522100038120b482d140210814020310094401030301020080e1503803c020300c0f030707101c0c102e90600030b440c2c45100e6a5020400d8411002200b10003604504103030550004420310b400090072460b006001d0411404030f940243c4200e65001040089420301c0c900c0c00e50114107080d086564003070007c074408018113915030300061065100d10f00700c0359a1603c84042554034080e0b404140c1c07440c0c1c0040c0c020340d00d0342085c01c2444640340024185c82082c0141880b0200100d2050401800350303405200704005038030054800d95000000d60018025140c01e01c81000c905106410010742403150b2892000c1c1004410030101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 107066888 1250 107065638 107065649
    0x40807020a0e0a0501050409021c14060106050406260112030909151805090d0c0809030706050c070611030a1409120d091d0f07020a0f06150b0703120510 67
    0x618158544406402c01031040d02c60100851400c000800c040c2002d1080060054004092010810700c0751314004042d141d0316007c41e44d008c0c4100800d086817808002c01c5e40a8501500c4881d211424510000c0a00c003030403403080d440d002a1001c0205400d2000c0c40141540c4500315001c011400b20b040c16071324000c03194042c103640c518040d4407550007011081c004c41910342400e07500261442426202c4155241078507000b40f0360700000629a000d034050503011001c184540a024105058100024100070701d82e8810404103d00045e040c0c0d0760b9006000c20800b40c04941404400000d841410568030b00030442c0c0e06090024444200c500e4403445425218403d02c002c044425000c0c0c400b550f00e4640316000203507030105d680d40d031022a8080d2003440d007091820600c41d070700b941d5a9417842c0558103420060017034000d6000703841d82c0e40b000c50b04000c040920b0f580952804210f80c019004403214642c0d2a0f400b204059130103020200009921000410301604005400b0500740c803829525820230b111503210 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 107068138 1250 107066888 107066899
    0x9060607120806090901051605030709030b040b0604111602090406090524070207050108161e030203060f0a08191e03020a060f060f0b0a02031b06040c1406090904080702 74
    0x1240c050035400030406110710303c10741e5103084c241c44030b0003c0c500740d0b8002d842343c44410810060500d0780b0b13072140004c1c0d40d0005003072070070403c580c1d980e4444151540702910140e69040b640f2040082c18201030041d41801c07041024201c0c41c0940340c0354049070040e0700e00320080c440c8a0f640041414003c2940240f078a042d08242901c8860041c12100c0d500c02d040c0103001104032052500165060f0f0003c60514100d641c10b85072f9051642c0e401010440c070280f000418000c2c0034201c992204100301000710400380c03030150744005a032814210100070044d04000e410921036800c568080c44139000100304c0c07200c4e41c940101c20004000881c41e000c0440083e20b41c40f111035044111290091550001c1c800d240c0038011102000000c04010402003a25644d020382d40450940b90400c21000c00c17148000c280d80401841070728149480d5845005008004032400350090703000c03e051000348804006554002c0c410000c0803010b0085200104003580680c400261151190700d0002e000e00011104403130a07540e00405 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 107069388 1250 107068138 107068163
    0x14040308040b090108060a060c030e060409020a0507051203040c1205010e01020307022a181b070309051c2d0210031d06010501080415020d0f0c0f05040e010509060607 73
    0x400b450346400003920380d07000440c14404034400b0b06040314084152200d80d5640a41038055440940381b0568040e0a01d0300318004100001e0300200702d00c0038000265040d543caa036035000c0703418414a8144459005140b200080042c000010800c0b00300b9011940134055402c0c200b034a90070864010205410041030950001003000852640400c81c014400c1c0042d61408081c0e20302d44400500c070803182eaa19030040c05016031103040e200700c070510341da012000d001200854285803001c48119044444120041a2050401c4c0701c20728000c020301d80d102040c030b044070205410907203c0c1200f80600303c9600c10070850180000c4075044c011860840d107590094501c840c0004258801402000c2d09516074054004011311202d1360640031035500c0c100c078070594989020391204c0d03d07110112914202c0d0203420701d608010401c0c0c0b070b4030140a060841003005000141d1345000c1c0101821111b603020109040110130081400b140b41002c1146040d0f40c42600d0400060340d402c4080b030800c1c865940b000c0d020000c42c89 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 107070638 1250 107069388 107069399
    0x90607120915030c1e031b0e0103060b030f04030e030f150406110a09050609030f03040b03010e070203030c0304033015091e0506010203071b030203100c0f180f06030f06080a121404030804 82
    0x235481c5001d6042139030200680756903000110180d01050724081c84aa0401d004100424031814040c0740b1964001d05a4a2810fa032101e11751520004001c200e8003250b02600700018032a2500c1910604259500301c01c0ca4a81d0900b801002c0204502030b040c4110030100c6c010342d268800300009020b581364501243d66880d114100d00a55030001d120f10b8030300815450024401c0b91010055a010f00d0322482c480d419078550b540e06643c0d00410442d046034012040000440c00c14283d0a50700c1c2040d00c841c40021002400024070990807810b030450054141858a42080282240a07040004403071380000103213601c400b00101d041d0300c680d0324080c0039503070b4485440720030b000b040d0030003400c4034800c80403982502c000c601800140ca10016050011440c5100141e502b54052506041c88400c03a010000d042038496904a5094a040d0803000010b076944091040031010f52046201426004004000c1c000040d594940c8000300c1c0c21014007000610a0311115490360781042d980a55072109100752503613140c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 107071888 1250 107070638 107070647
    0x406080a03210630050a08091804060e06060a050a09150801021b24010e04020d06050a021e03040b0103030f030f02070b0703050a09020a0506090607120915030c1e031b 73
    0xb50361801406842034600951008907005079004c1903884005040b1032242601d681c22590008403550b50410103810003141c42400b0040814841d510078103001482c0c60703801c847c15141020050215000d0301403036000740016070f20f0b00c0c0000e080300d4101d40f001c00c00600ca210781400c0c510b410703440103c203580003060700c681203120481c0d800c200155140c2101c981d41c504014018094154810340c42d007000440d8018003c80c03c410081c6030f0301031b0014013006096045540c2d11801c5890480d440d2802c9035003c01c0c89400040402d1740e0011503d2180c02d450300714201910790300c10411040c440102480454000d000d420342c001c0d08040c86416000c04110340302c0d0541c5c20b00c0c190060040b10b1141c0000e03c0c0400090b507413a041d1280940c01600600031100c0c1300e00384010701609a0000320b00950101301400078200080c034000243d181c200c500d5441400180c039088040c940e030684900c3c44800c0c5820980000480740d07102d0000f00320000308072030403424580380900035070003050304642020f090030030580908401a0007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 107073138 1250 107071888 107071919
    0x307030f03081b03011701091b090c030b0f0108040320100501060804150b030c0a120507120317040309031b05030d090b090d03050c06010807090b0406080a032106 71
    0x680ca508100e6543c0845003100460200709028100b041800103001c1440541c1d2403c000614030300000075002810f03102c89031011344035450720000c1496110144080c0c402d5000d602286080c0e0305003808545800000030743c50710141c80c2c0c55810809111b0001c0c1c2030500c00c90075004103607641811802c1040006c8082e64440b4101d007078200740079003480700001e10f0034401c0ea4014443c0c0d0300880c00c4899518560300e044003130200c4805c1e40758035120741c510141307082c2d485c0c0c40038100a01c3d004082d0801c140030b620b0f202e41071800c00c1d0720010414003501103003000300742c05c240d01d00445003001c4211a040e50300c0d4902901e0303007035887d00040c0c1295101c41e02c81544032413082c2c4000544900301c00f00d81584580030421505c80003a07008519189a0922030f00740701e4145940d000320540c0c4281001800d11080300c00d094034240b02607215402641c44140100712100d12480380903240030055030305009080c10b009002da031b6901841001010444045401c005280352030000c0b400038401e0400a110659850305002c1e440c102 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 107074388 1250 107073138 107073143
    0x110607080a0201020a03060f0503030a030e030c031b0106050303030403050708092d091035010e0304031101090509222114031b030a06030b0406020406081008030318010204050307030f 80
    0x901503020482c1c208c8828410f00300c1d403004000b94a40400507070104c0c06040c1e01c0b0b60502c1c1620050141c1303444600240054680e0780c0b41582461103022124501130300351a00e550143c2e010750002c0041c00003096012044400840e0003864060742c0750f03680703004112064162502910b00480148140c0309100c3d11201c1d038400040c0c2120304040503203564026025202861040c100b042071941981c401790018003444182e036400d00c201c8509d4995150040d90300703451412036a403600d0303080010288100442c0701307482400c500e000e180180105c0d050071301051000001400c00818a807102880102c100ca081c01c0b1051002d40c017604400b11403000c0700c107500c200c400c102c1051000c40c5481280821a82c11401528415040380080107a11000b448a03035441d580054410740c26980c5440c0d0100c08105460000c500882c0302c2c10b001680c6030710707210b001480713482c0140c410900040441c4041021920010640c1d411184050302d0002c141c000c02c44250091103142e100300e415004a00d00002802280d02400404a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 107075638 1250 107074388 107074391
    0x304050c0f03030a0c050109080304061506180303080901091b06020d0c080d05131208010f0902090307050f01030f0f0c02060f04050d0f1214071119110607080a0201020a03 75
    0x9200410041c2225084080766015030040c0900540103100b2002205024050000010b0120407903e511065910880f400c1d61515160204042c200c1079400c0020003c040ca8504940c41d00c501000004001640740f10140410420002090902e50290f1162034038550011514080b80c4048402c201c1c940c1c85886010050b0061000903071031180500044540381ea80401140e20b8801c0d10340a4000410020f81650700c1c401e250001c540c0020341d0040000700411041d1541c210075031400ca0300d4401e800c0d903608000b0324a80180070303000d4503480014205c011707500708895100c282d12244004034010310310610b100c0704150030402d04412003031850348841074810745030f03003692070691310b60981c40321b00c00f01558000c00e254080c945c0ba02d200c601c21181c00300c002c0310518080c01c9003025100c00c481034844096102c020b080c50b82c0180f200441d0058034034003602c3c4103080600801d403d200d040c03501800030800068403154150258072031036a5201c0c1203544003a40845019195040c9401c024001c1d0031648403800843d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 107076888 1250 107075638 107075653
    0x24020a030b0907031104030b0a090206070b040210110a1410060b09041404050a080717030901051e01060f0e180106020a060e03040b040303031503061b14040f03030c0312050705030405 80
    0x784d21a0203080c1c085280c50341100c1c5840c0c99955003c00c04d0380d004007503100d580c1e038840300c41006a58420042203110b0048611030100d04260040090070039a803d858014010042038000b00c3c1d10300404c04809090300540030242504042d00b0b2142803054940e10014402d11b000004101300c8150b0780545550181039500700040d46451002d1802c000080c1c1d0043d0640c0d103c900c0450024400800600042d03103e4a180080c018910450310004d400a0b90b038510541d45039020440c45504100900080103190703442003246502d4000d01900038540d840c10401000405080e503502a1100204c1140d03101541d030082c0455a03458100035115901d190044680c12b0822034041a840c5001041e103050760079084549107032502d169410b500070a00d42404404030300c41000d0000200b0b03d03070310400042c0d95402c0880d210000c030303101c001008142d41001ca0301e0501c5050005001501160008806495050070020100015820141c030000c01e00754501c1c084500b08010820855846800b45000d01c0c032500840b4081e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 107078138 1250 107076888 107076901
    0xf060302120609090a0210050d02122202010e1c0b04080901141804050612010603061b020106031106070c0918031706031528140612060424020a030b09 66
    0x242e43d4180d5880d02181e00c1056280c02603d841c404819000b00f4034104a840c0c1500d042ca00030907a0404200205064507080421890640703404500e1018124243c0300400d264807580041d01d15401001c0c164040e1441224008401c540f04c60540320441e0480d50714003803407610703260603030003503005000d00b50000e010070340b400003076880300c00640f20f90b1001e5010aa49200080080c08010700c03000f0001944413a81a8490b40060800c0c441e51004d54019803010030b0600001d10049440b03171b0030700022011a89440300420104100c1c0b9940803034400b0480b50316940d9041030514a07010140b98100c84001071904a81204d40c1d8000e41004152910a440c0c03030301a003654920461107810211000741d059040081e652021410102d101507000c003260100d0381840050042d0081694004482890b038181d42c0c44004c68028010115070303900101c1221010114400d05040c591144000381c00104250365902500442e000020707108950056074502c110b48805161100401503c3c4030151140581d03410740c0810301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 107079388 1250 107078138 107078149
    0x15051504051009060903110109030f0501050403080c0903030d02030c1b061504020703081812040305060f15150702030312071707030506010221041215060e0601080711070f0603021206 80
    0x80b00c4c060348620b01341c0d07446d5448560f43d00e24030408036810485030480210000300c22140340c098050141000181502d0315107000b8016090260100c01521001d0003041d55903a000401c039071120382800805601c903118428944c074039014070218070042403051118103400d80c80000390103200340012401013001002c21801c0c0800ca10500d130000c1d000414180015020b942006802034154840c4021586406400c2d81c10454a800c560800c4a194001400380007402035441c4840d908000d6107800308014510600025451801075074000c0c02021003c2030002c01e558050003a80c00007004205130150916018034001c2810b144226868001908100030680003440384c482e59110ba901a001080006102c4d500a9104509692000f060420410003c6040b40100320100c00c26031064800c42c0710480084410300a03507402da0000300c080c80160301080450307070f070201500390018202d080c18648a20140d1719141041090741140c134400c60390320300c0050450b900d68020010440c0d05080c001040d1500800c000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 107080638 1250 107079388 107079407
    0x120304030807120e09061c03020c030319020705040c02061303090b03011403190c05220c030509120315150c0f1b090610080711011107030e060a12150515040510 70
    0xa4128110904408041c3c1d407441c4d900e40c00c123000b801100c00c4000540c000925540c0405100d140360030080d0b00e2110195010060403002c0c0c60110780500520046407002565204010700110f404000900900181801380160078060003034420301582d2507071070340030090080c4180901070703021f8883c544107503181220900080349525800440181d00d14901001c0021520031f50681481c42c2214403d0480102c980784290300e0010f042e600e000c1803d16000b84000d0501c40c00b0310045000074401c00402c1900c0311040e008d10501c1d801102e402c01200401088042540074460f501e4019208810142424060016040085101034995401c01601c030340d041c00010300003503843c290090240100309504c14050241c45510507882e00d8280400b409908175242502c44002000c50b00100c00903144040c5076100d0200c054010301903803218a807500300200204003031f1415484620240d0b9407208001804903104501000b40740007881d1038500070890b0840c07400e940c0980304c0c0314460380040ca2081700850281c807601 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 107081888 1250 107080638 107080651
    0x3010e0a0b090c181807080c0a02060c07060603050a05061807030809090a0923120301080a1b05040603060605040b031c0c060b060406020303160815120304030807120e09 74
    0x850240e00c907050f00c4981600052500011003d1035040740b102a2514510074105031400310f1088240e0900c40340c0a04450380252821000c4403040041c3d0b00d83d0b5800150540c0c01c4140c3c150301c5075840f41e0a0410380b00600a50300003d0260141314a24400d124001070810700400e0910008088909840c0c1d001d940c903071841c803008100c5682403000040c81e1a25421095000405034001716064015944003040c03000b841c040020381400d00014807501400800c03403c0482065907104074903650400c0e2001c0c0c3c0d01c3c01e034118028140508242102811096500b8410040201600c18081d498032454a44080c256038010710b8003540c50201d420800703240001d85050200b140c000084149400b50300203c60700d8002040035070300680c44103101c080c00d4440304014001030110f98007840d02d030304007665035800c0c0c1000000f906041085580c20311601d5078040b0303101c5480d9103040700c68100b0544010400d505600a560003d4400c1001003843d00c01e0140b28400504500b80c03a070f8071800b41021010800100e080251560f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 107083138 1250 107081888 107081899
    0x1006150503060402070813090b030d17090a050f010606020f07030b0105120a0c060806030c01020d050d0c170718080a030519030b030a051b010c080d02031f090203010e0a0b 75
    0x20181490140004541000c0060300161078070446450703d00042d4450886581072581c0004100600c04d2613118903808140c04a006c0d0030040030840e4001d010240346441500110740c43c80110700040410801003006a900c5401d89030701d5200316a184d4020003451003401c0143c0150500d001d642e80002c00d205068030350056080320303140d01341424000c050011b8401c41d20180b040004145c0031030001c8600074024603941e41d8194561402006150409100582090541d44065060003401303401409039443c101c507100c4c0000d15102c5c00e030011107102c034030050310002042101040c065070341d0340131070303543c0c1c1103111250341c40e41c2c0580d038052003540c4402c150340c05000100240042c1c42d0684811509030490030341485c01158101600001a0402101c40001c0710290310507a45156a020301074103400c9040424201401150031a849550140c801c181d031800d89940d00100103420170740c407401250000d4401890669941c2e0321051403100a500031701074030b235a25034008001003004145008100000070090724 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 107084388 1250 107083138 107083169
    0xf02070906260312040803150607050a1103070e0903040905010b03090a060b0d02100306050f101205100806040308010602070e041e0c0b18040606050909070c02010e040504060e1006 79
    0x102d460704280b81800124030380c0420007010084c0035130035580390b02940c0143e020a549007800c032048581080c8440e6841d015803401c3c0701d4000881c0c2d010419181250308811040392501075a000282001c101d6084001301d00ca004061100750354000003e001910b003045d00070070680e40c070351201640501040b10111481d5010b687e1940c0018207070f412404100c600035080c001d2001d2107500207801b4a480c0e5545100099481000b040302d840c04001d581900300c1c080d02c00021070090360700001d203070340807076145545405e85036001b217600c0d5117014948000a01104050314940d0505150042c591103081c4502d07001403080010124080f81c01550303031801203274840341d4440d03c040e5050911400c10380414003551484111a40000c02a103801e008000101c2c181025850314018002000100c8010f9000b03203081007018410718020740c80790b41c0125088020783c05c0c03005000310a440100e4242e401400da072a005400c140c20301c0b003084500c4d00042c0600c5485400e94001c6e840301c212023000c070f07442442a1100c20b14901d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 107085638 1250 107084388 107084429
    0x501020d05250e030a0b0c03061306050a21050303010e040b01060e0604090914010507020a020102010614061209010e0a03050306040b030c131517060712051006030b060d0c0f02070906 80
    0x4000308040200139059039103415082e03c40c014211001c480f500c21010000080004501d0208107049101e9181c14080002906100108024824901400c0400c2e0440401c800040c0c8001d800c0ca0051136000041b2940c96844032840c0301070503015907045400e8401c444c00802c3c2240284844048000064141410701745400850790140141d100207407000c243c686c0012035400001c0c083c5520a0070150020102c2c030340580b000900b1900c25600c4159155010001d0240c556030300340840e07803d01054110040b0741d4480c00401d45c01055500e900000c50712403ca00c2c42c1c01c054215000e148205000c49041104055070710515031140c5001010540c070103113600e202c07401592650f00510410102044442c811601d44104581083c014005215180e01160800070150f0b8800070b001c0c10403402010500c140d040660200360180505e00900341410344170172a450440c0c03140815a0308009001c6010311074041d5041d40079240a000f180010018006c0910200c1c10b14114010081100e01b048001140c003400d20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 107086888 1250 107085638 107085647
    0xb0a0e0901120b060418120906110c0a0605220e1005030a050607111608011a061303030e150714060106050c100c0516060203010509011a190e030a0501020d0525 70
    0x2203104803c8412681001148000040c87e05902c19500c1d845101400c20300003400f010142210304c0c5071076022a034400e00c10b44034940e88d9022182c00d8103180e81c0302c0c1c0c411900400100130024101c2c46054a400c80003814501c007520081c001c00640310507004450300c66050540707442c80850b020b0039960203034004c220842d2203800d15490b18190003051320090044008048800d000a030f0040049030345600d80d1b841020b00d65408005402070840e125440c0c8803405100d515007020310300c40581803055400c1c4d60140c50300d40284070b42e1440098250141d6818007480c0841403031200140c1032019105400c00450114010700440d18065079000040600c0c4030410120805058a0200c1c5401c014083c800c080c1c07801c600e2210164440d1103003030b0141e00ca6040a09000007031105030b101c07240d14134a10081c00d03140204181100c144031b8002d40212543c1301d0039102990110000031280d46c05105a00014041c0201036014084030503e04405001c152500483ca0410704070a54150102c1b2010611030b075882c40c002c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 107088138 1250 107086888 107086901
    0xb061201061701090606050a0609180209060304030c03020f01060b070f05010603020402070c080105092103090f0d0f0207050f090106050c0f010212060f0409120c08040b0a0e0901120b0604 82
    0x440040341c1c00ba00c03030681c4418601c080042c07480b01da44034005241003103090f01629025000964800650383e2510f1310017001640c0034401e010100080034007040303a8103030680481e102c0c058040c10140d07590502d850000c2c00314500020a40c014080c0c40d1100d44e00d08410b0044c4000c40d140c52180500f000b40903107031540303150800d800c06c40700c0b503695800000041c0c070303140040e094403030250904c00480e62410f8201ca0030f5610044c0b8030807640d00040806203224401c007503000c2c0b000c2c10384e0120741d0b126a1496456440d1103408100a84a44140c1101c844202d074000304410151046034255a00a036070740041c840c44064162520354404100720040c0700a5203d0400350025107050300481d0580e80c0d48035000f508a81c081083c0f113480c1c2e429041081a130b82006090440084415a41001140026220040d001407070a10705001c00c10344007280c00600c0b0030748050303a01403d5942c00c0241e82d1000340c40080c0ca80805031a1280c000c030f120300000988028040707a29454a41c00c40c5a030f0380e00d95500e03000c00004090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 107089388 1250 107088138 107088169
    0x60601080106031a04180506100602060403110a050708070807090504020607020f190b03070806030f0606090c040308030c0d0b010207080c0607080c0607090819021e040212090c040f0204030b06 84
    0x158410b01341426600d0340078014041d585050b802031141003030b04205007481801410b2801d1801500d808118036540061222313405a01842d00c601d240c01c2c07203c64070342411030034203018029101e40100400d80c1c0c840410058201c8005504846000d0781d00c0701107806544080718003a43c84501071004c2e20250400c0b60120800e80e00007000300120001c107a110910342c1a02e90428112154080100800140c000d134110b904040f08400410021003c41601981c1e420000c0905015600d21008120141c6504056501859005080d0b903180d20700345000701481d40000d4540240c90381813a10003100d5500111b00601030380e4004002d400440550800d10003154880001110b4004040100a208000030300045004074019602c03200300740d140c880c5440c50030303070000c0c03150b540c0c0308102c2c00321401070b580e0300e6515080c00c1c042c9103051444d60030340002900078068161660b41c0c803a055010441418008260124640d008540400944080d244820f0481c051800014200c0d000800403510340d01e400303400c1d40345558 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 107090638 1250 107089388 107089421
    0x207030215011202090105060304150b0102030c010e01050411060301030b150a0f030b07020601051c0326070906020607031a1201060902040801140603030708090907050408010504111206060108010603 87
    0x2803031540142556400760f02c40741031411055220700c11803421003c5180104402c8466908500349a01c511826601c0680e401c1c0b066a40c1f44007100c03499000740141c0b042d04c2d000360001c114000c3c030044490302034102110111600d5460280c98805842c0c0242500d058035000b964142050741c44060400c480401e030907103991f0002070920009010320a480c00320000d1445640c0203211400c1c013060180c5889010b805c074922841d0105032022005040000e00700c045e5405281016400c8505040328903034420000b540318006541d24200200203802070510b0046400a500320f035019500c80c2c1c5d080781100c010081c004107000d0a05107044507803405c2c0c80f4540f01254407100001d4050303500c5061404982c841e5025114a944500c01440a595200c808aa00510980155141c0301e29a511004d140c803072051030b07912501207240451140d9101d681a6005000003a00801490a150a00c450050700300a08144660b05e644000160364002117500ba0103114183c54045241c1d00345941500504501c2a2070107004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 107091888 1250 107090638 107090653
    0x7030516020a0906030308070c0206190e150a0807080601020303060d051504050607030b0f0609010513090509150604020c06070503060d0506130203120c03040b09131a030c101202070302 81
    0x1070360b90420550080110340380025182d440c514003c0e00142d8000c1c441400d04c0f40c2c2c0000301c000341c3c8a035000c4503400030080104490b00d020b5000156954031b09468815002140c1116101d14010408000c1a241c900340e12051129900e584040f158a079044402c54010303001400814000c0c01d050310b010040d03912071000e6031085501c04d0b00c25000a07034210b40031740329139001c0d80030f00c0a195014400c4070b0080c1c60135140b1405105d41e140200da520b00c0f4100f1b0b2281000300c0020304560b00a4540303824006040705040600850800348440c03961602c01d600d4200d1030301e84c007002065403494a403003150309120141000d0041079403007210503102a00000e000c3e60700102680d40c03940004209005c0c840c822900c40e070507030402c0c200c14010b01d407803c240081408000441040790156080f40041600d04480691740c4455950150401003544003540d9001021700034240300b41100061904942d0907060242541220800e640440800c01d10100103006003010401c43d0386c4c1c086841d0003030740041c0000780c0a4011544007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 107093138 1250 107091888 107091893
    0x1a04141302040308180109080703020303030f0a020f0c0307150504020906040c030e0a0b0916081207030e10020a030806030c130207020d020a0314070608280603060c050912030f07030516 81
    0x169005c00010303490654541d00c0c02c0403d41c2c0115500004e00b12a03001000190b0659000c241e0360310014114490400d0940c0c0003e0481400f0f8044420004921070815200e0490202e0503130360307030085d0340d040320300000340c09111080c0030044c4111449990014030320030440e00da40d002e01000300b06244420040644400800c1540d5004100404101b845020101c400380362040301c00341403d1240c1c500041d240c900c114208921880000c140d00240d5032498071a075102c1daa80b406a83c2c1c0540314083c41e4104480392b4510010741e4002c130341551401d0180c1c0714a0045d5403032404042e155241203800b03940c0001d2001c0b0301c000705501c0740c1c0034002e00d600c040e080500c5a1603540014a50300100e90048500c0469000517230304c0490b05000e00401015542401800340c107100140010030f85041c42041807a600b100c06468148450b904034100171070308a081040b055100840041190340300c24610350164140781e00c031102032030002040f81d600202c49071011341485c0301542c00711105c2d4090b250075821009000e140101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 107094388 1250 107093138 107093153
    0x4030602070f1b06110102030606092107060305010e2514090301061712040e0115051e0c0c1f200f0a03030c0e010c022b06061a041413020403 62
    0xa421441c56040d1070f03600e0000c0c001d255456284001c0710907401030042c0240c5071141030655200100c125607100c16508100802d102008000c1082c544c540b080c8000015000e8160f03102c6810f8902d03070070400e00183d45610f041c6008038010a41704041e81e0030800040c0210b88a1844582803180030074200e49000b01c0c0074000307801d403203244d0007150203440b0010702810420b00c108030154100b00c51403401401c10b86843c1c1c11645a150500c04e0100600010b201c41c01024484e80480386d100030300300c01180040c00700c1d0040075229000f99980101d140b1941c20720921914040300444981c00350581210f811002c002001c0341d01c0e0621000100c2095071820550312a2501400308100c40380f4507000801100c4490708004098a801e0525141440740050366486641d9100e090229219019207420b40645c4412a40668546068584002c1100f800307400208101c1150440303402ca41840240440c1c441000c1003460341441180f003268440e00d6103500017134040c1011210720000c40c074803490043c1420381c0d07a1103101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 107095638 1250 107094388 107094413
    0x1090f1805060f0709080606010f0e0d0c050109050402040807170703080a030f0f0911101b0b06120c1e04061511100507020a06020304020f19090e0303070504030602070f 74
    0x84140e00800d00f00407a6110140900741e002c0344500d8116000c92528054544620000c3c2105041060b0040c8244c1c47c1800395125500508001c0d05951a00305182070144103802203005980c00501c0480c40040d80d460030b03009030b4050f00c0c408006001224984140c5031580d420740b2940034854090308000002060020018045010b01c80e200880c403010801c501c01d080300e0a08155528861134007030030001040d02040ca1900344c4000340c8081140b08110300c0d0946082a03210303540001000807180c0d401c100320920010b01e002d0701003034031b00407003242d00c0b21081901c482c0031040c25134000005401c400b0b801c02e411182c1d4854400c000c0e01c00198141c03500c8014420708800140e24000c0b60628100108203401040081c03041160780908004038103214074025190482030f4405040b298012005c1030540d515603c6500e80d00d400208501d800f5010300c0514400d01d0000d2060344100d80c64044181c80c0134034040700312841403455649141c0341c6811540d50344000c0d00010b50594500c81280c04942c00680002842c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 107096888 1250 107095638 107095643
    0xd020f06031e01060c030e01030c11070f0819050c011b0602030c070515010806191d010518060f060907030f0603080d060501020118110607050307030305070f0c0b01090f18 75
    0x581c6281402d440010304400107920076000c00c102a21104042607010907800c45520003480c0104914803415000c070342240e0002c0c0354041e2802102c0c0d00080340c4c07151200100c102c0d19203800341e0b05120f0042d00b81c50319851056001400d2a009484940c1c45988110036400900b0007540140f56001d945403180022a00122020140c1c0030000a1301000c1c03280c20060791031042c83c0401c580d441036041101051b02c4040292402c0c00031103e90f00050760103901e0740c002455090b00c4650401600e1000c60035540600301c2614500010995404180c021200120320a84203d00d01c0c41022003070741b5000240039004500402040405903030b5403103031048030700d18040c1800075800740f4440c07a11850000148002c5130300d554400d90640e031401048600c2161140004100e494202103e00044260500490850310a0070002050b60000141c500101505030f440f0500a0045940700f158941600c0c90603640040c4a400c09040701c01c0d0303403004100200c40d41e00610b40c165034130100464000251a450406060b0b1442e08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 107098138 1250 107096888 107096911
    0xb12060906010e16020d0311040b030a0204300201050904061e0504060f0f050409030201140103060f0b04020f0706090203070b0a08010305060c03040309060309020a0302090112030201110a020c0d020f0603 89
    0x4100718061083c3e02c0b9000308624141001c40b05a806000c1d6541d00f4401450302030540702c80320080c1181d0714000b664018520310f50001c0d62403030b081e14160000e504c28007034214007101c5c60b80710902001d065170b5400401403c94084894400c01c5400643e100e03004480b08590103529000045500041d4140d001e10079008021500c8003030b820102000b080d00c40ca9044405104891201000b2845410b030028007107981c143c0340044c0a10450504034054014500b420b045511460000000c00143d9404589420b1350b08500704224001e480400003039104024513210400018020b41020030001e9001004140c030003030440303501e29542d001e844115000f892045011440400042061007401d0295650007540150401d1035440c0a907005070002900307021345000c25568081d0201151565114140510f0300100052603941c1e4840c0600b020040b1903a0440042d42002025803521280200381c17011a600c0760050146030a1182c14440310100782942640c0c4036440707091403045a16244015405858003c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 107099388 1250 107098138 107098141
    0x70b2d04170d180b1c140907060e061c090606260a0302070b0f09031e010b010306060e0d02040204031704030212070e04080313060c0509040b04021204060b12060906 72
    0x32039820020809054810f2010704900110511001a40d1100b40d0342c1d103001c420346403600c03050307407407011005c00c540c468145240880d641c42ca1440c04015500c280480000c40c1d20240d05c07008100ca16a1085e040203401c50001d029912000700c2d1001090440540304800041400464513200181c41880d071091130754014440c0318505101800040c41c0e0403035140f034001c100c004000c7d507000b551841c0e41c1c490515400000705d52030903940d244404454508070020111140756078194080c5154080c19900c00307278a907190070710144240d4000d004920484d078168884480b8001004144600c0041d0144200d030303c15420080440040d1442c0100307035403407594200e101d1b12a0b00310310600500c3da0100e18041e00d01d80c05401c0402407042d000d40302e941d10640c040007440e182c2e180c2c901c0e0042c144003425001000075080011201c40b20794400d0142c91203170000c40381070019903020014007040380310318803031000c110440200090200e451a041804e80c3c41c0b0140240074801840710710a4103065041d107412119800400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 107100638 1250 107099388 107099429
    0x40504111c0b1212030a05130b01150305090d02060403030e0307150213050307030b070c020103230406050c1611010c08070b01060323150307050607140f070b2d04 71
    0x24a2011a58104000d1140c1c60305011120304170f01004002c20b402e40e03115400100920725000c0c0d6906169441601c02c0780550315032030b506840380241d48460000a1403c800070b1050800044e040c3c0c50030302d940d006007000d40c07210b803001c80242505070410399062100b08000710008501200b09050f6054108005888072011640400c1804840d44042e200340d1100c441030020415580c8420303080789080c00c0200041c82144010f9000e4024a032801c1c4201c400106c0d403600c00013586100912070b0b80b00b494104000d5030340040c20100f50050034907807003005400001500002e441681d4003c0c4a071014144030701883e240341d944460079881208222440400d03880100659605801744501440310380b41701c00044524201320382c400384e00040200092204081c508241a207042c01803d001d400046c00890703135609181404828020039100c1104944030780c1107103140d00700c404180501556014a5558a40b086184c011006864400061002441d26000c09440714101c0d1006100a02429a6210b11180d620 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 107101888 1250 107100638 107100649
    0x5040b1c0f080f130f0807050a090e010902120a020306070201150e09010b0406060507110303090105070b0601030f0f091e0506040b09190c1d01210f120e0901090204030305040504111c0b 81
    0x2c2e4003846c0103a00c10142400340359241d42c50003082d00c00384800019400d05800700140545001000690071002094921480b400042802d5812034001e0f41290303060b40303651030704034200e40c00ca91952440b40f0b103482c000c2c0801c1d00c1c5210b07841d800803161000400c856104a0000c0c08a803002d51080c0045840014480d0401c44210075201e11858114061030802401c480003a200784030b1190000c10601c11600016100d0780a94041401d10903805000c000117401c4900240080c46a5001690a824031480d000a05004030840608180e80100501111344440c0d854104003e00a41400c0b014004d6a6100c009580c2c41c0340f0340c51404d8004c02c40480600c1c81c040d000031550141106841c0c4060000005010001c0410500140e003903001c05000d020703240c40d04000c070251600071402820900344500d101c80f12640080302c181469011070f2102e0b090b9a0f1145c5441c00c920441c44020702186040c0001c0015243c254070800d04600703c4a909850070f2100403031200309030700c030140303114400741d481e001d0101d5400d11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 107103138 1250 107101888 107101919
    0x12c010206010e071b0f0501051008070509010305120304050708030a02100615020c0f03010204030c0b07110d030f0318020613210803060409080c0d050405040b1c0f080f13 75
    0x1206038143d01824200e0300144405040c900b1440790000045c00c4008104500e0250840150403600170005818000720846507100301d8031072841a0300c0398050100d49485c00e101c2190480f035000c0010182e13010350301100b941c07640005100352490302a8100000e074044d001c0c0000e1442c400b496015180c1240c1003540c0d02c0c07c9030311070b41100d4445844021603e45290700080d680251200c116030001c0d0b1000c010002901901c05d5800040c035008402d180025104c0031180601050780c4103034440c080454494050140702002c2c00d0700540040d40b0000b0140007107009a0140ca00303c01100c0b04100010041d8000c5203550340040300954481d0750120302040106610415841152130601d1000d41402a03519810000c1c080585014407450395000c0800030845c20904444521454000743c5900b800387c000042c0440d04180304443c0507904190034250340e40b41031034245004582150310042d41c81515100c84a40040d440d0701181c01040401a81c400500c141007e440e0305071564095818460925142c0420381c681c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 107104388 1250 107103138 107103149
    0x71803030c06050c16030504050907030c08040f06060302040c05030f0c1c020d18030c050c19060f0309020303031014090708060616081206210309060702012c01020601 73
    0x100101480065404084240741e60340180001c151600d0f0f4502d0400f1611440c2c2c404410443d01400c000105500100075004490f4100c8841e40d2035030301c50700e040d001c0c0c500005098002480000008000510035003000d18080e00039000014000c5d2240c2c0854101c41441c2c03984e0340490004000c02c000c2e02021279943d41d01c03525003400305060080c183c088980400d00e00503a81c007115000706041c2e60001e0b5691205a40c240d0b85a0b00d4200c00101c2c0c00c02070700e01000c80f081940c1340e001c0c0780c41c213010300c2c140f03c428940da03041d102c41e031160304074980300d0300b11b03840104a41580c0815442d24031440140c0d404001850003540c00303005c00d000b0640742100c201c04d00c0c0c00180d425801581c190040001554010040c10342c400425150a651401040d034100700d4207003c1c5c46d005058107001300d2014030306c0c821148182e100360001e0300c052042d408900011001c1c06114000040564010813024106040420207440400d01c18100885246681d482c81c1e0b0130228401c00c404500100786402078a19030703040040600401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 107105638 1250 107104388 107104427
    0x5030307080d1d06060607050c03101d0303060a06050c0a1a0907120c0501030e0a050106061701080309031f0f0f020703032a05070f1202010b03010609060b040512070503030a0807 78
    0x2d5200443ca500d07120003d11582c85864041451024090244406d4001d02c00040c150380c440c9405000b4031000704800541034218a445940804c13002a00004813402004024000c00b680751800c50304451640c000d91040c1c4040c0500080320000a44007011000e203481100c0200c1d80a240481181c0d01d0300c4e40350703030041050100c04840340300880e020262440c107484080c6000314244126130141c51904140450043c005e44c81c1c0000019000c2d80441481910841800c1106030b699031143d1380ad64a009402407a40d2540110078030080420100280d080d004c0c0300f910380881d0b2581c2c0c0702801000c585c0385280c1c440006800003848000c16034075100d080e641c4440c600800d0301042a402049900c02e41034114003050050000d54036090101a00280c11300903030040d1140740d07000c10700390003e010b0200800c81c1c40c02903003004004205074009009580aa5400f040e0701d50800d4505400c00801c1e800b5820f41c641140242403000c5901d44060004100350f44840e00c45a8240c07c01210090030703203607144c1c800500403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 107106888 1250 107105638 107105681
    0x50405100e0d0c020d03031e050a0c08010305060a1d0a0303090204060f210317040f0203101109040b06090d1b050d0c0b09011707120e060105220605030307080d 70
    0x750341000000701400c1e01505e102d14040b03101e14081d03000f0020700350b180d820050040c05011075903000c0d8005a120721040d04c2c042c04070380a943d00a03100c8140a01000706a5081880044c105c80c51541c840242d01142450782140c6003a00840141403d060400941c002502e8010b42c0041d03003090301405008042c0d05a818400d00d290511502150724443c4100c2050320340707408440103051003074808083c5003041c40e06250a03400c2c24a0080303002e60381000d0032030003800f0380d00d0348681030718a91003030b00140c0c480d80006078035200030841004003c1600da064a0ba02a0b400c2c02400190b441e55650700045600c103541200c805000d8003800d004210309039001901c2880385a10440010714160100c008440c0b00492039600c0720038050058543e05680301d651500c01c0402c00c2000341ca13680c010500e0800229425080114030900840c0540f5800d090249540246004100502c40183c0700c207040c1058001e4140041d015440303000107815944640802e440c41c900c00300711100b031030046210b9407104440b01100c01c03940 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 107108138 1250 107106888 107106913
    0x30705070f0503070218090d030903090504180c030501050f0c04050a0b090f04140114030c03070b09130204060804120f090311120f03030901051303020705060319050405100e 76
    0x16803082810080410710000d49075400c00c0300c2042691440703540140302c06138011810240b4100800c1c12903002d0064400c01e501080000d00a2055107191901551000e440c00d0406003804003400001c0e0100c81d2490b48510820302040b408200381d00514820720011031917041400d0304001c0b0000103051b840c100c07501000104402d5449226800c200c0304131070b40132500c0310000000100000d11521030301707030000c0c00d000c82420300e808101201d5068503400c1c1d18450213861801c040c10303903800c50f10120a41540c005c5205018032020000680803d1000804460305c000c508143d0000343c0e00140e010102041040f001d21080002a03020a5442170052415054540000d1401014115240320140c82c00b10700b40314000c12622414601809801c0e4141103078021802051690b54036031040b100d40070175501c3d1001241c0d040c5140c55041c946c16030550300601c845800c004c10450030390300c00760003400a502c1841c2001d07081180c90281610560007240a805095000b048001c10340758200c000c0200764210140e81d918 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 107109388 1250 107108138 107108147
    0x20a120b0c21090d080c031e07030f020d0504050601090212060402070206130303020106030c05061c050a0e0a0309031104020306150c0a17030f070e060708090f03070e09190b04030f030b0a08070e09030307 89
    0x10003030703441c8c545248140c0380c11308241c0041c5580c0c03c3d43c44d0181c2c00040d00301c0a0804a03001640102c0c42841290603586e650822201240110034003800c01c03004100c0804c4d130524258001d803024900003000705203072003038000a4120281c02c0b43d01c00c0b400b50751201c504006100200460b40000c06065400d1441d00100e40c0c0f007500c0252060101c1c0e240c40e5074580c04106940c0341540300304034806445c0212410708000c0e040180c83d114403440211a0000c50782802101c506003030003580d0068102a09144400304985940c070388540001440020710b109102c000c1002c54240c54040d0a01c08100c10000d82d01c0c05c04010300f0307100600003490b030014061890400741c010b465003800c8400e260340103a85191a000c022001440d03002200814030f0b0b26100740c0034045803807013810312141e0140111000302d9240544030710207148090445e0750701030603054402000401203401142c07011140002c1e40307000074804101000280c10302d241504015040e03405040b0500a095241c1501c503003062500c4000c50035854030381030043c07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 107110638 1250 107109388 107109421
    0xe0c030601080f100b0f0c0601080d0801030803190606030b12010506090613150603020306030d0c03050a14091809010e0c0303030a0207050712050307020a120b0c21090d080c03 77
    0x107a4594803e00080c40980c400922040034000100c0c4841d5501001d40700302103150442c00d8a0f0768580128000003c3c4120006a50b8007050101d807130344550707a86142ca4002c19030b04020300b811000c091603c00c0c540c9001007481500e000e80402d4500052561400043c4100d42c48810311425040e0b140006226480d03964500165100508840c8411010903560040002c2e00d0b681040b1380071024188000300d01507425030043d51040505034100d40e094400e03a0412039002c0382c41d150190100d20100641c0f804284a101c40107105010300948070b20700003181c80402c0020200201c6070903846d10050900400d07100c207010b1001144480d80c01440700c21000b5000070388a02c4054640c581803075000800d001000001c1c80110002c08800c0c69006103102541081610303540711110803071041901c000041342100e8541b00d802010344d008015250541d8404100a660b80d012883c2c90300c1800b00003612015020700c001f9420300c203180f004060004074030360315405440424041c1421003000710034020001425121950007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 107111888 1250 107110638 107110651
    0x512070c051c050c012f04031203020304081c060303030e030c1207050a0b1305010c0302042115020a0e0a0909020102030304030e0406030f0b041202120f03150a0e010e0c03060108 78
    0xd00d292011000d6500b8403c1c500041c10340e508103902441d40104030300000084a0042c4844000300706c1d4040108007610440c0001050844070880303601c1c40d54442d50146a0091040540c203152200c2d050b01c03000925440300c83c014403941c403040c051041650500840c270344880344030010360800c4004051141c8500044415810700c2c100802d01100f030003400c0000d07888050f041108030003203040142e22904a6100d0040a461540c02d00b445400c0061003442154120f801c0480b0301a051041c1c15480d14111241031402d50b07090980b0680240145054401070041d188141c031094803407101c000c240300103001107a10a420442c90040c140c00940d0300802105d40c01545071404030b200085100004004001c242c00140c140050807001c0c0040040481015008a01488191140840d2020101e030341e041703204001e5040c400c0500248070040e03020f0000e540c11900034140c080140305254007103001e4100642c40700307d20508140040041d150003000f5150082c0303419600601e107281400001e4070050f00a441c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 107113138 1250 107111888 107111923
    0x3040503070306110f03010b1801090608060906031c05040504061202030303010b03040602161101030b0307051c0809102111070f03050921010612050a11030304150512070c05 76
    0x1100d081c1420421990403400c5180d1682d01d0b541c454a2300d141d581c002481321105410015020510f0798024041c44044400302c0d0740d5801d6035515a0103210711004090003d40d0113226010001e00841c0c0e940c0c160705040c90483c0c2c0c2d40c68035103291030200015604a580165000d0510600300409030301c0100c03c0301d06650b80b005645540303481d68540f4200901c29034100c0c100c20401400c2c888d042104806901007546803d1b03805000e00e8803c84105a194981031107496170002c40200ba0079800350240c00003244c002e00813060541440001000700c0c07003a000c0b6250690003d0380c0300e0036490170b46040004250924419520070082c107211655080514400c0f4075010b002030112007407260415201e13000325816410080c002500d0006a4040361040394001006003c45500308500800d80403554207507184c0458000004103500c0f1680d444a42c01d06502c00354141c0c15000400c00400c06400b08400e00300c0c4000c455548540c0c0c0c0c44414402154100040c02683c10062404c000b00007140c1c0010704100c120a8105d503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 107114388 1250 107113138 107113151
    0xc150203070909020406051201170c040b01091208030609071b03180801090b04021003090b0402060702040e07120302160503030d1523030601060e01080f04050c060c0102090f010203040503070306 85
    0x1810b40e01c41c511507105030041800001c001c40d8465104018120070403420a41007500e9881b40340e95086004a4540d18007180c0c00f010110070249803542042d001d800041c100a200103848040b1850350002000307080e40d4540d000802c2c05440d080900f946a848885071601c4041d50440e8042030481d503185035405810002200d1016452148400c01c1100400004000300003812051400f00426030044506920921a65102c500c3c5180640107490369554001c0503803800e41d40f550301300b10b440d42100700700783d03001684c503030311030387d0303404080003050f01819203c1c0c8446665a1a481c00030300d0211000c03410080204a00b40803c0161000802d5640b842010400800d03a221304510203c100b882c039034400c0004184441220104400c08145507001c60b2040d010b40742e880e81c9500058518000d030f02c1c455400180500c6c001604144810000350b00a40300343e00360b4103590024000203816410900a110b0700380d50000e900c42e014130741180c5696181d43e081c0040d50500f890074000903124445488040c008a031100b9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 107115638 1250 107114388 107114401
    0x15040303090e060316260303070909020705010209120609010b040b09010312030f0f0902040510060801030f151103010806070801030302061503030d091b0906121e050723010c150203 79
    0x8201708070981c0e90084a000e041c0d40c1c030f9600221006820000c040302203c1c0f115100d6070700300030049a100e141c254031503220785481d129820000b94484032050340c480d50709110b0003001b5680c010000003400c5246004121034100b04200c10708480c14144468400c0d80760617101003031f94550b01501811031350450005007544100c1c81c81540607181a6070020040c1c4d140071022112400720f03900081015000341c80400030759803500c15100450405008403c00300e60110f0040000034800c0e0410b620311485030f40040841954042884282c0d9a031b001e0740d40c0603200100c014401c01108026691f80840d542c50161103a52441e10302945800c8042e1450401001c2c24071074030140d403000c0048502a1000d1002046101d1183c00c001141040708030000f02001048000018a4840780c010358069410484002400100c581c0d901504003441c0100c50a0010300b0003107030701c0850401e1008500404e141d480203140c1030880100d0a00d07070045e140310315050200c4100e184c03011404500c0c000c90b54807081d441c010303526100c1e0b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 107116888 1250 107115638 107115643
    0x60607020406080d0f02060613020703090e010920030432120c060106020f0d0507020418050a060506011b14030f2206030c020c0108060f030a03030b15040303090e0603 73
    0x840040e40160904100103255480000c043c408004d165a40c045030311480603080b80c9074402620180c0d4489418110040030464503401480418881d048c4610280d03618012308402e100c00364400054036955a0100d0b2940300c0000d031950b417049607418800d1542c60030380d4444540c1c01412244420000780c01c80c20030303480c100e0341c11040e1281c0119000ca0300e07075030300308031080c2c0c140d500c005d08484060103418000035050b030000420001821140b009028071403000d42081799113800c5100c2c180e0340140c862420100c02d250441c048209a80154082c005500042c14040305507400a061241004a8112242898030f0388003c282c10440e4010054120043c0b010807052950040d50300e44c00702c201c0000f98200a140d1000e00c11040149040c8800e003580781d45401c16000c42e0070700c007801c00250300030301d10380521584200155984900010300da22040c0c004080428500401c940c005c402293303884140c214146403c0d44402007825406130414a01410f5640062511032184a0710f1061289200812040d5406 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 107118138 1250 107116888 107116897
    0x2070504060e0a0b061308010506030c0f06041206020409050910141e040c0504150906080a0803010b0901031b020109021302030c07080a03230105010e1f110a0b0405031b1c080606 78
    0x1b00d04042d9031151161080390007000c0c190b0f104c91003403040700480302107406c14141c3d00303802000050195040c80c0c0b03410303410400c0c00d42c50003007103a55541c20000421103c029208050287d0a940002c044450070342e565002141d06003c0d20b1444d0180c0501041000c0591211854100440728152409900e4502e81100c4811245c2c10895110f410410201c4100c1186042d02c011109150300034040703954ac44a403503484260306103018141c94820801802170045007001490090010f15000a1203010000840c419101c0018110300603519aa21041586004640e000c0a1f03903611808520318213008950101d01c0c4602031000b48446400700e140c1c0c2c0014004c0d404018000700b01000e12038038040301c801154441c04240200b9020a440c0d0340d5010341d504100e04c3c00f01c0103521403043e003181e0121609064a030001d843c840c4186901c80d01211600048a0302e6505005601c650300440e158028032103030b110b2205d000b0741da1041c954004900d03042e031100c0c2c1c9415200b90403854101401d0035220400031030020f204 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 107119388 1250 107118138 107118157
    0x2030703030c12110601050459030f03041112010219050316030504031403130303061d1512010f020c240106080705090d0b0403030b0607020a0308130e0f0702070504060e0a0b06 77
    0x12400c01d50524a400c1000c5000c50455011010803809c2018103400007458403000303d0803480e03009100200c5044038003001541c00500070320401030f0058100001510041928032850340c165008540400b041d03680040d00c2c8400d070fa0904150f0f0541c50403058062011410311401001c054940000c82c06060054842c00862582001a03564034038121480800804e402101100000c0c0351400000302d4403a0300c007070f20310907141c48680141903850f40e0440090340d6070480e040c280d116503c6d45441a48000074400c221a514041d080541c440c4001c0d40221304002003950401c41e14000b0542c00312151015603a0746054682d9420700c281c1d1074079100000c594901030b40c1c4003a03030000f011000060610482c86071441c4103910a950a0003103003010f0044c456103000d00b100c02500320580f0751050001841d00f4000e046c000c0c41001d4845085a03694409040342c0d981070310201640848a07003480031042d81072003440e005d4501580c0608c891444c0125961110000074256002c041d45c1d0340c9405410f40d520000c5408103103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 107120638 1250 107119388 107119451
    0xf06060e0312130e2a03010e0f2e031115271302070512250809091f09020418150f08011409070e0408030406060302030703030c121106010504 62
    0x20f0080006802e140c5440e5802c9000300d6001c5c05c28085000c4041168142e403040e081c4500c140e21103840d080b8030042c000d40840c0f4031a6000c1c980308421351b14980741d0703007883d010414401a0f451540c14408156801200d08a0050005150ad200103107405000ca511140c0446403e0501c2c08040c40e050f0743c850795001c4000d0380581101e0850703d110581e500507008140c0103109035451900200041e4005115244c0240481e850f4503400500c1e400c2007003101e420160250b0b0041d442c022680c4002604142c080329400d070303009588140030400c1040710300c606001c1d01140100b145041c0c00d00014140561034641c84c55a030310740725865080c50700c494508020040c61b0001c20404143c2d01c1c0c000d56030107080b907480f5424032000c0c1100050303440440003035200200c6008040d050710036143c58072010300da941f0040080c5d54050300c0f880c002005803801c03c01d04000754080e82e00d1041d646080d187c00c44a20380040e407104c00f0084501c031101220700c004104103044620031900051030f020b8050801300d00030203000800e020b14 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 107121888 1250 107120638 107120641
    0x8070303020714070602070501030b04020409230a09020303040e130203010c0509040c1d100c0807060b1002010504111c0c14040b060301030809040b1201090302010f06060e0312130e 79
    0x5425070042c000700c42c480d51800c001e52030b0500140d9030300d1207180325100050340900c1e01002154000d41c480410040042c6c40035103459142d980c0c07042170391410301c5200603411000310018a101d0b02c191340142c028681080c01c1c8183d0000d500029a01c1c0224014402117003019000300b510340d8400c50040e119594003400a00c2054190342018240d9007158002c1d5020340d061155010003144039034001903483c118a0701000c40d000a40041c443c01007508003103601440394128a000218000c41d0181100c1442074101040340b10200e070030312010100304000682035a04180a005c0068043c021000c2131340f105581441941034001100d170740c0c1a900d00800760071202c544602041d02981c0c84002d0603401c81c1950305110220b01c4406004aa1100744806800c1c400c061120b01e5841c034080d0040880c0701801800805483e032051019402c5842403002200540c0d50351403d00f0305041d4a02078807000700452700b00804004040c502090721150049003581460400003508031481e542440418083c0ca840113010845 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 107123138 1250 107121888 107121893
    0x60c0c0b160e06090102060414120f09100503040503190210020a180501020a030801090203060d080a080f2514040305150717130204020c0c100e090f07021906090807 72
    0x211600180c0030000800407038404000d410140f08950403400e040c0c0c010802c80d6103a03196000c09800440d4120424094044440e01080151020b0041403045202c500d0750307503814008002c00542800b078442c042c031200b0300800c40410804002c1e188100c800f05002507601d0030100e8100e007415840426580420f10200c0c181c0300b090380c0020640305059441248085058070740c80161794070364810000800107018140103100103480c3d40c01454100c40c1c0a800004124141e980343e0f00e081e040303000d81c000010362a1040001001c00050160303007006441e000f40e0b03d40403150612220554132030180300140a810082c14100386802000c58000f55005026a404450544040c4400440591306040011b810203a500c040b0142480c110340200031030722043c1c020300460b9083c04040d41111503680b416004200340b641d140d444020380d4003403000d02035891100305442d0500f0400c410502500c140300261440c1c00b006402030f00041d50100420800030030003215001d5140410180c03e1400d001895010041581da04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 107124388 1250 107123138 107123161
    0xb06040f050117040209130302030d0903050a02100c1e0504090e0304150905010c140a06060905090d02010b06120c04090207050109110d020a0312020c060c0c030d050f0403060c0c0b 79
    0x281c5209a07210301440b206074090f40d480c01c000f510301952104517800072840b85c0707800758940600648640107032824950003242142c100c0e903000c0c00c1600840c1e40081c60040181d0706009078100340f001e484003004034a01800d0010210381010440d20030001c2c00301d01080c0381e18001d0301500c00404800d4002e10a01c858210a15100c1c1c0181c802c50480030b20492119406502420307640042c0c5806a460005c440c08079110b651104040c82c906ca00d050145480c414003042140c0200f1007e00b04005000c5482c1c102881c2c0d4038941150345000100310391402409140aa803020100c07006685144c20074080f54403051070f22502d42c42503620007100148005002c104021064015045240c0a4405810980e0381c080501c014850319401c0203621002c0001d0a10004110501103881e10300b052040740c0f2400d9202d400b140301e9500c5072084c640366030300ca42480d98442c90104680320310100c4e6450800e00342041c2c6020074010303009900000300400c0d1202c41c1d24440f82c0c8500305c5c50aa1070f1b004107d07007942d820705006152 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 107125638 1250 107124388 107124419
    0x810030c080c01020c0109031203020304020f0d03020105040b060a0308030c030a14010e250507020409110a140306070f1d1f05120c0301060203090d061b02100506042901030b0604 78
    0xd01501900700171100d2980143c3c62101100d4001000d640030302c012682c102c0081d40002c0040760301c06c3c02c0c1d140c1450300f5254a0418080a0b02c00d0b00001400d04081c100300c1c0100400410042c401c030581c550510000b4a1101666000304111145640701e8480c1e00090000c1c1400040959802002074000540603e0b01c070661401619404144840d0351860000202e42d941003003a220f02141d420884032005007416403150408134010117400020100c808000b6444a18035844488042c0c00c200e0182030a15050202c250410098101081c10740502c01e00984130420340e211001441d01054038912160f25a1401c040a206042e00414045901000c0c06842500800d00301c101941070040040c25034603c10045a0585115400640c200740c020b10420801c00c4024104413003540d280c0040484801c005100c606010711680c0103043c0e0040400c250408a881c010580c0f031065050503101214400c5585125401d500f030400041d441e40300640c0141c02034411b02c401a6040300b00060002000b0b6840c2080c40d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 107126888 1250 107125638 107125663
    0x1030e070b031f05010201060501090e10031506060212030402030604080703050c03120a18020102031e090306090c01170103020d060e01180c05010212030402130213120f020111030703020d0810030c08 87
    0x42d00fa098079240120300329500d84c0034090200f15200c3c4144000185040da00b139000c1c00416841706004e450f55981c40c850b90200130903603810358484030140552601404a0b8070407006442540e8110300c0c10380c0020750f443c0805440a0886030340068610149445141102c00004020044030380d502d03c0c1d89001c1050745c0301140e42c10303013240c0341054400c400071503003403000c11040e0141d00560400540d40919541c0e4401d50400481c107810030001c0f0040c1d500c1c20301070309200d2645900034040c0c4505000002d480b01110545680000c00840014001139a03100700c0340a8040d04100009412002070100d10f0051a1114100701c0480340e10100004001d4154001400d44000303a0a82c0c14040c44a02c0c0b242540c001640c1c003e40c080c1c080146400d10071a130f0b40c058890002031100c5c5100c07450740e4400282c1c162460b29400e45541d20103c5a01c010755030041003440701003241100462805015450003507d6000300d10000c0f0810401c03201013141500c104055502542e00302140113300b5940d203008640c2d0340f21100c1030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 107128138 1250 107126888 107126941
    0xe0d0803010e0f0702061506030703060e040c030215032e090e0d02010f0c140903190b040b010605070503031906080d08040606080705180604061a03101403070501030e070b03 76
    0x250014801b041c102c0c003035540b1414050482107004208410703500000c1602d001c165503000c00181041d001c4036581d00980c01b40100320760450440c01400080c0e606c2840d010080b1794100140304801c02c085ca540a07200b080468144115032400301d0042035091a42c2c001c1103c40d05002403034000d001c1c0816510744480705c0d40c00800842c10302d404888181c0e5000c0804c1030100d2160b500d0303a000300b9140c0300105514080202910090065070303603141100c42800801352014900350080000300000181c941780941143d0a20604041107079540d660390303100040c102075410806945100e00142150000800340142d2001c0c0d41c03a03029000c600806000f001c640030340e503040c2080400101841c010031000142e038409040e25a050324808001543c1c450302070140c0390400d55582d070000d0100d56130b0a00c140050f280008960b076074141803010500510040d00302d044204500801110a0f13039000404404541c0d003800c0108520040c1c851580c2018401d9204116400700042005812140e058090400344c07500f00d82c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 107129388 1250 107128138 107128141
    0x2030901050f010609060c020a0806010b0705160f05041e050a0902040b0d020609010f02100f0b0906010e0609100915020a05071d150303070213020309101b0e0d0803010e0f 75
    0x507284000400780710300c0703001c14011002030001c6c602c40d510140541d4006070074005040da5562400346459001d1b03111001040d0033140080c10000c1c248040c2c141c840200700712082c102e00382600b00700b00071000e00c24213110300d036030354074001001411140c04008031501040400491401421400281500ca14101c0c13040d41b80101140300c0340340c07800700701c842160040c05003414400301400540d00902c1ca00400d034298810310038010130b03285907401103170203480d8074150224910000009014418901616241c1806486041c4100a46460007aa204413030101e07240350310b64000c441d099072200300d507401c8501d01100500d00a2802c540004001401510400c01ca51050340d85a51034000043c2200c00c0b00c103c0e00e03500c000320340c084075a0040c5951000b4001d060f6403900d506a03002130002c0d00300e24002d120080d004804c00c0441142030220182d04141c4410601c01c0000700541109504070100c2c0000c10310001044104031525900c507a000c90560240343c1d02e030baa584a05a2a403070820491303890100801303540 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 107130638 1250 107129388 107129401
    0x301090608060f0f0c040305160315051303050f0c03070b060a05031903030902040e2505041109040f021201080c090c18010c240b030105091513240203090105 69
    0x90a24070540d0343c080f881c091034580401c00205800040c1042c0b085900c10300021010a009100401c071002840300a660300c9403944c074003e00442d0011803000001c900c2c200410000c05080300c803610750343e036043c40c040e6511050154014810b00482601c2020362001168860800808403403040c0a10021200b000002d5554400c06a480c40f540d201c0d46410600b9507582e0700080d01980000c1011840100046090907210b8201c2c0e1902d021800b421041500c0c0c41446590801e2a000e0140034042c02c0c0c500384001e00d0307070149044071441050001e50082c0c3c0e40302c101c084209010b0741903070031092512680c00c0c4556521130007a903841e04e0340340a01d80b00706903040202d500c0400442c100d40408100300e1a64111890340001995542d502a03025100b014140b140123480c14803100c450280420050b10004d02c8484001c1410700f150030040401141d50f001120f881616400221182d030f000d01240b8440383d00d642c05240c2001001da00054000f4200d000440c005082100764016500c02c0e000400200314556508 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 107131888 1250 107130638 107130643
    0x12100b030402030703080306030a02060d090b1b04030b0a0e1603030207060507030909020c0703050f0a061104061e03090501020d0204090b0904021e0d05030406092108030a051302040e030301090608 86
    0x1550003d5042c1e1000c542000041d1400d0044c550000c8003c080e52003e12440c0c021482942c084d0b44501c8090307544600002c100001950010b4101c500720540000c0304c4a03074808003010788070354000076051003411800159000043d8005003409803d0b58280c6005078090340107110110804e01084015000c3c0103c0411038a2050701907420a40d01036460941301e038a0720380c0400003544150600b038040d014224010000c10800c1000300e1000400310010480e00005003480b004843c134451000038040304c200820004603138044100c00341c0e0700c110901003410f940407000c140e0051548100080c095400403070928604032059001e003084811244050001c000c0c0f60080015525085270700035400743d500ca40c0344281181c1040b00120200010341840c4a0005035202c2c64551b13003181e031000001481419040c0411211518003070816005610320072200070300c5075510309841c040140381010180e964070000d644045110604466140c0207401008141c583d4440c590b02d81d0300900541071000c1c2040c03000110007600 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 107133138 1250 107131888 107131891
    0xe040f1407080a15030602070609170c0f0609030712020a1a0f09012f09060403060b15130303030c09150315140108040213090b0108060610081e0604020f12100b03 71
    0x800132503000c1c440c110358a0f880250410f41058440320341d1180c04ea0000b6242c81c460030703010072141003170684426041403e14506407011901c04000c1d00002c0600070f42003800010b940d4520751081d1818886045040c049140010010000c0e000a01011146204101480b0b05a02589503400d860107155940c151960a803041c1d0351040102141070815813400198207405d00071400c170000350162034410a440040c031285c11940094034846c0c0e0b40c014411144c501800459040f8070740f9000a030030143c0740103c0d442c0d0441e0034070019040c1502d0742c245151082c4546200c40141418842c0ba80c0c1110656000071300500000111460340084c1403c0429120791814040d1a2803070165241403140e582d5a0a005140030060a1407003007644031340c00c000018620b04410b60182401d80300030000c514201d030400540300010310303a00c42440740f080305102c291b0409060040714003050350045e031300302d849810110700203206a0101980d041c0c1d0100303502c0e00c2100c0d0742c06224001c2e400100801110703a1160100c02e0184030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 107134388 1250 107133138 107133161
    0xd0809010b0d05030a0c030203040504020f040e0a05040c03060906180f0204060e06101b080c0610060503100909021302160b0108011b180906090c170105010e010e040f1407080a 77
    0x80c0101103017584130780400364405200348162400d256031003011800380d0f048101148900280482c0601c030002d00115096445090342d031061055041c10384802c40c1200316808050000c5d91a9000d8a09006260f00b101fa004403103405a2052f90702e60b418040089001c11000301e04c1981045000900400002c11850180300000c1004d40ca618905105882e490b041000480c800201181100041780e0004080c0003c800c1903406064685064031920403142034a400c40828000c040c814807a41c5a17981c0010341c140c0d01c240e100090403810790700000701100303220860708007001c2c00003d03d5180c159140c07141c442a04d1041da9550001c5e40c85d060620300341c820454803014022003641880400030300c40c102003403d4a9008201540c4580c9a2828000740c0b5010340000f12540e032143e002d4a403c42e44160b81400307413030f100700045447c3d5040c030000070160301980130810b0400041601d031240325a19603210308200c214405003040419840c07940d441b040502100d01401003074840b030010b0b81d4000107000d510043d01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 107135638 1250 107134388 107134393
    0x10b0109180f0603120504080607050c07030f0203010b04240504020f0706050402120a0302030406091d1b0c0a0f06112803020c030d06090608010209090112080c0d0809010b0d05 77
    0x40907148410040011904880da1591100340010200350700410403280b40d2000d036903465032607050410312841d0100140220f41000420010880520790100312a81901c0d805039141d80c001003a400040e01400740c404400d54094074220041c01d000850741341003000d4109854290503503aa40d070b03040008030700500410411010b8100400d500060842d070141e640540f0080c142e50505490151036807071f248001004402590001905020b0b240c1c01001c501e00810319450501520b02c244810704008400c06000d8191002c1d8212200140403a083c06031104030341a0411200301058070709001108035002001941e000e031511081c414400380070800c40300b2603d0100d11800c4000c0860203048141d440d550400002c0503402d01040410920a20042508840000000c10702c2070400051004860855101d00b04980c81040806400d4680c0d800f000e04460b65903480f030400030850b0074515080d03c59202e03500b01c5402102c5002841a801941c40c0303001d001c1c107100070491400041d081c00114048401e0140a0780d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 107136888 1250 107135638 107135669
    0x6060203090d1707051207200105070b0c0910180506030c0703080601020a0204050a0e0c0a14010305040501090210020a03030605031203011e090507020f160522060e0f01030203010b0109 81
    0x3901208040c20120444401e43e032401d1515100d50382020705a000740c0fa404800065114140441006225240b03521148002400d44081c000a00a481105d40052071202c0c4800025000b03000e02003501d00210010700024118085048001d140e00000c0d6070b212211a00b5041c007080d42e00340a82903e1107400103007a024a4200a80c500b0368610500800841c11032041200324001a1118001d0078043c032070f06000402c507e04040311850914030070100483c09441c41102c204840c0f4200040e54526480a080000d40c1d0386403410100e014018802000e500280180c4078034055950020350400040c1c0203507010044181c0b9842010b440c1c43d400c0c00c0b401e0301c4440900041c000c03040c81d010142e0f4a45011000b0542c500e81c1c40782c01c201030300d0301150808007503080b580c1c6500001c04113114083c50740d800c3e0064260020300708000980200c44030b090703003244029500c2d5944200002680014050400007080510501c3e0011901c6040403090204900950070190200401d501400c00070302503c4803004a141300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 107138138 1250 107136888 107136893
    0x2030a11101805060717272401060e06030703020307030e0709020405030f0f12070f140a0642051e01020c010c030c0221010c0c0606060203090d 63
    0xc140200c0e00000301801204000042442a0312901580060465542003549401c0c00c080b800c02c14000c00d500180001c03139420301110401110956800307101c0301c00665060800c0514003925211818100890784a81c1c00c1d01418000c80000e0849401c2e62105c4000e40e50381c0703541084900030915a01c082d001001400850070040c042d4029581c0030b1010320300056003201e000d00003850300d04140e006401c100e50020b01404a400c0a02090803454040c0005200886801c5200c950340d1314150404043e00d000451403508100300c42d0341c0da6090b19004426000b0140b00e440c602600c807441c00701c0440d800d41c031340f80d0f091031000011080c0d409502401051101d0040d0301c10485008800d160610301e90680c03050402080a60310b10003400e01d82c402100c1000c404180310b40001e850460b140c4000c1b81802600002100080e80c82400c0000b110703415641610000021004421078060340d0201202c15400c09100d98032180e80070b01d648480c50b000705c4081c40510750345c49040c0c0c2c5030310401ca20640c000d010490314902 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 107139388 1250 107138138 107138147
    0x10225050a03120908070b010305070f05090115020a0803041208010608160e01020f0111070213020913020d06122103060f1e0e2406030115081b040b041a0301050102030a 74
    0x10501160f03080455580da0503034500c0c2e9150f0004200300c1b4002c41000041c024041e08216110140c407180007108170789401c0c107001402c2c040301446103031f003160801480075400074402d00a000110390f200d1580c0b9101c0c101403900310760458682c40f940c000140d1005c00019040d10407070060340281580400c160810080301d000302e0300310b40032241c500d055225064025021040921074003140c1c6500041041c1c980a1510401020740401120350b4035450051242e4421a512081200110b0724064401641c3c2e80407038501c0c0b8044c0070b80ba4000d045107000d000c0d040007840010344038005400002036900c0b042c5100d82206a04452460044003c82b5050200a0025501d0b12050340030b422400c0d03103609586a81c1da01910001d0030200e503018108600d440b50030b404081003031600d00c04900100c0d5280e003558108003080200c620150b50003400c0080e8070700882c800c0164403102c3c9000608440a90b55140c0c0c80d41088039031948940301d89680c100c011b081040101001209803816101c050b4040c5151410854003180e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 107140638 1250 107139388 107139407
    0x806030d09121a101707081c11060106030c08100e22080c160905010b0702060f0d090302011d0109050709020c0304170705100c030905041e0509010225050a03 69
    0x6590214003042000700d66000f440042c404c0c1c4858080c19481418015100f08030314100c0c6401c000c0b0b50121a091000580100f8000d001c184000f258513420080014115191244448212a41d000e14000400c2007549508101c02e81744450f142d8050607110a0b1850002c0b000034403c0c0e080c0b0511020220304040c80000c0400c001d1391b41c07048000c0c00c039030445d01c40b006141d0041030020031643c00901c640c800603840091090051442c40d400300b090790b2400301c450a50384500800207104a07400140d80d10075003020b205070740003800341000800180741c1c0d92030064000c0200300d42141080b900750407145403941c0140a90007107960b0040180813014600ba0311003010350000058003000780424000814102a02c00458855441d020003c140d03081c5007406118860034021162410050000e00460100380c00210500480d4419a80000c41480c2c040041054041c541c0d805581142080c05028801c0c80540292100c0145400385e10740e214550314502051103a103c4008242e5081031091801090144a01c41c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 107141888 1250 107140638 107140643
    0x601050d0906020c060403110601080303060402130305100f110901090e040201020307120203090907030b060304020d02011b030c051b01020a1e210806030f070e06030a0602030f04030806030d0912 85
    0x46441d804035a0b555050f40c0005401160541c040c000300300c2810b900410500040111001a01441d41442c41c020784a11000f4603c900813034000545800e080344a025500007117400400f41c821100360071600001500001c0c00003084a41042c1c140801090520221020201e0585500c603403d4a0102032104405009005905501051217264045401105250444e800c545d001d9030ba10007411042200400e00034051204240c80d010184506880d0300040781e0b0003940441d00c009400c02c1d2880103c900c4010f10035010501e10f03102c03119404040e00844071610252140d005d4a0b01680c0340400c4140d859141c145403030042c0d00c03105040010800030000c0e402031503504003105039103011980b10201035030400e03006a0080c604166252121036071220809400400840103003210719100002d9650301c10082c000d54071040100c17408560141e404100403207003254012070954880c940000e41001040c000c41e416804174211100003605d42c94007080c84207a070035031901c48104032804c10098501503500091304 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 107143138 1250 107141888 107141891
    0xc01020d0819050414100501030c0e0a060906060207030203100e0a0f11030106060e041406090115020f0607050903060903030f0103060507170406020406030b151b120415031109090601050d 82
    0x4142c020002c03406401c0c8514020901c8404414000c003105207003400c0b02d00d120f000306103458010300002d111041c00c5021104140141c030940d0301da91059500511741c2d50702141e84d1515100001410580101d0031104480c0210300703a034030060701f10242070203640050f00360f900f00d40c0000d08440d0001d4082d9003030645160084070051005810341020a0840710300ea04100d012642001100c00300e1300c0d01d806411441d00b21190065098201403020035480c000601548026400011456007014420041c001940000303104844181c20f0109010300140c1c00a0103146c0a401200001030300f09500104a901614100c108a0b055a29507142c2d8002088040c000d00c04118004c1e142c0074940c6c1307403d007299000b07500441d40103907150b10b0418003400b00c81030140b401e4042c10715030b02c0c1d48000e60001002d8541c06809849418800e00780020320904181905c0b50500c000784010401084402e079443e040a0f00b403c41d510100581b15082030802030b540100c1000c1c940c080358080020b89513500c10030240c190a000c8090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 107144388 1250 107143138 107143171
    0x203040c09150905130204052409090102130b0703080106050c0a240207030908070909111c020a0f0303080601080c07030e010909060e09010c050f0307110309060d02090a080c01020d08 80
    0x1c03c5402c3c0c801c10307030345555441d078903000c1d1805503e0244a01608165000814000e4850899007201c104a0580710103102c1d070070480c000b80e4200c000790100d1b40e0720b01c40320b1040e03041c4548403500d409058015030010b600065048001264080c061003c44001e94030301002011058125920706100c038464240d01c01f0301c0b0103401c404500340d1105002400b255440781e02d40c010518100351041e4a01016544032940d820700300112070000c1080e03040c0768a801c1100391214206100ca800e002000100540e4000303412880300f900c0027a01c90301056110083d40c1c442d6981c1c11031a02c40100442d40110b06455035007100341c0130003070312000902500024081344810b04000d0f5481d5904c2c402141102c084d5401b40081b02c01000030042c001200b0301c10080191a1800c105050001c0410b80b05c00902009040d071042c0002c6541d182d898a9081003a65004000105800d9941101840c104082e4000b403640c1801407aa51401094085002c640940d40b480180e0007031a11921030b801c1120800c10250008070803501509 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 107145638 1250 107144388 107144399
    0x10f020724090b010b0316020d0f03050606120f0f011509170f0706090305061608011a19030603140a0803070e060c190c060504050907032315130203040c0915 69
    0x10900174688407040c5620b034900001803198902c0702e203a00004541044009200454100084542602c681d140000343d6940b00004200540704e002900c000b070900590800080c603000b1410f9601c1303450350458032000340e42e80d90508014902e04e449200701149015a042c45030b000702d04020802d01441d01d084450700540c1c1c856550178070260fa00300400103199940d050040c0141002056000006038542000b804040c0b4001041508103000d80301c5800c80d40c0c0c80e40070203c2c0584003645d00c1c40e1014030002da81c0b03802c1240081e0090200d417008613000c604282c44c0011105000c190348004581107a4101c1c5955262101160100c1c04900d686521030020320114015078000c00407905249500d0140ea1040d06150524141100c0b06901640800508000c1445503890300d00c142600449a404d000c9100140264945802201c89800d694050740d0481000034aa800170845000c102c000d0354484004020110181305910048401604080720b4140c1005007180a0340306441c841d2206468145050300c41c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 107146888 1250 107145638 107145653
    0x61d061b1006080d11150103080903030705030409020301231806030718050907050901060914010e0d060f050a09020105270907020609010c2105040602210405010f02072409 75
    0x1a000341d02c3c20381c0301c4002c50706401d4203c014006002c198100500c544241c503009007103003c00500006100f841c02254410003900c1c204203460f041341e440b60a5070740b6076440305010402034000f4801c640443c440c6000c4070380460983c100c0204013035400740043c140c20180a01e9014660380182002c0e40604c030300b007000152a10343c8034041e2200000c240f0045094108403450501e0301c045600300340d01c00c042141c0100602c54001c045c91045583e0f8005ca0300552014000603640007032026010f84c1c008a60165003c02c01c8640e50158840c140040e1080103a5120040c40000321100d07280004c1c041081003059540b60400c040310012071404084014108960031404144240c400780c0e0014003680c00041408004032003070040780724091f09464a40720009080c0001c40c0f04001c11210b040c400d1b0307600c102280a21906804a03081030004004c14003404081c17160300000c809045400362a02d51825904d0940100a80211110203811292141503c052100c43c0c012415204941d0f008080c0d42d2900800020541d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 107148138 1250 107146888 107146901
    0x621030906041e0e0c070f03050409090809040501140d02061e0c0a0501140601080f19020a0f091a030103140102070615050f0109082e090b01061d061b10 67
    0x640c3e05007001d50010b041280e0300c51950096081031500c80100040f00c8443c4043d100116007140411184241a00f402d076004e00ca560884c41c00241803c085006100400b40207090b2040252030030080b07680d0f0b501d10b900403003100e6101c0c00d0340645445108805031818030080c0004005110b0301e8000030348405013100d041c2e8010141c8406075003001c07625506000c400e1140b28035480d0280c99074281403505d1000203040d004d008241c0100042031801060030071840c03c0d0ba9440d06020343c1c03811982c4200300000604402e04c6001002c00184202001180560401c103c4403002542250a1800c50342155503500320300d031848101041641d428403044010030001c5c000c1036006034414480c0502340d030401c030904c02e41c0700d0001c080c103041c81480041001a68400100740c41446440c2446512000004120900700210002d08050030b42c2004d4480091045c80403800e8121011510740e01c40c4240211601002c06132140d480701c0d4000414441103030703800b400000c03c1100360a801c0550304952202800c0c9001c0f07914 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 107149388 1250 107148138 107148149
    0x2702040b0a06031d0601030201050306040509010e0a0309140402160201050c031c0f0507050711010e01051b07141c06050c0405090906070e04020702150a030905030a0e040c08062103090604 82
    0x21100441d0701c40303240300b075040100241e07610064503503981948c0002c0c0c0b60780300c09030909005d1641c4000040b0303607810039401510b040060000380e915840213070600400c0c84d046801800017171039810f42c0c0e1120501e058821a090310740c01640c2089290712035001511290407522940038a40010801000112149031070201d03451111180060603c0440020700c00700d43e4010a01c030306100c82013000c03001085090301d01102d6030710300340f03400841710f60541c0040301e0600800888043c03200d04032000000e0300e100492403809032250040b145115140503010070100e00c0b000c0c0355907001c400d0550008004120f59030009540851181300c554640f9a44001140004d6401c8a111036540c21020a01140650140106000f4581201c0560030100b07250001044a2a0083c40d1000401c00040d4250114042d410401506030014140ca4a408041d20042c3c0400c0c03130300c10010320880c0b44c40d000b80015400b8048190098002800280d10110b201310034a40d503080266007a4450b1109110b04801c66850340010005001d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 107150638 1250 107149388 107149391
    0xa06020d17070e0a230a0e04060e03041a0409051501050301090507090b040602150a060b090409060b040914070911030604020702041104090f1407050304030c0c050918102702040b0a0603 81
    0xa020502e0071708003402c1900c190700d150800c0001040b9410070a820542200000031411040040c0a255104581c000724420400c4031440b6203804584c8050011a40300440512559032541d0441c0f5007100b0004c03c03140860f40070320051041d42d62a0740300c5540a019418000c201380d4441c145c4c080c40380c200e54881c0c00141d201c0c000046281e9042a40503412040103281440b2040c00c1181c5050b150042d43c52260149070341e80d08810034410190007451074510b000c2e004203e010454208035002c4191010a109148034050300041c0c2400944126442004003880c0c85045450300c03010007001c0d5009460607070740946c0700c0c1c84032039a006014000b800186194000012441c401d14201c40c1503661135600007101032040030802400036000f4049940c490391601d050081ca440c1468148404481c503005160051502e004204152410b20064441800301104030b4910f42c1c10309882d081070b51103160f1b601c8400720104140104109c480c2c003a50348114130080021899002d907a0224001c01c0c01b0354071100009 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 107151888 1250 107150638 107150669
    0x40305010b01210b0f0904051e0a0b01150c05011b0e060c030702010c020a0902040303030911120705090702100e03030103020f0d030c03120e010c0c020a06020d17070e0a 74
    0x921481644a200382040e07140d042c002041020100800070b2030302e450381d880d135610038103595440391108002c0c40300070b000080604160800980d10109103401007810800c603442e0001c09280021000020365200d42e111030b49070b003428901800c0c614200304840612469107007003c0010000c0c003800c00755051400104d100000040c100400304400c500360369010b1182084401c1541001004030342980340c0a0800f03501e02030b410320200d00716204550211400500c00302c0d02004141c1e242c0c106004d00c03402200c8500000c0f038403404000104d059522111419070103644104194203108126551168a07230040e2050451003420030b0b415100485010000b507003000006004505d051088074070782e001e0680d0842c92040b10783d038000d042d058040324080c0070701c0f041101c000d0056000e50010142801d010000344041d0070b003144041c0c0385142d07a843c1240b00d10b86800c40801c0c90352001a51013800c1145549600300703400c3d0012111003c0c040540b414081001d030346621011621009203a9005004012400420 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 107153138 1250 107151888 107151893
    0x20d0e10061208181c03230405060409022203060c03060902040b09011103093102030702120706020702180a050603060c0a120209180a050a11070201030b0d0b0a06050306060a0e0f070201090503030c0403 88
    0x7c004541780b2011805a0030b020500450b00c64809440070f03070b442c1c1c10740140d07100d840110001130032440d041c80d400d101594030400300c2000001e42020b080340310305071028000070f80c591500d00141e024070f009008004d9014004130f02991b00ca07801007003010780d02c039050700d207000403410101f8224240480c00490030380c0c440724402140c0604006143c480c2c031080760b045056003802400251031700c0300c889001d8a650004281e41e800d120b030607811103185a500420384100e0768102c043c8007040c440c3c11504500054a418000f491034200410080d10071a03881404607c1d200b07040a06544500e0040850034030f50360709004605540c6ca40340004180940000316401c07441c0f40241461082da0801804110043d08111802c2d400000075415a00d180743d09003004200280b2502c04942d811810300030150060b0b85550900c00580080d511020070b8403400d07010303140c0c035640340000d01040549a104940703484103d80300040c0100a1440321340c0d00030000344004110358500f81c603100d146400c180c03910b140d02d440c0041d04004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 107154388 1250 107153138 107153177
    0xd030c061104181116080c10050a0e070807121707080304051902090403120e010f05011701150302010c020310050103051b010c02090106080703020d0e10061208181c03 73
    0x8582032050000d0004810000542d5002e02420a800c0343c0c80f45101705100400c17102c4410354040300301c240102c40c8864004100b04014020940354a040b4518121007501c41440c00315011064a5041000300000c900e052801040351303000c0d00055428070030216100034103c0001c4001c00c0341d54055180b03151241081c0c18001d0400703200c0042d0300c150b030305460341b03500068540500c0581c0c003a030103050002411807a800c0b84e8018140012040010b940784c021014030402840d0300c141e0681d0f031520813480301030204e181e07075508a078000390100148003042a07003040190300c141444140544081c050310f081c901c4002d14134065410a8200300c400780c00c00c5221050702078013140907480c910800d107000420f00e0a580c01040c100c003018050101081408400203003500d000b601220100c10a40100300480c1c050305801c151104001c000190002d400c00b040000c0284080110b907440700d420040345072801f6100840d85001036844102150400c030903028040301c2c505018198400e090294940752000f10f2090714144 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 107155638 1250 107154388 107154419
    0x2409150b010912060b040b090703091106040e0f06030309030706021f1407080a06120b06040f11040b09040f060b0d06050603091506030f0703120806100e0d030c061104 73
    0x2810006200390030443c1c0080304000259050b04408001a41d082810129003e01082e2268903084510202400600c0354158441c0003080e00914121020f1000e802c200b120724440e074800d408114400a01081340a58080911900010003c0c1140d01c4d14840b407020031f05040c400c2c0e2210f405038015040344082d00c3e03241514a00d4011000c10300b0086041840d441150801d400b829483c204500c000005105510a50000b4040c0ca10480d070300d141070020b86410094400300312125030085061600149134030100c0c0c0580320404030b01c821200d041c24100440c124482d0000c1c0e1000d42d0003a00d074100f40d0268082c1e40300b410060001051680e1356090044240420740b4081d5000c039004600c10402c02c610075202107280312812260358084051074071407a0000f46042e9000134481c84074040e0000000400c80004401d0406d2045621521001d5403081c08100b094010400403401045041b1001c4106282c00006000200c6c800c5c1003400080140c0d0701c2b81301c21aa003d002422103990b00050074012441040d40e0b0340b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 107156888 1250 107155638 107155661
    0x1b0d090602010b0105041217040801020a120506090103080703030917040503160b0a0c170c0a1a0603120a022b090509130f050a080307021513020a03240915 68
    0x2400940003c0b00003d210348a24410b14088a00c090314600c2004002c03c84003c0d4003070f81c210415115034070340f45024000e5201010000c046a090303040900340344000d0041920401d8014040021a840d40d11081e250b070340002005c4040540d070310280000070700d044a100340004085420345072900c0c20081070501c1e00d4407d0001c4030704207146c042c01f00107440c03105c0202d8106904501d01185103008500d811000044030084100030102d0200d141400580002904101640240c00c4c41401d45c070b0040e1103d40100c02640c405405408c50401c00d00344901c440300808804005104864110481c6440f286150700d1600c60749030020600b40741c023490943c1c0000c1b0240500301c11207402d002070400070b02103101c07550403000c0100404d900c1103081c42480b406100c0301006c01e4000501c00d60b03038504480d0080d10b9105003100d1010f5070b12000040703403200001d80b00c000012a405092451040d05507141c0c09410b9130040a003c0290000e0030310780103504014021001030314032a00f00d01042000700074402003510b0108420 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 107158138 1250 107156888 107156891
    0x5060a050303032404021c0c1b0c05040b0a0503060403080103020108070e01020a1403070b040b1006170a0509010e25090903050a030b030106030204060e0f010e070f0806061b0d09060201 81
    0x6000600e80c20540001c0c100703502c1c4548001c10304c41240810003900500d5000c4007180c08a6100212100d21034000b4480c51815540740000f010348003000406140f0801d03c00744c1092138800c41400f10703040590041d20b0741e4070700800702460340d0341e208006450440200c400b1400079000780010030465800000c207680100540c00d141009003042c200003907641548400241c106420740b848500301074424404c82d480c03240c200c244800c851400782801104100107a4040440c01207411f00042c01d40d210301c1044e8030b4004401d080708203075116202d08002508014000020a5503150350092940d6004c00080c0c0c4403208880d507161003d0441c4081c02d0a44840341d0000000ea41040e0050300080c2d840f20494404500394200000e10040c19800300f80104501d4100940043c54088003085505243c0d05240c482c0e1442030781c030709450ba26540c2040d100e200c20355420300403550640e000c5400354082d5004a900450140419082045582401c49010b507802c01150303854112840c1500e40580c02940d58001e03240a000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 107159388 1250 107158138 107158141
    0x418050c01050a17040c090c0f180b04030f0212030d0b030114010f030b0903040b0315090703110904020906090d0b01060206070906120c020c030a030806040b0a03020306131e0605060a05030303 84
    0x4040c01c500c8502612038002510440040c0410070999035a01c01f80804000c10000c902c1103c038098180110414100701084215103802c01310b96403840603409590003038120300e09107461662050b1010000c0401268050410b0726411075010b0104041c2000d00c2203400003080160409090500312482c000c0010302c0104103000511409481242503411680d02642c0e2800f55514500400c0c1980640e41154156070000004e010078882c284405415010085601e40d8064480e8602a4200c4440081c800b40d1010180a01c55040c5002d601034080140c001d007541e4a00b5000e40001443c8000108003250309140c1000148140c990400ca1260321a445083c0154101d00380b610240c103005c4200106c0061688584651160910901980c0b14842000c1c04a40b082052403030040c1c480001154214055464026000c006180450720300c4200d980140c041d10710307501c44940e010308568415070151181c4440f0041d02a0400416410754251400381000203010f003000010412698807035844244603520900 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 107160638 1250 107159388 107159407
    0x20105060a1d070f1b0c090e0c09041101020c04050f1806043503040c140301020f19030b06040308070209070c0818010e06041d0703021306030b0409020418050c0105 72
    0x158003d8106801d820300450aa080400440e0104044400c80e24504804640d0300c080240b08a840004d0b1b604140c428041e19004c2076440c0e90700d0403500c0d8041e9100d517410f0081404202410209510f206062044c0c41e40b150001003c1402d40c0c4040d40c82d100100040c1041008411000c0100940b007114000544040d083c00d4461040c64001000c411b8020440081d91030502c1c1c4c1117416601881a10460b256141d00e0709050550810300309100340301c6941042d01c6601c0303845c941882100c1900a403250014204203c003245003500d100d01c0c40150041c95030311946400705695105c0a40001d520844001d507131505503105006003000046c0055040c41909417102e80080d508400f921000e0049a00c1005d00403800c40048941c5d00f86a44800c0c0c02440014012450420014008461f40c005103410443d030380b552a0218128170403501d2414080d0903044003848503074483e0b080184541801080812404501e80010f801c85580004210030100380404020401005000e000d0624009084c240e040c82001c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 107161888 1250 107160638 107160689
    0x6060c0302071406090d0b09101104090914070f090b0118050603041104050c070201080f0c1c0f0c031406040b0a0501120212040302070305060a0e0d080a0e0a03020105060a 75
    0xb03000b01d1514100f0f02c0a015036940ba401d065500d0460f0041c1003c03190005414090100981905c00b2015401220390082c290340f02401910f010f5103004a03140e162510704191680100000701c400c451001c030002000c032035048204144000350104030140103d20707207042000c1c0d08660039030344100d05114079201013000c0341c01c600c007545003100d4050325400d69035591791501a001c0d08070421110f41c030516110620124030b041704064185940700382c80d4400303c0e48403039400b160303696011103280768400d40801800d01e112070b0030342d40c034801100d108502003600c0c100010041c090303941c00d40ca40c1000980c0c541c10103c10400c02c46072a5040b04060f1010402040c0c0d10022078070009450007403d05015082c5090b83d0008000d0341100c14061000314140c3d01428549402901d034400d5201c241e51600c214804507400b95035500c00c41c10344800c074400805507400e0b046410741c1c06010042012000303580d20702c0551a00c510500030346c09150f00c00e034000201c1d460304008004944020303400c07410407010003d5111041c101c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 107163138 1250 107161888 107161903
    0x3060a020c010b030d050c011802090a150e04050a0b0601180302060307020703080d02040501030e0607091203090b0a0e0907030209090f0411100e090c09010e1306230406060c0302 78
    0x202405a940c0403a410142d0142c100c0b410000c4d014401d83d2403a42031554800041c03c0e030121445c0090200c0c41c20301c040b646113480d880c50b020351300909840101e840200c00d40d00070105010141c2c00703204101e035200c00d4414003040c04c030340545041c2c10182d03440040104143d48507a000409081c078880c649508e00205110904a0200078010b41c4000080741c00c1e14000c010210086134031800d0315940706c0c11105101c019400a104082c00701c1c0c00e00b060b40d24035200c0459041c1c400d42d01503071100c1d2410310340b000b1464091f988000030341c01c0c0694040701141801031080200f003501102d48031800c08802c6a0240301c11000c004000c5420503105000001c55a036071400e00c00e8109100c0c410710403031901e030fa0a0000900d0716001840760311091900f001100c142c0c2142170403d021008550302c000d20f680c0c10440b01280d100d10300358140010082540340d4594500147c5441050440c54000036805445420b40c1401128085031008200d0050907a00d00500c1d2a00031040503090900d001c05c04a5202e45e07020350744021 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 107164388 1250 107163138 107163151
    0x2010809070b0409020903060105090403050d09020402070b040303050f01080313030809040b0301232d0a0e010e07291b030705060f011d06010e011d0301050c1b0c0306 73
    0x8001040504008200040c060810302c280699903554443c20074000307601c11101280070340601000003c182c6420600c43c0c0c4541d8140e08c3d17452800f9000c841000080c01c5003002260320680c24044880404d1654600b03070310a611075180040d007810b111a00522940d0141d001010f07a034010400034810b06150644c110803030f580210056222010b00e4001000317400ca0112840e00b561a01424106070f5501c040710140071840c0c11281d070183d0f103400310450406e400d244500c4810b0010b0041c1c0411500210350000c1d4444003010340003407583d18200515081d208100c0000c207850344810810f100c201c0507a882000c1c484c8a8200e0840041c2051b0b4500c030242c010840048410b10a00d54154205c410134412260743c00e5208069507001c0c07914a0103866110802e00a001c0d2103101050354008680844001a0003414142c6420300c600343c41d80c0044400c004840c051400c40155442c004080c0c0e22709000f401d014003201c5900c144c0b1200b100c1140b015000b9980d060902030f910a0081c050300c5d4402080590b000304 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 107165638 1250 107164388 107164397
    0xb160605091f0e0c09040602030709060504050102120c0a02040f020901021002090a05041119051801051204110a0e0901020405011b030f0e06071406060f01020106050906060c01090b0403050a1205010308070201 91
    0x382000000b1382880700c08a0115001150f8200f0082000200da00452007100b281c0c4a41807010b1300c400d401c4070240564042c103405a0301c2103146208014040c0041d191161940c02102c0c2841c8095021800756201e412182c2042030b000724440456603018040b405a0804001c0c08504050050380000d0240c0c507a03100711381c051a95904107107d400401310440d401485285a03c8014881188005042d42c1c8508040120190b02410021466201d2800ca1754403400141040c1c00a40341c45d100c00c2a042c000400d440d0340156010780c00114122000c0c0c98902c5011b401000603201c9142070f002400c014003100000e00b490740f00320322000001703400c91201202d0500d81d1400700b003220300f04000708884c0d202e2200081c141d00c00501011f9044000024034901c1000c3c10b0310400000202940164240c0e400c600840d94050211030014189080c440003a03d92141c42c440040f4205610751074100c144c5c0019141500001e44c0091440c00c1d890f04601342c95111400701c01c0400056240da161092240240c0720000d0400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 107166888 1250 107165638 107165651
    0x70b040f0c030b0903030f010e011214010b030d021b060c0a0b0a140f061003050c12060d0206040b04090b03030301050904081b0607020f06010b030606030402010c0602040b160605091f 80
    0x800900c1c00a158007481d1901035041c41c0300740380d0303581e00111000290b0400c10740010130b620320301000c180d04a85c00c041e0141540015a83c45050054641405403020366075074900c1035682d07608100d0004100c460760050118004403c07000c039102c80c0c00c032064a0280f0010000c1e680042400107a143c0b44580041502019894030f61010b800340191241c500c04034400030060008680d81116200c1c0195802c031070b18504502c041400380e0544200721600c114041050001d81e1102124100d469804000104102003003c0301d81c2c0014210b401c60341105000c030b400450240b11052440c0304001241c44120015030031580741ca000164a4800280004c10901000c0303003416074940c00990602081ca4032000b40c070301e98a840030000350b4448294030000760500c00d08000041406402c0c084074051840940210f15541c0c440d001502c0c15542008100d40b0f144e420800064520042009409056030002d14202e06041904050301900c07005882c04aa5400c800d1000c04030341540114a2840a29020007280c0c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 107168138 1250 107166888 107166893
    0x409032001090611030105011710060e0109030501060e190905100f090b180114040203060105010c02030a0c060309030f0215010306050c070c1e08070e060118080a03020a020405060402070b040f 84
    0x50300d40114014007540c14131030004503500219000c0e40c107907403083e60703001915445451103030920030003070781c8821180d00e0888050209c031b0703c59200008140340c10b050410034180e0700e0703031181cbc219a950b40c02045d690300c4480c103104005800201d200c00409000c0f034144012040d5446403030b02c03221520315040003141c0c1d0305c80034844d04110740c01c82680290003556000d500e1500d06044110111742d11040015035282122504148c1c1241444501464003e03000740a582e080100540b0410400350003070780d15114a408030000221004049000f405580c0d4010a42407803519018041600312010001950010600031011a01203003215044030b030090700200d050388922100c0f510501c50441d01611010760000042802c1a40c2c080000000c0c00008040c15901d82c1c44100544a1110b40101c202c000070700320201d0103d612480900107035a60754041c5071400c039030350304c462482d02c643c5076412030250300190007000652900344100741e0b101100392400e514040d61962440c0e1100c50017040101a903115000c20f106 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 107169388 1250 107168138 107168141
    0x5070b0a05120a0f182f0f04020903030304050f1204030b07030504021903050a020901050a03030801030f0203100603051006060503071b052515030b0d0f050120070605060409032001 79
    0xd10080414200721076605840800c2500d00000310940e403c1156500a007024000354801b07007005000394100107195400c00d010450b410455080c160303480740c0c09101407141c540c0d00344001c60180b44070380010644070703150709040c6081001d4914094142e18043c042080842c00304c00c40c181d8005002c3c07030b0014255a40e440000d4040ca01305001991040c429200031081000015018010b41c0c000c60716000e6070f80c0d03110100308803915030f40801030000c2c10300001040087c02d00704100200c1072000302a558601c3c0083c0c1403004840e0039900684030790f400380001c640c0b00c003201c0c1318205c040d15081c0f51507459407500100180030303180c058003203002d1078a0b00410741050103000d101d115841c8e145400c3ea0411108484418120b81d080350041c0c60405022921102100d800ba00c118010102d0103041550388002c941c45400c40c8102091054609549a0b0300451a501e840394490014191008009455016a08169046680040c4460301851400c0101008680c00827207180701c000c41c10038089061072240113803a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 107170638 1250 107169388 107169401
    0xe04290109150f0620010c0c022704150e010507021c0212030f040515071b02030f0a0303020307022e0504031101061401120506090406020d060e1305070b0a05120a 71
    0x1543d5040500380130401652140c13090f64403441d4241c038502c00d400000011803c8a0b18290030704049003540100c50010308050358912000015601c0202c0c900e81e21413160200d40600700c80840d00b490300c1415100c001010b502c580441c10901d40020469460a440069900c541110307602d0701144041e0202030710300c1d108000000041440741c0e0303240e880b42844d403248a85050150713800c40384c6000d1500082424851150a188038003070f03a99583c030007107225440401d849074400c4002c0ea0540507900b03944407403640401c00c1d068030074402e039001603407854020b500070b0908041c14000ca5450b80d200314001d00b915a0000742c106040c4c100711000031244c969140940e001c040ca408505480d5003848800284000c02c0c15458112400c00e0700c545110103800103001084480895401ea48441c00030017250200300c1540c042c0c1a440c80109000401d0f0344c0350701c1011505601200c485c888c0d184984510010404140f104900400580a01c0303170402c0070285020f4200d0088803030540452044100040c8540070035040310 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 107171888 1250 107170638 107170649
    0xd140f010b0f0702060c0105040b1308040603020a09080d020a02010806030c010c0210020f06040c030606151b05010609091b08070501020d0807140a050a02160506040b07080d0203010e0429010915 85
    0x20380c0c0c078201b010303400c0d01805044600740c402180b2500001c000890010808191540c0500340d6481c103814040282c0013500050a02420028140f0003c00c19050400071405540352607001000c0300202803000511492005214a000e904485035001113660050000c1c0c200b40d0b4115205050500001742c00c030b1802214201485103031040d40103000038008903072004030a482c025034040c0200d688841d079100c884500c40c1e0b03840c00010f049911080000302410350101d0030b43d00c64000404c0742d660310502d4200b43c1724200741c15100100b560b2003443c020b692011030030004000000192910340e1500300081d4844012158450600c004d09000a903007034400d40e8141b001e00c00140750700f51140a039000007401074000185140151003000201c0d03600a1200e81490202c54005020b18a0315040042c060f90a41024000305d07a408001d000c0c1507000d49060010b503000c0c110b06e040c0505503103410704188a601e012501c0d0102c1c1042c4004591110b4544540301c54151800c1e000301284c010000c0b000c0402600752030b03104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 107173138 1250 107171888 107171899
    0x5130b040b06210a0b0d03050309150c09040e0d090e15090c03061c05060106030207050c060c0a0308010e060a0b0724020307021e030d110706060b0d140f010b0f0702 72
    0x107500803c0560610302d02e6042c0709081000d1182e580781c2016084a004c546201d0784400368851880009228500440d80251100c050f60b503041107048034040f082d8004e9030050718248003c1030440d11400d10344102c85c40d070b00000b001010407070165440545640c2203400350034428036220340014202024061a81442c490241040b56145041d05001c0119003058a03c90f1090f8080c10004d40001c1015000854007a04080501040d074a4464142c0c0250b2041c001191240515400e45000740d82e140040d05454135180054a416a03003460024120107050700a040d001000d02c043c01440c6e1110b4040c401980c04400c40d0543d658070f14100154032441f0b203000c50350341c404030b0f001d0b100c0c030f503099600a18021b010329002c80340050425840ca81d511001e00e060420795034000e0203d205014140d80180162115020710145803100c0d548400080d94602d401403c20300f140080c41d608201640c7c031848160ba20013080de04100c1c181034503234489055041c810400341003004100781c2d82030000041210701c0c0c141d00504 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 107174388 1250 107173138 107173147
    0x403060507031109131a0d350f0703110105040609121b08070201030e030a0c170f070b0a021b10060b07020307121a0403021e0705130b040b06 62
    0x4004025020407502003000a0426034a200c1031200c11081d01e5010030f0091030000300303900550800009002c0d407421711024080d0030000c400c00d51242c81a051801d0300074031043e05000203800282d82d0f90410005100c00321080341c005510320403007a40540c0c011880a0300b2090f0344000c2e6050840ba00102025a21165481c0c5810300c403c110080c0d05c507030040c500c61a0103d00300812468103540d9403100e481c80082c121080c04900c1e0000780320f0001080b02501c1410300083d10701c80f0000701ea00d0f5030030131076a480c08100e403e00003034140022800000803e880c444010742c030b0100751140c000b0381401681d44c014104040180459030186140d01035543c080c010580340d05801c082451040d60350250301544030400e51402c200814003d0322101100d0003603801900400d442441c2001240c1c22442104041d1407120f4818840c03081085041c400b1400740f4000d9004044143c0448003a5031442941b076003c92050b403168800b040301da02d440742c2044100c0c130f81040014510f243c600108004e008000702680e0301100004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 107175638 1250 107174388 107174393
    0x81e100e07080a0f0203150f18070c030e0a1508070210020f0a1e050313030207080105070306080c09060a060302220807080d0c0b190b030a0b090d1d0d02060f0403 71
    0x150b155110300000c503414814004590010740882c40b0503034034103800c0d0415007003851080c201000c1c80065000d001d01f03141c1c0050854015424102e005131280c400044400c40d050040c10361000440602c0d05088034403100c06031401006060a22616240c002886099400180140d009014812291a0b4800c080d5901d001000e03001245034030045084002c1030641d040c1816107000903940d402d0f55400c1c5d8236003038610b072154824000c0c0c2400311030089046206075240412011421301480d4041c40944d04d000c42c1560400607c03d003840c1d83d44541d02d00802c01e81080214175030f5003110309400c9420034240140c0c1e0b04100c161404d620394404c417102d021050048400a540000001c1310340c2203c1004054640789a03035080211800721809401038003000041011a071403e01c0c046e15503042d52094800041d004800030301203410510614816100d0111841c10403e2054060001005054061800059402c80c40ba803081c43d0483c2502c440707008541036042c034400c64507040d0850f0019082c00d5105034495a492 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 107176888 1250 107175638 107175647
    0xc03050309010f0305060307091d07090902040501050102010b030d110106050a0b21010f0b210f0108010507020d0804061a0a0803030a0f0c0e100e060c0c040b01081e100e07 75
    0x781a0900090b030103042c541c0c0552007442101d002c1e0301d000b000303401c2280c61300341e17410080e00ca02c042c011505907004411612190003004001d0052080140201d41c1c04110b004200c06c03a941640450306690410840da01540d50104072003005e2011400c14042c2c900a00d00f055005108039044141c0290f000138001c074182c3e62400c00342031580030407100d1a01c0f5144540594501c14020721a8840840c1507800910001310600050180c40b0958040304100c40c8001d00c00c030166a2043e5241e83d0981800310050040720028001e281d806200d0380020301401c1301c1104010700a4000030f101030300c0d0541d00c020150f01da01000c03802084902000701220b0345a0744402072035031243d01c1501da91045d07a240a10040e0f00b60024000c150000603d03442ea05180041c0e401801002802c90b00303200d080100c0f401c00c14555581d044041e001b6400b41d240107042000245090108680e4070840580c10710544200704600e040071305030054004401d04640200544542d4010010840c95400c03030200c02040034108070f0f480f50301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 107178138 1250 107176888 107176897
    0x60503040c0503010e0a170d060306090203101505041e020f0406030e0a021302030601020c03030f1309020c06130303090501050708040308160e010e13110306090a020c0307020d050a0c030503 83
    0x4191141e0110358980402d422603500d044408240d80008080c840840c1c00203943d145d03071008410903030f8034150240c0d154030101c90341604100c0f002641c42d0000c90a41c00c080180c0b103842c102403801000342d40485004020800054070680c4d10585e00c5441d9210840240d8501d20040c81d008502135450380412428125960018001c043c00a441c0c00c8005082c6440000c26507142c1c4c1d000703002d541184401c00041720182d8401442181548180c200c40f8000791020801040750180310805503480f50000c0c1489901212550300c440d400a005200c0442c40c100c001c80da0540040401c0d07a4070300708100b145025006010090b8000c1c0155281c0401c100b6466040020701d842144296100c0c806640c80810140c08481440148400622401340ba080c0c294041c0e000c01e201c20380000c09007000b012100e414281030ba03081c00d5980b2040e180c04401e00100d401c102007260341005640c40d041d424803035001c80441d0783c1c0c010700d04041d2007101c0e9000c81c0014081c1c144000c1d00c47e10341007403c0703040254132801d003640d80782d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 107179388 1250 107178138 107178143
    0x6090311060702060f04021c02030f060106030b030105010807290c010f27060e0f0307082a0307060902060706090303050919170304030203040e01150201060e01031a15060406050304 79
    0x303003200144041e40f02080c024490440716840d0310a0307890320780a0004880c06681000080780400054401594042001890208505000300529030412200900fa6404444440d010ba81010014000102c003c2075500985401c5002041020340c0728040c8890b0b00ca02010300b041040c00090319184064041d04a441080070b6640e0034004840068200352a0940803140c2c0d84100010070001c10000c0c15641011516840b500e040b9400304005105070743c216030250b482210703130700c90000e1200344c13039481112080700150904000042121400c201d06480c3d03c00d648004040542d00c00801c0210340c0c2e00d000307841c2c02c5608001d04200d2607090746409001000240c80c1250b0f148038154840a80b0b40e59900b4140400398402c2c03203401200d6400480500381d80016000710300f540800c2c0004507007882c12840c018002c1500800c05168903101540190844810303400100c500c4c0100c20042c400f040c00b02c0b041c1c14200001170100510355550034040c05042001c0e03210341d03600800002e0001070030303a48400910700890 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 107180638 1250 107179388 107179393
    0x41101030c1409090a112214060307050d3201140d02060331151b0804020102070503010c0504030209090309010e060a0c052d01050106080109020901090306090311 71
    0x41d8040c5041da2000404000703a00104403c0101c1161070412501c1160884c1d0804030102c0d1801040b8172891aa030040c04441c89080003210691172002c00400c8103100070003400d00040d901301c01c24004250030307110050100081c000001b030300d064203e0241e80101c86407100b1030005001c52541580540c1024144a9132075900307079041001246400712526010301a00300107040c106021403990030301c14950002803100d4050715801c04014840d24101c022142d40281a01000e8500984c80c0f52448640d070341c1d0312030510014035042c070320364042100f01c0c07007005001c466042965007030b907813440102e20300500c03500180d8255003400c3c0c03010089600240074106817807003121181d415a0702c903441c250356401082017141c00500304a40d224405d040070002890080b4440c580944a1609512142c0c40d012026180d04251015810f0f92881078060b682042e4489001d440244015458508014024034040c014904850350014013050705030300580c0800c0080d40e200d80244080c125908014012001a520209107030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 107181888 1250 107180638 107180651
    0x1a15180a060f080708070f0f09031401090506010602060403090302041e09060621080a05030403050c0712020103050901180b06030102040306050f07090509280207150f0606020d0c12030b060304110103 87
    0x202d0003403007140c0c4140102d1f541e00740c0c81e030032114041301c81c1c094400ea0001440091423021003c00c62683c205078a9929034000400d00310207074540341d854120145d00540840d00080c0a05c40000c2d8840c4005084a8044402081d940c084006244d90020007060041c100c600c2d00d074601040281c039030071130021101d03620381c2c2c5240d4105481c02e0104000d10301d50018901c203410000901524000c0b4007a5030054009c3c41e1071800c1c0440701841a240c0701594001105010803040040700b19a0301d401481e42c8622050000d0040140d0380c0560916800007402c0203005803912000240640c074254141c5000315006001030145040000b140d4200580030b482180000d2003960001c107950400d02e82c003900421200248802c0000713605041000641c01c3c039103481036103400300307d10700102c0c0c038a04507502c03400d00b1790000007040b6100700d81da0342c1240c00c20307800b00095400452003425070581259500f848140c000301010000000900200c00600300840da480c0e0205021045c0b005101c81d040110302241d40c02e80342000b12 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 107183138 1250 107181888 107181901
    0x171501031d0106082107120309050307050102071203060e0402010e0102031921060f1403070306020a020d030b041a15210108100b090412020a02030105011403011a15180a060f08 77
    0x174020301404048000004201c042c00085816248040c00c1c016072800040c1c9400c01e6035240d003158042c0a007a10f0790f079000700301d140c24402c0e80741d8001c0c8090754600b010003242c0d1410311200c0c0210300051020b41444035100c1402d0310359000303200310303609907001584400f0382612454014201108d4042c034224402415507032606121214441c0d40140c804050701981e10900c0c148075111482102c2400d0b58050241c0400003001401c1c0c1c2c0003070003014585030017a090a5219647c002e007110bc6030f002d864842d07400d201c071584000500203044440e190f425951209100d03c5c0e400c06641d14031500c580800d0180f807161075000c1101c40219851f05a80400702551900c41e44c00404801765816260301562016010300418009400c40d9030909030407a86e4010ba031041c01040e000070382110026444500900041c030384401d030b603240c28031400884000a445442c04c24071410040303069a504010380d03045034100040d2042070380700c20f0014000200300080c00760b4101500e03110000c0c0107551040c2c0c00400b003040c106c0414207 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 107184388 1250 107183138 107183173
    0xa050105010b090f120f0d0503010e07031e0b22140a0e0601141206012c1905060310060306090605070e010c02060f04090504060903020706171501031d010608 69
    0x212200500c03001c09504c0766010041402c10303500001070039100784c5003018414076040c0100c0b65419a00e40b41d2039200e6241c00102624210010694010035180c02c007450560300070488565040c05c5030b4080055140e4812001c44d03020200c5000d58569901c0c042c0c541d20028520f83c110390384110042094030343c80d498800046090b01d002d00f080f0b400581140c2c0060010b02700001c120707500314000070808107182c061055018104003003a0032410b0030108000071580c07444841c4031840341d1070f00c054407510818581180c000300c0d004980b0072583d000f2912000032650700d0740c01308084106003c88880c00c10242d60f0340d1902400808110034215100707820440020003d6001d51807590103020180c4501d80202e13696800c000880d402409403079107560b4140030101d00e502c1c040c850310748507074070640c00000d40c0d4201d820040d140800c1c0b64040c80030400300312105911071510080340c035004800b4690400d00c4205070001070380504641b10311050603007040c1c07040704452001504007600b201c42080584a01c0120758200b0304 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 107185638 1250 107184388 107184397
    0xe040204091b05070b06010c03050909100f06050f0909250201020a1b08030f0402012006060307090b01051c060e0c09040f0203061c050a05070312080c0405010c03050a031d0a050105010b 81
    0x1024000000000b46ca00e5000390380103100345200b490010725002801c0000381c80c281d030590310300d0819140210140b142076003081201018050a003130940c00d01c0c850341d98025003449044050f82c007540c03894010540c5100c1817010000084840c9003400300d00303000680002c2c000d40001182900150031140280030180101410001031900326290620b103a0b206023030182c100102501c224100040781c032007425200381e541c400444107117801018201c581030042c205860a056608400317640c5180c10071400350f0b40e030080c0485030615005c0c648000d10a18000d01d6800604003988a00e07000c540003410021187c1e0010014482c10b5002c4604100000041840804034081221216081900710000e4150007c85143c032003400343c0300b18115482c05c80703659101420012a540200c51902801c0346030080d003234108c080140e20603d1075000b281400c1c54000020022040020b001e014090001511410325120307400c8090820038803120481c880c849181071560f60200000d058545518080011601c42c81500448 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 107186888 1250 107185638 107185643
    0x503030907061704020103052a040e0603060708040f0615260d0914030c0a1401020d0807050403030c1b0b0c07091503060209060c010c02060105090708090703120e040204091b0507 78
    0x540c000c4d580d40d8019801400d0180401c01c07003911410319a44c2100d500d8164003040000c4203095a21a451f0480410707050801901103407280d00110101301d0110307032000070f02e540702d80c103c2828000041d4070b04103800100050000e0341003034044644003050380c866800d1f0403a90a580407554521441d85220a1034940300c2480d541c1c0d00140704500200500b284c0259140c600700c100800740c5422102900024842d5402070b032180300090201c0c402045550307014040002c2149003810403e241d454440d1000b0414416404002c080c40031b49500c042c1440742d040ca0f00080003440038a054074181d100c2510f00c4991b007001e4041c04061280820104034036074280518040c894141102421950641d40c48030040c2d00680d40e000e41106080c441340e140c0742d009000d86a418159500608585e505143c280000c9000013070a0006102c0302500340703c00001e0000703a1604070b0340c00900301004c585005004455002e000e11a56911a00202d0046003030075540c3c1c0481c0c1c010280100745400b6000c0240c1c02c1d1003034010800007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 107188138 1250 107186888 107186927
    0xd06060905040507140904060b03131b06090e04031b03021c02030f0702060906090604060903051203090d0c030201060b071401140721090b0a1a010201110a0315080604050303090706 79
    0xe40b07918005450103032001b0b100003000401c1003902c1c2c108408041d0000c841000521001100e1001440564244842005100107240008900341036020300b104400744a8001c084004400280503d4400c4811424201c10500240341c3c00003070b410000e68444072900d060240f00114402612040d00000c01c481c03465070043c40311420840e098082021070b4114010094120030304111205150b590b441c02000a428151144c5500508506000c2d1900c400d0810f01c503207180c0108103010b20003900140c4085d52030242e1170002240f40c00e41c0780490160078150f2104007ea800412440100010319140c0e4841c2c510141c000c0020300e02042030881c5001094440401140302d07600c0425074100307031491080003220340c500d0209035120144d8858100d00c40464922441540d548820744861150404e43d801c100c000f48001e004003900e3302e4401c00c50748140c00303c0005240e501c0c07039400414070902d95408001d02c000c00035100c20341b03064100640c583e40304950348201d41c0210000401d240e0300514004104034094001d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 107189388 1250 107188138 107188157
    0x601031505010509181315051b090f060301080f0f0a03050912010e060c070209060102070609050f0d0803040804050a0e1603020c010b0d080405100c050303061c06020d06060905040507 80
    0x195225440804c034550003600e4600c1c8030422221140c980c0d40242c80004142c030800710b10381805d86281c03848401000701c503804e0a007800f04400b035090390360050b40349507000a9070310f0b44200c0008401403010300c042d03a0032145c04800040c0500003c04c0c20410356a142e01982e4045050b154504c0c1c48603400724000300440c0c1e09018103246410012260045668400000151454400c910724038248089a0310000c240000a42104504040340f100d0b80010f020700040074040c1c2000300107040d40c07a9a01030b660190001c2000700710039075558403600b510290401d000550741e04190502d0030b650780c0540245400350800d41c60024400c0e9070750341ca441c854040304034405080d100c000d038201d000e944003002e21201e81d07480d92861501640c4178420400700701c3c440e0b01001e136038078039000601140d01c071603520080a000e0ba107181c00021460110031a940702e00103d030f44405003d03400800c101000714061740035000e2440820445800142d42d030111040d512643c449422250f0342d501000141c070401c031075400010b5903180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 107190638 1250 107189388 107189399
    0x6070c0303121817070503130b1306021c050c010902090a0b0f030d0c08090a03050d2a080f25060c0206061c020f13020a05030604150b0f03060103060306020304050a0b06010315 77
    0xc4c0942039052082c0266442c081c0800000800070029030015056030000003480103842425510850040400380007030105241c4440d50100c98114064501d0705101000903110650f0a0a52010505070f5000340704100d94242094080020030171800c195008020f80700243c945464000356201d070804441c0d03500381c00c20016a9030b140c499001000c03172603000048100d001c8000392042c08488503000441c2c3d51142301c58174403450001464140303052107401d2000d0100d07541c00b117212030701180c164028031342a40399500c481e981d140010000d4031010b0500c0e8480e80f0800030400c4842d40044c0c4840449608503495a140d0b0700411950801004290407d181c5440300c174401820510040551118020041007007520440300c00c0090b43d0050b064070002540020800071145498401ea140e507190f00d20545015500f0143d10208610a0203008000c40101100044581c0e10035000900555406042903484c0d041500d016541c401d0100b500320b503501d01c00c07000035406504c6441120348003e109404e800d0002d1404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 107191888 1250 107190638 107190683
    0x10905061504091e0605180304061116170f01050105090604090606090e010c03140f04080f090607030302040501021e1209040905190203070909080405090606070c03031218 75
    0x841c03040d081038a860902c00400d602d04008079100d101041201d0352082545041c0d412114010074041e038141c903500b0480d01814000054505850640c18180045000445050b242849404810f0550040303003501147c81000c0c4100d103260448458112200ca00e0b0f950443e44c2a0340003401103981141c7c0401c006030091500d5000900d055004010015800e80c541481c0020756416121122690303469854441c1103590520031140080520008810749003042220311504000140c4003400c100350114642c0030f159001d4080700c440c02c00c0241026920f00782458060007030b402030b01c201805405420600400d40d404503402c1074011440502130030800010a036010b0484d04440e070207580041d9100421000180208540703010460b11004001e0350500c2481014601034882c1c100c1d1080c0e50400b40b9032800242c40d142910255a803c440062960792a000810500d005182001e03203003000d6040000305060308450b000c1592203d1080c103010805c5c001c0607e10101001500091070040300042c2003e80031040b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 107193138 1250 107191888 107191921
    0x614040b0103140f240904030309021203030103050a120309030c06050901090c0803031006050a080f15030303150a0f050303040b09040e031c150608062202160c050301090506 76
    0x14140007510a81203002e03001c90800c111402c2d40000480414401c10203101c52a0b481e03482c40707005c00d82001200343c60214181500240004041c90b8031003101c4002c42d9107031451b030145c1d02c8140f4100c0381c0320f40e5241013903580d99000007400d03500c080344141302d006401d100f80610209280c00d43c0300c000d06c00c041d5070b40c1c20004040043c4005030656031210f016000500c04403829000780920380080d82c0724103040c2000244c0701e066a001800340402044425800d80d048850590b02c0324614042420507070740c10f44000c1d0410b003246903e6074180400010080404c0307100e08a04a001c2c0e041d61542d0b0050345601c1074a4401c1a64018181d0551051004003d85140355006001c5410f01a0001c07544030b10515281d89546c00c4001002e481422039101424445903501c11108040740021015508505d4941d0250880d940030302120300889400c0003201e21200d141404644500020300d086587e0b01c0002a0740d50a81c540309011201d0f070006103400100b078a8140a40c521a6401c0000340c8010749902c03400d10300d205d02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 107194244 1106 107193138 107193161
    0x30f0b01030501180905030d090b040b18121b0a0305070b13020f060a27050102060108010212060913050a0602030421050405043b0d0201061404 63
    0x4401c0c10f04ea1a9010ba107078006441c210504060f030540c400c44204840781814150300004004002208034425401041d03c20a55100c010500c84a02c0c0c0f540405000d59004888010219400e81c2c01003105008505e8481641103800c1d078410f00388803607100c096020841c003181c6441880f11204005910141500c0100da116a044d4002441d0414115016002d940c02254042e6a5409082040156011000c2444072045000d40c01614103109001b05401401800d000154821050003501d10301071250352300c40b0203590b9290a105204000415008200d5150414103011480034020006094014100583da80c6010300384100e00700f5001c130001c5414011130100586044e403001c10fa5099810454011503044028100c210010f42c8048102804004582008090409000204264450b43e5059801c58080d081059007220b02034460307e21500c43d0001e40580f5890142e010404160 = true := by decide +kernel

theorem cover : BRFrame.Cov 107014388 107194244 := by
  have h0 := BRFrame.cov_init 107014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 107014388 ≤ n) (h2 : n < 107194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
