-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2403
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:36:50.615623+00:00
-- url     : https://prove2.me/submissions/f3732c96-9b1b-44ca-b652-f522ea5e3482

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 432014388 ≤ n < 432194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 432015638 1250 432014388 432014413
    0x24020a24091403132403110403020d0f031101060303050405100905030708160b04060503060907140a020106050307060c081b010b0d030507200a1802090d052404080a03020c 75
    0x50385219a02400c2c401190744044002ca03000d102200c50307200002a010015070950511415406051310355414680020000c2888079169000e02441d00040d42040541140c0740070040600c4121100710300a442e04411602d25241007826640d072400002e00240c818841000a0b04040c0d004c1c04040199007040c40b08252079a01107460a00035911100c0c41e41e015550007521601005010700180021290007803a00e401c0500c058002d110140ca510b00462105000034912840740b07101980348107440d4085d5076111420305c0001c2c040d01a50151038400e0080041c009a4280500b8a00001c20ba00800d418104a4915418400702400818003800c035500c1d508202e8078bd90b60b10f1003050700c0c01d00c01c0d00c45d551180f0603070405400c0b65101d401c000041d80c0e11600c1da91191b944200781041290a4942c0d02201c202caa0490500070740610100e007600951101b040c082000170200720003814031480c0d4400100012004554500780c5000d03200981410130400c900e0b00994400c0d00105161070640c02140c078243c00c0032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 432016888 1250 432015638 432015653
    0x501050f06160b04050304030b07052b0f05101404090506040b040c051915030603150f140408190c030c03081302091603060b120a0b12010624020a2409 66
    0xf1181285c80e5040020140200301c3c100c2011900204e0f5440c109090415a1154220110041085081020101c001098050110f0b00999184d840c0c0603428400e40c00d003503024540c0e610306402607a10400a01d0303010055400c20703110380301c540c64104004000300e0f1a0742c0c8840d04200b002410030b4501d0344e0246808034250321903071402c00414414491030015180f400900c4000d090016003a40201410210100045042c00969001c41040d0702c0000412010921035000280740741c020140314219000104820b0020500c0a08400301440c1c440004e90944901e0460b80c0d600c0c610310080225040c0c50044011910030a1203d604c03c2c008001c5003045130300f0383c0001c2d096406c12102e0310f201d02641ea0500d0f50b581d600d802210700034440200c0c108d00b05583c0680f0300040000090007400443e0303440f4a030850558500d8800748680303804200030480c40761100000c580700344660850402c40e6441d01d010942d02da100044803c0e032540c1040d0007496200445200c98092403d0300503910303c064640b080305e404104032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 432018138 1250 432016888 432016891
    0xc14030307120501050f28090603080a0906050f070f23010504050f070303091502030f1c0b0d0f030311130e1605040b0a05130f08060402130501050f06160b 68
    0x1500e801c8800c41c2e41d59441015604140c100f2030291800c004a074135580c0344c0701c1081340094050a00303030310000032109660b8105246540702c00030340d906040001050100d03c0c0c2c001c003007801c015551010011b0726050192980d10600000034881354042103144081003c6500e0a00140c1c13180541f9082c448011a11001d0051100800101650f46000388020001704100c1000d03002c0400014020061460b10054a005003920501e50140850050317041058420b0003140c903c00500d083c00340d02e840c00b8000191b92604d0604c803136a1000d1501c900c445c42841d00710100d4090720340c49850101444900c1c0d80032000f4115201203060444401d0107581d44050040d000c2001030201c03007004a0030343c60700c0040da9414402d0046007009100d01048140035038403905048548500313240c103201d0380d1180130340059980110305500c4003032441c06081c1d0101d4040720100d07025005900071540240c200d0021013048040310001c0c031900703031701c1419511580c1b076504040010b030428440d20400300e01303941005d498080c01d510b030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 432019388 1250 432018138 432018151
    0x1808070201170f0a0b301615180302150d11030127140105240307050a0f0e060406030b01050708033c040b04260405040f020906030103030c140303 64
    0x10302c004004c1600c03078070b1240205a81003100e5540b9483e940d030141c1e02401c00720501c9100074081d12900162100c038100000d017a60741080ca0461409035480c100c4c805e124841d014207200007041d806a15994920065444007545d40003001044801c03040d507005003d562080812101c1d0545034014031119120b59000b55000308460b106e15411312198030000101c0c141075840000210389411004c103100c2e1803848a890554405a683c0308912000004502003900c0068401d18a45000801c226160742d22002a1180c2842030301c400759102c4849105981540750080b41d6600103406000420500d8406d80200e0701101d01030418a1070524551200d455942c812686061180100d0914008500d440d001e44100380110100010321500411061980828041c1003e410560108003140a11100305c0342c0740f51792410031500094404c000401400d080e08180701e01d9101d5841e00c80003840030052402240c000c500f00a000b20300e107a0850343d003914501040c01054402c00024400110001810001503010740c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 432020638 1250 432019388 432019411
    0x60c030801121407080c27010e0613021c052512110d060503060129031e040302150a02070b01180b091504061a0a080a0e07030b0901050703180807020117 67
    0x5402c00030b00080c0241c100101c40040b9151484040d11103414524505592844270010380e940c9611002441d8815125181c10700745100040f03039411000d451110038105018001c007070059503182d0240800000f2150301c0071078a4082100d494006900c600c0d0b060569600d03a66001508910003000d030304054100000078a81e240d0303101000d01091804010f4a40144110b040303c200120111400c0303400c540017400103007010715005c0049002090b5545078030004e000303524000c807560710313150600a598200d25105110100c12107404514045c1c983d000700c0d1b5070260046050070459103414480401c1070949040b55040c42e07a254005126691501440c0d80a00e43c103510281e0340344c101e141000704a07400c95004003552480021040e8110a402040c0e038001d1a950506072555a901540c04000e002c0514440181e8064607a02004005900c2e40c8540508481c3c8004c0000d542c60807030a07403c503a0000e008007500d9087d548a000000e19a00003080124418540000494454000101400402d03035039500442d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 432021888 1250 432020638 432020653
    0x303051c02160b0405070506270108100501200303040b0a0c1805060702010306090204080d02010b0d02030c060f0705030a030b010e0a051c0f082101060c03080112140708 74
    0x1050324000d940c0c21510030030001c40c80d103004201500155400410010f141d06015030004d42480710a01c00b0b0b000424010703003032a98440c142d80c2c0300c1c2002400c0c004000c3c56825030007442c0c9401d5204806641c419060103008006250901c00103491001071141d500c980d540c100c01c002018140d090010b58000c81c8180000c11050400000c07000503a281c0403200c2c01007164900c00321400800800c03180044030b03010388059a030392500b0700048000c0d02080e0480d000c0b050002500084000000810410180080d4020000801c002e42040030034100148040d6040c0e004501c104100d1901100502d0041e11203040545031042a0303a4490031500180c00c030601003554be030500706d40c958002e51003d40f06102110805910b030b007408001092440024000000c4441010144041100320481d05205c0c90300300724007a03166401401001c0c4a11002c004054540070004000920309014800720100d00c0d030705841700a050781c24203a4041d04a450020150f0b943c1081020120f1b034001c0038811800900350b41d2020300400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 432023138 1250 432021888 432021907
    0x2030a06090b1e1b0c010e0601060e060c030a050c250302130c080f0615040e07030b15040501032307080a1104081f02120c0903100b030c1002070f030305 67
    0x55050060088a5404080441c008030740804020558031044206131000c0b102c0b0464040140e50040b035641c07415540c64902c2c1507840410000d20a812039225a45841094199000340440c0b4000c5030117852150b48103000d450706850050010b00000079040c0110381d04585440c14200400c48800da81c0070f107000780c810051040d0b00340101078502c040c82c007050500040c1000000203008980081c40d01c1d0181c202500403801d550780702805600c043d02c1010713180d6100d64444180c111b100c2030545151000c645022801030081c1400b01c40340c80b0f00c6502c59016400e003450180150043e0150360b41800200000420940f5400c203643c1d203030b6000f001c007030313903001040d00d0580040421508490b0400600c1003043c4820014901e0004014040314501601268114520001038010340240c5070110a550746440411002140707800241401c8030b411411035000e01e1402590004541040c082d0700e8060f00005000812800e1014200026290910442c1c003001e9131108210401c54003074000306c001480008a0303551 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 432024388 1250 432023138 432023153
    0xc0c0b040806010e040b061219060608100608070b07300305180706050c07080706050c0c1009030807110405072f030306090403020f03030a020a230906070203070302030a0609 76
    0x34022004013140709080648490181641c0184458401d4024404100000000b440441f05130010240850108110303441c0c9100500f0150188958601c90118080301d8400c01e03004080c21100c03444003520001d03040110321881e0390301400003600d03459085400a480c00148003403613007844045405003102510004001015103030080d108502e41d43c0c4c400001c840840d00400c41c00112501070600741c0d56403000030411030504080d5400040c00340907103007001800c2c542100050001c2e0100c02c041d00c85400705542001059000c1e40c550720009070f1201024000208050300502406000e212004003080030340c0e0016040d500125010b00000300c101e983c00340c0d9100d006080b0465404411040c2000c1451102001c0e681d0000030005071240c0401800304041c1070003403103044100003450040d03d9883c5170a8a010300a0f50089208000244a03580c0f18a24850880b0b1480c03100c110fa440614984240720040100769044184180d030f040c0503807200000180d90410488102ea480f551000c01e0203c2503040012 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 432025638 1250 432024388 432024391
    0xd031a010c020303041415161401060605030a0c05280908060417070312060b0415081306150806040f0c0b030f060d0633080c060d05070c0c0b040806 65
    0x5040c0003420303807800016600401541c00340c0c1c03601e032120380d40c22180f103000a420b12000210f0720050400050401c81e46d548441026010074050003866130760b04568601d9034200c0d500351090000082c4103101041c41000e054001080c184107514000d0301b000700d500907071b1800c00703008102c644020458018074243c0a802010f00c1c0300605451001e8086454070b030312030800840c0101c80e8501407101c0003503000200b5009400c0801c800f80103000030003403241c83d095416000d9200d40155401088000c0000c0400f500c0303010303010301c100b140700b00c0b15030100343c980d40c0c00740640400800359450003d851004a40a44104212403040e400b81c50f040e603000c0e0084c1414a0326602540082644030001c0040090313101c0d41c4140705802c0441640c042160f100c0a00b8200001d00040c40f034201e00d07600808000420210740c2d00c2c0b001c05a050707101c50542c8a40d03145c7c0c21643e41c150310074000750403030030500c0300d210f0312982ea03405075905c1001030804507864541e070b50340d01d4001040c6e034002803491f640c0400c051241d40001c00c5180d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 432026888 1250 432025638 432025691
    0x801050114040b0403021306030803191535100906061a0a080903090607030f1d0d0615050a181404020d20090a0903032703200d03 57
    0xe07207024206a00f010f440c3c0301c0c03030101900500306244035032204c0d00d15030301200095400110444d1a030a09104112520114000780c540040c103003d20030400c0b1002d01d88070004ca88600d05954598070f118050301c40c5980c1c00f00c02c54003090344271038042100403605000011807403070303e0700380060554410700d800d10464416030800050044070040000b281d40e80300040751120082741c10440c669a88110300a0303c2c40c811000d20981040c404509007040541082d2000d4004e80c69807141c45168404181000c4916540d41845d5480031200815101160b950f60040c50400041031045a0740c40d00c0d840410540200e6034006004010b2003001c94404402e680700304160180055418550f0342000e400240c000d2810001c0940340754408000340d0072120f041c0000020202019040d8807131454124080344c001c2901e0704c0103801190170f0000400b8140c0b8047c0104a81803850609001c0034021502c0854a030303c4100300c0340b6951039403040c81d0f1074100c90401a11000034071542c2c02103480c3c505c5401c038010099001059 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 432028138 1250 432026888 432026927
    0x50108090a080f1303020a1d06041e0908130e04030f03050606030103080d02130314010c031b081b0d0507090501030b010207060302030601180315110304030c06180204050708010501 79
    0x71500060540c4085804202c08101d11035181c4030b60a4400540d0145944000d601c640805030004000300b543c00207002d5098028003030070fa1030365410b0038002928a06d1000201594280c140f040c0c01c0000750b405540d2190081035a14148030150300038418228054110b003100b003c00b14100800c02d0b0348005100d0000c10180740501c0541051f6001c20701a00040c0030041941002098041c02e5131210b40c19503520040950043c10304c2580c0b4104038002d0503c1c1e08072060107500b000f80405a89000b0f00903990030107150445104001e80c41801142c00a0b0090b254a07881110607843d800410154009807042c54003410000a050405110251021002d03900c01c034140760401c03169041580c0c0101d40344084860508025170380c0c0d503884004a600721084803484d000c40d0001c4c0c20100a00c408412681c916050030b442c10000055028201d5000b8003007260020000b0700ca40c45040000b411a07001120080b661000c60b5016203190750001e03003942d0040f1074401c0003d40141c010030007507902c4984200350440103a40c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 432029388 1250 432028138 432028153
    0xb070207030507062001180501060f0e0c130f081b010f020303130c12052103060d06020706140705090103110306010c080906040b07080309070e0f180a080a030605010809 74
    0x3034554458240d03200c0e0f42c2c18002e2040b0069506802056442d400c2020100200080e1f034561588408a42886809640561a00c2004500d90940441d44425550359070840c1d8031b10303030385c4090074a036550103003034854001d5000f07000c000358001e40720840001401405000c0d00a02040b140110904940c0e450303482d041264810307284415507008011070780c102714101200401c40e00a41000700400d1542e41c00901c01c080080e00740c406000000c5420b144e4075084c003d910318240d094009070001c502081e03a02991012844040c0000236030b690340104030440c0f00341e402213808440650140060b1f10102c6400c03002c51030000ba02c140740c3d030781446040700c803010b4140198214203003c0002024640d503600002c0c10110001440e04480da941c40039500280741e200d203883c0d030f01e840768900541e4503081034803c54070301e100c2e01c400403880b07110b200440ba10038407804484510300c1c0d07503408400c101c0081c0703150300345041d00a00703811201003400ca40040c42410b4540d140071030340c00e140000060051000800340003e0340c00c5501d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 432030638 1250 432029388 432029393
    0x3030406051206041b200f0c040f0501060203040b07050f0a060b0420090409170c1c0801060e090406020702150301080c0d12080c0d0501230d020a0519080313030b07020703 75
    0x400c001d40d4078601e061003030303140c25440c25074030781c000b400c1300c40010b2184810a5187c0000001c21101c0d1070804e5901381f254164508041c0103030303003080c081c503405a04103100c1444681040400384c12070728002c404841441e801a60168249075002400341c80d15600d912841041c0d0801b0b0141c44c18507c110460700c0203400110802ca0b9581c01800186403240c3d869103900c0052180c02c020047c545504658803e80d542c03800310034955a40d0244016000d00c040c004001c24500d8061082d00d0b04a904a07103031110380100000801c00e012030002d008072a560f80c244224405a200c1c8a080c03003508c241d100700c6a030b895041074100c40c0741110f24404503102d203a600521100284101401c0da07808842c500f0040c140340c0310402e00241b80d000d80c507000030340640340500001d05440e0866100c03c41108109060702002e0046062086c081551140650415040d400801103170034a80e455500701100c85860142c00303500d40d02e44905590082080d620710500d03071401070040c40b151009103608422030740001c08070a86143d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 432031888 1250 432030638 432030671
    0x1816140306091b09030111030604050f040b0106080a020f0a0c02010306230d0201090302030a060b150c3406050705060109020702090109050a0f051e0703060f0504090c03020303040605120604 83
    0x100142d00152003c00380050742021141602d2503100e006009004440800c0003009186d041200d64502c950b05100c041040407200d04540350140d81c000f50310200f160301b08241512000350103401e408125908003d0000c030003000d000601200b50181e070704d00c030301c504c0240001019a10745401039007890381e064a6201d145d41d201086005401e10036103820315548841e00060391140581d40c00a034060040103254801c002e441c1d40035010346101165551294030007070284c40540d00984003c6155a480020f182201081808400c88000e0380d908499041c500e4001030307402d481c1d68540c0050b0200e0303004100c3d64204182071192501600503d0383c09c40c108216500051440741040c4907250f038042e62800416000861a0001d8510b00041c42041c40f0a0400b039a12188101e028489204405401400318855501c41d00407901200d40318001d80d03000d02e00b407108000003000c0000301180c4240740c1000000050300c0c240302900041c4459212184c884404803039840704000c0c000c0030b1a00c21850280681d1841c07802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 432033138 1250 432031888 432031891
    0x4030305090d090611011401062601120f05071509261207030c1707030305060910090b0d0c03060b0a08010b090403050901051201090f0b040e150402181614030609 71
    0x15140c034040c5c10080c02e01042c01081441c00342c0480304011000418440d802042400240c07544140001c815522a054801522000e0150702c90245500e600320021030803107028070040a0203170041d40d100300e6030703074141c08111020440a0004103c48075001c100090300703c0346040416070606407200c0b2500c1c007410031584900030769a5810100b88041040d80034503101c2d44007807111940c812181085c041203009000541d81019408400080c00c080c00552203007050541c580c0500580d0380350a040504014085020b8545010f205420a900c01e01d000082030a03900024001c0d8084e0307100203070710f00c441d40c14000010007d4001700c6540e0704100f202612030722401c3c44594051341507c1c00c240c803141c070440100c515108800220080f4001c1200102d2106019440040304245920b02040103003407000500c82a5010000000000d0b00501e040c8c4504400b10003c0340c0c0c0c00761000301032440080410825a40c44a0b0640702d0f440c4041c0f4840c00f400c100b9404c0b00406410320b071600c008904514000c40051400d080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 432034388 1250 432033138 432033149
    0x711010e0c0114040f03030504050f010c2409020301020d0516090b070b070c0f0b060a1e03080906070203030408010b130207050d0f05190804060b1002060705030601050d060e04030305090d09 83
    0x1541c146459400c0c915100b950098410175020958450341c0e07040003840340e041401050b101341030005d10ba55096004590007410b042e84103001007000c10b540c009500e0300f4803403030412a2580307441c2c0a9520069400f0b100800040c00c400d0000140d60914094141118043c25500800c1c42845a018040c450007101512500c6900144182a560340c1e5882126240d81c8a0030051060349206900301c10040300364600341c410403040d01c10000103a502c403161504e11203042000c4202e5034040d1000d101061480c0c0040c138455901400c0c1d20b03d81120341d0f0100e851903101c1e40c4410300e140d540398103204070f17480d058603c170b85000400ca0080d81440000c3d1500e0b61500301d00b0b54200c0134005d142a503100c80034000c500380c42e00b80140c20b0885030348411102c0040e0101004403412a61a4503000510b96503142450034180f80404580c0101041c0c2e403007150a0ba2264009800981171040c14880c9036265225800f481c4064100503194201d107040c00d19015040c0d92001d0403a503030719002505410361503988101032038111034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 432035638 1250 432034388 432034397
    0xd0501080c0303180f0a08030721170c07080c060907051f0806030a15020909060d0309032d0f150501050f0d020402040905011e150e120f01140711010e0c01 68
    0x2038410000510320b40e82c0c5c656058001841003c0000c5006000c03010380581c0c0e024620540c9848141e504050203419807180a00200368601400301e41066500f18007a070008800d002185001c5098070b465140d40c00030801c1c1895036200d24100716100105004d01c500504017514004503003d20300365480003011158215108000c075800009100355030820681c2c0746a0f40200e4446500640070382c10780c010354014494103008150b0b500200d0380b1400c060024441068256450103605421a5168503802c00030f00c0c00e040303605038034907241c030001c451805540c5001d41c400c03404e0b84822200c914045000e07415417491541d403140791a0041042c0d80b18032400c0b62080c030085038501400c45861001030024003a680090000300d281c040081840a241030350b151707000700400420105243d4402c944031300d2071001a94400003480d102280d03006400e14600418081e80b118044d100d00c0c860841c0c0040c01c40b4500b59500c89000071060910035815006100e507031611030301d007009010400b000c030610741c1c1d1010038110035030421 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 432036888 1250 432035638 432035677
    0x711010f081302040c1205040809040c0c0c060516121211090a030b0714071103160305070b07080c0a1a0612070e040218070801064d010906020d0501080c0303 69
    0x6032041c00c8020340c40921b40301c01c12082c1414204103101d604032400c114005c81c6410038a2a400c0e0188818282543c0c1c41171000781c40c1340c2402000c80c0c0f06d402002d184140b1341041c2105000040c501001100000c2c05591451004442496a10180c40004030800c664038030400c42c554258a42000c2e110949800000b00760b915165007000b00c8814410300d500501600c2d0101e0342d03108010000880081600c804c8080b03e80490040d055460904c509210090443c1e101e4078041142c65186805040694008c811450501c40b6016009090991000040b2119040e0042e41502d0700108884241c01030301c01e031601446c5005203000642c0ea11544d0044039101651500058115642e8503500341c4c0c240c8164003a900701f4145a10040e00d140428003400020402c0070b44044500005484400700c8005d8001815842d02441209609480b0510740317011807205004410721554442401080c405511811340142e8400014103160300f01c2d081178000b4038813600881d101c0c654039507001083e01c4000700c0101020848 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 432038138 1250 432036888 432036911
    0x6160f050a0303050a3c06080304030c21030320030103031205010918030c02040f0e0f010e01020a09030305090301111801020f0c0f1e090103060203041209031e14030711010f08130204 80
    0x4088004006d200300f9043c1200880c101e0400b0000d00122445647d11849a0f41c544000d114080d00e03040080e042c141c2003211080110380f03c0c1e044a000c03011104444120180c6480c44142158001d80050b40410f401850800c2c56843c140b060070700409000904000c00c1d12031200c80885898400c4000d41005a40900303c025951964006480c2900c5076108107c42508101c0140c3c4640040f1400082c6501e881d08803040540180200d070702541c501d13070b1200d80007401c6950680fa241c1280c0314440d050366980f960a20340c610502c00400d44a40742468000074299120002460b00b41c42c1c8072010b145130807110680c2013a440b0401c1090f110703c421290200c41d4032145921040045044400540c0100070300000000c1c880c05a004501030360280c0140a038400340d4240544056085200c02001c0c1e03691522a4902e1400c002c080e641440d10440e62628080d4111320300d03920755040581c096880b500c6c065504075040da0040000c100c0c021031402c1030421032600c14280326189200d00c1019000300d40300c00380101c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 432039388 1250 432038138 432038231
    0xb0f0f101404061e0312110712051e011a010c17030606071505040c080a0c05010503191b02010c02150a0c2a12031a06160f050a0303050a 60
    0x140565071513098400c1ca01d81211080940c080c40141c600400081103520342d240b01da000054158100001007007400e01e08500c02881c6c4505801c01c0e50b450048400040b000d00f040c124004038001c0da2000881c951000b50001c48242d1001c100d25070601411807005000281c1820101400000703a108454680d5a06800710758640b2680318000d00603401d0300d41082199240750f011a025500410480e801d60361918a043d5540c0707252507010308541c81000b020811984128011944000745800121002021301500c4060700c3c2804401c3c00d12108003450210346540c248588141403d60388010040c1030310549070050408000b03030071082a1278964018824641c000c000e0955458036100b41c080024101041c00e0000301001c0f2811120303420754080702c1522501c24020030750640110071a0407030202004d0704015541d4086001d0210358402003900c0ca010695142c1840207103802030b005090551f0131490001d04403600200301e02d403034919002503110154107420181700e1000301509606000043c0f1540c010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 432040638 1250 432039388 432039401
    0xc0c150513051e07090c21060513050f07090e13050102070b010e04110303211b030f09190b0105010f0201060e090109020310020a23090d0b0f0f101404 66
    0x10300e607200b220a12007220644600f0701c0000116107040d0703030166803600110030036540c0c0d5000410001c4c51101440800ba449165070000c1e6501c22040001c1040d034400100740104540094416101c1d61441008550010490059030064062818845107400d200d49d016190901a20781058640090038072001c0100c2503045034541c40d0081000c032225a518401074410000c121011070b8400565501ca000b0350400000381d540051050b0003a104841204540c10a6508014042d40505010050094600c2c0c6000300441c0100d0f5951540411403070001c408030b1814440000d01700106103000f004c500821104040e160664400b444c084600c0016440104d0150685030880200d44254a00f840355028055000081440c0700342c00b40d034071032124030010004900864049034041841403500400e0b070105125091280c210703840d402414003080401049880c009203604950f801113000520202c140c0711a0225400b60140300d1801a5103441d00c101c00c0c044d00c103842211000c9034148806034190b80c0f6a00f080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 432041888 1250 432040638 432040643
    0xa0314070c030b06210706051e0a0302070b15061b0f07170d0908030d0207030c05011103010f150c111c0f1106160b10030221010c0c150513 61
    0x10705009489041900c0c20a8007030f0341c080d10500036000791001d50b1403040c480445000114011b4501140740100c1074465074001400c55030000785001041e5140302e188000b5021100160b6001a101c495038a810a9505c00c041c0040c00003031140040703060655140070445200c3c000c880146000300d201c0e164068a41981419100080d004203080420705050000000e40445902c0b82102c000000310741d000c2d90b4402c00d0f80900c6031283c004003c3c52955008a400620701d9510034a08003102100e00c0d00d401d07003120004142c2c000c00340307000001004007940d40b00c2810041e100d403402d400504661480c001e8020110410020070b2907107803502543c401e6840c07400d100180d411186201407403040f82c2c07034030004503003007039800b240d21940c08080f0019508040d01a030b071f501107648040b041030500c03d0701e03010710001c0001d0080c0c40f500e0304400301200580f01c40d01071060403e140790b0314040d44003001801c5400d442c00e048040040145481c10030307010883d992800a81c0c3d821a09000445407070b0a01c180c0319290000901 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 432043138 1250 432041888 432041903
    0x9090c05120a060506061809040c08030a05030613110a030b0a0b07050c040c0e09070305090c0409030513290309012c0706090f030602030709050a150201051302030a031407 75
    0xc0040814142c1e1010700c9081e040250340d60f00c0d0104202030107002803039010420a41c12000d0b681c20664003664105005030340546440d0f995580440c0745500101d0000001b440c0072040c02403c0c2030019024002600c200c5090105040a05004007075009480c42c3c4c00400d81c845401da051529001c0c8000040c02d00400072541d105800e0030a10f58888031800d000340500c0c0307002042000c103849003c540792900802802602141c498040c00c0740a800060000c017480e000f80c000596a650302c0d0701c0345500042c4251030786620b900b0030682c00203c2d0790007a03104402111032115032491003061003044403020502800b955841c0e0311f6400e102c600611010889915203000600282440746401c0000e2100510210848580503241d00301242c00d49018801c000710103041d1f1100f400040c01c1500034641c00201403030103005540c0c6d100c0028000c1fa01590040000324880b40880d0495503082c010030381e202c0541403035003542014070f44c0420b980f200d640c040a01001400c00194003d803103e01c0840e550903420400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 432044388 1250 432043138 432043159
    0x1303180303300e160f06020c090403090e1e1008030a050a17010b041802070809270a0606030b1509040908040306020c0622120f09090906020405040c05040b0409090c05 73
    0x26641d81c4008203000720215a0f5041400a03da05801c42d0360421b480044d4040e08010b5401310911501540180084041c015181d101245c0451020f000700d200b50420003104514807070b0102000c0362000042d00d856907190b02090148890307a000030864540e004145480c55440d00c260f0300490750318111090390a1300700210400087c1584045000d001a030710503d23245640c43e011140080c04910034400d00a0104400380700c2c807041490444c402d0344203401181402010341c1030290140b19558000c640f0455030aa60b00c6060100c69854450301d0112101960303501c2200c85a1540819036001c1d024403544681c0c1c441d02c3c0b45040090842c00d0ba4000d5502c243e05649807201c1441d599110a0f08440072103811036000014680c08a14201d1241003a40101070180342c40c0c14448103c8200084c0c41c2c00b1400e11030030a10002c0c11803603a100b0f01c02c05900401c001070b1503e003403404000595040d034692200700481840180400b07482c141c111801c9a1100703100103012030442c6414001101d0a500459004101c00e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 432045638 1250 432044388 432044411
    0x30c0105090a02040c0801060909052805090f0726070f1d060901180905071a091005031015020703080a110d030e0d120e06130318030330 60
    0x140104542e03200f1141800040d480c44030403200350100348100800944524030801001b0301552149800c62102401c80e4001400e401050403286c2030031081e400883c0d070300c17030400840310014006488414445000f41ca09289041038001001400409407050000300080480401900b001520003d024500e55081c101d6a16400d6185000501c1c0380134106034042000141d1606d031020900d416515544220f5102c54000c941d44402080c958404981c03031320402e040418495880e80350591f1145480c4030007030355200c101d0f05010000c0815101e46040c00340c1403050001104082c0800c0065800030345404102c0280c00e5000c0b860031589920103000c02c1000107215040700e9203d092407611500780d0084505a01d0803110440440d490040341442d01e4004684d42800c19104204080240f0700a06000c00c804112407801420148140e64552200e403e40c0b4120042542101c0c0d4208804a0040c040300710a1071a10094462014940b0501580c1c0b2000302504984000c55803070300280072482002c00800036400c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 432046888 1250 432045638 432045643
    0x30b090a0302060c12150a080304170118020d120c0f0602030f070207050f0103200d0506011103120609060102030c010501060201241503050601050403150621030c02060903030c010509 80
    0x26281500140904030018244a00e014116011404005d25100d82d55940452242140d080d0200c443d5004a4160001405203403c0000d00003828554800c041d5030220000681d0859444a182c040724005e488400800b50307841040c0c01050f0398010051003140b8080800803603149802c1071000304807c0754400c1c3c80040c000c07035134081c40c404c1008420000d02619440030990781d13920288990341d4000200030314003406510940003030542c0720b00301c2046200e48512141d03142e50354110031950160942e071102008a59a0310010482c058045540550718000041c0541090303139100a090901400e040000700384564400c00c121001071a948000f04007030b585030080207000c0c16400101c050341c0c1c43c0c0c01ca085000210030406040c2110304410b040013905c815039400390082e101c002d0a440c1480790a08c0004013183e135808814080442c4a41e000130154104030030044980034849a441c0c03142a42016100000d400c5201c1c122410340450f042600d449540f40000d2441c0300380304500341c4650030003080c0800072000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 432048138 1250 432046888 432046903
    0x18020913060606050a1218170d02030108033604020a1e0207050a1a0d0f02040f0806010302190e132a0e07050a020601140a030b07120f0203100303050c0106030b09 71
    0x741d95920103402420010000d440307d424018920540d181e40210000b201c020840900b9040340d108141000d448204240480c0c209038403a64068200140c0c640c220103002e54020313803010020440c2058080742c9900200205c0303401028900984d400618403050354001d98040800c0039400d28800600c0404440003503d4140742e01c10b5a018405130100494508003a130309110750422207241d100e080c05c00c2651100040e0032040f5503100096401c0001148002507906503030081c004203070040416515610602a44001980081804010a06092290f07841e1041c00c540c010300d03807401000c1e21001d6400c0640f806040c01d582d00c1c0720405100c581c00c416038005901c55040703607844802500a90794400090b600e505c610140d00c4016044980107120b500d0081001402c01103019003040300c05600c0340c0c0d0f6100350660a4418101140024100301ca4014080c041c0000700000d800e030542c15400c041ca14113041c040315000060500c800414420b4440d58254800700085030420030b110002d060900c11113407607001c1d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 432049388 1250 432048138 432048157
    0x614040504180b060103020315011d0a03030f0e01081e04171603090b09281503060e1303090620060705250b01050f040207060e030a02010c031802091306060605 70
    0x12000031307040303600034800c1d00c5c4920800000c5020f2014404c5c011626055050b03901c05040340e007040c0000d1b460b212840792101451190b25600001010001e0241404008245650421409004020600c0801007004522107105a004c011700e881d64038000d03401110350084400b8189c404508451002c4010b010380c070441c1e009031910048141c940d07496810911400e072159400c40c80c195034080d45400510741010030888100c80c1407120a460f010b241003168554a0007900090321181d042c0000900c1000c0241c102c1480d95001003222015900030344040511312440080c4a81ca0004c102940c90805813848950301c0c84050320f0b0f81d80707802240a46141c0001411a9100340e401070002c5100b00d90030f40085c030894000c00204035980ca0310b07081205901044104540041d02805030100103241402000041100d00001d1525490f0140d4000d0840e14148110420141841940c10703c01e401400300a482c0c503015a20340b12150f584100e100d0030070042c1c40d0011312581c604030000540c2c59110014260120 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 432050638 1250 432049388 432049403
    0x27070611010501051e031513020f0306070c1209050a080109061d060c09060706050a05061f05180102010b1e01031506020d120e0a0f05070905010609061404050418 71
    0x100d08011a0700700c40c02400f50a801c50800b034030381c19070355a80c0002008010001411900120750416200440d00c00c00c2d100390311140041d11041c42103291240c9402600300c0c00b038000f0102803801e09030080c9010903c25020305015001240e03040c24600c80c465003c00391801408448907944ea40160500802d8000410b84940b4540300504651007806155030720450a481c00601407503e030040403c01552010f03030116403010301004030000040741406128480c141c0c040c4c0008441c5480001d002802c1c4540840107942c480c41040401c02ca40c01a098030f08804003917022a84000030940180e0041a11584079540164500641449800c0140881c81486800e0741c06010103410301248010402c854059200542c012801c00e8000c684145411103012500410204403000440b60503802d00407500da0079144440c0030781d4040c3c14170804004400040c041080208500d41c5048401820304846004074801c00180c0c58401242d852020306a034003800009208200c00800e8242181d8800b40c0c1ea03000700c9800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 432051888 1250 432050638 432050657
    0xb12100801020903030f0903010f050f060a271a060f0301150311090607030c14070618270f0f05180a12030905011401080a05060114030304050108270706 67
    0x10360040c002d0380d10100001d4001c0d8145a02040041425000f1860040d059962140c1c002c00c041803900515001e91900084600c00307040120907c00316803036540061034219100410b9250680094070101c0060041820000e1100d078520014068111400c4402d54000300200f0082d0790100c11000850403100c8800c1c0c1c0c8680c02200800a030180c5010502002c464071040c854502241040c4008001203442850b0040c2c42d20034a5950150400721100c000c02594045c4109000d15904940b100c645d45e8980000034609500d4158174440b4941d6a01d034020030b51640e142c00b400304000640107040a00000c6100388028409401c00314014641158a0030825100040c20070b1006c401150323000c4d070a03401032080000c0251902040e00a045140f00c101c0707054ad80c1f4000d1035901c00310700300303500c0c041e204046c00f40c200c181e801e003422845c1c0304040c1c0120031b421114408807101c540d000070854040b01c0080c207103092a030f6107451001d414207407885c01000307a460f40b00310100d9080790081001001c0d1030300364031180743c83c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 432053138 1250 432051888 432051899
    0x60d021e0a1106040201080f061c030e040c14040303030209012d08061e060903030d020304050303010e0c040803071b1d070f023004080d03020414010e01050d0b01090b1210 75
    0x102c28051314080d000c94100e4012a880141c800180e6030310040290010f4048042100980700045083c401030f070004a49003665440c500d428002c4604800040c581503101c400350301309003d0035104905c8014141503002480c8032903a4010016040458410207000300c4020410303c0d490962591110684001002c070750008055191070074001030103400c088500c0d0307501d403480c105003c1d10f40d2081c451181c1c14030081c051540140d465000440c0301c0c40c8900007568a07949032407140503003c0005400407441c85024031081c020581c00109039024540c0082402892585100c141038140001750091000c200307401d240c1c10350300d2203206a401c0c09200c0c0340e541c200c0c4042009c44100e07104c410a03400d030303800030706010042c8404e2003401c07210000c00781e44607043c640340c981e948038081d10381b503070303020382c21010a030003280070050440030300d07080c94a1001c217007881d85100f181040000c2c640d00c1400191100c0f941e881e209444103910441010002d04401d80c0c0c0e903541c41c03c070720b00514102d800485059888101900e1b01154 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 432054388 1250 432053138 432053143
    0x2360a02190f02030702041a0d050c120a02030d0810030b090c12210c011b08010311040903050a0507060608030a030b04050610052b0f06080105130b06060d021e0a11 72
    0x42c603a80341d07020b10708254003982080f001c1c101c62202e43d006c00c1c0c8103009150036586c41046551903d8400d0005100a9000c10140070035850341e44540707052a00018070030b40168402281c1050100309034a021642c6a07107800c0d61003003e030521b400c00340c2003916010810410040001d0011511102201c0300110003800214407569902b0308c0b0116200740e02701c0400c0c1d0000c580020042d01414003540c0001c01e00b44036039004030312404c104032408400903000303a00400a0015401d00081c0c10300e000e840601090442c0d41700a0103903c104103015007046400200401806103540c01031025003071107020b5076615041284001d015090600c606441646007002190701840c0010400b82c940f80d06440380da0500700700c0711550016020280c0b0351440ea10400d12040b01e803c406200f421104002048000790041c00c000005007140c500500d4114040301020a98000c10046003c1a92203002121420b90390811010010042d00580d02200902e640c40e01101811205180240c403402d400c40d501c844400070364803816607 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 432055638 1250 432054388 432054407
    0x1a0717190306091a031b1305090105060a080102030f16120504050303060a0b120c0f0c0106030813060216090c050c01050c0403020f01020613020108040215160c060201020702360a0219 80
    0x280c1c1503000e240f07041c13401c0c03411b42e03102000f80d0802403109800d1154003c401d0141c85048951401c030780d55810800829141c4601c0b0f000140030201c00840c2141b51603060404581c101901c4c003100844c0c2c401c0d008002c288113050501d60340c01210410311042c10310340790165a0f90019943d4038424054018003081e11a0a6415501080c0303030442079100f9519040d20f907080c580d001c000c8021a4810400000020b074000340601801075200f202c105a03a80c0c90440c5007820151240c11040454000400111141c03600340480019100c1140d80011100030501e404d4900f886000c0c801c0e0800c0d401c4c00200a0901c4008001d003040728003d590048441c0000c100498854008071904c0f0f0103000c2180300d510141d441140f07869801392000d0321031010081a10300100060304051580c14105681e862614100943d600c4180000c1c60140000d50600d001503000400ac4071516094002483c083d0742542144420740b00e9604241c0405224072429060400c07155000e5401602e00f1405161400300341410b0511070304a00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 432056888 1250 432055638 432055691
    0x1020d0e0a030f060b1f0e040603030815012705040605010203120406050408040f0803090f0a0f120501060b0310060311040b03010e100306020307020102131a071719030609 75
    0x1014581181d55940722a800c1e400d0075140103503100c07583c42c007a8595084010166840c41101030700d01e0001030b401847c0300b0b040607503103029a05011003000040d0700325015640150080005020105100c030040b03403c0990400317150003c040050024080d480800c490714252041554180a000d4844006a070b40c1c1c0304504194a6070036282c0c00140c082246030b07000c55007140c400d582c0b9924181e503420f00d2810040b09600101d4190b000015514200d00e01012604c055400594400b011185448100d09901d4614440c5e455201d10f031595a80400c10294440c6001d401c44002c42c588a060001200c41c8000c044c1c0a9400800c2c507142d4101d1980700c4410917a0112003c40d080c440c6140e081641c910341d14280038000e18007003180c101c00031000483d11f0000e9031244d4001d40c0016200c51420080d00900c0040d036000201c1c0c02c14800030700c0300d846c4a8000326620f040d0008840901071000b0007045010380300f111842110110304983c14a482c0307606800120071919030000034841d0342d4039410a8400c28038111500d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 432058138 1250 432056888 432056899
    0x23032706040b0723030c1b0c010e0f180907030212061015030f09110a0e0108030f090d050708012003061008100b03010308030f0c0a0e221a01020d0e 65
    0x50320251103504d0f5514040d90301c612104c43c66182c801c110b0300941003510b058068090106040c600000a00c400070b0144054200a2415500d28000230f41124120500d0a0144c0810703441c5040b2501c3d4407a207400c00300783c190410300840c0b42c01000d01f900c42080f4041284140c0c50361890103500301000420303d00980044440710107680c94a0804000314005003401030901d80c039642d01142107000d45c402d07030740310901442e004000301c1408020055448816007003034080603400700043c00311410000035200301c02490f00010707070390700303290340005811100c8910024814461014041807001064010241142000300304420340701400c0b50f08542404110340981e0480c1c0c00b5000f892281d84548451500040c11401d54103207035460305150b0303c450303109800030394800e200042440784400c85201078903840460700500e9801c100c0b0344000200781c00b0078141a00d1245543d01550f2141c0c03100c60b0f80860b0030702c01000c000c02c140110560700680750780341b94070500d0143c002d0340203c01d0114082e650301407422400410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 432059388 1250 432058138 432058141
    0x110a050c01050a030f1d010c091404020310050d030203130f0e19060504020a1e05090d11131d0d080105130e0a050102040320010507110123032706040b 66
    0x4548070f40109004400f0035072118024803035141c0c5071003209100740c0c00c1107885405400440400342514010000102000681c6404210403542c0c03025004030590f046401503a20340311610b80146210203a04040d50264003491070b601010380000040102c01d440301c50341195107039140f202e2403003508544541d00d100300301080050042d540495022071416100000040e1054850300850103d801588000e03000c28070700b60445aa80843c07208203c240000d40c6403051610206001140d40c4840c110001048070b0080d54034941c5035981c41c0448402ea03025054200001404044514442c0e101207041928a000741203030250701500c0b442c0140d041e100040c0c114100b024809041d400200222040c207180d501480b4000400500c081c001080114041c1c1d00858149400103000785004080c101c07902d05000301000580001001440410003103030013401c02c1e511841e00003925983c04dd20109980e000088008200204103400781c0f811135001c1305100c1e8481951314103c014503070740c4d0800e0740d0107040201e8180 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 432060638 1250 432059388 432059413
    0x604020717090117090a05070f05030a02060c0f01020d0f05340207050310060609060309120c0f020901081e030909042d0302010209090c090a0605031305060f07110a05 73
    0x40240410601031500c00c88950078032032120005041a2505000d0f5046601400280030023081004090561141030054251808002030b130b4420180f04028014003010a4101c5003920078850003414200c01d4000f507564603400342140004141e400900c01016151030f001c0f90348400203901c440d03158000600208103000049262403c96840840c2d80c07405c501c14503401003910340301031141038149410907502240103030514101a01010080d001030003018030f00324040c004030344600803651501d00d085c1070031089c40c81d40d0b0a050b909a0720341807010390402d000900018262000107049200c418040101080002c1403144a030780f03a12a00714407542c480050004a00401c0d981d6000c2c840c180da800180383c05c014100d103040e40c1c103805140300560240c0d50114840c41c550a000c211075901400e0580c6071880d001c1d022000808214050050104000f00400002c4400c1d00314443d620200c1d400000303c0307003c0d223025140c08184443c100c131850000340b2000080c10b01a00000f0b054102141d00c400034203031001d82ca0b0b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 432061888 1250 432060638 432060683
    0x17090d080603010207080d05040204050105030d02030403170d05070c0b010f0f0e0a060305100603020102010c0e030d0e0303090301181713030b0a09080703020606031c1403040c0b030f01060806040207 87
    0x141600c0c2d4035540c200495000140510014a4028001c101c082803a15040c010032044071016072200d8004d030001d4010007501030303012045400740ca50107008000e1854508030b8103070060047e1085144030f00d2403d0f080c01440e40e00680c44004041c0715956080c6035a0b00d903145000390729480e110741503517001c07000c2041c4003049114919541c807001c0b4440c00601169261140c0f40341c0303449841101c41751940c03508140159642070168118800040c20060209100400441e54401e20700f58038004102502a001c99103a074248101c0d03000040c002e000f40400000d0260301502c1c0300100c0b40c01c840601c41314142000548500302560034020100381c045003864039541310003a840340b008014005640c3c1e00c4040c0000281103502800010380664014407c500e03100c018140360600301d003072020012440c40c1c251441942d00c03401400c0d28016200d9000c3c0c40780c07a246061500d0b0b10594120b0b40c02c0e1100882040881c007180c415541c100c409545c0d910005444a20901080b41701e0a80040c20001d1050400d45449120 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 432063138 1250 432061888 432061891
    0x70b0c0d050d023010030305030f04030201110a02150610051b0102120a06090507031116030e0d030f081302030604080f091306080d080f010e040302120a080103020117090d08 76
    0x81c1c2a0261034102c80c19500a01c1c1000c010000700896080d012444c52664955919503008101141c546043ca0840d100074042c0d000042c000c281e107a44060004007018803e400c640140c07031020344c0f025102c1113480c1020b034075480100400c0b4007060031000003586a1a101c000d142503801035885462406007801410580c40440d2808030741559000c004203906004205107841c4164515840020703018145042e075803e90344042c01b144105810102480304031882c050844e00c8410300c3c42e10544001c0507900d4151034010391180f0340c0c2d50040b0071468103428135401c50740d0540e100c501c542c3c0e10034159407646020808a1845080030750181d10200004001520351801001c1701d0791580290f50400c1e03207408c0052202180003603128526600c4000c01c011910041201601d44d055504110700c00e071607d1103040d65008014412440c0000c00d00000c107081c103000313000d010041e80030044010366408a003400684480707005e11040340001d1100340c0002da540c1002503114050300c60500504005a0f0140040740c03070650 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 432064388 1250 432063138 432063157
    0x70b0702070b0f1201090c09090b0111150414030301121101110109050a0c1a090d03050c030a0206070e0d080d09210207050913030c15141503070b0c0d05 67
    0x440300046400b0219201400c00709400c507030b070070b65200110340d40d0f20745880060307108003030050402c00d61034400340c3c11180c054241d030341000c00003445403007650048a4400e9a8808041c0c01c0c040e8a480d40070a0084195041c1320b5802a40d03d0f01180c4c0c000d80c10181d492009210f2450303542c51050080001800039039001504480500d03001d103051810007545400c48000d080c0c111000d5101ea8180c0c0100107080c1c480600074180c14554070b41c2c86026200501081c420030012070310445401c00c00104160180c02a248000c1d104002c490316070150600180d6103440649004e40030030301010712003500e0300c0d20300c000d00b40031035010342c0e0b542c10032401d001e1800141a03499811201420440030f443e04501c8441501c400c0e2010f40d500500710185044180036840a000e407038640550075a04801e00480c0c0c218941c96a9203500c03c00e5130390200c5800034804000c010b404410404018000240580100e46001c604071051085044e40c200d280e440d000708046214191180d15280c101080c070b44031090150001d0301e454007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 432065638 1250 432064388 432064393
    0x301030305031303090b0417010c05090f011101060306090b0109270221060c130b0901051e07020303070f050c0406140609030a150207030f03110f0f0712020d020d0e06070b0702 77
    0x91b00d500c0785e20803a400c190010400d000c400c160303a00c400c103000d0140b0903440f0a5420f08916064440000c5000028040701c0706041c4803000c0e01c6481a40000d51291000350741001c4100080b02203441e01401d88503080c49101d1072141407034a45400c1e0542211001c001c3e6000c0009040e100255501b8000ca050250a000c044081c3d510b50021081e0300c1444818400c0b01070400c1c49981320904c040482000f100c6412001404405128041c52640c1090840f844c1c2d0200c00d9101c6441d0b204001500c00521030680001d4040c000450740d0400c000000da0709076146440340060714695481c442c24002110280c0c13054182c00404444820b28070b040a000820420a02a06446150300c8a0321a1440580d4000810094030b40c0003030104141580441c0381140c0e85191322303062001c034440350003d0301e0501a80c0038400312030304002210b00410b40c540d012108403d130710500c030b00c0030b048406401030b45401a803a03480c809800307107202c849030700c1c1e10500107519482e900401440c10706070151983c0f07080c1c0d50b0090100c015031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 432066888 1250 432065638 432065657
    0x31303051f060f090902061c0617300f040902092d010807020a0503040f03021908070e0703061e060305090f070b031003050708030a09090b0f04110f0a0909110301030305031303 77
    0x20a0908c0089a030f034802001043c0383d071420050183e402d186110320340498002d0040c980720000002ea003040c0e0045903035164400740060001000080c03145001e02c0419600004002038075012503006040317401c0301207505601545001c0d01a00001c840c051002c0300f440c01100070800c0960240700070302d07089561441281c034101141d6545514540c46900440c0b44a00726110800840c90542c45040241404440c280840ea1424210a03036070045406400000c0344000300280140d4400c0e03001100070241e250360784814840b40b441075a918540341c090640000c0c10140014a8603a00064240c2660121070003060b80600d00307800c5004513040548a100c0d030001404001000c15070030410f132409001001c003c0d5a031400d0341203000d0942a500c0c0e120130300c03442c02d042c0603007001e40e554440740200f140103171000710ba03404450412100e20310515480010000020441900b034507440b000e29419110415010008080902201c00b5180001d20000340002d8080000512148001d0241a5480c1c464140304018 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 432068138 1250 432066888 432066907
    0xe07020d0c110d0c15020309130c1701090b01120204080a080711150d2910031e021308010b0a17070302041103040b0a060620031303051f060f09090206 66
    0x20f0200c4180140c603695070f5003005001000405150890503000f03800154684882c2c04085030062400050b24514140d0314843c0e148114040e940c2040c4203c4007400300281980c542d0021002021500502400502c4601001e40b40c01540d108850a0310303484002082101101d80e2420f45541c42124220b40507009403210101c2a01c030221300c50b024040320032400c0d8035031044182c41c00c200c80d01c2c01259001100189110594410b200c000d213000840107940c41103804034042000c3d400b505103135424098410b09034400781e0980c8416406017014034450804038a21569465a45080e90b030007101c0c06502440ca0001005000441f100c14411226138105541d031941c1e4a400040840f070005141e00303214003001023003004001c0b08620f00c5034405141c0d00f0420000d4202900108030400380e8180d42d96491100300004c0c1c1c00c040400c2a100d00120317185121101039106c0c80c240d5110385804580110803a166114071220b071282d40600c9040c1c41e240b0705444003141c41d000021015106082c400d0343c003c05d080114414 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 432069388 1250 432068138 432068149
    0x260103020102031c02190206060312040e07030905010213081c09030825050f0d030b04051915090e0f070e1312050f070c0f08010207080d020309011508160e07020d0c11 73
    0x192a2040c7c3c019050300d00c1c0110a06091140381c00300d0210310403081005212080e41141645d8102d001d41c5000141d02200e0f01d0700381e009106100c1000e109503522180050543d10008540c6052030300102c10464030140e417041640d041e03030304d0b0000600d0340348188240155180d01c0c00140c40d139804070607203444095580740c461904020f00000d840d20190003c0c41c42c1400705425000380303081c015041e1344c10825498004130b030502c0d07918045080c4200f0b84c1c03510401c0d00c2050040e07403c01c0c05000c17100010424105840001952000401d8070f12040703000d00c000000f03155a140140d40d10038911028590148101c80d541c084014280061003414024140071103000081002c000d0b2008603c51040110003905200050260003e41c2d801421260b004002c5400042d116505469007d9000780c070140e125164001c085000d081c00d1440c424501c04072034800500620005030320001010482144081d55494040d81d500c61041201e07100c02683c44513500c0c400e1584644460440c1c02d01411081401c8002d034000141d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 432070638 1250 432069388 432069427
    0x30b0114031b010f0e0415060c1101230307050f0408030c0f06010b0405010302070602190c0b06040603080306010503091f0605030f370501020a260103020102031c02 72
    0x510005458080030468181000030300000c907400c40d0000d401441c088002040c12442140340c2081101c20707190140c8903100e98120001500c003e140030f0107502d8407490b004010034002c10003695449082c80342c000b0154099050b1503505109a05201e4900c626020070813026800070f0880f0040010170010400d940c00c081000c0d0000d411450f01840d070714a51160403a10785004450140483e8014900400200c2190011113085070000c1c2009600c5420b5030a00500a0084030a09a10810081218030040c0d5202d20404080383c0305162101a60b01c640b0148000c80b007860100401c1c0840400c089100780d8090710113103500900d0b0008071140c2c40f610030100d460800504250071202c44d10b40c841030101e4501813201d007801125800c01400e18444185948100340a100d07194a9079100000101c1e210700301c034000008107150408001d568a80340d40c00002c151008510740d41007100c140c1181c02000060728008103040741e80581c000c50034115011090300b400c1004910a42149508025068804200c80e0108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 432071888 1250 432070638 432070649
    0x3110405030601030b191803021c1b08040509011d01080a02060301050609060702030a110102010e06060a03060c020708120d1a0102280b010315200a032705060403020705040903021b0a030b01 83
    0x20030480c040c0c50b001c4c0c544002c80c10b0002d101c2c0212b80c640d43d56160300c030900c2c1d040d8400b40d9107082d56050446c24040c41300c1c0300300c1d048aa00b0058040000ca8554011011032107815540ca031600b400b60398803084039484104a2000940c03020f410001041240340400c040c1c00003d1000f03012610b854284e5000a2600080e04821100c01807907610b0340d1903968081c41070540c607041d2035000d00072034034080f0300190b49400b0303500000700656955285c25034502d1003080058040e1600408a82601174000020201508000b00b10304c0c569083c00400c45c0e402140c801740004058043e002440d080c0400c10101c1c8c0a41c180b0403610480c1540031481e8808038041800b12030082d806500c0305082d1840c8200400182c8804000035071003410401254940f15903000100c468040c1186030004000300628100e8500111201403414000520b403071103070a0081c04a8040d0040b80701340c0071a551a5990024401680c442c210050050381041580341000115440041a404002810201201d4590752040c0c422402078110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 432073138 1250 432071888 432071921
    0xc071509150b030d020c100c05070e090c0105120612121602030c0103060e0708040512030411040f061802090402040503010c0518010e100f09051302070303110405030601030b19 77
    0x50001d010010b21507400200c605a0140c01400c1300300001a54803014404002e000c1c041c001d0484548070b10503c6940281c5a002007038070429642d8041c3c20044d01341c1521030030f07031a0007001c178100040e41c050400c81c3d01c0000c103000d1403404c65544c88200480109940c1c80e034038041c0a864031400e1000a554010300319541e412000041091690062601c0c110809013000e043c18038002d0240b1003c9800c240700c46e130084803454090881da0380d41c0b0f80075040849076890710400da900401808204209078247c400c0c1c040c01900c0800150805038564800d540207841800f4500d0350a0031070a0b468a6903400074000c141d4003910162419654101103402c45a00ca841400012404901d00360001030000c5441140310092a19880c000d05440c00102d40e10081c2080b44240002c201e20600c0c21030045005800410005000d40000d001d911200c10180d849000d080b00024074181000201002e00003c1e101078500280042c03e8903821651440c0c0800005071014902c15449111512046030700d026404104d084042c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 432074388 1250 432073138 432073163
    0x1501151d0312040f090e061e07112e06050a090b0307030206030708190b030c13090b0108010507111c0f0c0b040c09060504020a020a0b100f15081008060c071509 70
    0x20a05d04603035005038080500c1c2c000340240450b524802842c0f41d02c4001c03405071303011641c6425901781c8114004041203510743c05034403003480c0c20b21810400030901d000c00490507144803410960f8103084419600400340e00402c100018800300c0d0f040c0d4481d1542080190803101c040e500c0340c0002e01e264108940f1540010008400c0103000101002d2001c200003585506112644d502c90000c1d4680718201045406150140114921403c4e2034010b1340816401c50400c40c02561104000f0740a07100858510010070a104132880355554006254040313814920080704514000010803101a407441650741c08009002091a01240001c11042d000e6842428242203e6261007145d40c15207080c5e03030080307105520500030702510b241c01180c0e061203258000c1e0750040c251781d80c181e50404201c080c0c0042c0301810b0905008513020990341900c10030a191520360035120303601d160701541c08241601403209150001000729102001150141405c10300c1000c4034503003580c44d07a11810444800040503101102c0201 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 432075638 1250 432074388 432074399
    0xf06040b060c0613060b0d0f06060609060c12030623040c03020702060d0c02210705150c0f0306011211031e100302011d03030403051501151d0312040f 66
    0x100d03180000c6015078059003000541d0080544802c40240a104000d5030920a08100003aa5014000000c4000c2c50354010520500b01242036901101045481c0c510301000031440c3c2d401420510215040360740c4881c5890066550385c514140312130000c0e03041c0743e180c0348049807210310911302c00b0091501008202040c1d14010400050751941c25181c400c0c1441000240c0150300e0f0301d401c40f260035544400200c0d0340c1015080c00c80c50b202480e200c2c40380c6505c0f12a1038040180390b080c014034902d0300580c01c690031800155402e00c0e000c20143c4055600600402c6082208240640550b900880c141400c00307070b0b102c500c40f5404c02d45841ca006c2d02000400003040080c00110700e021962064484504d05d00e176880c0c03885100d0300c0d20b8001e0001906005007000104040c1c1d184881526070810090305594a031941c914002c0d603281e110140345400e00810000115080d02012900030310100c5590740c0c082a00d0704441740035020691b4110003900350180324145115409110010401446003d21603c4154a0103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 432076888 1250 432075638 432075641
    0x607080c071d192702220b13060806220f080712080105130e070906030c06020d111b030c2e03090b0115050c0d05040303030b060a0828050f0604 63
    0x1d00100c041c1c0d5107030481d03480f4050075003203418003900480c118070300b820a160b00020b6401c1c1d200d52100090781003d00b43e0008035403219001084041002c1d01d0600100054003491b80588a4501920405034007400003d5480b211101e0000340d1200c53340c1105948400c1516007092030000c0200a84040b0b100054441c1000400c480b0308050400e10326090b9042e50600000607961040100c11419a0382c071000011a400f40900082e001484007801c10030440c0da9078500941540803c0c41540c0160065800ba200d1080c01804882d600941d4a0054501030070782d5074041101c210808140da41510a5a8030030020341c840071801c50030b070002c00d0290564100c40b00d85003005410955440d404050500012000242044484506407400000c2513180c50300300c1041160300b800307103083e010064846c441c110003465411500034425a4007940e420f01c02c5607040000c0c0082c0d481080ca01c2d0b0000341ea88000078013008500c08039084490708a0780281080f03008035503c507003a0392060781c0f192141c12010b0188081460035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 432078138 1250 432076888 432076921
    0x408120603061302120f030408010c082a0304030e1003060801050603161a1c05040b010b040312201e0c15040e070e0d0503031506090607080c071d 64
    0x1c400400040c94198516201501151402401074021110000c0b80000c24404c54031910b9489049a4446035600b2080313028108a1640c0b001190341103000c500a000c0c1410209000f03403190005044401c07814180c0c194641c4014000c1e010070040f401018203d81e148034a130313402c2c1000c2e5540811141e042001007803c40c3c2c0c0282000b88070740d0211003045030b040c01840381581118082e0424030008104030324003050340e02c503190403100704090801907103e011001d0341c4240d0099014950610f126030700ea8103249494807860201900107050341ca0000421480340340304569509103e840e04108801c1141c100d031070070840c054161035041e500e902d290b28181d4204045580400c2c1210900c6030b40b884900c11a00d039100350b00640c0766035903103607002039042ca00a00281c0c801078000b4010381c2e408920750a24640301e40055501c581a002c11801940b4149024010340300d08000041010385426800da440309915441140304031818081c0c0d05000606441d040211428202040840d412a14241064400d031424 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 432079388 1250 432078138 432078151
    0xf0b030a0e030c0d0305061c1202010501060203040315090c0906230612010e090f0601030b011502011e1a040c0c1403070f023102040906061b08071406040812 69
    0x3040c482c6120450001402d1302248055050001d1203440d0b1b040071070122210740350076081980c8200c41700720800054040860707010782e065000f0415640c035407004a03160720407031201034110390380c943c0100c018045d95800301140c0b502c60400084a141e481c04c03030b00300740d96082e0300240c4400002007111028440c09041900e0700c09c000c403402890000320b400b030b54916017010700800b202c10303052200040b48500c0410440340080e111000f21120f96a403031501e0307a10041e0900a1646038101055044985070050103612000c00d018407809103001ca082c1e0b00e480003004103810201c0c0d209007005110003603071120b214407031201006544260050646d41040000410890720128090f4400c002140c045001064420f90341d550480b00348401103686200003650441740504522103ca84908503010085541e001703004940742200c0500041d03998000c01c0d220112103501c1e1240c0d442e100315280c000640785070000c21400348140000d18184080a41c490320f4268229001c507850000011039406140314414920341c07240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 432080638 1250 432079388 432079393
    0x10f0603080f0306010504091e1103060d08090f060d050a24120201140d1b020d090b0a021c020705090a110a1805120601092708130f0b030a0e 62
    0x528540d40c4080510521400b107a0042000c4081585a84210201e4000341040d10040c0312005020200c1c40300d000190b40c041c070000f1705d07044421460400c01c00a4910030340004112846c05850754950000359400640020b40c001440c04001086a50b843e002e0b0460344143d8a0008a51602a0304642203880d0083c0d02caa105c03000c11025195060f0740315582c01568208001e0003000129131005031051500c1d2901c2d601d0700b540110b0b45d08011613a0341d00540070303010309950904002d420340c602a61152210b0302c409001a100d05000e01c00c001c420001480020091f02c11900d42048401d000d01c03c03625181a034130016000000208094509074085035040700702100104290344402d000700f13280784610a800d9050240845600300f50515003580703100201b40c041c14007542c1680c1d001021b0303180c0000f40180d40005150216102d4540881c442c6145281912004c003840805035884495858102417520300d002000750002182080d1500740303280060104044850f00c90030454807050554065000000c401d5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 432081888 1250 432080638 432080651
    0x10c14090f03071d180f120a0c080f070525030b06030c040603082805090405060111010c1116030b060d0807170c0f0d0504060e120a0308040c0608090c0103050a0b030a050c03010f 78
    0x10350041202c050001301c4410307003a908c11154130b00382c50030340004c2e002600c2035202103018000030441100803c00c2c14400e50030748142109079108140c0b80c0a1031020b40800c4042071000344000740c148207845400c018020200c070810500703800003409842c03180e082110035107004140210740c6c0644001a03a80d050400701c6203800f11105544c0100300c1c0c007130440c8091089855101051090740509500e9002800e032300d00911014a60650140c40e800c81c00100000c2c91080810700340549403100054401d80750b10140007501034581078100320314110084010b5030030031020400d100000306410101c94030f40c5641041c140c1c5564501e0354560a20001d50342400d8030744c00000840c6040350380001202c0c1912554101011102081c60101c0e65002d001e02003241c1c00d104030b0240304103040d000824688101e11030009003114549035a03003101d0b109401d603201c0300143d02c81440c40000358040d810a59005220020001c0c1070104580028034102250308159002e0704244910b403414203080c0560305003244d143c201440710 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 432083138 1250 432081888 432081913
    0x5030c0d1d01120209010c020a08010e0706030212070e030f060f0f0105031507110a020d060204030b1006120c2a0c15090504150e070305010503010c14090f03071d18 72
    0x85501c4011121003084d80010f0030a826805290362421268018020080458440c8500350080400c20120411131050860000300c0b503100340225000060280800c0c4400d45418106540030901030303920b26414040c03100c140b50910001c205031407003105250182102c1e0700f02100d2a44403c207042c2c000d90700a4000c1c10076038440304560301c02c10350403000b50710b080308100d00031401040c1403801665000f0361001403120300c00103100380b5801510603203001c1c90140419884074000041800f005100f03003004107484010324808208180e103c05e560341c1c101d0401e01d48122003240c00b0160045030700703d01d24414191444000c00d01180c1480007029100185200112807421030700030b01000d42c02d2040a110b84d80791500c0c07a00c80301003100850b00500712009011058100401c1c00380140030240241c90083d071900c0071090110b446901e000c0000d225181400d440c02c1d03000e6091001c0300d02c034510629014440c2d5180040c5a148a4160601c003006000341d00d072003420458558020100180c0c20320607594481c001c95100c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 432084388 1250 432083138 432083147
    0x2100f1107050c0a120f141e0615040c08010e0c040b0d020a02010e01060f0b0318120a020c03060606091e120a0203010b0306070f050d1104030c051819020c070305030c0d1d01 76
    0x161b9030012000c0c854100305441d002d00d0010b4120100400c1c4c07640440700c1002240000c4c03841c0c05030340f42c0d004109502021605000c2250700b0822010001210031340108070290604050940058140212514041d100d404009403588200c492082d010341c00522240c02e16420720035821b500041c64001d000c028039101c0c0d10040401140910868810b000000c200e507030300f0308030201c5128000042529041c642481c440e440c2904000072800160096041c00702407858041615840b0f038070000c045904241e0010140058041d07901251400740703545044404160b41c0302c08541d0347c12030340c6170024000308406e441410b0a449222440b94000e82c011820310041e56003040c0ea44441040d44c0c68140d17101c001480003000585070580c284010510001004824040700c8406102640c4080d681481c000100c00316041084004450780000b40c840102d100e10409103d40040c05a00d04010885901c0c0c0e4030b0b80c0354641160302c50300b1141213541c003512540310000d4001d1100c802810f0010a201c0c1c440080600182 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 432085638 1250 432084388 432084413
    0xf1101121a120f01061d011212030b1309061d030f030708060a03060603080301090509210906071a0411010512070503100e0406060e060409020102100f1107050c0a12 72
    0x600c1910b0021400801100c100640f1082149841c02400084e50343c2c007075410b0b04480103505d6480e201e80c010021038003411000e1107011150f88202e20400101d9003100071001030603094061070b4000b14240451070300d455180200b80045004070000180900d1420f181044100090030104682d0810712455410060b00030540b603001559040500c1180d444000003408440380e81c10013442246840004020b220b0080041d5042c3c40d0f205004212030744412064a07a01c1402c5010121040b054908100b04a1503000141c0489030018103810300300300081e42c920501c60900468551b081803030500304030a00080f00428065000700703084c40c1d03203010312042b24681d060b03200814640602100001140c4031403c40609800180020310b5903210703174100303480c001024200b20b205044413800d1003c0410b00524007841010030096050f001001482d039001011400380c00c0b000c4058506594400200d0040725005004200b028403078406000c0500c010b800f00301c854460364015035081e50100c80004000380746140e002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 432086888 1250 432085638 432085691
    0xf0e0a0207030302040b0310030b0606090904141617150103020108070c05101406040b090105030304060c050316031e0504050904140c06160203010b030c060307050a0c0f110112 77
    0x5a075503011424203501a1140340e0000644d801c00200b0080c90036050003820080d607204510105440d180c81c41040b015015084840e5402400c400200e030004451074a0300e14406155400e40711219403002d02d801d9240155402052040501e41c010803465000748000184488040b00e01e1000b541543c00007070903900300800c50018480c2900a2005101d07003040010007000d21650244150045a425812b0211007a500580101d041c586002e1b4149829100035040c3c0380003400031814945801c10884520308107043c280c0d65404100000343c02c05c06810250581d00d07010f0303190f4103610441c541a154405c42059a0501000000e01c03013489250750350014540c001d6003040d80c0000a00014119a081104508000f9882140069120341980c00e006160b180c07035000710007c0003440c40c43c030140760310351444080b04c0e6404401000001ea041d030180c00130305802c0030a81b401c80121400c9907242c003480340310f03990240c44060700300c0c0042d98150b81c03084410f04413502780c49040c04040c141c81441c0b40080216044c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 432088138 1250 432086888 432086891
    0x624060309120d0e0c49081804050912091206010b0301051f0c1518030801050a0608090c011b0c0902030f07030207030e0906150301170c120705040c1e11070f0e0a 71
    0xb640000c00c0041c0300d06d8110401881d0107154184038a4450644d52200e14129402186c0b0703070940c1410b00d02886000d20844441000d010303070071114142c00326154041c4001603802201d4400c2011000350030010711f03011b0140089034560302d50610003080707060039101002e8800d2041c68a01c4a441591001e0740081c156403100c0e84012066003844d54002400504142d5050603015900c60024141d00c030010b10304841c010f1740e40c01505610740b04100c07004001190f4400599010321940c5140c4d512449082a10f08000070801a9540d050390b07030004800c610750300030b200140d00803050003ca0844082c40503000f0040c2c0c00c08515005142e0f4000d0320114421041503c0741030f4842c001420740d103e2400628100c41d8050074240e4a42e1034030031203540c010040c02c0c1040c56108440701ca50300c03030820004802400524074001c011251902c070400c4041c00b05414070708100004030a00720b6108011503200f40005e030498445c4000500c0540da02c07440d000f0346502c80400d15240400401010000b501d80c160800c411180 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 432089388 1250 432088138 432088219
    0x507080c09240409060510140103020a021f020c060c0d0b0904020904150e100f0e030310120c090e0102121b071b030f0503030106020624060309120d0e0c 67
    0x1a008000d400806030100b070412040107d000c111044070000e030350380761107a010720750308040c0110708074000d034a0f00c600560720150a4403e1404002510b15200108007005032070a149040341c541019429a0181d0140e0004074500350240c1107409500f100400c16203400c5107524007500050600e41014201412036113100c203042d1045481d07034002d40010f0252000b160038000128811500800010454041840ca8404011403601c0040112030045580d0303c500d114160615030501102030503070004480d0343c0b00c01c1c0000585c01075a03008101d41030302207400060b2038a000d01130520009038002d02c2d070300d030078192843ca09201c0c00d40d850940b4046a040801c2c6083c030364103480750360000d6206400240080d01100040e2003080030010056041e10510703401e8071029103c0c03a4910038220b001d003a2121803a40c81c51103510044c1062400303150b1100703070350702200c0141c0d441401c101100d0340074444501c0f0f8651500003441501c1d01c10400c1e40c0100c001560f04881610054003064455034280d0000b0705005a00c40c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 432090638 1250 432089388 432089461
    0x50714031e130201121b1b020d060207140a08030c1b100203012105030904051e0a0e0c090f060d05160602071703121609120507080c09 59
    0xd0814006a400c1c0041c03120a0a00c5207941c1400012400128001482c1c903034000003600383d601900b011080700495401c0c8070800001d00790781a851507140307050300c2241104441c0241e030b603605001c840c0f0b0f0300406006985020070304000c0c1da00303201c42e2056410303940b1182c41c05001a412400f200d6008a051800e41e450785050207030700306115461030b80b01e0b22034402c4000441e8004060703401503040315074001040316800402c0e11003607942c10b030840000d1320b6034100380305d08503150410360801607101c110050345404036404040f2a0103050015185c942d070165941100c000d100d0400c004aa80b0010300f200c03405c03068540701c5604070510b28000d000d18040c025240d81142044000c0000070071004440704000c40b42d645807440290790b00700a115100183c100303d0490b000301c40703022044680f01c406001d610f23000b42d907a00300f842940e00c0544400320200b0003055400207400041c0646041d25500c20400b408296150040c1d85240441007074240b4031901d4482c09010515100d100b084000c502b0b0103422005d45020034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 432091888 1250 432090638 432090661
    0x2030903040b031608090708030d020a03060803030703140703090b0420090705030f0c04050d06151e15260702150901200a091206231905071403 63
    0x42d0300c000301e00000442840a1900f1070455840000e8182d644c0740026901c0b00d102c0750380d45451f84500354480e0020003d5070300c48400382d0010412501c0c103050108840360346005541c619841241c582c00000d54811010307005150030008a500b15100740340500c144c0d51143c81e0040c4900019000415100c4020000303520400c00e00303404800100d004140100910f0300d84005030041d482110300c06081290b060010781c2e040130704001e94082c0d50380034ac00390404c410180c0e1028002c114001c12120001c00c0c024000500150401054043d8031098952080301303807801000344166049000070606204c1c0c600d800300c4154526211740301c1c0581c80003100407001c0e140c0f1081030703090100c00d140e2407816804800c108852104150403240154014454024841c0411401c0c02c4603402440780c0d010020b19042c0c410404c41c03141c0c0704c8020703100d402000c001070207148001d0500c056a8002c40400148031544041144801e000e24501000d2440e0cd0010b01a5151204c0020109003010346441050319011010820f0b02480c2c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 432093138 1250 432091888 432091897
    0x301050105041701091a041e030f030203040215041502010f0606020a031d0d0b061c0c050111100207050c1f05090d06091202100c030e06060603091c030c120e060a02030903 75
    0x40380c80820101d03894854098111401c47d8103070345850b104c41e80c41405c540d03410300b00c04040360103a071207500c0380b48203400480c0a580040c3c8140e034008480d1021250804d0042c0c000c000a000c641c54181d40c030191100c000e42540d2007404640301d01031404030700300446030700850402506541850b02040400c1c0280d000d0b58003c03840440d064210400304011802c00200d014450b00803881181c14103040f54120900c540c1484422800600381000c80c201004107500400310142d0155440095a0040d801130441604a8002010546169110300c0c6240d51605100d00040300c0310303078a40103c4500b80900000600103210b010300b414000c0d903000394a1000d20241d1f0b480801c049602c40c414582c010308201c0002d50b554002000d9902d09454150aa110180a031080e44c1e416208034016101c1651460b08001d80c9404c020204003060080c81d1480070304000d4800c403120604100d80300014440c11812008000c407917440001d022051601058000790343c000100e0950024158001503583d960350f50105095000d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 432094388 1250 432093138 432093143
    0x603051504080f130302040e060402011416050f0304051908062403031c0510121203090c0608010e06040212060f03100c090306050901050103081207020109021c0611030105010504170109 81
    0x740410303000c164004904c038082c120303802220300740010049600442d842d038034160b80080c0490b600c140c038070314425101c0025105140e840030000140c00d1160302e41ea41421001802c440032a0030002d0148160700e41861075441e100340d00e040d000c00c1e07181002c0c9440c1c1e03101d60181a4580b00140320f44001801201048030111105000c1c06a94850300e41121902c07042d0740c1064071034010390615000600ba005a40c001e03030211000481c08480c0b41125031690b404401158050404040d1100204000728200d440758000a1400707580e1460591b252021036009114064185446140100030b190501030045c96015000702e400c130303401c3c01608800320000c0e240500034990407480d1403c29084503107094205a0010489000784424009030751810b1505080b16024040101130704014400c803022540c5000c10780c3d5100d101740c0000545811180c000800c08440900059158000da900a80800500e4000d0800d5000d580c00d046045505210001c0e105000d075018210401042c1d08103280a21002d4100300c041c1074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 432095638 1250 432094388 432094417
    0xa12050a1b1a07110111100207020f04090b0708011a0403141e010605010e04060503060f0403030207021507060f060509160302070c141507020109030305031f1413060305150408 77
    0x710a030b012640c45812030075050700d014002085901455000d03400410112420f403000e0400d43d00301e442410003d4014581c10381e005050210f000000ba1101d1258410130b07400780b56040303c6403501c400d0040400c40160030a089845228008000004082007950b00340e0380c2c4881d801c1646800343c9103080c50000d0510b01500c282e138018030411140c200650144080d00d0302030766070488180d0302c2e5050005a8450b4400c55405034880c02c00600c82189000c60326400920910b805880c05141c0c1e0002120340300c0d0340c1900c2c2a031340340000d9050108001c5104052505c1601c0405011007840e010000b840e15000501d0105507000c40c0c41200d600901c82e038100c5403001d5015540b15800c1d0b44071900c14051441200c01d003400745000d6042c6070f890101450548441c181d05954441c84039085a030308a4550b0009421400660b080d03c128585000d010006074016021682e40650854500020000650400388421002a2818000f400442c0c004030b633440340c018902200c400b05403294940b83c8100d2190b40300a141e903e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 432096888 1250 432095638 432095669
    0x607021201050c0a23041412030d050a06120b0606030702031201030c030b07180915050303071b0f0509010b0f070b0f010302012a0f030e060a0c020a12050a1b 69
    0x1101c0300010305401e4406070340d64070500400c5c085500d065074401640754804a001d000c10032003101001d100901c81c280240070385061061940b081031850700700d4444811000d46400802403982c0e2584140f10080c804401301c0c00f1407100c0358175110b034801c4015000354000e020000c000380c4100e008204032415010b604040440c5503a680c101f22640e46003901080342d1070340d410000300b84c0c11071140d200f400b4010700d08400c41c050f041c44c240c0d42c500100300401100c249100740c00307000a000e42e0140098590a80142f0305101c3d5103d8402044005a40c03c0d0440025140b00100038001e6490b5107207070a06454100307061580c1d505d00890762034a24010703500024109040c18003004007488034641d03618107d91003038031130200300480c0c0d03a000d0303140c0201c00d16015040c441030240080461403070f48018503074078042e081040078510103001203203d0340d22080c0c510006c0307040305c6250011401c06040140041402e86003450220800f5134a0507120009460080d1200002d5404a804c005014181400425804030404c164 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 432098138 1250 432096888 432096901
    0x2220b180a111c0504030903061407090807140d061d030a08070203120c1303140c0a08030a0e01050c03040503010f0c1b02011b06140939060702120105 66
    0x8044049804522050800c4401e500542e501030507a810b04901c1e44022030403080c1c903002c48008290042056080011b031807070000106030244542056070749284607840d40740c5411800500030506035400102c3c554001002003201400c03510003200302a408880a06c40041c40b4200030000d810000c5184000790100c45188400d9100040188000a4035403603171207030b590301c40e0030503600c90083c0b52850420304880c00000d00c4013010b03400109003102d00031030201001500d80d01c0e4050b2140c410702080d00f595002c0109013203140303800c5032940300078120f03400103614114000e080100b844290301c0c41d042c10300601141c0202c50000034815100501005802000340c1c10042e900800036000b00e440d00c4c80801c1c40c00298060800c5141d100d0480107406840324000c0341070000c1342000c06900b044003681c3c099603801c4c450581e00c0b183c43c0e4650090009000400d0460300300565101600408425075016140b240001c2d0204100054007860b01c4404950b040d49980f014004101c05103140b00b410840c952814080004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 432099388 1250 432098138 432098179
    0x40b09010c0c170d0c0507031202150405071e08030a03090f0b1306050901090b2e140a06180b070606080109140106060306140f0117040605010e070c02220b 68
    0x5804036943c0c1296890104a0029104801c80c0d040241c025003100e001031022520070100004040503e00c103c1d4260001c1e40074000f40f40c40c007510102c03800e40040c801009010f844440c00e003014400a2113900d5820b04d40104c895881c860340e410300d400d05072100d200b5030034014140e1100c02c240340c02c448080e40620304401a000008803908040714044d107010041590b601c070510132011803035888a15040309840d80c003014205082c40e41c5036000d01012352528003940414140c4000014103284501c0151240c2141c108214400a80c00c10b1042081c411001d03d184240e090918007280d6189040f03d80d611000e0030441e010b4505900007488640c20b00c005030b41007006018000312804070b514020003009484a0088060b150b007481890640295844980070900e81200c80a0340c00780141400800b00c003220b000000c018004441c10f40e00641d980f001084040c40144070389034080c50714900b802c0000380550010307000340034149820001ca551940300003010807883e846400b41000040422180ca46031118124 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 432100638 1250 432099388 432099419
    0x303070c051e1e0418030207031208071b050102071a0a06080c0102120306040b030105070804140d0c080c0c030610031106040f031709100908060f0705040b09010c0c 72
    0x600400d40510050307100080926400d001e1000100141a000762501c420840c0025100c03c040d807040e682e0701000b190380c0d00a0358420303a15100b43c020300304480c130390700345820030307a44115055003401214020030171090751011070740002d0305c4075032821020904941042e90090240340c000520302108138502803503030145480c00704e219804c901014040f90f51520161910f460a81e00b0081c007690007461004440c0200d24082d540c80540a000001c91609480c006825280c0030384105002c01c20f11700611041c0f04c52000c405500b10610727002844003d5054100078030503a04104040d000ea0301c04541c03a8842c002c10301c02c030700c103c2c2402411034180f410400084016a07619110403603100d5103d0308a2400c0d81815401e0382c0c00c40e910f04119108861654845020000c0c180322840c0c0707008c004121101c002d80e544400c82045001c166200400141081d0490f45041d2016186600014444081018840d408412681503d500c00c640d151184c4102005840030b21590b50000c08550f600348000c40c5d030b103500b111a138 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 432101888 1250 432100638 432100649
    0x1b010b09011d091b0f032109210a080d090b04030908010c1103091c0813090b06070f03110a080706022a0a0201180323070b2104030c020303070c 63
    0x22a4548002640e40c402c4840c000e40804088010707030134124903080d803201098600c003800741c41c1c21541e1441d80172400390b83c0340d00f0b00c0044940812452403e003821254404003081c558151160b0030350000000e0354440c3c0014005050001c0091710189035400b0703070045035005522140c8040182030928000d400c01086020781c18044d031921030302c007080e070307110304a0404050480c0340954a84039111007441203480700e403600f5a00d000009110f403c0007491036030041c031002c2c0001e00c0e91800c03182807800d807000350784a10b08190b100b40c009004400200d440041088001d50303040c1403110491141581040c03d120046901034240381020032000140303c84c0c0d80007041c6400e812070300c0450310900816011356040c1000080c45842d80b094448100650080900c1203410071606480c0000030b03a29aa0f05070104070850303000f4000a8010460289000c0401030a005004c0c0103400c181440560355a0824a10078090354202e02c89156001c601418028440c0302c10203600542039030350f02c50003030410030480915440385 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 432103138 1250 432101888 432101939
    0x2030a05010306151d070c0c0b090301422606090601030302030301121b06020d08010515090906040e12040e15401415061b010b0901 58
    0x12025107200c0090f01805990200022003600d102c6000c00c80d642160003011402885614145c0802140501c40e4800041c275a000c0215903413642c00d0203142c00e46110300142d001141c6041905039020f032240c816401d01520200510440c4001440d94500a40040d4005a031118600b003003c042034510503040302030ba4070311200712401e907104c443c42c01c0d695020034840600160028001401494005001c502400b40541c0d4030410b982e401e08101c5103520942e030f000b040036034019001d0b01e51090300310701c0240c01014200c800d180c2d201a03e114002d21440307409440d501c81c00000b1300003002643c413540000c003034064180c01c9850042040c548041240c0c41030107440e401c2c541c9600000c50100e42d2030042a010380703000c0c00201414000c401d600c5c00b2080200c5031901c2248000030071800b02501d00c111140d00410010b0040340c030701200280e44610f11409818500201c1409030741e0640d5407a6070b0101c401003000181721030b048070494010180108107007003041d03610100c0c00000050142c5071812481a1280d0000c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 432104388 1250 432103138 432103151
    0x6091e05011203020304050904080910091706060306070f090312031d0705030a03050a0215074b0228110f0a05010806010905030601090c0f0918090201110102030a05010306 75
    0x201002070b01080c0c100100181d008000c01c1c486402d00125450b0441c5c410707001903041450b294002030035650041c03c440c00003100904108201e0f150585001072401c0580040c0c1810700313103c0d001c6510f41c0720007400300c01070004200d084082c43e0b220345521401560803240d445543c400c20500140540070701d16500406000144401e11100e10210b21901145d500038010414000300c1d0341c00b40d50a41010400e84298061040d020a6166070040d689201e4422035964488a228034215681e214121104001c04c0031200228501e40203a540300324481013280c4ca0006031410f036040384c22461b1601e214203030a14140c0d0000e02040c00c0e4a082403040c1c81511802100001030054400d100d0450010b101141c0d102c0185070040185502981403a50042418542011003035201d0001c2881e20b8001c1c3c0c0710080705691160b507190855884803004640b002c4500e04184900d01e040680704046074010541e2400aa54000b00340c110ba01501e243c0100c900c051009546910301058124000c00d024401542d0940c00d190 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 432105638 1250 432104388 432104399
    0x170a0e0c310506030715020a0f0609050f2b02030405131b021b010f0c061121041b030c170a02040c050307030f060b0d0b0d0506131a040b0c07050106091e0501 69
    0x351b0903031140b8a680100b1860703119890b40401615050f1003550002c0d5600c6050003c13030821701135107004019100c014504020507000e4001c0c2c04514240e0a01c80c09034140c1038520701d0b80c2c04812102242c0c81120050040502844020024810a045111082d2494111909140e00401e06000190f10100c40c1c00b920910756006480101c810b00e215000101c52901d00e00001c0c009a1003141170000d42c19406060400c015801e1301c0d451749441000300c40c0201001080100449840506807d204945100c6e00040ca1a503e168801e480e41c0200c0c02001d554400400d9003030001c010140a25800400a2040c0c1001c0c03a0090044d40c030640d6000c00003401c0040101e04400507000d484c0441d2210040d080c544002d504000d8018641030801c190320211030405e480c049401048214007456000d04640440760052402c1040484242007018401106804010105610100040c2d004600054460f40c90495150181c018280da03040203541c0751503c0e2071400031207054040540c3d140c1c40030100304056606c98 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 432106888 1250 432105638 432105659
    0x140f0907051c060902130b03070b04050612090111040f03061b0504050f01020a060905010b10020109030c02091e010801050615040503030922020a170a0e0c3105060307 73
    0x280950354214880300300720464842c004001c1000b850046030005074140041e400640a8034801e9401e8110303c0e2a071808800358038050000a009000c1d204160380340500d8580402d155003d04804000080940800200c071501d007900320000410911382e1669445e9100c104040f2200801c0c0015a00c01d1314201e201c01c0f4905256280a8940c00c00752941c03030510340343c0420019100c0da4199150f045000d8815040c0c00180b19000b00a0507500c10b20000c20f511104034140401040c0c000000802c41e03040c020140003094120b211890100d8040c0e03200c0d1075950b12191340f140d211a5603902c01e034103610418000100b09106600c03003400b034001160315290f100301e08407401761b5901450007001d40c1904200026121883c05041184140c2101a0200844400780480d80101d81280000ca00030411400310900c0880390b4107240c030703445403030190100400004103880541e40c407001034000b809601c2c00204080203c000712226040d80b107520024400c280b00e49000200540317025a01039006c1d1007001c40106200c07901 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 432108138 1250 432106888 432106903
    0x130603050d080f0f161202040b0c1c080a0b0d020916080606121f050604060914010503160f03020f0403060902030715050307050d29011e090501030504080409140f09 72
    0x10b840150341c260b160145e80b40c075a12810042481402109405454560400c1c0003800080103600380ca56100e107441c509140c200b41c01c040d90040d120300704001030080170380c000d042c0c01e4001144400010301d46402c040072032052249050041d43c0101d00b242041046040001c05650000e17241c0e48107401c40e110a030a106150042040c00058090100c000407448542040002d50088100000d44c0c0303155540c101080d601ea0141d04100f0020781c80c28024000660307000925848030b102032918034507502c2d02110012886c0c0c0d022610700c0c1001142110704d40080d20030740540c0d0b4030150a0360881e03a40c60752450300100a012000040b070290040c24400204246090609050038515485043c40c5a54400d41203a03d035002d8001c08000c11350300e00d00034806070605541d0303100d100e190340c004140b0f01c94040c002500e546025246440100100480c010b140b591050018013110002e0030082020384032881c0066003401550807404000e481c00c50021600506203208a00070700b04044603100c96180e00c400c40351680c24 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 432109388 1250 432108138 432108151
    0x170d050f0a17150f1210200a08010e0606031b090f0603010f080f0a0c120c0b0406030f150b0d0216021c1a0411090406020c0715020c0402120f0402130603050d080f 71
    0x2145035120100c413100e42112144016080a01c07010f041c7da140041c40343d0b0004241000001d010b1401400541c00d0310b02c1c01604500e04581c0d00307003035141860107110120a40319102090310300108000c2a00c2c1c0344c0c01710400c0030b190018100707a125a110440c0d140d54014500c00c81c166445041242800d5001c017042d45944c607504112901a61400c1140305e10f445001040102e8117828074520000c0c001e6042009000900800e83e0080f944408030807034036013610201c5c41200c00c1041212010405100303c00200e403480c107000e49026841d030000c08030308020514440740180d0051041580c10240c03414007080c105540e80305902d103034045110241d141041c101c089074002c0c201a1881810442441c161040c01c3d0b0080c45440058500074158030b440f030600c0c203140e00c880110154162034a119940500116440360f40c10f035011400c10302c00314102426042d0140101c640d090700c1c18082011f549920301c80300c00030f001054042c06429600d14055136a8112003000c0070029051002280840c8035070b0045601801 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 432110638 1250 432109388 432109393
    0x2011412072304121113240509060d12030207060e0102071703010b1608091c0c05041413020d0b0c0306090a06181a19170d050f0a17150f12 61
    0x340e46a417145104c0b421401190380c007494010000d8074100c11360240154208041440d0441d43c400d244440004201a4119910501070300007001444d4498003080644190020000c034003200410100b507000307200f490405004503041c4105202c400c1015001000254403404013048095031039070b600a41d0340000e001d0000140000c00404401902203c0c07215540360040c40d1a515158600001544603030965602820744a00e56407040e05201e0110100c0c0024801514140b00c003c954000c2445483e000038000412012240104815511000f44035003005522a421021b94100824040402d4004603046032040714207400141400380c00780250001c0704e4402440000d01007074051502e025000780c001f0502c0400040790741c601150389100141600c1d840e0842c19011041c204441301803e01c07012095104a0752000c95210451a8810129802c98000e20010b0380ca03044440001c0390485500c6030420041455101407020518403018009031050080b28100e4034200039100f0300492110581d120350143c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 432111888 1250 432110638 432110669
    0x61d090d0206091e07051e1219020d110301060f080105010801140a050402130f090201172203050705060109020a181a091f0f081506030402011412072304 67
    0x994181c500f0074144424030b410b9560300d61b01c503004203030b0807500000c040c01a5803010014500307a060218954070030100e02800307000604110000d0b40301c5084482d00080c000c000844041c4240065060065288080140240140d075030b6002100481c0040340101c407081d529060000503824414802c0c61a041c000300e060b003086555405100000341001002640c00021040b191079150b10f0320311640c541c030005c180c0c000984070f015000040c120030100c0701050b02c0503800c00a1180710000f10504140104c111881c008002130b803881c0c202c134240244000244140b00d901c0002c540360b2071540281c819018980d558034148a03607503140c012400c1051007610f1070043c500150b0400100c00314018040d40c040544115076002000c0e040d40903070104100c8903400114240c04a090456215003820381001c010260b5032584480720b8001441c521020b0300007410b00036a0b419070614071850505035110030007044000d03043c0f03261030a0054440700d920b110080101080c2c800c805540060042902e054a00340d83d84810304 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 432113138 1250 432111888 432111913
    0x3105070f02061312110102190906090f0506070209060d06090605040215030f0105011d03060f010618030b070c0309090c020a0302010e1f1512030e10050304110d06061d090d020609 78
    0xa402e11031001704a0b5401b0480c00711241d507141412010752505a070341150451504800900d035400b1500700e06900c81f0f4004080101d40e071010309441c240b40c0c0482e41c403001030729150002203100d860008028a03207418000200240940d0750311441c81540240c440401c042e0103d503c014480c40111607525140540d0001401a0f520880201c5810400e09082529003000c5800203031400400302c84ca020350446420050081c076501c003c54902014002d401c00450038119904d0b1912550010004420400c9019910040c5407060304a600105181c61041013007842503203000703440e85580b19050b00550300b000a10042410001500100240c80d1054501d66a4004504001501855079072694501141902203411b00c03900082808a9110b529009501c243c884240710041c0744500b8a4000e00c4018010440414070904091070b84400446a4803240d41d1a0324000d0010580c5401084c2400341200c4526980d0082d00d010310300803c0000c040f181c0c69a1985012070741c5080c121540c1001750001c0c03401048 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 432114388 1250 432113138 432113147
    0x2060f0c0d0518101e0c0504091a0a080f060609100302060306030a0c061d090610030209130221130f120e0301111206040b3105070f02061312 62
    0x2040004100d0b1442030009000c80346180414007541c24101960303403c00d4034407175580f1041320107103d5a181004c0c030003015080409820383c001c1c0e01c40c1c1240c4640f00c0035409200420b40000d494204401401c4403001c07034903960a2980c81d18902e0001e4114490040415a140b8040b11001c0c41001300d802080f01d46411542408021b0700050a0b1603007503ca000c0710344000030154008030001e01500e96507101e00c4540c5600e035200c0c92240101d01030280d22800d052003c0b40d2940c00300e0664101860401681c2c54001001144045012405a020940c400709002e11091181d101c6a040d41106104060f4191111f148103034000c03115800042a808580c0d4062000a1a40c81c804018103000c7c1001e6007000c80b600d01290035035180d404280c0890704001103840880f001d411403031703400190503a820040343c00340b00f000c14a40c00e0001c003480e88554884451808038600707640400601c40b5550810702c0541001d0902400001454030b000340540074100006045902e50300118080e160041e40704810114140810395 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 432115638 1250 432114388 432114391
    0x30607050c030904020a080402100804050c04020702010c050703080d0e03120103020409020a081203010e25111906020304021008150d0606030f1b1a07080c010b091003020102060f0c0d05 81
    0x2601c41c0403c0c412a041951984080c0401e0b038a01e8982e1641841e00b40f0422642c070203514800024002c500d401d10004c507a0000e50548950000c3c2c60041c0d5465007800181c681241c2d203407004200b0300ca50340c400f00c104409030002d40342000c00000103104079502e21415139240c2c0628a80c12284115041c010005490035411000e400350020f480341c0c4110761035440f110b0410b6030760241945034803000401008141c419918843d44094a400d1001d6844800f0070203941d030b00c910540c588200256a0300c3d003030500b1020300c41a05010400700611804101526040019410449080c3d00c0352407000700441b219801a000c0920a0fa0620540f0080d090031608004600340c0f072032400d641c15651000003000080c811046d01140d10300400324003605e8140b5041e11602c0c00842c0e0031805509064940040101000c8420340e9103c0c3d500440203a241d80900c202c07a07004045540da2103030b000080d2000c3c00180070f55041003a054034001e070f007501c05d0b59070340c80b08000c2c5290040c1c4562403180c0e0200005003154140d544039031b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 432116888 1250 432115638 432115657
    0xe0d02010516020636011b12090915080c1005070f0812010e040501061e0b1c02070c090c02030406170a0905010f150f06140307090504020406030b03011a03060705 71
    0x307a0030100042e1250a8040c41d82004040c499018142600a007031000c5e40348a00c040c003480c002085003000040301344680340c103080040500e1040716666a40700c1c01111440050164044d0800c5243d41140a10f1582012071040c00300c1c902a0301c208103441e003021004d00b21204003644030380386031501541e111303400344034000c0341038501c50028071692680080d040c0d030860007400070800c1380440781414140142143d0581c0c1c4a134400c0100701e5042c01e502d8480c0c034159030454060000243e11341c804044c103285c0d0360100308044141d042c8005101c01c2044034035080482239441b1500300b0451405c1d061002d980d2071090b4080c1002140140ba4001200410080415406400c003040828407480d20780d41d013800c2d2048200c841e40030940319a00318461581710701d00316008007508035800d405949042805010070440d101c605441d01d000000041101d8021300804008042c043e00c1155260303541c007030040c02060300e09015403081d400c1c207041c14500740e20600704e1031545000801408854841c0d10381070300c00780e0000342070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 432118138 1250 432116888 432116899
    0x207060c11090a05061201090b07050903160e04050f06011823040804090b0303030f04030f170a02120906060f040203060a120b04060509061918050109060c0e0d0201051602 75
    0x41620351a00381c0000c2c001d41102002003243d0800c176041002032801c65142d1482680350482c40008140740e12880c0742c110307103d42025a0390780242008207007080804d40311291444078a40d00081c40101c950002d900c258003d90550b4600c210201035a40c542d5801c2c42030003c5c6c00002040010400c2c2168010100100b680a04044074a2144295554400103e6066600d4007002ca03042040b2310842c000c140380c0440460244d865440d10101d8410041c80107000981089207a00804090034018104c070500692080310700603852820040c203002039440100c040035503410000220307240500014641d4000c40006003481d80590442042c4002034100030042c9074410480440041d2155100e00100d6090f400303425007561900c2c2508182e801d9400290a0014a60210b002c00c0740028400340c218086511144010900c0901b48ca001107507030072080b0001d8401d501e0b1000400800446600840160b11940c0300d01743c1c101c400c9010025030b40d040030400b0b0b0120300200300c484008a0909103085099200404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 432119388 1250 432118138 432118163
    0x42306090c1b0d030f021201170102070c15090f0312030f1d0a140c010903080c0102040506030c1806030c25061503050705060403020a060f0c02031b011e0207060c 71
    0x700b400c0025032012114582090007903419880c3d0502548000d50004107080d0300c0c0944402101080707080500c075039540b8080380350319016454020740455980f150403002500e6903a494241007102100000300c00d0300810181c000c0095106c0c980d95049084a0b04400c040b000a04015001c2c1d019291b0305170048502903070369502d0100c0d160a21607441c14041000700400d03016103d4a03199482e1443c940002400303500484240c207443c2e0f4400781210990750b0150f40c0e280c170b40402151703040c060700803074205c1544060301004002801c00307800b0146c0701500401e8200516040040140a601d21003a101126804010086403070301d4429625848041f81e2810680904506940c0b6150201d89881221244020005100b0400e1200c200014000b4100c125042032500c2e180d940090130b407214030300c507c0090004400700d02c5034060089000808543d0050292031116100e0340890a2201500322844d004c580301c03c0404140c24a0710f003c1c0b40091089400400a15007050425610041c52280c11107110200c0e02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 432120638 1250 432119388 432119407
    0x90c040c0e031006050603010b0706061d04060c0f27120b0108070e1003021003020904050c090a09050603070603110705010e030d06141e0a080304080309042306090c 72
    0x300d010210034880d0740e070031940703032078201054103004204203540f00240c1081018419590f610f011a81120000303250a9550505c500e02803000d000c0d103901000c1c410300716980600c840070815460301d100381d110711702c1006884001481510f600942154a0b000a00c40641c0030b000302036045101d084044a4215003050b16a0f00c264030120200001022035280403104010484078a081010310040c240300d041c11801d510f003082d025145d01c485444007130710902c8007800da880002c0c004d074110303490700c1d0303020708188135074601004100e800d544003200341401a505184009860203603031003024001d0300000c01821f1202d01d043c40c2180900f82010300c0c50791400d020406000055402d2090081c1d403c1f11201031030701c2d030307544401c07503070440f4030f19441071605442c0a00d001c920b55883e40400728201d1816901a42580d03000f502061018140c0c0e04150210f03c4005004610200000041c1c04c81c00011a000cac0140c0f428222900340302c11189540401854814000c230303155140000d04207900c070503540707240c500300500c22 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 432121888 1250 432120638 432120641
    0x123090a0209010e0907020a03030c05091c03020c0102010216080706140a0b090c2b0b040207030306080c060403021f020c0612150a0b09010311041203020d110610050108090c04 77
    0x6491628009a0004451410356005251310040c030354102c030007840c42d01e0201d034084c2d21051411401001c042e541d0301c039000042d00810903214846d2000e451850040003402c200841066030260681c09403194849284656205000326400c02807407038512207001c44140e03900b0603141c00c5000c0c101d40380c40d11100740038000b00c07200164900c40c0200103008150001004140042141c0281c4002c0d00c90790304004c1201410180300c0c44034003508040c40da130f5881b91400300358000107090411203654002c0c0001091824103526401c80810703540740d074054554a0494004204c07103842a40320081d0040b07518a41e882400d00081079651607100d26006544000801e80b001841a91127090200d80549034070003407019203103000050091592050300ea80485500b007003218401c9009039405617042544403410f008004030b60f081940e008040303400e140f001e949003520f406900c404401c980500007901585510500c80e00000e25940070301c56007a11061303002e04040044074000f070001c01d0051288507103114001246c036103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 432123138 1250 432121888 432121891
    0x9020301091505010501020a3807030e070503010c09050108070e1908190209130203031e1b01060510030c0c0b0f01060314040506070807090e070c021002030c06012309 73
    0x16020b4058809841e4501004540c0c041e000541154402d841e650b0003c0e01c80205450150341884401c000c000444d03c00310303c804201100385e2060540c1c00f05001200d90036411000c3c00003045025200380700d403500c05250885a240640700002603140400b0000355006a5081c0d8000ca21403800c500750000260108200010381c1081008801d1130100800074144280040090364010040b0a2400360f09a00010603140001d0818404035422001c000c0071540c04000300c80d41e07402e070200c840b080840100f08c0040c29411030f810580281d54103141d62100c0100621840c01600c82c0100042d54140701340500300c00030682c03c1c106034140144810b103500424181c1031640e104486010500c1115070401c0c1005050300d0311003500310b0396810b14401740000601c010605590200d4245071039403450b42c8031b90040301c000050b0391140420407003000512220a5220481c0402c1d603000740c40e00040c10120800c203c4e980e00c90408100419000315006002189043c603134100d25007001003035a600300c0742c054002500c0c13010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 432124388 1250 432123138 432123143
    0x809041e0c0c03092306090d0f0602180105030f0c13030218010303031a03030415021e0703050c10082403010e060f01090903022509050c120f160c060902030109 70
    0x20b40300812002c25074805000c0c2d0140044a80d40c1d41035411018009a580c41c1c682d140601c60240841d02d40c10540b40c2460300d0468a40000c505d1a110640f0304043c8004e40c000755004c115000a11840c038020350081003100d005103120207104600369980000c08055401150880100c5100002c0000c05a500c90307081400080b49910804200e516610b80070303049502c1303c0b0752803401e200c109001c25015600802640d0403600e10070041308020316081012401c104d041001c241241c5010306440c4164040014041d080d80d10980495446088590800003194441c004400005401c180001c0050f5500108161060000a0003a40041c1206c000900752031400255901030b038404004c105801d030403100002d005016070102001042900c0c1c6000f5240c1e085206001004002515034048441d0074a404000602c2c4c0040200f00d82c2c1040212513192f5881000c407140c00070021000305036070380004040680103842c016a900f0458503160015162400040000e80300c03903548421410250720280074940b602407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 432125638 1250 432124388 432124397
    0x20a1a060102120c01050a14130b0405160b0705060f0c0d0b01022a1f0503010b070f0501050a0c030507020607091412030316020f030a0f050903010b04091101030f090809041e0c 77
    0x1804412800840d1440f41e0b4011000a10308d003401240503404401001d07281c2c00c00c5100744240d60740d0800c0340c90302c0b03407220101380c500d264940300103001d08a0b072010308a218411416640c0301d4860300c070240c04d8900140e42d2801c806904020f2800c030151150b01606141c5410b0040c1c43e403404007121401428200e085e2101d0010b004130180c06000d00d40040001140c590307001002581c000e44240040841c00705000d082c0510000040220901c0b810f0006010141e622a000707100070304c1d06d441e100010b090360081400100303052002040300180040307030840c80307581166200f6a205140603201450010704803907040d040707150002e500b40d180d078051006501c9110340d11407814518488810013031a000d00ea6805240c90b8001340042e0512590114051810100a141447d1200d02d4280000c1c01007401d070200940c030501d8802d01c0020041d010003540808170090328100300c030310038090b64007040d110304032001030510808014003601441c00364403080c0400c052000606034440e105110804840c040e01c100300206 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 432126888 1250 432125638 432125641
    0x3040501180302010f0e03071703100305010903020a0c060305310f06200a091206020c150109110901080c0c190503040906090e0c0f060f0f030a0606020a1a060102120c0105 75
    0x17000314010822004c0307141005604c0c20743c907a201c918920104146034910a03000002040b0a019101c1c140b001468006000300100b0040f4a0701a54804c070208007205c90f40c0c02c1b05000a6294042e00c5140c2c0704085501e085841c104a030f02020b42d12680010b403410001c0442503032040410f650704d4007182c2080c030032180040c81c807424054040400383d5800038101c1600c402c001d02e60744a41e10100000403240c8a0f01d550120b00114905600a030044000c0903001c1d12070032012041e04009840858102c0f10320440c00c02419920014100381403061340c00c0c0a0100390014003007030a5030760140c020080e0115040917140803480140610400d050809400e0b00c1a0384003180a001c1c03035500f482408000d228a140400045804a000b00e49802c900600d803031060062101040c919111300046502c000c0c10140c107142e90389a144500a525007003a500e01034441e141003c0420a9400068003803000d80d0801001d09066680c0d12030b42081210040000d4110b000f01900c030307251886500c020b003488622a00010075103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 432128138 1250 432126888 432126911
    0x50d12120e0c2b111309030f030f02041d060a15050703120b0108040213060b03010602070f080c090402220908070506090607050a050f040e130507090605010806060304050118030201 79
    0x40030303800c0020804205000f402000506445841c040e103440e0b20010410800302000009582c2e104104005031a05080890280801d5071088400080e007440da2000c1000ca140e112480c0200c1c0924041e2003041f000b0486203e10349400c4240456004200420220b001d580b0b8003214070455842e402e050022801c042200c02c101500500c1000000303403a000c08001c1070104000080c0070700e4001d070000c1c0c0960354400000400c04842d4002e03401800802c1c031102d60302d582d100c0d00255038070114807030b21010602c4100301095040300030a17aa40340c070348018070f0030f10151110740800c20121100300d005001c402512038041c0151000d4055000b249000d480003035150007490600c03c0c01c03c000200010030540019080002d1260424199004e6042501c0e0858175031560a800c80858440ca820500b03600c3c810800304690300f032b4000c000200e030300c0c42502541d90300c5035905051001d03150903010701d5010580e10f0300060750301e05001c000f0307661081c00740340041030903075881082c400e55070b0f440102940142d4444454808 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 432129388 1250 432128138 432128149
    0x130308150a031403040e0f060604181b0f0f030501080c01030c051b030a1d090403030b0117041401200304080d060b070b04200607080a0201110c07060e0a050d12120e0c 73
    0x40c08030040b00319045a2030302e040050032710f100c0c07409160407141d040469003041c0030550740800c00519000039009041140c804000e083d9007246641e00300060401591040101e1081c01014101e0f88520700a040d034541407001500603280400107081080018030807540320b01034003546000388480a002840e030301c01500c03000512011105410b05001400b0268a80d1143c0703d160050307500c01e0b01440c1c000740c0d00350a0ba00403580400490503102001403040113000a2121400c02d03000c5048821f4000c10404556651100c1c507a1000c1070103481100781440090f012410550003440e000c0b2000c0000039040b62909110030b0560002142561000a010104400c00031908044c90711800583d28034912140b4440016207640709850004103801008502075403418000d4001401e04440c0b03948180d191220140404d503604010310866000480900b03c0c85c17014205a1460b0003607401c05031850b10790306010780703860b42c0c1e1803403052035241004140c0565002c40100c2d80f1447d96031030030700c0d806407103c1c4149004204 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 432130638 1250 432129388 432129391
    0x806060402070f031d0d11040c0905010206010e060d151d030412022709030705070504140705030411040e03040f080606010503040b0709030227130308150a031403040e 73
    0x500852040120401181c0c44808243d03405505151840407008841c03140180c100d070741c014064001008604e40d40c1001032145841c00501000e079010007515803071000442d021840e512809001d80c04c40801071010300420410607034000006000c9201d0b01ca80c40c1e0b91010401d90203c943c03201ca42c1d89002c0440c1d903031000c44030080c030452050011070606090062414003442407240c020300c00d50070042c4000a41d45030f60b5400304044c1021401c17a4580ca0300540558403944030781c2040310746000308080804c407803500d03115508401c030003103203d80843c1da204030095030a07034070241c800e4030140c8824048940d01c0e82d8901502000410407409961541e1809070011045001504844501c0d0013800400045990110640e039009800502003034103900c69001c21b40f1601b203103400280d000100c1080051041856031125184601c800851202da41c1d81e21001d000b00c1c1a8004008000411103000304600c0001504003584420b001050518002c2d031f259035200700d403800303404907001d0f0b900046010818110540800d6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 432131888 1250 432130638 432130651
    0x304030302160b150d03021e0c06030a05011805010308070201110c030a050c180c0a180f0f03021f080a150f090e0106061d060f0d0e0105040b0109140105040b12030a08010806 76
    0x8a005c2a107030380207515104019255240f90202081e00300d0020780c04c200d50811010050704083d0780b8101400c160300503200902903100c0032501d01d0f40c1141400480d00c140c82c101c80c1c00010207801c1404075401110192440c2d2030003a000c0c421042d143c0d01c0c5940501010703604611540c000c010328070350142408801000841ca0dd82c0b040c41c41002c0005519007401200d6078100549401003c01308544c000c44e070741c01c819400003c400c0352242c1000c100100d0040f0702030142c0b0300880e00000031680401d040d01d00039240ba107200c00000c01c4400412560030041d0031440c29034000701219a8607c1c3c94a100640c0741059901c81c00046460380710f041c41c1c01e0380a1244c40040e250a241c40070b03040101200f0350f40c1e10b61703801580b203001c2d913400103c4044881c04441034030411842c900c01802142e4031544814042e00043e98182d80d00f200300e0000251648891080381000a004005106107030318000c1004011702c0003949050b04405441d01c0c1d005021028001800e441446495400307155040100f214500350004089 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 432133138 1250 432131888 432131899
    0x20f07050f07230121020c060a02030a0b060910081b07150c02071a0c0c0d0f0203060106051e0705070e1f0501050909011806030501060612050a0207020a0501050304030302160b15 78
    0x40540340d078001603080c2c80040d11011140304140e4a0318905c001e12036096044424004e440503c0780490160b001140079501c42c075400e01202804000700b0005201d845a03403a448605903290708001030243c8100355004c424140c1e01c00c3c044400140c62603590b4000311080309d248000306418540c01d40d051140c0440300c6040c3c030040000504000c402e81c0c15540b100c60031038140c0340219480c40c02d808100550307980d428001e410224101712514216607441450790080f4800d000d43d000102d01030744920140d84d44224542140048120744c0550300301c0e241d02410080e90307580108940840c0340000c1c1e000680c045d100c80f200c0b0720481d04410485252400a580043d8100036080006000c6940c96026071410f48032034400c1074001d0388903501100000d00035035000601c0c0c0d500704500050402d4220920120100c60036800703002954a51418100324070482c41c000750302070400700b02030009500c075030050742c3c0c45480390030011b150403841030325810300750400842198054050f80070002030548100418107154800d4a4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 432134388 1250 432133138 432133199
    0x1d0a0c08011503030c08070501060e06130c0f0f03110a1806090e161806050c0706110a0605100b040306020304020f04050702071e0f080f0105070918020f07050f07 71
    0x50784803840003888042c04210245e010f00042c013000b00304176901d240c0d0000080040d15502c51008101c42000c54256204000343d8042504d40030f890300540d9040552662032000c203d0f00c1a4081d40c3e2860488440001c040c0d450307183d4800d1b03602c9900104410317a0541c42d50300f605051500c180d40b2310713130079600840c007000481c1104111149081c82d55035049400900b854488081000c400c4918100c84080c400b02c250304103000242442d000350013003405103103946c143c1708056103072041030700e4141c900320b030805180d030144020302c0210b0480c1c1d00440d0000701519955034402d030380c0c0102d680740750010303001656659400000d100071890060b62030641e0f004240d0701030020340742c412000fa490704030500c40d440c0c122008074207500d000f0111048500180150b980781c407a8a648551040d41e440c420303c1005140356180c04085080e16000b500084103c1313031000c00200d1400c1c2940c8a1101071b4114603106400501d05000a400007041400100010b00d012401030001c1071600b0b20b400034801310b402000c038030046c0d407a5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 432135638 1250 432134388 432134411
    0x50a12112a1902040209040504060b030105090c0a0b0a1809020c070e0103200109120506090c120607110a020a1508060103380603041a010603061503050a1d0a0c0801 72
    0x2c02d107092003000c0c410300505444600119010344103030001c840d0720a24202c1040208180c40c0e00001c1c002e80150001c001a030780304c00d40340e07a4454125488643c404030045c01080541007000060440701003900c1d10420301080461507100e00a599004558000d030040795290101c04100311140091012829100d410b5165885000b405c8aa50640062181c400c00311400c460f4010403003034000b0712a0003001040c1c0f0003281015505c4040c10f442451490240003114010307072400342c003203142d44a1005c02819654598600c00d0741e20110011402459004207038603940036070740d44801080280940212000b4552181000074200e0170000c2c4424145440c2840c0041d580e01c200350200000040714408070a02010156603503201c2080480855000700c00000f004100702c2140211003452540400c000030700c1e40c032000e05406940c01801030f028140111301c4100c00d41b6201e80c0200c0d4001a20700400200081c0c000003103c6081070810042078150700102c640001c000f4400d0848004000070002002940a0013 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 432136888 1250 432135638 432135643
    0xf0609060607060603021504090605060306010e060c011e05040506060a0305071a0706020c07080601090e15270f070803120106200a030906030b01031803050a12112a 72
    0x1500c003601030000070804004101060384010701540c0c00074603441d4003d003408031002c02503006000f411101800d0a030005064140700f4180c0740190016103c0705031521100b000d01c00346800242c01c1c41c02542d2107042d0525000c40c16034403003400548200c1d01040c2d80c60705051562401e880a40030a0051084060800104d00c0228241081e1401910202c00f04c504000c2858002c1c05100e4020740210700c0014040000d410000c0c2c0d0404945515080c4e503101e0707a86903150800c58240c0005451150802c0c0010b441c2c82000005c442c0d844100c08141100c482402044400f0780d140c011100f103ca5882140d04404c412000c1001304000c0030001c0003507113040c1c25080303814000641031181006000600603290703200f04c4504141007010140004036410503403e810010603007840e5120303050200c1c1c41c02c66216100d51103401a003207070050b031552041e41c003462541c0441c0e0300d50100c3c0d000010005000700358044e6212501138085013010382c8800517100d03110b4080b01546499103481b015903d0302d0f540e41218661002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 432138138 1250 432136888 432136891
    0x103021003110f04060215040b060f21101d10151a030709090212040201211a0913031d06160f03170c0d020309010204050d0803010e0f0609 61
    0x1aa00302080d09044501580a01006079404509080200e0b226103403039404000340080b2030307450b802c40c0d05010b116945c4103071414083e10702425003154000000d4240c2000c44002900c15401740c00c006040c25121001c0220001c104040103c94200c12410094205180545505840035519030035a910440280070340d60fa081c01c51101c0b046071501781021060305e100402600030481709400c0c003840500c1004084807036000301d40c60b0010030314074a80412015a0703032003682c91804d0340000549142c0c070749400541b40b10080f546540c46000c8080c84000c0210414000c0c2280754041c08040d0381009001c01c100840000000d00060011120b42908801310b540001c0c1d004000c400403451014a120342004504c26103c1c0c1d10200d503404500c0d90712082040070110f40004810f029035039280b20300d4001c2e00302c40300428054a8010700310206001c8504407209030383c019900141c6a03c0010301d4542e8460102c0d82803e1100700a0340c22071001b00c0100405004d83e0300d07040d448030b544100d020a170310f003520000c2c0c0001d20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 432139388 1250 432138138 432138143
    0x121403250609080301030c06020d03050103150e120c01020717070b13050f010606080f06101e0c1506080607051312050f100c0f09030507030204050c130e0601080105180103 75
    0x4610414406008a69010459083d04407041550745e607102d007040d40c0c03496181e01c240c1e4014452089818100c501c00d20469041e2684030900700003029055003500c1c081d0042111989150050045000c2107500d400001d183c07050303041002588400140c18408030300841c02c5201c81c015442000b41c0d0000903c11101954013481540160080c1c0e0b14a0802c940303054818131b81c0c00c14940c42c1680c0402c2681d0040d108a00c41c51407003071134010a50362142441940190240c40002050600307003003145411a0405200b0440914a00070707240c0291a2226030404409034014008556038550522094034207000065214075142401413800300f0035229100300782403e110b42c02c122403c101507181000f41c14041100112106008c131200e10050564100c0144900c103c16404117005180b4000c1c07943c010020141220380000251501b01d2540e000d000c09004000c180c49a03000c1308101c1c540070720940c48640d8001e003c080b200140c045c03034443c0002d000c0c0e080603080540301d0702002030007514500400b540c3c1e42c150707507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 432140638 1250 432139388 432139447
    0x9090a061802090f21010c08012103140318120904061208070f020d02030319080612070e0402010c080310090f05060d0615150c0204051509070f140301121403 69
    0x3d0000851244900300881c1145c00e650030910f0f00003030721f40d001141c0350513100d880e082e8419400c0150582c0c01204c01c0100700070045003040c1010b1400220b000040c590180c103040d030000c1c604099640d00c604055042c201100e0080c000300d84142142000d1050a001d00b001814684c046001e50311504254014258001c0c18001c036241500c085480762800e140b10a640541180e88481248101e085c02210024910300052241c4c000035000e807800e0042c41030082030250103840c286090600350450b6a400070001d905100400e0030740c100090980c03000707510424000920720049070501c050f41d801d50302e22000100540b41010184110796841070340c40a0a10b078010760000c0c02400c61103194600034081c1e03100c840c0110f0070901c1e100e0a1500020300660a502c00c031420405035650041092460140600f142e400108a03800a16450300440c4050081e1015080c407105c440072640304902c01d50300903042000503501c840840d40030020707414440490181707490051400e103007083c0302c10081d080c41c40349080f0a61 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 432141888 1250 432140638 432140659
    0x1f021c0b060909010e0403081501270b030705180301060617040c05030304080f120304031e03111305040e060103020f0d0c0e07111e0c0d0809090a061802090f 69
    0x19550001102c002120140c1085225070750fa010110303032494111000d1340031039402000100c0b00510964140c4d640e0f08141c4400d21140c104003a003130040d00b560440c041122f40c108101040c2140300c40c000d188a14072030b07035406a0301d4484c90001003a1100307900d0b04a00071784c18010140070482e00031250030301000c01c03180401d01980c0d031400d07c05149008c6a00c03490701400002004100c11102080520406800c14100c880c040d9001d0750541d8070344001c84001d00001e2000850707804da540c0c40100c1e054036465500d404103400140e040c2c1d204071031340300040081007110805010046070810380183d412406080380507000d29851600801c0100c070603015030a100d00300070740c0901e0812804001030009000c2850360000d0510b000100070702006800da02d00a080d11800c0d0300340300e4030554002d2407406210f02d1342c09020340c0038540707040c0525159503440403501c0d48820702c8141b16588503980350901c81c055420300403903944e01d010916003d5155626903000c0160041004010a03110240f044000d101d080e5015031341d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 432143138 1250 432141888 432141911
    0x12030601020304030303020d0b1206072c010305131e031403070f030e071e0501080c190813020d032d0e0f0d080d02040f06090608070f020c121f021c 65
    0x1017a0011086a008ac04480981c4a8110000300700f4803a284589808038828280141242c8865045200710200e024031458203030715501c42d410103a00103a86100c0d510804a50f076860b075010701c0c1c9440740032001d000c55801d6a414140c0c4155001d040e041070500f650700c1d42c1410600280b40c5d400c201a54070506845288910200000b002701000400540b4071505000e0404000000410490f100301c0b40050101030126002d04080401c07070b200e8030b030015103806280104e10b900341c0703021500a002046a4682c0c01e8040050303140e944902070701a03c6543d8003060f0080e00c040c00340716503070515183c030b44c41c40ca8212112510381d002540700180e00009c03107120b1301d2401200300044019800100040040c100450750b203400f010745030094400d80300340030520f0702015101d100484410040d4402e000000710501c02007000c2c14003c1d00340d0820704501c0c0c81951140d03124000803403503000c44044440700c00d40c052801490300c072204003000079409950030010740c40d01200001c2d034031030321910100800c900b580d121410b400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 432144388 1250 432143138 432143141
    0x105040203092d0703030801090b010509011b0f0602040e07020d02011b050d09061e0b10141812030703030e07081f020c01150501170402060f1b0604050a020312030601020304030303020d 81
    0x3c50f02c0400121014951a4070340140680000c2c4150a0014140022003520350b0159060300e601e03d0040e95040c50061655042000800003980705031482e81606080b03601041030b500061001c3c106040410089017070405000b46091803100b040703401c5914007000364100320011030b0006c20502c41850300c00d0b00c1d0340e803040f5071000030300c00310000512051921582d0380003807000208101b890324903403000308107020b81102402048640003640100050480f1803c1c12a03603081d402400c9840000401501000380d06804115000c540c4e1400086070f601c08030b02c100803d40e260060070400031468000e400d0491510b104140c0c2e030300308101c0a43d46500c1e28000da00407004030781d060f1246d80000700024403d150494003100c2c00300b1040c0c000c0030300050569a1802e085144800c0c101e002c1c640c06071480e0700d04059801c0c00b0ac0c554001080f44e002905c16146200b0b10440204070150145020302e01400d032200c0184101403425200018480341c1038814070030014680c6e004000d5030201c075010308002d40c1c0c030301341c40340d9078030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 432145638 1250 432144388 432144463
    0x10051b0918040605040314040b0405130f060306050a0b0f0609010503060d120e10180605090f0d0602041401090e070507030c0b100612020c190302010b1c0506010504020309 75
    0x40e40080700c4410801404101d0b009540558001c0d10f650072540c070710111071400c520907802000c2500c0010042044a4244907ca400032014031840c001036000ea1041040c0079101154401c1c0c9800d40c49405000c0340b95000c1c400e0a1000710111035011101d420308010400900030145481c0c188403000c00041d00c56202e10418440c3d440d0b00c01158400e4180c0b100b4060060010f801146010304445250742c9092409054a039120380e10005005507502d2030079104503074580c84294065001480304009590a07240d080701e0780351081c030400015807624100200603000d4646900c10394104030492004010f4040f054815941116680c13a00983c0c450541c2000c1c3d031020003400000300041985070030000029910030104040c0c5030303103540c1c40202c40c0110050f0f07016400b07080b401c2c020a41003c54003070585402c40c9013543c01d262081c0004541c0303000b0440000c40003083e404c40d01c03500b000c1c81e405540410109001250240078222800c50441c1000c60400d640e8045400900c85a02d6210880d0f110600003040c000303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 432146888 1250 432145638 432145669
    0x219021f0314070c0501231b040b0a020717010c080c030c1303060b040e1c030f0b040509030406090506040608040b181b0a080a021f0507080f070510051b09 68
    0x88070039041000d0020003044c440c3c01c080e620343d4079018022000c6c01c1c030302c040d66140d540700075400c42680d00c030701456039640007040d44d006c00031000800000802c404808064040f0f000113401400710145000201c00f10074602140820030360340340c0084400080d42103120705401c401d407050b20607125a280c8001c56040c0c815240502040d10210f1400002c00c0b065401060390943e096601b0721605013440038090b03598140b0f0051040c0c0030b11014801001074440c0e402007500201040021402001903000320b800c482040d20710b10031640001500707200d00c81d044000440184025280d541c502450f00500800908000c1d0006015410300c4011612008020044e0584001228141c03400c0c1d11011080e0800000d0b01b81d04c0d10301030428000006000b01001c80c1042c48282c01814058003a0702840c0841c0402c03c00c03040d59000d0000c00e01459000c1581c07400034043c10195110341c0c5035148583c0c02c0c207521b0b0101d8803981c84581da0030841000043c150001110024089100789a600d0318243c50008000c0d06010408 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 432148138 1250 432146888 432146921
    0x15100b0c1f271e0c05040c0504060f05040806070c11150301080f1f02090a1d070306090903091a1b070317070f030f0c05010f0c0219021f03 61
    0xc05500c5400c5078800105284080e9107800d090104107426242c4900750080603200f02d01c5844500c82c150301c1c9991091040d8825102000d80503160000902117031201d00007100003806c086001e1101c2038004240d0610141642405418549400010303559064020700359410044406540340400295582d52004901700500321080948200c291680b240c1003440354441a2180844a088070380020802130001030880c0b0140c0001c4183c007030010b001c0e5100080e042d4002c3c001090006204602c000758203c101040031800c0c2260404460003016903c0a40080106a20b000700035000240c1104001d8100e503020a8030b4100f086146903031100c03d000f44100e02110401c1d61040900b10040495a036040e28481d0349030029031a80100c10482601440c90000e004140b88420000032034080d0f0310f106844082490070b210f0100055443c04d01b035a505505104170720381c4580c4030f110607503014440f52010803401d000500072520075800040d0480c0c07400b580340c804192101000c1c0303991441303600040100c16010b0107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 432149388 1250 432148138 432148183
    0x110a0305010e060a0f02040305030f18120a06050a0c0507020d0809060a12180804180603080d02130503190605060f0301110705010f060b030a0518071715100b0c 70
    0x20342c2d41c0303410341103420380719240ca400704620700d0481c039209035070980e0b401c0350080d4100054101d0b10007a59001081c2103a00c1c0300c07807590329081f607a00c8071500242080d00101500c00d2204034603066040d070384040c050303c0f03401341420b0b4240000e46d80441650318185d01221030118503495800c200d0603034451180a660001c100007641550550400c1c00c134500004590001c004120000441e0000c2c101c240b280201807032001c000c2040000e10003452804c2c0345a00340f000050880c0d8035550007000c0d80c00240c0c543e20107900801e0b9821280d021510aa00400040d40a018003c3e10101742ea13029840118000b0031035545d50303020445946842c20210481c4030042c00802c40030f02c1110900500c1d40002004442542c00c01d070f2400d034200018040c400c12100240c41140c110385031102d00c08040c003001050028024072009240e0b9030140100840001050304098180c1d40007072640380c0609104800214215000020051203501d0792a15400c104866604804a490340845c500e410300b000c0204420180800d040c90 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 432150638 1250 432149388 432149411
    0xc03110c1f1106100f17061317070c0e1506030703090f08030a1b05070f030f020c0a180e060610030c05040810060509011202030d0f0c060e0a0506060913110a030501 72
    0x240c0013064400d040c0c0d800300c4d130ba86d5401c1c00d611040c2c51199946660342050b000b140d0000034041c20005c1042c0310b03c515040181441d50b03d404690003114065403100c0c0350420030440310031941038142e04048800c0702c04904509110124085200241c544e90805075500c1c0c0e0300043c0f00280744070300401039000c1c0341c1c2c5a4078282260b40501400d2145407601c02c8812040f4031035000c60142007103c08d0340f0b601c04420441c0000c21f8400341c890007030000c1c8040c294011442050788550310544001c015202800c2002440711f90f68100c007046030640059088194081c505201d0301d59039130000701c90000349915000c900e00d0564001100d45010b1640724082601c41e4401140c80c01c2a180c0141054074070079101203140da0798912450499096131707040a90150003010384401034500c902c0400c0c041e040d180c1845884a0160398403a002c49010740641102d58101c0e90b000d03001c000c000e024198204a0464048035a428001c0c40506007840503000201000000b0740c0c1c000c0c00b44c4605019200840c0c220000b08803840140c0b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 432151888 1250 432150638 432150661
    0x90a08071d01150f21020a0f0e06090604050d02010908030a020a0618080a080c1306080621060a020c0109060204030f0212010e0c0f0301020702100c03110c1f1106 71
    0x9008140c1141e6410001c154107480c03c94101e035034000ca6641c80c141503d0160250340a0011204030b070b40030b4840c0810514100c005000401e509440369540100313410f24404c0040c00059014411445030004011020007583c400c0141c9040c0c0d80704440881d0890700b01e10050ba16011603611104081c0404203540c0f00c0b05802140c0500c4190107001c050180000340b010303c100303070030000c0002400d0001c2440500ea000c0e115508050703101c0c1c0c41610041c500900d1040101a12600b90312010010307005104108440c1482042040d6902c06407500c070202d2000c202c2c071940c0703548004016094256020403942c103c0d0710250010302a80b0707004001156030b42e07120b0815480c03545156505900902600400700c1c071701d65052041c00d66000042c005460240004400c0169180620301d8003079056400b0700043c0f001d655409600c40070780038940c69a2405880c146400380c15699942a541700c41c0d0484035055109844041c0710b480b41c030204c216804198130500006892600f00386c81c011195108000c104003810011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 432153138 1250 432151888 432151919
    0x7120e01021614211207021617070812071e06090f03110c0102280605090c01020610060e010305070318031d0a050d021c06020a090f060f0212090a0807 66
    0xe18040e500740402800000d0a81c003203240310307404071403800c2008002d503c1c1200c20b606d42090305841070f5500c060800303641c1d601c14140390300800c145841d2051417600f0041e04220f50b038024403034003002d011036201d480b101807020b004003900a0300c641446080b80048140d4a012201641d0740917404001c6a561414400c42c4002525012000300340c40024088031288005004811408164028034503c0c0c0c0c05401c150301412181c0c02c0c2c0c003514a0031043c04000030349074010148036030b04650003030110700b08d00b100083ca04140070303018a00b80107820005201032980720300c2c0c071000c0c88020300f00880d01d62200740f000c0300108441281c0010841c2c0e14180e1008040e8400e80001c166010310201300d0211030200104070100d40302c0c2c80780e281d101c07081958420060a01580500d21701e181411400c0c0500201d40343da8060b60f000700301200000e08410802d02000f0482820640030700800c0c6002882c983e041e10000c1e640d404803081c031648481001c281690381d980c600703110b0006040c240060715180d541d61303c200b50949a1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 432154388 1250 432153138 432153173
    0x23070e090a15140414010e01090f0c050a0e0f0c09130c180e130f0c060809060a0912080c0f0f12062b020102011d0f0f0607120e010216 59
    0x41d4086041e1450b010707014a80300d6045150041c40c0c103072034665500314242026900d031406952204250499600b00388074459600703008190b016440301c40c6140001d000642c81d0043d5110f40385c01501400713000104201154801e4042022004c1c548030806450118050308070240e91100c4039100c40314951169400c602c081c180a911108a4140301e0709030520108460b00600107070114410000c2c21050b500c034601420b03207014130700654594800d80c8940071402e0154001c00c0229400724180010210300f0002541c0c400403079001045001020750781c00e0307080b10200c6101010480c0301000311341002031402c1224480701481d02101da442040d04111001500061080c01a01e414040092402d0401c3e08400c01140140103c0f10450703000400c007039400302b802d1f000517811903590300100180d404800e0390064000c1c200074010015081270a00d20341c90544038050040b00b40d001503090140150700014000701d40001000007151104d42102851b00a0251038512206000e15100050601c92502c503261007a42 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 432155638 1250 432154388 432154403
    0xe18070c051b10230415020708010b010507030804150c121d06190204030204020d0603050f0c1c03030f180c0e1311130f020318070323070e090a 63
    0x600510342d1082c01c0242c1490075040405040c030401c1c528840d581402c0300610490790b42c03c1d0841c02946045058005030000c41c4507106048400100f2170b010003030b040003040070000a0100c1c0d1565000245540213480d030090501c1103210200d810400f000d0a248601c6840c12020800300031601401800003600030710a510040c50008000114600390585011070402080281000d07191058502020400814080b0002c0e5080c0400b0006a840b40001d0505090700403011580720709504019040444204801c810340c0d10514240c482500c445103c641e03a0f0035030010f440b050300200e040c1039001d0900c15641d9000e05d403800c16070b05040b45e51010003501582c051440c0da51900e469025940e1104070079100603404030f9464180100107058078900c51600314002c0c00b003410700d4051001e00d609072981d41072441400ca030040100b20340220062a042c43c112694070041c0754451650b150100c070b203200c0209001d00180b60f902e280101c0300c1c0400c600c000400c0082035180103481c0c40070744241c40e400003100845221 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 432156888 1250 432155638 432155653
    0xb0f09180d0818032701020f010606050319020910030203061203220b03010305031911010c022503030c0206091918060f0e18070801060f08070905040308070e18070c05 73
    0x403d4000140c40084e401010017840c40340a4041e04280003248280d42e034118412052404134441c802c1c00740300300078902e5071610754503030a03c5400400b10900c4181c803184040e1051044189a594480c002e100746150780c14010303900d44420340030a2060782460a9000300b844001441c015802d103890500e09125251041c604d001504c80d120003c8911080c4405084d60f8020b205480c040e411140c075400424000d420160007108050001030300350343d003892102001d40c100c0310424100088201c055098a0181510407024900b545c0d405804041540070190107694045011100354030380740401e00c0c4080c0d000b940084456a200c045070200079040100c01c504d40d050400000b01030352410030810030381d8086910000143e039000c0106e901040b603c500400c02d0300c0740500c0000c0801c4203114103009415003142000a0340e040a5510303103044501c0e481101107528201c10000401c0c0d0211650b900042186005618111004000b403450100d0117040b0707410f00c80c24001c0c400c100307400c0310882003214810300c19520344 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 432158138 1250 432156888 432156931
    0x40c030209012307170309060916060806040209091017071a0307200a020a08060f042003061914060f2b030903150b0f09180d08 56
    0x141e0044160490119003111001c61588010b0fa10b024a10341500e200e884c20503e25895036074201100600025a1071000020b1243d40c990500c021a03000c20b0110007044040c12802c500300341141944510340c00c00c9407102c0882d07029501c540403903c404800500e00181ca0800303d01c0f81130900f107103219032000140e015071000004400410000300b110030030300d911007041c03d520034903a8890f40300074034250402c40103600748005130f0a040702c03812030305142c08000c1c80315140a1042c04000112508196002d6022004004ca40c030303d00401c5a9005500074040071904298400c1d13000a210512500e56160250004105008146000508074040b01c00d03c180441c08461140947c2240b00303a440342d0304568403a00c17404032400c040d40300901c940030710015000224a42c3c00700554039801240224001518844100107010580e80a00d001c508000c3e001c100e00a0a01c0c00a643c41900582e05801920300c0130019090b505441404e2858840490075140800c60048000f000381108460b03203001d0a4a103180d0300306 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 432159388 1250 432158138 432158141
    0x11511122110030222050708100b0315010e0a0b0304051f1505061812031b06070e040c0c02030607031506020d120e1207080a0e040902060d0b0f0a0f05040c03 69
    0x28800c0602d0303007000c440c203607000c0c005003113443d41c1c000101e10708402d41d44c240c0c0150751081034801d844030344c1d80c0d480034180000a4604100158400c0303401c4401032080c018040d0200014510008090801c40c3d0f00700c4c3d00801080c000f00756940802080980442000203200d00483c5030980c00300428500c007502d5001c0c855200c11180411030801101c00a4081840b0506002004002d032030118120540302060000000e080141840f112031503a07000820303600801c50000d0045007000021101605e441c4c54010401003101d1140500c091060b52210f40c1942c415000348503610000b60081c1c1900d11a10b032480c409001380103102d8540e4803200c01101c00290700b40c03000c542c44800f0b6090307668501c075260121590801034465510b43c215a40a41626001002d42c11300040c0a03651061040541303605c1c1000d4040d14414107200100e006c1e03410110140d00580c1c6100440301d4203600c0c21000100b001015000c900030803c120745240c2c0122009001280c0d001300e400c2400c040b0703441141e00340f150a051480850 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 432160638 1250 432159388 432159391
    0x9140a23040c09080307060c030608033915040204090606080f15070504030b040c05040c08091c09060c030e03061305010b031914030f070b010602010506100203030115111221 76
    0x40b450b00140070820000710181c00c582c0d2349402ca840e001c24040c2c0c84400c51800c1d6800005d50000016129003034410707211202402c1c01190000e924500c1c00740009200403a118004840805040d494180008045544503440850215040a010000c440d1243ea1290795045c255564041910950080c010110050303400f403031040701c41e90b072468145851643c03104810f09019008a0749926418004161900c440c41031070030107002c3c0e5075001054103141d0b036101e0501c042110400c5501c1700740310301207000d00d8101d030a000468001d860302c0d00f2200440c0c24121400d480302a09540d02d0b002d0b51051200078081f040541048600800007000203500420402d0b513140e030500d02d40c88400c5000c42c2c810740455041d008a40e100122841541c1c40c08840745812040c03640031220440300c3e4604c03c0010b00c8207560900c9480d901030400d83d140301480b0880c006c060b50300c5c04142b140e802808405500100c501d4407501442c90030300c0751803045802c0b8240114410000d604090405003c4000810301d00703280112240006 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 432161888 1250 432160638 432160649
    0x120e030c1f1809020f0304031b170a020102090901180608010513020f030708031201090b090603120a031e0e0606060a12150314010905060702030a09140a23040c09 71
    0x600014001d100c10346806202c11003042c602c0e02401400034400c6180c0c0000d1103402c50a0060694034a000d00e00070303100c4a40c2003104017410284d24039000c005107100344000700040603070312440e0b162044200220b01a00c10307650300a403c11203001c0000740e17040c405500b402c01d6000b50141840103584900d0b159003240c9048856440700302e10980e041001d402e01c1180c13203000c514041e082d03504468480448a140d503003d00304c50080100982c004002c900014800c0c0c0c822503208980700442c5042100010f07594210a400c5803881c0503001032442c0c40300d4000e42c0b103860000046210b1650f48114030100d6002004280d6140096004900c0001d2083c500b0208407540760640f503d0704c58003807071070507544001041e04400b607a9048005517004008940301c00b01101c420000000007140e81405841c00d142002009001001551320500041400e50f400c9150704007514145030085c01d0700e450000000d403101d041c6500026200e4902100303006040c91004440340310603402d0754140401d5140b03010132203810520703110340c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 432163138 1250 432161888 432161929
    0x4020d0f0e010b031209060423100c03120f0204080a06020702030709062106020d02030c1e041406210915090304030c09051f0b0a17010b0322120e030c 66
    0x4000d03810025805820072400141480e42041d07168034020b0704c0d440d07403200d8404509c0824200803805103482c014240c031101d058030b06903809205940c2d002c0c291495207422018803c0c3c0310303100079182c011190f054400500080c0c00315034144155051210080d8422710099001c1e000306400460058040e0040e04202d03030700d00d800105600407201c10856001c0e40c0300400ca41b03041e020001c0000045503800694001e6401c250069501e500f0b2480100140040740c41d020b5032464103000c20030904500c1382d940d00140d41c082e9591030391050450008004403c880385000503e0303034500309100000c4800505241b880d5480c00030b1003900e840340070450f50340e400303a4840245022000f80d0f0034440c40b012134001642105420a407144c20b4844240c503842c2c003484a8010a0380344270302080c02c0503500e51204540b082401801c3d0080320f9035052078590242ca01c0028011049000621056608070080c0d042c80002103401440e0b141d035881590f040141a01842c1441c103101e403280c1c040c080300900d0001a8040480100c80c02c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 432164388 1250 432163138 432163153
    0x31e0c0507080a02150f060102060f060f061309060e090d020f060c07030309020d2603160305060a0308040e060906031b21101d031c02130504020d0f0e010b03 69
    0x1180c45140e4060356840f0700f14000c5011a109081000400c0b5005102d0f01d0018100351800000091501c040108020a0300020343c003803181a46071019440c2c65000702f90703001540c4445076804041c02801d2903000082c00c900d44440014286070b6585468003590f441e4003542e03842c52082034100d948410a0403000c013190000c0021403180c00c0454001c00c2054401e06012406001e143c0002d402c16624800550342030b441c0c0944442030045030390015010000c1c00a4107811820403100e00400c540b921a200700070b141e036132000b2030000e03591491f9040c01107611000c880d40d203d4640c0459501094203580d40e600807402000030403071507c4d0224803103800355200304620020041c1d8078100821003c0e40c0d4500003068459440055046100f40f10800b0007400b0a200420410001401254484038580343c4501a404c107001091740ba420702a050303c000485001e01589502c0c0106040c10408617a0303014550061000076034107031310221034200d44495620302c20304200e83c0000c109594282c400c150017171a4107801002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 432165638 1250 432164388 432164393
    0xa0e1c0305040f1e020a080d170c1303150f0603110f0402091306170304290f071a0f012108070827010201020a09090203040f12031e0c0507 61
    0x901c6254860300a01c5080c807040346644564000904005030713400c0003030390030300e04106508291006800800d054001030824295000e402460404034825030301201b1101408a045030150600303581100f0150103003c0782450343c80c0340c07040003884142000e0241500300501224001c40900c00d40d0110381d000600b060070601c0880c01c010740d0344802c4c4a000d500507428040c4940715114013001d0394000d0404400091110b0410440d007102041400b80302083e940f08000c00c0c88040c1d040a07480b402040707095009404024041030241d07441c0540700d5a85032610000c50450280300c4007100820344110000446445034880f07030030f0071403021400d0007a40d0b050b100506000c07419403035020b07110f80041d028068007410400f0760390380c04401358070040001c4803001d900c01c0c2d01ea85061404035030304030f0858240021458454200c0014184403498032411543ca0303800710000b801e202c040b00c020100242d0103081e2034002c100d4020043c0c0101410110014080b0001e0041c84482c80c0030311a80192503202c1e200d06080a1b00356 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 432166888 1250 432165638 432165641
    0x3040611070e060f040f06090f0b061810030e1501150206061c0602070b010308070c0e04151a1522120803041e08030f0627070320030a0e1c03 62
    0x54046801c180d035406c0c01180c1d958144100310141c0f005c040045180313455200185c00f61002e4030302e982d2043c50100b104c0c11a6410f00301d00c01090744829140754400f00c0007224290000c2002c050900014043c80d288000d00d80001a40c8905903800004001c0030003400ea03a00300e070746500459060b6004002031300302c040707a403501245038005a44950340142c0741103030941d920b40c144603080e401250302c12000319001c402c100400b0b0407d405007c41d80c4c4198034910b800d4440c280c1603c05034008458890390b40d03003030081c154000051941c005801426890741800841d404559980c400c01100d82e18040d61900c0340016070800c08601c04170b500090b209010501c454442002551001e402102d02c840c00c08410310820080c44415100036010300d4009450380791040d0a4140d914008000340d01c6a040c45010516129102542030251070002003212200c5d504c24000350010208084940c00720420f00d02c120040718007140c010740c428003002c174081c1700d5880c0036000181d803045151280d030b15151f0124042c107181d9201e17 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 432168138 1250 432166888 432166909
    0x6030503190201050601080f0a2d0b0913020d0201050405181b070807060c2606010914100e1c0f02030708010213140f040c0305040308010b0a020304120c080f03040611070e06 76
    0x1100d00040d51040780400a2540c2ba49810850054070803c0601c28071740e2014444c039003150700140d03000b2055241000031601e01c447c0c00d0034000d116800000c07a0350190792140094501802d0050003108462488103001c0a20b03100407100d410003441b14045c0440f05c805100140c41410b86d124114070304103401e541d00d401c05048600a484104103103032035000e0031220032101d91641d0003c1c002442d4614240b18000500d83c1420340c005184074035500c41c0f0003503035449040280c281c008103072410700809141540041d00390800481c0f013001b982001c000040c1400746800141c3c0c035852080342101c0403d42c1c0c540040d07007070380564001001408000d1004002d2003420011010031760f00f004088101c814852800501100d1010b000240003e80d00c0c400c100030160021542c07405403620b100360f181041d141d010000d640348540c1c09258032818000ca911010070407803242030800340048009a407800714981403450341d20f07007191140b41d00040f1921000f002c41c40303001c01e0000c261058815580c0c0c05940351028880c0010a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 432169388 1250 432168138 432168151
    0x605030d350705030103060b0307030206090103020d060308031e090d05070201140904060b0414180106050d0e1207030210023901050a0501091401080304140307080106030503190201050601080f 84
    0x8800003030350301d0401c000a1091041d8810348400e03440f03504508290044030800034070a80298001c080c1800940e80320025038440340002d282c00350b640c81a40a03840c003d080e05501c0100503181c00700078000d240034011280310300c0102001d0722031400e0f070302c01e03811a03a540b280305c45e400302250b4204821400b40d441070030b020081448214a2514011000c0c01150886820390b005018012021405001c41034100884084110048500c1c11200003d030349040165401031040301c080c000300040f80490450b9035040807055550340010f0b1200502d01c414003e0855204030700460060091640303115450410b072003516a420141b04052140140400c0003200b00506410828100c000400c41014941001d0041c0e030f114540c000c40c045825450040070344d003a21179140041c44c200e5070600042c81160400000c2e03408484141a48036505400d61001c6400d10780d4a410038080c5500780080441408070000c018141c107009035058081e51032820408900304c80042d83d40e07900007030307201e400301d0980350b80c00c0c4034160000f5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 432170638 1250 432169388 432169457
    0x30b0402070c0b0304051f05070f080601080c03130c0b07020102010c0516291003111e091008030307020304030b13050d0f090510080a050f09120c19030c02040605030d 73
    0x3550050f411078200b241d8103e02c51512303a82000170b240d51080a00340c1c014039a042110f050305207400040c2035400d0090040640001c00300c00980c0c50310001e1603401c007103a00b01d9600446d40d40c4074104405203034804241a405982011a0001031502c1001242d4644402c140e11501e1070b0f03041da807140c10a17944500500b0490603114401c1c2074070703542040d206000d0074105034001c071010305d03601e0541c0c05070701091402c0744200f10a02c0c0c101c03400c04404514045100c0111440b1610b65190420000b0608840e0002c0520341300c04010030028940000c000c200340c90142800d100716a8a10070750380d89440050070000c20680042e00c8807140f081c064040b103492101a03060800e503290f1600d0104070000310000c9801c000038059014440001c0c1c4a00c625a04150240c3c5170703400c0f03407612042e1165079281040c0c5d1503070000000280318161036028401d80c03034000d07052248500074034001d09009215101d41039090b4400c41ca04071000819140000b0078201101071615203554880001c0c1c44203c400258880ca21075a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 432171888 1250 432170638 432170653
    0x403020a060501090f06060806010f110f030c0f070b0a0914040b030d030603020f06030402030a170f03100312170c07140f0307050f0d0e040c0e0d06020901030b0402070c0b030405 78
    0x74260300415019001c0c103100002c802d51034000c04000d42d10142c2c011018012150305104690b640b1860702c502498031170401700d040f00c29440c543d61610701c4840c0103010740e000100c0d0007400920003140c0350302001c5440e01224041c5846004c4070002e481440f0006001c1000d01d40200003040c01481021a80c4030002c00001360216a0b4000c241011640c0041030000f82c5d5a0405000f18a040c0f240205001400d42c4c8032411450507601196441000210242c21070f9050f80b0300010340c0c0c1d071880c115030f040d505503e045900ca061904040c014080c1300d001c1142c2446007a0201c071066882003c20040ba1508e0104805284e118002d02e040726030702c40c45003031756018504524400300310000c0011068009040000b140e441000382045420030b2000c42d50504544c00101118401550107210100144011680003803030710f034040c00c252280c8424641482d040002107905a0502080b90301403c0003070350a88050168005000c00c11040b445540790003006401d1500050001c180840c02550780644104101c4402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 432173138 1250 432171888 432171893
    0xa060806030c0d0302100c0e06070609082203140303091515150a09050a08030342100302091c080408060f010311060309150406111b070b091003050403020a 68
    0x343c0300c40c40b00540259205084100000c1003501c0746110341c401034a402e501c041e00070800036a21717101e00c0802500054075020218103000116040700c04107058504003103011320035680190b9202c902440181c80400886a070400c050070301108403481900d07010068006240700f1841d03050718a40c040c04c0003c0140b4144400c541a4440d6100c42c107283c01e204d10718640795804140028230040f40c6030402d90044040e9081001030107070003c05e0b260806440200c100340e0600031350340c01c0b000107901081d01300180584591aa201c4185e85031122101c031040e00d400c1a400b480000540030b034414102c4141d042505000c0920b40904c1044900b07070410f11682041d031510b81c1d21070034546011819504a507042000744010401c20400d541070303e80700d050580f102400d500c1c180d40029103901d0001100c80341240489c0c0020f080084076403180b4030040744482c4807919002c0003d152403a501d540c5210b000d2078400c080d40841c0501151041e035800700002802d030f0300f0070000b0040480140c82d003d041101503210b6074024000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 432174388 1250 432173138 432173149
    0x1120e0f0a1b08010c081506160807021002010e0c19030b070207290d02090d06020d02090108010e0f0c0703030f05040305180a03110f060c01020a05040515090a060806030c 75
    0x1d01a0254807a01a408040d80000076149410f81c40652140e00d4051017002440d0071181c2203178080310002e440399010800c8008070b08144162200400401d804080b9002001104400b07861043e0090383d00758611a40510141d00703d540441500609510111609105240c22041c084200c2c80c1d08103406042542e070b03603403400c046800b80d43c01005a00400024085074035010145041ba29000140e6904404e40810010151144440081100d03030000380e031100303503114030702d85403600342d4016411940c0300411403100f0001d400a002160000d403800b40000f0302d42922100050060042d06501b0360152100d9440444540c40601c0c01ca013030540719400500915000c0c421a07110300e000c0d455055807a50360385a8155241264001c140c411070030b0000c01e1000c54041400105403500c241c3e880c032807a03103074400061958002c070951400e80f9070002904818080d40480900202d031800d480a00181c00362640043d01401034240e440e42040c01800100203041c0308024083e080740000e0b054a101a1000d0f0200c2d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 432175638 1250 432174388 432174403
    0x15090903051b150903040f09020c030c0d0e010e03010203100e040f14060a05010e15010513030209100e010f080c0105030a06050d03081501091202311509020901120e0f 73
    0x3001c94101a89095a0341d0440407400d0b44454480007451429003400d4003442c0f4011f25010300a01154041081001800104102d03a07030017291108560110b80c51000041491598801d8030f4001090031242c0c0c9414201402541e010310788564010390010709000318107100b6040100161103e49a110310368007c03071a0350f5243c800c180f16003c06410240f4003042c6040a4610617072058181504600401c0035041801420f40308082d400d01e00180d60702e0300754005115026590704042d40c080c814206000e10000e24403440400c40b00f000d000030801d6030362140000302d025881d21030401c942e040a00396041540c8182c4c0115444072941700d0000f84540c0b41d10200b81084c061001c02c401082035003091061400c1449043e1044890074a0524451030030f02c0c00042605075001d2000f0301904c9044030254041c040d0003c1030310050b5813060041c0481d4521f00075240602482e00030178481c0344d0000c5011030000c0d1540200e650640041e142c1d0310000c3c544202e480002c0c10301c4c2c40b9400c050300581c0c850f569404ca003441381c0c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 432176888 1250 432175638 432175687
    0xc02030d0504171c05071b020d03022d01061a03010308070f0f03120f150905250f12060b0304110103060320090f040201021c020a0c060804060f1509090305 68
    0xc144c030900d100003403003c45801030812410b014403d4034074480d5030040250001c00541c16103886081550b6031500340e1408007043c1512010282008210300102200007041a000a4200081c03042c80d903640d0541700100800e01c890181140b0400040c000301e00340c0402000c0d6907100f01d040c00801c481e40d482c0c80c600308031980c404400042620307002010131032040c007400f000752607184420000c82c059901c0c4901168614411402c2c85611b13900050802c030701145014950421481c002240c140c00c5403401042070500300600d801103260b1161030307080465688901015145180446442c6d41c646841c2d8406044031400503604240c3c0b11000400082c06144000130080c14103000703800e01c1c0e00712004012407a040106400100684041040007603030f80056a1440030341e065807030201112000d14201d00f001c0c02c0e9000078202e010381c88030001724958020b00240c41103004260802420b04c0000611090315040043c0f1008022080b000f0703c02d0300902ea00401d001032081c2442454044c1e1141c801442c101c00c038040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 432178138 1250 432176888 432176917
    0x1503040302070e2d0a140705041806030507150f02010e120c030918092404030302220602100506011e0f0306180218090910200705060108100c02030d050417 68
    0x14440f01e002c40f1b02030f64800a054041c2c400045c0b030559001003850255114420300c40200c000d00e008622941c1c1e0054001e0f541000c15100c200741c4603450003010001d42d43c1d03130500051030000805c00c603d106110304000d218284015146203030410900400d03175004829282441d000070810200c131a0b440c148542d040d4039000782508420700e0700da400079061104410b100302c208404110b01403525a400c88405038016850f040050700c83c10002202c000754214844109203045500c074010031a180c00049000032040d281e1002d01440e50f0704c400444000280c051003008a0310f5071061b0880441c0560440400090140b60000e4486d545441d02a6580d040407a01a480360340020b400e50041702d0074669120590302514460003505009203000d54031108a060424590784e504030000b140e400000d8002104501c2d503e84684640c03290900e40e072a28030a00c1059540d114611004182030002c2c0610300514450341c0141d400c01020b0011100945002003045070141c400000c1c15a001171610060030740c038081c2414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 432179388 1250 432178138 432178141
    0x1b190302010b0102120d051503030a0c0203190807022101090c051201140a05060d23010b0102061003030818010222050103050c0d1a1e1503040302070e2d 67
    0x90103421100000401411034004c001030346841c60350700c1c0c00c803022002d4000001400b0350f46c003101c111401d0004140c3e03541c1030100040040c00290f020a4221800d402141a250345681848944500720300800004004081c24010070025203422040503050711b0308400030b01c070364891310f174502421204429421a1035a240e403805000718109070200c41d0800c00500020890060002001405040c00030814a0056240d1000031b00b81e80310154001d00990b400364100304003603c40c041c40c9000e81481c40c1c0c2c04485628200c107140c40c039880010b481d0b018007003008040c0d803110304589044589003402840900710702078042d0030161300c8409100500c0b2207032141c0212012a400300d004500c0c004240e90002d4109400d15040c0305114038908215034507140700b88000541d004900c0c0002c43c1c00010403010550100103881c82000ca03100d1149414100b070b40843c0ca510240448041e5090b690005450160040c1d0004c1e0f0107100300320900400c22740020100a191000b4225001120134801c0894803006500c80d0500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 432180638 1250 432179388 432179393
    0x70203070c0e0106080402130b0d08030109051005010806010f0c080a050316030e030409050703231605070c1a041208090913050a230105090c0117070c081b19 69
    0x10380380050b103a10040e40042e5490540000d04000d00680040e1041520b005900c4080d1074035480220000d8010b0000880780700d02d801d201c08c2c1504244505c85101d81030400003a54101242145002e03600161910300154451100440c1c02c0070814598806100c1d200d05841c0100c0e00c00d801410700c8001c103a0f0340d26138915103108400c980660751903104080c582030074040c602c00e00021094500751a140c03032000807144d0f52040110081c01d003c01c1c801510095031034448124030005058144501308401c07240118000e94201210ba900c00c022015040c441c40700800d00108440400900b0210441010181499190001c90302c500139138450480c2d100e1000100000b0720305080e510035900c0b100800c104204560b042c0c60350350b00c5280c00b050080102164192541c1c00c07404003404100034800c010000c100516002d4601c0e035540d00e04600a90125103030007244080f4030f2181f001a80705102c5640d804142c01c2c5241c0c0c0701d00c0260440a0401600c0f440350440030354620703040022051401c107913404480500742c40e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 432181888 1250 432180638 432180653
    0x2120903030a0b0a0e01060f2c0a0f03080702040b061908010501030b01090608181c1112030c0706110909090c010e03010c0918060306060807031b0e1305010f0507020307 74
    0x843c1c2a0048040800420000d81074081e103070b04490b020f0520003c00c041594007160358404c8420b002850340100c130040b014405001c0e180b07055080c02a5050035005488100400045245110042c40f0410420500c401420f06420011882d171014107064145441ea65402c10030101c000d07030307610001e07003c1001048a0342e41350040328500c190a09100d0111800c00350001c002040040410312000074298850701d40c04820404041a00240100c000b180003444400511010f00014482c025125448561a00124840c204c0f4010440300320a02e04d030034801c0e03513036030b024014084c8a401504401d0280000e191545900b039841103180a01800c000016800050103080304684483d02070303894051040b800b40e03000b130050410790349000c52614000188517408005072006400007043c0a0038220001010700b0005040d1090383e210b085203818464500b918a02c01088a00c00d03440382c181e505012030041d2200c4030300a00158000c1c8004601d00c21043d1141040c0d132029104500141d000090000512151 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 432183138 1250 432181888 432181901
    0x1f0b0301020f0d0c050406051803070b1912020f09120709090609060507020c060301210804030606050a0605120a0504020613060f031406031b032803030f0b0a031502120903030a 77
    0x102c0c10f11754101400c0807001401806042d00000032400c8841306409956410801d90008000f008840e6940d0a0014a05480c01d50207500d0580410307902d0040a520707880fa4000c0c2d540340c1c3e4401850314204000541008041e000200d00c48046000f040404162222280a07038500036006a10100380300519182110888400078051811900043c030803c01076074410080328115403420035917800b5000403154030200507100d139000074440f0700c0000e4004104200f82e0401011a601140c0c450600740d1f0368007041d1003d1003905022120398060304005608000240e00c81608180090200e5003400e00042c4c43c03146c404010340048021a061003012801d15606010f41c118044402c0107500320750506401007961519280e0030110241c11280310b03035049480400c0214421000150311805078901d400c403403000c114409400360006400c05003625032403110341c0220071010102030405504c40b4511384446a0f884101d044c0c900c0115020807040c08460b405120441c0620800d13805550b6a08080600c0c1080343e14 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 432184388 1250 432183138 432183161
    0x10060906030c0801030213060e040c0509010b120a05070c02040c030b04050c12130623100902071e11220e010908030c0c030405180a0f0e1f0b0301020f0d 67
    0x1004004030582e9808143e05044941c150760100030a01d0f1350415001424040e009a80d000814108010034010408450b80440300d0607070b00344003d42d0306c584210056120340048084d402c008403010409921070b0b90f2207580d00003940d1034040608062980000c00f0b0740c801401d483c00181e201c0c418030446107058402c6c182c000c0081d03d03034140340c8810b2103c030341c85010f401844960382d001002c0044090100d640c0043e2001d60651180010142c10741c040d4610101c0207652900414030000000b2640302c00c14400c0780c200301c8d008005106141c841217468203131400340f000200c4a0018040b024003032500c0703503040c01e950020280030311300002e417001524504688443d607003044c0d56810900c02d01c0c0468550b0084a0b000540712090710740c1d0310701c00300e082c40c69031190303600694002c508451a40c64207180740500c03a0003204950001e21010203070000705c4050350369820031213001da0800d086007803108407180603c0c0c682000d040300200380d4810b00b0000030f007240c00541d105a41c000001848141074040e920800100c0306 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 432185638 1250 432184388 432184391
    0x40309080714010c150e0601030501050115080f060f03010e070e130c0501180b04170d080106020c12210a18030506010306110910050a020f1b10171006090603 69
    0x1c0c40c140201c01c0d80d903060780ca541d0510a060a4607024441c552040729000b5000f00000e01c500303085100700701d0347c170303c0d00b440152455441c000c00424901c51180940d210841640d40d0605151500e0710b50502c45600a8045a80910911010480703918203004442e04504803801410445291018880d03008d480201116450030031003160800040064020400392442031030030009600442080421105450f0880b90300c0c0280072800217410055402c01d40b441118540c1904c01200c105442610514401e003d02e2001d81c00c440c1e0b81401e82e050681c0048140c007040400c45103401100a1070000c03465405243c05c40b05200002c40308a900d070030403c110440c0441d9114540664a15100e260300d800040c0001802c00d03840d5007066071160820029200c4881c07000300300e640745460010f000380445c0d119000701400350107880001c0302c0040021405481c442045095903845100348000c1189206445524009204c070984c84121801d04a182092003164503026800c4004d04080010300400082d601410400d03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 432186888 1250 432185638 432185653
    0xf06041b1d0c1b0a12030b1c170f0309060403110307080d1104050603070c0201091e330203130b091c083c07050d080402030106050604060804030908 65
    0x107a80045510b611070300481a4986411030010301c0700c0340b072101d80442002e030b1142c2c2d00c0240a01401d2804010401703170b943c404004c061407244c14040300444001c040050000e10b1a448008a002010142600703091003440030301d401c03803828821034a604141d803502580e03400350b001c000806070004407681e10540319000650074104e031a96191090302c2020403004207151500c1c080011414488107607405407400400554582c901010018120500114242d000450030400018910300d54400030354045844c01c01c502516080403040151a02c5203101c80056145040e40d03900b01910a04071040c8a60b225409595501c00403c0e410101105c690424100101c08200000082d60f40d1001c00000701881c9000010003401410420701d14051800180c5070303003418140c5802440c0c08002e10440d044203001403050320440a81d184182400b90110040541e8084c5003601d00c100c1c0146020b80d401032000b000441d5203501e40e40801c04942103640b2040101d1050401e008c00c04d034004440744007a280e488000d0441 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 432188138 1250 432186888 432186929
    0xb010203092b06020706020c0601150905040513050303010e0a0b010503060d030e120105190e030a0905011d031504020315070203190e0402030c070c06020a0b0c0c0f06041b 75
    0x44545622019400303024030316800700d02e29031841c441d0a855410401c215110419410450007940c800400c1c04158003075074002203540362100798400b10000040c0c1da84d8680b903084c0803c1c400140800b40070059045c0181014500040c02000250301819611500d0b6000d800d0a01e10501a100c007c40d089050101c140100402d5803241c8031184841e58042c50000c4c4001d06001c0441c0d10613200808081c010f500300001c00440030409002c8980254014400304882030a02504584038014080c0650002d0101da50400c819849806c103050031303400d44201c0340c05000c54540007074a03050071011031211125a10b0100025860f081c0b002103a803100031180d86216180c075a00007034403840f4501c41c0350300390040d056804609502c10140c9403550640504115600e080000503c00300344c1000030b0480d15006c4840000c41c803544041039103d00942d11041c1480f584d00ca80c4011503088e007105090441520407030004043c480003c001450060b0301075850101c02a2801120201410f429044860000c8101190000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 432189388 1250 432188138 432188149
    0x8010b03040b071d040504030801080c010323061503011203080c07030c03120e060f18070e040611071e05070801020c100b01090305060a02040e0609011206050603012705010b01020309 80
    0xf80902546000c41960701409118900004288405a002850301042104242d0024039650681c3e0f00802281d540d51000f20045040d04c1c03010201e2501003242e05d484c049006058250550409001401c8002010350b01030012800d4000340d020b59101c85d090150b0005040c0c00104058002402c2c0d0107c610706240c0307031006440400f04400080400021070b4040d01d0704001d9600480c54440c9181c00d0b2821801c14240558510b00e080d10042032104a140d90b0000715000050000100c420000044001c0c0e41ea684982004158401e00c40440d03031000c006c07200001c1c60540002d40a1444040819003044103401c00320f103000811b410070148d5070306c100107860f00b100380000c0060401c42a6240810103c00000040301d140200360b10040642c40b4243c18400070300110340181041c0d400c070040c2c150b01c9950740d004001080c0301c00c0c8100d0300d00382101c0d880d800100b5030b1038000301d40c0300e5130150000ca1810252980301c0190f600320944140f502540d0401442000420b01581e414000244011810050044001b0f407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 432190638 1250 432189388 432189391
    0xa0e2d0604111003060e061e100507050d02010b010c08071a01180e07062012040b22050a1205010b060c0106030302070e1b0a0e0619080601090e0c0a020715030c08010b03040b 76
    0x5115180b0000c8101840900003071180305220040d0900d801040b20349c0c3c0151060b04207a0048441e8012000340080091052140549600050b0743c1c41d0781d41a050340b10b445107030340904c2044d40c91400c001440340b05112255211030091403007071060300c49103142d4140b400495281da1281c3c50540c00c150400c0040f20750102884404442001c070150840c0c03401c8494902d880101d814078800080c000c84d0020312120355001601c0580d19a02203958200824841d09000366154041c1550080c43c0e03400078820303a1501a041c41800d445000005401e05000c800110242c1140e401d280440e0745481c07082c000c260381404020002c103507040902404d4280745410541030804804a100e00d41e10129100d000d851141041c003110520107040603030784003522051008084038501c1e00c0e07000700d0000404141d040d40704e5a0380100b240c100301c0101c98541c45456180c96281e210030a03d40841c410440d02140030286903840100200c00b54800043d041800e180103805150140d01481c0303644000d008100100d6960340f0343c00d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 432191888 1250 432190638 432190651
    0x10507020705010e04150b0405151c1107060e0f101104030f1e2d0210081b0c030d14100e100e0f0406050a0e2d0604111003060e 56
    0x1001c12004d14011400600c1a01030140400c3c00c69000000c00000d01c0001f802510f5050320140146030b41211101c24074804e402c0e031424440c0e00c14848007282e1304658413152403040b19103c1726203814520348906050f17070040d032030b58007280e0403d007041203034800100038101002c0b58070b60041c02007040820807480caa016500c00a42072050181c1480704109242c151707180e00c40440c83d048121001d4905058911175010402d01009500d03104130b0144807840d00c0124407035075900529100c500c4404c054101d50000d400b40410700001c442c000134440404040015210110543c0011030700c540c003054181041d034000c0d48207000c02c40c8006050240c0c80760140944c1d8196108c0703541d07801c00d648601014220912581d80866030103d0510140b007000080204414080c0b8001d032001d01940e00e0360f0031100101d072210300001010354440408403011000802143d401580084013540d410425801824109202200c04452070304000c0b4030041c00b0300e820a01c7c800300000501e41003080e01d0400c1c01420380e848004c0d211 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 432193138 1250 432191888 432191897
    0x30c03160b130b0c07060f0302070f0212010209040c050c010b01110a0b1f080307380604090618051506220e030f07020108010911030402090405030c0a0b0603060901050702070501 78
    0x700b0103259030030803002d0007855048840356603003981084070b980b0b0b0707001c0b4001c03040082d0a442d02c000045209000780c0c2c000700d80000140c1d0f01c040380b990801540b520450625030f4595000e0198110329a200e100d46250710409456007591511410707030250845074800c2c0540e05210f64401d800140b0035000030155400b80e40f08421a031142c03104c0e803105050415148403409803103c00000820b0f03262011001e0b0203558400c461183c10042d112034810741c5655034065045000724104070882c0004051003902c2d07003240d03000e03100113100c3c030040c1c80b0704080d180241042d00034140c0c901c40310b0003000000c1003c0c1d0340e86070000d40e0020503410800001100d4a5000300b08505c00010f00039803e04249803544103103a03001c000001c4030707078a103404032461a43d0f811440090340405c540c20000107135003a0b64020b09401c4500c20b00b105185548aa0804c51408000b4100b56410701c014030403540d20807401c0000c40c513114001c0c038908a8515000b4100b51a0440080c5101c504d40d0420060040c15a0002000c0c02030740c509003403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 432194244 1106 432193138 432193147
    0xd0c031206050f01030c050c01090305040e09060105131d250504020304020303070206160c08010510051002060f070e04140702011113120f02100e030c03160b 69
    0x2400c3e41209048940e4809580300398007540400245040150615000315030a501b100c00514003100841c00000d41800300000a4001d6a0700000c4d007070040440e5030410021511884900c0419554181c5858580c120008400e000c5c034400d801c24400c41e2034080710300701d101310b8084103900c0d100041c0034020400f08503803c02e4000c4138860317078001e40210700d403911b11f909104481e4000315845801008851468000905420020009003c4400017082c40d0500b50810b1a505456500c801d201d03024904c01e42c034803d84c011485d1540b122950002a0169036465000e540c554442c034149030744245080201d070b104514680c40030380505184d5008101d00200b0426141551083c032030420b017282161403082204061201010454510800c6ca40c041000180d01107950a14202c0f030100100d144942d00304880e007800c200f246204041100200554202240c07031481000450107030748805c0c0400038 = true := by decide +kernel

theorem cover : BRFrame.Cov 432014388 432194244 := by
  have h0 := BRFrame.cov_init 432014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 432014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 432014388 ≤ n) (h2 : n < 432194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
