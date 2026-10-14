-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2502
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:54:07.009439+00:00
-- url     : https://prove2.me/submissions/823a7274-e877-4df7-be49-5fdf11ec2983

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 449820143 ≤ n < 450000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 449821393 1250 449820143 449820181
    0xa06121a060702280f03030e0d0c1710050c04090b03030a1e27090e0d0c110102162904120201030b0402160b043f02100230 54
    0x35a1541c40d0650804c1480b209120a00e95107405011016a036103003d200c019413070307000a4001801c021051000382c1080c407101251907604c8030b1559072a03403903c2004819110740403200c40755802001d5040c10700c41810f00945004440500e40b00d940c039807610f100c803400c55042086240c000e400a00414881641109003c00e0b14060340c1401070580c000c0100458610b8984003e994500909155080321003145040c0b1348251040c02d4401c104007000c0c0f0002944d283c0d2a0b00e0310380000b030140240c050000e640c540c0416408001170048550310301116003040ca450b000398000b18010100074940c280b13405103220701d441024281e100c5042c40d003401e141203e1001062214041d0506803140030300142c6454950407030301d401951035844083d00d41e071407030164641c610a0b10182d0b50040c400c82d00c0d101540b240071445c8806402d00200d0302c1c81c0c070890a09024101140001c2d44217500405041035124402e90004105140da10240004602900380303141452035101d04201ca0300c01450b60030420700c2c1043e44031041c0c02c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 449822643 1250 449821393 449821399
    0x516050f0c0f01050d0203091e010c03151202010e062808100303080a091103010c0302070c08120406110c10051207170c071b03030818030c0d05030403020c0a06121a060702 75
    0x28a54a184101d490700a24220103100030070310720880c1d03800c09c40c10352000100f0fa640c0d0f13901340311030704549805203156403142c000c82c2c070000703103003078400b0010341c0100c503e41055000a40101e09242d40c19420005140c020300303022080f4020746027112205540a0140c0e580282d9070079901c1c0703d0314119140140040c60051115001c550b442140e0000d00c11100c68504c3c100c08028020f0081d4821480000d000c0c2d04a40802c950b840021200801d2140c1d01064102070300e101166030034145450140c0c100c601d0498441450111b000d500070240941c1c840c0c1035540c3d00851103840d82541e1f000004202d00704c00da4020281000c0000c1a070342c038007c0c1c14144100d1600030021540d201d48403038490401c0d8a81e5a0a0b18040300f80201681000040640180400d88564070340d404821144e401104c0098403403280202c00c052681051400319521400b81002d140c00c180a841214400201d420100d070000c0c80035017004020400e2030344103005d1203109000386e00503440e035400440c0054000c9008100d49004104000348 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 449823893 1250 449822643 449822647
    0x6120a0308045a20010908030a0507020922030810080105010e0a110309030901050d23101d0a050c120a061802030c03160516050f0c0f01050d02 63
    0x60a2400ba42c80b000c3c100c032550f0140400c90b2000080741c0c0c00c0844030030b011a0100358000042c01c0c1e4440307484075948180e401c220240203802020089451024a015000c3d042c0043d90501040a80c0100003828075094651911691122107004108044400400e0f030760310711144030860450002d0381c2400310394681d850304082c00991127140b100d18a103042c507040f4030b043e58644400010387c40200301c5514010942d40004011074144050343c201d19100803540c00c0250b901c108008105035100c1c0e402403101802d802400a6060007994180d5402641070b0030240d8181704003811312541c1003440d500e020003040b401e6401d2501e040543e08440c1d00c0c0c407009007800610f595400c005541d0801e080300311500c010780c171000c4444a161801c1c0c240d00415090207200049070190181016192691003160b0168801080c000d0866803924061003102c003900e42c403d82040414425120580700b4901036580346489000904501c0d0030110b100d62600d404000c0d014030032810504000c145907000400c55280032145039002d6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 449825143 1250 449823893 449823923
    0xa022e0b0d110f03031936060807030f0606030504170c070902030c0705071707081513031e050418020a08040206070c05090406020304110d0206040506070f080c0606120a030804 77
    0x81c103602540c9a070203056001c01210303007507041c7c0c00f03901c0fa444241107921006041c0c03604814402c0202e0a8101e41505841540c41409450302504605170301140d1443c0200d8202c0403183c4100c10366180e5440403003ca5110401c1c402041001c07070140d010503c0045d2038605211003000a10340c0c0340110302c00e00c1c1031154008086071110300003104503105650001c049170051650780b001c048016403080d07240540c0b800303040c030f010030144000300f141c22040020001d00500c2d03454416168a90300101c000c2241031050010240c640b50540300d140420280d5240c6505440c2c1d0700e001d82c5a8030314080c11515080072403042181d04a0250054001500b258040d070340075807240030702d00d032141034044d1030f410040d403200ca641d04100400c040da8004600c0396103c0c0c60410a072501d11024042d2540401c0b60080d40315900340700c00d104509241021300f10841c091851094195150f440c1d00c0c2e010350150200d40104c8e00501c04010702c034100840d8180100d05608001c0a071010a6140200007007400f620003007100c000796001d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 449826393 1250 449825143 449825149
    0x2c0d0e0d03090b0a11060901020a2a0c080304060f030203010b1e0d05190b0909151b070f0b0601020a0f0618050607020c0915150a022e0b0d110f 63
    0x4009032030450803c1d6035070591441c000d00022204083e07000f003841418005900d542041c0252240428070340c4a6051024940110641c0002c0544001f4025400006a040070801d408824030003440e0351800303160b07180d00303080006003249800d62007841454010001081026000001c46407000b5002802c1c0d1007154004008940c184a44100c90114a00b0300091041c14041c1300941ca01400e902202000500080b0b0241704e442041140c1c01c980d00c2c0c00601c80001050500c000055000d00004010340b900019001000d020b5000030360103443e84e001c1c1c00002000c104801c0d20391034004209000070710441c0c90503684e04015103403016004203410b4982c50602c80c21002c140001d9440d41d80041541c01516100c1c20081d45c41c1d00108519201d14000030101c3c8056480b21542c09801c0350140081000c07440541003c60039500100888085100f5035188002d05402071006040c2585a4001804000020740c909400e503107601844034824020182c0c24000038000001071051214140e5488070107100c58400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 449827643 1250 449826393 449826407
    0x50102070b0f06040506100c03200109141005060303030115090e2508070f032705030d05010f0b2706040b130902130e0c0403062c0d0e0d03 61
    0x4001e1a4141d24420300c9000902d4201ca184500020f54040040c2d594940030805013802006145012924046039840400c1c03140c2d8107403c00d0903241e030644031580425540e81d1708440703000105884803482811350714064402407181d070422410040042c002401e01500103034a0784811b100f200248190400c1000c041e5000340c4960000b442a070801480602c3c10611007861904003103144405c00d04540407445403180100f10031400342d0070594544d080401080010b500509118000001440e071003c60f51152714900305420603018880e41c0a16194060401c2c02e1040c4c600c1a04600f808407180d000070b0040f5240501a580d440c030440d010201240741d50150a20519181084107821900000b40441c0d00e0303c003603008089600044c40c40721021982c458484040f0302480010840f21101c0400800c0790074507589405812103109404907290035075a40e22507045032180820910104011201c140440c1020000d04038010100000740c01c0e2181151001081015020981840340b4030314074007501030500c2000f07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 449828893 1250 449827643 449827657
    0x614030c103903020c0907090603020c0f4e0f0c0106090c0f08010e0c031b0a0f031b08040b070201060807031104061d0a0c0516060b090c0403030207050d050102 70
    0x850b80300e07080c1c107800c00ba18241c141c4020640151080030206034070ba007480c440d0b140c8a8452a640c1003140b0f400c01208a02a6010b00d004404510401d800c1614440741800920038204503200d50300d40c54903614905034030810916540459407190b0201000ca008602018603845c80108092590f03210708507103814507035010b045034901203507207000c0380810b4084c0140d0041c480c1180036110140310071028a42128100401d00507581c0050800e008101407141250181d0f421010b20101003400c0d40412035640f106410400d50140054201099655216010700c20012411560b0842d08a02008850041c0c240480648000c000a01c100001100c0510030361140000e0110001600c1d00a642e0b400c2034804005040c2440d407042e460a58001400003588064843d41035100e204440d8698030704401c1b030014044210640309104040107840c50200703884200c1000203108542c0018503442190a022a10500414210500a08200c1070010a40024560048501c21204000c103101c951070180d0290059034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 449830143 1250 449828893 449828957
    0x315020f04080f07032a170111031005150306030d080711030c0709050a021306030b010203090411183003091503161706100e03100614030c10 62
    0x3c01c0401e50400708a01d81101c3c0202d000000221007007501400700c21803811810081d05103040c0404c4a4040110041849015000000703a12400e05c0d02e102107035802140c0007003406910030400c0c007162a10507000f964444560017500c0c00c41c030380075010075954840b0101e004140022540050010751081d0b400309458841e24081d2900c84000d03e07607495139401c4030701032403c00900300310003d01c2c1c1d0b102c140300ba031b05040070240340030094901c1c00009070010400c4a0007a81140001c0007a5285a20343d405405120050381c1320090b610081c03042c514000b5010320030701034400e40285081d0070702c800026a485540810151707100761854a8004001d18510030710300f100b500843c0040c00717030309001c0e080c41c06184988581e09942023600a034540c122550800c8202114403443c405010414500303089000340c2e44600c40b420906c80b901c0183d0006441c014a954000d01c0143c0c80b54000c0c06642d00039650061075403010340c0100030900814001401040d522448102080030000d40e60460030031707060034980095070070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 449831393 1250 449830143 449830153
    0x2a0815040b010e06130f0c1119020607060213060f111b040b01111203060306070f0207090c031d01020309070f03080f090102160602010c110a031d0a0b03090c12070315020f0408 77
    0x1d406c00c18040d180444804002c9907501300c2a01c080d08020445501a4401c514140c000658560030080305400841c0c055821170f6003805070009101d130b1080000060310180d124058004449440100a81d101001604c150b4108030031310710342448030a03500202c4200403500460074018010049410601004841c0c00d90f1041e001c481200c200700c00021070040c0025029210541d0380c5090542d005a04125040d0050380010000c015009850780000301c54101464046a003411128070041074203000030500b6626503001090084400d010850b0200402d442e9400c0c501c45442d5448500c1c0501a081115000036000540151540e00c20300505859200250184000c103840b910002c2c0204800310350000070840050030301110120008800d042c4a6140d541d119100c506004290800c80c80102240c1e0403d41c03510700810700855070009517208554a00040100c245aa810891120300081c1d45103402e0f0401c10052006c03c0100b000a1703a0411307451009696a5030140281c00399105540c4030307005074014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 449832643 1250 449831393 449831411
    0xc0906240721170406050a0b06030709062a021002010b13090b1302060732031905090102100c120903020606120c100c2a0815040b010e0613 61
    0x1520511800e540b681c01005540320031000340a0310040c1c0201209210300032000c2c005030004190381c000075070004800d40d0104d130040e007460115a458206441d01030228118541c1070080d07a90150840c0502c1c4102040421034003c0d16400040468884d1406170045120200c80c98005000350002901168041d246100d8181502c2124008003407c5204489507904440403c01100e030465008041d41d400504031481c0c103180e60b460011110b510071142101d0000c01c2c540c0e5038001d10b40038040c0f41184150028594841840d0040114a1120103281041c0501403060381c03401d0743c0c0021807450840c103001000a14105548040d541c540801543d01e00300d0303040c0480c2c10304041d03010a1580c024081611004842c006424090303446000b050740064105080c1c1c0381c9144118480d02c2c004280d14052142e140c2d0b504c0d1411058841c028000000500940703804104000c100010007010f080900d030440c0a002e1410300d40d03a0f914803140c0621076016195405001700300303266204c10052004910102c420000011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 449833893 1250 449832643 449832653
    0x70312171b1c0b060a1e1404090906140901020a090b0f040e0a020f0f070b0a06080c040b2d01110d0509300714060301031a0711012307020c09062407 65
    0xc00200080c1e480c2d01d0160f202820501980f0b41d01030351000340801f18101424130300917600902d4035075810b481c01c940b101c100705026031460003d94000c009480005d07940b000221009450240d05603c10702014908211130208400070ba415502030342d00c52800103d02e915135000a202034068400380c80d8801c4800958140c41c90044001802618070981030101c1d20b0380c426695030125a014407a00e1602d4000c0d03010080c1a161950100c180e03028001c007440d0f4100003103402c0200310390481c44501c624860b81c1d4204260341da003102ca4149400e00076001000c0416000c0c1c8000c00300d004001d4254002e0300302281071400701001c0001c2074405000308006003107000300802c0380c0d0365540c0c00b842508401c03180c8440d40c5006052041c1182d040c0c1760003404201d0404e545210042504400a00701c134100010304070b18114800b400c0c020807611f04008a032000c0e080d11044000d403082403029100000b59072040c003013034070f2a0721829400c503880030040700c400d0a00c202501d8034003641d8540741c600b01001400016507c003044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 449835143 1250 449833893 449833907
    0x1080c1c1b1a0315060307090e060604030f060504021c0807030e0f062a0703020604260601091e0c0f08091c0503040c090504020112090203070312171b1c0b060a 70
    0xd810a121060140a5806221046c1301c11f072000d00014400090a00054800702d205030707001003018024515090707883d1541d94000001a13821a03440761030788144001d45c85d00401c2507801204800072104090a01d98806090340704a1034000c0078407a200d0070003240365840d1144680000409008995541816000301e003000243d20f802040c200148504a80140c0c00043d00c5015294040d141c40e1600c2d05120203110140d803800d00d041040c0c800d103a810100300d4001c2c0319250017030039500c01c003040300743c0499010799000500c803081202140ca0012000b01c10740d40309400d0300140003903081c800482c5d01c40545050030200d52075003181070403510141e12a090355100000f5846140682c4006280741d46a414107815150b094038043c3c0015050328006e226075103a44d000220042c401001c86005d1307552940da8501031801106a503000c650545e120f403029851006100e98811501c0040c40d86000d6904000081402002038421080c0145a1110701d0355800390302204600d0001001d640c1c8501824a000b8401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 449836393 1250 449835143 449835151
    0x10090516020111210901060302150c0709140c070302011b020c0109090e060606030907030c0303080105010e090912130806040b1f180c0e090a0501080c1c1b1a03 70
    0x15841c145140d581002c4039070540d440401103041009071411055241c5648440180005d40955030312000080140e0783c102000d107050603001c041548070b9a0070647c6a04048550f807080c4040f0b824003441846042412000960000403040501c0e03d070400d9007030890040c05042c03a40c0b14200da2003503075542d8007600050749100d109003d03611400007980300c00c003602c19501401c61407400c035448180410b0729490301c0d902955124000c14100e40c0c280d40d60340c4a800400515074000e1b0302080c40c0b10014402940c0c00b60038690444000c0e5000c21450901c845410340d0761043c03840b4140d0281c00860b1190f050030b460403810001305554003c8420340e003450308003042c880c1803d0300c0400802914041c410f8010384401d03a03103011294030003a080440000d40340d26602800c015413080080020171404840140e989641080c042c1b0030703d040c002042e43c140380700c0c60702e8003a07060706982c45418030300307100e810043c240d1200e030051945c803015034424030013803042c50341807482260481030200170240d0b009909400484003035489 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 449837643 1250 449836393 449836397
    0x90b0a0f0612020a030f02030f0d200a03022806020d02190810051309080a0905041107170903120712080f0103030c060903050c070602070f050f0a0e10090516 69
    0x14042d030303640d1007802589107188001d4100c2e80b0b00a0410100f105501d02050715400601601c0700c084442e1446c60a004410b079451000c1041021a0503640b20115220400300780b00800810b10141d494a020b0350304c110020000360180540740d0080940308010340098140b541c001000d64031141c07070410080103500312045ea00d82d4010006840c5400c18891f82d54507014000f01c00c0c01d40c00075410030050203181c01c1c03680c6103083c0403901d8103240f10001d2105401810641c00d5981d48007025401c082c2000f0a0f200310011050301c0c100306100400206240403040d19a00b14240405640c8246040c00f1034107180a005281490000100310b10052200000c1043d0302080329507500390440d96030042c4a00000300a000113000540c405101400007503440c1d0013107441c42e0107414042c6c1000711047c9054035005854000e000140c02046080004c02404001c28010b000700301c40141c038480f41c01001c180c450025120f80041c030144030300403030031910151107080c02608a40b07000b485a03140c02c120191943c010309107a040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 449838893 1250 449837643 449837651
    0x2619260c1b090a2c0a200f0103020c12090f100f080f13080d0b09070c03110304080a02060d020c060c040806131e0201110a0f150608070506030901090b0a0f 68
    0x2005000c0c0d100d243c8101018144100000c0d081c4c20202c4d440d00510034012080744609299140070030511181c0580600704524071038103000c606824400e40003e201090303070501d40184095030030004042079584600482c0500c030358407107004000042c80a0300e0380a420303800c942186441d56002c0e41c0f107a046519071045444900080e05c440c00600040903040311002510004506440c0c0020b00c001c0080003490340404001ca04114090002801141c050300c04001003402581d0070340070150041141d890001203080510300b401d1400710615243d55180400a10541d0f0018400c0d226158a0307043c0c901030b264140c02c941340c1d440c0101c6880341c9540240200314a51084800154070140c0c4000c55118113a07020924040d4149040c6646010300e5014000f02c5c140416110546d180240401244413001e001c2c00192540e00c00380e061691203001d20f18102000217040010a01c40c40d0303070014401e0101d550a50b81b1035980e03130380e6041031801001020402801d583c1d194083c443e820b5050f17089a041ea000401c0100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 449840143 1250 449838893 449838901
    0x8010b040305030412020d060e07150201020c060609190f06093b030c0a1209050306090604080f04050d121d0a09152619260c1b09 57
    0x2415000d6480010501da2041000f406505c0301030005600341031018188a0302e0310407540d608802c1d500311100c044410341c4825410070060051015268070402e190008501d8130f00e040991503108c40f0002d068a0083d02094041103000f01c002e902c94203894100070003080b10340d00201034280901040c2c4944855107040402544250750070801d041401410070302036011507400108200d1400d081c03102201103071b02007808400d8012105000e01701c0090b1040441b955001103081c03010701545880e0700594006e5000b68104400d00c08001742c82a00310360030031922600c64040e40184242442140c010079003100d4420360204c100070040244203925a21511303050640d0009030048010064002c0800d03504c8025050100400c203119403000904401c500340c84011541c40301c840002c12110701080c480c414040e001240c10320a403c0c0101200c401c0b848a000c91002c407141c0383c40c12071208034018011543c14203160035403000441000c8031b2031109040250f030401c024412150a684d11403822907400340c4c0c6200002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 449841393 1250 449840143 449840159
    0x30c1e0c280c0e1b0a0e03100c0e090402061b060609010b040e0f061f050c0706031806020d020403050a240504170d140903040906050901060c080708070f08041403010c0503070c02010e090a06060801 86
    0x9d07040500542c0c1d00c40042d20325640412a500c4009030003aa0400b00c00c0103d881d4241801c400408c269900d5030080c003050800b2014480c040a0580c09000d6200d82400248030414031414155040201418886660b403940b5000456100206a00c000304543e8684e03c4060250071801401e2419044415510103c0d40c4050a9007070310b90450450012040f0100c01e600022078560180444401c503100c010304040d00c079a907003031410070401d000303641007103810310240d65440040064a91f0089032004c01e0000c2c0c1055030711100c4c50b15420101d051001d03008070303110300c00d06450343c80760b0ba1038415a00c082244e400d22001460b101c0d442809044456800d0001c080340e9400c005140c64100c030516a80c210a22209440740512508040011681c5420420184001c10300070444180118020050940c0d65441c2000d034030320390303898046418000e9062803192213110780c0003410340707a0048250402490200080c8012981001c0c080c2ca0164071601c52020f203d400c0f280b640c07101080e2099519100502d03602c41c018 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 449842643 1250 449841393 449841401
    0x103030807090f120f061410150906080c090d0b09070515040303030e070f081516080a181410060614030c1e0c280c0e1b0a0e0310 57
    0x40110011803c08104026a50002c52800803802040408911041d46c0d03100419601000a00f545050107401407000d255070b00039100c0c00403c20700c80002d81c1410003c4010701500706500c5500184503001d4000364000c4082c00c1120009d0500800c2d81600080a02d415248000e080d910040b041c030401c0c501241506089289481c6000344012040c18146075903001c401410306c00e010481a4002c116001071602c0150588030050042c50015111181018074080d541100007082d84102c90040380c2c00e0000b4035001a901600018040e03400302d070144503200e4040d151661490002c041030300c54400038101c10000f2600010b076032454030b03041c403c0541e2084201c0e03414000000021800a04102192110002800405000021242c4101d02204c0c101d07030455586c02c0504e600c982c580000140080c3c480f0030301c1018801652016a9080281c0d998842c5003020344103004030003c070f6500102048842605051095000a03135a0201c0e5403040c111500514003110042518064428141e42e03007802081406 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 449843893 1250 449842643 449842649
    0x5061009020703050306040e010204050312030a051014010c050c10080109140f0a0b03120307030e010501240e0303040e0412030b370306151806060f05030709081005010303080709 78
    0x4e40c15003107454130010800101440c2c0340c1041c2d02e65003007200050a031424407001080e030081c01141900c900c1c1042030f42050340c100401c0044114009601800500e0b050001c0c8980d41500703180550300d003011494520b10345030700306e82c81c0b681c0b003883c03481c03003009580e0311020040c143d580c0c4e0780003403103211041106001084410344404190443e940c00248542c0c07980d0784403401401e4001c0440d00040d0f030303a45454051703600c16240640000e450b807940b0641c018090240c1c0e40141b01d8000700180704052b500b04101c1e10001c400c886410018000101c540c01e076810000d4a0161880c1004803038141000c1c0341007845c000c2d400400300042400c1102842c040d161901e000c0f550135482c505011441c800160042c20000d043c1030112800b64440e540110100d11a841400f4200714080000140e0b2428085c1c0e05603414050b81c2d10021301c508104041c0321503640a40340008103240c6007030582e160b40b0340340790550f64043d0f103130081d042e1841494040058040c007500007134100c9009803998500381d01c0d132132401c69009176140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 449845143 1250 449843893 449843897
    0x16210204061211040e040f0b040b06031b0109170309060307020d11071d06030a0510050702120c1203071209050a030f080f060603070c0203011803020c0a060e04050703090f05061009020703 82
    0x480100301c170810000c45035901500c42c45207494958a20b070780340c2c186944c0c1076400391107580c169800c00ca40c40c01c003041030044120b00000046454448034000030061400341c0690303009251611547d8500c01e404000351190074100900198032440c0c1910000e6845103002d16103c00200350030850940e17a03102140e400e06035a010b08000c40b01c42c11111488201c030354050b0407a03402d8030820507018080780c01408401c0001462290104081c1040c00c4e0080c41c00380469412011004100300c4171122810002c0c40400b030045d0200d00c191241e48100c4203403141e2580c00d8406508504000003070080040204110501a2007901c2d9960911016203040315503070b42c1124440b0306038003402d003c1603035454101c002c1c542c81725191900000403200b950129003982c8035500752500e52403d42c0b03411000c2580522072002506000d0714054001803411100070200780d0b900c07210f280615603c40218000c00e00c0fa41001c1400b54000c18044100405450300f90782d910800c8411011443d0b1800c40820740310811700890b01070a80603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 449846393 1250 449845143 449845147
    0x702070e0112081c14100602030a02101d0601030312050c19080a0b04020c010b04050906040305030112082a120f0706050a24240816210204061211 64
    0x81d94495403c3d43c01241508503203e0800e840300109003540c0201c15540d100b65000240c181400c04d202d41e1110b100742c01800c1036400a02a01c1041540000e0000c07500d0282c070004240d004900d1407050b003800e0f50181d001d001e8001c1400220038190080c0a0b10090f240000c000c100d80e80d0352a070420210300500b140303034040b408a060401541441440156001145007c0c0090420507400c0000d003203900c2000201170390303515403142c104540340a1040c00d07404403420020701020300d01a50018110701c0305014514001e0100d41170082401881001e03202a0034114a003103041c8241d1908480c4500f000d840804070754890030180103040b070754046c10b554002c82e0030580d030741c02c041440e035aa0002d490001c040c500d4056036030300c108000811659001380701d001c885244000c1176042c4071078607500701c045000641004130901103082c03c181e400040350358025102c1c0000408c03030303254800440c1e175a03184007402030110150501d8649485e49075802030007151019141c0d5130102c1c401c007000200b512031003240b1810310002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 449847643 1250 449846393 449846429
    0x1140d0204050714031303030605150f0714060c0d0b0307081c030219090509010603020304020f01050702060c1c02100e071703040b07050d030524040b01030b04060b030702070e01 78
    0x1d6004035030000007600304401018450b00384c4010541085030780c1c040c120b91020400c014107401d0710410019000039117a485024880110016480c401c6100a80c20301c00f000490405002680c002e4502440c17070081544c0e46800d00c1e03e802171060700104040d04500d482d04880051510f8002031580403a58440064000c0039210003a5500b4500700e00025810300d0f400f00000c1904080003180450340381c00da512040c0b00107081030180210310354141c0210f400d042c030403c10710015a8601003032901100092910301d1381d4509501c0403a209024001d0700c500540f045040790b0342c10070040b001d0440e501c00740382e00b16441019540300450031340740540ca00c000c0c2500403a005000c10080b81c882103030404a0b070003c81c1e150a65540e0106299440010182e0301c58019444c52010140c0c1030003259001030800c45210003401c8d80c1040c1200d0650500441489643d8400b0050500c0c5d002c1e8000d00c1d110725006204010069590304107006a62040b180c2c10010301a80001060480207003030074905035a0b8a803008100441 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 449848893 1250 449847643 449847649
    0x1202031b01021e011d120d0b04060302120601090506060703052208030c03040503011a0f0d140a0f02041409071e0b04120309090221040f0804150801140d02 68
    0x401049603504500801010400c0314003580c5401c40c03985500000040c00c2d134404000740c186038a100c04100c425401000d04030b01a40d81030010340c1c0b83c5d07000d180c000150044000e40094020415070748020b42000c09500c001205800118103581212803540d020700c038075514001080041d2040001c020082401803081d100720003a0711881c2c246801101c0b84250905841c3e800880c6550000c1904480300c1d440001c0c00d0102c2d080078054080380b002c8401c003140b948040d240000708480d4101d0009401540f0080710001402481c0c98dc54101c40c030b0090a4230403410107410040f81444144409030b01440c00c11842911541c00d03080720600c140111005441c0090400b5888103c0745d14403018900a1001c1820101c0d02c40103482c000d1000700624071400031048500c1c5800707000c04002d035110215151040c0050180d80c0200700c0350703408409001c3d041050640e11450250082c450444025101c400c1c0810040b407001c02f24010b56284031195220401160fa0710040380d80800b08021034070380c00800034904600141 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 449850143 1250 449848893 449848933
    0x71803060c0905030d050f1e1c060b041206051504020409020702090c070f023a02120a200a090c02070314010606050f090112090b060411030907051c0b04030305010906120203 76
    0x2ca01290540880948d1300d0f0368000c650130542c040171404c540141146109040e038442d08000f4210100d0540c1058030b400c1c0b562548940030300020300781d95200d20025a0080039040c032001c0c0700300024011511141c460b8000340003900076513022400740507010702180314581081c041c0c03545558801178071211061700313a09102d040d0340000041340b1008942c451915451a401851202000e00000a40001e003410700400001c9200c12140c0030390364114288840204d908055050300514045101d07507140750502010484e4036503180c3c40213403101e20f0101c100482c20782c080b5491084134025200303d06500d840c0c0c0e280c5030882d00e13184030700d001180081209560300070107807014000d030b007005041c12481d88080d180c000c02078504007001290509054402c10809280504c00c40d1030006040c4207480c114030b08554001e945610038001c840c414614000d1002500820b4803a03004050352200151040d41090f2074064054102030044030320316414000046141d118080a00b11600e4004004092200c2200010318001e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 449851393 1250 449850143 449850157
    0x14090910090c120b060f060a080a0b1305040804170d02071404020c01020c0105190924021c39110313030f060b030106051503071803060c0905030d050f 66
    0x440b501070000100c00c003181001c0e280e61402204620b466150042c200b055001d2903200c205d00c92101480b069190300e6001315016404a800003001a900358000b0010744080003000040e0706c8181800204800c001e103020291080320550f0118007180c001d07a4000039122042060b21800503031018408210741940c0d90b40e46c204c86000a000180760965290015017642d0100c10644488d0f074440041c1710014510034241203000390418010044084503540d42e55469400c0c40c0282101c180205a10508541a40c100c0716a0004d54005040c44204680c0c0304020706204040b04140c014646a0100c03040c2c03001d072819005042d5058410102c82101320180c030340a045800302c424910003807000303075070582002c103d00c0c0203540600050240e06e4018a01f441c00d40700350000142c0241d050000800060f00d40a040c0040180e52000207a1a640c41b03640444421002c103e4180c000381041d0b1000040c0700c110b500410444a50360b5441c214a0b40b5241810303900d0701d008100d4400a038040100846205005d4003400c80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 449852643 1250 449851393 449851403
    0x51b0d0b060f0604090207030807050f0901050c010e010204080d11060118050414100614060705030405120102121e0a05250c060207060b03070906080a0803060d12091409091009 77
    0x20107441c442c04240542c2007a0004004190300050035030600d40c00c05012940190b680c6000c2c0c0c582401c1801c55200c41c0154468141404400b041c4480550000e422548605140303500840d112540c4405e82a6070745000040c580101d41c20701d4210f440c4030004202a410b880d03500017001200805c4006080080100800903070b641d5100c1c8040c1c08041c032061000c0850b02040c4070012850900341a8010080c00c401c55665200b03036010042c800015a01000f5034086a108840518031221030b0180e00380a0310030601e4490440111008001c0341c611102c85402994448401c181d850741c1d07844100e04102c0310165003800b10381004c0c2698402d040c10150440c2c200a81c42e1400c052001820b40c0c4200a80c1c000c0a070445020781c4030b800000c0176044c01c1003003000500c2d03025001e02c802854130745031507143d140250b8082c0880c2c40000020340396403030341c40c031440c1540e82c440c1c03103c5006103e980c00108006c0c007500400000f01e4100208018074508402c3c403030701846076140503040d5006591101c20040c0b00054044403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 449853893 1250 449852643 449852659
    0x10c11030c030609060a18020f010f0903050d03050f070c0f1b0f0807060f17072d08071814120c030a05010b0307062c0319050109051b0d0b06 62
    0x300340d40b030910140703010b9100007005204604000f42001d095034200c0024000140c7c00846130000f682d50441c99650800c002c2c00c0c00c081c40c1110540c00c071104000f942010b4000d02c901040300103442c0d40b6510061041d451071800840e25128504d0482c1d0901e01000b000e4244541d80310110003180b9480c0300d87c0500b9060740031400d940c0755a2040c0b0103e102281d07012040760340060324108065500521181402078031803402000e0729901401041801e030003d00100c3c01c009403240d00d0300c0c08080b44082d48414a0b00c00114002d0070030340311002005802c00f01e805500088140201e0202c5840b950b2014060742d010f00c100c5814400d0703010030b000004105013003134941c0b807180c124178407000e49041c854494424000d20021640710014020b143c5803c00c01e40c00082000030603848011480d0041c2413002103142014031622550b00311200103031174a0b405004980c0d040007441c10302000c00a055021783c281c54481e200b82c0c0c041a0303007030b042c403031049100d024100e4101c0c20806008000400d00a80c03e544400001c1001c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 449855143 1250 449853893 449853913
    0xc1c21030e01060e060f04050709061223060103060b0f0d0b0a0905090604170f04060507150f0207150203131b030807030302041d060a090e010b19030308070806010c1103 74
    0x54252903c030783c010b80320800c420302400381c0b80c101045241502d244c2520144040d0a02030300080c1460018411182003004072005c00e200541c1d5a00040c6111003021509100800d03012a60441c010044d82d2050219180210010b2075060308000d9800b003160114402e4203025081d1032a80c054003ca83da056409005100e010503100001e2290902034030600300200110b190501d0032610040d540c2e0282a102c8000f40b001018a80a041c112030603036800e890069100c113082d280c003020745071401d501041ea07e0700307055240004043d030b507015110b0103015940c120724a034850325242c0100c3c03206039400980d05443c8886007011451003010703c9480945034441d0300c240d9a0300e868034400c2c5c0d0081c2204400280d00082c04000c940c034100c8100051380400d00d0301c150141012000102800341c50b01c030741c120039503d482c0c8000034840c0c2035000d4014408040c08800e40d103000802016001c402ca8003040b13001c03c0800d4003180c00c091040e4200c40c070a0344180c41d012020b03081901d6a100d2420341e00892641403080d03a00342 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 449856393 1250 449855143 449855171
    0x30c02040501080102030103020315010f03020f130c02010b0103060f1202040b12070b13061b17091302120708010e0c0304141606030501080f03030408160210020c1c2103 74
    0x490003840c20f04001612035045204140c18a403514600030400c1c800680180980014810341d141225411104840c174180c11102090a2a40d102d01c0c8411441c9000d600605c060303019040b0700640c94003660100000d5403284509400382180c0e000d10030341000401030090050415034408000b88200408508280014081061410701180c0080c403100d00003065904000950070b900c0e002520303940c100600c0003170311703002c0000c0c0e81c07034503488044c00240301c9155601204032036204540886102138041d5070f200c50842c14080103507200200b070074a50a10000001c08481c170a108182c140d554210501d40303151214122143d00350000303070090750030110746051103810385404c01403d0406620344500c8880240741440203021a00141c0c01441d00d40c0000e9489550755401104407548183d00081312503c407420700d04a1b401644032943c00035041480311800e8081c07203400140c0c081401008880e05000d14030502c03400c540c1c0801215004001c1421030402e1420216050240c80b480807007840c001941088103013903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 449857643 1250 449856393 449856401
    0x602070506040f0611041d060f18040c0911030a0c1e1e0203040b0f031017060930030604090b01121a04020105040608070c06110a0e03071a07030c0204 66
    0x4071403580c0503c19440421005008041c41d0351300041c5640e00382494036551043d00304d4240303400350340f40000100164240d40d030b00402c00d4101030050440029080303d11007206000b08143c60517946801000340000c0e24065038080d4400c08035074030842e1421034840c11004005015400080c40901003080c04800001501c0340044611301c01c0c9a5a07182c2140003d20360300304800116502808542040200740310a1140320200c0d1790140000c001e0765520741d60410b9084130740813141c0042c50145044c229a886820380003500074000c1101c241a2114803090109a03050005c1940390507a0010707000f0010489903000d2009164800005031000c02c8848841d51030110740b03802600101a41c4201400510501c00c0c450384000441d09620ae00300d2040c105900040d005005038480c1b1410010303640000781943e441a415062410b0f400b240500400442254000164001c07003640760000f0011003a550741858005141400c580b1400d540403a140a0360141c01406d0344409405d60034444031048200041e01c841c49 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 449858893 1250 449857643 449857651
    0xf0a0b04080331290a030f0f0902010801050f0a050604030602071407060801060809010b030604050d02010b010801030812040309080f0114130c0b0c010b060c010e0c01090819110603100608060621040602070506 91
    0x500015080c100041c481f084410750121901c505160161003801070741c001c8121410348008551620140310440001307942501c15810054200c400428000100117540d0054030b05148207610a520189083c91140e40d518081e2240100144100780100030300ca00034034050f60070065034000811a2000900424038100c02a18100d949900004980903501c0e8284603c0703403951024a040419545035403107040b07041c010840b1040d610700343c1c2c41c04181054000c1c101c1d1001000c0c0e913170030307240b00e103401601c140e000f030100c484850102036407840025511802c0f4100c0c05031072588044103001041c140280000e40d40c100050005196503210030010240ea43e6001038200750b00c2c4070b000460320320a0005a0360400c0c03540700440303040c040440f609114928021880120310b02000c6040c114a00d82401c00e0280f0f103c00303501d80e03a040100003003489140c00c00034500c032040d100c03661641d288507120007040c024544516900803444208000c1100da03078036500401d80760824010722015013002d0140d100c007418410265 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 449860143 1250 449858893 449858897
    0x50114010306051008030327150103170408030304330e0f010b031b01030f050f07020606010807020a17090301060b030f01140603060f0a0b04080331290a 67
    0x64010030400c54103015055120007012501c0c04501c0c42c10407035a542c1e00000d44000f4100360300358598081e40348800a5400603141c00c0081301c041d10020f407002d0403c81c000380415039980304d4035100d450384002544101d404036000f100055156a40315101c410f0100c0841050b400d4980741c4040361500120502d203645090030b248507000a070311100360b510074600100c1d8042c03d8181d904058601865680101d840013003513019010a40c189507070400121300410130852441c0106240400780295541004003542c0300701d0094085641c141c8801005507052802150500c0041e4091450840020401e600121329607a0801985090501d540002401d69a2a0f000030081c1c190220800504528801146c1d0050040200c0c1d07501c0080030501007072540c0320013050300d40250500c810b03a01e542d44801302c101000b0080c820403e501c0d1501c902885490354081200d03500007a214000c00c005506160740b100e000420a8515002c0c030518084a0a02091017482c1c03001400d80b403e1407142200489000421241c2c0841e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 449861393 1250 449860143 449860181
    0x3030702100e0106030f12020c040516020c19170c09040f120f14160204140a0f0209060405010c1b24020303090d0318060906050117060f0708130501 65
    0x1441070358202c9241190318a09a814080100007003110f02c40501140c50304014409100120340405910300100856455001480c18041110b1000c0d1a8011428940c150b030941d140031200008200885100c008400355020341d110042004400c003900130070103001e00805464105688000040c0e840301c044406a0300301c8945800081000303c40141c0e084200103605210130840e0380c2c00c200801001e130780130b661549544002800c01c508100304550f2500c40f81d00902c00c1c00918101810040708480950384200e1503414048002c108503102e000391486090090100c0e403e062400004403142541c00c141034441c03a1001d4528210418420940300c0500000501103e0f50781c141c00c000920784d03126003107a400f150801e10500031040c00100310408040d02500c2e001c10781501c2038800b200c0d08428804000d14052900040c00100400c07508024101d80d9414640f600c00c50070740541a86480303044401485100020000070020b07030080101980140400264a02030b0410756241402c4460362039805800c0e04003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 449862643 1250 449861393 449861413
    0x3010801050112120c031b0f031101020406050717040b03010b0901020c04141314011d01060b0405090a09081215090a0612020616170705011a100309021203030702 71
    0x24001e090060990500c3c0c480500540c1c2c40710003000005090400402105d080b400c01498494014041d040c905116002c0c0100917a1622040c004c40100003100807802d21181014880c2041c0301361011150f060b290580382c11856611440c108800b00d51552031004240000300d0212900310246000e81a0b4625150365408200006807400062100080c8a1400c210340c45042c001c0625000d90848283c1c1301c440c208102c1440c0940009207503444000c540d41c6401c40010314034080500344100220210020000786440b4415101c991041e030146503002190714000c1104011290b000c41c20704c0c0d000d0b0404905104003001800f000000c1a9910441d0410ba42c98207111841c1400b005600240905010040280742c81490340030741d01602c40107441203d0106101440c0c0500c0000045001e5000309040c1401031000f450740025000040180c03125071070903a03280c6094801c00340065000c0c100603c00107040c080480100c0190001c40b008980207003060740c1c80081c0e000100041d40c081d2020742c01501903e24 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 449863893 1250 449862643 449862659
    0x6040305040608130f150603061104050a0503060907061404090c09030203100504020901060e030a06020a2a030207050f22020301061b02061204021206010f03060c0846020301 76
    0xc02500729001a60400c514134002884140722580d52584010062080d8402d0405074000380700c10340c0042d120340d05041c0380025140000000340151036040f1002203041d516041072541e11a4200c03240812680024414000c0710301440da140451000500c00503d8941c075191240240c40d841484003001c80c011103410700440c40d044c0403030740704810301c010100590702d45500010501c40d4184074460034003514071842d1189407820b100301181203030003007025550340f001200c00818501d48400d540031241004400c0c085909003484480d00c042d60168020480c2c20300780f001300480000e02581c42584220b81c0700800541444040d030130403d040e4400e100580343d6150146c05031900080480d000c5920000e6051000140e4422050702c107415078003049c0c6017150f0307151700c041420414581d20046840c45181b00018640800c00c12550640f8030412081c8800d202e007003020707105040260340c982200e04045600500d102440885030b60540184117074001d0b28120a01007440d9543c4a00c82c00882c0c940001c01402440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 449865143 1250 449863893 449863907
    0x30e120d1416020a11010e0d0b010e01051e1e03011a1002010c0503161107030606080d08060d0b0c0d0c0302040f150c240507020f0610061209050f060403050406 70
    0x1800c0789900c074801020100c020b441e40b40c6440021712504a4a01c2550540d10400c6007aa4a0a0291205440c02c6143c1004820071401b4424680d031452080c002090074103050f42c0c1c03150010b0703020300c040411500c080d04000301c11000d49039a40140400305d00d00c14156409000d86031407140505032213440d5600345000e0120900b0034174080e00079607040032252661558480120782c1e0040350002c007543c0190780c00c402100c1e00c514503000c19a030b920912030003100b0300200d85d009808403003a2000f110300c40400100c0c02d0741d040707404039181c551029541c600d40e40450724002001c1c1e48804c4030001a460040013014001c22602c000d45801c6c0000c0e40840c0502c0350108581c40e15000c3d21200030f408003181c25540c00108900c5810300f00910a020200900803032808001c0507082100980400341f019251801c0020368445440140c04564850f940c0881c480030300240001090b41d1300395031202c03000c0c42448001c40103080342c02d000f2036240c851120031804140003030142a004070310a5650507659864180010655 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 449866393 1250 449865143 449865151
    0xb0d0f030c0c0609060903030305090a080a021f060b0a0509130c0c050613210c02060301030f1a04020f0402070515130201110708030d092406051806060a030e120d14 72
    0x20045103c1c0600172280c00c0700c000350480354189004545d41da42c800d402801e01c403481034014410340020424620090300440d90140144000002d0880048103035074200603500b5510070100403101c208207154065128800801e440c150103800983c14842100e1000121084002141d0003e03e844890f81c2c10424280070280d00901c140300c000840c4181610744a20140c506416201140c0c1080c2c14511002c0c003503689042c0307090300100000d450b90394a044c50301c1140c001c10f0088030410b03000700d01960100d10b040c0f50103020380d40141c8001030700f24840007448020b500807441550144103240482103961601844c0500c01e2003204014598418036100140500a8405c44003140e900002c0301801414400016a00c80c0c110f505408900300d4481d05100c400d0444130603000151120f201600d610540c025000320742240d009485143e825060156102030301031080d5282544201c0800c142d1203080c1c841c0d040303401031a40303410035620450b004454182090340003400d086401919002d501c018801840c2c006640 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 449867643 1250 449866393 449866397
    0x50318060c06010522020706050601080a0c09030b071107030f0b1e0c0906190905011b020607060f061d04150902030c10050409060816080d080a0b0d0f030c0c06 70
    0x41241c030000e0706466800500541d03004a11100b20500f022003141c118200546407180b045607509450306080d0003801c1c0403500e45020414207804100b02840a2040800096071a55480d03456030039543d43e02d030050006400e85007008000360b03071940030980034007030280118451043e404803d1a140342c40b43e4645001003000442032010301401004114950400343e1080c098103c050703403055140b00044250141603549940428891070f031030980c6070080d140d6001e943c0240c80320102c0c452143d030602c902d00f1016000940010091101d500000c80c81c3c2c001c0c407c900d60000d03001c241c1c10b0b15003699071000c01e040350400c4980b0400781e040c4403c1c070202c010b118a6008207040d05003c40c541d96000b0a64800303640d5a024051441c9801c80c50603644944162005003004240070300c980c0c2d0340d03069442c1c0d6900c8000c503640e4961610300000034916100140d900f440e4407664072a0b00043e0307600083c80006014030201035420860351440b04000504110102502a2003501c1d104551203c50510402d8440340341c2090303003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 449868893 1250 449867643 449867647
    0x1b06030402030a15020d02030901090b0f01080c041503050303040c0e0108030405060a0806130516021606020d0c0f02060703090e0708060105090d0309080307030c032703020607081605031806 83
    0x980c0300401c02120b0540c005400b00c036070242414031300c0020b20400131080300051020052000512064000100b01d034011040240113417244070018000701c4003846001d50740e030710400800c0000c0c2030980042620039100003417420070a076a40c81c1c2074115401203400b110540d140c40c01c140048011041e00794050294003004500703160401010414a114070080d141c1804210000500e860b641c2c80c0b0f50980203914400d041c0200d080000000311105c0c440701d0a180540030b440040321450a420015500316200d50b0300500c4464055103007a28006001c04094400c0081402d1800268407101c00800c100743c402d86d00c4000c81480c2640301d19655a0180030081004001c1c401d2080036a4050152080518201c07195891418581341c02e0b90b03a0b0296620241c151302012401505040e0881036003c9614007d84440d4812000c501000494680400d92515900448101031025045c100003030301d480f0b441100001d1605c09940011441c01c00d03901c40450341d69100203404107541d210900c00b08405803042d01c800e4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 449870143 1250 449868893 449868901
    0x606021c050702010509190b0c1009110906120601060e01090909050c012f030a0215040c0306050406020f0d0e010e070303120908071208090c120307030f020106090e1b0603 75
    0x40240c8124a0082c4c104080440d4445943d526075a00c51558540d000f107284070b0641e10307200c551640e0485011960ba80c000c001d04040581500d02034980e0f119408821070b400d41101004000c0c049602501c800d4110002146110402004000c1a4003802c0b8544455900c00d1008000421031071642d0018100d032070600d85a03000081000901d610ba400307003403c216040d0306488030b4000000038030842624449542c200c880e0410b181c00701c01480640c10a500791000840610324820780408143c40081644404c010704001090315503015a030000c0c4103010151825499801030382407030700001240014507030799250046010500344120b840d01c88000010f440075914644020b0f040641095042180503140d140040c100065581140d401d10b5110000d01d4800b40c2084006141c1c03031040343c007a50b80388101c0460010902e084240b0300c442460103170086140980b03641c1c0072101c0d13101c41d40398542550b40321000450040703980e014a40c114003130a030040031010b02c00c3c0004100ea06e41110440d0054504100380 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 449871393 1250 449870143 449870147
    0x30b030d0c080a2307060b04051f031401021303080c071401210e07120506070302040b0313110909030c1c050a0503091f1a0117060f010c150606021c 65
    0x907494100302410f00740000d0b90350b10f50002d04d102d40071004030480240015a80301300242540a542c202e10103450400c195174842050391148101c000741c40c20954400b0400700300013045d10007620344c0c072600030002504240002d20f0303084411650740c0080324039107008a103000700c541082106c40020054440190030391503d00001a03c07032000b01d00c544189540e101055116400c140d00000c990192110803504050750718502108220900d250458141c0910004111818842d0007920161203060000c0c910719194072044103082d40320000d0842c0d1074507a9544020183c0e81e00800300e4030800040029540d42d403c6d00400c14140704c0c40424161252040981d80c1184503800070a48080701c2071030500319900e460701540300d032600409045210615660076061120540c1c5a04211041c041407805034107500c03a9200151003140003403095803481070040c00015818034200101c61114807041c104002005000c0e00d901c40004240f90801c2209510351208001c86907041050001001030441d40c08103101d483c80b00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 449872643 1250 449871393 449871397
    0x5040911010314061507020111030f2808060f0f030708030c010f1e090312020c010f0c23090a090504050a12020304080303150a12030905030105150a050409050c10030b030d0c08 77
    0x83c01d010303030000c06c0c620116405041409811060714088076211107504081c405241e0056131464003d45100c0c24141071030a90014a04200441d5183c1000c41d54a000502c8505448028056446070989000c980b00c0e031814060800503240d440040c55a5100459229003582c0d448071080b09014503205001042420400d40c1d03401d2003410b0000803d4039900ba04003101c0c40d8900b0400035501c2c0d840002d0310314001c4015030041554041070f0000f440000c038074180030b40394520362610039119040341117a64100769400c480200500c90300100501c480030384444208007203442c115422201c6500890703580c403c1c0061142488000403e600c001c600c1c1c107041103401512408064898038032514124801d0106588601701d48002c0c000c881030380e094000023818000c080790b0580c411703940654a000041a04071055055903501c0d02005461f410745149000180401041540e80a40d07035801a10a6400345544010301038401540e103950200c0c200e50103c0030141010b002e2031032a0305100c0100100000500d0101c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 449873893 1250 449872643 449872669
    0x1521030e0a140907050c0706021f1404030c0302032218020c12030604090b090d0f1b0b060307030c030506100b0304030801230307080f0c060702030c090a060504091101031406 76
    0x74201800752113080c8141c2d054001c2d89081c08590045100120b50305a00041051424080c0207a004c0400d59440000044841115000000031180c000250219003d21ba080940342d100344100d80c40c040c200d11040b6410190814402c1c04071007803107030801805a280501c0b42941c59020021807074210510440c5d075a03880c100240145030310000c40001c2d2943c0e5158130541c0480e0f00b0801186840c41c20741030b080d45401180e01510081600204d000d021607203d400d008405c103c0c0d5041c004429a43c03900c0718000883c000f840320368544108603000c40042c1c814400d000085100304010601810710211580400e9015040800612028010000881e600440d058119030610303441d00c0c04070700c1d0354241c200a40c070b9004030960188901c000c0083c0d94600003944c484804c0c450300a5801a203048810032829200c0c1c8540079505074001034070742c8410300e000c111840d002030007940001545607640f0045000d480c141c2005031406089007817000541c3d41c05008111610410b50820000c5282650029040d214030032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 449875143 1250 449873893 449873899
    0x307030b03070b16030c050f07061115070504180f021917150d03020c210c0f09010b0a02031c050f070302161218080601060e010815041521030e0a14 65
    0x6c000041402000c2c414500c207440e00302c0580d884580c4600300545062207a0340b1990507403250001c40c40f00707101032440790350282c2000d07980c2c80d103003a10b822a1581d0b5558a41d003060700156803070300003070703403040c04c510080c2290f16050440b0100c0b281c000a021b820200d09120190850300c00d0000c000c184524160713065a034141c1140e03405503403261402c04030710304400b0210040c0c00c401a04240650300360110000701e20b899485044903030413007001c0140031415030024071180d0080140e41c018800b4442d0040501028603240c411282803000381122580f0f00088035aa0006060760381d8144802ea03c07000c584c5a9005105040940c40c09120211304c0010020f40301d005043d441001110064036441424840c00b004818051050100c2c0c40b20b01e4952101001c1c42081c010440e405d6404540d54060000700c1d100d20700504c140002c11603128107000240248451366113548041304008600309103910904a0801d034122401c1507032000c00e28015103071a81188a56100e4105e40c01c08016080c4061501351000c8019 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 449876393 1250 449875143 449875157
    0x303010b0301121a0f060f0a061e02011e0204140402031603090c09060b040810090b0a090201050702060a1d3a0602040b281b03140307030b03070b1603 66
    0x900b040013410b03042130000c443c03030f100103400d00641800340803e15004030400c45208000b48144010807248002d02e02c1500085501040000c03030884031100ca01245440b00d000109003600c81142c0070f0707980c0b0484074511032200d6020405025036006c0a0700216022020340c1d007140785080c0198100b852009a425039420162242d4032441004a40d080080c014100510203002040c0c65011328021078010b400f86030304038031803c074100c1d02084090041100207a00803c02c102213499100a20f03014160000041e23060040030400580161175040007090b001d46241c1d01c90043d8402990307110b030651000d00c980c9203e024520004d14006802c80d2842110060400c06104a540c0340360a002c0881c440c048023070000303031012500003a83c0c00c00d0002400404c4074286991f0b181b210200112450f0580202040c001913500321015104120000380b00351458002d0a0101800c8900c0b076a406090380211141d0001984402d11040c450130100007500140003206403803810501e0740f40e07104161070705408014080001c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 449877643 1250 449876393 449876429
    0x9120b0901060e15120a0c0b0d022205030d0c0510020a03060f0801090b0703090c050108061309030201062105030a18030c0e0615031510180305100e0303010b0301 71
    0x425840340c0020b1403c0120b00c856450300b003280042e00202103280383d00449100350201006a0041591044141c1c010200b9020a00b00400c41d41d4a403c0351100d11092039081100000c0b4064201c0c0300b50b060314414107150036060509080c14241418250810240920100d1b07100020b040070030440e80503c0c84210058840041000c01c07000b416050b40203c80b18820100003041804042d0000300b803c1c0d0141e0300c207182c0c0d920780a00407400c0315042103010f040a16079041c24420741d8844d900061b0000c030b0050046440341e072080310a0044818122003100507039541c403402c100b044814440d9182250071100d03443d854400c42d444d001e490340715060103217041250940500e0070b505d050510fa4009903070426400350220340c42d00c201544140c01903c00c0762040b90120000f170210b809000850344a0f12000c0b0382c410808109001388030005a52221071028002c02c103042c04c14892140500500650142008000d2011401261412100030f0200509260420401403000f08c2c0316030201c9044480d041b418044400d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 449878893 1250 449877643 449877661
    0x201140a0f091e03080c0c070302150d0f06060905040213090902030f06040b06031b100c02010e040c26060a030327060e010306060207060c022205040b0a0c09120b 71
    0x840b1000c01031542e4080407901c08000c0d1440c0250209038429100d1a40caa161010450114041ca81e640006640501014401410004500c0590f4040010070310304015450000c0c00070b666600e809118503070703078601c800c01c0fa141c1e001c000b8400a1005071000c40ca0580d291400000c4880f0074010500c84684400d113072030440d141085031140c8002108140e800d075081900c1e04d0380ca55002528514460700c200d14070181841a903003c2e21046180080410b692b04950000554a8040c801000e0307040c0200107880303a00300e80f514002c000503140240d907000310100b00061200380041144200c4a07143c0030030010892551079001c4c1041c1906d42505154001038103062802d1031410046035080344644200c40009145500640ea140c0c10301c2c801d803400d004450307c84000f2070350340b82c1c24442c50f40010141b841d40e601500702a000c48480048070503080101102d1840d40800340e85d4103039000c03560203500b07104221034100c0e107100c2e09820029030300d007550b580b030b00c0d0000200803007900120240001c1d40799004980510 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 449880143 1250 449878893 449878901
    0x1403150603040804080d0e0117100b1303020301111e1b0106030c0510031b050f04030b010e180a030503010608090a050a030801051206060d111212190201140a0f 70
    0x260004106076940d140500c2c050401e508907201e032891a01c55a1503143c200c0b070188050151526040e526009011114100500c081d07a015012591000310042c000c541451404014000801d400d080490164594414142115400c0c4000300c100d00c428040754103201310120801400c0c210001101d81c82d10032008401c250200e900c0040b20480d807034200004208545001e01c0403c40c1c904458441d10a80039010680a4868091b65007040300d1038070021002d080d0103400075007820452000d80d5800c154403a079603035240380001e80002c01d9000c1c0c14000c000345d0b1680004080b46d41039248000d42001210f40e80c001c0c1081c003060140d03400780081c201c001140c1350f008004e0f0304005500074044840310350300b0f81800b0340314032801c1c02514041c80200000b40900c900005005002d95001380020032104641d4507580000350055181c19400010000c50303650000c4104110078140c448500302c2c0351356280036426050401361542c051001d5905200711440301c540141540e540c0803030503040c041240995980b200e0010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 449881393 1250 449880143 449880181
    0x303090206120a0b01110c010c061505190515070b01031104020d0504060501030209070201230c1b01050603011407020a06050a0b060c1c0c02030303070c060615020a0501060608071403 80
    0x48a0b00300c1000541c0c411600f0000f900d040a882d4002c0c0c0e50300501030161110300c141083c0740490a180722480019859610880c11007241500032040592501c0018003c0e421030b405a000c002c803a40c00034800d07858400c1941045c503900000c07862a204942c2d54034000400c05200c003034070843e06040c500340303152101e804864156000340c40400a0346407a14240700180801c0c081039000c1c501c504d00261030180144200c82c5010500085522549288200444030a00c010030850400c4418020700340140341404544040720240c0e40013040c0d030300c0c044080c0340c2140c00c1040b2140c40590444140a04290045128040150800f0012919070750395132540019000500f0802d070429000131784900d4802020641c001a81c0c02c00b080902c0394522000101ea01010025029604d81c1080002c1148140102d402d451000d1081c00b000c1a896507544810803500288034002c009a04002c600500b0000c00307120381000b9268038140ba40b40d0f4200300400900c02201c41d02040d1021100001140c45290024520703544 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 449882643 1250 449881393 449881417
    0x103050a03080a0f020c01020d050117030d0f021213110303070c0e06030c03060a090c080706020c062203030e030114010e07030b060d063803040803070c15021803190303090206 77
    0x5104100b243c020300270f40c0507590b1910325924000003c03480000440d60110004034000041d4108104440d0340f4000705140000b900c2480e40c2000035a1800118120071485200140c1000c002541182060301d00c40000010491098100f007001500245503614000240c480010001e00c1d1551a81c000c83e2800c002121615803500c10f040c1040a200c1068000d288030503c6514040c00841e6600783c0c5507a586080d000d0304015070030141102d0003c2c1003140140668411605029101607407d05000070000b0854009600240000081c59190b0070309000b4683c940c40c4620200342170790301d000500d054085000e418141007549446040d4001c0d80d8a4050360020f00000404100e455581c0c908214603a041c0180d00d0300030300c07025001008042009554041444003000001e01d1592150b42d00121640000c2c860014014400d904901080e00101c0c1c51030b1183c0c03000b4006a5070503080000300f0188a0482242d44254800003000c0c03600240c0a0400350855418100460059880c0c070000d0554001c1e0365002d64 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 449883893 1250 449882643 449882647
    0x3060a0b031b120601170d0203070209011a04030c0e061e09010e09030f0f13170303040326040b070e0d0312020d0605030d0c15050f1303090b0703031b080103050a03080a0f02 76
    0x101d00706c501510302040c0c1800d07022100d1070344540300d09980703900800002940c0310040e00700421848100a042d141030b90441c3d000320b4605620723030395614407509640d000851007110302400c0041e50304040d810095031200c0d009410031000c031110f00150107444140a41d07a10b44804002213411a181001075441c02c1e030741b52401503102d100c280003035181500402c0c400e0003d140410400542c10342040380307440c1075890f100041c500d10b03540c5031010355060007988098800001041000c0034040c2400e490140903030310415421000c0c1c01e040900620342c3c0c1ca8440c0072481440f44078030000020b5001721040080c001c5417040540c031500307141b0b50000202801c0e030020307405025648411480681c8079100320081ca1040c8035510070b945422001000726901141c551402d8607440001c144d04556a030070106800388039241034440709854080001241d00900070840210b5120381e00c1c58001408403120000d103843c20b180a4105601d16156140d4a4000050180601007810b002c0b48140358541c01480003000171b90000c5d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 449885143 1250 449883893 449883899
    0x31e060b060408060615041a0307020a021003050a0506040e0307150f140916060e01031509020f0c150402010c020607030e0d0b01080c04061a310503060a0b031b120601 73
    0xea2505001c03100c1c00d00c1900035811b4460014a0001941c040c0c2e21801d0700d0b0000707002c0d00303500280c440d0300c09000c07030080d442958001030069840800c940c030001c00e05d40d000700719410301c1b240360750582d40080c22051089007003a072071940c1c0724000810350341547c2c0c02c4440e80850810b207440060040c41d28207000300500741408221040b0581c0c0c25505400380d4004801c6894400d41c80c500c0305680e80803030040c1000103000001d05100c0c0e6100e138210107000042c03c600c000d0300c0ca50324030040c0c00300e03446100301001c42100855040791460083c009903040180074141d11070f80d841c2c640d0000342041c9406070001e110f400b020802c03c00303040c403510345800b890b1800f80c4003006000d168100091845401d20600115201d08821000c0c80e08107406035008658000d1b02640d60522140600c84840d00404041801004010441c4002006007810800480e08450100f040c80d4101030038113040a400a05e00d2100d00d0511880383c07250785000881170300710203410fa180c2885880400000348261100349014076030b0301c1640004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 449886393 1250 449885143 449885159
    0x14090301090f02100801050a14063604051b03130506010602100605040b030703060f0212010f0306050c1815190f03180f060209061b010c080f01031e060b0604 69
    0xc0c2c41550300032940030300d01451620381119000400d0203003503088455200100810205200d14240680000b0000c0742007020508400785101a50003054044c0340030b250035041c00d030304900c0448090324820394092203640740c40c0e1446071086002d8102d50040303080010005020742c6100c1a1405000e130301605540d16940d41d100002d544100c6803aa0501c060b140000c0040c0601d0103104961001d4000f901810101c0d2864551100404100c403a0a000c250200143d940152102204030702815034164074468441c00e60401104448008140a6a441007048800b403458250740c1143d04410007120302e40441c010004002d811800f8420170710118562504208600c2900041211400398455074108100c0d0080300400c0d09168109002808070380034048410003180a50700200260300d400303000d0b54a0880c0005a860303d040c2c1a010000c5175035900e00c41440900e0b03026801ca40c0101500480d641c0395419902d518128610104440901095084c01c5204104d00d94001e0105044024040c030b488650756400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 449887643 1250 449886393 449886413
    0x200f030f0a080a0903020604150605031f0c030203060604140f040f050421200c090103030815150901050703140c0a1403161e06020d140603010c020d1409030109 70
    0x3103102142d1503400040b41c00c40144a5078600360703011340c01480981c40d1922108410042c0f4030303142c400d058403000b0100d11a2420422181079001002001900a500b80521021140340b86410030070035004005111182d03581324103031b40a07107070f0707203c1d40001100c031b000c0c0000d12940791250070b61340140c1010214401c0340e0903075001e94450b60155280e80e08049040701c00403208400550b4800c00f241e8460b05114001c000d841d50060000310300b108503003210b903214000884082c1d00341c1c4101c0015086104210310209140301c50059024160344240d001c07190078a0b00c28103802a50241c504000340412281c0c2454851411481c3d0000300300300180e61030b031080c2c3c40c2544400080400f5100441d4100c0f0842c00201c0004c111416698076a94000007000f640e40c0b0150098495088641700c8101c4054140c0821018401005074048030440080c1c4400d04005410340308000800c007074401c0e494010140200d54010443c500880c000385048188001224160160341c0103003601c84d60550b1800741e1a50800c00d6480c0c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 449888893 1250 449887643 449887657
    0xf03060b09070906110a050a060504120804080301171507030f0e0705090a180b0c0717190315090e1b09041203050601170709031110200f030f 62
    0x1905000d06a26202070104648007580c1280000e03464900400000340b140404145403503642c01968011055030716094944540ca039410340f1640d80d0391050104100d000d040880c408040e500b4842c0700d914203519205103901051207550b194008a0002d4041030700140404800e007041025443c2c040c2c00d000c44010000d00c00007415001c41d1b4500a42550400d40008524007207401c0180b0303c83c0c0a66402c2c0c03104020746251440c82d4072215001c4030070342c00180703c800024400c642100c40030f5140c20840c05e0003940d81c115050900388040082200c12280d00b4030803a4a182d0781d19a050101e84140313400d140910b114845c3d4032030b01c040d034604591241c0000d008240e1a2002559591088030299110104140030405460081004c6001071036a54128040d80010b5440300050400010000d0300306284c10f880b0400300c40b00e0780013450908041c810040c12105c0c100c10f900d0300307681215180c04c0b03030131025102c451710700031050684008085401e6520010085500c00d4280b920075a500d0700c0b02d40e0024981034005903 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 449890143 1250 449888893 449888903
    0x801051f0603060503031b0304030f0614010e011805180d05070b0601090609300b070807080910050405030c03120f0603120a03090201030f1505030f0307120819060f03 73
    0x300006191440303409260f055901c0100070314541001d0900c0c0302002c840c452403c4119010501001002c18000110111100e0082c00b01055100381c014ae8042d103408141c100040f0215032900512407092004442d0004446c0341400195640b5400000c014048c1c245c114101c00b80704400c4841007081d03005000c0c282a40c411a10a503c03512040019039205240f03011304400203601e070101304904a04904da624540d100700800150350b18040c6001c7c20751030301401094803a00444405d014805501a001552010300b910b04543c050802c0044291581e0b224403201e200c4980340c2c0080f078248034050013124840311740e0340c040720364401c800c0c7c966505a00c400c585090b00d0500000c00aa0541008262000e0400c07800d8412032a00641700b400b50010410b40109070304043c0c1c1d40d183c02e0000c140c00c4c42810824040d8102c4550254549800c00d440c0c00c0520701d0200041e0030502041c00055190402c90b42c50580c141003d000640e120003804440c0041c007a102410b042c1058400200b2116913418036044e41c0c028 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 449891393 1250 449890143 449890201
    0xa090b0f0405010506030c03040c0b0403060b031c051812010903030b030601381314040c050c0c01050f12100e071707110c0406080115080d050d020d06080105 69
    0x40400c11048035401d04c20150003910810000700304000321001141e10a12a0308090266622171340070303080755002604100c0c2c00d03aa071080410a41d140c100541c0904140f102c900307000200b0314400080c014098210001181d8180098030b0b40f007980c2c2d0803120181007032008020401c01c101818001c0c00b5050f20003040740a40542c10012400890030362881c06080520a0f401c401d1101c489001103c00c1000b60301c1e19400c040c10b010012120f0001d40b403250040020310340304a200300c9003904000880b0a1a0018018018104100d81c1b80780c0012400c032010303030700c00d080003074460000030347c0c044182c4500c1e8180034483c0240e00410502c441c00c0c400780020f071541c00d10080303070980c3c40a00070b550700c4000180645503030f114000003a640c28401c6500750000e00780707801550111200c0d080441c0565495400c480c40c56511440c00d040010064034030000104001c50081a035604981405003461286803090b00e04a5000208025001c215030400d000404101c402081503142c8408000090440c0c411a00318800c44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 449892643 1250 449891393 449891419
    0x1101030608060f0f130f030f0c0b090f0f0c010e040b03210c011d100507110f0705090718030303020d1103040b06031c14130305030406080114091e0603010b0a090b 71
    0x106880215031700c0d0388007210f02901c841a80741500d0550006400f50304002c414904080007580caa40202e01030150a00140052401d07816298102024103084107025800300b0000080b0740c0c2c0c05030301050b0081c4107890000c0d00c4007085020a05007000c080c4141e60344451a50003000d1040e0200040c0241002c04000b004441c41403240c0a51040380420280350550007503682c0c00400302c040c3e01c800e4200012b03003402c00b85c100d00041000d0030148001e82d005407a0300510020082800c00c40f6046070f0240c031524043c911844d05c4210b115003a03405000c09810550301042004203003441d540140781c191820a11316403203182514141c043c03284112040350181c0503200907044a440050215002040e9684842510b224043c41c9605c0c0d039003140700a045003519030800000410310900c001c01c0903100d5691000082d40c100f0010b2011203841008144c0504c1d001c40c208006808101e040d41040150010380300d81c3e9854040009025040f116a00c8e54410703400840000c501105d640408400882914101043d00c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 449893893 1250 449892643 449892661
    0x603060e0402010c140f060a0f05010b0403030507140a0215030a1a0913240603140f030a050309012d061d01030f0813030c09050108030306010c1101030608060f0f 71
    0x28150740080c04074a5143d646000118a620220034503120002168081d801401505143c1041a105929200d50f904210001c64007680142405400316034200e0f49840c0ca180e400030102c1c481c00750302600381c503c0c49590000c02142802146112a0010000302c1c1c0400b03002482400d540c0f09503018074846281000c100070300f80e0030b0709205e50350b960010102c100c02c1e07940040721982d10b42c03030b12411035560307041341c060050810b01510764045025410000060341c50070761404850a40c580d20840525900c201490b034022103000085511501040c580f0135120345400b40414050f05154070260080000c05821440d1118009400b90300c0318180c2c071050015660b520301011740d00c02c2c0b001d07800c85102c000303500500204842141514172503105680c600e28196012454003241c1b0081d8108a8a88072000001c100344022801020301518072240503510358105000003904506901d42c004283c01c00c541d42120741c9a020f98449401060300d101035400c9413030030040501c2c40c007070b0458150380500005000303d0a640 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 449895143 1250 449893893 449893919
    0x51f080114131502090114030405070906120f0f0c1d061f02030306091512010b0102010f1437091a010b0a032c030a09050103051b070812040804060306 66
    0x168014062200f0020003103240d07030103540001d00c1c0c10305003c4049030007105224a20300842c8981c0c0698043d000311420000000d041d03409641c0510b2682e080c2c80c0d00c0d200030410070b0030030051a079030205054404981c4c1d8504420001c80c035034400303c07091601600d030118880c0da210030144150300443c0d1300041d02000074800c1c2221100c0c8171b080c60043e4401d00010302e9034200290b107150232003071441e442001c002c800b0000442d8811460a80d05899444540951440d6024081d11031014800042401016210f514412a01c040204a2040601440c407502c0300c4030350300c490a00c0c88a5038421100b0100d10a6204000941072211085030660813046204031492160303c005810707a89000c1700c4501d4206003c20490141044002040454640d441200070b03441d4a1019600301c07800c90340165450301c3c1582000344c940d000c0eaa00031070515090034204030401d01540004030b4806043c3d201d03640c43e100e041c101002940282c2c01202d080f0f008a0041c0001e10494902410071201d1030f942c107120154840100302400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 449896393 1250 449895143 449895181
    0x80c0105090f030a120209030313060e0919020913240b0403030503061005130e19060f0b0a050c01060b0405151c090819030e070501020a021003051f080114 68
    0x25400502c110800c031842a46002c0d600d403080c017030150070314401000090660303100200300b0f01c040141c1e802c204140354000f80d00041000046601440b50b01d0403d203055580c00000b0246089a81d0006000310b25940d800c410b124502140f09040107021070708548003001d41e00342103a00019200c3d2140c0040c52200940445059a500d07a0b5071506680b64103060021402c26210401c1c24090244a110100e81c8c843c10101e000b010750310800103507402c0101d5400602c40d0102d07140130800d03051610920400000c001c0c0281103c202c0418070b951041c403500119014040c400d40b000e415400c3c41d000040c651070281c0604140c400448041744001050481c0b110b039481030203a0599503488050042c401d02005501040b803240c0a20501d919001d4201411121218a040b800300400c7e030f900d00d5200c5081c1d04114207009058280020300070500da9400180d40c112008212008040e150400034100350b511042e2051103005c1c4030b8503c102c158641c81c46901a0500511820080710000001200702070918000101c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 449897643 1250 449896393 449896423
    0x904050a14070504291507080f0a030c0c020904020114070506130615080606270a0c020106060320070203120301090209031605012106150c0611090109120f06020304080c010509 77
    0x84400c29078280140c6e00a48401a82c0c03811081c0034240220b48040000c0c490302c3d110010a80e600c10900c0e6000d0116105911480204500703401d854006868048005400580900b8040f4881e01c0b1000c20703820070300c580c0b0002050780c00b9000034050041c0c4450460080f05200d05428070402c07d030064814501c4220f48125415688200c021903240e042292181e0f603090149003c0074140382061507240c6080c54152185040590349031030380700384d480d82846141c02518551800f448024400580d600c602d50040e454103000c00000102c507411075408000ca45600940485501e40b0b96030f54524400c001d4028500c05030081c0a50000c1d6114640140035900c20354505842d07180856444c40054030f40300c40011b540c450001d1780d40502003640143d00c12944441c04440d034030340d0003a900c54584079080d16a08000040600420700a00d05542e1300300640c1c00039287d100310341c11800707421400d2080c035109072054050324191001040c0300500c03411100a05082e00c11034000e02c010740392042d0b45941d0b50816400d2441c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 449898893 1250 449897643 449897711
    0x405040501050d12080606190f090602070f0e130c0e1b090a26061f09020315270a1a0109081009110603073204050904050a14070504 58
    0x621130380921146600b2007400b412003420b080c3c0004050300081003072255400464400103401c6601070380125a80e0141c41240301504980b407074000300300c201440070302580070b005100400081716041a81c0c004c0107aa0f410080c46143e25644000c001c14403001540c0f1100d200403242030304515030a280c0202da0f0503900240c02000520701c1d0509010041a03400107900080310307031002c412182740c2c040003064010b44400c00d0f848030b4080914254480c0300490303030010120500600811500144c10000c41044150980b02c41b02d0402310200450b600c01460b6000005103410141403210121080c0e2040403900359107002141c1540e0a0001500e400c4141d2040700c04a5000f40c0070403801d90031580081e194236128110184801d920030000400c41d800c02c07a007a0000540304d0030101200350440e00381c05900655800302c0c0703010701160070406900f44103c0c0246401075240101140c00c000b03042018000740c60704401410b10444101181d181c5031800307031113154400c50078135540e130072a11100c0c00c00003c0d007034100349495 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 449900143 1250 449898893 449898923
    0xa03031d1605060913090c090f09050a03080702120c07090c020a111329010e0907081b0903010914071508010e040821220b040611040504110405040501050d 68
    0x80b407160700c10100c03640c00415065001017983c00502409200c82d1080003110f042c541000a404102e80019071005100c074100706041d0041000851965907403a01450b045034240c0c0c52000070ba1402004011080c545000020104581040030400f44207580c03548900340301112a002c0c04076503c00410402030102148030510810720b01e0f05007180c40d01c1144840e8041030840c1c1c0a4888402c0a0310441101260b02c03604072144000e690002c0c1455814904850b44139490422048c0104010700040c00c0800c8907031821060022a513808c0203850100d88014000d0140310400d03c0d01d41001c11180946604610800c50003207100d0410b19030580701107605649410381c1c2e82c6000c085042551003c0c20a0b00c1c5402c0c00c1240b002e6a081d01c01b9155192040340c0c028a03c1810701031b01e60b07030503094840000c2364020b07890803010f030000d0006440e5641058024001113160b1680c042c07100214405c0703030706c031640c0b05207402c111112588203000504102c900407241007015aa0340d4052000c24503011130020f0400284c05118 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 449901393 1250 449900143 449900149
    0x11030a030c03061d0a05010f0806070513051e04060806070c03050f12010b130608190e0c06130303081302150f12040606090c1106011403030c0a03031d1605 68
    0x95a80350203a0b1602045039942e4001082c203903801003000e501c0c10501d0a04001c500061401041d00402403d4151140d007441c2151142d00d5100207000c04081140008040e441c0004144615000e4100107283c1b200b10910810065040312060543d94011420a00c0c0065214000310303416200d400b07961252178003940746903801c84142d80706250030300c0401010b0054010040001e000107005e8114035103501d96640c5000c5000300307004c4a56101c80304012146042040403400312404a4003281d100c0310104104101c501d00c3c0c1e04242c3d250f6017098000c0c102254030014a500401800c0031030f406529404d03001d8a0740d6000c11000308401c40048e400203104408502007503043d00090a0008095020701d04100c6e0040d80306022100650302540c000d0b45440007444655514400c2030304050030780c20445100044010b203507840302c20512641040700c5400201c0f6600762002d10803100f045900005903142607145180103802841d0400d200b100300a49105802003080001800c03c0c0300b2010021230b8422245040300f0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 449902643 1250 449901393 449901401
    0x13120e011b06021210081c02030901080c1606021803010b1507080d05091515181801020309010c020f0604031d120307062405150d0b0603010602010b030c0111030a03 72
    0x4200c940c20382c01c01c1011904d13091a82d0040c060b9184849190215162035145442c200004104903a400030340550404515000000c4a03a5407400f030a2182a680c0c8030609541c1c1802480846005805c40030840e07000c00c242d580c001e00d103020868094805d0100c0110506080fa0403004015400902e076200f070034100f201e00400b170400d1a1150000c4c0d80382c84d03207080e00d54049e240c05803600c050304d50042c5020601001900b04490380008044000c400221400300050400712107504210600807810000c211000441000f003410301020500a640c1c80c184580c91600030721034101740100500130300910100110001c1501d41c051500b40d40c41c0c00c15200d14130001001c111214250507070141c41e03111203106921092015012103406500300149401003007011080c0e10340c80080050344040010400e01003039449003640d2046001902d05c2503202da007812030800081c51500c100580c4000d01000019a00c0e40c15001001d10250980607121450f40c0b200054400740d1103e0300b82c0c100b0342c0003030200601861007030344 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 449903893 1250 449902643 449902697
    0xc0305160c060e16080604030306091a0f0f031203100501110a0605090c0d030503040c050604080d2102070c0801060510080a0905070f06020102040f08030c070e04081213120e01 77
    0xc0c1c91040a2130040219070841d60751010009070030080801003415018072502c2c00900404505100f15141181c02d103080307219643c2c10758441c03505001d40000300d480d03801005000c500c010b404c5070b01c07560109180c2080b42d0070442d00c00b903030740c0818040850107504c110349654052070508024400c1400980d02c490143c90000c10211091042241c2e41029030388142e01e41d004c8900039241c040da00d08040c03d026001d008960080e5006000170001080a40340c0003800d4044480070b4540701c03020001014064070b01000400740e2131480390001c50090148180241e4100c12540000c0003042142d64034800d100c0c83d078030202e41240c0403070414400140000240d400030701205129001b980e055a840300d14404042c6030342c2d040380c40182c0d8089000d200d0105240409400760403000021402d00d120b036506582d441d40c103402001948404400424100400c0323006843c050148201d41a0305490400c01a10201030500401d44500300342001020b070460286c9001e003030a44041e540d021040c0080c0720b9008100040c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 449905143 1250 449903893 449903921
    0xd0f0e1f110307031a031506060c1203011d01061d0405090c09090601061d030304060e06130603050403090e060901030b0c0d021b12030c1c090212010c0305160c06 71
    0x20710800391040300e0004520650141d1400900901c1400d0031451240d411100c80c1e01036030049040a030022603034150140c0c4000229038166a50b1440981a41072041d2170511200c910f6000c400450600c071180c080800c0e041e2002e5071003601d6030740c0d1a030482c0d1000f002e581d6800c07a418410003006842c140f80e081f655000b02548121484039490700e005c50210340040318a49442e801040051010b01d501801e00002650035150030705000d0142400641c2720300c6030f4820003050000d11101c24034641c48071000c1d00d0160a40110032102555100030240c09440c1c12070381103000900c00140454090240b4183ca40a404060040103140c1c2c01c5035240d0036000170180029241c00c13802c0c003020721441850f0008098a01314504186599039151809915090901e54800c40c007100620400000c807118806a580c102c0034040c824121055220b0303c43e0082111080c040e401c41c09610b070518201405400c4191000d065a0b8200210760319500040481c20080e03d4810014082211107400b040302500500d6400d040c1c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 449906393 1250 449905143 449905151
    0x813030e030a1a0c18090a0b0a03050d08130305120910090606050901060c080d050705120903090a1a16140619140618040c0308030a020d0f0e1f 63
    0x10000103454100d41200445102e0080500c40205101062010340c219414001c80e0b805c001d10203401c8102d000d40c00c055a801043c00e03000061714199150050f04100c107000e400386000c41d403a0300701140c54250400b5200f0218640c0b9001c2400d2074070303003c040f08480340c1661301e039400c10380100d8051908450140201d00c0e10f2140414100c0c88607124031401541521900000940da490701c028000c0d803a4050b0f0212003403064200d04200841c0c9110700716001e5681090000440b5610504191004d0080c480d0022240b500042006083c81c070000040c00076040484d841030800342d680c0d40e429004101c41004038175070300702884082ca06043c8024040e10300c510600740526201c0d180c03100985401011a422180108900301844913442c2c54462020440d5007500c200d0558031300603000c5010b00b1412103d02d0703141000400000d0038072080507981c502840d070114910340e03242071101525019400c90004c0e038860625004405070018142e2203283c008800b0b500c050006540c500c0320303113640503014488034502e050311 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 449907643 1250 449906393 449906417
    0x1c170609090705032508010b010c0803070318060b010e09061e01020703020d030807090f03080702100e0d1128122102061909031403060d020d140d0f081303 68
    0x1440325105104445c904402d40b20050104110751408503401000c0b1a490020010100c0c3d0340490891002c607003202c440d540d6070f116460210000c0c101411b030b07110070740810800c0b042080b6040e0005083c5904c2680c40450310b000d11000c01c91101000da42da60790028998030708448954031406c0c0341da0403c00500558120b11790b41e8022071502601d540c41100010000000c03c10601c2e04048154050039100002541560855a60780554400c500b0041d2140c0034110300c440b03a0318801c0d1100146510060542050303000d241c500f4061010002a405100701440241d2042225003d8ac16009034014001c20520300c07498400e1b2050b00c038200f400e098a4071f22040c401855020080c3c102040c1d0f51805500401403881c1c945000b003038014080f517000040c1802c10791000c01203640480c65002d00301001400c10b0f500d441c2c0c180065514480c555009410021203003000e001c2c04500301e80f51000d94486008e450244011b20703000c0b03a0002d400c590901c0451000c101250f00114005402500b0503c01e042c49514500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 449908893 1250 449907643 449907649
    0x61407020f0c130905030c250305120306130f050103030311090a0e07140f0a021b0904020f0a0f0305010605130b03060117070918030f0305071b02211c170609090705 72
    0x1c4007000b8111f00d5400b40d0001881081c1222200c03007244420442c00c0c2109040d075807074584034010070741c0f07070041c1c070300f0110102e00160f807029288080c810803010200300c080804600540030b40000d21007503001c6842d107001040c0482a040454542500003069070302c03003c0c1003400c40100804058240d034104450580c41000c100c0f4540018520310389840a0b842c2c079103002050080c41c10300e856040216042c100c641709003194561400c040d130030543c100c92284000011802055000740d50b540607000b003018144000092205c10b60201d400d03510290f8000d030303400b00c10441c02c10903142c0d200303005500355010308010018103403180102e180c07000c2801c042c1d5201c1c0d503803220244141c0340001140340c0040c62310840c000c00c050700810f03801c16140445c141809140b0344000040d02c3c00c0d0107181c2d0350104102c0d00c0440c3c001c40d6203088903a000044450444802411308500903580c41041c2000440b02c00d81140d07080d900c413401281c1d41c8030010044000040d4540d101000d0001d0b80301c01401030761480c410090080307480d81d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 449910143 1250 449908893 449908897
    0x310050d051e0a110d0c060305091606031e06080a020904050a020a09050105100216090e03070f29040209010510030e07060509042d0b060d09061407020f0c13090503 72
    0x902e4980040c4040781c038508200c1c05043c0150450303886110391840d00c0c030000755240001d404603402c60030001210f81c3e42600260070041580c040440742100d05001040841d01540410704006170116041c4501c1c070740b030002008403111401840d85a0b480207000b1401458141011584071740300d10180c0e10b5800301503010034064019a04840c4031951584018080703070901c503001c0796845820784001c3c61455a071410001c0c40b1001800b4100c3c40544a0031180c140300010022a40784662144500c481018141019400c0002400880549400c1000e5442c42010b821811034001e580040c141a4603918000c00c005040084490407400e054a5100003018a041800604d0040209886095590640004201c2128400c001111801915145603519042e40510a403642c0796041400100c070019400042c01c240508420107443c00d00301040c14041104542092810103015010022552a0103d00b0380e1600c007103104020320347e4400c6049500902d05040c0d02d02440041982c0021090100e4031190701756 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 449911393 1250 449910143 449910193
    0x30f0b2d0703050a230c040e013c1401030e030705010e240f0408070507090f0c0e030a060506220b0307050a030218040303140103120909020310050d05 66
    0x680100c410450807a4040c0202603016020070070400240140d51164003030060000044513003080c00c1c20005005140080031035018100030406080d656a40c0e0f861584805481414488807045007048201c0814850001850580e92085040d4200d400e21301800031560207410b01d05e040549480b20a180d0140c103100510303103140108000b146540305c01240074a0304900a02d01d4001e5209150b451b41c0c105000a01160090030a5425954980f0740342030202c1103000b80c040160072400b40c018001407403002a8042c0c60004030f82e6400307200647c42041d0036550b00822840194054000714092000a5031a07030280b81c3c4088001e2a11007040b2406010358040743c1004040300e0302c00d0380c2e00740d0f1511364030302003101c400203000c216942c0c0300c0d483c110360105428500b42c1584000144144010400f0980250401c07980d48a84a848004541c0d50723080c407042e01c3c800c0e0f551aa021402c00a0007007030740c040d82e008a074840d140684010020034541805d10003803011b115826111401480001c1d46550310554200c001d03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 449912643 1250 449911393 449911471
    0x30a02060406170f131112010c022104060e0609010908060702251505131d190b0303160f0503030c03010315050105130207020316060807090609030f0b 66
    0xf40326507503200c4001c40040605005114000e04042108401c0c3c03102106082d15403011200c851041020302195032101585003001c8607500b0100720506641d0b001424010b41c0852a602918501d6860501400707485a0300070440040d45981c0c90400307078140407008181070401854404d81c503e030749001242c10030105642d0100142c001447c44102e6411043d0ba03400c80b06c00103181041180e00d400c0e000f817141a024507020040c0000803800840207890940d07000010510340d00080c8012400444e00d0740018001c44001404800004010001c882c191240708011704028006500e0040075480304200d180d500d0a048405150307000540707001075003d0020f5401910483d081d2a2694154541102803c02a0b4807031981c0601d0400100701e16610031a808442800080005a03103000500100e030074492034513407141100000420001344103600200e514402c45050313031401403260b118281100d808107a40300c046c0c4086100012080132800324094260840105c540d48640800800c0c070a0f8915500c450502c0b003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 449913893 1250 449912643 449912657
    0xa0e0a0b0412120b06070201032c030a171302010513031b06030e0f0606040209151204050d09081203101203020a0507120f0b0603030c01110403060b0f060a0e030a02060406 75
    0x110b9680050f0030944120421105000c0c0300c1c02d00011a00d14017441c1e40290400d51100c1e500000c120104000f80c0e210b141202c4e0303842c40507076031201c229031b20ba010740c100e0341c0040d080400c25100b11440c10700d01c0e4000d8003080300c3c02d42000c40540045416400c41c50780d10320101110440000000d20607603d4a40f4884000503d4400616019028080314034585442240e0741080308440003040002c1802d0354800700c11180117858411000104102e4030300009400c06810000590001905842514a01c507078465000c88030b50042d03804046400038024450351000782c0c41450089004600d510166900074003044004443e50b0f03a4805c10300095455800c1500980c01208078a014010203006001c050300000c007130018045403a603200d1480c6204040042d200c0140800404e00f1540e003441100d00345ca0300d41000748102e05110404114590191104591540c0303030555920450802c0e402d000000d00c0001c007d18100104110300352491403140c0b60041d0315004055036040160398510103400035061650b0f50300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 449915143 1250 449913893 449913923
    0x601050c1b012717030c06163b0420070809040603080c160b070303020c0f100b03010e010e121615020a020f01051009090201030609020301090e0714090a0e0a0b04 71
    0x1e100c280341c6003c4c20000341c00400000e80394000008220f07800c03100c161480305126900d440200d13001c0c1100c5c2e05c2618949601280c4855810b03c91207100707450100d003490005400c030903c003004203d82e0300406804c102c6d900c08556060f503441000103050046e0240345400c5c41c00d200000001c040b9807058004803015080416008480c5800304100350320b20750528420360390181443c1c15030586010f28100101099000030b000441035900b03000c034440c8400003408460146225800001c040c0240742c070441e01a49c6020343c084408101401942c41c0540d8000240031000e85031440c07003242d0f9010000311210348041b103565400248171403100d2610246284401600c4000c5260000d0401108103c03803c226030414044c08040416400c0300b03021120550000a50446540f0058010703040700c1d400080000e102000004d1049282d81201d08807201c50000d45000b16202d100300f289100610041c09d42040741000081c040b5485980030b40b440c000341c00b00701d902c44001642c40c0484418121021510404c000100c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 449916393 1250 449915143 449915159
    0xb16120201201e0a03020c10020301051302040f050909070e1609052215080619060608010b04121e120801050d05060a020307180308120601050c1b0127 66
    0x140b01414944401520f040f500e0301620710201454821204140000120618100e0095045903580c240410686442003081ea1030480250003d01ca040d000e03072408000d00e0248242442190107a4101101c0e8035045030a200c240008039800410203030b0580b1544401103211910691414420700c841e1040c1003404000b900000c203050540d51145026103944207540004c0c01c081101002002107288000800600c80b2001c446076803a03c2c4d010352003a000f144107020310644c15400c4d0f0301d044881d21105024569640c601241d070310700c00340300b001d840f403405000900c411818484500788213401440200b901c03415481d0700300041c80038018100c0e29090405c0a6107409034016220b5401840110380d945410002529000e840f080000c101030090380d4000b00007800035000b0090b0565100244040d480110b0702c1c0d180c0300a0039885607a01d02000850f550020307540b50f200303d0440381808842d43c060101c05101e00c0100200982d01100c060502c160b01500803446858001249061883d42c01c08040075032500100d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 449917643 1250 449916393 449916431
    0x429040e0a060f03051e01021b100e12030a0e100606051c0e15090a0f300c080c0a02040f091e03020a03230a200708070b16120201 57
    0x205076250850001080443d60109026081c0014403c81806002c0c06c0c201c090300a00c01e0700850500040e020710245403a500005011304603a9a045013008100c0e1100511a9140b94401d200c001200302003000802040c07039070300000105500101207441c040800540b0301d0590388a41c2002000030004254020501424500d030303042c420700f00000304030300c04462222948604018910407400c200440126400c2c5030100492254241c02c0050341c00895260701e000451000d4841948c1e0030360a91003d030030b51042c030700030b002c115891182e1034145611003140c0d04c4040c0e0f50487c80841d045030040c0484803015032039034000c9400310703001c0090008403483e01c0c2c80d258525604015800c20022001d840e404002500016480d10341c83c1c1609001c0151440048a11144c484c03070f8513030b518400300c0841c0c084d44007508034a90b407a00340843c03c2d14078054101207501a540b5245072107440075070341c0309040821110041c8030080c2012603000c00c10159400da161922041c41d080d0000d80e00050795103101600c05c10044001c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 449918893 1250 449917643 449917649
    0x204181a010309030e040b060c0d180609050d1205090316060909061d04020630160c1401020906070c0501020d0503040c061202071b15090b0429040e0a06 67
    0x202040a0803e544000700201d503030280182c0541e6652900e0841c950b545c409079141e6100780c5d0101c907042e092070310000b0b1000034000d0061000150304070001c00c2850080000308266a0040c0c18600743c3c80030f03a25928008000c03e0a010144201004203440c1d5403030a0100440100001040c1c52115107402d200074494903d650010030701c1c520b404000c0c03001440f0b90b14444038811250384411000e032254000140301d440f4140c01d0500c4200c50107020411018429001500c00c200d144100309207680300b00080c91412100c2d116032000410002510001481c40007103806c4c08402c82c0001401c0050f0400410103961011310f081d152014154404c20480d0707810010b07180007105c14582542182403603170740c025540580740180000d00c4150391034500110003690549414a4216500100e020382c0d4500440c04400c4a0086401d40e42800d21100c0e801c2d03010300300c1c603c211041d99241030301e480c1c07400341000c1c203944940c080d604035035a241d881d40e040640000007500c00307440e001407408103a0500024600440c1c510354 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 449920143 1250 449918893 449918897
    0x17070207050a0f14060702010e06070b01080610030321060b0a11070602160311030c041406040b0402160b040c0308070b010f080d09090c140a05070510140601050703030204181a01 78
    0x42d50070f000078180d1602080b90384c101556150340f01d012a20059034240291402140c0089011032000d041c4802d040081d412101c1e404e05685558a5800031030070800c00303601020740400c07032002c00b01e105042c510415003100c140c403000000c1c596403036445402240d440031164100040c1c22184030440c40e901403001400421003070000b080001030b00e030941c05446c44140320141c1905071070311107d456514244240d10060300010010800d842c82c80140020380b00064483c14041c8d40f0749801c480c080c0c1098400c442203841402032001888d4000c0d95a188142e030010806c90790480400400800101c0d40300180c100c0fa480358114514640c1814031a0414541e50b901001c80c9170f0002c52580c041d20313044000241900d06415012881c140c4c105015201050144a4259180d0000803030080c150340c020701030b0207024810700580e9148103030310702d1483c15114907030800c400784140607010440540c01032000f042600e2090802509259071a400c5c14034907214030a06001958603108141000e043c030100e100d080c29024 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 449921393 1250 449920143 449920169
    0x2011704020f10020304150c03020114010e060409030309020d03020a021807050316050c0a1407090e0319021c0e09060301051e090c0a08150105030d050706050717070207050a 76
    0x41d00066042c0350720107005806030580f0008800118400e0080300d0190901f6200f44160307208002c4024102c02d1482401c0d4019460300041d5190701489681c46812500320b00400101c54440c02c00304002440a86011001c1c9540c03415a20700584032002d501c15124000d0b0043c101c0200d084c01401841041c802e00200c0b0000c20500b04800c054018003600e4200d46061403140c4007100e1080280e816200d0744881e036005101c0e001302d6a04118805511105d809081000e9600203640c940d00b40007940d032074040102c016001440b000c414680b0804d421910852940304640240b01809050006c89a0f00e048043c00904210780c029201d0400510550f003143c0d068000700f00c04d180200140e0f030501240d40881046a401c01c1c00301e41001e40802c64545039280003011501c8682e616004c071030b078070300c60015502c0c500051403000080c10f02e03000c0b03095203160b2010780741c0031300c2e20503107a03149801084020a05c80600c0040c41018410301032906805200d039406800810719142440200b0290905592020340c00b43e1503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 449922643 1250 449921393 449921401
    0x8040807270b0411070501050103030f181a13120539060d0c08161b060203100b03040f0b09010b030d0e0607051504110103090b240a060c020117 63
    0x107803454255844080d000010b001044800040280c45060104c500540300429280140201036100904070f078426210240004c40c0700b001922446214401c1c8034140341e091004000c514104446c01d4441569a00c000f450711800b040300145c00d00e515005291845010040354081040030450320341d008081420300c40c610715082405021158588034901082529007280f03600c9a1600019900401c209810510004074440401083e8040485040c140982d0701e10740c80204030b008011000342804011034031550203802e900ea11020b0f40c40a00074041004d0350300c0c00010515401e4001e075018500c03c4410f45140c51443c1080c401d0240041c015180603490502141c80c03d60300080c0140095600d4182031014640c9140050070034050307101c01600f24011017100101701d039800c200d903500c80d40c411810301d14865081030045085a000d208010300252120000c182d105c2e00c15020f01c4104c100c200959000d840c41c3c00c01003512045290310850204244040b400c003150b0304850350380381c0000d200fa018071051030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 449923893 1250 449922643 449922689
    0x31030906091a0c01060b0c0c010206060907080c030907050d081c05010f05040c02011e1e020f0412112805030312151207080607030c170105010311090d08040807 70
    0x91030814001a10300c0020f00c0b100701c3c11003904071200900181d00c0c0c054640b10343d90700a5441d1042003108a0050098074005006482c101440c3d9001e030039595144a40c6654203030041140b0381c0050a03d042078070400800180f99550f5030b0200c039250b4412156640c071000100710100c0d1000a1342243c000403420980140304940024134203808843c4112800f042403650114180e00522401c00b00b4a80740e10400d8284c1c040c80e415401031070750fa50802024101412142040e43c049000e04052801d20354001c201c20032120109040d02c0d0001d40c0210220320080164000188006410040d0400940520410030106110600c0d242d0002c00c0168041d6261484031041c42c3c02d6100028012a00c00503000c07410540c50f200c03e4003000d03511398007000716501c0d592140c55443d9901002c0b41c00d4800207044c00c0b454041c40340b1400c08814000d00c0c0015180ca81c1e400d0100560241c0069540380c44c0302c40060000750a00d6503105d22101c085402000b0969441d41001c1100d400c100464001d50000d04000c00d8840c0030745 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 449925143 1250 449923893 449923919
    0x1b21030402150a1d03060415050a060902130f0b03160804230c030d050403170a1107180b0a063f15080703030206010b0f0702100807030b04061503053103090609 70
    0x23100c120400141e60391840d41d01e4000b000c01e9081010300e82d10100d104144280320316240d10507100450800c600050360b034045001184411a540888103980002444045008030715081d04a486105442c040603038035690481000b42c00384a40105d54005c0c2c00340c0d001c5003010b00100070314504628000341391500315200c07840110b0040044202d81030300083d46d58442c40c412080745096565620581d4000c60751124003507840009070b2900d48101f4544000b24041c0c0c81d02003842000c0300e100d0b4565603194500304018074150b11034420030a03110800c0b07481c0c509071415481c400c0483c01d0980b1b080058000031215902042c50b4103034010404a0380001e90910110340c001500904491072030843d10758600101c01002c015003c1c0c0e4000a4010040c1034050f2809608264610711a654681e020030810961104010584082d4170400100482e00c0d009403404a00c41c0c1c100c0340e48554090f4511a010300f0340050f241c86400503400044c0c0c400401d4a80c0020541e208803254010040ca16003c8030090524002524103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 449926393 1250 449925143 449925173
    0x10914030a0f1d041404030206010605030f0c07140115031704060503010b070611030a060311100801150c300e030d1b0b0c1b21030402150a1d030604 65
    0xc0040f600c4420030960b03004907801c0e048400600103014200261071000d4410005a50850260140b0800072441d40e10600507039125881c004d0a0380c0c65519035000b40c11195225800a84003030740e082c0104200c6035024090f600001280c0c40708106024030714284001c0503601602c1114040170100f10402c005548041030b24191912074211507a281c03018545000180082812070030403200100410140e003440da8050011280250b0500718507000090400c24012007000766107000c641134070018001e841034180b41d100e0444040c00c080004036050b44881000c00f50160000b04880c8a150b02d003003030540c071004c0b00c05100c011401d1003698034240d400040c0e01c0d113201b0b00c21070080010780719100d40682151201003052507040031004166040500040416500001c181000003070407044003a4003e50005040103841d00403508070b219031080c440320b03140a90028000307a920030a41d0703141c0024420384000810000c1450b840380c40090b03101d0300a20112a110f000d14502c40d4101d1001c0001180306c0c03c0301da071700d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 449927643 1250 449926393 449926397
    0x30c0311030a0509241501020d080426030c04080d11070e060d14060a0b0a061b1704240f0c02092a0d050c0901050f0a0c0602030405010914030a0f 64
    0xc01c2d6100d6000750702e04980a0103607a8465020108601410f038212a40c5000c1c0007011b40785a0040d660100681e5601d0100ca9503d0001c1c4402c000100030603c20301300384401c000000c0300243d0080201010f2140d98005942800b942c1c02c001404018582040000c400c410314681022a05601951000f0f9210100d500c2400006005140081c805680f003100b0280119402490100302c200c0340c4c02803a5847c00e04aa0280c0450315103a00c004051802c803601104941240d5a0181030000781e4250710507c1b200000211071403013090703401414031032403140504060400d00c8440f0410200e2101e070102031481480f40f01c002d22920001c000c2c6d4181e4821311150388203405503030380340c40703030311003121114400341c03210a00349810301401c41e588458240e10004141c521080f52017803115840e81c3c007600c00e2a11554444501284040020401c0c03655540c018040001043c1040c907501d03c25521024140d90003200d0840c1c450f55500b00000402804410342060188503034015801c11806850160042d0810551541 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 449928893 1250 449927643 449927651
    0x40f06111b0609060d1b021204090b030106080a29070c020f010e12030a020f0303070f0c0f0c090605041505060d0216080703022b0c080913060305030a030c0311030a 72
    0x415142c02049610b06100507149030707039481c0320b10700c0d880090003125140b045480241518469035031000642c00c281c0c000107940a49018030748121100200904541e00d5015500d0f15000200300344148000b0921078020400d04040381d800c0c9905480401003100d41000c040406028444040c2d07000303006c40e43e101c0e4152a0030818049890060b1849400707071040c03607881b480c9641300c0c10181a010024103d0101d058003142d80610441551130b40383d0208443c52800140c54404061a40d807080c080ca00100f4001e1000e050780c852a1b480d10850f1080e281c00c04400692110300810190420703100c0d860703243d00c503000b15040c0e40d4200400141180f0450110305103680d0085518032441d03032000450070f1314540c030902d200d585c0d00c800c0c41d010f51641c108000c03440e070841c40e1003005072008105031040d003c088c0a07542c1e95241da036455502d00103a90030001d01c2c00e800c00400c003485030001e071051107400b001e180258000c6881380c90800700107080e5896019a1000c0506041c03020188004507402d50b6041104400086 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 449930143 1250 449928893 449928943
    0x304030b1302010e2d0402040302030d050715052703070209060f040b090a1b020f0706050724090501060602010b13090201030912050a09050a0503031801020709020f040f0611 76
    0x1c071302d002007000b40c42c0d01c0581469003034041c00507100e1680d8640c405004400489825900f000700b28001c0d840043d4042e0441101c080b59248960000c0c90b40c14800c81c503401c081c0856240c072600300c91007165048066807000e2075405031422000286101040f4104c011807800d101075000c1402d00c880500514050541d006c61640d165407203030409880010083c040d0011850300c000c042d400351a2015140c120410040c0306050f04a01c041040ca404440f0302004001892400c0707c01c48090703200d03070b000760b6801020b648804c980b10200c010600302c08581c10000700e10001c2c9400c00710300316101c0d80d2052003968900042c00596441e8810f000c18001c0e403001c3d00150750790150005070007410004100601c881c820340508000250410054507100d07400f0b981b0b0b0314940740c680082c065030362428020254141d01c00c0c80b4010380c148105031038a0304188117205a550007a40c2e04d0810041e41c004400020800300003180601090684522a4008011034988480c20754240c8034915110340b41d4045140319000311034040c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 449931393 1250 449930143 449930147
    0x309030905030a03050702040b0a031e020607060e030307031d07090e01021204140f0c0f090a09020a09021c1a0d08040509040c0602060a09020102030a0c0c17010212090304030b130201 80
    0x12100801d00502610500285403030028a01d92042c1003c92141c1c0c80d02c1074034202810103007060002c2d41e80c015450340c90940c14062007044241f41402c100e07030013482040b620740041d00c94090f4200c1030f01304400540d101d082c603820203400c0c2c07000300001788501d0a0500c16044021030014021045a0101d0000201c200740c114406000e446030000d0045040640c4c0180400c1249501c0c5040c020450f19059551400301d86030300319220844a51016409410600e0850040c41c241c140c603034007c0d654601c005039a14030380e070100d2044e68069000790503882e404251444110248500011110303150801000f103c40940250035903141d404000500401d94104210204849102110080e00c0000c1c11860a4503061500c2d154812083c001c6200600580b0082040e182150103030500e1585e0580165091690f0301030308494211a0340c80903500c02d42c54003000604424000ea0603480a0458000583d8855419800f03582080001e040da030721940c820001000829400804140c2045094050185180c0a4001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 449932643 1250 449931393 449931407
    0xc2003010e031305130b01020706081509090607110a17070c0f0909060e031e03071b0c0501091e03320c0a0506040b04090b0d050304030317010b1801030903 68
    0x31019a502c800180b00040200c40c0c0307030543c2142e004803600d0902401d1190150152040c0081c2c050143e07029076014001180241146ca40c0b0908041054000503c103000080c1090415180b448054001c0c9062208443e804141b940c910324058008040c400016903482c410f0074a0f80c0850507801e00b022804208000b072800c01c4200034486c2441220b13480351a842d040300184102e4204803002c03464000000706031440441990005c0c00b665003000316401440d85110760a510007407191080140c0c59011220303042d401c1c030750803140c640202000c0440710b0401d0009841081960059203121030b4901c41d1909640602c0c110710141d907400b0280c14039140381240c4e0040400d2284400b0300c0143c0d400c20780760040150000c1c8140e00070b0303003c0780c0084d01a5035510071f02c515442980580540c1c1342c0d003000300b44030101158100c859150b002810609015880f070b110a81181c200350070880000e00c80652a44540070301a00300d40c054448444002d10741041059000c6402c1c00310f80041d814180c682030184149805061 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 449933893 1250 449932643 449932661
    0x150714040b25020d080904060e07080a0c03020c070b031e090616020106051c0b0f0118020309070b040b131a09040c09031202100501090606091806050d140606010c200301 74
    0x100d95800c0c4c1e25242960264200401c60740c0944e28140c00014512400400c2d14000c001075242e1588540b514034802d000b903c140540301e01815001c0020201c003e80400c4400e0040c0898600d039522814068544585105040c0d40d042c1140d807044144108010007082140c1c01c0b5a82c1200310901c80e04007034041c0d01400d00382c0e000c140d00072205d82c18000b441c015042c601e0700540c820f851400850ba5000c850a114001c00e005080a500c0b00720f132400300001c219801107400120f842e01b141e66841e80d89004503680d0388181c100c1c001d4206c0118031001c2c40b841c2492503201600074002c81c8003c1d5881c0d2070255980c0d010b040c0c1454800e544441c0e01d0400c1c140141c8890020b50f40019400c0910390a40101039522501c1d028010003680c544400000e2103c02403088405642152b552032850030f240c107105004000300c0c0b4241c000425600c43e000200c5c1d994001c18010b8452003444181e0390310841909560900030020003203818030400e1142140007401000060758000a101c1c2c00034504980310012900400e0200b03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 449935143 1250 449933893 449933899
    0x10e041110050a0e040c020d0338090705070206071104090b070f0207060215041101020f0304030605151e01030c021006122609060703030e150714040b2502 68
    0x506124503042e80300c00100040c1e1116160311080e000308405004c1200c015a04940043e00800341041e0844c0c440e0b008582805820040301502c00011a043c003810302d100e000340440341c0c0d2072000009a5060040a544c1c0c043c8440c01d103039081c2010f94000c501107104000c0010030001030f84426021542c0c0365071002da010798126001100c0e502e81000050b00000718441d407080540320384136000401910014950301c54800441d01e001080c1c0300c568441c00c3d003c10049585055002d14501480b1000c0200050001140540000b140d40d040050f81440071464114040e0701400892902989481ca6a600041c8080d0f0030729000590142442c13040341021a1001800f401c58100107001400c032090000001140703000d01d0442e454005004a102d00707412600c2c400c43c0713181c901800809420b1031b010b4080d051090103428042034500204600c01d040410b074402203045265510140480342e50301c640400382c110f10f4034000c2d92030103007002c505d00c040f030141513410301c849068004c00380b40050781803040c501c59076030203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 449936393 1250 449935143 449935159
    0xf0414460f021b06010f1a0c0a0b0a09030905010806181b1204060c0302070201081b070b27010605030304091a04090302100b0108010e040809030f191b030209010e0411 73
    0x480082c10105200031003400381c40b131400085a60012510b41d50100e488030304181e040c1070a44a0816515000000119000d0003442c0b0b5070004034a0034020a80300c0c1c0088440001d0400340d918014140e1109504111f04120002e010820756803117204d04850000400d40c0b0303c410300d40d206c11082d81e140406200c64070000001207883c1d0f6001c441024928081ca200b607400b4083c142c81204214128041d03002c1c00380c006248a808151001c0203121411070000e03d1085007490911035840d4000207000c10783e02e40841c5940000c040e40e55040b0701c24291048440000240051860500000d917a07014501805c401a030355004c00820681030f1a481004600021b407044c41041103d040194407020038081da10341c154207001031103001b50b100f1704025058840908582e803031901c440c1c4034500550488000f090701445660840c481400b01008009038604040c5d44680c2c2e20411480d1401d05c21410901c0100003c400180610040e550f40762014155a808071100060350743c1ea051108d88034081e031000c19004566 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 449937643 1250 449936393 449936407
    0x70b250c030321062903040b0610020f031204021002210901050c0f0303071206030510050a15080705131a010828020304020f060a090506090f0414460f02 67
    0x8100c3c2171003402582440c044444101421280c503448119001030100c03c01000203400e920b04000c440050352072030310403501b111501d011440d2843e0b100b541e440201010110400c000c5140c49860f8840c5040c0a01c06800842202c0d814000c141001c2e03003480c100342101240e0000140d00c59415a00f00034004c0c81240c21036804554159201d9000b610350344006490180740c4000020305000e00022603034030030001d000300030800b60654002d04000d81000c001d507443d801c407c81c0402c080f1480d00701a050b41c40107840500d15210401c08010500b41c400510a41003681103001a0b5407606820075114080c00d100c6c1540e92a5035101d01c0c1c180c01d071b03000c2c1000c85a6802c3c64031200380c259401740d88100c1c42520303207100d08000001040020301030070080c0e00000d11080c40601603800d0280241c9550b55001c1c000b0100d80038004006403c0c1c810354000e03054110041d908200c400c402c1c0f151300031840c01d02e013100381c1c402c51003460f40c0f00c1c1c10142015000848044001f401c0c0c00c00b005607401201c0c5c820364404110f442e508 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 449938893 1250 449937643 449937659
    0x60c0c1207060f180807020409081b0f0607030e0307320606031b311406090705040e0103170f0a020303060f0103060b04050d080705070b250c03032106 66
    0x1c10807003200c02514180315100c4c1d906800c0d00c07402496400220650510540d03a00304400340002001c204c40d0000203020700440083c1c0150000410501030010b48151100b82d1030b41480e0002c0203144400305824500c2c0d6a0388442c006c0221600301e50000400407070a00038108101c42080d0010945607211005c1001c159588030102d0780300c0c040c540440541e54040400b460310b00c6020f40c03800c85154004000750302c1d1107422400b03481d0351140749445080341e40f000746c02c0c2031240e0498051030f508116801e108002c00050380780251080398800c1c0d07107040850405003000d07034070103000c3c505010041ca0044482402110745240c002901c820050305e0f00115611108503c000303413250002c1d01c40c64000c01c42d6010038211507000e8042c01042d500d812080c14101840e02c01001001098103105071140030040083c003000c501c0c14401c0c20701401c60284c0241e9201c40d41c002d000d010055811001c542513441208203800103143e5110306040f41e0301840d100030b1040481c4280c10b0400d15100329007003518034010000441403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 449940143 1250 449938893 449938901
    0x909030304061112010e101e0e0f0103080f1c05070f0816022d030c060105090108010e0a030e030309090403080105030d0302161b0b162102060c0c120706 67
    0xe1184100b444010300f1240e02c02e166004d40743e86a403d00d402c0a0041c480720f0018480c0541c40340380041d1000a181e40d4004012a00c0ba40a00e41c00182e94086018480003859409240e0020454020500c640d85151038012035030107003007441c5000400c0050701b12a41c08503180859603111022208208c00d0801c42b01c00f500e4400c0e0303c00b685010400300000120b170750039040034414014034242c0252004030443d0000130041f41c2001e0f0790705001400041d0302d4260460410160201540c0c2d5402083d06504040800000080581c4540566810030040801c01300c0046181000203a140c200600c9040098000074110f0080044454110524008000505510001c0c10707040b40c4055095031300100310750004805030710410750b40ea00c0040300c103141701e80026010314400c00050b201007151000603468000000d1161702401c0810400a40c030710600c01800540130142e003003a031201c90b040008444104006c0c1d2154001080d032007807104041281502c130315082c003059002e0703550612400d6892603245040c030010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 449941393 1250 449940143 449940151
    0x80c070b0f0a0f020c1c110601090c030e0a080f0901090302100c060c05160b070c0b090601050a140f121608100c091d1b4b160209090303 60
    0x15400e20b1914802c3d61028800c80b0070803224200501090000320802d2001e501c00002c1101c20815116045c4640640c00d00c4554042c00a10b0b2011803008031080d8028141c0b001040e0454168028500c04d000050a010850381020316401c8039585481250006070f540c20200ea101940000d010514070072619408658081c80c030748030304002c0141c0c62000004482d2801038410345121a42d04440f6100810403c44486502402501d0403402c410b046a030340703248040c1c040c0d03207800040d442070f40144018a011900c81c009017001d10b42200d080a0a20001203014142103905801340340805e400f002c1c1c08005000c0100d058864032012007032650344020066840082c1806105103038036089040224038411305c3d10008a403443e113101001a00c1401d0941001003011700306404812001100b0900d0900b5400a080d400212920060043c0d5030031060758885046050307801040c95060407c0040d0000c454101c105107070242c18000c0e00c1c3c40c01c4841a810a0400d040c020754000484010055103140020080d845 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 449942643 1250 449941393 449941411
    0x30f0201080c0c070308160507030b07020613080904020310080d0c1703010b0a080c1204390614070b040c050a1410030e190602031e060303040303080c070b0f 69
    0x1071581e80400a4005004196002d91107070003445080002c83e681c40301034160b04103000f0158221300500e0707031201d00d0000035500450303c1100c21000c001c401c03901402826800405522184000141590345e80b80b14480c804545215950220100d035030400881d054030054000c06003100c01440c01540080c003e0181880111411491410050300402404050700d0407a40141200c078106010040103442c20a0000c1c035070111000244520049200b4201c603050059004d0240c8040400090b8081100c0303d604550342c0d01c072181c05101400c0000076079a0010b0841d85286481d504003028400d130003206204240003e800070544005202c00d0142030340c1141d045403001c98511001c582e8801220035581c2c10941c8a41e40003151030140c80721107001e50803240210382401c003a1005903109501c11034900c0800142501d00c558040204401d00c9110202d400206003403001402c22441d251001035034a21540c08000c04000d01e036004601860042000d4849180d0b12050307201062905003441c0d80d26040c01c07203040744 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 449943893 1250 449942643 449942657
    0x203010515090d020d1511040e070206060a0302120a08120108010606110703080f040803181e03120c120304051b04052a0d2406050a020a0b070302090604030f0201 71
    0x5001c5003080d0844440e040080c10450110714142c0800c8007034103100d4019a9485503543c545903041041c2c3c03140c28400c040000c4295212404c1c6054180c804800414540540d4800300030300c012075842041c1c40c401c407981125440125142441c41034207156206000805614010407019400d0456003e203505075402c0b00002c004c1e2a03540e00045800b94202280c0d2059604003e60500c00308100768001d00300d0100f050401c9240507642c4149501c1d40c1c3c4205a00581c4051400300300030701d494201d50903c080c0c6201c1560000f4450610002507c40e0200030b50040500d20000d004121840c003070240c020210099031500c0e40360300e4a42003807500d8069801000d000400c1c5c03900003000ba458288641c5004280c0d0384128443d800a194200072046580700088500c0b44040c0013003051241c0a0181c3c28140c4540205c0040e002c05080d031211880015401c40fa09020050240300c24031a8006015810103802090105440d1140e8405400030300c50126020b400102c0040c001c070921082c8400360124504c00c0c0e880030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 449945143 1250 449943893 449943919
    0x60f080606040c080708070512010605070c0510050a05030604060911041a270f0913050f0106030305160c0308030a091b0308091311070b0115080c12070c0f050102030105 74
    0x1048682c41c2140f00f0129905001141505d84258041079111126007040f52801e060000c40c48043d01090380322600042000400400b00480c952800c00240300580700741384614418a8007400501480850300101710010001460543c1d807500080000c11444104000c000341c0d40300844c2c000d03071060180644d80302c66850030b01c1d0203000307020490303005107071540c55036104401054021a5040c1c8089440350b0107698070151108603514011210302542490442882c0500030303180180c02c0543c034841e003100e1a450480104082500302048440c0c5030304811311a0005011841d01980c00e00b0359030005010504040204052108151301580085005450b01c0000c10542e1004140d8811b0300d01005001d46418003075011281401d244000c20742d122180c1c01b04107440a2000c41141e900040401c0c0d07903a80310b000041006a0f41c22038460080c00300e0b40ba240090349001c00813201c03544a50f08402810b54840400100700a1040c04c008810540c01506461000840e040980c082d40007805024482c1e15540000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 449946393 1250 449945143 449945149
    0x4140102061005030714120d02010b04060f0513091a150f030606150c010b04020f071208040b01120f05010f05011e030f0803100b0703020a0605060609061209030d060f080606 76
    0x20440f90014014100d560800505610030301080700d029400240c80d14140101c1c3e80b0520250100e5802503000103902400c0408120a40b910390380311881600022005003c07903142c0398420f02407501d50042c007040c4401c0c07034500800c10030502040105200041024880040c1d46100b442615a000300c0d84c41041c030805004140c0c480c5002d617400c0707a21000c1007003507106160600d0050188000050000142545c445012605036440001000440440011548100480b4103e1030465000d0741c9040d128901d0541e0f140080620103010b24221b00703201c004a44200003041c2c605030742c000da101e802404010313014481c20003c1c0c5020b00403600c43c810040b180107401c1c520309155030100c2c1c2c0c00440d013000000c01900ea000f400c5c0d20180440044a560b040c01180c6241010001c1040c0da100c0d50050140b8412401c00f0012a80f010348001e10411013080304442c01d0307540b2030544245080032041208185c40340d1a02c203203948100c00e041c251080c20524001042404051510100c80d02c881c2520000d544442c20 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 449947643 1250 449946393 449946421
    0x50405010e0a06120e10090813080102041505070c05100503090106060819180503030c070606081902040213090f090501050f06030303130309030b010e090f0a11150409020414010206 79
    0x20300780004d900f6101c120050b425603003103204103032000401d4606d240080007078001550034400c001c0c0c5215000240450510b02c00d030300c070140140000303030003103003000c1c1401068030030500c10010070010490045200400d011132140c9007001418000c00155102c0f20750385019105802c1214101d2065180010000e42c49003e1040030f80329844c1e030aa080140046410300c0001410524451000c00762041c00c24030016208200850080340500d004607240c400500e041c802781c0391a904680500c0e00042640c1181da911441e1380200e0340c0d411140561580360001c0c00140800e1264031040389281400514142c0741c2c115401a503000340148000d10090380c0e0b04014280e21a01500c0c0203415610400c0000e05440310f000044103840e10a1038140945c5035030b500c40c0e400c0d003542a0484141c0641040c1880100c04040040b62100c400c3c1c031028003e040801c1c0c640d00c8211280c03e0000d0300429100c209801c0d04040c100840380030f06911502152120b440d00d10706000e05841d40c8123680903204280118502e0203010309 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 449948893 1250 449947643 449947649
    0xe01090803010b0f1b0105041e0507062601170c010302121302060f0f04060323041202010b1c02032104050f0409020603130309050109180e0a12050405010e0a 69
    0x100d80c0d1640e460180c62502c0340d8424020407401800902c03050140c2400e040d0310418201c20a0300204640c1002d007428125a80c4030424048802c031200a0480020008900ca1040300c3c1c060034035a40c442c640301c0800703c0c0c1740d280c1e030341c1ea6041d0008800046000c030440e0815403026030254003101c8015200e540154100d00c1510070380d40e5055010000030300c00400950031100030503c0075004909041700507119801c1500810324184001d02c02003014045254184142c00c0a0001c6c0b000510001e05d207000054900040900094415891110075080c014001d4004010803440130f81241c54094600b01040c041c070906250483c031038000e0345411a40c8031284c1140510220071120718515080ca03200030068800e400011494009442e8418200588d481c4400b8500c11000740f4480d98140704c00b841e00074114110b80c0c200d6414031801c040c09003d800301048210441b0904c0325000a03407100b805507618900035200c840105003c03042440b4004190348031000c1c1c03048407400c1e01c80c03580c100c2c2d11104029001030540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 449950143 1250 449948893 449948903
    0xc2c07050a12090309030503040e0402031218090907120602070b06010903020a140d060504081305190306090c080f030d051308033702180405060d0305070c0f06120e0109 74
    0x4a92000e009a4551200f2080e80c464146400440c2e40d81d0344040c01c540041d40201c80307a1600000700301c250704041c8400c02d501007481100b0380c640706a10b04900c890400b01e4400c84e000d2190b0a0019000da00d0800140000e0001c020100c4851600341c0b900001940c0003e0007102c0c008510000300d540fa500600fa03180903294000e06080440e4240103030400500306441c0d000354820f680302c1d020004a03600c0e01c40d25000703a0046010390349c1d0b0301da98100d081858480354040c43c01146820040d14501d4414040002682c0c0d0055020804044500b410640c1024640015015016035200340050103400001030188645e500c000f80500d5031030a1413548601005a009408540100001450140611105a0765007140b0402500850501801c20940302c90784015511856000030302940c64034043d0b44200303520400311014485481c080001c10300e02c4120200081c00d018021902400b04000000c800011304454202000100d40c2d4500007030491102c40040c51a013807812410f40410441030051020305a000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 449951393 1250 449950143 449950157
    0x915080105010f0513031a090706120b010c02090c22050102030d1e0c02010c02010b040207020303091c06050a060609083004080a0c0635040c2c07050a 66
    0x84015503d9070220300412041010810a004214950143c500302641c090300c01c40c600303840101c5d80503c0540c005080020164480c440c20001564402011852001c4522010401c1311004005841c001803001000b50300101000401c44001c400d0300181c110b02000c41e03000c640e80d44000310b0a08180c0402d02030540140c000b001401402322258101c0381e1420347d004001d0000c2a400c0c040001200c4c1c46221280040c1d4580801e0b290f00760342401446040038040350700b10300d01261680000d50380d10501003101c1c0500142c0c40c50340d0188010039490300c400c0d500101d040c00075180c03d05d4002c2c014503c9000302c0300803c4504001141d82d080014541091140141350001c0748000f01e4018440354a0769400d51502075402c00000c52401f90901c500c0d10040e114004100305c4d14103111015080e003202c15040e2000050403581c04680b001075032400200001d0800900180d600d8504000d0300002280e0000c03d24100500c6004020381b03030003105000d00c00303012880c283c05610741041c111101d200f071500d004001608 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 449952643 1250 449951393 449951399
    0x90f0103150b0a051903030e0f0d060c0203120103050a0c120b0a090203070b04030503191e0507020f040207050606100305070c02060c1c020d020d020d080a051305071509150801 77
    0x1c260300204202500a100e020000e607100c001400e41101c101c10443c0014500d60200200742d00000d90405000b021540c0c81060398214000c03552455004ad0041c00307517600c408100118900030700803204040c0d10302251408a40e100c0c280190b0301c3c615043c0440c0d03048202c00c8000303003201e0707000303003400c20103a210742020815100c5800690150031050710503a0b0500031245c00080c009000d0005100461003940070b9a25502c905c900300841c100d544586800f0711088201e08452144c0000007104085114100340703407103900c9400480c130b02468400501d0b40042c8005026414002c3c00181e07244100320844006600090615044042d14030941e110700200d820404804014508200640401ca00e40320848001c0e0070301506c0c2a0310075101901100168010f10780a24038954148a40c2d111094640000c0402c800804001446500c005150307087c09941c4002151059003090100c00540f0341000c100c3d80400c0d100c911030625001084d1100010803081c440000741400d2942170344002d03c409840f0b01d01261f203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 449953893 1250 449952643 449952683
    0x1805010b0f0325030e07080f060f0a090c091a240c03130e060102061f05060315090a020a0315240c2a06051204020105090102150c09090f0103 62
    0x40500700300500b50180e103050f44041e140003c040550300c90382c1e0380030507001c040360065410001c02da00a5035180d0482001e111200f90001a4650031a00440710f201c0252b0b0b034448004000d018011000b41200d101e4680000d0801e000d81003001240703038088442c2e400052130410400d4207410510316404078546100100701e0030200c0070142904d540345105480c9001604075407044120310541102d4690440d00b800d01c4025681000100d61203480c02407142070075010820302404c10740c56441118403c2c00d00100150b11301c0508103000000340d5000c2d20007a4941840380010000e900303d07000e81800246008407129150b00701c18080021103a00c0c5010914003001502703a28907108620000b04144400011400b002401000d00c5510700c40c0c0c00640100c0d0116000e0b0b0030705448410358040741c1004018040080106001904ad94001e542400c04030703540d00c14800181d00b0958405c1880e030b440302105003000028240e10004040c01102103d500b09a03070754a03010400001e4080c0806815500780c641000c00c501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 449955143 1250 449953893 449953897
    0xe04090512030c090904080301080712081e0c030a0e01080603120f0304060207020904060b1f0206063a0501060906080d030f1e0c020106060e0612042105041805010b0f 73
    0x159080380c1d00381303884440c0010603d0403c0944048a400100000420400030248200b01c090700807003544401000007502d03030494501030039091000e08512444204820840c08040b1013105050806898075030009050141100009080c10f601064008000a00f540340c0450400c50340d500c2034503080e00f0f220301c500b61402540c00c020000c54100e6403c0140c440507175a000c2d40d6070704c55485000042030141646c02401001c020320800941000d6030101c071025102d40228205034007400c1501c04400c0c900051482004d40510101c0319140c80549a0509c84e00c0a05c0140000500c3d00480007480510350300d02c125000c03507142e442121407030b4011200d98440c140c800d42000b101d00080500c0070488462907001d4402c900d0507018003820390382d555245603c40b2602800340304020903150402d5105002403e0214010f40b00d403000b410b00050040c80001e0030080349041d207180c0900b03048031268209405800240c0700ba4010301075000104458a0400750025407800303094141c960071401d003810802000c0c2c09999075 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 449956393 1250 449955143 449955151
    0x9050f06220605150a0b0c0c0607020a060804020d0615080f0312180a0b130b060f0f100203042606010906060c140c1909060b0403050a030f11030703050a0e0409051203 73
    0x145042c0c003e04d1039030307881000300340180c40c2484940383d0380d0f0624089245801d06220f006e6010b0502442804050703900c150003c03080742c006081c00b144e95a52440000c114a4440b2001420700d8680b02110243d100c031598124141c403104411070300c80340300c621209560b0303008030f40c0c0c10650200c19000040007000d002004120002c121000c4400b00e2902d55240381c90090110781030a2041c004071051001d00c2640c07400160031090a80c2c8584800032040040340b041809001660300031100000b090070003a1017002160020290300311400300c0002c034006006000c006005203d0054442c100001c40e0444241c4200400c071811034490180e840c05540c0c6001c0d0105030761180030414000c5040707d00750b40d01c0d00002da241c0d49811151032040070307050240c02d00c04c88080c2e800c640700030310003804103000040740021034441c00c5400d800c01a854a1103402d08440e544000410b4514500000c0369200c101500300300944180d003610340710a0035030052081404100c45180201400a41c4200ca10031500005c0000844d00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 449957643 1250 449956393 449956411
    0x180912032307020c040606030b0310150e09010509011d0c1c060203070c0507080a0201050d05090304050a06050d051305150405010b04020c0705130510090209030a020409050f06220605 80
    0x300201c00480e21400c80c11554680907030011125101e213480c041c810038018181078102040129051800f01741ea0b09400000040301640e250441050034241494500007441c402c0460130325450101041406000140c40c004480e42c00c0c18410001080d000c165440c0464186000300820003c4000b00044d07100d50759800d1001c5a1901c0c040c00110700d042c0011441042503485000c514103242c50094503007911907011079881d4100c01002d5005030381c03040c00c80b403003d0700c51407012609403130f041c483d68210b1244c3d43c4402c1e840340c2484030000d000f64202019045040d1401c0003000581ea80070383c40b0f0405680c0d5100100a03420a071000400b0081c09207086800500801c000203c1c07181490200e0102d91002c3e081c03440e60b61088504100303130b29003601031600b060b84000c0c041c0480e0138035074018462003415026195034543c000c43c0d011a1510200f00c0503102d107030010030502c4000d4190034225110b42d007050074046075006000024044c54030554451000c0751023174910142d6059035485420082402070f1960720 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 449958893 1250 449957643 449957681
    0x5060703050a140d0e0d020f070902070804080106301a04110901140916050a140702040515240307200601090203070f1425170418091203 60
    0x303203040f14007014008940031400005000092200041d140401d00403503482198481e4a14850510b0041501c00480d09401405619011207181a503840d0042e9003102103650700e001ea001503401550a64007070444544c0d140060844040d04140140141c0c2602c06882100d41c801c25040313007407196120a900c00e000704e12844401074a0000034000ca5400ea005e080c03c002a051b0f085900d1505281441d00701c40101341ca110511026500a0640d014910200040c0140140b06401c0c180c00881102c0d04d0950007081040b4604c0c10700c0050740c2c800350b40c0d200d990080e42030340560440981c100641c0c0b40030944c2080e04d5400c1d0f80d07524804450070b010040c01940144c1003111402d14207141080038078003800850001680368508000000c20110030b4480c144100420752a80e1102d011071b00046404040545a5549984000c0701e402014000c03001e00007400c0c82400001d42d28602080d2001d031050b12101103840302d2480700904c10700c00b87d884407600581022000040d206c44140240e0102d00084000d4210761 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 449960143 1250 449958893 449958917
    0x50d0c0305101a120a20040810180b07020a050607051903020c0a15090b090a060e070b0904050c160303060512071a2503030905060606030106050d0c200304091505060703050a 76
    0x240f502e030f8020304440c0c5140f40119040c0319080c01270009440c07a00c05039404028241000070b2ba11000d600410b406040342301080c0c04900c91034070a1080d004043e40010468450703060005000b4120b5000c240f095401c0070311761000c034440e03900c42e000711a21040700078028140d00c000740e2a010308510304070711074100d504c3c4c0d03507010080001c11b60301c0c00030f100c0d82e11500030784081000c07410800243c81d02c081d803c0e070240c0c102410501018840b10141c40d19618103880000306a07544040075501e501ca0368070320302200c61208103188100369054200a007600c0c019103258880101c0520030661b100124040d5402d446108048500b01820700d40242102e125008a8002d5806a00e0551210500030036826030029844002e18030900c0b00410296401407000d8550500e990325000b00204035003d0810031081703c6d52111455544c462096500c0386d0344044011030801502e0350305000c5641caa00c05d02c00d074404c1c00c0c200103002c0d03403c10420110100300c841c09042203180523000d1303070100c0755079111a5400062107a03901c410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 449961393 1250 449960143 449960171
    0x9032e024f03060e06010b0a03050402030a0c1202040608060c07080f040e071709060f040b0402030a29010e0105060a051c1505120a11010f050d0c0305101a120a 70
    0x96000501d0000100c1201e0842c24440103450003841500403a521500c0104101000c500441c0e25042551600103810b0f1507920001c0d0815000e00170140101c06c0d4000080b0302c5243c0e907182d400403d44220360410074690b5441007980c0b80d0780115080c414485007405140003182644c0b000b0005c042014460500c0c054492001c5104154155091000a505415603540c0c0078844c02540f40c1094011300108518902506401003400c00104014070380603503000441e0454a04024602c0d0880d88034010000c032001500c42500140c0c0c080004121110128000054028610442c0d605a50010b8040c43c0b410012241c1644c1d181c0c00440380385128100c0207c02000c08402e8850701c44d14078680340c20395615903d080100b18020002c8210600103410461004c0001500035002081e02c51003820441c0d045015405d09a800380107018142c004a81170007070464001d64503500040c0b090858400d100d01c216111502d9181507074040105e80d041140c1002140c0c0c85003d0b544003998801ca01140c04219113100f8608 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 449962643 1250 449961393 449961517
    0x6140f150a181707170601030f060e0111180411040504020f04080a23030307090509180312040201110a03080a0b0f032b050708180609032e02 62
    0xb10740e04490140310345038201002440030600508100360403101170f041c25061152070f0030043c4001400580c25100300000c01442d40c215a02000e22500200000302e51450804070340c1d489200c4400140e400d0020f035002c1c0745014410000c0088411020904260030700741448002d40c450801e0010743c2c4010700000981ea0810020035444602c180350114911502c14000d000310785d10314072501c42e540c2040c070400c03000603130205e4488120341003140e5105d0980ca070660b404041440b040281d110380d01001881480817401c041c002406039100b80c1e1818a020150550640c855031100c00080001d2081c1010661903c081d41007101903440003000003000901200c0040d1404009400040c461011404450564151240e003180141c1d4581403551400d0260f54030301c8860312914030798031002829250583d02540390070081e21460100a0100d5441e90111565907040f5581905180c4d542001d02e10313501c51040c0e841c001e40d200d038913092450104c0c0b6820740c00c5460040480c410039103102c4d600c1c1c01c1c11008100100381 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 449963893 1250 449962643 449962649
    0x9061508130204200702030615100c03032301051302030103030212130f290406090504020315060720010c0b040b06030a05011506080604090f0215040803040906140f150a18 75
    0x80310791780e4a46106150601000a24200c5000801d1608004903216205101580c8400e8a4180601001450b05a0040081808100b84e4a00c104004141c880101c82290305880003103c88000030b144261b8a101a440b007400001c1c0160040d001014003c1400805004060784072500d09440344c4d22145050490700084d4048004c000242c016160040c4018440164000440d1b410038034060070440003038240034107480383c0d50065600000080e4280704100d0110302c00c1b140107291560703030895401d0044485262004060505801c6c07000800150302070700e075a11050350300981d0051580e4903902c0e00c8400140042030190107015800ad448d002403804c0c411011301d6240a401c41c4007450a03e00e00600c0120010034170350007245405412000710300340d50b003a540c040354100c0e520141110030002d0303e2594090350303001d094688004070b000f180b02100348e0441001ea80f220400e10222101400c20448240c4443e9802900000007038107000d821403181c2d000700904103150410142c1c0107582030b5403202444480c4c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 449965143 1250 449963893 449963951
    0x80c0304080d03052a16062a0215101a090904080c0d0809100b0105040803040303030b100c020901050103020309030c0312090d0504060e010503041104140109061508130204 75
    0x104028210f03040d4001c01031068400c201010032045d0f2110701900d04c0703441e04807200503000c0c41c614010061030f9000540c0840f00c0305030800300c40902c14402080f10600940b900b0240c010944c800500c5e100381922180724486071444a4012441c0528400201c45050400b2000030070400406100e0b4960703081c1c0c0d40c0a54480c41505503907592401c111410101c2c40040310081140c5602482001c110000e804075550a0002000503810303003100042e9014440c1d42e00c2041e0714080440c00006054140e070003030b408001c00307039044c0e02c2469201400700c914182d1001d00941c08052200107001e01e500c0b940c0503552000180003204d203410009048249503421402c81d11010405103020085289414802007402e1840c5051042c1094102078015150000d00c51400e810004080700140078040002544202003030007a0007000381c1d43e02501200e20a02d804d00800c03000d54102980007410042d52800a0013003151a9162142ca4650b245110104401c41d40c040e40d016485140d0950f0407640c002c0148840140a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 449966393 1250 449965143 449965151
    0xc030204050601050a170a09150509060121120224040519151e090302030901020f1b0d080c0f150601020309012012030a0b040605030f0307080c0304080d03 68
    0x1510400050751401461141002414000c4001260f00714550b540404c0003042d1144850380e910020500030300594902619030f00e0700c0d01c041800c0301041e42c440c5020301c05601c2901c00036a00c0d11490100740d800d60450f06900c40c3e032008844003013452000300c0d4203d0150b600c16100c144949800d01c07880700100e44420040c0b0f0b05803000303000c1080303001c109200d03092441c01c0c501030825941d51074100100e400305500d1150203465610a502a0b06820700d4002229400c20080103c1c0b6040d0500a6903500301c0e96184d400b40c0308540d1103014410300010728541d8103401e040c105c5001c0c3c2840e014402d0010001c40100c582c0c2d58140600400c5090074040d07040300c1e030449401050040303401075140001d41d02c0a044241036400401c0320301543c0c1d9002084c14a18419864141c00041e030b41c0030140d25041e104d25691440c014040240003007842d003500300e406203040480b002c1c000a512a400c02d40c80d8680201c0115142d031080040400045901016241000020094901340740d07903440580c0c00c045003903d103100020703a5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 449967643 1250 449966393 449966399
    0x7050c01050f0103020d0f0602090d11031b0a0612060f0b03060907050c1504080705012903031213052104050112090c0302090a06080f0f0d020d0203160c03050a0c 71
    0x1d00c079181d0b010321103000d1202a540f43d900803e075104044040a841c803000b0f03024201c1031264a404840b01018064481c904510381c030b051014020002103205807081c020f078000200c80301c0c01c0040c91551440c0007008560300514184c1c0980d49a009000d1760805240c64007000142044038141c0c071001009442032095492a01c4001c0004000000b80490305100301440014110300c0e000400c035511108400e940055529070f41400000d0b801a800003c00660070501803480d600c1c103450040b8400540586064412000c1c0e41c00c25889000f000540307420105ea0000080e6102c0c82c8149460750107005d0002d813841d80e8400384220761442e009003541c034072884001a0802c05560300c4108000f04954603801041600d0b026510442030500601c006480340c0840c1020800103980c07076002000518a00c0c1c02c650060340a060001c1c3c44c0c0400d00b0100c2c50901407407000c05083c5001043d65511460030b5400b85180010755648903040c2c11080100360380414940b0302c00300009130b0401400c010a800b42c1c0c10308071120700d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 449968893 1250 449967643 449967667
    0xc0607090f06090303050702060418090506090309180c090907170703060509040b06040e010207140c03030c070e041a0a150b0c0c010806031009030c061803270801050705 74
    0x10099001003205128000204031043c1d2140442042c0c9600d4901b5075511003079800000c8241c00350b80c00494055111748079191007880340c3c1e48158016031003a001d8070042e96480501d03645a00a52003603c1c4c0040c0510400e0883d004651030725603015070032158590a103c40e40011641a650032039031b0390040303110702143c00c3d56074550004d00f5500214a190622050781480007043c01c1d1f40014000400b050241c41c04035078035a45035049036521000c1c1100854071030500341800149407014050141e42c03070090100600c00750a020007203c04044038440280a02c40c40c01004821022000340113442d140825108084c0940c0c15820780da0141080c10404908080c400d22140d844107240d500034015a2400c02a8551000011424114510382420410050b907262030100b800c010302c41400e07542030f524082c040b500301500511440c0c1b20500034281007104003c504880c0e500d004e5030401c0a0040b9075651440c90840c8640c46000c4201d10011403032041003135403020a1400d40c2d0056030418086200495800c640c40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 449970143 1250 449968893 449968907
    0x705060903070c12020a090c120e150a021201181811010810060e0d03031803260408030a0216020a060207060f030209060307030c0212120f06010e090609070e060c0607 73
    0x142c4c1c40c610082a085a0016482a54500c00c02640a4a4038a00c041c601d010341c1945954050710301c02448403d02d9207000d15103031125100c1515041d440400406c0c0450700a20270380e020484043c4071a1501e90030301c0a058080c481c01d41d5100001c80c1c94111007480c41580c2c00c05559014410205240d1492284001401c1991b008046444041802404101e055440110300a5002081d0380d00b085500171030400b28054418460010150302c0280031490030560701c07201c1c80c011401010100781103d140c030a440c503030100040c0d9000d040554288040781c100380c401e80c01008180b01072200401559030581c0416072181c1154041005a080701404200f03098111610091300d004a00d01149000111400034409000180c19081016076030703051850780d540204041010080204011500d07000c4151007030000c032108a03110a10302d819100401c10729401240040b4440c44000c1c03011025a03500c0092180c40900101400100041c10b510105035840c0c010081030810341140c060220b034942800058001c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 449971393 1250 449970143 449970149
    0xd060504020a02070e0c16080c010e030c0d031107050d0801030203010e0d14070c1a07120c050a0605061906080a05150a0608090c06040b0c0706030c120e030705060903070c 75
    0x5500421845015542c01301d90882561081580212541c41e941c500030300b076010720790700c13100583d1a0698130006d21030400041c0102d41c200f08001d0001c13000181901d900ca0040d182402510b40c820a901c05d40e890003908100382d007032030080845080c24859143c69150000b403080d0213000c0360118005100354102030098924150456005084207840c0c50b1004054086048689401c0300c80428120100142c2c0c2100c500200b143d00c0b00324074030258140241d44150b00c0075400f21036100700791140c00c00e0603001d0181651001d811030060503d256864696a01805000744a10303888007060401c2481071242d01a40d401412060f6a9540c852815500c1d000403524040d00281d07009150703401c590b2403070741c503800c0c8801503446a192120b519180e00094031300d01008402d2440e8015404140030440b4681e0302c000c0c010488035030f401c0b501000d541f400700303500b00c1e4281151710f000030700a124240c80720f21191304012030115000302200e02d40142034482a0500314155440c0c0d8840c2c00004044c400c5c003002d094040d0107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 449972643 1250 449971393 449971399
    0x617090a060903050d11040b091201090b25021605120a06060605070303050609040209060d0305070204090f050d030605030c0f1507062c03030703050405010e0d0216061107030f0f06110d0605 83
    0x240034204140b070710427401010141440f480d11036a40324140c090a41100e03807003a038400d51040090510000c00202c00c2a43c1d1682441a107265041c59041440003a00740d94506010804514042c144400e01600c05000c0102544510403000340d680094a90300c2540001c041ea0383e03a0540f0342d03045140c0102643c001800b5a480f80798244103110150f41c0f80500c45411030403c81d8945140c0e0603515050390395004140c0042d501c90310f03058440081c0131214900000a5102d281620640f080c0983c007542110910700403580c140d1b104009901e09030410300140c46d018000100f60803805841030b02888081e41c8605001c0b924951943e140ca1100400b00c400c49803510074110600c2c0c403415074407030105e680c0d00004180720b0401d51210081001d00c4000e6014080400114068555403140e9007001307540c4080d03007a40c05d420a10342c444005003c91041d0215104c00810b14007030224076165885e1540104080c1c4420340d085031000c001c0d400044c80c9482079101e403c0310003c519446400d034940d8a03085913440d501240c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 449973893 1250 449972643 449972647
    0x8061005040810180839060f07050c01020f090a0b0a080402011b0203150f01060e0f060a090b03070f02100c080f19090501050a060605040617090a060903050d11 70
    0x2200c2c100110351214a603491035000115002040c0004540052140c4080c0002a00082c5a2101c00c2c6001c80070f070079032209130070107440a2030440c001405041d5900e440182d50700000c012900b89a12401901d4110140d0b15142d03040840342500c0b06c0c22a8400386184002060001e44141941030003060000100a12080799081c1101c1c690042c0c00618020402410400c4a14810440440441130f0440882d0040c0c01c9640e0307248916040c0c440201305960310704256900703100006900d40300361030001c1c41d404080d05101e013652a41e01132042c190015a951400c1c060b20140216982d80040301451007014941e40b25444510100320181c10042e0a5800d82d254030700f0b040d00d180490f60070612607034111030300810710500d903540c1c20b40524106002d00b07101c18456042c00740480900405402c9540144401402040440c0e519182552075208e41d11035500030074424030000320a1050100f04503400503001e415a2030f6000e0640e607500c21136026400850100e0380c0030844096464541c480c01f1000c0d822111000c3c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 449975143 1250 449973893 449973899
    0xf060405071215090c03090b0a0209010e0103110904140f090c010813030e060a03021308010207022107030510021206010c03121a0a080109020108090a03050a0c1b060806100504 77
    0x144400308007142d032040350392260004801c4052071580007008050504080040420480004000e803040c0103003500c40500a5010900d000d1305882110024041616101221f615500042d80a00200410750411742c005000d412410789850264108886080414206610349000e0601946501030000c480540c0650440e001d180d8108129a40010442d9141c55142d102d80c9002c5524181030020b050b04440302103000e0840c50f40507005440b0071803a82e1500020541c503a0245803c0340103070300004e0350050004c45221604012401c4400c0409120b005031003506480fa11898685001b0404030520254001800203200b01c0304001c454220009180c41c6142c103005490041111a07590720102400d40d07078100901139150132682c200002e1074090301d0840321540d0b48940718020800c80c1c04c146e01181c0c0b2400080c0c01ca03540481e50314041a41030315a5818902d10000454051071540001c41d40e0340060700c4001e083c1e08180c0c0511000b4015075844030340c545000401c1c0014070f0914030708a014454140028 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 449976393 1250 449975143 449975147
    0x50a1704060818013801081302060c100203040f02040605010206100302010f2d0e06070b040b0c0c0a0c0609060513150306030213063f0302010b06120f06040507 70
    0x86500300c0542c0400c0d4520055030b43e02e650040c030340754441c1141000d041c0504024201a0996980800c3c010049110300144240c01074803c22030464040a41144943c0000010714004000c3c0c48140c605204842c02035075440e80b6441240c1c000d0720103448a2030310b0450201180b40034050040070b48030031700c0034003400e040042b120b89001c8a64003000741808004915400000d11440000811400140c202202ca10b03014200c03d407a44580400c00000480018070a819030910300d0032203000c558400c0d007041c1c181c0e4494070398141107200038005c01090a41000f07107020400e800c01807140604d0180d89a240414a0a030000d080c0000a0b132000050000c240704c0d1140c0812003c080d03e040b00c024480402c6003001184c4110000c140d103810003948611182842810030400e0341c08641035507480e40c03020260341b140310701840e181c50158030089100720100110640419a031070311841010310038000032030200507003400101c03280c110545110200c21034804011084440409260708131500f560100500d0a00c01c0d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 449977643 1250 449976393 449976407
    0x240609011209050313030b0115050c0325150b030f0c0d0602070f0c0b03010305060a0b130c0309021f021504120f140703080f060f01121a030109050a170406 68
    0x1d0094256950303001003003400801d10072101122801d1310000191a05c0345085500c501c82800b0b8003900c1c0c10039914070082c5030300030011980e004049200850070040c02c1403c0c450b00a801e504600f544004505000380017440b40394051941d040d0900d0040342c41c0d1200d100349440c0c058000d03c0c24030558404000c054071611005004650190802c03405a81c0f08047c2c100f05c6e03014001450018203026000d500011148022806581030300d1194040c0c13402512980208400d40741d142c10120f0780059102c100ea2980b4046034000b10100d4890b04001c140e84500d60001132111315511411a24000310318407448a040d07041c0b0131482d020700f4154400c1c04500300368032010f08815800c4555014800f040103c0200d443c022510900c1203000c844a0304c1da542d0f01c40c41e0007041004150380c550110b001281c0403a01900d8407a400144c0c0940607503800a590020704003540141211403664070070615030038640791184e20280544100e40e80148000d05c5900e07582c0c6003815201840c2203d001400e04203100a10200382d00c114 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 449978893 1250 449977643 449977667
    0x203010b1b150109020903070503060708040212150105040f0b0d03121103040f0b04020114030901020a08091f02030c071406071404030803011203030b130c0206130b18030405030624060901 82
    0x84016190341d046c0d80424a0301c02c490300480e6241c401c05082081007a4032428240c880ea10950300d12485800c4020300d542d0714401c40c01c120201e40c0d9031900502c403a0900d9404001c5001d1059008a118110100805c0405065900c2540040d4089801e0b40000040340a00b04142e4641e0401618615043d1901d402c41070711128000e1440300b43c0f0000c1415a8031500341e10b07043c51604003031a40c0d03078144004403500070341c071140b0002d010850020014501d00400300756001446505403903421000e01520311980298002003050307810400a025050124007644100c0b040707034001318001c0445040503880070f801c0d60703010180c1e90314441041006000207000c40301928110342c200e0510184160b0310380350036005403688001035904840b88070050005000a500a080100b41076000d8903001d84913440003960b0720004020191400407014045000400288040c80300e140c0e20100350381c10a0384500009090080c1a00d02c410f00078060748185000140f850600d001f2131030200c4a45240515003800a032107070311515 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 449980143 1250 449978893 449978909
    0x121701031203060e1503070f0b0d0507140f0309070e0405030f090112094b23060907051008150f061303030215040b0f07120203010b1b1501 61
    0x329034007400341d01a4010f1000380409000300c08481c9050140c070b405004010364014070910440d4000520340700f10750107040544d440c10305000d01c0d10754010035040c00f8100213081c0350204101c0034050340e60100a403000d4009007103181c03c1e8070b942c3c2c240b103d000e034a421610b4100000e000e0007201404006600081211054254554500d4503480035500603541000080350705008503040c035000000308481c55040d2081c554201c001056048181084800d500d901a80009180403115824440c6070300d0881d84200e60754480c1101e003000900c00c0401c00480c1c429106c4681d035542c041d00a100381d0304824402040505402d950310b01c14040c0004004200400181c0306040c0c0f0b00c6800101422a11103103c61030b43e105016105907a1180c0e0009050704000641c40300381c0c010701451441c502e08105500d0850b0080f60404042200ca84403000600700c40003001d44107009001d545031030384c032402c0c0d042c3c000f5600800030300c0d18607512000c8400e460302c440c00d4084200c034510f0f00300c002200800314181c0d5585041d40c5c100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 449981393 1250 449980143 449980163
    0x2010806120a0b250f03050703050c03063601170a200d300801080601050907020f0d020a0b0a0c090e130203030705010b041116030c0218070c12170103 66
    0x8207140c00031404d5600f039120f04100d0411521111039410040601e02c03004250b808000c0d43c1e88414045040350b4040d036004148400400205d01c480c600b040c1da0460134004a6225030401119110360031403070800000100c9040346030030042007032080400d0080c0c45808088068454880641d5074a60100c3c031400310b40c0b401c6641c0c840b000002d92200c03413050104c2907010302d2941440e2550340407900014140002c0356182d210401a070b011892040000324100c0303d0100040079164204020030203901402040002184991640d10810380d00403c84c2c010840e40070b03006046d60160714140480031900040100e14060f080c41141140980d10085040890760130078140417183d04d500c4402d05181c0c0000700044c1d4184804113048003884019403146c550035a084030b04111107140c2c20b0380c8448034041c1c0c07440d5000d040348001490300483c2c000c00150310303014801443c500d031142030001c20342d81e622005d40e00782c8000361032094000c042000c02c401d0854001e00c01c2c103000c0021140380c03807500c00384201404000d00c04120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 449982643 1250 449981393 449981401
    0x70503030604180503030702070305101e020703020c06040e0103050d0e1c0302100603080306030706030902010f050a0905060f120c03160c06020f0f07150b0906040e210702010806120a0b 81
    0xf1001c0050089a4000b003520303981e00305204000e40c0d030100340c0400c0e138050107504808000007a81d44544e00742d18241d400015031304451031142900a42000740d080c0c0540c003400038860800d0369441d00420140220300003a11032541541059480e10203c0c800030f105010501003201c00596486003061400b01550700d1040c07400d02c191400300c0c2010300c0c039050901d0290a20501004104194014610910090f030854640070358489c01202900c140384400303404110320780d0020315524031400051061480a0400c1185ca65880000c140b159100751342c1e104400d640840c00800961002d00c1203030300100d0810700607046090004441101020074102101400003240440e01004559016500c051101f0600710707454030703000100140380780e00440c41200c01c2c8455401c0b042c4082038910075070384200d00c00f074038002c0d09076146400d2000600d864083c00c8850300c9828039403a4452080141071000c0070f00748004640701d0396240b002609945002c0c041078800c024030004461046000138119030026000a581070054407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 449983893 1250 449982643 449982671
    0xc07020301060e0a0b04050609010617071803030e040b040b031f0914060603070603020301141002010e0601090c0315030807080a05041a03040b0108010b0f0f04140a1d03070503030604 80
    0x1025070f00114441c000c2100304040c4000540c410b41a901040d5428806561a84100704020000340108404511140401c1000c1091031604179030114283c203041c019028421541c0c2c00510a03a0700c1100000d4240c140380307280e420036000b40074040e40e040d281480b0b1710966100007034442000b88410006000703107000c082c400c508190080705640390031134210108030800b006003c3c0c960a0407111107000340700d03000c00020640d00c64401c8904036403441035120505800340003080030030b00144c2e90305400c543d241e4503500c2a1040c01d00000f4001c091000700090580d0001030080c0948901001d03458608401c0502040812265401c8070040342d031003450142d071034884070f00944e0140515004401804004416150100c80101c02540a507016100c44006170b80c2e80d10f649402d13180719101c802d402810340d4150384c18509020700c0d082c9421000602c04140c16480400c1200100001c0324440d461a8880510100b4101000c91404805900384041e501d0403600e80c5a0682d40e220160520340250b40e10581c0080c451 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 449985143 1250 449983893 449983901
    0x24050901030902120d0207050108040308040b0c09100f021603050a0206210403020609102a03020409020c0601051c050303010b0705030904020c0a05011a0a05040504080d06150306060311030c07020301 87
    0xb42d8010002c4c2802842000e80959030ba80c04015000580300380c1070046400d40c010500d8521556150b40c80c110719550f150f403103c0c8400310180100c840d0520900240703d840d9034034070342040c41010715911003924440c2c02c80000c1c6030641070390b200f4450802100050021610101c0d940014580560340c06584911865924464101c056141d0110b07000c65410b1104040d8042211401000d5070400c5030090685a6161001c0302c00c413011101502c00308003440d160465030207500b09502c010390700303006081941e01c98400f0300f0b036400380d600c039041f50b0040350040c809441c200349489103500c244124914030000a94519613a403006000341c40f800b00d00494401c0410208000702c0380c4200000d80155180c1d00745081003aa51104824225819401c2c0488074002c0100205404500c490080504541910301414071006010140c03040d40d062200300021007501456000300f83c0100225044012140300f0002d0040480e82d642e08024101428200c2410303a1140c05025607400c04695401e00740e980600d840028018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 449986393 1250 449985143 449985161
    0xa0201052211031009050d03150e0a050601021e0f12040605030c0f040b0d050402090f090c010c02030f010c0c02030717030a14120c040f0b0301030b0708040f08030901050403092405090103 82
    0x8241005e80d040204040424500c806000d5a00c040c0103212105001444500076801020745c1c1444510000d68030005035081540c002c1018010f86800c4001160080c1c8a05000781e85443c40d917004101c6e40d01101c40030012a448690070389803117802c190410f00c004000384405003005802c0308011540c08000c01c00142210028200b0240c41640c03501c2c840490800340200300c50592081d1501000200d0300307107901100d0780c0b107044510090940310f109540152020740021500303a03058410801d00d43d03580c660900c1030280c600e40381d45604180070b4562040514041c030035001003440702c40c40f0841000202d000015204c1d01010340c20044582d000b9521030440c5400381c174035031040060542d000c2c085030100c114010300503514a914102c072300713540710483c6040610081c4802804524480002010341e0700c00e074441c541151084a040a4080c410303140d079000307500269480c3c01e01c4d0750359000b40002c0640000700c94004208441d0100a5400346540c8507086009000404052040004414032160f02c070381c0c054604 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 449987643 1250 449986393 449986423
    0x60c01090c1a120f10081203090111040e0f060d0501051312021203180304230414010308030601122d0c0e13020702150a02030a020105221103 62
    0x100c091a0424600030314051103842c2c2c0040320607641900c000e00d003004a40c4002a024a0121a920365003241d1000c1c40000b000d0101c59100c01c403001c00c0440c0d081c040c880c0c005c03900e451020f03100d0400802c25400c42c0c0205151040801003008100300741308041d14195444581c00c869188580d68444c0842d0f00010700c07500050065181408024800c00d00030b86446c4070a0080b405161044210f4038103903603031548400300f0300505200b800003650942000e030702910300d015504203aa0816942d0701c2c603003803101d02480b03032058040780117080403226061504c266a45181a48520710b12135245844e880018400a4042410007400030720000390b0f0700d00c41d00449042645085510380200038500306040440171100000303051800e004194503a944a403e0807010450f00805030f81030021220401c400940c009401240c0080340710308510214910710340606007038642c0343c02030f640c2c401d0aa10000e00b1984014200f500864000c5003030103101004803541c1c861540d00990004030402c82c103001900d441000a01d81c64 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 449988893 1250 449987643 449987651
    0x1d1303020a02120618120f09060c01020408070e0603060c0415021615021b0102190c0e01060503090f0d14090103060f03081c0b0f0f040b210c01030515010e060c01 71
    0xd150500060010322445c45124140c0f030420300121180d44441c0d60b68003510200d8018400501c58042d0140100000100100040e1520107003040795401d98006611010094005c0f00d010420f041b944000242e0080044016280c145820745c2ea88580d8000d500503412212245046020158001c102d100031180d03a680803003203801d640c1c40d844038a03c501e1401c204014001c031618000c100c9462807040031880016000b13442d41540c0d01140003401d0088000c1a034220401e03c500280342160901d009003e80056980c040d601d00d404032a080c0380a4000301c0e280380300d82c00103000c20340641d03020789034607a01c0845121840d914000c0d04012005010190821014004550400070400020000070710b004034400b80072200b0b40c5281c00700d42088600c2c0066180e00328105241c1041d5518001040d519040380081001543d0341002005c40d4889150311071030348c81004c1c0510041c0007102c0402942007202404d18040c0201c0c50048032107200350956045143c10720a01441783c021658400c001d655a40e810840200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 449990143 1250 449988893 449988919
    0x8030a0b0414010b03310201080402030304030803090105010302010e010507022b02033c2d0607030902041b051b03090d082512080a0b04020c06101d1303020a02 70
    0xe9003a8000d5a02c510082c1c1101446c0c031540310061303282000008841082c0c0d40034406034005441500f070062040b645400104004000507034290040d50080703540b05d000080c030350f04520015000b0070001e02381e64107102c82441000016a6506204414072420401034428041c001c0f0ba01c4400d082700301c00081d410f0044100d07140440e0226071b140305a03080780c16061400103120b0080b04d078860400000c0c00040307810907059034503041c610700078510800008215540d429940382d0307012414208141d030010002074541d2440030940c902406004d00b5080d42d1803010110108003100a03200344148a14080308104400700e075191448107005490513000081e00f9010144420310b071007200e40e40b0071000d02d9040501d103000c258290140112464010340e00003225545220910303010b8980502c02002034440b0790301c400d680355041e26a80050500500f401e0014401800c001001c00146c400503002000d8000d540d80750820010030442d0707455081028040d0a9944441d41d08007207003007225600029410400c0b0100798 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 449991393 1250 449990143 449990159
    0x4111020060a050a0c0c0b0c1204110a06090b22092c0706080a2a0306030c050306100b13031a04060c02060c0a11030d09050c091308030a0b041401 64
    0x441c816402e966041010740e80310541d98044400000301000043c2c03a03400c034640094240e10666400c1400c0c0c0c500c40e414501001300c070603002c82e0111001c40d07410302000c1032030001c0c3c00c207030001c0805842107003000a0f40070b06142501c0458000d81d514032400c4e180d290b0b4010390b1000c0300050310000c0d21010205004240c450b0164500306082c141806d046800100c2d00d8110702907010408030152802e5a44107005a12014401409401c51109402c0340c0b10034060b10310801703000d1864042142c03c0c0c2d0f850200d65545141010600b040050340001d000e81c001e002008007200101c11107005456008205507140c0d01010180c09950600d86c1000f0110300c040b130300b0300d1001c040000404d4429031045006100390380c08804226203403241518607400301d080510009500b00e0289000307202205141c030480382855907074a40d00c810b881d0b84034400c1e5903030303046454005c0450400c4d403003a41d400255851500100c1042d540e840d00315100081590096540d1414130560503980c540141341602c2c907000c40118a561600b580b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 449992643 1250 449991393 449991403
    0x70311030d05012103120f0f0f0c181508180304080a0c050d0b06090c0d15063018210f090506090411190206010f090504111020 56
    0x1404c1850a4041c14400351100005426402c0c542d00d50744141c01529090281c0c40038140d5003c0c404075032501c82035600c20716041e6100380e40d400094440041010741032154081c0c00705003030411880d00c00401035010710100d00f00d01d003c4051070346c892030118a1980c9560366400b400d0208203c044c09408001000911030b400000c4800503a809804484036090f40e4100b00400342e03050040003400c10203800001900c908d8514415a40490000a51840e1081c203400c49807c459803034448100c1e401d80c14100f4005c01d94800c0d8030440c04151024100c51120706091290642e4824002d16050030b91118806042c20360b000d05140c00d0300c0d6001c818000c0c0036004112142c08128032199190004d00c252407410a854415604c41c0110380c0050b040510300002041840058540084d020803611020410400d8440205102e1014254a540035046035410154582912030305503003e032468034142024000402c400c0f41e02402242412a04d9110925441d4401d4492071f6202460752003147c0305210351007260b400410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 449993893 1250 449992643 449992649
    0x9090411040b0a2c090a15150f0e0603030901050d0c02011e0c030b040204050625020a120b0109140109150b19080a0908030403051305150406080f0103050c06070311030d0501 76
    0xb20103aa488100440c0c0c0307501501c22070720006640c0c4084c06d103901007980319030750781d0485491890100d41407038100041000703c14a54031010908949030300c104030443c842c640c003a4004404601552402d403400700000c101d070042c42c25a4403595560350219108034000d501401100c017032510755034403000c6500e07000c000400d41d40000070042428055180014a0188200d030305846001740124105151a10181c9910007003003d40204001202a0800507a99002d43c01004040d51847c1c60501191440c0010b50a041a40071168a41c105200342c90b130515104d400a040d2500d242c00007403000d82002d24100780c0c980d60f90191100003c006003c4911201c191104c4070300c1c504945030120300b52520718001c0125000303000041c3c4048000e101181c000f0303200300020864039526400d121210394071140051010115400179424089000804102d071b41d4200842c0c0740d00070444000740d03902e989562603850300d507010100c144e0300c51240003914404060003080c8004541031500304807600c0324201840e1500501c800c0c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 449995143 1250 449993893 449993939
    0x31e0c09021b010516050a110f160b030103020607022b05010b030717120a110f0115140a050f060c0307050106060207150f050703121b08010b09090411040b0a 69
    0x1200700740c0c500005018460040c4e401c3c4d290303d803588407003800486d04c54004030641c00402845860001c12014100f1040700c415962601402c04140f004840b00144603487d84500e603071840900040026030760f0f14081c0d44800d90140ca403200d6000842c040980001c02d20740010081e400c1000c0c20009101d015441001c149106a0480c0c0e5015241e4010b14100000c2500a40680d0b22200e0038010010144014010322552410024400d01007121a80e04040a4512040207a90740d440e2000c2c02601c0ac40080700203240710a0070a40c9a0700c1c43c00414400340c1e10f409400d0162026000d000b4064964004480c03064126105a0703813104858600745010700464450207006200e50000401c8801c07682c0001c0304034601d603440d00384c082a103d04069803280c208080681c144810040201c05580b0980201d02402c07443c070741e85040408044501138071040c41078115030004881031014040d0b80e100c0e94000341d003040d005541d0031001070403100020040c180b11114540c20050240c000641c4403c065400c03a14a0086 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 449996393 1250 449995143 449995177
    0x30c0302041206050a201b0f0601030f0611070302210d140a11091e010c020d0b100b0f0f070f06061203020c1e090a1b110c030a020a031e0c0902 63
    0x22001b0a000503420303000081c4040100c10b4030b2507441c004c8000130480300f00580e030315010308050081c2000000d074010742d10320030202841003c1103401e105254542d00d800061324200b00864070f0082d40d9499603400c0400111030311182100203a035180607209283c49401d400e0084240b402e603011104901614207258013414035011060f8190300e50184e03054403202a2a4220a200b08041c024040c0b9445c0d03a45414407410783c0b011409078881c1c81c0c80000340c0b4007901030301c0030b0383c20000c0c0c0060079505103500048081d20240701c50705131803200000b19113902d903d0060040d100d40301805d0600344101d500b1310040000e840d1040c001004030320011100507560003502940c80383d81c1030f41c0c1844450b002c10501035180c0140041c182c2010b20b04880c07603070307046091100002a0380210340c1c50030002e100342e6941c040110f010710840072090071042122000c600d200f0303006060340d020654046440300c40c950000030500b540901402d9041d031451440f05441540103404038124555641e41e000c000e52294030390600e030804c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 449997643 1250 449996393 449996411
    0x406061e03020a0504020922020906030c071b03050607030e011e0c0801090911090406020c010e07080f0a050606101701120b060402030702070b031314060f180d030c0302041206050a 79
    0x140b01fa2420104050b00003815107444000103421a001c1004040e403240c1e003400440c007103484076805940700b0708050b44002e0380c40020341400a4010203110745da0f48119260b91007800081d8011403056048080c030305011a00c806840c51050140c5200a05031440314103080400e1000704440c1c000400c1c000142e29601c41503600e480b0b10000b9240e101a002d080e4800029240e11380d03080c05e048032940903000d50340050a01004003406801c5d95a1010851100d40c858031050000b00d4003880501d050032680c4008061035001941c4007920f13440001c00c020b10804071110304030003041c003c3c01d000c80c0192003285c8000240d0b0b1a8072024070900c4940d80185d4401c0500da001801c241080d01c2102e001d001d11b5001400180d00c3c002e000d0380303e680010114286540110f00040000c0c030010700c01c8000802ca180030300a00e140061800d0100c1074024001c8070600c000c034280308415000415840b10030340451801051090b50400103402901c00c540c0314040c036519940c241d0003848802c0c1e210702d000e5842607205000c0d41c08 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 449998893 1250 449997643 449997649
    0x10030c050616080f04170c090a0b0a0e100509040303020c210d2004031a07020a21091a0307020706081033020f0c031b04050406061e03020a05 62
    0x64003240d00c0b0040c210280000100b43c50304040c1440184240c8401e00d4103441d010440305c4024510420718280c1d100130326240729840c04554540e4007202d521003c00c0030b1036004001501e00c2e446441504e00c901040c1002ca1001c125694180001c2e02c00504190664101890028000c0d4844e0710008124000d5028611000701030788000c0402c02c10440000b400e040164002200030301520020140900c821128981c038850240c0190000714005e000c014401550082108840b2a00400300000c43d0030810400700050044004c60010381887d9607203200c4003d07200c00c1610200c620b500b104240007541442d010303551030071741c005503c107861590030b0fa03401d241d40c0c003c180e603104e509071041c2d98542560790007031084044090402074401c5100340b11814140b01c40d844004a100301640c24001600200c080325880b0104000d000d40f10320781a070050400a20850302091141d44601c44140f0564031100070078103125441d0480000740207402044401203070300180c040e005103001d12040380180114240011685 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 450000000 1107 449998893 449998897
    0x150605070303112118060a0504030f0801060210020904020d0203040302060711030a050d090201050c0106081c03050f070309050a0f150e0613082110030c0506 69
    0x400d03241c100202034a0f21007240f6440b140013001441d240d0140c2146800c0c42c4e601c20b494500c9076480d10380249000c2c00004103205414807406d802c0c80b031a502075600050140d403081e111443c40040c80d00d004c0c0c511400900c61030015070407100c1d0850010030507070010040e40100410040c135000e10903405204a0300160303000e8006901060410140070b801110b4403011440307a400440c184140800c0c000e100e441440902c00e54a91152082c40459008406560304200000c009120040e01e0340310803a030b1000040d88407540300d0b040b10050604e4500038401c60340901e40300391100b005503a40d41410303809444240007c544c1d0748545031035003020841420390b012200c2e1203454115a0349003103d80c00c4059900a02905e801078010f00148544001c550031051256540015039a44a0101e400d148891107440001038072201c0603141000103150007024100c055a10030518032003010303200d4043c01894 = true := by decide +kernel

theorem cover : BRFrame.Cov 449820143 450000000 := by
  have h0 := BRFrame.cov_init 449820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 449820143 ≤ n) (h2 : n < 450000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
