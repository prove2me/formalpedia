-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4836
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:53:53.132826+00:00
-- url     : https://prove2.me/submissions/649df727-2f1d-4e1e-b150-b96829b67203

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 869604316 ≤ n < 869784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 869605566 1250 869604316 869604341
    0xc050414040203041a070207081c020c0f13140a11030405060112020112060605180a080c0103020d18121206060804080306040f050a0204091a01051e0405030718 70
    0x145440d041410900080d00d08001941c040c0d81c0000100c1d041105000c890020615912035800090400820007501c0f107055210303040781841070b1105010b4202192045140203c0b01e500107020030f251030024001c100d00c10000240c2d2007408016075881500b21400360b81c04404d007007181d01503507203403024440b030443c0c0595490000c058814410840019400903040341900c00d580e1032904204401d10040f500080100c45079144942045400114550808003a01d25a15000320803151950080144400c4020034800c0100c01d41c8517110000b1554025401000c4004040c0404590700701c200d4a075408006080004941b014505015005c0a5501c01e0340706d0061180844140b00c441d140103130050103030102800280000400001142c016070300e9a10860030103250b40c0040c03083d4034004c4902c4000b504103110b0030340c5442c14910407429407009940c811150700f070161190390606c0400143c558240428680d0680314003020000400c035564204940001007203148a020281c0c0015603c03141592008100c0300c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 869606816 1250 869605566 869605577
    0xd0509030315060d0f020d020c19020a061103130608040308070305010b03040201110c03011a1008041e0503040f0305030418090b150d210f0f02030904181a09010c 71
    0x848080c120b10980e0303036154421195103440301c086aa082000f00078244c1c074910302034400604c801d550343c1c080d000b41c80c2d43d50308841960b0480c05d00b100c4a180441c00c46c0c070000e40c428180001400442c0c02406810110110f5100710307414407c000a8510452426420000100d022a8100020981c0c018412030380046640340070312455140c6460080c150001410033030500c001c0740d090882103807080081b180c14590040081c0304400542280384182d030380040f0064000c0341040703401031805000340000d038016640014007081300b6a51050501180b05489011243c50008000004211502e402444040e41c0034034080c1d55124507026a03001c24448810322081410b0034200c03d140452103074850254418060b5070b01300e51048010000078400204c00c04020b20003502e00c506a911040041700200e001c0582d521030902890000c40c007540c031a000034000c500140e004125100580c20141c010324000804400b024440f440e813592501c1d643e54a444110036003021a000300103082109006040f042895403c10703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 869608066 1250 869606816 869606821
    0x24c1b050703140d02031f05030a021f0c1502040503071202091f08010227040b0901030f0201022b030b040b0d03030b060409020f0315030610052101020f0d05090303 72
    0x9001402000009020703c510b491241110f61908400c0b903402e44041c0400311340c2ca00d010701d0030b1001050300c1e4000c2200c2c0b20100e100450f590600198480c00b8a40040034050b4489041d5854241040400c201c0d10801200c0c0401c0b900080000d21290388a1360780c20303009030f211400c0006140ca0700c80180d0154036183c24200c091f00140e104c002d02107811100003000d911500712986500040040c1300c0d03008803401d6100044000d0501019184a64008a1a88400d060720301060030401138070600340503d54008111401000015805101c04e00520f2041c0141c03500100c0c043c040c0403010280c500340c00607107040c1c1111079501680c94400d03089404401c8800704810140000400d4001112540c020240356032005001d03899910354081e2402042e60103810742d5603200340810048a03400680d4540c0085d0604000685289004074025114500c24491030a10358038240404c403505105086940e000c84803407110943c800c0080c001028010350019289a846002c42c208100f100c000402d0210f00d50010301c103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 869609316 1250 869608066 869608121
    0xb13110c0613080307050a090308130806060904170313080d0501080f0607053127020a080a020a0e04090b161e030c050f030f01170d024c 60
    0x51340d400c800d1501d0165200c0624080540741e030030154002800d0854041440c22880003c55001401d43d0461400e894964480b482070040840080e42c00400d43c4ca019181b25598003801c03405180e110f02c000c080c1c5840e401d10781c1c881c2c070040d501846040e00156100c0300140284030007000000e5423654568000c2056140011000b4801c2c010300104104020741c8201e0740b41c1c84805018000c0715900340c0000108081d984000f600402c03986c1c907250307800081c03101030104110522442902c40303c64594032440c01550320000032000a40c402251072040c421a030038001c01c00d48492140d0400548517030b40c507407400e0510400703210240b6440003655041100c0140301c40e4603003184214074881d00c41641404100e01da000e560582e00d600540c0d0742014080404020082c0000c203103402c543c12180c6100d140091001d4290b030268451001e22400380142e801a01c901800c0354540c005102158080e51048011051407281142c4800c0104065100701c1c807001d5568107100e00c0c6204005003041c0d581c070040082070200f41c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 869610566 1250 869609316 869609333
    0x11116150207170d080606041503050403050d0c020105180c0d02061b0f070f050607050c15160305070210020105011208030a06050a080a05010b010201110d0b13110c0613 74
    0x5400c4005114000d040999008108400207020001800a15402c140c03842580d03d4100080c15400603458170042800340c10a0011141903800c07014104514100f10b60064014100180c01101004020008800d03031101c0f40c81901110802c0390b0011500741441040d402e94103150500e0804550444c41012495035603101584807000e506441c0c1c80d40719140844140d44055020007800100c2c06803150018000318041070101c00e403402d03601c101c1007013521402400b02601603003c00810325031000d00217041c14540241d0001c2103100e402216803818490100402d12002011801c801240c004148481107180c001c485583d0700305913100800040d8076000e840704820680c1080a46010030020214003103889a82140c00580009000079225559403c4625a161101700f010b03541940b0341420040c50358418041c140d940c00c150650242040c2c07401013200b00030044000d056038066903804544141000134010302c45d9a1400005060b110b4400d00d0741c040c1400001007840309141d40d8199540002034050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 869611816 1250 869610566 869610569
    0x30c0303120b040b182706011707030c050409060b06041d0603030a053013020306090705030d12020c07030323030c030f0601030905070e011a0306130504030909090f02011116 76
    0x103a6211805c6e840340c0d100c1c18074140c5c10f2042d094a4100c0d14090311602540014100c0c103c1d0080c0316901d07291300d6260100b94940c45640802000e22100141c00c200c9450f207a0820031125002e40000142c540041c1c1c002222640107a001d44c000b070301181c144860a4820350f4296500607400c3d00030710b00e82141c0b110001c10503c030700001160b13507221500c220b420081050700d20300b5818500d549007048038182841c141e04071884a1100b01e1081c030942002030068440456003004892000e0700419903424032301002c0d5035044030035580c0480d56174288105166800c08100356001180030f81c0300c0186114034021010352032501440001c24509080091201c41c0003000300300d81c0c1c401038201080c00d140d220340340120064101e01c440640a84601080070030400e0310042c10038100c0d0b41c050300c070210300c4200103d496164082100d21a41c4060900c01034201e4049540005509c94440e00e403103100d090300c03281940c040740d0554406958000014030480c0171941c00c003505050314800d500040002c0082030385250003181c100d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 869613066 1250 869611816 869611849
    0x10509071208040b1b07090522051506031002130510080903040e0402040207020907022503080301050603042613300321091b030201090b03070207030c0303120b040b 72
    0x4004401c0e85c903060910306103030302180c02c0e1400300ea60746010700c0c0900340c00e0b80e000da1000f03000d11503005028451109000c000303600c070001d0700202c2c1c031a5112440203d00109125054040c000000f01c440f40144028000306407095031100c0303094102014031442c0c42117648643e050060283c14082c034280300005540c12035130200310490301c035030762403011501a0142c0040207400404070001e1102c106d40100f101703110240022010303003040e181e1100708054140d1f00d1001410b501020001402035042c1074004543c00360142c0c1410802d85c00c0b0403d07800400d824078000c0031840f100407410100c0502400b0000000b0580d9141a800040c000c1030780441c024403480329040442444005001050f0141424655040d107001001105445140c000341c0a0480010110751104001d0884051062000410019690103942c0d0350040c50078a07000546990010341903c0a51080700400800102a43d512101440c442c2d0341e8001186010030142061702d10070303080280324034101031100a0300d4448c2400b211603404d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 869614316 1250 869613066 869613089
    0xa0b0a11160203070b030103080a17010b0703030e030408070308071a01050a05010e12010609060e1e0601121503210816051c15030b0a110a0c210201050907120804 71
    0x6842c0300083c42c1400b02d0f840300d5100d0700040000014002d103080904040303a16500c2c0e104200714910118103418030240641c0041c0d07001402000b000c644258000300481554108803490305488001c0070f454551558000c6491400004e0100304015184100301e81c00700c0001900101c1d0f50524000540907120b9014050400980d1841001d10b42c1d1525034218980c91340200800c140758960b215800035200b180903d83c210718120f07020800c0e02311341011850690701c4010181030b00c0c0d00c510b4011180090a82603104809449030f2000004d21700514001e4000c5110b104640c40c0d0009a40400e0700b01d600c00810310041c0b040080401101c11643d10154240740340030314206a6402a0314401c0200a642030800f02c1c42c04d140407080c1c4400c0d1400814841580d004110b0500c00356908412a03094803041401e465421030144880b00ac040d004850b0110310707a02c240300d113800242440104041c00d41000a1880050791201d06000b240710301400028090b0452011039070342c1442940310034055100d5481039960010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 869615566 1250 869614316 869614357
    0xc0213232701140c0d0605030f0d051c111201080c0f150408010f270f110a030501020c07050a1a18030102040305030f07030e01031b082203020a0b0a11 66
    0x1c002c2d03101c81201c036540a0100c1840c1402c00420310590010104004080d18081d07000c101840d0010701c00111b085c1c510020103c2400c9070384121030f81d800c28500640c6c5c80d207121506060303041250007400c06041c01c410040d40c50700c5411a4044030b0842c1a80f02851030303003000c8401c41d4540c803441c02e0350016071025502d0045c40c0070030707403208100c0c2e01c12036110021035480d12851013168103072600800c00090303d00c0c990302008603c00002d1075a001182c4070044c4806c505818000000e031900d502c500c1c2c42a40204146195a9640c5641d826680f247d480e01500350080e180a004500e0f00610041c00b034045003813842e45041c04a401502c4522a00600100e00c005510303440c00d0558013501114050740d8030070103584c0c50300d00503000200c450700f1045044021509105224200754030900c110380342103034208006610380101507419201c0120152080da07280d00e0162010542a000f4400c0000e5079129500400050406060107002c03007001410200a0314202059820080d04413130030707950340c0b4041c521a040c022 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 869616816 1250 869615566 869615641
    0x2d3b130b270601090510060207090f0906050109050916060c060905071e080c09060a030209070c02061c05150a051012050c0c100b03030f0a0c021323 65
    0x544007020070906070540c111a400200e00480d81c42d0480f40984002d04c9103480319107191381421a10700400c4010791000700104510b8045400c03101104001400000b044403403a111181992002d1f000081503e465005018400c40c0800c00d140116802060580c101400d000c40105030704a0f80001030700d0980c8505190050000500c8854000c01540d0b42904001c0c0c4610415810200b4900c83e800c024007946190081600307000200e80d1060340c0c02841c211815065508018000001810203401c03c02548203102c0181ca41340010908101c08016054250b03c0c0741440c0c0e020b50300c00504500c003402c01940051020b40360700250b101915002c459000401c0b807210821500001150304040b56207041c9414491241d203003030014050031084400b41ea600062003804201920600145950954010000c9144e240344000151181d1100c41c0303031000d68050036070000b603481c0c4110420550b03419030720800c4040e004110070340f0000902e100c00303016540340744c0050600c8041c1251001c9070801000c0c0030f4458040f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 869618066 1250 869616816 869616841
    0xf1404120c051c020907020105070f11010b040c03021801020a0c0b1b0a15062c0703021315091d0a0c0c020402220902042d3b130b 57
    0x34060103000341c805400f85015070000c0202100041e402610020082a000c9106020382c601c0741c0010f88583c81e880030003400440300e00d02d101052165a55a51a00711003958880c0a2800030491698025803524040b0307450b8684d600340c2080f014190b6000c0003802c4001405610043c0454905003002521908640e07030200d00d804246840701018003e45030f1000c101701803c0b00782c401508845101700150350b01c900340d8003440e800d002c100203801442c484401180ca145510115481903003450098202503d142c0701e0790903100503070085100e08001e080102642c03540604400010000d11b8801610340f09a0341d00c10180b03c0000c0c02c0d04041548409002500d14010025a085960301510131540c43e6501a20070b1160850b5000d4407034800e072203002c002002004c90080d60199440700030302080c3c4082100e4880381c0707005840310324407031481c5056000980000b070030307950701d00c0207040035980f000350f444174581c046458001c02107805500c04141c2449008580e07082e800d0300c4181c0c03060080400f0b464103e5454072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 869619316 1250 869618066 869618069
    0x6130804030219180506030c2b0c080d03020304080706050a0603021c020406090203060f0d020f12160911030601081e1315050f1f0e010f0302010f1404120c 68
    0x1008200c540d180410400d01d040b10004581c5501440c0e0407004e2214120802d0703030f0701590100d505503c01001d04a192802240342004030301e01c55000200c481c00740c1c60b0b6020501007848199500f20802e4070400a1038018044000c84500602d002c501d140343c940d03540d001314000c40304007600403559000094500c915960102000d150010180d100d0040035802034078180311f940c4c904a00941c00c00c540040c2815107802501d005000003801160880e030080c040c42004050b82070b00340d0380706804010110807915600041c280c0b148110300603066503c2040d0300a164107585a10810600d0b1916285010559040080c0c83c0c0100c42403810542a40381c60494010006842401341182000e020600041e54088030003000c07554030030a0102c0d0f802584140c0070f412904216100c0d1a98542000041d20460101912087d0005090783c4230240c030b07848138a407140c108d03401d030080804810818010310640d07170080008a02c0b111207103400451420369040d01c07600d5001c0d600c140c80319107011801032020044046032000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 869620566 1250 869619316 869619319
    0x705040905040f14070506040b0d0605120c011808060403030e100f0606020c0109030b06010f0c0813050a15200c0d0b0106030e071508070e0918010501060f02061308040302 75
    0x2a0400f03082c2000b424804038001c491518201c513820040d00c00115003201140c030020056030906242a0400d4070f80d13400702d90318240c8c0c0c3d5a11800030407540e407912154040c221003400102403401e0b01c00c0c00585902c1c54403071210720b41e280364030041240020005046030710030390520340820840c1e00200b401c0e10b030818001c1c0c00e0781c0e01424848049007040c2650300c0745040702c2d4168212141c403500d0f04010744180080d80406005030030b54000081840d4020b02d0403030310a030b9851074040054500f603140d00449400445a4004440d0944000c11103450716440c800c000c1c000d1140080700c0f011f11000064100545072005d002c078244c120550b00f85005061104004001d009044515109042e00c2d0010641400b402a180801d203000c0f149030a6102c00202001070b540c0484c0d45a05402001d0001d80302d409006000340d003002000b41c41080c8580b10080e102d03000760142a60280100210b0420390f09552b4141c11010130009046013540da4241d0005075039400c40600a07441c00c0c0101c8a06040895218681001c0d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 869621816 1250 869620566 869620571
    0xc0e090702011407030b03030409020a02030f0c0f070b0c03030411011202040e090d0306051e06090a0306020904051620030d02030708150306070f0318120e01020c0306070f0807050409 80
    0x4103510360103403c0030081d01e14082c039512640d52022001c0d02159100c0032450340580c010300c0280450b4155038014201c07102c0c00d0040302d04102141061581c0c50340900105005038100502298240e2000c00041c00501700300000340341405d035152030807a80d034040204050440c80d00840002405c1c4d0203240400350825401e4019075446890301d40300b070200744044d990307418540b08402c0c40302e5125220380f207860146d1700d0060a5040b00b05041c19000c2d010754180303801981c4900108141000780da0751080040041d84510070258951074171008000807182c00402d2850f040400e00001d55903554408180c109210941c01041107101103401514514001c00507404070040c4000148400e89030044052031013001d07001c6400050301e215070300741600c8410685489003c10318024cc022440c5000e82c006c00f0700e12540d0540000c030210b00b515101a00455146402c01040c16850301c412156070610030407242c108160700401043c10010380007083d041140070590100403515002c580c0c40ca04c02c20444009048502d801d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 869623066 1250 869621816 869621821
    0x702060a090905150f1005031605041214010f061505183f10020906071a070e041a01030c0c052b020c09070e030a0803040c0806180c040c0e09 62
    0x50540c00d104ca094902c103e07042030784d00c4101d103841c065603500c83d5003660f07445086417991280c0200000004240c40300f400700500003c56007040d464501148540107107071046108080c040c0b01400c4494002c04604d5540c00c001081c0304443c0c42d4800d8000a0086180c816a154039045c6500e1010f0540c0030210b41c420440c010300014160002c4011b03003103840c608000044a000c205000c031042024a0003150789402041c1031842e541680d60280c0890940500100d02d01082c0c0c4d40c0c1d40d18060074440c0d41400c0046400d00744181d150b440741c040741ca00401901c08002810328071509010182c0c4200d42241095141c12910036814450050f410a0961080480c0c0070845a07055410401510b00d0900001e0110185005210b0388001200c080380e143c0036015054a8503208000c8a0303181c400680150940301e0600007000090340c0350019407146000c1c1c0c1d5100720503814890454180080a03000349224600c85050048251f004202071503280c4048500180c0c142500d8400c0d00d410404000c9254019503043c01c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 869624316 1250 869623066 869623081
    0x503030601030c020319030c0e04140702011b1d180c07020405060109030b0412090807060207080c010201050f01061d060d0911010801060c0f080c010903021e01050c0702060a090905 79
    0x1460203600c00340c909204240740740b441240d5a01401440d010700202190592560744e00a9000720201406450504403000308e4001141c10f607414180c00301c24510b140000c120403280d0a22480c0d4001d4400940640b5000d01110b00400b5140b200070410500c02e902031503040766a8410865071483d4102001010562030802142080b6030000042680520b0810300020b01c9903108011007000e403503001c030020f0301c191a5503e8017204c0700200340201c801c1c0094104045003500d810881ca50040003d03500034240c15060144050420700100e4049040da0704003030074858030408262840341540c00c0b40c50f02d9000c00c90703045048070340f000d10310b58403e03000710000400035030740c0c001340e0054000a4015080300d8190700c1e1a000445d5031680c00d00c101e1000410801030400000d00400d15800c82500a600c5103003000921541315003120003411040700568801c4c1b11640601d0b64440c1346480b80d40790311008000d40c1c41d10400700d02c07403441a6603000b4032508000030300c0c0c2c503100e00403068a006881203200c2001140390020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 869625566 1250 869624316 869624323
    0x2d071b03060b0103020304020d06180501020c0717060c0a05030901090b0f040b181b04240e01060f120c1205010f081911042309010621031e0e060705 65
    0x603a01d103030405041d00c455501a008403400703030303a014002c04507c81640e2142c50040145000b034000165006820300080f400074005403050103442405010503c0c5030880b031815039a444603001d030664010300d040001e8050040f0548004130200e06141d039503503842c00c110b82d006004141c402403034542e2120a2084508100090520503072003000c0d10765107a19038040c40c034000000c07540310005640c0940740d41d40481101203490148c0030000380c0003041d41001407900c400f048a40710079401a10780380300300400600b48008151401040d103030414640d1079625071401015041c05803200c9080759101c0d280102014490300c401d0300703645803e0404100550319001ca000c2e4811851140d85100c0c40741412080e41180001d0101c101c080e0301c1082075840804140510001e800e4079824940070300314441000d15034030701e5019540e1080301408000a40780d82050f40f8103460314601000462390140440350b040019810076a080601c1d500b0b51103880d01d0100303030142115181c40c2c0381c08041d040f12000c14200104080003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 869626816 1250 869625566 869625569
    0x80d060603050a0f1b120b0406140910140904020a1502010b1201020406050301090e030f03040b0906010f080c010c2303041805130f0f0b070203120c2d071b 68
    0x801800103044c2508000309071041034144500080c1900200740d40309001e803c0c2000924050400441d00003140c00000b0222550399001c1d4049017400d2000040514081c00c5250303000b02c0d4004081c0782c0904180c105100c05400c0e5103010300514a260114081d0342c0c95581d0480140070304900c101d07480072180c000a010305000c40c211806868414078184241406009a030b09070f95503542c03043d046a2070700c0c1c00795028041c00c114000d01070000b00700c0c0441110910000f540304502800c4e9109040c14100c84c15403810405a00c50080a5039442043c015400d010441e000c642e0003d20b00b40b0201601410b200000300c95203280c00da129010301c40f5068900c04080086e10842c2c2e000540c4082883c10300781208103440084450861441e0300b280048009540c0440201400b401603000c04d000141c960344101544d2020f07609100507174001f10b8190030308112003150f550f1081100040c1420710141001c101c50300d00fa00295282d0011001680c0ca404444100542d402117412290083d03510100442e13080054285 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 869628066 1250 869626816 869626831
    0x312090f12173112020a1a010605040b09010e120c280506070804150c02042a0e0d0f032006070c0f0302031611100813030309080d06060305 61
    0x2110b25681000032500c0c205118502044000c0c0700315400f4100c60000003031a165290f0503509004124000c2030403880c0c110001c2c00d20381c0003070449610504100e608400401c21b810325421416005012060b0302c601640d084901103078402d0713111401000182c40c121611403505400c46540c404950b41403030005a0083e80f50300a440e43c2085c00350034100c256106172001d075103138010f164410041200341440d900802605004840b85414141c903401c103400311003082e140d4000041c0800c2494419481c040c070804100032580f03e4909800c0d0808809107090802c0040c88a013400200c41c800c08050322440c0c008904698004a480c2c01170780c02d85409400346075a41c020455240c42c210301c82980403c0040d6650258040f030b103668400c02d8455441d0500d40003511811005c40c0001e0103410b0000708400c14801407680b007a143d8144084816061149a500f0071414074108660b1205028806000b00c0740c410400703406280208030142c0900302502030744502841004540d103001000140d5560650015014020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 869629316 1250 869628066 869628077
    0xd081f090c050913020a030f06120b040503040306050a0903030b0d0c030b0c1b01021305033016121103070804030f020103060506030403030603050c0a05130e0c0d050708150906040312090f12 83
    0x89200501c3c00309c0780e040c0503048000c01b105941c44041081403191a90040c4103504492034152290b40d0002030714070640c2c610501d1a1a0b100d20820540c04d4054950301540070380714141c525449840d660031056203031001070b090414800106e401507841d1011510010241000c10540c0309524003241d000350701c0030036030700304902040c1001302e01c616012030040c0403120317055000010030a070351003164040c2d0300b040b01c3c0c0070501d141049038594940c0342e0350a039017545014400f10503003280c4443c80a42041440c81c05071070715400c00c100e43d40c0014403510907201a2a04080175060008240c070050b401003146400c525806100802008105a410f40103c019603200d10203845009046c2e0043c03102804284c0103403130f80070a00c0c5a8001c100a01e940c80f4103c41540d40c0111602c0d0306545e408590748001c610070a0300c0e640c03c4003e041c04250300070090010001c0c0102941e10b0a880e041c0d00c040d4454134050801010080101b141900906039500a5400c0c42c0e001041140104c96a140010443c1101c4044401069 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 869630566 1250 869629316 869629331
    0x3081c020405010203181c12090803250606030c1e050103020f030c03060f150d140108071802070204060e0f07110c010c0302070b0c0d081f090c050913020a03 69
    0x1464001e0380e040390010780055040ca924010b0300e44034a82c225000d00d410108104000c44680040201088018003802100342c40c900a20740040411401e0303080103489a1041154032181c3c0304e980100d8444080c660345184007a0f803945813200190181d0752024100c02c40c0300e030000c60150504a500704161550003030440c086983c0380d00540c10ba01821107140014101880090401c140071802154010320041c00c1c114800a0000044c018000161140111407008a017525452000d8031440768500700040300c5241c190301d40b0041c40c0d95605a4003440000b2400001c9050400c0520b40544143d158000d00030b0040d182c407030000d5840c101007240c42104114040002c220b5143c000d441220b4442d203403002030191401c04000554048045000c11421885003140000d02140300201030080d43c0c0d8044060b04110840c0c407001001010b0180c2000c90b401c1158908442c41c280002846040301c4510601080f010002202500c141c0900480380b5040180701030122100b0005a00402c0901c880351804c20035603 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 869631816 1250 869630566 869630617
    0x1106070203191d040e0c0301110d0627021309020a120b04020a0c080f0403050a050a0303050c030f0420041d07060509030309092d010510030c051903150308 68
    0x80780b001c460825843e01c1104000c005080a8000c0b20140030b540302120380341d04401c2c000c6400c581805110880f4180c011a0004a107841c0340a644000c191846000b00d416036500030031403006003107110400180b40e00041d0340c1d200c680404c030514024888050110340719080b450010b07103c0d5084621110f0107929040c170f60325640c50076109a0300d5000b202d0359081400051540ea8910580c0030198410300c01005020000008000304103141b255441039001d400c02409621b00982aa8409070060440c050b080c0204a9442d0b015040301d40c1c050f800c00808070100400c806001040038810081c1504030f07092528003905286000307508204451500704503921a0703500d40d811261800b40320502c40e8503400420162009181000050f40c0000c01542400c0030030000d2449616581c510b203036010f12184103400104030b0303454210092034090101703080521030000e01010040040c80703220342c0b60784105906002d48051038480d501c0218441e840c0007038007000b56140d044c83c06190300200d031518800c180c0140c290720507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 869633066 1250 869631816 869631827
    0x3061a031b030c03060d05070f090f14091c0905120a030e010801080a020411130f0e010e161b080a020c040f0b01021207030c0b0f0f060409170703110607020319 70
    0x10314026820641503440d1703c800c10a500d149640152103c1c802c407403000ca403aa05240034240200001d0384002004210000c07441c05a41300c404c1c00480b184000e104001c80094003186a41455204002c440c3c1500640e4506030b8450b81d040d04419041001042102d040c03060000718100a80c0c02611a4445105084d0045901c100c0034018070102d40c00c04280c21005007059005910650007010406081048203c000560440344d0350180c0a0191490020001e8240e030800c00e03400350421500d003000901c0c0180f20401c484201e10f500a0402c10961425400c601d00f68101c50900ca03480500d090b9a403050000007580c07081c60452581c45640f03003148014410030903105025880806070043c3c2040e12aa11265240e0b812150042c2d05228012003a0000101201501485a00e001525820604185500000e212001040309014520b082038080101341d20b4a05609501c401c054001d0350342e04103140031641e48003e506d102945101e05805d0007016074000c80a031110481d0180c1c800549181500221103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 869634316 1250 869633066 869633071
    0x110a020a0b1c0f091203020906070f1401050403090801060f0531020a0503100605070213111204050601030317150105031b03070815030c0f0409020103061a031b03 71
    0x40c0105420020480e020703603040074202400450a4600c00706842009030001c0ea2000c2e84000c0000303603180210b0080200fa00c04070744400f90685000c50070b03c0441004520703240b040c0c61001e020909407900100410103810728103181440781030002d00c06030070b051030041c001d4034543c000c031040c81d403c0c00c402241503060408000304480006029800d0300d07031009040000401488540301030010349100300202c90352103000030f115244e40c40d500e5a5607840c1020403a0287d421507000141003040800c400c1002d42c7d100d00c0242d000050944002800b5007004000040c64401c0069080591901408010900c0004074100d030480780a40c0380d104403000107070f401500d070b508215401c038504c4205540296240d4403c001444d445221118052001158500241c0054000b140d44000082e619402c0001000c220200d2850b00c11098000740f440c0e01010340000c5171050320f8800d85000c0e030b907605a54415a8401e4002000800070710144051258003000d030084079600880e103015186500f4050308201a0860b4100c91 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 869635566 1250 869634316 869634319
    0xa0e0309030c040b190f0f05060a021519060305010608010f02091c020a051f02011d1504020a030c03050d02061302013e0109020102010f0b0108010e13060f0c110a02 72
    0x151000b007102044001c1c01c850140130342240074000038a15202c8035140b000003070802d0202d0416902c0c41c010500342e40807416000716000b60b00500c002c21013940c001842c090351070060071891503e6030303445142c0c061b0a00000c81c44241c03e4100728002080c46019444942a6908080207002008d52800040309038400c5e41c80007034200c903208101e020707003520503901900c04900c01400b841619643c0c1c0001008188820186485804c02d5412882c10f26024842d0300745803050b078281000101e030380160031600c6682c0d400c0350b10507a0390300d00c002501310b59a406800c405164032030f44000505031242441d0307650b4400380c40620054841e4801141410030601520420a0741c16901d00d4226040c0e43c02d890409807612200650ba41c901c1c40d40305103c03001c1c400d8240d2240072410000a80900031703000090130358217a00c540c00320701454409052902e0743c0c80003580f415123a40d07003404015a221000c03003000044145002610281c5045010f9856800c0c035001034044003843d82c0d803a8030a0703801011160b03d5041004e4000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 869636816 1250 869635566 869635573
    0x12060a0302060f0a0c0203061005120706022a15030106021e070510030e01090302010c0929031806040510050f09071517040f021813081c020a080a0e030903 68
    0x40f00b880c28040240180516445c01c080400020b5000c00e00c0d040056440061503040b0350300070b0080341403c41d120007950004100810b80503290280103034851101400800c1070842240c0c040c421200111140c0720403050260140d25036511054865055400030700490005000e8072880010040e201d4041305035016148029100151808042029450710808400117048d20380502004002c404c0c401c115002d40290000b08034904038101c010711004a035004a6141402100e91a1003510303505a8110bc5076205503407543d5a44441e841521b80e94402d144c800e030340e8400c4404000070000c010070003080341850a1814016600c81c441c41c0c1c0d010b50000c076100b0140303070b224403030030071005101c4040c04038804054284001031500f20500c1800342c1380204da041d44d854010491080c04c50824403100c4031b0fa80200c405407001800c203203003070965a00390303218050503030040407030f028001c411070120400f00c011746488119910769140c0c401810b43c0400702c814100c07940c5084541121103102104840904400a018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 869638066 1250 869636816 869636827
    0x70302120a30150e07020a0308040210050f03041a060402070f0f24051602060405070b0a0315141809100213090203010e0412090303050412030201110a0512060a030206 73
    0x142401220210121040003060403454203480d00306201d1410541002044011200d0611304942c0e8080d0010f04141c1c1154403104140c1c02082d40205001d40155048401c1c072540c03608010216181d000d0700070803d103103030400018407017000103820340d10341010000c13501002d02d07966030b2007004124000c40301c002e0a44207003025840009841c14205490082c07243d41d5020100d600c0ad0380030003d9600d542c100d491500e44c1c5030306024504020081320603004140d48001c10491400c0e81c1c2d5980c484149100382c4a00800c04101c032040c843c0280c001111a06100815407a06907542503140c04605c402c54000d401000e0703540729240d03088a100c1c0d24a1040c0e0b0f2100083c0030801c0700d0301507030000703500c00d40b0402e2801ca1f4919010580300201d000842c000c0035140840382103070525003810781c550742d007e07881c02003844101540ac01c0007a400405070740c00c942e42110003454513000740c10309a000d40390000310841c000ca0002403052115801c1806800342d258900010f440032303034486046c07080c0e0800074000654044014001d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 869639316 1250 869638066 869638097
    0x12050906060112180818090f0c04060507080c06040605042307050607020609040c02010501030b16080103080703020102070512030a110414040216060507120c0e010e1c0209040503070302120a 83
    0x8111140082e4100c0704000d00c280c0b01c0005c1508460011500c041030342611040c2c07441e0a5484980100c2003440044140c105820104154811840760206011010500e20184039440e000d4070348041651082d07600a2810340b4240000308000c035003c8a15810140201d946105c3c00440c03103a6038000140207010003030510041001c1900242e00c01c0768440703410015105503448a01a001d2148841d40000c50701d94110f242400100c900104a00000050502e07003c0040f0b902019a6045a410a40180d500c90403800c1c01c034060310610a01030700ba44101c0386244030803a050001580f040e1000001006464000110555103104521030b0646903030000c40c1d80e424610f4664002e000d8501e600039000c0b600e404d541d03160029640201c4a80c3c0214030f4450b03005075191107500414110000c0c2d440d0403140c10790404006800429403a60950203095100c40d0750304c42c0d00402000d0158289c008009522503d024a442c0b90740b9888003100710b006001d0707061010704010985054400c00400b0303441ea21500b04a0780f4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 869640566 1250 869639316 869639321
    0x90201080703051005040e15130302060c03100504090f062304021314090105090705090603210d0e0c040605040b030304030f0501110a2304051806030a1212050906060112 74
    0x2021314002100c0e540c0000740d01e40e10361090000d07000403203000d0207018000300b45c40030036140e004101d000c62000c0f400d1580002a4082212a4070000d000d20554580e150082503240c81411034100347c4d00185003c02c040103111a410116005900c038590620045801200381c16000500e014106200d900b401c022800502d02101c2c1f01001d00d4000714000341c3d0a001c803030760144000c41620000c1c9140d54800038410382030000d00c1003401500f8141d400b8040382c100a804281d403181c0c240b90000032551000c2440318034004040c1101c0502d425183c041c402c100300c01000c1926801072410f010300c0f5900d848000500e41c2400d014240a5101c010050350420b880c54031142c440781d80301107007210306550703e036092210604d801010b041d48548568507109044640c091000300844009031581c8001014001001955502d80b40d003210352602c0c4000c1d620588500303010901d40800070034010400076030344e010208201d80c04001c8548004611030180000c0c2c94001c022900c0760340039240d00d40040c0c449801d40c4280644d03074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 869641816 1250 869640566 869640571
    0xc0302040f1202030307021f0e0103060b0a030518100b0a050f030a120203071a01090c03060b0306041512030e3303091c031d03030c04030b0c070b04050703031209020108070305 77
    0x11381541e161468603030018a02094080c00c9010904400c48122070702c95000105a00300e000a007000c0141070f052050030640b030b000b11164181095141c500242125540c41e640c0960954480f084a249001440e01e02001d400303241c00f00b50049403614800103036440c00c814000107001001c2c000c1c268590064450024003c070306100300065200800000380050320ba1070580300b20b554400c800502650518085c00165100500600c08160500f1b50a1000004403821640c1202c03048400182d6010070340c680065443d01a800100a081540101c0050542004042e0898141159402001c01070f120781304440c649041e410301102111490303c00c11903415071000350f0b04a4a01c2007294420210340030043c280401890b00c25000176182c42000e0b440f400306003d2400503d081d100503500f51700d007102d06178616014601c4003405107140000401c91140400084854440d04601c05120b1460f090401aa5070580c6100031400140c54200e0f9a00d583c0103446040002c580c169602412600d40c61821070251802 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 869643066 1250 869641816 869641819
    0xb03010e0102161b080f010902090901020909070807090b120108010c0f0f0c060b06030a0902011d090a11090a081b0a12300207030209130b04140c0d0f060c0302040f1202 74
    0x11020882c021704101246032007140e00c0010a023080b50307106002142c0e4018011129aa00500c2404540d6a074002202c1d07222885103044401035445c02d1045174a54040c1d032220251000010303014007a900380c880c085040e1600d10b4000d00800c41c400c4800c80d00720100800c1c190000d200d5803400403542d44181c0740c00c08118000d110124030b002c01980094407543c015130384000660341c0c0342c08100442d40c0214040e15080c201c200440f20f000d0320350340805c4070a1001445030b8005643e0324160070841d50742c2e4080e00d04203400509034550080c2c6500a5641d58081480c001c150419002c1c620b000310710b402108041a683c40d0200032503c5007107a0303908102d51034548ca83c680501148092504c642481c2010310801030403a900800c0e05c146140184107401c5006803d0000744c1030b480c00868085040c901c94190401d5124000e5034a260000e40305c9030403d0b561200440c1d04c100c064030381d134061091409001c00d050f401241c08000000781402d045d412485184a8031035030306c03403061081001c03a00e2401076580340f500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 869644316 1250 869643066 869643113
    0x6091a070b071206050301020f0a26070206040507150f03020702011112070209010b04080303220c0b0406030c0c02131509020721080609040f02030a0b0a0b03010e010216 74
    0x4941d0358440452040718410001600900111508411030103003400408050b002146004000e02d1300249510808001e0400c0c0b214881a4002e04c2018107490b41c41c0b00400d4884400c01e04103000c0c0203440314001e4800361201d100d034900c0030509908801080703403012241e44489808414000f029006908021000d07810702c400c00c920031100c4402441100000001844005d5603174041e0301c10090080c030182c2120301445024041440745c044000b040301d402024400245401c95000f40018103035004014005010055003030000420900c82e0010300f00340d0baa191010b01215015035011034800000c00f202030340c01801844400202d00890f4001e500a02c90030040d21030194850f030901d4142da00160040b0b03980281d034441e58004100c02d005800e610701071464112370794104200000e01c04074001e800645980d80f0b10004070110360f800c1103540d02c40d90780300c210602c80d45859150b800c010306030b11b06418041d500308000940800c50610031100b0b070790503901d45100201150344402001103114030400403480b4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 869645566 1250 869644316 869644327
    0x50612011427060709180905060105041503170d06061704030f020304092c070b0405060906090301090c0807060f0c1203111801120e0c0f041104030f050c0a06091a 71
    0xa0040c000f46100e010981c686509803480d103103096801c000d60b002080c02983ca800050383c0010f42c04106507046403011a00030039500c449500181008180382d10040050405180b880b140c59a994007420405001000c00c00031036a551509407844070607101100c020702024400100001c3c0100d92800c8281ba943c03044074105a1203020520890f0200188042000e04002c006942060345000310070005902602a02042d46445035042080c003d038020580b01d00c0300071840521079110b0340141d843d020300040081c80a0040c42c14034008000c2d45020b03003141e9014568001c0b0700c00380651a6951101510790341c200342000103894518801a0f060300e050101511603500030341c4513114101900c454085c0c08591181081c165001514000030841e810030705030b040c1001840d4407440824803100e001c00c19242108a0b0a1001c0014001c18040040003641d12001c02e002c014001190740c0c2c403050790701c0340040341c00702c1c03560300d08000d20101c2d544900400119581e809224078203407041401050303c0c2c40c00c00715080c017 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 869646816 1250 869645566 869645641
    0x3070b0411030a081e0906031602150f0402040506031b0127031203061415030a0f0608031b0307121110050c0c01051506180609130506120114 62
    0x568900819202c04c070300810307040700200c1c0b003e514100410070f502c8a01d00c0c00e405140461000d0000801d54074103150320032030031101d6138024401d507003410a1442020000740b501440794620f180c000d4500303a00861602000498500303000401e440c08609054250503a90220001160002c7c0342c000b5003041055030300644032805090465000285101e1000841c2c0c0d5106628020704889403903026044206102040034080c4e01c031644412500f0268810b03680c0d59580c0c065020700541f000000480c1c2c0a0302c1c00d4000150244040003815440141c614610006003103890165640c2c0221000035122007045941c41901e5406140c1c80d00c1010309480176942015954514841194821211030303a00910000e24014484801e2080e40c1e4080070340c100f54076400c080d4001180d0103000d0401c01e0340090503090700004031565140305958403401c3c01004c4802402080072040d0142400b5541da90060a5034600400140306c18000c10074902080a030703442070b1b5562080100c1c500c0800c5040701d0f581110010b407a2101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 869648066 1250 869646816 869646823
    0x4051908010903050712091a071b0b0a02010605030a172817070203120705030c09040f0b090112080a030b010c05100501080708010c050313080903030c0622020303070b041103 76
    0x210b500030b454454845a05081080e5a50380130820030007000341e049800d10104040d50241c8280301c00400b20152144028a803603100004d031407421403003044031580001480450000101000c0419500a10106d60341d02c05065581a009200900300d8040c009448103c0c45002c3c060310509518132840d100000c03d40c02049008031010380740d0400150000750000c48102e0f005136054002409200640c034147c6015000e8103031400c060301d01c800700080000031034641107c46050b13070009072004004100c03024040d00c200c801800e5803985140100c562a00010b01103503801e40e40c00b082d070340040d2000e151103400c480071070041144040d8103050218010003200400d20810044441c4ca00003040000c0c41d504240c05c1c1442c0082c240d0011f20785a0500030740071140c59208081c0c98008001302d80140c4000c01c00c6c0f822506074020b4400c095014823010505d00081d0b48005802e80c0110065130038400300c4e401c408400000c03c050400f000c2c1d090b0b0310801440b0009401d055106910500039480c0418404201d00020304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 869649316 1250 869648066 869648081
    0x703150204080d0903030e09100f080618012d0204170604150b0d02040b1302030f07110a030507150e0d170f0f18070915090e0c03030405190801 63
    0x8016408503041c0410035080212012070482810280c100034610394004103852202c0d03070040d0040000350003007011011b84104404c081c003150003074400741035240d0118650300c0300f0496011b00341016100c0004031000040c4a0f4004000c0701040130383c008070f009840e01c960490000030780c0004035420440014201c41d41d21600034100c0403400508000d06150030b008070002100040301ca400c038a03000c052708043d95607004a407031240c0d0507940410140b8411001500c840c0c544401511040d000100f08203c0421412a481c030540e02030701c4408803081a013550a65806c0011401404110100324000c0030903803a0f4000d140c0c24405090204030b5641210503207040c4404000b128020480d180002c0d01100482c900c010350003c814060004586016020f031002c0d044023501e152001d0180c083c0558034040240325a0004d000c1140003400980351030070542c2d40c1e40c1d100303100b114540c40c41e15281c0801c00e0000725542614080050042d41801d0821080045c0b4a4803080103040300c41c1c9480c0002181134080c0034042 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 869650566 1250 869649316 869649353
    0x219110301050408040602060709140d020f040c050a0207060503060603070e0402073c050601030204180606061706120706030f0b0d0c140d05060103080d3b030421050703 74
    0x544440c90840041e08c0d11001400c1030040c0070015a050149080c0001c41d0502600c084400c02009000c03400400e00c400c0d2061803482c1c00078180b0303100100041d0401d0040107040703e07950072105007903501c610071200350009403086030b80018208040b0352000e200c1c400321000918024801490710340c80ea030720102d1600d45404842d491070941c4400740145400700e007407844100d80104114540144036900c46441d90b40500000b8800c1e6074681001078000d550540b201d210640c48401006130a843d640050009803002110030104e00b2600c0c0010940d00300101f405d2080401c250062581070705200c420b901501080549001495580f0858215640c41c0a41c84011601401250303034081d0820520b03000c0c019904d084103000c0c0c00c60b268100005000010807a0450b500040c203143c40d015030580c1c15003e014170400d000c103072607548007440088582c1d02e036450b508044003400f45440a003010320700c0c075201e00582c41004203008080c6070440f0404181407035040d080340b140c010b0380c000a03140d03035507202c805c0344410300d24 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 869651816 1250 869650566 869650583
    0x613050303070e1f231e18180604050601170a1d03040f051e130c050f120a05060f1c1401020f040906080105040803011e0b04080a200102191103010504 66
    0xf40800e402c5055025404050400f0b061906c1040712a8003980080006002000300000412801c544880b01c0740e10040740e4000d064050101d65800d00c7c00c5649030a80380f4910542c90440401c0080d80944a01200c02500110840c0345684ac80481c2c4028400341c40000b40c50446265084508501400144080d20f200c508030302016041409004c00c078a520910400b0002d4402d030a400070340c1d41d00404002141240d80c002c03403010061841210301e070081a0f107042a1010208413420f02d8a004403046100e10300e42c001c01c116503903903401080070505250004a03084000c0a02d8202c9040d140c1e4010270b1007900400f481264000ca0159203800c84e0320601d805040743e14003050920543c01140140c0006140b103000a00c158246511403891134441846100d4844034014100c096481d401180070340101444050711703031a2039490f58055241d404102040320b1880f80b4001c0440b400c0d00c5d01250fa980007506038020208012000e0410740f0842c0346800c182ca140000d40260300a6075402d0050740e00c100d104410a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 869653066 1250 869651816 869651837
    0xc1f0305011a120c040902070807060b09010b19020319030b010f05030405060601050304020f09010305070f1205100c11010c050a120e060a02090f040504140613050303070e1f 76
    0x80840300c040c0c100d40041142c800146510280310010780b841100310480076000b6448026180a1510583c0d200c1112140046400300a00140c074000d441c41502410303050115204880822000407400d025010003180140040880401f07a01e0321038180344400c1c0111f918040e0b10715800500c186c10890980c0010b0b45a4400c540c2c42d59100c01081c205565a00704507003103081c165544d544505008042134104100400001d017590b848011241c02500041d0001404d0b50b1039007002621800d15000d04c190a00081d2030010f00c01c540d503000510525000005803803401c1e01c514220300500b910200000420103c240315040040d0f00703120b5501d050340951206981c4c2d003000301d00500040300380800c400250345041c0c00c1100c19070300490703c16030162100030016622452900090380788190514202d0f000b0f890507040004004400401000c1204644102c4186581c1d01032811207020090000410310f42003480071940d954042c2e002c844402e91300402c1343e0741c50401c6004190000e014064400c00069a4000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 869654316 1250 869653066 869653129
    0x5090f070e07050412080f0309011406030f03071502091201020901030c05032205010e1b040e0313031407030f080a030605150901080408040f080706090e0103230c 71
    0xd0000030400d04601c06001d15100001a01d140264400e0310944000e072610301003040005030850f040c0a00403500c13143c4905141d81c0e0079000b40301016100d01c00011200c042511454001214010180150000d518199444c2d490141401c03505c018084ca083d000d0188000c00d5981014401120302241c00040c1c440c1034100c001015100c061082ca820310038100140407110b490340b4072451003440d85625000400031140380c114018641036000318560300a0340b040184814050b200891965421141030012044100d100342e00e0303209442002d030030b4460328041000014600004821003489410a840c000c0e55a0344540c0490b07464610126501d00d000140740200381d40500c29070f0040c0005039a8040341410760340c0b10b81124850368003064144001c03440090100f02c1000115800350001c1c4c0c40d02078203c4e039a4000039582d41e1650181c50041602c3c44808580102c00b0200c4504885d00300c0e0000300d418403442d00b40e242c0004042d5203000c1c0b40c0180c0d6aa103e02d034480c0a0101c203100049a0154405180b100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 869655566 1250 869654316 869654323
    0x8180604080f1504021813080a11070905010f1707050d030314090a030504092c060712110306040c110105040c150305040f020103050709270c05070c14010207030605090f 74
    0x72040d95608611a0074000940c03517104190412100c50803a03840340e40c85d0381000c00118801f846000700000c0001450742c403100e0303101a040190310a2503080b00d003c01d8407002d0070404e848003401004c44c5646106010485402c480750208a0b1501c0076081c1d916007512000480c10082801c0c01c180d0200e13403100310920f00b1084e03000840d40d10650440140200b000c0300d83d00100980b046108004e2035580b10f1030821811010303280041282281d01c0c1c800c0001414102030300b51500701c02c0f15180c0101c6c5102104850707416450084d6100c2021500340c1c1c1d031440d07490f0b1301040010715075030700e850b0200913000c1e8410740010400d20525020354001d8803141840f52900c1c20400035114510b29074810141040280000501442c0309140455824240840e090b0340384c00c4100c3d95401560710400b035180c820805801c04404050f1468001b1005103070510803039072041c030140c0d0540300b4100002c1c10340600500070058040c0c43c11040030030810510507281241e030f0380c0d00c43e40d09032402034819401c1c54002c44140c41d075001042 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 869656816 1250 869655566 869655583
    0x8190f031e090e13050c090a0f06080f010e031305061e0d0603062f0919060c0201020115080c040509210d05061c080319020a170601080606040308180604080f 69
    0xb04030445198141da54640f06c03200341024500401d10100410a454a0703500075840402c4485000c2210a03038411030160780d641103c041c03aa8651902c0c40f41840490b010049484400086205500884c030708001c0c000c030360744100c0d4a44e80000f141d000d803d400c84032050003000e01102d04580840c4086c00d5007007010881c0c003442000644000720a1241d0281014a44600900010001d089441e0812040404c02080b00100404c90208103030b8404a95142c000c4000c840680c005e034000c00802d070350070203690341070368040c00707080740d1a40504a003206600d4141c002d03503403048216081c1c5004a0066000a0a0700c0c10040c5d500b00f031450102e1045942c281c81d1180c554043c0089a0b03150804094070684a003071524814090a402c80002c0096060314078841081600da40d140c1d01156604407505000340f080c41d00c08010303101c08889001142c0b4941c0704140740c0d40a40d8004041510b13281c40c65880e000580d0181d11214182c406100b020071082e44c510025000420200300503044c0c940c0c400303020740c2c20724002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 869658066 1250 869656816 869656831
    0x36060c010903080106050a0f0e030304030204020415080a02030601051204033024031211030d060518010e1603062408091c03050603010f0603060209010908190f031e090e 74
    0xc2c821100e074998070401c0b6400115083c2000356000041c9e5000c03074214419a04040d400600015000032628240d1948084c128450ba0710607225840c0d40001d10182c1c8010740303490707000900500c5a80382d000c003024041608580b090034003040d40c00c807104040c03042d50020010031080300c0d40400c050100c07038014090003008214401e5158040c10168420101c1d2100f503001c00781c142008a076400c52100c0c00350f03000912070050682286e440380707060b14628024007450700409010312a0840090400302e921100c06060760a100d59030070307841e661045000710030074400b90b0450801d612200d0006422a002c90040060500c5298901c04403d40b40c0002e044890060468002c540c000c002c0d20b40e10610643e80c03a400340c40d0340d140109d0192540f40000303024282080c1c07140c807a2450180008100b2045900500f000760081e202d1000c055030340c0040580300c401c0205542510907030540d070b50300045c07001c00205a05510030f007448202c0c40c4600b5241c007031641d242c6003048003151018500744601c00c914400603070f00848 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 869659316 1250 869658066 869658077
    0x901021509060708100e090102032706010605180d080903070e0408040605071103031603020607090311060d110c010903140c100e0106271136060c010903080106 70
    0x6001c44955600c0000030001400c2020b4480031420842d2080c0240d80100590fa034180c885040105151b4000e6105481150b000c6c5448803826a030200041c0c100000501103102524060f803a04800390b030b0303da100c400c40c0e1821310840c1e600c006a0b0b90758000800f0110b8000d00102d9200d0050f40281032410195401081502c0d036030400304400075900c0d0084400b44c5400703251043c1c4a41c0c0741d25104840908041030242d1500000c200f008001c598400382c030300c6442c020707401c40300d00340c84d8101c040d07841444502000d004001d840c804110700b070a00ca002013401020f0682c000503906501d501c964103e40003c600f20b803640e511070801034240340d0300464800342c00c500c0303142d6145003c0da82202d05a4070403038050060101a00c80307a000c00454429800a4001d050a6680c106075895480260b454450038803480241030780307061000c2c031019412a040d2201c000c10031000c0c1d94010791281e00160060450085024940041c024907085906c80380041c0c11070114040c00400c40d2500e616018007001b0058009008204 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 869660566 1250 869659316 869659321
    0x1809140c060f07030e330c07030f02060904060f14100e010e01090312030c120612141617010c0305090c150d0608030909010603022d0d05040809010215 66
    0x81c0e03048111604112101d100d559680b0003403030306454031400500c00c940d0000101c0c18120f040d18110258400410940080104c0240711115444075405044d81510850b4002c503801c1c00010307c042c1251602e0343c0004c2180c1d01300900140003400b92145600310407060000044d08000c0030200b001c0b40d060000c011113446400d000036440081c0101150f0712028100701058000344172590103039540c41d002c0d40d0800c5112541c81d401000140c042e0005400740d0000840c80b800c030540c95451441602c05403103007040ca01d030200340207488000c12580090260302c6c2d2401954112480180310f146008020100c100313501c80301c04c03100c000c2c0034216106080e1050a00d4100030800c4400c010100f160100c440041303851a8a8170711540f6600424022001d9180c4110715154021442240020103440540411940300c03411382e895030400c030168005c810b104a4043c070301414107080300b8100c10751504136580c07007c019414583c80138001b600740c40064606803180c180c0020540c99659040c4400c080f410144503c62683d030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 869661816 1250 869660566 869660569
    0x170f0703050a15020c07080d230901031d0313030c06020313170f120316021504080a0c02040f09050717030f0901051b060124020c090606041809140c 65
    0x20446002e00400c980540d00c1101207401e00c542c10303a4050303ca1501181c2e2142d80303c4c2000c680d1500c080007040c003c119143c0010207215060050344c4801d20154011a08202c003480054014201d440d41c001c4400da522071000d0059230b401c0000e0031462180d1040124001d02c1c50415601507040c0790408070454004200e0030000000d42c85909044407590441e441007014900c6610307007000a40c05451405001e0b400c02c90310407069010156000b0550485c41e0550b0098000c8240e958506c8000045554085880005c002c5000030001e400040007905101c0312040d0141d002408588001002a0740c1554414030304040c03010402000c0f020703103002c01060603142c48508084e40d890051500349d0102510000e8035001c03d91082c01666030b02c0a20602ea031703c0010a04020a407182e00902800c4ca007502c2c0c0107241341803445070401c50031500000d40c0241003805502001c1c0643d0080090400c7d40215003040002149090810002d026052003140010341d10240d1600c01003080c2e000301803903008d0344101c1c1080181d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 869663066 1250 869661816 869661823
    0x6030617031902030c0307030509090a0b0310150b030901090c060e03030f090406030f0c06030e03090603071b14010b01090504020403031e090816180c080c0c0a0c170f070305 76
    0xb40844410214840d00d5640012441e600c110701401e0854003010a00c8410143c100015180e228822144a00309030f484409840844140c84007180d4168050300d0925141c40c415405081c80c4410303010104900c40e290b0380c01c000503510a54144002da95179880c0070f01031019105200c005400e062030183e040c400c0150009070f80780210580c0100001e00081c0003075082d80e46510100096601c0102c41c60100c0d214103000b5550340d918400c80d40441d007000d45c569500d82010046465960f4000c0000f41543c42e0544200c90040c80c003d07021075076000d80101e040214402c18480c0b0003048030700f0008241c1d5096800010100c05060b40110701a80c0140010300c0000d42080041026065204c0a940c4801172200d0071107050a080c0e000148a02401503805e014207443e03080f010680744550034240c485024940340c032088503085101400000c0004001c5040c40c1045801007810740e9034001140c1079018951602e41607043c840d4071540c200702c0742e124140c4000500b40000e0304111803071000703802d0072483c544410340c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 869664316 1250 869663066 869663077
    0x1060c1e03021c0e09041407540510050a1503020f0d1107020f06070c030b1f1401021c1205060621071103071a10031b0603061703 57
    0x3d440020510140882c0b081000200101c03000f00380142c1d908040c00d00c0340d1220031141c2501014050600c0c0402c03140442c4c0585004101d2a4007802440306002d905281d1a000c501c0680442d441e40c1c40c0742c00c6420307690a480301c4503100d0003180028581404110241068403681c01107024a140420800c4100d848828240f000451401c0259849064060a407210b1007640704050140e46042c01d400c8110f4500301c00751000d503200307a9240c038050348803a0400c040d40c0150800144070030f29101c02070001030010f00e60346411014100c80c0015007602d501c0104038981042c2c1080301450100c2c2000e0301c0969041200d41c40d0400743c0034041c07041c0101640c0c028141c0030000341010940c2c2d1a0030100303520f034031150200e8542e02151141840c0360118641e50720244c140a0760020006440c550001e14035241c080304a40b641c503841416410305001c620000c81b6081c40050090507a91a07451000002c130701201e02c580034407080954440e12107400d2000107000c4640300d81001e0701c1000001d103800d8940e8000002c441d03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 869665566 1250 869664316 869664343
    0x40f05011e0b0306130603050f030a0206060a0b160201121109040506090402010f180521070501030c020304180e0d0c051912112a27070804081201060c1e0302 69
    0x50f0214010413085c081d1810b54802009842400801741c013111010024003120592a070035107100d901c0342001c01031200389901441d403160b00104032050700b00010305000c6103010710604000c000c000c50001030004030b408100c000601c1c0703400024840c03000d2406204440d440541150740c4605414181c00081c015505189180e050000b07600000b603640d004480f820004140041900521202c5103602030082d000d1501c00d003506100300e80c0082420b41c02800703010400d0804e41e00075400c203860007403848465038003445c0000c0080ea490201160016042c8184010b2540d01e8a41d10300c044000d00e002e070314248000f03035526242e44041182100040c0d0320001000a4019441c040000b9125001c3c5035081841c801c0100340218480d03034010100c032141c1c11281c201010222039400b0001c00304100182001c0800e021042050000300001d005240686440c60b080707400344071040d003040d424050064100c0f0003078110f8008140c031013041000700800134451400c4100c4c0c2c03030108004812266000f03076503403088d0902d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 869666816 1250 869665566 869665579
    0x409051e2215060305210f0a0903060e0703031d0a09020c010e0105011e06092409090203090c09012108031504050114010221070f060b040f05011e0b0306 67
    0x110780d200c0062840e00c2542010b8007945940d03401160700c0003001a40720480e124000e110300058844071950100000c0c3c25000052890551660344c440c11560100303c0d84814040030000200c0456013a219402140d51500c00803c8110300b94100501950441c401c0590000d451200c90074450f12881c8004007101c503071040160701e45010400759409443c0c0e00c3e015442079071800d0000a0554100011000300c41d22502c01e5800e4181c40740000c44511002d400f5421400c06841401d0801d55192001000e04030110701c0e006030201d4032040f00c2401c2e6401a12030030032550108444101e1407400061142c0180740803400400711240392078030010b002e1910340001d000c20070041b00207000f0242d004841c01c120394004008000c03a40e150384010201d11242002d5a0041c89001240e000034004008404580c60240141034109004c0369203d500110030807104a62a5403290b51050554032107004805c021482d4070800301e41c66040c0610f01c08500d8100c6512149802d900c80100700b2491244100c982140c811f441c039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 869668066 1250 869666816 869666851
    0xa060915031113030303050711060f07110d080f0703230406021306050c01050609071d130c0c0201020c040204051305041e05030a12110306040905070513020409051e 72
    0x9400402070072810340380050b8001108003400c01507140300426280b0a40341004613440b2154104d4a0072021406000158001000b01e00c5892841080d213500407100e2038105820015400490308141059642c2c4000c0b60039203080c007201c00d0801c008585e122007280b40c100040c11a070f0b0500c84410343c0d210300a0b111050100003003014002690100c441c04042c001810700050f66443e4010310580c8000c4d4440705951130a03012419a1500e001c840d0b01454160b564010f8065100b40e250030306039119110241d001e94440203e82c000d6100d4003505e40d00022684030464194268000a41400000b2000604c2144100414000383d50347c041003182175007103090005055039452401512404541c0d1000b00102e6280320884100640000140440819a0307650841c41c0d0200b0000f005a4450030019040d81ca814400180f40782050b80c02510714a020704102e80c50b590341c80d000b040c581c480700d000e1052010f400060502035210700c0d001340f40d00089e0b030251034400c87d441c4c443d011100101c041c00305403180700e00410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 869669316 1250 869668066 869668109
    0x9040c0b13050a061101060e0103080307110109120917010c02031605010b030a2d02130c020c12061b0f09040902010903080a080109060605030f0c031b03040f0507050a0609 75
    0x40c0769015000181c880c100d4551107480142102c0d040e40c260801d250708004022402c0407146540c00d048030b80c859800340c00d545421000b554400100e200a101c959621000710340415034501d18050700590301d4807030f64801800c000402d68451400452403d0f035030b0401d0b20042c0303801d5000040306c0001c441c82d002600d03e40b810745030250240ca00c42c0d85260f45407280b400100f05100c80b0060043c0300c004841103500003000c40c2c0203110881c12038140041e5103c103a02c400c03950510394640002e241045d41348156020b03214a1000079001ea1810340c40e0000c60f82c080020810400200d070300d0002400312000716942029881244201184030b0702c1206802213440c1c501000c116402010f002c005940e0001e12980c44030190712008100b014248600b06189050680005a0f140100100d0340918010011228103640c1c9900130410b0360b10240081c1c50f02c4103003c5c8082c48a03203e000265009501c109112840d11801c0d080052a2508681040d48500300c091020403890750048068001c0715020854440003005100e03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 869670566 1250 869669316 869669347
    0x90a06150f0803030a0c11060f0604060e0f040318140f01090e0901051f0302011b1106070305071101260702120d020d142e12150b09040c0b 61
    0x18003009280400e0100803402d8180400610300c9088404c00c10403401d88007103000c60f00d1039000175568500c0c0d08500042800d00c68008036090f0710060240010800c3c569503100504000021980c4036140c0c2407400501c02015031007400e500340d514010101d05d1201d400d00c114240c040c0d4400c100c051203034403403922907a896400754038004000d02c164a80180b083c070b00030315001d000e032504503103407100c0c95a90041042c0c181929100801501e4048c0e589203081b6880c0e440c2d100c1c01007400407085c0c0e1450007028051046680701001803034120b00c0f0340e80da16140d003c03508d08070500002158625062180700529006c803146040704140c25001b46103402402c0f41c58400060341082121000c003622240d000400030201902900204640c081006003000f4441120124200d059420b5a41032500002c054204588500208405500c845204106100039540d00ca03258003071042814200c600002241c2e00740b510f00010b1085801d42e0308240c45200340d80c40d00c2d0780d40c19811410743c01140c01c02d0f1004985144a0380f03548 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 869671816 1250 869670566 869670569
    0x21605010e07060e240a0905120d080a050403170c090d0c180506150f0c0a030e0a081b301608030f0f1608280503090a0615 54
    0x6802040521205074065856035500c1c010100415020605080d01d800c014900281010940345100e40021503080c030b1010950040c0030700382c20800000c2000c90241d0f84d001d690010036100038002c100025807604c01600060008181002c03251800081101081d040300380141e4510108421071019901c07840c04c1102402005d403096041320480000e5000c0000301c402580680d085a039000c80000305041103041a00c00482e1403940290360a0840c8400a00c0a00906041492282d2140c14401c04100c041c1c900300301110b040c0c0001e05078840c0020300d42000c0b9512409041800007074021208459214550110544040c0740540d01409000c00112030340e11001d04001c420880c8154442141c1001981d2055000302d40c02840c089464001114007000080f10031204006045a080c4442c4107920f1281350030450b201c0d01c0f01c0e00034160a800043c45d150082c404c00401c012422110001b0031303100003800d500014802c047c4003041050100085000408030f0f40680d11050206401d41c030004000c0c2001d200b0b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 869673066 1250 869671816 869671823
    0xa0b0309030306041b0905060307030e030d15060203030c090108150904050604032a02040e210706140142020105090c0303030708041203110d0f1508030d0216 69
    0x4028400c041201200440c040c0d0b104032400c1c040818000403100c03400403483c11510200b882000c3c200101c0c10700c00045e56100d0300e2814000703140a65006603904652065103034409203542d8000d6504607529403a403039001360501d88001e50542c6004068041a8030810b0407190500501d01c002480c06090003121148680d409051141c07281080e01d44130360b0300d08042c0c0d000c502140d9201851103400c03c00003d141c94031145005a0014500140c00340030080421500c490454043c46103694441f00440603800d1342403d440481c03594401c034230b0400b40f0884007480d040c1805401c401e001005000d18180300800030610422070740d83d0619466004060002c152290104110f40c2c84070508109034041d0701162007590034a041d0b0b400310819004150712448121070650200b60741c2008a40801c3c40e18034400d0b07001c00541400694054820400f000d641c1140c9142190242c07641180340c10030440d40101c03846542d218444040407428425096168040e207102d0140081c0d0110304148880d02d6050b100071840c2c0c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 869674316 1250 869673066 869673089
    0xc0304030c0e0709210201030509070f0f03050d080f0726011d0603010903021c0c0804030f12030c0530010b03040b0718060e03030d1505120703020d110a 67
    0x5a03140703100d04103a030480f0800f002c100900c41c0041c5254855584078480e140e02c040020080c1070343e50065006000c0a004100c13644990038010074030b12440403180d00a014844814188185945001803804a01095410800a000302400f00c1c580600e404076030011500d007070044c0c0155200080500c0c0402d442043e0545820101c000210861001440c201d0f4120b000e490030308075034841c02854280c0e044800c0040c01079200700510b444044804c40b07540184941441e1964000c00355032560103041c0c00c0b5410a440b440c0711800100304001c08102d140d159a40e8504082c49444022030307021740b950243c400300103103800d03501c0100d0b2614400c03040014031031406407511078440d503100d00100305242c104075021582800204040b4070b071503018826800c0204003180c000ba01007030034904100c40c0414103205d2281c00d44010300038105440303043d002d03000c11006000062000d252900003000100390303c40084da07940e81c122590030b03c05629441d0002810356044900d1420003071080020174412078580e444070a13400c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 869675566 1250 869674316 869674319
    0x6081b01230309010b0d110103090f060204150809010c090e100b0d1505061602040b0f130c080112020109140f120706020615100c0303020d091a090a12050c0304030c 72
    0x1c0280140d030003100b011000300080c0c03030503400340640750021560143c041151000d44c017200b584240c00c0405018411102c1f01c0075000b007a0b4a00099810a4000002e040107011862210591010a00d07600c49007020081c4108280c0c01c4002d070035884607000351448591810001480340e0003079401c4000606080e5035565807003440754003850060021038840e0140c45048040004d040c070b090001d540181c182102c00e2013034042c25500b00001801c41c004c1494002d9080080c10000d42d60b03040106c0c10359007454002141464515100502e1440140c01810300b0754000481c07040503036840301030001514800c0c002102c01181220005aa2440f0f00c101250300803030201010030711800114210b41143c0c40e54003111082c1e00c0f100b00c2542c00503a4091080d4010b002d030007455096600c61026843d8040c080c1c2401894040c1c45030104040e5540740c8402d445206401c0369112a8225000c15140e002d2a0750000d800c601c4a143d0300d0400711610011001c08100000c07601c510306580910031600110f44c082d09010019 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 869676816 1250 869675566 869675627
    0x109050a0303091a030c2203060207030c060e1209040203060d08031609060c1212140c04050109170309190b0315040b0117130f060e1f06081b01 63
    0x4031580a00894003000c4200002e904e400b070403d0300d020340071900500b800c1c1444059100041c00c1404d140d0f6000484501c400400b08103d4801010001e000e0341e5031409a00035814a4000da90100889050380e50014843c100b000000c541a1003050008403030240e03482d00c5003400940f100200380b10150546c28004180b00740c10b0214640408800040d807181240b041d500c1a003620280c2040d08050705401c0625441c510f41c03846800c180742030301c61500300024401040c070303010742191208035101d00c031400002805009568120800c0f0b0002c0078888000002c1085644403980c80340103006005018420071064a6591115903440c94054051040f6a5850b0314024542510009140900a0013180340c80c00c00c1d0419440b0718491b61140c000400c02da02c00e07481c0c02d0300c402c10750015101c040c0c40e0034030018a4100000c1c5d681c0940e800d041c034448001d01c2c0c00030140c15403c54170080100c0a084040c0340110030861800c001c9540c034201303200d54012404241c0807000503920405040030f00c49903c0c46090b0420000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 869678066 1250 869676816 869676827
    0x21c1b02040213141306030309260f010b03010f180f031106040302100e030307020a15200c062a030a090501050702010606020c01030c0e0d05190c0923060904020109050a0303 76
    0x8501d004c8803019100d400c0304265004854060001a0010305816011f002100c20344580d0f144000032110304001c4282e01c490ac03181820b240110741c000c01d035180d4110602da03140900a040c001d40c1800c200b0040c44054014201ca0903524142c010800c1180d520340c070303041c140104494060444c00c5026940c2500e040d250081d2138070445d203103262131207184c03501450046c2c0d000015203202d6000e80d0000c201031281c941307401c1c1c4609000602d00030a9519000c400b007401c00c04003401003503d00d580c030380161240040c0404508005005001400321420140250213a018029040600c1400c030851a076032502c0b01c48a1038003400b5255030142c00d07036003007405100e02107505604c1703003040b2000c41d402d0700c4404c00540b004400f43c941c48003100001408490310071555150100b41c407203030715128008841c407a148280038003071010724401c41501c0072914806c00b080446203900508121700307040713034100310348440101c02070030004805001c0600401440000800f164010321164018040040060180f5039403032030004d01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 869679316 1250 869678066 869678099
    0x6030507090e07060e0d060b0312070506010806010e1b0711060c03070209061207090b0d0f03080f090a15020d0605030601171002180118091b021c1b02040213 69
    0x4143c412804006070261040c0f90000340040010102c044c3c2d815151110760241c030113091626410b004419824002810f07040040820a20542c00386c4050742c03500c0c1c400d070304201050348410780000c4208100490559400d980103540302c000ea217125280e900d5409c01c1c10112032002c0035560807280000d40d080304110004007821885100b00c070005083d9561909210400d6a498202000e59008880500c44000207030403007180340c4d00151541010b61400d032160308281c02c09007800d9000c60b0020b001d100661620700f6545910002c071b50001d207a0b0843d0b580e64540d10751400d040711031340f840d13000c9031501c502c00c4160080380080200400f180c01550712641c0b4603052a007400c441107143e100d14000040a40064029a000800a41080309000c0744c004019a036880c80c04c10482003008112a012a84108a2240c40e014043c0c404c52068070104800020b4a0309820803801c840e5080503031509800542c1c8505010144000460705206140c003034030120b4040c2c0185442a030071403d4210000c20905d0b106018480e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 869680566 1250 869679316 869679341
    0x180204150501080a0c0201020d05040b0718080307030e0f04060303030c0e12060f07142206030203190c030917070218190b060c0114241f030603050709 66
    0x4503061603a24004211400d501c6103038007041c00080040c1d00c6054a51042c0800b04041c000985401850b9101c00220380044800b210312410080522500031340c81140c07596900000e662a400860801000710b95070300034140d0003000c000f5064001e50032602c40c1d8040350a24540500180502a241d141c0500927002d100b070b00364005000d00103070560f9854454800840485907501514240d200c0c0803000090807001030814081c401800c1009000001d500c00411001080c04038440103030744d8420059441104581c0404101401403090042002184043e00d0185100120000e0303680e00510040c0e018000d80d680150403815050909100204240c0003811100d100b1602242c40d407900c0403a101a6002c15075404404151800403240401c620358407a000c580c0c0000c20090070403185114103400c0d507800b1080c2c1200782e0508000c0c41514820350300766014840c0021902e5900090000100f0f2880e0780c408551100003805c28610180c96000c2c0d0701c0703500515000320a448209807111050000382c54020b0096 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 869681816 1250 869680566 869680571
    0x1b0607020f0c010203090a030b04110604030c140906060a030e0c13020309062d0408070b0c190207060c082a0303150d030e0609132c0105041221180204 66
    0x6540c20b40c0701004480c251b6000034800c8100303500310786829405c01001001150281410f0b032810425a950301c2c0034100551040d54554003060400007288034041d0400d08141c001d03010181886081c0c1d03503800a41390b10140621f400940d0003003080040745414080e4040310f0304a10070326080d404c0115076800562241101c4012220140c45562904851005004140d02841c00c1610541000c0300c0e4100c490790014082d6100c1070034100c003900c508102400a070355040040d407002442805d56102600000b0401c01c540c00900b681c1c41c42d00d8030150104c44194002810304c0d00c006a0040080c1c49000741003800040042c5400014202140c43c5c0d50300d50068070700241030720050700c00340300c10b00d040c041c11103480354982d071084480226003040c0a00c0c0c7d040240c0301076004c0700c4040344582201c658412126400c0154241010220803274190a0080ba03800d001e200160341000c0801c0041480710800540c3c0d581750307140030b92039455100420000140c419504561180c1065001c400208208041c0d50b002d9000722000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 869683066 1250 869681816 869681833
    0xa060f0c11030406050f0c1f020414090f01180e010e0a02090a020403050705040504020102031c021c0e03030c0903070e0f070807021b120307021302190f0c02061b0607020f 75
    0x107240d528010f41c880c1c2c0000410801c40c030580208404007070808040c00c1800c03070301ca10f64002e0844000e6200d0080309813070b09902080400042c3c000039400108994103580e0601d181c2421407458403114814040c04042101c0700510540d00750640d4000340304000c0034402003040900003000191a0090000706a00c100c00d800301040500b1564030031501240d90100003401c01d5440c00701807001802c4000d00613819400305200c000c0c1d00007850600504112f80c01140182c0d20a40500d08c1400911803402070129580f4001010100c101c00100322b079007080c4507125154480c0241c0001078503000f102e0f04811094481d1900340140180700094490045915444032110f580c0c42c41e208a80d2562103403100100f1000d031036911602810b05910040d420750b8894103030f03885e05d0f03090740124104040e410300184203190300248506c5860b0013803c2e0941d10480c940b03001c41d07440131040c0c2c00819240f000d04001c0d102c0d084c0020300501992a00580400d4405910700780c1d690342c90b11a402940300c070014000c60060340a40d558 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 869684316 1250 869683066 869683097
    0x1003060617061e070e0d080307030f060605090922051608120306030c130e0f031c0917090402040f0b0d150602101d0102070c0305010606020d0c140a060f0c 68
    0x250f824940a908110001c00d5031040000c41d80140410601703504401020400b5000c1180d8400451154042c2d8901080070044054801c4c05c90380345500020030004180b0141c0b00564407078105079085071400748555480f00c100440c107804c0100600004001d84038841040c00d00c407c04101d980308584035801900e80f0b040c1d0f0450812107620003202c0e540d600d90058040d0711035a18090500d50380910a00c0340000303115940324081803801c040d45e40c6114169102043e444c0981508140f00d01c10b504440c40c0600c141e044994540400c07040b40c0790302502001011850103405e450b1541510f0007011141414141c0b9555541e107007089a100f0003540c6d020324184034130604481e0340b410380788045514a500909009004440050040ca0806403015100c107840c0c03200141c0a909001400c0518001d84803074030b00b0f51840c6001401c443c820b03807001055401c85181010b1723054128841c0c20f250348d041040100030540c0580c00300e0600000c0710b07000f0241450701203041c81c0e01e4966800001151510b4076440c0c0005e50303401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 869685566 1250 869684316 869684341
    0x20a03200106060804030e04050618180609010b0913350d02040e0603060402091519060807090e0106050702060a170403050c2b030e1c031b030c090e100306061706 71
    0x200e200380c022f00f00032200c40300c100f6030b8a000b07540035200d1540c07890f0002070390000c07a0402c001a60412591380d1540e922401d00d00c0c108800c01e0300f00c1030401166001c00340e69500c3c59900560680541c0f40350380074841c21001c268245502401191304a52443ea5070b80c849009d00303009402c9070144150302c00e81b060001d500b5050005040740103580042c183c520070b6660009500301c80607407000a6070440d0071000501c40c2d400000c15010f025005948850f52603140c061001071a146542c0c0c0031462100c1c07070200400800303400808981e25542c0540d00035a03100307440e21094072080f95030b0500c41407101100040105240e0f118000d001200c1c881030644490f42004010022890b0b105a444050a0203c8185030381c020300aa204e0035101c00341005a0b615001d41554403e01d1401c40300c07111001c41d4440c0c6034410040d1002220b500c0c0034510782002c2280c2c2054000041002045000e444110300814003c504100e0275044a180250b074019001d101407600d5000803038440d10050301545061203400041012143c003107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 869686816 1250 869685566 869685571
    0x309360c03011401231b0304150314010311130608060906011a0708181c030c06060f0308090909030903071d070206010e0a050a062102011e020a03200106060804030e0405 74
    0x800003001d940000041500e0540c04003402ea0700d1707a00c40402410005500340048c02c02003c00c440c4441003035040d110040c0a450b0080c0c1c2010382c02c20700d6070041c000100228008808020140c0c1da9801c05203100303048500910b51900b180040703100740300c02c0201c0c1c480005103441c1030310f40e000345600e418210b2141ca0300c10f5008031440280420b100303015240c44504440c0442c210900d005154524400c49a0b00104142d030003100d0030360001d80310b0342002090205034090f80e001402c610005500440c40c603152188a400344001d190f1040351500c0104081183c204181d0310391000007015545032580e1081619018031203118842050501c0800040b05680041381d43da0490707820b551850b00665076801e8240c000d1900038600d4004603510203000c224518803051000203d032000074540010070703403030002400d940d5103248400782e07000e04010304022a5501043c0c00c4007041d030509040c0300301161100c0700c1c00c81043d0418581141c2d86400030000b0040d82c00380d03265018900a844050340c03040c40c40e0034041580d604 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 869688066 1250 869686816 869686847
    0xc030b06030c240c0a080a0f0e0f0f010305092a130c0c020d080409151706070f0c060b10081e0c251a15030309360c03011401 55
    0x4200c50034002501c10b000611485040b1801c0d6134485d606643da00400f600003504c800b00251100740f072303000315039001010b046101d42c040f5960106250a14001100380340141441410036031600d0118034440c508003c114a9080c0080481e41d0000a0400f2411680030325001c051040b00309504440b000390061044001c0c460881ea070f01841d5501940030b000121803000e00481d01b81400700400640840603101d41c061403503c111500300c60701d160000c01042174004001150380e68110340184507005401201c18043e44480b810151300c2c0010f14240302c0018044105002c0d00006590743c403068250748407902c40c3c17064041c001001d80d44080462004403080c0200e403080f4005400b0042d0320f032038040d10a2182e03410407110b454003442408a0b5950001d022603903501d10700a41d009401e021003075100784100002c0403016401135007072810050000e0f110b046000e4503d280c142c0a0080780034109000c80003020380545201ca1944c20303060030761117844250b009104100d0440240000803010b984101e80d00c0130301016 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 869689316 1250 869688066 869688109
    0x10c11060403050c1f060f06080621030f0c0c01030e1507080c09063c040306050a0e0f0a02011b080d0b0f0409030305090d11060a020c0a0c030b06030c 66
    0x3107030303030b410746650380101c40126443c85a0005051440c02c010340540e000c107008000410303034501c0e003841c12801c640c4a40040381404016020003c0d02d45520030180720706e00319101d000d46e8041c4040112410740c49220000c0e0740b03200c0005030300e40000200040301103400000fa60f040000030700da0300500c1d43b102012001a10300c8400100490041c138813440c54135402c43e4511812a10b449951000903280d40d01103e241400a00c0e4035210100d0220f510a100b0105c036010360720305940031070b4500306200d03078440ca000003040b527541c440105004814960200722480c0d0f04208a401071441c0d00642951860002012800584604100c8980c141454202140a030740140014201981d24140e00007070b001030542543c1007001e40c003200f0f40c0e56031340340207080c05103000c1d480c001098101312070101e0a200084100009101c14040000024031001580580c40030008100603243c4404210b0307503003440c80d50304003e4100c460200011051007103904045010760012030880381407400728800d021095100e407629045111 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 869690566 1250 869689316 869689321
    0x30306170f070902030916080c03070b0f0f0c0102090a0308071b0b030406020901170a02070b010b030106270b0315041802100c11090901060513110a0516050d020f010c1106 75
    0x203003250045d50300103134002d0035641c2c4182c6a146e800d100508652100d20f040d4000f142c48c030340c507040034040000580a9015002d24041548038402c401d48200c0d0001d08500340300082d0788c0d0740c144080d41900d884110080114001c5584d0b81090305068008101c1519452500c1950f00d2071031a180724100e003154114004a07046036116142c810003500702240306411f2111f9003503128007030480000e03082d100b4800314400607121a294103015440c40416004040b48000420050014540002c040c44002101e1201c1e1040e000c4000d10410400045901540e001d103000700521144d00805500c0c12002030040e00d003086100c10070152049407000c1100c010f0742040444640c00586442858501c000c280610b00440c0500501030114580181c12500314420341d542c0d54040c03080340351140e03855400008405060007095031801045185125030f481c44401d0081c00640007a000c1058203481c3c0e066500300c010381e5000313814000080d48400002000d040e055207001e590041d03040c0201545e5400351650780050146a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 869691816 1250 869690566 869690579
    0x50108192301090b0711070801061805190603050705011106040201091401050c060a02040f0b0408030406030c1101021308060109022b0b10170f04031d01050c0109030306170f07 77
    0x8200042600300c1035490f1041c0300d02245840002502919155840c03103a18280042e02a0421030b80307405c500041d07410070100f0806006071040151031343c00c2c001c90001c1d61b5218074103801103200003803000d80255428060300005000c00071582c1b108541c070a80396408900e0100d81c2c4d980e2a4079080f01e0003804103400d01014401d43e40c80002013010300c00c043c10100c1c40c22260826003480d0400c00c840c500ca50503000503060004050881c0784500620381940000d040c241040781e0036849000360700402c001c260362214030010680c4100d0200c0321444044000710368520120032901c400000600500c019442450000104200d0750b00c00c990180c0b20b00581441ca0414420000c8034000c440154007400646540c408055917849030784400c0b02880c62340f1510f40d0103800c0845500c203500003d12000036001d41c82d0800000c84e411107016a11501c0c2d103424030481100b4080162035600500c041116150300e8805c083c0d0815406a100300140c801c948004e201e1145c0341a0000e948001d01010740c840703a00031380401c1208 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 869693066 1250 869691816 869691863
    0x3190e01210213090b04060b070308070c0507030215130e011401080907050402041719030c02010807180609090b061602090c0409090f020f180c07031e0305010819 71
    0x903007490560140c90810310342010a04140d0a41141c2015a81c0d114440380c1403400b48034071802010765000d0903040005507140544681030090046090060035041003003003200a00203d000346600a00742e00c1021034102c100310441d00a29040d0440703004034540412000c5281c48000e049507065914249210012401140c4031803000d00b10300c4491103000e0b000b14041c0e45500141000e02380e111100113456064803607c1d89402e000840742d40910740409848800b2035408507100c9421502030908801a45070340b81d08942ca850305550752000f02d207007403002058003a40400a0003c070340c3e1ba0300e4184061030020040201c030f44030301100c0d01144071080c002600182880840d00c0d80c42a03121f44200e081c103503603aa0f00b00036506510360031a0803003645480380c0c00314540611140d00102c5c054901307286040364182c42e44400003021f4140da41d81e0101144400815201c2ca07502107648403126801c015154042e04050302a0000303000f0206140201a0307040c6a8220500810340f040360401110240e0340c00310103a0584 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 869694316 1250 869693066 869693117
    0x604081206041e1509060b0c070f21150903050301060906021515030f161503020315011110023004030807030c0509030a110f120703140102040f0803190e01 68
    0x109841c11800052010158401c407001010340a4103aa908c20104490600f401039541010310030f10080d21003880001e20000f00e428800e1140085100d07440c074603051440c2d0040034500300c0c0c00c41c10300b448103180c10194041c5c06507040b070b4a80e8444445082c0c03140c205176181d044503e0640a402444000925843c0344c0f4140344411010190945403036203480c015060600c500031143e85903e0103015010803401809032251080b0071864038003107003182414140c001c25510703200302c4c0504028941c4680c002d4075a040c4001d5074540304002c0f08664803107007540c14046445140b101030100b03400310841c1c010440f0f44130510078400c82d85903448044540d50708109500a041c0b100300da108101007800f460040d51000c1000406050203200394001d10307138880c020403100701c45d20301c42c0c240500506c5150079070b040c0e00091100b091f40e510260810425204060160081c00360344d2069400010b0a000024403000110082038283d040d0b58484900706075008042e201002c011040c540001c4c4005000d02e98810000340004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 869695566 1250 869694316 869694341
    0x705030304020418211706180c160606030b070201020f03180a0c03050c09060406050f27180613030906051b030d0f1802060703050c0f0604081206041e 66
    0x12001c030079200c034581c0020150503046650b010b0280b5400043e003220205081c0d81c031201c01e0402c0c6d89004008128503420189070803403600d180d0404102000340d0941618001c41d00c0c680220250002c0d030800b03602601c200d00c01511207017840004100900e206000b00c5420402560f500b514540710303c4045000d01401d00c07001c080d10300882d03882d140001c84c8846024000e40c0114004d1030004c0b076010070031002c001c000d002c0e2441180382070001c03c042e0315102070307500441e181100c83c803688075104510260403806c0c0c0441c00c1a000b03996001c01800054070300746032010b204004201c8081e90381e05060544c104180c0c0c003015011450340e40c0100501c0344144010b04501102d00c40c404210317100d81025500c1c580003580c81d040c0b04c3e5110541802044100e11808046425090300110300344259000b00c0c0007881360300009810801d0000c1c550300d00c41d01c204480d1144040b520f088850a280034140320000780c00505014046001384804104c0e20304d03060048000c10030005488014403030704823140c06d004081030820705 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 869696816 1250 869695566 869695601
    0xf07020102040302220b010207080d050a050714010e1e030702100309020a030c140901031a100f060c11060a0e0f12010e03090102060f13060c030f02280507050303040204 74
    0x103c0183c8410003022010b00c1d4100a2882241302e490b420340c159130301095a10304643c00200100300b0142c0002c0e0241284449040190740c40c418010221414031400c0710203010a441300c03440c0c8142040560080483c1d21031b80702501c4540c3d24250070300091007600d440f0030009a100307000d0000980740c0714200216400840c200000c000e0f00d01e80c042800304803d58000d65201c03021800410400150901224080c1c3c42122031078441e40c1181d40c2d20990442d800d4105040401c040002002c103078510700e00001510850b07101c070080e25641c03d401040d042001c1c0c0e0448452000a1040200d414a072042d00c001064548030300040c41028030510507070340c00700103045602844440d50500151821b1285201c0c15a904000e1030b51039072a800060f00e040405041400144000e90411032408a200c124007011070f07200401140c1d0009114089001e0408806000320052000600804008107514200e041800c0d8110000c840302d40c80d1030035602d0b4000c00c84054400c0c1c108000180051070254072005462540301c007039 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 869698066 1250 869696816 869696819
    0x91c0c290a05090d0203090108010909080408160807090b010e010c0303020d0e0606040509071208030405070b160c050a0b0a0c0c030c06050a030f06030218252a0b0f0702010204 77
    0x8012510005039181c0c000d05075100c0a000c8a001e0034010300305140740600080d4681042c1030002840218140b2882c00c605640d0030307001040001e41000c40d0010007c3c202101c603200d48c52150603111000038820000580300c1c581000603410700a006443d1503100503128521020000e0005452944c4c491070b08404040d420071080d170b42c1c05614880c400e0480d0045009100e50315141092000b1a50050304003400d5a000d04010410f501900c107070101e5907580807900e603890351281c0c5070240c0f078415503402481040c1004580340400c511100341c404840d40c061310445020a541d5070601210b2070751800354502000c2e00b000b05400700380c0240c103504000d0388164800110584d99480710150308055804c200b0000350002180082c00b641401035603500e1145400420200345543d0000d0300c003001034084d0450880e4828009803050440e03452042d0902c401c803000702850a07111000a00400368000c2e454250f6503844641c102108000c0d10103040d10b030f8044150f032065202c4100e10b00c4100c4004081d00c0456408010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 869699316 1250 869698066 869698133
    0x50a17043210060305010b0604030b270106060e091303050406031505060c0c12010c0807030506060d060f050120060117071a071e02010e06181503091c0c 67
    0x382c1c00b2030020344000102c0c9401d5103040c40c04d445001c6111441600b0074813051021800e51205107402c2400c210408818a0007100700d40103100d0300340003015080d407a02d040000c416401078141d0103009070858401d01183c2c0d031040712600c40201804042c0004209120601066000c2d5100d915080b4411500418030703682c4d40d0024401f035100750341d1410150444030034111720b410010300b20610020410000d008034510403038000c00128000700003034205a150f0010800c6a2500c800701c500d10004503005010881c1c0351101d11a15038113a10800d80065089610440126071545201504403580800780c041e42e441c0048501d082c0d00d080703045040900810400040c455000d040060400740002405502e661283c2400c0c7c90072141010040f900750309442c0700d00010303a88400031071940307041100c080d074550300b040340b034446150600b40120390401101c003140702550055030091441900141c04039109001039020300b0316950110547d48002c5580e01103400700241082c0491304c100060f41c4070501c1c13145801d90 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 869700566 1250 869699316 869699323
    0x50601110d0f09170d03050714030f0709030f0606060e010509030a080306060c060a0506010201110a080f10090f020702031b0a0909061b0c06060501020c0f090a0209030d050a170432 79
    0x40c4c0e000843c5d40070050001d81c1c0c540500509a120310740741400503c1c4140419200c0092000408541111840348001a2510700800300880515040101c503004614149411001170810b1300503540030405180c0707d449150b10500450f240b500018000c1c00403903200e0fa50b601758039040607188550020082c000c04ca0f961a04000b00b41c801c0303904160102e40d604182c0000fa086580c0d000b0340c0d140c159010440e200300d2136000310455400005402504000707540b0004c4a50701021075800540440d4104143d42d4921003540c0c0180c190360f0700840540d19000700c00c5850511080080c81c5054002040d1030040140c0000d541c03004081501500c1e022655081040c031140c41e040c680c940010128480d080080c0030f0280310300c00c03600980000e000516454000b4800600c135071a00ca0316035441185000c00090310201140c0607519440b1028044030ba140c900c0d03940c058060342048440300e000541d0552050540b41501c489103000e1a040307110b010b160000b02181c0c00c48169060001000450324285442c8502c02c01c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 869701816 1250 869700566 869700599
    0x8030603010f02071209080706081302031219030b0402040503071a2802010f0b090112151d150c0909070216091b03021305010f021519050601110d0f09 66
    0x118503140030185d0b0f8100142a80304c1e42d0b000700701d0311b03070180e2024088640c0000700250020348940180c4144911440002c6c03408010349a1400040380100b01000003164045400b03a0f00302d4103860a0090b0103c54051008034040d511905615503c0b0441c204169003070800c07080340d161401d0414a2800504041551011410320350354800e401582d004295030726030a02c14610341d071346002030030300c0340f2410240011002d09040c020300c00903007200b039140d20402c4031400c0c0038800041440014000c040a1043c4c0c400c0e511005403000c0c4045c003c9520804904010342d03092131080000748452401d0155510910841d460014044825440313444842c1d01444048005003009002400d0042004c00c00a00e980811450b040740d43c0c0c081c03500501c1420300440b280d0300810140c9100303203401034072210781c82801c0340350000c046000203013030140714280a9204c80c0700c40150000c10305c0c00c40c24002c40d100c480c011500c1000b590030381c4405421035110851348901c201081c024594052070040c144d01c3c1c5404003440c103840203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 869703066 1250 869701816 869701823
    0x3061807121103070e01180f0f30031b021806011b0c12052802032e0c1124070216090507051b0a02090f0606040308030603010f0207 58
    0x8052070160919203801030350160351041c6206811410074007005450313548034228031410301c1180d14129042084004614000f05401e0100c0c0c001250381d5440c5603034440039402450842d1040c030020000385007030310794242d0b00b0040101e81080c100d500c03030301d04840b00b00481c00c40f41404014180000e01590750312000c04c0c00c10780c80c0032003105e007405e001001501d040d0894000141c0003d8407003c001c007182c40740c0c0c2400204e4121031002d2079007007540c1c5080d42c03e1564038180307089510100101c00c0c000702c0140b160f90000f54030a0b801c480c001444411102c0c1c0001c43d40d100e41c0046a200ea443d900e05220b5a04413000d110303054281020fa401139051294200790000c8100c070700500000707107082400014031030490b400c8482400a8403403101c041d0020406064140502051186c990000c40c042d14491030881d0580d02c000ca194820b00240c014002e9210040340000340d22501c440c20100c2c3c04e4000880d500d600840d0000e00b002d2810f0300c1e5907220025a00003c005503855541e840740f0215014042c001044420320 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 869704316 1250 869703066 869703077
    0xa0309080a08151210050a0b040509030408010f020414011b02030316020307090c0c0b100b070b04050607021b04090206040b0706020a0f0503070f110f0d0306140609130203061807 78
    0x820f03080380f800ca0800c03e100503105440e11241c4020302c900220b883d03200c4001d0340d0004101d075a61150030b1005814103040c41a005864642004001c0d100030001d0010b0701d146100a01620307041c8903c6c0020b901441c0075a0780750314002e000d22041580503406400b54400d00c140c01c805628403c0c1c00283c01e541240d42e2800c42c07542d5004a900840c60280301e18005400641c100300550292001d0042c01404017180007015220164040f42c45128007600001c0142441d400c000e580b02c6c4145480006c20009030340884852040c3c030b003c10920f50020401000100300400d01461800100d01000080c14250707609a0308810200700204030300c11a900103168a03405000b02581c6c40384a03401c014403c0f0035039090a81040414001d10803001d610503000c3c5005040c626102003c600d8034250142841c001d0609050b65112f44100c86441e80d030503800c12800c68280c81c01e04c41600c051102030010034421002c0055002c146070103510389000b034560166401400240041c001300c07403182c40c070041d1000d0640c2c10340045035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 869705566 1250 869704316 869704321
    0xd020a48140601091812050c0f0a05010213121109070e03060109020702011707080c0901090e090105070e0303210a020910020f060a020f071212140f0703050c0f0a0309080a08 76
    0x580740200801041d0030b20982113400006d481d0380d80003c0c01c1d00c4050081020028003000e1000041018154a650b904141c0384520303041d207020b82c008e511840b00c603955058103c90000302501000c2d200c26405030815141480085c41e413040148034240140001d052000d10700034100c84d40c9082010764041c10041c02d00613a0b6603040d00004d41009814980700103807945440c00c008034140d002c1300c0250020716400e012031b19101c00300c006861803803c0b42c100207002d000c044100006a103054000074050561629101101444441415120300c59803608200180881c08001e0000e1403070000386902500c01c920040c10b08021400289025000010340700050f401b002640e42c940c202882200d0b0400d60090046140c01c2000c0b041203c58001c54102400328140c5142d0903e090b4040c0d00041d14640780c01c4404c0081c400006000ca20200342a40c0041d4920411000102194000d12410340180300380b03007029061002e80d5101c5840c640c44400c0882c209919044140002180e02001e0700003070300d071074498007000d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 869706816 1250 869705566 869705579
    0x31508060907360f0504150608030a0c0201110c190602100614040207020d0b0123060a1704170d3e1b030d020a48140601 53
    0x40c01600942d402c0e00b0b241e0300303441010f0010502000080c44038014102d410402c2d650080c02016901d0040703105904050412003080303628006c43c494240b14a408100c2c481e116454540d0340e028590100703010440b80350415000d917000700c4440b080860300c03030100c82c0c0d0001d0705401b0a00c135119140c1c06002c401c1383c48806119240c0c043c003626603400a1848204103480c50480e10b50143c5103464407050096900280f446d0a5480e01080082c50b150042c00c81c05d4507507500c1d014000f50914280002e00c140007103c0310303107190749410422100c1c0b019130360b6541159550103031240b911880000d08100c81c0c414008188001d98500c00014041840c80e09800040706044461f031100361103000c1040a45114152000005148490300d03151080c0d0b5240c0c2442e51201640e00d450703002156084e000400b2403102003400114610070360004c18205585589a1010403541000c5c100700c0b140c00c01240c0d1406c0c80508440702e41320140c884000568041e01c41c5200c001100740c56055404541203110a00e640051006200c2d2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 869708066 1250 869706816 869706823
    0x3080304031106091009050c1009080106060305040206041527030c050f210c060408010608010b180c07030c0b07030c020f0f120703020f030301060e010306050d021c030315080609 78
    0x1d054410040c0083c0c1c50032044180e1038412482880e2a01c3c0c2d81c44000c1c20038003904001d118001440600003070101d4040500181025000c0d1003020b10f070f5800c3c443e011030814030038002d09014640c080d007002c0c1483d0030001c0c505c1c50000340c1d052520401000707402d00c1c691000c01e244000c4808041100c1c0980b1541581012041d1400c1504803500680c019003482000d501c03142030f04488107100d0074134240c2402005034414101001e464409910100c08074000ca4095010342c411022034040c40001c00004402001f40040c00c0c40342448040214006400101524000c50081120078420b01c0d06d01d4120016903034892814a00391100400696036010541030580c041140070900407403100100b4001000c2d03041265102142c507040c4a80e9100840c0070b83c1094000c0040700600c15034081904c0d241c2d83c540e54001c1403400b0340c0868500003070400c040000c0a0500c81340c0c16120b90f03009031242c00c4401c00000c02040030714143d14224101980c0e400840e9a51a8548200b009031402d0005404241003030b00b8034614 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 869709316 1250 869708066 869708087
    0x319020c031615060311120705060a090e010609030302030d02071109040506100614090f030a0501241512020912010e0a060b060406080f090a05062e030302060c07140102040308030403 80
    0x90b01d600c4c3c4001400810b078940d0b407444400d1302c101d0309207404070b100c41d03030840c101507060f032020f50070003004101c0800d00d07504039a91100303803503d04a849080340e03a01c8008584d110340354400500540c1082241e1000e0365960f4004100c50b0340184000d005403120340c808504e45010844064810740c1101003880700340114120280000c144d1450540400c80c40040c6400c203074440c6140c182c0c89880c1132072190901391000d12110350b059820070300800c03030091100074599203446440040b0000680380311000c1a84000c505c4145031203419503507849820806120780c0c0780254020100558004000792002e0f400c800240156403c0729800800340c10005018601401520b080c070351402d11600003031100340b03d103d070701c2641582e003c803130304074403140a498941041e410808000710203132283c00b030741041110005403842d0310304501031110316031002540d4001803030394881420700000340103070041c81c08250403940910103061400d0117104400b00401b400c0484508a9101d907200302c8000901000304400c1c9a0003009800b0b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 869710566 1250 869709316 869709353
    0xe06040c03060f060f090e19050102090925050a0c20040f02070b0412050c011802100305100b090609030f010b120601030305070f0602160b060405010f0b0319020c0316 73
    0x104c4103081024401900c3c000b0b0003030b01c4001383e980f112000c4400d010480100101888102e80d50882940e08010703010390b000b5441c0c54001d41610b4013289080d50340c5002800354001020002c001581403044c01c80b000c5c0c1c0700c5410881044240748400d4040b030fa0f148102203101c0280104024852001010702041e00c401c01200c80c0c0321740c81804804082100440c0680e030107a40194024100c103056141900c0c0707405408082c201c60740c601801702c10814201d02c50b41101070700803101d002100000900440035074a00f00d801d150720122440e801c0200d07040c10405441c44400060003903041c003005e040801c2c6084000340d01604070382e46823040002d82e4200344606c007400405080c042c1c5219030640d24098811310640600500705e445041d080410300440307a050303811314507078186045d802c4081800c0100c0d450340d051719103a01c0703076240c80000110710301da51942404881c9190303026411075a03180d10314284256213000b18640c55800f001002c45000d814002003203102d08a48072a0154000741c100512100032099541 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 869711816 1250 869710566 869710571
    0x1c05031005091807210b04020d0c0e0103060b09070c020f0f04110d0b03030c15060f18061002060615090d0624050a06080103060902031507020d2c01080a0e06040c03060f 74
    0x8044100310306405e0491542100a4600c01d031514400704e601300e80440c20280495142d010003145403900f01c00c28034122802a20284400d1185904002ca01041038a1440124412000c11401030500d1000d007109460000c0c441c012059a94002c9070a5038284a1444840840003d01a11076412407103401c0d503850082c1c00079418039400da60712a94800305000007080020342000018600c0d0344031031055408800240c040d41c1c2004041099400200003550894412003400c001090914400624070f80f0481004003402c1d0795000800c00d03136055600c64044160001d0080e203510010502c280194030240d07941e510350154808980d40300007020300c0c5a0700722512070b0001580c20440564040290b90542e42c104000040046881c400a8604400744000c1442c504400c401c000e240c0d034000c110710a10240c19181c501a6081c84490040140b5283c041189034941810700f120030755201d40141b42c1e01c004081000103080c0748151000349840400c0390100d403081c000c140140100309442c006c100002410304800d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 869713066 1250 869711816 869711849
    0x8030c09031c02030a05130906060314061807110a05060f0f0c03090d0518100e0118030206040b03090a0b010b07031116141c0609141c05031005091807 66
    0x25105c1c07182420b0075042010100c0c0301240390ba00201804001c2000100401c511640c0c0c00c800703409040c1955810401806007800600346003000005080d150046141c0045550383d17541040d0b510b0320103413913030740003070f102e2080580c00242080100e036000e1001d10742d0003c0c05182007070146c001840010903200640000b030092085d00c000019080405940070f003080f41e201c1a204100c015060046200c5660081c441018883c416401c0041d070f50140e903081e07850b591118200511301c510544503200c003e4220134100810086c04c041c04002d180c00c9440d02c0d003070b03074400030310f1341c6801811102c2078010a0090600242030b03420150806210207100c002c2c4c070007410080701c905c0002c03480c40c2c609209881014000107072200c500c3e03581c40c00210300c9001041c2c141e0b442c619682040c00040c48000c00854541843c1004000204070001e1507210700d00c8541d4060b264495200720860b81504050500391141041c5840070500d5a50000e81c3c1d031284c0e9202d20302c00100202250075510340001d03a801803c100240102 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 869714316 1250 869713066 869713123
    0x1a01090c11031e16060510150c110109080d0815090f18030f0a030905070b1201031716050c090610020304062a03120c021207021c08030c0903 62
    0x944100c0d101040c3c0402d0440051003110209100d11030312410b00c648440005010000e07280d0209004d411100c081c2c0004540b502c50007000c0185540d2540d0201e0b2413400850300091052041c08410310043c5401f409403030340c94290310714204080c43c0001c04202d0080400050b00010b80c54136001d604111408515401c18084501882501528030a02d41d40c0346006a000c0360130400413200c0c0010423103072007030780e80d56030440080003807192107001c9400307000e0007100044181c40747c010755224000d1180c004126905c0d681d220446803004200104072403206000013445001030003442a0540c0c010400741c01400f2026041208040000b41410700c11221001003076040b030350004c20f80d01510700c0c900303240000e1040e031040b101c14503902011442c56a286e5180080030964400c0f168001d010b2220303014802d50450f0402603031504022400d4580c81e03071301800214050301d807130445c02100b0046200350070761501c03558840303130b060b41d10459610000010010300e08810381002c00040d0f041e04007010319088994010321 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 869715566 1250 869714316 869714323
    0xc0d2d020f0405060307021204140102060c03010305060601050c01060b070b0406140907090e030405121608030301081b040e100501151707232808060a09050c04031a01090c11 76
    0x19884c0203c2020000698060081182030524a000f156481e29a603454800d04245003040c2001401030080350041480480c10505580c141c1382e0040c0034050564640004543c0764110301c4101c2c01035901c0d00800244200b0700b40c01800007501480527454286440c1c20150f0a841e140182c48540e610101c04100d10902c0c003184000650703440503004a00c08140c461aa490740c01791340c0200743e1040c101e149103a0803040c0080c62480c640c40c041190714006540d8040c20b5161700003441407a016803c4401185584002c5074820000d0120040c03002a403041e01841c07541c41c0c46041d48012400d29510401404542d02c0b4030080e84840315030b0315080810901005004051410181484051004913000b01c4081d15440511441040c040d600a81e290031b030383c0d51015211089812528002400d0a84041c2154800c0c0300603885a0409800d1800282c03074207030143c008090041151803030000034000800020114000f41c100e4030b40ca541805c10325418000c80504899101c3d0b0200c0500060b041d10541a10020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 869716816 1250 869715566 869715569
    0x110a080f130206030a14060628171302031e100203090703080a03050a0b0a0501081b16030e1306060c081827101d0c0d2d020f04 56
    0xca03900001d032680c54a00c603811590410007944000f0101c100495050750b540a286103800e614420382154580b8014001c0070303c145048521040081c55484405960f42685444180e440303150602d02c000400c00310f4a00824107507a102c0319200d0301d03036109055150402c8040030741044040016003c80035040c003c0c0c0c1d60743c01640b21a005a80210014000c6082071003410003e58002400c0359490760003240c01001804101d52034101d90703281000c1d15180781061342c9250140c1d8010b03125900181c03039180c8002000c80702d44020442a46c1c040020078101003002103040ca40500c031703444540f0b400044004228401905125404501d8607000e010409542d002c4408525603400402c025580c0c41246262070119840f41d41481d000510b10010001d031029224032a04585034189400c0c140c1d07140c4003140f208070708252040140000c22220095461a808101c0c9501700c1f119005003490100c207444a641038504020041d100c040c02447c2d10300020401d200c401d00ea80c070104004614044039202c0014007400355 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 869718066 1250 869716816 869716831
    0x30d020d170c0c0304081f05070e0d050109201e0a180b06180405060f030d050a0c0b09010203010807090213090e01020912010b040c0804110103180b04050d03110a08 72
    0x2100d0101c1c0c0038445002c22551008030241c1500c0e034813500c40d5905039a0f507000d01400404241d0f254a01200c401c098490f2600841e21640d5094800f10b6100800c143e103c1d107040c0a8900317550726079500700041c444420081e9081c240b46440035500f0602405c11200302e4a0358031154003080e45503840c1409944101c01d8009840c64080714803981102411100011f00600040f141c00940004000303c89152441c00d2292000084400340896a10b54041c46000c120503505c00b03815905c804540c07102c0d54002c0b00541846003040c50040702a8035183c4488a401409030349492650354008018800c81c1420f1040d040a411038460a43c48d003001c500c0c400740501c0080c0700b65103440381c0d2a0181003c80100390103c0e45404070050403c1c022000e04da001030b00901c1d060400a1041d807810203604021401510310340c1c80350b508050500e1410100d28010f40150004114003450400101d50704000981d01e00b00c5c0034041e40c00b500003402808203500000d012030314000249100303002d040c0301949025038010314450b0b1000d074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 869719316 1250 869718066 869718107
    0x8071202041d0408070b010b250210030e24040b100e07031a032b0212090409020105210109150503030318070801180c0504060503150601021e010b030d020d 68
    0x160780c18008054011001c5c02002446081c00000e20300e0010000340030300d030351500c08851040c0c0c10700c0c000101c003400051000390003144004076a10507034005e60140c0b1586001000f901c0c2040804070410b91440c0b40e40c04200c09001c21441880b051090101d8159400143ca80300c80008501f405032181d60311500900842c109a190030490b82000105206085021405400c96150082044420640d041e0700072108008a1640d0307101e881484c400107001d0400e404019a56140a03041004d200c050600e00205030f051103010000e4000d03941040e04ca6103182598581404015414030624505544000804c9046054034800c103000c2540e0110490307800200503040b021142c0024140282031804a40c060724282d403901d850002035151048168603001e205100c5100142d4a0b103040000300c40300e6014040d0550720605101c0642201c1c21411a04540140111a134451888220030740e2400c6440614041da5184c5010802d1802c0810454100c201580003801d6101c030b208000400c51ba64140d810301d5801c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 869720566 1250 869719316 869719321
    0x812040902280809010509010209010e040f02090603040b041e1203050a1b0906170c09060304060f150918020303180a08010203011707080a0b150f0a030308071202041d 73
    0x81581a40c5150607590080020315507502c0c0d58040c08540e0121101d40310382d42010300080c01071206108461048105071203030070f9140c1d001d80922005090565040c44040e500300001039803942e0700c2001d980700c0e600c290514155480c0c10314180c18600a0541800402e200c03220301c10001132103642650b40c1c213001d14a00020749d951041501e80240080240c0c2d05928002d050161310311681c00b0340c0320008c2e075040da214142d4043d10a811803105203002c80d1002100c05061002018524042c030003580c009001f80004900440c85001100850301030303a081600d6000041c004011002c45405900200442403085021080140e004240c89204071700100f4411a0344180050483e51202d111802409207071000b15282d45c5c668490901c80100c01401c40c1c0548200d9500103807a88001450319012640300351f0f52200ba0b01d81da641501c0c0760f8407084290f548800b0120004046841340b0400000450107991281c1701424000c03000b901c8203500490b903070700942c0108024408007004a03c2c1c1120340d42910395031010381e0f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 869721816 1250 869720566 869720587
    0x602090402130603020c0f0f0601090e0f030d0f060905130803100305150105010e03030301031505060f03100609050709230d0b0f011a0403030806090a20070c0812040902 74
    0x80c07040502004035102c80000209200c0d901d41d0240c10006c500300c0c02c507142072662140d00c95a48100e0070030f0300110b41c80307800180a45003a5030410b0030b03038030400b408980080150380000c07170554114440a449a0ba51095480328240c264050040149105c450401560403c88a0340c1c1d443d03c2220006020118004081810140990000001903420405407011164903801034010390400388141c0e03002070500c422201c914a808402c8034102c0e540b04900c40c000c0c08500c1b601001801e4000c00c07403035002c02510b0186d1140e45040c010012090054000001c0941c01c01414400b10b54001e0321480400900d01024481c150302904141021060f10700c0c01d4030b00403517041c0016942d00c400310000b82075003000b405124100c040c0c24042410380b90f08105041d490b01420040e800325000701d200150020701d104c0e02040c3c0c5403d001460640020b040100407440c480c2098842d00000303481000c0700b640c2ca0001440c1c4080c0b2451828040250421401078517900c6111409c0014034000c1e40034202c10540d00041a8204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 869723066 1250 869721816 869721821
    0x105030604140705101814060d0902010311070f0302070b09030d0819060806090d030b0117070903050f0705090105040e061605042c09012702121203040c09090f06020904 74
    0x10540145419440e000b0b1200080107030305800c141840b071002c085c0000c100c0312501086007c1041020340000e0404252060702d1000d0800790005038180360352124004a418403107002007840c03d00602e410790382d43c2c880b071400901e020305e107600100c00031400340481482c6a80100e00308418118903d03000700c0c4c0c1d840c2d050410456038410300c4000d001501e48400024807a00c0400c18501c2990b542040e03031088841148154281d40182107100e0015601b2803032000300c40c10300d071780c4035400c1415854a03040707a0f80c6951321180740c00c403030040703c0d4915404460100103d10708014264007405c0d0644060200d4903810402d56980c100141c145540300c0c0c010517008040a12900039030b4010b103803803412510340002c0030a50042003050170680c000340e0300550000030304141050040c2004d03141022014403550a44550464480c214200c00300d0340030348000d42c00311482200f005802c8008101681c2d1a0b520300741460016100c0045501c03049420307040000040106210455180065410403005030b600d41594001a00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 869724316 1250 869723066 869723069
    0xc02010f0e01140f0103030507060221070801090c0207051e1c0309030b0c07050601090f020d05010e090c030f0318060702030312010f050607020d021203071205120f01050306041407 79
    0x40c81d15181c0020703881d41d01504014a511400011600e15840f402c00309904803009000140101303a0402c0703400d000030420382c02040d00c0031155400c806040000904410b0031803080c3c8520000a482400610488519206103002e120701800144205481c01000c21802c091407410701307244401c039400f0f0040c0354540f1101307059000610080c0344001c1c1c6180c50080c10146882c001550400c803004002032804940320121850075070084000c00d40c1c2e030b10b0b255031000540366418440d42038580a0000381102c0c50340e40103041c041c1c500d905105a0320715024203120300e030811440b44148258840c03041103e0282d008411030b0507052120404110740103615001c00c1e06840f5a1034001c1d003510002030b90b682d1040e10191001e0503103541c8000c07900280e60310820040707035004094011b94051a03182c0040c0041c944100c8080308501d601064905049880d00e0f082c0a18001d8135011000c134030300040075488880c00344107042e4480003200c2c3c1e40c0c00c55410500441d649042c002c1c4000c01512040703000c060603d204024140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 869725566 1250 869724316 869724341
    0x31a040317070503100509012108160804051002060609040f020f1809210d0b0f0a06080106020f0a031704030909050c07020307211e0503190206280c0201 67
    0x1d110b810150070040840d44101d42d51881c801c41c00201042c1d42c03918100703403412900a0001160702003c688445407000c420014100c403560010004075480b402051224581d183c01500b655448503d00014801c821940c00013110854111104016450760380c4a08207070429008092060900050320110300344410404416510443c1c4525000241d174040d03040a100300905000e80d5410300d403440d0cc4003001c0b13440030700741c1c030007040140304011603d090360b44404032898004003c0c400705001400131505004441c1c1003071001807460340c014001280c040012100c0303900382c480280b00c0c550240d02c00404420700c80c04500c0d40c0e09030f00d0002c1010705118100000c00ba1103820003c002c0b078148030f8010003107035020b8a8201d0180c061140d0010729400b01c1400041013040c1442130b004411480d60354a8000b4800c0c0b020100b0901c00110762002180080001d05400410340d04c0c03843c0d031040b051501918121004000b25105c1c1115441c910402401000002c20b00304180c3c03001c16280c42c88a0280c1c0900506500003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 869726816 1250 869725566 869725607
    0x501060c081822180803190906090605040c12050606090c0d050901150909081605070801062606070c0201050a0e0306040b041a09031602060f0d09060b030304031a0403 73
    0x101c05a0703c0b51011035680800a081003104040c0505144c000c01d404a81c00350042c6001e100094125048013002404607000210018514000c2d0ba20041120344032401620f206980b40100310822640b03108000c0a03120541d103640d98914540d81d0182d03194402000580540c030200d011178640d0440e60140c600417a61610705200038a07241076410300801151801761481010584005070440c43c610400c100303140c010180502c0c1c403403418441c01442c605420216407511031000300241c985020311500001d8500c2c2105503a550303c1605a0140c15031350700390144e809800c5030003406590b580104544529a40c2800e00c1a12828005401d4841d0902c040c0f50075058002e40c41003008000d01d00521500c1180700d900321181c0c909080d1501364101a040b550a0302580c020001003002010a06001b012a03200030a21440c02c803072039054a503207412000c400c90780b0a444440e0132080080d2401203405002c030aa0056007894695103442c1801039010b92040500201c1c1c0002c18285441080305404a50329903008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 869728066 1250 869726816 869726839
    0x1b0f030e09040f0312110301360b03210d0c091a031b070506150d1a1501110a170408031b0d1403040305180307060302040306050a0501060c0818 63
    0x2040480c2e40d094084000890100203001c5a01703841c414200807103d41d040d06821030713081c40c00002c010b0301d0304849004e00d00640c5400344582070300c1c06000e4070884800080440d03100f041c01d0038145040101d403c05128540340200ca19074500c021008c0c0c40c203008020002003480068a0415215031106411a4030418107100d01c0a10440000000f1400b85200c00c0d148898200b251300e0092480c0118100104146c01c1b4201052002140c031609400d4000010424a00180a55280c2000032800e0082d584001c6a407003c0103500350292454000811081c01c003501c0385400403610507212041603000800740700d00d01d40481a200d500c0740681d000f80180e442283e5649040181443c00407a011203c2d500c2407103460f00011031103120b00c4040312540003201130305007940c40710f941c169000c0d00b040f81c83d10003001841d00707041c10a81d402c005500c01852940c600680d210f0a5080980a50710010000d40ca11402c06004000382540301048814003a001080e00d03440310031901c00345460a05849603681c0c0314031072007070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 869729316 1250 869728066 869728073
    0x210b100c03090e06030613030201020c060f0906071403060d06020904020a0504033e010302090a0e0105101b080a020f01020310090b0f031c02070e04080a0801061b0f030e0904 76
    0x12a550124069100e6880745666850f841040c081e01312140c0343c05400c06d4001c10112920302c1c8040c0c2c507840c0720340000b504000c0d6507000315191620407240c00014207091802d01c58a03000611056811005610b0003000e13200b03400130740c1c105520003c0c1810f0f0181004052203424806240c0c10b4a01040c0024415943c3d4031290400811580040c04141c6440500c400700c2c100c00c0c6121605650701c01545040c183d03122301e64069150400315a02c000c40c0c18181c00300490750040e84c50780b2104000d09186101c081c1d61354103200c01d010a032503045030a034080c4040e0300720421640b1180c007112150654000001c50707550402e054100c2c10700741024031402040d8004000d00c5080a903103840c072019940400006c00141e01d1032801c00c1040700a20050a81641201d0030f000e01c580c0044200320702444080c012141d110f5911034180c0c1e001d010446044c0c1340e400c00442c040242650115190340142060300d00842c0407031450025451456801070000c20440100c840d1508160240f15400907004009200c4607080c500b505 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 869730566 1250 869729316 869729327
    0x3030408220e0705090a05030109050f12180607020315070507020f040c1b0615030f020f010906210609020705030c010c03020301180e12070f0c15210b10 67
    0x80ca401100c00390241042140402a901c0d501100d442c21948010354503880801d030303480d42c04003158a030403804502020480b0b072000d009070130b441d620030b400800d20700301c0b0300100174104100740d420402d0001c1c00b040f07020908011008407007001e0100716a00756640c10144000391a284c400c08c201c072492101c0750100200960020090001d03a030007a51400740b1201034a04001c12070f800c071800f42c40417035069070050b1a890a126400020f0342c1c07041d0000142e460b4084480096400c5aa00464076904445002001c504014034559007040c005c1c02c00094980c184003026041c404101c0f040d402d038100a80c1480c00111181e004540209502d000455640701a41011502d0f80e001c00c10340d000315800c000100c02102e10034404caa0490b0141d0008072200c05407201144040c0c061400d12440c00d20a0b0f81c0c840d401c483e0400010080c80c0e224002e050520702c0d242c940758840c084a64440011140c159620f0300030b00390840c203505e9220041d601325180c150303100b0841500a207140300000d908100340c80561050b450308907 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 869731816 1250 869730566 869730577
    0xe150907050108010f061116140f040621060207060c0e01020d020f061305030c0d05120a0c0203030703050919060e070504060b040501111504060203070e01080402030604020f1203030408 81
    0x4000d85844503240c800558803003000780700d0800c3c80d030b0313003600100303e011702c600c0e0340642182c1500240d404010002071201540d1140d50405508102c4000d041000e91070064800031881d0302c250f809000152606000d49610760340c00304075104080c500d82c02d020030018503604883c0c056a00090801c0303c00308200c0000c055429a94089000d88580040c4205aa00000d40201c02c0d64412005003a03a07a18291100c48407031001c0300c1100c89100a02c03800f081d1400c10300c8600c601210b50740c3c1e200e071260042c1c43c8507072000f0009801c28182c140303031264103540d1540c0801125031090381400e002c25540c43c2d2801c1e603454102206541c032001040f104102c01040815085901c01d240c0d07800450340010788580030003045a215100d1144050410042080300d5401140c1c00c001c10800c4106840708410764103c3c40040100440b411520590300008014000703821105001c0444002c0c60400640c0c0343c50750100350703142405040a0711910200c0d030115050b9a48404440000601c03800f0b590b240d09051030700c0d82e00e43c0c00c01d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 869733066 1250 869731816 869731831
    0xf05010201060803251e0210230c2107030e01090b0403030c0c030210120606020f07030210030e0a0309030b0f0105010c0b060f10120c020d140d020405060f03060315010b040303030f0e15 81
    0xa0810100c0e07140c0b0075080010250a01c8018001610740b20100020768ac0c0280070750481405102c200e60004554107504040c18a0b05000442d940e41c214a4004c20402a03412200d0521548030405e101040d403c3c020303942540da241c24242010310035802c101110ba9120344c0029800910486d00f080302640c0540506000f40e584841440002e840e001c042ea194609141c01c210705a2040400b0009890040c03101504007006040c00100d049909400ca41030018002c0309601103036140710200104036107460032035845005840003d24950410340006c01090710001b01605442440c000304003a07940e2055141c89940c8020407094510840c100003800340e41e03080c000203510601d80016402c0c03503400031030345400d100742c0ca9132400d02c040b5004800b140c0c00d42010056141e116824000459281c540724000e000980c80c2c3c000c80c540341d00d41401003520340208001101d140e4214140100004405c42041c2c4080d640d00d800c01058030004843e9100041034002185411449500c5241c64101e415096050251740d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 869734316 1250 869733066 869733079
    0x50405160f06050d020f0c011805160e0109020a140301270b060a0503090a020a2d03030207090903210912170106030908071b0f05010201060803251e02 66
    0x688003009800041c0341e01c41e94002c16420042190042820342c014000115540642070406030000d0049085800040715000c1d4141540d03850400d01c4010443d114407c114503420f0300005050007001c7d40340b070704117101d9400074680208030581c48a0041151141604c60480030750b031650394540099544841e445100400c0d0961200c0c03015240da000d005040c036900000c3d1256180034000f50048580c1e500040c5842004d000e11010403006903500302018009200300c18100d1003642100b14603a400100c0750076071720032a02001c40100300094012500d00119400c149c00010210403605082e07804101c4550213580b204c81c121040d000103030150340030b0f102c007902480c4041e0303202d0440c13442a0b07a000303c1c00c2e102000b0610345200412103180709c0d820400182d4801c0307141e01d0a0000c036a454000c00e00d207003603501e0100042080c05104072014150b900780104070920007030000500d840c5126459200d0407050394010b121074074020103e100140c4882d0542c0d035004010301450000900c01140c00440e441c0124800c2c2c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 869735566 1250 869734316 869734319
    0x1140705040510050309030403170c01111312030906080a02090301151a040f12031b0507080f2b1e05030105090a0e0c04050402040f060f050a0812030f0601020102070605040516 77
    0xc0c45003058a220b640311b0740085103001d0441d04c03200f0744418800002e080031203080064644581080c040c10120345d107803048142d2920f000c2900d42158101940000011002c00c2e092480401c4e8013040400480d070060500e100c1c562a043e1150000c0c0c0300d048280c82d01503007481d600105100b8480340c10f00c200e5140041907050070124010308050342c420761203207440702118140d05110406240c0042d15505100742009500c00003a20310312600d2206003001a90107410049040002110501c4100c5041c4400c0d130113440302000c0710516205211620000c07500381e403000c004d10f51030503006802071200282000d0410ba02040120030040c400d41c800d0158034003c07803440002c144070035441c2c0916010105208007610152084405220044c00c00070f0090740d20070b0320b5500300c90b610314480c1702d810082c155840100650505000501180803110303404002c25034845030180c00c1d24000340d4162900642002241c5c01541c0760400104c0c0640540040542030f240b0f480140020404001200010164440c0b03452035040e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 869736816 1250 869735566 869735599
    0x3010606090b03041212090602030f09071215060e130302010c0906051c060b030c13120506070c0f0203060a06091a0a0915080a0303050118020702150a02011407050405 73
    0x1c5140e10a40c084140c0600214000940c0c2d4030304103030013000314a030138003025071606410404d0712070821040d0fa001c1e80c00010711101c0035241111a5118001c1401001d07154500240070010500d000c13809030600040d00b04d10040241c1d2038000c0700041104080ac04a1424400d090b003d00c40c40350340c3d04901540c6864488401c80e03000c5c90040381150382d83d4580e6070a02120002980c01d5400035980c0043c1c1c15520680460303a11407410146006004240035561941c0e64000c7d59019400250070040d002d4440850071400034800040607a840102494040750071507040c0384c00109510086402941405104100300001410380e00c510f085500ca508144600304115144e42c40c500b0300b8009140d045a50780d074040c04441d581e50404083d08140340250a065a84c0f050780300e060801c0c089044000a89038401044040b4050900c10103260715580d08621b4504207a000804105c18851100616000400d4401059000798029038052101808041c2e13140352101004010f644a1b0254500c111014105504072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 869738066 1250 869736816 869736827
    0x30509032401030b07110a0507060f0e0f06090d08030702010b040c0e10140c01150e183d0902010f02030c0c04020d0e1b01200c1905100e03010606 64
    0x48400481d5014182d007551944030112500074450010700240c0700000a40b4801040941107036030203800902a02c40c20204010820040c200015042050840004207255100f039002c19420008661007035480b0302d1140404e82809002d0000b8100c658044100a081a0190440e070303900300c1d04076001c0000148240381940c000d110124810f40042101c4c01e985411401680f51144c4c100900040328209088004200d0a403800440c4188900c00714403020055411040c03070107900711910600404541809400d10b9586480500c11948001d41d9120134040b90410380082c1e4150621520030b000000f20240549005408040c0d42240051014088046d0152001c42074810322551440036120314200e8004200103504110440d01269a035407843c11507000d4104902000098600382d21f1000e070349490b00150100c648a4039111100c5c551050f50f000210022600561a1004650f104007040c510326a0b0640b01290360000ce80103102c0040000640d6000019008001d004800030310015444142c01c940 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 869739316 1250 869738066 869738113
    0x20d03080114091e0612030a050c1e12090f1c020a050f030705040e030c060103050d020105060f060409053705090a0302120703120f0506010e150405012a03050903 71
    0x220105070204c100c0e4800e204101c00c41d04924014810b82e82e01140c10049402c560110404101041001810802402c003c0c05001c0b4180f00c00303003078800c405c2400c51003962107a0160001481c8503100049001103541c80d000c4c1a03050940281c1441300300701504407141080e01090700d0030ba02c11440c0040c0050217142056038010700c86005005029803c0c501408d000c040c03c04008450700e640814000300710070076000c00c4124002c40c09480244101c40c0c490318003a0031510040d042ca0701442400a96001a4544c00125000c441041d40b00151903503d070f004904031503845100002d21054a880c0c084840700c1d0411103090a613504210070001e40d100d80000c603075100c40d413a0707000f0050307045440240048000040601410350007420f00c0c8011102c0400d41808070f51410003000100e9540f030003030050650744003074285618641071302c0e0440e05000400c003549540c040ca00c078540c10131116452040054040211a046900d04900d20101c004410b03c3c0181043c2c000700e038411b00a1003014a8400c0d1512039690010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 869740566 1250 869739316 869739331
    0x712050c0901030c170109060213051807050a050d09060e25030203060408092106190203091b030a0615030b0c0403120528020d030e2d0a020d0308011409 67
    0x10700c0546085c000d51801c40c0e0954100c101556104a0f12011801174001030544251080307085807194100810040001c039200d0820f4202207101003000700e841c3e00070049452260950402d203449400c85851a8090112400d00421190900c0b40b80b814100e00040c00400603090003141000c603101800c01c44807d230050740b00181d07241e444880420045140c440007440e0780e000140080e141c00301d400079102050741c20641c8a400300d03400f400402114024000c0c104007881c1c0d09000551031810050344203a66810120000310100406403843c3c0c549540030004092415440341082c00b44040002d0402c844242a12041ea29502008001021420b80500f2502501e501a0784e84503800610281100c00f9040210707a07919405060b40000c0c1030f0000249508480002503005102c0080410001800e9448881e08a041c03903018911001c00c6a80401c0c91195030b010481d00d0400f00803c1200f06c614156200102a401001d00d141403001d156200031024103a60290141e40501410203080c811151411500714 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 869741816 1250 869740566 869740583
    0xd0b180d0e09090703020613060906140d0e1903210603020102070b1e121609140d050a140709060e0112140c041a0a050406030f0b0403050c0712050c090103 68
    0xe07801c0c681441030580140002d41112421526540401d007e0f611403000030b2001c08012404000c040e0b4400c03000f00160406141c0b00321050b400c1c04607550720b0f00400741070410a6898062040c00c2c0c041c03c0103102401b40c03070302c0100d454049003030a010b0703c410000700ca00c1c080012551541981d04040707000b16400ca076410380c000c01c15103207441c2880342150080c0300840003142e42420910703051480000601400c20003640c84180038200001007605005600240c5030510041c07002c20449800700c004469100003050720105410405842c0042c00c140702041e0040580002612000001d4000075002c019984c40e20b0081000700e0b15022100301000007441000d0324071618140c86030001d4088084046401511400c41c0c0d50102e12030001002c0d1083c6800c0140b5480a03510b101c1d6044c03403e200701100400c801c2d2401c10034142552582d0308407440300f1401515104a04011904051042c001c0b01e00000148007516500380d01e07642e80c0410140240d409071601c0c81020902d220920708050064101c03503020040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 869743066 1250 869741816 869741837
    0x30b090108030a050f0c161409090c131103070305070807021b010c080c070b0a17060315130501110904051e150d150902100207120204051003020d0b180d 67
    0x104d031036510044821600312428404500007070801c220340400800f0620150340a1800c040c030070b03000d1080c001805440b91100f9024008030200105540c187d10005881c0403801c001c904600b54090a41800314211840000003045a405d41c0b60f4040d600460a0396031b40d01c00e90322803130341c00c03651703000000f680d083c05004c20915120558040d03a180180d0310712035070310f01e07050681e4642250304086890b480348625000004669a50b158000941c00c1c0601d600d101d11110b504012010070b9903408002d08a20107540c0d0a004200540884801d540c01c40d64014024489220880c980395125008201c0b075034000c030300301000b0501c0a0010f0f600e0001c0c0c40706840c4074107800d03030780c82130711800d08030100016a802c40c2c04484074074040344120030b0900480c00f00e00b201090502040c818004120380743c2a0715411900000400d1180080d00312040804030b4040714080b50b40c2d00d914880d0203203200b059100a5001100c0d42014081121500c00244108250781d00050b00c2c0c90342000998903604071300c1d02c01001504d0043d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 869744316 1250 869743066 869743087
    0x7120501380f130504050607020708070f1203050702030a050703020102012304241514040203060310020d1b0f020d080106120f0204270b04090c03060504260a030b09010803 75
    0x1001490400180042040c19040fa40c0d541100d5085d1429101ca401c420200125140c04005c190b000b1315104000380802840d12400103220a1640591803804441003010000e00d0700c10307001e82e10042d030002c0039940c050a491030040c3d603504452000304e000d035007072940100b11841e5041300003a10b505011003011041d42ca40c1c1c1d490602684407106107101c0000304902080d07496091081d070510f89052010f03d00e0103400c020301001e0300340c400c0ea10588610300402c1000036544000c2044400401c00d04005a21040301c00d600b407014144502680c036480d00310803907800c82568840c0ea0304000301b8054082c2c0d04c85104c803500445014200b40114800b00e5200d900714980004540d11080f8403102d0054010306040d00c42000380010980680c090b900c1c1920b00c00d5490080b03800c1e101c0c60b001e48008403030400c9128525990184000050721000c0c040d1541d4000040c10302c00e07001e800304000c0300c5c005a8000000d903075100f03081c00d94100819140010703207805054081ca007402c04032981624030041c025401c042a880 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 869745566 1250 869744316 869744329
    0x12010509070c06061d10060f18051507110a0b03010501140c0f072402190201031803050c0106050108130b1305060a021209010b010c1101020712050138 66
    0x1001c0c1c004100c0840707518030101d42c00d03100d90f03006040088400e2030240030007510601d0384207010300208045400c082c002c115040c0c00c50b5075000407803440e040c41c0011400c0c611424070170248603800660081742c0410b50040c8030401c00000e0041920901022400100e520300b40413504243d40104142c1e80c000304018400c0750300070324080800e0110020601c0c0341403071240389141025142d040c00c002c2030f030003c2010b00c82d403450780b040c9a030714480c00104410386a4034024000c0da55012000001000c0101c2c4010380c003075920070b420075071955000c40c2e030200301c20041e4500204554040340511145518000003c40e082d0b10844280d4050703070203c0d00c043da03a0802c544602d13041690290042e4444078640510b2800a07400380b000f944548503004d00161240040d030248080c01d131f40245000481d07450054000140d80e00301040100c001e410100704120b28001c100145e141c40c007075400944103801c8500408c0d040100541000d400c400c3c040c1c08144212011a01d60854180070700c0040802c00c060f44061011818040c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 869746816 1250 869745566 869745571
    0x70213110408010906090b06030d1b17180a060302120103020f0301021303060c0306061e0c080c0f01020c010c020d12090203190b240a06051602100f08010b12010509 72
    0x1030015440d00b95160041ea08607005090200d030341d140c43d54086424400032404503540010f09601030501100741d40c100410703103c101140092402140d0342034009001c0c00000b0121010b80c0c0c012025a10142100303020b545030381c5c1c8000301e07106045c40507000c10b60030b2003802036840c4052420440071481e421903080208181400c000150103641c03d100d00b0180006050758140107602592000a5001070000024180c0d442504000c0a00a042041d00391840c1c00c201080c2d60b240e00e6240c0460342018514002c0480d1083c5004044144102e840a0842000640c000c01d004000d1100800c503e10703101d039003a600c070181d141c21540451104003002c1d008070b03803c0c2c204280c001c1c4000d003a19a44641c8411244078150603410540340a05841c081103440064038515100400c0d2084003114960b0701c2c04009030b04180540101410003e01003002000101000c1641c000f140e4000d050300d46c400d460780001407110341c014001c2c0c0c0004079004000502c1a050300d040b500e1000042014100b00c1e0300b01408d106542501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 869748066 1250 869746816 869746841
    0x2120a17100b0f1b03071203110a05030a1505030d11152a07080a2001091e05010e03070b220c03080c0a060f061a0f1801090305150703050903070213 65
    0x90140f000c0701080240014107005115003c00d001e10f1f51a04c500070708460460b4566954202c041080700d000a4018080e0795001c0c141600100d131403065000c1448006030182d00540c0c01d40f00d00302c150340f44650081c00301d83c1307000e4101c012960104c20360322000e040158190342c42901d40440d803031801c1d8034800f0190345100c05d81424a0b400c0c500591a541d882c2c0ca40d04c059032040000d038002c215a0450341c056070401c203000749140b0091061080030b88840103443c40b094817844110b540519003038108002900001d0345181d2100c15240c4840c01401c082d00c04e45030881d034200e16041c82101c010003421840c0120000e207604688104c07a5070b4223540c4c800c110399008513101001440f0f402c110000280590040d020b024510100126515141205052040d0b42c400075282620310107004460020f07212509036142d44010500004504001710700594020312140c1015060380200c0000d18010701d10002d510f405a25281d40070007065949070b036100e07107c2c094103c000398041c400011000d0b0701d52094001d6030f080100d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 869749316 1250 869748066 869748097
    0xb0106050a02030705480906030a05061501022103040b04150c0e040506060a0c0b0a060e04030504030b0610050a120605040e07080c0901050a090c02120a17100b0f 71
    0x101905c3e450301e4030822511202000e15000088200b03414440e2840c1908880b1004032030380e0340b654010754580500302c0c18003d80259241030000d805680c0030013290094a4018059801908148480301d42864041502a003d8070915407070342c020003440d180c00c025015a568290381141c40f0b9a685003c00080034009650001c3d49000320410040d4502c9480d061f002c107605c4100e50030900708180300c188d4800501062148a05000303580301e19405c031280007012540444084607980e134a00b15900205505c2c1c11200c08810524200b0013056006030061003600d00a001d4414a99684c1c020054480300d240f0020300080c4080c004603032030740d0141080c500702480c814004100310f51104081421601103441a0409074400d8100700201c59003400907654480c42580c7d501c1a5604060115804080c2442042182603540c0128103006100f4803400703c10f403407004030342030391240c0342d05008103203110480d48500300d480a0380118982d040e403400c0c0501280c0703071181003a0400c110342e1921a0590041080f100c20b015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 869750566 1250 869749316 869749327
    0x10629120a1b080604060b04050a03060902152d0f0d0905010b030f1b030604110d030c020402030f06010e092a13033c0b18010504030e0118030b0106050a0203 69
    0x11000304070b242d50300d60719580d11002403030031104020580345c00350701100c0300400802c001d0000c0e0b100d2402a4040e21b0700100045911900c0d0310210b0301c1850001c1410f1055500803e112140c50307040c00c94400150701c450b00c40c048450b4803105580c1c2c144100820807032103810821012409800030380103d03400743d00800000070054403a074003190901c0100100c00a2940000e954070105020b00400c200e01000254000e00c454176041d076822101302066a0950710403000760390700300d0803d84070707029682c0229805030003503489040800c0b103a52240c109841c03040c04a940c00c00310144034200907041e80d1080b16402000c0107040410045801144001541340440c00307010000500da451a440030b100c021407041042d607400c4100090f081c00680001e100960003002e12100e030b1219600a14800c0d0055604812028070544498114121450354181c0c0c0a04070b500b804200b20600d50000006000c1880a881ea07818040000301c2212004009000c0100740800c1c000050044d03900c600d01400c0e1680107070040342d1610 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 869751816 1250 869750566 869750591
    0xe0109020301090b060a0e040b06061b010204260a1a07051e03071e080a020a0e1c0201030b0d1a0402061303110a150503130312020a02010629120a 64
    0x43c1c800078800c1e20f0002c428018805982003482c1e94900038019110141c2040c1081d50350b94160b810b0141c140ea00c0784001140040c1c5840c51013400442c0d51450000841d9515a81c0b49072202500210b018521000500ca0640e00a6000810090440ea600c245e1080c1490841d03921120100009411313841000800c1c07181c0340c400b182c1100c0d40001181c01b55282c986034501210f00405003031020300c5440144003460f40b402c500715001107003140c1006800d0707009621038001c0d044c1122403801420b811f940c45801e454204000d80b0b20000e4950042e4000e9a01740903000704601030020145450400404040c2c507958030104d03079900b20044a81062009214502d440c032814903125100070715400640e110148000081a1450800e4101009000303002507181c00340501d400240c1903004c0203065078485202105600c040512446009000c1182e146007107446201c03a4400a000f03024a024242c281c1a02038405000401c07a95400c070b2003030b01c0d09407045113482e10a42002208031005400c1600b0903031200300d130440c0e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 869753066 1250 869751816 869751821
    0x6270e0c03070603021201050a1206051312080f0105060c07060e0303040509040c1d04030e01081017011d0f030316050c0321100302010f1404092d05010b0d0e0109020301 74
    0x1411544d6000d41c54400740e48540e012810180d110301d2150600700e504000544003260f14401c01600000e00140640d03a076520841e00c04000700d0010080b138501e042e080d4495400c400102e015250366486110303641e0f203840511246214084418509920010f41005000e2003603000300196180607060b6402e00fa41ca0020130303012030b0181c0b400c85018001d200140720342540300e1503580000c08200f162000310304103610301402c1c40301080c20942c1000715250018108442d2111100002c160304402d00f8255490f040409000f01000094a0301c8010548803c0c54403503000110384101c3c542042c080e514640350203202c40781c00740c40d905c16072092120606c6a0500761000b072000e05030300060710f0013035080100301c0d130450020000300802c84400c58101d01800d0000d43d070701c228440409040d030309010034217401c80c030380d41c40d55805103a004d200914201105424200e4a40c6030411040d5944090488480244a8070070b0685109000d0070407010810b0280005200c0190006007100e900309000240781a480c2e00401d0a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 869754316 1250 869753066 869753069
    0x16080a1e050f15150f0f2107020114010e060d0f082101031505060120010603110402130603020d0e0709090b0c07051b0f03010203040308071e020c06031008060405060403020106270e0c0307 82
    0xa00084021508847d0f011042c41707035000c4090f01c000c00015601c0d8404125100c0c060040700344426440002070841e4a070b00401c94010390300100b03071500007200c1d40f40280e00c590002c029041c2c01000d9264040390100d00408040c11b80c1e602001043e10400100100030080030000c043ca810401404202802000e140000040d898881000443c0c101d088d0306000e076009940c200d40394000c3d4070422288801d02603085038903003514507605c0e01690b18407000300170402401d02031070040214096443d000840826540c8140c400a11403190015281d96249c02c141c854001c00c0d038090115005907035100f1003111034244291038480010200142e405003440468220f800880701100403d1080040c4a4007d40003201e00081d01c807645041c1c84a80d80d501002501d402c1c8030410540640004800b05451041840010303000e08101d500301d440b140b4040c10415034840c5e040d1001c0d005540380450200300805483e05040740000461904520303e0500c121310f600500b01021020b01c680640115031480d0f6409008000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 869755566 1250 869754316 869754337
    0xc04020d060312020a05060105120c0d02060904110c100e1506010207030c0612110a02100207020a15091a09090106180918051516080a1e050f15150f0f 66
    0xc2c01900701e01e04541f0b0244103030440d038403841d203800c2c00d03850f5000009441d46c0300c4a002d5a00022036041480420300034040c15048a600070308068180c2505c641076000760169440310003c82e04030207003440724601212003880c2c2c40803081d0400100151000c04029510740c2100040c4100c407021a601d403034840c050300c0705800070b400003180304241c01c40c6200280580300e43e8402030903200d071900d9040d20340a0340d10811106411030440c1c021990006561365100550004c144461021409404076880286050864041ca43c91000643d015810100c103c1041d9008541c0142c90f190b0140d090000548003411001908407182801e2003011a601c075460045031440c1000fa50040d1918500c0d1034a10f061552060500a00e000310804004090310100309165410f02c1a0a00205c541c0350f0b80380800142c049241301c0071404035505c059124040c21940034910030701070464110340e0380d02c03040450405606850030a640c8840d4a000c5d41e980544904000c1c1040e01c6c486158a140500d6603140c0700c503039002174030883e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 869756816 1250 869755566 869755573
    0x1e04060207020118151b0501090c0e1012140102161113150b070203070801140f13050a020f030304091d011d0303190603081324020c04020d06031202 65
    0x1e400c5582201c054030703120809002000c40300f41092080d500c00d20403800701c81d040150302d0001030a0b0b540710400b840750711508100280840300d81402e00000c0071415208801006044000159042c034035a2601c40c181d900d1903054216580c903d461707038440c06130302c0c00b0064401d55003009004038164100700c40300d00c60303440354868881980c004400c20004241c001106062242045100e800c0c42503004280c6c0d00351000c4001864941500b400401d1418000d604403841e10f618004044c001a2205040e940c0300300d402c2101d08120707955800b50449480a0f041c4020301950080c0711210041c07816840d504002203014007104c0c10300341c2d00c00c1c1c2d900603500c800800381e02c902c0254001200300c14081c0103c0c1c0420014120150b5880307031480c072250741c0340320050802200307a03810318a10344885900c0c4c011100441c0c1109009440700b64804400000800d28480e510561800c03e005110703111400c1c49000586200b80c020b0444155504103100c040d61100386062143c0d40d81f03140c04000140880d00c80b040180f000c0c1c6c000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 869758066 1250 869756816 869756827
    0x11818050403030f0207080d1a330403030507020d08190c380405010f0203070201021908010605070b040813030f0605060f090402061b0106060e01020c0d02010c02091e040602 76
    0x74007103070f01c4800c403601301900400501020400d244101c0302030906840e8002104094540c1c02c400c640e50760400d03154024101780341d4a1462010104000070101d902c00000d1038803000c070038151a00d1046100040c0450b40c20b200400c007503e800803821110900031071200c2e18000c0700300c0311404c061803d0403840010074500178250341404615000780b0b1880c0c14154010103031802c0025103020303000300e0f0700b4680c01c00e501d81c200060030040c0a40080489482e401c6044d516030905e144081d010350010340342d02000715602410504500c0c85990100e04071440c0d40c8030b85151803901e84401c84800b0f0f0003030090b0b0340c00404206100182074200140c00040d801903012030809000c0e4a0450140e68010f02014401c0d1982e1520442035903030001c6a507005a4110390143e80d40008000541c1c00728203c01490f5070b25442c0440008000c3e42007805002c62250036800d5480844003801045904881c21001034000350640c1030103001820709856403034000c44030080300c91f20307442401403038254140100c80c2207800302d402080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 869759316 1250 869758066 869758073
    0x9150f120a0e0601030209070512040b010312030504121409060c010507140327010b040614030f0303100b071a01120204060b03041101032c0a0302060912090118180504 73
    0x58109003040801e00400b081282803503580c0c601800301030321500703d2001240070580070344210340020101070000d200314601824901c114071400d01c0152041c0d941b500403410414032920800d0b2285501c9146546010801e22080310f450341000740c425506082002080d169a841c2c001518100030388600110f030914200c0402090850b14030510040d500081c0207101e4440d02c135040440901c840710304005409400c0010702c43c050800c114815400900d0f00c000401e60190b10311501c4403980084d0111409803010b030300c070703190b9a2008480b603041d0f0b14440801030000021b441e00502c1614000e00c0500d08558030a040501801003e03400811965152080042117007400e00036031001300082d00c0158214540303a15001040030840c0b104604042c0d54102d28462440c100c6000301e105078141000c07a80034410307000e6881da603454110095015118000024204407000508098100c02d030135a440d09244a030070054505001e034290740c0680c140013140214500c18084000802010030308030103e1181010304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 869760566 1250 869759316 869759347
    0x6040e150307080d0503150d0f0204050606070b04020f042c0c0f010e010c021c0b090709200c070504050a14070e0a03080f190c1106130b09150f 63
    0xa00c118007a030001c15081111941c0800c810f06815000c1c205965030b5036401c0340301643e200301c3c0c45070140c3c03000038040d05106100071042e1078000c0030f209075020065074907006c00f0044c6038003a2042c000c1c90713203604100041c0141005030840106900c050400704600444031002d502c41140c1c2c00c1622400c509900360a00b00860400c07518880c40310030f50b041e07140c0001c4040024401d100c200c0341c0724180b0459102840440d02c541000300c1c900b03880b9003940d1081c0c01c0176140c00d54910000ba0341b890143c1c8078182c404901c0508921800401c020502c5040c60005200104982e15030461f00307500c0d0080c05588400146500c4502800e44101080c0100155130183d0548090410b04090b01c0801042900e0588035455182d0861240641c0e8000380d580b030300ca6050041d15480b610624804c07901311100c040344400c2140d003060750304480c0352040484d501c05080e0300c1c06005483c01185844043c0500d5220304210b0602910020100c0760805801c0c0480c0c6806501110071a07841000c0c030080300200021030810502250 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 869761816 1250 869760566 869760601
    0x50d0206010e01060f03150305061f0503072405280810050625020d0c05030d0e130b0111060108071701060b07032a0b0a0c0305090717030906040e 64
    0x352928900b550400030003c11a03030182290b02c0c00d16039910450f4030014a0560312400540c0c1c0030b811134079540b0307015200c080381c940001c1c0c24000e00d04000c040420103140119070745058802000110000b09a8036003d0308000c4400000942448004c121180d40118142503800042041014000550b80a082c00402d111801802000e0800040c2c07800e011542d1418100d81c3e6041c00c6030030302d800c0100c01040451616140b60320007503001311403100a00c1080162101241165011001d9401da01c04104041c2d4400710105400b40e40646070034110038151030030741d20185000d00c043c9800c440390801000e07071501c0c040c001c1c7c014250076440303490108001205005074401c00c0c90302400074007615113043e0382d1081c58018144010184034186044e41c100c8000d01089071511800c4c442c1494000501d03040c10307084490140d8414100d181801c86106083c4d000e0301807207009000701e030000d040741450603035403251205a43c1c0000540b13020801c5206501c0c0da50701c01500181552170602002030a22511b42c65041d200e9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 869763066 1250 869761816 869761829
    0x118030c0f1a0901080403141b06071b0506131a07021605040e0a021e030604030f09150c1103010e100b2701150c06060602010c2706111603050d020601 66
    0x10084070703005985c0181e40d140c01c130354075003800d1010300030f10300748014103000716043d0310140100003509180d4080001402d9003d1340740b6480c2d540d14817841040c40b48900c8050840a04164048800b150107240302003002c4c06c0715070041a02e900925411500380c40c3c0e06405550f0407005900c42d00810080c03605001e5020010301c001c0350100702011101e000d0355241e54403800081c4c419045141c5a50700c0c203142c00d80c01d030704143c402800e40e1103074a840c2c03038041c1400b50303030401d010b00040340c0400100311814120290384000700e10b0b480d02148061280c1d50314004036140c6100e103415540300d29507442e42e000704022680c05c103148890b0200746100c105061110148030001c60158440500c0e9401c0c90112030786c2c2c0c055042d03500344883d01202040602060343d9001d442000200f00f11b241c018006101e60b03040d8030036a082c8441d681d88d4890304902c0458103449440b40034090302180c290b20380801c0054040c803000c54200c54210140d44c1c6200f46e0605030b030400c1c0c403603038820f9171190012041c4038042c03503041c001c3d240508034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 869764316 1250 869763066 869763119
    0xf0a0b030303100509090c1c03020609060105010c060209150301060c02040b030312040b0a0e1204030b0a0c05180409061104080f3d0603030f0e0d020306060118030c0f 73
    0x1408540c00221404a1013a107009243d9a00440d5042000744052480440302a1651810204c503c11240e0f04221755501035005020ba440070941d0228042110b45c100c460580d500800c00849403149402944042106a4800b00c2030b8004c000c1c46a62030040c43c0200640c1e1034190780c4a0302030051009881c1c03007034180f9110390030401c5005140741c0049034854210f40c11665070011039543e40301c050010041011035564600c600c0403a00c3c1d034450701400070000c1d41d10601d600210350315808050b005a5040c840742e400802c00600581148040d0044003080300b0038020004141201e007a11100221040034038a482d440700c00240070300032280c08120104084260700c00402c04004821500b154601e00001c480714210701d02040c0d040c014000d8004a2500350b441c0804200c0f09541c1d02e070207095414464080360204145034090891071404050034082d007030f00640a00480d54410300111101d403411180301c030030041080004800700319083c0c1b005001c0c00d00d0315041c40e11942044850705600b903502568812400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 869765566 1250 869764316 869764321
    0x212090705132f16080723120a020304120c0905010605030f06040c09080d0809071d1503070312020a0201140f19020f1009120203130605030a140f0a0b030303 69
    0x180040e0801c103600b80c3c00d00162148a000002c2080c6214010001e0000361102d401c2400b0300003505c008181c4548204110300d00c40003202c0c8000384000022054410540041000350388030302c1170304001c01680c951031066038075007034450382103c010b1920320900341d03007a1208407020300c4032851511035035025200c94108070381940707400000c0c550445030043c03401d4000c41d02c0e1181c9901681c0254140705c06030030202d0603118080c0d074500b8002d15000c0b040702c42183c144107402c0c1c0014001c100320a0000040c50600c5114000d940b44a2641e9a0010204540d1303058441d8910000101c0ca9020509400d031180c6d42c0030b80844181c81c0001050100d03440302c192a480002c0101e68040c085030700403500000d4100118071a426000842a0f08110300581c5a207001d01031303407552022500c0558441c601891007102210a001c5120301c040340e03a40030f924200c40140c00d03001e100384055405200610b503c84044030010441c0c13104001415005c0e04c1c00d44807844035003484002c0c031030800c850740105050348100b80c00550952 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 869766816 1250 869765566 869765591
    0xa0203010b04090b041b0e1e062a1c1806121a06221e1205030403050706030b1002010b0a0501050d060537060e090604021209070513 58
    0x91280f0b12070006210758964091829840d41d800c01000b141c6019140882c100b0a0a00a04001c0c40c2c0301002c0e04c2001c20301401c180b51545a00c12002d1808003030711807030030700c4000c200c0d5820002d10140380d0150080081452000304204000705400203080804441c01c060701c0a40140030080710104401121410180601540f41c0c884900b6001e8000180c011840a01c110000c4243d44904c80085402c00e40000b803000c402212484032030100442c104c0e050110a90f1615080c1080050710280c004945180004014080303603442040d029034010400d403072600c0d68a41c1c6551800a085d405003010030b403a200084610300d841c611180d10602180000c3c00800d04000024041c0085402001d0611001048005030701560b580f00c103000c0c05010f0212031142480e1044501c09040c40e0381c1c82d10b080c038003a4007002116464001c10300c003168416200d50001810318000c001046400809031504950f0910116007943d00c48030010f40541071003006012214200b10510004418007216020802d05200444602 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 869768066 1250 869766816 869766839
    0x3050f071a160303020c0d0905030f01110306120f011a0f010c0c0603020a0212040807080c01091406160f030906020609011e020304060908040b0904060504060b030a090203240f0a020301 81
    0x3815890001642c98118a140c10740084c050050700c140e442c4a58219112990740250240003603a40860032140181419003a690a9880c1d800040034030031402d002241903820b00c0c000c00808000500c00741e0708950400f91620782121101c03a00c5420500b00909007a805040861010134502406c1c1b03007080c80200a5141c400440159100710420581d00241c0b80405c20f1003400340800d0140317030340b01e00340e83c0d1540c0c3c041c003980c0c1d104c8034000c1c6c410038000d0401030241507020b40e44480c201c8844103182c225010740a0b0800805400c80300218046848010001000942c006107541c5114400d0302c03090000e600b0200002d107042001020060345038540051042a0b808400d00500c050160100c050380e295901d1400201030000c0c50720007080023401180105030261500040c0840320303004d850402040381e960302007109407441071041542c6518100003295800a080d081030a4040c005011a20414a803d420309081d4170426900d0a00540c001c003401403078502e041141c1e4000161440035030440d4101500010f8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 869769316 1250 869768066 869768077
    0xb010503190b031e01060b03090d0c0c170303040b0a0b0612090a06020c07060f1409010c0204110a0c05190525030618150e061305120403050f071a 64
    0x244110348000031000d03100742e007102c1e50000e40a401da8850340103100c999041d070070402000c80165402c004010854100c14402e8911820310400104040d076000c80b016180154012400d40d03d04480300408550484045100d54000060400850b9285030ad41405d5150241c054941c002c400c2c1002c81249107a92000b090381c02582807200200c4c0036490721803245260554241c4014403440c0045445201c0c4000412040102e80c04ea0716075400d0315500e040308440c1c050044d641000d0020341030003031122551048a002000d1840034200040f02144d038018003c0c0760704800e8421000812140362841006014407014400c5003d21004a402d0440360713584a48804a10000c101184075056201804008800724000156000b080400c00d840514004070400300075190140c80070a81048206143d001c0344c0b0400c641d01e440078001e002d890700d800030003101080300e40106441511841003015070780000c2c14014001503129100a041c060b44141440e0b04104407603200320446071b010a08400c40207240c101703c44 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 869770566 1250 869769316 869769331
    0x1050a11070b18120607080a27080405180c0304060b0607020415090c0e0315090a150504030801050306070e130213120209101206090c03050d120510050319050109050a060209130b010503 81
    0xd4149c190816a0030294400021f400304842d0308101206028450004200380c0740103071440d2441001015204180e0b817810350780181800420400203006c0303102c42c1d1249964000c018002c2e1724201d01c42d00090165003c880004080c40003501c4100103040651003180d4010000e030038150540b00345075001944074810505446104004000054100701052094810242d0720400d00d564175808180d11170024682110704801103000e910001c9803520300014114400c541c1c42c1c1d03400540301d5500f41801000c0c103912206400c0280c09200b00401504200c0400c0090442c40c040315006480c940100700c400e0070050f2232483e25500306002404820795030b06480300076075000000401c5030840c611f0300c0c1458605a51003c2d046d40104640c003000c6950114941d1785050141e1010322464582c003442400e074102a21409074564480103078a00d41e40e11454131894018040d1000040d82c0503a900c03100c1c00d00b07215682c200c031480c1e800a803001e0a0318041903e86030340725600e5001c0141c00500000640144006003a00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 869771816 1250 869770566 869770571
    0x180f270a0c0216030b090a0219030201090e06090412050c0d1205071103031501050415050903060a0501050d02010c3306080604020a091802040612110d0201050a11070b18120607080a 79
    0x41d1103946c0c01c104803204280c0c00381c182d51186445d040c3c4492036a00502049000481d00c07100003648030545542e4501604c0000d0030707544581c546a40b84c1c96041e955940280c140300f024030500821150a02114a10070f500f51110324081580c01480e404460b4020311130000d00c00e03008603e10083d07034000192035021445078242c182c00d04a003401601c0c5401550b101c407502000031030107110304980c880040d101469040c2d044600e1900c0e80308000c02a03c0003401081c2d0400e001451f00809907205140aa5503a4001c0720203480018036102112000384030880c07480e030444000d40e101d60b071020740ca10440b0b000f0f0500c41e02426003401d1036400928030300006d10a81d071300a92951413640c80c2100e0301c2070b4444420380c02041001455900c0502042c01610b4070429200c4c20b4003200048900d09040903150082e5074141c0d100c0740340681e03410f4243ca12a82c00344840c440c80c81911030114800724440010900d007120203280700380b480044802c01009060345200554250855024055030740d401a21854000b010020007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 869773066 1250 869771816 869771821
    0x606031b0602150906010b16060c0f0305070305062409040608060105030d1701061d0306040c17030928080601080a020907020d1d010c02030105012603180f270a0c0216030b 75
    0x29124610009031016042600e04101e0051036074100c00d00bc0d4441803991030910195072240c409400f02c400450b0f4594118000c0000303084150880a001c08403002d030180010304205000000ca001c175841d5800c00328003503001c04014031161400304100e00c1e0041a900d40080e66002902c40d00c0307130f002c0061140c1d84c140701480d081500b0594081c00c000b107088034064210340151402d820203201e606a01d02c00c00e94200111138031034920440c08021150303c0000680303500d80d62800c1c0c0d0110a0302001d40b80d0507036809140c070440850512000d01c1058002c00300b01c00180480c0340745004100c0d81007000f49c032220179544100d8589000541244070901d070b140c0c913070218440b00c000b40b1005a4851321070303000080d8103510301340c004240c1d40248881c3c102008161030740e000a043c0d042c2c201c50ba480c8220041c02c0442c1400031800750951904d030440c0000c4c1d11025110501c462a03000031075842c1c4034011840c0a204e40190104103001005104884d0150051f00c000d0401e0003201c0c20010368007080d800003404c4008001d00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 869774316 1250 869773066 869773087
    0xa02040e0d051e16060501060e03031e0a0c021c1506141504090204060201090c060201020c0a15060b210708070504300f0b0606180d0606031b0602150906010b 69
    0x1581d14200da20304d104516881c60b444e00303a004002c00d000c1c12004c514034100968240c1000800d50b1101698554581d40303810b00b070401c200250b0031408001007080340728405040161140b424111a4648102c141c28808003646054170a45140401c8041d40c1498441e0420030005400c00c0404030440036920722a6044000307011007082c2c4a00e0b00001c011034000140041e02d1507055101e9121140a550b451040641b5803408a00740c5c030903100510740340d0b0b112140402c045180b8200300c40c07001d040d60b10001340309951003080c0025600b2004800701d03141c050540c00780c0310101c1aa08a5070040c0d0525241c81603141400000e0b08500490041c0311200322028640402000c048a80c0701034a8424505071691141c0b9180ca0643c840c48000102d40d412700759808140e050510f84282e030b204841e00c049104a249801d42031040072a18054180c52041d03da140000100f10002c1204010141c14507030300d54158103011002c0c0ca42a8100f4800e1580350000d401c11003415401716010341500c00c03410803250365482d80700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 869775566 1250 869774316 869774377
    0xb0106051c09050a080c1f02030103241503060f0b0a0e0703020a03150f0501110303160302181e180c18030f03121503030304020a06050d0f0203090a02040e0d05 70
    0x1310001c20448000401d945902400078031800211002c00c01d00c2e07124a2407102800a9010a100041910f10112070042021003000007848503a881c072540007800446260490380742510a0344291541d50f55200120b131030f41181c0c0190f149000c0d0540360b8280c52440d1004070030721000000c140c40c0803d58089076030001d49220360088040913030314106a2076669210080c0207100076440c850980400e455140201c12288084242c074410105581c2808000c9075010003a0060351184a005c1d09028800130700c40346aa864400400345441d50003480100390400c2c2003400800d4524410038001c0c00203000c00c111030300483c44101d4295000d10301c048407040502401091a0513100c01d03079000140004210303070b01102c048070503440c4a801f6140b02c00140910340c2c024161a48029100650401040d502c00e0000303500620003014094040f150020f12a86e02d0103c00089030401c0c0c440c15419042102e08000b50b1929008010030307000203401800d080c49045c240940288544410b408a2106c4600480036020140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 869776816 1250 869775566 869775583
    0x3081513051618061e12020a081009150b0f0f0a031b030e0309040504031101060f1a0306091b0f03040b06040c08010b0a1107170303040b0106051c0905 66
    0x140d6090081e4100071441078400e016030a00e6500091031450003024600760038010344216101d54840c4503004000b40003000d041d02810808100303014900c0051060100c00d44002c01c0b0341950750b40c500055051a076091802000b856200d1400c01d42003ca11981c502000301f900001c41c1c029081c02c0b962402c5002d0001914055441c03180708481c008150f0382013441d01030f00400d081c0e420b05c5035904d2988981301c0c000c0d0211000380410784c640354000d1009078a5803c113176000783e030414000e003800c0042d1260455050b09582c459004021540d6002c8070401051342000584160645111000d0341145485408035508882c02402c11210568000381907030003a9182084903949807940c0d009540d06d00d000c1c01e004070080801e40d05140114a44010712200a00ca5640f0354180c54001c400c091400580201c1200c040e503e40084041e00d02072450000340c01130b890310707c1c2c0c08030410200181d91640743c941442c1c4225241640014284503081200c4c1c0b10502c0303202400c400001c003e0100098520080c1822827810050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 869778066 1250 869776816 869776849
    0x209030c0d031d100c0212010b03010615120c050f0f041e1e05030615040b060426071202062b05090d0e0303041a070606240c030815 58
    0x1e081014040c0340d40100706038560080880e000842158070740030702140b41c04210103807000882c118413482c01843c00001c20394250481c1000031512081c042c0c0000e00b1500e641c1d02c02d02000080040c016031941e040001990b404034074000c1041942101c00c0017820b01d100361000c98006d4140090946055041941614082c100348890103145c0d0010801c40b1807000c0b03050194036246001e030000f2451080f81c00380400140c3d20080c001e80219104e9101c40c508002207030301502e52058440c1446a20383c0c0b50100500010724004c9589268181c90002200c40c09000c1c150b004c4807900501402d0042c113541035040c1242d03075030544c2c4407955410f55500d010610300c0d001c41c4e8581e18000d1100140240c1701c00390030560080c1c85e00000d580c542d644030041902c4c000f00c800d0425406410510080200145070160704405015502c1d42610303107a81a80c881c012202030342c010b920a54460101d81000a8403204031002c0c0503402d04101c1e00407505c0d42c50190210100414010342c40e80b540c6102880c03525103164114040c1407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 869779316 1250 869778066 869778079
    0x1e0906090f0605030c10120209030316060e280c081903120b09040f17120f011403060f060a0801021201090c0305040c090903020321070f0f120209030c 66
    0x4036095040003821601140301c0301e15040c428080b90700c1c07401068251030b610b002080072180080b082019078004556403d00c508041e800c0c0550341b80c0741c42c10300003800403110800c40310061403250310740784046130181c0b204490180c3c4013072038400c0340ca40811010302c521000e4102d4040740c4c000c07500e0110b0301900c150304920424064550701c0c103048680c0d6034580905522940b15260480d40b1203c011084440d00c0c2c180b254084040e070045800f14250400c86001d140c0140b003e080d4440807151080010b40c0203030400e0000803210002c006001e143e112201d03000d07281c6001000b81040c02d090000781e0f15400074090300108142d200101e9140c0d6076020a1000803d6010002c2d5240c941aa0400009850900c6000f0000341070403804245c0310700c43d114241c42280d11544401e03082e0704104000004041e6050205c1c10751000704611112004840348083c007a040441d01c0c41c0309450142802031074207041141030414010600c0340610843e4001e0b030040c40c440c3c82c4800051319401c0681c0064a40a081c20b016170b007120 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 869780566 1250 869779316 869779319
    0x1021303031707140a120f15090f02090f1207080601060309030311030103021507080d0207140c0f0616030c02040c17070c0201121d1501090c0c05071e0906 68
    0x103420600242c0e222082160341c0074507a4582105a54007105121201040042080081819401085003040000400f030002581d020044c684100311402040008401c80e00402c1c00c21045104d4000c0c803090280c060340641c202451000407401e0b0342c07540010980301321158086514180c2081007107100502c4028200c4040356501c000140041134140f0f0240c00080c1005c1c45401185030580c11207040304da000d05801c2042c0c044428030000398200340d008884218003000001e00360015400a0130030240a25941e802079030061201c0b13490401d1421031140180440b5206212951302d51040d146a42101420561501d00520b0b0490780780e462200000d52061410000568241c2e0080e00108600e1481d0181c0165840d550f000350740350302c00c0d002c0080c0045d90008100040030843e0b0061400380c02d44c7c0d00c0d04003011409040503411702c00010960080d001c00c0c403004008003400d5015940e011491420150010a440d8072011b80750795180c0240180d204803401600142e404480840340240b031100360420032507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 869781816 1250 869780566 869780573
    0x3080c1609050603071205070512150405010c120507211d0a0201090806090706031d19110a0e1b0f040f080706030c020616091208090a0f0b0708030901021303 69
    0x103120070303185a8001d100d00e40e80400e4a120f13414180c4170301ba82090042400d1480d0074100180c00792007525042e40c17030007044001e24604150501d500e004c0c510610000c250b60343c0403000204409100841c4450580c205801c2c0025590401250281480c5e1000b9118060b011218444003070010b550f42e800e410f03c0702c4041d08210010200785403024500c00d81e544031b142c654a50306240c4d10340d42034650342c800342c1050303c1c01c11455000780e004100141d8038540750102d0004045509042c43c001360b580d03520000140800000300304403640d604041c4001182c0160040e400c0000c076045e0100010600150070200062400a011000041d03801040c110304015658949500010004201c00d2041558074403d02001054042c01707405181a0600a40d0082071607076141d007602c0c0e02040c0c061a100080c40050000415900348600045d00d28602422241e0303520401034013842022006036000c1c800a0450f41303030900c624040e11088541d115000f0b80a26100d44600d000386009108034481d09040b03429241001040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 869783066 1250 869781816 869781821
    0x321071b0c2c01081c0f091d0403022523090c0a08010815061e06180909030405090c0717070b070807020f0c060f0c0d0e130c0903080c1609 61
    0x90074002c42d640d41c2c266070304c140040c2d4440000d0f2668281034901400f030345032203101d034100c0c04d20540c03a40f4010100d580c1e40c05140c443e00300f5800194501500f25000c20061540400c424103425060200c0302d50300d203c6400d5514495161800348000c90f02900709142200c0002640c6090030010040200e102e50030b040d8000c1c4426070000d486000802e610400002c1c4103080070458680f242142c56503004155141c60070000c0d2450043d94010400000384039510040d1541c0c0d019041d016545070541d043c000d41e0808000d8603000081c54a0350701e0703104020504c0b45d07407030384038216410544003c5a0f07515003a0328a00384400200200c00341c00c10300004640300c01407001f208071280c0694265100c10301c1a4403020400ca8803800d003a6018502c5512040ca45462402c01070300801030031241c100d48904240810b50345070305000b116603102000640222950b0801c0c6007440480d4140829000100003541e4800000340c0441020b100107407481c0c501003103c00e9032980a00240e2507804001d10124002525002d58100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 869784172 1106 869783066 869783129
    0x602010b2d150c0f0f16031a090f031306031416111002031608010609140910080a0b1017060a0e0703020d050321071b0c 53
    0x1003440c014040804041031310000f0300f42c400344562001e450003110136050108910744480400005034140b9030b102e0035413403007581d1807555070b81e081003d82400641040f00e40710b400300141c299614030b05028800300751007158804000d90041c0901c070884501080b5050409901d00381401e00361540611310f03540c03640d02c0ba40200c410b241c07051258030043c1d8009440d040311107140c4544191150b40c100312903501422261810003100d516050482e02c0156207c24154051150180440e03600f51030000300070080c0061500f2180f0054030b9140882d100305045440c402c88402c10300010446c0440d14540c0b40003100040010f11280e117401c1d00d0a0002d003491301005085200d05440000161074410101e02c3c060b0240015648901c17000c4044134070411510074801092861004125206400c090300301c2c1da180b024200c8680d0f100c0b0524040400c11101e400404440c03400c56001103000941c18110769 = true := by decide +kernel

theorem cover : BRFrame.Cov 869604316 869784172 := by
  have h0 := BRFrame.cov_init 869604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 869604316 ≤ n) (h2 : n < 869784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
