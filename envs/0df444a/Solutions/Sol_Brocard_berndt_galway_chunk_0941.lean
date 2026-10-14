-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0941
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:18:22.267748+00:00
-- url     : https://prove2.me/submissions/dabee847-0d83-4017-be78-e04faebd9a89

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 169064748 ≤ n < 169244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 169065998 1250 169064748 169064767
    0x90609150c06010602060c0406121b1211070f12020118050102180438120106050a05030102031006110c10020606040f06150513050405070c050c04090b010b03071103 72
    0x30061007107030281002d541c41070766945401d981d544800d075042403201000b03020078480144035280c0001c1c542e032030305808207102c690717462418000d408003c40c00340000c5868150352940f40d858002c540d04010507003000f500e0207141d526007c01c5502d0740c0034000c012000074098124028402d400c50111003074411032007891031a0341c0c5040e034000c0d8030200d4500388101241d101107101d844c0c28855000c0d140114941c50014041c000820301c84a0460211041c18910440392802d40341c030780c0402881e0308603072040006151802c100070050004441d500a520981c010801c02c0380d0942040c034120111803007030520803e021185141d05080852083c002604200a43c0d01410460b50001c0d04500400e0700780e804100007115503100b201960154050440903040303804000184520800040038078148003800f1183d4540c40704000380c240d074000e031090400100c40340741d1001480070030b0014a0400104640401c200c005503078420f072a030711052141c020803582c040b00040340e041c040c80344a01d00858490580e6a200400c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 169067248 1250 169065998 169066039
    0x20a0503040c050102150c0c1e0304030201090803180d03090e0705030a0b010c031d060c0a05160906140402030901020705070807060f03110d0e0a0c060e0108060402031b090609 77
    0x8580680e060305402800003030f02d5001107140900110107480c06049070740d4140d82c014195000c2140260f2600c1401142c0000d64100c4039403400c03d08190740a5980d440c90340c00010311942039a0490711b0203400c08c00603005030ba83c103400072044001054400c00315400c00c90a040d02c02c6031095010301ca9400c00344041108650744480154410404220100000503110b401100c0c5031710b092400030f0208101503080800c1380e14503800e10700d0514000f0509482c007904403895038108003060340e00300c039903610803c4a040c1f20385510120401034442d403e010007403686044900695000d1070310b5424003e03a8004040707034480000390100c03400a03800c10308840300d0350740d2130a81941e120064440d100c00207040315049813030184280243d02d000705802291030304119041d09070308001c103040e08010f601441003040e850009080c80b40700000404035600d03500f000040810024254440003401c5901c214030400030031a00001d41c25000003046003850019031900c1d5aa00400c4031481990139a99008507640406c0c980410b05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 169068498 1250 169067248 169067251
    0x708280c03210507020114030a1806020712110d030c0302070209040f200f120f0a03031418030307080403121103090c0a0e010e0a02040306020c0c0103061517100504020a0503 76
    0x1881c0b058003030400c00340c804a0300b60068010003400248a080c0410003026030034080c6410102071080010700d5070b0510111001501140030131940c450300071902d1004d10003070390354096000c055400c1c801c0c085020101802d0300d0b0407441411303805150f40c03450060042440380d819981d0199010b465015a4101f504244001102d50501120510000d41c45d1b00485410380405403010f0201a148071030301c3e9108010054031140c0465500d0180c865010740e83c070400f80c10004151220300035200002c4ea91480d1442652032500240b04040c017010b20700c0c3e8410130f401d0000840e6403100740b510b4014555200ca20b41103c0118540ca4258049420800d440c40d502045c3c200642c020030500c421203ca00c011031003071040648240c401d40f403041001c03000400841c50740c40300186d402141c0b42c00c0145000e80360f5441c003040703170403194461005a00065500d00d182d40c040c45048050f00c42d41600140e000d0f14504d005000b44000391006510034000e070080740102c410003540c0005400c000b481503482d0902c42e40d009003c0e410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 169069748 1250 169068498 169068533
    0x30103050c0f01030b1c1502030f040c0f030201050d050711070612051e130510050a0c020f06010b0d0f09080d0926070201050a050c060708180708280c03 67
    0x599181c2c02c0258068414861000400b8081d1705420700c00c650003a80c80a407060040d1480041c8114a000ca450244015481a0205043c2121781d042500b0070f0fa1403848190414040c00044203018009031384c1040a403071708100c2807071000c100c81d503808408031142500e03194a100d86219004008c02d802e608141202c0c0d058207071150402ca60b5803580d140c4202a8010218100041003050110761041080c00807181d07814000e208941307404290300c1e603003012180c0458079103051550b0b44241c980e200e03606115129551508000500541d410100000e150f0301c1034054840d0950b95841060030603000581100f00100d4200b0340840c4c40364880c4084101a14a540080310303e8501f1185950190b0074980c0700807017000b21103407a1401c0c4000760340191182e600480f008028000b0078006001d03c27000400c03090344995056a0360002c4ca061845060b00d50208200350788d880c1e03401404040c440d2500010708010104c2c40e000e001403185850780010100c1111120025080082c2940c000c01480021035414540740c7c1d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 169070998 1250 169069748 169069759
    0x3010602010b0904080a14040b03010f17060603061614040b0d05010803070308270313090c03290d120e03210702040b0402040b0d0b031c05040306110906030103050c 72
    0x101c10000304810898100c0c1d0060410801b03000c440c40551203a1401c185203281e00449900d00782d110342852206070801d078802d4001e40300403e010b004038444100c8022842c070540700100603034100100041e071a409d0017800318080c001e0081d0381485040c41144503c840d401003180403680e0350b855034454403c950013200340d208041e040100000f94244000102c8400035015645e14007251a444072080c5646280c002e06106000406401080300005000601c00d56170360f80c042e50040d5180c0000c11040e20b00000301c00c014989011541c409562902040022441000411440704c000c06000600b121700700000141407005041c400000c65a008440301039418412411901c000c200410b20020320120300c94000707c9072005005a60042c1016041041a428010710141c1010b0300c51918200c29040307050020300982e00d4040714a110f007014400700e42c5500c03c20707070a447c1001d0114406403091040f40b10080595070b9a0a507071201c0c0c4041800c2d50310220b0014149562960b59040c90381c0d40391040c2c0065413051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 169072248 1250 169070998 169071011
    0x9140d020a030903030e0604091e06050103021303080d0f090b0717070f030b040f050921030103020307050607030207080a08030603100e0c0607020406030803010603090b070e0607082101060201020301060201 90
    0x940005188040325a0641d54802070f02d0560341c045840301082101d5a130000814030010540c044217008102e041d400010a40b950290078801502c140c90036644107a050510400103041e0983c405440030b4241c0c4d8011f0180c130f96400b244410900140b00840d910b03d113243c90800c0c00c00c2004110850716005d510107540c0c0c100e2141c540040b000000005954060214840d03001c0c05881e03d000760007813200d0080003440050032101f44054103080d5501200e010203a60041c400c911880702d2069404400404141101030a541c11a40480ea4411407401950f10410b0701140754000c0510801c0100701070640c505c240c941c8515245008140d40c1c0094818920900aa103800b280000852158107641e501c031700000c3c900f0300c20240c00c0c0056940701c00c038160b810a888080100c0403c0b43c09005500901241e640010303007022030304080304208000b8007142c0402a0300c0444408a0f40c580081e1540c1541003d00f02d603039055548400d02c040d12404a03442040c01d0b0a0000013074494044d8003a50407512142c00900c40c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 169073498 1250 169072248 169072273
    0x109140a050c07060903021912021b0604030b0615040b040311010806100806130203010e090f03040e07200f060603060121060f0b1f0e04020f0d09030e040914 69
    0x20390748110390785003080000b0700c4002e0114001d500988560303406070055480395401d20403110340c005504682901c2d5201c0d030380036014407503078104500352031071002d8640d1051a0741301d180000c2a03031140c0e00c0050200c452075001f0940076601c201d441105051020310301c965960740c500340708000c1c1d04284070554441002c440303a0385455008003010b034482c45008241c249102011001030794005800340c02103400240030341554030104031501c0114003030441480310400624042e1209440c02e10303025040c1711560401d020030060005000741d110340044c0716042440f11079100100c0713041807142c0c02248c40e0302c92040036400d0114040100d6514000c0c2d8042e800c4d252181c1e01c0301440e46200014035840d034041d044641d0006d000c25a240e0045000c014041d4012807600700a01c0064064003103003a400401009902e02d85030010f40000321401c25040a42d010b50408445518141c0303a4045c1101c92a4031b00e84810700042010f1188004085c5040010000c0144d005903080140e00c03c0070302c441a0400c2d00c40c0400f0300d004c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 169074748 1250 169073498 169073501
    0x230109050904021f0e060c1f0905100504030c02040203040b1b0901020c01110705030109050d110613021309051002121015110705060a0c050d0804022b08030109140a 72
    0x11483d00600341d440d46050141003201c114400120b040b08000b1000d00744007140e41d401d0003c0c949101a03500420242e810440c034000300f80200902800b46600d000e152000040d400f042c201c0f504200110001002c0d9114101074944080f4054001e60084c400003c000c2000030320059640101d51003800c1d003030480b1100d02d40010a00c00c90454601590040c1e60304007244d813048a070440503c90711815680c040f82d0741c901080c01d541041500320380f01d8004200c0c4c2d03d0082c1d800481c81408902da900140082c0c2013054001140ad078046001a02070020444891030294240c1c1040900c0c41d1300c01d0480b45c00200050400c0004c0d00303c1d0024010000740040481c0d4901c040c0f140400036203c06040c00040c0784020354061b614010f030300040c07034041c4c0960341c07000481d81d0b07560000c0e00e502e0706252110404000986405070074038818800a40c01c0c08014828040561609050240c020300003200300c40c10203d4004030900f044001c02c034010900800080081024501500040c0d070300780f4507411000854499141580 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 169075998 1250 169074748 169074751
    0x5120403230d02103803060c090114280207090605030703051020070515010602010c02120309070e040c0509070f1413080307030e0a14010c1b2301090509 67
    0x401a07200c20340801001c0301c60f60204419116845040c010a044800c100442c0f020380170036107441907030b2000c01112600702803100c16400012200100d141c20949000a41107040403115201d051134080359100010407a045101822a00d00ca0380c1410100031110003540c03032140e40600f201050800b6000034590800148030700989910001070409518004948001040d01a20007180741214001c20803044110b1402030081c0741c011000362229100014565021040c180c2c001c4045a01d000c020211441d07002c24014200000c1010740c5969131180c0c02d4440c607240054005001da00e40c608140020480010001c0d022540195003801107903888980658800070307000c00c60f4000c2a40e40780400c5000c4072101c018201c0b1140d540350385641e41c0d1102511481d64006040444c08150000e0341407945107401484140101020780e41034021410200001b0030b01e200418000b040e242401c2044000b100300a01140090302c4440796403110030610001000c04008403005640c0890110345c070105060038580000d6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 169077248 1250 169075998 169076023
    0x50408060610050403020603070207090605091603090804150909050a05101415041d16050702120c090702060a180c03241509240509040512040323 64
    0x182030a40c0c40100748500728460100d00307820450100800700050f0760750300203907001d80030300c2d8002d0440354182065203040f129507400061052260004010110305081c401100d12281441d006c2403640032442c00341061301131340d00034940c0e424084000d80417150748525060116260317100148183d84522685d02d085550070b8072110b180824043c01805001c0f80340c00000141800600b46181403803480044800c540c1098005401c000303490f0801d0813480003c0d0f04103503002005100400c5102c550920003a2440c07180b110000d003d2400ca100345c0c00804420b01c001d0140c6c004c00380c0115031910f0079171002074580394100c0d61000300914140610341d4620603a600c00d91050f41c8550107808090440e01e0b8540a010952904840e0b142100030f8600c4600c22802603103034414040e41c0200009003409000f10640e41603200505107480f070760341c0c1044000a14030032001100d0042d00c01c54082d403540e080460400ca54404001e4050318001000003c004500028482c88000440c5907032009200041d019120303601e20054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 169078498 1250 169077248 169077253
    0xa080a09050d0f1404150e03011413060e0601090209010f08060604121e030f0908460c0e0c0309100b03030d0f05041b0e07140c060906011401050408 65
    0x3212082d405081d0907040220b403030600200e8644041948415503110303400c80c2c60011484440101d915400c045031116004003203000340101c248034000b50307100c00002441100d07280e40469141d018000c00d0b500000a8180100c20b95400d50b840d00f2680c3d02a600540c0258002040802c01e010306d50311032030740d25005e80b10041101349000c4c90444800844004c022003980d4680131910300c0f04c00b0030502000203100c94842c0e162400f00d440340303d10141c103144040d40001c446402540d4503505281e101000046842030f1413409403c412180510303445c455003811030080c0011000b000c1034081c00000d018072001c9452011400c040d95498071042503640c0801c2c1d805000940c808a0103400700e11007500201521040070302180c2c01c6c00468510002520700880040c01c2c03169030380741488148002e00c40340c2c4008000b400607180f0030610305219160310140042c0400e04000300e402480c5156100b120443c0c1c110036144084620b5401c003004055104c1c0c3d42031050081404c0803081c94a01540140c080e10100d4107081c01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 169079748 1250 169078498 169078513
    0x1b0b0301050108040204022a010f060b0304121b03080f1005010c030e1f0903060b06091f0215040809010801050306090307020d0c0905010b040e070c0f0303090303200a080a0905 77
    0x191160f04001d0f100700d0f44260240010903540c00a9500380310094028000214011400005c031402c44c0c02009403030030900d08040c010301c0050359030001c498100d41e111288004c0c400c5042c100b103a11072800e0900c0c4144203030546d8114140341d803000c2c031207020f00340409030f40d031040d250b0b003002c03840c584981d01c54a40070a00074503c03800428041d0204802500b40038143d102c2ca41c46c03034110070b410160000704050110328149014010303c1002d100b000c50309002902c1181c58440d801002440b0818291801d8003000140c4400c08076880c400e10902601514180201c11b213810585449a0b860300140e40480c009000d107000000c0b0b0385030000d207480c0581d5000300a1883e2001e143c080c01522128248141d54481e141c40c1c00044040840c42030500900d215550140c0702d40c10701c040d00640313000c040c01220401504c80500c20200d00404140d90941d60305017800074500c4104d00c0d0541c044d105414240c020030b00c02d440c1128802c09260002d18080c409945d505085d03a58480400c0d040b2004020068442d501079003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 169080998 1250 169079748 169079759
    0x7110c0d330f15030507030b180601060c05010c2f010902060307080f0f040b0c0307110709020d060b03011208070203120304030306050a0503060f0703180501020f03041b0b0301 77
    0x290848a000820400301c01c4a04000c0e0303048181c118148030310407110340d5a0921030070740340c5a21901c09000034080700d40b40c140e451504c0b55035540855000c00340890700c0b890301040c1a109035410441380c0c0901d00055130159070303650501402c95080c400702650350b54208002c2c440603501c100c0380442004100d0240301050420880c00a605045070989a013042d9a58040b540143c4e542e48040d511404003952040c2030781c41c3c0314900c1010360740c0240100c880d0010990a00000500244480740e0201005400c5506ca035501c80048400c1d1450002485050050702c20105101ea40c1e50000e004a0805603018001c055982061211501c001d218500c0403a056650038800a800700c8000c00d842400281103e2030078140b803030426640d500c26541200420b984007000c100c1401d01f070203004001e010450282c0f0017450440340e500081c40c1c004055000f0580e8070020905604006810300072402e0700040219180c0c0350002040c41543d2003503500395a29403d40c3ca500080220b5210307440b09503410258803500f10391904 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 169082248 1250 169080998 169081013
    0x50c0709150f0e1602060714130b07210e01050d020d0204030b13020a060c030e01270b0306040b0604061704060209120a02130e070506130e090607110c0d 67
    0x70703585a4007200e040300001664568014469010301040c0c094000b0908050041e020300d40c0304881854199048103040100e21368110f1104804c41d410110700d2642c5000204800890341c946404c0080c2044010818100784a2000c00c2115036a40c64612400300060a84054036601d5a0120040c0007500030411083e8009440d00a800911750307054025081a8495071a003c1d40c3d0412180c80d08403a152050240c203600d05640c144004008c2814224421290303610021705140c542c03c4401d061000c9014a000f42242502c0500402c06036000c0c846110780c0c0b20041c4141d254016600700e0700c502c0c18034108250718500841254203c800c140c07501c060301261007642c1070050070300800c00c1d00c40545c01e011100c0c0c00c1d01d401602c0d94500c0c40c120041d21400c90148100484004419030b01d00340c151400c000031488000001c0c00c0005d49104941e110785500c09551b510049130201d8002d010540700b07500600c003000d1000940180565141d4445217080301241c240242d4944182403c0380e40040c14070101008500704 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 169083498 1250 169082248 169082261
    0x20705031e12040303120f150e06010e100504080c06040e010312050705010906060905240d080f0706090309060c05030406030209040906051f09140a0c020733050c0709 73
    0x240090b14078804400004030b20a8000b94001e8020415100c1c01e220005242d20404141580d4500c3c100400c410700781003a00c0603c440e02480502c807841c440419020707802502c0350681d5560013081c1c240c0d0052000001482d50b085071144030f21a03c111903c540d01c6140c0350007900c041e1041d1039040c4115030b1842d19042c1c81c0c004000108002e00c40e0411192010510130f0240f147c800d40034040c0468500e10702800e402c12644014113014120401c0600c000500c03003c110b51030718086044601d00756544060400751042d2144c28903903e03c86000103400c030204001f5410112905002e0344480f01c0e010340c2c400c42600d02d034400220050039504100018408030740039901400002001030300c001920341c890b65503171b01102e1041c0da0084500c281c0b0342c44103107045400726140d4080c041d02e41b424001d0400b11500220382d40750242a0039142c0d43c4078451301c4000e601c00c000c04001484036200c405c038040600340341c2001c000c0e49c1000b000d9480fa80401c00c0c00800b4041c80445100e2151000100450b070301c0c2c41c5070385006061 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 169084748 1250 169083498 169083553
    0x1101021303240501080a022709010204030b01062c01020309040207060b030f030f0301090903090806100e1b031918060605031209010215071e03150909052e05040f1202070503 76
    0x30505500b00e090048040402d2107580a480010780e4cc500f14140324504040c16827260f01005000e00c0d0081c000d40d8010f0000c884081c0c04441d280c04400c5000060b4150b004052695410a1020440304d007444000e401450307030340d402601903440040030340083c0340d201c2c4191015035045603c200010050303840241e120940d01030292812411043d182c08100b400d0280640e9a00a6584400c40901412000300788850f000400b03600000802d21600e003040209010050805003038131030141c0340380303042c42c81504288420001844031148444592910900401290003401d01902c95110b1a44041e10404221a046e120580040090b00c82400310710800302c0c00106180300304404440380b1005540c01100900c1201c44a440100380d626040140030a161510f91280001500b00740e80440898000314404a880030306d10358039261030300c0058450484080b0300300100c05003403800f02007000b03000c0d404003604041403041c0b20220034545c000508036626080c0f800303140e13070680200410141040140d40502603910 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 169085998 1250 169084748 169084789
    0xc1401090b0c090915012001020405030703080409060b04050a0e0a11030a0c08060411040e0406090807060f1505090c0c0c03010509060402010f02060c0a1101021303240501080a02 78
    0x618a80e40c0d40207100003075a29a008030404a040091813074841d40140e440000380c48810303010a0b400300028000e202000030031100c404d25103043c8840950a40444010304005811140c481d070752031501407a030398018801c000c000c3c1e16042c4040780300c0242c00d00321422a0f000404620a050429401e5860070030061b100e0700d01ea943d2466400740c02e00c5040d02452244902a5001540c0d030f01c094005401d8130b8008250610407880c0c1288469010f0482068070161440040c0e0000b440d030316490100c000f08034000b80944011004030b460801c00050390800200b40d482c0e0078051040300d8041d0302d0808070800328011310343c0c040d019100240d0140700d00c2d4040c00440d074003c403c80b51030004c51008242110410748003030300983c00800421081d560441c0e80620402c9180c80242600c1c03401d44a40e410302e0140045100030006412113002000b14250166101142503504807070180f5030300e140c05481003a10351103800d980c0d614247d4441d2100314920909048400d04030103400e030b001056003041340c000d203012910f280c3c54 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 169087248 1250 169085998 169086011
    0x6030c0e0a0b0918060a03060b060705060a051504090209041722030210110607140d0c03091403040302010c060509030f0f090102100b03100c050415051803010b010c1401 74
    0x35510030107403100402c1c9030b4880d2035079102d03801e003840401c0101040c41d651618044052100310b4a4009a10088a810180c0010160510000602d0503c12030002030031238414942030100c08403242d44094020059881414800100c0380203010070b490000300069441080c5000140208131404030000c1d801510550341d07454003960002e941103c03c1145100004c0075010b2001748118100303550441c0e80d100d09410101c1e4280710000040d0b03990170b40100320f181004008071240da220114402510001c1c500c040e020300032060b500f40d008005080c00f0000703545000114114558900021040300c0540342c0603961100100c0282d103c281c09088003603c4155284401c001da203048052040c003400c544507202c80c20580d1080e401000a00c2c11802c038032040c200515004601c5030310790b0005042940f054800d0030200d4045c003518000d5669024035804000c0d501d1544800c6a402c40d4803000078014100c01141c291001600c5800f8036089a0420045034003154210300500c01048001141c4503101044030000710740c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 169088498 1250 169087248 169087277
    0xf0b1902030d0f060e1503030d0c02031b0a030f0809250b0c10150b0a0e030f010e071d0705160501060b070b01031412030c090d02031501060801080a020a06030c 70
    0xc4601540712600f080b982c480c0c05101c00d1402d0581e042e00004001940ea09500b412000252603204070300395180f0050350b54400c0c40c0c80b98000e1040d520622020f0b40b124010300311400020740c44454070790007203000850003104d8406480c000c008181c014034844e80101407000810030540b4846014400c450740880100c84002501c2126000418080c0d11000241640c0e03403a500480f0155180b80303031120f201001d410001d021690007201910107810f80b80c503013000d19905000c042070a1000c809001402c1c1c2d4284000c0c000700d01c81c0007501100300c6000541c0390300d000e00aa031a840c0030301400d440407400034800700b106040c4d03406a490200000c0b40a040001140f6554490340c8000340c2c00060200d40300220b41004005205134041c0004509001c0c0018164500c0391020b1224a803200502c4074400590129440829803a00400302e542c2a83c09030465199101509015251410034400c503c0010b001d0b00c0082924030300400d5484404d5405484561281d0070318205030040c0030480e14400400c06505c140a08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 169089748 1250 169088498 169088501
    0xe030c06070504150c0f02040b041503051f0b0a0b030c190207150216030b09100f0905010615021002030403140703030b03010b01180e07110a0302160f0b1902030d 71
    0x3032034103884080d600ca24040c180d03a0200f00340703140013050003a2100c002e008a88080c004d402c8669040303d00041c030007a580d0005000b02000024280c0c0c2e603424201c048108040000c184002302941483c07400c072024481281070a41e4048030100b0f030001d84441040218141c2d0b1409107801030300f21880c01d4102500b40e2403096440c80b01200c0580180c0c0300040c20000040315817000c4001d612680b002d019808030b00c401030200140c0e188401450451428002584100c0500010300440340c10102846051000861903001d410302e00e0007580d40d5441c0540005811000581b07120030000c46401601609200c04940f20003500000c0c016400c0c0501d598200c800340030041d000b0900705100703850000c0c18a0b0940706043c211603040820506001d020b1021660554070b02506008940c039588074080a6903032040101c4003501801c40f14800c0e4811b66025108051b000320700c100c9075907400e00c40300601c0e5990b1614813400008500c101c1c81843e0040249111612840700192400d940030b0040303901d450100c560440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 169090998 1250 169089748 169089751
    0x40b0702010e030d080f0109022a10020a090302040506060c070b070807020901030f06060b0913020702030703061e110a0e01030b0f030d020a03110601030c0e0405010908030c09010f021605040e030c06 87
    0xc0094a01c0f01044101d10001b24082c0c05850008411820001c03550041004003002e84034840c18401601d070f03035100c4124100301d080d04004002009640b110340b04c180240c14409240004c901c1241407400060341410100190340b091540d201c0201082460102c0800041e80305030300a44400004128100c003507128080100d00840c4101c11104c07409000b0300b004011506641c0081042010411161817a903492030300ca2680407070000e4006036241000d10002e40746c4030a95000030000b43c20320740003100300300c100c0c0603180420302c1c0c0180601108842d144022803602c1030011301c6011071041d140a091a510a611448200c0e8004d05041b0100c150103001a1804032024003100060384408250010180e01c0000c03c903091080c0c20007880e00d5415561a0254040d907409a030050391080c90000d018410b003500506551078121305100c0c0d5900f0400ba20300c0c0aa4401800d07907002c600125810100b41e44000307019582d07485a13024001d5081d042008000250400b0b0003040300c0762000348103103142c10a0501515 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 169092248 1250 169090998 169091023
    0x61303081303030e0901060e01140403060e21040e04030c0f0204140907060c0c2c0702030a1103031e060f040e030904110c0a030e0406031a071b0206040b0702010e03 72
    0x7160480c03661a00800c07958036030310382d14040e181c00401007080d20f80214102c042c1c0c02003400e107181c6690000c800700c002d9025a40c00078014a040c0100c0e00190a40461036500140c82c120702104c01c6259602040107510842c414015100340750000030380800c1c400c0980b103c881384202101074109415400150696000240e09d8050986410900c0105c143c104000d400602d5503050820041c0c0301070b202c18500800e103200d070b1000c00c9030280c0100070f060812900031000860a440350303000c40c2040c2c84000e5481d00300b0302c800c0340403501c1d01da40420b00d20340000039244107a000c13403141c01c800d0300344440c01c009a183c0900304607046044106c401c40d855070349004009440c10540300031070700c88001c94200000c0d200d106078020280c84082140d0503035100301260202c031942c2c050800ba80f156840d600468010075199001a010105581d0903201c40a540c3c081c09005561640d90a440d5911000340d0480c01582501300a600603410003080241103c207402400c1d40500504045560104802c042800c00354001c808 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 169093498 1250 169092248 169092277
    0x1002010b040e0a0507210506010b041503050c030703150503010f05040b0a05060d0807030e090f0703060603060605040302011b020603090307210c0204051003050d0e03120a080606130308 81
    0x4411503080c07030300c9448401c0040000a180e807a803036846032516607145001c3c6944c21040d0200c030500c0803c1240311b900c03800c0e520404840c08d540e0f40d81d440060303980203402000c9240a020b1100c200c424070a0184500416121a8840c03554032880c00076001008080502d00e4005a01d00c0009181e503800e1065081503120a81d02151138034203450041082080103050700720291405080c443c060b00e429400d10b04003076120032095134030384003070609803000908500b0140d8031200c0041006011481140150301641140c0c80c240801500c410098080d65414048d80d000608280002c00c00b41d885424459100700c110101a00110410f401068165004440c41b5100d40e1000030440200608403c010020005640604030300071803407500140216400180a031040b40c80703c000c225200d451024001c011903214045602603034100c0b201411a19040b003e040c464055825100040a0102c049401542203035581e0340c02660344400f0010290001d1142c517480d10141d040200000700418001c00b071144000c803c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 169094748 1250 169093498 169093511
    0x80d0306090b0301020703020a08130305010c171311060a030e1009140c01091206140405100e060103080a11070b04060507023309060705060a060302180405030901080411100201 77
    0x3003100503500b801050501980c4100102c4000c00c2d03000c620f41040c0ca9200d02c80310341d540c8004200d6508040d0355003003d03116520f400e244109036900b202144e109840044504115540c60344800910200c4440d006401096418401000e0385803113001860203075168140050b2903180e040c1038504d04540782140501d03043e5142c0d000010712542c6082000100e0001c4010620385881000003420480b0b82e200d803140c1c0030402c082c00340402000390800340400341d028011820358901401c207070740d841c1c110090000402d0b00c0d02d50721001e00b040114905058a400ca200c10785000d261410441da40e250114000031613000d91100840e500085000801c018241551025251100c1d0700410070101100c8140c103000d00d007026440d03144440075a81001c2403801840e0260f4840c0744400204185100d24030000b4840d000b010200710300010360707510440903640280e0303951f1281d0008079004c21741d4072002da4010b040c2d503000f40082c644030343c0b140ba40d1503401841400d103c0014507600c07011919042c40d02044e400035235115003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 169095998 1250 169094748 169094759
    0x9020306010306081b040e030f160309050306040f11040204031109060111250f031e0201050d1104090e2b021507030c02010e01110f1605030c030c0606030309011e09080d0306 76
    0x42c030031f0310360700000558074104000900354040d215012075486216172007030040f0181401781121f140202030240941c0e80c0e0303290074a48030440111000c4120390940801180c016075041c60300c00e031802d60b42d100070015162442c00c0e04000ea15003000f80b14504106500c900364154503414800f0038400364409001000030030300b0490f84610080c1c07035001100e511403501c10030004901e00302070b0140c0c2009075080000f1541c4460004032924840e074103043c1065030601a26119a2800c40014012070701241c0d001c00071600240c120644986029607400d2010756501d98120900c47c00c0703080c6800403251401203640348100d80e1107110300103000b2240380380420b5031224684020b0b502030040e121520418402007021100e400740000c0f060140303e45202c101d45c0302003605c1c880303001086d114080b60381d0044210398a601da690300c410350702e6200100400c1c0d103001d10b40120341503080000655504480c141c580c080080c0c02020504d9210b03040b1540b5000b041800c2000144800090100360b89030b21030b03642d001c100d250802 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 169097248 1250 169095998 169096001
    0x2010513032906032815020f041404090f0213091a01030218010b0f0906090402040b040807060809030a030b010507020d060c170c04060f0c12020303100e070909020306010306081b04 79
    0x5010500031741105140001200b03a00b203400c40c029078002c074010140c0340181050400242d0040046000c036200003640c034455110500a042120007101c48030070344000e01c2091106540c01310307000404408400a0711801803505415290f13540c0e04810000a80380c1440e01c5800c811000015107881c0a07001d10014419070802c03410101940442d8401c2442035403400c00c0b04181881801e419040308500400e01c0036280e40c07808111044801c00410640d11951a000c1c030704030b142d006e44551019882100e0000030414098144284140c03083c1c4040d6003000d0f6118403e401403c401c204060402c1420010140113076908402c464045011352030000d21003010300005001c4070080d03641e03083c0c083c01f070100700190915088211070507a006460310680b8021402000d8507060a1520020a05840d03907000c10358181d80000a18170440484e40411407191b66640c510411060954043c0000781d10404240000241030f002103800803010b141c0013501a41e81d403500340c2000400718146885d04c03080c00d400c000070300e4135 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 169098498 1250 169097248 169097251
    0x603060f06030507020d051305220c110304120326041106090d060c051b0f070f0e0f0612010204080c090f1e04061d030d06150c020105130329 62
    0xc0e81000c03c081d04207003d020f9960407424040c2410001d00203508024905481140002408007800c503d07060541e2881403810011025030900505240101913400c0900c207a40110310500322401641c0b41c40e04040d860318041043c050103401740113a80300485d000d694054482080b15143c24000e04242c00c080c80c0065900c969140000d20401003407084559030303a203c1c00c210201e640d10450002d4113414581c0140c40d18011040d0b40103a11840e5020241e01030404503a4a400e640411309a405068461082c182d90006900490aa14441c0301c0060100c0002c0d03441140c00c40c50040c0031090303800e4201c0d41d1600fa40e000b07800c0b030415504461000010fa007000f070001500041003e0028003140f401c50101480f01c003107594218181c080b001d010405002180d8008444640c0c0c003c214596860000301b2181c0e280e11a807204079605d4504280002d11002211080400d0b40c00c0f9a1019003040c026001140c860b00006130600c05200c01050000c002564196012030107030304048521480c618001e10030204200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 169099748 1250 169098498 169098509
    0x1e01020a0314010506040b0304020a03050f070603140c042102030d050408150f04030c03030b09040606060f03141b040f0e010e010f0605030103120e0301050f01090e01021314010c06060603060f 84
    0x180300b0018400f9548031800c2c0c0c0c0030f942440b404542c9a80d101e00015180401652000d010360042103060008100003141a90940302e0340d0710103004552010790248020f0740c04861141803036509110503c14100416403409090140040045100c51542c000900f01801c01d1a00004070b00c00103000c00c841503043c0104403542c01040c110b500a0310740141e07002c8422000600040c100540d0368100d0b000c1500035489002200d03030242c034600d003624040c40d0010040c4218042c042c040340c81c01c4900c50301c561080c0180d0080003901c4010503521307124880103001e15081142041d408260501c800f2994484a0711550300800d098000c02c442d035403402c0340000310380e41e040c0c100d00e0030030f4140a424402c180e005070460b0304580d404950501e6401c1400c804035684800c20144c2e90313041d407d11090120b40703020703440c1050603602160000c00c118450207003843d00b04c1c850103520282440400c0c1e02080070000c0034440c20482c2c81c045c144194000c000d5618102142c0e81a0403040120340d0360f10041c0b05108401e00003a0103040c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 169100998 1250 169099748 169099781
    0xa0b1003050702010606021f02090a120503040608090610050f03150a0212060a0b09101b1103300d0603240b0f03100f061a03180111030c030403021e01020a03 69
    0x40303441c62460075040045004104a92700083e00d41580e4031001c0230000180286804105e1708010361520315101e60152050500160148000c100c0d05030000c540e060103500c800951010b0503140105200707484040d200119414020101c40d00b001544640b42e561041c0d100d00c1c030040c0c1d15950b00c03058001065000c0c2c921802280b80e0700052101000c20411904045403c4030708056800704498101c401c9040ca01810681c008400c041c641008a03644d0f41c0a0031210450607100c02c0b02000918400d41c3d80300d0601c0303d80400e481b6a40b00d1081c030340c1f80000c082d0414000000300c2ca49481f0349a00868980300000071030008030901600098444c2840703a10584007003100c00304480d40010001030b03030b140304074000300c01701c90790382c40c03500e03c0818240d030008004004050384a014200030348124070254108403000340403030341214101d000604040c411541d804a406c100c02e0300b1502c0d2205400c00c1c1d600014421015841022044250602800910070000400c400050b9913900c0c038080013800d44401140d0800000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 169102248 1250 169100998 169101013
    0xf0601090b1c06170d110304050a0305010c020d05090604060c061107050d020c010f080f0a0e0105010609060806060c0d120f060b09100801140d06110a030506190e0a050a0b100305070201060602 84
    0x404610001701c0c14242c40d203400c2c3c1c403000c09101ca040d482a030303010950129090300000104031040d0004102110306c0e800760744841c10b02c0841a0b03498401d0f8500144d2126040000740300241c06840d031291994080d40b000100ca04c021010211554803100d015100ca6106c000c03405e40c0150304105035200c0460a103403003400c00040c0304019100ca50051306400085c1405030005011a010754131515400c11040c0007809103503969000502900e402d4010343c4009006000000c2c2c65041c65811190184000700080190f207080700d0040750902030b0a0f083c101e4030b40c0c0b524040c81107100c040c0a00da01501408100b16542d000070010030109038041d41052050050b10001003200312020203010745641c5040e290508545d40d6480d0810090140d40d403c0345c420480450340f40c039907607815840148901c2c81580d07660182005007207400c46626107841180410484c1c90005000d541c4180c200d0350300079010b40c9000c255064103200040c603008004003000002a0f40f0700030005600c0e4240070310304c0100000e00203007400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 169103498 1250 169102248 169102289
    0x180b1c090309052206180605030c0d061d0604030806040b09040308011703040806090a1a09030901120e0604060903031a0105030406020a05040e0115030501060e090f0601090b1c06 78
    0xb01a0b981c440d107446821004410504000f1010105480422070141001101d07200d21407031342d0201062805071002d9150840124490600080b80243d40c1c00003445a000e01409540f018080c10403480940200c0c42d0200740c03c1904201041000e000d24841c3c0c40c1e000e010315000342030004076488412410302c03503a00c030414000801e81205c1070a0664900307043e801c494104d0005080c1c40c40c442c5d58061109407003803408103c2c0600011170895000e62041c2e07078959948865900560b020401030b240c42903582c1040250318015800303180c85003a40a108a40070804802c504401401e2580440c4d05640c0c1d146c40b9500c0a041541c14440c0f03860503441c022525241c0720203900024030b030f808018401000c00340d0019001c59907a0081c01503a00510303002164400c1981c55035100e4019102100003400860304220012594600928090040000c06001e41a030380d556480b07a0315a0000c09403c81c1d051200da80030204020050000400310415030341005003411a070741d0400001c460041d400780c08014000324a1108 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 169104748 1250 169103498 169103507
    0x4060b03040212030f0a031505010302040305030a03050702070e0a090209090d090e040804031211160b0304020118030c0f08150106020a0305030405190c03060b04050702030f0703180b1c0903 83
    0x82058043d100041e01c09201490f052940c0300b000c24055850401113035504c030340d5078103800c0100c000c1440c4445c0300099603140f0040d0280d000700d000c01095a0814400015864401d51007240c0c00105c40c4121801c007a96102030340403414003035402010140e1220b407400c095060401160b0740000600c4014282d00e82c146000500c6400c69000c0c039503021100201043c1030010340e409540285811411034141d051b82e18502800300c140d90f006d02c40d0706020b0b2903004030042c11110075020031501c11101040c50b40c0e65a03801100c10b0883c0018a040201c0d5405c0040302150752440c1580180080d509004405410000c50300d190201600c05464039261000c0180725680d40860300f118481d5040c2003c54503502c6500d031880c14000e080501100d82900c0b08101c401780f015007803555040300c0c040c5074100280c4082070107000c252201251405d0143e0701c00c000e80079040800b08000e0807070303600910704450303031018a40d28682ca03000c0ea5448414080c402069409440c003020000903501000307100b04201d048295a000381 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 169105998 1250 169104748 169104751
    0xf0c2316060909090309080d261311030a0b07090906050a05130504080c06040b040b010602010b01080115051c1a030a0f0818060c07030b01050a06080c03070c290604060b03 75
    0x2006141c5a940613000c06001710009405400240240c6402d1008210000e0802c002400300040082c01da000401402d0759030a48580500c0a18680c80703901da4258413204d40300188618003d0b018030801c288440481c00d87e1340028011801d956411b100c1d14503003040007013030300d83c0c60300b00c41d106030344180c010420b6584141a408220000f0310000c1040d42c0c4034102020140100c21550f140b60240c201040100148550141d11403441500e0003070303441c0d0f00c41808070308a032510b40100340030800d4000140005d150300500440d2180071480c0c07103403a00301d40240428907810700940014185841c0c41c580d52440480b000c00e4a410082134000309403406441d140d55055240744000505a8440014201112481c04c0042610810080c040c0c03540c5400d1103580c2c40c0e07503038090310090720012481c0380081780c00d2030070814410445400b075403408407948509080c0b0074141d001528002c04c0c44840b610000014101100c210440318103d2600e286030701c00090111950b00c801000144528900078007400700c1c11a11080c0ea = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 169107248 1250 169105998 169106009
    0xc0c100903020307020d0321020c0a0f05071a270105180f100806040608030a0e2704030c06060608160c05010902060301180f0c02030a0f0c23160609 65
    0x403910008034101641988610403001c1c0d08080e1041e6010b003450740059a44d0144650401c000301c800e10310702422001c90040c2904410160484c4c0545400b02e43c02c44013100c1e80038018000d0f110440d9903416038454244a440b003203011900003041c00c1000340d1201883c40c0101c003d0701450703482955508002440b600c10380b01c14500c04c44403074100340990b8550300020184140c02501c070051601180d84058000c04007107894501c42c070f003070000c0825190404410394110a0551300c601060b50110410080b0360054154000780504444a01180c120b9000c115140158001d44030703503100c00c8050a103002991000c1c3c1099040c496600300703024181b4000c0005003103101c2180342c200001c4c0414541603016026580020354058008000402c110086000c0a07d018215030010020751810361421340c180c40502032a800580c00902a003003a040c0542030035480c00403070b840c000840240c00c6c0c0d40c02e0340c00c00206180000964846858000b90541001204d200760403000c10b10340c00303520f0704800a00341c0080b801031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 169108498 1250 169107248 169107251
    0xf030204050f06010c02101202160212010603020603220206280804050712080c161e0b0403060209180a050f010b0903120a02161409070c08030406090f0210030605090c0c10 75
    0x100c010790308ca8206c00503d080c8600055540d40544441c01c4200740464805900c23602c5100f640b604410014403a0307a0840354054407040c11a41d603c800c215900022241000c01c08051130079a40069550f01c00400640405249401c0c5944034551040f0010b60a400c0d00818820303443d0604c404148006110700440d41018005400d08802e0301d81000035016103401c041c5544510b0b58104001c0060031403a900740d50a00300710b00a03207400e0b01b5924501c100302d1311400e00c9a5201f004144041545a00202171a200203803e84800904a00c90070201204c11034081c2d22139544d40741800500103200c0d220030300400f001202c50f4200b241c1800002d4031200800c0d901482c400f03001420181d407900905c0989040340040e202035042c180d0742c00d03821000510040c2100d1140c100ca400086074580205210044560003125050075607845503102c20003040841400d03685800b000109000603511100f0000c11100169004101d00303151101b40420200e004d4008019000240705c0c41da4051000520114540d004000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 169109748 1250 169108498 169108519
    0x9050a1d06040f1709100c120e0618040e0a03030f0b0d020319050f030a110105010509090706050a030209091608090d05161a0103031d0102010c09050105070201180f030204050f06010c02 81
    0x610070b124407034506044c0d00041c50784004446e0541010710f607082580580c40b111100c9018420856201c1c0320040341c42d50084085c010029808000710004240b411301420005814001d10340c110314201220108400191b268004070403a0861070081d040c03200802c0c0d4408080c810581c0c0000d0703d8034207140300107103010604012181448403c02098040b000382c0340560b9500e561382240105180ba259100c0032540d82440000600c6040880c80b807881240c400d805011214185030701103c0d10b600c400c03400300070150280104140342d03541401241c007881c19000b01c040078000a44000e40800c4004060507040c5d080100c010040b241c01c58129000e108001c0c004c00c090511a18040300c00b01d000c400b1268179560081b0020081680107604d84140b02103001540040140c03d02c0124207039410350309020001103603000c0c1044154041c41c049d01e0313100d2050518019000390b0074070a00e103050142d4007d204489034001c082081d0300f024071940d034104464807488076103494681d0003e0403007603103007c0c02405504400c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 169110998 1250 169109748 169109783
    0x801030c0e040203070b0324090c07150608060a0618050c03060609010309050609010b120d1713061a100302130b07030210091a0708250909050a1d06040f 67
    0x44040981030101d400ca490341400c03188c010041d40c00600100c404440e80343c02030014503050859610910f4041055071a02d1800e944e202404810b81050003e2251a2400030800300300078840c003803240489010000c0e43c5450900d8507002c01c0400c880d0402c2c001e00e004280911034540400300ea038425016640d41341d07214503c0c40120001d01095801918500821090003582d08064109032008241101c1c6100304601440d0200c0e2503550300f102e12004900c1000710401c403603024458941d4030510010104080f040c240d107620f803d6550b03d014204500d000c007940c8411038501020074407620562464214145400c600c5500a000c20341e0040001c00b050200d50030007054800c000403480d10882160501c801c541d00d19200441c0303e400c200c1110304015040001300514810088203105002e0345503841070f01c224009454880c05444416001082a81800424803891a00409000340fa5203940001d84c210300c0784032500511081400c1380500d070403030350038807010074001c10841c07080c25000b000d80c401e4040c0c0741d0f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 169112248 1250 169110998 169111003
    0x80a050c03161407180b0409080c0d090803090105070f02030703080c03030a111801140d0606110606030a020a031b030c0801050f061207060e06072a05010801030c0e040203 75
    0xe11400a00c8001404106030051400010001e403203400309882c40b0301c030156400d448001c18080d03414140d2031101e000a400010707402c01c101c0f1000151000800030b0302d81d180e030b80280d8421400c04005d0f50041c41d0b0f000440354001000c400514007070003c2c6007010020400200300307114295000d00019150000ca800f550b40a10050b001160307c10075841da120360720880d26450350422030f0000d010501e000044c0c0b01080c00d0f4412600c10782c50714403110b180d4280385801500c1e202c00342690300014020600085030949034a10400d00900740c0c1f42c1f20041d00d0146901490b16001000346018000d8109601d1040180c46401c9a503003a80d510108950f0b904e9500304942c1c0c01845c50f944090284409d1040006000c0810745c086030241c0d0003200e4251a03aa07071901800109407910440f1110780d0f2242a040103e02d12892001c83c203500028401458260551146590b20409a0320310000c3c2441d0f0046003042d84810650b107008100a0130520351079891611154428909403080c04141c2190000107011541d05 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 169113498 1250 169112248 169112257
    0xb0703080a02220906120c030204020a020106170f0f0c0307180f0218130504020906010509060712030e060106020f060f0601050c07030b0109060819080a0216240f0c080a05 75
    0x30210011115803940503e60301d448264400c841180380303010800300361241651041c01c50690054a404022403455003404000e501c030b03107154421550ba42c8000300745004a00c11400309208a500140031211142140da403c01c07409603200300c1076034848404010940c0b0007154840840e40c52802c10b600b64110303c0040c5003d024425a4071103110f10010384120207144907034600882010680f159107088414480d40c0d011070704e00fa100650700c030f51000c001442d650310401c000c02c0c0c1480040c20309802c1621a664002c0343c546919182e2000ca41c03540c155a0301c66104000ba2401082140700030603001c40e003000c0f095190380340901004505103c0718001000c50340110100d0b242c000030202103540d03040d528145042035a03002c3c090000340f241001070000c1d61308400913040106218180d0a500700560f1503032900c1722584102e003c50198010200b07442d200100880d102c01c0101072071510403e80954080c0c0791f82c024842003440000380440071003c20005644500304244541d44500001d42c0c980883c10140c801c3e005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 169114748 1250 169113498 169113517
    0xd021315120503030708090a0f0219050a120b0c0307050a031109031006091802090c03040c05030a050a15061202090403030608100902150304050d1202090a03050312010806010b0703080a02 82
    0x1d040c180100b004000001035110780403c1d506c0303007502c1d100d4540b0942c940a044030083d2460b0300c0034850101514140c0e55080b1074008521150203034030703034400209022150710307881401a240c0c440b00c0d1105100304c2c0070fa00c42c2e1124120710018518906090301405078083e00c41e54804141d0745441c8600a10540d00807695036050080840704207030201d10b500c001501c010b00402c0425402c0c850700c4003c0c05101d00c0550780c0543d00621501095807081e40500d03a40d04000c20503120b15000003000641030311305112240c1d083e80a9005006408402e0420a04003400307120380368511454a502001015117007010f040c8065030440d003281c42c6490301d0404801500b00c58114034100e00a0321030166011041d40d228034072980c829106220b91050300031300002540400c44014025411819034455054803410b03c40c84450300180005041c12040c601003040a402900111919840018001e452208100e4a00d00600014008114544c180b51300e1490301e0264020080501902001147c10210315405480e200007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 169115998 1250 169114748 169114769
    0x71e03030216060903020c010f050714010b060c0f0c061804020a02120c0a0b0f010620030c0709140a0504030207060c050a020907080708161b0503090d03030b0f0d021315 74
    0x102c403400c082d070040642d035a00320094417542482003c1940283c017000b003072103255213034242044025140c4c1c200d404e0910396017003190f5507100088501c03540c0b001c0181010b000004014006d0751300c0c0c812603901e440c2e14010418420181401010304407130440c400d4800604069802680700c1061f01004d920300000740c11441d05054003c100c0d000305a40006400b100c5078001d18920840d500e4503034100400c1d001c28010341000680c000100c54030200c1000d95500c90b82800070850b46040805001503042c09031581005150940311030811800703000359000380340c0002c4501c20030000c50509030340195480032584640c4090200c10303120b400c20701c0010b12008030400c0d005010341049240c80700004040500460b0228081007411000c0b607442201034598407018a00b0f519031008400c1c0b04035901c620340740800ea04503003d00c02088405460b03200c2615250b04644a40c0340403d442000904020250120341c40441c05403c0e02400f000243c1d0301c50f0f04245150320f0054000580e041080c080c0b0760040201d410402081 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 169117248 1250 169115998 169116037
    0x8070603271202100b0612060a0807150906030e0d21020c0706030513120c0602041d01090b04110d0b15160210090e0a0c030209030708070f0605071e030302 68
    0x70202c40c0c614494500d4607426161041c15050380c96049503254104d042e009030b800e01507241e80004105065030401c5008020405042d034400d440791901d141500032002c4c1d0303840500e41c6003100303401c84e4440003c1e0405041c1880007000c40254203940c1d04490001c4402c01013262580d250764101c2d0365000030408100c0d8400d41d600c2095503c4d60b583c4003581d02c696000a49444006800420842c00080c003c55000011036140d0720020b00c00c861030404204207848c8135130b003004000b500840e030600200701c4003002070040e4180e61402c42a4003c4079100c0c10218007490401c1f105038400c441c031104903401280501000265850403101041800204100d0300d03030307100320001d2001c0002500641000100c3d108450030000c50ba81c031030040700c40095504ca000c1486c10b003400883e11010380e640110b84090007034640141424040c0000070b18080c0160f0016407644c003e440180a000034000030800a005941040c5240c1229a6510100d00151141190707802035444030307d804041c4203404540c071110240f104000310 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 169118498 1250 169117248 169117253
    0x50a02042a030b0616060207120905151c06030506041b08030405062508070b060d0b0c070204090204110a02070b03010503060c132c07020a030815011106010602060717010807060327 79
    0xa60020702305561240c5040c5040407040d1160400760107442002d491644002d8945040c1c20f0950404101c442c0c14000112031032030b44156900c6000020360155005001c24101030424200c0384100d120403500c148084003003400342c00b00000c121021518140c59250ba41c908000c0500c100c018500f00d404080030514203141d003407000d900080e00c5150300400c041c0c001900e1300020040d41242c050300007000d03890100300082c503c00404004e0031030f060002d0303c04034403030450794005012a401c1c100210064000401d100300c446504102c20300241c00610f40c03592641d414800042d9451600170240c500106000600b502c80078030884010005143c4a20740d0603901580e4820460401140c0c240110441c0001000a10340d5200250320407201d40c25885980990306c40100c030004002c40a04a2414882c1048a002c0700c01c204021850080007942c0c06020a410f10050003000c0e880f0050741d110349105100010710400801080c0c0c03d0440d14241400110103007a20b2014118540fa01000f2070f001e620314580009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 169119748 1250 169118498 169118501
    0x1504050105010503070b070f02010f0507210f0806030a020607031202040608070e030a0b0708060411071103010b0d03050a0315080a030c020a050301110d090816050a02042a030b061606 80
    0x1620011402e0b111969141c00418206d4001d00c2c401511302c4814980007030142d40a02200041e10b03d140c40c1052805410303480323040c000c100c061510841800c407498070003159a4050343c40c405812052800207490308107800020b03500c48c2c24110181c800c800002d01107040502420800c01480908041076440e50703a40c00c405805400c0444181000c00c6281c5035100031351402081541303455a00c602d29030004e40b43c44008039640341300203003442c1e0020381d215031900c1c654085102522815102e010400503800740300e01403500751100f2804c1c26020301240b442003000240c01c04103540ca100c035940f800041c610040359810004a01580c4034401c2c074001d03500140140b40d88600c2c2100014000d0b0760040b00a0350f100c0c10b00d402c0315110781c54590090b0060080c03000e00d03901d036000104c41c00e0003070324040d040c0003c094810800c4030300044110f4442d40220184c5085040034006c403540040f20b44044042c4291032220bc80702103c0614200003010350311106104640d68440c00c0d50480c40381c04140141d004940d140620 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 169120998 1250 169119748 169119751
    0x9130b1302130c080a0c1b0813080616080a090b0c09042004090b060c070f0905060108071d120d030905120c120a0c02060313020f180115021504050105 66
    0x2d0161020300c1600b90102424001c41000c2c3d400e65403451a81d41e99045404001c10000c0c075000100001541a54100e07c840515400428002d4590036a01c00c4520f8030400041900d511074469034100000308030901c121802c8010503652181030044881d90b5103080e140c020402303010018515103041d8144007105041202030039140c0001d54041003c00d16005805a0040414a10540680003044180012241508455000ea2014110780d08002c0e072034400e00d041004030f800c6a603012103098010000c01405008454102000703083c2480c5500b0208c600500003a1300b030b1200084200071a080840741d85401d5101c03110103040741c095032201d00411703900030041d00904105583c0ca21501460881107036844d0704951710401500014090794903000000d200380d4000c0151074040c0610606e002d00541c072440001c520858484401000d07d00e6144104940d00196809660041040360012032402c00d01c0311540381902c400d800502d04806041c5012071400c40010401c1c00219008018801040815001203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 169122248 1250 169120998 169121003
    0x1e0215040611010603240f050c0316030b06030105120a060e010c09050f0a0302010309210210050f070e090a020702030f01060914160f0c080c1b040905030909130b13 72
    0x2d001030024041c2d070b42030300e0300c900025010386c42c040c01001608400140441c2c01038402c00c0042a10303054080c40c0400c0302c1d01281c400d4103044001003000401c450300130790303198680005d003410401072407100301040d2a40414055a80284454041c43d081201c081202400c0540e000d44140240311480000c1800303028210401c0c004a80c2c2214003145074505100140c405110180821064510b0740e001180901807010007540c07406202d5484103a5100100c2c07200d5400013180e00101070202150104404882000700712038444940d00c024846219030144400007814070440d804400e0391920030010b0700034407079900003d61510440304000110340042d044801240c860701030400c0031a122003010894844100c0751117403000300621010a00f1401540c0011880d40342c3d2401340380382c0c0706903510443c07164040d06108980c5c3d40441c2031201c094080c00820b400a40e8143c40c2804000141d580701960381c0950303036060784140314a000240001c0c0301007511403800c58200071401003e003440070aa56040e400c41805 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 169123498 1250 169122248 169122257
    0x907030201080a0608210405120c03060c0a080403111009030801090501060203070201122003070302030906061f03020d020d090803010e010909030c02010c0f0606080705030609070f031e02150406 85
    0x55038980c0c0f80d10074001151418006000c010056803400b0b00e0a070b1010a015078054800e000116141e20394040600e20002003c00070b28a840f000c0c41018604035004007a500d1007a002c10040041990014145810540c18208001d58240103402503013803d150324540441d50346803441090034168480f03823050417510700220030002d60341c072100e04903203e104405010340414041201d030800c1000da58840c080f0840ba40c1104008044a5000ba508651007a601d48002940100034040d259800f80304140e003091046a207150352400c0170030b80400d8000c500c051541410341c02314258004078040d0f0121070200d045080c08001d00380d06407800000580081c029840c010103003074008a00917260740300e0200c02c030b500360322002e48030b01481c0d0046801c0c40030400f08850b01900040f1141c00151140074102c081d220000140200d5401c03d41071501e8420000d101007560745c480c04d800c1155424a02004003904e40001400040c125180b0248481424000e40290000300308554030007800b6100b4042c1003520610ba88 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 169124748 1250 169123498 169123501
    0x60a0e0705071a130b0a0b1302090f03012d0e01091a070318060b01020a0f0510111204110a080d0c03170f07030b1818070e040b1303120203090703020108 67
    0x1d483d002d42404031403900440400110700c10200308000310780c6520424039500407440e0310045000c01c0906c0340b001261000241c001c00c0c5904645042c161214049174142c0082040d10402c3d50402c95940c2014101061041507180c050282d6010750010301001d070300140240002e40462521850018204102d020030207400d4010070030b15480f0b80035580f101e021035154804025000e4803000020f1003c800d00705e06510442801a0003e42e6441c0010b840e140120060002a071f000b071100300503503141c241d080351161020448010000403221185030807503002070002080394410780110f0b00951003a000304a4500c80c3c1400c0c008003903801044000c0040c0300f581d401a0320151803104020041c4266861850307100c1490010382007520907400031456200041c400b015014210380140d0030041c0030b1f07590413202001c0c0f041c04c880c50102003104c000203200c185120509403502c0c1d2510801c0060103401d84070340f005d5034035002e41410311403074141409114001045580303041040103507550702030510003280450030000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 169125998 1250 169124748 169124783
    0x61b0a02190b030103030f0c1509141f021e04080304060e0d020f0103050712060803070b01080c011b08040e07050c010b04020906090607020a1a040e160e0603060a0e070507 75
    0x720448102d4140501c0039041d40d0031a9070680d11001185c024104000200d808800460290b004105103d681048001084221400c080300e003408013208440940d840141980c802d2001446800c8540140b070000680750966020043c0b90144e80d00200f4021031804207012625401c080020411109076480b51280d031160401440503620900001a60001c0440503680b20340d4001e80000e580a0464030f0001220464100841e0464103581c100040c59400071400c80c0411841e003210b24050304072240100302512010000902e040c2c461a60b0340c1d407040e140c180c0f840c10041e80703209590151009815109c01490905002400d03900303c5040307002c1541c20245480c113142010320071900030b0040a01818a0100c1c548148062a48904022a009501c1140000b02c4520348282038000d100018030140c0d5491a1080265041e00003602c0340d44a04a0490054021504985128103906058810f03544941d03801c0001411032071168000108800b046041004040d0311030001e009075482501200499003c05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 169127248 1250 169125998 169126039
    0xa080322050d0c06030c0e03010203010623090d23060a0903200d14040519080601091e090201030f050a06060224061210150501030e01021804020306061b0a02 69
    0x1444041d10f64400c20105022591194000b4501d407181400e241d007181c8181c0b0003103402c82c6e000743e100500107000c1c540000410b441c0c0740c0c4292255083e2000d0a070811400380c0c001a241d55140b0001003807a40d9592075000084010b0f0b003140e2107d06444250380091421000341c10250100040c103e0014015501c00719621228450500203503081c0402800301d14001e800070b9559085c0b40c80c0101881c101400009400d40d070710128004c06280066401c01610304e880045813421a040c0c00103150b490515698491001e103003e40906000b000e17070000b08100c501400140d004020f0300c0003c2c1f590f6801c1000700184264144c01542c110f403038940c01c4840f102c60102c0001d104040b2000d44031031381038400c0c0200d9420314101c440d03861660151401d4451343c4800c440e40e10110740203081b1000b07526103140020006503030540b150754400c810b410029454070200314010500203255404c61403003164084041016522002c00340c40c601c1106882c0721850a041903a810303581e8002c00d6040b4400c4a460400000a2441 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 169128498 1250 169127248 169127269
    0x70e0103231908030703090f150c090303020c0409020a090510150c030e040e0c0303120a1a01020c1306080a050c04110406140a0201150b03180613060504020a08032205 73
    0x2e81d9414001e400003541c580c85283d002902e420101130300e45c02400003042a81501c10f4165105031240c80342408068904d000f40e80701d1520040c240440d1240800c007007500840c0302081040220f8001402c19518030010b0b440d007070583c00183c01603241504006041c0c8504058130103032460301e203001a40c0000070318220f40030b881e41680100014490030782c081c4241400d4214103ca60a4902983c80c1040d50380c0100b440c5d40c2020b002514052a0042031100c4112503210303907504031f034803031078186040e60031440081c0d038071007011031041c3c081e03041040e54402d0748100380d02400161400d6001c0c1c803800c0d012800c0030741d40d6a00f601e802c144124038040038820222a200101c50880d079107038844070b1a48888060042650b0461030300030040d5503d41440d420014101054a00a001c0d41c080300c54403420b2070440d03c14514100c05003105551310007000e214202c00000c03640410a0341c410390114860343c881c4081440c0384101d601000451001082d02e24084085103a00e110b0103194104200c002a030725010045c82514 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 169129748 1250 169128498 169128523
    0x10503011109060c010603020d0c060314010e070e010c0c0602100f0207020306012309071d010207030803061306080f031c0b0105070807050a0f05031e0f03060111070e010323 76
    0x1c1085906403500340700c4050f02040c4003400000500039601c1d00450a40101d0213002c4035019120310040c8001a0548110700c81098880c01c032502c01c1d81001e184071203d4101a100b07406002440c02d10b400d5030303840341c401a425035a02c8000320007003554a0034082d69805805240090075030a150072203500196610030740d07000f10340041c020070080c0d00e810351031034204a806d0801c4141d00e64258440401e0b072070f00010240a43c8443d80d5080c90b005100d16010110001c1740c00c080c0c1150802d035010404903482d50280c03900b1080c100c800c41111a0101d400400401c0e4507032081100e400755121400b0444000b0001c3c08240c240400d0610401d07a001c000c04080380d660352a458003156003230000c0d00c08a48800d0280486a00c558112000742c901ca0f128007242c0d54030780030b04071303910350000511001111000001000402182448500741040303511400b495000080c8064100941d01c0c40240380719404000230001440100f80c00005943c603424408169445480251a4046403840d04c00490200140c038840d01172 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 169130998 1250 169129748 169129781
    0xe19020906160c0306020c03040501030509060907060e0307050904210221030601110a060c020f010c0c020d08130e270c01141b03030618010509010e0408120108011401050301 76
    0x901021249802c4501000c1a241280600d01c0840054038500c010041081000000d42e01d55261500040039900010011035040d0804401d01c55101030001e400d5003620510b05264155141d59000700e45442c120350b015940c40030301c98040c8003d00046258040300300d04c0740c881d030300c042c42e9581c0d20580e65902c2c4c5c0e018034080d5400e8180d460034501031001c0034540040f01450440301181048004a24100800704141c1d06103656034000c0851503010044403101c282050000c1c40b0f25030039104050058044428042d00441201c9050000c10018a04840b50b50350401c081e406501d0701c1d2061500c42600880b04469201e0410800c8120500d8401e5029014040740340101a4095140011560015410701945d0310b1031041c01030b6118941040b4800c41d12190000c01540c0b00c0c603084081040000c0340b0682c000b510b0358110014421307a1219510141550f188840c08046515289030856161250840c0c11030303296102000070407040700640045000c41524600440507981f201c0805089414030ba50354800f01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 169132248 1250 169130998 169131007
    0x90a0303050d090204020703030f050106090f0b160209040b0732130b0d150f080c27070c021905030c1002031608090a21020105070f020a0e19020906 65
    0xa4811002403254240b03444000c201c0e45050360200341a078220b10320440201c0c2d06c5045406814005100303c500400c0d4501d001c0e118140b5081c00c40949120700d02611000d1100000c0065401040540c1c0040166010340668020314080c1003800c1141401d80d10301c0d0011300c2d00c2603020b81e00c2042c0b8000240502c1400798240149078000440b02e0a503010301c001c501190160f4500190891042c0d001d000d80000a510100b0104103071500d054030b000043d044030000621041084c4600c420020703440002080c1550617411081c001d081b085020140408809102c14031501003240b590f9011001c41d40551080d0785254896400061211044916015a68050f48803209204e80d0380b07800e203c09001e010150066910705110114145042c00d2603036000c2d9903044c00001d10010074240b4180140044c0000d00b810400400348211242c480c080c102400b90400402140910a0018068024a030194020001241c80355111411110000100c6440f100030b07292140014281c480c1d4022580d42040081c1560b1a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 169133498 1250 169132248 169132253
    0x601080d0206180a0213020d110f030609070513061706030114040b10030501110304050d2105060a1d0f011509032603041a010f0b120601210509010b06090a03 69
    0x1070b080f101103203001c1c0c0e00c10410014050380b0f40141d41c00c035002d1519400f6a07119407800007001a50707114840c4201381201002940e0003880c034401580d4020b00b0454000c02d564a404404940a002d81103213241d80e0520318000285840c0c024010202c08a888003500704166a850308150032281441c3e4104030940c030120000700010702118199500c004040b2801070340d1500c039101c3c1d500b11503c542035408003481c0001440244a01001540346510051070f284644902c074091304078004220342120821281c580000c0b40b469070b01c00c2c1c0781740b0182c08800c0c1d5801005c050fa44812840f0701040d250b540c40c20701000008515110b0b4468081e0380e06409441d40f800451540c0ea40b41e10341469544030390042c0144880c0305a4890501000314021805042e541d841444242c600c80b01240341a440124a100c940e10308100c0c80c4d2054080c0e07a0303569a00341c040c141650303130000142c50300404000115101c6030542c1c40401c40d030a1b03590140780180d040400801c2030100ca081803108506c01c00001c680d208042e0b1204000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 169134748 1250 169133498 169133521
    0x30b010504110a0e01050c07080a15050c040e1009020c010506040e01020306060702010521010314070b090109090c0905031f0f02070803040803180d0f08060d120e0f090a02040302030601080d0206 85
    0x13071040062502d00c0c602403401080f1801c004240d0840d8486030004484a011b10912020002001a503618100582c3c100318070201528450b9114074000348200c3c1c000692504840583c400c000c24102109541d80c8000900c05402480203c4003a4461864070b07107040c500f81014401d07244a69005030586242149580040d541038000840c00c1288000b10b5000040c0c114404180034001c5201e03019110300240f10103174550410740c00303800c9511281c00c00e03c80c150141e030340a900324044542c640300c001041d12108400701ca00c10131941169070540b04a40103a804900100041c540700074a0710002c20001100c800310005070310a145001d040c000c0c2c140081004941381e01c005507007205120344500201c2150300d20190508803003d40420201c0c84144003584c1c010381052169a1015045a52426600b102d40c3c502c40501988807001041008401c03000345182c942c2000e04c03004c10001028202c1914000b05440041c3d032090204034081e020f007000000b01c030a40081c0c034400f01500d0b0340182c00a9620011080c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 169135998 1250 169134748 169134767
    0x13020a0306020a080603151b09011709030406030f05130b090f060103051c030509100507140705010e010c08010609090f0f0c080108060c0705120a02030405031204030b010504110a 78
    0x2a40104050400000a161031008002c48046138940500da407916000700350070304900c8070202c0d881498045c2000500c0c46c09221880405c051030500719103e544950040750600c1d003200c203000640e40e540742032146c48040080130380f0031102030b55000e001c105d890716031003803e880342529114007400012210000058101400642c410060b0003166841f0321008034007403501d10207900c2643e45820240b440390703040c8014816210000400e040a000350b08000407140d40c0d13400f01400c90b088003603a40d801714507194802c1303010003038000c2210402515241c890903c039009040103500c0c001130398a0a507a5036883c1c2e00032081c4604803162510b0f4040501d00c0c180c1c800c8050000c0e070300c1c415101950f48040da01000502d12401020903581d0b6110480e0358140070200345072400c040c105a00e50601031101030005000020704d0000c3c02142d00c15113854080840060307140d030060350419545405202e020404c904541400351045900842d01018181d9840d03052004503403502c4c0003030b55903040810900444d00e020704401e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 169137248 1250 169135998 169136003
    0xf0405040e0c09070507031409091303021c0503013006020d020702040606030915051b09030c0d030c050d090b090105130506030a06030b090d082d0703050f090d0813 72
    0x1200b458000c0000201d0b240c0d070484a800200d400401e40d501030540c8018a0201d90050202e070f2440c104c0100c0000302d10420080108090034514941d00d01094402e00404024200c507400001c00484080800381050b042400b42c5d66003c0003007240000040f06c915060000c40b1300d900d40c10500862a600c403070020703502103441189126000c0101c2c01c0186c4030340c402d02e0000c00c0107070350003d0001d80f5890640f41546400038180040c1c1d040c0703400c0c0240c840d485c4600d90000182c0101c0076503918030481c00b2900341185aa92958880019980c800606801010300f50a20340f0510603103469598183c3c058815007428043ca5847c214140041d9100f540036074020184e10890a0030010203550701c0c4001955a481102daa801e690340342c40c010020098103580260300010b40c04080e00039600d160b003005180c40001840c000f000341e51002c000a111440c25880005082012072402c070301d02e07140700050b01800043e209007800001c0f00e80000c0c5140f0303010414407607408040d82d403e5159120103e4120506000c002c05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 169138498 1250 169137248 169137253
    0x8040b040309180b1e030705060c01140a090507150f080c190e0f041a04020a11030c010605090c0909040305093c12060103150f2a050f0405040e 63
    0x1c541840c1c14403105010b05404000881d04130600414850b540c081c40398202d409684111180042d994089030705416601e054910070380b80d050a00a040c00341546c4120b020446a0031018084000c40a403c01d0114900490440310002eaaa6030300c00d4400003a00d51000001e0711100e61085000d210b00070554108400101075804c02c00785e9402c07d0380c4c161080904101283c1c491050241c01c0c109010002a0408121b4040080c2e405c018182c810401d80c81c0103c922581e4001400c201c000e00824040d1140804041126120343c2d028841c1f50003404140580c0b4840d158401c002003092060300101d501d412401b07400b0690030f4449650980c0d01c0d40050411561040050044115200c00040806804241d80100140c02c40c3c2c46280d50051100d15482c031800b51041c418103142c0000700044160440c0e9100c14280d90240a001004009200346c960f503e040300d08068001d440c10b0040c900a80701c0250499603100118101300e0280d40500c10348518102c2c01e03c0c2800200309070310b441c0e4011281d11985605 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 169139748 1250 169138498 169138517
    0x150a02030405061614150a0608120a020120180a05031905190302010621030c1101030605090412020106060e0d110d231902060324061308010f02070308040b0403 70
    0x101d003e0209031580d049483c075848601d401d4a40044403010359006a47c1100c1000802d040c4200b981e261714040e2102d00c40017a0008504060610075030001418038041c240c1c0200200c24021074682c41c0c1e0040c1500c0c003a4050311181c0010b20f140c5600c1307242c11190024010200a607040f40306003000c2c042c8c841c050f18103000d41200d48000c0c5041070b02e2900410700c030382d000060041c10928100c00c440118004104c40440d503159900020750802152030f14103800c00727058951020440c004a002c0c090a40280d6000049441440f0412540b90f90041000b442c5030000c0c0300850302e521003260000e40d036074440703036000100308102000324804407401001080e015041c000451140d032102c100301c556600b102151080c07005c3c3d4060200f8014044078882c1010f000c080a20150103400046903030002034051049030300d041030910506000c062454040380e8024000684803000701c450010074050742e201e542100c0d424802400305e00c59591007141c89103036041c7c403107510b40d07101d1351141d040c000c400410031800c0c03001200e0f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 169140998 1250 169139748 169139753
    0x60108060a091d0105090118030810150512130b18030706020c0a020a0b03060a03080906161103010f0e070909050307321b090910020708030402150a020304050616 71
    0xd042e00480c141c00303624543e003030560481030845034014001415a49402c0d4041502c0f95201443d91080d9050300d40071440362555041c4040d41807144c1c5c8500821007000c0c20028040d5080809000d905003034840050079641c40b40ba0245c003000b00074400424120080d00003500602c0e4001b0200304c4108880100c1b42052007a50380c120482e8450030007200c460340100c1c04c3d20210320f40310203403030301030a04d090103182141414008128610710764040184a840041080c03031490302c804040d503500c11209182400c0c24101c605000e0300400c03041e51150302a50078180f107028074048a0054250001c80311000349035180c07070401c0030402031084801c120f030f05010801119011414010100c03140b1041558076480d1058032a450f95036030b141ca802c5901c401e0304420518465003262900c0310384071610580305000286e48456040782000c10460918140358408200f14081c0595030024511440c4262030156065034844203030803003401004c0300500160f008010a01c03450400c0b101400311000c0c01e002d07803100c420403603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 169142248 1250 169140998 169141001
    0x5130509040c030c08070311040c0c0506160306090b0d060207030203070b09010509100b0112050910020f0c0d05040b07240203071d060306030a0b0c070b0108070306060503010212060108060a09 84
    0x5407819102000b0700c0341c09109000b28041001c0003420410002c0c0142807079039868110801d01001001e20403560f034012210054010520740c58000d501c0025942d1b10315201050320800c10030100c000d40041d123019000b0031550030500c030303050b0070090080100d0320f1036217184d84500107940701d08421803c501007800804006a01c141c540b5008a03940000031074146407100342c0c586086c8402c083c00708040d00301203007000b04da41c001c6c2d40c155925500480102e1250f541401c03213860581b070366020034400c52001800c000801a000054003013111040292102491a0302c021605030086001e80c5000c00c8013000485c4c00143d1015042103140e800401105200e00540c3e00a802c0341c104440d640d010a14070302c010380581c0300b50301e200c0700c0c0c9020468036203007141440008241e84d0210200c00a1840340d07404041034040c0c0d030110641d10701030381c001e0200c22150303182c140041d02e50b11203101c12908541031401c0850685018000e03250405a0300090011540c1c80c0001107801100140c00a9003145000101040c4c24045 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 169143498 1250 169142248 169142251
    0x21015030f0611040b070b060402040b040e2503020c1527010609061202090601080c1b0c0303030106030605151e180a062a050a0206071a010e04020406091b05130509 72
    0x41e000e0290700e820b901e050294103410010308c4107218520401041c04030151704001c3e03806484081e05102c06643d503031008a004c0c01140f4001d1940d07103040300c0b03002c42d10b107038103800a00ea00141c06081d80e540900316403204142c04070946151900c0340c000030804280140c825101c0e0100b0a8a900101c0c401d540c41c0d1410040300c0d608c1d04a2105010750707824003010360800b8028a90403040a02e4411540c1c03404020741c0348680205005102c80c42c00c82c2481c140051400c0007540082c8078014152581e95a40da1800b5008124911a1034007504807001e480041e24506800d80c3c070002c0b00500c4080d1008003031802d6003250390081030b004013680c4d00580544c0c902d03195603103604041c0a040e101c812091054041e03600303003011500010b040000c0024450b000103a070200300800101c4d4181c3c0d42a413958500d103450f00704000f000c4031141a42981d1000022011038298045014a000780e038100f0417642c403036400400390b0300040c080c1030403502c00c50003000380244500010464240340801040101c0c0c2c8400000745174400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 169144748 1250 169143498 169143509
    0x180405060306150d140105070e062b0209130506040b0108070c170d02070302060604051005030c09040602090d060903170402090f361522020a0306050408030403021015030f061104 78
    0x540314100123045030401c091120184c0c04450550419424021403480756803456020400044078110700e00b99640c0580685280c40c900030091819005980402001000e040b11260702c19030800764004099401030b54940d000e5035981d50341c02c50309203154654802291400200411080303040115000c4446584040c054261195000d00325900b421000c0005030342d005041100440c800d0300c03003041150303000142d9081700c1200f80e42201142d501c504007000280500b00c0d607141c00030000c85502e001c21119912a6072440d1182d180d4219483c49807410b820b140501b118020740100440010540c01581454085e40c408000720b082000465140307480e0311100d0a407000700761503082c4042c42d2040c560050002d40040640c1c038503004080e1500c581c034034109803e14500d086109012030b50041c155141e103090b00016580000041c451410680b0b080400c039842110150018001c8111384010200c0c1c2c0e00480b031b03401d0420b581c8129682e081d5101c0600c030b14021702c4101c07055995403001c0100920500043d000412 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 169145998 1250 169144748 169144751
    0x301090c0903020d0303091a01050a0608220506091501140906030c1c020a05030609061602010e06160e090105101409120d02070605040e1308130902180405060306150d1401 75
    0x60b0700c1c81c2c00381c0d0f01d900540c00850386e60023850041c4280d44600c02c80340c04480e0f80340b404541c0da0310b07214032195042080c801c60700c0d0b0184120902c80c2c00e01c0350024442d4040c074a458200e80d4a017508801d45078a102c02805800c108100b4182900182d20304400d03584d400c40c000905070360b02d00c5640400920180c491805c01041401040c03c4d12040d4640000070342c00500b8190080c20700781ca40800c1558480000500703401509100c803141541d414800d500507501c4090550454915060190031000201580840840040d00d40142c4403624201003200074101c032806044058021448030040d5504d42c240f8007000d0310310b2002d000444583d514106001040e900b1035000d070110740d051401c0207041030f840d070b040581805000c020410006e00600c910640c0450f45660985280002e441c0024462169480b0001460745003100450428520350007442c0308015450705501e0030511400f804280d903c2141c1841e4983c1081c00051785050b0381d0420310800000007410410342d551186d98088030703600c5807000c12043e030307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 169147248 1250 169145998 169146011
    0x5010b13090506040b04050a1703060a150903061d100203040201080f040b04020d0303020d0510090f150306020711030d030506010207060908030a180f0306200f0301090c0903020d0303 80
    0x28100006088001065180e0038480500c00d82c036215a10a0080e0009144204a0340060103006084c8903042106034850b0050100c1c01c0941d00c1c0009980064072080d1107480340c107000080981045900e00710480450b01c0700c4c1d0b01c0364915242c0c0001000144e02c00c0d02da0743e014592082400100740892003840c0d0100e40b0068403814180001000400010b00002e43c05401d08180800300390130008450b4495070458580391462410300d012006400740b05040d104c658140303024401c0c2c41aa8031007031010b07591000020494105c800e0000c809858000256504c0f00313008030f8081c004a4219001801d115020300c0c404043d8201000120345007000c1d4122882c0026525028001d1640c0d050010303100801c00380c500041c0c51400e0520320f903181e01c2529808402d01c44840c1030801c007118103070326613130003484250b11000140340c0c8d9042020180000c0d6181c01c80003146c4080e04c07400350485006941408181c5a0200d086a08105145004145100b01c0d04203102c51010000010380d1380410100040b40b2030350300482c80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 169148498 1250 169147248 169147271
    0x30d02150708010503070b3007020c041b080604090b01031a0f1b070201030608010c09050a08071a1e0a0908060f1b0a09031205030f0a0603050a0204021804090501 71
    0x140940a0300c20420802801c1c010807030b560340003070b8031b80c00d0382c00c000d9095680c1d5030080442242e9048040c00000b03841940002c6036040303944c0542041c800c055a80039958401c0754003082000b210808004403541178113444800d110980f10300001a40007202510003e8042c82c19160a0b42c5164240e0048880b41e61141241c091044917a00c0c45411a0302d111a008090604042c103241c44ca801075120008000003107948401e40e882600440300600e203c030001c0190254044005140326403d0144500504510354000b809003400501d100c21a820402091a50401c0108202c0c442e4094908038850a04011003204c802c0c468030020031550025842e03101400b40341c00303801418508000c11960113000c0a004010800d42040c2c1c031140c2c010f5414854654400c00303504103650640c402e400c00340140d00d00107214243d454210000358003403282105a0345259844040400580d00d56000003405a0003112001c4018201034000e0810344414100c00385d07000a03100d01080071105422000d4400b42c0d104c1258000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 169149748 1250 169148498 169148533
    0x3150a0b03040822030201020604022b0501020d0b010c050c010c17030705040609060c1a1b07061a12070302060d060b1611010e0d020d020609090403090e0609091515030d02 75
    0x9006800050344e03986075400103911008000c002902510910701d02c00340540c881c24110381240d842406580041581c0c1c1081030003904002d0406240500c0d1602d04036140d07005170308141c81184c2c00001444120000001140c2c1050b0030841213a074098000003144000d64540083c602c50324641c1e40c0c4a4440d40b40440050410a4550144041c00f106440c11300215601702c210303110f914034034a00080342e80ca0f1500070700030f8095201710b081c64140d008120f91081064a07000007070320f280d8400101381001d202200700724045854010f0300746981c0c0070342010801400c00801501c8107060940b0001241c90795243c0c00c6c942035200d01130021204058026030340800200326180a4a020284cd16a00b546c4200020940f20406000060b00c80c41c103000d8a0821580c0d010304480c0c2c0780c500600140e0a0341441e01e80074080c1c45280c064481031041800004517103041181441d441a6039840052102c50000b203800760540324040c0c180c403084485500c4050703003a01d007000740801480c510350050060302130500c20450b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 169150998 1250 169149748 169149787
    0x3071509090c021515030706120e07050a0306111e0912010b01050703030b0a0f1205060a09021c020a1a0706050c0c030a080702030d050a020c0f1203150a0b030408 71
    0x5070320351810002041803540090301042440d4003a0b21408652110215850702079007032080c95030306110700d10300461507c1e80803070f07540f14805071101d007801480e00142c3c1c85038039080326008490300501d031a1400c04c08612982c0142da00e1102c840125440d100310554101500d602101500006400014030400c0d1814182d540c5221341000d00001c02c0105500303c002451380c419a0800303410142c071041d4103040c682c0c03140c034204010b12a43c054000c038541d54442c45110424000070982d594020900018440e2400d0f02030795010540c02030141411226035085030b0002c15007500261713000341030801e0100c1d019080700181d940e0100d148501030388400c40307454100c05031280246503510184c01481001601e035400001d071864507400d030a20103015684d403901241b540c000e016210f00341504144c1800351072602c580c01001424462400c0c1d661442180755003503941d5034041c85242c00700500f0400a40d0324820340142e18a03901000f070601047eaa51103441009a8206803000e50300d4120000e20b01103c00503500c0c105 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 169152248 1250 169150998 169151009
    0xa0b060f030105090c0d0606091b110303010b0403030809030910020f0c011e03021c020a0507060501060810032909070609050109060909050c07020d03020606010210063203071509 78
    0x80c0041e01c0c001081e070707481d48000e19400307008111b65483d8400304035030307500004094282460304010100c0000160f400804c0d580c1d2b00b01c40410a82805610824400f10859050712028484e0310300e024516a8111107400c0020400038140c00144500032641d035640301c0c03514002000394003c0814a80b00d0405c00c2c2400780c58504641444482c0709004c50a44803090300011070351450074010f072901c09441070741d1420344401180031042d510000c0e030b0043c0307290010040c0c410303103000f400c0c104039a0b0307210141543d40001c203032200c1e8036401c408101040041e0311a10100714404011320440100c64072403000c1036810006449500380c5400040041c0f00040c0d00c03003814030060100742f0300100707120f00d807200141c6048154041d103a5281c1c0c8400c00644605a038078100c411b007903406041c1a08910003802c00946907203041d04e04030b0050046506001c000416030091400b903c01da01e203282010900c2c4401d125191074180380540800038481c2c2d2600d00c540c0d05210440040c502c915203050125400e850041c9031036000d4110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 169153498 1250 169152248 169152251
    0x20d061703130e15030a0b1905061311160602040918080a0810050901120302060708071205040501091b030303050f1005011d040501061205010f08030909070903050a0b060f0301 77
    0x792102c240e000b1401e02c102d500c00e0031600c10549440c40307240008070301c90120ba41c051084100c0380d010460580c01203480340032112441c885602d516004401a98403e5038042e500422040c110b0044007119400940c80382600e0444074540074204041c24010561050140d9481c1d03030202d020010301c101030088400c0c1c050f038007529490420307003580d401400e405600b0400c0100004040081c45103008840c202000c0c08004150019545c0c1d108400001c1c0710000001f200107024280124040500078a0b485d8050740310f6071500e405260526020700b0003803600038810340d0a592a03400c164045040300303031642e080111240b0016046821410003a0551703074090041100e50404004210912010204001c1030304c000340717800003000b107401620050b081c0142000300e602c14a408000070b0441e0f0461254103519800f4441440700340c0c2e90304440060709840b03209100e10740e041001400c0d070600e04808401c2e07015580b41064840070340c99440f128035100710740d041102c2343d0000708244042803418403444501a01e00720700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 169154748 1250 169153498 169153507
    0xd030902182806051302030601030c0f020c0415090f091a0105010509040e2b020c0111071518060e09220809060c15060f0108010305060112060906020d061703 69
    0x40c07210818185594004090610030700700501c2d002d6600860700820004290784102d0100c28080d50007540241c60f001d02080c130f85030b11103c4a86c000c0340c1e211103414080d00035004e40300b140b00c01d01c0301401d103600940e80c3e0346a05100105061107140b0484984c00700b6564000341c081000d2401c008070b00500050b05000703d0490004001907a8010100c0c2c03c20b003000e03900881e0315560484031910780602e84800500c13000041c00300b008071550040d000700c1131000c55421509000d407281c00664403840c0300b03075030424190000c440c14069648060f0f4041207050040c40d02c50500300c0c07140c61075001105203402c103100107200305d603d0442c0703850441340d003540200040300c032000858480a13203940a522684002003541c24045000a900d0b0748246c02da0305140041c3c0d0035290b0030700c040c04020718022411560113101d541c5503265401d031940301f082503d0503030342c0c40703c002c22050f42445d070034850a01000004403455030702c610072030001a0311800517001c507004512000c5601810a06156410341810f100813600b0b44c010301 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 169155998 1250 169154748 169154761
    0x70201051803070f020406030f1407050f090c0306010207030510020c0105010603020405011b05070f030b010504200d0b270702010c02030901120b1801060c11011b0803090f0d03090218 80
    0x402c40d90140e6110340d41c0041030130b0b14800309000e40303500c0d80040c0040024048031014804840c850807150f0603014160744105440d44104405801c1c03a124171504240c54200080c440541403001310f030003c10500440c0c9445039030f940c2e280d103443d0442c5917050b6080d40100708040440c4090050030701400c2c00d400c3c290700b0305042a0001f0f00392611000c8003050b0000894140040c85418048040502811565242c2403600d03400c0c907404050003886858051403500b10058240011a19402d2a82101046551400311200260f4002d800061441c980c801d0340c10a90380c6120382d0000580c07001c8a06410400b0841c0b030580006801c50b400c0c405006c06640080004036020303a4400e200c040c441120342d400061118001c00490400740c004420041820300150001c1996500280c1040b5050710031030013000d82c81d00241c0112090040c00c00884c266041012007600001c1d8001c001c2d40d40b03d16000100d9180c0d0788240210382c174100b07034800c1b90b101003035440300601c00b9810034080b49540141c2840704c0350803900b03120 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 169157248 1250 169155998 169156003
    0x312060913350915070b0c03070908010c030b09070c08031612020c2107050d0c140a0c08161d10091509180c060f02030c150702010518 59
    0x14000906010381d803240348000b9000d45010b403002540b061403000c000004600003000903845401038611860001d0011000d9000e04070444407803d910032030030401c64031101e04003009504041d145006001c0c10362404100b60300700344103485a0400300d0f40d02150f40c1c002039040c002c14810281240c003c01c5030106401c0046069041125000907032007031043d0200b000c0c01e00485180002c0401403944500004039111300840000300034448481128031007400d11038a4000142603c1520f80007400c9400810082c1c0c0c810b0b00408040380454001c00c0071a4888185041d628240003450300c0c2100e48a003120700c24010760f42d00700107001d031640c0b4061040c14901e082046aa12819101d48043e6410180000048856000306200002040a03050509c14039040d010760046a460f24050705007c00e01c2e1041301d010b16621000d10801e126008a1900000703400c07e60200d9a20760103400d003105500c02002005440e200412250400100034480c0030581d06280d41d0090950390054142696007203501102c20640030007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 169158498 1250 169157248 169157281
    0x31e07020a0b060d0503130602060903070f0b270f07060c0305030604090305190e042009010305150a08010b1302070201021b130c030209030709060b04061209020307060203120609 78
    0x149014041c0d80d522000905401413524006000d804085450388926104542c0e20040ea02170740c0a80ba0182e84038032100c0d680e070250b070340c0c05408400061680c101250480041c113400c0041004000480ac1186155900c0c41114941d4916564007400300c000d10400c0c1809800040e140e0303407a084d0805440c0f0346005040f800043d041c1c0c0d22076a924080e00c000c05004008589a400c0041c104103280888601e0103070000003491111409107041140440c070940940100d5510071103a00056800d00c1c0321040118018200180091015201c900017114190383c1c1c2e014040007002e0802c004608400c81c0b006001801e801040e42624a07030052104500503a00812202c043c501400a1030141404500001310300300c2c0041140160245012052800d83e0340c1034000f40184641502224801c81c1d4451203001100c00c184108030090500380001d0000714403d0000c01c920310740542022411203416000641000340590001e00560310000d03130700d0f0005070b0003c01d40d6802201201c00400600c0c01d4658201450072 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 169159748 1250 169158498 169158503
    0x30c0905012705040e0d08060a030201052208120901020709020301240509061b060702070e01061209020907090512030306061204030507060603080d060e01080a060b01051c02031e07020a 81
    0x8501c045025807035002c1c0c1c1e540002c20005105009441c0007052031601ca0381d818410000094286001600504050b44540c084030b82c180e455a241c0001a9032460080c1401d100321905092020381c000343d1120304000801d4100c040d0b00c4541c1d41d408940001929181c1903610030602e450044c4010001c80c41000c0301d5111100c3c400740e0080e00403842c0701085420b80304900340e0350760100d4040703596003011750b141100d5411000b261084505684030f554060b681c4020780d12400700104802c00050044510a0020f0541103280020102d4040307900d6000501c00c41d0100c400b00d001076400d0008108910b00420310803070300348800c0003441c030710b00304000400c0c0688141c141151107401e4950101d010140b086089880c11608200d00304845500c0780303085c90041e0b00031490365980500785030000c5081502c00110340c0c101da2514006010030a420b0317440401030700300711103401c0c103124052040c05a40d481d070795130035003c400d008003005982c1d1030400c60103859080c000e0780440b201d100c6072041084998002944001c1140c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 169160998 1250 169159748 169159787
    0x90718171005041e08040905090703060c0c110123120f1b072006070f11030304060e09070302120f0106170405030904150506042310140d0213080a03030c090501 70
    0xc0d0729007811010381c4607541c403260340c26123803000f04072042d88081080c4094a10907041801a51032643c801c80b540040945c01410915107010701d0310541d8000c41000306440145a1080400220813007041480c2d0081044c0301c000808072410000070340c400c010b10a0703005d05500d1400c08030102e00030f0745990b90f0040c840c0c0103008054540282403482443e250404104000500c1169600c405207041000810101c00440da5008080e2410003d4513020040d00c0c16602d02d0f5584000040c910401c1010301e5030b01401c071400780350b0301b00305500710260300025070303445071440c000302c04182e52604200074844400322810079601c2c1500418840002d2003c400c880504c1070880d8040f52980351445802003903161a8070040d40914001000182c207070031a15101c040b0f083d140041c180d15074200301403100405100d804d04000441d04c1e20414020055a00a018625828a8018140380c040a0041c0c004111508010342a41c0030421040c2016030500078148151458980f0300071281c40d10001800100309400e101e205e45 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 169162248 1250 169160998 169161053
    0x903041a040f08010903080c09030d120f18050609010207030f03090606170c01110a0f031b0516050915030c0411070606030f14030a0203070209071817100504 69
    0x21032003101a038014200b003404220015a564254a00912060704102c000c2202040050892048078050710707819803010f0050024030829140c101c0d614050700380b10115040c3d85188092801c1c542c1c1c03007000d00e8582248410030b400a828100b50f460042d00034080c128585c0108081d40000c2d903c040c2c02203411546040c00300e00f02603189090b034081c00c8107400c002c2e407441d03460007507ea08650000342e11f400d0180030b0b00c032681ea003541070228640381e130002c030b002401c269082000280005d01c17595013100b07035543c0304072031a01030318031583e4507400d210701000c000c4c01c4581c1421041c0510f103407102d241c41c1c00005d2000607401020010b800310382c40b508144c071070324441c41d03403180d0010704040d1410403610015403120040002c40c3c4c0f207151045c0c95014611090f60000007041c4041d001c084000102d9000c05442d800840c20545a46e0800900310402000300f41080340454106404e081c06517a100041d1135002840f00d00c140c0b0300c0e0303102454505801d0b10200340d94282428003002c030740c0310308621101c1141d592001c40c40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 169163498 1250 169162248 169162289
    0x50c072117041511040f080102120c0702061902010f0b030a0f1401021c150803030108101e051303120c0c0f0c0b0d0608061e061009050d060e011103090304 68
    0x4004030340f101c207602c1c075080455001c0c0000c94200140b0580340301e000d8a07032045459072019400c034004c402c2140c0e070004031400411355000303182e4050440e80d0700c02480940340c048117080058001d8410000100941c0d110100441c045000e4001c03402100019001080041e405484a224000403520701800400010b18000e010351000c4d0101e03038901c90341ea40c510303a12030b0019003102c0c01405403c445c1c0400b15000100881d60f1703400070048904a603440030040600e60480581038004246102d01a000c501c5155417200d8146642d0165078840d10f06042010340c101c0c0b02d8103020349498000c51900100d646000045640e4507003003400b03400000e070482c12030a01694640345c0088007443c2c0d5081a030920308081800500404030750001020340d40da42064682c0794607681801d205501e520784980311220804e0000861604009108042e84880352808010042e502c0000c180749403002c810564909441c1c2d00c5440c0d0010090043d28401c038031039026603182d80303401281262240601c0c05101c1040b5100d0704041c07003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 169164748 1250 169163498 169163513
    0xf141e0103320603060f010e06010203070c14040f0b1302090406080105010e091b06070821010605070c05030601060203030c1806030a1a0306060a061110050c07211704 73
    0x2403441100c1d441c05408801040c01541c88440103440c0141c030603000010701e413820b001c507031240114a4800806416400d103046120a254010b04850440c4001d125030b83c01304050191080003008065074102c8103c142c50240402d6644840c43c0c008100e05007070914040340c0720200784034101480d0300300c0140c44405040000d07010300b01c140e00c80a485e608010011485181c450305003801008101c08861092a10800329040e440c11200c0d82c41d401f210620400703000c12040300060031030034182400b04010714410400d6002071042a0010000180081030071420020100c0e0104c1c081e0400f280148010361420070020340d240320080c10a1035205c0f010803c00c00030181648100c03110b08004011a46925150b1500d100401040048a4103980701d00c02c601c00701d0401003001c0340a44005400c0324a09800c000702030720000038010841030584176200d0000c424007520b2003200e0040b01020030032a9034041c5402c060317010034268109040d4020915886241041d000103400702c0d081680140c8000786e40e11400c0c51103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 169165998 1250 169164748 169164761
    0x5090105040306050708070f0903020f060d1b110c010216170f0d0e0a0e0403080601080921070b160e040504080405030a060506090912031504110f040f141e0103 70
    0xb0005400c010a000080c6e0b0400140d5100346020398a001545503071f8003044401c501e66100c06500700010501400e50b03404e296008050808101c400810007400c0f2400c040c100769170035885100000c8071070803600c030700c00c4c4c2c00e202040415901b44001d10060154880000c1520382d00c0c440e420035a18a00e00c0480f6400091045a6400d020003007030307400c12400002d0103064552644002071080d50101c41c0800c107a0561005540030701e416954856040c2c0d00c610064130300c0c584c060010440d91141c100c3c85200c00f4400d072010248091000c40058440e000c40c540031500300c90281c035480c0d010b124000c2e6a8410750340019203800c0044115804038198072541042440c510464010f076806000d228044000d110603600803601455090700c80c1c5c1019a20119903e07164411906c0c0c001c61000104042060b140d5070100e0480e103050b00902c0080d208040914000741075101c0c0d941007410550116041009080b81e2000c8030013000880d1441a5800070080051720f000c007008006601d1310300070241c62010f170f4403076400359 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 169167248 1250 169165998 169166003
    0xe010f09051306051e09060616110303040504091a0702070e1302061207081503010e0a02040e070e0906010602060a02030c0f0a0309021201020c0601090e07060c140601170d110d050901050403 83
    0x1d80005007070341c030700341c00c95103d170583d103802083d010020980c5411700100700c51011003d500c050f04214842d580f1035005c25007070581c3c194188070510010a030340d07656125468842c7c2c81660407441c003040d80103a030f100f4100010041d0040d50015241007021a07903c4254642c412065609030940c168544006600d502542c00420510190303501003248198015110b1405103160400e0f1803135001c9200c080500740c401c0710350082025040380e1030307000050402e5003007058550341ca034050714425503d0b1405140c0c40d40c4101d41c2c40445d940458010000c0c030340c051211503007040143c0c1b0194a1031410340e04140c007510039002c80c01460035002900d858900e00c26880740c0001d079801170408040300b5200301218081e400c103207a085900d005d10f400003d500281445240301d6009500090300c0301a182440075a1540c1c511392007075804110529040c01010b8060101034060310300d0303040c0380e2803000407004900d10300003801c0c0889040c40b04440030748040d600c00107149400c41c5600d01e446039031120004012181c500540c2d000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 169168498 1250 169167248 169167259
    0xa02040312030b030c030f031c060306020a0206041a01080c010c0501204302011101090303020d0c0e09040803070207090f0203040203060f010e0a09031b050c010e010f0905130605 78
    0x70400d0103500d6081009000e00407412605044007220406444040d40401c1075501c2e4420003900303041b88595807092040003104100015403e50b00d07102c400a85e4845115000180c0008040008110101c0c102240421765458421419810451500c1da240310700005241440030349604081004001d42060040c0394004000050722045032a00341c546412031503e8240d200d03280b49044030300100207003c00c10b0701a4601d00d0002004101103a203c401c80800005074104400f01110080401d024021140003512942d80140d40308030040080041f5414460010b04000224014100540e10082c500c0d42182e0010406603407034465800981c0343c52440c0c0d1100607080e080c456020b19071142d581c0503501c158000c2c1c0603030300a5550890b04c812a22002d004028001c0c090502056400384c0992215120900c40e0a280411203074040024412064208040b00c103a48161002c151650707000505020a00082c02c100340010011100504800000c0c05002e004603024004441000d12a0b08004000c14000d0314 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 169169748 1250 169168498 169168523
    0xb040e07121b0207050a090c0c141c110601090c0e04052203181502120304030215010305100b0418060b030703080f040609080a080307030203060d060507020a0203010f050702070b030a020403 83
    0x2010f510b540781d41c030555126011b1880b001078808240e00070441200c010750f84611503001150380707030494060320004e0700030184160325608510b41e0300500880102800c68603007492030380c5034103205443c1210513080b4200007030034450022100e40d00103d49811205017150040382e2980ca82488413105100b481c5840d030003408410b41381081c190003410100000d00bd400358484200d071140c06140c0c5644070040f0342001a07020000c003c80000450014681041c42031050310103a2070340d100c508181017000c0e081645d403074204c4007203804a18500e2142e206a528103030382c10303c80c40240c810142001002c841025102a44071250114940c3c0c042c0728100180d5030080801d40c80c2c4042411103c0290080e001d0074010480500b004161811b00184038038a140c0e0198ec85403850341d420004501940001d01501c5c0c200c00510240c100080c0d280c00360300e205803491f0b40100860440c900415007074450820015400c1c0340303804140300c00e040c0d011842800342d800072083ca603540d4541703901840c000c0c1700f1a840a00840000c60 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 169170998 1250 169169748 169169801
    0x402031503120a02010f0c090e0405030405040218030114040213021c09050729040303120b0307080d14031006030504021804050606090a2c070522060b040e0712 70
    0x500f41c030065030ba00812052001d0301c0b2100444a25020240100700c110300104050790640c003855520902c100256401c05603502c0201d0280c0e00800215a51440000c0c2100b0079414244161003040c0d40c94644421281407a4002c03500411b80c0002d00078a0603000104500c02d0406611f603524079421915080280300301c18200319890759400c0c01001e411080b001042d07545440403990382c0c140c403010f5080d141e00d058603650b01900c80345003840c0c0c40d1a07060380356400788036117603000c2c48950010040500a0316002c002803500a1041c0315101360380e0094001413041c050b8420b90103039101c0075640b039401d000495442c0d03400010f105003c03c86c1161158030009040104101d00403802d00d0040c0400d40b8408290340340e49150006035040d890a10305115080c1ca048220b044210004055030003450f003d44440580b107001141c40c503d50315107000201c040b078002250807580544a008000c0050a890300c0c00c05050030403000c0c4101c00a07020100f0841104007840e001c1d1070503171040700d604040840b400038400301003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 169172248 1250 169170998 169171033
    0xc090302090a0f0b010c1113062d0b0403050709020919030516140f041d03070605090c0f010503070e04020d02040e060103050c0903150a060305250902040f050402031503 74
    0x3d0300e440c0c01590501c4520399a55001c0c1980020003135105600e81a0782d8010418060f0345000101c01c144c0712501c491000411715407011401443c88001c280700908000120300c0c00070021190760050303070300100c10402040800c002280038000d40d41c1d203820159803070304500c00081e000200da04c207211451507a1140002004000031b00740181d0303030069030418401d90395000004188003245a526401280c5041490074600c2c00740e024000d1404070310700c0c0c820762a13012118680b07550400d503c215441b135030f50414002c510f08104001c1c0d07003954040300c81c0032604460030700007051070102625240a02c0440c1d0207034105136840b0b4040c2c51003079004800454483d580e030320401c81071020603200c181c007107440e01f40440c0f0a200f4800440710701c0c0300c0c068024500d1415100e89030006c001c2c01881c1c480029030b1041c000c00080d109100f00180000ea400c800c511725100f040c5021000540340d031001c04903a204010030444502c099a07403000311641218016140e83c1d6400c2c82191402c003007041c2c0355050144c015508a80c0610 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 169173498 1250 169172248 169172261
    0x409020f0a110303010f0905040f0503030a0b040e0a020a0303050307110a0614100302030d0c0303140924090d030e031224060708090603040302030d110d1113090c090302090a 76
    0x182c0c0d6003030040c400704401c050b10380c8000e004491101d0f01c14001440f0141e52904040d80152181101c01412445070712990b046400540b000b02c201622030031614240e15060113170183d83d003884400341c060f01c0c2d413640c001140c040d0030788401400c0c0070300400060390060081888450320107402007a550368950310b285c0301c0c0082c04000c022440512007000841d00d003601d5401c000302505e501500030102110244400d0380c40b588101c80c00c404041c4c8617031003214420318411005004072035000084c1001c0343c0d84c810b01041001101c1c249059007040c2000c00c101d41d00000740003103000c10300e428005880d040500f0100e0852150074400c0190402940600100e00d0038a86428012141540c1a883c516140d000f005554442d4a001038860b89051048040350f107001c030002e5800c40d1003801100d1070b00d00500344a00588a18544140341d504020542d25038841e00c40c019519590803440680e407404156052460305511980202c0c995143d071502030741501401008101e024680003010900246803d414800150a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 169174748 1250 169173498 169173517
    0x41b03140a0b01080102090a140402130308030105101d0108180303040302060603060a0209030a08030a06030b0a02070303180b130c090f150605040302091302060d0203040f0b090c03030405060d020409020f 89
    0x840b10001500d03040610075182c1c1d034507000b410207040358a080c1c03040c040e0080c460b5105901c207508010010070f0410b84451940298032800540392607601d41010032040c507624203e1b000c00d00104180f940d04840341050742c804c07001424207060f07130240c40b02e9460300e05030700d200580d55180b032200005010906400040c45441440128101c521a5403031945920680c00754000d40c640591120544400042024021b142c2c0680e21500015045507a9113940c0800c40b001e6900c400115400998103040c5039250050300364040c00100b071404d980c90148c0d900003400748001c00c07070340855000d421154104140d2610032002044510000d020b5031344081d0030f40004090710f00c450b4203c11403070740700011001d02a000740c80c2100d800034000c2200d9503941c10b44c2d089810000d1002c81e80042c0410400403d034855102650041c0e0041f0502c10740300724645024000341c40c0181283d00d803603004004a01d000e9400004581c00c1e02c000350794058403130a144030748038040d02580c2c1000c5250790011403810300d0650721001401c50202d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 169175998 1250 169174748 169174763
    0xc01050105010516061802030106060f0e013b040f0b03071a19120203010308071a09032a07080f0d0e1509030a12030b03010c0306050306041b03140a 65
    0x90307880d8015503142c0304413a4200c0500e0301298121011034030a601044410382443d815581c000107907400242100c00300c1e00b000340490450701071603010716448115a0800f500070b003860b40100e0035040f2606070b014994410440c0e4a09003130768807003903c050306202160104010307000b44020808551345a0240c2003444d0f5480c003d114100000840c401101c459440b0044030005041ca001003400d0f07907030305000220241c4000e015288400102c1101588001c5009500070b00c0d1164481a4903d07010019038007034940100c520103481d00703001140700044225012900440103c408103220074626030724840d0030300f080183c50b02401c100090706100c04120455400100d0707080e14604046540c058031441035809903d5080800801107030709448060001740805d483c010100c41400d01c460360b948110411034607841e00000d49840001840741400d003c2e02134180c00c42d0400340002d50910002c2036485100802c0500b110f501e01801c2607048150118500182d40c010b401c9145170044441c419966a40341003040701c0c030700b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 169177248 1250 169175998 169176001
    0x301051206040b0a0e07080715090b090315100b0d05010501110604030e010503060a03120c140a030c110a050d1a0105091515090d03020c0405090d05070b0702010f020a02030c0105 78
    0x110041407491007154840c00c51146078542900e01300041001543d4805a442a40d2021442c903608101000050070300c401c03000400c8451500084c04101c20768012881048180840b028a070340114031542e880303100303122030750882d40c840c00454100b1809a20014190710006508041d015158010606846003a02d40000d1080100c5501d6580e070000c0b134000e00000c4085014001c150310038001035411180003402041b04540329241d600352205500303000381c040b8640c0d180c040104804000d00340d00785a1404060400c1916a40b80900f124045041c014020010b85040500642c0c9068400c0c0140001414000c00d00c1c1e0b403890504070130081c2d0140075440921900c000034003490a940b181c0c2c4140421002d080017014440140080c03149070084080001c0000c1c840c1d41441c1e25075880e543d0807203010380e0007040c00b46d48400900c0704a034000b5200048a40101411805164200741110701d2198050340420070340d0b94411040740103010502d00740e03807240d0001170b45409641c2d000010300b1070040c4410081065 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 169178498 1250 169177248 169177279
    0xf060507020904320c0a0821090625030e04020a050910020c10020a0b010905012402030903011104050f01090608071b05070f0e07110309090406090f0503030105 70
    0xa00440600942c80640b201c0040e0000c0c0d00c0d60890360f03000080c1900c50044000800c001031031101c10681941c0d0a50001080042c640340140f8050001c01307811000d485219050342a80c0700100c042e8010030f40350440003035003520503110001101ca802c13142d0382e0400e600032010102e00e241c4c0416002c00f90001080f100c0080880e10b00b80c400c8405400080d16034a05d05407003e0180a2040701d80045041903005800e00e941c2c041e19108007005201c40150b0180c51284d60520b030881c2040710682080d45420316040043c012045145450721f16050f8121120b80c202c02c1b020b404034a54030640e644503826508040141d01119402400b03842039420881e9030340c0382800800011969000148100c0001407007540209440398011094121904030341c40d15250a84007039112645080e07590760000c080350880087c2080300300d04080c4c407184c010b240791502400c0107001032411a52801100304944c4242e1803007001c01c04108541e403280404a03405001c42045000908100781c494009104440c010050900321410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 169179748 1250 169178498 169178507
    0x3101815030204090320010608160e06010507020a170d030c03020702030c060f0906040e0f100609030b1e0403030603020f030a0c0b0304290405150103120e0406090f02040f06 76
    0x104429034681900216186408103c00382510090079000d000c1d1844000000701d030a60708849100030b12000102d02240340c50f28662502100001450040c00b410005000036056201081d4011000340791864641e505800010400002640302400c10030231f0214000d004440030940806c000c816860420402f07000000030703001c0c1d20801c04000c2d0325030429401c0382010b1910501411042401003101410520004040340650340700e6040790140c041003404000d41280010780082d8807200701c0c0d2409030b04518000c009000001c95000c000e180621403070028a1111800044c01c29404103481b01c455281040d0802034020101400141c0c020049c01e21400d809080008020440d15071216010b00001d01e04440800c9a0f04040c1c811910381d0444010074001060780c00e403203002c40075501a80403142c102440c00619280e8015142400d4041a000400100700030100c040900380341070500d211010400400100107240a03006481424900348540202c2d44203075014005139200e00d40b111000e50307240d68007500d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 169180998 1250 169179748 169179761
    0xc050c060f011d090c090c0c0f1005060301090b040b070e150d0c08090304230307180606020c0f0103020c0106030c060309060e010207050d18120f0b071805040b0f0303031018 76
    0x40c1c4175130080305031406a003007003c1e880d03a106107144901824032180111440c01d00d020401c075080d50754030010003041066814400c407504020118001c00100c11030b42d4034003601d01402480a4102410b07240011181d9001e141408681c5600a0014404005c0035032005403c0d001003d111011510705052515600c2c01070343e109004400b040002c50610f0f1030222064850905030505010300d00148442c41d1072030301c04000082c0540b480240e2241c205529510107000c803606940720908540c000700580403151140000031075910400c0ca03015a0b2100d8080201c3c0c0545050f41c00145010031749a8000b4440b64198441503031039119a01c14400001101551801d038000c5240150145d0801c4030a2808180100821540000000988031405949040c94607030641e0031642552000c0203c4510800c0050700d802c0705d42d000840f410700349031100004c0d489003060340e050700900c1d025030340c1d0303944100c5036a98400b5100f00302600141140d95911300402004030000744d911620180000b0310740c40d518440c24030301840 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 169182248 1250 169180998 169181011
    0xa1803090b07030903080c070501020d0302041a2104060f0b03011e091419031e140d0204030813092a14070602070b060a05120309040c050c060f011d 65
    0x1080d15505100e41c00c4100c1d48040c40441c180102c01400200048844002c5e1400914600280c144680f4160019040244800300101054170400c0709000020a8900101414514403619a03d840703d000d0100c040025040c260b202e1080d4010400c01000300603000081c4c00740c04c01c1000e01001c0d03910300615080c1c0b241c454044410001000e60310000410f60362020503454042e980c10400352010140840c20718001250000c85522600c2100c814143c0044103400707410388480310070b50114400e29005105148680d907111041c0b400280c8006006800e80594001d580c03c5590a0b583d103a4102d20b898110f040380c450000c0050030643c00c625410502c90500040820101c031000c7d4900c2587c0c0211085103158550712003801e0f040c0200d00c0821501d1014001041c401e901000703042c00e0407010014000c4045d0f01c480d01c514a0089082c002c0b98010081d568240c50607500842d41ca05c486500343d0b028000c001040f8260f200342802c02c1b00b4000d600c3c00f10741c101c601d051400711404d030802840b51070080044030030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 169183498 1250 169182248 169182257
    0x1091112060609040203240405150601080411032505030609031c020310120609110901050102070317070204020f0a11030906030103110310020a0201150503150415090b040305030a1803 80
    0x4802d81003000c1425442480103041d200a842d000b20f9000005c0d0150300d5454003524030404000400c41e0810100e0040ba4884203001100c1c6031420000b8000c1600400040840100d1810542d03140c9040180040080304080c040c44122644500e5100d440064850308c0d100f803080c08041402e840d03000c0101c680740254100041c4403500e8001044020750700103844170414624512000429110f5080842c2001d4455800803803034000d1420440ca8400000140318400c010b1080100110ba800103070328401c0741e0b4410b014070300307141740800002110301404402075041800000d0760115261548021300c1d101c001c0c0c0d203419045001007110140d5a015281441d034010004100500100700c161500301010300c0d00404a407600302d00710403100140e070401700c0c80c6c0b00980c0d1141880400c00718991705501c06008250001e00c44485000c2c540701c180c07440a800581501c524040c004508030079508541c4480e504005107080604041c9402881035204580c6080c6040c584403680b1001d001c02c024503031145425666 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 169184748 1250 169183498 169183501
    0x30503090d0507090c08090105091b120309030111040305070e01053001090c05031209060307030509070b0703120605011107030314070209010320060307051204060b0607050109111206 80
    0x284124a03249140541d000c1c0306100002584c00701600817100007071041e545803410f84c10019411400d41c0c3c0050301302c6c42c031a0006188921402d83e225592031100c00e0440304040c801056440c500d0941c49102d804e08c0e09542412008100c1500001c02481101c0c07148088030038440da00c81c25a0500300080c060903502221f034440c50801a1000d566103010354864100c140070398104880c40d2800c56110368002c81300c05a07035101c1004a4641486a4603001541c2c0d4005441c00c400000040c1403480010008814150340f43c2c045440c0c17860800c0000f014000c070300340362070361081d650030094110b2500d506c003090724508000d0301040e254440c030307204015102e00c1c0c00140340c03143c11a54140e40b01d100d21040158a4041402240056680d00d03030294001c0d8001e0001490710038099103070541101010080c02e00a500800502890f985d02c8006c036160030030526030f050807640b030b107150501c042c1649248240d408440030039400c2c2400010740c88507500622602c41008041800c206003c010310069181d032216820200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 169185998 1250 169184748 169184767
    0x803100e0c040312140f130e0f06040b010903030e12011e1401060306052119060902040c020303060105041a090901060201151403030a031d030f030f07080621100614010e0a030503 78
    0x401a013039840394135802011071f03900c03205550701c030400480c0c0c40e0090703c00000511074203045c148905070700b120082c41c200030202c1c10764030090a07005000712054050011456405d00082080d0311001d0841c1007c0e802c5004022205501d01c05005881a0313042c07044620000052903a0182c4600c404031000900700500000c0e02c0c05894000d0f070b4420546078828007071441c01813082201c00589403030151151a0019104260b030040c8800c5611040c41d4000350340c400c1003070040301d80e002400d5800701d43c1c1800080418192200d500001c84c010844007070340009640001240f0b10381c040d004804481c040c40841149150385000c24120103860702080c039010f800c10090016041d00c2070300f142500310841882012118010424a03145030b000072a07040d00001c02005008103940758820141d0441d42500e0034039a94100140020b150541146000c481d90502510135528018180013a218403495014100410b5070380e903028003884100000c03210300103100721001c00c0d8245412091107080c0c03600304000354107064401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 169187248 1250 169185998 169186027
    0x10608061b0c01061505040906120b06120307020d0f02041503021509030c060a0305070909020f0f220f0510030510050d0c03060609021b01020a020a0803100e0c04031214 74
    0x101002d03000355220200401d8020221904040d05043c40e40c5841c2d0f101c1c640410030080310604d801114901080040c004045040e4204c61504100c0880c0c4e0341d907101c1400d0100500d140b0500d0402500904007070898814000e8401246403164000d990510490604c8a4849401c010310301000354010000d050b07220b0001c80c0f000281c645420b014040b2031404080034002a845c1e008256200d00098070b80d0104400c003940994500010300d89420158100220158628044d0190384001000364501250421400ba000c80044c03056141c20b00780d4010b12074855501d0b10b8212003e00490b0f0142c1d508543e082e2001303201c1c0c443c1922a0348510040c0307095500786010031400c00c1c0c54010645091940c0c00c00400400c0d41c910032400105080a030040e80c440e000ea24070481059500c641c45500c0c0d1042c010355070140e401050100000b07912024180d42c0360b5a021240c10181100d030001d01200d081c40c0100144e041c449001001034034042c1c04103048200c1d440302e049030310004c2c4640c41c200100e401e1100c00e4520204 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 169188498 1250 169187248 169187257
    0x1080f24130906060b03090706140d02270628022e2003060103090c080a030903051510060e01140a020a03090509070c030c171209010608061b 62
    0x38248480e4055580c00202000d4541034a4100e40341d40b14607150800c4140d10600005010a0030320310b003145064020703640c54203101c0c801c04050110f5000103040d4410408200d521100c0504002c540301c249084041d00303519050b14800070a01c0156070244d05903e8600143d6120b290442234000540c50a45546040001529600b9042d4419002132500715018940348010300486c0000080d40340c7c85200540e0141d8010040c201c40d04981d10f90000f0aa50f41c0108803a4000c0003802c010a5400796844c1400380030456a110701c0440c000c01888800301a4001e0080381142d0041c012074000c00b81034040c4018801e4140c60720740000f00500c600f080680d00445403e59400014106802c0c0c0e4445140800c5496100024a00040e00074859120130950010078500142c81d003540c4c4682d6915000c0d10141c00317502c0c90b09c00a4144039820f200003003082405820800c0c103100c100070594030340380940351081c4005e5054030844240d50800002040e002c40000340f240c4109040445050541c03400900c40300103510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 169189748 1250 169188498 169188541
    0x2c070918080c0a0b04030203030f100b030a0e0703080c0703020307051e010c150212011d040803061e0607050102070b0f0c0d110705010c050301090c0305010803030727030c030c0501080f 81
    0x41ea6110034081030780703130030120f1140d4003980240d50b49180010545104801c0204070651580540a092003800840410741e03034007203108030000400c0a1a0003807103180a0a940c001881c0c1c003000207468a05403408901c20003103d00c00d600300c0700020b840350b040000c00c00e10341c00e01c3e0030b56003d0101310b00300940c45140800c1c2040e003c1c42e04050150311404041060b42d11003044074403100e07035050040107407082607070b000c40d1035a007019890360803420b02d540c0e0700c025031101800880c4560840c0503040042036144400c1007041d44020041a5107020328070f0114080e40009100f554401c00c1100003a5188401001840c800c012442203145040019214040107001020701d1142c0e010f01031000f08005842481104080b14240d1150703500c030743c07620140da4161400301c201034042608010041080a2000081d00d401c0305860422107951110000981200c5001001188418100500000600c0545852041540d01038110604100e45450056460904c00d0700d000c64000f40c0280081c1c468407411200280204 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 169190998 1250 169189748 169189753
    0xf030a020f1516030801091b0e030c0301050916050316051e120601080609011a09061215010f09060612090203030c0a080d0509010b222c070918080c 65
    0x14103900c5661990040200c2103044808880000181500030b1015070040407461f0302130006404004100000000b240070200c288051801c41c0101940c0a120442e00c8080c06002000b8610300080300d256941d44d228101e0118a01d46000800d01c3e00f4041602049041010342031400c113450401800140c00f602d4010144070940c0000000035030350780b40716017600e41e503210004051a5040000d102e0030184090490f0710319a00d4101601017903410124100c5400004407499034847d690600800c06105941c02c1020184c0541a8848011500c40e801b20b41a1115159201881500c0350b05d017001b250001d005041c0132540403401c1901c0da0704e0a400404c0d41500c01b40c01d49062180e410b8035103142c042101000c13203a0b16404603201c100100c40d4405c1c2607000304480001d0140d64460720108420b022040300501004800ca8a04111201c21350450030032040300346107101e11000c41c0c50b600b420040c0c110981c507809004d0540001440c2255006025000c100302c807100000f42c0d516034514420340d110040000060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 169192248 1250 169190998 169191019
    0x140a09030602120702010b0a051305041505010e04030e0a0f120c08070f061403101e0509100602012901050d09060510030b01080d0c060905011b030c0306050f030a020f 73
    0x307807140060310000a9055a44003503080100d0041e003507a00c52a0000e0203003510800405c100d948104001d0b00301d09402100107000d480e142001c2c0007405407551100308207410540009145c04030b60b508035101314042d541da85880c090751000c00c441c40840c0e115411460101d00c500b0b02c030380300d41c003e40d81d4030051203003480c80e420750b90314100706050003695840320400f0b03800e4078010041650003007142030003c901c0700d00080c554075000c548040c520307040e4020341078482603090001c11496601c0b0100d0000c1d040040c001015850300100e1030880c030000380600001542030034131030440b50680b203c0c41d030319021004141d078171001c2c026001114140c00c0850142d4a10f9150000b2102245240c42200d0003403040d25540d4004c1d906600700703d80c803140182d000110741d0b40207a004d040403e510000c05d0441a1340801c1c0880e165031141406800741c07140242700e2a11070030342c0340d0012a01b034150740541f26600c0d0380c0d28248a81a40c1c0c0d000c00c0545002c2181403900758101240724801842c1c0b85d4411005404010683c03c240d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 169193498 1250 169192248 169192253
    0x2030c072010020d120603020607060b1216060f02011407050c0718050109110c06060d021519030e010b0607021002070e040503071104020301210204020405060c01090611040303140a0903 81
    0x1200b21003900d08096003028065064840e13010b071041510340c1c8928010300040d8956808142d0754400c801014040716618204007805070340d440c4213501441428411140360b0344281e2001001d000302071103454003180c00304602d01c3c0842e0043c01501d03010b05507044801030a83e1101400e507450b902225000c0c10358040c00d0400301e413200c190700f03841241115450000030198106030090b412504959a108582c003828480c95421020000c1c4603a400304044e16961340c6d1400c40c1c40414981507496018000040000c200390743d5101c04c0300342503c85280031703a4091200c820040b500703600b2602c95010154009204202100150034005507000c2c020300b951044036441c556032800100501d10644044540750030004121083c856030145248910608440451540d4541010b0326064440040c059104035a981222019540c4980c140c13030041801038110381e03039001000c4280d8024400380d00100c913501e2400d24101d84000602c4150707416a41d06480e4040d01410380c1e01da10031181c0040402c24100721411201100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 169194748 1250 169193498 169193509
    0x20f030406020105013f1e081305041a04110c07181104060c02040b150d15080c01140309011506080712090c210c08030403021302030c0720 61
    0x401c80781d030000460354185080b284c2c1c611801228860b640e94140c20300c100b0241e0b09282ca421181000f4070a5404440b14505280344203811102210341c600804a80307424071400000810340690243d9202c840c817a11401080201c2d00c00c142d55061031030030780502c0c1140c0c3c14a6407248100e4050029072600b03040340200c182d07240860075004022004c02c0e6203054480d0078424010440d03409100c94100d420700f070500704010b011b028001303070181c4600c2d11030300304110340d888810100329802c0d00c0c80122540c0300340b028410805090020803028900600280000d2054004541d2500000050752090b0404200c1c08103070a103078102074056080c0355603c84000900c01281d010040040400d6180d41c003292408207005401464548841102c00d0f040545200001e4000e10540301942c25012480f4a51468455a100f0340142158028038038030300c20300c0219400304000040c104176482203031707003010701512103c549041c0d0101741c2d014014000b00744003201c0000e214081c0100d0051001d9528000550354400145 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 169195998 1250 169194748 169194757
    0x1a0f0f030102040312110604170a1214090c01080c03040620190e04090b0106110f0106080f01110f03150f040c090602060705040f0e09030403020a0b0408010c08060603070f020f03 78
    0x1110380181580084c40c00350469944206d28203008068186440d00e500d6843c04c0507001000d8245c08440000c4c655100c40c05900ca2004012032039608002d0300c021480072010800c81135900312028410342c5048a03040d84140001442401c1440c070340c90071a102c0380e503070b0005410462074600099903d44444070b8070400340c40c090110a01111f81c0584100c602c03500240130142c4a03a0404c5c0500e05000d08d01000c1169640018116071240c50549046101010b550381420080b21841f607455003001e02c005004d941c000303020111250103000030401d49400850b200c0c200d01c1400c0300c0303400e004010f03c0064103840b25000200c0500102620303685055294200040c22100340700b43c03281c0440c40c4404107002d1140d040054503800219414000c2c5801d00303001e203c1c808403800d8421118071001040c0001d110340b600384140d0b0300466000d0009480d803610764244c0700454008d070081079401c1d03280c4030890003d14403850f6028080c41c80502001c0c03945c1c0b64442d040f103500812003803d1066100340304005004080800092 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 169197248 1250 169195998 169196003
    0x12080d11091804061103010e040209040c0518010302040c0207290d02161103280203071205150a150e07020109201c02013f0c080a1a0f0f0301020403 65
    0x862689840e250000448217a0075a1400514041c00144070354003a41c0c80b44d9400503011501a41669101d00c5e00f201d601d072070ba400607a000102114000c1c00340082c2808641030b2807003101c081c803c1308110034049139070310f41071f125094a01b1042002d0700e03083e00d40d403260803180c18a0b21040c10300d0601900f403103500360780c000c1440c000e9100c164403006c001e0001e10000e944603180210064003a400d10081050035550045240d030b503000b1010310440707045580030040480140701180c040d07020007407107041c0591506102c4506a800408000000d070f0800180d02c01c0808020713100444180403810900458002a801450417007550b42c0c40310402d001c03aa1240f400d5203001c240c4070302011010100028810703820740040d090100101031100000060380c000c0d0480d81d030110541c204003450940f4521a8003400c08040c1818640c0b0b002c2d58074005a88515000006104440d440f80017460310b441e610742007100d080c90404070502c03144005054007481d00702404141e80f400204248507280700031000900f203a100c2c1c3d208 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 169198498 1250 169197248 169197289
    0x6031709031903021612061b121a030601090c11061621111e041d04020102031209010b0a051c0b270105041106161722080712080d1109 59
    0x41c904100d601c1c00b071a00c03440d00c2d4000f0500c076108d011f44060000c00c170200c0c0d0180c1440d1200410100c80d4050035402c079101d01d00030b04403510355035142c1490000b00b40d420010f50004140c0070a0305840c0b900000d9090140d0000b00103205604441041201c0c0801903440014203035984c0d002d49100d103842802156148000c1210550391105140202909202071a00300c62200750b040c0010040060308986c1c603800038400c1142c501d500d954501c0101d04520900b00740041401341c24080c030440709030560044003006801d85512201d103850324104500c480c0c496148202030031640312210000740e01801820b0700881c0d080c0e02038241c03c0100c080303885100c0b08081408904d80d920740401060006c0340c0191140440c040d01c405242c4140440041680390461002034024203a002040404100000446034940002d48611034074006101810758030b1202441004c54500c113000f0042228084852000c1d0300b42c0e4004100d074503010f128240e40000d405142c4515a0a6a052080483d42d85440c031810380502000c030320 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 169199748 1250 169198498 169198529
    0xf12010e0606120f031c0b0d060f15180f0608030f13061115091002210603031815041a1902010204030b010323030d060317090319030216 60
    0x380500051002e03c1200d03203a10408050800c40d03400b10071144420710128800f0130002d001102e8201502c0c0b8898402d8120b80d06002c4038080c0300195216a001c03490b450002e004015080c02020311803000c0e4014a099515142d07260700e1600002c1c2c0c0010300360001a040461708540d18401c450071341d008020003401301c500001da9a00345a038400a0800540902e0801d415040351914180c0d903500707440640405601d00c898045144142d00b006550844140c0a00135582c40d040d5840d1100c1102c154400788182c0540040429628034020059034095184c00c010041c280201030204100c3e028045003218139400c081001149801e8100300302d01c5091038041c0043d69031000400c41002000d50303440280210f92061005200140040f90001d0449820240502d00315522404103c106282c14142c16104d20002400003071090310ac1d00184100c0380aa030008040f4240c00e00e4005191140e40b480c10380c550441503101406a1411208018040c00303841102d5920030b078001920b0141c42d040d0030411100700c2e01c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 169200998 1250 169199748 169199761
    0x80d090b0a060308031f050418050c101d0409080318070b070c17010f0606090f1a070605070507080d0605090c0c1e010209040f020310170c0f12010e06 66
    0x2285a0820058001048294a0340d00c0300c134043e00001d8a01aa41d0034145007250485403200300ca080540801081041445040102c603010840a001e04403032601444500301503510b000c4101000741c58290721980d14201c3c043d620310041394140101580d0183c9d0300d2500030f02040c0028040d51041c00f4000c1c030414110260001d80f850080668001004048100b06c0030000030b101c1c0c40382c1800c8480d1088038043c3e03080007090080c0940700c00703403940c0c0400d13150000010b1115880780510088490305070052074203d40b501184c001d1003c6940a030350440108005180000f100b9501c1180d05c00da552402e141080c0c40381e924006542e00411800740780341e88411003440360789072031909160841d0304414103501d80100c1506543e100c0500b000303c0c100740842400c11000341c01c0290111024110010010042d1560303e0401c1002074000791010204281001f0021848540650b89603103405003d0008007412604c01c0d0030046071240044440c0d03003280c0b8003203400324000c10900419440b019004081c00507403605c1c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 169202248 1250 169200998 169201013
    0x30c030405070f150305180a0c030b07091d0406090212010c020706080f040209150a0b030108070609050d0b0a02120108030702010206070e0f0120030a020303010f08010203070f0302070f080d09 84
    0x3d4000e005805580b030010004000000d880c21400089800e01042695074510486a08941000351400034021a4000740c1040a03040140e02070740c0c4074900200b003030345404004841c040a54000d20420b400d480303902c0710400c1600c0c0090360307015100da000440d40031601d5010903000c0c2c1d540c034443d090b684e4449e200c0c80b200c282c050095102404251500b1000c0f440d02404c040c0c0c140c0f001500190007000c00c203000c262050100f00010444000c05040f11007569070320310041846038800d1207501103a010b0b007000860380e5446903401204840008104040400300b9807100d510701d800261180321030541c01c02c825030704400d50b031409034001e20648020b96101c81d141e000190411000508100802605c140800355581d00c10700d64002c4018213181c8183c107511012500710305490b041c294240140300110b81106455030020086040e40d85182000d00711a40d00d080543c281d02040c0c400d64003041c04510072000040c880d42c0a401d00078000c541c0c24250020a44419025900007021051884d454814071310501168 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 169203498 1250 169202248 169202263
    0x250b0730120504030804020613030b16030608030903030319180b07030b090603070b0703030f150315020304080d110904050405070501090806040b01050f12190b0a0b0a060e01050d02030c030405 84
    0x940c002d100340c0c5055a002050358030003d000a108030004201a5011104801c0c41000382d94014400d00c041c2c21b11401c28030341c0c90036410610340080d050110104203c0790100c10b451443c0f0001c0c00030b6046450392045200c00e08545034600c0e203000d40d600d412030810170010380f444840d40d00910140809080421005041e50040320140e0b000308904800d11060747c5001843c0c00858903010030709510b421003481c084002e0104246040040b0b4104181e01400c860074291442c00c89100d20440345c860384400c0c1e20340703050b4001214007a01d41c00d002e0219000021164100d010f00b80d0700c44144502e00700507000000c040320802e40b0243d8043e40034402c1844103580003100980038003034980040c444c41c9000ea850310703c1c0c3c0005001e510b01911003a0400b00d0540c490420522404103000f05840451944411169110b00d4107403060300c2c14550390f0086051742c2072510840c2041d00001c0c29107041603042c10350aa901c03144a41d0b4950400500b00000441107100b40f000e50302a064080c0d83c66902d0401e402c105281080c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 169204748 1250 169203498 169203527
    0x30306091b030209130f02091c03080f04020109030f0c050f010903022b0b01060e09070309050a1106040807060206180c0907030509070306050103050c03250b0730 71
    0xd020280c070210440110324a81403210340c40c026a40d29100d60110f440c3c41da00074504203200741441c58840c1002c18a0f00503200c071600641d07105210315998a201d00510401040107404182100e0210b559182d098030890362290041c10503582a82e62580c40701904100c001c0c050b1144030882d0024031040c80c0205207452090024640403c10300d095800041e03009452808071f083c031200c682d0400c800200703d00d40c650070140d00b24583d415150703503d01001c3c1250702c400c0c10681c41402d0220001d4010707402446411009030300600186011070075035a8288142a80100c01c950111042c04002100c1e00208001e0020b420f165025000500303001c01c01c0c0c1d01c000080030303402e02560404580d040840c1c0b03402c408c481d4001c5e20b0b4500440d040c0c0302e070b441d01c80c2000c2c100e800141815003060004030500000064000d680b68040c1c080700d401c840f80b0b100300542803000b403d84001c240a1004208104003219001c0c01d419800341011040c1c40003036080642c0108050a801007074404041c100303041d21500404098503285 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 169205998 1250 169204748 169204751
    0x80117030714300a0806130903020f07050603010f060c050a05030310053a110907030603110d03020d11010b030601030b0103021003060602031c020915033405031e0f0403030609 77
    0x20303c99034042d02580100200001080340030000201320782c0d0707441c6c411803814202d40302c2002000e410b420000c0d100c2c404020080c07140c6c45074007000149420210222030490b403006e116503140c00c1c00c05030111094402101d082c1c0d102c2c400d040b90a000b090090000314020700d41009111347d541d1070320f402e000d0216289403505100700c1d52241036800c03164102e902c00c0c81c40000042c03803079010380380740c500105104900f104080c0c01202000800c030032160140e03c02800c0da030182c0302c915030601c0204104000d03e5046800207005801c01d40561001c02c1c0941d01003100301103454004201d00b422200420320f030100036403003514035620350f600402c00d40c20f2003200301150b030245d40380a00440c0d08028010b9500d110b407440001000e001c1c81c0c3d69111040c0c0c0b540c151000c0e00401803000d00c4500000952f821103400a40e002e5900d25038111400307460600f06004040501c50b400400349001110500980e40b0790402000b80740ca0a07600240e0711824050464a644030304240c0c0707026416424070303080040c102e5456400111707940d07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 169207248 1250 169205998 169206073
    0x30601051b100614061206031006030602040e012102010e01030902090f04030f0206070c1707080a03090606120c050d050c060c0a15090503270402041d09060601080117030714 76
    0x944914048450058406d03148a04c652a40000700c2c0c074004c80340d8808002c0d40c1c0b80180100030014641c006000319925012950803690303c5e05000600b01094104403515243c0103d418001940142075646051905060000c4c2d200219004108000f200b241ea951448040700108010150007500340c4103c0d03001440181098588400090301c0d80f000f80001801d180c1d07004c0c101c990108000021a00160303070054255403103900c5003102402600000c503048655500304003010034484e44401c0080406600b01c0e4812460902d01418401110482070080d10f89014040340103040f40c640e0b800409691460b4030003030080b02150300f40050740305400d200311140c042c100341c035003c0801c03400019034401120752107017680008280e5144801004001c400c0360b070050b0002c140010240c00344006000b055000c0011030026a8411124a8807001c04a5000740414198001440390f000310342c4209041548060450b403400c101511490030407500c405200400754005c60a202c2e007851032190410007031859840c2c03100312 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 169208498 1250 169207248 169207289
    0xc02061605071718181b0f0a05090d0204090c031104060e07110c04060807081c02191104060906030203210a032c01090b010f03050d05030601051b1006 66
    0x30440c0f02100d030301d003040100f219107151240f0790031291046001000018640f44102000007540d004546521180c1550b17081000c40c540b1800440f10100d0500b08503514148802d0010341c0d094220514240e0003a40c07100341900161500d10541001034022440d01030706501c4c500d070800c82c03404d4501d0070702c0c069030600d00e0030400c00c0c00c10010203401111608107403072814a41c0030344a10b4149812540383d4001c0c24001c0c0000c0703071040418114183d401324030945111505001c400c944c01c90810700618010f0748400307240122404a89a4400076502ca1401001c04200303100000d070076100141c0106401c203075102d00410462800304044401040b0407881c010800e0421401581207005005014080c1502e075063718031390840100701c1280492450000c021401c0d0000183ca008000c00417044810251200010510b00200e400c00c604680c1d00c0401091549050441150f080d080a04800d05101d0184036047d10156000100141c080ea60320040141c034828980142c1074824030350200508000c441e00d40e108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 169209748 1250 169208498 169208513
    0xc060d1a040527120d020901050d0f020a2007120812070201022709010e0901110c03090f09010803040603020a0e030a0609050607050702150a05070b0c070201020106060f0f1409040c0206160507 84
    0x5c4a41d0785480040c0c4854a034401a102c40c85046040b0001514128625010408960180801d441d007940d0320900c000513807095959800707555031442182c1d030240000700302d81410309448110360391040034520f051114807079484510003410303a140b0707000d41d4011802e914004104510500181c0d10590182024242080425410b09040c09020252045070780090000c4c5003d4201516600f0f00d00e1080d555003001580403902c0e43c2051001034855014090500c0141c54010180340c10b072281e2034051440c103482c140d41139000f903109001c25428090701540102c00c1e40c1d014032218003018000d82020400031401e2800b181841c500902841c14000c0c18406140540c0f240d5078208618514160040c0e030318034210009039141d000b5100010402c61400c01003055640d01040a003865030f2007a00240806030300c4140aa501d01005400d600000e131203e640d80044610031180c4400043c0c0d41e58110f880d2100321400f060945100c1c0c40100d000d80d1102c42800582c0b08008402e01d5000722524180d41011110fa48506 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 169210998 1250 169209748 169209757
    0x21501180f02090a2309040b01170715050a080a0e031b01150b0c07051c0f0c0816063509120310080f0c060d1a04052712 53
    0x144095840c1c2400c510405141e04407902844010321014056030b4980030b141440e5041e0340e0b0030890b00b21a45030510039003040d1011038011a404150f080803682002c070726107281410305803480c40511941000003019150700801e030580d10500c1da10703da9280e5035034001515529024140c0f0785160324024070201e4945010013614100d05050030403802490114050030302604c0288410510001c0103c000140366207508010044442000d05440440d6510b1081000e000640c84005500394030003910100054150103502908910495030ba43d035030740d101d02803103142c2300d90300e09030116401810b001800b5494010812340849401d402d4511203800c6040080244150038401c1854503800040c00324060801c04c0c0094201d520720424226141e01d000340e4030032803a80140c420ad41117801403020507407503a40c0201d04500400005803240e0301d800c2e0b4150b0070740e00a041c804801d070b2111040c2d9070070390700d0307591103004032801211004d40301d1907020110215184498988800c06030264003180c0314105810707640c0c045c3e5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 169212248 1250 169210998 169211039
    0x6050c0118170a02010e0106080106031205030708040b0406020c06010b13051c0f032106050a05010201021201050922050a0201030b0105040f061b1a07080109110906090103110403060606021501 84
    0x645400f031409040c0e0141c0761540c150601542820004180d103c01503001104403805507201105001c1c05070310950f000d100035900030002620000c0040c0100e41c00103403d5410903c5600b0040ca4405081e0000341400b02c2070300805114440029810034004100c0441c00103000c0480d620f81050003104061140e0380d2004000500c0d1003c0704903500141802001c4034040040a4a00703504040185c1054800603c4035001e40e03840364800110101d07440d4814406d44029100ba041580840d03402e1604110750908000d1940300b40305040035440702e00250140004000da807003400207140b10800d0348005070a45180a0100b4100300c41404200154038030448018102c5d101401c1c406010101e500c0160300344522120b0103884540b06189034500e400d08051004e00c111030369170b0742d64041d90302da1080c5000c1d40d01030740440130a607105002000700c0d8507214000b40310501050400043c529070140c483c1556070401c2d03006a42495907110100300c2c2c02d030144460041c1c1207442c400c8005c10b605201e401c2d01c20f050b001204 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 169213498 1250 169212248 169212293
    0x90705011404060507170909040804050a15020a021e060d090b0a02120a051312050304060605060f04050f0409140703060e1c0c03090f17010f15030807060209040606050c0118 76
    0x40c6c4110003a403c088070102803010f80180b000d0724250801d1541913003d0311901d8050318448000040c41c008191440c0111082640a071801e89095000c000c01703607411079044075107106800c80b07a140030390b01d22000300981035030800c1c041801e84031400d00c00c4110b9002000300448030300401806141da03041c00415980044441c070f0004181c0c64520040c0984056043c0081030325004220500c1459000782c06544598400d0009200c2191604240300a07406010282201c29038103000a00c072514080015040c9244041c0c40010f5500c1d490b180c1000c0d05c080c0c0e49118056401901c020300a0001d01d000b86002140c2c003500401c811000700f5011210140801d20090400c003500100c6400c05129400c610014401403410081c1d05444041080413030609400742c540e03c1d031030b201007840048024081d1108510340c9000b69080c40d03107951162400c2d41c4c00f01400f142c540e82c4c204143c00940c0d40303921983c4007400151795019180c4841000d40c500f191401d0707422861180ca10420400000c00801880001e000760702c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 169214748 1250 169213498 169213523
    0x1501021b090c13030804060c0b0a060e07050c1603060204032109150c020904030201050702010c080105090f07090902040306020702040f0b03060126010504110a0b131e0806090705011404060507 84
    0x16411800f600c1c0c1d080100400030015000801c15804030440c00714500640161100d03440d0064010704a07402e070711410703410180c80b1000680940c043c0303018041140ca00c1068841c02070a44800d203004840e1500222901540424140240301301d01003d551403a02480c44d0844543c2804800342c01403c031842204081801c2c0ac07080c4003414400c01d4640700543d4050a03091390307410700d4a0041d001c0c00003180c80d03000642c03030007c4841c021481b03401864101e0300c01801c002c0641e200c450400c240c580000b45180103001003102d00040e440300303a100510041d400ba00c00143c030381d040c030301c100401c2c0c41c40480c0d00070030742d800c0110b440c0d01a42d000c5070aa0440d059502c41c1000850305510703089440c500c000e180100c5501e481d00300b02c148010a240302c4446203044403e40d21440d2201110045401008045440c1d0704120300300f4408164005188605901c85002d409003495480000501c0c0110480f00e001c0780b030f0080142040706580040d01c001007030309190035860a0904284008007117000b148400340c00d0340d14101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 169215998 1250 169214748 169214767
    0x30a051801110d0306080c0f010c08090a0f0608011509080d080403140d061a0f030711030417030c0f01020a1d0604090e071503050f130203151501021b090c 68
    0x80404480c0700401e058540d0750a580d08003a00a05d44e520605065001e100811318075460800c02c0300d880054161540d240010040c0ca070140350f41c004131079054001d102090081082c0300840c8015008001c0c1c4d5844400560401c40020079900240c6600d40c00d000060310140104803010071513145c00391440c60540c04c50795980c28110b070b40403170340f0403086545a0001603107140c46607540c03c520241c50075504004030001c038214038013101e0710400304960301402c401d0003c50000c034071510510210200d68070460b42859110070300760954241d8480142e105a00c0002c50f030462500a000e60010703101d11342c00031414410900c0303019248030030707040b4500386202c01001d42c40655907820381501c0141039034200801c429001ca40349265030b440180500043c0c880100e14200c0341034072901480c2d00c90400402c5c22491600c540303801c82000c0c80402401c99250207004d400c160190440c1c0300c1c1d14400ca000003044071400100e600060b0920404000500200d00001c1200b09261100510207070001d03048900a95039820742c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 169217248 1250 169215998 169216007
    0xd0302010f020408030a030b0f0609060c0106030206030a0f050601020a020901140409152f090f03030702041401050a050102120a08070212070c1805071205060415030b090f030a051801 80
    0x1c505141c141c510124022840c80400005010130001540342000b0341c18a82041018603003003981c1441c0d116404104402180c00c00c640070309039100c02c05001040311904c95001489540044805008803a50740c000c40866500070701450303802c07003c20700141a00b040c5580100d0a185814001c031600001b0f803003900c082c1070311641d02c41524a50010306440e07203455103a000310f01416280450b8401e0180c20000a20405d420090004c40380c80301c001c1082c94a0282c5050200402c5079001c00360b81070009121202c00360b10385004551b00794180348a010401d41c141020403141d00d0444c0c0002d81154805400001c14441d090102c5450881504060f1156034440301c08031720f00503200c400204409c0010501c18104156604124103a501e07422110200d6240b40309020115141119403400180210700ca250402001d64030803a00100c000e0404100206020040155403400d540100e844140650401c080e40304103100f0a0216544100918680440050b0003002070081d082d03900400c10504803401c03c04c0c1e004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 169218498 1250 169217248 169217261
    0x403050c0c060f040f0501020313140424030510090506040b0c040b07050c03010f0e150a0e01060e160c0b010611150a020717030c041e0906080f010b040c0e0d030201 72
    0x204860341c2c0b0702e0f9203030403030166421512590f0300191045102003410360011094070040045230020f00515464142500c0c5e4001407040565045030781e8564040f0100e40c0300040000030300b0601050031841c1c1c518501545840c1c652001004290324220310000094004590150001e40009083e11681c8030155100780c81c0c03050350701c1100fa14000080550820501040040d41280203c001300001d80d5802c0a487c15200e202000c03c4a6401c888100540c60080004158100d00349401c00107002303c5d080702c0c0c43d08490282d04131640401c0e140c1d08100300000070924411180f5000d05d408100342c0c8865440d9151400180580000d000d400072880304000b200f00440f8003980d00e14400e842c440d041402d6040c0c029805401c4c2580e03c25940007804045404110440c0d0081c520f01c1e4801d0718081c40c00e80e20300c8204d0015507262400d42c0b619540010444c1d802d000d048007030b092a402500400c000189031608503240606980d018a040c5007040d404160005480203004001340c2d1000c08214103450308a004000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 169219748 1250 169218498 169218523
    0x1050310300b01091a010c060f060503100f0501050d0807080d020c1501060215010e150d0f03030203060108091b04020a020307050106060e150f031b070506010e0a0b060702090403050c 80
    0x1006140402e220400030014101c2c0c411500803c031108483d456101100007045450b40418000c0305a82c0005009520950b41c0c000141400100b20b625000004c0c00c1004851024420300d407550b03115040300e6034a204003401860111007013084102c242c0c1e074080c02401889005803c1c800085104c0348a804103804684103a002d180a0b1000b5071210444046400c4083c081c0000621980c2c050025046e2807548040c1079849075103172840035035217a524050100412034912074101c0b4500c203456000400c00d14040c05000d01c43c2d1000b689a1034550001800054010680410340d4040500110807109035280400307224002d5401685d5980300c0c072810707861842a400018010b40ca0004005409580f0001030422110103c50381140503042c0384000303007140244407031981c030002c04002080480028460600032440101ca03018100030b016214a820250242c2c01000317601401c904210708403229108184040400f00c07191800c1091580114140301030050004040c03080000706600b5281082100552592 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 169220998 1250 169219748 169219829
    0xa0506240a05062d0414010302031e100302190501020105160e1302070803090109060506032a0415060804050c060309100b0a080109050c10140a0305040602090a0314070501050310 78
    0x310703c0d130350116269029220308210001c0c898144d100a61090084034002d04102e403050340000b50040515503ca24007508040403112031150020042e201c0b0b0314200c00700d25141104610720791828002900303540c1c004140354604034810b80008003858000d00c200503a0401035560007111010780700003400910402d44090510034003c000c20055044c1500000d0320303148513410a00c01d0b03407218402d0541d00d44603450796100b1a6002d068412407220f00c00700d270b582138082c000c10109420b10183d0107a9809031058201e0400203500308201300130710600b0425031000381c00c1902c50070715600d03003105120340b40c40c0c02c0040c0d624440d4540e60504050340d03c84034001c01400210000b08a0341e042b80c50569a54140d40941c00d015100f10100c00c01d0545c0035200d4001800d000340300440c6480d030342020460041200900486059071300f44001c03404c0342c0b61184c41202841c414541d000b10582000320980ca40145030f031007581000420010014041d00c45a0801c04450000f040f40300c3da4018202d125803d00b035040418030900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 169222248 1250 169220998 169221067
    0xc060203100f090b01140c03040b03091e06071803080405040b010c0611070b01120b0601050d151202090a15060311041206140a05042409050a0506240a0506 68
    0x1c0759113521021103000242c0ba9800c2045446200c40c4290103075181d91005604144810071214000700002c42c2c0c000c0d5560103035484400c0d6201c0404046900c02152041a40440c0070441003d8110540c001c00c400038518a10f9950315581e111101440b650040e41d0040d07032178507c0700c0641d900501360300100c154400f4082c0101020074035030304416041040c00360350045410f0000281d2007607000386010100d8100c240005140d803040010340d46580850f6800f481c450703507244000100c490246252024000a550011040e0058010800301000140c1a14003152400c000c031185456903035410310803145282400b00e0070b44c5440381704071002d01076036021040ca002c9580607401048250352041840c0d420070407180003141c42d50040f200803500122002082c00042d82120001c40d070b116200b14225103c210004a45482e56681c0c1c2ea06020354420100c4040c0d20031400d20070742100c0244d030382ccd441c0000a42840c1c1961400000514844102d00c5082c0c06130400203108080c2e0202c807a0308418910100703e00400340c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 169223498 1250 169222248 169222259
    0xb0f100c060c2708070308030c041203080703050a020909061c0602130503010c0c031704020a0803070308060a06210911090723040b180105090d0606030b06030307030c060203100f 78
    0x15210f51076901d2901442c003071402c0d0600b00645040c8419203262000500700d060550799200c0c026030000e010006502d1080c480013507034010a500e0140424460366500d903090500200280658501803ca448a02e006002ea84903a031115401c45500031b20840f212903218125042c4101c1c0c240809001600c90b6000040020004914005d10000c442041c0d0003040113100032601159860211a0010000303400449203480c0455132000d25130300140000d041c201110f03a1002c54602d980e105030000c43c00300c0c800c201001745500d8807241500c014505810441d0a00e0107841d81026424400ca025003501a5074400d58014060184421a0400700260407503180c0d09113510b01030140d904188100c00c0b00c0e400b03584000c045a034140b054400300d4141c1c04030f1a003018243d0607810051203010300c1c210b04201d0b0034428030700030780e40d0b60440c41300740c0d40a200001000d40c2141081d0103070920041141c0e02a034410000400083c0d40080f04044060700a0300050f1203440f5000d00c1c4400d0041580011040860311501044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 169224748 1250 169223498 169223507
    0x30103210315060201050906010503012d2703093006020d181205040b0913090606090b090603060c0714011b08010806060a05010e010e0414040b06030706030b0f100c060c 74
    0x424901f401c8071401d03031f80c6408240c207840008045200e07507401c00442d001c401816800c58000b001c14103101003002042180400011500901c44150303148582c00f442092640242440024001489041c40011803180340e003e00105c0c0e02d603001d6644c1003072550b124180195030b410b66000000c5414140441082c89410a0708058041c2050720456044a2581c1c500d6001c1c10445003100c96404000c0c1c20810200f0810092584d148401c2d140c0325104d003e4100014020300c5800c025100307121340050090304000502100c204020b002501951024042c01480d480f490241e501581e4407900141d441f5543d810070a01400c100e1034003070b4100f0300844907000080e0700304a01d18103071200c0b0340c12034210340c0e00c001c10401d889000340301d81400f2917803015003c6025446400391042c1054007030320100300619807810b00146000c3c111015104a03c41c8014810146010300c2110001c0c4407910742480603410010005071111104170781ea61203264000c440050b65401038000301c2105422600810200000340360140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 169225998 1250 169224748 169224751
    0x204090518160e0403050c01050108060916210c0b1204120f080109020309120f0901080f0f060405150301050a050609061002120a090506130503060a0203010321031506020105 76
    0x1156801c1c2076010001d0010354150881070040300551598075001c103a20700c030328000d0030560400c1010004034940403801d000b00383c0205940001019249005040c00e81001c2d8040300030005c5030404041005074510b0030803e004c100c00581a22500011146844114016294080d41442030301007202056042ca003e215480b4501426640100d500c2002007200e183c0d905070380d5800486c11220051205452590240d0341c440452012141180042d102898464200e01c68906903200002122984c0d27580c00080705422450303580c034403000340c01c0460715906007480040419000f13039980d9001803802c0d00d00501c3e0a411043c041c0c0200605e040c91404007025000c1154918014000c0c1c0e0081182401c04d00540c20668280381e02614540141034640b031440ea01190364501049116140413615540d07240040c1441d014642c210301d030340c61402c800d2606001c0000c02d001c08591040c801003001c01c00705911040f007603140c0d958a60050158280a400401f00d1409030f081100c003400000c40c080c0e40550009 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 169227248 1250 169225998 169226011
    0x3051b1e030310090b130e030d09151103010e0a0b06161406011502100504050a0503160515060f060a2f0613050a170c0607031d0c1e01050c0102040905 66
    0xc442c4562a054840291801340302450f4110102200001c81c61005502210011f03141205503894900010385070740507101c4407801543c07a0b5083d405a14030180b41840b40e0180c0a079041d02c41411585003401c101c108100c0207114000f103545407221064150340380011903140005400b501d16a840c841d0900d2119000000240710b41441050000304001990300c0580c0042c85665006240c80303d212514900030b84030142049031503101e010400350000b2030602c00727411a4411802d4501510a0320b043c824a0602c2c0c0340000740d00e61041409000507a2141809a00265415a206039440c20110001c071480082080b00959032200300004150b00301c58555480350203011074040700e00a031211404244c102c01590030050940e841454440c00050044200300401560a103106040c000d140b007406040007400c9a590300000c0d5203203d40c0b2924441402c4140c241c1e200c040007440d2000c1500c000c240e0510510300d002441d00d4800d0329030801d0340c2c454400c032038050002c04001d5403a030b5034880c0d02c40060710060318072 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 169228498 1250 169227248 169227271
    0x50a080a0e04182406080d0201053102100e0405070207080f01052208040b0708190e0d14030f07050601050f01050f04060c0609060509150601050703051b1e0303 70
    0x1c0120b81d0000044254104d801c101c0407209142d40c400f00302c84a203404a520181039440d02d00004450109214444400025400204051501503400b12001c1c6180200c00320050090740c1220081c0c0603141042082981a10303100c106032000b9070300740c9403001d00358070007075015090004004600ba80410b501007200c020101329003040490060f43c1d800d89508542e401f00c0c00f11903500b02049203a0700001500c0590151500c1c074505903d640b0420045e611424081d03514501c0003039030707021540d010001481c41110301e1030900f01103260600014030488180030050003011039691701d181610742c10b0007160040c07120740c820320741d4568140c54640c2e101c5409100301403080800240c100c0c1154020300840d210b10304904038003840c1a007807072001d8454410054080d9215552944580e000079036030320072640a00407203801040550311312440348c0d008030001003000c0c0c1000000d00590000a8008041d10741c10b2400410808907980d0a2403079600d42608460407028004109000500801006c4001c500414601a2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 169229748 1250 169228498 169228511
    0x90405180f03120a1107050703030e09060109030503070b150a080f010b0102011803030504081c0504060501140d0201111924150501050315041a030606120d0507050a080a0e04 76
    0xe260345030300806120b056495a4840000e01d84c0c1890307401640e0040d00320300d54504200341d68641d14542a003c0c3c0003100400ea020010302c54501d0300d0350310b07107500000c24600382c1c41a9003141d4440c0d480e17004484006212054020116448800d1a5020305c540b140141207800510f0340ca01c6220340d118140000c1100355440d249080c00c0a51043c060040740e01b240d020300c1075196000782d4084004000003041960130361400c4c408030321004071038031078001e11580a00c400f04882c18035042101c01c8403010ba2100141c8a100510724205864003602c9001c4240c0909015410180185086090004140100103101409400e900c10042c9080d44928484911400e09558100d140e84081c1250f109009054511760b0960041040b584188019644010b040501550800b08103010400350350300c2048003001c9904003404401320742000c00035603038400c008a4000c002d05040c4542340d5111071042c18140100f1100146100034403000300801c44840d0360101c507096030f03480d42c0d0b08003c000c01c19616429119505212 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 169230998 1250 169229748 169229773
    0xf0d090c0308310f0e0a02120a02071101032702010509091303020601080313031502091f030c0c120c0f1a040212010519050712020c2d100b010509040518 67
    0x1e0481003a940b110160b041403e01700f20f000441d4040c010002d0080d69020407040d4003441031130b54168011300b020f44000d601c441661401740075805000aa090405140180e404055040420141c10401000b182e4504020f11800100c034a0301c508031039150841b541e1303010312407401040c3c18a004d241d406503080d2051640c881c0070203034403440781c1c40c90054485c030075000a1010690744016854203140101e001440c204042020500e80c03070120300781e411041080d0307990340c480c5505400f901e43d10410720b241c082c240300e81d0341e500d004c5014000701401c810000d80c40b464004100d200400303008001d8020840d0741170206d400c40090742c0000f04a500303d018400c0552540c04079401401680c0c0507130000c000450810340708001d008001c04000b0840700c00c2010254800e002240607200a1410544100203072000c6450450300707039614852004049031034041442803036201c403004594032445001000c808906400c8510040729240503005070325034031600e4801800401118010440c580403400c0c2c0a0b1508200c8c5403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 169232248 1250 169230998 169231087
    0xf11160f0e0c07110a03050a0507060f02070f030f0f0212031914070f032006010f0602150a0228020a030e040204080a0305070204060e010f0303140f0d090c0308 70
    0x1c0d42c1d18403142e80e080c000f2000080c0e59013400480c030000a4004050566039441c0c05180452444065409400012041c021994800c0d07070442c894185000500641d8a0402d44a019501e50b200c080c069003a030760380c95020001c4990007411400d0f001400c2e900c01000d0214000d489a004506d0b0a44107078585a5280000e80a80414460342a06e000c1c0503051001d0780d16900e0b11201c492408a080042c6410a00c980041403a1015198074600c401803509606240701001c00074010b40140d01503500c2025400c2134030a215101f154041d8000348096100c1500240b43c019090725403000481c822240384031380c070b40d9540c00642003281c2030203030780c40c001d03840f0181060008078490f50140c0c101c07540000d100c0402090080e4003c1c0b00c00c5201410000c0c0072580c41030041c031044d0080e084903058070003a00082041c5503100c2c030074a000002d09103020703246c203020b00302c40c610300d03c100d90b0b00014003502c501c210014084901c4003032000f1a008074401d541c40486596586a05a80e90007600e0f07040813484440d04000c070803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 169233498 1250 169232248 169232251
    0x3010303020f19021813080f070b010b13031e06060303030c0e0405040c05060708090d0c0602161401120f0c0504061d0d06111b0a0c090c020a030f11160f0e 68
    0xd00410850260301c60821703140d440040c0150a9480704c400c0c400e000070300300c50040000f207140c581200e8035009203281105104d103060f40040103400b820310481c1150303180a43c5200407241d0090621828044080a0240410440c840607228a00d005000410b26806030000d148110050360b5001509400b40100400c6403000c1d540034040092810b424402c82c10700c0307130050882e0707400b070303e22182011803080004d01b01100c0e402044406400d0540b0070442c09070100f11013505220341c004880d031704600300308102080c000408041030401c582010050b40e00462548607000701041c0c40f2061001c5000c9150161284e4800e21a0800040c00071800007901800130700c450502c160010520741310310b402c40d140c40001c0c01e01c400085408160070004001e4410064141d1000742d440c4c1d901403c1d141d00c03281007030710390b50340546e02c090011410a000101d010b50b0100b14a4a416410304022840e1914480200c9844022100040c0140b05050003500c02c101c03c1c141e440d0464040c0950400225190151481070100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 169234748 1250 169233498 169233503
    0x150a02190c050d030b060d0501120606120503031314030d0b011d03060f0601030216060603060c05090d030c03300b0d0203070b031302100e04150501050912010e0303010303020f19 78
    0x80700b6503c90244203402c00c411180f4006c2005042c03911049800c022903000f03034032462600c81642c0800c0d08202d218001d0800030403080345080700010064680380c5d02d9100007007440c62580030242e0719508020000440750207602c1d150040b00c0d180d0300b84280410041c00e0510a8a02040ea55251307076113100d1360440076402c00007014018280c136071030701890801d0128001d400941455028400150301070104e200f1900b0180c05640081142461810b254088030f00017510031042040821294030030303403110204844096414030301481842c50390b04007111100c07043c0036000c102991030200210302403184090480e4440340c001d020024050324500f00a000b080c05030009406400080d8104203104008010750752065a000740d0102c0786101d07500140300003001b51a40404118103070000d040a081520404000862950a402c096414400007a0003406501c00c920311900f0b43c22418020603100f90450f088507529102240d45a507101d14010303440351500d405110084c810201612901101c000ca121070054 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 169235998 1250 169234748 169234753
    0xb18060109031403091008041a010b0315010c02040204081e011a090a090803040b041b0803160305040e0115140405090c0a03090f08090a05040209100e03150a02190c05 73
    0x10310755a5070099020f01404001c5080c00140078540540d2035018804451440d10350b5419081e10701460041c00c810141810030310440310f014014400c100c0c00c0b0302100d03009544980c1d014000312110700101e98001c40004000e40040c00440e0020b030444002540e00034140b032441801002a0824100314201e46c038401b260100a40300c12044140c40c242441c034035801c100d42c010b01017089400354861892035032040d1000c07204c0350038400c1040309101d12800000010611980a400e010b858280300f036a42c2e01032580c110424100241030801014003501c119001062a001c0c11181076075508002c40c40c1c0103904175110003180b450840603204034001e80858040d1540200140d00d1a21201025106074002c011544c052541e244909000f0900d000c0c485075500784103049456a0354014414040001110707071045004030300500c080c96182d0f4031100100c40b202424504400c0c0440c4c14000249001024042c4898403802213040c4400c050858001b07110002c0c00e014811842d48141508540c0018502c401400c20b4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 169237248 1250 169235998 169236017
    0x51903110315010303090509071e08070c0506010801060335030601050c0102160204060504090305091203072f011b0b040c0f060c020406090c0c0b06150d0b180601 71
    0x60410000846203500280803500c1461111a40c00041c0c0d00c01e80003500802c440f6407041055181803103083e0303444035180c5000c001c114000d400c4186030758584100301052119100000f25000d00c0b030b10542c80d159800404440789940d4071400341e4000c04050109860320700b890103032031013660000f4200c85546034845d600ba00d1964180b03c05a03020340c0010b050300381000401c00c50f01401d444240054108100407000103d0100f1291041004031451039002a01540c18917030820017003500a41690300441060b80c8144e058181c444980c1d00354814010000c0c0060054039800b0b8200300103101041c5104400c55181b004003c0c0e400040d240084030f0b4029042ca002454600c4000400d0112015041445102d00d0307101d1a40300e101d00790b81d140007030f00240c0018a08060344801c1d0310749401010024541c02d20b0401c0749000d10b03030004241034032801000d4410722218021503e40d4841022103509000d0b0899a180c81d13000807100c100c050038111003d07520462003800020ba5444003071390224003070310058480f200d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 169238498 1250 169237248 169237253
    0x906030307140312040b070e092208040f08030301030309120b06040b01022a1512180c040f020d1a01050d1a100801081207020102070902030a0f150609051903 69
    0x494480c08801c5194002401903540b404c03001c0702c2482c02203219440c060300600d8100002407101c0343c10160309203d6083d035024402d01d0b144240341c11084103800a0010721900d02400c0c001075500c00c0b540320b610005012080041d02c02000310145040e00e20a54801c04025903600000003004004007010740441040004907010340340c81d0f4404200c5c4041030044e940ea01d544030100c409c0c0420b04500c0420840c0031140003080c146403840e8000707151821003210314200841c180749a40f0300e040007007005000c0660b801c1062941c6004000d402011423006200340000a05d20542c0300180d00300b404108191810014482441400c4070042c4400c010103a4900c2d042c04881e81605001c0d100c109c031480c00080e080060340c001926007070031000c40f0310000d0f158a085940b41044240c0780c400c3c0a0340050304c020040c400c0c80010303139010030104112070f03247c0000343e101e4442e04110300082059040516115117041051703601905202c1002080354810340711803d00d190350724180408440c50b80304241140070014400e100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 169239748 1250 169238498 169238513
    0xb07090617010e1e010e01050f0103150e1b0f040f0902030603060703150807031202060112170304170c0c10170a020a0507051510050a0302061b100204120605060906030307 75
    0x14080405040c131000c0100f81d840740155002d0a0b049205040d82410044c0444d041441c500001004280380800070f030500a600030018420b240075a00143d0401808140c0c2880d05034241c0c010910604a03e039aa2000d000301d044a030303070051007100491003114000041102c0144241d9204941c00703409040c4956500704201c000b040409060480000f00150100300d410040001e2005144621580700000f5500440680b030502c0582c032102c82c0700c0d01c00c880d0b400000c4905550314996030f46403410301d80b00e40395850100c80401d24000c400464110119551034105000603010301c21600c2604c4041d035100f81008115588042d40c070848810602080104d0725420556000304091041440c1c804e003041410381d221810b1071030b41c400195407081c020003401840028181068001c110459101c00a81c0c595804a44a401030280380c8200030340c0e060349864040014084030b030a0003900d102c210b590395240c0007a0030300d170080c0307800c01e40340c0c286800d001900504101130501e00513840140107504004440c0d80b0b501 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 169240998 1250 169239748 169239751
    0x1605090103110c10200412030503040305041a090103050106110a0f050102160305070501050a1b080601030912051b010501121202151503101401060c0804050901030b07090617010e 78
    0x107018070000c20a035551070b0030910260313100046000020031070300c41103200c030700e20201d5543c48450300c0001044100000b0781003181c20a140ea80c10f050098403030307469003010348103801a40c3c489a9040a0001c090401105041c010700740d24030262001c1002e640c0300c1908540c0c0c102c1e02034003008280c3c05801c0f848041661252030700c0f80305229100140c07806403030481040c0002c038040021000b01f000480c0e80b0742000340070301036035034401e1400904000760f410040803114000002c3e0310b490700b40030001d004920301c0c1c1d10a4016010464114151404c4800da14100400c3c580c400c0100c00c0959146c1d81881100b1801030141604807103181c9008080540a0f4884000460520003043c0039440f40e05084e081c4150180102481051410482d1010241500034503084c03103880c114020312145024840202e8400c440c04881c150307451458444c2c0907540e07901e005291442a0303001075500411075000002080302c0c00802c40c1c450031542d5a0800b1a580c0c03010155100c0001c11a80710030341c0441c02c01401004107400da5503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 169242248 1250 169240998 169241021
    0x3010e0a021c0c03050f0c0328030c0203031b1b0307050603070f050d052403030304031d0109030602030f0402010e030601080601180f0207050d08010605120f0711070806040b1605090103 81
    0x3c26055590399211441c0505945103e000c5401030001c402c1c80e03107400c1c0701100c5095441f23032001289201e03801064613184600400202884031203400d007030540d282001602c19040c0d140076102406d2030903981d01665a003038070b60300c2524040746001c43c074814100481c1c4141100d501400090540d1100102a518100301b02071312010403200307100d600d014040ca0700981780503500503a038062051310b54060102c01254680c0c0b100f806036004005110002e940410494501c184c003030358400b4140070003801260b1008140d4000303400c5900220034000d4901e03080300d2844c02540b00740c84608171410b8840c00e00d521103e09206101c001c0d00034a004000c4030300c0183c5158010070030410001a03800e44500300c1d6040f60000700c0e05071140d13800300107402c0000d5001064a409044c281c04c0c000d090841c8441e4415080e00010816910f0740403400100d4200d40c0925543d0708020441003d69101c80d845848403580c0350b408803000e54510380d800000c074402110b0004040c040c0c40e91965032510b0400188010740c0501035100e02e8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 169243498 1250 169242248 169242263
    0x1050f0d0209070c020103052203110102130b03090708060403051c0603080408030c0106050609031f0b0a241803030f170a020a081509061909020403060b03010e0a021c 73
    0x9400142c0d600d03842da0780315004503150700409243d5400014120b64000345200300031032207111083d410700e5012a880c0405545880c10070780d8110700c82d00c101d02a02800400080d19420141d020480e00c032240c0c09588180d0b80c00c0111758400c2d0b542c00085507200e8041c4c4014011400c1003145142c1c83c410745042040f5001c99501c0843d405560ba03954000a40c8164401200c0350000304118026240c2070050800902045400c50b00f4114040c0020751109c0511400284030700d80030005001301c502a802101810380d008100110b050358a05070356000c9503010307800190903501810b20640080c000c8840b45044007041c460710090307174116642030301c00c50900401c10b4184040c031184441e0032031303005129500c951000e08026807101e1940703002400c003880140101140005104c0038180a0300c4400343c0542c01503040356400c0c145100b04201c40d4050710b843c1c116104c00c0f400010040148610394202441d84070080c0d00803c441c503115105580c440040c0100254000c1e2900c0303100c1040409446107aa119000d150f4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 169244604 1106 169243498 169243519
    0x2270601020c0f0d0302150a020703140a0905090402180718050a031203020313060608060601170f06010e12030c0a031103040f2303010c09031b080601050f 68
    0x83e080e006084c034031502c00501d8800c018900700e08400300c1b115121818950916000381d4003180c0c4c10340103c0c9a0100e201c05140348101220362400c200c0daa50b4034010704240130002c420802074416a40300c07444030500031100c02d04241e0140140724030f88540c0715007100f01c600121000c243d58840c2e84580050103081001c1071010700c0f0407556441c103260041c0c2d60ba0740c40e14003c00301c866048003e0b003507a1900f4030111704420005162400341409890718003d80001c1e42a03ca004401100c40c4440780300c901000c541103500507071f1107006c0302d64000c0800040b00e441d00102032a64111600c80002903000ba414001070580002c0e107034048920f0500514585410011001c842c1c542e240304a03402e0301100c1c10f00480a01d50420406c8030b018001b402841001ca256070000c203d40300c140000d0b0380480c240000c10207959242085c403000c990400340502616031a01003044640c0d0140040c5941200d1441c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 169064748 169244604 := by
  have h0 := BRFrame.cov_init 169064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 169064748 ≤ n) (h2 : n < 169244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
