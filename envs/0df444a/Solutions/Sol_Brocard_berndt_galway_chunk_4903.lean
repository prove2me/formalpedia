-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4903
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:06:41.482117+00:00
-- url     : https://prove2.me/submissions/9ced887e-7ea9-4570-b20a-c99cbe530152

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 881654676 ≤ n < 881834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 881655926 1250 881654676 881654681
    0x20601030c0806270705060d090209060301051302010c060e19060c090f0b21040b0402090c18040b011806050a180b0306010c020a0e01030f020f040e070b0309120f090f0a18 75
    0x18000d03035480340945c04101382c0c132820b000d41002d913055600803070501041d104225a5180081015000b60714000030422940d68280c000c4680940a08040ba0704d0071480c1401c0c0040c00d1480c403170002e548148581c5000c816402c0d801c3d80002c1d805104c0c02c0100b080740307e400b180d0341d201c940708200031402400000e10003014284000c001d008001000d801d80c10041035010f0b070b80c2c43d6040b682504e45606083c100419130826104a070b61150100b00c400d8544121010007810a00280d086a40115650410740141c5d0b4000e01c00010040d01d420035007020159102c000415583c851a1003d0002ea09031500000a51000c60741c102551540c6490358110340d0742400440362042451016a403011205400003081a25441124003841c040c2411a0810398140103100001140b0041c3c140214544013080a81140c00b00c0d40798185c0300c0820300c01e82d8a4417201d148174541a00c030681103030980c00000d170100f102240d0304028002e5100c1603509846c4803003c401044603000707103071103010900030002600c1a0489081c2d07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 881657176 1250 881655926 881655991
    0x613030e030a051c050d05010b07050c060a05030a0b01120e10061508010b09041d0a0302280f02220605032401122103150f0501140f0702030d020601030c0806 69
    0x180362142c01d003186e050844d01521400c3e4010100100c0025400d01440028055401041d2054598928004080342c004203a44801011000480e070765110410359a0f115844a440b01062107a0034000d690400000340d813158401c814450503207182110014a107000074000e2034020505880303c000740d80c60544d03901007550024003c01c0d03105079105451125a4042070700072024041d01d600500d03560241c0e01c1c0c042d00e0b000d461540c1080040e410b002032560050820000e10455501680c00300000000380f0105803082440c540381001906111340d1240072442d1036008000302c0310114105c03a250300c2c0701d0780340425070064aa01c101521540000500403e203c4504100301540f09984803250960459240002d00101d101d03c035001a845152402039070408000110140c03030316589400c815440e103c006882a00010800c410103403001c0750034000d10350030030156402c1d41c1d005001d41da041c07000d0b060000d494103004d02048038403551000001c1003994000610910403442c003599140001c0807201440c95201c003c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 881658426 1250 881657176 881657233
    0x1e0605010527060f040f081207060c03060f142e0804031101021c0b1207060c261905090117430333080613030e030a05 52
    0x4410807080d031901c400c001002c1002ea0045856107850802407001103d02082e8401d00d0b4230340c03101810700450f003281d000f16112103501c1240040d254111074001d0303002c1c1c0403992044040110302d100000e2908144154011190703001ca4603030790004413400116140341e140004031610381810f403055104182c0180d2400d030b0858046d051030138003c104480813a0980e4005000003948a881041009410425000d0b0401c0d129044658042403001e1444d1141da45a544c4251020051030714443c00c18042c421a0581020900918030800311101003480c1c1300aa10280c601040c1d54404004003005920582c262122050141c6d20300d40c224010a8000d00c0b018005070000f00c000106c401620524009070350407801803080207405c1c0c168000d691031901e4041071518881014075007420040c903202400d41900d42002008040044d80028107048000126000c40d049140240709010612403807100841250300414466521850440070810525881d0841000000e201c0e9000c508000803000c031006403444800070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 881659676 1250 881658426 881658487
    0x12020307050d0306060801050105191d030313060207050d21030b0612040b06030a0b0613140a05010e010b04060c0f0201050c16030210030216060e0a060c031e06050105 73
    0x450745074142800124141c0d20046a5101001c006040d00800c20341c3c0109000d0074042d040a40d0481d40e150006507614400d0100062000040c4000f202e2800e1340d6041c41000d81101d4840780592a00c1c000e001d200d014900c054481c9a200040741d18184100000056008508110484880600081c40c17141d07185940c081c5a02c07014074180c540c8650000e0544107465001070f96041c00c19080c02e00c0d40a0000c0c00103400f07508010710203000700304069041504000309032407484a0503a90031306100202116a45220001c41c1c650a100540680e40c1100381aa44075104008044c4daa442a940043c841d0f8411140850034210800c808107501c514004d2101c4d006042080c54a80c0b07032a01c035400c0903030712800c131130901d0000f0b48240254180300340d03804402d0f101410308500d0404510104030300440ca506000784007a44400c0b22202c904014040c103601940d000100348820b40c07103d0409005085401c540ca0859400203405000410650003210110381042e120503160648a50000c074121f124194805400309 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 881660926 1250 881659676 881659687
    0x4030f0602090a0e0c0703030606020c03250e040507090c03091703060d05010f020a111605120f060f1608070509150705060a020a0908070f0603021b1b012a120203 71
    0x4d465160b0749206034005280c46a494150b441c001e82114540e4000208560090204044135140000d502c1075140d50311500081c0134a005101003c0c0e40b4841d0800309906800406010401500040c10300c16584014800d015078001d02d1400c03000c45814800c060b15001c100903091a6441031207000b1070f04810050100c0603c100d01c0d840e410700356400d01010b894800c0c2c4c000f80080406900510006800d954000505140c85101c42100344003e00381c00340e544103000c0c261143c602c3d10403c2150001c01a0302a0955040d403900481e0401c403404222000401025101a0290114882d59009100e40c1e4184c0b03902e07003804180020f22400d44000f81c40360300568410819140401c504015143c403906108201503031721000c689004080c521a6405512268401c56041c010044d80c1030110054585e24600140c40781c560425214111000c0c4e41201c00f140654003940c0030f0b0410702544c004178508281c0301e8403441100034408503402c0c850315060314043c0008114613000145009031421105d412803040702e0900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 881662176 1250 881660926 881660939
    0x19031e0c06110c15010503010f0e030315360109140c0a030e06040813151b0c1710060f0501140a0c08030f101d0f0702071802071704030f0602090a 64
    0x1c2902000300713500b000041000f8502401582e000c44440c00042c4034128154400aa413404041e000c0e501c51060304684d58141c0e282c10442600c46103501d080c080084940b031410400c0306c200003800c00810b01c0b9480002c200a1040d0180e6117034181d02c00305801ba1a5108140310b00940c0114070040304060701d5002c0b00610001c10428180100d01900d001544e030300c550154021a0100d0703a00c01650b6803580d952040c1c90582142d00d000038240c0a840035015801c40d80390003900d03c42c03160841d24032205d5448034202100070004192804815640e030410800e82c81c0c80100e5402c010078070401d8000741014500080842e0440301034041c900c002d003888a11080300d5a95640280c000b158003081c040346c2c03d0200803440b40c0b5010000018944100380061805101c010014000d0004266416091005012402092080103803030020010002c54900c851820b110f00006075002d0b4806071110310301c154428030444028421031b030840741c0c0090300344032014260340c844000c0d4000441c1c40303078010110080003404c0f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 881663426 1250 881662176 881662183
    0x1e0711010c032c03100b0907141b100b1c0f0606091d0c1c020d11060f091e010207060f1404090b0310090305091207050319031e0c06110c 60
    0x8803840d0f00c8446001a000c414107180c04840319901c140d0740d0600508912580740d11f02403d410014034a011041000d031411079070090300c42c010282042100f0558a124400700104103040320030202d52060141e41681d07410003030000044120342d120000030124000004441c00e500c00d402905c075010100c1c240d6510405a02141d1040101040085150b40d008c4035148090004d4028598100d420031f814000c20311440030303060140070000f030041c2c81000b60700b0144080d0240b240d40d54200204402d82c4e584202051001ca600909151805aa0414a40c07207905400c01310341c150004041c6d00410b011850010112010078031a010070080c020a034902828032a0303201d0081010b8035a450f0301048100302441814500040310b0380b0360f14028075100001e000a60301c001252103890085400c900c50603206d1400d28140805da9100c6a454402d8944118041507124011100580240c848241a404001220200b50100d020100c00112100c0030880002c1e03055001842a115210b03103103003080e240124042c074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 881664676 1250 881663426 881663477
    0x2060703050402030325060e2514040b060706050405010f1805030d1d12070c0608070e100207090204030b060a0605030f191b020f0708030403030c02151e1e0711010c03 73
    0x1043c9c001e25000d00c501000013003103030031000030380100d54a25450284080c0f0b0200401e00090f1080d521006a0281039a42c44203651140b904018200b2103404e040c50000c2c0281500d0b01d06998031400c0295004245420b80040114160000007139480c10040d81c100000070101e00401986803003c040740c2800d2110704000d0804071a0001260302d03610083e41c1000805220141c0c800410400510100007003950300041c54208407005071180ea000310700c050350507410600d00f0f03041001028400b05000062007800348000380501401e9421004040d200e140c211643d10080b60035414911030100450003414000030b0301000030a480c0000505000d280c503640d0040c3c50460089401030340980c51540c602c08084c00400010f04150000f0f62600745143d0380075290b000000e001a02c2a5002c08c180e4480c042807108985049400c40c0d000c80080c442403044d8040c0381c00004004098003c1010046030f110f800100f12201c69810003000c81c0344205540c01102c406010301c00441c01c01004600c840c0ca01d00b106294140e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 881665926 1250 881664676 881664701
    0xd050f070f1a010303140a0e0f13180611070c0b090a03021f0305060a060f050c1903050703021009020a09020903100218091302220b1503070206070305040203032506 72
    0x102d50b54910308008020b005210f06182805a04101e044c1d0340c02d8101c10000038843c015124451200d1081c0300060f41000941e9415041c0c0d402e0071940705401244500e001003280c8920030812480241010382d600078010200c0050214400000601c91441554098506010020004603060780c40b075000c41c00d03404d0404081586807800c0309107421490f40500406512010555403420f815141810007480c180e00c0032404418820b00081d10101103509124aa02e07a81c1052841040e050b11481c006203160f0240750150014018881840c01d20400d40c02501d607040d0b00182440a06418203001c40029840a01c07500d07070501c04d60004885145482c000b50451000030700c03042019921010034803910b01070040402121280f82d01c03c1e003005030745103c00203402c1984000103801d0a0070310f41f4030100811000c10706541c030500005408000150401c002d41c41072a0396070035106030b522110002e0b000d40e20241d074000e6240e0001d10011700c60f004c0c0d07540206400740c0340300251850402c0c1521000100d81c0d6002c041d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 881667176 1250 881665926 881665973
    0xf081602040e0f121c0c0f0f0306060819180b150904050d350403030b0d050c0603090c090910050105030a05070603050415050a0b120d050f070f 63
    0x3035250920502ca101819240508000340028400b0380e01d030100c18a615920b050040b03003040000c0103c1318120a09003442408001d07500b07140c60301030718030720103a8894000110042c0580380924460b02840b0111061602c0d50046610b81446c84107816200d4074000c0c2015950f4045104000d4100107640742c43c1340200091072aa0410000c48001f0381c20b1005540d0140040e40c003800300141d000118400300042500c0d080424150b013160810040340c1300b1038603104040f0f5038680c100805800300001030181d0700c039807002c00c0075419440920540b80225100031b806500720308109503450401c0c81c011070f8002c2016040e23a00c00480040003440c4804240e400321141c1d409000c0c030b40002e2105114580c00340c401240108500c00d035aa07101642e50a0030700844e010540c880000c00c2c02c000a03580300304003091508000740700c64a41070515800a05406500511540c002b41c404103181502140370105010315a88541c90708c0a0342c0b805404a9102c81800c507000d090703040d0340501103510181c0a01407119031036040d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 881668426 1250 881667176 881667217
    0x3050f0c061512010b030c06090d020915090105090705072006070c1e0f0b160b0c0a03060501050a05070b060d0609152009040f2a080109060b03130f08 66
    0xa0046030f4907184112100d681c0751402072800c9a4000038400250380089070a01da0b2210208045803990213041c1000350060441004d211a0304400172449281100c1a41d965015270fa0752010413803117242c03d1381c1500220784c0420101001c1219505c1403000020841201c0c425902c805010605541c0102010350f8000404041400740e003007117940c009143c46001102c80c00690030328600c1e002c1c1850611580100710b000041410945400d81c898002c859009000c080447c03a090f19480e465503c11010070700000c0c9008004152503015405590708207126035a064207142940e41c50340c90120340a040117900240048842c0300081c01130182444192040000940180c424004413003540c4d980c428174680c9182010219600140b03c1040c1d07820844200d0380841c075440c01400321402031640000c00307040e2081070032190180c1ca480e4120303c840800d19548410340c50ba61503c0e008216607680c00349003171000c0c003007010400c1d1207504c061007142707140243c0419402c0034243d9240c280795071003840d200d0341c200e0000d0103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 881669676 1250 881668426 881668429
    0x306020901020a052e021206061b0706080604051e06010e0f0d032102090315061305040b0709050f0d170f030901060f08010c0206010605030a110c1c180303050f0c0615 73
    0xc04502840e090f242c1507003800c43c400318a80742c1d6030004220a00030b15012a9440c2b00002c0000000c80c0030402da07007503030712283d225840201100c3e001c070b0f8203901403402c00300440d03050000c8036401003502e460303000b90a00c4ca8840000444000b030b800259191f00500102c20407519a440341005074040e4441e481384000424410a1440c0c03601c4d440c070460348003620501910340a520003145c1540540b00e42003449240e541d60000160108808e420349440203071034042003004110510308554000c000b03e40381c410708a5540c004220b04160010666030b04101100c0305400001c16540c0f508101a601d003e03490b0500f03030503035074080d015002202c0b030390543c1c1c5d1030300703010844e4940c000600d0b0090300c607440091120514000c006036450906102d070a01300000040041c42e040b0031903224108030200c0e6407040d40e441d40c084c103002da40c491602440c0d48648010901041c44240582d030341484014a2640c840c11151450304c0a035000c0d081401c2c00303405400100a101100240bd01100303200f181da0203502d60000c0100c20 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 881670926 1250 881669676 881669743
    0x20c060a050609070530072c0d060b01030e0a062909042a060201050a11090306040609080d090b09070506030106050412020f0303131a040f0306020901020a05 69
    0x2d04850055050905200d1501e42c408100c80d29000900000d044059950005c00c3e0050b0a8420003081d002c241d50a02400030340c00825512918110b0395140d1385c1d1b444840d14000c00c11621340b003065110007220405400180d407504061052001418006100034800c103159080c0070486500300c0b200b95680c0b07080300640c0070494074104941e4030399144e010720720b50107004180319820240000e800048a049450310902543d070903c0035042041d506503078041d42d0342001078064001540e01c00c00d207604000100140c40b1191041e02c001390f038000c008201e951225200d120041002a000b40c0d44040f08200b8007140c40d0f0b503406070f4914244280100181c81c80d2100c60a420078801c2d4101500c2610100f00410010307500000781d4040d20103400644040c0160361000070041d80ca0b102c42607400d80004103217994024450345103a07003190405400301d031491a107403400d082c591107a405182c5209031038010078804201198090145001d060046404125541d210545040c191201d05040c0f81c07480c0706800001708c3d00d1b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 881672176 1250 881670926 881670931
    0x40308190524030c0604260a11120c042c2a0f090108031c020702010203190c05060c0d1d2112010e010302330c030d020c060a05 56
    0x8034100000e04091014461201400c145880100c1001c180b000e00d40d40d043c8100110708070000c1c04981d58596071180e0040345002c8480044441000311011411081d012034941c50711b0368442034020b81500d01c0e13420007000d088003590302d503000c2c8200d282c6001c02d0b4603184600400080300341100340307030800c0d0980161480300011010300066000700d1088000c040340203150140741d40009074000390007055403020940030031600b01d00c80d51252a0303000000b072200021004004028a42e004040440010000c2100341d11540c41c000340164400c1140d4440c6001e0070580b0401441d0301d1420180b004c4d4551a40d41c5407035016525041d0010000880e001c003103885104244104800303056440400ca4010070b102d8480c003d0300d0040114007421401c1108100004040f141c44100081c26100f10b56101c0c5132041202d1403d020413030260a80c0006840e600402c1000186090b2841441283c00b07200c510890917140c000015600b841e101c00e0281d000e8860b4980054880c00204200500840c80d21480310402e46002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 881673426 1250 881672176 881672221
    0x718050601020c131d010915060503070303080417040b1b01060512060a0902061201080714011d010e1507030206060a0f0b040b09032406130606020d0c02040207050105040308 76
    0x2c0e0f841596191502ca83c0719484149818002552034006540042c000c80c0021101406502e0640328000300300c2c0713108081c0044c0441080410445407100705040c0d13560158000500420840703400079001074400d00c0110103000789828624282541d50f205003d1b00d4200c0b00602540c101c5401c0340e40031521007403291a00412085449054107030240c09565110007001d8501d82c0382549030040d490a6450301802c4607001034501101d00102d40e500c03504151110f02070b004481700b031038041168101c90740c400c03248010840790b100344403021085000010758182031003101d21500300323016030321030100413980e00d0180c00c56038060380190440e441c03c1e00410240040315006541400500801131140038030060a40707081d228078400444d621405034000903d07220300c2e80481e510448c81005040c400c80c4c2039601f1240a148140c880080504200c01d140064802d90b0085000585c403883c900d140451240300e002403d1070015000603d0919540c64031802d540c4101d82c00c5d408540200c0c1801000c039614040d440440c48e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 881674676 1250 881673426 881673433
    0x304230318041a19090b03011b030504020310020a110111071110090e180d020c150703110d0e0a0e040203030f03041505010303080a06291b071805060102 67
    0x1950107050900c1804406601941e0346510f400603a00030288400401c04005001860201880c00b1003940800c180c00380c140030900305420742c0d50f00e0605000e0200b0607424489019015008040b00310010800180240e034980305010074034100080307500c01849980d440b0f81c0c8100918031480c00f89425101407080c2082c08080400c801804664614803028841d2400c5428854503100002c0c02c9a5450715600642a080e0400c024800409201401110700d40710700d1094802c0d50f40c410f10180e8403141601a41d50f0090f0900d1050082e6140c40c50052900f54400d041030040c81c211250203a01e042504991200425180c270b0313142030107142100c091030042100c0c0746403a1940c075059006c20344074058203200d0714094001201280410403c0410781e050f100c48101c04001541e56400d006000301c00c1940c0032444146012800302d00321031911203441c07403c04038900300d139040c00c50504000b80719808191032854410100201e41e11139541405020020440c501c800e0f10a901c40e20100000c464018101906551 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 881675926 1250 881674676 881674687
    0x10021504030f180f2106060612060e150112020705100c09080a080f280c0b0a0e06060d0305070b01170706090e070324121406010b0f030a06030803042303 67
    0x840942c860085d6a010401d0100000d1058403000070400542d2000b0015800c000d40030581035800601444030701c813400c1040c080e13159503103601100040240c800701d00f040307150203a5407100d50280007042000f4499860062800e5000c0d283d150501003146452410903440340d800c1c015840e4481b00ca14068040a03000d403080724801d80e02c000b010710440c5600d120051000c640310b0a1308503824881403001d2006405115003281d02074000b020190b44034070454040074001c0200f804007207284201048480d040307004002a40f82c400411103c1c81100004400300503081200c40d0004503900b031064000e1045200d444400440c61241c40e081050640082d005c002140c80100445000002c10682000203420000740403c0d001807544120b03100c404036400c11100000001410386e4103a4407041186008214449241d5001e55000b03450b80028441c88000401c00d001c0c8070428188000150b8000a4850001a0f00e6940e9030316482250411101540c0360f1805981c0b80b0b43c10700b04e0f80161502c0c1c2c1c4401001c0c61418 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 881677176 1250 881675926 881675939
    0x120c13061719060c170c090109080d020a02010c1b0e010602250b032e1809030801030219080114040203010b01020c0114130909110310020a090510021504030f18 70
    0x1011142e014090548980704482e2032800b40f4050b82d8040740038108550f02d071900c50000b100903440f031500640000d0b2580000581d0101c0450b0142c0740c004141d001d4108640c0940045421241d06102a10024034140210840000c2c14600d00014150300d10124500d615007a00642020442c00302d4401080401ccd014031207950881400405480212519907101d440783c3c0e4a010182c4112401030062a0100070f0011541c11044400c1c41141c0110540f00800c07000480300c03905468400e0f40c000c01007882900180300600e807045100c1d96000c5507004a19120380d40d8240c880c25948002c0010b40410310b40c0040c4025410203008070f0344604422300007400c400046d400020058014008941c201a8000c9803172038030301c0e528075001c000501d0810401d2003000041d080843e403034001d04a0040c8613118214003490010340600988001e02c8807615090b040a2600c001d000c6007030001040201103006920040c1020ae041e103524600236800707035960403488a407001d0007a182c1541c200c3c03d80a0050200001c0100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 881678426 1250 881677176 881677213
    0x1d030604031b052a030307170901021507032c060711250504050f010806010b07020406031209080c060f22050303040602010507030f0b01020c120c130617 67
    0x30703a05150100e02c510003040070803031541441000410078000c452000038208080c0001001c0000b5240801c0c0c030743c038009410140d0300d06c9030000c02001000c0006401e09619003030006440b40141c103005980007900c1c54200007000c40d20440d0114003281d070740c0190b05840c89000c040c68100c14180c140d01c030298a001c141e074681d613203401050f900401800c90600041c540741480444100b070811910360b04a040f00b42c200c41c0d8502d0f8a0700429015a1400000642844a9a0100741250140c45c0501051313420426066034070f60000909a8200d40c0324080040003451303010007000003000f240d68901d40300b42002d101d81d08200032801d409105040a000f1102c0e409045400c40b4859254134941c680e518501000c0b1142c080c0c15940076039414000864005019a01074000510406142c3d030200708644030152440201c45201099900590005005800609003428200c00020601c0225405542402e00040e4186c401040007002a61590020011411400580300100d904d0f030b00500340c01e14402048201 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 881679676 1250 881678426 881678431
    0xc02120405010c0b180f010501031e0317100b040e09010f023115080a052214010b06031603051b0f03041e030507140c1003022214011d0306 61
    0x3015003142c0800c000c0b01d82c0b1500040d00c5d0703901c80103845500c2da481c8440d0340200340901c0145e0711114803034224109032950202c28018558542c6540a00b40c1e55450038445101d0010010002c10406050115181109002500007008085114030b11444d2248010342035035901c0381c1c0c40b802c1c0c600502400b074468100081d613013080c0b580c1c0001c0840035030503213405196260840d4001c0100301001091407020720340c4945560700c58a4850300900154640c10a40e82c8072500c0c020404c0a155804072104000030420440c8840c1da24030100086220761000b400510181d00c20b40d1707043d80105c44a06062411034260094a5001c0c1d1302c080d810030030a4101148400c14410170b00c540c0700d1510000002000c0020b410114103c2c03c0f40714000b0500c10a4a10740031302154090f41c0309407494000d070b02801a00070800281c1081e0b01030064032400030850424400e4019401c00d0740b86003008001507082a00c0e21900440401c000c0190311000d200302502c14001510b9501c081090030102e0b14030f6001840c4a88002500a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 881680926 1250 881679676 881679683
    0x301090332030a0518061006080a0b03060709150206091b15210c0a140309010603020d0f11010507110618190501080a020c0c0405040507030c090c02120405010c 70
    0x708880d0103a1001c41820151008406410102100384010392000c0c1e80b100d40b0402064448802c009440c010490b035982c0200c3c1d1521159a28200c14050288581c2840b9001007481202203540c004800019080103421614407000a45001003080661804058582c00030082e00240c611030800701d040580b1444420041182c40c071070004d0b070b030180d9101c04466004443c0501c5031661035503071081d084c0da01120080d0407110711000c2c1d40d02140f410800f0000b20b405084664848111103800d00b43c0e1490345030030040200350155604c82001001d600e5411014540c41d00c0750314424060038281ca8003000141d000102181080340c1030103001c00040c0e030211070303a4030200c0840d410b94940307080c001050040715584900942001e5112502e101e181c0301814810240c5000740c0b17401d141c958447c1088803c034000c0c01d460f00c6080d400801320001e40e08042d440141c1042c041c3d401e48080645a4440c489071440b02d5000c81007141e4cc500607203007140d0381441307210f00310445640064541490140000c102c480c1070000503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 881682176 1250 881680926 881680967
    0xe030606060304170f040618181a040f0207020901060c05030a050f04170d0e010206060d02090603012012010b16030e012c010212120417090a030c03030e03010903 71
    0x3d003c1c002c80c483c40d42c00d420030700050940e6415042c40d000340650800c1c400e44010844d1100141000100c55030b02e8002d80c1c441a00c0c240b400c42d043c20540c006000b40940c0414400301d01440780c495920f450060600208504c0030159480046205100708198140d020340304100c000070b02200091004411a00e90900710310304039441e50070700011600b06200300c4c4e206103600f1581100a05c000e00300883c2120140036a520360003104800c030801640c03110005ca5030160302c254000401001407402841c0300303401c000090300010750013008040c6401c008040c100070340b1020340b0104110410503410301c985d501500c500c07200d07241000c14080070030102d548910b00080903c0030355401c0d41040c1e4818441484902d41045a04446942608c4071585403d109801e50f8018022010341000302c4e20b018048816900440c0c5007400280d845880c0d240540500340c0e01041c100784200720740d02030b540e565020030024600503025191818550310b00580882c0545c062203009034103110601c4080303034214080a103041e85d0981c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 881683426 1250 881682176 881682181
    0x501020312091501030311100b060a140d020307030504021c030507060b01020c10110d03060308090d0206040e0f0609090607020c10110a061b1103041e080118050d0e0306060603 77
    0x10070b0502514050b43c0401e10300000c000400d150303201e081d1042c0a8030752026296080e013900403a8003510f40402c1556000002005142c240500ca40005d5004c0c003154010703a8204131602000500341e03030050300c82c0c1c0002a200d01c2030109501e401c03818031103914070340807124091003455036020300680a010300240801344d0f103102181040c6d00a12000310740301c2e4014080d80c2040c007003440242000b07960909501051044071026011a80207204400660340c002920b581043c801e1410031460302075882080340c1010b818000010b0b03c0302138681c4180100d40e2590715000a16040d0140704241e10700034141082640441c0500c4002500801d0950140400b510f09001d2298042419940d400000242080c14030810080c4010302180380d01040c2c0782c003544280440740b03464110b02110004240006490705803c208000c121100ca105840e01494004400c50000c0070790324500d50b0b003110041c2984402e1140140142e200b00001031021040310030650500e4088000c2250100380e0b1404024500750080100001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 881684676 1250 881683426 881683441
    0x90702101503240c031e020c0f060c070b0c0423010203040510051803150a0b0d020a0e04050c040515060313021207060e010906121d07060309140303010501020312 71
    0x15070301454200f0010140002010b0040ca50840d080c2501c42e00d05140078880095248640600d40c00e0790301d030945000e220404901e11500079800a00309803a01d21600070b55030404607091142c1c6100d64039024200f034441a0341d003004032211200418000c0214030810080c8242e8100a41c900407100c00c011203078111810f9400180c2c07661044e0b81110394032544c052607021413a6031100003451940400d903012918400380006250343c8140c41c01410500601a0000030f1020400e580812044d440003000161901c50036000300f0740b105c01c2500808540c20a9004000522804100752500b907441507400304954540120a00c024960140c45030f8818240000407846d005074980d409400550010200300a4111480829a584581d840342c50301142049d14980c03251b6014191040449050340c490341400018980640010801c0d00c90300350090400501c1c00710408030402c01e02d0081c00d0300741c4001841043c2030900004640c2c00000040f01c0d40c0c0200014409642c2c080203130342c002c4c40c40034610005503ca204 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 881685926 1250 881684676 881684711
    0x50418060302060f22140d0f0f0804061107031119030204020d05010e151309020118091a03010216060c120f0f14130210020709050a0209040b09070210 66
    0x41c400303544140c021607400000840b100c000c3c681202420109006000b10001e0f0a4038451140319803000c43c4900200006181403001c54001c0f2548a4515500c102800f5560718500350140c40042e10b2045011509006d266009450104003011440052440303900d9561010440303103a0307503600360051155218840312482d049003180c0185900410664403110315000d4100101002d00c60002c1851229000c80c1c2d90414080000c1d0303510303501070000100b11b40d1001c9400040d20881404904000440d12030352000314040241d400903101030200403541d560781000c1610729243c91200c092081e4810410000a80610000340fa400da60286005c01e24a10301681511062001d00c1840307687ca00f840b9040032282c60a61008181c041ca0001c20403100707050031041203600904980c00e0815013101c0c0f2100003d860004040b4101c540e4510441c0c0b030300780c0c5944000d4180d400607917016130702e103402045e112031600c0e0500030b91580c14030944103004c0c14688240001d40e40c07604584502c00c02d07696250f000700e04a5001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 881687176 1250 881685926 881685929
    0x103140610091701090203160605070b0c0d050403031406120a1e1e1a01080c12010e0709090b060108091507090e09030a08010e06100503150a03050609150705041806 72
    0x502c0005811180414104e028091400c400c03442406a15103511420400c0c2c0ea2090682d001030366014200b815540da14842c1c11800391201000b01e109101c405800540740c02464402c038800d0f42c000c036000c1244dc0d02401041c02c05400d80e4810b8000c00c0c09820f280708005908040540c014440d40c14013406008801c0d404040c4501c042c041c0080448400881d6480d2100c80c4d4005200fa84c2c41c00418809030710f03400300c6500038080d03441160818410400c2502c0c0800c00b150b040000a0000940e840c0280202441c140c3e85502921038a03071949600818050f9040340180e011a080c00c0501c098907124081c00e45505140c00022140340213070001c00d0301184101254400b4001c02d05071221541403080800d55250000204403001940100022600281c445c1001c0d01420b00503011085408440c10199050f4100600790210240a00d50b0040301c1c0e5a40b11982d4002c41c09007014002500781600428146903036008101d02d005020414424600e500400b01c80881c0c00a0a40000e04007560320700c00c014001c0c9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 881688426 1250 881687176 881687189
    0x290d0b030a050f0c0118360f140709050d03110d08060f01090807091109030303100e090304060804141c09062a0f1b030503030411010314061009 63
    0xd02104008000001500c200110841d50484281105841c0116a29010500b194002520100c400c001b40e00c408596640544462003160b000c0c00c0008040b80e501f5103840c1604610700d0740310382d0348045650480c49000040e942d940e540035028a040e00c000741c448030451141034000c1501300c184005061040c51140101c0461500390359803c07404c00c50041c691001522072500c01d5041d55000d00323542d0300440300c000464201031b01812070540f0b0192a1802482041c0c414440c41c8000c1240c3c000780e50b0240300540c0701e00140c0d00a07580103070404044207034420008100000c01d5000300320901109401071400d07a4065032104580802c140f418210314104480001060003800c8900c51180c50a50406240d000340c402035514218015040c0350240820100305030b2121a1741031342103620f00400d1003c04074400990140c3c400b0f03031208a040c00020344144c1a0743c025103c0360030200600041007101804048103400928042c40140004111041148006401c603441484210b1654803441e0140d001003004102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 881689676 1250 881688426 881688433
    0x903150906180d090b0a0c020604170c180610030b0603040b0402102a0219080d090b040e0a1505040e0601080601171c0e09040303090507290d0b03 64
    0x1404000655202815100101c0c200399107403000245000c000f41260000e1074503a10010070a10303000070380480f41c1c828100720741004818480180907032a418000e05c02031418001c40700c44c0a0303000704007904151900803054441c0034801c91880f128031340c0c9402e41e504507401b21441c040c071000000c002c0c0c006100701001d164120b5004403c01c001d101e40c2c030160501c00e50003078031b6000c0100d8518000300c0e0b8805002c5100d851041e081004c2640c0c03500131401c0f041105201415082140100d024100d02100285e80300c0c0383c907540301700d500000155000c40c04000600400d0181814241400c28250015600901502c8071a86d214120b0504008619001006040180080244242c200c030700a03100d00c000d0056000501c541c600001d210391060064900d441d0003039002e81510881c00d400c181400401109050402403012120115503840100e001c5c0150720030346000500442c14540607080c00c0566000300f07401203002a11003441401a805802d448510f258000c0d0340b50406041d640c024950950174640512 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 881690926 1250 881689676 881689681
    0x204090e010203060f15180d050610090f0209100810051002100e07050102210d0203161106040302060c07021c030309020a09180f03170709061704080708090315 70
    0x80c06500441c000c440030381d03150141d041410140841c00300d8002001201006c20859100c00c400c540c0084642940c006002c50f0b5500640d0f02e40602c0c00505072140d0441c0c1e102910200031444552048110300c1c24080400d505280c42d800008040c0303a940b500c2101405400f20000c1d00b0344e0390000c5118040c003401015400c0c07800711f114000755601070000301600400c0c036080207403091503400501d90084600c141c1c0100020f411a140c0300c2e05d8054000703890202c6903024030503034000340c2031070010310300c110311049070307988084a01a030041211820390040b5680740c100ca014400440d501040304d40d840501c501c00325035189600d101191901c26480107100700841c0340c9082408041d8160013111100b402102c80d0340d02d9589442d044070407a900380d01c020340310030385500c04a0002002c941c40070b003405029060a6082e010460902a0403c008840f800001082c0c00f00501c455500308821168180e844442102103241a43e1001d02600c1030381c02c05417540b180401c584c40656010482520007a0011140305000d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 881692176 1250 881690926 881690951
    0x3020d0c031e091707030210020a020114060121050c04030c0f091409030909060105210103030906020d12110c070306020408061815090c0312030f0a0c0f1101020409 72
    0x81003210518003040d2005525449a003119004400502c4e41044512407076640d407202040066000c440100c0550103400043d01640c14903101502d000302090b000440c1641a240d45000c070550000c2082d41030141111303400c00128014600025100182d2000040c1078680d0404075441c0c2c055130344020701e229002c00340801c2c1e140480e10f1034021030710005d03018010b05003c5c4160440256040300d0091780e991083c0404030281c40c0ca061000d0700103106060052411051819184036005418403003e5012400304c0108105644080080c000700a1403001d420080c5802c94014180e514851400380d07400c0e15402c107800104845c03401c80303d41e41c40400c200c0700904d03a607250100194001c0d11400006029090016641d403d580d10040c0c80d001114000c1c0c009840d018501c02e500180c094500f00491060807542991600c0c200a00c051002101d2407840e180d1030012404511786c10000e1412078a07504100c0745101290b000080700040341c00e20300b401a2084c130500b400d1402400750b40e0000305482d041100c1d0440c3d5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 881693426 1250 881692176 881692181
    0x213060f0906080d0f0804240b09100518270d0e09010f0506070c0b0c2d0a150e07090906050901090803060f01020307081207020f0c1f03020d0c03 64
    0x121101d110090008541c3c682e2075544450754160700d00089800c24112036940d52045205c151300521504a80c0c00c0207070b0051511a1464180001640c0c460740c2d20155290f0745002c00e0000c1d07004085004000019082c0404201c0d0003090401207508007060001042e200013040c2c2d0500e80b000280e5183c00f640c401d030b40c0e951a80d1501019408808a48030218a042900b0718803621416100822400003a01d0f282c42c0c188941a40131031401d440b21644248d0200f02c45145c1c400521400e07003404024205010080e60300400c5408100d4008189500c00c504608181000b180c0da000b03007074110307400c0b8040100400d018809460a20545ca9143c020301d4004203d41510b58041d00d401802440d00304440c2c0d940600039403c0302d10b4818050141101403000488a00c0d01408003c200801071040d00d09005255881145581000200711020000801000000c581c100600300b05000088014403148030403102040348442c00f00c14902d2440d1420b109621203901a07011200c2514842c4020008240c111200400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 881694676 1250 881693426 881693429
    0x3010207060501051c032001090c030b06040b0d0c030305071a070807030507020c0a051306050d1119060c08090d0b070309030e0a0302030312070201090f05030409050c0a0503130213060f 81
    0x30610305c916101e070342821403502e81d100d090380c1500c510300514081c808a0720300204900f001c0e101907403510030400000f03c08101140040d4819610881c0604102c0208002c0e2041940454042e4075810003c20204158030501c07422a5090b080c4959100245d09000264908800c4c13010342c4810b40905000601c0e03440309515100310003541c2c0420050322003020403600c810301448110b50020162030148507514101c03081d1440403030140b0000420666440c04900c0344146d4840a442030703050310110401070b050218180d0401580400b0b1810050304203c005810044221b10141c000e0384017140b64426070322104074860b4425003001107052540341001004018006400d0110005012007070400d61505092225400b0303290b00a0285003072440e8500c0700c034591180141961308564031026204045030351200c054185a01a10185a07514182001981070301c1024240d01c00d02001000b59140b299405000c0d40d420503401c07244840d501d640d80c000110036044164640007440d00d840360009140303420006000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 881695926 1250 881694676 881694679
    0x1e08030c04080d0302070203061f170f0d03020c07030b0a020f0d0c031d0a080d180c08070b0310050d0201030e1209090114240418020403050105181b01020c0301020706050105 76
    0x100401e003c0101242a0300594100942661002c0007145405c000301a42180000340e13001c0349455985d54481d002150420b58003007450304e40002c40340e040030102c1880380081c0c0140034101580760403e121860740d030750742c1d15100250401010102003081e01c3e80c95011225180d0303451100544842844c503901004101c0c2161420102c1c0c609488640c0405100304c00d440303512620f101a000c600d0700c0c1d8885c03001d1548100310243d50390b0f070ba1f01091018076105075000d4681c02d004141142c030403130503c0c2850380760a42035008550b48217024810040503070112900700060b10b0003900d000003075812500c0180d0207030003034446600c03180c05208603001030300c00e00c030000d840550400c4447c0d40e410b913aa104811000082d20203201d81001100304104078020403441095403151031101f407d4075042d5a00307440084050181050010785030002410014070000340030706030f00028005050318080c9a02c9100307960b6250310b000302901c2038404000084c4135a0007807003035001d0200007034000e540e625560714040c4000d242c240140d5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 881697176 1250 881695926 881695933
    0x30f0904050f011a07020303070b0f01180b0603010b0702043c1a0405270106090e030316030e0a0209130c1203120b06211008010212041e08030c0408 65
    0x41000700b504000034101d800140b40070004507403020006080d607000520030380e0180300800c01100010142c1302d1151003809094600001035041004000c5000c818950903c5882e041c000142074541d2444200e03411078485c3c0350b48694038141032022801902c81c40811400c03d003040c0324011414420065030003281c203629440d500b585040300100300f04a401c0c2c501442c5050550788480135841c145039108941000051840726000d90840710808181d20b0402042003659456090070000a0710a024003808403400c07801070f41c1946440b04151140c0514612450b0425440b110001a0101c06001d242100b40d00581020203c0c9481c3c601c4a904454810040f41c0c55000498001109422005840d20143d4155980305482004004140251500c5428285d0004080002c481c10320980810034080058840e0340a480c0d107480d01c2043c40c2c4114030752000701640d0040002607621006100030f0b03540035510070007410041682d00e00d0084188100314000b01943d200000f40801030b103031030024000f11400b54044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 881698426 1250 881697176 881697181
    0x170604110a080c04021b0601171b09040b0c090a03140705100c0605042103050a05060a06021e0a0f0312050601090e0118152c011a07080705030f090405 66
    0x203006403800039104440b0b041e080b01000951500c2c15800a007203d62181c00c180f118240340044003410325500f0780c407806818044141803596510280a0170070003003802c0c40b0f40c10101007818041401054000e200510f03a441c0c0d10000b6401100c880280c401c3c0c010090105509a03071a4134118011316121640410507110b040000503c600d010150340b0a00b140e80d9480121130758156543c50064240600111800c070341502c00c5a010510071520304420030b0305990701061074140b90b00380508441e0040c2503039014090340c0a05000c540d8000419541c01c941c0007603414148006030b03c0640c1806828000140703401c10115011061640c0041050000d8003505000c03c6651902c800649000030b01d8400c901d003082041004016a11303803003c20060b1030010240100300c4259800d40c0110500441e00007904144030300e4103855076440c0b20000001c1c1202452520070455040c1241c0240d00c15140f0310b801d5441000142d02d00c10000560f0075624040d60090860340c551405400482594100d081d1840c01103142200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 881699676 1250 881698426 881698429
    0xf06070f0b0114120111071520030114030705011b030e030f060907080705130c0210050108030d1d0a0b10030813090c02010213060e040204030516030b072606040617060411 75
    0x40c0041c2d1510007046d28a84103c0d03640e82c44880a40c0107030501c066949110300443c4800d00e2243c6001c10305910561030703403981040e1407900d00c0c240282c00c07031b40030303500144080c4000d90300030190a490400301780c021480840e2515003190210304001c0702c01d03018040d6000034030007040c0000344d00b0301a41455040d10310b4070b80c85940c0d15965111521440ba40070180c0d00b23015504411781da0003070301201c00c0b600c141d80d804500c120102043c2d8000380d00c00202c035440052100b801a220384901d001c05040e82c100c000c540900e05400c0c41e50790b20035520180a011072040801c2820785450a008011030744800c0c155190103100c0800707624a0794601c00d58004508007202460124410b10840d00c81c0d00989910016650500c4021242c2c3c510b004c10310b07030f041a420000400881c5040005400168103c01303505101c606620f85803000110141a40e010300080152032a0040207101c131940384000100d54400700e503500c03000014041c044541c411211341d11070207119108498003040d0f05110310b00601044d00c0d009000300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 881700926 1250 881699676 881699681
    0x51507050409020715020a0c0c0603020901050301090c031b0806090c0f1b0f0708010f0605012d050d0501141f0e04051806130c0806060f06070f0b01141201 68
    0x2105500080c030304100030301148034281d01038100b4900409945040ca440180104100c0c0d002c40180c00206200440640c100481e021070f481c090140c9180550600b00d400c00041d1840c0810f000d0000410b4640e851442607911951081c3e41c107645c0d07850840300c181c41110b40940080b81c26030f0301c21b000302030000009480000410440d003110714890b48140c5003080c2910302c82500c0390030700141d07503d6008020a18601c80810070041d0054245040001040041c450705001100c050f503002c2c42c14402025041041e00609001d88201d0a1221036054483d001d6424101c41c184181c5034020700c03291900c800858240340314080300601500a503925611091007450080001e1030001c07440c00014000d40105401d0b0a1940005400605001d28043c07481503107400300b800c001007282c1d6444180225201355041c4000c0007020350042804001401c840e0400c2004101c14510b4031031424040e00d0002144010031441c03003807a203505070304500c0d2020a541c440003030320081e22403c44201d1142201c081c04158110041c03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 881702176 1250 881700926 881700931
    0x6030c010f0c300306170a0f0501090f080a020c0906090115050d1a10050a08040f0807020a060207061202090307030209060d0c0906050a14010c0303020912030d05040515 74
    0x58503807004008a03401c044486502100d811030705055602480440f000899050b0281c100030b0039803500c80c40c900e80e1002801c4403031a07400045a1041614012406540818091102a0095210300c0c041c030240c10030b28090041e00100424007895102c00c00b043c00140c0001e480011216420b640344d0b07001c1003040251070042507803d6a8462148001080308102d903e040700328580c2603080171408c01c11892594400c07201102c1381800c041403d6441d148540c6055402d49141e9003076424010300706a580400205056001440241140e6013034041d0320034807000304140c8650300d40c028603c1c054203448110094503400030b80b040c280401c60045170445014618020f42d0341c40701d400f900400c5151700e0764080020641006d4800c0da0800c034900340b0b42010031080303c0c10a0240102110100e01c8500c0d0005200b10982c02e9804900752102544407800b5581e40282000e2040340c146c5009030700d555541c40010041d0500010840f250b01c80022489204101074108a12030350281c401e4429520149000c100e450104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 881703426 1250 881702176 881702179
    0x30302030a12200d110d0203010303030b0a0308070611040305190b01171b0f1002010c0e090412082701060f0902090a062a050c2103040b0f0c0102070b09010506030c 72
    0x6141903540d80c00d0355001800002c504c1e088040b60096007843c00319030f19130204c410020695000130040c01030503003501030402e000e4070a8030b10f45006851522200c1d072602640d0001007403c2c0d1158261004a8030100581c1c024503089000d42c2c00c14038001d4100000307091000702c2180c0f641402c4c0000120a6020003000d449051001c016003170507241d41510100044032010040d510140030300d08005181c840801c05c81c081c13a4190000955680d602502400c07008404000900c904001002c202c000350803058412041480342c140310445849850440c000c0c00e5003440c050034290044158245c000a054010b5000c8440c2100040280c54075500000d050381704036404e00c0d42140706030200700b000c24412611101211001c0c8800500014050640036100300b45580a0320554401b6029440c5890440d400c3c108078161901e2084180301d1004d81075441e4000d03403207450009370010841002c49000f240488810fa20300c08000c559800d07040c034201c1c0304c0a100395200c890562a140005440d4140003401d03001c8800b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 881704676 1250 881703426 881703461
    0x211214040e0c040e010b040f0816060c03231c02071113090b0a050601080a1406010e03070b030112050f012007110a060302190903080405120f0601030302030a12 70
    0x801e94240032154001d4400e048903802000700241050f19800700e03501800d80e42d40090b50715451302200304503800240c0c1000c00c0e103070040000340411000f83d1551404650380c90034040c2e0840c155082c16107100401441e40d0740500c4c0c082c6000311074541c011000384104090000d500e003054258084c110224095200d0042250300c02c00010842c41c03030009004260b44080c0b400100300b40f415070340c804110341019505910626114010301480c0c1d03030008207c03580076003c5501041040c84140701548041d1707001e0030060500c42d0b400c08190490310306021a0b0b0280007070343c0d060707076403541c0d81c14499841d5020300c0740540301d9000c0e110000d509030f0b4040c0038881c90b81c0c04000c040c941c19080703406d072550164000e1008490b5501416038111040d294041180000d24250300d0060f185da10b41d2103103901d0500e4001041d010043c2c9260148006210f0720240e80581d041903ca092000e0100700d006440c0c40b104c840c200c480f91007103800000801d079001000f00141c00840d980d0b84044c01ea08101c03d01680c0070500b94420441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 881705926 1250 881704676 881704679
    0x151b080a0c020c133c05010605090f01030e190c1a0304031d1c0b07080901060e0112030302072406091107061104090903030e013c0621121404 62
    0x14040c5c120103149600521448000000c0300c1c42461140b610a0300c488901601d2000c40c0ca00000303d00c9442d0052000b4100a8500304260300041c544203102c55600781415034400d029038008204000382101c2a100340040d00400c15941810403400310f4501c1480c1e01802c01400e080f80a07181807040c0d03030150340e050b2210780b000c000d8440c0101c0e07910644512142c000301031240d0380d91000004203003941900e000da41d03e090642400f03030005080c900c005250441303580c1412001c000903140b665070a411034030720703825010502c4076a140c00c80c06441903200151002d1801881a402d01c2e001c002003100340c8110364800c000d100d82d42c225840c02d0710100360003c3d425440078058600407410070380055900c0344c3d0743c44030703a480c20791100e80708400c0b90300030881580066507c03540c044081d4003d21070006c42c9001c20340d25045840807085041103080d0500e02503822200511070000c00c44015403c66009800d040111074a100c294480c4902507100204017569058910b07004042c031240030f2400c0c50b00c0c0000c1c07540000c1c50306 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 881707176 1250 881705926 881705959
    0x3010b06030115022d1006060e010309060209042a0206100501050903010608070801061d091e0a0203101a090105091f0b040617070206070804151b080a0c020c 69
    0x85984480f4015409072825612000c0c0078440c142c921004031103000440b036403003021078030f2403d0b111090600d03909240c82802c0c081a6013105800300d55410034640030a4074074a0f0301c2d000003e8001d0400c01070f00711f42021f007801a601c2400c510800e4168580c0c001c07400741000e81d0001c0780e071050301350703080006840d05074020b200550bc9100102005000900003181c000c2d0b582c4a0701d440c080040c1d00049041e50349920034016001420283c2140034003950b40d0320700c40d0501e040700381c3c0c0310340030700c42c1d10501001d100017490042c110901c00c668016400a081d64000e000c0d40644034003801d550810100c501c00c508101100038034040210606880c0003401054860341e0348c507589200010303100012072402000d041c001562854200041c0007803c1d203542d401c0c0301c12620b003071611512000a48500e0641d0442d00c100250540c0c1f0000a50344aa000600c14615442c508400301c01001004a46600880c0340d81400c2c0200e82c02100307d82c050040030100300040d1612110498480800010940d40030341a004082041d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 881708426 1250 881707176 881707199
    0x110304030507050102160507050a0b0408060705090a030506040b0f01090c0f05090604091508070611030304080f04080d0306080609030a0503062707022803120507031104030f05070503010b060301 85
    0x2c28415800140381c804000b441c0401001c2003042120a42d020075020310050030481944001011a001000d09150034404450740741e4100400440411802040103125590b0300c00041e4001c0da00b040c15100c07182883d00b0070340d200d0001203e285014804500001884001500c202d00c0305040c0340e03071016541e95450204584592042c066107502c402c0611022450110720309c91804000134107a0f001c94400e190440300c5080c005190f002d0010300004a00e000e01514011041302c0d4050b621200507503894400024260190045421001c0903204215003a1145901a400a419030b510802216425170311094481e550307120305003180700007440c00e101282107802c11092603803010140d414500800701c20b0a08040080c0c008640510040c3e110741c940c8148207262001500e07440d49010141d8a0f1220151000781480c0800308850b50b5056803540010b001d244071b94088100752030301e03102640d5100c0d640e0801414040b80c4d02401e03210340c0030328800020341d272805100700c01041001078001030851380b801e81d01815 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 881709676 1250 881708426 881708437
    0x3021b2b022236170a080609090c0a030f0305190807020c030304050d0b04020402041a03070809070608070c050f160518060f0d05030d020a0f0f0c0507140f1f121103040305 75
    0x503c60985030213030008a01041c0070717107002003955640f101c80d450b00004007d680e420181a0300c0c0c094112285408590f140da41a81007600c0c0c1101c1c1800031408030b40b60071982803159072a07000003c0460400d254403c0d5004c02d1190280a550b821180500e00030010142c03a0700c56889015405240b021a0700002480d4080c0d0076800740c001400142055039442d8203600381940b141e051818140b002042007889908040300c980c129001074028501a401c2c03401c0a842c0c0003000d890002070180c440c46d4502000010480851052852400d850480140e00c1d0070340304031582401918400c0030792b1454942c20125004c0f08522032100100380384030904900341806008986c060080d50940802c104103884e00d4541d00042aa414050b03803504030290b007100b4003c01d401c02c6410050100084072010502140c1e00082c07000c1500d42140c220041605190006596944042a2150400b150000c1026140c0c40100c0c4116010010717255009036098120f010381c00c8945130b64486942600a001040c0806e101d4400b405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 881710926 1250 881709676 881709683
    0x601022a0d021f0306031a0403080105121603050f010c030b060f0a02161202150903280b0c0c010506030d0504061d06031303021b2b022236 61
    0x564005040410943c0c180c1040c030b1011948607041081000001540c065000440391210440c6043c665002007403040306218080c13141e41c03414001d04221400b80000740d031155110300901e000640d246403142c3c030f030b6244004036082d551034002d40074404c60082c02340b0003c0c2800100390501d440b18901052840340c0008401c00214480d00e1000f48002d07001c1607254001d0320310390200003058109481045041c100c601400e4000003014010000070351000140c0b0181c035505034a58417400d41101d40e00709140ca0aa090181c03140e041c040610440456100c001d10310380c41180e00138130a0341e0741c440501d50b850407510b000c0070004000704401c01c2a64072620852400140c840c80c044135034200880002c105403c145c55400741054141042030400d078040001402080e50010810300c0036030401d0000d0805081c5103501203079420b0646054520400140c12100c50ba41c0c02800b41ca00d4050703182e17400f00301c0c081514107040407074600300300740b0b40f01c100841450380c10728070040622900388280c0744844600c200744c26045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 881712176 1250 881710926 881710939
    0x907020f07081c0509060703080a0b100c1b080d0521040302031c151a0f0f1201120210030e161508010b070f0305070f0213050601022a0d02 61
    0xc140080c0e003030040d10000c102c2c040c01440c00007203c4984035902c0c00510700040500c4010808500241c0342d901c1610103a41d05410210542d5542c2106900035020b00308070721398401742100501080139040450b82080500691003071350342e100810107800300b6a49500442d00d583c0d2010504083c2544200f00034a0510340003030400c40030105160361350940460542d8100e000d0f82010403401c440b03140e102291912000c50850500c00c0101852000e140f4903818012440d0074406611034a044c0c1c0f522100302e0703000040c090305c01c07550785201e90a0301c000b03500b00f0791380c0c0e1201001c500f000040f0b00d1030b0211030306505074008100d035030300510242c4182d00030b02030301400740390030b015203203e030b103642244c4114280003040c86407044090013503640b400405051050704109100c0d5400e005170302c04100f00300215032110354541000307650b0780080e04101c110906002002503000c0302000c201990940e02d03070800c5000307060030380880790201540401200030720005c10f0701100721003038a660360302103103040c940002e03407540040c004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 881713426 1250 881712176 881712193
    0x1f0501080727110405031507120e0f0a0605090706050319020a021606050a0e041a060901203909070e040f020405031c090506070804091e0c031a090702 66
    0xb5420ba800c001c3c550000248041010000d600f410300041840001d51015402c0c985400c440c050708801b140072150b00c030280d40e0144508600000c000b109800c11404044408100c0d9501d0203402600741281c00a1980c002d803e0005515802001500d004440c03810300c082c44941c07080c01c220025000419180c08510401d16030345600040008844068261562220350740c0d00082070203000c448454003041e00540c03603c2c0148c07a100d0f040b24540c0c007890008807a0b0710703616802040100c858099604195010b401442600d1f62118800a00303180c240341400e5132650311014194242d0204014803c4503e4120010303401d074081450400320391640300c0322905141c1500250b1502241c102e0390500c1010740c2c082e50006003480b0034581003141ca030740c1d1000e8045144194210302001400d030a80d91103040c0c064400402d100042140c0c03801502d018002d0413004005410020542c001100c000300420b080b06850040d04441092080c018804080c4078209800100c6070080c0c00e104004000818103021801820f42 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 881714676 1250 881713426 881713499
    0x91a031c0f21050a0e010501060e01021c110601060e130b180406110703050c0c100f030507050f0d1b030e0a020f0d0803070207151d010e0a171f05010807 67
    0x40c0f5024000a00000515503d0f80c14200d01712601078010200340900d182e008104c0b80ea00190343c00c0c07201040c9425120104d1440d8040e200c0c901c000c221410a40503000c008685558130071101c03400e400c81112034004954840703440d20201c5d05150440c84d0800206090b915000c5004030700076410601c40e00c0c000611040c0d401c010501d5801002d130071000035000040b40c01c0c020108100182c4006800c50f4140490b02c07100c40007400050300c0e41010f0050603203600004c2c1070b07503000301c064540fa00901200180c0c0c4110a042410040c04074100703003408901210045d40031144a485001c2e5140110001400c070040d0076000c02516420301d42c017080d81300e13600242d540c4c0001e05200c0550b01401054004042103810140f1040712020001020b80c20400c3c0094160240b000d40c090210480d107003800d0a21580b00b050011410703908081e040b114044644100e400c4110b00c000404009038102d0b10b56045100c6022540707601915000c6c443c103426588009070030b102c00710350705a4030f2800c1e242084d100ca1040c5500c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 881715926 1250 881714676 881714681
    0x17040f03020607031e200106210c030c0303110f01110d09170d05010614090f36061002010b03030306040506120f100f05071d0a091a031c0f21 62
    0xa8100300040f014801b07640c00c480d0707200c0c2c000b04070018400240302690600c0629103032440b40606480c034400001d280d031810f001d11116407002454010f1500e4000b2a00e90802800e210000304401e00c01c3d100e4491010781290040c807500c900d00030581c4540b8540740500028201800809c5400e641403a10307000082051404200108010b141100010405601d01030b0094020861414855280c1030200902000c903991118401007000301200d00581205411422001c3d8407121800076280181c0c1a031b80d4180c003ea4000c1075480b84404440091030f1840c461002c07401c0e030350000c68840d05580b0610101d851881c09821040e4003480241017078406140300348909291451001c11203035242c214803130300e00451542d0f000302c400719041e6100910007030410400041203242c03a20b0a500f03400b2000d00c680d440c0c599a00400700010441c100c07080c41011041d413107000c81c64600040c100e100e0300c10381040040d040e115060303524525000f919502c2071030714144403c0d50360083d40103180c01000902c8112030006041403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 881717176 1250 881715926 881715977
    0x30d0c0201030e2d15040b011a071202011d0705031b03011e090302190b0f0705090310060e010f03170d060918030905061c0b030313030f17040f0302060703 68
    0x4400340513900301941c1c0601e00b41080c007940320180003144070405c404240d078001c2c001d0445000c102d070781d031200c0c0401c140c00c0000e010b4203000521441e485030209200e141d054000208003100308502a1444456002d420742d80c60321803042c07540540017030541d582568408400032620000240010825240300c9541c1d54075440d1700281205003039070312a502410b060741005800340f40c0400650308403001701c09454442e0902c4000b011015040744550000d5841c61051042d41c00c00c00001c4d0803036248a500e1040d90700542020f00400c035605440000000d80c503490140d604049a0300442d616880d0f0400700c80b030020076440b180a50340b040da240c550004000107248280c1358001d41d03c1081032051445490300400a103040c0e4071035031040d00b041c48404110324601110170b00c501580b4a00003060280d00c004a8258004e065075075181c840c010703a002050080d0310030790000f42c40c46400e4208610041e089400c40e40d00032402042da055548072010300050030000000d184048c080d0070183c00349088400c100b030352020354 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 881718426 1250 881717176 881717233
    0xd0809010b030f1f06030c03020607032d0221030105090705090306040c060f020705060913090212030a080f160813320312130c080129030d0c0201030e 66
    0x8032060f0b5030801280a0202c013251907055003807001a285885400030034110380400303445520001400e03001c2601940d014902c50100c00390017861110205400d03103080e04110002c1015018400c0e0400584108150b03090480c40c0e50030256040d64240400c1c40b087c000010100c07005c0c0001004804039654017042132034410b610410b035151041d1b0800f01d006000b0030000281c6015540304034414441690b80c039042d6a1800350079242c9035000380601c11138101500f81c03204041e4202d02e140740e40c9540030b88013000a02808005888100594440002002c40c41004490001103d607a84a91140c201d02c41c40b400368003d10044400c0b01041c00a8840142c1075654210031044000009000c203086003c1a003200b40d22480700c409107080c054055140003035284000e004c04101c0c40c1c0c81401c0d904101c01894001d01804584008024144060f02c0c030b180d0b0a4100710803000f040040003000c402c80c0c0b030000b0344041d5800040d5502c100c40c40050b0b0044d8050000501d180c602401500c3c5490401d1815040c0c030080410b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 881719676 1250 881718426 881718433
    0x1606020a18181107062f07020901150c060204030c0e010e040b04171b060402090c18090a110a0302120604060312080a020d110910090f170705060414041a01020d0809010b030f 76
    0x1c0c04031b020075031103800402909580c0c0062009402507075620b8003440c1101c2407194686895100c1356011540d11181c0e0b600100500d102040100500c090f69180c80b059540051401c5e030380d079880340c3d1001c0c4403c0b02110020a00c400300c0c0000f0303000640905403100c20b18a0ba90310315082c05001c41c03400d001d4400f03841540b0320650140c420802035103004503503103400c155060700c094039050442d202c161300440c0b600080350051480f0008180604030540c0f040c07031141921880d0a460700e000400c000c0c00380d40006005c043c080e0140d808101c842c907051250004491740628418688891810151002c1a00900c0740e0416079007801503c400c2c00160050641600365020786960f120700300410030082d00c22a01c144010405100f00a0002480c82c40e8290144c030500c00701d00641c400c00801e00c03454400c1c43d82003650000703070201d40000c4030600080062001042260140010341c42642e040d5446003010b4074450041c0d00030703460700c01e00b00d00513a13080b90080038031f00000c03c40100c0c4502082ca4400f01e920355004690 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 881720926 1250 881719676 881719721
    0x3070809032b080c0309101e09140105060612150a080304090905060c0c15040f1a06010f0e0901120606050d0807120309080d111606020a1818110706 65
    0xe60003040c1c5036100c460314424500b103041041ca402d030b5a040d00c45400b000207036032318684004540380c489178484002c071240e8213114052182ca0310311012042541040107543c200300124010340341010603241c0030621411b2010450760742201c0c401110518102c00c03904031a1858011800000c248004c101a103c2900085088051031801f9483c1c104000c090300c0010703400307000c03200074020041001f480e01a42c2c800041e035a0b848904004030160003115008220100007401041480300c000c1441d44506426203c1c2500c42003001000d941800880c09070903030101d01c43c40107004500042ca44c0005003802410001851034940001c202c03010301c031000c1511007541c081103030000c1183d0031205c5807440106180c2407245505640c0c0d040707007501510310b09045e42030303c4201c580c058088a0050701c4c607880001141c55001c0030035003003590082d03106400c0000020300c0d60840d130480d0b95540015104640408545500d0070342400d603880014000042081f00306d010030480c2c500825400c1c02400e5034100c06421802000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 881722176 1250 881720926 881721013
    0x1d040c020f0d05030c16050f030d05012420070803030c0d060f0b040302040b01050c0109030c121d040908040b0a0806030606090103020108070c0302011e0203040b180307080903 77
    0x86400b840035001c01000304100000034400c1000d83c2d1a04070b000c116050035452524102d410700e80b60409544080c840440d60079001a41908554106ca01c0e2240d200c00500050a4400c216192845058045031079508506051a591a60010000318840964003455250012141140e00079900c021000c540851039029480300c901c200b00040201d0400c401e1401c1c41c2149049141c0607601c0003922690342d0b049071180c3c91f40a40221003504541e840204407420862401401401c0d00342c0c5c05403120780040441300700044c0a4040003000d0045150781128600f00b0804000c064400c159044a8a02003400005088007820015042107016501e89031894074003003003490701c2c20000078015485001c6600041006d80d800c901c0c043c0e00300e00e05181ca80d40001e600d0800343d01400d0f0403a0201e994100101810000c2c01096000d1801a803081c98004865215500d040c141b0b0680e180b00501d00760000c000150014034010000e000c407400150a81c1d00c003110007501c071082c454004c3d22110013001044040f1060 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 881723426 1250 881722176 881722183
    0x140a020c041802010206191d010203180309240c030a09090c020d0f08130c120203010f200315060a1709071818080c010e28031d040c020f 60
    0x311000d55280240a003a074000039920000502000040c8021560320300c14101c040d0088c020700303d10a014425400c4500380c01038000d520840302c90301a051a1040b1205c0403070088111401302000501c100e00c20205002d150304030055100603e541080b042080845010040c8042c00004449880324040946000308103826640e0f0301400e0300c219004014541000c5412061010f1504080d2800354030651742c0718500780446030540d10240c040c01080d0400103840000c05000c0c1e034401c3c802c0e0000e0101e4088460a04c068850b02c035120280513030309551881c08406558042c642c401210843e0f10311020500c004074100b50301a03000f8200140d00d08a00c204051421085213030002290304c010940d031858440b1035100c50303520610704494a0340300c1000d9164101400c441c42d0705c95410405696032003c900510354005c1c503000b070303c400c01801b8901c803400c240c44404078103811901c1e1118022006582c4c4d9034003103501110b80001c02038449017080359104a51641d2081601c442d80607001010309205a03002c4516 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 881724676 1250 881723426 881723441
    0x30e011e06050111120a0c06022b110c03030604110714031b0f06011403010e100f0c0831050607020d09090e032502090c0a031404021e01140a020c04 65
    0x24079407100d4010004170b0050400c41d18800c10916085822104e40d2619801a1240240c2103460032101d88034601251608500d00d1102401d0481c00c02254418a107201264002c00300250040c0e0410f00004060741040c1e04050744886229482510b002c0d81c9544211b08481000840780c1d40b40d10200d8440e2000c02c000d00342030900511a40141070600c540801760b580c5400500401c60072154228001805032002d400c46032149003402c0543d07454101c01c540e100c0060640f0700c000a5941c3c00c0c000034012060140b808680070b0728170710a151540300c558600100c0300688100c0c400d030014806141d0a00864418071040e4041d8010f42e002d400d0042146000500c400723070a410218a45203070a5001c207500d4030000803a0340a20480c01c0030000303000200000750700d55450702406034210405808010a01c0151001801505d280c0d840230041e035410700d892802d1000080301c0080d08030550540c102c0c0c0003160b19030310000340702c014945050f1402d040f00307a401143c2c201e9090f60000d40d000749001c440c5407400b80913011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 881725926 1250 881724676 881724707
    0x3030207180513030c032a0606050d02010906030e2a182e080304031b09090c1e180209011716050c0c0312070203100912030e011e060501 60
    0x85418408204404811040380040a10040501e45c00402d8016080d0301d503444005070401c804041c0340c104070204c0c51102c840440e0218607000c004a103038a40412035104440d0180d640413a103178182281a401006003140045c4d4030302c901c00d064103403041c500501c04540b00d000c88450346040169800e2011102280305101c00507105a800c128453740c0c800003e00140040d000081c5626000103284d114408a83e0030000c000e0100240c00f00a202440448240680004420320051035481c5c41d014200c900000c4000d08214100c041040341c004840148070002c0d441100c206241c0342e0b10611141e017255001100650160003180002c050b41c2c00100f021940002d180c1000f0700c80c0f408504441c491460b03030b5511010311001040ca440940810001d020f04484003404803440858210358520032500301100880c4280725900404092a10600420314400e91201103900c0500c80031300c00b54040c2116100415503590382d5007030025070000031403014003141d17400403000403040d041c07a0005205280040300340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 881727176 1250 881725926 881725931
    0x30b07030903230f13080d020a051b030c060d151707081506010c17040e0a051303090509150405011202091e0a20030f0a05090705060d020901090b040303020718 70
    0x20410b020382d000c216101241c138950416502c800f8410800f06050180c0c002c00d00a10980c0c031890440c4d0340000d56103400380e0003001164070a00300380c40360141c41d200038601c00d90141c101e0703035200585041480282c021908501e0b000b1900c0000c0701d60700704400d081540844408540565800050300d01444450050448000545822550b02880c80b44450016200c1d904000540e4041800d20140c001d0107100800408001503486a5480500524200a48168203490f2414020400d041103440b04450300641c142c407801d294600c1e0808002c0082401844030550020861011740c01d03644602c201e81c081d020b000f865000851050040c0000003038024440b00034ad0304035450001c9081309030364440303501100e000008241070900d0a48400e180000c40020302d0108408010300517a004030f000000c1c404c07810803104000e140d5403001300760340ea14510b01c1015080041004039281015250300180794010060604505655807480206507540c010b600c15001a0031604040c080802c80025003203601e0481e1105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 881728426 1250 881727176 881727227
    0x806190311060c030c0f030909060f0f0415052808060c0304060f0f05040302010219090f0b0904410c040e0402010c0506070c020a0806041119030b07030903 68
    0xa07118229204802a881150302059070309031814100229808400b461081e0744512001e5100c0c1340e920b03000b05042c07038411200200040c1050030450651900482c000345007280840b500800d100c0286500d100d06008004600000304040d20303a003248031f0340600c40c20178404041840c0b540f040b4200c01e00da003101c0040e411a4cc2405200309a1300c0c20fa80d045500410001a66502d0444850041002400329244c45081004100a264040d170141c04a2a6489001c400719618450101c550703c0c000d0081d9202d03d81005024040d0907400d4000d4455100060000294455171410740c500822064041039940d034140003141090000e0303840088614120180c4080c2c0d282044a00c2030403e0141d0301540300c400c0c06a8002506580c81910315800700740e0032000341d58039810300e0400200207080c010001e034040c03503035141c0c00a01c4200001e0654070075604242c2c45090045d242003001810008508584203080c400c0301d0100110301d620000e24000c5500391800115110180b40180002c54070207920150760860418 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 881729676 1250 881728426 881728433
    0x1502040f061107030507061d0d2d0203120415030203060d02010507030309060516030e0f030415170f0609060409111003110304060507020c100219061b08061903 70
    0x805054540710b0a29581c2d030314440e5049441c100c072980c4040c0c102e200701400040d01c1071b0805090300303201a511010a01a80c500018001040c11014005149401c07000340100c00c1c034150110540c41c408110344180656006400013071034040300d043e03e0000402c0014003008420f034840401c1f80030a01500b415801d5242c01030002d1804100c903c0d02a050100000b10f003c20107100394090801d00f41c0c801000c001906100820b68600b01200040c040030920f8083c081c011510b000500078030740030409006600c1d01c0e050032007003805c0031002d55694051200c001148015625800c4400d8480e04604006110f980313041320810507600c4c03015000328003892038000d040c40407406080f0381c019240f034203070b6600000e03000065044004014448900800c2c480c08018081000781c070703070005401654540d08541c0c5c02c0c4210b40c01c00520480100d24240541c1c851b114280380031001c642003154103400b62000040c1c62003d0b4810300450001000a0302c0040c402c4802c00c0254508620703440007031000f41d110070922a04580c1c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 881730926 1250 881729676 881729699
    0xa0e06120d05090103200304201c1203020405030a03110105010501050304030c140c1c0b1b0a0c050309041b020706050310050607020d02030d0507061b12020904060504050c07150204 79
    0x3c203034101611120b00191b0078100409441910070140d04040d035908d031a080c80d06616842d80540c5e21640b50314554000c0c0c5140080c503640585600202c1d500100c030341c43da1101d091040e002115424181c0a1000041c2d036541406035004c01070184d242d403881030001040035402c584050700300c641409001d00078000441e600408a8a205a0140c4005000340e0004151490f0082040c1566032140300f034081c010341a4004400c04c00c0f1140304454240594543d81d0ba100d20070001341460164141040c0410743d400c5125089400c103544c0254107903440d0010010214003a075400c08208000c00c000000138801300d59042100d50024105490502d0039400d1a1054185803c510700c41c441c403540d1702044100075942d50550034138025034010211402141d844402510680040d04180c60040c507000308910300028060314100103800725a1400482e1a94812500c02074000000480e0048d603504000303c5d2589591040790300030100c0d00c0544e5110340c043c1c81c21041c0203070203c10404d40b450060004000409032030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 881732176 1250 881730926 881730937
    0x601021020041e050a0e180c0a0b0c010b0301050c070201050f070204091109060f09180705030709150902090609010818100501230927070906060f110a150b0a0e06120d05 74
    0x1000d00c7c0620341d20140c3d134501940c403e0b1144d40207119502c0041c070700c0c0030100180a544004030090000a030311a082600301d65080350160346081342000007200640c40743e001032600c250020354481c100300300390700824200e895810045408200310a0201681e140091080350b0016080326813296442c0c05070003007156030a01820000e80b2869011a0402c402e10a21062018186c042d0440c2c2d2210b0780e601514016141000d41040303100001800131468039505d00131178084034009040e45180103c03c0e4011504040300030290307a003182c04501c0c108105181400404500303400168007060720350420386450031605081d06041c018500d0032a41400544954400c01e90044085800048142210500400100d0f16100441c0710b401064800700f08581107501500c00da84241d0389110440024400540b18407681a58100d0660712481d1200000b030841c641000e01226105008100080c1440100e00c0c4581550458128003140a00b00000c0e400c110013440188038050340101030003035400034060035500c0785 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 881733426 1250 881732176 881732191
    0x905150d021c0807081b07060206220503070308060901060908151803040e22032c030f1e010c091404090c03030e010f0302030601021020041e050a0e 65
    0x42d00045090361402906480885030406940b42d03444c0c820380b600c007207164803564401c6004641402000401100000d5601c00c1d61110f40040c0360b1074862218000b017000480b0b0700700018840042070b070320008400340b004d44401407280d10790b44402c0c1070100421601310416001002045803d50301000280400103040050030a011202e035140d8651102800c1e020420007003000b6580700000f03002a1107000640710b00d100b0440591807581100e0000c6104001d2030103160054005504c9110344420381c15001e09103074411101005010b40080150b02081c00e000103810b0140d0103801450031544400c03d1402c9c00d8400c1e40c0410001c010001c020000a0a0301c0007502909941c1040e860360a1025240c5a0180f40443d4222100c518020303664640203100301c4032400510300040d00d8907001613441d07000380280c902560058002d0f003854080b2650000042c080c4082d41481e40c6550b9100c00e0030003103c240140040e202d01920600003030040325044403510400d51100d40111420710b01080309455500255401c142c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 881734676 1250 881733426 881733439
    0x1c06050105090702030403200604030f060c0f0c0b18060a1e180b040809030a080a1b051b0102120c030c0f060f040209180d050309013603170405070905150d02 69
    0x391ba0094450000351421240c1200000ac0c1c040144030091031000002403181500f84030103240040102d40e81c80003000da00c0080f070741048050002955203110300394000754040c0440400d214845086151207002c4c1d0f0000000fa81e10000c60002c040300500080203e101d6803020b0124043c203160034446441d4045020b80721003810008101004100b008440c0d404038002d085038440070041c1880320b056408001490003142041daa16420760041000c003c1e48290404090418484030710340d000d420100d00a266411400384810350150315030f003a400f50030f084152400440d20b030303420540c84614080c03150345034203121340c0800e04010800001c501146c2d40544d0584001242d071302c86a21715801c0d1002e0700301e01c103001c0c02003800144002b5805000f543c419616080284000700c240da40041d031000301c0d10aa03001c90301c40d040200b41741540350706500d49428880c1c607200581420040702c0001c8000709460840303860f0081c2070200000006030041c150001e96104040c0c81c2d10381c00c500090404003581800030300400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 881735926 1250 881734676 881734703
    0xb010e0a030b010323030a03021c090203060c0c100203150f18060409020f060705060406200706150e010611100b0f0f0a0b0d0207060c0806060a110703021c06050105090702030403 78
    0x14102c43c40c41c5c001c0c48020b0704494442c55926000f6001c1e400400e5919081d0010002c054000d41c9140900340400c0d4000d00900551f4075054821040c0358403400d42841180300e0300200b000409214401144180d00c1c5106011892050500708204401601b82082c401c000711503406403002c404507000d030703004401280c0009103002c0c1032010800d1103001d504503617441b1001099110500001240583c41148608810081c044070318804030aa8507580b6921138103907a003445440b00003401c503409840d1510030208000c0f03400f55500001c0c951807009030410000103000c1045541240400c00c03242c0720002e1130303403424410224100c01003041d1a420900540c0318001c1072041c8100c40c0c5070199460081c01941e0485039962940004110181d0301c00c0350200c51484c03402d0a4680c6192040361264080d800080000303241c60400b10b002ca5918400d0195107549009800d400801a03031010982110480425446023545945042c10001c8910590010b8020b44518080055081d8003104540640b0342c0621212001c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 881737176 1250 881735926 881735963
    0x1207060c05192a0807140d020d030c061503020d02190801060b1309110406080a1e0b0310060b0307050a1b11030706030c050315010e040c030b010e0a030b0103 69
    0x10140c225a1440078840c03400c01c9050144508590b200000303c1400844540c1ca404603900144080e4860351661741c210500a101144200540c080440750080403070700540900d80014030003402074a0100d012510480c049010040e0034040e2000c410483c000c0d12071130301e1940d0045401d0f03101d0203500a100301c0f5448448621640020180c5001d000303000000c001c0c041e214402171806902c042407410583c20040c00000d034680c3c01d4040d12899154100d04a800c00b460840c0941303203803a0290141249648940203280700780074031404999114213402c408548030109109140c240350382003040b0120941004018084081c111041343c1d0840028034102e41d5070f03025a202101c130062841415821004442c00d0b4801307100e1415100640c038042101540c104ca5035400042d8200e8940c2c440c0c00c800300f4410b0000a48c554600040b0004011040c18072a090004450020b02141c402600d030744003183c2d9a0041c001d141d40e00500849544105840300440182103480d520014030341407000074000070200444000c41e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 881738426 1250 881737176 881737183
    0x1011120d0e0109060c11030408030f0a051b011a06070b060f0105071707050f1b13240f06050a1b030c0f050703060f0c2007051306141207060c05 63
    0x10011954001c103e2401d0624051015000740c05c2c040300003409014032201c5c0c0c030501004460407144134a000b549860401d072840005c0d0f8101040542c14044203100b0949035956007075140464900020001a440f00141d11481c140030041140c240103620510101c000902c0c1d010615800c00c508035200c205a29100e80100c0b0705120340b00c802010886440d0000d100040b29034040c10000d0710407402e8490103006d20108a50340c00b2501c104401590000c007244815080c4000c0080000c00000310205041010182041c00072210110814104210740d070108401c0014100050240890b403408600c1c11b0b412980c010403809441c1c07404000032030f141c1d01c0c1a0030580640084030b11607034480b5074008a089903040294030723290a03120a07a03080d410242d10405c060b00301c1c170812885802548601d00700310b1920010f03410303203510440b00d141a880b4581c408a400d5403030720300b100d098885503200815020306200a07010031822403410341d401011003031520a201c14000c18902e098038180c6c41c1000307050082d42030142c034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 881739676 1250 881738426 881738441
    0x10c02040b0303270301180b0a090803090307140601060918180b0708070206010b030c030405070e0c07140a0308160504090c09060810030b1b0405040e0c1011120d 71
    0x181840300190301c0c1c07148150301030041044c000da059071002e007000d4501414244c0b280403500d410013511041c1d4a40004003820039960b001000c006000602136001e07600c1010380d40c42075603a03440740d900c040742c2c41c000c002000c0900c491240c040d00151003154074015003e800c52030180500c2c130b0202e4660080903000b0b26240c2c04905a45c0200f01d00ca6080c000c0341c01c007080a9042515500002520070002541c2c490000518034100c540842d4224610760b00c0c0b407903203006034002800803111402040c078009030714801d071032540d409000c1070008141d41c6d000500c0e001032130307402680605000383c101c480d420000c240c020101d564060301c1a000c7d480c42503e0000c0403200c0740300369041001e0315881d0007210021103a01444078030035114241c842610300d88824450b0440031400c0c1c400180450140c40000d40070910070548134440030703518004036080c6510307040041c058800f07001a1000740d51195001c010203241000380d192840c02d950a00740c40c4c45d20a46103040d215047e00175110b03404c002c005401c41107038103194403424 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 881740926 1250 881739676 881739679
    0x12051608040b030f10030302071202030c0301062414030127020a030207021e10030b01020a080d0507201504150f0f0f140402150f0403030f1b050c010c02040b 69
    0x199595110540c41c0d14540040c1c07003a18242a0f13940002c1c0d545100d085d64541038a07090f400401e00d4501d01031848141c00031604040340c26000d0076100d42c215890274046c0704c0140402410019210280440015048000f41e89110400034078180824450144608a0f13064414891241c80e41100321200520007840044c0340000c102e100181d450340c595030580c00303491180d1080301c012528079044031601d212400c6408000d0350050a4010480d411750081d070201d41c0006043c0142c492800c0c4948a80f103094106911005000d80c4800c00c00c81d10550129409105145c103031070310b2100c5400403140542d103140007100d0f4050000d9080115061011008100c1c480401c1e840d001e109100920b1a084080e080e908080e074490741c280003514030350385038601502d00d00112003071001d610b035540c3d074013000b0903007501d1444000900c81c01c03c41602045200b1000340007031802503c61002161aa5000601034244116005580008080d03d9000900003042d48800040c1c2460000da080019000080040c040602881d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 881742176 1250 881740926 881740943
    0x219031b05090d23160f0b0f030a050a0f0204121505010e01060507030201111b060609060607020d0606082b0906050d1508010c09060801050a080a0f15050a1a0409120516 74
    0x400c481c0b0390170f400d0344064800d811104811156110b034078020a00401050005406082c80003601e01c20040d030000e507103d5001d10f07001c1401d8140b00400c0d42241d02c1508002d1250300400385010034844d01c00360012108100c0802000203614140040c0c41c03000040c002c11040250000c0c030f41003454400d400c8a090710400c1c0700c2c81551000b00005181040c141c509140b03e490003100c00080c402d00d000c1196500c41c1c80007802a80c6030911580c2007280002070640d00300c030303000c0e80c0e810b001c151080208800c03450791380c0c000300250044003e4200074801c018038400503010440788800070700c052640b150542c5d81002084901040b00003400c070b0300c07a401c040303150000c1074958a0a030300701400f143d004c0c00510031241d254550003040d0b601c0b1018445141c0450081a140c0d0b07121840000000380005001140b1602540030000b1400f00c404280c1c09480c820b0300d00c0c088082e00d030520406910402240c108007420110782c00c000081d15580c80d183c502030191031768800c0c400c2c0031411087d00c10b00742145068640c1d102ca00c6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 881743426 1250 881742176 881742193
    0x213170a02091e070e0111010e1207030216091d01020c0a06020702040b090901050a0e0a021804030c0b04050c0a35030c0f03041e0602031c0219031b05090d23 69
    0x246502060340b205c500161154070f415508040c18440e0020022038203000c4d10f640d0f0030079200f1114652108000720118410300441e1b444803004104d0300d80c040d246400f808140034810030312815885030701c104510000c0e441081241218440014550503a81d40038001584034581400064010054444a00d81124151080220102041d4030051042080600800c00111060f64540c0e40c0c441031140203400800c00000d903030070317a001240a1503100d482441c00c5411105143e403203070301e481015101152658404400301980e880c10000721000740403c54600d01310f9001c2c0c0d00c0000b50044c0c40044940072801480e8480c10b401ca0148101e92002c0316882c21189002c200d500320b55a00e43c014441c072500c0300402942c203140e001410040104685642d801035007840b40b04880b40c080e5101038841f44180990810000f1841b0480c026505603900300b40d20f0028500124410810964610415072000c1260400c4100c056030340d9003602030f51054200442e9001005c0c0d520385506140084040c140c070601c500e90030b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 881744676 1250 881743426 881743441
    0x140f0309060a0f090206070b1005030708070e01270b01091e0e07090501050a11160e060103051005060a11010905061311010206010308040b03040615090213170a02091e 73
    0x401d94061080c01d0030400c142c2c01600d4903001103c03520b60b00203610810421102020810901520fa0000d0703003000c20b44540c96503a00003d14003600345d44400c946401400c0100f00c05840e104189005281951401c40c40240e0075402200d448056496590815076500801c1d0a5900c200e10610180860300002c02d0449180010480000410312400c2041505180090080e600c2441001c04075075040e10303031908100b00c1e03100940318035403a0b0340100a10310919a0008111150814001c011b0551041c00013031801e00500040580340010031590b6a0340e0f0341c0108000325101c20040f107541030084e140000182d0a0000403038050260150b01911710300c500d0050000c1b8100d001c8000004920501801481060280040e030301d5500c2480050b01d1940207000401c0000c21460007143c0c0b161203060005801c0d684541410510000b5820034080150702003080d0b0001e81c0600d0644016105000d400034041d04120b46035036940c0104407000703008010010210700e000442400ea61352080c0e0300c10381690315140540 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 881745926 1250 881744676 881744683
    0x11031303030207030c0816050f07120210110a120813020303040b0702031203010807050a0e060904141c0f02071d01152303061503100b0912160515040608040201140f0309 74
    0xf40c0552307460040109250a00800007400350071260a01003580b4038010301d80030060f01c0300c085003481040c004801b80e840900301d01444804400c51240c00600350002002200070004a401420000d0300040018203a025a80000a543c11145c060904595815440c03004c03d090026011a240003d4004000840e00a90220f482001e0742d0b030642c0d8510000342c0d19502961800d80980310590070640c40804035000c00e14820f034212094450314120b6498541c0042d80302c4068200d108004000782440c00c240120f560b06000110052481c040a60f1480c0500d01c8080c00740f1106106400503000c4d0000c0f00307220140501d4094002c012040301c0032101c107a040c20b51f0489940111940741c401c2201c02100103599a804042d0b070f008030310580702200108d040c000108200e030310190b0407940c060030a00c0e1f03a12010a00300120700030b0390064511114404e01d0714090000341880503040280021041c0800c2c446540e000f9a030f02c4d840798091820300d42071407072805e04155510600307049400d46000001085401d86000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 881747176 1250 881745926 881745967
    0x150c090a120605071701121110020d1d01051b071d0a060605041422090c050a060306151b1a060f04051302041e090f030311031303030207030c08 63
    0x1030600740695924080c1c00c0b6041d0002d05e00001d626041c440c0184003038640c8055800c695031080a18003c3c05829000081f5000f0b241640c0341c0c01a4000c00011200c03a90203058480880744004070201c01c94004000a0034901070300c034000416404000380e003403042204004842c001c00011400f00d4980302c101030040318110040750016101410520001601842401200c048401c0d1090001e400d0305000c00300700440740390710114080d800902040b040000039074032806580c00d01c17540030b400f4024a403101303215400503290b03ca102411302d800d4007005940c580880194446a291511009090924000200305410401c01030401d04c80b042010a031490070061440c042c03103040b40e03108a406150000c01080d81c900300d5120300803400500e0044010304007034008001c101c0707101041d44d03070300f00e540c040b0003040b55a401410303202030864094680074036030103204200702d03d190101c107507180d131404040711615140e0502e001020940c2c006207c2050610940307066140e680d10900640e6540c0480701c01c600640c000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 881748426 1250 881747176 881747183
    0xa0b0408011103040309060c02010314010909050c033409110a08090a1e02010e151b07030c121a0702010606020c03150a0b1f0c031709150c090a12 64
    0x2c000720901441c54840c19248501d5250359000800c50a03e00110390284d00820101d0500d501c401c03800818054010400d4040c00d5000000180212a414058544105000084c0c0260860301e0522401760b6050b141c1241c440300c4d00750f2840032050500c44050000402e030300200c0d042e840d0107a1030880c0e0700054028030551700240d48240580d121100c90f82d48906818000619070f0030764990101e9030070f4001608100c083d00504002d6850f8203440c011460001000c4100800007100140c8442d110030480441450080c04500814000b82560f9421440c000d0600440041d51b2a0110000c100401c09600403040d80b000c920708041403c2880029000c0c05a0380901d40260180540b240614140000c0946a0280100405d0200e4540310014401070042010030380d00a9900111440050702c1e4094808004155545d8003183c00d40c0d40c100100880d98400440300d00940440600c117088200050200c900c60000341072148540310310a440c2014400d24070750703d401803d81200081d0752822024024082c1b0300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 881749676 1250 881748426 881748431
    0xb041b15020a030e010909020f0d14010e01120618060e07080102131e0b07030c0303150501020303040311031b0f1c080a0c021f050a0e01021c050a0b0a0b040801 70
    0x1110340801044521480c00100168070140c515400710381300c1c40150b245142d06042045106468020007410303a0f01c900031016600b10002130350b04900b0b4031072244e01c110382e42070000c028103541407000c4081092818411a40d64400c00c280d15414041154408404000400c80c421904051458408054504004484554010030b480000c4090b0180215085030087d0301e100e100e41402c113550004120401c080000c1c5002e9621400b0a00034034000041c4581030181d1518103500b2003d180090954840783c03c40e1000300b0001d801049566000001ea94000d84d141c104146240340c94601e00d442c60050460b80c0328000b400400c2080311850100f280070300d000c0e0000c203a81003881c03003500f96100c42c807024540780d001601070350004102800300e500a1083c1c01051050342c0b1001414486d040d021925076811a0b5407964800c248017071810a44100c0034681000c02c000d41c28801c00f8050380541219000113100550f885078005507545013070341d0080d06074003001401701c2640340e2208100009600580540061580b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 881750926 1250 881749676 881749679
    0x2b020f22080c1c08130303021b0402040e0f060d171e041a03181516090b090607020604030204020313030f09030b0a09260903150f060402070f0b041b 65
    0x741c003181c0300c00c421001401c00300480c14012100c0c1201030804100340e602d11002c1c41131600050901c030309130b80114044d60003001da003035006855500407195466014400c510421040103165840e6004070b500c48140812400c06580b044041040d1b40001d0100400300c01c402e40b404d550304c405100242c001170481c1420004600300a250300d82651140340900743c01c202d0100c0081c9002e00e0300034001c41d484644100b5401000d54074000e07292405940d440c20800b4040c5200402c800c0401050780d034035170742c459480c044140518060307026056106079101c15019110026008055440c0d103012a0010340d07026008641ea444c2045003060f00602070913080700040c1130713444100c40c0c040c421503048056075000150807030705846101c012002006820070840e01000f0f83c1030344514030700b810700d0342c5404603510001c450383d250a607008150400301b0b1a4040030420282405004001542800140c1d000d00242d5005950300414104546451041c4800a000d9180401040100510744034208241c4500400003545503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 881752176 1250 881750926 881750939
    0x606091109030c090601050d06080a02102609010b0a030605041a01060f0309060902120706080c040b04091a1519050306031f0b060409061503022b020f22 67
    0x41c030400c1005503141d07000d111002c94500d40181c1582d04002c0506005143c0b51103c003e07102610000d030702401d1aa002078050009604040b44000415505860701c9420300c007078030101c0540c00b246070f00d0042c4071651078000510302c94400d41c045180120010503000c00323583c0e02e00e8034101801080360100d45080f0401c0e2045198104040074906846039501d82941e641e2400d8800c600411510600b0368070030740c54000f10400742c0c0311304005d541011009000703091194240500503000e170002400709209503808100070004084241e0560301554090301c000f180700d0140c01c01184c95085030410465001c5020314140285c0d40b0504000e0240041c2c1514141c81c4e80030081d000e64407808100c41c2c054143e0059403080d1041c0904031087e01da05c003507a0b603002176850008004905203800c030b90800001c181c2e1707540c014040c203124000840071644851030154a415a581c0a040c2142540b181022402e5007030b4107052141d0850787c0549400c500e0004203261585103e400380c900101500810038403c4480d103c2c0030034403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 881753426 1250 881752176 881752211
    0x60f051002030c0a0b04020607020d0503090117270f01110301030c050d0c063f05010906050a0632040302040b0108060105190c0b070807110c1f0203070f060609 70
    0xc0d010080044c00a04c10f4a40b5030401001c001002240c0c4480104400b42c01070303582c04a0782d800d4030700400085031030300010b000140c4a079000c400034120000c00b40301006a400303143e909038048500720210f140c40d203220b031100301860411036078102000741d4286444125844e41c1c0102079412240141140c00700950343c3c10611654854903d00940840c0c00ea003400e22403140250342d420700e52400c00c042d41e5004002c85c80c11101c01600383c10f0701500150940401c1c140d45100e406503a0240ca40c51904100c0c0501d0800003940441151240106210044003603041000c282d80c400e01d1a103491804503401d4110f0300b21601d15591180c0022171080b40303801d14030050b5521840f02e03203201d804186c5805241047c111428190020859800380402c0650290758000850380c4400394002c2d0055120f6030400d046c0914060066220810140c3c0c8640c46880c149500f6503400e55240010006585940b40b2030394081c00880c103500c035090000d4000c440c0f001d4444104072013644014102e42004108000411622031341204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 881754676 1250 881753426 881753437
    0x90a02150712050307020a050a050106050a0f140f1809100f0507020c13020d020f0d050112030206072006070f030f110702060313151a0f090a0504080d060f05100203 72
    0x240603000d68910107618010f20065400c001c0d00c0c0103d0302c0828080d030b212842c0c10b40c0d055040b1080d944502080029007007c0400d400504603a01c805110a41840c0c0c84207419081c62810900c60b2254400111060700c42c000a0070a8141e00111312040d0719080880c47c0c0c0d5040a2100200241c2c54440c501d851001680301c0e05020305850303809411080009401c0100c0c4c804022076508007103500300502c580007a440d1000340641258801600e48910851211038200c4a05a000d441c1407500080340c0b500103640490b1103a40003000303041c070301042e6a00d0300031444400c04001900102d41301e51001d1003c110340002200d04000d02d56038040c000e03c5034074045001943d0700707148034038070141c0700380008801894100f001c0c0d07602070160003103480c0c00181a2a5513020b00c02c143d1081d101c05035529a080710703a0012a660705c500035401d480300031840600a0200e00003c100805181c0140c1d92903020808002c03001089584082a030703e41071081503141d14a550040340300d4414544a401060403242031240040180da0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 881755926 1250 881754676 881754683
    0xb011b02010c11031f0b031504030906031113030f05160501020a060e030903070f090b0603041113060b1c0518060c03070509031005060906040e0c041e05090a021507 72
    0x6591040b2507030b035022503001d80110039506015800c1e02d800c0005030101d04480c0070321240e502280e004907050505040001840240c00d91044941c00c100210b50004920002c490051400241c1c28422504200e414083d200541602240601d000001d2002c45c002c0b052140f8094000d4852108008036822102e11044c82094056086844c0143c0070807a90351054241e040c41000780d07803a141034600041d0401005400c480107494076480d0500280b40c541c0301e94204204240d80301e40c91400d15840d000500320868840d14462803010140300410a01604500020b100f0010200c0d251081c00c2c250307070402c1142d030302c100052619120010b81c2a861161480e01c035103084402030162500c1e0017150b8049030340000c0651007808820804104c403901c0c10400aa50300350101e500181c1410020b040001001c8007410b050721039401c2106181d80c1c00800b00c0d2040312000300b01c500042202c100640d20020315020804901254986010046000e8002c01c2c00c2008031300c02c8524980030b41c100c8980c50058040c240015 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 881757176 1250 881755926 881755937
    0x4080a03031a042705030403120c211e0e15220e06010f02150a05010608060f0f2215031202030f030a0c0c080d0e060105030309091609050909010b011b0201 68
    0x83d0204c14102e2901164060b078180ea24003078503503c071401c96403442d20300c100004035488128010f0010841c8102c41014200c008903c0c40281e111000300310500b054103104030150390030b40440c00b45009101010502e9409041d4251012040481020f150044080d5440802440c1d200800c40e1400d6201e1100381c1d40c4089540000341c90701001140c0d400c04d00d50095003584902c8207500220301c1841500c40c070031106071001050079070528400521402016180318050b03498141d649510341d4403c40d00044000c0f0645100b010034000f005a8198070401020044425241440c48000030001c100c4a03c25280208585144000550b01c100d94902c5082520070b1840c0d000d201203003030340010b03810000c10407141c2c0c5086113204202d5194080254080700ba80100d0598414213105045800e007c10f90040c201103020314140340f28280032a40e80d8100400e0092250100441081ca0a005000e042c0c080c0030050415130681c036100c6443d500074400361404030b01040149480c4440514281c0c50b805003568103a42e203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 881758426 1250 881757176 881757221
    0x411010212040b0c070f24030e0a120311070c0305060f061513031a0610110706050d1d070f0f1a1e18120109170a0504080a03031a04 58
    0x103d603d40c1c12030210300c8a240100000000c3c8140140c44038000741158648000c10387c1c030350001103080c400e105e0090b00140f5003403442d4440a014045003406000e50840d078102a03001414030210000c050081b80302c1071103d004030b2403400740650710031200282d03441a012500c4a0725455071440300c40a04a401c0c960289010750356089408a21014190828003503412281c8161070381c1e142d408040e100003e000c4c03104900b4081140515004103080009401d038107148503d10000c814058880c110f82c000c030002c0c0500040c8548103042c103580480352001806402d00501c0c0501c1745c400c4c0c1c55801a201e540750981c2c0c240d0012a6041c0500c2102048540b0b9900c2420414a2a030b200107a941051040b02801d4170201200407840e01b500c4010015002c000d40f80e065046040c004108085010356403c01c01607141009071000145210807216010b0703e000407003911124400c004031001d10450f04008024003401d0302d520308160701500010700f03009500078900307080b0140d401407000303c845440015100c8001d0604 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 881759676 1250 881758426 881758439
    0x60304030c06060807120b0f070503341709070f03022b080c010c08060d0204110c120d0f140403050d06120503030f0702030703020606060913050708041101021204 71
    0x407a04500c1100003150460742e5450481c140000c0d94802800076200e24240b0041006002059070302205800ca4034409040c141401441c0b170000804000e806028803090f2484500c007050581e00d102e4400703084901d2131a10f8070340200969400041989880c1c07881d000314064801c00314121003a12007a032100d4802034a50b400f0002440c0d401c80345034101020482c1200f180c07803580040e40900500412034250780740d080315505030859451002d00801c016910090020f6a504c180c0c0c13010070345130101d4011640b2049825001c555129030704200318a0303c02c2a843d106100303110310103032010301c25071241001000d003640401c1c400d03a1030115010074080c0000e40002d00081c02080606004e9104000020f60b0035142e503000d200032802490103031203035071000c82086100e40e100c0b80d023903601c407803c0e1001c0d42c109070f01c55030069915203014000612480e000310b06980306846008804048542d502d40601c03160400e04000307081c104050307030103560b010144845015a03500001c1c1d46042c800700c0440d5245094600070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 881760926 1250 881759676 881759687
    0x1050d03020604290901060302030c0f1c050c0919060501050c0303040b1008010608030405150c060103120309080d090c05040c050d0b040f0e031206030a0b0a050403030f0e07031401060506030403 85
    0x24030030b00e80d000e004c088040742c0100a0944510540c0c83c080009001070450042625140c40c0c083c0861003407052030802c0c42c9a4a0300040e10502448103400340e01344000f580b1b412424024002407240c2c100c080c0d0f904100b0302c01c20310011529100824801006400e4980c0011104c0d48140131485540e42c4c41040400c4c0050401d40c5c0c486d0b408459815140035050710380f42d2403401c2d110b00e41d0204516a002150174051464903001805064402c615a01c3c600700d81d840b06a07840f2001403002609014140b400784005238041c0d005007207480d5001c80c01d0b036950360580380000000c1c90320340d8007901d072100c207518042110b0801e442032280c90b080303544440d8100300340c03445250701400400c0803858019865240c81141c1c05054022003030400d640501458503403c0c144007682035940020b2409200303500041c21132001c00d0a28585a4018a0b40f400c04241c50340c030740c01c094000c1c00384a010019020310301031034041488008202d030301c142c0b8807521180d1007020b0031010f19820b0b2030450150561201c02000441c00090055 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 881762176 1250 881760926 881760953
    0x30908030f090a0c121a01150c0614010e18011103060f0310020f030603160b0a030504031107030c080c060711090403021e0705011e0c0305130504110c0601050d03020604 74
    0x4408039503d020301551442600c6165500070451405200f070304a040044440c1921441c4554840c07000a962505440070305160300c0100c6041400000d51601080c0300803a005504c4058000e90303000390f6542c0d1134208850300c2c1c40480c0c00c8194144060001d90346040f06001d514111068400321905645a201c1046802100e00d050664988900d9800c02100303000342c0081c01e004924101403903200e207014400d060502d4400107110100002d000340030f0141c00b4105003a036a0509003440d00041c1540e540c581070300c41c003100b4200d003200c0c2e1080381400003c0001100c038800036611300c03a00303642400c2913040a000385c0c0e00800c00010040ca19006012009041c00303c5200da203d4001d10456402c1c2c4114020018202c00344a404062504511400d00c91940c1080c084810f008c8a440c042c1c0102e420400020a20340f4502802000c20900040090140084c18801c40c0030380030040003084100340000002c14035910202d42c500040c007800c0000256458282c200e242d0f12900b40c0c0182400c1d50300c030ba0384c60340441030300c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 881763426 1250 881762176 881762191
    0xf09090309030a0804060809061303050f041e032a0320090708010501020717031207030239062401020127060e060601050703110f01090c03060c030908030f 68
    0x10710041040796010011084840d00880c025945d9600300b40d0018903000c8024011070613548032006001c1060054901c5e501035030740600d0081d48800c0381b03c101101d54030031a4000600a072019040d26440c412900224003140e2003200710190340c400031204040d00c1240752504d0300325024400c50401c0400c1c40b200124202c50b00700c1d549515481004c50018852000544244c000541960018407070f9580401512010380340054011803584c0d0020b650380e681c0c2c4509407412080c1c2a0203004507009501940544004030f84000002c480e0360368416007000800d00ca090052102d2215a41850340014086542401000501000013044101c0000c0c840c010a84440c09030441d940e0f005904081d11150414682041c1003002504444c07001d410900c0030303180f43c0040700b59a40c100d0400d201e043c0ea00309044075446989420b05d440300301300044481c1c3c1410031040c07140640707500344031032881007028542040d82641c2c8074034420080b8419041c011400c64082c1c42009001c90420804201d403000000d0240303a002d0b50303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 881764676 1250 881763426 881763433
    0xb030706051c11070303180b0105041805070b090109230904030c02060403140115150c03030603050f060610020c090c090609150a110114011a0f0705030a110307020f0909 74
    0xe15150b50811502411020204128003250580c1090341c13501548400d412200340719070300701c0340588500b8030303403041840b917180304568800b40385051004075101108010780100a603001c107990748020016aa1110800d0303400602ca010703000c203c4091413450408290000848440702610041c14018901c0014205805000c2c44040c02ca0040c1c0d9000001d01c0030394415110b80a15902d841c241d6400c0d02e490250520107180c6035082404299100b4000740c105113580e10b060548503009003010f030020003507078001500a02074009604051030001940078010079058170040c4109181c140104d88400500382040da0000d2114082809080301e6000f0f0000f41e8801000b051074400030100085054071101e940c0040307810301160440c00340d90080f654141c2d0000d54802407040312801c4001c0854148140610f5000c80880c4081890400212054411580d582404261349410300d0511382c1d500d0b0415400307038000800c0b00c2c1c0031580c251400320079501a40d5020340001241040c08040141c1d02c00c001f801e003001c0c0e12 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 881765926 1250 881764676 881764717
    0x3270a03050a03050a0909142809050106032609150f030403020d091a030a020307051b0606030615030604020409170d090b06010c0b0a05150907030518010b03070605 72
    0x41d001d0003018195846900c0c4c0d640d40e0b08450780c001e0454806e030303070081011501d0484001c1d040c2188003440d580c00650701c4c1c0035400c00ca50103211281c103100d0303100844c440340b803402844400700141584090b043c3c0303002d41c548400f4152084090052031240501c032910b40c003010b000e0008541072400ca082c0c01d0109814195040c0070160500001c1a0000c407015801a4030451100b0341d0950848940d0300584455803c2510b008148861844148406401c0c0007240e5400000100c50f540300302c05540c0030400c603140d5495002007480c110ba943e880c0980e98540b00e8041c580c08103002c1c6c05080c2101d02004c8001d00070f40401d030b030b170760b004c000c01401c00c07240c10f664402c2100d100c42d102d0004003000b00641303000514000349960850500d0808004020700b03250601150780768410225000030b030420f921505030500411995510384034401c00140d070301611600080c20005108413680c060b00454886d2102650038090003141505140c26030b000d9050254042d040010148500d61040707004010743c00d1041c81c40103481 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 881767176 1250 881765926 881765933
    0x2070e07140c10060602030f07080d090506010b1801030c0807050a18080106030311211b0712050d0e0105090411040b040303020a051c120914060a1d03270a03 69
    0x140d0000071210b410b5000b40c08000c151540a03c915805083d00f071004500f4940c01e12034501c060311030428007808107a408030b01d40480c014181c108080950303100c1305842c190750f5503005010b141e07003082d08003840c600b1403101080055442031007507145290545e40d0780516521079581c291f40d00d911400303601c0100004607101282d0404e05201000080c584c28000144940c60341c01d00901c1c803c88411302c40d519030855020f030290082c8903004d01c880c40c90508051170f80c40003100d1005006004040b90313540c02d0300881800198110380d0b11035158078280134400b5a807092a4958003180d008400302c00c1c4a0214100740004900b50600780d0000515070000b1400600d41501c07401042c1d107580080e0f10442c0140d00a0078020b04102d820710114140c0214107106104105540001404000c070702051607071601e83c2d039001c100c2400360b050304504196200000307880c1c4905140c41080c0280207090034101c410054010303480584100041140c124882070009001d90360f9080041002040e01a0803041d4041106640840070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 881768426 1250 881767176 881767217
    0xc0d0e130929060a080a0803220507080d080114090f0c09030715021c0906050d0b040207110306090304060215040204091410060b18010c0213320702070e07 68
    0x24442d50007000051030060104080010b080d000708955401c5241b40000140c00001500d17001101040c1500440050020301900e10000b03040107002c0f44111900000e49500c0810010b402e02516a81c03e00282e03290b0044810703103280b460754140c014400400165140c00400329030768204001603030356494a641c03c0d0003c0d150a40741d810003c401703610fa1440444841c1c0410110002600d05600f6030840100e0f05006009003003144141001d1010005803e80712041030b07030103125000d0b40140210f444c0c49060030510b5404905000c03050183c8aa20045400801d000080d9811900d05074000c14500b0070585104407005009031089070499210342a03840003951002089072803001c15002071408580c3c003041030382550303104e40c4207041c1048100410448150b6890030f13410044021700f4034860302401031001c500b16152070907103400c25510741841500e2200d0010b00d02246294185600c4203e0f4510003c141001348041da1f0b89005039101003820000a0500525242d2048160901500030310884421040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 881769676 1250 881768426 881768483
    0xa1418041a0d1104180210080604020712080403030c1d1915080a150303090509090c19091a0109031707051e1605280807030302030c0d0e1309 62
    0x1d10300140c2c0d0b510074490130244120302d00010300e00e031402c01002060f00800e002c041180d100d5001c000c250000141b03261100c1c0c040b100e074546e100c03410420040780540c005105100985084000030b00304440340342c100d40f18031088030f0004029888074841c0f1403690304020743d40c90080040e048240000b0b40020f0441c60404220001b0407984d198030303020786800791050084034889514030003080d86801043c0013099002d90040250349050b04e45022644a1401c0d0600e0008511580c0c2d0348071849402c00380c40e00d000c0103070300c3e4100c8000010a10007120721035071a49104071203500160010740510b50800100e0219943c0c111500003d441c5d0500c0c10302941c9640f8202480078016012580c12b040b880244442d081001d4103a80288050300d0916900b8080044c0451821745000c8000d0002000013146e6940703106550b400030521001107502c030594911b8083d44076009520112000c0c00b60a00721004c1d13900410740801018401080001a0715034a0000b0000344038120040d15218268500710b0805c00007445401c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 881770926 1250 881769676 881769683
    0x3070201020a090e01060e0907050706092103060b071e0b0a14010806090d050a020f03040e04030e10021011070204020304230a02010905040905030f0304080a1418041a0d 74
    0x59540d401c0c2c01001e01800499440307100d030840c0f02c80c01045a41e030310054006601e01c08071200009a1103115044440340280e4401404c80c42c40e0050000c20040000802c20000e0001c4201e00001020944107800320348080c816440007600800c042000114221400c0b400400507115040c001c40352501c0307600740b494084640d811810754411850701090740030b00c841130042c100780b0020301a620f0804030032030311800b050309510103100020500151441c002e00100581c405032501310398803150754520250345010b0689013540818000c849055103400c040840e1903101c1c2d042c2d0000c100104405004100400d02c541c5c0c4204a2681402482c00503500c50000310300032405000c071507104208001c840140702e000740c014071100e40d101c5141000180d0704241d81100b2101c08036030001d800700386401c00c5404e510440c51103212515000040004220790031000d0000c42c5015a01d40d1113030100440c01404a21a03000c10b0900103032001c0740c1c901d8501e4560808174451103078100c140d401c50f94043c080341e0105000b00044 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 881772176 1250 881770926 881770931
    0x90806010b180a0620010e010c1e0201110316090b0d1433060706150f0b040b1c1b09180603080901050a02191a130c06030c030e010203070201 62
    0x400c1015441e03180c50721000d41201d414030758a04d00074001d4003c15114500c15080c50040ca07400d000442c0c02c0d40700c0d0380044142c0300203101070a013070f40b00186211401c00552000039103103014004030510501c1850042409411110b1854850344e0300c4000808081c440070b0100302d2003d1001c1b6007000380c10301400e0b1803034100700e011414402c0001c40d101194001030101c540100e030222500780e09035164801440c09048003040e18007000415010034440d20950002405803030604840e004407004007203000089400049140f80295240e001c4401544034501c101c1d242070740240316041c10400210190500300e45850340004640c4442c0d6102c0ca260a0351101d10004548510000c100d102042c10700d2402d042c9807038104200803421a0b0742c04d00c03107001e442d82c2c9a0400038080380320108070740200100581845100180140320318030b841c0002c5403144948100d141d0b007000310041104150103403844c201840e84602a06100ca00b0554110007d1000d40075034010151903d10305518030b5001c1c0b00550103045680d001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 881773426 1250 881772176 881772187
    0x6050a021b012003160c05030601090204140907032d060506030405120a17090106090e010c080726040605010e090307080a0e0a170c011b030801031101090806010b 71
    0x180c207154841040380d00540300c000109200781ea014000301011161000f02e1280d054015510501d940200100000c200d20394032845018014110710500071134604a08072940c1d40c1c1c031854040142c0c0924800e64090180e00002040c03146004441694459107a00d00007a00060b004e0740c003a503404c01e100781c1340101c10301861001c205002901400c07000d04000c0c0c43c12880c6050540c0c40f5070346c8440800c03141c0310810703010540603074440c89610030350300c02c10030610307a8041e50520380380d02ca000704658030840c0c0c035443c6850100000b5100600440c140c08840d034486440035590b040c025039803068110103101b052814824088804020801d90038001c1380600c60014070380d81442c0d080c0440c1d610150030030b20658001e1144000060301e000450318019500c0c03805040b0021841c1c040750000c60b1a41218480d80d4103480b00001c1c01000107115051003100340d0702c942404400d070401040071980494042e00007051032006201003448014a11011241850440b045659984c60242044070a800c200404000040c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 881774676 1250 881773426 881773447
    0xf04030801150c0f080408060a02120f01180f2403110102160311010e0402040b0d0c08090d0507080c0607091502010c09050f03070b180a0b0304390605 66
    0x111a4058601c44030102c0e640c0b8811103010b8120060804001c00d9541d0480102c4200084c9030706440040029904540880c1403184850000c0c1d0090204001100f1000340001e0641c5841034220741210b04262080241040504074000a05007607200800d2803a1a02ca1b2a411003413541041e80a00f10000d018540f402e0842c80c1c044600d040b40d1607500d04540c03001c4103801d004442000c040d4126980104e0f80c3d2a642e0048005850000e00207508a500510200c0c00190310514030f0018010b006050343c040120740d460742016030700c41a054908038041c0d4001503c00c90294020303001411080e01502c0e5040c141041d400c05a850150102c950b0000141c4c5048100441e13003130540c0018107101180003d001010071083c0050008640740310b454441c3c3d0900d405016161010310030b070f0b8090302406010b5503403600b5003070002e00c01c145134a1596020b0808001e0018094541c0426203024940c0003584880001216150f2480c0c150000c0420320022003202d403113007010490140c0a001020907842e016100e401f01d21 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 881775926 1250 881774676 881774687
    0x51207020a2c1005030a1415010315090203100203010b120a0c020303070f0c0b090615010203130b03040804080a03080403031a0307051309061805010b100e01031109090f0403 76
    0x40c84030280703036010682d86422215070807800c550210000030840c0c9075034841400c840e20340c400d940042e0305802804041c0c030600c400d02580b0140c8050201c201c407001c4a000300201a0304409105c0588480e460b2109151481290b42000c1105800101112031004484104070201e034020786c08010702030000a50070f8020090704101a5000b0107a8004004030648030b44041e440c0d103c010703c40c1c0d0402c6402c1c0041020346004146a11015070094640e45d503d29011250680da0300b0165052a240040c1c07094103841ca600c000201c903074003850306803918050351601d07220f03500542010303104903101c03c0103100204050300c0400145004c24080d6840c10303468101818042d003124000c801c2c81e510718200380a44030301900c00185032400c4400c141c8140030310340b000c484503800804124100801307003420035110400e1900d02c1c001b4450610b0054008001c0c4407801c0c4c04000344a02e46442085c003055a40c200c1c519198040c3d17115914446600ca000352409503c00c1c00039195090840700700c1c148003407150500050540c8070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 881777176 1250 881775926 881775929
    0x2040b0f0c0706230306060f13030201080105060a0c0809120d080601122d0f0903020a02030c030f070e10090c20010506061806040e0f01032105030a020a0c051207020a 73
    0x3d0409241240305400141c0c18000c00c044c203004240c80c00070208006881e01d00413a070040d2907060109440e80660122425815010320059001981e55400410030740b0300003040310b04286203501c4400c031a0110366640d503040d402c00324040ba0700a6408201004d4800f0600084001d04c86680d1481c410f8071b4076100240481c07280012080041d4a842014064500a803011000c0c41d100304001d10f00d0f209001c01d41d0030103007d02a4158056030304101e40d0800b055000035040002c0c174402c4045d201100701c5501415901d20200600c4411541701050400543d1200b070115904424103078042d40545031920350000550f00800024000204403070398655001074185e140b0346848641ca0003e01c0141840000a44540a03a803010341c504001000115a903036030301c2048034000c0000d130f030042e512460070300d560412a4809103c10764002640005048010825460806141149848031403c584602c900710700250001d001c80d000f40441070070800045042044442c102c503c50804503583c40445c0d1060180c0c40b81d16 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 881778426 1250 881777176 881777189
    0x406020f060c041206020c0c060415120b0a1502031908070e0d11010e01110a030801230928150513020306090406020705070f0e0709050d0203070b0d02040b0f0c07 71
    0x144814420090404c4200b83c25603040b10015031604c101301d00e014246100305040b240c0c03110001038002001040114505401003030b544801d40ca81451213030780c00c00d50707040890584c0d01c00c0c68141c2c20702050300008001d01c0c0d08540c82c07040702d048c0740d80318021100500c1c2000001002c1201c01d001c10651503486110703941603401c140c8000102d202c5640c0e91805554024810a051003210701d282c0d0016481200d0b03850040024500301d80b0b04010758100a0703c008002c0c000d031442c0200c008040d07610f0900040d2805104680941a0b400b9552034440050078101d0140c00c46e1840c0c0c004031558450000640140b5940051030305420505602c1e00081180380911781c036510079920b00600804c0030560342c000721180c0c8540c00c0341e00540e56440e14906682801c005400c0741885024000021660031100c3c0001407003010140c680900c0151148108a500ca4240350002d40c550b04c240c00511414980502405100c286001c01506081c2c9600210401c0d82141c43c18001c00c400c04104684002c008000e648002d288 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 881779676 1250 881778426 881778451
    0x6091305150612011a0f010c08040608220c05090604090c0e090102120106080105090c040311011d03251505190509090103030e030114090c0d0609080406020f06 70
    0x16680d095125086900701401005000c00001e10a403a440380c0302c040080b42a0007000b008400e84c000c107151511040c04980070703104c500070001d1903500440700c640445402c442001d040c07516049040300d0085d801070104084814806810302c01001d65006402040d100308040700b0a603052005100400034010845481181010700c0c450104420f403450000341c81d100341140c044c80c2e89040d1441d0184c410b45d0000c0302c5900c1d50030000208a588124800e06840080b15030b11110784a00d000e00b8a180141c3c00701811034901c4401c0c0300240c0d806820f6800041e01f1004080000c418220001b0381044103010030b800c40510143c12802d400300b0610410406400b041881440c00c0b000148014030b94010f64044003c00d080031000902024000c01c15610000700040500c1103075070b16482c0007032040f02c203060300300d0107076080191a205070400e0490585c032484045005040d14801001008680030f8489000d0355680e98031400c2d000440c2d03860b4010000760106400800e025032038046064602000140308218209 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 881780926 1250 881779676 881779711
    0xa0f02041413050609030f180f0d03080114030705010e21030a050a08090a0308220503030705070510090827030114071b0c06030905031c0c03110414061c0908030609 72
    0x887d66041d148600d60600004014050f52000b0a001d01101075501c0d5110140d400440101540080400d042c0d03810f0b1107040c00030164450615039503524501891707001c1440d400f82901c1d1410406004034070300c0c0003001e028900010502502d402e550105110000090b000240f10000303d401c0032a0136004031441c030003418000320944004041c80c00103404007011140325540001c5580e0041d200c0c0c80c40fa03400c0025641d5030304004070041d1036a84400c0c01110140100c10784074400c100c00c0d206035801d40d50010800341c0303030048918285002051158500910300d5054490301d1407500c09120391225176510883c2050b060401070406044188140145206104c2c18608840001c0d0207140740320440f800b90078040703000051460902d003580600078607504080401c6a40c0c61008015410007942c242c0c507a03c3c1000340f4254050718580500c1240242d0070f5512455207040c00d1401c0c88401450314880d084d0160910080c0c000004051703541e02030301565107010200074800c0506e041e821050700700c0380d842184841038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 881782176 1250 881780926 881780947
    0xc17090303010504110c07080a0b011d0705030603030c161409070906180518100603180f140a03051c0204140f01030e070303021f020c0a0f0204141305060903 69
    0x80c801401144d02554540c130110384c0d442d000000b40c5080245480582d070300503407a4030505030b44040c410815515030409500024243c091b0b629aa0200410383c451044540d50310f0005440f154400781143e60944400c010008151360188800c04180400c001882d501a04c0d007918100101c40c072500d00d5116404c01c00c00c2c03043e0240c128400108a0b01581040e50f0030760030b01690034100090720b074041d0741c110007105070300103107100c600c00380078426455042d214411589a0204408507203040021001c40c160401c502004121064040e420840c4070b04c80329500060720781c0d02c440c106446503074220f01240f00869a803840b01c40000b82c034050401c45100c114207003454050380e40c442d0450b80044602442210102101603440317504600d80c2d0b03030400c0b0101c6298541e44e03d0b009580741d1074100d8007103001c10170303c0001e58041e40600031594030102c9d403401080c1a01068440c418881e2400c0007c9030f10075030b41c0c110103d000c15000d2030540f0640300401c2c0c44c80c400382981000b81c1010741c010a4010281c00030007600002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 881783426 1250 881782176 881782183
    0x50702010e0d0c06090f113f0307120f110a02060d091b12051e1f06091a01024605152502030d0216060e010c1709 50
    0x398024601030071a106141401c40050910400107400b480d28a103003041406000840500346030020b03101d041c0036030fa01c0c034100e03810701003d0194600303040454112a1015141d10618002303214103078003528a016040e07035079120b07029240580f140218900c0001c2c1e490140d04007001800101c000c01c0900301c050200c0e0700088451240000e40250341e03030f41380000010b01c00c1444c03100d100e083da20300004804036101c0310950382c0034466400c00c89151044150520701010b1441149038070b482940001d150308a810200d03851244001d9041003c21991404002001c0705540210003860000d0351501c090b81031003000081c04c1001001d401012b8a102c0408a005105c1e0f1107a07407016208011420a142050004a6070f009408644043c00e0792141a88502c40051603090b010702401d98a40724070b00002100b00c1911007000d625040c400940c0090121100707034000ca030018603140c82030f202010b60079905030380e64000b204d200c1d586a00c141d0703554200400c0c1c071b103400003d84080301f0000c5129404a180070480d40c0d6030b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 881784676 1250 881783426 881783443
    0x60915200a170709090b1507030302074d0307060e06090d08190c110405040f020306071205010f0f1703040b0412121d01032a02010b0301050702010e 65
    0x4140000c0c01c0321103030788164032150420080d105141903d040c004401400410340d8081c1e03200091400c5502d20403071829100c00c1156045107181a8100061a01c1c03d030000d4005001c2036988141516640c030a0319a040002e41640517106881c1038040d01c01106115101d280a005809a004079009001c03566000030304075046079424600311203031404500c0407410340c1c0600100705401c00c0c4013105c101e04000401000e040c030f5242c00e80020010000d0180205d44202160801500400701070714100306904140d001980d00900441c0ca4454241440c0e011a01d480c50448461000401414100c0f0141020f0300840d8010980b041c1003428240c00c02040031a6107141d8802e1101c0622001c4034400f42100070f0054030028400018007949a80d516003500e00c2282542d1411a81084018040c029203401610040c40d03180c0c0b0500065440710a00005400624443c00004a61603580c101c0c4c280d003040d150740c80c1d03e0420301d950000c54082010024142034440c0900300a00350790400c450310302c0c1d40c040017a0303041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 881785926 1250 881784676 881784731
    0x17040b0a020c011a120303010b0d020304060615050c011a0102030f1c020328050103030c02120a171b0d0c1e0813380a020f0703060915 59
    0x5034a60015600003441074102200c0154204081d0008111981d644c2c40d440000c20b4030f0004141c1e01c8101c00c9501c1e840300b40200d0040c0c0e00180204080b80e0800e6001d142d10502c254000200320b9200c400300712602e140904110001740d00080d042d25411805c1c0580b601d4120390b07000f1002c0100711000080d4603400386901c092012036022450110500c004580000a40200f030000c5590f4108100b0fa6802c450071071030000c400441014420b80b1810a5100d224101c0382c142c0c0d941d029441c155400c00500002d02c0059032034501c20b121304580419801a01c1030340c0000b03104003aa594a40110307080d248001003082440071030300303c08480c440d00ba801c10541c443d5280d01c02d13001c50520907c408e0302c801420520001901c2c0a2020a9a08800c441a0300100c29110043c001e10036241e15850401d0110000495200c01001046145c1110a62082c0a010032150750300584a980e14084803003480c00801d07500c01d0302e0360740c4c0320f50240c414407240f000f411305144154401480440582040940c01007000c07244074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 881787176 1250 881785926 881785943
    0x30831090c090e0c0a0f091404021c05070915020f030a080603070b0a051206030a030207290c060f011e050915041a03010e030406020712020a052d011704 67
    0x203800726482200d11101420781c5450158540c01d109400e01100d80150046001007000d07880e600d00d00900419810084a80300345424040030303c80000c1c0806034111802402c4201c100c2d010620b13104220340074481c031401550340d0f40300d20075260446107140050301046001c20740d00038039103c144031400402160744908850800c403096499050201c0c1c034052259211030801d44011612100304c551010050126811400000c0360741c0c0c0f6900c0805480b4054004000c01692110804221402c1c503422041c04c0007038020f03a0003801141c8080594510740c00155020752a030030071000c111400b44c44d902090b015041000c0200c9a004040c64480d0110700a8082d1a21901c100c6001a00c854422008580c0221000d802400920300e02e50ba804d40d02440321544502c2035080400c000e29414001082c3c80c00c852541d8020690a032400004001d02e0603080c0081c1c0e04204c0551010072142c9030700300c84804680f503000700e00b8540c42483c1501403510281101041c10050802c1e070940e8214125614950002e4214070300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 881788426 1250 881787176 881787191
    0x4110d15020f04180e060114090720070815130312020309030712080601020d020c060a14160b1021080c011b020a0308100e16020a020a03083109 63
    0x70380303000340030f01d51102040e80d01001c158110072000d5044030b1702c00b440c02003c9a26598891442040c18110718074440d40088100d000180100d2040c5a81412004400c0780e40850b100ca84580070b06051040e0440102d07a8030840c031410080e02501202c1d42d0118010140382006201a1340040141c403c10000301d85c0c1c42c0d0044042034007400c05104540c842c5900c0701004071455010ba03000381140d40210342040c0540203060007154407a001180203220020000c10b158074111100509031900e041d91f007aa000d10280034841c09041108441d40c508003640034104080044c508499041d40201440d0042080c0350001c654030083c0c002d074109121340759a07002c005244c4038601d091b5901d0042110103050700910520300e1024100c50b80100700091440d0182c1d45540013651021401c0084441500c121244580aa0001000100702140c80b03050048248152105600c0720340000310718044030b8200303480e11000001e2043d03118075003004000040781540e52542044085000302a0306084034803030000c04540f02e018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 881789676 1250 881788426 881788447
    0x604020d0c05180a05060a0501052d0301030311160b25020d0b0a06060c0b040605042f0f010e0a1a040f080f010b030303010807030f03030204081504110d1502 69
    0x1180c40607100103000041c000000d44020714140f070003a60303c0040c0c2d40c075040103d40c0381e040c944030120650b101a1111303403510303402c1604290350320015000c802a02e681010743c0c0c9601c441010080d8021800303a900e540382129400d50302c03420807490f03c40c0104142c40c5075904000340b500d0402503030241081031b0558140c140d012280300003030200c1c201d4000c0d44842030070300180c01c101400400d140250b10790001088040c2e01e415003614600081200035001040d100e0014001a081d900280ea005118503880596280b04440314801d144414445505492070641050031a040000c040c0384800800d1824190705840d5102041c107178441030091582094402079500d112448000072900145410b0080301a41540c13850069210f4690220031103003542407003044002441c0000c00c1c0c0b4142c92010001d00007043c0303555518801d51321030080807002e064080c080000c07100e02c24003a0240811203404100c0040c40c1c64500142400450040c5510802c006091000030034013a14920104112030900180c2e00e002c185c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 881790926 1250 881789676 881789693
    0x150105060d1d0a0302012003060402030408041205010c0e0d0b0f060303040b07050105100b07122114040218090c010c061104180b0603152e020f100b030604020d 70
    0x204002405145920b00146100d00010101040c5009a00800c544024070b80d13224401e0710700859400a0410070b0010802516040d801160840d21400a90340740c03542c1c80301e809480728408c0c030b415500741e50f440b40080c0c030700d80e000442e10001d08400c803a4015100482c1c0c0e41d00c00710300c0e4050a6495901c503140001411a10108111409030001c84999a207486461403e00d018050403a0b20b40400807c900000540da03400c00c5c151002c19501c042c800c0c01d00d481c00b800c01c890321035005012295000403e05490948000342c42040c1c03815403a00c041e44494603284c014440541102061000342ca0460780c10407030010404146034550940034642410304403c83e0405001504000340500c3c1c3d140d8002500150809880d031680c0e8403554811803d114080e60f000412a050004580c81a00d405c43e540a00647c1c0c68084048501d418000d8806e0348100c100103960320b4000004d4140e0750141e405404d0414800c0b40411031714030f030303901840e200b4401c1c0d01c05d40c0c1c0840d482e1100904003c0c018040c88401c04100310525 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 881792176 1250 881790926 881790941
    0x305120a061e03150603051207060b0a1403010c020c0604092a0201060501091a120a020d05190f02182110021b0c0a0302060313021c02040e150105060d 66
    0x41980c509414500e040340a10b2400d80b00071a81007042c003c01201c01d58032805050101c4c0d8119020b8078041c02d10203116401035000c14001c072001652000c01090380c3c6d450b030300fa54019104101a83c000ca400000515084448495041080d584002002c3d00d041c4e43d000c0c100d40c241c0d102c0c941e0104401c0032401803481c0d074180e01e210314544414a0340d03540d05a250f0550002040f25000d0303807841d04d050703a110b050300c3c00303131212008814032080e007004440080b8003200d80d003642001158800503e4806802c50f164211281555544041c464907240c10048130018001d80c070180c02c3e191011403921145410744180008510461402006181d800c07a4a411040c118910460b201405581c2c8114000000c0310080d40500010000b100f210400c105d407003540040c1400600c0d4002d88100c0c161070860302040b805400c02001c0306120f00f5000580c000503244e10402d500040d03440c50039600316042910401c0140c8441920102ca6907200c2c50004116084d030707034041411074000344c41059942420010310390240900 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 881793426 1250 881792176 881792189
    0x4080102030c0a020706080f04121b051507090807090b06160303061d041208190207080d0605030c030a121b0f140102090a0b0d0221010e10030305120a06 67
    0x88104a101c0b0041001010624883d0703080d610955140e8109564084042d128242080303001d01c002400240f03580c900b54034420903820b080384101c5140544281003030101c001110f081d0454004e0000381950300003130380e170412454145440e04600f0110030654408a034030689401c03039101c007481d030442e4981d00d048616000c050380001001d0903441c14007070041c2c040c5200b4044024036400c100c49080c0f071004109402158800e0040351003003c0ea19080303071240406840c01c1c005003513402038080c84403c144000c008680c4102201610b91554070b0700e4904445e00c0e81c0c0428000c1d04240d901e00071654001c07449000c10742d40400300b40c18503540e0003006c50351310030012510f1010f544010108802d03c250104d0801c5014070864841c940c454074080b5031401c1c0c0c006c0c60001d541194204034140000d00307040c8041c000500380440c005040184810070b505d06122800c1100000c0011a4010700054803021000e65100d0150b280711406146180d074001c005202e03407a80b80d41c1c00502c4e03d01145a940309030308108010500e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 881794676 1250 881793426 881793431
    0x70602030f010608250c030210020a030b03070503010917160c1d06010f0207120206070b070c050f0309010e040e031204030e03070e100302061e07060902100c210203040801 75
    0x1040c0c074020101220038082c40012440322000200f008130124841c54844811041424410701c0d103800542e4250041107040b81907000d640103600b4804114400303403005449030384d00460810b840030141418245984c200d2802641410800f0001c5901104958050107040c542c0c07a41d64008520b180724998000740c00200280c001c41c800244a05031103100300080c6002044980180c0c070b80100654042d400e1844120250300b00a4007082848400301456031501d0001e0300307440c13804c4090340d1a0310814204030760141c042032486401006101c410810801541c0c0d520000710f00d402c09440020785241c0c52040b940e0701c12a140c94103c1d40d22602881500e05010000e030b60a6082e0034a450060301e060a4022081d02030301c510580014000c103900b50300342c080e09540202030b450f2400c4d40c091148a07072044c0c0008007030350205007000101d0000c190041c0704a500603a8001980840c0c2c1c41000000b41200c11000c08000141c1000720100c0c2c3d4644d6510809281d440a240c00b40350104000da00714055a40180341a52 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 881795926 1250 881794676 881794681
    0x307050921011a190e19050f010311010804110607080d0f1a040b090a050a0b0a03051f0b061b07080709200c100b150313030e011b03050f07060203 64
    0x403054000a20b82c09000303815002c0c100040c828050307028078081c4c22504110b0014001c001c2c0d5001030020a401c001d080070f1100e42c0030491240c0d0b000b603413404c1e0380740100210010010400d001a09601304441102403134111814102501c4200e902c44070400c85510807a40041c204080145010403100a010251402e00640444441c1480241f5031070412200f802206010a07055103000c0c45413041070240149000d60340e4503200010b000902009100001003a40c44200c9a138036521340800b2002988500010030200042c1042c07980d1004012030700e40d40072402d040c1007c44554414040e501815490858001c048007480a4903103040d03125445000d0601034601d01240b80c03641034008000d03000c50018240c20314510004503421921523038070b1490403600008030310000d0042c4c0d5002450130000081500c044c065942c0c010aa01b41c4c400c1d034403c0c610030802c982080806812013500c00b02c2150900b414001a4091143c45c48030b0a15840010208200010001842150742d02510360054020004546a1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 881797176 1250 881795926 881795989
    0x305070512060f10030b091006140306040b2e08010f0e100308040b091207080307080d0b030714040c030903080106031e021303030908031c0902040f0e06010609050f0603070509 77
    0x500640c00300700c0c040c06d020030004840500c10310010082318920780c1c0d110ae003c2d252926112851304080c0c2855481a01c03907082d04038640d0740c0307c444a00c943c00d00385e40d80110b890304016a581400c07088881414418404010018054035003032010445045202c946660354901079081c034412141d80000307000e10004200401e141c2071b80c0e8040c10002c40c00740c440f45400e036800030000745da40301c291081281c503a1080292200059500015080020301070901080300002d84c40085e003000c031070342c0128200000105d4010400c0c076041c090a0300c00d0314141020801103c403510b000b0036807003050040c0300c02e0544410140d038000c250000700d0b00394010001d208540b19018a40b00c5e100705406407000754005040c400c0d000c07640c07500100071600c5e031703240b5541010703203e40100c40c0480103072241e421b081c3da01c40e688140c0303002c5051441c080d014009164030040d26856062400180801080b60043c40c061090900101801e807203160490b900f043d01410050346884040e070000c0c0010249010154441c0b14089065048 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 881798426 1250 881797176 881797181
    0x402090d0b01080712050706030b01050f1206011e0c11010c06110403050706021222080109030c14070803031302030109120810091a1201390305070512060f1003 70
    0x16200300d1000e6801465950032000171403884600041e0441d00944410401a030081e800b915079580c040c105a414503214415441040d0004a03500a240c40b00c8030406c800c540e07100c0c0044100054080c1f8804403400f19841c01401d9184011008110485040140c10142e000342c1028984035405070003802400782c5030503440b006422501c01143d140c0310301c00020134030a0010614904840782154000c5c03c000d6060824012400e0806602d118201d120001003140ca03020300622060f1400303510f42000d00a203070b140550700801c21000d2041550403890003801804408804c5a4020380d244525012002c921300009006113040360b0300a048250b079030039900000750032008061241100380480300145076500018000e40b0607a004410b0b11003e09403000483d031418154611a008050000207281c816118440030034115800320b2002d040126120300d11240402103605420450615082c03142d8180003601030054042d2051603100300203040005a1586c44020041010788402007814004440c1260007500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 881799676 1250 881798426 881798429
    0x10905130218102102040902040b0703020c0a06020705090c1605060a0e06040c05190b0a0c11042307031e09050f0616030e07090606050c2808090402090d0b01 69
    0x41c1c1e030112088800700d407516241403c440030701c940324882d581e40442001007148105241070003240d5803e001c045001c0c03000d480580094012080403556134401820080d00d080100001d483c4191202c1000b4805030361301180d854200c640981d86401c80707032203113000c442c403d00496011411100b40e2800c00703018003c0002d0314900510b00c00b07004120a40054071156198032045030701070190b00c6101d90801131820480d9000d0362600c002c0c01445219601c070103402c100c0d0fa0202c205940080c0d0401c20282c14401d681c503041d004000b04071820004c9180c0c0e05414078200000c10080260382c1000700006034054005d4100042840e0f4040c440c00011030480703044c030000d00c90a40141c401d4070540710600c080741e000241281c0583c8803c810a068450800402c5019190541c0962168000c038000021084c4590040e1000f4049036111183c0b115600f541c00c0b0302d427604407503e81c034074402c4203003104034030211101446260941083d1000d5a8044407008070300684280102550401d204850074414410690031050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 881800926 1250 881799676 881799697
    0x2070b011e08030a11030d050103030203031e01050d02060906130303030213090504021813080d05070f05041a0706110d0603050f03070201050910020a02180a1b08150109051302 77
    0x200445416120100380e82050051058943c0704110001c92180216000c58211403010200d0b46020341d141d0107101034900a0780204c0142c0d02c080309120150742e407910120f100316030706661191258507140c0007441d404201d61029000e00c5e00040c2c20030b01d903251042250520020b881e518040141d9a180044c001d41c060b10400b040451546804030b45041c6902400c0e00641e002803070072500302050580c80721101c40141917560004c80c50500c85c3c1c00510302001400042c0c072201030000781d5151010340079201075502c008020801008010612041c200c050204a494500d0004030352100400c0c034005d8010146e03c426941c0c1d40501043d5494800225040002900d1007401a220403100b030080260342d0380102c210084c0443c405101003941d906103c41040031000c4184126014000e80c1c0d008943d4004025a203c81c8103003129081000940040c01140c0d5402d56403501e0307041d034224145005000e4803000d08001403003240000844601c1e84070729002e002901d00103004d01390b5000c05c2002c0000a5000c012544c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 881802176 1250 881800926 881800949
    0xd0e0102011506020d0809100c0c0506070905030616030209040603050a0303060b13030f0f06180c060516110109030c141507080f030415090b0919050705130f02070b01 73
    0x540c07408a0082e49000c455a0350010803c071084c417101664100c1c0010310f07099082c0700c1d0313121107150a0030034040e6503290036450715607000d88480c1c1c0c104141007800c020310344018080300c00300411964400290781503204c50540201c060030341c04090214040d1040c618201ea001e800d00784c1c04001e00101003805540284244c404000382586c0b0000080c0c18000c403014190f003850078070810004940b514410000322480740f00d07440000c03041e40c1d880100b225041d0441000700840c044001c0100a01c615542c40a00312a0905a0500c6140c000750f0151544503c80100305800101d4080201d90240e40c0700c10165030301204400105854030032150703403030f000910310611a071240b5190702190381e154400c541c841504203801e54586402402208541d5001501c00c444241c1c0b2a060b104d291440c6100390300c0c0c080d10800c514070183c18000030041c03500c00801d0301c0780c2e0040800c0f160400010030000c1c2c00812943c041c4c0c5d0303c0c1d02d080070009500c001801c252160b0100d050000440c04104010024024103880110450 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 881803426 1250 881802176 881802191
    0x4060e010c0905130b010509150c010609140a0218040e011401091509020c0a030f09030602030a050f06030c090708060d0606080d0908030406211e0e0f030702151b0d0e010201 76
    0x24098481c40170006000c254104075540c502d081034040160864007406030f280c5005403925010303084480c00e5019201c40c40e941c03a540400311a07410130880d00411010025030600010f4100402070300c6107007000c60310607651060f0660006c030302034002e400d4441d50015481c9482d0780d515100005808240458259a0b02c46500461100b07114400d031100d1042d00e80080a05d0b000300c0d80d00b960b201c20760300100b005101001d200000085d11038001544280750a8002046906203c0a81e969107003000c1c000328801e4101d02d13a001100e445040509500031014039107103a207070b00e035140401d4803000006400740c00c03a414045c020501510010350090f040c170140d9190ba621950302c0a4140e100e0081d07015402c0003401c1d50207490a02c85112000740c47d4441c180e840014640c844688124102110540107590786450344002c4120f55000d01408007200100ba02561801100c0e600280d2006603440c40d0754549800070800c48a1034070407a040707100c0030544504844c003418000b10b01800400081d5002401582442e52 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 881804676 1250 881803426 881803459
    0xf04020102281203020c060114030d0c0b0406050c091512070801030b0c3f2505032d100501020a080d02090d1b03020f03010606050405060304060e010c0905 68
    0x180c4081c02c40401542a0007188140c0e14160301d00c0c54101d0600405800703014040b030f1b81d10180141802000082800c10a000001040c5810141c541c080c1e4004d018a48926002143c3d01d00c0005038440c1c0c8c01000001d8503a5000000c031514000d0000481e04003d020810709071141c42c801c010a0003401005c046007a559540c41e04540e000000d000c014800505070001c5150741e00c00c00c002e441918010740e81c0301542038101c600d43e003a0152030258201d10020829444035545039045182d500103900700d80c802804c0c1d84940d0041080b001840c100030401000200040302060700040c5100805507900c0030101620180401c940440420f4901c0703421814010b400241a40c0006100108240d01c0040c0500323080b504034446009400c043e03200e9420580700060500090441c01c1a01100101c60040d141d0140c203500520850340c1e180401030380640c0c900a000d101c1250030409072412140116101550380d03540b440d14034090070b4030314a4401c0c3c035801d003070105900c0354204420300241c41064801b00400901c440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 881805926 1250 881804676 881804713
    0x37091b092c01062309030309060703090e0a0f0e0c01020706050d06050636090103020f18040305040f0506041404020f0d0c1707020328110616030e0d0203040e1308030f04020102 77
    0x341b64103a0003041075182138280080544110f500a00b482001d056451181d40000c680031280c03182110794841c5e03c0204c030590380c440e20f040c13141c1c850010540a10f000b0000703582c50640d4064801808804109072000c84c42a030012b202501000c0d055a8542090300c9500d100c401c0c0380076483c2c4400c1a408405d01001c0c02c0721980000000c00144001d0090346540c0034000000c28010b82c00b078000c2d10310103c6c41c0301c5801482c03c0718000c0384039544081d0b170740d0728094082140c4622908a02d12a50301000104159007441103450310842040b01c005a031414648450b0781c2d40c0c800c2d007400208040c10155000340b0550000d01c000e206180f14a080a140d98030240203c0e200d109010024181c1214284054108142e0064080c4401c0172420f05902e40c540c050f40c0640fa05104444000300c04250490b01c413201e40e4103000306a103440061000340304942900382c01030f48034019405020380101b807607000200b00c985251541c469640d0410640d41e81c0b800c11030b5900341d47d10422903040e4050300c00c903600c0c1115850840d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 881807176 1250 881805926 881805937
    0xf0a0e180109020a03060e0906011a09031b040605120606010f030b0303070f05101d21031602011b0e18130237091b092c010623 56
    0x2030141141a800d0910020007500810002070030590350f035001080d02c0c415500c2c100d02590400000305000e41c50441125032440150000e040000303820300c800d1026807000112110a0a12942c0003c01c00f400c40000c0b500810b01f40c0d01c1183d01c07a0303085c2c0c40703071850420214540f40031705020390300c260b4200720000094041e61014484590554402c010480225000c526800b4089200714103a031100348289230321105860444074411444d6070580006044202c0800075220000d804901c407520782c8c0d40200142243e400018081c8414075145008140e01c18400e40c0f140c01e241c800d070108070450086042008118200c4904000d001c0c0c0d003c100b17440000030f030701d180c0310744140b9203030850701300b501620340c244101d6182194a02c1100d40416400c4027140a10144507111080341c01da5024849140c02d5040080cad88040c00035049505050750315101050f84001c4403c00d6582040c100300300343c1c0100f42c803007580603c4002002174151403d000440c603107034002c448091030900301c0c910002007156464510f4052046 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 881808426 1250 881807176 881807209
    0xf05011b090302041509020d0c271a1309060e060118090915060608041e020a030f0305070c08030c101407110703080406020a060606320c030f0a0e 64
    0x14150400051910360005d606800a0161a140742580c51043c40c099820160fa1a1b61241e1241c502000321984510070203500d2010600c03004d51203002d61070549094a281c0610596038425040c40c40555100d88222024106403100c6500450340d0303400f418009007454050040007429981c04034407075620894016032035035219a0b000b400380d8070b0800785000804618030101c407040a04420303580a0206885484010452521172202c3ca10f4945003100790780c52080040d0102d0782000070481c0142c0c0b070300d004000c1039982c00103548080d01001c0c00c0c00d41e201e000341140100307114801000071030b0071070740400a4583c50704172000700c86000b003040c40904150381200110200802b20701c0e0004480340c3c460781c9400d18070060003050f1030a154498444080b13035401500b0440241c1d02011108041001c0c621491005020381c0c0340010114003602c1840c1c040543c03644500f4501c0381d1000086c400103403490102d4a40014050071a596002001d6001a55422440709800425040030b1100c4403814800d1111090440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 881809676 1250 881808426 881808437
    0x200406060f140c07080f0109020906010810030204090213150303020705010f021504020103180305030618010302090708060f0a17152205030702041a030f07080a030e1c0f05011b 77
    0x40b450700800300707400141d24070240f0f02c9076040000300001c0c10710401c9100304441001107000c0c1403500500c010490f014283c0fa0401c0f0b081f400700007007102c40303044000a0f40c2d8100d0300400d61900234000905000221049151074030b16251054401e0981c030101403003160701c2502600c5050b40d860005440800d071040700300b005a004403440f4054141140d10547d409841410001070003001d00ca00400210f00240702103021a40c0003041c01120300e0900c2c4516003490240c81c0ca0320305503065a012a650380f0b40a810300c2c041c0b1190f0404107002d40e07038a11203c108881c002d0700082d0300c0e40e5181c1e0311039584101c104044040f805807074403002a10f412004243c0c0304042e03003070408401c40140c2145500700e41600500741d92500060050320010399803070207140e840c15058040400c419130b20b034003050305105400101e4a41c07584541401c100004c00030480301029600360038810f08035900000030071103640300120030300c1031048900200d404212800c0c441b1010030b07001e4002000001c02250802140402440c1071401066 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 881810926 1250 881809676 881809697
    0x609060c131a04080706090602070807061233061106040302060f0702010f0501140f01020601080c0112022a1902010206190b130c0e0f150304050703200406060f 70
    0x3040c020032a041003042d4101a89015035031800141000c9170b54112a001800f00c0008100c030950402c0801d0180001c4406045405e240c013001030071001c20b0300300714814140c4508500c100910052403c410840c0446100c11400741805034400110b07066001e8080842e0301e00e20740880c0319400290251003a64036030018400341c5c03111030083c2000380000303040d03500f1507403100e03200703051440b80c0c1c040c090081800b011540704d0340180c40b0410040b986800030160440d445a80104140e9a000690243c0751100703084c05044010038036078a07000307886030252000b10300c40112049007000c4400c444160860100c0f10640e102812404804e4820141c4054082e0040c1e0200001c1494143c24841131021450075410000c1c2083c0d002c004203810b2511740c45000d60940d51104805189500b203c00140e04603412140390540004007000212140441d80984c04a000044001001c1003c00c000034800f442d040115107a0080c007d841803000c0c21a400807041c011802d0100008015005010221030828580c0b1800b0000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 881812176 1250 881810926 881810939
    0x1f02040803031810060305011b030c09230a03050a0c050a030309050103110409090b0609011d01030f080903030301290405061206011e02010f060609050312160b090609060c13 76
    0x1020190039043e14003403084030309503008082c803506000f54464000400c0751a107109821a8462549003000c05140c149117501e00b1456200c6400d106640e0948000b594024032800321040b120301c07803a82c298010764118008400d220b0300041362030840703104c7d800455805442e0018400111074070b100045c080354a0400038081c0b580203400009400050110a0b800c0c00c1e80c41100030309550000784142d4480307120506005a80c200450300380d000d025140c80c46403201c651901c480010300b10501c400742c0000711185038101000206400c80c1c00d5a400102181e8482d40c4a564280014180b107032003c400264a0300c080c040703888040150340c01c94400400450170300d084140402c0351501c000f014241040035071101d80c038100802d154802403404550340005554107a094096040701d045412007018002c40701820046554005203051842c13241d199040d8035940c00c03101c1c10038030351809080286000364902c03c0108510000440c1440380340c01c54200c419548a03840c506803148100c0700000c54101741e1400a2001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 881813426 1250 881812176 881812201
    0x30207020d061109010e0406120b090a12021c0806010905060d0b06160201180b0a110705031c17100506090f13230c030123040c021f0204080303 63
    0x450300242201e40112001e50b03400c0102d5400c20700b0707a40341920101d002d00c0785582c4024401c22601d01900c0800c14103081c64a483c40c0414800c42c01481c0b4052100001c00e0f8110038031072119041d61200d00d18900c0c12040801070344644801d022003a42914044030080150f10a150041c0107039011b071102c0744403500304004d200c4140d001d005a8800343c0e4580381c020b090b5860b08002071007581c0e20b10400080401c00c1e0b1000612500b19020300311080d0000c0e48041c4200f075a039104452400c910340c10034200824a8084560400754940c1c802d0383c1c18004c680d05400105400543c0c80301980d89583c8002504418085e000c2c0308100079501c14903445e00505081c460760805400800c2d54100003000410408480030001e600c242d0041184a00103450740d8000040e030505440541d81e140741a01e241c1313040d250030604c000c0c2c940414412a80100403a0540032880048261206040c0e030000e0004c0c8030030032410780081d5844880d15090000d9035180c2109213140c00c403070300c241e5050700c5051001d146191603000b941d680 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 881814676 1250 881813426 881813437
    0x1501050702010c12180906210c0f061808010515100207030b04140c0a03050c1309050f0105160504030206180f090f0420180702210310140d030302 64
    0x500445041d41400324080d40c442c603400582960700e0500c1e001c424170010540030f600e139000b0005603080000038030440048068803200d03821a208140303001020f03400c001c43e90150750b0340502d0302441802e0f0007007001c035407100c00d0003203d01a08606031348180d0354150203800c8a104945117185d244641c034500c0d1061030302ca0740c2c9000c0e44c0940d1040700e03169600ea8580e06024032090310100c0e11013048000401e04980203101700c0b1407400b42180c2d10cd08082c5903403555a103405c030140c0894800c0ca0140c14840042c0150f90000c89016001421102c3c2490300c000710a000b8001502d120b12040b0ba10001c90701d4140c810b208450950f030b4040d00042c2030070340030801c840d1649420b00b9400c0d48290400417085064540c020b11502c2600e414112001c01d040c0707410620340c0c00c43e05541030609000c10550540c019141c0030b001c10020742d4200c01e03a0240f6941c1e180b00702e040800140118070031581c0c030502d03070f0707411041080514002c01105000d00c18043e40c0751120142c41d070042101540001850f83d42002080c042e41c0a0701 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 881815926 1250 881814676 881814679
    0x60415050f1011010f09170406090603020708070b010b0a02060907050f040e250905010f050916020f01050c1201050306010f0e070918091e1502160203032109061501050702 75
    0x2d50303d0446200082c25292880c4914000603030360681d000a11804c8642c003042002d80640303207444c090400500805610041c000c40017819000a80e120411010701d048a0340c81d600302c4800300055031070b00a80c1c00207030f201007101c1005206200c041203a05c60080740503000c40e4402010401c44188010611000e0b00c2524400316041c015440034414491005096041c850210034002c0911420304800030f080761010b0f00f2042c040d180c0d0b02d5051280342c441030062504498409071107000203680340c42c101c0c60140002d2201d6030950a0105119240b4681c1c4064004181449600480c9070303210801d241d504c5000b4810105203071401350040010028040f20309801074100d10f8031003081d80e1200d03804846880c280400c0700711309907039140030320501202c10400c4c0c480200c101410440c9280da41c0b12905415409245d641392a903000820408040442c0320810341d480d400703010750b81c0302e4050744980e92510750600e0300c000d0030240b894005205001e010a90310305c40c1155000c1407090f07030111001125150411001203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 881817176 1250 881815926 881815937
    0xc030a27030f1205060d0f15090c0f05030c0612071103040f170a020f0609300607021906150504020d0c020115061202031e090105060415050f10 63
    0x1242a4800e00c0004a54a03000c0d8640c00c8180d080300000400b00d242410f0703503100007441c10702800a26a15110300911403504484020784c58580d078100021344026080e000b410107490103844030104412007025000f05c0c1c91500c0c001207003030780e03c8060685415003000d0943d0700640030010070000880320070000d5017080b101d240c588404641034140303916650141e04036500c10750741a001008041c40c100e4030302e0490320003080a000340051690128000b46003405500c0d1283c00c1c0418099400d494000d505414100759804001480003680404524900074241c028403e00801e0001680c0e0b900009d142429500484228800a070302e0361185801081c901c0e0041d810000701c40350006a41e035036800030744922039040400250020780c420010782140e280040450500c0880502009401d4014901c01c0c056182a100565282e0380ca5401940c46030503000e909050006c807030b003440030f00e42e01540032a1042d50305840410803e1030f0070002d0b2540729036502c2020b521904016440d8407500b40140c1440d074540007803c2c003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 881818426 1250 881817176 881817221
    0x122004170c060409020d0c031a2803061e090201050403110406050909030307020f0f1e0106080a08030403021b062a01180c0909080306101202041503140c030a 69
    0x81c00c281c3c0182d21184c2003e40120b01d1489600b018400c0c808145070505080041c208003102c8408007070103c1c82c2c924812200d201d1180d21144a203403010382402000030340c00ea0342603141d240050041c80a462441c0301d002095509088180f0b1030310804461640503101c40d400c151441d55040d0030300c02c0c0d805040d81c00540318540091152151102e00b802282100050b60304c03880e10050080c038090714015220310550268611012000c000720300c0c442d1500040401400c1a944008220302400c09984000312600c202e800e00010300c0080400b641c0aa03100b9800c3d204c1440d541c01d060300038040e40f84451607109804128100030320b176813041140b44000320303019450360f803c080c0044682180c0c455401c8a661000342000c450800203819044001341c00411402c02c07409a650322102d40d9804002c04030f03800340c0741c604040000980590862400122405001c0d56201e03141d00a140b00c40300043d4003103002c20300300080503500810b8480f04038850044040c42030706594540d0386481c041d0103050305070501035610701213 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 881819676 1250 881818426 881818429
    0xf1518100606030e061e0c1e1b0f0a11040b31110310052e0906031118010e120609010204240c020603071707122004170c 53
    0x40100034480741c1c5001800304d90100205040400041c9682007921084002c8850200803402c19604544800145030711120341e543d8450014000484020402c100030070301d2562415001c1e0100c0f030001e140c8041e03412000d800d01005030380318515a0300a0405aa401c0c0a01903800c00d0b81c8a800320180080403003a00d400300c0a18010003c10100703c051112100d03e4000c00040c04a000340006008200c40b07043c0f03181f406030491103c003c19401018451a091500300b0410b4004106009800c1c201044054036006c0c1c59801500074000c521598010904041300c0d81a515a220155068010036580e000d14480ba03060044561104040704a0760200160302001030408080120600c01d40b0000e00041e40c83d41802d0b030082040d805416100c9241002c9019059081d134060001c03c0055030542e0701c41d807642c40d426400c1e00d2112520003c841d094030900d040106451380310b4500f280e1840005001c00826048038684482c10060080214920900700803c2120b000074542100f032145841042d5a40c2d400d82e4030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 881820926 1250 881819676 881819681
    0x4051c031b090806060f01200309120606040b220e03160510062903070c1e12140a080a0605030102070b010f092003040c050916020f151810 61
    0x5507000004124100c203004111003040465080b280444440320500c5006000a064124440300c880302e03441503600a10901d0405c0054808451000b400380c4041481078402c580d54031005c81d04c162046040100380030381403c00d5920a10414180c1030b0804402c1100d40c0381c480580801c0700b0540d080c3c0b2082000c4020a8003d503c20154544100080e249034604a801d400943c0c81907000a083c441000b841c0da0b100100415240240c10429040640c880e80c59800980c0e99002c070410140031440c00010340c804a410416140a11520400e4801b84540d1801c000720741100220b040e00391800e40411110031954001c90000d80c1c0495130000102d046911900803c2c04d9030005401100c101008000611400d04505c0780300380034040c1c60030108005c6144a00103c8005105e550320314800c000080890140800084040701400300506105031030b090603000d0000c40103c804541005008410310700181e150040391200c03c10408001c081d4443d207070103c80c620900711208201b40f40b803050403181c03080c1c8582030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 881822176 1250 881820926 881820971
    0x12080601021510030611090604171002030f092103180703060f0213080d0903080d0e0109030509030d051e0a170c0711060901121802120c0a0e04051c03 66
    0x4190303c8154900e14a000705c183d46450035001943c2a0521022000791904001ea03012104c50001c003140580c428002c250400c010410440e4160b8000020800d41036031445034503004200c1441180e56003605000002d01c0c044d580d40c445408824104042000402c0c00003a0004d2060010700f074a003250ba6039a00c0008860400702c5040c1e13900c5d000f0801f1503207001403040c201c0082480402410f2156000c100091044400f40402031042401184400c082032a541c081c050004908000300301e0300c0158140034002390000c080c020300c2071241c03e4000d6202442082516102250300f420004c8440c5040c1036404603800c000505000c002c80304036140c0c04445c1f84461507000f030500703207130b44c540c0d030203503410808800c92904501c94080c0304c0c1003040c1c80d80c0d640c0c054070039103035090154000600350190f5841c00a140b402c483c2d0280d400800007440c0074511001182042030b144080f100c50030020307034822507425090021140a4559040403082d2255a03003580c06541415a05103170001c2e004070303d400600421144e2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 881823426 1250 881822176 881822191
    0x51806040c050907020d0c060507110a06052208120403020c0a06180905010b090409081b0309090a0b03030a0305040615031203060f0f0302011b0c030818010c120806010215 75
    0x20321000c00880c2410008213412000c40e1020381441c0810300f02c054000c030243c07a030090482c0c0e515000100054810240c2e514582041d400741e079005c0c0803504100011700000d41da000c078030003c03aa08a01c0c0003a0703408143c5064903407020000c0d00f040c4c00556000c052f1800180140d00703600a01540101c0b80e0b0310803074501c000d000c058441c03a000c041003102c82200b80d4503503004a940c4a1078900144148085030040d00c5800b48215030202c2d40702c085140604c031a005691040b1901a504000b41d02c1020010010300300724507040d100d200c9180e0b286071141080d11113501866400d81c00410804000e1440380d08010f40c0f02d07018000c00318070073300994001e0582075030b80c0d84182c0e0180c11810742114100c1e81409060018002c2e400001c26035401d01c40e07e5001b000d078612009040c049140c00460549000649041a00d40c000c00504c5201d80c0c0c904101031242e201c0f0140c0034950380c0889034000c03c1d60007189014131890700441c2c503124540b0071803070541c0d1510000e8041c50551248861407012548072414040c4900d02 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 881824676 1250 881823426 881823443
    0x1404120807140a0209040f110312041a090a15050918010302030105180d05210114030f1c0503130506070f0306090902060f0a0908010c1701091503020405180604 70
    0x10030304164000d0726051000700b02c40e800c644101c1015136903000d1500d4101e03421200300ca409040034507116068040c001a201e80601076095205001300300034025100310355030005c403a403100511038940b011502c6241822540108001c0f03043c8181080041022004082410318a18041c202d80c000f50003540402502c290000d96000180704504080c0105600120140507074600d114441080c180c6074104200220204400482d178201c0c01c244181001d01480780803503290310302e0350711024403000c40030480400324000d2040610801480c1000240345450040d5440d000d000302c850440112030f0780d403020b0300d940c140001c0041354074046041403140502409c10364840c80c1a1071a295009419103000b40d109643c0945003c070710a000da2180000c0b203019904851420360346089102c020360f101c02d165000320245602c1e18031401c0d44960040b01d043c0001c4030744217448200d6a603031900d143c103a49055138441012b4030403400030401030910303402254001c24100a0400c0400c16040c800780742500c100c80a40b41d119 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 881825926 1250 881824676 881824687
    0x507060905062706070e03010f02032511190c03060212010509160203090904050a29010e010501051905040503012f09011704060912080a05060406060c0314041208 71
    0x10500d83c0f55045002480401d0710008a19901c0f40e40300e6000070a00020f0040e1400e503280550f5080d4050584007891000071500c80c00c0c0b00b945121509092101e80804503013000000c0d1070345008641d44085207071424010305607080000128001035800d00710890701d07200b007031034040009a0a030000d001160480007100307485601d040c0070440d100002805c01707900000d042080020496020080319000001507440402ca030b2101d00d005468183c7c8413001814414a08a0706c0d103400c1142c052260384812021490026a62034200240c00301d0300a201390741c0459010083c14822a04d07007180b1810169140c200f46090950740c101081c20741d0700000e40b595801014400c150100e9040101c040380003041c0e80102410075581c80d0001e00040c800e4450150280d00328000502084010740050000301c2d0301c0482d0440310000d003140a0719200e800e0b1a0428110300b030000141d0036040602c141c2c4111901c907503804c42103140c1c5880c1600c0c0240c0c0c2c0000c1c0241d8440420021601204114202c24410f1044012030303680c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 881827176 1250 881825926 881825941
    0x60501083906120a06051203070807140f0303070e0126070c06020d0b0406231e0a032003120a0f0512090a050d0e060714010b040e010e0c0307030f060c050706090506 72
    0x320106d0f001039116210000c0b040310110303000410707910802c0e48145401e41d100a02c1c01d082c00d5912009400014921881c03205015012001c000f0314055010354440c211b607101450010b42d48109108000030b90041d041c1d4006070344510840b43c040d00f117030076030038905810707032141c2c41e240f0580e440050340304030075a200c651420f801e0070544611402000d030b40400d089560031482c518044104420b6402d88250307944034030420b06050a400390844011b00800001e141c0b5968500580c8040d40703040d01c0c5071181c4030414010840e00f40030850902e5070102c031603200e02d80000b4050995503148a2540300c01001420b10000508420400d00c0d01e001d0303480b640003000350450700d01c1c01c1841c11485980b400104414200030040d6910744a09a40f440c1d6406900d500c8218288a4154010000350040780e601604240c8401c0340e004041d441480400105030555200e060503e00b499610303546844028501e11104003810b0114196500032801d540321460403a10740070a036140c1405030764a0120680d00d40e003040b010f2050380d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 881828426 1250 881827176 881827181
    0x28020d02061605030403171005090f090c060c010b190939030b040f090b0106030b09060f030a0c08030c070906120b090c0a12060501083906120a 63
    0x9100401051030020414940810032a03042010301c00044046400c15005143e02032032421000c00b144c4540c40c003410503101230300d614483c21340a8000e0f1404600180242e10226124954000051a0320154002804500d900159030080255a620452152030380d0f802c0945111102e100015030401d428129a40d00b1540c800707261140e0301c028820030001010041001c108542c80300121000d102c40450401e4004e01410100c0740d0303001d8584880c41050207041d61080c16054011520f02d2080e82e00c40b0425000c84600b4038929911881483c0080c00e240b1348038845141c0c02c240501070350080c540507a07030080860060380003d03132140c2001c20001340c03c0408011401c020640c030103003441040e00e000d6903c0d8601f0001c9002400c42c01001c0c0000c2e07003640c02003004060450010b011980d115a030f0b030700a032042010f01d40c01107400d58140300c0001040750700001d41d20140390000c61282d41700b58150110349512801503d403070300f4100c990080c0707036035640c1c4080c041d0241c3c5c4039060780d0301a1407404080a004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 881829676 1250 881828426 881828443
    0x216030c0501240308280f0f030612060905010e0105040524010501050403060903140f0406090e0423010b0d06020714070e01091116050a051e031c022802 67
    0x5182403080311980403d40749010081100d402001c225503c01207103608580d25000b043c075041c110079000b140c0846039544403c007150300085c00c1da252030349450ba5803812402d0324010710035644049000749501001c54255030044944903c02c000009400080215083c20b46808490984098000c20300c1c40c110035041d00804401e000042d20310000c071350704000020300140141e01010741090350315030022081502805001c0741d01d2882070300036512000d000381085090b0344540600e000241809400040516a00700024001c40e8042820047d4086010000194000034460601c040d900d40100c15201d031100f442029140d4011200583d0300e01040c06d02c44000490180790000c1075015400802000c00803114040c103650300b210000c51800c0d0b070b603c1500b41c1405502c2c080301821005d00c1a00041180000d2010b84803441581586c0c0800d805d0703403d07a0380c0181c40245020381c41d041045100b003000a090700d10f0b40d0040d04544014103103000c118525507000d038241d0000c1d000c1903402d900d008030607804120310305 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 881830926 1250 881829676 881829701
    0x3070e01030b0a05130609052b090e010503031803120a0315060203070b06061b060c03181209040b01090936050a0605270709051e07120216030c0501 65
    0x400c2e403c01e4a004114018034a5002e480d06d6070710b10607201005010301c10605070201c049130140111003009809140c0c083c548403044040382aa000016141882442c0e1504942e4020301660511641c061601200d40c0c200701002d03414003a40b0440d11044c40310f00043c20070032005503800a98200744a0003039600d0341180c1c01c40c605550041c86003500048502c4e8501c4d40c41803017615101d40310b68443c0031400c0001e840143c45d0a00d40291000c01160540703000256208010b41012280d505801000c42500c40b00d179080312500f503850400001d48182001e411403a42c2ca40180b410b11103017a66002c00c4000c842c242e620300c0704175a180050044a640c40b55000900c4140d001c403000c50340178803035a22076640e80c401840082c25203032940c002441484400ba0319821003220340c000b25103a54064102e1640703e40d880e0103050401450f000115032040c4810b1412010160228030198981d2258201030761036030000b14a91035565000c12000026001601000c9807452081c0c594032841d69151500364252072102e207181 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 881832176 1250 881830926 881830931
    0xb0705120f012111130b061612030905060714040f240e0109091d032208030a05030121150605040b0f0f130207050601060c02090f07050a0311040503070e01030b0a 71
    0x3501003444d0b80c60149080b00d08490b1062941207031803c1202400010014075401040440c10200265054035a20a90f512403c0d07400022031410105408460034001c01401d55403100000038180f90080c0480803180403907009150a0039920300c0b00c0c81d200545500181c03070b99020f21081180c3e400501500f0068030010741003034000d80b40c6190008000440703a114000307000b074440c0444006006090225100300c5440010391380d4038034100d05110303000000100c01a0301d2404120002982040100540c0d544c01d21075622603246901c3d0402466081852089901e6510008440803000030800c1e1102c03003015604420204916107880c0400007100c2010900ca8001d1100b60204800c981e030307003180144924011a4a0118541c070040341c08001e01840c18018401c0c8178190020500c40d0300201740c0d54141c1d200b1603455110b40d403840d205e90303c16107040d5407020104006000b070030889130003600401c00740c22040841c0e60a0950700e0300000e1602c2d10f181d01c80888440042e0041c4140070b41944a560300c04040d0405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 881833426 1250 881832176 881832239
    0x3061b0f08070e01030207020d1e020a09021608030601020115090c1209120c08040b070b0610050c1b1507060507020105010b040305030313060f0207210e09040b0705120f01 75
    0x1034502c18544641d0f6040540c002104011550380300344c103112298000c1c00c90184500c01d152110400c02589100360b20480207001c0000f0141100e0003100c1c160140908420001449603940c082540c01c00340180c1e0665413039104403584e40030050420300c003c00f8918408540107524900280c048046221039116032420100d104010514480510055045626000980d10070606060040d4003c3c0e030400c0500361070008800b42030041c5d594080b401205c4c1120800c05038a422001a201c61041c500d04216680003d01c0901c10025182081d1aa21101804105a14182c801e014401c0e50081318103c444582d07820520003880d9091045c58003414000c24510b20300790a68554607542c5c08000d207800540035010700c00398100300c501c0c0c005180211485400795110110303843c1130031a50704141764061003142c01031440440c062007070440b89510302015025104548582d1607040b440030000b014401031100030801092482441d05002e0302c40e1801011017800c55040990440d002c208449c0300c02440c4000d101d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 881834532 1106 881833426 881833441
    0x10150c0303050a270c09240e06010c0b0a0b060c0123100e06150408060702060c070b0106031817040f17060103081303061b0f08 56
    0x8080c0000e9941e204910121555002c003011001c1181d2443c6243d030f404400da001540340a080984011611406c1c090142d411480e0a02ca0f1840c07a00c503070300043c0b140e90001d0030140c840c1003403440303840c209040002e00259218a020b0704000801000c11a240c0040e0300640882e100a8401500d40c4501c05246001f407603c066440c200041c2e22104841e503800204d1818841d4803100040e5142074103018000b0080f681c020401900442a000080001a0f078a03015000030301080004002920705000d0090074a600549000384108080c0b10920014191103e15419030300c19150000712a0b1102003100020a06d01c0c8024192000082d495603140e00b00c2c0b4014003e4030141c60300700900540e1200c14548100200c450300000740c21a00061000880c004018108000021410450075480f0740716072048407103103005c80c14100c0d5082150061141c000f912881d03860040e0a003c80d5600e024403 = true := by decide +kernel

theorem cover : BRFrame.Cov 881654676 881834532 := by
  have h0 := BRFrame.cov_init 881654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 881654676 ≤ n) (h2 : n < 881834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
