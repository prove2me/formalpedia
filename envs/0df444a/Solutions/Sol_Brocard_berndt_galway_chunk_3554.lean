-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3554
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:59:58.537022+00:00
-- url     : https://prove2.me/submissions/0ac09c43-6f6e-46b8-a66a-3c7ecd469535

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 639028776 ≤ n < 639208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 639030026 1250 639028776 639028783
    0x1b050d03020f15061507050f120d061a0f0903120d0f05090303040309050d080909010f05011e1e0c05030301060e0a0906060f03020a0e130515010507020a060c08120108 73
    0x4006503429609003400c40b10b80043c10703900031260194021110682c44030f41c0309031903020b481b550b44903008403044810510541842c14520907004170302040300040001c2180201c3c00380e4001011109820040e1960100c082c400030700500442020ba0740011a5002d0656800c02189101078010140f0039035604802ca9024003804890a0f002610b44c2090042540d003240042100d00c210303015074800000c50700b010100400c0c102203103026108043d080c410b021403555088160b034004c0000b50320f00c2c140c00b86001c00140ca081c2951302c03a070004408101000d0350003900408120710000b41103001e290345800300d0109a9841641a9002d401e40c80048004070380719070040080e1121440840340c1c4022182d442e08680261400c034004d10001602c030f048245c0c1c842d4044d4000d07200c40140e90905c0206070900c0c034003080d4441401c500000e981920f40003400b0b828000312030009213111013868407500d0400d0980110b000076002d0300c11201080703586075129091084000c203884003001c00ca101c0d10040d5a450020720355 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 639031276 1250 639030026 639030043
    0x315010b0c07051f05030c0d0f0207020a09181e080706050a051044062a04030f110a060206040506060d12080c13030303090c1707031b050d0302 63
    0x140706040c00030460f45130000301d440300014103d001da0710850a202003100e49400250104100b04014468030081003003d0003541e151622241005807101340c1da004100e0100b00d184d018040e0140360643c000c00c10440f01030940c13402b5402c54000520300301030401e80c00040c59a060044e00c1c449000c80e41404105481e00003030f00030404408144020b4407101c4247d066110701c1d00c2041540003102a4511410000219440141104000785291402480310040410103030a00c20103d51700050b08003d1048003c03540f00c5211603e202501044104ea40c03040d1049205070302020300740c8240100c4003010807107080710204580d14042c00e042d0400b5601c070342c041d540301400e4030200e405008003c00154542071080c003030009290052000702001c00400410f0380d00310805808440c03802c0081154800702c02c42058241c2c01980b0a50740040c0b10380103420554a102d01603000f42d004940d0002e100b4113404800202402a02d030080344240c4046071703549000050060f1648065000711220142c00b00385070b0003080703c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 639032526 1250 639031276 639031297
    0x303110408070321090509130f020a1205010c18050103050a1119020705031612050a06022a030c151305070f0303110d080c07080c06180706030b100e0315010b 69
    0x851051944c00e0554000c02c040c020346800070364120000e041050002d040220f114011114040011034036000302e03180608070b80201941c2600080e41c001000401d200700d00d118560340c80c0442c0b64101e80c601e00c9068170f03c00d21500d81050b8407180882c07020400355100b21044901d80210a07038407202d6510b4581001c40412107a0094018168006054100801c02d01d00300700c0000c20344c0c54000d05201c61540d510030040e6007a251031241ca654400061010700c01070907806e101c1501c0e2500041c400317552031394980e4121015803040c6c0040c00f028a00780d0300080c0745c045200781101e0020303440e13440e80740790700d0703040962840502584610b100016003450f00204040070b490207a40c5841466031600310056543c4c4002817010005540340380001e0045c0400340107420740510a21000c1e140c4040c040e4000e141010640b81566036544028401c0d0080358200506001032496003000d1148a60b0800022032400e00c0f10516000d01a541c0c0b104402583c0610154036000040c00c1c40b0840e40d615265036021540005a00f813 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 639033776 1250 639032526 639032573
    0x20106150906270510120e060a110903060109020313050d0509040c0305040b0f1801061e0f03110d06140a05010f080c09061003153206030403031104080703 68
    0x30a030440700140c1c2070f071458101440c0b031901c15240005005585507141075500c10403125028a0030104103030300680407d01d01120040445081c082d0090003240c107a0302001c0c0b8560010840c1039041d03100410800d044400c000340068407503841302507030b418400341003000818034000c03020f40398000c4d50408050006650140c0d0204201e8040400c29021900250b034044c02100c05d0f031002500b00c0c1c402440b0598002048034070000c240c0c407081280c0342075461517040848100e4481c0d07001c0c2100c003049000100101605000c04061515503200c460190501808990051811161640a100745034000c944011b91180c071899451a00c1c10705580108000c1c06408800001000006100200059084543c000082c440d6800340caa0394100310401881422001c00c3c0b5407a130480c41d9400c240d1403e140f000b040d4031007810004141d43c80c00d50354003032501ca0100b40c4002503540000b50302d0f1a810181c0b90311039490b05001641464200c2d810f00340e0701960b0b021520303c6c071554101104002c6500c1c28200302040d140b840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 639035026 1250 639033776 639033797
    0x4062102041d04080d0e0312060904030906080606090607060b0f031606030218030703080403030e030d170720030c01110c0d0c0f06021b060703060e07030c020106150906 74
    0x4490a07403089100e245010030480382040c2d9140794250a0716086845541058074124110740e5403403e907001ea0781c009445810202d40314035101c01c43c1201507400101124503a41ca03142c0b40d0380107400a1024010b1200700030082c00010282d4841104550748800e00420181d200c00c4030746003410190000121080c0a90780021b2164014240002c81451207940f00d1500ba070294244030003140290082480820700e0816982e50540300d0300c0911609025600072203030940c2d07542c00c42c100070b0b10340c0703000000300b60103a400f000d5000300b4140e0041041d440c0310482c1854040030b860303203c02250f0407002c41141183c1013451102c9901e4100d0000000d1800042d070100a0010441010141c3d44d14007410100082d190450b00c03506220750300c92248415064070440302e1000b1445561070309001ca802480ba403442030721380c0301d002405e8000c042011950242041c50305010300f40c1098248142d02c54050100c206050300c424030024010b00030340060000d001c64900c140b24015504100a00007211845803c021860020304c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 639036276 1250 639035026 639035087
    0x403170315091603020c190507030b0c07080306131b0315080106150309030210050a020301030b01080c030a030f020c031213080f0303041b08030a0c020a0603290409080406 75
    0x26075440b800440908103075180c03e07a10182e0107036000d0070825105000d80c9990300a00c0c0c40d0118501842406440100015402d41c0360240b03e807039020741841c071a40c201340810400500c0d078008a0794482c2f03003612101c000410030f1500c00040c02d01c581c1600301c245000458404c07140e03419031045c00c020b205210004050341d502c0044600701c0b442ca004841e007490030b0004160120303010381c2241002c40c0c4a4411580d505152021400441e503040e128a030740a50000010014845d04841150241010b90080c0041045000010380d590454000c010203010200f00c405800700c1c020f2080c0d054000b0080c0a03500e0741403004100c4029607015031460021703910011000706903070800046104a04411400540c40c580f2a0b0b21040e200c2d411045240150103402100414640000d00241c510300940f0f4440d00c8242d219841008a29400350300039804052a1141386174121000044a8400000c4400c1c8192612342100106028103407100001c1c007420307000a000103003194010b410086003015040e81f0000d0541511 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 639037526 1250 639036276 639036289
    0x60b0306130f29010b030603100c05031f0f060809010f0c0c1b09020c0303100b1305010819020f070c120b0a1518060305100603081605030403170315 65
    0x9101501040304080b00c0350003c0c40c2e50490610403c140030340c084400b4107001c031281503440b00342c01502103010048140200b90808020140c0c1d0440010002d10200b110305000400720300000340030000c0d10500d0044002640703030314a90031020300010b02942e0003480e200c00700904071040980700044c0d5580f07400b084050201142c428100310420359984c091280c20f80361a80224283c1d46040440c14034000c07040001c4641e524030052620b40ca84001850700c81c5400c0441485404840e0702c060011802000740c0740b0701c40410300d2403c0541d0400d0a00d680540c46a144003681c40c41070a650417080c40c40042c49445007106403003d440e141d881105151441c545507241c00781190031404000301a81010ba002c190302c460560440031203540b648081c03c0016594081440260310020075000c401660340a040c01402428400f110001d50b11100c2407000a07e1030361500c82034800c8804c0c2c5c1115001c120700000c00c100d828000ca074021500403960081840c0c0700f80200381a503209039400e8544802100300e0a180c1d08261 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 639038776 1250 639037526 639037561
    0xc080c0a17070501050a05090306070306050f0415050103020c070f030506100b07170703180303050912070f0b0c07080109060218120a060b01171e090303090c0f0402090409060b0306 79
    0x6101a0040a241200640d01904007007419420b0010070708c44c42ca0300e41c608100c035512801d007542d8007240407803901041c001042d12414000c0d0086051865041110b040140f008046502c2840d0050391804440710260a21006130041c07080700d680e07500d0010a006002491900801824002e28412230707032002d100000340700c0c0e44801007000e0b0301c20110360740340840d10003c0c0020078080d0405007840c06030158450303d042c0e0f5940017207000c240c001ca0701c20300d1070414003035881c0e110b08480002c241c440c5c00d250b141d41110328284101a082900010f840f130602030103001c103100a02442c0000d2140e0400e61030803d000c0e402c02d0b8954100e400b40a0421881494180d4810710080a640060412080b0544031a0050314103000440d050058102603100e241c0c100e0b0664500c19040800000a494042c03000803100700009000d100355540f00b807040c0541e1181c003041000850908885501e04100303604080383c0a406080d00d025031247c44e00a00105202c21500496503200f0100d0036501c85680c2c100c08441c0380c4845 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 639040026 1250 639038776 639038819
    0x3090304050a12240e0a12201f020c0715030b0a0b071506052d03010e031c06150e03010b0a1d06030a020d12020f060c1c090c080c0a 58
    0x2200340031310b0001008004c82c1481402480003289590390000c460749881107291040300c5015819181d101d069610104a00c010b0382e0715010100040c440343c10099423219803180c4094040200c2808001e5100103504a40d0b107000541c0075500035540d162055184818201405000300c1d0500352040b4075881c11508560079603212074007450820f0f00b15110300001101540041c03401070358510001c06c180e526429080141c2d05544194100d480408803800340b4400c2200016001780e04025448002c00303000300c107a5545103144d51004200d03400c00200c030409808540d000d0752041120075090b00c400c0c0e81c00300300050880019400bd10042440100b0b001c0d54012611a0001a4000002c075544107010354062641155004084030000003c0346c000a002c1a481603040b12102c915041210045e03030140038946506281d80040c00e0340b8a080381034100f0900c115034140004903142044c4116034501540071812043d040810400c986480c1c151250303403154104549880b89981070400030b000710200e955070440400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 639041276 1250 639040026 639040043
    0x1e070201050106121a121f0b030319091a0a0206090f060615040312091a04050114160f0813080102090f09040c090e0a030e040b0f1c020603090304050a12 67
    0x940c1d049000042110141e1758800201111000069642d071000f03902e55484440090150341041d41181800c40300848011840d2900b06030ba1400340d60350110981381a81c0c5401915400e909410104a4140e1441c1e0400c051505034042500c40b40c01154000d170001c15003580881c1c90986800804541da9070b212200a0081d5001c0c600003006801e0500d007520602e1002e4003068181074032581c8803524040103206100c0010b100400401102c00c594211a401c1280a10302d02d04d002d052100003080310501e0482c8241c080b00014a00e11000000905403e02c02d42140b40341c1251089440c010320701303520144e4190044800d5102c007080040c010b200b10390544100525800c20010328805021034200c2c010019108642c0761f00d400038007a441d50107901c10316859a4007402e10600c180c40c0c050000c0205001841c00760b403030150807088640710788078082d010050884184108a260551705c030b204c0b0100030740007500014044140150400e001001e0019204100d41c900c11150325010564240801c500b4041c26180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 639042526 1250 639041276 639041297
    0x90b18040f2d110d051005011403010e0411061207030b031b040f1107120828050402060c0109031d060307050304171905031006030221130b1e070201050106 68
    0x8142c0c040100c82c00d11031540802c45101646039070300300390001e14000382500c1d1540100a411000e221102020b41403d08101c0c1500c50100042145404140130310080b88880001080030300803075016807804004001c1c84156500f00c3e007070103c03a00324802c2d581c90003c2400c1000da40e4281c5030209444501c0000c4504e420000c0076410100400b80c503103001104c000c0ca503034881c000d501021a10090410305c0c01041c8031403285124500080541000030f0004640b0001c1c01d035030b80106402c9031146250929198804106620b41c0d0000402074841c5071203d41c0950b20340500701c0d04140d008a0f005400d1050041032408483e0440c0a0101a00c0101c80c4040051000c10010300000c105004018042e80d86a0780d8904250390070a850202d05604100e07000030820100030001d035807480ea400d100142409107410b508080842d21400429510041440505444a0000340b0741d40048079032142050340001e2000c805080c400e002520075400308240c5050044454001102070340140901c0f4100c1d04d00350307549046003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 639043776 1250 639042526 639042581
    0xc0301081506040b031c0f0e1f0306081e070b0301050d0b100503071d10030210030207030201020702040f230f041103030d110d1514040c090b18040f 65
    0x10301c4001c000c0c940c400e40c1d80d0111105900d00304036045c03490030b0102040c2c8000340508006801d0288080105080007100c554003400c070f0300c0d8000c0314a00d0144035160750180d00d504c5101034000e0400307500701c04042e2007a00c0004101506031110181c01e40c5020b130070f0314600368595110000600c002d004140d04642001711040001e001860031680c0034207821740c180240307600c800000303040484a6100c03c81c242148041c0c19540314901264941000d440c800605a032840e6502041c0c4011080d203840003459400703e145010300d8000e40450394216030043c000c202404104059070001c0c441c91b000c0300304965842407a003140b6911b840c1c1d050300481811080c07202c0da42c2e50740d5444030381040c2d41c14001d4141c001840310052204050040c000e0700c0c0c8032200c6440c2c803005418081d4007114180c00c03403855403d011601c03c1201252a0800d01c260a8041e0740c0031486144214099840343e640b40e1110b1240a00055081c6480006c50854401c840c02200d00380161135401840105441c0d00e88400e1309500403403a22a0500b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 639045026 1250 639043776 639043813
    0x120b0601050708210412020118021905091008070602030a050f030612011508190b0a0b010c0f060207050c0604140f01020c1e15120c03040f0605010810050c030108 71
    0x8203208040203407418030000500d401e00701c51481301100e44c405070390501c8100a9003104141a01c1c01c0351008000294000034000080002a58043d0040352041400c1c1c800c070b100d0041400107410003400d11021070914840d8140401440d22811b0102d0080c50741c082000340c408003c990900d00c141c4c0c1c94909000c0d0020013084207500141c0342a40c80003803241c0418104000303004482c1451100c40d08032100d45c0c0341140841c10507403800400ca501d144044158000505220107250700900d400000080d0700140f240181d811104100015045107414110002004110340051149a00c1031099440742c09101080c40814001ea0080c4202290080c280c03404a050a500442c610030301481103408240e9014081001321144105240d1001445504001d076420300e01408070651244400e4240340148480b4509842000504461350220001010505116080342e22005aa41200f000c0050b0b59540500b103694841034250344d146079041c41d0010302039100c018180c0f4102d40c00344000d0101c003507400010401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 639046276 1250 639045026 639045037
    0x1e1c14070809030a0c03030e0f0103022b0b030a120f030c0c0206030615040b04080f0307050a120509100801090b0d1e031236031b0503071401020310120b060105 70
    0x80504c90606075201050084c4100c50085001e03807203a40300040c110302881000200e01030014145401004030f50740594001101c0500000340c2110b407030300c0642c8881080d024012007240a5030500c0780c20014020b104042e035044500c0005030301d5544442540c03c1d01642620034030b0030703180c0c041a1075180041c0581055401540c0c444001861b04010603052000c90150340c1164000c480392039004034040c8014030081181d135031928120b030019070810401e980e41a60701c08075884018030044a4801e1220728a01600590f008210f0041140e540590510030003026100e00340300e600005410f1100c90301c102d0a15840c1c002255030014020140145054214410700c024000200d0070030404c1d49201d001c0807841d00c181202c031052500200030b0070500e0414803200c100060060b07000541d030380c0c10310b00000350450342d210009a80d87d17428200d000b01c1350500c0d90039070003440005840c2024009160780344500640c0258420400d80742d050180c29103420a00141c480c0500006110074082c6022484a601440c054103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 639047526 1250 639046276 639046279
    0x62d0906040227091b01020105061302070f05010203090a211202160602040b040e0105091501230304060605130207110f060702030d08040b06060325021e1c14070809 72
    0x20760007481c100303031440143d000301c0c0d41400c0c40e0003696071101052070603014007000c1c0300240300070301250415200103005402e5544031803110f990300251131401c102c0c0750300c0f00c88000d40e0440e008545a1510200403500e0746e903040003c03226512200400c0781240e015640c200c0201c0d81c1c560314803540d20308010074400254840724652100c8542484a440003950a00080010342207242000780c41e60324048c4100008030040e000944202c983c1010031908030100c01c8400101582480d0a400600040340860012190920040ca1021000040000b40255070300701108a803000d4608000c0c03074280c03d078040201e000710135008060100300c015501407403078009030191182030f00511030340c5420015400246880030360040b40380812075140422081c4039282811640c1300005803086451443d000001c07861102040d00c2e10b10031032080d084400301141c800c10400e50792101442d210030050080761621651103c20818010311422a018210180c5100e01c40403032071a050903ca071828001c00e643e55a900350051520305 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 639048776 1250 639047526 639047569
    0x30c1707080901031a0310140112080f09010c06090b041202011b140d09050d090906060c2a0603020c100e0a0209040501200702030c01110714030f062d09060402 70
    0x1040a81c0d000d1001c0c4030700d032420b8035000070350b510b9007a80c2c1c40c41d800c2305a0001601c00d480e20046d9010440d20300469001c0301031403004c02c2e13490074181c00503541c0306846800504400e20741100707603081119201d0803d0003580100ea0780640c031101064200c0c240c41c00081c290351005500048482c0080c040d109224141541810003402c0c0900c1c0310910741159100001903e060744212000081c4580160740740d0080e0440c0c0f50240540c030b0400708044c107400d00c48032000300030344002c2c1c468000307406000116040c0040c1c8850000180b03940c8880080180d00300318035441082c041d41651495107003041c03244810b80b5244101911842d0916001c100340303040001c01c140c03859501c99052000c0026580d0710501c2d003110241d8500e44410160050514195910600906000320882604120000018640100c0b801c4840c04017495240d10040380c02e000454050480a11079800ae210340e1070000411321000088540c62840700030418008901100e40a0f2072035080c07500b089010501508014002141050500606 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 639050026 1250 639048776 639048821
    0x1401020a0602030705040312080c03010b030c0714030405031b18041e260328060302040f090224180a0e0709060206010b09010e040209010e0d030c170708090103 70
    0x7000203a070701c2184c01000051001400340104292801019020020341c41c100c9400e10f0100c622007624801030040000390a000300000d800c2d0082181101e0049501101100c0d100840d0000c0d250307250040d025084c407030b0160300e241e1000200d183d004000e00b00030050034409450291200c103040054060401d4411031050740305803101410000009034114458504001003008002524034044d44491040e19821010030520220740200180110100000c3c100256405a04030f0610010711550748000d40041c10b080101e40600300c0d9510041090740203694a4041108451400e0005c0d00c100644103154a424000329000420103030600346080f401820414005444404840020b402141d1090001c1e2440b181030000c06c2c8c1c140041030040101d11405030400b40f0b4600042c0100e01c02082e02c6000759408540b0058036031082403084d2031a680030b44510102103441c1001854044a11000e440c4020440107a108069000045480d40ba400c6000d180c207184550700118081c0c0300c85402d10002c00d0540d40c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 639051276 1250 639050026 639050033
    0x15070b06030c1512161707023d2a090e0123060901140f040321030c0504030314070c08010608100e0606061e1c06031511041401020a 58
    0x118041c3e10180303500e442d14800c0040c6084e400400c1c0140101c91141a40285604125080e8034004030481d1501e4540c0c0e500300032031421651003400c078214042103443c420200c200404120419040a0301400107503680755240d000d996458400301c601410541d04400b840001d18003101408505152079905142d881c2604402d1030300030f030132080c0012441c21601000714046403202d4000c2c0300c29544c95081907859400030b024807110410300d45e6040c0c2c002441c2d0001c0703c8900b00310340203158030449103251020061001005081911001d01c0402d1400010030310503405001908c04580c1d050fa02e84514942841d026145038101407400c441441e4041008079111500380186d001400003040286a000003200c2d03600c099500485101c10150012018020f0344e495031021140c482500e0002d802901995941101280c419404007070321040c2d441e40520311004450b040031040381d01503d104240740d51414100801c5810780d6950f002420000c07c010451000c0c0285082c51503a0140180c0318020410344 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 639052526 1250 639051276 639051289
    0x509100e162c0f04090b06010f0c02030109051507020a1e050a1703190b030c2b080418021314060c0304030605041a01060e01030203040609080703180515070b06030c 72
    0x1840605840224000500c00c2c14030b0b03d80e003555002c1c221824420b8484540b142c000034003001d40407604118180c001048401d0040000b040c0b0540d0181c02000248101d08103180c40e06010360000115910070f80214103217500c0041e80708403403038000003c0c07035040c2c1c00d001400e403442c80400c00031110381c044c00100c180450780e0313601d44103206101c0f0500c4550b40d1900405d44280c4030401d0050503035940c5064900c9079903480014101e0100c0c2e8003502c056008040d1215003003010341d81740c0310551040c1901c3c01c0341410084500050011104c6800c00350554401c0040913005034050420760445808503800100704020070307000004811078000d04028038120800380d1103170640c2d005070420b0740d9440d1510140700412005211541004050010100465050880c010900c0d249102100d0401d074020001c03805100c2954032a003c8594401d00141d601c040500e000303800000d200314100c00c00704910300c000409042078050210455195a2014a000c5480d5154201054081d0040c0d0300751040c3e0603c0041512002c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 639053776 1250 639052526 639052577
    0x1050117070c031707080a0f020c0a06050703060b0a090e0c0322020118171c0c0807022b1a060d0204020c010e0a08041701020a05040302060315090c040509100e16 71
    0x561b505480340c0383c00004401650142051218120301c10408010003000215403542c84650100c1d0101e62601c606208501800481e00905266000020041500740d001910002114a8141024910780d1031440581c00d40c041151030040070340c905180040c600105c445108907003441410030030204e0308040c440003107001c003075002524110b040c074054110203035003000500d00040b50310555180b0f0741c55444009101d4106007400420804003c1015001c541d54072044a03181c8685070700034040c2d040c5d401e007070072083c5d0200182520002041c4250703001d45030002ca42c00b4894140a000141c01c8182582030000941c020f00291010355a101641e40700d91009000c402400d0740114109603c80341041150b03078803060811407071010750384108803418651344c000301528202c1e0780440b0030688950b05c4005103803d000c000525141c1c08007070f40c000c00241c280944082c009444041da0301c120141e5401411000d80d1034a40500d0300d049a0b5500014500500d941500c404014070345400c80c03030481000d04c40068803401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 639055026 1250 639053776 639053791
    0x804020d02060d110313230c10050904020706060905090d0f050c0114070e0108071704080a030b09011e052202071e080d0e011a0405130803090309040501050117070c0317 74
    0x4200c040c109101000c480130001a0f40d0a030030400c41e100340c060081e07848060f08141d50041d440c01d49c8812006000b036040d500c85080260080d585d8149501d08400100114010707680d4562401d008580c0380400007600d6900204180c6400c100700b2103007001503503540c21440b00e8840564131140d1f20b50000c108040c12900450740ca884680c0d0120008001415000004011004010114000c880c0c540c000040300c94006412004095407441244000c130040c1401486140d0040f6541c400001c0a541c011000e41540380c0145960b411161602d04104c180da98060b02c810050401290019500c0c08550040c000240b10b0000d0303900e20300c11007032180214101d08800392180140410048071441f4580030700012080c952000704000b42e04006058071454140d91b4950103507548800290507a103a0081c60352805030040c480d03603180e1401f2016543c0ea035100b072601c01c0c01a800c00b0000075055015160f085508500303544101203503030ba184412a40ca0400c24016010001400700303541484642c916102c1c0181d80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 639056276 1250 639055026 639055051
    0xf0203070309061404170f0114280905010c0e0f060a0c06020306030c0d060f050a050f0f04110307141e0a031e080316140f0d05190c0f08070804020d02060d1103 70
    0x1401f0300381c21034008005c6411210b41d031348100030b0b030f0002070016485000300c00c00c0908510700301051100010050799200a1045d8a00342420340741035040440284690701c125071220b00320340c0c182e007400000d00512441c540400c01a0110400080180c5c0255901c0b02001d012101c2c040c1035100058041403680c81c00b522019503842c0b4011080041707000c0d95602280c2030b2001d028a0400114080b01000000c10840300d1980c918041001c000e440c1c0700b00501454000c007141c044030380798a1400c414414a04050744692918050442c1400114001c00c0c46850001d110365505882c6440340c0c42a800201e1751105801d10303031440000010700101c080d41c01070001d0b0403c211070414860b00074201c2c1e0410b44906191100c1801294061080c0b08112848a001d0200c0820355445021002803074441403c030152a40742001050b21541d90700203e03031410b41540c0d585081060f1140d40060b80d8650301034501a40104910a807072015003803103002010792081c00b00c8009801e07845101904019003090350407841940307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 639057526 1250 639056276 639056293
    0x121d030415030b030304031e02010903170c0622030c03021f0209091003120c0606050913050d0503070c1106091e040c0302030906070804020a080a060c0f020307030906140417 76
    0x503454803c901c186042680114a0181580c5603a004000368001c0080e9044a05415208591007080d000c802154401c01908542120518030402d681003482d00c031646c0e1103541c0014420030041c00c044200c480c420407001c40c00e00c41a440488550f003664205805510400e00c0c0001002c20304c00c4024240143c00b403006842d09012030800c02b820700c01600600710521444801d00104060441139000303807182d810b0117008401c107842c0c100054401e66222581c0080c2c010304000c103146001c40045003940c4204150f03202e02240040a81d8540016680e0000044083d00d000002407102d9003a80c040682c0106082e08022500c00002c140115008140703000d14918001c03443d041c2050f0003003410305051805d0550540c030300501160342d140d100400f128200184240400c0c10b544600c840c96026051000960309802d034642002d00246c0046800f45001910340d009c204941407020003a100d2055055035404c10051a020382200e15400201d00d0b14440d070b80402001078580c6240444070782c09a0380764040c02d0000b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 639058776 1250 639057526 639057569
    0xc05060903031b011b2c0a05030304080c030c010c030c021917010f050c09012106030818010e090105030a260a080907060507052e060e041101050406121d0304 69
    0x10b0045c8141d01071000c8024405da400d50784410420f07825400200e50105640c840000500d074203001d03440b8503058000007402060301035012034a080c4104041d0b044400505aa40045400458900001d00041c0f030a40107a0018984552a13162107580707921000304464403911240b1035010b800d03100110907992800250241d04040c0202075000380c1e14008581000d0b284070000e0000484030382e4610380f14a040406c0f0031900b04d940d12030400b40d43c00040391925803030800710341482e91200181d80d03804564009051075541c82d00c800240d0580e100603028141a2450380c0d542105002e40c03d860444807160b07458100c000000c9100600154282c6507640070240c2065402e007420a00709801000030060b00b001802c001c10340001e246403500c44451080280c4c3c414034424a0100c05266074044c0c01c080c10080c002a0305d06175504514055030003615001c80707100b0104010359107486a03104a1020030317511004880c1a85540e40302991040c10015400000055424103600b9980560040341c2041c0b1204140102e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 639060026 1250 639058776 639058811
    0x1a0702010f020601080304090b1504120b0f060d0209180d030c0e04110405092a030a0c030e100c0207032118060c0f1b08011b020106030c05060903031b01 67
    0x1044030742c00509829410102c0b8181c5a00c2940520404141c944801005c40d440e04a110a410b809441700980c68607160f40d0741c1440012480000d56004646c4004101c42c00125441d05018000007400700743c40b40e81c1542880b000f184c2c010700305800035804420354603090b48103102c8052030169541e00042d5010172408060202810101018003a502d000c04480340c1004035802c540580d01d0441328405079541c0c444038448410b000803600f4000002c4030310780b40c076200444d2020b140182d104820611841e600c4c10000c4040f2550754240c05020340c419094400b10750150f502c40d88070584c181c4180e42c40c1a85071b49844202c8201c110081c88880342e60041c0c400410303809003140a04016804032b4201e45031030030320000c1c048201200050039024041c02503004000740c40918125888040b680840040d9958841c14000e084440d0101c003401c0b010701c1113043c440d20622400c8181d80e4000c000460003030034003040c000710740c10548680d6014801044914030ba2860f48a800c50000d0034a0000704940d802105138680 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 639061276 1250 639060026 639060047
    0x14070b03060120060f090f030f07060f09020a1503060e10030b07110616050d091520030103060218031603050706090605030711190318080c0603040f08041a070201 71
    0x310102840f400c400700a40c00b1801070740110801e1211111a100d00d022242081c03403500f0b03100c0c12448001082c40300d80c54544060121940034440400c82000d001441d5002e0341c4850388020b600c4142d0000c10300c0840700e1000d4001500310149000504240c4400309410885001e44441c020360785515820420040a00241a030020042c076003c3e8402048490450f60f5a202078428403480c1803483c00320062a1254003540c5507803400c5002444855001e09001891103e2000100000c03810a0000c0f10003a41e0794032800d100700303158504c1034a507070310310344605000b500000300c0210501e9048001844503901000605880c1142c91242d10381c8a2075450254a030000c1d030342c004400d02803e99000c000140e000410b81e54024601e003458505112100c1c0300d03604180c044414044158104008070b014140e1040a005e201c0088030032202003552504a01070703550300d01402c1d00d50700c240b0410000d40001e04d210b040d0904036126140060801d511103082100300c2e41801c4070a411100f020070101c080d581d00c41c041c0e04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 639062526 1250 639061276 639061307
    0x90c020f0d030c0224090d0f020a0b060a030803010f08011a060a0e151801120e0d12061211010f0f020705100c1b081606020d080414070b030601 63
    0x106034140d000d951218507080300841031540d601c001c042c2c480d000744400e1501600d40b0800c0a504040d441c0e825108110540b10540c40303104991803200528040c500c119440e0003c0c1e0014003c1440f02d90792901c2e594002461183c22262120b00040012420740146020b484030a12011540e4142a03910303003164a09107082d02460389649100c41c55413140011a0b43da98842d192120016107201c000c25855500c60105000c00c13580010720041d550100048030800c420b0036070f511800c0e4441d00d14090141c2c3c0000e031404001e80c00ac45060809035008202c400d890303410f1001d000ca0815540d0360002140e03080004281e07000c1c509200e0840a0b580c0c070080c1d003d03400b86241005505c0e620351000007175a030310140c002c4600503101c000b0044442d602400d10000480d9100031140c003144400184044d0b145424440e004813032085103114990128054907180523240c3c0d43d401082c0c54211604119000c0001500c2501e00d048041040d09925009000710700c06030040104e640e640742040f4000400c5100801e6841 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 639063776 1250 639062526 639062533
    0x60e07111b1309061e06090b06190f1b0b15091608070c0507090b03060f040308070305040201050d0c09030c0f1a0c2503060507090b2b020a09090c02 65
    0x40041d590b03200c40380d01e441c03400c050015140000d4075140008000103c00c201c603410302c8001a203040015a0094420b40304114020b1194810310003c0c082d15026915809094030b031104d108100c21441100c02e0445c01016241c844580462340700a540c00400c8403405132010402d207820460403c0303244a10507a0307220152044055498143d41c000c80c440c841c40c2c0041d0030401000086002d0501c02c0000aa29981100035075031402c4d5510f40c000700600c4400e959900900500001803046040303074600c1407103160507859840c0290b0303513103500720014000180120305001b0f003441140b88d03007201303481010310140b0346132a0040400c0c11414098604a07040e800f011011515244c14055228290341820400f100000b01076103550401060030300301403182d8114600c5610610208402c0000788444404584c09914200200e4889420480c4d140b4194001c140c1c44100070003001210920349040131760000103004913203280d40700d88044c090590348881040800159045400d000380c0d0355601c1100500c48450004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 639065026 1250 639063776 639063823
    0x30d05100b0a020d1e1b17040803090907030c0f0c0201050418360f0609060513030305090a020f010c02010c33231506042303060f0a0e01060e0711 64
    0x4001c018011b114412984c1018050001c00220305000c0c0c0c00080050b00c03213070303c981e16080c905036640c0180b090b451180400c00d0200da62280640706054140c0b03804d0361061132401c240982a9800580358404904210040100040f0b01c00c100100d4174201d91160004034040c80860280c10489003540704040b1031400554013400c0315003914418a00890b8006e40c0004407841c1414540010008110301804550601d0f041080c84500312042c8201d8034881d071010031441d200d11291130356842510130002c0d004940c424104e000f542c05100e1040d000703071052403d18040c0c10703195204414000c074003a4016001000142c1e503940031580044a29804900e800c08101c04100160401000268090381c0c00c001c2408c10081000d280580c52080100035000d00f1040d96035650752940d0340502d003581c400d466070041960000000d8034000c03c0a03400b801610030a18140d451b02d2350440000c0100d40001c4031159a12100025181110071046102e02c5664407512440d42040c0d201c24100401403d0a80d01c0c6980b840a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 639066276 1250 639065026 639065087
    0x9060b0a0f21080409050403020d090f0509191406100810140607050a050c0f062107050d1a01030c18030f031101020711031e030d05100b0a020d 63
    0x4160807620203400c00c0c190359480b0714201940300039000300540048070000d030110300e541250300098010f40c8a50708580e005403c004044400002902518550b500a1a03042080345403074100030350040483e04821a6171a8a400361804a40545502034000c0c4641c10070003855160804845a41d001c9504005109240030161180c2807a1980107503070b03403000072000010750340c1c40e00c0e000d46510560000480c0e40c091302c0c5081682e40c60011404c0148a640e10310708003482c07428044107a441f000c2080324803070348240d451482d00002941c014000820094140700202003038090f4003d104d411050190b01c5401d1024075000141036030f4807018000103000500010b6002c4148920b44d074001c8a410a03007000880c104d9190403141c14843e40c0c003000d510b40c000b00b0108144620683c1e0407142000c1101201d584a00707003271591010b91418203602c80342750010b101003030140900c1c0c0c21255000a0605040050a4076010300cae80c0e041e0015240c03040181c3c410314925541d66042251034035002c07034020001c0d0b40e00c0518507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 639067526 1250 639066276 639066299
    0xd06031104181b051002010b0319020f0f06190903060c02280201030f0203010602010506030c0a080c090603030d1409060f15011d060a0f08160e0d0305090405070309060b0a 75
    0x44002e011a2100c806100c0e03c16400002d1005410010b082c20300e42d104e5000024080c00882c021f1511070300440c4000c18542c0d02e010300d030541c61640500b03407000c2400d142d010411410382c00440e954003c00b080004094242c0c1c142c5c0f0640c0c10810320b4498815030303421401c189044036003100451066500102140005950800310701b0852208004503000c140340321300c0128064154001014441e9002000104030180c064010510480d41501103d1404000401b08000962079204140340c9070004c24000f81c60703040224a050388100003900712407a24090750401030855005031403a8021141040621403a05018400d49401c20042c030b080d19520700f880303903c55080204100010b418080c0e101c542c0e117807444843c10740c001e01240c020191521600c0100c80a000e0b41040075480c0c001404080005049409010341c2c43d4400540e55034003221000c00205000781040f032840c0641c180041030010004075a0340d405044d01c604100c0c0c1e4040340c103c0d0245480801d0b5111421620b225850b9004180205880c10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 639068776 1250 639067526 639067571
    0x3040506181011150f07050c07050603040506010e01080d020d030f09020301052701110304060207141213080d0206062b05150c0c1f020d020d06031104 66
    0x1100d9503551001d15003880c403082030001001c1d80d0000c401001550b03005030024120001800030405039490303286856000c0e16150000c88500b040c1212076400b048540784184060100420720f13004403880140c803000011001c0e08116801c5900d41c1c007410051002a800c032401078010704000e40106106d0500d500c0180d180e1405000807810565207110802130501a6040501c0341c07038010700200a00c0c00c1091500884a442c401c2410007600c5007520008640c10512640e00510600da003202d017591119079034a4081c1d841208150b0b070002c594401c241d42510203110300e80300c0c0d1441c2c48405944044094042d03a60501690285a298111440e030045140e00460710340c0c0d1011003103410441460130080142c03410a075600081d460390340c0d054466400c000000a90303400011200840541035070300d116a01c400380c81b81c08072030b5441d90400310f009565a13002c0e1144668071240c0080142c100b001c0100544126000b6000c9040c1c529192002081405045c1340d0b41d04d0182000ea40c1440545c0704a541d2a9040300d40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 639070026 1250 639068776 639068779
    0x15060605040b071e0f0b041106041d0408040b130302040605040c052d0a0206060f09070f1d091f090606090e060a1205030c070b09011e030b030709090b0117030405 71
    0x203500c030040340c031a038882c0140c000680c000e034541701004142c03c00c8000300c14101c0c0e00f00e0b0f50812160301c1c001d003480d10809035030840301e200c5030850503000300781052100840c001d0700c11181d9600c00d1001003501c244a5002e441126189078070191b020b40340d801000b0a0311340300d034480e6001d285020440c1450b02d9002c4222040c42c000b1030312451440d00c4d0812486401420700d01c0d07034901d81c0c50101c1c89281c425404120580a0130f0b04899120400e4030748010000e451209465140110381c2185c0c007050b00e00e010b000600c003490502c00003940c3c00d40396240819600d04003101c45c12000009158a4001c1c000280c61050180c54041c008002242c1800000b0f4258100b9004031056100c4070b80010b80301d80d840c9280c4a01501e101d4911140f003c4151800c141d0369044480446105d0240d840041a0b48000340250744078808140d5031144410340700404400e80230a211462401c0644070b607103450198808000e842c004004411000918540b03900b0a100405010b800022441000d20004600010000141c07410b0310340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 639071276 1250 639070026 639070043
    0xf180b0f0f042d120903020a3602040e16110d020c1513090b090106030209030c0112140907060e0102030405100305071704080a03060e0402091602030705010915060605040b07 76
    0xa03c0303081d2140120300b0500109160f01e070420b4070b14469885650b80003102c2c401d4800c08000ca8448501c4460004001416000c1d5003030a40407140c00e5204400d8011102074980c0d00515080d110305e8202144802210540f0494407400c24411207a41c0c4034140d251300b10900805088400740100300251150f84000b241032150309050000c0d4503c218010490b40351003d808448180c0580d40e02051020703101110006124040020000494500134002c0b075142010040185c100e6510000041d10b284c0d040600d2110350f503a40c5c2c6503000a0380b034150008d9002c1c48020000b800c1180c90284001d2a0541c0c0b4040181150014001041641c45d04444215280e469007004140c95031003d404452003404410000748020500c0f00b40811700c800e80e001003102c02415503061202035110f04070f1445c2c405064600070741007102c40000070407240417840c00c8203046513071344152480c184032074a84c00c3c2500e0303500505480c1e002413400c001c01c10658600c120401410039040c50360400b45041054411409407140140c035449 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 639072526 1250 639071276 639071333
    0x6051309020d03080603151602010e12040b13030605040506060a081b040203180d0f02150601120533040b010206062b06020c01020a03051f03060f180b0f0f04 69
    0x540502070f05001f003114420361822807900302c007411a00e0b12420802405540384c982c04040400300400e031801d1b1014a20b400d14139081c40d01400a8032030b8823820000401110100c00400040d40600070a030080f4081c0d001404503080000420116900641c0440d00550115903503d0080e00c003441c0070090400120360041c1c5a41c0c03148a601601c5003450003652041c010030700d0520005410115032800a1104d908071541d848410611468441e0244c8a16020611007c041410790070180c00459200e411125500401c03840440110700c060850380f21044c0c6142ea82c08040040c0c1820300c0398007602d4000348010b0030f20741046804074101c1c824000c1d00398845801d500d04100e140c07500600f20b000031680180115590202c3c010003a000350440c1180714006400c000c003050308c102c103c144480381002024070442030340d840c55440c0b42c02005103024008030103850b090103101040880b08944911405419010014a00300321604418040200f480e00303a50401e034140404100300441050310b0b410509460842d03003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 639073776 1250 639072526 639072529
    0x10f050f150d0e0a05010f200903070302040f0614030102070b0609091504060203041110050a26040b0711010c020c10021005040516060c0210050a0c0b04050106051309020d030806 78
    0x28442c2910040aa900348510011201d0380004c14200e294001e0008101c41d000d281c0d4010241d800090b09189020ba10494910000d030540b0004d1400c1d480060031100d0042e542ea002c5020b6541103c07642d0860395850701c080010f821841084066010b08800031442d02070555981c410f018006404903004607004800209800760420a0310b030754100c035191030342e540d00d014035088000e94400c503000c89120a6080520b60b032402c19040d01443c0c107040340c036030381d041144c0300d0400c680007491070380746100308134080a00030b0400f072034070480d14011401000c0e44102c07441c0801020340f00c894030001071025a85003810381c5613565808107030b581100c8801c039009207440840000c201d26040c000c070202200315180a0a000030404009903d881481d0482d0034600c0c6035944d03103c1511341c010766070070103500050844081c06c001e5100ba002000c00b5081030400c0103100080f5100c070349400b4001c441c201c0340d680d940c000600403072030007003225000302119040601c0012484d03808034a1004103510010240804d04c00411503a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 639075026 1250 639073776 639073819
    0x30d0509190803060a0e2517040606031202030f0403171903060302031e030403080a09152a0f02120f0d020a1a1014040f1404020108010f050f 62
    0x10000704401d0400508080c24400d4050380140c1e40c862050000010000e03950081c070750028410131000219017103001040c440030911541c00d282c903404000005482d1000310030506503e501582c0503031400144141546404046003480140036010b56001b0300c03180000d9103000003104e0070350b68003c0048122012800301090304d030140043d003100e5845010308408100740d00d03070f202d2070403039000b2030031600c42485511094000c6004004111820f4100304020302c0130a1000008143d200400d00d40090060358552950700684030394254080012041d007000040189400d11070305011a4120340c61020303e01a5552003000c1d60390b07100c0240036070807480c07002402040520903c21640340d6030090b1440030312043d00013503c81ca11082c085403243c07a818604840c03981451496445071030905403005000341040c1d081000320f400d103420103902685038968102c0350041802003444a40d1b25401c40040da050520015100100580007007240c44041402004242d1f14985008940c010a80380010041407a0000000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 639076276 1250 639075026 639075043
    0x150904020715050901110307050a050313020303073005070b060d060608012a080106081902040303051b0a0b06040f02040308030112030f1b1103100e031c0608030d0509 73
    0x1540c003036080e29169402c40d41000e84a940c11200070802503051034100d9042c2c1c002500c083c0b002400a01c100d400031405a4019030b000317891705003101890341d11580000d1560317220030012030317064206020854085038041e550f442040d0101c1c901c0840a410617000810038014800040c00e1340c2000c402080058540f001000b44a68121100703006003919960014040d09000000d2040d2001000003034101d00369060220300d5002c00c0f992040800d900e4820100c403040000780400e0101d07040c6039800414429a84024401148130351038080d25840c0c14011043d00910403a5141c60030340084000c0d030b0004c0d0745001000e9004400f1680020011401c0001c24001d004542004041180020000c43c440041c030031a0f0b500e40d44203a0340c1c0703000032150303640840748560030100c880462341d140c460780c00c0002e07482c0e070701d040c0c0840c0c010f01110b404c2220810560180c4128814100b090b41000610010350441045186003180382158103020040c40d140c0c0d440da41e0b100d20520f11100c2580c840c0030889102007844200d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 639077526 1250 639076276 639076283
    0x3200c0405280b0a0801140f04022b0201030501062102031003020a0807210c2306122a0f090103061829010e040905071a030405010501060504051509040207 68
    0x2442c25960101c200080c00651180c520502d410b0134002104001401085414800d40301d10008a0710b4240554480140c05403003268890461072900010804852040c11110780d6190100c41c0583d0500025041b1401030300071104000ba02119445031019040d0007080440c02c3d8200107170f0381d40e0750251f20344031a07400303810083d4811282d90300004c40050009520040c3d601001110321500b00d036034210a482820242c00070314401c0b0a40040020a13182c002580400d000c40c90080c9021101d440020101e502c05050034121804078810b210700320780000c1c903440c80540e4100450581d54481708242c840c03030003901d071004050800000c0c2b0b200e9030b074840c1d04000014189156070310b0500c601f036101c100c007404108103007586002404c0c210811516003e0840e12200e80107844204040c5d6200b03081c080986100f9100341c4040c0302d010000a90004a05849615082d014900301e40728281071400901350b62060340884200681484184442c0c7e4450701540c0a00b40c105c0c203d00c2e90b810812010501034007030640040d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 639078776 1250 639077526 639077581
    0x804080304201804110103020a0215130816030e060c03070f14010606120b0109050607060b150d06050315060312070c090f0b03150903040506210702030703200c0405 72
    0x541a0f44030880e0030500652043c0044201520f000c4011401c900480750503d005900c0700301c0200501451049003600a0641085007120400c0398a6184030340c2e11401c0b140c01500d040400e600c090541c0080f180001010444003680780c180c108414590700e025072140a45688043c244c2034040200c07440900380c80c142804001d1040c555110405007440c1d2014440464040c24104605915031080040c2d0701a118000e1006090102a4807044020700b0030001d610381098050720340d0500710090001400e2807251018000c10b00d14200014181001108442c07401c2d03407289101400555540410f400c00d1504085400a460300028148102d0004065018006141c0707440c065042d80340e101e4011495001c0150100e030320384401050b08200c4042c08883d07038021900280010700c210702d8050003c0c0254407103450710314000c0c1c4080007242541101515001d0140c0e0002420808058109507001358020070704041c072a0201c500c0c502c4035103489401c0c0034548034640e910f001859502d001d01142d60020b0031003641 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 639080026 1250 639078776 639078799
    0x30b0f1c05010507020a0515070503071b060609020c0106141c0f08040602330604050a110c010b0406050910060302070602071b0f0f08120901050906031510080408030420 74
    0x281d00e070003080c1b1050752903000e80480880021500d5004038050255503484620b5503a50000403102c040354480040b141e8021802c5c060301044990050b60064600080c0050343e030104400742c10300f103070a95403041407541d50500501186d0743d940228800c407800c1c82401d03000c4400c400d1800f0020300c0c0c200b041c01003400d9030102d808200c580e40007590b04c000c400003000255013800c60074110801d205840c0d01c0280985441c9000075100d00340340e00a42e27045401c07000e000c41e0041c8080d00124583d000300c910506a40c0d900c40004443e0305e0103001d9000100ba043c0e4141c071050400c01441c0800d40114081c00d401e064000035468100320142d4100c030802d0350040349410b55600b036046203000c2400d042c8903d02c0c0c0c844282c4008030744180da00c51340008580840004003450207650032a1600340d08094102414840144a0301340b90341c403024003c2d8801d0141401000714002110b08200300c1c280508002010000444104800030700307008102c2c0c1e00140c2185507041158800390b09800c200c02c450310182e8100803240c90 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 639081276 1250 639080026 639080041
    0xb0d02030103020405010e131410090812010f0e0114011e02060a05071b032001110304060c051912090c1401120e0d0f020f0106150807030b0f1c050105 66
    0x180d41038910860f000d10040c0d84c1d4201c402d034607050907920003a1007074410000600003802d0002031440c0600584c00e41381941d0300c0030001c0b82161502502039423180030000e05100c0d15007002110502500418520b0303400103040400300c2d04082814001e0017110100e45103440d1085e0b0184d1a46904030451269401603007141e450b00944920f1309032140025182404040303084c190046404200400c032822507100800d0003034078120340d128004041d148619070001d00d03c0603558800e000703010300c0460002d80079039071303061074035044040302e070210014001c018050204520b603002405030600241868500b00c0e480984d16400500280030b1220010b01c03080384004001a04201c011148a004400f42c030b626148030940d00b0808151344c1010507502c10764200101802d500c03801541070b400501880c0c4129401d184164048a0849031a0340050000c9116044c881e40703043c0e4402c0e4140c0e403051103450203110a00c000c1020800c20403150b18028480c00450b5545d0701440003042030b442070990010024007071420701c4203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 639082526 1250 639081276 639081281
    0x70504060f05090a05061c03110105070c05060f040803010510020f150a14010e07030203090708010e16060315031403070812040506012c04020d0206191e020a020f0a0b0d 74
    0xc42d0501408445001640c1c03085103100d00340c03045d88050221440a01401e99803000541511021028060b08607809c3d04008401d20074075201d01e5003512566810015424107524201c8028801a030483c41c010070400000d207944240c0341154006c0c0c5101c49000c9907000c040c0d0412070341002062043c070510144440680140c41d4443c00f403000075104000320400760f038525154071024014120b00060300c40216901500c0380e03009542c001e030184152003800d40c035086078600b51030001201d84482e0307118135088001c0b50000407002d402008281000c202d101040d21481d4407080031071001900116200c0b80300755200000b40200c900899102e422966500051100040d406806980c280c03054847e0340300204a6451903050300ea50450b4004182c4a541030484508039541c10041003241c0007a0750000303c500584a0501500810307600401000c0310713240d5400000c001407803030030345080c0d650044025030b2043d54002c241000c29039015640e4154085e02c440200f60359006a1b807005d03c0d50305000800074030b41035056 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 639083776 1250 639082526 639082529
    0x501020c0d0e1512040f050303100e131109091c1e020f0a14010902090c09030c010e0f0d231f05042a0b0307050706271202070504060f 59
    0x58803100c0310040d069050100c3d04084054205020008001885251201c80310066006201320503a800076146a59040c3c10b42d08151060380e01c44a005806100c548211400d10f540803500344c0301c000804400e5110102d8554102e03005030b0266400c103001c0780700b00b0802c4c0300c1c1101200b50860741d000c5000c0c56850040014210311554111569000050101c3d503102003016024003940100503c10900d20f915215007e9020b5a510340203596101007580050b2a200d01b032512403803d116003030351142481000c0c1410528519000c0e170401484c408400c03403594a450039a1300c50801540e0b1201c0c01c1030103107403002030016941c2ca42400d510284003454a401c40000352031308079011500c013040b44061044100416100f0542c0d005100d00c2ea5480500c1050190345100320318880f480f0010801140c0c1e49210300c0d810380c0b00b075684c800001c42c0010203200340581801f03000000312400480c0100b034004c0413809603410500c200000c101d005580e903c508402d2080181e500504001082001416525944001c56003440e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 639085026 1250 639083776 639083803
    0x60e0109170717070f060504062d140c060906090f0312160201090c03060515060f120601110d050a0311090f040b04060b040e0106020c030d0c17070501020c 68
    0x54480c08074581d050031401d08005a00500240400c03420700b030000c010002825211540c0d07200388072000600c600c999040000601081d29007030b81c0e075418110001c0040e06603c07180c4404410150560b214281c201d0f5040e104038040d8a00b800d00c510034890921014880d20742541002d100e070074240158590003040f458042c000002c2110f440c8104503004548a005182800c5240e0300441c0c0040d00c05103001031034041d407042ea0320000035103555a50b00c13642c4140c025041521003580e10010011202400a68601e030a28101d030858203060716440c140c4102d1040076100c0a080144078040360303081e405490104c01e40301c1c107002500c08032149900300420700d4012654182c00070717050280b400c0e108080c00c000c803112041c024080740d444481707200074840a03020071410a40c010740c0c4d44000194249054028001520034004601040d51406400a00c3c10002d441114826001a96410101a04084442c000f50350001c44030a428a4685001d24940076100c809040c075400000c0195808a0110722090b0710b008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 639086276 1250 639085026 639085037
    0x612020c0102070503040e250507020109031407180e030418090212030d14190c1b05030c010c020601050d0b06030102090d06020901171902030a06031a040308150a0b070f02040204060e01 81
    0x1108244c465001000708982c0a590300c21100e071000230b9102d4401840c81c81c0c01810a410515540d40e40c20461450105a108507138014810612165840d840c10030603080b140d110500241b0044041c1c26200c0c4590b2203084654a0105504101c540d146d030007a80c07095800030b00356881c1d40f5842880d191683d00244540c1c00c52454030403030304007112440c050140a0040c0c00b0120181c12134941a4030010900c3c02105d100f80001c81540350300a040410444d55103e200301e0207980c4900b81c40c01483d096a012004560942d004000140003c2d1511200404090340017900a281512098003203402803140703041c00d40d00306814650384014002076400a0040006c02c2c1c2e213646c90035002034041c450550040d141da0948286031010040c4084007a005150401019400011010768907522016100b40705103d4541c080103440c20803051580140025a0001c004003440f080e5030318903000107142c2c2c2a03d0280a545090200b4042c0074800046448004141c2c0540300b10343d51070301c400c0301070035208441160700d00160 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 639087526 1250 639086276 639086281
    0x1805030304031103120a05181e06180a1506080d03050124050a0c020a0512010608060c0a0207060f031811030c01140702040b061c0605041112010612020c0102070503040e 74
    0x2000013040342c08040c4190300d10314030398440c80382d0007014200142c1026a240c02c010b4540407201c0090144003d41e150560b035a000c40300c041401c181c10100c004020007920841072a0f445c1d0210004241149540d52000d0b04000d00035049032801e00408254120018a10170005100d11480d05944114162242d80400034050449182c00802422000f00d02400042c018008084044c0c0070b000304500035807004210703180c869190b0000c41d1a85d4004c668070107a90b9114142040105014043d507500503030101140b03482c0040b00c0202a41d916a1440fa03036042001c070903070341c200d218880e0b07210703031281811440303030b240c201d141810046103030842c4088180c480d0251440e0b68940b503005a400024840000c800c0a04005d496000c000040502c02e0443d40c0000b03041042e038001c1c06c0b05500407024042541c900158582c00d21040c0400c440c01004500400365081101e081405484140b0b2811540d41b442c04101101075031001d84043d00445c1c089603001d40c0080703002c074100700010002c0d0081c0c0d024403142c3c45065 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 639088776 1250 639087526 639087557
    0x606080d09030201050f070203060c0304060c09060c020607061e06080d090e360303040b0c0301030f0605060a090c03060509060105040e041416060c0209060103050709050d06180503030403 82
    0x106650346200001c980a2a010401035006030080c1c12900c00c144201c03424041d254000c64145035088540ca482c8010000c200400c2084074881c0f0703040c401c030b20302d80100d015042c140064401d950140340a442082d0100e01c4070100502904015801e0b501924014000c81c62611005e000e04128080c24240d4010b44540c0e5210b5842008076408564054a220f4100d40300c0f2021000085558030f40c441504503d441003100c9402e501c100c242e40c40c034041300115641d16160810301d03c0d10b0300162034144c40950800040001c0340e46030540c0b485003a0000800181e0341c0341e280001c0d40ca040f144d48501e241d02d0030070b00c01c6212282c243d8085404c40d0401d4400700103039618803004440503c1203000d0342103046400350200d00464040d00342e00100743c00c0c2078112110712034103035501940080a5806000003c0280d80301c0342c00c505109003090b4100302c0a080920035030030321100181c040c000c5070244901a59201303c1400501010b6085000080c440d80400440c121003824419102e9000311000d8010858904600848 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 639090026 1250 639088776 639088783
    0x3170307020d23181804060b060a050a0e030a0c12060e0606060708070516091d010515041806050a021914180d0b01080102040611060f1b0f0a0201050103060608 70
    0x41d941c1810010040f4581080c070f0920382145130032001c3d0f5005410b0210168803442c0c001c0d01142003009091849140c02e180460942c0c9418103481c1c066036003480344c0c0900d00d8200382030340c40d281d2050401d5841044c0036000310785415401700020309100800c0030001000400b4030304030380c04940a0003090100340c84203940b1903a604000c4d0703410b60b0020410030416011450400c003a0010703600c100140c41c3d159413030384000c1c84201c0b59500b00400c0c0765540c40c10141860181305411140c2c1c00d25400070b1129142c0346041c0c4118803c001c511600650302c1c3c0500854810200d241040c4240e48500c0c1000340d418500c52980007504035a10743c0c04400713400c021140040e806603210701c0c01184c04408403441c00006c0c00c055618869094142c50b00029002c44c000001850844501c0c040d003805800140c03910314046000346220081c1e5007141240c0c0144080c080720449000003180c0c021307038100621100c9080035080322400e225841c449101181e000c21080104c56044d0041c038101d034050a003c4c4016a01c0e910392a85 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 639091276 1250 639090026 639090047
    0x180105040f02190e09011512150213090f050402010f1403070518030f100f0b030a0209090c0a060306052e08060a0b0a121b080a090c03170307020d 64
    0xc0d60000600340061030a000410014010340c100f0380100c694558200164403015207040b0101e9443e500203000700645c12042d9401400c0146c08803805004039218450024080e940c1c0740310490f00028202d09030381500900780010032111034200070790b07034120000c2c1000300b101703660403800100c441007494101d5102d851000c154540c40241c47e0300c0c0da15104400d803015171141c041c81d50340f40320316403004000341e4003030200c00840d41d0b44c03101900051800a1560045400341707400380070702e10318042c0c00c03824030349000407a007002950540b500c1c1501d49581c450203240ca00302801c00c0341e100c600301744081782c001e9142e08a5012900203560a10410884148418065540000306c1c00c107440d01c003d12a41c558803e403601c0d6040107005c2c00c07402e8001c0d260000440300d5440700075800c0104140105040e40115180704906415001c00381d45250810079003401041c01c0001307004290ba10361640b80720b50511042e4250311008562148291a480400e044000e580390822940b110160040c03641100360b8a004008000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 639092526 1250 639091276 639091283
    0x9081002191119050d090801111c0b090103080c010e0a020d02040c090806090f16082a061318060302010801060c030309051b1002011401050105180a0303030518010504 73
    0x111558074401045403495225810a0050b2186030381c0b007504a40c400c01d8600c20f01e4010780141c107458410b03510150440f080f513030101c078541c0e02d000201c10700e07080d15000342d58024124112282c0f190144a000c0409001c7c0554216800120040000200550740006005840b00c1c50002c3c82031100ca0003110342c48600c03002000c0d410103400c507400790051600c1e80c080311802c0c000c0d0811454190300c50f41c1721031501204540b07400c10b81d0320014904c0e188503410486030409440c0b54190103600b82c1460b48058507090984082c411301a910b540c000d450201601488099a40284c0483d4036811062001c142021540c801c8032040600d44003c020019039601441e0107590301030b140e00c0820f9227008411101510912016010103031364041c1c800009030180140c00344c1c2d010680b045a80f00107c0c408100b080c54403902c0407010f43e850103550203203074034801904a044640900780380c1d4440a140c4103030000c18004204e0a0303441003211f600401090740582c030a40c050701120354292003100e0640c41c624200ea80644015 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 639093776 1250 639092526 639092557
    0x1e0a05120322060207140f1203040203150c3007050c21091c0b010611190201090503160e01050303040b0304020f0a08060403050301050315220201050903030a09081002 73
    0x8600c030304580e1031942c4510b00c00d00b00145044150386440400131044d0214121030303002007a080891040401c40c08981000300704105144d0704207076001a0341c0d0025070445c030a1000100e00061490780070001543c0c481002503082c1c4c0614030380c007882c0c076158400e809800d00c9144800704c0030400461244094981d070007003050040c01c0c081c441400144a4040c040c120202d84c1004112003615900c60350442d070040c0d0024507161880600c6480c0c0440a450140c00210070040e41048110840100140d034050300e924200e4200c601220a000407038036405c3d1504401e03094400c00351248917403440407009408494201911482d181d032511f0405490344102c0c0714a248460303091000c076000d0f01d800c0c1c803034a5080000601107888980d441041d1414003108171001d4000c95008001084035003401e005081008d51310003004c0d401c0e0301d002e085442d0008080300e035502d0f801d16100600070859000303600300c62020034010102c03600c0c1c1050720300050a107020360244403814020118240380d1202d040c000d40b11040140a0b51 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 639095026 1250 639093776 639093811
    0xc21150905031b10060f1502010c08150a0504061e14060706050a02070b091b0d030c0b06040e0106230d080a1428110606030303070c051e0a051203 64
    0x80c5070f07080c80100280b890078010041114401d001c02d2040c01e00602c000c0c0b40303528880d454035115010141082c02d40b0070a6904101569005941c003001080d07000e4207240500e4034180640c8003181c09228581c000940251038240c2c04a004880003090007401c0704021210751910380c4a1502c1c00307120800c018003941180d03041c01407000041c0780340c10450b031082000d4801030804a503a1200c0c00c4101e0141c8910910b41c0000c110036444002e1109514403010b01a6090840d00665135001044003290010141c828607025001c00d0459680785c01000c0800340c684002c0c8021611a411507020101c41032110396164908035202c030700c82c10501108a00c0c0c80e04590094104110190156603030f958446d8010b0304074000700404144ac5240c0c2031504808104112440030041c1c000e00080c10300d00d4a0001c80d11140d01140c10050160350000840354045501d02d040703081980350f480c016107030003130b2003840c2c010800010305400c1d02080001514900280100202c400140007805805c0d45444256210031020644415 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 639096276 1250 639095026 639095047
    0xb090c03120415021609020901090e01050a0e0a0b030a11030c12030405040902030a0b0109060e1510030f0e060906070f05130b071a07110f15130c2115090503 69
    0x80050320383d12640143d0340c0107940c14550703620513410358108a422035804200c8081d2540d00c640c2c0780000d020754000703d07a15941018001a10010700e4416101a213440b00c0000708000280e0704000c4140d0005001c0311034540c0b940c81c0100c0c81550b080c138414000d00c200c0710051701a20b040500740d64641c1505003c1c510342410441031001510f501c51007a45c1500c585811200080d00b1444201d000f80300310784001500324240140300034902c8000c3d02d600a400a6088000e015546503401c1403108070301410300103070030210b10002c40040e140e0954042e1150107008104008401e0106010307101d004965a8060010007103030303044d1503074000c03102200d00c41c408861092140c0c1c0113140003020050f020303030000004400d186082c0e01daa480c1c110342e80780000d007410b125030070310180800041d2440010300001e030410885119800d0f11039800145140759100da0500800e080c070900b40c0c4100d0160011f80d100100340240c400c140008501c03441000c0300c3e4101500d0121958035040c0c1b10b44203e540d4050060340c6026000318 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 639097526 1250 639096276 639096299
    0x120908030f09160801050a0f140f0601031503060204150512010e07090f060e0f100c0602250f150b06030c1e0a02070303020709020306090105120312040b090c031204 72
    0xc00e0711400b881810645000080c0b48600c0b00004c18404001094515014140f5400c0e0341e28003505600f0507003040944c0741c1091108100340d40c08400420301150568aa800490142c02c81d80340f00b0450b4402404080180f14158000f131099030369004c1d401d10702e003080c050101c800e4401c03243d1958442c5604001441111526203d15800545615000c040562903003120b00c242d01d104da000340082240c6411403103442c02c0140080d12101c0741121070603260301d8549000f40554241100060896030300281c070107408070f19030f050514025442180c03000094010302d0f02d08101e80401c50300380c89050794015560022110b034001c3e01da2408000c0e00160440c0c452104404654018501c100c11400442c0d04100001c072864010345800380d00b0b50b00401c442c070324504000c0d042c01d0003034004034a03a13401081001f02589a100455044440541d0760140c0041d81000e401d007140034034421a078100310341d031080c002402022610385002d1100c220586403081c2c4043d041558603500524029412142400304205801e0b00b030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 639098776 1250 639097526 639097531
    0x121a0f1906080702010b13061d25020a0c0f26190807020415090c050c030910090b0703181401020a0303051b1215011107030605070302160c0501120908030f 68
    0x18000811b480e4100d1001a2000210a480b554030b02d59404040180c0701c18012910300c09982000f0a50700340c24016404500019900c4c100380ea9604181503420b10207108001e4110700c5d6401c46001d03e070150700c44620901482451140c034813050400722608588100031040070100e01318010082c030100d0781004510300000b4100000392400030041c818400940c5450243c085194164440341c4c03009410070340200f0407500c100c1c84440c1007240a20a101038560000300b2a05504000c0f6110516100d019200325116041d41e0042c007918075001c03412104148c0c00000c04008440d01c029001501a1908020001c4101c0e0b110510b006a200c101000042406940580e8110050281e1300244802c2000300000603400b480d040909500c24900704845a460f18003040da441d802460b00b44441441c00a0240d42e0f04028000a010301d956040440d042d18002c4d1b04843e86023490f1810091442e03ca0b06005d02e00c80d85910816001c10040902203e0300503052003030039811a400a911820b5441d0202d2820289000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 639100026 1250 639098776 639098791
    0x120b040c05030303040501050402120a170c0307080f0a1419030f021303110f0d08040b03070302040f0617060102060c070b180f030a031401030f030f121a0f190608 71
    0x2035000200341d40d10140001c601c03841c0524008985410700340306010750902c82d401080c100d030b000000e0400000707a0301c0300381d03040c00001d40305000d490740740c0300d08198114410108018096140003901c0ca400030544006018040c586484039180a01031040d21031443c1f00306984200904d24100300000014000d503c050040c405000c801410904200e040516840380c940050b284807403001c4004140d032900c5d00800b440d1004c140c036182502c6003180d81d07480e030300d00890280150b641400700014990364800e505660081101c668500000344e0388500c051300c0b03c00080d03643c440d0a41c0b8400064501e500000d5007601034801e500e41646131000326150001d0302c443c003070400e96184900800040700f521081241208032132040c1c011350340d00c01c140134024080304c1a01d01001c1090881400400100d0030009003800800d0b0141061107858400040440350580c0c0305e000007010600d00041100000419054090010015160041c24041003c00c2184a0003d22200151038a1b079000c144021031203030507240e4210701f1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 639101276 1250 639100026 639100043
    0x9070909060b1209010b030703080715051e0a051b07020a091a0a1409070c1e0c0f0806040f030e010212030f06090124180f1e0f120b04 59
    0x32603003103280c151201c0340d1002c8140c00c00819000340900c1c4840119030810b0512008200d00603401c000f03c0c1d1542c40c603210242044801041d0f100a11001c0c107068072011a0640c4204113600d044054088421010100b9060042c202e5000440400782845180d000c2d04580350905003c0405803400d04090f030040c10102d0b0040e00440000600c5c020034003030801c150450580c580030b403400d80d4060180d00701040c4c0c4007041d140d0000c00c2041081c1c0741c1c48401c580102641c1340ca0003842c05541840d076901c510109c02e99031050b402002c24018451070814200c181d54038201c080c0d01030303556896103940c1e0b158151030203420905176051103000280503c502000094060040c0c1c0c0c2c0140b1486160a220b42080720b103061a01d000d50b040020701d2400c480800d01620048200303403220006094280c45034400c5455400a008100e030402e420101441c3c07040c4d00420b42601ca00c0515030321480c00c4280e003041c4014100400001440c0405e0b480c024075001004d07581c82480580400b081526600c101c0400500b05864013203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 639102526 1250 639101276 639101279
    0x2150a0c0501050112030e061312060e150403020c030706080c030916030f02040f05070e120c13020d051003050a060f0204170a1505061503040203010b120718020315090709 75
    0xc900780110341c020210b1017405614411281406004103010f6071425201c0c0c20b0403c0f03c0c1205808242c1280281c413108100d03800c0540c900d25180e0000c1a01308050340e602c0c4603001d915111103c101d0003e5100764801d078241d4013109540c500341030b55600319005440c0861186000250000713111006980d201c0c00d0031080301d0740d51291400d10b0064101070741080e100703017841044d00411b50426000b20b480d0f20007182e804009614010000814034528050418807a1001c0312442d480601c0400000b12036010046c200d6880c09801070400e0b0096018240900401e414900054401400143d41800310303074005001d00b0000c3d0b100da41c1c45004110404d02a001c650307080c00040b50290304460804841403400d40144500055424030f04c0001c40350701003881c0864180b408018240c0c40d002c043c00040d22145c1800e80d01c98482c2d01c000790240201444054000000f000752101c0e2071b200007181001c882c100c0100d101381c2c0c1c0707240c90b0802c2a80700031034005e00c0110b0360403c179030040e04015600d1a402882d5251143c40c05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 639103776 1250 639102526 639102533
    0x60105010c060e0a12050406031506080403030c0c120c0b010807030b0705031308071202010b0306100b070602040e0f040b070206090a0f0f06050a0506042a080613050901060e07050702150a0c 83
    0x5c00b00c8440542c00904049401e0103011b03010700c14401589200001200710a00c0c001004005940040c401810991a1003144980c2d41c0a841c40c00f00013940041055902c54580100030424002200e0940c1c0b1002050000101e59801041030019a46c00c40c0d640200c558071504213503440d03030001d4a05040b0746985000c140c0411600d0010b0075003140300d01c4802c403201050000080c01e4540320400184a41c10007428041160250030a000c00c41d2490700c5242e407103803080d0030107100a024550004200c10056410030840065801c08948200e00c52100306c0110307180c03c10203e030350f040200c40e1003126902c0380405c1c0000c103007a2807150106070712910400044015035a128400c1d6481a9043d1f030501c0d40301c3c010300c0b80c039180c54024481e515002c035038080d140703400c15001e4a0360410703400e5808041c08441030108405859110060420001143d01409507040100c969402008a440380300100c1c807044000c0742207a40f1417800c4804568004015484040c1c2d42c001191407540039041c0034062010230051840003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 639105026 1250 639103776 639103793
    0xc03030109090209161215090f020a0318030c1e0203031603110d1e09050d080717040b0a0f030e0109030206150901030825020409080a0e03060105010c060e0a 69
    0x680100c450102c1c04041d18414083c04100c05802c40d61004000c03103122030030a90201702800c1000b0940170100d0446c08404801240c2d403016000444035904150312100704503800e0700103018944541d175082200d65090950043e00c4051000001d0001e0b1b83c46111178007140310070001c00e01c1340002c022455820030455000a26503441200c0c0070788540c41c244c0c1d009041c0340d0030000d0301041c080b00802505c142c0020100091412110760074200c0401d104641d00c460103403040d1681c00141c00c4c0a048203080180c142000d64484d041054100e402602800424041101c0c110072f0303504441400440c00e0400089c0f04003910038024900092080660b50900140000000d018004105020390007504050034000380b49180a4112130352240264103403001000007550000840d10791907080d103100d00302e070140b40c5504480d40c008110040e500c81e0034180f1540911900c0f50040004100545a2030000400e81091544502c0d09108090201c1c200c103004038003140c2c10790042c2d06850800303400c0c0c503080c82e0759543c2c1c0d214 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 639106276 1250 639105026 639105029
    0x7080f0d060923160c0f080f130b1c050403210e010f02030709121a190c090803030a0f320c071101050c0a0b010e06030d0903020303040902030c0c030301 67
    0x1081c0d1200804441503003400c003803007010b042c92010750302c40345003040702042c2250a246007013041241050180c02880007483c0c03100d40303050348640907642e5049032908412003034001c5941522688403a4000082080345c10b0308441e080f080281c0c0c0465504151001b1000070a00180141c0c02e00c10041c00c1a0300690114056058200600b00d0008901140103040c0b401c507486850390108192041050115071900001a0b90403900c4681d8150113004d80d41c9001140341e20900d04000990b104c80040c499034204c101c8284811010302c200070400c83d0358800007195034002c1d9100e0000c00b070b0420400b04038282d40340c2d00481c101d40e65119000c2900081d140000030b18640c522035040d00a20b007105444102c540e040145c1e60441708101519042143c107072102d179080580e084141e810701c480064402c1c040784080c088502040d0304070070300164a41c2c0d83c00c41442400700844046129004145441d11100e0140d15802c05880d009402182000c0c24903030381c80300035030000d8020881d01ea4240108001d03c04104000c50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 639107526 1250 639106276 639106289
    0x3080c2d0619180503180405010b1b071a0316050327120c0705010813050c040506011202031e012c1b0a020106032f091009060e09060a0e0307080f0d06 66
    0x40d55a11150584002080419a00c6114500388001003002c18200000e451180030082e402f00155240c4500c20351500d001d660100b500204e185605008944040c400f6600c1108603440c2c0d19200c440c80c2608981512088517500c5060341850240c240b1030031042c2440d90309554210407191406d03400a188003041d000759803201d20313940c04040103001c5564801803140d0071a41c4582c0255503c07000c2e40e240368452001900791401a1f59a07000505aa84918060001840024011540c1e030424040010112003541d0408001080031800041c101d40d02810110a10740103204001000c0100c4100060000014100000d600242c80003100001c04580040c104e804503600009545461803804a0a14028040f40e00c0b5500b81140722004000203660005240101113074070303800c1543c0d1f00e00c2d26100040c0540298031101e01d4a00c002c81e5a4840260a5001d01d40c0300003202d06959a500610080d590f009812280d140c100303024507400500310710050b0100c2a00200c4850501e02045040804c8440650049 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 639108776 1250 639107526 639107533
    0x110c0f0d0c030207090213050405040b04061b051602060408060108060108060106140a05031305060a0221010321050c030a0c021905090c070c03080c2d06191805 70
    0x42418010821452451000da800c05001901e000e8902a40300c2055100e04104641c00042d000c0c0c4001ca41d10750a40501002030040005040905000710040d8048a08942c00362828030040e6503003080d500424003406944d521103180200350300990110301081c4500b00c0e002034040c8000305002c2d1041c01510702038040440200115851b294520b0320381681a445801405810030b8456044103800d0304440b11007503607040c0580c0e6500c0300b81e502d0000075407086018015000d514280b003122251034004121400100b5150946960510308115a0001c01c0c8002042220400c03003d1151506e090310208440f8030b54180301d0309207520a088582154407500003c4002501c0b5010390003180780ca41d42c1200f40b01c4600360701005c0d2604001c0803540d8810007514000ca04140403c064007002941c44c424800b4692008160751240100e044456a074250401400981c640c040a400510702050400b0700d600800d0340020b080e507031518039241e074010400340159018151603161140760001005c3c1c1c09032034584a000203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 639110026 1250 639108776 639108793
    0x70303050601021b0a091a030a0c0503010b010509090604180c1508010e0f01050f03011503061a0303070507030209040f1208070809010e0304090b0a05090403081014091801110c 77
    0x2030a281c04144002c034003500005040a054507805c0d1401d040d612054400590024502c01c800c0825422034a200c0d03052042c01c188004000c211000c0d0002c858007540240402c0703465400640305402000b60300c5401502d020700041032490250014041c580f80c403020f4441508098548205180d50b5400810a54030003010412209605c01900e50041c07012402100403404c003000c40144000041c81801d210b040030083c18480740d9401e510000401501841010005a4915000000d000c1c02120f42c848092241ca810b600c1381008000c8442d140d6100c000780c170380241994200000580c01410558150700f811407031000180d004540103404100e142c80341009854211002040c240008000810303507410560007000c100e000000392002d9400306c00c800700c1c0700303059003004c602c0e002ca00c0d42c40b450340070190340c0901042c036800000040c0106001410042070580f03480ca1203094010b50740003a60000f00c1c480014442034400441003038105446030000c5007038610b00c87d244440750415052542c280d08400034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 639111276 1250 639110026 639110029
    0x40501140304050c010c020114180405090a05030f0a09030204021c1b020c0904141f0f05060a0b0c1f0c03051b07080a05040513060e28020c0708030703030506 69
    0x502900ca1240c611218a03500d400d0340c400e81c940880743c0138203050120940030f540031a030058013200b00e0070751005110fa07201e00c0303182980d0080007020a0183e001c4c42c81d00002c2603a10324007041600c0200e8008000318039250030b289038145940c0c4004200f07020802c0713004000c40140d59038001442110b01082c1007810003001d0011800868501c0c5010144c0700c0c0c4c0c2d600b180c1c0b54281c1c0102e00030808405c00c50300440315503602e04040207407190a030381c03050150042d00c010100b00076040449003080424041d0810007050715980c08821035509540c2e03d544400700500800500300000000d100302c2071044261104401140c0d41744001c415945007459140782c035048290340081d0306205103a0b0001179008035404e03020041501a6a41c4203008010f410ba2100094000c25940110102d0300205405001d1000214460400d0402001140a0300100c07031050400f180c04012141586000300c861804074403141482d14040300c2c025404031950001c64000e4400c0060302400500142000502913103000c101da1901e01d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 639112526 1250 639111276 639111287
    0x1302040305100b1e061c0509160612051e010b1c02030408070b06030a350306010f11010b0301051e07020303070206150f100906030c0309110d030c0b010b040501 70
    0xd11440b12586031420340807032035442c0005041c29130b802c3e0b5181e2462100d1030010991520a54a0181c2c051841c001079140d00d0b44a60702c400d1041506905550141d00c0e60a100c518030540d81c89420001000380c401ca071000b05d50303a84001c0d0007141d014801c03030710510040b12510321540e00b40d03c0002d20b004c0200308613403c50b081541c0190700c2c0f102110114a90b1820341e440b0b940a000f5290060440502040050100c1c0c400b08145807000341c0041143d800b200d04110207600b160390051540070024051a04010482008415203000d0503050b1210800043c01c0d075800c80fa48021b20104a402e50740b2030386074404e151070a100301d070300032500c6040a41c940b001a502c103216014010705013004560007002008659a4040380c0070303800c0b0181c0c54a8461031806440010542c020750014283d00c100814450000035801c07045903002c0b124192418002c40310b0050007501150700c8001c2c064251500d01204180504e096130740358421902c42e04140c04d0581240d2195011600260000c0c002043d0010f0203000390368106 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 639113776 1250 639112526 639112543
    0x5010504090308010b0708040b07110f040501081902040f0c0305100e07201203011401120b0114030916080703050705060f0f07030908010c020304170303130813051302040305 76
    0x103039400e2020341a2550001c015480c1403013400342d04071001c00c0580400c041c00341150000d203814121580c850025090002408031b5800605100d040312152002581c1054000c2c94100c40c00c070700103040c140e0740c04901110b003240c0c1c0c01c10032a880380e543c1c800410469014440d464002c0031980c3e000415140101820001daa1550403c141944015040010b882c2c1d0248d90600c8840c0c5c0d900d103500403a50b011491901d13004140403503e11000f030100005c14002c2d006246480300f40000da071105890428016440102d41181c400705000540c0701c6001c040740c1044000441d04107100d981160b490fa00c07000d101c000c40402c4c41e0040c107050b8001c80c4080040c0700c0c2c00c10010000d03001c100c40f29407130b0280406980c0d82c94443e600210f40d134110003040d001c3c18180206901ca0081c04098000e00854081c954025200c0d400790240400e0407000391080d801280c000015a4840c1102030060303c03030901c640c1c5415a15801200220400f441041400319840c0c484001882502407014409030300ca03420b520f0014140000c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 639115026 1250 639113776 639113779
    0x6061509081209100c0f030806180702031801020f2b020c030a022e08190506060d09050a1205030a050f04022803020a150e090c0406181503050a050105 66
    0xc01c000b241c00c0758060407115140750864905005079200302054408003039061000d880f1100315072a01c801d040d001014a440f40b5401c55061500240c500c40000601e0811389000b070041c1d00603c02c1e0416144d00c208407042d90481401210b1a0070b00b81c003010f80c5058500e00b001c0021680000740401d0070482905561650f5203280050683c1c0305a07540441c2e520075040002070b1203104408004940240c03020400d1040d00002c2c0c4a040350506080b030082d210070300a403070020600700b003d101d01c50f48400501c569802034500400d450306c3d004158829101529040c2420340d0701f03001c0c0c080041d0000744806841e10f0703803d180340c81c0c02da26460b0a8882400312100101050b81c500d00d403004010040e81c80148499501380040609401802201284001c080d00e94000039000300380408040382040f03c90030311103210521030703a4078400d42d400072081c08441d90065a921819060130b0006118043c02041c104030841c013240030958451b5511205041c07824901040c810100740d584051100000841c084d4501500c0d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 639116276 1250 639115026 639115033
    0x702030a150b1206071206090c030c020c1503010308210a05331e0d0c03050105010504060f1205011103150103050f010f030b1003080a0f02010f11190c0606150908 71
    0x103d400080c1c549200400714003c001000c1740358480c061907544282e02030081c812040000d41d0344404064003c1030b9941102000d032154400c2d400c7c1c9850814140a54402c40342c00c10303030459107581d17580711042d00000340761800e02176807441240e90410514012449005030f1a004a43c9091110070310180700d001c80751480f642c1c1c1c400801c50864160000c0007103260803003030760351071240b280d4601c181e802d140202410f035502c1900c2c207480c40f06110f000d10090701074a000700020041030340d86008010850360103214002d0601c2c001b10041003201581c682603001a400303000089080c2c540040c01105560048805040c080d4410b495148196410310915a00402c6a810110350754101111400e09080b9440024081c1003140c0005a56100040d4184000c59010100903260f0000603000b84c111209209410015032900400e540f60600c40d01881102807091803000c1e140a010001003e20266500e00352410f102e1101f40c29000074071948100001408160701e0003c18081c9805c00a0030140964802142c41c1d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 639117526 1250 639116276 639116299
    0x210305011409010b0d06080f0c04050919120215040c090c03050405030d150506030a090b0c040f062f0706030e1c0c020d0f06060608010909050c0f060702030a150b 71
    0x100d40380582c6040d41c2442c41066210300d0b100b2000e00c0a4403a5400c030460314000c500b481d85c00440d00041c1408461011078090220f950f54605140c0e58601e0308800342605607074002d0ba42c0c04100c050798030b895007101c0c901c1600c00b5540101c1140f41d00746401d5404951440036a007080003406040d1062424000703061a0520042c10a62a540c0e91b80c061000e000c03100036903d500c1c0543c0e503510100c20b0b07002040e000d4802616860321481c01d100820014109a80080c00700000402d018a18001c0b6000d5400b0740100702d2000341070281c2142c00342040e213418103150300030f9041ca118203104030000b003e520140c8001080c04030704142008003960050680440c081d40201660b0100c1b03100880b02180158252810013010005400040c03a0796401d01e00190903220070454010602c082e80d0007550507902c0a80343d0003126641c40c01a0390442c1c0707201c40064499000001d03560024a800d1816050b5120020550360500815800084c20080ca600b4100c690003000300c0e2020603005280100407107544211110078420 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 639118776 1250 639117526 639117529
    0x20a0b06060904090f080903150c1207050904050426091804030203071a0f06100519050c0111030115030203061c031b0318170705010c08072103050114 66
    0x425010304000d20850021684100545403036012415554000e5500c0b40f00c0440f6090201040c0c0c0300800c41c501900442207600c0c00701112914460085181954607444d0040c00c01045000000103054039041260400c80a103c0b0355035805a540158000e660015a0506c014501c0e03d54001024034182c04071414403540520740d80f4a00051441c0c0000760707030100103607180c1c80c04074110711a42100030200300500c40481da0090301040054450084a4602e059680b203c03001c0128010302502901b0010b1000c00001c800c50407111022007190031282042030416611485490a40741900a01c1da5500310100041141c252440d101d24a510460b08085141d4205038010412440d00342210706040e010800d19401090b00ca803505d0b000f003000d000f0341c403454500649401050f01001d4000c01c1504c805061005c14100102c4030801c18031640200145611860300303005540c0c90001c00d1080d51003c0080c4076070008a600101e1408076881244100d031011104007902800b100ea045e00000038074101d5604c0039855 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 639120026 1250 639118776 639118793
    0x30607020118032006010b031806040803130203120c0d121b0f0210060902030403170c040911120403020102090a1e14040209100806041a0904020603070c0c0605031501020a 75
    0x80075014135005122084031181c034010b1508518102c0b00034403685000080d820380c0180610302070b151165007e080b41d0582e42c411a40c1b844161070107800800104085841c2890314a035030000d0703503c054161144017810045c0140203070021605449541c0040c4003c2c00324903407103802c4000c1055200c2003040000307200e04210001e00120905581440600c0300040481e9000300032002c00304403103080a102003030b2601b0b0f41c50043e4006031800c40104032350620211b01c528100c49510310403041d41c0409802c0901d400301400181c59548196a4106010017807043e190f805001c005100724040c0d000940c0e07840c280020310000d111583e200d140403082008600b042c2a01c0c000b03008048030060713504508001e56650000c2c00901c140740c08a94422010f546e036a00541e008040c1c2445040e040724108003076601c002026021141404243d540032180d08000f4005140c02c0000e1508585545480792000540359074500d1201066000400404e502200b04000444400d07907110b0a20003e2002c1c00382c0a01580d01c440e032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 639121276 1250 639120026 639120071
    0xa0c090e0109020703110105010605071101031806020a0c0f0c0e010b0309030f1c02072409021c061107050105040b181009050c03010204030b04021f050a03022a0c0306070201 76
    0x882c1d5400242d1901850310801c4001e640401e074200801440d41d50740e50240050344100400c0342c107000318005115656000b40302c0d400da14074050ba08840302c03410941e1903030025444000f400f018000d906e41902d011865100051304518410036140c0c800b00d0500741d40304c5004405078881943c0d19400c0042000030b02d004015100d48104c0c0521281e20341c80c541c42c09072110f030021604c4075115031000c130741c11051000f070f104160800c140040d040c07041600c2100c090070594003200300103904101080c401080c0040780888503100c1b107006202c0051016141d40b80121245c0c01440207030340a80d100c9082c41306101d0b80e1404560880080c40c1180c0350f080d09c4d041400c0d210f240d00131280706815a074207401c1d0b00f80f00d0140601c0d010b01400400842d5925120301e0700140300c0c04151030aa00034072407150600c8030105042108130910103281c540506000c0684000c0300a50300c5003000d50700203c40d13150380c1401590340400d29511809004047c2c203082d400039091500c1c000c0014145400c6a0400350f04070014950501844c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 639122526 1250 639121276 639121289
    0xe100b1210030209041a090d02331609083d110c0c0609010806060d0b0301021306120605150a05040b0a08160c0c0e15040c080a0c090e01 60
    0x220380e9600e404415040401d40d0340040e4110060300c007004100710400280003820f21941c24110055203c8900c0c456461a0104246026a002082590f42e035000444010a0b04807040d41d001070140c03400743d1030760001c13409545086030b01c81031114181d61140c000c5410300c050014040141041079104843c03000c0f500c0c030040200c010140440c00e030114809518000c03819840301c500e0500031000300f035040b00601c4d4070108041149000c0c11428000d140f804c81d040f11300b10101603503041c8094aa1008201255000f444060b03801541c1d9454000961420300180190182800c1c640e580c40e4179111011b04110040e4400d6003040d858002d06004503581d4080c44040d1055a000d40340e102e0200d204140c0781c0d40305135040140629004560258096032081c003161068056216003070200b14007940c140c0d0001010100104840380307940080c0100b400c48048140c1c040511030800c41200c0301040401c2c1100c80504240d0b0000f0350090421030304013103e010700140f40c100d1786008402d451820702c03480d019250602424 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 639123776 1250 639122526 639122557
    0x24021635150c16021e040c0f020705061201060f1b0506070e0f03070303140f03010e010311060423211e07030206160609021507020301060605040602030307111f05010e100b 75
    0x4c001c0f98071034680c5d8605014018004000341404d030080580f8140030030005000500c00d040c0041001c2c1056000e54060090880b01e04007540d00700704043e103510186000c21010403801500003031446140d0000a03400c0e9004038007a00890410040040104010310126401030352244004e503c2c47e10000798600c05c484e014981103039801c43c66056003005200340000c1004c0d01e0008000400c60031150000103040300d00c02d086845013200b081040c028540164460801400c00186041e02034030034800307240b28020402040507410500c0007118502e2a252120600329541c00003030000407903010020b64641c510070380e2005118041c82e680c005004d51142c451008035440d8010074000030130a03035812100398258000e100f00900031114009001c1c0c0d400101040c2c2c4250f090100c001a014050350458058800c2c0b81d002d1499a52845d2095a004000840040303041c814950380034818080030a400480c40400800404c0651600e1800480b021000d89200d500400d6501c00301302c5001c4050440b800c9001c0c10401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 639125026 1250 639123776 639123799
    0x30f0308041e050105150d051038010e030f210f07050f100b0a05090912040b070c15050a080901020405040624021635150c1602 56
    0x42000345030400515200c00d003107000c1c04000301074000c0c1d889110780d00140c017500c4070800b08007d218249264040d0054002074250703801403015400c248000d00c0544665400c88000350070300400440d004040f5504092451035050666a004a041d01c442200720001c1501107900409107071165814450020b5507030740000788144d410300200c1500c0f04c0103030b880c03900e645580007410080d84441403440c40070402d014844002880413614482c80d8002c0c007014144004071401d00040c0300704508003a1004920344200341d0091502d8624030001c002506013040a0394407101140b801d110501c1c2c01c1d8101034004041c03043c601da645135003c400d8503004603403031400c01070644962050038020703c501d410a640050401c04041103030700074246008151408400e02c0760001d60030843c220b0712105c50700320703d2260f500900710401554a41d800040400716210382208480030f08015445400101c4a07480b510a03000482d06021055514102e01c3c1d000c00155046803500c615607060340000a00d84a00a1140020054 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 639126276 1250 639125026 639125033
    0x60c110d1b0503040306020309060f0c03070c030c0c06030b010e030136060c020c0a15120e07080105040c1d09030d11161b0801090b0c09012a06050c0301030f030804 72
    0x30101c0800d030001c0560783d41e96100c1c01c200d006980111184a458422000403403078002c00c401d000b030710581400d2259030071030b04c44007012180d40959200a500300016403101d840400c00303885801d4010601602d0001d10001403000241c41d02e0000a1100c0c480e91609404002041d0904084d030300c0e05003003881e501c01c100300c03940e1441c0000002080c082c01d030614001004c04119000a60302204000489a9a40d140d40c2e0310310451000800091400c00030380001c2644d4801d1540c4d8000e644503480c1074040c0d0380400d4581300f005086440c200c40603030b20001c1d0310a0070000c580410400c2d02003c1e03414030b03042c8034918142418030360740d2140310b10b40100607603603042141c0540c845405884c02203000c1140c07031121004900f0020002d981c4900701400f002c07800c080001d10a0414400e1041c1c00f40e02c614010607035030f00d80b124034245401020b5841d040c400c0014005c00d150201282e10704014045214401940010742810b800b241c0008152146d05402000184003080304805a204119807515011340320780d68528 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 639127526 1250 639126276 639126317
    0x721150914070f060305060609010f08101205030909180703110118080a230a020409020d0b07050c0c01020d0c0213140711161a0a05090d030309060c110d 67
    0x1420740024020755001045240d003998000e0121905980c0503c800d4640c10f0411046202c1c6d80d690901161800b0300c48140035004500320b6501c0003d0300d9000b481c041c0d4039050070100300d2800000302d0700b80d080003ca00c4124075241810b01e1300003042d111112a5200e501d60407d40d9052280805016112403050011040c4e200d005000c40c1d10b441c10001d2004650344100c4984d44d94404134084034180b441402401d501c200c108161080c841080000b03000c00a25a000d000043c04072010aa070071040440307190740845c04811042d03000340401ea44850780c421040d4441070401a0180010b41150030010040e008140c2c0070350040c1120fa0100e81d0b101c0503c03c1d041501000b414400e544a2101c1700000030015590380080c1e0540f01c03240400d080e10950b44e04940e14106c01c2c0b6580c0903000741705035502c10109110091030050840440d2a0501d00e00e04911100011a46441c0d800d048000903285c101003410803645000c0c0292070409801c048180d94014600143c8910380700b0418420006020141c0a000a010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 639128776 1250 639127526 639127553
    0x10303210f0515010206040305031603020c060c1e0304020303040e07020f0609070f0611100207140a0f0210031b0305060f180108151302060906040b0c07211509 70
    0x5040030048150400c035008003500d01260003203d120181108610300307500100e0701510440e85952040c2c907580d1519460b0100021508a1000301a401e1100800c05a0700700b21241c0180840560592604184520700c0751070019a1800401da05040c402d10005850000954041d00e14060b16003041c4e0750b0302c060407443c00035200040c0300303144201400d1042c0d15a0104030f25083d944545412122301d6182c107415160005803011104041d4800254030101c51015030140c013480e48901c41042c403504400c440e0034541100810306894003141503e8060840c5400c8455000c12070701030509014904410080d21400071050801c8403d1544480c0054020707607541c042c100b50903030020404003c02c070b840a074100c0300070000d0007240460303c145000c651416600d0341403039100b10f0440000f0940c00010741e09102d00e40d0040d03100941c002005000216120f080c0c0c1005c3c000312603680b001070165515200c8003517a1105d000048a00c0c540000910101060f8500c2100001c68401100800c40d100c0310701e030114002110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 639130026 1250 639128776 639128837
    0x41104091103120a080c0304030917060106021501150c0212123103060f02040906030615050402030712020705330c030f071d040213052106010303 64
    0x3489000420003210445103608400705a04550088001241d030841510a25800b07801080207800042d00f80c001a1005640c801e122b031910f206c585136100220804029610314440c6a5000712005004180d07040100200900481000f4920b9500d4080209045070400d4214030030400200c03018410340d1145460500c1818803801114440e0103e0300c50b008007500503d002d03d820510000c4074a080c3c00d0f070101410121180515410025499566240024201c1e0500c0101da03540920000504ca900f034825100218060341005c07803000d281000740644000309801c0144601d105005200b03801c1d911681c0c441d0109240f04e00180c0c0d490143c10314500c0c2148004020f0319250003c07010540c824003001503440000842010b10919440300400405103000031030301140144480c0000031100c5110f0f15045807858440c2a90312128003e117004242660300c01d050700305c81c1c0f1586040420260a0060854505c005896880d41600b4103908001ea146c0c0b4042c80090100941002180b4030282c0c1c1d4803059107003244 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 639131276 1250 639130026 639130031
    0x31005062d07110a27140c0d0e01060e0c090103330608090316020f0d061b03020412020111070906080705120307031e110303041a01061404030308041104 67
    0x420308071214140d0001008883c040800340840e9803505040c031042c016941d000508440038000c96000d0b40c110740e40d0000c070b0b506440d11022694626110280341d40d014a07005080303160b5035000c044030340c01900d180040c00c80d1240e140c54403c010705c0e2485e00c107194101005038561541e404000c001200a00002c0c24005107000411200c8004004111180780402441d80589520640c0c3c499040d0340b010b804840007511a0010081050903240c080b030300144040c4024400300511000d5400315000b60014070040760030a64800c030040c150316819070f82003251202ca160552401d42482d0103503031621100d24009051001059042c2c402a100f400241c000c0c05400e00b003004001d1340c440c002581c8045a1003207a000781d000498140b00203402001300c40d41d0680503216400c44038541010320010b903050000c4402005030f034240c4861b07032240034001503002c0ca014001ca0303a101c6050905a01c5070385810307070094061050740c0c1030745200480e008060301c045903010306000b8500d9545050001c3d8074403031030003041e91061 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 639132526 1250 639131276 639131347
    0x50c0c0a0b060109080f03030402150301060e0f130203180c030f0316050c1203070309060e0603041104020d020d02370503130804061106060613050f030102071b170303100506 76
    0x100000c0607609c030324001c0b251804543d540060400d200d100a00075000080c466a1204042c1e05088101082c0e82401910040608800e4040581240c0043d00c1038440302c1c07984851407041910812401322840011005007415204007090a0795a10424000d000c11300992100c503401c0c80380505c5070f001c080e02c01034044640c5109035004079860351300c20501200405c502010101e021485400d000002d180040c010ba031441d280c5d61130b42d5000d0040302100c1075125400304042e020600300c90001c0d00c08001c0511000d13032107145807088844403011103030419034922450030b070082e411030081401004116541c01c11555a03110048005005d40c81c1100c00342c8031490005e0000307509540310301601946501982984c4558031880c040118a00c14002c403042c401007604400d000500e007a2555000040c0010001440c2000d2995080344185002c0c10408038000000b40400c40031080b010311004c00201c1c040074510358503000b100451880140c0c0100e5004280100d2110304007007210181401c0c7c4820400350740c4080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 639133776 1250 639132526 639132553
    0x50112091a0108060a0b2220120a0504030212030901090203150702010e0c01020c010e04090b1f0b0304030215070e2218051024080709050c0c0a0b06010908 68
    0x1c100c2072280807894400c940002d200c1002902ca00a9098801486000380c1d154181311001e81200205907608807694442070540c1d0846600d4003850143c1030700740120303103400c91103444034400700c00281103a142c0da08000030440020381c08070fa81c90b00091541c0940762641c44800c405801085d510100a400d1b00c074004c060340700c21404595581c8107180a034000e10203403984220442e22021401146405a8002d1103c081c0d0f0b9806001c801c800b000000d80001100a41a1101c210b82203095941503105001024021043c41c2d002041034054038040c00c1c9546503003800d5030000d40d80c8030b29601501c1c0d10340800001c81d601c240700b070300300d00c540900090075858420798240b2401c2142040800310a01c861401c101c94030f8503603e090490a24680041c041d01d050004042c8030780181c0f4411480c02000c0000c01c0b03200701c04070f00171a03030480600031400052840c1810701c65807100300c40000e070811032520810300c022000c4090000340b25125aa102c8010b4405031107040040c0c900d80b01d241c0000045014904009044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 639135026 1250 639133776 639133823
    0x90509210a11031309140610121a1504050f0d1e060e100b0405090c130209011103070c1806030b0403030c050c0d02011b080115051e071b081605011209 66
    0x100c0a81c0c15000201c0c2c581104004003203042d0026100030aa09d003e8500400e481a80b01d0500360800451103000040d080000484044030017803032400000c0041814005801d0201403000c101030243c821f00e813644059126070101d0088480c2c10b40c411001c00d40480c0403c00359400c4004d84480301422202260900d038540006420501000c83c029450800044d6a0781800038414034003000240c010280c241543c2e0100020794080c20504d41482140d201d13020b1403000403c0184030b01800740141059180c1040081d06664041209a6042c14285076045c00840d01c030f80c14154010760315080001e4400085141038581e40103101001e07401380030f000c00260a10b901900703c0452400520700040c0314050030f45081d12a03403801c0c01048022400800039800450090006005070030094001e07003c0d09403444c07504199030341f1159003202c3c500344c55000018448000c14406020700403030070107001030f03600f230451005419105204880c1002091080c00381c40c0701e0142e228082541d00726034103040c00c0c1d680340f03c410320 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 639136276 1250 639135026 639135041
    0x403081602030d03230405010605091e0c131202040603020406080703150905061f090207120206181b0111060c1209070e130318090509210a11031309 65
    0x240581100c0c0f003040d074071a100c1d001c2c0e03041c038502c01c880d841000c41e01d103204411002401183c0542d03803014040b03040e03030f112142944a0b0703494400c0c0380c14403818030040e004051b0029000208000303051000080414518180c0801d48618160b000c42c100c41c0c030300024003c0c06282d80043d41240c42c0a0b03005c0341c8440c001c210802541c4c040e0448003050040c0c0080e000844810710ba0150140c0c00aa0102d44448804070300b100203111420b84405a158644080c40304030390200200311002180700d280a1a555018407409511180300740c00c18103481c10000305940c4a000c03041d41e01000b2400c08002c01185d81c041c00001c820a9520070450b805403821419400703050344010b480c909501041000203c0f80180000c07880d0540344c1d242c080107030340d032654400748248000740c3ca811814465004003c280101180c1da0100092589844c0420b039030501c4206d0500b8090b144203401d8503d4000c100e1000707200b1001c01180c820440a06d403a02c10044184180d5065001d503d51445c5036560441001440d00a5500041d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 639137526 1250 639136276 639136279
    0x1021603020c1512150109090e0c0109050f0307090b03010207050709060f051504090b1210201e18060d1a0f0f09040606050409080715050c0f0a0201020403081602 71
    0x38008440854814280114141041204d0100c8002440c40060080400c5081030606291040c65101e51009040d1035000c00101c4160f03204240f203004d2036910080d0a0000d140a444e0300014460b0640401c0d100d107254043d08200d42e844076a0001103172002d41c1214010780d0407200f919107481c4c841c0b1003100600a00d100d600c600c075803540c202040515088090084006610310104d1400d840d1000b060302409404403015408111b9076100700c0e141c0c8042c00820580c44121200159903a140490091b4a00d002080b503042d580060002240c1100044100c2d100710700d210b07000c21749070300480094100c50001240d100d500160040741611041049030082015001c9000c01928201520014045c2d941050581c0c030b507000c0212304454445081c903407000c0350450b0107400040752013034454010074165440180100d60301e60300041c2440502509090b107d42e6150380081c1031225003018424500ad0780254500011707240c0001507045400c0b0b000350304440045a006007100c1c3c485c0c08484640e046030384152001e0b0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 639138776 1250 639137526 639137539
    0x3c01080609070e04060209130905012703230714010b01020a0209220b130b060901030f020910031203020a030b03070602100b120604050c1309020609040e01021603020c 73
    0x45008080840d10a2148000d032000b48541850440304800c802800351054507001da00300581074540d220420040d6100c800100c01050000c0707d40340450844011985810000c2040e08680c4c80c500f00d00010340c58001d07018070b03200650100c03004101d0649402048000e0807003030000f90b09d4081002d0074a801b1032001b100402002440c04480041e42c0f0361041103c020b42c000303400000582130a81c5a003d0340c01441c41903000726a0451141d80e4aa11014140e9580700c4000321506200b0802640301e180300e9202c58140c0d480d400951455540421840014400a100d81c0082c000245400341070321a8a00071500400c0980c0e080304e2103031010f0000e50000d121000000e083c40307a1460141400188601101c24540c018800b802c10741c60301a0081a41440c0154010355410b9441708010041002e54051405070000e8001246c4500402070350507a095a0305110505006d409409641c80e442074bd0380500e07099801080c0c200e00c408a50f4028440c04000703856880010104100b419400901040d45071000c2e10305 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 639140026 1250 639138776 639138779
    0x30111220e011a190f0f05030105100f0c14070f0b12041410150609120309091a060c1b030d0509010804110916090f0f03020d020604050919050601090803030a053c01 72
    0x121614480ad018003900000301c040c294403d140700c2d0403000c0140480d07160107401c81b0301990300c1c124a00d16104032a0706640c4502c0f01400342102c0d5060728402001c985580d98506140035280700103014005102520070100442c200007160300c10302c0202020f8000e00410816030f900703007032403426100003070042c9400203040e00400705c0d0100ba003001c8400c10b80d4250700e95950143c680340100000d82400b100c002075800014080040903103a680103044d04410010280c0a040c2070996401081003885142510a520420040d4402034200c02100c00c0104203181040e01617899040002004158401081e0400c61220030418000c15200c1401400185560380795106a9100703144428a4403c1c020031082c0300c5503060802c0145004036000c54030510103021142019920000110031541c210344002070300610b1132624101041501c91644e1114003402c00042d01428480d202d642c0380030007005100481e581d2b03004200144006d41c9480300001c0004018407241d001608101c0c9440f42da52141a11104074000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 639141276 1250 639140026 639140057
    0x1b080606010e090f09120f040905060d080a080717040f0b060f0a0b0702120f0321190f14071116080a03050d0b030111220e011a190f 58
    0x20003801841259035803102840d080301a00040c16103071740b03841317052120301c852034106000e400000b2583d910591035030302c5d082e50041526401806644505403550301030001480310030503108101480d141c10b44842e5500c0c0740503900c08011540c3c4020404850080200b002070a14500900c648200b040e400680c50300420301080745010b1081640c0001d204909000c000100c1002d401d00a00050250882c40c000ca40c1550412100d8030408103160800554051620265800c0180100c45100c0c000e0461400c04c218800b41000e05a5800100c0e444884051100307030285c1280c141c1c1007074041203068501f00600c0107000204c0d05080040380b401024050700300c00c0a1550180c04031110b0314090302c0002041e80d421185548001c44000c0955500c3c00c11040a450921845910043d82d2044030f6580c55040c04c5001d004805000140740170100500510070300d80316a4005d41100e501c050030003654014095075071658000e1b01002005a1340c01017550007440d60200c80b4241ca0507072519140c44059480d403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 639142526 1250 639141276 639141287
    0x213090e0c1518150c0a0201110f060c07020f190603060807120b071101090803040303270212010902130b0a12120c0204180302060906010801020403030c0f0503071b08060601 76
    0x8a8195034803010f0188103210b01c2e415002c60010500201005181840030340924415004440ea01e0700d25841484a4403c43d41c05c08585403408400710f00070000c2050324400d142d40c1c0c0400400404101101040e100115112007881503241200105085500c684035003411041d00c8403440340400003401d00000056048011070840180d070b4040ca01040740419030f80303441001d00c20281140c81006101c0980c410078010a1082e208040d10540d01596a81005c2c1801803d8403649448144280d50784444150550303038250090400507030668120709640c0485200e940189103102011750440840d80d22076070800520761002d09a41030884041c4400764030340406240056a403c030003440c220100580d920001c0c002c00994680d01c4c401800820f160300010f0902904001240c41140075070712003c1401740311102800a18054005c0a00031030038113185880040c06e0081340354001d84401010f52841060180603c112800301c0d07000b140d400001410741894110041c906e1048803000d0054401145d03d561284 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 639143776 1250 639142526 639142549
    0x105061e0a050f0a03050328080702060721020a0806040c03050c0f070f02180a3c0f05010b0a080702012a02011b0c0507050604030c03150213090e0c 65
    0x281c0205034103818441841150102e104000e54031012078040040029010401407180400c1001003004a00d24090b0b001086503071400a07034140b025080400c55070a030b00044040c1c0c048507600d42000c1280c03101d20000c809003203268000e100d05000203150441e442d0030180c500e00031700054508200800d40d00340c00301d0480c0c10581e500803920070104540001c0005a5000e009a203009001080c05030229900055024050529000080860100300901425244501c52031840f000440c04100c0400100308003420b18103c5000d240b600d0250200f00503481140e0100030341401100382000a961503a4480b0b0154221103840c0001655417000204030b00d00c103009480410030700380d8400c440040400d007090065408021010b04541d84e42e41d000000302003110a0040001054a59100d100d80e03a080083c01c0c55040c2c0c0003076000b000c04010400008a554045000304c94001c450154080c1000780404064420245441e50300384c208000462001090381c003600186c030141040300d0091041505111003641c40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 639145026 1250 639143776 639143779
    0x13090b10030b310b0604050a0b0a05040f0204090507111b2202070c0b042102030a0605071403191a010e011b0c0315140f01150e030f0105061e 62
    0x5100490124900320003024416020707203c0004080e506000c3e0b6401c00b040c10a81500e031100401d0a016107818988180c1d40c2201d801c69082c060011940c0104158103000d105048c043caa0311228042a804140d060782e001d4091030700103100b0b50401100c002c200c085022440d0240307000d680c0074540c1c4648800c0e00410052009003000c4074107010040300b40c041000040444620a0f0200107480020b10304442c010040c1c608485401d845d10b042031401d03100c1004910204800711540d0000e000969400100b020981e584140e0114079551fa51b00c0c21183e60508100e030102c102004420321460304103900c113503001152080c80c104a490803c1c0041c07a6440c582201050100348000a40c0d10554412a121100009a10280805000c00707a4504ea810b5035990303c162240c48100d9181141d1102500400c1e40300800300c11000031500303001140794100701c010320481c1c03441509640103108050098200c0411440002d09680024681c045441c0c0a4031044038443e00c01d400407248400c10b00c80900264246a10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 639146276 1250 639145026 639145043
    0x10e0913021c08031008010c050a091a160f0204201204061118031009021509041d060601090501050c070b03060303130b0a030b090f13020f13090b1003 66
    0x34641c0901c00d4148903403100c55120030304a064500840e08035030040d0700510b03000110444442c541002035084a0b2100c0c954810420100007102c94154461180e4007982ea40040d10084c0b408000c0b0301208038496098559604143c061500003404011030142c45100d000340c0b0103110220101100054001e0030740b400c071072000070034014018492105994240d00902c602000162842c0c41d080b890443d0b00214113481c0090f50064070b005031030606200715484a10002014841c0000d1507002481c4140d1601e100e59136500040b640c00074640d0386410102a0210700c0d219424030b0301001a000792100da0845000b40407441c03903030b000211544140308540307121900c0c00240c0022070820701c5910f031036800908101d6052109121803c0100c8100711002c0040035039240440c0c1c0d500031814094280d5030501199031003065240200721000081c2c900055103c8200010681d00e100742d4400205116043d000160f000f01101409009924451740b151162a0045560304d680382c0d1241513a44452826002c014004003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 639147526 1250 639146276 639146311
    0x11030103110f030601140a1401051e07080304060f0b01080108030901030c0c02030d020a0302060a2f130806010504060806130311070308031e09030702030c101709010605010e09 77
    0x554500e600000e480e8014041c480d03500381c500000303140013000c2e0041d00d003401d03800c2d001030b01500e000f451000050002d0042c00103054030020000c1e01900a0300c41e015650b4031403402c0200c440c0340c541d040303442e031a5102c269a42c490178036083c09001490701d48000e2582600e00401440d8660152403406c1c102d4544000030741c83c00d20007000440c090060020090141706039100203d0050340d040c002e04405104030ba0003030801c0c0303540d414020f02d460805040b01955601e0801d2991000c8402181d0180c204c0c4941c90f0000c1107607540000500f180308000313521030140c58800d07020a06e10000300300c0c0b41c100d580864040c850a5140e600d03260b10350301c00b916401508801008005c0000c0d00a00121a000e1821001c0c2d0340c1d0143c0d25112101d50354021183c041c100b0400b040700c00040d00702030844942080e818402141428001c1c0d000ca980d0b00d501070b45e094484c400341030140c15203e104c0d40e5a00540d40941c2c010011a0401d485104e01a00050165902150880b4103520340c0b42010500ea5104d4010040081d4942 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 639148776 1250 639147526 639147533
    0x60702090a0b0a0b1b06060108040804030f0c08012f0412021215090d0206070504060237030309050705010c02060d020a0e0a17161d0c0c01050408040e0a11030103 71
    0x811107102c60030307000440c96200003070300b41c06040030740051340b12144c0800604034000006400d0410080210381405054000d20011601e182c0036101540e0f880303990718101c010f050030b01c03010925003940241c1e0307d50300708081d07055200c20803000c854080c0b20402d07007000e40740c40350300303030613080b40a1805000613410322100e580e4058a0095400486c5070350b0034003520751102812152550410080b0381c3d00c2480e1b4040550f00208a5040022030ba00c0521441c0c043d00301401c2450094a540c0d14108501c01c0e41c0341401c2c20000c01c4182c040c81503102000c0910083c0140c52072071301030003400c6854400d54060140030f00c0050154041c1d000c00c6030300d0b54001d217094541f00e803044a01c4029085080c3c1312081280ca03040311b00e4a501c2c0c880b8441e01610304075041c1d044100303440b00030501d040c0322201d09039036807025020104104000712046000021844100151a5684010041481c0035030402144c1075801d080c144402c0c004004020010f580340312244031100c1c2e4501240e001134800701045030030382c1c40e800c00c01003010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 639150026 1250 639148776 639148781
    0x90d110601050618061603050304051b060d02130b030a0e070e06010c0b0a090f0c090b010c0309090c110a0c0e01060509030c040b060d110901021e0a0803041502030a020d0b060702090a 80
    0x4031341d0010482c0d0304280704540800064104804d044003c50300000520051000801c04c1000c0d001e20038404003030610144000c20014060307400c1340702c0d8040e00450192054078140c108032015000c0e900480e40c0300d00d044c0c1841070103420709120354001070080f1000410108806d0514610401d03060b1940ca61200b40c681e9036100c04c071801481131000980e1103048900181c019428084040c1c0a0081006582c0c1442c0d0504200e4204001c0d05051190f05a034410009030410103160031142c034420300003014821004152031000309201c07240755034052224800704005542c2e41100946201a5520881da0788545041d00c15205001395113915a01c0503c2801c128582504040c1407814082c00850a040c42c0da0585802d81d10011b00c4030b1011280420810b08550741042141c101c0009455982010040c0444080e203559081c2c030060850800000011f051000900d900c0b1448918a4402c645c0d924146a129001f5045803c3c8100c00038188010785500f40760900a6841042c0c0082180325a52036110f0a90300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 639151276 1250 639150026 639150067
    0x313090614060a0519050a0305070305040b040b10030803090d0e090c070b0601030b0d0c06031526010e0a0b0108060a051e0901112a010504030c030e0d0605090d1106010506 75
    0x40000c05c200e585031035107420784400302021094840302e0b1282c0c47e03400054140c4000808071020940b4110403c004102c1d240300039074005403c000d11400948036a004640f1600507500040c1083d580001801900c0d840001d00011100780c1e591440e00c0350038010100403003000e040d260741ca50340c802070004170701107020b402500e5000f9105040016406210001255900780c8002090f188280c00241c100318082c1c150140e920100b1303080380600215400c0500d00388004c2290881c00144c49440c040000c2c1c0c500c025440f95403182c80000031210300340114500740d17020b102c3c240140c5030140034481c04111401e03514050180544010880760301c40c2078105e4500c40020000070040034096403588010300d01078810000900810b80d2604480080214607950f41843e140e00c00c1d64051142e141070100004658841010b281041c0d05103040d08061080a0000b0903210603884040c0c0755a03e04401d0050b540700c00116480d101015885111281d043e521030280c4510b030911945401050400c400f0440745035110b461003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 639152526 1250 639151276 639151297
    0x105010c170315090f0403020709020412062007050a050106051801050108040c0510030b1c1e06090209070507030e0d11130204081209131802040f020714031309061406 73
    0x506203000f0900080e032404041c0c5800d400a4124421701045c140e040c0400c1d0302410401e04158901460103190722024600c00001601156450003046464810002c030120710325030000d0000e840d0003890034050340310074036031904403202d41c41e10301c1c002124141640c504078020010021440143c0c40e1000549a07550020001ca138129850701c40403455658104480e90f104801d50340c002001f145820601805100c914441d403c84101138034214001004c02001d01604881c12203d15503072a0545400405040341e810020351010003041003206081e4810050000c041c021f948a041a4060f1002e1144944015070042c042e4510010400500d092162040003a10b6004900500c1e1603a1a5907590034100340e11402c00180710b00080c50200d41c6000c000240030000d030010f08002400812241d00d030b0340162100e00900468841c030303034500340c004294140e9004a41225031180141c440382e0301316489030b000c900700404400103030401040807489032240600b07603040d08900e002e8241d2001d081000ea5000b090004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 639153776 1250 639152526 639152551
    0x207050a03081c0f02040819050a120207031406070314060d1202030903030d060608010e1009111c05180c010c06090c1d01090617030d110408030f0408060105010c1703 73
    0x8007110f000d5403180081c054002c03040107031102e042110355800e21280000300120020350004002c0450404030700520180c0d400071424034005803004069081482d05c0d88003801801550208181c051000b160b038a200b0358032650100300c1c1c40903904455003000340544101d0380103160030440d840010710f01d80104a80c40d5039801100d04010034080002d2956000414a0b00c15541b01c0a040000c140c0180c1c48034050440c07620b00766000d250051044941d0511441104180c5445500e00ea07000312048045a115016114420490603007424510026003015580b2100c604031410342c04503d48001301d010100d00105946100c1951803c0d00c42e04080c01301001d0a507403026001d080040c20f407003040c51420004512001c141c18642c50310b01d00504444040d0311241e070320785a14207110000d440c0801150019602c49100240103140da503003040c0b55010340c0d0401038217407100040e0001c440011002500c2100c6000c01107070401ea8850004591035a0740d950000c1002041800c8801685994405540d00800604e0718 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 639155026 1250 639153776 639153817
    0x503071506180204030c050907020303130c0906080607111603020121020412060e060106090b282f1e01200a080601020a0201050306061b03040f05010f0207050a0308 72
    0x20400790000061610306554002020006c0013621a1300d18010b000454640c020781c0317031504d4044c6d101c0c40020001a401685502070404010403500406c1c042d0080c00070401125444044c043e0b40d80400b036500c4004034030306c040c415a1240340091070042d030301400ac40e015991403031540190b41038900004603083d525070214540305c0464080c80a88020943c40c180c405498086081010894003007801d1035003550080401400300c6604500c82c0c00840b0000702a141c0e40e615501d1150790300783d030a551003081a20725201d001c96041e80c402c81c0c0c10401c8158240c15506039059040848441c1280c0310710150941048452451401c464000d14102865050000c0b83d08800309038515007410806006503614071000c504420120fa205028a82c000070238001007007000d0352500081d200c0d01000f450b0314070074140085c8905e00b9031030700c40c13140396000581c00480b622180c40c0c000c0092001030038013880c2c0c0003d250402c0b480d40c2503c00102d0b001141c00c0607241806260031615651580d81c0b1800203004d048800200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 639156276 1250 639155026 639155039
    0x180a0503030c01020a1412160c1401050730020a0903082b05040b0109180f0f02013f0212070804060b0103060612020d110c16060306030503071506 64
    0x2e01c1e0019400000507078401840030003420304001c503142e8400d08030051102e5140e002d8100c4600f42c014600305103014845502003000c84d001200c541d0700420452005800c60007400301500682d002d000e050301c905a03031004a5182c900035006c01622540c110a0002040005900b503500801001d1942e14113082400c0d01d984607014142e00c2041b071800d02000c601492020307204108411551070011990034000c80c2003a4a90810841041c01542c06c029a0345041c001900310f001043d0040c5648000c402030307043e49d242000c8948c6024460141d01040c440c0990002d01900e4017030300c1480004191150001c031920252000341c6802c4640307031420b8160b08000c04031172aa2284507441c464080f541d00c031140c80c48c2c146009003d0343c19401009051500303000c404d00406400c12440c4030840d506107001622030880d204003001901900b110302c500c000c40040c0c2c80e40c0d80040400c60f41301035560500d40044040e641e01c0110100d540c28400909990024015240082c580350500340c6094608200800c00948503039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 639157526 1250 639156276 639156283
    0x702090604110c0307050c10090302030c100519030f0b06040503070e0a06031a0a06082103061c03020d1706100c03110f07060306080a0f080703050c0a0602030103140c06180a0503 78
    0xc0c0251502c0d48030341042c10180c50042341c20b00f991320780d070328021059610b15400b10f03668000e02618184206c0350b4105103480d040c0310f1b1054a8a48682580802c0c0c2100c080c1c8020380204815583d58044074100340c0c04003290705012080701c08480e8041c00401034903160031500c00c020300015155441c01902d9002c000040361021700c03254604116483c0070101402c001850404a80040e481009103400c9407100e100848a40341103201e8802036403008584d2a0355103c005040702650304c0620980d07014817000d180030306600040700c000401550702d13140300a41811662a5600c2400c451007036000d8082030401d0007140c40f55a401c6c042c03074030904150308a004280003442c00c14800f6014148a03a0050700100701d510b41c14003c00340105400ca018101100c3c161300c0703404280000a070003500003040040c800003011721500440307101010400580794581d0081c64000003941c0f00388003c0c0c40455402c450101c0340380300031031003240c408402040180340020072003280071698995010103503c0140c00310b001402d0f85007032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 639158776 1250 639157526 639157537
    0x1a16080403112416080f0d0b1801030507030201030b030a0c080c1305090a1103070b040b0318240a150b030901060803040f09050a061d07080c0702090604110c03 70
    0x1281d0703000d06040701c5424443d9080300500038040118200e410005800140c4044880440c0780740301e81c031021103660a113140b440c481c1003c02100d0610000b00844401c03020350051100e9003048070700005d1554210703107644074208203000103091500151030410066010b54440351f1414009401d548107410f00781c6132a5054000c070303841000d450b009001d05168915210030480e034038010781d103010450743c204410344654031044108014101406100d923415150390400c0318800034a456040305603540e4507044560380a40081d0390001c01c1201020350007100c0301b404204600302c040c0c510300e510700c0c2c0c0ca440c841c040a0040007a20304100035988041812205c1c00403003980020700818400f16660b4101800024212001540a02e11a4006000900541e203800031040700310b0f01e0f145404100d5480b50300405004203a29480121038074580140c03c10307800c4406940341d00c00c2e046a11141000e94849220700c074103200f0a00b0095003d500400014100d2805a002200c003082e00d0000c0b509040c09101441e2655114 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 639160026 1250 639158776 639158783
    0xa03020d0317091b060703110303070509150a0e010c0602090604060c020a0504060533041e060302040f1211100215060f090c0306040f0c12060f1a16080403 68
    0x14402060041c500c035402c1290040002802044005100914070510558079100988211000910320003414800e0600e410b4042a0700141c990328100341a0103080c90380590a03042c01224400d50b10b9003221800e5041d0341907a8a151120381044400000441e108105164201c40190317080c0040c448640301c0f04050406000c10b034440903000b500314010440f402c1120390149204a007010028004d54032013a80c0c8085450380c40c038505c00c410482c2c1403060300c452048814441c081a0110300081e060482c40343c42c5424210b101c0c9070b02c00240c1c03921822410703070cc5240100943d00314640b41c10400e1904546e08a952903000c3e032649800100450002100f0300d140241d100d0040c2d00404c0160310310103c017410f643d00004200d81d10100c20140700b022410b2224000e0124040e207401100281c0740362100d4024a00da0400301c503040080800d09800902003004a24480351800d10b80385010511070b01c22010352060b2842452013103070720128101015a180e00c80b150074031103070181424100c0020b140d9000750015510 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 639161276 1250 639160026 639160037
    0x6060905010806041a060d180b071706031b030304031b031401090f03030c0e031510090b0a0311150705030a0816080a05060a080304030c1403031206040b0a03020d03 72
    0x5030500040c142180a404a40704600d82140034901c5003004500b41c0300008244c81c240e031111625941d540080c030ba00250020704e07000021f800002c120008825034441c000940f6684506803039000d500c1030200c800c4030700c1c94141c2d025481042d1200c1040110007002e41004040768549512681c9034900f50701c0d200d00821400e43e25200a10820004140140d100c012200080140d692035842d815081c140c038110117001d01d903450300d107030000b6842180030044c0c3c50006822280c4451424003d6021000100d41d00c0c50818001ea8003c60101c40314041c4c114a51001041d4015450035900c0d13503d032030240c0e09001c3c0c0d0703c00302d40d4044829100343d60b00a4041d503070084001e1600c0e014030080c09004480014805130829622001950b6441c0d0060f02441e08035110b100002403d40c2c030040031907005810b0307411a200034440800c0020070130006458440c04e4584680100c14882214401d05990340900c80c2d0056070300315010006115820242e01640d510903001b008052407507541d40100790014400841600001d8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 639162526 1250 639161276 639161279
    0x51305070b13271107050d03050a020c030313112403100e0703020403210816030e1f0e06070f1101060506070b0412082a070602120108121809070201060306060609 71
    0x2580c1c07140c0c1226041c0200094a0405c0d990743d515220340f9490028803d240d41c85001ca160031440b0340c140e0301c140243e50101d0f80d890510040c0c007a070040d101082103601d00a440c0c10784101d030500380d45210a000443d48450180908004a407960750001404044031181e100c00019207401a000b03403034010003403a240141c4d2103003541015400840d0200c8222620603402d882900803e42c0b0414180c1d20800505e03800c2c1c09050b62520480142003078211030030181c4140108140c000c1c00c83d520b00b4004142246c02008251140c0703044688811b0219007200c003240f01014180601030048100000c59101e00707000041141d20303031000a0340e54004600a80300c0b841c0480030801041545009004581d200d1300341800d803858035031000e04c1c500b00c81010010040010546001c40490940c0c00d03100701d194009025516086a0b06040300b10543c240b0400c00300e032240302480e90740c00024804540000c020b0091504a024144040c031201d0000035105004566132000b0003c0810420b10410001d03000703650f034021219 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 639163776 1250 639162526 639162599
    0xd0f020607050a0503220204050106050408070807050f090711070303081501091a0f16060b031203130212030c010f0209030c0411181c060c03051305070b13 68
    0x140c000c201c0c00c2842010000c402120f9080703c192903201610070000004841c060010900008502c2802508a41048002301e06540c1041c090300603503410400329401660380b0031229580301490b1007610340001485018561600300084240d034001d50302d080440224060407000d51030b01070981e10941c00074400300103100140c04540c0c0f240051800074038001c1486400c00b408a1003200700140b031301e45030760340c002000070203c0415425504003441201d440c0e805100709082090240c130280e00058400d000d20046403d2142e082d0b410703680525101c610101c2d140c81030b94280070b513102880484401603c001d000310b4640071424007910029064510000d61030303010304000d0628114100244038440c50501886504c0c0384e802c80142c41d4018200c000c2c5942018888001c221800304405030616456005022902440f61a0308280454000c85e0350802407903541101384506280f26040062994000a000304800100c44018104a039180044458866964002d1032503500101c2c1e202100c0b01e180c480c031101e0b07d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 639165026 1250 639163776 639163783
    0xc070e06040b0d03020d0f090b040312020106050d170f09040e070302010f020a02091b040807120c0e06031519150e07020f190f020907020307020405091c0e0301020c0d0f02 75
    0x1c0c010103448080705515142c4c0c000e1740b0384e50b000d0000410014038090500381c451081c0358071001030050a80056507161207051105056040072101c00140d820000002201d0a00c1c0e6000d828058010004d0900c82d180d128180c0c40d0340d8130409a8607071215040c40424403958070740c4200141c80b6481c07801041040e00d1840090105030300180a01c0039500a0072000f0b0140e22410f0860b9881401165680595100e1241c1c20340d0300d0081c2e40103170605220f034030001304444a490b1011038009003c0c0101c10901d6603202c40c1c0b181341041c12503100b90160054220904125a02d2508680141c075aa80103902c80361085015412512801c40b0740e103018074140801c02184401e070905e81d4105169101a1241d0312810f101e8030f91b0345d0321020100360f8500d840700b060307000c1c002d171440305074a125401819080241400c0388001d5803038004d9242a803059180c440401c403010780008002c4110018681c20150124411005403400160662256007554081015211521050003283c0e001a82ca403a202c200d0214050002d26 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 639166276 1250 639165026 639165041
    0x6060e040b1005030d0c020d120206012328090e0a1a07020304060c0507050907030209090a0c08011202060d0c091805040b0112150e0d02190209010b09060c070e0604 72
    0xa5a000c2040144034a4030003041117224045281042c0c01140104e00c08990580d4107148060080f4001c401e22103012035001ca802d604a0f1648134040d051030b8001d0b51341c3c0390021801000c195120201020130151640101900d04690403031121031111b595440c4800000d44040800c03001003a0040c1d003513101001070089942d00902c002008409140c94042e80c082d40e288668028501400380f1f440d034500402c0000c0011402514001e031081c0e21038280b40340040c01a4002540c1d192180c0100030004202d6001351142c41e1b1925020b42c0c416510b6441e00d20380c828010341e155410703a00a14200070030720f004006030188001d0481d0a0b07940019062070006030100c41c0d56003031101c00ca140d042000340700114803c01041419500d145400d030400d0881803518a284a0440c980f51440504182110343c05600c0031400401c00031032502504c8000f007501602e11306000c0c02510003940450b40b04018040c1c1c42d01a80540181c400181c4824500182c8281042c074060725540001120ba4a82d4100702d02400d103401040c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 639167526 1250 639166276 639166291
    0x609100f051e06030f0d0804020a05030309090a150f121a01150305060111010e0a03020706170a0c020102090a0e01050114030103200105090409030c0204050106180306020f0706060e040b 81
    0x410380c1030000400c02c080c0401c0003498080c4548101050b01581c09004258600400d182221000d501c1214050800d6404031010b81c4034440c200c00002c1e95090110494030048002081046503a0b941248100105000038007508001d03c1d0070000720344e02c000240004040c20005203101e403982040e00d07103514441c06003580d09070200c42510041042c01000c1e02909100403450502188503501c40e801240c055070300b50322201040d03080100040c11283c0104041315864040ea09071102c058603070307005861105200307075000212001c00c00020031500c1c1c290b000341c04800741c40c40054503241d400000224440600c2e00514210300206004020320342c0c00040d601c0d011200109403904541c5107032900402d2944003c4000c500300a07003210306907d68400d504644071810b004200b04980199424000c0201c4541d940490159241000204110303001c5c040c107032195102c8072030040140d42180ea6041c003a410048a140307501505021000001d4041c1c0070341800741c058042c0000c002e141c07500f0328807505130000d032041e03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 639168776 1250 639167526 639167531
    0x212001021c060807031101030b09160320090d1b0b0309100b0609010507020d05030301090606120b090610050403060f0c030b101d06070f030c030f0e0906010305180609100f 75
    0xf04003128000c541081201d8110400c01c50400041005030060800341d84010361010200c030070060340c6400e041a0600c83c00315660208011908000c1d0242a550509090000c1540c10310240f40b4901c0c00590b100c3c83e051085c001800c030010f5540d4403e07005801508200160714022080054039501007054040a11a00200b8000151024013042003031189100460400000190440c203640701c501c06942016030100841b0b540390b030f583c3d60340c000400701400b03107100140030025003400404141c043ca4000c0e04004140e4500da4851a042000c042900e07080c803c280300080c840040410158840c01421108010000c80c0f50404448010101c1d0b1061000ca48155031030341c0b05200c0a940860082100d4800713031816041b20814200141c001d01484500822502c0c0008098080540c0450180d290318407e80320303141c159240e1481514803400050a0a8200700f022002070722562080c1c0000e50424551000c1d014448244070b9610700707041e0100c440030b03a2075011a003c8030f50300c10a40301e11019402120000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 639170026 1250 639168776 639168779
    0x13060206091f0513020d030e100e061b1f0614040207032012040f170f0303060d060207050d02150a0c02100e0c1e04140103212001021c06 60
    0xca095940070703600c0188102d603440b00000c000d60302c1c00c80d6810060383c005100c1040c418036464002c18405442520301d001da4408000c542055005980d041c907070444c010402400e0400c84d0001402120030805c0300d41710b07441034072840402440c0030400e40048150715440030610078100020343d0000440c89400c0c80c0181d104000d6031000c00c2d4404112003000c41e09417100328100d80558800c6207404030783c0c6080c0702c1c0704000050010700070b040f0300c13006021074041d1aa4404401002d10406484001c0c0d010000070310742003040000d82e149000d1b86078807022442032000504064030f5032038652518044031000e40250303002410180c01d0f5004a41066408071840e18140030f010455100252540825448141c4480e1507a291000e03400c0248500a1f08181c044d00c0100c955904400000441041c207480501961414106802e140740308101b941c1603d40007206600402c1d00400c250a100705122400c10030062800300c0880401c0d0480c0106068240e590009600c4040d02c1800040644107102040c5006103050030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 639171276 1250 639170026 639170053
    0x220c080609040809010c08040b0406031a040e07060c0602120906250e150708030f07180303090513060503030a12050105030601270209040216050609061005100203040b1306020609 78
    0x100d1344203031000e18056500307a50b14030b411074847c0a1a0000e001c100d2010030041081903043d0b20074101c410304141c10070350b4103e03a80b00344002c07180300d4032002c1900c1e0030100c000c0c0415802600c00e642c08074803a01c0018034100398800e40f108604001d0301c142d540d035041075003400503203103041c05c2401003194825220f00b0a10b0503140d024002540200b0518090044074808030669500501901c0fa40c40d04044840c0e40d81c5051003500d42c044400700e5011021900480d40361070500c9210700c03201c1c203a0794542c40e00c1c1034450800d410030400480c88035510241d544c55807404540c6480c00e001070301e00d541c02a15141d45016451034030105492058010501a40c040c50040205603005501c0003420b601c0b40107030544003c40c001c5240060311550388ca180d002800021501080340c40c040f00003581e01d0003441501d90136200d41015948810b020b550170035191101320000d010394540000080d040c0c070082d0044a15182e510312020348541c01c00141c0c120410890481044400c0e0103115295200c004900680b032080540d05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 639172526 1250 639171276 639171293
    0x30b18060303032e03050c0108070c0b0c0711041e1808030c07030909050f0414030315010509031f09420b13090302011a01020a0b0402220c08060904 65
    0x30036040c48088091142c280308a0404ca0492038485003456554166850b824015950f454000081303000614490003d54891312a0682e4200950f100c1c24025403600d5101c40d03c5100e8104980907030b04100080485c0781603640d540706203001c8043d0600c0200c0b10041040c0028122141200c0f492a0403522098650004030a40b04582c0e1042c6100700c0e454903a051820201d44003425600645a0913140401340b04a0b04009001c2030300c564070030070744803a03d02542c0d0b42a5841340001c2c3c0d01d280c83c107025055200700d0303580564050059110040c1c00c980c00c404184902111961400c0d203611421581c0e440b0b018140400300c40c016070091000c22402190350440b10b440308810070903003624000d070f90006400704c0d80214542c2108403161380042032a0092034107111200e0042215042c12000340d031a005c0642140e464600111039a240c05801802c8041000e48030100c0070203000308100da1005d0400d03846c400300c402441d003510768000c1041b0005080005004050404400588550700c100c01c58401c100010345407a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 639173776 1250 639172526 639172531
    0x311040b07060507090512060a0c0c031e111501150207031a0408071a15030d0c1514180705030c0a121103100b0405010b161704090c030b1806030303 65
    0x10b0000680d940c4081045418400c542c0015602c0030203c4032440c281d1800085c55070041c55043c2003048140280d420a4400707460b040401800f1803d20100c45142c03440320b0940180c0c0106c1400c003070340b04814582079141010100c00000200704001070050082c0d1b4005242e81c414030103a4001842c1003411a140c901420a808015200140344140002c003044220810380d4945540295202c0c2011840340007003409901c1101c0540198444502e10078541c0340009920301641078a89505c0d8807812181c4442d101846200c41e0050780a499403055039508420300d200e188940200c810080017114044142c0d42028101d90000d0322950bc280600b40329507440300c100100b03e890f00102d1252500051900703004000301c0015450f410b0041149480e0301c841c0769088005441c43c00c680800c076983c1c03a108803031564027400e000030012150401440c400259043c4991003204203806456080945d01c0c0c0700316080d2030780380c400d100c002504c42400b02a1400c000283e080c0d01203800c860402c0c1d5107008030119a490200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 639175026 1250 639173776 639173783
    0xc0c09040c030203030f03010e0a0614010302160c0f0f0f082a0a090501090b01050f0a030e19061a04200a1209140616090302090601200c010311040b07 66
    0x3180400c661422410015070380035042d40d4035000c11030703030800342c64109104aa41d9a4030001c0001d801100720f2207902e007603480c0080c140080340d001d00011070094022060303240d080c00e00c05c50800007080d5a80418001085801710300c1d0038160400c500da159644541c0c2c8501606001c980303060004003408541c0c81500940c40b54102282845017aa54580da070400c1c7c40381e6000f118014021950503480c1c2c10450580780c21a40c03e0000c146e000004540d1031280c84c0071140006000d01020100520a80080d551104e0185c225203c0444e03845016000d5050072a048072002d40e10441c484140ca1210040010548201c40070000c10440c4121700c10342140004542d504248009050700007103009400c01c0c10031503c41e2608100074140d503d403030714144403060603050603407140b500003070000007180e01410b10990702581c6081d0a14555400d1140840d0060555410300c1034620320182010f0303000c02d1030741039012008002c110201d0240009001c079030b0403400265910708104418016044804c007140c031030a0340f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 639176276 1250 639175026 639175039
    0x1017010308072a051905030304050f030109120309050c0f0105070f061d0106080f010c170c27090609270a08070b040b0105040513060c0201090b0a0905120c0c 69
    0x240380141101030048543c00c61180300591862071254428a440143d803001d070703100801940c015890302c0b40c0305090700c156070b0b155104100c288800e00b0100c0f00b050349c80c4005400816414103d42d07820306a241070a030001c000a40e100c07404030900500304582105100c09584079242c1d06141c4000078400c0c4602e0f10081c0500c0e6007402040108001c0d030f405581e8036400000002ca014800e07601d198040c04a511501c0d240740714032808011048410300c02d41404001a44030419403079042c0a40060248009000c0d0812000c180440302402e449100c0550486040e521400c02180b00350081100800010303001c54090030003001008040366990300e003160315a0120601e40d0749070f03803440551898200760501c010a40d81c8041042c2040002c15403000740150300c18198502144e80312001e001c00c4a00440d0601011401d81d00b04c8030124900b907102000030b00440c8004100c82c2100e031903141ca060000c0c1c800380c1c07103640d50300c81c01c0e03007841000d0000303d02c0000003600d00c506d400822020a82c1d540c0840c00f01a20488 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 639177526 1250 639176276 639176287
    0xf0501090b0703230d050a15180e0115090e07080607030e0c1302040819031403060f0d05070f170a060b031e0c0a060c0b04080d11030a02091017010308 66
    0x10300420fa0380c4108081444e5901002c884a1640d0b2903a800500700c40c0c03000c41c184408121840c400c0e003e680d00c0c42c03510041d14245180f810913011664014a02d1000c11150340c0e201440301800280241007140e00991003408425260a00c0e1004441c1d1100f1000e40301d800614092054500101d0b50b56001140c83c0340110360100c0c450b42080c10144100380750341d48204400500003602289030060300448680c0002d540c00310340240c1c000705041c10a41070050010b5440c081000c50204980099034100402400003444545410089008030a2a04c0183c503103a20020301007180c0411a011500944002d040c8100c9000040841540c0c0700020200140b0b8a9100c00100d465610208140f0030b00300924980c0c00b03501740c01d0b00c40591b20341e003480c28000c0c050280c1c80c50106006000e8205007088a0340f0490300100741c0d90300d03160381c01300ba0020080880c42640340c0380388200103080c86000c0e5010341c2c1c4ca0340d40180d41d42030134000c21007680500c80c510750070320044201712448035507501016170440341c00000455895 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 639178776 1250 639177526 639177533
    0x203180a0f02011d0603090f0c100c0201080c090402070c0806010602010612080c0a080d0b04051b12070509220612120c061401140a091116060b0d0f0b010f0501090b07 73
    0x30b209242c1c4e0b86400c1000070040069007500010304022441800c025900e140001c0405d006014059a003800c01151540300601d0055114540c40b0341e10008182c04141003850740380025090764400c0c01c0503a10784c022003905001241d42070002a0041c13145000810055140c43d01c000c0100d1903004010b001c81c0c1020900d0a6144024426076890990001c411640c42c4886a0000002c0c00c0608055028034640f4001884d02454080006141d4520208041c2426402840c3c0480d07964010400c0d02044400e02025649413140c540e000300e0140c8003030013031030101d546004c40400c039601070340100005540c0c20480c00100d4004424941c0708052481d080030390203400c1c24204060220001a902004e0548000040384041e5030f08000322134070111424100e00ea40c902c04907081c1d940f2110868200340003045180198400d802c04601810310039000403c940382100009102040b0180040e141070300c52040340700810202c69580e902515420444202050030440024003983c40b60003156212030300042c011003031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 639180026 1250 639178776 639178817
    0x120e2803050105071115190b040605190611031602060c0106121211010b0319020f03030a0305075703021b0904110d03210203180a0f0201 60
    0x1441d0044000d0040c4c0c2090300f801030507460325865808407801035440d601c84e10442d481809008018000c02c913040c5003c01d00101e001000c0c0114a254010350b5210001540d440742104c591044c0080c2c2e23120034002d481c20001812920080d0b90104280c0c008200e090a24a1144140d00b011901902c51701d854ad030481c1440c41c0144046c0d046217001500c011121420030402c9602640f050300a0f65a10180722100446107080e6032503405010350540001c0e0b0425411140070441d203030340b18001003e103400f902d20040400e007107900440c0418002500d0b0401c0100740c6801000450b41409609800005601720101c40d0030805054181c03204040b01b10500c000b900480224400180582522600c042100c40d10b03010b9070394040fa1076880e07030f445801c205010345898a90342042c07003281c000203010840da412904102e1702c0c501030715085040c8403644094540300141c1c6400c9000100d211a40180d581c2440128400f156103180303002000e650100c5803800c00a00182d070035480d82c55081c06c1240c4031340c5486d68071014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 639181276 1250 639180026 639180029
    0x803152704030221190c020d02060901020a170403050708070608150105190c0b0c0f030606090303211905090c0112020d0c1701080d08070e010c0b04050307120e28 71
    0x850714a08443c130044250400d000740203220000034180d03010713204035105603019070103054040d5001c0c1c001d902c42805070509030000c00b01f2000500c107030f81422049a503200b87c1552100d80d00303620010085418401c1000400054004e01f0880001300007182c90200001d08507103005081d402c80c8052200e4403a06039028400b510780402c00a032820074131070300f0210000c1003000e03091416610a55508040b404180480e0201e40b41151409001807540d50b6aa041c010203038083c00d801c5070144803c2041034540811030085201c103041400d4006520704158004460032042001d21200d03c61803c0c040c4240b80d00001010011840282420100c020618154500900a80e00c0180c1c680341092070401d100307507100781c070036148a9010380064026601c50040b29641e51145028602198188000c00c2a0034040c8c0d24011059a0500d00034001c0e504994175030400c0e0703038107a50071241c1c2c0e070002c100c0c0c2c410451011140c400081d0189800e42e0f40240080000d8614144140401800d803034030070215904001444180c030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 639182526 1250 639181276 639181303
    0xd0603080408010f0b040e0a02041112160210020a0804120c05061e010b040312080c070f030323060a0b0c0a05060f071e08040b0a090b010308031527040302 68
    0x80e150780d074540d08280600042c400c0c0c0710403a86400c40d0f80206180501c20400d00c00340c6500185240721682e401d0100174810791061840c1260103011400011100400549c45401d00301800000b03a041103101911785400c4002142106005000301068694400034180c3d00c1500a0000404100702c49026103440f902070a014016010740d80030426400410044010071143c0b02000118580e66480306650500943c00000e01c0980700b01c001c0c45030b0500c2102d60f550003550884040c0d1610b8030035034600706043c2d0341d0103048010a4a501481150b0b0b0a42c50b05410100d50301055001c846c5401d40000300002441c0c0607490006502003422118510204120030b0304907440b42c00c4510a003030010f03d040601e00708981c0980080e03204600200c0920803940610412039044d1111186070b00c2d0307a60303131a0710702c04000d0540c0409d60703807107100e080454140c1c22064000d5014490186c0e8a060450b0076416078210f12031420b00450b02c807004109085d4044010018541096451044548951400303e0405101d8a80c09 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 639183776 1250 639182526 639182543
    0x60c0105070906110708070603050907080d020a020a050103021c110c0105040b1b04030b010b18030307121803050309062109060a0f27030201020f1303020a0801110f0d0603 75
    0x11074a40c2202e8060140c03001511400d1280c1854000290785107128000c0c0c02035908190010071840b8001c0e00010f400092035025105025180c803042803400780e003035484034011f9110484140560816542c10300c0039040c00c1c0303000e502c1c002c00d11001d06d48004031f18501c20040b130b0703641001f9800c50010406550012142030f0081c0240c0c24107040c801114001610b0300302c00c40c0b400c062040d0190403480100c50840380d00114500583e8a080e04c0078200c0d402924440c600a00001844021136034188018400c02d449801c0303101074221031940090000b0b11890031050b1b140b501082c2480401d4000003660b003880d400315403050313841c030300c5044100d840052980d0103a200600072003804042140030840307511900d816141080801d8500d1051000da500d490b0a052030248a04030a058406003c81a18480d50103800050b1400c844000d0700c140e168880d084030010704c0c2c6108010300c114681004204010090b280c000d0202c04a0b5010181c01da2084803005144480c000420300403e5406810103070081d600202503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 639185026 1250 639183776 639183781
    0x61f0504050d1103011d0d0c0c05090705030907050f01091211060a0207080f0d1b0318060e120609071710050c030402040506010f1b1b090222060e040209060c0105 71
    0x203a60303c440c0022800b4031030350a00ca1a82860070361641c00665291350140203003800f072402c42060750120b9602e2002e0344c1ca0380204401150549900c958107008034581e64580d0b40e04e241440305941000d0083e04a680f01d4540480d904400d680c1c0254050240d852000390701924080d1850030a880028000400350230000115000c50001d4002c9020740c01c80d110300040d44c10720050740c0f80c610b4982c201d9600d041c011801c0c92941c2c580c117510040715a004907100c0d050105200c002003c0014240314a5801400000c010003000c90103410007030004480060240c00502c0b260802c4c980040d1104113a00800200b0141101d00c840c49040402c4203840f00c0381150000c0000e0700380303000c907540f055004480a034092400d00c1c2c00301da00d82d446803500300142e04c041e6a4054200d54008451102d1701512201914024660b0a80020707240242c9042801000324002c0180c0d01c560782c42d80700b80032545009d80c0070000d0904c44402c204094010841c005209011140180e03a0010348000a287c2d00035154905c14540c40c0404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 639186276 1250 639185026 639185033
    0xa03020a021c02031203060301090f21080f060409020d1505011a031e151f020607050c0307030e040615170c0a0c060c0905030307060515010305061f0504050d 69
    0x8906a40e14000c1c1e920030101e5030364000484490801c034200a40540c0000e0b4001c0300050240003175900710750003c1c004990b2081c1740c1ca803c82d000c0d014542c2551705c0a03207c1404040340b030700159496903203000350400d11a248ac00c0d5000400150000f01554040d039142d903101821566804d03100c6c0143d070307800710f520344e000d00c00141200014003090041030003105650b5100074030400800d0940b0700c114030241148000030b0040f0203411036194040e108035589000104400c0c40355a03070391140c01008440b52401000200084c0000b8581f40014142809101c81085040032141c4007104440900e500350400000b0030355402c021030b006241c5544000d0320100f0412540c0380712a40110304416203058540340d540b282d11075000400d1944500e80b4517001140c00080800e00140c3c6030740001c00d44469504200728525510004030742990b02208048507100e548000b00960034005006a02035458207103000c00017460400c0c0451030040341440000f80000e60f42800c0001241b29000304c0b80945005401c3c01d06019a40c038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 639187526 1250 639186276 639186283
    0x1b0303050a020d0e030607120e010f1b03060f15050f030106020f0c120304170a08031e0a0506060a080405072103020105090d14160f0308060f0f130e0705030a0302 71
    0x31001d000500981d000788101d10f02c02c10440d600b03038100401030440d98550520a4a0f07802688881e660403940b5480d00400c00c807820311800300c120113604004607045040422400d00011038101c0d100601d031816800b40181e0b80b1403241d010940c0c4088000c64980500040159810b0058403043e400c0c0060000c0003082c082d0780442c0c4000940c0000382181d41203074990b0100082d5903921180c0c00701551060104002e0071a03a0124410203071900b000784e4500c0c5e1119180c030040b0b60300c101c0f00c48640200301c803802e03d41c0c4d003440800b0301d41c0103581c144204114103207a00012064841d9031251810080c03074074081030501a05000e25401404030119020042001000706c03c485442c0c00c0083d0059407030709000545914000c40c01c10f0081e151651603680b015090034003192240c00065100450a546500c001d0000b90b1440640300000d000340c581c540719103888410040310380703c404010750045000d480e030400daa840701c00042c44446400000894843e481c041003914000b41036102d81d0340345c4503500c0314805054010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 639188776 1250 639187526 639187537
    0xf1e0304030e12010516120b040609090c0b030405121b16080114090d0302160803040803180c0f040209031609021308060403050904020304110d06050106020d0216030f1b030305 77
    0x50b81c0074030242841d03500213405ca420480d079640c141d014901030071005900c20401034580e41c015200c0060100110b20104044503010340000c200075a80d90480b109201000b114a002041484c5001c1e25601c0c1c0707a034550f901c0e95141101005603400c04944462069490910740740e000010204490182c140520540c0c0741001da44a490500e501e00441704962843c00012680b0614030880100541340f46108110002c0d480b4980c1640b40010500c0010b0016a50790000d501450281c0010794403403d0000360f04400c10090b985904050b40150f01d820103035210040a1000c07403004030340c01610b41c0042004a801e002c00c0c54071a100ba1a44070308040b418001030b50143c1000400c46e000111000e0300c0302140350350f581c8282c502401054050211210b603140c56002194880e12030f003060325000d02c0c54030101d600c002c1019400c498941d155001802440e40c1000040c0100f9110302c01041038a42e1130700c0c0002c156403140405000380c81038003500d000703026800e00147d45000110300100200c13a40da040040154114 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 639190026 1250 639188776 639188779
    0x5100309051911010e01020c0603070522030201030b060405010807080a0f1806050f01031502071704060c11090705041a0405030d080708071716140f09010e04050c0f1e0304030e 77
    0x4403414080c0c0f55200300c03808091594117800403d014100320007000034540000317001d00700b0405c040000c40801012070758040380b609541c60605460070b0443c0700140607602511403a07406054248003c0229a034003000094006180b0704000240b511620500c00141105c0395992813070a00780500300414143d44010890401d000e84400c0005031949061801c1c1c00348203110150840703125505041e03011503140e00900201b4400c071003114801e10107101600179508194003600100e807400c0c0c0311000344074000e10020408082140d1603c1c0500d4042c50241c91070203280555504005280e0044081e5403041c8100c8024100c000c00b02c1d03131010050003006000307050031507c1100041000011801701d0b40900c02238551124045189a201c1d0b45032a024111841200c54036010000c0300711465061022480090450980307070b9011640d182141e40016149150540c43c0c10f004901e04000c100a06c40d4000a86407901c2034030241c00d80c1c4680d4400d0b1074808002034540704600304800014802095000004020003440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 639191276 1250 639190026 639190043
    0x60d0209280203070504030201050d06030c0e0402040509070513020d020d0f06170109050316050a0c080105100e0c040b0309101410060206070207062102030103051e070609051003090519 81
    0xc1c10314040701603000659a80307000c40c10a100c1440190b000304080c3c0070044000e800056540c0d580d480d0741d00c51244036400751a1244030302c81408194102409074951011041c030082c210949090003141c2c0395510040d00041960307000c10041001ca0117034040700c02554820000f40019031821240c80001c0c103251042031044e08040b00c4581c00001d060180004642e0008055410300302c102c10294a50001d0031403c035518018015000700003507030401103c002d4a4500c0002030b5902d400030342903800075915005016000da0390800c0003c01c2050740201d50981362529591601c0f034650482652418900303898002c071450034943c980d10764440c0052a40d103e420445100c2da922956504140d84801041e2030100050f0082103090040c00c0c02101c06c910b0b1901918209203944001400e00340c00c80c0c0080e0402c13511f6820040c1151020495107603580400807000707000c1c02805181500107840021644201740c041e070710040c8812841c501a03801141e003583c2280945002240e4a48500541908100e0440d10040f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 639192526 1250 639191276 639191341
    0xe0627013209030a050d09051c080108010915020a0e060f090306060406050105180f10021005070203121b09060705210f07080c122a0109080a08060d0209 67
    0xc8078041ca0241d54400081d620b80500148101c1e5603901c51a00302c2140340e01d520304800060410011122464416415503141e00c4000c84c00826071441a80b1071203103a8105884440803030346190f030030724410a0042c1d0060f40c40d80c0e003070002e460600c4102d075555400203000c0f445421060020000b4030121200300c080e80c045540301010070080f0f5a1034042c090000e00184000181175220742e85511404000416213507010350302c0400a0314110704081c0e0b40c00103030040380e008010744840d4010300c0c2d001001d6002031130070320a40307450104014400520004981d40340310808108465220111640310794040c1495550310103d007072250380d4178281c1048a5403501e4a0710b4000d0944074a206990409030150b6999103001c80c0c0d078440fa450342d00a58405c14040c040d65141452004040c40144101c03880044901501c1c50103031140d0f480307185100d1010901340d041c101d60100091000c402c4032504039060519500c00c0c0caa600c04600c0c100c0c075410f8001c0d003000f540001c4c00004814448628030794014044640b0307024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 639193776 1250 639192526 639192611
    0x6030f14010c05040510170c0903100615050703090b0f0c0606010905150a09050d050114090604030804031d3703020a09270c06030e010e062701 63
    0xe50503242d10600040302444244450b28160b0703103000c90180c6a203000300140d03180320050b01218400f59200c040d1070200003054842810305003c42c0032480413600d0104080c80c0390040701c4401c0e03012100350000700000099002c04040c001e404000191012050582c1c40c2e4240701c0703448616901041900d4101e00c05c110001d0710540c454640d40d420346c1c43c040c0900d882141c1814641d41c0f90b070052441001402080703000131810b601c542c4680c815590082d8004150090240341106481e000600079910130781004040102207500401d070180c001c0e0781407a10002c48550b004500354002c83c8410304561150501442d50b00400c0d0b07003807400c1300d0310801d0110400420000502159001c0c08c07844004d4004102d42c1040000b0b561301d5110b942100c9010040107101c007120b110301404500e0310301080301ca07540700c00c10074400c9903411300c03032008201c19070750080180c4514a1401c2d9629000101000c070072054003008081102c0c4005007000c40e08000000920102c000c02d1144260036100d080f0540c950000340700c0b00c0e50750 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 639195026 1250 639193776 639193781
    0x6050409050c011103040e0a09030305061e1306120f0201030506030a05071806080a030507230c0f0f040914061e070f09030b0c0d1505031209031006030f1401 69
    0x2403aa10000824651206000550300d50507006030711344450209004c005441c0182c56140e500c9000c40080c001071060306071502400711103010b00300c0750055150a44201e0f001780c502400c104549000c0307948660b0040f07030101d0300028005039008004082002c003442001c0107a104014107815100342c8090201da03407400305059641d1000d03d80542030350f1006104100c801c0502d802100d41550148021510b9500c500126140c194010b80032000a24001101018000344120030164041c41c0015403005407003003410719542d0740003203000c1440303940c903031100c3c480711b036a1490721140200c0e02a20900001c1a80d0404400780401d036504081c0c00e001e0000010b14510071b00c10100044440040e80e64403c0d00c5495007100e00c94041c200c1e0f00240900c0e204e001c400700300e0101d1034500c18805d01124075900c0940500c03520035984103140c10361f003030102040c0902041e940460340304620030780620020b4403011400002483d000344507038905001803500e44040240810501120042d60140c03014140c03680e050090b140c01c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 639196276 1250 639195026 639195041
    0x8040204111c05100803041d07020106050109210b0a230609012d0e060f010309110f061b010c0810060c3909060506091005030405120f090103060504 65
    0x80300d0b90200030b54065507441c0d2100f03400c06000612242543c2d110482c60b40303540d00640254100c15240d005c6400310b105240d140603401140d500c000d0041920307203400030f010303e1500d0140610304d422040c06e030510300101c48034070103105800424243e41410210031841c0245042d40f059810048032042e8003003900c480c18000d50203803001600250a50703180458a500d260ba01401520301008c5012910842ca0620140c0c100a030a00d020800000c5c1000410000c03540c1e040c6082506041c00c3c44890404282172400c0031088800a4441d008200c440c0750000360f040c8105051942c0400d8118049640ca4405600806402086880b801210b8030f44000c0000e5901c0580320f8100003503909980400051180d90201480b50f000c056040040c4500c00ea0003003c3c0900c00004810b03110711b0700420420b131758a40c0540e8004100945401c0e190900100201d203242c030b4001c0891040c8075001011038100070301000303111500c0403960103458449160915400090b480a040640000d06201020075140350038030804a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 639197526 1250 639196276 639196297
    0xa030f0203010b2a010504110a060804020d080a0c0f0503030109060f030c121403070b0910060806270f03030a0f050105010c060b0f15040806070e0a030f1707030804020411 75
    0x10305107100c821402494a44d4100d81c04100003441c000001ca00000f40104c83c017840c41144910307030696a6000340318913080d00da44000308028060050002507203901008081c4142c014021540e624603004080c1c0d40c02c50150710040c50008440c0e0044140400403000d036040e44c03640c803810b101081c1d90b41c0b20b20b40154460301000d003107201d0100d4200311200c840001c14240c2071240624150540b00e86402c603003140c21a1809403040003840e0300700003500000f4071200704900f11060003044110b0412280a9503003034010701e80102004204031500c0504100d00e000050700c0c03582c00888890314a604003c50b1650003d50744884800d00740b40d81d0710314200d42801000e05036001030b5143c007000b0301c103911000301402080041c180c1080f2806071142c00c80d1505000c00484102031204d01d80d80360714058071a843c1810040405040211000b4501c1e1541d407500024811240c001c002905440c92504217018071001c896503e00740c448002500d00105504000c546120354000c590400440c002c40e00341140912407504400e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 639198776 1250 639197526 639197549
    0x309051c021f09080a030c091205010203070f02060c0a260106050c0d0c17130b19021b031c03110409050702150106090515070209040b100906080c09090c040507050a030f020301 77
    0x5200b051b00c0395002c101c1400c6a86085a82d80d9500c1d085040c6140c00f5450a84151f500001004140398108036400c2e0111042d1000707000c5860710252540b498050426604200030f1181d08684401019554010006c4400700b81e40b501e07542d4458002e401c0c0c5d848516902000e00a01202602880c090503042c501a6002140329860340442e514060480e03010003041003c2006c11000480c503400000041c1400d8041d020100440c0360b443c40c0081e240042d11b21007004110384801070a5402c0d20041507403035803d511500700400b00039132072400760050304103441c1e600c941000121300000c3c540c82c00d4000b5030040100340c09650260907124030441c0300c0c100901501010600c464010003260802c0203100c0407070380b20403c038141809a0b0b5030004071241d805507010b0b50780d8ac0402e0141304000d613030307513040b00c000300784613101001410320300841c8030b480b07440300c1c4000d0b0b1040601c82c00090264005004d6200c1d521760050040100d03181040010740300b50420743c1328000080c600716000072080401d00c21a0305984540c801c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 639200026 1250 639198776 639198787
    0x70501020709111e0c070506070c0e0c0f070c0513150b0c0309060d0603031106070c030c02011710060908010b0d060905190606151704030309051c021f0908 68
    0x6030009002c3d03042c0d04102001040040300110103100205407020030b160801d0582c0c50385290f4040c0c2c50150640c00c41032240004000860000302403031864421104819090506542c4400500d2a113006a55100c5034103600010b0301c1080110040995040d40c00483d0200c0030064a40c47c814221000050856120882900d05108424440000d804007102100440349010080000714503240c202e20041c07541030340ca40805004250704040c0035140340c002d04005203050324103200024030b5025201409014060380c1e034008030559100350f440040107424402403032080d050400b070720003a220b114400c010014003803c0c804101020180603407401c04030b0007080d90140c09000d032034238402001d80340d00c02c403941d1007014072150f4008141c60481c48114000d00d00018103615100002100f01114030590302000000e0041c544c5104480c201c06402c25003601e0b000602280501e429843c140310705290240b070b15240a241e0390000c0c0d0000342d42c2c414116402030107441c00355081040060355100100142024010b021 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 639201276 1250 639200026 639200039
    0xf010e07030c08060409080f0a120e010b0a030b071b0f05010507020304051509060d0c050d060f0b0d0e10060b0702040605030f03070206030c040905041211070e01050409060e121b0705010207 83
    0x1000841d401001403503d40612100c0c22311050340042c2d0b104011a0030000c9000c1074058900c12038201c06109002801000307c040001551b000d00e900004000c009000c2c0803e107810301c6550460f44200c0010007000c500310413030404901c8050b00d11400c407403030340c01c0100040c822032000c4107039401c55802500404038140140d0a55410b40c1100c03041b20341200f030601c403805d100c2c943da002e4841c0014070350320b40e2603644200781c03c400151505900700b00e40809030318008110300103080040343c1a200122078005051000b00980c81c0c200042c840314007404074100f4002085030a8080000c2214600c00c4a003040340c103603940280341d1540c130141101c0341700360014404203002d13003007020007187d006070501d040515064441107250101c039000d031004d130b52100c09070344170464a5401850400b070080c500f2000342212442c10500c68103131030050040502868540400104000403030300320b801090030030020b81e07409601c800d030b410056402c28201c07003841501c0401d015035503000100d02c0809545041c0e0107850710b60304014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 639202526 1250 639201276 639201281
    0x5061305010b03030304060506091006050a0e210c010314011a0306060c0d1205072f01150b180a08030f3004050c22050901140f010e07030c080604 64
    0x8050312035548420340c001d069a000e000035482103100e2580003c01d400c2200500060303800081c5510001c100d61a018841d00c0d4020f01542c81d56065807900202c6100401c0104444a400c503ca070a440782a08515882c01200400c003036a013603400303980802c24440710b0b0a4401d13407076200303214160785070050711400c0c00f00424940085a000b040940b61500e452081e03014585000c00d1a650344000842c42c035250180145640951a0004511710f00780e4140c01e0403400780b10101c0744900010040a00101501091080c20b41001c42042d9600502c20f414694481402881d035010501c04040f060503a030142043d4070704000b10500f521012401541041700500c11940e040e800214007008180010f84c40041c2002d8011300c09804541c80541c0140c1802d00d440c0c094035206004002c141705d50303511031440d800c0c02c9260300c0c2c2400d0b916560b02d000c5000e4941c044207500404040c1c070714444041d07200080141414081d59040c0c1266400024040340307940d5607504900702c4038083e2082001a0808010940c40e01e00354 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 639203776 1250 639202526 639202561
    0x7020a03081909051516050301051e30071d0403030f020702040501030809100806010203072901061107050603060a1202040b0618120a02150c010f230709030506 70
    0x402c0000c030300069480d154070b420840040d0700140d10741c1e0020081902c3d500c805014000101e4100f550841d410000042e100c043d0002e034141d140307000344400902507030700c18120f220000071101c0140c8088040c0c0d590304940c120301c03002131b084070701c00e030400020100030303520040c6503500c540080c0c10040d071215542100900600c843c100c009079004d10644000d070f0746500c0303014000c40c8a0341507190342d00c04010901081c2c2011400c0703801402009010000207076000700460b40c400c3c2d03000f00d06648800200041210301e124500700c03001e910000d00004036405400c0303801011508035000413260925514030803c4000d00c42200c02c55040952000304101e026600440044103920080020030230500c0280842d0403604107030425480e41c0404540c8603002d01f0465040001c0030400009080024016004101200700040d210340c2241c0c000503400283d114294806002d5852000e0f0602542d07501c545605050032102c0c80e03600d06030074054041f40c00d484c083d818070422258000d0180c40c2551b02d01c8034004924911 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 639205026 1250 639203776 639203821
    0x121819150809210306040f05060a090914010e030405030f03090f010f1e180801140402190f030f030f080405150a09020402160308070f2304090f1407020a0308 69
    0x75200001070382c0f20120000211421507035040d0362285849810441580c00c0911110b0256140409114041c0c850031b003a10f069507541c080101c0d004c03206140c9040401d8860010100a502e0082c1e25054040040010070403220f0440403204000750101030756850f4401c49042e0359004101420403a070079401404c0d00007541c0d26a003043c1c401d0024400070f0014145603071002c0000589004616007003040c00f5000203000d07140f1030000300640760100c504100d040e640544082e2240000c84480c15854021009100c080c4c050380c1202e4031001e680c1c1c50440041c0c113001c81d00f1000309007488041c0040d14800c0c80340030b101c0c0da0410020607000c00740e445032401c41d12002e4214510b0b41d48914150002d0380b0349000500d4005c400f001d8044680807039081c02011940041c000008000314081c62034107aa510600d038080c40303200492001c810740590701c4800d08a200320340c030180c00682080c160340c083c4000b6034060a04501103541000e11a5112072040340c5070380c0c082e01d000707012652000204444c1072440400ba04001203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 639206276 1250 639205026 639205033
    0x15090c0424050c010e06010302011404030b0a0504022709060f0408070b07140f090f27250507060b1531180b0a0e0402040b03121819150809 61
    0x800d244c25600000301c0798210750b2040004004659114107802060780d582924503081038215500c10801c0e42000d0034107646035488038040f800391342d1402e00c83c095070044003000c0d03007501d00081034128900b00b04850007440d82c011f200008960300b802404491103181c0c040100ea2510059545d800340b051f8019011204100002c00108111301c100c100800400611220060715010382e60100520020b5840703070303e8010945141d04145401c1e1001f002a4121201d4055081c19610814603070a443d92141c1d000f07842c03003c0c2007544e900c045c1e0801c00070015280030f200180403a88101084c8174091030244c03081d80c1e44450400000d01b10b09140d0000c411065400c0318030b1040042c44181c503245a603d181c21080c140b0100c0460203442d051071b88a2184081b9040e2802c5004a10307000c000ea400c854002c001a00854840010403859507050210b42d0a0700700d032120042e150001507040d07110502c449a03145000344004083c0700324640280400710100d8070f6803084019404895041140c42d02809000d4019510 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 639207526 1250 639206276 639206287
    0x3050405070905010f0504053103050c0d031a030105010b030a090c081c020d090f03120216140102010b010e3a0b1009150b0f07020301020315090c042405 67
    0x15041c001c841c000c000c980654004c950504081200715440078040320301e811100c0e9404800e009e90348140c3c0e0b40c401e1030911600201241420259803a04c901030b00c80c0c00030b0141d20004180582c0540c0840600e281118042000c000c070381d410725081b600280541d001010040c00050640001504605141c034031400a820209542d400c4013490a106e50605209020316a000b078030002c1e0341045100766200d103070300e44604024500810103c0001d024040584440030032802c0d6589140208480944a400e6180c0c0b0025160785003402c02c0c840c1c20b08902540107500301000c018a943c454a01c0c1203a82c000140301c600406150104881300c024030450300d41001c0ca02034051401c0400400041e10072500651090031240b804c03510b001c2d6800004d80003078076424642881599a450080800d900703982810640fa40d5036103000740c04085078051440001e61540c00002046450901c0205480500350240c611181549441c00001e00d01d0182e0702524000b04c40c084409482c040041e4092480080b50303007451403804 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 639208633 1107 639207526 639207539
    0x27190201081f050118050d03021b011805130e03030f07090b030c1c0b030102040305160504140a050640020a1215080102030f070e030106050108070305040507 69
    0x2042c610394000302041700d041c000c1c0141c40c0040040a0711040c919009649040100c01a0b8140020101403c00380d401107848030300d030101c1414511422400c040a000030410361001c80e40c9800c0e200d07901405500702c188029800340d8004c240408042c5071844024241c00d006500542844404008100c2d1042822050700d204031044090044241c8155a142011700200c01540c5e605501c0081e00208002002440a40c540b0382c00344180307100c690b40c5040000721500700c0300c0c103800801c020300080d00d4800d070b0354410b40e400b900080c910341343c00662144032041c0c22407007000c80b40c1c0e143c582c0e401c9103610542c90110242d07004240b1390540c83c1c2a24a80014011301e1f1340c69260a1031031301d540d0241540941601b400024100940007191285090394908e4001e0000303a0304000811540c0b4a12a190309041c081c9a098510684546410ba194400700b180109030052080d9410b000720900400c1c403 = true := by decide +kernel

theorem cover : BRFrame.Cov 639028776 639208633 := by
  have h0 := BRFrame.cov_init 639028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 639028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 639028776 ≤ n) (h2 : n < 639208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
