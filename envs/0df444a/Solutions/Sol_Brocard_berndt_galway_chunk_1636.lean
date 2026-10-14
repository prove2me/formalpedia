-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1636
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:58:55.682068+00:00
-- url     : https://prove2.me/submissions/aa1b59db-dd51-4a32-bcf4-05c81a3a2773

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 294064748 ≤ n < 294244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 294065998 1250 294064748 294064753
    0xc020c12010e011806060803030103030c06021b0316020f190b07140303190b0d0b06041d0307061d070605030a050705070f080c0d0c081b030d0f0515040c14030c0408 72
    0x150704c12544909580d0072401c4842c5030502400150b542c1c4d000c800e0781d048a40680350b0641508095407144000e40c010101c4d00183c0302030a081c0b0050940800c00380031021b200d070092b0004c0428a00411408900540c07a0034850700510b81c4c1500031240100402003116049040f154841c2010315080007004030340030b00503401d44404800c03c0740d00310603500e120100740c1c9804000c0100195040611003621034180024100400d007201040e25420990301034460340341c560715034114145003080c0d000e0643d440040e050710140e071203a4100080f14616101f0300101e2401c0c00041000e54500741d8050220b0000400400c5070315510b00c002000386000c4c0d01110581940680282c02001151400c908940c108920800e4548500107000025901038000d0000194004050a00344401d1480d241c0106181410000c001d0000f4014200d00240f140605c1b84504507603100440c1c103181c4509651580c40013104a584100c4c1410b600804650300a030721801c0c040005110b40e0380c0ca130b480003c84199132055501c0f503003451 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 294067248 1250 294065998 294066011
    0x2030709033203031308130902160b071e0e010306031509060606030b060d0e07050d08040603050f06090f180d0909111e1303230607030c020c12010e01 66
    0xb01200414071420084a440302691403440d140c1140d80380000c81e82104018246082c0e0404212542d0103400c0c658600c15107403800540760000002680c2090740140c800490a2012a007048062a0a00da01040510380244407500320401c1d000601860055041840403140651101d6403007504034802542d04103084140c0d101d980c80b0003500904c00d141d03041da0418600b44c0e0104403944a4080c130401603000904540c20401503421080c01030100055040c140e01c528640060581c45820480004c1402821410349072464940c0103070544000802e4101000c0c0d5001c00c001c0d81e5503030324903801c3d04800f9040500450f07580d00543c0c0230030078400d2300002500744500458929402e41c0001c2e55001c0d514000710501c90028460344400d003d000300b4010108070400101c030640d00c400f91801403d00d0100107401320076000d0b41d03515900c0c5e902d02580f03c01d03030340c1c0d21440380602d1007910f0410200d41c10200e45d1508108180710101d0080d212807071212540d1055149010041c0072803025003280c1c141c1d0003d4002040344 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 294068498 1250 294067248 294067283
    0x605040f02031c0c1421130f0b0708031314010603200a031202011b11160e0610140301060e0a0602030a0203030c22030602090a081b040203070903 64
    0x68411008089210b48590360400c1e0328001001c0b07a00c00c0000094131400c1420509a5880c1d01400210f10780800a1281c40085600105044040e825102c0f040c44040d41d9040c1c0507001c2c0c00b281a0541000180d168481d00400c98140c84808039400c01d6080000d0644a45902031118440c0d03030481005010000d2003a074a070b01540c030641c8580b040785d01c1035094031820918002d4249494001c800303c40d5101a40090410110342d0f0340014482490091000040200d5400030918460441207100000117030a008281d01d01a0200809102540c00584814034140361003070403001c8a400801d803074014500321070b14550310740c024040030b181d0b0004191866102d60711240020900301100d845903104590104000880d42e00200803124242c0d65603000d1480d60f5550703010380c203060348100f0031208640f21000f01210306a01b4400c0071409580301d003a02607556012102041840c400582001c40c01d900b00708034100c4940008046600301040644001d80c8a41d1900340645540e9aa6400605044a0040708852 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 294069748 1250 294068498 294068513
    0x60207051609060f0504180204270804060f0c0c060e04140103150501060c0b0a050402010c050f0c01020106050a05090a0f06080d080604270201080405030c010c020c100201020306030703030e0607060504 88
    0x7650644c4800100503540d91042005840005104000707111000203610b0250074183c0042d03c007a0210000040c0c0940030481d0b03101540d100c04425601c40740041824041d050340665180b08134001c9250000210315991161001000c0510421051050350b264009282d19241c1150b0f140b51352091405045607940c3c18800d89440d42200e000e90f8240c5003900104c0c10b17031b01a556414105800c00740200841d070310044014006d080180c000d03818000072034803020010307001b08070005404003e04050104142d03003100190a40310b0540149100b6503a80c90140400d0715a202400d5120803406e0700801c071075100c074001d1801000781d81c204c0480f80c05081d01d1a50b00c2134208180e1070160302d040e10f0030011600c5500c0d8a1180f20160840b0100c13401e4103004c5480598070403e2030070342041c02801a83e1500020f070141c1c50843e150202d18201681021001110f58945055050b000a1441c0002d40c03451500c0c0300000d03180c0d5001d00004041c000c071440c0c1c4016507100d950980f003a955001000704602c1c1801d082150 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 294070998 1250 294069748 294069761
    0xf0204090905070b0301240207090203040809040c02030301080307110f04090503070c050a0315020a1e02070e0108060103080301051c050a0809191a0a0203070215121012060207051609 80
    0xda10740310b441000550184c0010840381240c02e2110100580e4050b4031800900684c0d8114040451058242c04103001c9154070007940a00e00c104c1a0ba41e50708681024082030f62501c0103a0001c2d900203000410101c2d201008a8002d2030388007201026181003800000d4808040702013840d0810301d08240f1508000000006100080c080c45088081590740c1d0200507034195540802459091403140c02c41d2107003880e401400c019402402e05c4d01c9120b003254200c0d48881043c4042e4001603001e218100864140c018486e8050014003014081540c19038851070500c2c801071283d203024015222a40003025a00400c03241100d41c08001c1e01d268159504050780c4607082005218460103c030002da000c0500499100d0045901c000c2e40160380b00030201c40780c0000d810041d1854190b020800c00302005a0b91a0b050a20201d1080c0d01d440e05e4640d107140030b01410f0342c0180490703215101e403141482802c1003660000c655690086015a0300d40a9151260900c01c0302c901d001c620b9640740c1c2000c01c02c03501036000754 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 294072248 1250 294070998 294071003
    0x220b0f0106110a03020d0302160f05031305030114070f090e0705190c1101050a0e040609021e0301060c24050a06090c0203040506090f030c06030109090605180c0409060f02040909 78
    0x7640c0c1c0301c2c0500038603610303076142e484000e0241e448101041100c40c0039401030300c801c0310320f079401404040c2d07191602044a0000101242c075500000342c0c80c1c441b421207c8000e8080e0005400810503034050382040394604001070407900520800b15140040700348603800901c00341492044001d00e07414404800792194110540c12407440000c60b244406883c81040b560301225041011044141e07070b8400195400d41c020751b9180104580500f18600c241c4585c042c8000800c01558016620810a00d20102e4031011402c42c40721210204010824281d1181c1c1020355540c1020600719641820182e80d03004680d030a10f5980d0b542d040c081007003d03150481d84032400300c03802600180030b0428000c40c00c980b01e100310700800380e2044040c0410340d502d04000c4401000e006015084440503078039100020102d4009a200822640c0c685c1c50010070403c040c016079400120031030302841441e0130407240c01e4441038485962070149a49100749000c1c000540c10400744240b2001046540b1511039070f884026100e480c0b0103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 294073498 1250 294072248 294072257
    0x9081603091a12040b0705131e0911030c03092409061f060e04022511030a0b010302040b0f1f091401050a0c0c0302100c0b10030b220b0f0106 62
    0x6103a074440304441101c00c9071503110300c6003c41d070752517a5405500e004058003072000c0000502081000f104ea20244001511429075203803140400440b510340c1b20156030f009000500d09054101c600c0e0000801a2074000440c107403450b45a685822400340390881007503025207032040740440410104001034216000b201042c0590b00141e5501051205814440945170742201d0181010090a88101100d40091600400242c80e001c4604888048200742c43c501e04410780b5000e02100030003281e266000d4803a04258050140034204c4c1c1c695098120701440064001c03610303110306144035907070502e40800e445001488c819200720313040c03c480006050703841c142000c61300240340844d031818000039540d41200140d643c5441e12007074031340c12640000c0300101203800c400464808401070351303000c0c01d900c0b07c405250307181c078140400c0f42020214150003400107009200120414004584280001a40103410b03c00544000e0f20010440b0f200da03c044030041e060304400010300002d0001030b00958105c9129955 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 294074748 1250 294073498 294073529
    0x30b040b0a2603191e091a0d060608070e0d020918030408250e040215210c070302012d05220c050a0b070c090908160309 53
    0x502048411150015501010034002000815400500040380302c24421405141280c0d00c40789030700e590842c1e58004c81c00099000d000154031303404001000300c40c4038210002100002d2500c0680111300c036010300d50310807815011304000b0000c40c0d41229a2101c000304200011a95854010502c1c4001d41c0c20000041401c500703e0300301d1920030064002d02e6002801c0c11801d8503802c114898000d200190152103000c28440014006020300001500c0710554035988102018805c4504555030783d40c1000c0070248426013444096100c42130a00c00d00198078005a83d10f00300c4503901042801001c100d041e400c41d20740200b026100c0c3c004003411450b4800d800a2080041ea45800700c0200543c0f4001c10515000e0b44140c2119170064026035040642c0c0c280d400f0612100380241c6040c0d40418505450f104642c1104100078101001c0c840d00805144d0161400c20500c0d80c0c1d851307018615441030071401c81e1039561110611804030704a46100184619180c4102403a2501504201d858851208915012403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 294075998 1250 294074748 294074771
    0x706021e0c01050411010504210203152805010e070c11120304050f030a0b0403140d0e0a120906021209040e06010320040c0f030203090c0a09060f0b0f0708030403030915050703 77
    0x195016913641b03420041c4502000310b14443da89e0103a00f801d1380c1c1413244000c0f0440003400d00304054080ca061800849006000c942e03884081070b0231101c002506840d050040000c1000d6140c00703a002500c40c5404480400c69041c0400782032401400300358810015420743c0034100d0700000030403c6580a89a8040e02000501010b80322011060301501e000d11000001c2c00107442010b0081d60801ca07039441e03a04050555a8503811910303c50040d0381c0030340c0705580740c1c0d09101034820035105042d81031410224140c00c1400c02500d0300c0b10180644000040410001c03001d035100d412075600c82004104548856070b5074241035501c8800a403805000d0103515002144a0419020391211595141c039203c64078920034004a00039840202000064098003001e54580d0b81d4403000c031001814055408220b0300d080c84200c0441c4022648240600101000540d003030408680030342c4c00b1250003e0145440359243c2c1070980142104c4a401860280c204c02021800e64003076206500420712580c0821666101c86d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 294077248 1250 294075998 294076007
    0x40b0f0415230307050d0c030501090c14100f0f030e10051006020102030f0103170d050a020a02070608152413090606020307020a03060f110304051e060c0706021e0c0105041101 77
    0x80701003c1d05038000103814805403c0c02004441d086200b09040c001c05a81d030780702d207400c54002202c01c4036001e4402d44100308d00c2401d000c0034007504c0002c9a003801a6207001e01d000e06000304101c000e0080c040c0b10881250124001c0d840025031a507404c082e281002d4441281070b0003804102d07911004000a4200411003510500c00d50344a00704101c851211a429616002100c800c511120030744100d0402a4040072049801010700903204060090381300c15518401030b0500880b60041c104000307002c42003001c101d00e00885408018404d0300da60580440c100100300c83d02c40003210621098500041c181d4a080d07842d21000b0444900d49420052981c407040204d85030700c180340700a0341c0120480c0061011800030360000c0d14484021500040c441a5000d04041e41d400c110f030169029000140d1110b14405050700ca0004084140040c1101349488042ca0015000304170004e8000c1e81d010070800c1c0244035a5480c000803080e412001600e4074038050341c15000e80400c890868010860060040d03682d4000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 294078498 1250 294077248 294077309
    0x6031f0506090f01230d140a0303061406070f020105070f080901140a12150915080705040b030604080306030c120a030306050906010e04021804051e06010c030509040b0f0415 76
    0x10340d01a1710300010301d10712840f07500301c140a040758040d1b5012080f00001e0b41e030401c2d40c00700c0099080502442150fa0401404982140c1d0042c4140c0c444079524004564890b41210030303955000a0070b9101c00700600049400e80100007000745800f20f100044420b01070750f40060005e0071426620901c1241c1c590458010324007803003440c08040342c0004010f0b40341d40c030650054402e00054019600700799556810f0358081e1030480e2801d0b89140d14540042c00401d0051100201030001510140011b001d06008280d5640001744068604100400407030b41d00c1c0da0500c44c20181c120010b08142070f036820950303056110001010201d001c0307440c0200c000340904207051498820303a81611811184264041800081e61001d00390a0304080c101e20702d584103968900ca042e00404440304000340c8901b140103d00101c03100902403c2c140819100e801c0c002a038090100c03020403505035000701e0901022008901a525084012684281454031020010303031002680f100f00c414510369500c11482100d4400c90f0090b2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 294079748 1250 294078498 294078509
    0x909010b030906092d210a02010e03040311060309031314041b0509130b040c031413080f0d0f0c08150f0a030b1f08070f05012606031f0506090f01 64
    0x200d01d90310081154041400c8490780800d054034110303002011420707128006d49044008840010455040c4035034244210f0040300c107072074000c524003800c42d150100d0600c4582c0d1201d10030384c000000a0003a002c180180c0c1d280e200039415048001d80c546400e00da024096142d964000c0b0f14224801030440041144006081480e44845141c441d410047c40001541284481c0281c2c1d00c411800103e6106d522a4203441c04507650b0004110f0740300041e05007181c0d4080d006142c90340310110003502080c00241110000800510301942d190b41000112014264004002a41c203213080c010001a0303400c50000c2e0300c5100040103480b500c03e000800c03c4004803000d0b16a540200e4440c0d800d2001503070000c642900201c81100041c034441703041503c2da1408441e5008169945c2100104101400e4580900b80142400342004103041c1d00703031401c913074144c0c1841030003040c550325800100700a903c080c4200991489840e504d80a6041c4c1c004054002c1e05d01651118040c11181001400ca0214150651305885 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 294080998 1250 294079748 294079783
    0xb03010f090f02390a0f0302010c1805010e010c08030403031a011103250c080d0e091612180f1112071e0b04090b010315050f0607080909010b03090609 66
    0x803400c0300c2c0c03000280d013641c65803a0750325a02d1400114035a010884600114800c00c481d45c5403040ca403070002c1c2540d14402c2c100050140c0a078844a684050081c1e2209480b000c0c41d0003501c404070070004a030101c0e0f400c030014120b810000309200a15905410800c19030442c9141080041141c00046400310050f09205100c2d400c2417044804104450202c04800a0f418180d10f0b0084941d40700d508565040c2d6001d100e455012001a40703486800c01603007490200105ca2007003161501820302c1c81030b02c0c84040d480080040e421903000502200d50700044080101741c003000c2540c442031a141ba10080c0c03402c0251880c40d040299403017946032050460b11005601c50280c8401e903c2c0400340c04510807003155254403507006020214001d003080001e13000034040b10340d000c0b61038081040090111100600454085101500c0c00d002c0ca448405410342c4040b815250360b43d44004900b44500d490289117030311544404024000580319129a01441c000e03010801030300c8440d01c800020b107039030301c612500c43c1d010304 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 294082248 1250 294080998 294081037
    0xc0d0f0e040203060a0f0b0309060907030b1f0f090c1803030504030803041509060204030303150303360b03010503060c07051911120607090902120a0905070b03010f090f02 75
    0x14140307900910742060000e04100700171510f0384001d0628024a41051403018008401c0003044802040031940000d10240584803040c11502c03680304203e4001d00d00044c8600c0414090780c0c0000440c4050010038066000300c003000d84802148002c0d02080341d907070001581c0105c41e0881040903412200c1260380c5a1110f625061440e510103040b500010015905040c0c07580e4a825034400900455490510510f00180d8450440c0b80c0a02218045000300c00030310b6625609100090304140200d01070f0010f001e85294500e0713840b40d050403d244070501110030307000701744d00011030000140286042e030300d0440503180d407a85d421400d00440e0040403406480c96005581b0610f403034502c00071000415000d02c4501c0b65113450304c0013140000d0002440011568400300400412680c007440100190444c4042540341c0390000c46184410b1102800603003d4036902c10100d801c01404008607001450107170380d040c0e169a596a080010341a041c800c42c0c030514204002c001c504032092086500c01141c103480e49610 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 294083498 1250 294082248 294082277
    0x9011115070e031501120c080a030c02090603011107140d080709060e010912150e03070507030212031e0c07091103040b19090f051006030507060806010201061a0c0d0f 73
    0x45503045843d0301402142c04280c5510320036101c850180c5442e4024128030070312441e011000c00d03c0c0c0e81c018035154010b10741d00c1c000a03900c11170121800d6012a81c1c2a003a40380c03040002d00404807400d0080b5180c80025201c402c12182c01c40c0b0203544e1950009558141c0352410081d60803030b1048500c1000105407080a11449014000155007007106150020201c2c2c1c1304d0703860a10000d0f0340c0c0015980304c40c1800001d2500f000c1405070352000001000558204826590342e04ea85007800c0c00001c2c420022260a103604a104105807804442e0089031320b0404008150480f01aa0001d5011003881c0103114002c94031a0760b6001d400601d014510b0071a103541e0759911a500342000c05006040110405901084900340314000d00c2002802001240c240b803000386003035403a00700100d0101d0a02d600b060780c00c2000c1040810600212001e45c200802d55903103002c0101e00400b400e420203458100480187d000f03101d41d1501518240c1c000f04122100b03403041a005030755010002c0d4041002132003c00e00c0040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 294084748 1250 294083498 294083507
    0xc084518060a060c0c0905180c0102030a051b030c030f0c0d050f030a0c0c050102040b090a050a0806071407080703080609071706010c030201060e280501150f020319050901111507 78
    0x7401360051354924650343d11400c06006549082e1125a0201403100132041c0c0c0e1302c02400703a840c12640900081d8508400d400024101c0c1c040c41084010119010849030054441441180d070000d0050040d42d80d10141001c46029640121010724403e106108003058500d000d030f0b0444144e0898440420704658400c0b5034000509004000e8030100080b50b0b1000000600034000b42c40900701d0301007811740b0f443c4010140841324605a01092050f04980401c1050b40c0d008260990014001d203000040304501c580d1036001841003c40041500e040040d0203800d05034800b222902030a42241d48102076190300074110354404800c01c1d070480d112800e101087c4690f00030001801d009100380000b0815607030750b851001081d00101d030103000c9071564084840b65840300151381281d05064010801595040c200e40e0504004403500403424400074645908009008005441000d014507054100109103010010041d0304200540c5d4007088280c08200d0001001040c410040000d041e450300255030384810440713 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 294085998 1250 294084748 294084767
    0x5090a05072105090d0507081207091a1b2d0f070806100b0a02120306010e12011e06300503040e0402010905010c084518060a06 56
    0x3050000605a0591126065810b000040050000080d80c0d1600c0307603106081130181180c0380108181000b046000450740c409840500d842c44002c41c1e00e6035241042511072003d240c1190f15080740da21007800e02c030001c0d14000c1c500500f0460a200240d0f01600003190307034006d140d98801140c0901500004114443c61007010548090000c55000541010916080c450190450600c60304018108201550f910001400030054518001e1030017a400000944511039040c0807241d50305c001001c0390030b0368070071582500c00500003005500001c1c14801c010740207140000d0380050f5204c03051480e010900c070034496182114054030b03515034803103180208602c03400d03000c80300e0000c1080c0c0314400e0004210100081d101034920665000c07094145400050700070305540e070105041005003001503002892000a0300d240031213803034800354406009203907001c40c1d0103078600101c3c40d80c8280c4001c007040e00c100740740f0280d418001d42d24442078180120107240b85800c100c0300f03980c1225019100300191071007120f040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 294087248 1250 294085998 294086011
    0x151c0b011b030809060c0903100e1219020c1e041113030f14070f060807020c090c120a060b0313061b090e0703061a09301605090a05 58
    0x15030a4503040c598490041c015400e0300000d68040411000010802004e90044495503e00f410b140715400002d90701c5404901c19102c1c00e840f59040348440900b040800341d0940c4582d112520342400000309207142c00d580c0481401032042004c0c0180c075017800ea41ca15441002140d20700b035840401c03402e00006e04200200c001d42043c2c01c1003070300009920b8030301043c0a10710500c6c2d80c02c1c011340d15003402c04219000d0b10178107100d074116040030040c0d41d00b11070200381104c0450030030175020350300c05205908168510010a40000015007081030203070b9010014150184884112030068540c030000d00111286030103a010419020004914413009150701a10a00d2207a8004101d814241c00c1f00054550000040408940d4440c03080c0040001c100e0b80c181c1c413024a15080041900d020f528140e03d50300750342d40388030800c1700258040c1c05440b16549d12801c201d94210313400500c0c18401000200d40240b07020320401d0f00501c40030000114032100c100342224001030940b1501d48584002000814000e00807 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 294088498 1250 294087248 294087257
    0x2c010e0307121110113c1f110a080c0417010504061103060307180f06080309010906110a1104090b090a05060108010e03070807240b151c0b01 62
    0x40c80503460140034407543c4280c0f144602d00d541c01c428040507203010340c500c0c2d00340700c40000c2d40a13030202c0002d07604400c40b41503070b00d0300d201c10441c2d20304048000101c3c4490540f00154409105403400008107100c040303030340040c2108200301030070003079044a94100e61036168000402c200c054807407180d0800c030781001d202e200f014501503903170000302e00c10092040c5096069459108220601c020752262049001d0b911000d6480c51800030300103525420140522801001c00034070a501c02c440603070040241d5a181c0d841003003039070f4490cd04e082d500d401007112140001c1b00d00c08003085040c81810f1304200c90400000400d0440d2080d036440b8814141201c200341c10550b83c0e40030102040f20030300d01c240612812400707412003101c0d50420f542000340507041544268100400f01800b80c0c0700004540d4000c1d0860405600c8000318940089141040c0240010f44060481c14800c036075200c1c7c0c8124a2900c1c101c440885e040c425134003800305400b0b04070004025000718031240c650081681c001c4102620b05160 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 294089748 1250 294088498 294088513
    0xd0507080c120c010c0e0a120f080c07060206150411030a0b0f09010617010b030709030b06040902180a060603060f12060e1b0a05040621030c0f030f2c010e03 69
    0x74280390b80d048804803080aa45581020460940010502540200a42c0c81c10201c80c20956030301c0d08035485180040075082e9141c110000e1110b0f1200b40d8008a24220607200e0343c070b84c1d44000964645e02555034104418000c0420320240c6058070424808040910310b0a00f9552031030341e00720092180300d0b9174a8010217101c110440035581d03512030f0b038040d01c1c0c26160001c0d14442c1e84c140c45012a4141c22409952034100300b80403109401c00b07014004c0ba548140d031141c06a03600c10100d0003a00c074080f0700a4021181c04c610f01592031566184600c20751304181e041251fa03540319811800d4540a2082e201c1c00040540140624a200f010050f038440c02184041a0180e05146151800c002c0c8000044142d031901d05046040c82c0210714440146070480e418000c4034100700c103030300c40348406041130003100205a0280e41098003c19550000c50381145a03d031034001c00341809401031049040c10400076154100321584401101c1c09064880c41c0380340202d03000b035401c0e00103480c0d400d03030000d840340d05104504 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 294090998 1250 294089748 294089773
    0x280503040308040306050a0b0111031e120a0b2d10170705042c060f0d060207080d0b090403080105041116050f0c0d0b1329090f0d0507080c 61
    0xc00500044d44120030004031031034074102102c02c84901c00c14883c100040c100c52010030320400001d03207a040c010a052120b0381550b5210300d01d020b214900d0804080040c070020020601c180e540710060800c8191081c84a21008200000c001c202203540c0f0304a41c480440c4021060034000624262200181480002e4068002c2080107088045807400001040001c040c05002d0b442c010f0b8018040541202609105203000250000c0038000e02007030041c100700485035802c0c0d07200c44c451180e980e00842d0440d40c1d18000d00b0301428a6015001a03a0141d0814006000c1410500220340c0f0541e010703030b6005c086900344000c10000d003802080030403181006001d4403141c0e055010300010014401c2c1c009140d00e01c8070315903903400c00c014008402d2103020000c0c41c00c004138003135400142d40b21040d41c0243c0c003050703500e01e880c5012011886080b2825151004103403000c0a07120400d034002c124000c00c40da05070112220b43c9955003540742090b0b002802c140840400502d04401800c204d545500c140d03801c010302d80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 294092248 1250 294090998 294091013
    0x301080d080a270c080708060a0e0316050a0201180302030d2d0c050607090b030412030609050a09050609060c250503070507030b07030c05040e0601020c1306172805030403 75
    0x28460340d010b07000d8243d24008020b0700c04072680c001d050035070160030b0903840d000e003464071400000c182c059002e848404070455482d003071084805522480d0680c241c00c44d0300b0b00f001580c8803200c12049011403200001d4000755034401c2c003c0001c6030340c000c5c014000c2444c40ca07000c50794620140c10340c130300741200d01080c06a181c0840d145421074030110f03034442032001031609201c4d01e400c1002e4403002c10302000d982d0074400d58503681c3c100c95100b5000700c140d00001002d403008500509440d484001e42c40d141800784020f24a03940c001e2080b990281c011180161100da43c00f0341c544030150703202c0503007440422407103a1904542e254032002d14514000002480120b8652504603886000111040d8000790014030402098007603560304880140360801c08104008400340c0648075600402e40031824240c00110350342e02c2013010036030300d0713001402d40380c94440c080050501a10701400b81c61101c1420740c250200002c400184400d0000000000826502440e050f0205040984d0f40a94441c0010003001c408150917 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 294093498 1250 294092248 294092291
    0x61804050a0c020c0f150f0403051623091810020c0c03071a0d0905010b03071e080c0a0b03071704030f260c16020a030c03170301080d080a 61
    0x41000100c1c02c4051402e00900780541100070038811590389001881c2e5403690060b20300030340c0c41080781c82d5640f01404500e550b1401250b20003050f178402d41113880b02420389050700b442210300d8600c201d91a422882c4004560400d05001e06410440210000700d841c0d405019440c1e18100442c142c3d0b621511102d4010705030b0b449041c40d148a6407010541c0d81d42410108200c00080107110000400c0803550012140b2905c17400c1160503615441d4015602400000c3d40b2110360440d009040302c940344ea407101c1180c400540c0c5600c1c40601415030703c00050601010a03440703202e96004181c094858100081a4050780001d40010100540410000200040171050303d0245019171158060f5120100307008084603d107000607120b80c0101802d43c98800f11682c03002d50080103000f51261511076180c0c0c0b2980040ca00940654032520cc4a00081813102c0100303000241e900540c520b41066000d10708448043c4001c0c490202c0d507500c620701d280000c3d8403d400d07072904a0807140003c43d4085004403118010f210 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 294094748 1250 294093498 294093511
    0xd05030423030d02070b031504090f0501060b0a0e060d02040803070308060f01050403030c0204091415010f050405060d03030216020a03060b1305090703140f1606140708030606180405 80
    0x700d9102918011114000310303480518201e004040742942803000940b21010346c4110561140040085450031203c2e0402e20a4080d01600c10800301c4040d0034245d580700b4100c0801d503540e500e41100030844120307004c115003560405d0346440c02c01691000900000b58444244254003070780c24070000c501c007001400180303107450003030307542841608000c4100120070400c0c150740d0307041c40410401080000d4000b214141e0b03250f0122000103c4030058101540300c001c2d580c480c550940142d55a40b07400042e0341003502c7c140c0740500c120042e06a260f409100c1110011340e9640c0d801195401c00c00d000070720a4000304a00400d070700411919184580c041005125241c1040b603002d6104e80c1c8810304c0d82445c2c0043e005142074042c0900290800380c0d00b1640f14252404094800c1e40a4001001428001c0041341e42808525044800100100d41310610007980c601513800041c2c0407001c10084280c0345425154155040407005d451038a40c401046010350280005040d000070400c10101a1b603614480c8610986 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 294095998 1250 294094748 294094769
    0x1b060908040e10060903021809010b100f02010501090c020c0603040501060b190e040c27031502030f090307120e0103240501120203010b0706051b0a020d080108030a1d0d050304 77
    0x81c461a0f022403980681c0080b420071407031540c204050707501c02c0c280e40e407a9624501000890f80b0303604d00d514050320410030166080914500350311141e40d44201c2070301e61184641e000700050307626924103006581e81170700d4410040c0e00c0404029550301c0d01d10001d540182c842c80c00042c100b59946c081c00300903003149110004420a854107402803a8228030340f59000c060846081001c280e10341c1000c2d01020540003072007209684818000808500204260051340d080300200e06075800d844e0619010354000c54200c0e140318048408140e980c540082510000c65100c502d009482d00740040494001c111450454105900c40c1000b04200d4000c40400f500119030104541c4113608110001d8243c1c3c141c6001501072610400040043d02d8410040e120244c5e440000400c050321800e203001000810800382d4446150009030611a580d00041d23034000800c3c0d241c0700c61605a036104032040e1217002e000e024201040c00c410700c01c1014a00040b0000e5040801030541c040e001301900c0c1c151030364000350441c0c0e4444 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 294097248 1250 294095998 294096001
    0x807050108090f0d1d0a0308040510050403080306060d1413142a0f13150b09030c0d05120708040f08073002040921030c1b060908040e 59
    0xc0d64405032556100c07003074000034480d103d0400c80b40c41d51080e00f100503200b0014074480c1008002808126680300c0d2100602c0b51101c0380d2241041c260300d031312620a80344103841840e80000c641c0e000310261002c507034000c2c804509640d102030600c82c0d01c2d489a0000c100da103584500108030b10a0b10f04105000e00d5100460312940a018a021140c005e101b071001c1030355070f10ac40404141d0741e541c0841403000080301026840090081c801042c040c25103800c0596020b113040c071300076924400c02c1c1e00036a9140e505082c00c0c14600e03520400340c407113031050149003500764206a0103020b403800c0c0030051590083c032072012a61202d50404881c88079800c050700c00c46003100001810840c0803209442c600290042d1400b80414901c0e001e004003494484015001c088541502d2000d01040c4072090204030540141c01445801c501d407a06103860300d181c1d118051445440085800664441d2052007428111030310b854125401c0503600004e6010800d10840c0c0e52900c40380c0c00030000d2038140150005004003805a2041d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 294098498 1250 294097248 294097259
    0x40303030f0b04020313120e060417030c0304061101060603021204140718020409050919140f03070b040302191502160606030b010303021203160507140714010e060310060f05040905010807 82
    0x6000395602c0c0032040148c41401d0039101d0342ca000481c1c040b90000c540b00f40e041810003000600f5800351010604940c00086030001d00140c1080c13080240141030340003003000584600003a8100d01800b1031003c208000200007400041c070f42180d856058903604120b42d1019950401100d0091036401d405c10f459030003103010020642e10b80242d5800550f20000b401c00070018422008048101260292000a061020fa05401c0c0300b442240c0314110100d007941d60783c036024200340e02c143e241031310100c2c014800c0000c0012081409020415000d81c01086140c10b10240c041080203500201607004060b840440074100081082c0702d400011885002050341562660030044e0a0211012003080c07030960400c10032010201003540000d11005030306000c1c0e2114654241800c1c5000d0640310101c00d4440d84c10080307601c80b0034070710f00614070000760780300c41707170000c601c03090241c24081941c5028a12100ca1401e200050040d41209020081071811ba0705190382c0701030f520140c450030f070720481040d00118802e014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 294099748 1250 294098498 294098513
    0x2e11010b010201091707031e0f140c0d1206051905041103040305090405100816090e0307110f010507050d0807030b18280c0201020c0d090803040303030f0b04020313 72
    0x40c105000d0000304040c40750b5031180e00c80100c0c016070038108a040003c49004250089514654860026103002410507031501c0261080c0e140780080404903588400f40c0b89032002c00001c982a80d40340174042c05000c109400140c0324000d070101c0541e091500c405000c1150f0b02c843c0490240500403010b20a51107143c0f005000032903810404514501504004120200b03801204480c8680000d94000549664519a628143d0b003150401c0400e405040700e050700303d0b400c2210a0044e540c800c6404c00904041c0200d10741d584c401c410009003e44a21400c005880c94003c480600c0c00d0b0042c188503142c0740e401c0e0758403030400d010300f103c000114003503006000b0300c1589407040385255101078501e680d80814a1400c42144100100002e0508003041c03c2100c00e01e05803526030201556042e01484000e8400c480a4041d400014960407203104000c10541c4151003503010504440035100a145428119101140904003d01d20f8405080c1c5684000c01a03444610055215209140c004000254149003029 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 294100998 1250 294099748 294099761
    0x20405010b2109070302100c0303140106090b031504090308040b100b04030620040807080c04092303090312030a140c0a1116080706020d0201020309030304022e1101 72
    0x514464050004210401c5040007040c6030081c0c0c000b04295954031080040c0c602911034000035005203030140c0310b17451035400890f1403074154030075201400288100d420480003680248500350001d0300d400342c20080540d0620095030001c2041b01e03008400c2c51101c004c24103a8800090840000d80312504000602c0580300b40704e600111405c140725201450416240103500482c04042c01c400d98034084901c0002c0150061500c40f107040d92500d445980e51032076142c4810240c030400c0014014054000d420b86414418040380721740c420035507150408110b84040000c0040083c02d51240310803ca100640c0d941004204541d40b500217444d0340c3e070710b0724041c41c0382529111041105200302003024007145a10702c40a980b140c404034603140141222085443d4600b541c0c20003810012016440301062500c804503664050320703241c0d001c0303680c82c10445004078202e1004a40150b4642c03c10b102090040ca04003001d10901185100c2c20182c01440c90980d405110040f01030340d01003061000c41b000c40382c20038058403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 294102248 1250 294100998 294101009
    0xa020a033b03160b0409060b16030e190f05270708060105090402130825031101050d0c0305060a060216090902041409010903020709090201050a12021b030702040501 72
    0x180c00060001d85000007000c0400700c1c000350010044441025074608005415800341c50101c0c0c40d0006942d002c00c0650342c0e01900840c1085ea007480800b2841d600540e040f16055911060154030ba50300640b412608034445500e00e0764008042078160300450000c00000c0040c1051450401c80c480c5001c0400441e090010071051100d5400341c0980e15101824505a9102c0194180319003165150001203451340300d440e0b4810360284c804102d40d50440ca244103080d06403001c9c2c00071142c0e036039a05c0c0405a0344869061840ca940e05000800740300080200e034440e180e00e0018101541000c0300c0007400b50507185200180c0340025601e40c20440342c0c0ca01595032900421003030015100c0d6159042c40584142128024100c0071b603282c110450031500c0701d03401041010804c1d0710030803c50074200c0030280a440100002d81c0144280b51303003c2060702c0544546130483e036058581a10b000036418044c4c1d0224004030300e415407140d00303000c0e544510304a00385800b03101c1c8843d806035645800360b00c1008100c65068008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 294103498 1250 294102248 294102287
    0x31e0201240815060a090c020c0a1220010507020d061e060602070504020c030d020c060f060603010b030a0e0705192c011e1a030103060b090402100e04110a020a03 71
    0x80000c20004600c4000b100b01c0740c0f0007a11140c0d103043c04504a080940d110680c81ca141aa41c070481ca980072450702140c030f4003252a01d0005554603078403035200030039030310142004010f0704c0401c44522461200441080040c10142d040561a4000514140b039002e0306464050300c410044044030801180d6450661024a08000e11420014000d590b40c40314003a450045a001500000c501000c00c25166003a2407420300b90355821078070000c140c0b210020f032035a26650802602094a074907144040d24182c844140046095a03103d01410380540441285000c66000d00e0074080380d2603c40b0300700400c8065507410f0f0b2041040c90841018043c0004407400784031000603074104802c9408003910b03241120b24070a842d0041801440d0302c0d48524025500c50b04d0130b9a41200703031808584072040030318102ea0241c0010481c40080c2c5050001c030314021030b0000c0d40040000c0603500002d0180c00444840700c2c015000080380c004104148066a016200d05405644510340b0070007050f03440702c403052144101a28 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 294104748 1250 294103498 294103571
    0xd11012018150a140903010603210306060c0206092202090111011406010c02031c080402130c0e011115040f02091b07020d03030f05190b1c06020304031e0201 69
    0x6850f0240e200010100107010350f1841c0e94920703042c1995210b11004008021a41c0d40385480c400b2007001070000380021919135040e4580d03c0c000c0c824001111000d864a8245c600c40740d0801c13020b80d112103895a801602c8007500054001382ca010840031f40c0380004010780da1204030002400060742c0401e1002280e0401d480c4400301c400140b00b280c0c02c400282400030f043d00b61880080d050000500304059034041c101c0ca0351308581c1d40066140c0c0214020b4800c52040003031109030000b43c65042c64034001144220840020301d521401010580894450564807001005014101e1145081d44d0650720021500c211400b9447c240c04800e402202d03110b004403585120656602640c007500300c000e40302c0d004440800c014107009410a010520380044100300038a04548030001401e044000c404407585402d420362100d05101c40c0c0740c004210b2502071600c80044c00e07a0340001035030008000b01e0400c01000040140000100311007418944035400204000c0b81581d000d1080c5150003016880702d202000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 294105998 1250 294104748 294104779
    0xf022808130c05040f09020d030c030806040603050303150604090c02010204090e0606130c0509090414070608060121020c010903080118020a050904050403021f0f0b120d11012018 78
    0xc02c010448005640c0480d074043d04200c07010003000c0148001e17401c200c20002c00340c20541c0c41040716080601c83c0e1030382580350702c80400303210880e10079000040440e801000414580340c22469440d0441c0d000800d560f1416469407260003d940c405004040980e40129041c049001240195245900500700610880c0b418200043d00700c8010301840301c02c6235450782c207585007911841c1115101500a4080110340c200380c0f40c032040400b80c0d82500046030013007500114903940704070010f502459059540400c0d41050260300725088400c8010f40c0810b40c0c0c00c102e048042c82c8203010311001d00b80261102c460962601d030f00207032540003207030300200100c1c0304001210189802c40c00361074010030b00395000101c558403460141d20f4541070f00380841e94509228850822403211b6007040c049140ca1800034400003030040c062100c50b030301003412501c039030700160311800c143c510881480388480d503031600108081c01c810f502d5107002100260130680f09100000c90182d486942c0b1080621150269020328000c0d1080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 294107248 1250 294105998 294106013
    0x51f05130201090e1902041403060907081e1e03071208010e0408090d0203061602010b010905150309120720090f0402040c02010e060c03150607030801090f02280813 72
    0x1030007504c0d20f8003044800f06208001d21180321070005681582103642e15128006807500c440d0f50200d1390700c2842580000b541503040800c0900072100424010442a00f8480001501e100c803d000c3d041c4d540314444202c03050030024091080b0403200c11000e1603550143e402e0800d0803074280c144040034041280010480c46840009640c6e0041e00300314481d85900342c01001941d07501c582ca0004c0d6240c414001406400e075128a64541840300c0e0b60002c02c1800190001520346966a00ca4254420181d43d4208035032200e0380011036000c80610705a0703d00110f00c1c1e4401c20f241d042170300180c8007000101000d4403022400c801c03c5c440c84100300da51140c2480d10300c0b4401c3d8140d1008000900454440700701c3c040c1130b03000f50416440d40c0c510800f9945149852042c240301500700300c4071080b01007015240a00c41d41820300445806a4059a034269a40c2c20700e0004005021243c17007891259508014122290111140154410022402c07510f0070300d0074090000d106481c041e00d0010240000520b8600003100ca = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 294108498 1250 294107248 294107267
    0x90d08041e0609120e09060a0605040e0c0c15040611030112060e0705030a0311060a05130308060d0c0b070303050a180b130614010602060f0f040b060d051f05130201 72
    0x1100c500081d40d5110729150000d04034840c40100442d800c145071400480c0c000e07a03100b454020a6401c0c8290755103000c10000c1180482c0f003190041030040001b40156251800026842504021807900c0e241e41c0800b0141351005c842220142c400c0a5420f1000b00038450082a030304c0e0b00b808010b83d0865042580b040304103c4a43e42c0100300740d03a6074175180d080c454244000d8006281c0102507929038801c0d410040c2098800d5051000c05020b9080002d00c05421403203214022107440a2154066060f640e0544100c00040c00c0e5991140303080c6c414400043d40d80710080b0140c901800070765207401c128070b00a82541c401800e0b42000c0e83c01c022031440e4841d00300003100805a004002103015440b03480044881e18401540a8142400d058105800c8007071040d01741d040318a6a42121225900e140501d0300740001500e03c040f00c46111004180441ca042c08041d401800003405029a0b81d415520b1501d441e0900034411801201c2a20106103813010f842030f25400400413aa4941c1e10646a0009104124 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 294109748 1250 294108498 294108533
    0x1103041a09030423010c0b0903040314011a01260c09010f030908092701060504030b0a020a1403060301020c16050a0501020f030a030519060306090605011212030e0c0307030605090d0804 81
    0x2030f001004d0065030721681c4401203c0d50440b03240c10300c2d4108445126120380c420300060b00c1d020402803040720705090502c1918a101811410b100d407146400b001110790580f003045804080420300c0341d01c1000b8081c809564010a540a88a50b4810b02d280015211866000e2110141481c1c9400000850500c0041310032840088072000c0c0c84000c10045c0005a8110224024842d40e82900110311150840000c10940e4040c04185c0703132503514160b6060580c03096400c9da10000342140c040f610f440d8401c0d00078640040c00180098101045984990b01d0303c080c416080080940380481000242020702e02c0d580602420303c003800060307134540200c1303a680c419542640101941d1381c0005468039607410754061261040b50003407160580d24248038029001030201641e242e481c0100004140000c030301c80b071480316808000302d26401d81c520f00070303001041070fa030b185400c5001d140b4103d449070b0350070b002080c0903501c2100e00280c941085407000749804807502c4403c060002c05404e0001040c10000070b400940c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 294110998 1250 294109748 294109799
    0x2010e010203041706101a0702150d05040303360206030603010b06070f0b01090621060f110408070b091f0c12080f0a0c1407061103041a090304 63
    0x48000004034074610850380032500070600400d2401002c030300468054000c9840021201c001c548074840f42c0c654001d00d0f440050007101c20003a55006081603030340c22004410040c0214142100341c520032050340c00407142100040d64510b42c0c00c030034941d4412242030518001e41c0400088550310100c0407241041000a03104510210020702295825080a40d14980180c02507440704102e1512502c1100c8295080b18414900c3e030010401a40d60710a441c2200c1780c0c64407006800c0030f0034280220f01c0004030015104030b034440c000700e00e44000500940d88841004818280d030ba5180802041c1461810740184410100c01c100d507120507502d00740440450041d4041d404d0005481110941d000c000e039032001042d5a21030900c00001070b401c40c0c1c415105040403a14485159111b0304039004940103000c4190200d160f011252180750900c00c0035020440c40b030840026000e0074403d541398180c00c2120111400c2001c000b441010124070024031303030010840c81c0103509003824100800d20f00b0501076041882c1c0c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 294112248 1250 294110998 294111017
    0xe030322080f1603090501020a0209040201050a2f06090c0f21100e01140702030a1d0409060c020d05040b03010608190e07151112030712020406020d0e09040b01030201 73
    0x201d4804903000c07010303155400e40d994962403014a640c040c5441042c0d0205101c140c00041c0c1d0b500115075094440d80c01004c0030041e41d51603005543c903401030407401080040c401a50520302d003881c0100e8180e03071016541c5400402071b44111600d0003200601c00700642d00300d8030015006840e008012200c1440c00c540b460b1510105e070107410754280500c0300300c410b280f00f8201075105059440c0c4c00106408686030080c401c1c82080701da082c0504c281900c990300164820071202e000d503482a40c1002490448080003100c0725410000034040eaa02000706403241655041850401c40d0108001208116542030150030207103031450088080c04144500c10074445036100040d000c600c1c001100525560b0b0f010200080c08001d1300725644c520150155003011003441d0814184140101803202e941b14940e4020800120391007111011900060010800d000050b540c0c0c0c04130000f00c0c0040d002516040e030041801d06d1407035000a081c0c40e2200c003220b01916241e0203002c00b107003500c01e0b1b05056980a0820003660b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 294113498 1250 294112248 294112253
    0x16020609060c030f03010e070804110123120709240c0f060e0c010207050409080301120f0c091506050a0c0f02060f0a02060612150106110a170c010e030322 68
    0xc522800190400340c0c0000164204c0840010303000d10b051b50044013040c9000d60303c084e416070b0720041c143c0d4040c04801c003299071140150700c0307440b101001c40b04500c11500c002030f200c108034980e070b00030082c400200f0024004010049c1d5002d441d40004017810116102030010a580c0506480c5614810000300000c200d038141c240a0000c04002c0705942c80942040813000e08224280c036805100d503954014040c01400040b2890540510030826030402e114a155074600008812800040071040b50850f0b0003101c0c0f0702c082103101d00c02500420b42c600d030118181c200c01e1109000840c150f00402c007444002e1011010a60f0302c6841000c3c40b66111890b2903202805000107140d13409005600b000c0c2c3c03a8001100310495030302103020b0f8060081030703c0d145000301a43c0c00340740c0c03a0011100e290b401d070400840100305061103a2000e110044400301a0784401103c0d440340900c0304000002541e05030000200b05400c6603091190002c1d03850400040c50841c2821070000b0901a064088483e038080040c107134000303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 294114748 1250 294113498 294113509
    0xc0132190219051b010b01090905090a020d0305030a050c0a0c060b03010e0d021005100b0304021c080714100e061617070c1a040804061103130e1b16020609 68
    0x403400c01051184099910640002c1c0030342d01c200e21601d8100d16020995403041c2c2c050246d001600300c142c503510500d80c1030000040003441c1c010318a81c41c9100300c220303920260320361410320965075010781c1d075842e44ca00d0810031000039a007010b0040b22010408010368500e17070f82d01030702d00c580329135100390040369000303034000064090800d22115a02034003604070001d044940006002002d5075281005000303035600c44402031407081c1d01c1d00c00c19400c10700c02c000080040c94009200000d608413181c11314008419a180ca200c50703002030303004991030400050301400c116030030801101a960140b00034000304900801c50394641c0030181c0b48403c1c00c0d1541e02a0a40d4a0188521407001c0c0002a002051460168401001d00c0e00352441079407401404040480382c0c401c05400b0920070b0fa0070080300c0d49024a007110440c1e0003582e001c4100c415001c2401001c0c0201d2852800c6030080c150498a0981c0d800c140b4090481c885103a80e83c1052800108403540c21182d68491100510707404403042612240c141002c02d5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 294115998 1250 294114748 294114757
    0x50901120f0218060a0e271f0606020c0301180f150212070e120c09070e1504090e070605091507080a09050405070f09050f0d050d030507020c010f021906110c01321902 73
    0x540710388230030340c401c0410401030780124201c0788181e00320b0b154130084600740f60884c2c02e01d2008158200752940c03090b000c54002256080010711616000d00c11005218850040380c201240d0b49410400c0c030800d1001c0382c0d5108a0403c031185084441c0c507907402901e04e0b00344e505d400000280e0300401401000400d4a030207565000340d1038901402440100c1e18000b0040101e50140c028881168504601c00041c40310024205040d81c81d55241d00e80390030a25020003680154403401c03a04540e20070004800010f16500242008a0446d2a81c00829040c80208030076104001c010100300008241e1400130a580040d03480b040342d10503101c0d5081001c1c00d201045490300c2c1c0e680003812364800d894030354840342e9041d4011303807003203500380c1c00e4500c0c409019004541e40801ca4003500010390006000c0000007541810500c802840361304d0004000301c40b29000d544a80186140315010395480201c4c0300014580c03952464103054813072143c001015005c03540070380c902000c0d081e0210089810812020b60300180c1c100c070b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 294117248 1250 294115998 294116023
    0x130f020904020721020d02150a0f060801020703080a11090d0809030106080d020c09070801090509070504051501080c040b0307110723100801050901120f0218060a0e27 73
    0x290f580346018100011544014500501e004580b1824082c0305071012400c1050882c0560103010024502c840c056691030000d000401155507a0302903070f0f401e0160b480b0b0300c001844880d0000da00ca039102c1c00c0180548600a000042550507c0c1c0c0501d0080c003400203c40c00d030003007291017800d15881420802014024404c2194140d880e00002085c003910020707004550207080d03802c40d48001c41901c10310000b0801610414042044000140320074516a0400d50340160454102e80341560394000250903601c0654120248140300e9000c0341c01075034071440c0030f030744800320300d103901e180618014500c0e6a6100041c1444c003004107415080c000c1c0c56090100078001c01c3e61030844e462084114120340c46502c581d00307010740b0485044540d04080c03070180b48560704a410040030000e0503840e200507210b03581100319080720310788003150403400107aa0310801a009411805014076140c507048060058049042e0050b5034100400c000300880011400e035001580d42101102c82c1c0404003d591452800d01100c010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 294118498 1250 294117248 294117251
    0x504110301151e1a03061c030c02010f05190f020f160302150c0109060f18030c03050a11030d0507090815071b051b041506080a0c050f030403020a020f0f130f020904 72
    0x42418031000130103540a00800c4482092440d5104100810345079041c000070b02040301e080305100598010101c0c0a068441e84c00c0c0075290035a14810106443c0c1a040d9900c086034a811254090a504001e40800e644509009060960000c9921402e65050f40307c001c0c4070f9829270201c10a83c8000c44283c0300c000b13101c000280b080c14110300d000c1c4058181c0e9500c005200b40b8011108018005001d1003068464150711420355810441c1c5080701d80d54404100340b0203015800c500b09010040820041c07460701c0c2003100c0015603042202c3c0003050718800f54402d0005d540038844107500f5041d10518180c010199041144e503a540c54402010031030307500c41014056025590f01010180812151180f0f002411a01040b62038604011240c1842e514014040000e44650000e00e500d810395029800d800d8090804c90704050030b268142034a5801124100d0060300300ca4091821404c03d15002402d401d422181503528101c1c0401103002410400080f8000b41e480344040c503840c0300c180d4102c4a030310002400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 294119748 1250 294118498 294118529
    0x40b0a020601060f0c0218040303110d05041203060303050f21010305010b1f020705090c07020a03050d110c31020a2006010b0f0a0e030706030504110301151e 69
    0x19403101d41c02d108103004900d500d444440c441e0302c601c480c107141c1a401010300d10344500c007031090041c1c0f070781c028411028541e032094800342400e200c001400c0780007054107011032140b03840c2c036001d2410044041018145400c0117400d100094224080d548840180b903410383d290162811241c60203110034115103032001c07080d8000f006001064100020f0103a0580340c290640d0701d420b4088041c600c90071800c80058000d0f100500c03803454408071181d00002c015101074100017550300000d5487d0340d1350340701302c8965111000e8065030b5030704544920310781100e441c040d0104454610100f0241140b000e1030f4012a80401c801c01c1c0030040d1425007251072560a0b1086480d0f818040e0094a4010451020000ca24441c14010800c60001035820f05950040d12102d0400031452035a44113500220843c2062003c40304803541192003c01040c801004140d40214050505083c80c142e00020940c8c09070081c0d0400160310001c03030841400f0421961000e0786441184002d084120320b444440e00b102482c6043e144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 294120998 1250 294119748 294119767
    0x131109040605070f020a02100c03050909150102060709150503060102011d071806050f040b060c06190b01172701021303030e010203180d06020906070c0603050c120109050601020102040b 81
    0x30710882c4580c03403a0f1102c46100c0d4013807409030b035a00f8865000a5201c5654010070301c20a2080180005041c440e087c06d6051100400005003000b0302203e6441c4912035066101a0300d60341000403540140300d0303040100140741004811040102c00c0d2004106121002002c43e5207a4400d6110b00148010446802c881c6042000c0303081d121446031003800c21981d00c40c180404c0c80800d520480c01241c4005110080c40a240300910014000380d445465000c0803d2013403582144043c0603c61088175505c03c1c0c4c058103510480c4001c21101c884609504110a00d058a0082048028083c0c0c011203024807800310745405407444910780300700e01c01404055002280700440f0214240a02013a030b0306c2071302ca00c5a0300b000d000049a50380521342d02030a0f07000300f1202d00c1951381066407111602a00842001d80703021615004100c140c0c0c801d04080b20490100d110420505500d48a40c5400c0005003a9091800c20700d80f020801c6200180903180d03e1645c0e4502243d9240e0003507040b1401000c04802e001c1d00c803424031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 294122248 1250 294120998 294121001
    0x14040203060705070f1e0f030915050c03040e0402031c0503010e01140f130e0706091503110f090d0209041103070906151215081609090c0e1e15150703081311090406 72
    0x1072103016a40c60400c800d40480c14010001e407100c00d6004cc00441c2814540b00350300700018030190040c9c0e01401031101c10400680039458141d207648a50b11a2036172945801311615403444142d008004040150445071407540e14200c541c013082d08100c0310110120b03010781a45004100450910005105000c00011b909403c9115507049942c540760f6544c502881400542c240c2e04c00020313004184008000b090919001d041c050f01d40c140b0702510510380030704651301203040c031682910240c071001e0308003407c0152071a003040042d01520380d04405001240ca031641085c0419030300d101079000c1c0219aa68840c808160780d20003e05400e4200000381c0316644c0d03d0a15440d5a07c03c0281540901000c1c804140e82d8110701070b00c4c840c1c070343c40842c80d0b200528100310203505100241c5003480d0000044900551541c000092a0003003851660340c044642a0000b085400d0900c1c03500d07110b01000a0000c0301c003098000c541c183e070000c3d071101c540700001100c1c41d040c00c00b10303e181607080d8019038003804d000500c0b0b010f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 294123498 1250 294122248 294122267
    0x30b10020109050c0402191b0803070815030c031f09060c080601020d02060603070b0a1101050106050d18150903020f030706150b120705090406080114040203060705070f1e0f03 77
    0x83c00540398a10959420f00082c0d03c544002e6903e048403511090a03801d1050260084045240e031102c40e105805580320704447e881039a03141c00080c3c41d002030051004021004900c050707030880080c40003c002c0300100e0b465039200c0024464819085a04104074001c0f9000000364640c403c1040012401200b0064203c0030f094600600506c00c81108030341d654000120180107290090080541d54507000184040d80e000d0401403080000c044000201d082c000d00409028102649485488800301c04441017140d16428a10541c00103011525020031b9060110100d41c420b5001c0104691001c0d0500340d01d082c001000c844244c0c40002104000d1000c1d95002c01c100c1403c0b1000040751954031640030105024000c800c606440340070010811041c0541c00a000713071400034001003000d960742c042541c01c56101080602d454555181007008615050100542c00303c00c03070500d54201070040e252072040080c0c8440003050074000c000007282880103501e0860b0300f603a0000c0000c2801d6694600100130041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 294124748 1250 294123498 294123503
    0x503030421091802090306070f1211091c0215120601050306060a080619080604060506010216120305071401020703030b0f030a06050c0403050d05180d080304060507030b10020109 78
    0x1001140c01c1480c0360480004907801041e5840082e102e080109541c50805681450b050195003002540c3d20f60b1400e1012a01c41d0b010350715281c0030242000c0018180f079100d8030908174250300c0c0080c5507000580040a50b42811010303104007401c05058100d03050048480311000c0d600c4041804a050131086039002000c039030a50408000d0540c4440e0019201400250740080e44100144003c181c03031803051290310b5004200400ec04158151040300c0008a1465006030510b03070058000c0005004240c007906800010030301c024042d0b0410520403603a0310665025441111082c07220750800c6c140b00d80306592846030403181d120103108443c254a8001c1d4000c1d803080300440d0078214171210500d045000341900ca813000d00070704044250703507550800501c2c1c002c0030600c150741c09220120101d042001500d00d110901e4803020b80e504420880000103c1c41c541440344140c410514040001b4020401e03203800681c00503010030f040c0c4400c00241d002d04403140c0b003030360050307004401c041100b81d054000d00482c50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 294125998 1250 294124748 294124763
    0x604200310092903060f01050409020307231c0308040b04110402031005280b0d06090903030501061b050d03020f1e04261e0a051b0109061112090d0b010305030304 71
    0x40383c000c207040e00d500003240c04500c100450b03401004142040d0b08a00d4072107100900f034075007054590007103400260b41220000d0710341107103640c647c80c1c50401d1041465100072400d441c44420403a551700516940c1b0041004003a60b241d40c0108040121400300100c5038030000308255141e140140300d084541e102c92044521544040c607003086c40b4036013801c08240c02c1840c14448041d2a050003903207843e0342c0c884c210070003c15948000001c1c07611014426090300074403170707176000c1281d516001d40100300035981103d02480d100340d00d00310800071358001480c00c1c8030b0a8600b00940c550b000103c0c0c0c0d80346070013403880100c0c101e03a2030b081c00d0403c1444000203106840c8840c0d0700260171445640e51040041340361024045980c401c1a00c2c541c1e0030b61016001280702000130448011109581d1001c1c145040644040048100f5003a00074456801c0b144184c06444a4074000d2495050302d0002955a000301200c1c82c6130f07040000b413289840c0c07030324001c00c003c440e0442d500104551f580e14120b556903104440584550 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 294127248 1250 294125998 294126071
    0x3090a09051519030807060b041b270e070201052e0b090a2303120901121505060c0f06060d0302070902030703091403090108060420031009 61
    0x804003441114010841c2000c41c940c2c0e0700494062244903c801e00318455440c00802c00040042c10010042440c144a41000b0405040d00000d000940301c40000e0900300060486410b442d240d801002e0643e0441c1100e40aa04402410601e1a0118250708211b00000421040107071042e01504071030f004d103410360380d54160701f001600229401d003e2460001c11031028100c040007442503610107408020b10050180e54440e40d079504d4480264200448218481012024a2038a20301440861410302c0070414480c070344403408000a210440032352174114025568100c0d24400c910120a45000d0940644400e0703541b0200004680d54a13000000c621803841045d0000d0141d0030031030b110030324069250f0020401642841c1c20b4401a410040c07031030301011359403500140498060540c100342c1c94580401b07141e40b4002c1b080014515240200054021410440540d080c07002202450540801d044a29501c9072100300e160308081c4095801503414a007048081c035184042d8860b0f562280c01c001100c5183d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 294128498 1250 294127248 294127259
    0x4050103050c010f0905060702060c1204150305090c0d061d01020a091403120a0f0201021303200a1535010f09060b030703180c0602210309030a1b120203090a 69
    0x409000d0086c41d802030707814405400141804000b41c400e1222200580ea225511182000c403260080e070700684811401903058006a5094450540c00c070300a04080d064502803800403822161483d9002010103035585590001800100302c03540410301610000d56a07804a0000100000d0141c002c0c039044003140019290a480c0c00100e0f103480303a01180f5800d081806004055a109040e02100815550200b00040900d0001e07007040d80a036100301c51102e000c0241c60307551000c440c600c51005008544a403021b02482034602d90760210803040e46002a071100c000702c200104e1001c84100110141c0c2c1503607920000107814600c0314103076071203d101d08026566490325001515400e11480305064010004202102c0c880d401640b4240451010000325079003e650303500c03c030f01d150780c44000143c1104400e2602400513481c0d0203d161f802c017903d02c2c114102035171116100e201d164005d0040c09601d9100710342500d0901c0fa140d0355a90400034000303503520340000181d1203030300c0220352030f200e11046403000c03c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 294129748 1250 294128498 294128507
    0x7050c010e0d05032d0c07020d080f030114030109030915022a0103050615030103030e0d0206130e0903040e0a0203180a08030108061303080f090f3702010f0c08040504050103050c010f 80
    0xb041078400c19000c091b03e0f00d600104481d88181d030180e03044000c4501c03440c08545690004d00e00002c01458041ea29890034419034136801c14403038418401c0e41010366500101764481c05070010b681000d01e486900310007510059103414941c01c01c2a210886521505400400d400554403101d0070a8a0620640d40e5000801098070320201d006911440240010300200b8852071607010485030242840c00070559a400051444d00075170764901066001a1007407040001c00703a845600a01c1100c011800c1909101d803140c071004c0c0003488070740740030340c0071001500300420202d48441c1900c1c400207a50a00d1414105080e440e8001d00807070b202c610410f0042420404a101c450404980541c2c034100c0503242e514800e2000c00d0050080e001c076210b504000c0e2a0541e0603c2050303410741c1695401026144102d500d0142c030350309100702d0884c0c2901900b003400582d81108001800715001c0c5005040311b40186041c40c51406075400454100345860001700030480001460303079201800342c0394030b403100b0343724a01120b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 294130998 1250 294129748 294129811
    0x8150c0a080a05090a14160503030c070e0a060302041b022803050306030c10020114010e071b050304030605070906030f0c02030f07060e0d0f1403070807050c010e0d0503 74
    0x5000980c414001103141c00c003a40002c1d000301e500b13826150941c0c996100c141c58a168085e48114580040d8100d40301d045031126984010041a4040d5050038401407015440305894820f0084a800010024081d403455600003000740d07500034010010130020300d0340c6400f00146144841c001d072090310200c445e00c41c000110042c0079200074092002c0502256422102a0809002c1c41c1d018070070713074501c100c0c90b82d80c0da40300021002e21a07000181c460f6121080b1640103d041e41f144046c0190301d000e00000c2580210660b11720303820005c04c40018062441e2044c5144215803016080b907203440180030350103074401d144070101c074100c0e40c080c0000b0407440000c00489a011030b002d00507030700410201c0700c00106800680300480c0980e20014240c100017002500781100c0c21403040000c0c0300c1022510303004c2d820038600d007002d0150070142030030b5181c038038005400201c01500102c180000440c06503414a002d411009500100c5016a240c0240f071610190568000b0fa48140c01d13140340c10890843d00381d40341c0b80303039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 294132248 1250 294130998 294131017
    0x3030a05071a190f020d0e21090604050111120423061c0b0d020301050109050108010c090305212203020102010605060c06040b06040209031506040507080106050a11070f08150c 77
    0x9003500c0f110302d030b501c8010a640781114803400c4e001d10074810a91001d1044c0c1c15007441d6007014105928015034000b030b11a4028802001c044010f000c034140e0354680209582c19130b00c00382444c184295080103076515000d1b4070300d01d10112000c00200070038402d07401007181600400c1c0b500180f075007510000820101d8000c81e003841c00c00030115412100055195007091040d11405442001c00354031580109003511000d0300b05030341840e00c4000400c5000000d1080e01c92865091404400c00d90031907552a450b007032002d40309021030021100c4140c50b5000841165410503c0d8052080030080070b82d01c0300c1b1007491600c8141e015500c0c06800007040e007000b0040f40c0b641d03400ca4010f030000d560f903541e695071946009428550070981c00e000081035510b0402c5520b03031074138099440000c00d10b4000c01300300035180c0c014a014200410f010042120b00d8020041c0c40000205013003180d900454070740094901010f580c032246014011001c0001c680301c001c588210036107840b08842090381da91000200c40c0b0303c40c28212 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 294133498 1250 294132248 294132271
    0x9100e04150e010e06061509060d050601030b0d030809060705030c1e0d0e060f100e0c09030109020a150306090b0a0312050c03120f070309021003150503030a05071a 72
    0x90028807004000355504101d204002540380c0070000850031564a02441c5101d40d100c1030900c612854009449880021030030a4649003124000206185003d8001c40640c1c0f0ba80b01c00115042d80e02070780003104100000380c101c0003014450b0500410580302641d03090b1150103808081130405120308112031042441091092509580e1602494441043c1e2298411201e0a00610031200300c82d01419080050b820014281410400712000844401038000315044000035802c0084a454114180e400341c00740a1007038943d40ba8101007809042c590000941c41810b690004c10071844603e8420710078100d5507020400c061721405458200e4003200b0725150b102d909910108000b81c6054241418000035281c11410181da1100481c9507821403003441d189489010304000611098004440c0d11401600c4c00b0321550400f60085444805500c0e820410941c590a0342a50700400300001e90007400050b0885c0d40c1d80280c420024a80d0300905001c0380caa584103404409407032110038081d801000584403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 294134748 1250 294133498 294133501
    0x60316030c18060f02030d0f0c180609050d1e061e090209010b03060a03050303070905010e030105060a090b0303130305060a0c18180e0d0306060306080a1703100e0a060509100e 77
    0xc00e4580c1481c1200000c211b10082090b0f4030326100354010f180c214200d40c400802c1451000e42c0107040340c0040000c220070850b85510070410300750b10840301c01c100d40e005e90702e64903660740c2030401a4820260342520f00d140403591038114100a071551181d41903800386c0300c3c61800c00300c152032400191000448085c4d40842c440300144032910010004640101008010f00039540c1d80fa5182030454200b05e42800220360205400c0120f0350b001444004070b6401103008011914000380041c4189541e405590343c075035525070010049840400443c2e8800b20b4050881e80803c0e900d01d0002d5072101c04684c0104100d044c00004c4900c14004c060080d800403d40890103406800c1110b2a03c0c9002c100070908052615040c0300e46161106200c401e14042c19a07502140d82c500f072081c0079080d1440343e4031484055000840d410041204070543c0d010712181d044400750341762521051502040d01541103c000c14883c00700340920071040d648040d04994090f00d460100b9039400e07401d40240002e502c21102d200120702d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 294135998 1250 294134748 294134759
    0x901120b010902030916030605091002031603090809030f01020301090608010e0a0813121505010e0112021519050408010c03060302060a111c0908010e010b24040302060316030c18 78
    0x10095903005c03000304211205042003d81490f03860459074003e803610360b560340602c40041010700101100040342d4109615504200c00e42d00c040204c10f4100d1420142d407080400100900c040480d03848071002021605c0c030f44210141c4500075413007841400d202c580b5017040012082c20602400d141115207101401041d0000e45507900396034049000d02ca075200d441440030860300302c103035940010140030f400800c410b071050990904c121103068028a000100c0a4010003492458000c022016641503404180881003544130000c240907962540316081c910001e0006070b150b10102510403142004000e015818500d101682121494000a5000601085045503150080d0880010040080d0890340d0000d29030740c096800344017001e540c8001440d028800c10850b4400d0180300341c1101a507000300640816100000c111881d04080e0052600800041e0700205801c1d000365401540c01408540d0349181c103910b40c1c00342100c1500d0600c042803902e0711014070f0070b204d4203000c2c0d88525204c16490380f0f6818031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 294137248 1250 294135998 294136001
    0x60908060114010c121404060314102402100e01093302090d150b0a09110306040504031106040609021509090f150409110a051009061b060c0804020901120b0109 70
    0x11801700c00e11090781102c0e07144086050041008007101c0e90009890811510b002c003008102800c0f4503400b000d07000c8144402a0b00155511701a0540100404080e0000105901f0002d6188010584614240c0100010340d419000301950a1180707480c5070312901c0301d81c000102c0c10f40380c2e046a0f4010b00d002c2008200004603500504401034000c2071610085140d50b207801200701200402a0802d880c0c0b2600721003814030300301c99405441c0c103000522000164100d001090f02004009070b10843e03d43c00444c007171500500700c103a030030302014040d12654600340c07c03c00d001e484014000c90040100b0350f030007251414104281c80c0103800081940c00c403616401e01d5101c02c0c0034098070060984245c11030b0500700303a4a40c032805100c00d01c0303120490300c1c2e007030b941d4100400304105a00a0340030702188150f003650140c3c003035070f2141520118100f90110041c6012103000701e2a0b22a40141082c0c070308004c03038000c3c9801090742e0b44154421200008030b030303032900403500c141c5190000c010f1280f4403100042c010074205 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 294138498 1250 294137248 294137273
    0x100b1809070903060504050d08100b0d1d1203090d14030604090302032101051e0d153e160803091518010e1507180f060908060114010c 59
    0x39482c040d0100303620307602d900b82102c03419a401c96030360b800341055034842d035040350a20f948a06408103441d2820700d0b2100c1056103201e04030880040b107030340700c401601c0540500f80340c4006850210454014601d50904449143c0c0241d4074a07210340704150b00080d0952181c070003000940034951b00182581c0300c000920019191281007181540001c1c4045800c203460450b8411903094884809051545410144280b152080a1501c0702034544100301c001e50b20380700390001c0203e80c0302045508100000314060000c100c443d0700120540300341e4446403900c20fa500f001c80c1510510002c2407613001c000c0c1c15805507500c64071038000424903280c035440c00403840b008003450b444600c4a00b031341c209100c800ca4005000c10102e41c00340b91000c0c81504102070000134803604841035a0030009007508504042d9000f5649002001c0c0350820034070980c07104040f890900b000006100c690f6562100700e40384e81000d0038085050041050303521444e00001018000000b0803510b4081c1a110010389039210f803200d1000090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 294139748 1250 294138498 294138511
    0x604060e0c0f190b0d06180606050306010503090a06020a0e130903090510030b100207150e06190c02030a050f010e0a020a030605060105071a150906030606060c0f0102070b100b1809 79
    0xf02090700045400384000101045c1c24408000a0901c2c104000941c0b008042c03c0c2a0034400e01d060b4092003803c3e040800c5a8100b1401d0901c1d80e200c0c0c0d69806a0351400ba64668000c104c00d001050380b003001c0303400c20541612000115034a15520401a42c95030072601c40c42c4005e400134806410402581c00e0003207500224186601e00410101404408610104446110f500c0182c0c030100c0b0070000c0106107051100b00c0840c5141913844016144002102c9000d080d00030f600a5400c01540c8601501410124886960190603124805840d003400703900c428141c1e520401d19402e03c440d5101410000c02c58442c1c42d0b0b40184124941030454403600300407c0000c0c010b0b81408800c1003054040784410340d4105c842c04c0c106c0303182141403401c9000107a81451481c056405504540144160b83e50b01194455206c4415a41503448080c031845803440d004c043d810115807544005841070038400c036800c0c180e10a044c079070902e9200a546850b110070901c80c4d848100c0c04014010010102464806511504420f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 294140998 1250 294139748 294139789
    0x108010314070e2a04060906050a030f05130b16080423030301030602130b0a0c0f020303160501090c1505030103030f020a0c0e0f0a1a09130c080604060e0c0f 69
    0xc0c0c03100c3d6403050450050b80d00c030b0380280c0b03100700e40c00c00900920180e044124200c80000c2c281807603c0da0180c9075035100d0040c0c2061200201d4a418424031030340c8840101e44c01c1c5801800942030200390b0000e0f02003680c5054801b038081c4800110110031644041c2c3d16188203949802c0250f582d85c4031244600004081c000c00c3d01113a441d0040100d0f0100050340c017a500981c80142d0301c02c54031005500f580c02039403003d0300c0340b0010320103100aa500001c241c140030750000b045900041480c80000d00b14031074512101e850480c0340d260403060140550141030460304c94080f90a02c41c0c1c03a2030003010001c00070350160001440030070050000034480d100313054170b01003a40111000807000740c5d40c01522036410b07080700c4131008004003000710502111203002c2d080034012400700440444804403080005400350980d000d44181d034045010204c0b1102d2469120780c009000d9907500e5140d41c0d50503120801914295901d0b820010480c62038000821503104070007004050840b141e007040d00340b0451300300480312020801c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 294142248 1250 294140998 294141013
    0x213030503070302150921070c090e01060609050613180209150706140609070f05090301020a03091b050d02120c0a0f05030f0609030d0504080403050d0e120c0108010314 74
    0xca0400c09010840d00c0394000d00380b501100360782e600386810020b29000581d4809103072400c80c0544000803044165407090a10341d03039685428941041c800a41c0300c03c034403515091010403811410740c003074400e440305a51020341040d40d48040081c1401b400350410748245e65190100920309403200c09149800241c0c001504000c88040041d070481c0c4940303500401c142002402e14200101d510584c184418580d40c00841c1d400e06038041040f02c1d2000b032444040c0f11080280d4460203003c1c02c2505ca02c180010300175582d8000f44440140070301003111044451209072403018801d400130a03401400d851300a05092074800a50b001c2003959400c1c070383e080c403141c0034003000c0342c4164a44826142c007a100c481c2000051030b142c00c0030b06140c42a108609070b09508206d007072124502c1e0201c12030707a02640600c0e02150707940795030130a16060701c0396500040540c4103075400c8c101c0301c0390040d0300300e03a80401c11509802c2001d01494119103415035030b40e080303000440b90401440000d0304590031100c20f241403822110103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 294143498 1250 294142248 294142253
    0x2406010c0c1203080402040c02190b0723071a0405032502090405060103020f060c03090d02180a0e0105010b070201020d12150b1b01023a050c0a030605040507050d021303 74
    0xb580880e4000b0340c0002d002d00c0800c03083d82800e02580501028610041c14082d00e00c184c0144010b082c0c0c4802041801c2443c046602c440c2315107010340d40000c40e00c103552140907010f40348840300d41c03240c42c0841c0c00700403180d44400003200c0205620311481e00f20300518500a01c0580e15869042200c800c80c034414551a00c0d100076032a410881446680302d040144000e5040d4010081141700c2902d215100c3d0a00f0421920950001b10a9075500d0200380c480301090002440003803100d00c210010044500f0f409410016050034a800110072045203200801280c1d0302c40b40050418802d1801c064056848007a44902040c0700c1d00c0b030015003044102d070000d25090702e0154032001004945c13050b0800400414040c0e2040005a0003100341300c00c074002145082d50b546401c40f00079405c0d8080040c0030f0b01e0009501c0c2c189034a4a0280003561894104000c01e10382441e00c00c21640200c8403002c002031404801140c503041170f115441c05029942c03110b6040080d1721764004060b50080c6103203041c03200503c400000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 294144748 1250 294143498 294143519
    0x15060a08060a020708130303170622020306030106030807080a080108060601050a120b120304030201090b03040f0b0403020f0106062610051c021203041703041503020c030c0607050c2406010c0c 84
    0x1540c407039035450105040c0f000e40110852404ad0a031403185940c41c2112030b030342c24224030a003642c140803640544c403560766200080c0182050360001d4010200007a00b0010020b0700002070414a00c4c5407a010020390302c2c0d401c2e180e681e003404c1f101c3d14003145040200107070350fa0041207094509003050001150740d052102c04101e44280d020500c5c0c00951001c1024401c41da0481d002e04043d1000c0f41640c0c3c21850715443d0000300d50034200d0041c000c0c121040101e003d0510134004c4100e4404400000d011440d40c4079401441650340c080801c90382e1035445160322a400f154515540120100740351900058148020031480042d8110b46c0250030307501541c4000180ca5106d01c1c46940110798010310b44540c90a0803208082040c1c0340303080516001040140086119100d00c0c1c59040400e113401a140d03414412094654402c64400450300d00c0341c54100504181e0160003000d45101020565419000d11855031100c0311038503940c3d1084010003400075465510070900350401c980034450300c80303000799504003114 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 294145998 1250 294144748 294144787
    0x304021c03031a0d1203051f030c0905070206130b102304060b0c060a02090a08030309060123030703120302120c0301091d0a030806060903030c15060a08060a020708 72
    0xa011a4a6940c00300210f103006211094002d0103480c078445546041d900c10008a1040d4058405d159959010802d102d104d51144a20451100c00d03051681780c9030300340108442c4043c03041c1e244c01810300000400c07181c80031840074003421403441072000a070300c0c1d56030f010031011006144001c20f0f0b80c15100001c00410464454084454030706119160503846018001945e5903600300219202082060a0b140080006e203a50701c0700120382c0c0180c07034954510000d82074502550010380188004000c0c404505070108003103040705c045070f030082d8290f02ca094031852012a1420596810b4001c00c3c4104003044070310504e8601c1c0c151a14006140c108900101303910b59500340d6009125510100c0103101d2010035220300c2e0700410f14003a80c0e404585000c442140e03174420342d0100404124a4a020075203a403108015074900c80c030014180e03911a2541c0c2902561ba070140d504d4240f00222983c04120181008241c000a80e0700c04009028190746020a004c040d51080404a51780c0d1420003e10340d2008a41c850130 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 294147248 1250 294145998 294146003
    0x70b06091815010305060606030105010c15061206050a0b1504030b0901140103140c18150d0204021615050c12100812030f070f020606010e130911131e020304021c 71
    0x12a9154110b0601d40d11b4880f0081c0018040c040400040c800341c0c0c2c2241c40300d220503a00c082c0d810f50300c1540d00da41001806d07040d0700480802c504008c00804002158100b81e114068041003041751491100401902480e51010700b5002c4008200500100e885641034940c0100b00d0300001c990b1845c1d1709020044403409030b00c143c0e1403004402031040c5105060011800c480c03822030300c1007041019401101c01c45680902280d6080700300c0580c0201c1c5031200c6a0181c0110f400030710454440c0c45012103a454408031440407270b1a143d2481090400006074030880307000320400c1160798184085003610141c6400301500e022442901c43c60000b4440c4010040c4c050f05e88580d00e0b4140c2c030307070a020701940c00400000d80f800d41401039054100c032659a0026155600000902e003440402000102003100208948001101c542c00c0111000a000152009085031481604c00786411a050542c0500312200030440c00400b4602c140d4040d000141030700030b990000d000826418000c0120700720380c080072010100c03c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 294148498 1250 294147248 294147283
    0x120b0616050325021503071d1c050c0f04020708041a0c03030106050d0507020303060d08030709081204050102190b010b031e070f1814090c1608090405010506070b060918 74
    0x400214200710548281d01c9256212446c00d5041480d00a007040b168085180b030307644920001804565143c0d411441c0b200800d80422920700f403641881034560341d04416003030103001000c80a003a581060300c2242c90554211a100c0c1c00d00342440ca071000644101c01c0031240504080c49030400c0d003030090000b90b00804958960554450103c00e1060641d41c004242c0c1c1d0654000307001f000055102c05180046159110b150303c0c0c4d403540d466405075220b40003900113080a21a50491050a05902d0000c2c803d8032426002c13601d03803490000e2039808000c030407100108040c4521004001031005140038541040740980c0c5018a200b00140d01e0400c034900300c0e40c010015401d00e05420141d600300301c1d041500090804241d2505050002003150f07041b140407064042c81640e00000c20b942c00700b03800d54640d81d2a142460380d03000510700700b8a0b00b9070060b0b01002d1051349040c1c0005214607020040310b01070303a8446032035191980c0d940704100d00844000c1071490a020ba201c42047c11010600410000c840380514 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 294149748 1250 294148498 294148567
    0x70b1305060301082e1d100c02030412060b0612040c0e070507080304111c15060f090902010c0b13050c030c2d090a0c120b06160503 58
    0x410650010065004900400c410070051084920224204a03140e4080308580c503555500d0311502200010142d209105619081e90191255810700c0c0f01c501d03a000c0745003110211046004080c0498070040b90a4000da80b00304030800c00700b42c1c0461400801c0e40541c03800100b034445400440c64035801a420b00c07605400d10701c10042000001c446640141010380381c5a00d40e80381003100901607204140000c4c001401c04000142000b140c2020481a80805858512010203030382210520524000d0212000c03138060003040d214030418800d000840341064100d542c0c3c61301d03103848503000309480c2070268108051540b503200400e80701581d4501401c0b2070081020017101904001c0e0424501d898007610941140781d40427001e540300b130352900d85a50782d0f01a400c080b012084007404003244142c08643c00403811400c01405881c4c6500004d91740560b0344840440c040e61000e4040bc65649040c9580c0c840b4050144644c40140142d00c1000d10388510201c074135200e0500034000075a040217041c2010b1441e44c90 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 294150998 1250 294149748 294149767
    0x90c0402070b0a052802090616050d02060c0306010903020f0612090d0f02010b06070201030b0d1703070e010f12240305070f0b0a0c0605060d06020d06090606090303090e07030e070b 79
    0x442c41743c2c08100ba941c0c0e010036005241107074001d060014030b80102d07990085111900350f9904800c5850301c0091340500300003a215850110b0f02da0802c0c050340400b42c043d403000240583d000380300304d91241c20140c4da88000c550542e0b0801007001e0700f030602141c100409200240710020640300e0b241c0200600001443e0918440740c008000040d00445c90381107904240d5046059101c074800c1d20341e419030900340801c0c409010340200c0c801d61aa154043c007410060b01406c103645111400640c00340702160380c1c002040304448019a20001c1d0300b448a40014100110740ca41c40860354400c910380c0c50032502da50f0908002a1304400551a03580003540d16401103181041025108080d2000a200060406040c8856600d01400480450201800d03070703911600024207c2d50750010b003801c5a940b01c841151210311990446000380414010381c8142850081e022401500440b014000c8940c143d444910309804c1c101c81c003065171400b03004001850786034140441100005e11907040a48807400341180c80303c0a03803 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 294152248 1250 294150998 294151001
    0xf091406060402210c070209040c030b01050405271c020606040f0b0d0f0204090c260c100315050d15050c180105090f040f06080f190b090c0402070b0a 66
    0x1e00a103120380d00c1008030390449450001552180f180c0081420f44680c4d0340111401c045c400c044000b5482602c401c10402000f0040c01d55405036400380c04000c2c070b180e890704140700480341e05542000400384e0100c4070040104105600c440380603051030984200d070500c07031101c900500c1d00340300741c101682025041100074280b0f44240725003248040d4003400021226808940414000c810107011080c00ba8288810b6403110340140d451294403a0311000d480d40d444c4c02428690171000c803040c20080100200801003a00090741c0011940300500032190704145880603001401c0d5413041c81443c0d801d0b450700154950300c00c25019030003401484424803100207505810211140207200500702c01051180c8245e00c0d05002c0103402001003820300503695454407002441d100151504268401c2c107100b090351040c1a140c11403411540348100320f842c038181070040c698079420240c3c1c140d00240642140440800c4019076200e80101044069900601540340440e09030783c002d03c0c013980c920f8802400d01503070303481c035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 294153498 1250 294152248 294152251
    0x4090f020301050a0314150a0902010e010c0302030d0b18040609021c0506010905041b0f0f090263090f0406020906040803041502120c030d050a0f091406 67
    0x89004526660504000070f2000040f40000f4108088800a03042e010308108100000081c140c003d00002c2d00e0988960f60103402c488504900081c204100c45203d54060322a1b058003541c16005941415000d03c0880c0c01004445400c07644103204599085502074500c0010b8010b601820000c030b0004001e0060191001d8190446114a01d0301065a8003061020030700c2815503401c94001b0410751958108081d180740c00c0500008901d007211000900b6040c0020f020007140d031089890740b030595a8000344400c0b4000d421041b095480d117000301c94074003001503000841204118807107100c03640d00900544102d81d5001001801e1001c80c624019074442e800301c018081d10f404813010300c941c3c03030800b030b910501100c0600010a0b041d0013040c10384c41c65441c04161000380c4500700c00c60351510f590b07008606004502000d00005170003141c0c1070012540d085402c54450b0450b040007149400900800e1100411008200390b80345903450710f110000056602072124402d018070888452043c0e000d0409042c980d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 294154748 1250 294153498 294153521
    0x12021e040b0d051e070e0103060510020c01110d09120f1203020705010b0d02010507030e03071e090f090503041512020c16061d010e0f030d08090c0a12110a0e010b0409 73
    0xf0091144c252051011000da0f074804110324105051081d0700005a001e88210b401c80ca51180401c041c491201ea40001c4d0b0b958443c0f000d0f40d441036401440c2c2c582a8803000329a45031030000340020014414100c0c070f01e6070b040b10140729034003889000e100d0b43c4403140180c1d01c8002c5040080d40000e10708082c8a400d01500103c40f5046841c201050385540c0080d00a01c95000d0080034040a942e0524044d50203208640041180030503050b0307038840c03d0080b00d40038100c0e8050320010616200c1c2c6c100600380948252043c00ba03105c0008e5280a0910302c1c00c1010705000e0f002081080b48107000303125085842c0c00a001440400401003810402d2031001007958105904004200141007142035800030910100b207031000800e0904503006d4036020085003a105442100d96058820403202d1011070764040381c4240320303060307501c00c0d204020054000c01c91010720511030107004507190341000740403552213070068283c140c00801150f100c664500900901010990109000300c8000c5010001c078503e0340641c840820 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 294155998 1250 294154748 294154771
    0x1b06141803031e04060b0909030c06090a020a0303080c040f141f0818010908030f040201080f0c071e150608070b19140d0204090617030a12021e040b0d05 67
    0x82c00624142e1120402c0c00d0315030400c85510f000c101070244907400300c90fa1a0f0081e20650f0300d864000f8603242da0f0741c002c4106080034481c40000512200c0e01055401d052076000b88007035445031950b2003c0fa00c1007005880103d060004000004040c100d111fa0040145582c1f9101c0c5081d50004082000300d0030060b4542c0508a000d00071102c00a5104e5520b907808110240c20405500038002598014256510000d0070840b000080c841e9440030114405d1265200766114440380d5200001821080003d48108551000a104031030008200c40d01d1107425603103211030078261114607110501118a201400c49070260348100074008198184594405040c8592001b03140040742040384000c82c4c3e03c002d1820800c160403600f071f00d0b411041c0301112166240d8000664941c0e0715000d9100041c003103489103007020482c648541211103008015981c00d00d0751030300e6425140b039031840700d81c003e54030000024206840c3c1c501e0541180c6042005003000e0075142c10815164000c5003030000807908040c00c21404103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 294157248 1250 294155998 294156001
    0x507030209030d050a090306060308090418080f03040303091a040303060f03020114090103021b0d1205061021020a050909070306080307030e0a05040f20090d02011b0614180303 77
    0xb5200020190720050032442c1c00e075552201081c3c21107440c4202c0d00020070041c1004400002c1c810048042d00624030116420807070060301d881314440303003090311034018400001808680c0c0512003110195520031b0182c100850701043d180d0300c900d400c1ca103401c80190800c10490a020505901d48a14000f07001050601910a030a540010305882c81150403202466400912642c0e80d0340319070191440822860071001038080c0802030740740c440344100300703200004480c01c0300d4150101e0310b400348a006000140411590740c0000e0800c94481e074200702e00c015001c141942e030801c0d11141d4401000d00c2105c42d0f981c1a00c80a101c001c10410b01c5014024804250134800280010b090210489074040d5142c1020f0243d054204085031101840c3e602903680301d45401452106110f180d002640d1501c2c2c14506003030310b6070140f4803400041c000d86440c2d4ad040301d00403000c040154046c9012440f04825502d0b495200c007103e9569909a41d8240342c07040800b4044410301071f2078082618102c0240c00e448003c0d5086 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 294158498 1250 294157248 294157267
    0x7180501020c09041a04080c010b09070e06090d17070302061e0c0c0f1501140108010e010501050c01092a0603092d0501090b01060e09060f010f0207090504030c020405070302 76
    0x50b600c0d079840d024410b0908001041c10003c5000500420840756a81d10201d407400c0d0a1481c2d02d600a6100c0300c00035400d080146036140742682540e4402c01c1a40c44505290350b524080c40130340e0304001e9100350015001a4000f010562811a240410080502580d035444440ca070023030a00d20050310000984408107906034140001c0c100d45640940c07224103241d00d1389542e2092901e8940c49a85d5400c140c0942c010103a0324482080d9440e061700c1d098902e1385404403002c4011038070100240728406402c000d0a0041c400781d84910014072911280328000b05401c0c9140d240c940380160340d1251029a07299035450362454200d1403101c44001c02003070a04001c00390507500d40c09880c050005030040041c0500c40b4000d82182c0c041d1001c0c030032540000082107950101d00d040c0c45010000c1c06504049078282580c64a01c1c54000305143c41107002074842001d6088820041d90070715a4254440c00f5402000c00220303d4003d14495280702c0c0f406a5609549100240188000c13a0340143c0341c0410503004004032681d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 294159748 1250 294158498 294158503
    0x705070e160e060a05090d080a030203040308130f02130603080c06070f0c05031608040b07241e0b0d050f10180b040f0302030d0f0e0c010503100902250503030718050102 74
    0x2d804c45541000c9542e601900700090f034500382100010414075010540e10728242c5d141e400386101d1446511142d03080e0700c9031054650301c20b2032510018102c008600b400401400c00304011172803005d0b80381000c01c19036102c2d51841c49580090700d405845d030784844100141240c0c0081d001d0390242c0a803d0a10074a0129183c007502e0f8440c40d84186010000310701000208041602150020400c0b0b155032a10355026103004400b80e14503442d42c42040542d1070050380100c43c41d225000800d0f14401a10568825400c020000340043d200803580c04040021440003164051103100e03c4a002c0700041c202803402d0004400881e448554104655111030f509440003603941200d160b00706e500320031400560450761400328036622620340b98600c11410008801062521034208903400010740041d80d9040d901d08004680302e0100f1240700c0d441c110600006c000540c0fa80e4000c210303180350404007196902600d600400c0350390b2200421581d5610001c10000c00340d2740494042c200c4960512008000352400700002d6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 294160998 1250 294159748 294159757
    0x3140f0103031b020d08070f02040606050a020706120b100f0f050711010507060e0102041e0503010509210405060a09091404020f041a03060903040302010f08012103050705070e160e06 80
    0x941d00282e00a00c43e043d591800802040d056011501c180d0b590340515054510003c2480d0803030050b0300b4400007203401c1c2c0c000e0041d28110100340d030091069a2800e02d08950545054060380a03103980d4017440809a26003101582a481d05a110840620520200100a011f0300ba0024040010501101000800c0c00c3d030740044000d03092134102e480d83d805040000c0204031600c07120106600c0041c000845e810607503400d000c264403214207603e04030758a10900d401d84a0481c0d0010f21900300d00e00c1c1628441119170481305c0c04c000d000324541003580b207501007a100c2c0e10510790400400da42050402101da01c80c000d034180c401b80d0800840c07aa05259010811b40c07402c1d040060b2003a9150001100f06190740c5007000014140101150041c1c2011401251254007a00041c0d00048911191000c094002e8140d54100c0703254030251a5020071400111482200b131100072810090304001c00c07030101d20200195070250040612850480c00c0916560160400c064120b805005040400a04942d907080685 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 294162248 1250 294160998 294161027
    0xb09060a0309022710170a50010209010801031e0515040b0603030703020a080901120e071410140c03120103140106061106061003150603140f010303 65
    0x890000c2c034520008180061301054001c000c03424085800340c4590819030503001d180391059032060039445010304040c00220060404140c1c0c840300e410030003c2c00c0c035402038464132010140d4030301102843c1b6404100117803804000d01c4040300d940c00c00300640704081e4500c10145080000310303d4102c010001034040e1078144000750103205201c2003014514032110304000e1030390384201a58080403c0341c4043c50910760503101610911041400030b059030400004888000c0e405400400c0c000750241d482c000c150b803040014604009210540040740d00550103001d14810b205c00c0075246c03250619100809181300c001c0094030a45000400f40e128175008943c4540d01c55100211542e10301d900784420789144502038003d80700031440c400000610543c01e4941580c0d4518100902455650b03010856500d0288000300c00c4039080907000c102549412000c841e031503115420003041214245400c52401625980424042030711a009100d000201185642d40000e200d01542410350546d01e004000040c0c20110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 294163498 1250 294162248 294162251
    0xd0f0f030b03030409020d090b01060306081209010c06020406081608010b041e120321140705091906092907200a06110f010c0203030a0b0109081608070b09060a03 71
    0x1c14640e520b080c82103030042e0810708002c0d956500c58a100400500d03040000340c800000c50400407504901c20f00076101103441c80001460704c400c0501e0141c06552211030058103000203000854000f50b81030010344000c1115448903101c0d0300d0f02052980014481e05403910401072450014001442034071305075015140da080c6004004410044d02c0d540040050300410680c0500040c03010030143e010709803031180d034014948481c8441252070040d040d10b1814140c000310280c84800950401d00c00e50142c07054106c0100b0f005a01071848081d42928481038100100040700500b088c8401c0307e076040010b922984810302d40782d0711122110800c0041c0196100146188128070f2401c502512400550159800052203196100c0e581d15000d4080c0e048a02d1101e002d005501c000340c42c010040c85032561464064021314550303544c0225540052400480d59814082c500c1c03030224103030a08101c3c0d05800c03203010f4032240342079050030000c2d45409940d030b11050186038100020034961300c90500369200946c40342030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 294164748 1250 294163498 294163511
    0x2010b042a020703050f060601020f1c05030406021306020f0d05090a0605030606040b0309071d1314010e0703080304030915020a0f141902040f0b18090304051509030d0f0f03 76
    0x403030900f1425440a8414030441c600c00e0381d03401020a0b40750144900340c003102d1560b000c1c0200a0b4403141d8005240044940c50307413580d01450b009000440d0b025100740801483c0030300c035684280c1040040e40200e03005a001079440e2100c034004002c0c80c0400c06043c00c00f182040c0b1040001800001a0302a0300d00b01700011021070342d142c50301c0007901c01600324055495100e1400b4221513998110f144a0b40100d00c8407201c00030181c503100c04809000e5515403202011f5040705032600304100030b01c8504e180701036585003440408a2802e01c000c0001e14441c1441c640c1c2da0500d0f081c01069000560016515408a00300559240c0d8000070079025070741e84040400020701060403d40c5003072507551080c20440c0140031000380c500c9101804012170500c2107508000c80c10740a81d1100c02c6505282501d50015941011846d4400c00804c001d07170310009250840e40740030f4641000c0760941c4141d1901040c0b4103408242200c01d80360601080110500c0791178154010b514000c001403c4810321a200000d1640c1c0d0503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 294165998 1250 294164748 294164831
    0x80d08091b031e16090b1009032303040504060e0a1505030d0c031b0803060108090106060912050f01020f120c0f0d05040f0215040303021603080708160f0602030702010b04 75
    0x1340c19040d4a62079920035201d0f80d5502d075076000c0c080c07401c2d001e0312900342c0d685400400c0d0b0080390b080d001c2d01d4010300c4980c00c074003404096072a09544810302a07110b100070b010004032a9998010180540444580c03500b881c2046164070080c0c3c0d403200703007184c0074054812091000351000038409804500c42c0c0341800d962409801d041c1c4290441101d02c1c900c01070b06001450a2042120082d40911070a0740c0c0c03458145d8400c84641c1c202c501901030800006c5035880b0801c01c0f00c0d0340a00107c1c980e4022015945415140c0d180f65089034050b1151006449021803440c00344041c25079000d030b200c60014003240c0751034061320040003144205210707050000d035200003080500c60743d01e2660703201c150301506031319400900403071505541d00148021030040c8640340384000001d006403040021281e00032804c600b0241569035000454005481e540c1c1144e110344404d501180342d00b402000a00d000c0c150060362401d10030340080c00d541e201042180074608141441742503038802d903441240c82c120f1f5241a00352400c2803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 294167248 1250 294165998 294166003
    0x306030203031614010911060f12010909022106010614090a0e090d0e0a05010f1101050703090c05040b0a03060b030c030f0f060106080f041506080d08091b031e 70
    0x5810194151101194002019941c20180782500d801036408801014404558500360740c02c42000500d002100d12180c0c1e12410030700b002e04181c40c40c07000c06c5130603e0100109040741c15000d1b4030002c02643c0b00c2c07003d8070541c102a403c2070403401c0c0c021410070448a000305003554641d010303c00d150401030b40c650500c0c9011000d5090300e20544000304407480d80307550781c403e1115000090f00c1002e000d0081840c0702d40c006010309010a60300102824551209103044010342c0d02844044041d410b0243d050000c2c1c0c0c6404003031040034840c40064600240500e041d06003c901019103401060103603282c000b00b25034943e508044801280d520840200b480340c00c0c0404a418214060111070301413281d42d421104480011814507000515202107035000e82e0386100440700c64805589401101d135080001c10f0100c0e2565a21071030440004601245055603402864a0840e50b0300c503080c00140c0d04024092090000c0c025201c02c40c3c24800d101400490060000340c5900103c0d448101c490030440801403000000d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 294168498 1250 294167248 294167261
    0x206010b030f060f060703081008010209150c07080a0807052812031512120c1509061b120c0504210c05060f0c0105161707090e0a0b04061a030c030703 66
    0x1400143d2540e01b00e03e030241442006645445440700e00720004100e401052080d02d10100b40203100c0c0e4a403c8c400c0107000035075881a903184019004a0202050b0080c0400488140500c107103a031556807055801c1442c2001614644445106403140e5400340310a402c403106111103400c5a92801462078043d4254001e1440c115503134040c01c04560b002400404080820700071500800b4081034192108900b21200840f0510041c071010407411101c600d041698010b10740c00c1d10886001400c1801c20320000e212800c1030700b100c0c00064901c030076040701098034007444042400d1130510b94200b03403c00c1120081000c0b5804101d0105541700800414400d03041c80c0c220040c44040c0c1a181d0b10304051003020242d03413005401c80180c0d0b0808001c200f807820300000b0426254001c4d0f49941e10060594110202c45101805085c01c01c00c081c01e0100703280c0703402526540900010180000d04035060400d0009640d015400507500c915190709580350105080c0459030300c22441c8801580e2591004410b90040c400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 294169748 1250 294168498 294168529
    0xf0f020a1b091406010801120c0306021b011503030905040c0302040b04030f050d080f1501050c01050906010630050601020a05070b0406030605040912030b030a060e010902010f0206010b030f06 84
    0x2604107000c00e144180754152010b55540794000e00c0100780700a03c014560109440d0640007034520001000407652800240b00c07070704e01c614114840650b403a00c83d0800d0745c00c14000d03074001040c5401c1d00b01842e4402d1103060001e01e20014036040305455910f019140030701911405014540350240d200c0b41d036100c2d40c1200e020780000d081c0c0d59241c0c0d84904020b070140d51007900807070300c0b0303c10760b030040c10414010454070744200f11404c0960f141381d898199007503813000c0d080b0b08a414000c041c41000032040c400c1c011144520740810040481e98501070700141035410440d03501c0102d40c2e024891202c2c5a07141c00e841208901403241c003041c1521b803000102c0c40c041600c80e020300360b409003080114504103038400800c11102c00ba5800c0c803a0b240c54000300300c21900110001040b180f414a1201c2800d400303900b00d008038000040c04d44021201c20384540d4182c9a1004da034003010307595281d85104541e0010701c48900b01c0714904c010a15503051100385401407002415034041e10450400080b495650f143c4054060103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 294170998 1250 294169748 294169763
    0x307090801090b0105180903221d0a060b0906030402210a08210c0d0b0112110408060f040804060e1c03050901080903090d020d0c1a04060201050609070f0f020a 70
    0xe0604102e01005028060030384102e000b19054040310342c8010030b69000c0e00c04900690700e004541036045100103404018401d011030078103000a404400310b5038807a9118140341c00740b2a2b61400f22460000c848280d003200440c42014001130010b82c46140680742e2155061700d1140c154042c0000f01030210499050210740383c852010300031b003006030100c0980080c0e008208260032140000c0c1810000c41c40441d428607025105228042514081e5009526004010704004003500388000c400815103c0c1302d8081803028400141c2000914410000c284c1c1c0b002c10900007a440f400e0941d50100c0610451240d413040100303c14131118580d803100d40c0c0b21458041c064044621075078624000c0c0040d0000d4030064080b1391503c000a1403102d01104a854100005003820824680340d0b003085a094503d00069514080702040482c2e021845000d104030109850031454440b80341a00090a4940051646014001c240d040c000d0594025081c02149101400c2c85100c01d640c50714100d203842c0e074400c130103413101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 294172248 1250 294170998 294171011
    0x40e13210e0102120702010c060b0a08011a0d0f15110a0915020f03031b07020414091e0c060f0702130b011407170a1707030b0405010504150b0307090801 67
    0x2048101000035480c0392a150144006004401a621058008101c1000c4042000b41800540c403c1501100c0d0b02c0c480c1000158807060040412403603001c1d908042c0047e03542d1403203030391a12154446d51001001c02c683d0054120754943c5c906140c0d54407901d0041c050085d4041d007800100380e60b00001d0801001000341500e5250030100180301088500c42e2460142c41c0b140102281880451461000c0380c0141c0290300e1902e4036a2122a4940081890403da403c10303c200001039599000c0c0b00081107588459072982e04100c0e00d0f00e420b00340302c0103407242005030302403103650180c4002c10b01c0c926841e0200c8034030342ca698080360120341d0b512400c90300075070080000103407041140703a42e400071514010a07a030b100c0c690307000da465094503031213120405803003a40791581c10710802c0404001000c01c6642e92921f02c5420644c0e480c00c05030403c06440c4078010039101c406500013400c00d88165401401e080754244551000014101c2035600c0c40d000d42d120b0303c440003001034011401400d0748002001244000c0102 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 294173498 1250 294172248 294172283
    0x5060403120e01020c0a11181008070b0c19020f040513030206010605070c12031b060203061507120806120a08030f0f100e040f0804080102031005030105070203040e13 73
    0x5400741084110751580c42c00c0e4080004000c144292094000c0044c000c0000324010744442c20b11b8030380c3c0712130702d84d001c0c3c1c1c8107100f20b00041213000b50340d0107020b80311030362125142007940f054104586904890607081c0140903042d00d00c04000340c2c21910000340001c9250243c06030001c02c0440f041441b420f81c00600b09010710000c48890f51f041090f0354000e0703096070f0181c0d8943c0012a40c512441c60040c0c8848030361300e8140030404800031200400c46c0b0038100315455020b40f550701102c9804c424400d503078069000c4204001410440711148209070b00b00c40092a003175456643e01e40c2455182ca647c000c011034480092015150381c040019000031800c01ca9540345210300c2c001c8041d500c01c80e40429210107560110300034500c5903030703450b0142240b0901c10400c3c508001c3d2202c2c41450082c0190b488021040e1a5404a490500200301904c07050740056902e15029109814135642c03907100c0d50003a031400042044c0141d001c0142c4003074601d0845861700c680c80784c0c01e8000d82c07030005900c041c00790320003000844003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 294174748 1250 294173498 294173507
    0x14010c020d0225171b151c0204080d020307030905061c0e1e070815040f0b0405150f0103110d05060a0e0102040306020a0917060603070510020a061d012a031805060403 73
    0x10030304a07241c2c0c84420f2005803050040c2d8081307480315030b52400c00600141c07100911103c1c0c0a0454086400c00504041e2b484004130714100e1010300d81005600300003200028940d000004901400c003c4e950350740703081000c4010038000c40425001c40034983e5074080d401c0c0c034044248902ca4a6980001001c440700c803029410a803602c0d8140300e021860310500c00a00c150400456100b4402c0e500544180210301c203944804c082450014011140b074017402013a50211b4440b441058011000050745c01150340c1107181001d0320014840b00c95101e46c04411804000800028049500848622001c650300a0404506002e40201d40000300100e0001c41e000c06c0340366000c0c80640c2100c260300c2d80d466006503400704c401d0312910240e4100d505500098804e0010b1304294421401654503481210b21190540d19090100d65030440e420910b80d040e04080450304000f4081e103900e2100c46c01c40c0b14501c03441146c0c4036401c000b8882911080c103851707116035002010b2420706c40c049141c015003510b242e4509860001c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 294175998 1250 294174748 294174763
    0x11130606030c1e03051e0c0301030311010509100e0a0b09030a020c1012020a09030b04050714190509060307261207050a03030e160314010c020d022517 66
    0x10000782c030b42a48205000c0c4108554580040c42d000c61144aaa03040803c90140c9401410004081180180b800f040641940081d20840d20000490384a50540c54010010707440006020030a03810078083c44410746012a42c00000383c2c1640001440d00c00510105041080c18000500440500030421001c000c003c4007d00b00143c0543c26038110518450410041601d00d064000001c3c00c001043c6407403142e41d138004c00210400c3c1c140290484d541e5660700c20b4071142101c0456890304619400c0050300d100942040000b00c044964020450318500102034113070b090710880c3e1042c000c03800864201c0e1024001c12000d0020380d5003041e001d034032000c0100104180b01d10400e01d2403090b001c00003140341c044400c2c1c800c2c05034443c003e8000b0303803c00e49049000e8801c0c2483c40c404c5010f1511729200d207400645003107005522400501c00d00d50020314505007151907803102d503803e64001ca50059190b5901003004d215980014000c3c80c00b1140795101842089016040201100d403404c02c114110b40d00065441c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 294177248 1250 294175998 294176009
    0x60f0406260601050111030322080f070506070e0d11040e060412091d010501051b06070c060e010902011407030509032b021f0b180a020417030307080601030504111306 73
    0xb180640d030303201d004444000860042070303115001800841c040d100c0d402030b01c5006440c0040304526128a03030f01c03100040d030b102e04800910071400260707249c100001440070300d9000545042160200300c150002c81d01c2007a04000c02418201e0820081c05a982d41e5800b220b0318a1403642100c400f46014034103141c80d50b04088006c008104124000100841d0221200018005108d00460030741d1030701d401941c564220020301200b031520322b54070607090303d801c010313061064070b4585c1d504442ca0b419003490300c100c60314001c003200207904040d40180981d0300000c0808084c218084040d903102a03e003412221405504001e680c54012a0903c0a001c5c3ea003d40101d21044125290415105030312810707a038641480703a0908440303010803007207851000d20350702403140c103480038007958004525001a40c54228044030044038107a804902030100032850f9038240c001140c403400a6246050180024190110050080381056201d100040410020b00501640c6101c007a1140d49240c440c11606009016140500e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 294178498 1250 294177248 294177253
    0x61103061305070905010807110109111014040e040807060203040c0303030f140c0d020f0c030301060306080f0a020405130203100b120705011e021501080a0303050a09020108060f040626 81
    0x10190302501e00d1107100e0141c0100d880b00c54005103864010350b4944002024201407044100c0b400001880a0040501892041e2240100e00045200b001003505d280c0400c1d07004c201150f249010074807404000c680035646a2501c403011541c0c1d500d0005410321490a009006a002100344020000030004031030980e8030a480034808004083d801c4012100d0102d000d038136481d0510085051f0b650b071100100100c1c00384100c09894a00800c0e002c20040d400355003140c4003680000010810b09a06204440240c60358038050541e200d0340702d204582d40d82029a010380f01d55600c40c081505d011070040032065483c0e0150030f407a041c0074084c050710f0003403050150301406000d040768040c2d5007503000308450080d0b80c416140c114450004c090100c0c0ca0441009200040d48510011452344c01240c40c4000d008151a10040544021303d103002000d40d100a00711078449801e0075030840050f07030001601e0f9448503081d108541d440340c9802c0014007a101990003000b01d942103030304610b9203003283c040100d00e2450f04800c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 294179748 1250 294178498 294178519
    0x2d030a02150c031909020102011b210e0d03111c020702011403091f14010b0c070b0913240906051804030206061003060e0a05040516150c05070306110306 67
    0x840345190b100885020071070041c4c840004499018070b920104c07409006100001d140c00c0700016501d0680001018607001c104d084405d0050380c07074441100340001211603001c1c000c01c200601c20550b0344080c0c24402c0113043d1640421481c0c4003865054842d9508540712002540c094401c1c2c0000179031045109900040c240daa0702c4030701c540d042c2c045a0046c14000000c004480b4840302c40b022450b4201c2c00c030300e0102d460b00001c000d1084048070301c0b80a4120880c0260790740703451036075031403500f40036520104409005101e0321840360740b0b01488490496095201150381c510050360312128060494120f854480084404a9016440d0784142c05403102650316411b2101c424100303480c5a001190000c005910020000f500c80c00c2013030030001070543d02d08000c505070351140385100d0300300c004880442c24681e846041200b0711008104040500d640f80300d821a43e1800c060079094440041401c00c4140542d01202ea81000410822130000b1504000c041004205c21011060640d000b40c80c0c06214012880 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 294180998 1250 294179748 294179761
    0x3090f0106080c01030b0d021503070219020307060804020102160821040b030a020c03040b0c0c090f06010c2a030809010f0914042d0504060e0309032d030a0215 70
    0x400c840c02e840110004140b82d446030b00044000c0e202c8941850b400850f80206680161110140c07170542c4080d00a2268407032405002c02440e120703c010380a9001526080e0040240c1c074041400b0056611600e4080c041e5035542c00140d1a003031903a4114007004850355000941d044000c244541c2c124141084544071984841040807140100d000c0c410100c01c0805c049404480b05e640180303420b40c201c00c00da90400742d4601c0180c1c8250020410303c5510740182c0d1300124285841d03841241c1c08180300c180905103040810000303010480c2c440c40141050751608190000c4544041038094a010942c140c1010a49900c2c020310b0940121200e140442d8460f500d5100c00c80c002c0d21170505a500c044004044a2100030420002c0c044013018140c8070f08001042c5038001c220006500344060b1403990100d050300385071520074100e86a0f014151425001440608403d981c00301e00b9450348040090701d15540b00748014580a10290b8aa04021030302c4001070201c10150046140341c1d50100321021085160380d8007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 294182248 1250 294180998 294181001
    0x61303021306211412030106120c0e0d0201030b0d050c0405090303070206040602070c0909060e0d0206061302132105010510050f0607240f050a0212161107090203090f01 74
    0x1402109a0125100021034507401000c070344010f81400790f40c06001640c01c1c410361a00300170321101c0090303945d04000018028160840c4070b030145e1001412040003940040b0000811340500403000c24410801401c2c0300066a210ba001441c8405005000b00704c110210314119581d80d0a50a8040c00f550401c0c002440010012094034420b90a640203090160754a82d6002d000758840704040342c01c4413852101040318801841140100340c85140005020625a4640ba2400c40d5240400003158400801c010141c1c446000e000300300c0c01c0e400c0001d03864400c41e600a02e0801d4040c0c01c080005010900000404080c0711146403005000313178020003060715840762040c000905c6004098000f0180d03042c0b510a404c2c02401060100e001e010490b40ca80c400360780c05803d02500d0220607804c0c546521a0102c0e802c4584a80c5400449454046142c14580248003807460380050620760090040c800300c07110360380a05144002c00138403c040c3c0d00072544848090000790016603407840c2c0c03842002c80030500c0740d005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 294183498 1250 294182248 294182261
    0x7110a060f080712050106030b03010b09101202030304030501021204120207080c21062505090a030b04051507020a03030b0d02131806020409090210090e0a0216020613030213 76
    0x40da1880145004070106407002d6501500400802812100c0a01e01414910440b4040d2110790307800310300d8110301d8007094259104408428424281e00092000f0200d1450500d000c6561100320104103803028000603055000d181d01c082e042e9400022001e000c480c0c042c0360144a107205012000c03503a14a040e0483c1d48030f03000d00440680364410801c1307030841c1c6802c2403181900c0c040e219803003410040384a80740d1300700581512030070001c000f01c18102100c01005003254002d81960b2400e54204043d00e4001109144144009004040170a000c00c091050070b0104903150780f18480c6014403404c019500a5542e0700d580c5082d00003a107031241e0744190380f41c02c042400314560001c100300c0480c99914892002061103901445043d0392003030034500008c146001400040c034040c800040c080c0e0290040c4040455251421000c020001106010042c01e4800d40c0f900b001c9007880c0142c43e21011004240ba456000380d0181d8000d5000c14084294480c00c0a040d042d40c1c4251215000400201801341c1556078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 294184748 1250 294183498 294183509
    0x2070b0a11040602030d0f020c1f0609020a050403060e01020403020d0f02030c010507050c1318140d0e0604030b07020c090f040c1e060318082d0403020f0d140106090207110a 76
    0x104070f140240c0540e6004001500c4032200010724049c482c0154500d801504a04295480c50030045003101415500c180c034010420398109624000e40d644006080d44a1808000d103203d566103644104600258141c1e030166601400460b020861030a1401788142c444404038440d204d4614180600d508c90750035607003043c6e03000c0000c000c17000034001005030311100140c1c0340c14926582c03840f101412500c08007502031140143e035009680d8110640c40d90500804071100d40a02000440c0c0b2095078482404071030407a40c01004070400e64031a220100d06040802040940c010000000c4c08240c01d15001c0c124016403181040740211076036003c06c030034004202c0908407601c200310301040050300d000e0b4024007200e003c04224074400c801183c0c2d9240840e0002c100d118112076042040c500d00c102a20b0010765241c81c4000d142c0d0800c1d02d1540014a44001b00e601d407401070920310b180c00c04024915103e0307408600090000e0104076201c400c090001d4003c00d0054401c00100c00d400851400c03d9603510301a240e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 294185998 1250 294184748 294184753
    0x50708010c0504050909010e010f02090414070801060809070510110d030603030801170705030607180f050618012c01090605070206090105031314060f0c190305060103020d02070b0a11040602 83
    0x1440c00c01044420720001b040d141043d503c03414410b0003820203100d844105607020400603281c8032a003092200710351030320b00f0050380c110412003440540c0b034102c0c040c1d034115030072031510340800d1380c440c1442805c0ca4002da000a412803501d1043c1045580c1000b4074011321030701003048030319002c98140c080f0180d0380503220140200c2c110070010306c10b09074400200c0c0b000000780c004503011a41d650380400c0c07a14104558580000b00140556030f01d61001d161030200502045c94070404403030400c1d00051452084c8005505845201600d458659003c0c180c491902c4600d10804454034203102503c811101c00c02c62031f83c0c000b8140d05c201080a0303000d8400d9507007036a0040c240714141200107006482d1640044c00f51134110808690001c0010070303030000d000040c2480e00c060019400c20031405000d10801521041c09400305000e000c11905400740c40d0344203000c051a011460341c8800b00164004d10900d00c2c080c00380c2d40001602c405100c48040c40380d019841c0ca06040020018017100300100d0b005030b021b6540140c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 294187248 1250 294185998 294186007
    0xc03021603050c0c091003110909120313050a0c0305060a020a05040e09030913020c1c051801050c0109050f0f030c070b03042f01030c0302040617130c12050708010c05 73
    0x80d12031070180c0f4011411800721421851100e00098a450b0100c5840e45010030840081c42000225006203103034020035034149030b460822440603511041611a20800c01202000084d4041d031008800c402d01c5070824252000c0310080d060001586006000645051151001040319113083d0710840307240c110180d4885080500308030008011800140004c0e900c0e100c01d03c00ba8101e903640345a00d1000e0004e003a001a520307045051801d0404003942d00754907480545041102000da001001c513141c0c0d0525190903030380c0360030550060780c160103240c80750b640b150701e480510001c1000c0001c42603c020301034812200100860a00903039248030b0a9002001504558030801002d501a805545c002e4490f03c02082071003d001c41c624405410340c0d04030030600b06000c22031400d07941c06106d00b81080300c00e4074055103050706041c8003500c0000c08070041008400d03d14001462441c410101c03903a501e47c07001c0800c09a1780d0340d06859038181420a0300782c8486c084c42c200050260f005202c5d490403844c00d82c8509003031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 294188498 1250 294187248 294187253
    0x60f0e010c05012403170306090103110a1716080303061813080d091208040b010b0703051603090e010605130603020a0203092214090a0215040f03080a030c030216 71
    0x742000702048a0365902c4641840d08403100d00b40466030300203800b1180446a02d54100740c801c030b1049851842200b8010402e1200f2030300c90160007410741c1e0b00148410700303500902021500c1802103511100380c0b4048840b09803118100403840c00252640e0b05000000e5a484501640d120f1100f030724456481408500021818042c0c0103609602c00040310481c8039103902621001a103510070101021003640c1d5050703c00410010b90444000d00b00c440c0340c002400e2906640303030504241d0601400f01182c8002c130343d40c81014402c2040f500241d1a83c0c0300120f902c20185005440342e20580200c041c41c0b0300500000c12940e11810a035098070a50400b03c0d00003922f818411ba0080d41f0071440d480443c00200700307041e1243c4804c84a00c00d80e00403e400b441c0c005d04208841021900709483e10b002d140070300f030b00b4007610784800030b09200d00e2501201e08811324102c08031425010300c40c82d03108900d0410b290070000203200a4602510a0055580f000e201c15400100201c2c202d00c90300c1e025140303903120010002b02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 294189748 1250 294188498 294188507
    0x705030a290a0203040309080115060305090c271305030a0309030905031b0405090a02060301031b080a0510050726100b0d0501090b040c051b031b0309010207060f0e01 73
    0x101000d5200802820840810420364030700c204071601070005400100384070405a1205041008081d10002041341007440c06903041800789511481c4205615400817819024050203601c81000c0d00418040c2d0001650458005da041c00a02580f403d0842900041302421190700710702600e07034054091443d10068880580040500e00710540401280140225850320f081003c10044c0591004610701c2c401e071441004241d40c3d008200c140941c001200d0310b40161130b20010740381034070303844900c0300300c40c041d280041e030120005a40011a588502600c3c10240100422241050403c11a00344103980c0c50b1801501c85607158034141e01c01840c8000482c0100b491820410342040101c1c03090070502d40d42d000f00c0006e9410000030200010b40d2000100900e007454403911f6118082603409110111a42001030418000c001c0c54501c828540d200a13409050140304403140050840040143c0300e90a1400315500c3c3c001040031f5000d440f07004000700b02c1502440c0b0072000202c45659000301c1c1101c4400458 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 294190998 1250 294189748 294189773
    0x209061e04031a0402040e0c010f12020c030f030f1f03030f200d111b01081005040207030807180f1205150c030702060f06030a0f080d0c03020c0705030705030a 70
    0x4240d40401d10002c0005001800f620124070810070303032648581400c0c01044100c1d1450102000b059103e820309003003590f000780b81e1203080c82140c1403010701002c1c95120080030780701d5605401782c2400700003241c01581000c200a18055202022030308510f90301c20b003078441c184182514040342c424600508100080c4514014140f0510505c1e00e20268003004d40d5001e00c0881445a0170119007280b2400d219043e400400c185001e0b51100050403003450f140b880f041c81411900303082d4104400d0307600261035600076029070002008068001c554804032400c00038401a02a90344d039000554902c1d44501054104062506272200e00d4901c0e803a031407610600d01e0101031624012103d45c000d08a000100c1c0c1d020f0131040d40328032101e00205e07a41c0e14040c04001e040c128001c04180324850b40205004240c0c0340000d000d007115500c01e207000d81c48130160034000024000c1c00300703e140c4d080c14000200307101c55164014101110744c08046a4060391074204042d2192018080e0641681c419010000803501c1c1c0303c03070003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 294192248 1250 294190998 294191047
    0x3050712020f060d090221010c020321071709030a030b01050a02060601180803031e0601021501060e01030204150c060e0705030a0b0c1902031c050106020a0b0721090b010504020906 79
    0x60b4481c031076400300d040310225610802685401f01e034000c0031400280140c45403500d8900c017540c5040603050300c5514540c1443d901250898030176000900b030900425882400c8105030308800210b26000841507541d034001c1ca42240017038141020480325501550503150342d06450340180c015070782c49100464072200c9402c0308aa82040340900000c50001c2400110b010708929070a40428003180140c040c59080d000d401c00e411940a0100560ba0340e400c036404c06c0c1942c17258039240c1208090b5500482c00b0f0b01a03900030a588800c491009a101600000f137412440e20982c0c0600c50300180204c040d0f2281018031030240c0540140c01460300203a100304250f54030901d01c21400341400801c440021101d50342124010140e0300003d212802039588604240340c200284c01c09106035070401100944881c0c00740f000804a08040e004a086c1038010710003d290b0f002c00c0286044d00c100d004804002401c0c010800341c0c0c95060080002c02e06003881d0084440a00000d4826490140402851841482011b034030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 294193498 1250 294192248 294192251
    0x1704030e1908030d110c07032603090f0d0807050906031305011806050c040303050412030c021512090d1e0207050d0b040506100315020d110708030103050712020f060d 73
    0x740080d000035003403540207020450025500da45070b0701e9182d8100d0354107040c012504c51081c081c840780100e000420005490b44240b1106020f00407041a20a6145003280d41e403541d07001104104160000103141411081030b40200c60b065a100502681c104000380d4004000490030040440f590510f072001b07603000405a003200d400701d48951292402c4401181950486143d80c06a03042440218044c1c070b40c008203a0705156141070710f10356010301244a207110302480c41041304c02e41002c0c1802881401005038001e042c6c2c43d181d0522941d6280b00d540b0405040d80800d0619000c81d1814400107400b4900c04581d031190310105104c0c10321902e0f0200000e01c44c804500c10104c001c1150740300d2003041d00742a0322564102410341460f1602c0f6007402401041d003441d0701c006480c00c002280c100c00040140455803c40183c2d04c1c0e20300c024810180600d41e92480001500003590400c2040740c600440c1220b0090064885030b544520035030640c00b0400c1c034089e43c4080100702006691402800604001410610 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 294194748 1250 294193498 294193519
    0x90203031306020105010608011401020714010e1f1101051b0c10020a05030103170c0601051215011d0f1b0d020c161505041a21040b0106030b011704030e 67
    0x22219050181c9401c4100142d4562004002007034000d04c1550141c80701e0365840b40881d2030b9400003940c0f84030394401c9424550303006003501c5099014080b48940c01d00050040d5a150815007032000c130862442c4200400900f41c0200761004400610409008581c0c40d00c68000001c100d8000b11226000450192264051034900e0301c072940180c4010320810281e922515281c0d8903504041c1001284540d4201c01030310100030304098680003084180c1550310843c0d03c11103800d11200030600d0802222480c6004141010010401004400d041c55914042514450155446c01e6002c10000303000d8880d04900aa14000742220404a0b03000d0408038142c0500182480980c003803c510f400406100080002d81280c01807010b01c95642000304400c04504020349031600d0703ea004444007084091440b0407003c01310f03400c554400c10041c0d90a104500c10707001e03900d134185800c103a03030104000e02c11140441d02c1c081104615501914240303080e421340349029002955191001c0d5110016903810329405004041c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 294195998 1250 294194748 294194767
    0x6040c030b100206041a0c0d0c030b1c06050105150a08070e0901120b0a0c0c0215040e010e09010c0311070b10030519060506040203011511070302060304141005091009020303 76
    0x202108907500b0a68020002400c0604050790071080d10201c1c03091481c19031042051250014084070f1034001ea051000643c4d0360b82200c110028604c055030705602200b1182900003e8080203e218201030041d4030400c40d13641c0c1c032020001341c00350800420340000d1003441302d0302180b4040e0818aa02201c0303030520382a816185400203401c17047c00d03080b0294901005507100248900300d40340aa00801009040105219100010744000840b5500030b04c10800c01e030b018074a520b02002620b00500136030900740055615030072440f1a9020459441d055580380100c080b92580c428098011541c1d0203121103480c1041940b00d2812a80004003000da112881410000c0040c0c070400910a0030703e004049104900384a02e8514250b510203811a44140c2c018001400042c08400710281c283c00d850614402e004c0b000d915080c14032840e80c0c00a03600c604040b041006100c4001c807480b007c201c51a05403500740000124020484800f038500c4641c0360703c10b1090072101d00c01940403155143c00102101e0800c04904c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 294197248 1250 294195998 294196009
    0x130309090f14070215011215020d060501020f030a0818010216051b011d0409140a061a18011a04051e010f050a050f03060d0609050c010f03020405060306040c030b 71
    0x80c566030101d035482e00501405003a03001c02580000c140e2001e09422020340130f5030400d44c0f4060042c7e00003074130100070b10800c2062020440341d040000c12801d5491300c409158031801130903944100d41c05802100c004508082d8040201e5000702071713035218451035403500305450b0205007a01240746810341d420811900021100c1c010445224401c230001c1c4104844100c2c0000d9004440c3c080070705000000358075609035201d003a140c02420b08280c2d80000c0d0391400b410800420100070402c1501070140e0020070b0103010741e54014141c0e290741d0051401c2e10704c00c544140700035825000452000705110fa0014410b0300008000541c03052078186440b0308160301c03400041c01000c2000f203030798009108042d15154650708000e19680342241800c0c03243c20a000e00201030041d2060440010080030000006a915625250751148440c1c100704200400f5140b403401960316003240d8121800301d03035400510355250b40b10b8000c42d003c0d903a010b49007034250780311300d0709000240001440140034180c40c1c07040071a070717034940 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 294198498 1250 294197248 294197261
    0x30c0e100803130303030b040b1c02011b0b0105011e0c020d0c09290a080a0b0601091d18071d041505100609080c06030f0403020a02030706030c020c030703050613030909 74
    0x2075000c03e0042840c500e009011181c035900501c0c055402c0004400c21380d51040064403034405440c8a08400c2041480129140c2c0b840e8040c00008403146001074003801811a2214160b42080c0c035040c100388440400d000501000d4448100010350301c02d00c41006003410300441e1b821b2072060394442c5089443d00683d80540705074240075441c001c4100c007209503400085103002e1110400359500d0070003c2c20100415100c81080782d010f0013140401c004544a6442012110000c01100c1005105d080340940984102c00b010f90b071150030800c03a114010030101021441c40220b505600400c0d4040c0d00c4418034ac4144100104241c03600b9400c0c204240250300103001d40342c0315082007141441035a003400000340c80440d054204084540c041e180c8030f001900c3d800200c0b42c01180025030301f28a6503443c80d040745800c0e21070780006d4260040e0040015150b4158000307201d86072481c0c0a8580380004001030556030380e050700c00600b841d0300c2600030603990400040c0c0d007900e0b54004c0c50854001a110070204054800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 294199748 1250 294198498 294198517
    0x6180b03070c020114070f02061308010f020d0b01020105060603240406060509031207320f071d0421120c0c0b150f0909030706090506040308010e01030c0e100803 71
    0x1000c1035142c0456a22043d0100c20102515290341000060713190303996175130801d9600034082e14000450421a0341c44588400042100400a12500620140407006500840c6030400c00742d040248040c40c560041c0a03043c401c1001510841c15540c40c190b04500b900c40c0104614852000301c1000b51751901c580c05000c0c00741c04a0b499180e52907145078241032038103211140098141400f805842c0010b562600c05420b00b066004803d0841c03200100403054403051418940154032441e1203280000d20b020504804031180c035070364a42d110700f002104c105c01040c2194003e168015840100604448810b0107038462445071134030b030603481c58030f402c084203c0c0c41c0c020785940031410600000c003c002e0b48204c8154440300300c9620746640c078440d40101e130140c003540507011b11480152002a408440c1007095800d1103030800e01c2400300f000c650418035200c0c1010380342540042d40f40d500119550815116407030490740e1104021070329624201d01e5107900c00010f82000c0001c203401c10009001e07442080a03041691 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 294200998 1250 294199748 294199757
    0x311010203161d040614090708070203090103091401090b0a18020f09100509040302010f06090c051b24090601050d02240426100b01020a1712040302031b0307020a06180b0307 76
    0x42c6c01c0700400010400c000d00c0c04081114801c10846d0407070303010066804654080c01e012443c0800341c60904030246151901c41c860750b10302183e03482848040e50065024081c651010025000d02640b484003600900704082d420240036020007140741010380160303a101400f00001c2640580f58000900d1011040d14141c1c0140e46072a032b83c0301c41d003445209040040454800c200903401201c20042d103140903018600c0002030b0f40203043c3c4045101408552022082c0d20b03544180c0b9107c00c45140d11901050b81e508805100302c00c000319460408202c11418241c0040c200426004451081346440c03050040303070075400d0790a20000414040b51060300c40c120485400351880f848003000260303c0c10042070180c29105043c80785000c016600840c0310f0b00741ca44c204040c0e450100a6050322044e07445082c10410300700b90014104018564040040c1003581c0c01102054030306500e1000965807030087c0701b40a940310b0fa04d0f00041185034000d9900100e80008501001d19855481213204002e402c12101d540108 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 294202248 1250 294200998 294201029
    0xf1224020c160504180803100e1602010e160e04050c0d060c020f0c1e030307080a0905030601090b0a0b0a1e030501050109050a081b0316120311010203161d0406 70
    0x741c400c0c4800342c0038080940f401c100c00300341c0f1810381c803500c1e90072580942484400030218805031030300f0080304c014001d03601d0f024505003040180260b18041c071900c500019464460703641c1008002144011340c1d404c000344a2403102d810700000f07811600016104544030b100e201c040c03102c0d43d15004940420107025241c009010544650b010341002d0740342c1c088a42c81c1d0800c50710b40d940ca60b9600100710710790342182e00070b0320141466800300745180306812000e04800386c0030034200d598650182c04030040d42e0080c1c0130f56407142d2360354105a00703840407201416401030301c40340305009400000300508030300107252a0100030307006440c0812003c521145403203000242c0380d4005001c65600640210300500d42504c80b002c0d0341d454510720315101e0403052600803840788201d40410321950300304030602044125031140c3c400d4980e114030801501c110b2500807808280d0261464801600600c2500c0c400c001c01e000c640e4030a02c0c0c1e408212001c5038a00c0f0141ba85130914804200b807501c80344121000761006201002c1503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 294203498 1250 294202248 294202273
    0x2107060507030618140c09010314180f030c071503090816060b0609131517060106030c0c020607030e061b01050a0e0303040215070501060e0a05100f1224020c 69
    0x1031142c4054001a80e0804080f01035032002c06080f20f6022044503401c07030319180c7e0b95004034080c01c28040c10140e000621018844007117131419544100c0c9910004503a1402a90503030151030303000c1d540c074600003604004402c0025a95602068000c01c10a140000c4d480701d85546600c0140c0115605003d10b01c2079600080421615118890310203c084072201c0c1005880d01c00666000ea04020740d181c843d494103240e0588640c1d0b144500003605c088110680d030341c0d2444c6016640c1e07000903c560b40009080103154145a400b0702000c000040d00504031500d0034406440503a4101ea010010b0341e000401004441c034803482407051608800d49000011416060460703c00040d54003203585942507400803c10300005035a010b0f440713008203080c108183d4442c40207040c0380f4010006a400520b00e50611310030441208969400385200392a020ba5650a25807240c9078441010214010b100001f000707034044c403000c103902d12001c02d940c418103481c04000a03404a100d0f41681c1100b404481d20703a0003480c20511 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 294204748 1250 294203498 294203519
    0x1e030103060c0206150604180e0d27120809030724021b0303031815010311030f1501060e0d0f0506010e0f070804140c03070602161721070605070306 65
    0x41041405c844111644981d0b4001034052240d807054150120b0900341c02420044280c0003000594035003001c0c1d44e18240b544401401c1130340c3c9403080b51712241e55004d4004102c0018030200342902c41001c0d041360001e420355039660090780700c10503660780f40c42401350000c1c002d48400b0703d810034031812009115800214140c081c3ca00380e080c5070341070200b030781c0c4140c0f20009442c00000d50b60701141c07040c0d4801685c040183c0c00340c00d140040d10140d82c91840354002100b84900342d50b042c0c00421081c0c003224003043c00141e40e03d44445082c2c02c000c0400340140010810640701e00d15502500c1d400402011003c4101d503104603103110901da0440319030708880010040c40799840b41107648048050684681da25104070010903541d00200001d01804080800202580f001c2000304000c0f40082d0880d118a03031900030103076036031440220980d0349150201300410180c001401074851014400c00034079110030740143d0080b0300134011800d4540c0b000d007400580c0c0030415900610380602110b4800190342401d200da0041e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 294205998 1250 294204748 294204751
    0x30414010c0203251706100509040b04060e070506030115030605060a020a062d0605130b0d022412010906060804030507020405040c0506220f0510051e030103060c0206 73
    0x141440054a01c0001584000c111525800c880300500e54141d41001030a103481440380e002107007004403803038001040a40000d409401801d101d194140030559510401c1010401254020b000c08040c0c07000c5800213445030041098102601c09450300c240c2c461012a0094209a1010380203140341215810099014466000600f00c1511410b181005228029580d0410380c01c000b880703a551000c51052000c408107040c43d81441020103d408640312603512400b40045024941c842d14203002000c22070440761240d90a1200701429880c070401e840d408004000080d000c0c024034950081083c60910005000140800540d000142c1841d5041610b00c10850302d15421540503c8508401d01006c41c0d000b4040da20720944c1154086100ea0310b80c0341060540f0566441550010000b1406011040b01c00c0d04c0400701418008a014034250f442c1d059a032214001c1c4900740c4c001c10300c0807c16540d00c1c82040103010b1105801c0101540c0e458016271000e5940c02684240c840310340d940c2d0700300c17803940e410310405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 294207248 1250 294205998 294206039
    0x2071a01170a0b10090218040c180605091314041b0b040b1b030c010911060a0f050c0a2003010e010e03220306020d0501030b0c070519050a0c06020304 66
    0x107036038012441c00c140d59620200b8202030310602140002503200610021031002403d0f0324401552501824241c003265903c03610401841749080000002441d8442e0000510060010500180040c50480c0558156200c3d10340e8030b400c003240909826544002c1c0c05504a0041c1404451495180030705103568510101d010007141e0440c0c0840c104200d00c08034068405035201090880d648600030444800604150290844030380000301c0c21003c00340040d401541c06a01904c031107030741000003404201c17181c89178400210224601d030040341d440343d2007500030b44043c2c020181100d001d144192034051803d00000080602c0212128400296003400c0c020310000c600408001d2103490200710040351640507501d0548444615540e07005ca5140d44808054000d54000b58110340d2051203141070f802800090000b612881100800b203141c40000300c088510403071b00031000d011081c0100c0c5150140800c1c2c81c100f41c441c0c2c440c1d40390702000f080703139034010707a00810441d001155128a000d00c403012000d60000306 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 294208498 1250 294207248 294207269
    0x612050601080c1f051306080601090807180207080417010603060c1e1407060e03220f050d0f0b131103010e07030210020f061821090f03070902071a01 66
    0xd0980d0b98503000c0d8003031550907007441c1000ca200b07000413080313030280694603c14080711214400010815001100940985001e07620012400c4d150252196121194822600701d49041c8964000d111140e6001e080d101d40b02c0c04001e844c150707650403500107401c2070a034090b40c0b0b40d5450604000708200352003400004840b905104c01076045002d1001d00510400c0c4080081c0810b503000854007418a0040f032b4160b40d03111004001c2c4900b031801041c0d5981010040c003000c00342c1d04506d1100d0740c1160100c0301c01c58590312041c0c41c1c160b003803a0030f003c1d1410300c030319040300e00c44910b5008400080700d131074200e0300c51000034407120008e0595041031415503444100c42400380c1d1405208480d410000300301082525015103054180700207408040b0324000201c5c8036011240241014421038408005100c0d581e03010318801c59044c400e050307420482c001c814011003181d60800700594030050900703562b90000b40300000c0a8500e02c40d80c501c43c030303410380e8403060080360004207444901c007081000103003150240c1240c818 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 294209748 1250 294208498 294208513
    0x7200d09170a061a03160812030118111207050306011805030c0607020a0f0b1309050606040323060106090f090203042406031a0103050f0c0a0614040504061205060108 73
    0x7103040c1c4450500401500c42510b400340410342000e405900d100060002d82100d81032125002001181c0c2c10b10f001c2c0a03040d000e8043c51451031002c00095078103035004c0c040e00d40c810590101d0890300910422980d1044620f060200c1c0c450801400b000314851405515200d50b20f14205000600c00c268524003000031001003282840f0341d450000781c130000c10805590541d5200d47d40d00005009019660001400a0044402180c82c0c10040060200c65040103e1006034540701e004940a6680888003260440340910081009c10810504802c1a850135482410001c400000840c00c180098000001045041d41e080141c0c4a201810000034404040c00b10b046040c10b990718445500e46a4000342c803802d40300303800c01000d412544680015a804400d0080c2d28607000e1300d1006d04542480299003502a540180351051408240c2c4100c600000301980c4084d400c0200a54041e0f890f00102820280144004203907038582d407068802502c12440c1c078003002c01ca20301e0001d26280d0140c210980035088500e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 294210998 1250 294209748 294209789
    0x1211030607090b2a030c011b0504050f0904031101063203030a200f0604061a09160e03010e03040f06051c050a1112010306051006021507200d09 63
    0x4095401d40b50081c100c000040c1c032080401c2d800300104e0009007495000000784084404015802042442c00688101026034810700f819180350080340b19a60704040002c8201c1c0035880d14071185680b01d40310b4180550200d03110810b0500b108c0d8244c00c142c946c4a1444130303000000c41c008a243d08540000c1e1000b208074007086001c03136102d0051041e100c0070311182804c0c02006a8074500b9070600d20754010111843c020b420700c12281d5603402954283c3c1d11914201c0032100100c1d4400070ba02d00c2c184050700821690712860500b003103032608041e1071020864187c844d403038a60303800e000e408044400c40000b10389860401205d142000c1c5150302001c2840010072001f5a01422094002c40340b140b5080e00007055903540c07100c00c01034180018070b20000300780007880d0391008070601c0c0c03102e041e203025910400a581d43c600488d4000204c03402108090390040710724000d00706c00b19040940c000d40520304007030b014146400c0014203404040441c02c0f5078100507002480310f036100c002540104148401440400041c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 294212248 1250 294210998 294211019
    0x105060c0c0d0618290105030d08040201030b0d080304170909041b0335040b0906090a0305070e0109051015030b0a05060c0c0102060a090302061f121103060709 70
    0x1541860003001c460950500780012680308102404d05201459195480ea2a000c40400841414003082d80302403540c075181d840c842d41105050341e1001d002820f5441070010180e880761070003041241055103a45494801b030715422408110b0610400ca11030316403c091807c4400c140d400c408041c80148180315001c1150f465980107a00310b80c200200c03084000d99204031025809040d000540400c01c1c42520088001c0c0e06d0901103504020551105803500c0c4d02400c880f064030030741c841ca007a000d41c02c3c400d001562810301c0c02054403d400810040703500e036880c0d40b01c03401d06031b19a01c90701e2001c03241c50040002a00030f0082c00d5100502c6449102254101001d5110080c05c1c14104800c0603030700c3c0c541c0308840c0c4501101d900070f403030f00074079407070701d4990355101544c0d510f648003a62401406010b0201e030b005130490150711800eaa00d90090010703a9103442d00300800f00c0881610541e0400c00d0f4000080c40303941000d14541090144010003001c3e91031009247c6424000b0f08003904204080908100ea000700c0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 294213498 1250 294212248 294212263
    0x604140c030c040317091f140f0c0601120302100b100c0816050309101b0602031e0c0702040b01050a02210403150b090f0408030109020322030f080105060c 68
    0x5604035140e4481c82e00803080350140d07410092102d01c0c813041c034040307140c20180500482c0e10200e891120200c44804901c0134030710318620f50700101d200f802c0d09040300144000600000882e6018041c1480c0800d40f009250036400e07840000404820200481859818840f4259001c0c02c52024040e40c4400f001003546408500806010025400308a00800c1800e104039020001c406d031151458a42504010b5229401040568803a00c00c8a9908034094000c0110b564088204240f0f140e07030b046584c41c0c40010b58002013900311045000c4507009480341c0c1200d00e01d0300034510408100d854255034410301085520702a40503044c010144880e241d00340e070010f0f00808450500b10841d00490a030303900c00c100c034052600300404007114001c0c030b03c1c0701c01440d40c450b40700840300300d58654154440207000810320303c040d1800b409500c4204014003088540d030f001136402152190415280c0304030224030600007040389908400003a06a1402c2c1c1450394800764090240100b12102c40c03924400308019942e4801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 294214748 1250 294213498 294213511
    0x31e0b040209101e06022404020d021f0c020a1d06100311070605160f090b070302120301030b06031b011227140106080a0309091508030f040e060414 65
    0x10540003d04680080c0140c034010441c00920040900d0003034000c2c1219085402618010312a030000103a903400e4010301c060500510703001c10700340c0303459a4080c8040c410300800300b0703600b201c0103804d2134040c83c0c0141e000d49482c1109903610f0031140c40a02c100700a000559000e00d0450002514032280411003c1d1075a4000204030f403c4812002d1490b415030103010b1051401446403004501c43c000d20009420a0340306107050020500c00208003c0c003928803d210082100000e8400402404007103008401007482d2030083c01115941203841098040c40e070300c01d0b00125425022082030202c1030400b000416900d0200c24400c080078040300d0700081c800c850c0450b22202540d22248481a40450030600c2c01111084d44941031400b8a1414100805031003280c900b40950f00c1e100001420031030200d94403281903410382c1c0350b141e1589810b1100c40603080042c9000c039040c0252100145003d0108000c1c400f038241d0510013615103180c10000300101000805d5903010f60b081594607440c40e85e00c5141c4950014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 294215998 1250 294214748 294214759
    0xf0c1e0f0d050301060e0301090b0a090204050f010303090506070303021207050c0c180a020a050c010c0e09150607030f030f0c020c0a120b0f04031205010603140a0905070608060f0613031e0b0402 85
    0x70606c00240900072805000d88400490030074880d070f1031180d0b0001c085060084d079041c005925110541f4200c4030091001500154500d00240454580343d0014118940246400b5080c425269181046000c0c150745600114000085001d580d041c2408140c1c03000304100c03000041458002c11080030303190000d0081944035170004002c40118040e40680d030300346103c0d00080056040551021301900c04100303400e0700c98514034000a5101c40c8030080514a0200549070a04102440d80d05680300c2c40e072405414140368a40b0154806c040782845842c4028a0a03030050018008810900080071219008020004e100c0404400400e110402c45a001090003856404581d902d06080b1107002c401008070000300d00f004000503099905800c0316051810400c7c901c40d81d0380f9486141001c07118100e02c02803d5030030800041020034081c07855140d01500180c0240e0800205100050880d0b100352000c0c0308042c800302d414024858401c0e03c80320802e03541083d2000441b020b4a44e00801100103000900c106e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 294217248 1250 294215998 294216017
    0x1050111010f020304080304021503040f060903030b031c0f030e21040522050a141314010f050901050903040302060d09030e04020a021e160b0f0c1e0f0d05030106 71
    0x41800d5005010840103084119144d050034031b0140d21952058500380e2244040b600300481e4100b0301400c480c003480c0e008840e0014060507540b090007620a03001c05800b81940c40f040c491a946043c0090190310080003040802c603184140041c0141e0080302d5800c0c2090f14040240069000008415000c048801941603420441c0c003500051480b6603001a900034029a4100001c440b54295900c65004100c0040c441c554607004c3e80801c0b18201d411004610006002060450504070310300f030051401100c101d2510141c40360318a0035a150034812090443d5600100130f203510080c4690382e0000c0f01d61001d5840d052031500014072a02440da07404100c40c0e0307510f81101c10180601c0603e0308200c0c0250056445880703d98019440d24100c944080141d00d11000c03007120401d0204e01c1484001142c4040ea00050400701078030340e1030b0415007140d6003480042014910b00d02c2c040011788591507817020b611008510800195042501c41060f0514950201d00e07203114050300442070b01d054179000d2801d105207 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 294218498 1250 294217248 294217277
    0xf0e0c01020c01050c0309100f030c052a0703080f04051f0206040b0a020c010908032d1b0d060905090f0604050c06160c180b060304171b011a011412010501 68
    0xa5101d001031f80380e800340c40c0817600440e450308060a0f482c410780503141008600ca0752001910548a91801406455241c401e452207409a1018951210140d02e0444828139242d03a40c840c2150300540b5944081000420100002c0c50818860b134070740110014410403c0e121410043d54640c1c02410040c11290103200050909000f507050312541001080240008001400d040380c05074800e81c0c0c410300cc0a20480340140244c010b2070448420752604004408980d0340b45284810100a0740c411080e2030020032a154001950f402502c000d040840070000f02c0341850030b506454400b10b40d1040989400c05410807022400205690440314425a4950750320700d100070030704281d80c1310300c1c500500c82c0e40d80072800f050002440c401406c500011080c00c22940e2017071780c00c01c001c500046070000c4c03940e0011000300000c1030306039010b00591801045440c1842d44c00007000e60940c0c0b5414401e1201d10329100c7c1d810b90540e070085c024075501c119481498a44030f030880b1496507100d414050340c0e0601030081109401e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 294219748 1250 294218498 294218503
    0xf090b031203091f05010e011707030b06030a080d0b1008071d0a1824080712060e0f01020706050a0539042402010606020303040f0503040e0a0f0e0c01020c01050c 71
    0x701c07100c0c40d0b182c642c071300d144601643c006100c280101c0400a40f0310b000803408944140c031080551601c000204500c038603607a603034070a280004000c03a4243c0500d02c410000503088034041c00c03043d540d444002c01c032116608140508809207444400030003e4503402d000c605078100ca02c21100301451020000d501c1d0b40540426050069a800003421600c0d1262074100d0903030680c81909000c0680c0d035440d030106000c11460240c100d8034010280c41d81c2055404000ca40d641d00041100031707200d40c40102d025400c59403018145030807005500000c0e500041d505041001c2446041c0c0d210440610401c028104444021500761526590108482c041c00c041514034030700c80e025180e40b42d0701005041c0e85a48828a00390b01181c02c1e86240c4001d01940b2840e540a401800303004180c800c9507004609655441d141d02101024200054426001c1003201150795005110002d100e4401e482020929082c003d0300c490403902041200315131904490200c140903a804503103441c4c018400d103419030311040c0c41e202c0c0c5070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 294220998 1250 294219748 294219763
    0xa1d0402120c070314040605040605032214070b040308090105030402030109060f090b0c0f09100e0619080f090613060216030215071d0d060b0a030c0f090b03120309 72
    0x90a03101c50a04000700400c14030010000c45100c1c1e40c0c0e0f04210960304179010041e000d580242c1d80410030600c07044c45850311560195a0000d24200140c50180310307803501c0403144450070320607600d10b294000000c52100c0c0400100c0020280882800c3c40e05107542c403000402d0085821445c10408000701083c15581c094202964182d00300108100d00045440c4981c01442400300c11240082c40d40c0028840340404815950503541d40400e072850260010104000180d4080901c4284001104041425103d260207852600d03440c6540303003400101002c0203040780b50000e0859130a6a40b040401c00c229102054058204450b1640900790a400d86051700c040c2c0640d9100c221150a0981d180080c1540055242c07000f0001210400c0c0c5900e034040100c1e060002001d0f0400c02c0c202005e003450a81c10101c032207400e0f41d400b61800140c01014140080c00400d50381d031050b68403810552003071001c95800540c1c4e60007450020010010b042007440429214282075100c08003034107011000519008042c005207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 294222248 1250 294220998 294221017
    0x20d0c02132a030203041203051003060204060207090f0b031519020f12100e040209060a08010f090204060504090515100e011e1719030e0d0503090906060a1d0402 71
    0x14020076069400c4140c00ca0b072901000c000d44000350080c0d014207030292088901540e004480d40040070002c400c240c0c040d003800303403240d00c3c0d421400e0b50000c007013400d40c80544045d0031140d000d404c071540380251a006032001400d80040862901e80058400d980014403600311132410080e0324890b542d50a402c0420516449882d01001e0000480800100c0003000400422000550001c1a40c0380c0502e540840c09213401403141c0000c110740801d000d4948440b03010f034046030040c003400080c0c0e10344550b5800d58044848210100340c07122600d004525040c05844043c101c00ea800300200c01d5161200c0e55511041040d200c03821071924041a8072400041d080b4000d08500130300d8664035603444200710359408014110165000014102162008501d024408024001d000505800c0a241585100c026084d4011004e0003003a0301c850307480361182a8400301850141001d0b50311410a0707003c0c0108000f00074002d5104820422201122a410419049007403101c51001980106400c0100707009100702d0401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 294223498 1250 294222248 294222251
    0x60b0306061e0c0f010204050907110d080c0910030c0f030c0504050d0204140f01030b0f0402130b01020f0105070f0201110c07030321020417010b03070308090f010c0c1212020706020d0c0213 83
    0x1c103026411305400800885009441034100ca40e40c800040b10380c0c0c111070890101c5504202c0c06501007034429201c0790740085550441c18a403041400002c2c1203881e4184824000c039484281d1540c0d065008266104c001d5075506062001e007140d4140100144110300445204880b400b1f941741c1503443e030b6417000d074107450680d03001c0d0b5080c00d00d16500524042c0034030046030214020030000d01605010046107029a40c0504500c1d100c916018403040940b558580b010304500c94102a0007403030b0b009006460080301e598407100b41018000c04000c1c25603080c00c12550301c1071000c22901e0302007440040c0c000708580d01132800e0f080c00c0c1111001c10302d0a800f2104030040d460300108001c5200610b0b8141c103610a00c4040081188001000a05403145110b20001d400d00d0740c14040308d50141008034225680d01c20524006103817410950782c3c07402010494020719032240c0500510802c00c00c5401d030015260040f0700003452103625100d002540c400550b2910010800e1a681035001c64807100b008208100c04c5980 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 294224748 1250 294223498 294223513
    0x5040201020309210f0102090307080a0305120604020d0501030b070e18060d14070e1008010b090703020903011512110a030b04062003070f090909030e040e070b1c060b0306061e0c 78
    0x13014088d40040e45410301c82d0007122800540c204c2d00040e041d2207964103481e00ca0620310340c5030039042d09000007003803581c01580170082c28030680054030525028520400c0c0440039814411001805980c4004801d8010076000716014044000c07038150b158421004c81c0c64289101c0c25150045010000b048107131072a10036400302099421151a003140700c3c02c00031260580843d9030305151400c1e1644007040ca81c2000d0300c076004c41c461611036001004280d4000c0c0010603094101011107107199a2580001c1c5181d105640d85c0d010030081a440ca40003203000c0325451004c600b50303101c0d000d1450001c0c200803d216640c50441d0f0520201d8190503007036030300d4400c04d50340fa46000e0002825002c030045051001400310300c000300d210000c2d440b03181d1000360195200e85002e01070205110003000c210080c2c007550b1003110000100e4142002c010020380071041c40f000b5a004008000f801a105c41d038000ca8010305090003000b0150b04d6117010380729000303111096070308083c03000310700c2019038881e00484c290300340a03405 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 294225998 1250 294224748 294224773
    0x130b0409080c0a0512030c0909060105040f031a10030b01120c0918021002010e0307080f0d020310031110051602010e06030c120115050a0c03140d0f0f0504020102030921 74
    0xa4414189402402545c80c415a5070b1103c1d881807108640075100d641045c09030114034100401034a038841d80605003149016103521103078220781080c2e403084a1407413145c01c0b00c80703100310510981600000c2040616030304905581c2ca00541020501400c0d1800c080e00b182c1c5002d00c242021850000c05e0280c804024000f01401e901300b2040d80c5900c207038052507005600703c1880784144242c0141109820146040524a0781d0701e0411368460103400101c0701d400c1c404802d04503510300c011402001c40c1c0074040d0407540f0f03600e420880c196150038410702c02d201e6252040c9446070000e048419140600d0030032400a00f580c8010398110902401103500035501200304209001d040c8001e200345507610340409080ea036101c00d804135400b02d018502000580c1401700d6629180603208843d0854401d0800360060f04000706040381580000800e1603201f62920454144030000b4411510400390440e4140113a140c1900080c0d070b20306c0782645943c0541001c0d10454903580c80312039984901078950065803488103041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 294227248 1250 294225998 294226003
    0x4050409030e10090806150112020a210203070210020d1805010f1406030304030b040312021c05010501081506030903120f0709060f0f051b030705100609020702130b0409080c 76
    0x882c5018000e03450646a03180060040e1140c10071902031200801c441d68030800300003850710750001450705224451550039002c3e9628006001c00c502d080c2daa000413550500000102c42c214140101c0141e84100140550944d02060642451041c101c1c0075035100c004051710b50041040c0100201000c07402d00051040081c1900040f050342c08031101401000c00000341c5a00200b0180da1f0300b0f134141d02c00c01c810000600243c0d42d1030f03403140c003d0920b404400f581d517040034145da02c06008940051410522010320320094420940034040a04e0040c070589403d00c0d1580641111080b894481c940c007100082c0c890f201002241c10b00801300c451540b86040c1300016445800c029145003000c240380542c042445440740940a00c150103507582d68034010303184841540e1070b5104024a0034880c1c1152090580840200020000b180c400d00050a040c0420503c0100700d41180d00404c8956004111540c05641c901a83c0b80411800d8013000030780c0c400802c0043c004107207181c40108400b801041c0c1c00a010f602 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 294228498 1250 294227248 294227267
    0x50607020c0a1a03010e060102010b18040506010b03010e061908070b040315050606030a0c0e060301121a01050102030a11150921030606190e06041e12020102150c0405040903 76
    0x541e2015045a11044103549560950708419603560f810b20041061041c2d14680d56003150040c000041c01c11600c00c082a04000d0010000c1000c100d003105000800c0403c1280c2c5004108d030424581c2194140030790084690b60140c40e282c820f08190b45100c6000c100d041ca034134000c0100408031101d80340e0310981c5401a41091000381c030f8003003c0c0c42020402545500a8510440c0001c10080c91940d0f00c800103001080340c50b80d04010403c550410005640390400218042e0144c0d002800e00a9820302d40444002c03100041c0300122000240100700a980000c1a030740031820a0800d60406807481c00e000d0300d13284558541041101c0c00b5024070040400208009a0088c24400d0844004c025000300f102c0622098400c0d540000b0100011164900804044609010a03180608004502c44d00142030b641043c0c000a2118841c40198000442130642c00801800000c0001c0c901c07025540020f901d0320502c1109840d0519408002001c00c1281e5084502400380140100704915035401c0043c1051305 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 294229748 1250 294228498 294228523
    0xc070501021212040b04050102040803040b031603060e070c0515010303050703021b0607020f0301021204060501091d060703020310120b1e06030c01030b0102010b040e0c0a050a3005060702 82
    0x20002c100d01e0711012003040b80c140e40d0211000c0c107200d40b900d81d41c00da006000203000b80c501b55402e1101103400e80e0140014001003182c00001600c90800301485007c946005851105140c0b0b004000c201040850850035407204803070801d00c1d20004d032800c0290600303100a03801e54000c1124000403081542110240070582c0c040d40c00ca814000080c801e50514080030301c900b40e8415014841c200041c6043c1108407031120000d000941418034840c100c825800013907404640198030b92005002d8600103104071107045054920001c00203001c107440980b00d11000e080390080680010024211032031100d503100040005180001030408c860070306110064003990400c0c4920890140340740b0980950000d0707805002d0040c041c11000c84480015801440344002ca103055540f030302c030700c204241c1d1148901d040c10291070f00603143c400c41543c100301da80c40c2650080792141601e034170288845461410042d00c800b4120148012105400b5441d80c201000c45200070494843c030380810000a5002c910340c0702c10744 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 294230998 1250 294229748 294229753
    0x16080a0506011802040807081011030705092707030b030609120d0b010c0213060801110307051804060f081b06120a050405070302092a0406170a02040b040f03030e030601141002010e01020c07050102 86
    0x880c03500790404610bc107680440c0018428001c0399410300c0d00c031003420b145e01505c280602c4000034405d61700e50254011942d00002c80c1e50b95440340741d80c0c01c4c00d100044d48403444002030811500001402c00310740c054140c520344025510f4444118a90041100a06440d0020718000c8200c42651500002c0e0511b40100300c40c550034200c0c9811400c9000c81070741e00601c84ca403506404c01c940304803003c4481c000d0011981d405a25100001040c0002102e541d01030a6104013410032840fa02d128112448484040c2d1800b0707190400c214001e00d11310085a03500501030346804102504d55040061901015820207544102203070180076840600d00048600b1080c010719107804001e0810348080c89020324410440841e869400030b40d43c17003008903900340c0c0c48401040012b0500781c442000700d03074980040d0080403a51032403150a005040d0003406e05a080842100144420b41c1000458000120100f100da40640003071640000060b000b03401074035250b44000300071501d5a8500102030368a41e80c5d03105060250 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 294232248 1250 294230998 294231011
    0x6040506160c060903030903060906061a0904050f01060e091302090c070204050f01030203250b0a26010b04062d08180a08092b0516080a05060118020408070810 70
    0x113001d180001d0449415407640b80000745580c84503006801014012500c0076a5018042420800650420403c01c1c0d04180030741ca504002051004030f41000c0c1c2503c02508100c4010030200340d003e50038103807005003601c00a001d42c5803c91040101c18401d0f00003135114650300100400340401c08081c00141780212418001a02d6480c002001081c1c01e004c040d4154110290740a21422240c81d104001008068174035191507840750076162640204001c00b0000c3d0000044074200d10000300c02080c00d4a0003000a40f095145c1b0034160790b24401c902c504c00c24840c8039110150075007100c200b80b070010140e08141d010001071800c0300504800c0100e03200740808045003091610f038840011b50010890b80081e10300d00e0b1001000820503002c80c003001d10385502400061750b200c043e51402040350300b140b0401c002c0c02105c801c041410500f080a4001c10710691014101f10081400001d4060466807042a2000b4080346007400300c000c4d100da600042d4103031060b503000081c1030b2070004806800c0c601e101400c1004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 294233498 1250 294232248 294232259
    0x8070c0b0703081b1603050a1b06020301080106050a0f09110409020706090311010e0601050f190f050103050a020702010f0c06021b030c0f03090a0b2802030c0f0c060a03020906040506160c 82
    0x39000b03c1c40404540144505400002805840105a5040c260419440700d10276140c2c8460400f1a40e0310032500d954020004101098003405500b014160844c3e000d210142010500d01040d80035100b8840c406481c0d2918a81103421013044070050107611500b5941e45119040036000340c890340a08a0001d000740c844042041818407c80c44400e5500020703041c5039181c54100003040c1c0f03010300b40c2c5600000c42e0400d01d00d41c258040c0d541d002401600900c0d400ca41c5020005003ca44008040f01c5c406070040250000503030380b1440e24540b01e0002d00304203031075480c0c0f403c00c8002070082a10403804a14144001e0290610000140c01109080c00444901800d284041612409402140c41e00802029802d2204018200103060080c101070300ca20740e0010f000301c009210035410041000135030000901d01490300380c01e00c81c2049001c080300c01002c035080c2c0600031031300038400e0380c0401003050fa0214140400781c3e1108119002030030010081031302c4003003000c0000b00b00c40304400f045458402644000a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 294234748 1250 294233498 294233551
    0x8010c0e040209130209120f0708010e06010b070b07020a02040e0f070504061a161b0302010f030606082d090d110d170a02071208060117011208070c0b070308 69
    0xc40c41c800380a1816440d254500d200103900103064803a0b20035001c1881c2d8006200401181a001d2400c000400300d0900e070281490840320700c0003078600550030140050181c0d400000881d581075601c12100402640c92d000c040341400541c8000950181c140580c0303460604000070540341010303090b002d450100d0307681d2040000320342c000d129201d0044c440030a00d400c1104000060101c817030220700001d5101d40e0551b110751500808890090120071692418000d40d41e121189503c014402e0400b000024204030b001b40c03145074000d01310103100b1105001d0b07001c4001d40c250980f1440c07a000382c0710149410f00882c0e841d1500480144000098084103814409840009040400e014aa2142c3c00841e181035003503101480c0050411040c55020401d0344000b0307450488107001c0c40e8142d506c13803200e41045000180140c1d2041c0b10f0100000007000148450303841c014080b0503580d4803403402640c0b4529454042c0003031285900880c00200080345050516400210b0360344900c1c050706501c038119046601c0100c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 294235998 1250 294234748 294234757
    0xf120a2301090507050f0118030503070b01050108090a060e0a050303010b04080f070308030103030f1106090f0d090317071703090c0a1706130c0b0f0705060702060603120a0302090a08010c0e0402 85
    0x10000c0c1d2000004110fa801c0030a004100c6c800185403200f1841142414002941d01c2caa00450b500d900002d86202031006d1600f441d405084246000a41400d001c5082540c4514004000d88007030f81e100030640342c0e00c07000c10400d40041d9201058a881e581c0d110208038050f0010301c101c03003143c0a0b2216141c10040042108002d4940c492221400c40e421900d08845048002a11400380580c0e510400c00013032007000f00d50305c83d0a0682c000c20609184006a070305207070340180700c1010b00445c4401400003d800754002c00c00700001107a99a11800f6906040048400800c0702d030803c0f49000044c08024540452100000042a503041880644ea01013504030141d0100e000c0072203400c600081340000035020744035220b0b9402a0110081039880f407600803095400390003007015101000038507108010080c00403590101030b90020346060f252a00c0404d40700d088113000c2c0c41d19158002264840c890081e41501c3c1080c03406003d0010380b949a9503464020080044410b0200c0d54820070000c03071340341500858 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 294237248 1250 294235998 294236003
    0xb0f04050307030e040216060b100e030a0201030b1804030f020f030414060a030f020c0705120a03390f1b0609060e04020708030705041505040806060f120a230109 71
    0x15442c14200b0b4804131180d00781443d4090b44641c013044400d500701204121400880d01440b00020114002e1b010400300107001e0400c1820711140000c5403000b42e030045910740540c4d40a080c0480c50302800c400040303070002e01c41c1e000e00d03214101400703010a159000400402200150302203031056480389400e19038a000d40d204003280c003590440c2e4402ca5040000103002500d8a905001c2000c10302c0c4040f14090f6001010008180d600201d0708100f9480c00c0201c500d10200035101401024420b510014840c1110b44004510340381c54000c030810510200300038a58510145440c280c09604a2070f10b6149120940002e55a61720406806803014007829125003c03540c090b107400491034a0050107440c040030000c18550701650a100307910201d40641c1c000c500c5011540e440c99602d80c00c2c400b51040a90008515400b0060180710602c03e4140c0000c0c2c4940009089850242040030000080c1840c4284064140140501000b0404229600b021140102d040d903000a54045001d0312a03400c903600350101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 294238498 1250 294237248 294237253
    0x7050303040f020f0a0e2e05010e0a03061506200a030e060c0303100f081203010b090a12030f08070e03120a0201060816090c05071a06030c0d0c030b0f0405 68
    0x206000031004401c0012a41c0f0140180089808080000b006482d0b0340e4000b5004041510070409003000c0c5040c1d5850301d9201c1010310300903010361980300007824424040c46061040603031080c101e07641c1e001c6180380210351042081c00380085a201824040c0418881c000c0882c0e00f041c2d440036540d00e0340b4169031642d00c0d10002480c4620854900700c1d800010007212a811031000c00843c44100014802148101e496400541d0442e24140d801c2001864581c4801000d8001c04014036014010300c04581c116201c3c841c10381e07250714006001a2100c00700303910200400380d180109900300360b04250601d0300002180c032804c0103a0b071000310982e19120201f02e103039415042034100c231000e20f0422000e045042c0c0c0c64800025030540390740c0c1c40d0313180105000c01c922580e010080200100f0481d070144071b0a48a007072901c00c4c00c0083c40d0f9203d040065403085405030540b5060000740b010f8504009589034044001c1135100c03451054107040d00e103825140825a0902186000104003001d01e149180c001c1d43d21100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 294239748 1250 294238498 294238501
    0x4050303030403140f0c0c12011b0302130506031e0a0b061b1c05040801230601260a0b0414070e19030c0303090602010c1805100203040306020721020307050303 70
    0x8003250807000c4030700840807135603080c82080c2049805001920a2540c024000c0c02c0d152803200030013411200c007040100081c0c1c18403031020a0346010a00815107000079050140c1c0369100704400300e0440c0c1d21504020341011020003005038880c0040140324803500130741c0c03420038251581550142030743d504170302030b0360044020006004651404207c1494182130441607645c414002450000d000602d50285000500e011405220241c000c5c07080600301000e29007511010000c480005200d004010003190500400c03580c500c192039010401c50380c190141442e03040c014542045c0d25801092000b0300740d40103924090550501040c43c0c1c80700c0d8056141c2d0b45400c44607400b20b601704021500c91909006420301d0304440000011079031202c2c280554440d84884c06002c1c240740d0004c2c2120155003110b41080703c2e50004280912000c0303140025a041681c10642c00d800f401000d0389103108130352000f441140300190800070721011841d000c09100d049211a90b20401d00300d404ca03075030300507401e020708150030800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 294240998 1250 294239748 294239753
    0x110d020d1b060207060506100804020f09090f1219020705181e01090209120105100b0d020f0409020c060702030a0516140a0507090b0a08060a0e011b020102040501090b040503030304 79
    0x201c15203024115996011a4005603940e003000d80c3c0050404481c06a01c55041c400c541c501000c1410200c3c00d030345441103103031070141c0003e0307042001c0000c220b002c0c0710b245020480740c5400b0f00480499861140c22100e2250240c0c40009983c1d001d00107590b1310200c0980306903c030030f2000c5480f60460700c005080b4440305420140c40c0380080d5026049201201c804c0750515490510070107864001c060080d00144c561885e00140711100090071200a00e5074580f6003000099480f462a8200351160074601c1503c808144851000074400e0b6140224224030205000522200d15002004a442c500e800d071031b165226070b90140d0392402202c100d1303c0030403001e12064110608880e03d20f11024000c04d0115204140c0c00d03080d5007028110f11096805400054043c0312201d068000c008039903c0a885480143e031520149540b0703010040c00000d211519200702e460600025088000b40040244240d060507158201c080d000354810b00c20355021522103040001c01e100704c47e0a6804950340603026626540e680da = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 294242248 1250 294240998 294241007
    0x12021608030d0e070302090403170114030a170c1506040c11030304060e07030c0915060e0f040515061306020705030a02060708160605011412010513140724110d020d 72
    0xc2c521241e140b04410713001000d41d075425945400b55010f40c6481c01c40c594007103000ba00302901608840341c040d442c1c1e110101d117528002240140150095108144220680024042c038407801180c41d900c1e03c100c0300c080398004051031000d401030104a43c00c1291680f00003007643c410555220107445038100784001804104d0940007040307031403080d800750381916480e0360f15221501503a0304002c0ca526a2059903200c0466010a40c01c050140c0c5d080104092464500040c0b0031210b0b50f080d94011a260b5020800c03400e10268007100381c0070002c2c042c81c0c440c00c074810111042c407100e225840040c0702c0d001c00000c0c2d50401292200c0856009001180b0b018a0340c1c84654040d400b164000a03500c2583c0c2a43d004a1058402d6602801d402c181c07440b9814541010072480210586801c02a640741000388241b803029082d40c00e200c039600a039074400044000b006a0f0a160b5150b0001c618159101e110b01c0f0644016050a0010f149a449203105241d00c050055984d80307030700f10440090783c41041c1304240c0794051b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 294243498 1250 294242248 294242261
    0x120b03121e040605030105120a0203100e12071a01120f03050708091002070f05040605130b150304060c110a2307120f060b091e070c0501050412021608030d 68
    0x101074214000040403600c0310541c0d10aa02a5000590100c018040b624090b80c03901d41e8018060014001919182c0009440b011144205c5501681c7e07142c1c2505d80504c01d000238a02403000040d2551070324042e08000b900042c800081c0001028120004140000710401010035039410062100d00410342e030340d06032501e6000f400142d030f103600f05218407107041d50750449000c02110f46074040d000043c582450408102019080544203605000050001d5101e4108105400880c101c001c2840300c48100480d0500d071011448600e0031800004010034428150020110300b03103240ea5002110031a40310054480358600c0c03008040500840c00794145c03085290b00362106070810800d4510541c0c0c1c0786101030108201c2002250129402c03a42030081c00700398802c01d05050340544d00c81c00f00745005e8004000051030003000b244c082d94042c012a030304178451118800a180d01070000c01507810300f401d1007001000558140700061150141540d01100c01e03101c0603003240c008034010350402c1800089800900070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 294244604 1106 294243498 294243517
    0xb090d050f160f0f02031207030f030e070f0801050f010b0304020a031e02130b0405010506092407081c150f0303050a09080f0d120b0312 60
    0x4000c41290036212410407465a600c11011495840b072140b07000203410395501c403041c001009110049525801d000b01c088862054411416030300314072401900500003809920703803a69240c001e0700240030f40c8120f841a12849074455411194905040c0d10a019507919901400a00c180c002c808a02418034103600d18514a00b0ba00822881406848000c00502002101c1306954a00080b050f081075402400c40744201c00a42202009d41500c04c1030b10700c62490300c2c000182034900f140888554000281c800d00b0203446000d40d04100b0041b0307041c492000c6500b005011300017041c0c04010030340e600203425101440c03010b4010040c1150a1a03207081420680c00f04288010030900c002401141d91618140f40c1ea50390300340b03045030307407401d00c1c0d02100c91442180d8034072030aa1000700c0c500c402100741faa550a1118414491382055038900040c2d26099080001020018032004004050906 = true := by decide +kernel

theorem cover : BRFrame.Cov 294064748 294244604 := by
  have h0 := BRFrame.cov_init 294064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 294064748 ≤ n) (h2 : n < 294244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
