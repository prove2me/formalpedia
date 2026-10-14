-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1638
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:59:33.890983+00:00
-- url     : https://prove2.me/submissions/e22ba0fc-0d5f-4908-9e7e-9280b8381963

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 294424460 ≤ n < 294604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 294425710 1250 294424460 294424463
    0xe270a0503190e01020706080a09210219020906060f1603030c0f020610060e0f0a180501050a06080a0207031205040308070914010e2403240103090209040b060a0f03 72
    0x3080040c61460042d00010341d031050103194144040b1010b00100000c0d035548291040d401004909008100110f159801075950107801442c105880e040d039091a41140128035004000352040e0502640ea444905241001c2c00390024001085a60748505001341c55110070703030b40c0031a10380030000207030490042a000da11396400796400041700c1e00700c40800b401003a031004603181958071403401c00c0f00001d11810000181d41c414582448180560320100d42d5030060031025035403100220760041500c4942180880301030194200600c0646d07070703900074480c1c0e00881c2c7c05401c0004002400091940034150010007100c0d00c43d14081c2500d011140da01400c0300d009079821400a1014014031a50b180d001c0d0a074400350661600c1b010707618070b01000181c08080c0609a25020700c14840c1c20101c44084403a80000b00c4c0c2c0b203084403a0b41c915000d000c40801c0d80c9030408c00e84032040c0c1602c0d08415948640704030348404c8c2c0c0c090308541d2181c17100d40782c814041c00c00038007141d800f2160410218511200d000c4400045 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 294426960 1250 294425710 294425713
    0x803090109151b0c02220e06070c2018010623040f17011413030f050a20010b031f0506190501051b1c0314010e270a05 52
    0x10041d842c04040300c4100c1e11056508038100500c0d40e100002410b41a4111030003814007003402c001c6440807445036440804070500d854034044203180ca032482500004075079005103054401c2c40c0e503521000d0b9410256000003808a1a0700110a00c403030300300c0504030a8170b01008040d0251184d0207500716800d80026000100040c00e518840d01100956200e040c4041003100c040ca400c1504001540080c82d150303115822200001652810480e03c0039070100b404c40c0505185500c861034140c40180010a1750308003140003a00d6050390034102c51044043e1055003125a039910146003084179a1500c040d80304d0702d40462556200324188041c0e42c10803050343e250300c08c819010a1080c012190000303d9100400303140c09101418500d42484403a2920300d0240d402c242411529000114011250740246007511741e00c5104187c54041c074003003624201481704029a500344400141440400614a000e120382c2451048203030200e005400300c940503c945001c5405d00305103140761000c0f1646000034601065506 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 294428210 1250 294426960 294426971
    0xf030809040c0c020303030c1c0903030903090605030408040902180a062a080703050f0409050903040f081f0e21070b060604060210091406160833030a08030901 70
    0x490a150291800129041c18800c00f0002c4030340100c2d40f28880104010701309440001c2d8868246200403c80307100707604001c400c00550f0340d240b03806402400004401c0d800300381714a00020b040352184d02224403403580401210b041912700309410f8080c1d0000d03540300d801c1440003111480c0030749030003204a0040900303039980f40c1d4405580003076001880a07252924080e121400a500c0855a900c00300c9020f07030381c14981030b55038416001a42e03000e80a9604007580d598100402d02640c100e000000d4000e80340c0c188601c5c6046544d803803401e50b03101e52180c0ca08103000e10b505000845900356601c154210302c4500c090b1696505100c2a44d405070034100c080c0b0040c25130101c1c1343e0003400240070f070b03165100c2d0040d15507034945030034070388084d50b25108030a08038002ca0f01c801d100820001c480c106844c40d162502d00f151030354281101a85503a11904600100013078030840007030801440c90091240a00313118120340c02c01e01c40800920b502c010300020080c2c15204141031500020050001544614514000041c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 294429460 1250 294428210 294428227
    0xc0703031515080708070906080105090709270b0616020111010f02040b0421020a030b0910060801020711090601140705010e06040516060302030712090c090f020405010206010b07030503070503100f0308 88
    0x4c05e000500640c0030009034107002e1202a07000901d45040d100100c460800b2035441c40c5040301c524203681c01018003501c0489202c409a00d0b01210203040d917000400500158401400b0302c051340c010215241c070352207030a0303440a0155024580d00f4034004c0310080089080e1003800b40f04403c4ea03016501c001c480341400601044000102e482241907102d100800c0203500b885500040d2000300680000742c04070b00d103140410544041040f400ca089501c201b0180601c40d50781507118000c1d00118801c1d5060392501840c80c1c075901d001e250161094105840720000724070404489000c603044040205c443e5035989000c0791001c6002c02505103d144528010945048004c0d5140d078500d16a90168040c58014400e000c01e01e82c11458124840c1d0103c440007a02d5a41810302200003100369010417000d034601401c40100300080d03001401038402c00c2c1c0845400da60b8030018500140f1944ea0003900082c030a1010540c3d5034400d40003580c20182d00340695004949800c003480010700746520449a00000040010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 294430710 1250 294429460 294429467
    0x1e0a0c03291203040b03070503130209010b18030d0504180207050f0618010203060d0f02010201020d0f290d02010c14030c07091b0903060b030a080c010b0102150c07030315150807 78
    0x20b18014480d000e075091526110a600c079901010300780f0010f000020002500d00106101c286084a400624460071941c0d140101c403840d5001c1c8440d0340242c10102e4804800d820300191108192a5039601c9038540744c94140d0b4480765034510302254541035001c028810104200b000615445000603010340601d0524181c1b0280240744065200c0c01640184108142c60303a80441848806400484401041040e440101e00a110312201c0d00d41c2e15103040085c50103254140d002030b403081920745291124149040d080c00d0407502c0f003d00c00707900c0300c10070b561507005511801150303640910030000c0800d440002c42404d829500241e081030100d070302c001b0003004842c040b80551401030b075240a20402c90f043c1030000030003500c2c5c0c0d4040030306095100c0600c0527440d101005540c20094102e48266114101840510701030028495501d00602c030f0500c042c40b000383c054415502400080c00c0441c40c260142da02030f030107000b5416122400320142c00001031189034100221241d10040d50300c0a41624004401070b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 294431960 1250 294430710 294430729
    0x100306030f060f052421030a08060f1219020a08070603090c09090503090411090307080709110a1704061d0a301404080d08040b1e0a0c0329 61
    0x41c80505100b400343e020307900070a2003400901015511304049a41d105076030700e0700d103410a06c801c0c45884002414621580d06c50001d030b000e09012260307400c40700b081500700160103050711110728182e0800404000040b801c14402e6020903c0079000105c855a182c01c81c43c206002d540c0721501080e102c0c4044410000c8089181000e0520b40204001d01e007202d0311125074a0248001050055079240c107941c101840040a581c283c0c4401000c558a180e122001551200e9041c46400c241c83e0a01680445091240c0c0544240d10840e586404401c0b0907684148a80d010203017090f6046541c450703a18005203200c01c0d01801d41102d03840205062a96440c2201c00c404400400c0140a003100080d14008030b0201d159140c0002c55150003500020801c4400c038641c0705075400b1000c0c501c0303104034500900390001e944074811405500300035803651703c03205540030700311350b01030101c400508030740014003e400c85c2d030b010054480da1443c00050302c4403c12000149408420841040b20300581e51005643c038104084 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 294433210 1250 294431960 294431971
    0x6080f06040212060910030611040e09010509061f03020a0e060f03060c0d090204110a0305010602060121080a0318060209030d02120403020409080c01090b0a060501030e0606100306030f060f05 84
    0x21460103030000300240100380040c164a110350100400720b504802c00c2038002c6d0141d80c0101080004412040281d981580240300d04030b001048080003480303030103040c400c0c14030803580040a0300715540c4003000120304400d110306640ba400000f01010015840d03a54001c005000300150088481c1001c9040002030b00d01008124441e5202c00308114500744180c0545036909402c08001c01c005003144005805008035000152001c2e0012030b11385085681500254103c03041c0d40c090b2962b60b600e69120903405074441c10000300d42040e01c24070030006080c0d200207143c5850035150000d0500d000d108058000c14020070b0688940380c0124489020307180510402051640034002003440311215262030072030b40070b00d11010744a10340d22041002031288160071200c0e900490402040580705500c2c11340900c40d010749003403045514014020800d54005e100f00c03543c0041202c01040c0079070b58034080280c0c05694290071010951940c20000001e1000c1a24075041c0c0e108601c0450320081d00b566220449000a20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 294434460 1250 294433210 294433219
    0x50d0801180e070303210203090d0f32090301020d0c0306210b0402060f07030c050d05090603150109150c06050a0902060d0c02031303030804020f1e0f0409050706080f06 74
    0x744600c50100000d815000c5030745c1814020341420035215081b03605450088080d064078000800c000d55108003003081d50b103201c0b403500c0d203d00c40020402c00712039001155840502d04d61f50360804458089a401804a69844c1d001e1824a0701218502190a90300808804e042c4503440784132450101d43c05004050180a600c0d841002e00c1c1c0d8030701042c0c42c80c001d400c0c0300035011640210100c0c2c20340d1180011152031592500e6500e0b40c4026501d4018500086950300344e0b07242c090f01d40f0b07514040c0d1051048a00c4500000c05541c1149c4900192642c0180061561b0b4180300c42c81a0001b0251080c3d030300c3d88440c1426445004e0701441d49c0c02d102081d00c6000307160b0905903241c041c4060060761024141d03210008488000200740003418400e0345940300e00b20130079075202440b140010806600c03441a5102e64825180344541401d900c00f8000096440c1d542801558040c04201041e400c0210300d4a03031002c00280040350030b020380d0701c1d064282002c540221000072841d01c01c00c010409604d10481d0448020788 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 294435710 1250 294434460 294434471
    0x20c071505091e01020705132c0d050a1706010c0c08010f06080a03020a08130b1602012705010c1b1403061b030c07020f0a0f090f0203101a07050d080118 67
    0x40000e403203100c01e0288912554230300c65000724058055100d41120341d050031101a0301c54081410703405d815070035a207803450b620070941c089074004c0c420b0051f81c0c2c0c00348040d255640f81c8900c54099402c5000010002070403c00e01c031100d0400300c4e0400700b02d4401009054000690700541010000c2901c946030412039550b03001e000c045c40043d40c0000c4018981e40c01050290704d501e2003201140c10b0440540c007840d0304150115400c55043c44000700031040380c1c0300340c8480082c440d100818403045909000ba0b4000e040030000708009550098600041d07941c07203000d50302610300c40441c02462550154100340e070210200c000c03041003810200401c542007541c000248a07030390f00040c4e1101044c40300400c0000d01d44130200d110001c6480714846600304040043ca0050402d40300d402c100e4489905103c1c1e09105130910103802c0d8129554822a401030104e450a0386545017804070411452034a8003025004000c100035250125030144114141c0350311540e0380020b5035150280c00460081d601c0b940e903030301d9407520 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 294436960 1250 294435710 294435769
    0x602090a03061b1707030c0203130b040e010509070c110a050301090501020d050903072105070f050109020928230405070302010f031109040c0306120821060d0303020c07150509 77
    0x100c02940300ba131514011890070300500c1f00302d0079400384c4403c0742900f40c1074040202d0000340760400740040d270301d510060403100d070307a1a010081800c038169404070101c4c3c00500c122000c10005001e00d4261107010f0003c2036000c0d61100420300311480d0480545e107996002ca0b074003c00016034024190044402c100450030709070603850b815060311409114480c0e00010300d00c4130214038002d80075140625007000c3c65400c1c20480b810003c0c041e09044004a10501c00d4000041840032010843c02501d8030f01c2c03032100110010b50100000074940c0f6649038071380703002646003c4031400b0320b44c0030184501c3c070540c05072280601e11310014001c405030b070100d081414109611400141c03418401d0782c0c0320342003c44020860080c200400d40040526030042e480000c14031b03d003001400a0040100348000140c64504000010082d9801021000b661010340c80001e00b94842e001c00d100c2d03000341c140c0079038900544241640e80d0340c401640041c15480c00340072070008144013206141c001c000c0c0542403c0380c80e1002c40c52420 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 294438210 1250 294436960 294436997
    0x804020102120a02070e13120908030a121107080417011a0409030905060f04260a080d15030b0f09060f0c070507091a130204030f030503040602090a03061b 68
    0x7082d00700c0d0881c0d00c04248900414800c1080c98000c20340f550000b00f4a040550b484001850200c10a482e801380103284000740751700c244914011551a0805142842102003084404445003000c03080400e0311003600814140c5100300409517140f090500f107580f40d1404a01044080344050191601e9260030480558a007401c42c050300b401000700e030001040001860151880009500311640183e00400c04426500c03598006000341c65003503150301e142c41001407440d40d00a005000d0003040c0d40002c03201c0b000251800340a011040c0707a1030008100201c1e5001034008901c1c0d254030a64961a440782031008102c4101c1102d904442c2c0200540094a0400751141c500302000d0110800504002100810301600380200c00190401002c1408a5801c803585001e040422034034442c80b07107500c4070303800302030361712a100700c0b82102d6014640c070030740392900d44040d281600002c20a031001602000b000300c855030796406460266100f03400004481518041c0000160f05283c0c801050085807100c51817100305 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 294439460 1250 294438210 294438223
    0x20109020603011701090b04030206100512030a0f111005060a1211011d1e03060915061306150305100f06080c0705070e0f06030d050405010c030f2c0f010804020102 72
    0x80070003d0f41c4010801803092401801911b1014000981780c0080c03004066010035158082d0408111814100d5102e008100030340d9041c4000d94a203500400024407911300451510f902601541451403c0c41d066000e0b0604040801068143e1780f41e95000308032007840e200e00c40d8800f9010a4803181c0c102c0e0095521481c903440d00d102d40c6814440259805840340354080456681e91201604107074551268042c0340020b8899404c1c01d40c807030700034840000c0c452540001c0e8010582104017544e400e50325200284104c1147c00c904904078141c0b12440410204c1d10b0982200c035428265a001030145800c0e40070055140361504094120001840100266a40000e0154010425040070b554a0a151030b02d1403138181c0561040c12846a02d10402090003091001180326074030540a031989071001c214100e070f051049000c0c0ca40400c0c254400480400d03c02d007040381c4100d485040c5070300230301c680c00c9a0b40c400c00c60b01c49500c81c2c0c008078019500742608201078000311700344080c2028200e0b8101940040d48400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 294440710 1250 294439460 294439469
    0x4020d0609020a12050609060f090a1e060203040305030a061e030305090406080f0d1206031a130b16030f0b24070602030103061a0f060a2303010603090b010602010902060301 76
    0xe403207128400c250742d00c06100400910340424200070b03c0c001458840e4484108403203c60040c0100b500158130352420742e140c0c41c071540351440900007c1c0e58a07518080b0122405d2004a580044d5030010340001d5024030003140580c0c040d403591a11303844c2c040484001c0e24040d03040750b1114400c0a0941c201f541c0d004646000342c95040c1000e9848014240100c0e0003010300c0d0340500302c01c0c480c0b00e1080d00b6040c0701081d0264400030b0340d80e40124146900a20b28255411440001c100600f0088841c070070071800f0a100d5000322810a000c001c46440341c4503064481800d40e15480012014850b0b441d18a825104507000900d4a14050000114800001d01c507240303000c4010b0180075160082400e1289000300300c0c2d03540c0e580100219201d585031705081009042000110b020f000d15424000c46500d0010140c0501190050071b0031310b0846110000c444001c00840f4488080e02e00b9460341c111040c440c000b940c081c3c5115540000c01c4a4942480a8200b106901c0360341964980b0601d2805a10740c082141d054a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 294441960 1250 294440710 294440723
    0xb09061302031c210c0f0813030309030c02040e0d02150103051c11030a0804060605030303042301020c1f0c05030f01030f02280806060f09040b040201020c090c0a080a020304020d 78
    0x1404510030603601607080c1d0728151100308080004c0d01c0b0042e6140d219082076030003942d520381020740d00d0105440800090700c0c404d15040b410b41c1000c000078469001300040324400c0c40c003c0300c070b290180c0c081000e90380100450031080d0031551b100c41515504014a10706118400004041035140d138036255180c00c005086107130004282d203004c4170391134040c80d051002c09000d030044980e10001540018200e00f01620201c40140c01e00d000050350340360010949001c0d51304501501c540c0c5c820b8a00d420100200d0000c81481d5540a00071a100324405000f000c10f0b04400300c002038044044580d011080b22907122520b82030010a0080c028400d18040169056992209500e104151a400003412801070b4020041c11110521340c5020000f007288a80d030111030142040301c20a03240c02040041050b00340001c541c22954100020300821015640103801c2801801030380d0410068401040031120704a41e030810321100042d07a030319481e9100c9921640a01480f00440c1103090035030029224003400c0380081c011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 294443210 1250 294441960 294442003
    0x120b0603041205070804030b1609030b06190f060e040b0901060f0c0201021f0b040e01290d020a0602060907050306060f28090c1404030305160309090203040b0906130203 74
    0x840e4083d200b00d5600c603800500c155280d65076898290800d02045950040454004882e25081800742c4201e41c19264000240a00c9503180018022484c1e400016040c104041360320005200c03000300800707806840d640c0d4401782030b04c0341c0d081440240c80000002900400507600100301c000c1c9d206501c108000117520b0300401c03003159400100e150010440e00c2a02c2001c85031200035207011542e011004455041ea003d2140a04100f070040c200c90071140344650441e801c1002c04018401d14902c88803084000740050209002c64010030b0303d4100b00c1e007000004d80d20580500a10710b0040042c5002030804400510b258540103000c1541d490395003441c0c90280c036111401004171480305070504200007101213aa081c0381c4d83c8603401400380a803103245c1ca01050b01407200d000078804c03d4041b50196a010b8584c80c0c40d00d07205410150051000100640400c20344020201b260b402c240000c6000703e000b40b018403031904240440c0350500c513020b486000304421134840751005880c041101d6841a4075420309120 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 294444460 1250 294443210 294443243
    0x60f030d050d020f160209130c090c030608030301080114150f0d060902030a2604050f0105160501060f1701020a020a03030209030f06270307110405040204022107120b060304 76
    0x207030050504030030a1000100310404c0380c0c02c10300517030702e003030303802295142410f4a0b4054000d150615025000d4003030912180b081c800d00d1142c1e00f140c50309004518000030465a2440c2035415038000380c12401d1241d4440d03941d04059501184025080b450850742c814014201000048a0001d00d000050040c00414032020611205900420074650040c0642e4100b004070f15000c440030140c80c038180e01d58440404c12000d8030704064165816281d024282c02c250300900401905c0580261100049107000860000c002650a00900001304000c01d10480a1410031007501d1005c021901030f008580e00c10b0014030459a03001584282c0c860f01400d0059882c0f400f04003180c145107140c1e48031125442000c1c140500500d120740301c0803001c440c5202c0f40e00c000d0702c00e00d1030307503241d21560034007070603202c0f00710001c480d81e2a150b0b01094000d07200410043c81c01700f045d22000700700004902804034005d085010840c196820184e120184031003864200b207c0b81e030b880c00151aa01001d8806800f2a01c410b4805c403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 294445710 1250 294444460 294444487
    0xc2208100f0e0f070305100603320f030304110d0506181204080f0d030e06010905070219140f010501050d062f04140604062705100306050405060f030d05 67
    0x3100a5851059804401042c8030f081d80c2e450140c8400c0b24503215951000d50018031622031001500e600000312150b008044040e40302d0406040d01e00d0102c200c444d60812005c5104000c0c400280c0c46c0803010310b4581c503140c2801c0e81c461042580d15405482c089420300006100801d503150311008041000000951403050a0b01c0c1820b81180000340709030004000c11520ba0000d25039228001c080c00f00c0700c0504941e0300440644648440c4000541d0014006001c003c0c1c050304a940d1160040c4110f03103020503200c1d50403080403100e001c02c1d40d400788214203c016100c0280107210348501004024004c2e54980004103034190f1210700c0c017401c8a5030724020f50003440104240700040800e120f034200c0e80d05003030750005004c952192203080844800344200007000d04000e8182c604a86550302c03010300d15400c001852643e120841d6000003060405400800c6e1696290740f605981c01c41e50341c0c0010898280030500c02282c1c0043d02c1c80e48902555050b44640c1e40d00080c40582068440c13420035103400c400030304403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 294446960 1250 294445710 294445721
    0x5060d0609050702030403060e010614090c070b0412020f010c0504182004050a060806010c020609180f07110106030807020f0a030b041a07170103110a09050c2208100f 73
    0x210441e40c01c201c2400a200e80c00806403050b02c1c003840040101106802442d400c0703407214843d15099181c0320b01c0328a9140341c50140a98005014500ca520302400340d41c81443d500d10403101103aa500210b400200720560401140e8503502c1080000c00a520380004040d10070701a03481403415011805800c00300d9041c0d01e0700310701e9032258000340e0b8101c0103000e03100d1b0158a421500505026420340350700099040e108403503450042e107060715114610000b603003c0c0441940601103c075044840d0f18900410345103d41c0040c1e01c540c60744101c0002c0f90411680041c4036448182c00c40b00f00741c1c1404014008a8244d000326406140d0440b2644a007001c2080400ea522003070342c1c00a05034050000401091205c1300c1c004040e24115516421020341c0c4800c029503c414540b104440401e10040040c800100d803008800c4140341c0050030b0780c07506507450b4142030650740700b183e4550380c035040811445100e080b5900217074081c54403510b01c030409508252a20b075881c81880707038841e80301d91910048403000300d07540d00c035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 294448210 1250 294446960 294446969
    0x327062a2101080d020313060804320705010c0827061303031b03170c0d020f040302030c0303070b15040f0e0a03080609092d07030309060206130b0105060d06 69
    0x14001ca0650760706001d04040030911074111503004401a00c0c036070320700c048100c4140350280004030600c203040943c1156140d8004004480e0340e400034074041d1500c4807801c000319a40000740030f0400c10080c590300b0039040c17403203940c0418144002c080f601c50001340d100c8143c074140d049520485540c0e00910862491841031a003425410100000d00180b54500d000a002d058900940f01c0546c026045441811169a060009800200b400112032441c0342d01440c520303040034010b0016030400b0400c100c03c81c2268002c4110600c0c01c000001c0030800c50030140702404403094224055400c1c40c0181c2c0b90b100310090002e00c1031050054040c0b8654075540d49a100c40850202c1d80410001440d50055140c0d844000031002e8000c1051007000174641c0c41e2501050303104002c8070028001c0c205220310380c603052001c0802a084070005c0320414002c1c44c0820072031900103500a075120245075181c058040c1c106500500121480a05922402c000c101ca03072000a044950a580595440780d91a03c200d000b056980c11 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 294449460 1250 294448210 294448237
    0x2090a030204020f041d1e0c0405042f0c012f03090a0b010e01090506090603030d020a02070b130608090309030703030c02060d1103010611160501030504030c080327062a 74
    0x20040d02d0f2801d40011b075403142c0c0f441d242007100c5200603e0500103006044410480302c1a04000500803400d10750040d0403403c2c94110020b0040c050101803501c0e5000305090742d441c8402c0405c6080038a902409801ca8403031140400c1c60745210100503c44603101c50004042c01000000041004064200800c43c40c40703401c030351281030f296141c80081030030340b0080c82207401040c182030100c1d48034500710300b0190240707070f0003001540750000511501c2e001c1d400204007001907014841c0c000580c0d410b045d00800034410b00903201001141016800340c407060010704101416072041c000102c841e00c0025608055031303018100b041c84030075a44002a868030400880c180d145007045c002c2801d0410b2040518140c900076251121000f2001000c15a22040c0c4c0d1503034820422844020003540d40a45d110982290003458420b54414503615071410b90343c410f540110071103d503c8580781c401c003403000d80034008902200c00381416007400e40310750092000c0504510644000038200e41304002030f5004031640c00b070030401c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 294450710 1250 294449460 294449489
    0x1081b0c07031712180a02090c04090906020702100c0f02060912150f090c0d06200705031806031e06060903100b03101401060e01090e091f02090a030204020f04 70
    0x103a40f04070300d802540c40d0120214a240128400f030440c0c41607248059181c10081250314071a4003040055607000c1d28540c42d9074820400407595a980d4000d03a02880e0240001598503401841170188108146852008201807421050002016020034800f0540c0480d03849480c0c54010000404040011101c0c2440e481481981e22155652044051160480200e034030b2080c1c1d02d4005a41c0c6480440403041d91080c42c400820000130556031012050101c0c101c401c2c1c0c110101d07070f01500d110b40c0c8601c4003902e09a00205074041202000000005049416a9454218100104242d51156103600c404490031000c00c0007030826107408054951581009040b641c80c2213080e15243d0040464404403400fa014140c80c412900460380240d86003100607901c800401d07883c040d000c4a00035075000c822030411408400003e4a14600342040d80510009006411045607404410b000085807111880c1c02c2c50040c058408140d943d03200c0b5400306ca8040ea03000d0303545c500d4000800001d01c5140c120910404111 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 294451960 1250 294450710 294450743
    0x70e03010b1c06050f0c0a030e01090206130e0c091804060902041a0405010503190f05031306080621101a18010611010b0901030f020102030c0d1d01081b0c0703 70
    0x11a1654000e02558040044d80c441c0c02c002407044904894400d081c10342000140c4601d40b2035445560000003007030002030243c245900051680d445849110242010f24400384483c20701022400e03000100700c030204d40380c03000200105528074400b20022503205507800028091000302d0b003005054a90050003048051070743c100c41d0664511019041d0300035440c000000c101410002429412420030701c00450b0a4038280d664400c0c82c5080081c215800e0005108a000c442c0a603100f00d00504002e450382030043c6003020900a8a01010101c10b52551640c20749211011000c02e83d12000d261100c00441d0003802080e542142d04003a05005811102003001c0c0c203124041d0549036410384050b0703602d1501c2c000501d502e02e1b0036240a840040c1c0d102030b0a1004100203100e000c100c01c6254818010fa90404210080c10790508451905010100c0c558810680201b42c24210080c8402000d08000c45a0700340217540c0800d44020480003501c10314006821041d241d02000100025584541088900e2854 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 294453210 1250 294451960 294451999
    0xf0801031518050d090509060f040506120d0e040c020a15021e0403110a0b0309030a120b19180e1f020c190303060e0105030303070e0406120516170303070e03010b 71
    0xc01d04194001745d019035020a81d841c0403020240142e00c004c00511012916508110003031070701429a55000303c100d0b036860090003050004c070071440d880e9240d80540c55906010300c003d07503d50303820a1003150840a154000141100600c020083d52040f0060b207401c000300032403409112111105c10b00c003d02003130000402808500841d1040416500011903544e9a08118a05c1c04103944541c800e800902c92059030303e224001e458040d01c4011008240c4000f00404112a82c02105100d00711580700700c400d00c2440004010807021002d6001e08004640e40d9034001e54075260000260300a401250000710720072110b50301624082c403606029100410f01800000389503001884c030071404641004400034800715518507040c1200c202501540c07541d55030a00441745d0140d001c425580c020355407000400c103940c5540503071103003d00c900010280c04545908144d041400d59102c2d144d03241c0d251503201500310000c0b042e2500024070341407c6400d00400303c0040e000d02a203d40c041d4020102d0443e82c40b20116 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 294454460 1250 294453210 294453223
    0x260c0a030b0a0e0d02030706020306060d0504060515060c150405072c0903040e0a0f150f03050f0606010e01051b010212010306231314060906160f080103151805 70
    0xa864004001c1e1040c03011640740c0750b80507884c191016030018440e500c045400c5400441e8083e0000300045c0c41d0810b520284412500c007901c00307a84d01555842000700c0c85e1148080d01c4070b0600110754043c10102c00651543c3c0d030307440386543d45100d00508004a01000001c024240c060190005604441c18007503840c0c881711000a400da807040141da101040005e4004000c440c240c3d02000f0001c1003a40d506901d1350060301400c0340305641c1c1584c600c2d04441c0c802c640110800540460507c1a1840340f45003000e600e8221702c54007403401904a242882101ea0f08010302003003040d803e003407042c5c0701d0780002e0031100070364109100400e00f54000101400400200b030b50884c103a0384140310400001d544032407020500c151219a50601d2849240402c5050283d103000042561007148041c80042940409604040c01910041901d80c40f500c00c0c0660700c034005030001c9040c0b035103141441c04409113003401030030b0404c188409080c442c0c0d900c40044103076402d60080101506100c3e0f5a980502032407406d2960343c0e2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 294455710 1250 294454460 294454471
    0x703030b0316030b04060e210a14040f0e04050a080408060f0f0405071a040f0e070908191101090e090f01051501020604020f010c0b0c070b0c04260c0a030b 68
    0x480708a507101c40c0c2c00000c1801075030f4004c00351401aa40369a500e000910b40e00b400c80c2010311401061841c0503410082004c011840749420700e4541070800300c0907200c40c407900e079501c0300c0c01ca0a1100b44640600014480202c9a8844140d50340780c80c0c0b41022814028681405020324500140c0807500c00c200248076400b58012900e048a42c0c3c7e10102c40031843d04042d10000c195030480c260030090401801800700e0f0800303040030828a003c0d0ba0740e007404c003221100c1d4468210f0483d174108111155130042c40c1d5600400700c000140525030340700903000c22001c07004403000b0a622481e03001d00601e64450704c500c10140c4600f00300765035181000c034100b540d564841404120158241400035481480b0340c1c40300e4403070505c1030b0005c1800ba1220341c00c2011000c2880b10441c10070000c0c0f8182c42c041150302c000b041c000c0bd18aa00c00e03075144900c0c01e0062000b18000d110b1070342d008041008006d6107044441180c0c2e1014601800c0103041c8030100c0321030800b03004c4001e150f841070800c0008406d201c2e600035100e0096 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 294456960 1250 294455710 294455713
    0x618020c07141f0219060e01050a0606050706230405010911191a070b0c0a0f0309150b040b03030d0b0a0812040b0703050408010513060c14031303140703030b03 70
    0x240c0d070703001c001c0c0c14100c0c4010030703c0d00808032103015555041c0c0c980c0288100815401650012600307a00300800c0a2039003641900c20a854000d1012003071020322a00350000f0f442c403428481207040c03031400360492107148802003c8503641e01d4090380ca1100c0d20224044200d01e04170408503420f00d402c000d4040c21182c003098a8140032549040309900d0b0a03048650024105408014000c1c89c0c07400303840d2140382c1080700c1c2100c0300080050400040d0144000d52041e456140520785420301c0d400002c20003818000c0784010b040c5020003541c08034250019002e0f03606501a00130608040c1305000c1000f4001854416401d8440842d02e200d60b290750b038101e6074845006540c1c234885241e0b00d100c07860351035003080c40030f80c0d074080c7c00c0009101c000301d088005c0a406009061941c501075445c1c094500b102c50880d046480540210503500812015002c0d12209a41b01d24150415104124080c2006d20014005448441d005002107007014001c07642c84001010384440c5a446240e58140500a0039a41c11240d109 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 294458210 1250 294456960 294456973
    0x10501030b0d1707150207061b02030301030c050603040f0b040302100b0301061206091a040b06040f1517150c04030c0512120717070c0905060103021804020307030618020c 75
    0x16402c1528840010a81250300c3d4010400f01040c40c122690188106881d45000241500981e41c0240001c3c80010b01ca42c4001507068070700d920b564650b20040350080e04541040004102007404100a8000c1e01e904803880c99503a12549009040c045060320000d03c130706801d4041109054012403059441c4141282c1800310520240404d800c0781c12a000d4081ca02c4401078120000c1030483d0b2080200a11500010765030f0404002c0301201110222412608404464100b050300d041c180509101c0c03680b800c1c0240007000607801b20f030003820384600508199891203480001c1d000420080c421410410790508003e41c145202c120045910a000030758103a15000300c006420308086841c4002400850007506400c07104110000059110341400d941316800500071800d00881e0000522416125480ca45100352070620340d0025071301c006110754141803042c04202e0a03030041c960400b1300d10700100da006036255646041500200425000b207081e000592441c206445100d5000305040a400341c120340f00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 294459460 1250 294458210 294458231
    0x61803050f0f0606061629040f02040f020301141203190302090a06170a0b040207080a0305100e130312020f070309060801080601031a07110d0302091e032107020301060e01050103 78
    0x210ba12070320805440100c1c40c40300100107e40100307614071806928518088442c0c48402c8824507103081130b6029503400c00c410740c200017186401c2c4610185410820f00c04d41c2150700d413240006003901d0443c500d90192180c1c000500095a0600c00c40c1e001000c10701d0b500e0340781080d4000050007904034203102c2c2d001c3e074514440406c00c540600e00c800021a4114049403c1e03603190380d0320030080c1403c1080e55400640134402d00c0f000482c00e2000c0e03da040010380c1c3c002018070f001800032a0340041640061412001c240c10700c0f40d142d6003031804901141d05801c16006807601111110000e1091340d080700052040403034140109035000d010322007140c5003541c9645290340c032000d01c56102c407002e1000a004038002002e45104071200341c040342e4010101d0074081c0d4509207401407182412800c030908000a5400100445145800f1140328001000454080c01220310500440c1d80e45d0055003c240c950351060043c0040011008100e4441642c00380c02840743c0742e61000000381030b101c02e010b610b001c00d003440107144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 294460710 1250 294459460 294459469
    0x10f091e1a0603090742030209060301032f06161a0103081209010b0603060d020d0c2607050f121e060f060102030a1202031003060510030b07080c04061803050f0f0606 73
    0xd81e1090b0501d80c0aa070030780030100740004081b80501c0051540901c0900095644d0b100614000c0d80a0055902e04144121103a02e0030b88801c4a03a11403c0c0e45400d0000341074441c41c003510070500d4824030410003400e41e4105001c0c0c1e1aa41c002c42030344894014004000c1000f80700103020305203c1c24070342d0361454449450182c00e850341c032240300e5000380c1d003072000540915140513005402800600340380284c0d09151245608100280c000000100c651080034400c00c2074101d1310665980c048001c1d040c45400c200c00a01285031200180c0d02c22845140080802d0781c0600c203138454455032120341070b07808a0b44030304146c1b1441c0456030f2040e14406840020865400401120200c200da6070381c0b50711950b00b9030f06000007904058450280007041d80808030001d0584d11989000342c20240a4405043c0740d4602484c5007640142450100300f14541407000744c0f00e42030240c805031040c90a210a4101104480a205a04541c030140641c4121072868401c401c021070b1542c03002034080103a031034542d104000c0c403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 294461960 1250 294460710 294460769
    0xa03080c0607021c050d0e030d1508030901080103080d0b210c0114070210110109050f01050703090201090b1c0218030705030304081e10090308010f091e1a06030907 72
    0x9909250035244840c804c034824402090003611410001610004a007025441c40c0c03c0308850111a5660301030300c41c00e4401d0b00020a00502c5000300a40ca03288201d00001c000045c1032100030000140858040c10600c095006110103040c050102a405403100d002015003418001c10003100d07018540c400e401d194403074842009100b0b42040203600d085001c0e400e001d401e01c0d00d07281040800140207080f400d20071b0203000d80754056025000902070f108600312103e0031200c001d0031000915140604460041c1d0300801440308444551000ba81c031054115082c203080d401c40070524210030300c0042c8882100409104003400250103400700c2e10b003191104d051598034480d900903030000d41d000700d03103010201c4615403010170310900c0c10043d54a04103105a544c030640d04402c1d070403800303d040400103019000200015030000c1900a00074440090b80c50504100040c019100300095074039102c5165400b444002075010300d100c0a0039240c1e4a140c0700320984c1d00c581c01ca0043c1240042c50700c0c0c0084018100b103142 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 294463210 1250 294461960 294461983
    0xc030f0114011b03020f070b0703030501090608071a120a060305010b04061a160209090106080d03051311030c130b1c05100b030708010204030308070e1e0402090f0a03080c060702 78
    0x550a46280600f18500201c001000403011482800c8089a035a0414024000105640f080300ca86030705c42440d000c2c0550700c0517009182002d1a1a0042028000010300708007201c0c15039031040804810780441c2d154501c90202503486412011040c01800074256101c981180d002da00204100c201000801042d41c6441c45008411200560b0320090340c41060300900804070f10502c642e0341000c540d4045500c502d821101c240340341c2d40d00c650810006100b444000600c81c018a003c1000f0b02d860104140380c17011403100a400a010550a43c1f02a20200044550402d008100c010031110480c0c03e00054044600b40318040c40c26042550f0650381401c41480400d98080c025014404141c4000002000011002d6070305109034000000e450b14288000e002071402580c6074801444e1090003c1e0081c0c01110f5118020041d541039601e690100107182042c034081110b0244c0d84032100c0000682400c0103580e09540005910000010451007000829190b04510207072044e1f42d46181d81643c07a1120810b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 294464460 1250 294463210 294463217
    0x230414030417034f0305070915060801030b011e05040e0d030606091a03040c030b070201050702060601090513050a150b0c0c0d080301180f020412020909030f09010c0206120c030f011401 81
    0x213030200351180c8588040c200166103255402d0540d9a807101d51600f10b580e40142019aa24884410a00108012503001d40210b081014055140d59941c00040205202e02c407200c0c84a4060300c080c0a0401d115200105002002440f566100d0f510b2652201c480040702c2000c24a80070000401900a400f00d40444245034104c001c82d184803155500300d030340006c10444450b0142417001c000680340d030a07090300442e166800040c1d140b1304148040c0c030b0198042c1009051100c00760041080313580318081440510181c0e8001701c0c2c070b42c540c05510000f4200aa40604561004c0f800c0441d9200189000d4041d240c552811503c400700d200381401004000010050110300080005001c080311185900b4131016040c1000941c1c3c2407000011400ca070841d4005644105205905000390302c1d0164206400c00c4200300994030f4042c04640306a618410300c0105810700c80c031100c1c000c095568500a40d8120314240e00700365980d2030a100e1240c8103500c2190b041065024403030022640c03126800c041040a0720684 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 294465710 1250 294464460 294464557
    0x7170d0c110705040b1807120c08010302150a020a050d050703030b0d08040510020c04060e06091e13020a03050d0509031b060d09110406081023041403041703 69
    0x30f081c40040c0900ea41003a42108038089003108080c08201c00d40c4c80f0748419910011120801405001130700c240795103c00800c00fa800061025907910024170841001c24543d5558403e10114182e0a001ca0100082c06034007806100e16051138000e0014010940300b9582081048140c0c402c001110489200c00341c4100810300c000e101c2803d0030f000c50380e14402d684c0111600742003c04006420b540840d001802500350800912005040036000d04c0e411040c6107178a00020340c6c00c3c00d8078003604c482c004d100310a401000c038206425034984403400d0024580107002d80f00b24005505018065910032483c00303000313101d82c291283d4074065400b4a00a10540144080e14044c80941c543e0003030543d0010507121400e100c401e8060319a15407007050001c1c15210044c0030074401555400007240c500940e2107074220219840c1074080c1303401c3e08a10754004c1d84081e00b0024590b00103409481c50007660002041c580c00c405180040280000c003a01120002400d04c10450117100e1f00c03940c4101c5255800c0c00a0038600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 294466960 1250 294465710 294465719
    0x1110306100918090201091d0604230c030f010f03030c170c0102180906010c020d021302070807050726030d1a0307180e03070210030507030207170d0c1107 68
    0xa0100c031140710301c1441d040040355160b00c500d402d00480710500c501010740da0400d120455820564080c018004003c41d041480d09503c44412443e40c0104407510403a60790001c090002c401c080c0310800c4505618500b42c080c90426141901a40305607849040403124000004807820b1081142c0c0989a060f958407911480300d0f03803207482c9940401c005560300e00d400e000b0509107203400d1024240070ac0e0625494654180c83c00c0c18085c9040c0b0180c002810001c10100402c056200e101c00d0b2040780ea4141d403040c6d050120362980740024000c2120040600d82c0c00144401409000034031030b4269408080b200e0b000c118604407034040c0c0c0721002c0080020341c009110402c0d5800156101415886600d1300f1030340404008000a400d1811907004900d0b01c6c004440701c1115059948a40c14a201a0100840c50701880360001400054032401d80350405440300c000481c5103100c1d80595500943c080c03015007900154450900b1150800c0a040e820a46042d140e48030f024032402604c441d61130580041c08006050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 294468210 1250 294466960 294466969
    0x9110d020903120d050f0612031b1009200d0b070e0f0909030c060109021305060304060b0d03031a0a0e2e0608041506080309060c0c0d03020c0f010201110306 69
    0x3051859414002c040307041c00090f00c60310080c0305410041030001541c0c90210b6144801e49009000b603401255040c1e60301c2680c440000c1106c000e0010501c1540101c42e404210034905622140a0a42c0712304128110303003001103109000c8440c0d0301c85800d030240541480300f032108550007284013401013000350002c9916280101400d04800d20042c0002504d00e45020218802c94800d40b11a130346a41300040c600d400840510029001d400e2003c015440c20000e00c0754104010214000d030b5100c0c6000101140401c01982d101c040e000101400c158400760903030501900500c20110100790002d450781c0c212010b0300d803001e2600705980385c60b0114005030f00e0b20010200b808440c50300440003841d20107081400d4030341f0b1048c0c1d6001400b403076850718040d15061401407111030079240003c6000742040028011440c0100940f11a000251040c984816500c00c400e80f425401520307071a08000002595024180e0115141e602c500007500c0419005145c2c000483c221508460f0100390b0203001d0012540c3d9140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 294469460 1250 294468210 294468217
    0x130b060f0702030a20010207060203040308071209170c01030b010825050c01140601020c1537030501090b1804110102070e070203030105010f03020a051e0f04060305040c09110d02 78
    0x9803c0340c194080d00d58403078448240e05c082c58607003803200e403010100540c0d0410680020b0043c601c061802e1519650f5081500d0280d02d500a011100034074000342d40d9485200c05000a08a00d0480803c2624800c0d40e42e40350741100c0c00082c0080e051811035071103540601d10660050304241c503406841d062084044e00300001142c010810441d081000d0020b044007402801c28118080c20041c26509041c000640b5180e261094a40201245484c0c0c1901150341c00a440880e084807252010002c8180e840c101c40652240168076006504181078100c142d255003c1d82c161102003608004c80e00448040005011406441d52030b2a04900c00203400500000c440d6441e440d0180100c41100e03031aa0005200e60304119a038000691010004001d5581d002109000c2d84649080440c60007134021802010340c841d019485031081c001e415a0a2624001d00455006180703905006485649501008010748001d807810f0358944126180400c81880e24070590720344400f120078861400b250350425401a41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 294470710 1250 294469460 294469463
    0x20102192303090a091407080403020703020901031a010501030219120b0405070206040b060103093f09090b030304140d060207061a0316050a2310020c130b060f07 71
    0xc4031035503046109280071901400301450030000d5a01c8401103410300098080300c2e4002c01d25142040d003041070000e024020b50b81c0002e0716150848003079031241016440c0a000380d03c001d40001d8081300000c203204500c4903904441405e000c0000c1d459989000440070780c02030724141e01110003001c00e0405007900400306184030038509000407401d03603803041c000b40440d80205c40301d1015811030342c00c00013004990410258810000d0a080288504540300c054015400000030380c03a85003411f01c14070903c05207007032a01c504c0694a144264445c4264801000700402e44210160742d0b082c1100e2281d903103070100c161001c0d1840d42c006220f49203000810841c014045d800140c4030b041e8200300305004500c040c045d000c1803c1c240820b080140d1040c405040c0380c0044400c0350043d100c2d041c5806c4c002aa0f81000d06012203160172907d07001481c101800ca41d08c100345110703099105100003c2e08a500740c01203503600c580541107d409070382d1001d03034010340103442030503c00503031150041100903048140359020f0200380e07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 294471960 1250 294470710 294470723
    0x2030417100603050102091302040b0406080c1b0106050109051e0904140102040306060e0c09090612030d1a1206010f180605090a0e060a092409020a1707060305010302010219 76
    0x1c00a8210480032200710740c0040e00c941e500000c1e0702015048c8000c41411404007010f04620786458103180d1081401507002c0ca01c104411400880e0b9517184c8407058400c110101904000c1000c000381a140c000c18940c4a2035012414903000040c03180303402c4043d52000d0106011089660407894100045403d0050080b40d09075802c40050350f8808092025001540c40381200060050508050b049008801450201512003c022040c0d25407102402c29401900542e40d00400d000818091421030048007000061070380b070028055051565110003010f080c0e42a0f95003114049e002000940320003090040300404010210f0070041840e411003491010092000c0004126031500e00003640d0303201c26500345280603195100c0d981059030501c04160422000c03c410071400d0200d0742d4000200d0f012126800c4644901c2e5403103021620360307400400d0a1507004003080704140d1a40014095001c2c085c003042c81c076101d50324000c5003050007449040e050303940580040143c0c0d6112030789040a41800b20701140d00c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 294473210 1250 294471960 294471973
    0xb0601020a120201140105100f030c050c0d0507020f0303041211210a0309080304050a0504110f160302010506030c010c0f061b0306171b09130510060503010c0c0302030417 75
    0x4514040020b15151040da4004140c440001412003070240068102e6171141c80010300380d01c4480d0b04041e40c250428400c5c03d01088100d04458107403250700681e002200d80b0b0052982a000382036020008004092084a04a80c0110f08005050381c9000d01d0094240203000c007000200414404c030f0b107a464900004003000340600344001003001d11420107204a0544d13215948000806130030460031401781c10281c0c01141050300c1c0c5070000340448254031030b280c0103956a004802d00d0564500865041c0c2240c2c10080d90b40301d9400301c0c41021842d1034241680154600800f0071140d00c0c0100d030b0056140c0701650349044059103500d0300b0342c59512040341129410f5480340740620001580c5181d481c07060083c1c40014034286007022244803590810f00707044868120b40060380902c070b4000042c04255506540c2c0e0002a5204100078030391300e01c101d40c0600f140c0318070340303003110090201c4c1c014034180c91050340244a2411184800d4402568080001b409604140001d02c07000c06840340540480c048801200e02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 294474460 1250 294473210 294473213
    0x103150e010c030509210418060806040c0e090a030c0305090f0406181116080702180c1306080f040212010b090a0606020105010f0f0e0a0f020c100b06090d0b0601020a 73
    0x848100502d2200401e848100708004000140408414a0503034050751201c03404203044550b5500c218024002c901d00322210800010035a41d01400c0904412000c88000f0304003824013a031500d0b418810700401c100300d0700004d11500d41c00308000c800150b040d00d481ca01060280d4042c2c40702d4002c07014082c2c215103450031b01e0f06265160b000d1440180f03020740050301094020f4240f0800d44202124515030300100300409585031864400c00c01c074103070300b0520942d100c20130707880001d22852000c1510a10580c408083c480d409556100600801066024114000c1d0340d4034015501c0650444020611403410f0340050090b05050044031480c1d82d12900001d20310440c1c100282c000785059030521585a0340d60000c1c0b015580921486014008041401d0882864035101d14600c0901d402100e22421107840880c7d220011900310340f2132184018004d5482d910700c8140c2d5940c0305040000e404d40107052180749146800c0140450720203100c0609001300c80225910747c22051100a80624110b1050025400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 294475710 1250 294474460 294474463
    0x80d050403050910030b0f1801291b0706030c021b060d060303021e07080303070c0c0b030711152a04051203210c070b06030c060c0a03170c030103150e 66
    0x40140380709845c00100b402c0040240400c048520b0364841c01250301c01400c060b191510700115044600d6150002e9901d21441440b450344130f1031004511404c94041048550080f03852400f2581c001420b040f02c01c0740b6515a0200c0a40c2e0255a881000d0303004000b407182110752003c02c40850242c0500000d01e461100401c041c1200da043d842a001a00030084440c00e1201011500000020318001080d0140c00c0812440c4c0ba0f00c0b003d04418184000c60144104102401c0d6040b001880a00c1141c0e0711f910b402d45010b40054070300881c410030750281e5402c00c044483c184040c0340c040c2d00b810450020500303040502c407a00340030020740c40c072880c2428800010f80350b440c10811f001280d5004050354a90180100003800c015860009079800c003a05001c10207980303200ba00b40d8142c1904503229070050b49402c030110b41080c0004202c0d507000760340002c007410092000204c443c0030503c00c0c1c1d900046c00d000e419800c1070f41c03c82981d0104d4844410001000415a1a1611100a95100030024034085020000c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 294476960 1250 294475710 294475729
    0x120c03040204060506191805010f0c0507120f03021e030a05180301091a0106080c07030e01031503080322020f1203120109050f01080109033006090506030c01020a080d0504030509 78
    0x42982c6c044505001702c01944400b9a400b0704201c050707582c062900304030019210800307400b1418100005034540308240705040007100000e1291602216402500d81860760a0b0509010190058860524152107280070b600540c0c030802d410801840c10140308807012620fa600c00f111400d40300d01301d81c0032814259003e1158140e03807031141548041481c0b004241c440742c001d0507030103802031000040c20802c1210900044484544e410700e04241420300c0500182e0081074030040b00040c030740e903c03480441040b01d40f0004500901c3c180c401e1020403042101d10308504881e45400941106051013044a40d06202c4036112224050109507414000348085209124500b64820342072035854100b400000a4048121405000860000d1088007141e03100900021204051000c0c41102001500800000f00c05006e040141c00d07c8240b00d5240c3c0c500c0080082e100c113a4441e886400340c081e01840035800015402040c80c0e01c401c405003483c0003940b206004040082c070540c01c4c0728040100c0245646e404068 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 294478210 1250 294476960 294476977
    0xe010f050402040c090b12060d0f05010e011b050d0504050f0303240105180d0302011e02040302041103010807030611190f030609020310030b040204110703090e0c120c03040204060506 80
    0x103080c50a03004000c10365458005490078004584001d00144025400722000390480c00580c40c1c1940310500400c2d00720a0900006e01543d400240e03542c20080c040d0003001c1e440060100a2101e003080c5a04001c46025200100022030010401e03e2240e00b090381007282d203d4000d400b034440392041400e0050075a0307c01c850700030a05800301d0104280c42c4904445c0100d4580a1920b5410000030608000c510040c0c2c110141c400c1c04142130107400c06101750800c4610412410010a10b0200102440301075045404202d1085082c00714180810b00c0b98400c0c0e80c1280e1403080107100340391842c1c560f0001800c0700405c8981c655401c1120121502100030f41c410100107a0350b807076100211290300182101e610341c006400e428010401c0c020700390340702c4c061a800d49400c00282122a1074510000703004044640c0180314914010448100780754100300d20301c0c101e408000d2104000d03581c0c0d420120b4940f080d504010b003100d500d0b8001c2509400d00d800619030003440640006420b40c0c540d8000381140d00400070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 294479460 1250 294478210 294478241
    0x200304080a050a1202060f06220c050405090901020309030306090405190c060216240c2102060106020d02100e0c1e031608060606030c1c0219050a0c020f040e01 70
    0x220f03504000e010040c0c840c0d0913540c0e00c0a0941c81c244041580c0041d080680350900c1005e0000f00d8852071441c0c040f0780c0400144580c0100001c180d803c001405581040c80341510400340000084e40040c418000c5902c00d4190307201862071603070382c00100039104002500c03d82d503a00c590784500300c40b43c480040014600d40030f040650340d401e2820078001c1c0b90051200504c84003002415081050a001a50740071210100c10100408240200c804503140b866450300980b10f4001c908528241c8420100480080d0f80c0d20f50a8504580e201d03c01641c0e01c0303807120281c0c4016406644001400e541c07d5200300c100413249020b840458080c000020307188440000c1241764a80075800155561408000c07a00d0391030b02c3d10301002d075201d00d00745895484003070080001d40100350000018140744004011510311801c00c0e40c0300b40300d21801c03d10440094100345a10010600a440040c034054003580c10b8401c110390a5641c6072800c01c43d6400d02000c15170a440c815000360b1203402030601c1100a004000c090f2040c02c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 294480710 1250 294479460 294479473
    0x10306200d050a06050414010b0c030f041706092a1807020d021c0203071b080709060305060106030911210a0f0c06050324030a0f0317010503010c200304080a05 70
    0x3c52004542030340e84954131652810011507015000d841c0402d0454801c4883d1a494184080e078960542c80307584860081700700c0009000c100d07103d00200c29041000700c0c0044031001c3e0740e0501d04940d1104414550080d240d10640e1a4040c50240794101508440c007504042000200b45031b12425a1010381d940340c0540c00c05d050300700030280c0c10000542c00103c03041840041c00d41401003e0b46900c9081d074042c1507110f0000403c1c80c89038844451000420b9200201c1d144c1598942850300200040d010071109401510b0001400601c2401407450340754100c40011b880d4040001000402104a248040001a0484100d41c4050180301c0d1529031070040003015030250141c900460b01544a421403c1803050510030b00411100d81c0410072407003803c80d054850904804000285402c0a01100904442a40140380c04165100d901080e840000e9942c400043c1d80768010107007600d900c95000030000e1025001d201000c81d01c0e8055414025042041d0380c68152610f0700b0509100007041c00b40c2e466409007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 294481960 1250 294480710 294480721
    0x528080a020a0b04230d1d0d020307030308070212031b16061b030f020a0e150f0301030c08101a040b01090b071110020327030115090f14040b010306200d05 68
    0x1d200b60105c2c0742c4190140010041c500400b4000544004035842c151801003407410140e06c2d1081d04c0480c03160020125054103a072071400400c003d00032242c01c0014056074a801010386098811f490048203501e07850010300031010300c60400790b00024038614004003000307040c0f0081911440744981074440301e5030304c1c20034110108028040c0c5401075102081d61f481000351120351580540448171124080340c5103588180300168085850003080c45500c1c00c0301d00000000100242c0344d4003281101c00d84d1090b940740c24641c8910390304440501e4010100e8a9001700c9a4040c0c1c03400381d100b012007990505041c03074100e4507004c4811454200c180c080785c00c1d0242644040003840c0007000b440c04400c10380b004525084c5a041e0804c98000940038210300c0058017000303d00310356005c1d0011000c081c0c0c1c088a907070b0320540d070b00e0841e80503000044a09116500d004400e001d8415101500c07440b40e07401858504140c2d18640e2030304001c02001d940811080e00140c4000c940c1c0000314020001825040d00104480c00d01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 294483210 1250 294481960 294482003
    0x1081e0109150e01050d0b07090305100b01080c030915070504090e03030103061404080906030411100c0201120c0e090702120a031a0406050315070e0315040528080a020a0b04 76
    0x2c5400c44500c07400d0102c010040c0ea50f45000e4464003d620400303a000b0b03034031602e9055848800715000241180900401182020196440508009000d90b100c5106490341c14040c8424881a030342d684060300a00344100d80c685240c044180c0043c99460b00764a025603881c0100c044905602d010301d02034000000405c144210f500072481845022100745803942015541c0500d207220308034115000f04000b000107401d1000325019814203002c05001c462880020301030040035015910001c90100d5a0345205a040d40203d200d0140c00c400c0c291070f1007001c8030750042003000c5020014410403c512075003486441354401a009040c0901107510086502c3c00301e040d0291103d23050042160049142a10400c92641e0000700d101c0304407a030b2000d42c909510b9011084450440c00d032500c5070540710300314070401040c90940d0310502c1035007d00161941c10103128003049402e44040345410f0000140440140031420030f000505181c0c0960040301d404039090358401000003000ca038160792083c4280e10707101e40081e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 294484460 1250 294483210 294483251
    0x150c030908070b0d0e011b0f0306030b0a020306090106050906071e0501061d06012d1107120b0a090c0513020d1104080d0207050105040603020c031b030c1905070501081e0109 76
    0x107014009010034001d01110244142c87c0d0300314101040f222891101c6070b1402035000304055508852a24920b2408542c41c1c8044d520640b081c50040c0380480001a286218400391294504000d004500d400e20903142c00152034070962008001d0440079038004001407007445001c0003030200c03040c0c45401c1c00c5076007064140c9080007840c2c43d05001082c104e0306121084003441174a03003135490404070003036040e140d001ca440a0000100042500c40c4200c00314125007001003002c40c5c0d6108006a9402d55941c040c018240c641580b402003011000b05c10920191078440c01c0c1a00661900740014148628041c4913026240d0440050b2126800020180010712007804180104a2680001d040303042c40e003800284030348114400d200c1050ba001c50100640d84040c001c5450a0b443c0d280d2400300c004508900345e4480c0e03c20b260101c450721520042303050a1030442584a080d58001010346245450003006540000b4020300d108468698502d000c0c10440c81401c6087c003801440c44000b0b40e6010000400361800c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 294485710 1250 294484460 294484481
    0x9041b0f050102030417010e15090115030f0f0f0f0308070905010305091f0204080f01151d010b0d060806042102030c060406091a0f04060b0a150c030908070b0d 70
    0x200d0240140090b980000032542252822030300c4800103103540401e1401068280c4450b80700e8090015801441c035580c00455010f090518000c200701107128074000da404c5041c4c0300080c20b803859079041101041c40800b043c0c2800d40541d10101d80303042c8a0f82c80407000d150356a0300301c0101c2d5a402c04e02440c2544900d4a00c0600000c1c00e080009091851803190344a02140c040d9050341e02c8100a1b00309014290143e0b0002c2c94000c044072190182c581500c0c2c0608075210285101404401c800a00150f800043e0b00d12580340d8682410a81d01f403100c00903080d40007242c006981c0d9100c030700005802c2010001e1030f1040d03001d805107032143c0080041c0418404024403000045600901001d08148004a46103400560007000051048054170388003d207404510700724111410170b442008040b0700c042c16440e201e1441200304100320840c0c00c1c02c22080c00f070503001d82e0924108400307818007040d01900381d00703008600032306044001c180d0381c40c5480d151640340c0d017000b0925030f408121103d01700300a024040c01d08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 294486960 1250 294485710 294485729
    0xf0907090f2309130f14030a0207141f0e0604051206070206070f0912051513060f15050f0301090606060215060a05032d0102130e0f0f150a0509041b 65
    0x1814403a460310b400c1c141018018112085e1030120908000000c5803001710b4181120030b80e5103c01c8603540284d10380995100e41c0301d503000312030307159103080c0b5061490010b05100c5a080000070700304803000b02d6048440c54111500301608010228599403500451200c070649107004007101c0c40c00d148000c1c00d240f8041c1007c070500c1320540049101d1904502c000d000d0341e60a83c10740c4190011420224580420341449040a0600d00c091003032001c0000d4104400502818080c411401c0e9071811404841590100c00421f40c1c850b002840989007450305218000001400450b0550583c0c4819044500990266015902c1680d00c000958003600c011136001c80116080000355181001085c0c58036010090408007200803a0035070045800b071004081035210320341c021520340c40031442d00700303c0c041c0c5802281e200c0409280050542038140075214800c0500246012194603440c002400e008203040e200d07517128403110700109640d02c0700fa19003845140140011414903059070f00a00340e01c0056086440d14 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 294488210 1250 294486960 294486979
    0x40803160522181a0d020402090a09200c03040510020f12091206010b1803030d0501060905150c07090209030703350c0a1e080d0606030513020f0907090f23 68
    0x10013040c00c1094030240000e81d05000d000b075203440002d0080c400c81c1d5480e0340c80038800a001c51951000c2c0d21641500c02c800c41807038907402c0d03210300074811400b842040081075442007105001034181100094548101401154603025809800130708210a090421200d0100032920808501c3c1c18a00da520ba60501d0018100c00d50402e0b04941040c491402c019000c545000c250410300d450810445a410306800420000b0756110071005003401518450b0030320480c0b0b41104148801540400c8540001c1018014207089103402c1591001e900105140c60b458055440c0001c0411f1920740d000d003d4420840300546849561034018110081d010080c4919000c1400b176903511800001e4040c20503601301290327507118001560002e40ca481c400000404a0368085142d0402004540008042d107800e600d007803220342d480303092a2014050582004e0342c001000028000d050504508a0740c02030401d04e0980007403500d6080b50340021110368040110f0080c0850780d007890b0300b500880300d0301003281110000c61 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 294489460 1250 294488210 294488231
    0x1a0102160b12060607140307050105060f0d0b04020112020d02030907080102030105010c0809150a03090203010e06060310050408090a080a0606080a11192d050904080316052218 77
    0x820b02071071128107164800300c0302080d00340d502c00e81580d560a6001ca04041300c100141495610380d044140c040701c8030340c01d01c00032641c24501b002410719904000741224001c2d08031a2610706440740f01030000d0707042c454551014a00200c09000819100140010259480c00e0410105260a0785580300240e141d1050005000030307a800110b03258865000714802da218951a8006400c24040001d0641d140a00184486c3c0e11901034200d119038a008800030030010b2090013005450300b6003200c030554150414803a0b030004003000d521403130b002030080443c5402d00000d0f8000c900312103050f401040e46644480040010003483c0d00030030000c0c00024024012039000c81d6141c551f00e40390000340d5445000c20500941d03055050500000092261100660103012031200786c580c0d4a5242903055000000c901c408078150030107000c00c03401154800744051455840403201590103400700543c4c400c21101300405c80401c810000d01065080c40ea00c040c10302d4518101c0d83c40c3c41081d00031010601141080000d09 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 294490710 1250 294489460 294489479
    0x6030e0c330f0715180302060106050c190305071407270b220e19021917060f090d0e040e0307140a0303230103030e0a091a010216 57
    0x5540368140d008100420400c152054034002e102c00640c0003100480c43c00d00b80b011042c0d80b83c4e40c01069020400c8850701102240325940040e00340038002d03900407001041442d11840040038031003002da0a0f68201c02201c040c1c4042810401c0059001410110310701d820300000032100c210000492008001152038070f00301c00340103440340441074409071200120740083c48840e049200041d130000c00131501d524220440341802026182007950b483d2130b1504200d20001c0c0000e1650143c0c1c0609401c4c1400701d000da003000401030002104050050725018001881e05a8810310000f8903089004ac048a00c1c117650644000d4100400c003906a60241c0003015001d90012501002e1902c1a2400f00d040c5150002e402d10718464050000c01d035000d0302905103a01340d40072880540c9184259024043c0e00d0300100c0c1c1003200300d60420101440703a445401080028094095011a413001030f0181c1c80c2d8680ea008a901101e10b00b080810440481c0013080469690610012092890040418501e603040201c0f50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 294491960 1250 294490710 294490759
    0x706081006141b0f0d1803020a030213060503070b07031803231f02040302040e0705090f0411040f0b0906060f12090c0d0c03030f05180d060b0a06030e0c 67
    0x14081010b00203072900e403160095038104224112582140c0780e10907035088655550f91084828030000b0b00b038400f1051202c21a030903010840c1d40081c01d101180341160200082503907030000305d100341603840c070300010300d510309004040c0140f050b60512500d0b902d541c10054260300317881192030030b11040e4000c01d100141000700c2d6800000c003201507140c038030301060708145e1070040e14a02c40d4085402400001203420103d40082054034800c0c0d400f0b0000400483c5070b2a503c0003a400344035403110314140024840204e0b020f139a07a015008045d036841e5101c8605c0403a01711101c24036246855078540361007072046c1c100700031043d0300410180c400c5440c0003a41c20101c0143d00a20b08510300030b400b12000700720050005c2040d02c504250003028034400400d04c3c508040c002d43d0502c4203d0104d040000165074150090064030b40328012a00d140906440f08002c10406284c0e500e801c4484580e1303044d070301d42c46c0d03107948038904042c3c805a200000c40010303071007070346240400b803504840c4034800500844200b0041c08002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 294493210 1250 294491960 294491987
    0x80a09030518010c050f0c030f060906060d060b060a091409040203030a0513170102030702100605031902040f0504060b04060b0304110d0213050c2701080115030209040501080706081006 81
    0x2000c0100c2e014400403208085a91360140071071040304074111200c50040f400b40c02d4028110304803400021003d0116454081c11588484160070400008007107050584040b0307885407043c40300007801800c40000035040d400c26034842d000241030460a0000e01e000c44d041064008d012194460303641b500c1d0340000d41e0380c49039001c5a01088800700e0101c940900c03041c1e91a021b416200c4440362050b520580030340c004e40046901034014401c0300ea0403614542e42d48100003e83e000680506800900e003c80c403100707035240c100b00301d8020f03645002c2c61100c00c90902c6191700480c4614404038100000741d003003100351001e40d00a0000f9400820520001540c42c40110044500986410300c12038524000600d00e0300311600d0549020741000c041021240c1c3d8035000304180c2c10080e000c280101100900d80210400901e078250225044500610a02400c1c0005002641c4940b4026141c803111802080a40d403081e8000809544841c03014040541c103d40130036800400205441c901e079107007020050100d03000c0020b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 294494460 1250 294493210 294493237
    0x3060503210c01020d060905040516030807021014070501290108010e071119170f0a0e030f01020f04030524040623160816170a090b040b0106080a090305 67
    0x10380044640b004e4043c3d844030348212404110f4241e46604200240c101150304480034020840c890940d1110880707810103894100f040c1900703180880d400d002020801041c0030341400302c4100181c0b40848084028410b5612070000403442c1d054404110000304d03280c40c110089240c6010f001407090340c0c49151030f811140751104200381500c0b107110a48512203103010b54035041c0648544242a0040c07030580418151041d044524040f05900000b100e03401800621841c1074810000b801c0014460264070a075400024166003204044881070f50882c1c0c024452407190040200b8200180302060043c0385151540d462103076200400f65104984080740180024030349541c642c140030f43c282c42401140b0440003809480f13005410052015094a070202c22045c000580100c00038a010f03e00890710b8084100d1510360129038038101a48040009006003e003041c01c0d624103004001c20400300c8001e00031030181c1220321065060000c020081d140042c10654070b6401d20840900007540803040707036030103a490382 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 294495710 1250 294494460 294494467
    0x50a030906020903070e10090204030312090c080709090b010b09030a0f03020102071b0e0a09020f040c0c020904030f1b0209070e010309051b01030c030b0d0b0709030804150306050321 80
    0x54403000030b002c0d20203065090712901c440882d4040708803030040c0c00b40c1f030f2800d00748550f103035103050340c10a91095000080001d8511151039129924a400c612507051103100c08091140d01e45022901d0301d14070b42d028003c07440d10b440c282410700007035a181d1070140080300070706032411440b00d001c01c0d03440071807031001032a080c80340004c04241031003941552001d90b0701100100d030f200441c00b1803c094121600440c440202c510780030030764100c0b481c0705a52a441d409045c01462000c0e40381040005c0c0f1000000c00240080403496400583e0780342c01180c403c520030b40f1032a04800d0348000090102040158210700c012910740c4084c05071ba2070091007940903c00d03141082c0d43d1660100100c000c0e282c45100105244038142d04901d440b500c0b610f212000d0305003a6420003070a02410011815551499019604540940d40d00c0b400f01d80305140550340580c86040401900f81e80781c0c3d8010095000b41c1c8040340d40b5404042400141d0f0f8180900b500901c000c80040040112204500720210640d51111500e80c6000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 294496960 1250 294495710 294495713
    0x18190902090723030406060f0801090f06050709090e03030907080703030c1209091503020405130819030e030309070f061e08070221131707090f0f1a1e01050a0309 71
    0x3c0c119070710351070441c84503441e8181440c5c820060b1400740039100010482c5500411039290500c05c480d11720703410007050480800342c0d80b01c0c5001040054556020443c090700c0106100220f0b000300e5440341c5140c80210380d41d14144110900707151a0b80c1216800783c100780c0302040071a5215003544265900040f03c8000c03401d11200c16a0f2001495202c101d40c0340c244820160111031442c0c015045a00aa40038000d44d80c1c0c05010f009000a0070303900820b01c4005000d94800703d040f411850300d401d08603050000d00f44101015603441e50b0800c458418065202504c148040702054269100030718460801f090343c1c2b50a442d4448c034100380d0b031081c9001c00c0262800151920f10030096524502c10400391045520401880341c241907001142808410024100000304bd140340065210014141c502901610741000c90040103030013182c40041c4110b80341c005101c0e440880c0d100b0900710001102140110581120031300005003280410008854440e01601c0c05a0360000111080c0348100e144c00141c10394035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 294498210 1250 294496960 294496997
    0x20c100f0b3102030c1804060b300408040905060a0506040611070b0909130f06110d0f0603020906010e01090807060e0315011d040809181909020907 65
    0x1110701a6000800355019030010b031142c4448450001020000d000e11016241900240e220a49001010b0b9400308a113090442d10082c28119a92000300045012a1307910342d4a01160080500c080d2240121070070310610ba1440141001d890f000001740314405e1a054450400900903485555249921500050030503500c205808000d0f01008017819203a58440300000c044129281640b2058032580e880400c594805000b41c801662000780890714a9a40c82500c200340403a0b4801194080090031402e80010f880c0d0041c0e05911130204007540c1c0341d20500d000788040c2c4181c0308803071080514000c410302c00340c0c48254070310340e02190a0070031100401d03580c80102e078040280d034803c41907400f03031032004a0030303a502440c0081140411001c96580c000c0300038400140c030034280b007050b4040c188001803051940c00704241c2d0760b005020b04800c0381010017820103e5450000800e4002406450f80d0030811580341c03051414540c3c0300640c00c02c0000140030b43c003050030243d0140000041c460f1105035100d80c2040d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 294499460 1250 294498210 294498221
    0x70602070203010507031a0d0203072d0b0304060b0f10030c0521060909151b0403051507030501090b060d0509030912150c03090a02010e010e10110c04020c100f 70
    0x10701500030001032400d25401401041c1d9040507a04d03401b0b14a410710301902e0410007003a842600140580b2046103014008503c40c1c500c3c00c0420304203d241084041b00080d203d140343d0040010a8225a4070f180515003002211103280070325104003101140180e1a8036440e4180b030122201e41030001c1c0c0c041a4035000d407081d005500344c00300b507a41d4140c80c401c1120000400c2c64001c0b4025280714450380c941e002d0098032031003c00500c15004101d00000750604a413882d44074810012488914a07103a00c0c0d84806003815140058000b601c0c51120502400c1340d450311a06004010b40b410401c0007a0715000010014440c0c500882c007038944030008100800001c2c0200c1e84501402400c643c00800301d613542d90b40300c840c800c1c0a01d00c44480d90001030825640c070740071607110300780c1c0c0000703407064400035030054540d188000ea0300c604004007400b170806182c64170518101c0c0350a0b184c56102000c000b8012203480e1815160400307002c0d074010301144242c90300008114065040482e0046040d108440c600c400504 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 294500710 1250 294499460 294499463
    0x3f0503090d080c0c0301091218120503130902090a0501053f0703060f120507090e0a050c0607030906110a12050a080f01050906280b0a0810180207060207 67
    0x2501141000000b600410410351600c06551403c081c0e00308050032500c484002a080c401841c03880440341d0700c81d034418410007003420003051002da16151580700000000200300c0c1c10344d10015585011040358140031005000201d41946003a2a6801091102807140b25040c1440b1021480020551150403c407080100d42a04001081481e031410b449540340054240090525680840e0290f0301c240102d0b02928000790070022410f2a045546a48402c0d10350107481902503800086640103880c002c0c07a4030300ea1041c00411710a421814102c0c11711542468891190f0802c001010020b604004807104441b8281020520302008a54290030f215901c4001001004807004802207141c100c4080c1c01d0489aa40e1880b50960b0342124915003400300f0302609034401c401c4000541c0b00d01e0071703101007600b6103c4880307a507000001041c0c180001202da500b204c96031150101d000030155038803174102603201c010083c4411703201b0f03d0030010100b90709021150b608211b40010301030040c4801034040b00d040310b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 294501960 1250 294500710 294500719
    0x1a0d1d0f0a051e0a060e03121b0307050706020c070303020d1412060904030908010f0203100905060d110310140601020d1b060f09080d15080706080606070212030a08013f050309 77
    0x4002c06d0107560784a03801800d038921081c08103000b080c421140c00c0001d80807030313258800c081d1039a1035039207040d166a04407000881e50290200061030400c0b009029000045101c0d80007040400c0c85010082d103425039010130a00224800d00807074900b040c0420340e20b504410103560040c2c3d50780b02ca0400b1942c00125401090b01d40d8244000700704003a4469000314410b40340c1d0010442e481c0d48845070b040603560103880f40381e484036001e80c511010034a0240c001c00d401800500b215030744100b0104400950b503641c00d00340d008250960406c14156014804036102520600d001c0b076000445426101000c1420280640000ea55503c20141c00c5403590020f01d6850304100034540314010154200c0c09062011103100d41007064100000d20502d002540c802a02e029458205469641c4000d114181d008038038283c0e0322102c404103e43d0880303010300051050104a5a4050207076040c400c1399180c0172080e5850b051b2482c03880c500c0203845240002110300480340019241900c3c1d0450030700f685907014402000340e11 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 294503210 1250 294501960 294501971
    0x150c070e070c0c0e0711030705060a0c090b090922050105150a0509010b0309100e030315011b02040e070308070b040c050d080a0c0c0e0a021c02131a0d1d0f0a051e0a06 73
    0x9c1c4480060303014415011902c040c060701480000480d01907059110301004040c003404411500e24103100e510358442c0380040305c400350014000d486240d40500c3d410540f101e0b5903800901c82d903e1001c421054402c0380a07030700800c401c0c0c54800030880c5a2014440c040d4245404004910071400511000c0890740264105000401420440b580c403540140d0340000e0144203030381481010b500503441414180034141a11552043c80e07001c0c00013501110708252010b020b04807002c0300251107038000d4804503011b841e0505445c5094035181e20814031540020b445020241c040c040001d6004049882c81a518584151400300394507010180489a8108480e0b2400300000c201264066602400d100d01c4c06000490b2200026012901288940e41304ca004005a0520030300110000b81078150b03040e071014404505c0d02030b505a040045601c2c0c08034808041203100600c2e011240200920300b003c1004c8005041c404a0558800e5640d403020007940900603140c00200703c120400380481d914090b0440700a020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 294504460 1250 294503210 294503213
    0xb07110a0f0510080f011203050408070608060112050405060103030e060702040608060a11090f0613120b06100206161b2a0609060906030506150c070e070c0c0e07110307 74
    0x20425000e00071280035014107428400074910440d4054040c161007a600d66151f401c01e081c1d0020307901d00c41825005d100c8100030000300307240304021450042a540c2d41d002414242074000500300c0c00c1a041c0c403400542860140320102d0800700c0d0107411a80d160600b800e80d4122400030500078014844040c0d401803600500240c000004113105129100d004030402c40105220800725850140d2244190001c904a402982d1400d1840061048030b1b0310918420207035540c0d5103840403000d064081260f16810200904c101410603080f041c540b03445034000b61210b49400da03041d000208803412010300b044003100300d502541c0220900c0040007a00102254009403041440c401141078030b045402c100c50a088001902c288904883c4040d00ca076552003034030291402204801502c0c01802065002211000295180781c1d014001d10300d040024002e000e5107403070200b54a41100004203400144498101c05d0030008110080003000e0324000814509642c80e22401140d005200818060300e51100207123000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 294505710 1250 294504460 294504479
    0xa180f050c01030f0e0c1c080a02010b1503011503050c04080a0f02030c0d03090e0705190f08070302130314100c050c010b0a0303140306031f0609050c03100b07110a 72
    0xc0c81c22003030324107010070200c104c0c503e4221001c083d100e6030345400c020743d040180e290078240050001000140e603003a50641e40c85540300c90740180441c0300941c1d076640c140301003401c10700041c840d66005000d2071821585003070741d0410f494201c00700c0c1c001019035071400596a4810142900d001e0441c980450f2100d010b50301e0018aca0310002d81040c0c1c403c2c0710300c4501090318904400410041940743d40d41c00c210034030b000040b80c42107402504843c28083c046c0b00c0030340b0742c4009d103485101044003076444000c0d4100301800505001005401e42c0e0030140100145c102802031140c2c00c0c021603a00a444800c901d00b01000d00d403c101000708419041030070102946411540507020b00034607140b41c0d001700401c801400c10011420964803000b00400c911495118906e0b06000245905c110007400307a0700224246526044038102e0502c441d00700ca60703948410300c0300380c03c603111b65940840002815403035800c142c03858103039803041413181c0400d10600045203000c11032140f131381070000c11002e4600b07280c2d51740703a0060740c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 294506960 1250 294505710 294505723
    0x72a15020a140c010b04050a02040b04050111102c0c031c03020405060f031006020105070806090405160608150402041d07090902040305010501061b022b0b011e0506070302060a180f05 80
    0xa1b881075003886c0101d41411424800c403821680f000d0680c0e46000e25000041d145410b02080c1030240340549003c1c14001d031180d0140303909480c4000701c1d2078000c1c503810074202e80c0608088140207441d48500c28800041c1c40005800301c0d40c1030340e0b094903401c8400f0302c28120081d01c160b40055400500201d600b2003588010310103180a0a0744040d010010b6881e4030b0101e00b280d108841c2074000845480c003049113401d12625454116024a0030744030f0801d170401420079400403a91000c1d00007000f0b5820081812100e5000c0e0400540c1150b080d4030b000c0c030b880e511060b6140c8504614002d15961400300e2000340c020f040035002005848001e644850340d07424001d0007080c0900c00c09000c200d9550f10b558050321043c1680d03030015401001d1440c0c8000585c65842001702d0b5065400f001c0d0b00050503003010aa076846c0302402402990641310002f00c01300d2805100000c42d43c4414080c8000b030104400082d0085401c1ea03000020700b0380010210b409840440d81c2891505014180d0b80e00202114180207011908 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 294508210 1250 294506960 294506981
    0x13080d05010501230406140702120a1e080306060c030909010810140c0720040e0303091b0303040e0a09120302181203040501080405010212072a15020a140c01 69
    0x4072941030340e4074130300c2c0c0340c036088080500b0301c1e91103040200b40b000c1402a01c1e011614041040158200302145d4007050402000e00c9501c9016030290840c0070800064040f012000076403130302e07103807030440d43c0b552084410f000103086180f00710700104040d214001c0800c141c032420f0400520032115941d48071041c6456581001103c490744c0e06040145070840c8200d000a4080c0039540c1c0d84030300e03040d0151200c1c41a5000d40000e0515014041203c52a9503a1800703040b0818440c01c0c09140d81c3d0500030107551500b041c0b100301c100b00d00022174900403695400310a4a044540ca40034045241e6542d60006005103240c042c01400d108030a0a800307000c5074140e02034000c5150016440700e03100440420003e9510031640c000d039040d40b040000b80659440382d00c4441d0480d126400243c201100c4815441e800038040340e001001a401d0b10904180b4480700124108030700000c02060111549910384245a00569900302c05241d00000d081207403522540034940c4400088440a40359001d004440f406005031118 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 294509460 1250 294508210 294508217
    0x403030801090b0109180e012d050105180907150306141f03181a190c020303011202030a050106090c021e0d21060603020304020405160c03050313080d05010501 70
    0x20688002070f00c100e00c507031241612000c400c1d070b25024190400d04168101c03e50400d845114040a040b024052581d40059180c1480100004c815410768001400848013020b281010b00400441d143c010050070030004552601180e503139a0007141d40303080e12640c0030f000b5000c440c4c2c1c00b9002c2c840d4994814000c2e2900c030f4048644510303c1004000e1b26402d21040034a0740c416a160240c8130078080da1101a0a0030160f6007407002e42042e4842c01d0140c06420b1401508244600c1000b00d00751201c0c80300844290400030410003490074031002540d03070005014860125400e8001e000079541d080186d032141e154058024800c10381c903804058090a03070202000058800c00d099144c01c4035450381d002030003030f016074010301400b50100d00489140e415000400c0c1030591454000e00c45c0e04041c0105c5010344080d44026a503828244184421100000c080f2022812920310741000540e000c56100c01c420341510b08291661900001450b1001a1140007045d05000040794070300000d030f5801281c1220401d88 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 294510710 1250 294509460 294509477
    0xa020a050904030e060a03110c070e070f090308090a03051e0606010c08070803070c050304120314030609071413030308150d120c0501060b0f070c050f060d0b0301090611040303 77
    0x510100d408251001800f2445002c3d20444c14200f800c043e100d000c10a25010589412119400180d40c0c03221401c1000f07500441c000f403223045451000190848200d2600041c1c058039900c0040000115001c02000740400103030000b0f00399510031410000d0760f0408151030591103480107400700a41d042680c10124024000000c1d080d6000d01c03809245143c108001c0c501e0181640e0b2040000d600040c43c0005110300c800c02003010440030401381018140c4800a2410319149060150006001008008000700100100802600c48280c0c290700020242040c0e51400c0c41610340d10348074040c0003054403a645003640004103056000c00c00c5401200074440701c000882203c0148a942c1c1c5494001030709144009500e07100c214440d002c0703148200d00560000441684a4401c0042680000304602001c3d01c04544c40003408010841d0500810080b503500c1d003068003070004946c0a00403501d42c8a0042d54a06c1d20520307130344007900442c0d5807552040c0e0800c0340c1d4800c00e08280300e90f0400e01041d0005940ba4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 294511960 1250 294510710 294510719
    0x14040b030c03190236250e0103200a110a030512180d0302180301090b06010323010306020417030702090118140c0301060e09010302090114030f060106020a020a 70
    0x8502000c41101c00340242515580302908426420000d41049810040c004184014110794801000c84070104100602d0b91403050070804051080180000442520402035611a1010a8414070712403800d400d01d030003480e0328000160024800d201d0611036049e00f140c120020b40301454000c1c603445040740c8911113518091402c035541d034081c5410080105004000c1b400400701011100d5502020741d401c1814201c101c00400d0f401c020101c42c0580219402040d41c44076072100848100200304290000c216041903034a13410b048030710140500d41030550320707074030748080903040d21010508414400d06400156560b10741940254040d20a580e00b8080320410700c0c01c1114040126148145c0003400c039442a4207040d55050500401c03001076103a10703914580d45070070481c0020034500c43d190141895441f58900a006022000d903105854810ba1407030006000691350710750880c0c15550700c255400c00301030b001d50100c0e01d0300b640302d502c0300704c0b91042c24000503100381e0020342c40500354400d80d0140c10103541e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 294513210 1250 294511960 294511963
    0x3200a110102090a1e09021306110a0525031a04020f01050313030503190c03060e010801060605030a0207060b1c02040f020c0307060b06090d30142214040b03 69
    0x185107030303298003042c1c1c43e10402c01d14000d40b03c041102c5c80141c100d031038159511080710040341d004802c4211031040c202c804210381c54200d031000c08072001980103060650496980c154690007045500c0f4139200d100c10300c0d20310610180c031031107000d90f501c50f0300b4074401c1e01890380c40d1000d058102e0b0202c0c0300345406420945c640d4802c00a0f00c0c0205640d519107102614155410766603608014101500104d151001c0c2080d00316170b00411c01515502c1d10001201030906140b90b104501c1600034000e903030304100c010000780c0e41c000c0440394461044800142c58044910b4100e02070311840003901c0d4000f010310305440480303810688503171207a8401c03281001034510710340c3d400301607000350035140c40107800c00e1203440701003000c0780c010320b05000b4001d20a84c9031841c1000042e240c050560b40660b40744c05a1884c14203e0148a46005251084403001000c0c8054401c001448910700c1418802c0c0130a012039140d1550054401540da076800c00408416040d480e00c072034102402c605094a881541002160301281c00d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 294514460 1250 294513210 294513217
    0x18120501020301170a05031b010209090f040203070501030c0c02041d01050702100c0f050307050306040e0106180b030c09160c061103190e06070309050c0402030411130e0307020d0303200a110102 85
    0x6018007d1410b0103a0301381214140b9218400c10082d95400b0003088a29a0f92b2005991080c3d08200d0480d54504050040c54900300068000c0d6050520706a040e18116800c013049040c1070340d0440780841c0005481e2040401d200c41c1901e40c1000e50309000c14090b0701034010480c07124050350042d0030000d40e03401d41001c41c2c0141c10001d410340850400c0021404040c440c0f002140d00143c09040440c0062a07200802d08550140e480049182084440c03030040c0001030280425001e0100d0042140031081c00001b580800058052081104200d00000c4414001d0072641e40d6190411010081005c1100c0c0c2584281c0c0112540042c03da8000302d90f20842002c2d10400201c003004200070803d940c2c3d6500b09800070101d00740d040c5c1d002e02c034441c4546141d42d158001184118416211070320215a82014001c0181078000c60480950a080807030007038600000070f030744500ba011a0500300142c004e080a80c020302504038060400b081c603460007286402e13002d00920090f5040d13503c070003150f004240450300700e00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 294515710 1250 294514460 294514463
    0x7020f0a0f030e1c0b100501050711010c1506030c0302011205040b070305090f07140906060403030507020d11030d0207051201021303080903010b0a090603050c0a030305090118120501020301170a 85
    0x74401007441c010034415205194100006007030f4840d8180c000301801605000404201d55414011080140f17038640e031011280200001e0030440d0601c03402d0369030340c147c00c0038942d691410042051800c009000001303a0101010b001c6490411074640c59040c161038012050200f81e000c211078074140307181c3c01e0403032044900c0386c1c0d0040a00020341d101c1c07402c108c02804019068203210700c142c803d5002050414810b440050100000d036a0320900c8210038408004c03130051200348210300910081004c80c3c1c20900302c4055550460350300c50f43c212945030030b502c004405060b00d0b0705481440940c0764181e4000a5481c00e40d0411520034001c0e075008140f05085c0d20070001403201c2d80d000c8030f40800015410001804080c88010000703c0c40d00c00000214040d104558001213409485010070000d110051084e41007041c01682e40340c00c640d04603100501030303200c3c03440303050304010000b203112a400300f4004414016162440082c40a66400d00740070307010390020b02588050400d56003175427424a00c001800c80419 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 294516960 1250 294515710 294515723
    0x8010b0612070f02100204090501050901080d090303051e0c061b0a0906111e060415020304020a0509040c0801020408151846050607020d081902040510050307020f0a 72
    0x15959000b003141c00654000c2d0101c15486603042c072818414860010380040c2240040001e9a50300d02030410402180691000c81950080750001d040c960740403004071b06407601402c105658884820080140d25a68a800c9042c40800b0491034003178440401c0d042e000c1c000110341240304130078089080c1010303c80e40e12480041640700404100b01380c0100040b20000d90a501901c02c1d60449209030602c038284c0080000094000d0030030031003003001c0700c42c8504200d0b0b1105011402c5140c030b83d01280144030f150003907d00c0340704200000390800a0382c0c2c5131a000b92001c1c0c40250b40340c0d90b036480880d603038403200219140e66040d1040040d107254a2015005c07412040000102603070203020813024240285040c2c0b102c031201c190185c1b9842d403048041c001c40003030100540200c170003d03035003061703820044064681d60440d04450b00080780345911081c0f044e0464030100c807421145601008000003482154459a04000d8012000c49407a4111001d1803140c4c1d00707a02680d1000d025800010740f50f1440ea00001c101c3e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 294518210 1250 294516960 294516997
    0x40906031110111b060c16061106190207060f0f020d0b0603061810031a31080a0c021e0f0d0312050a060b190f05040501172a030108010b06 61
    0x341d2062812041c0b8201034880c40c58020425030150403c3c0c4c1500507c110f000704624100955507221056144401c85400900540c1c20440c5440509030408012100c60f039801140c0c12085c88210b500040b803000030070204000705a07040c946040030350402c5015039205d40c90203602103001c5c00d0070b40440744101401082c403070f0f00303041100d2624940c0a001d4200d000545640d40c010000071111120031454070a00032503010b0500c2e240800005080d58880c2c07500341031803080040d0f01494030a240d4000b90940c0306501d6a11510901e40440d080340c20000c000e9030054071038841d072452034410b140a2601180c10ba03000c030781c603c55003428000d8850030490000c000603200004071030340074900d600c10b90f0480003801021851540c1d40200940d19006401082000a1520660b41d1b048e80c005c20214080401410444e0601c1d244c1000600386003412154404804410000940175203030031032030000b1550310074801d014000c1c010781406007a0380003401028000c0d0b1910541654914040040c0c52030102e1800300ca011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 294519460 1250 294518210 294518233
    0x190c0506070f1707021504060e0f01210902150c07170a02060c010e070e0c0405010309150c0906020705090408030408070312050a02250302070303080c04090603111011 73
    0x4650701029042da0000c00e00001030b0000350140510b11803055034904201c2e11000140104645003030403410503c26100101701c100a49504010078504041c000c45c0d0040b481c00340000141e03600c0e160704644d01407100301c0c0c910947c000505544201181402685c40740484d02c410b000022031403048801c031030480d80c81800c04010a1080c0d0702d1264100c040201950b2100c0401c0d80446c8032500601c640040c142d448054000c6050001c020b044004c000e0b50700e5401e501d080581c0344465501c030350b002e503034100b40d1244400814409600107602c804007031078008225180402c00d00a00302d8815004120050203501000100c601d00a500035000341d0700400c19904e10348896450901951240708201c05016124005540c90050ba12072240309068035800503a0740c8046038100e82c6410345c0a8282c40b20040602d90780d5021a41c005010130681e0341c1828030301c01607295800d00c8052740c0a07071740c851040030b81850800b00401c0068518500c54000a0311203681e012401d403000c0d9600020400c0550a95001036001c80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 294520710 1250 294519460 294519469
    0x21c0c05090f0f070c080a170901050c091215090606010801230103020a0e0a0b0c2107060905151003110132091f1707080703050402061b0f190c05 64
    0x2500084217090110900410303076241001604043c4010001ca10307603c1c8101c0e91140b4a803101039004103048020001c40ca42009608020300a07011142e008400c02000300c40d508408110560b865400480c0720006450001c21056984a044a0f164005844440001040400e6040407020650310356034000451961800441c000d4100c1840e0904100d54040324100c0c1c1e0312030303a01c3c040290500305130702c940e2189003001c010310300282c03040918804415451184907108d0280305407041c0540c4035002041aa409092051800803002c0b070044510050b1028020030703044005008085a100365450303d0b1564440c0c1c010740315032080b5548012060108042e18101701d1b911a0354004041e802c01409060101000204240002e02101102c02111704401d001d0380a801c20b14100d0002e4481c047c400c941d1611210003080280c010300114103041e03c400100c3d003190749a005841c407041102c9940503098400258180d95a041c41a50025501a441e080f82c110b050340162507003250b0300720000341d400503c2c0c0028007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 294521960 1250 294520710 294520741
    0x90c06070c0e0703091416092004140f04050c030711070b0c0a06050c0405130b040f020f090406060806010c0803090705030307080c0105070c02130c0309021c0c05090f 73
    0x4a075008080c120104030b0505a4504500441590350001200704a83c600010183c1102d128903002d03034005031b404201c03c1c3e00b80c1203010688001d04070114070b010342501d9608007400700b1103005888400200d40400c0e009000c800c50b403041e2800700c0b0615442012035003440100c950039104600a01c004000080b5000e019800c40406029003c1c21610110350395100c114883e0003403038440095402050b401d07030078400c2d24010a60811401c030421842c180c1303003400241010004400045405840700841341895440354071090b50b03c5010401503540302030960303d80c0d041e980042c6080c0c1c410340c03800f0804200c15200e80c8280f8840e600684803890120340036121010307643c10042440e0098482c110001c2460f407002d20182901c107206081e413945540f0b48c46200707800c0d43c0c80180140100038440840d000503980b4200d000c83c0040c00040c0018054a03c100101c0280c00c203101301075000903494000080c8190056007142c1c5440c064080901070039140c0c030800501010541d41c050480c200d48000c601d0340c50800310803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 294523210 1250 294521960 294521963
    0x21060a0b070b1807080d0305010e27010b0307060302040e0702010b030c010518030f07030308090a1502031504050408030702010f09081801050403060908040f050d0c030b06060702031603021008090c0607 88
    0x10280f20340d054400091502c5003942011165401c403041184c1e03910b40500641d400341c034140035030380c00901c1c0c02e0f03003464003071802c8100140342c005844451200850080d4041d202d15140074060314240d9448600c043e001e5030044c4651000803841c0d0f40020030b00783c810300c154206408018060196840d6070001152030750801a102603030001103040800c66607401f00081d1617001c5220f80541643d0b0b1031403c0203405003000900c0c00c0166007084803200f00082c40010070f080300105070702c2c0040e141c0e2103410009406218086240340c019290400707200c18014080055840341b507056000303000004601c0d00c854141e400c1c60300d00521100381408003400541200100511048061500710300307240e502d8031a0401d40f40200025206010001424026800034440f404007402c0240d4803504a844d695460b005011010320020307140f4062040410300e00d07a1810100d400254000f000c40342a10b0351860740c01030905051004030311408507812402120303400740039200e11961855018003c80301e02c1d613090002c0c80c1d101000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 294524460 1250 294523210 294523231
    0x5010e0601321e07060902010e0907020705240a1107060c020d0602070512030408030403030b010905060d0c052b0b0901180b06160b271209040603050321060a0b070b 72
    0x61040403620f40913010503130140d0f1001c01d24444034000508880c08003041a801110141e007001b102a400040d18001c42e50b06039a028011808a800c1c0030fa041c07200060142e1103d40040c234410520b6020540000385082c00c000d46008554a01c01941c0c2c903100700758001d4009048084501c04944294050a40d80c2d001e107040c1ca6a1402199111103d0740c81254111640b48005c01400305043e41481922500d82c07080c200044040c5c01c240000b0755070b005a08103402060344411040c00101d03c6502618a10710180b070b4410001041101d11032403000002d01c00411aa1811182580d07514100303119504032400503c5d440c102c1684c0041c10000b804800c0900c030b800c48420040c030703082d02c41200d204280a90141040c041d0324140480b98103039881307043c20103000c1c400e0000110f091200e808074800c441d0394881c500c0d440d55200c00f10041400b4001d10fa0000c0c225000c0414809046900c02e807402600c1c212461800c6120350380e0808109050346640150344441c5018454040021141e14059821100d80740 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 294525710 1250 294524460 294524497
    0xc0c0e130f050a0b042901050f040b0f060d0c0e040b0d38150d030801050d03090b070804080d05070f080f0d0c110114090a1e0605010e060132 62
    0x448010b4a00344c01e840072110f441c0c80040e00400c00d045103024903444143d45003084500d5140800207201802d04584030341c0b040d640d821050065030703a035404651040d60060845a1148240082080100210010140401c440c1d6210a0007441e081c800d4080d6000000c0c8024041c0860f5100c0d8141c4603084d840058001010040d40e401000c0c40c0c1c0080800c00521383e51156884ca09034001007105804031282034084c002030301c0e10000017034000420074191402030b120010080c2642c2412600512158840b04007210005202024007540c0c80081080d241c442044a042e1460510100d407984110000a0b081d918001556000261028020300910f0300c000031071420115144c02c0c040807210b143e90590f010440c41600081000c0c03003030140806260b000f040f502480c0c681011003e440d050640300080072151202610b65060340d04100e80e00203540c01903400c010f035685520600e90490000d42e010360208000300400d040c840b000501240e0403584051505142c003000080c0c54003281c1191640751902c10008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 294526960 1250 294525710 294525713
    0x718051008070816330215090c0f010f0507060c0309060c09090501090207171b060928150c030b030a030e04050c07120503061903030c0c0e130f050a 65
    0x200301410250510f000a0091000e6a00c8403490400f0994060104840c4070b003640e0388190500380f00c0500f20014004866903090505104908042c03040d40f600790034000800500a40610020758290b4101040d640c8202203150301c401559080c0804444000140c0108240380009000f50000c41995584e400c000c00d41d88a513070760780c1040d1070482e18400f000600b03894040049000d18044c8a00424040034214944012900d402c55450f00c0c83d1a26055024005040c140e02c80510302c0c0000c00400940a40b840c1d0704003910340319115528148210241c40030003203404600b4901c500380e031a03450342c44916008d50b6450224401c01621084095006055490411404d90745040c000040c2a41c4241d80e1920010020009c000440d840074280c28002d00c424010307200022075208981c10341c95030b1800d1240d12aa200030010319001a288580d141d03410801034000105034010341071082c2240303d6603440062680307840400201140c1210030783c400c144e003403103140d001c580b050070380044c018001e070241c034600c0070340e0b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 294528210 1250 294526960 294526963
    0x2160305091c03020d021006120605040f06020c03030403020c031f051003060c020309011805060a050f040306060902071202011413020a0e0702030c0d03020306210a06090308180718051008 82
    0xb2200d0540160708045501159164180107081c5540900d00c42004168105071900f0020710250310300919141e40c483c0454280060070f07000c2c210307440d4000c08c01d644e01e1900c00402910384d00152401c0f0094441c020f1070440a203130100ba00c0f65461b1711383c2c45001006500d44c07040d00c080d01015000d4a9024401c005c048003084250103014040e0300150000c43c0d0318803072500010305880108109180c03204241c042440701d0f540e458100c680020143c5803440d2205403000d2a1344851080398002015a85028000202500b0300d0b0058101940603588540500d000c80206909890080b0500395060700300f03000090400301ca0095107400580050820000c081d1685103080408405454480241e4004558080141800c0101d84908070003850158154180394020445800000c2559a4810340c80300030000c14000402140e503026800410600003442c4034180602105e02c250f409248189148401607000d4100060780340481f071017101c5000710320301c42c5c1600000a0501500480f00900c00c6000050f08040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 294529460 1250 294528210 294528259
    0x60506041b03020301150c120509060c07060210110903060f1b37020c0f04140412120e0a0803041406040b1e01080307031d040c1709010216030509 64
    0x2003070344005940c0d50510004071030211b41080c0c400c0c1089441510000024500c00c04010043c803641003445d103910b2900002040d038000c0b91042d4100d4811980001025540050015026040324808000895404901d46007a1061588164055010301c01091050182c00c18440e80201180b080740a20203003000c03100000c0e400340c1d5441407000c000221030810481945540d696001c0c250710405245030140c0806500c6000483c6444c1c860f02c8000e00203100c43e240d5130040070300310900c80c3c0130080034902480c0150300c845210030403030b002031805502e0911190352417086082101c0f00304028809004c495648120710360009000711010304c030f5608101d0081d0000c00070305010301d226500884080c80d250045280c210048052455041840d0004124042c808011031701d00310f40526044038454200b001c640500725481b0800c1e90014074200500040ca540520900a818814980041d064403449012400c1c3d0140c0550700e01e00b140303003c910000080c0640000d010454002e400040000e62507000e0511640c3d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 294530710 1250 294529460 294529511
    0x12090b0c03090901060e0915010504030204020d1a120a0b150a030c1d0601090509070c050d110f06010501051c0b04091202010b010206010f05120c03071e0801140406050604 75
    0x24030100b00005140391a205180c0904041d24043c1c90300294a00000d103581000707406001c0865a8000c9040d46d64031a0302101d000e0350f0050030035591041800d48200040c028540f40306c01d00c1d00c10706981004e9182c8180d20403c2d9030b01c4240141880c0700e00b070b2540305204101600c1c01000030150b20000c0350513212401e00e00020340c0900c40005c1c0162905240b01d8020811054086101814034101305840e03801849450036210f040e200030007160740312101038410700101e500251040c42489403207442d540c0d0100308512144400d005481c2c10590100c0b0b165600c1400380100780c04518103009892180014001041501d0500c000109884140801282c111240a13400341c540d0104a041c5d1028583c09004217650024280300400aa40c580340c2c0040050342d80703000b000d2040c07000102d074165242003088104007560008040c1d5404594805070885111801070050125070306404001030020018803e00c220000351101600055a4665a0300d00400d002070000e82e1059551007844007040c10680d0460342c04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 294531960 1250 294530710 294530713
    0x4030203071509090207171b0a1410110d02090d12080411030f0607053105040501080303090a0f171204060e030c12161205040312050304080712090b0c 66
    0x880b90054010414800c68200c0c40955004101100000381d4411f030410700c090002c15165120542080c410b0507142d4242d181c09400d104645140d810702054010380d41d130103c0130500700c46003e02203107014815954040301c914001c2c40700740f0100741100c00b42e400900c060710009100800e10511551641d116400071854040010319074010041004865106c00d500c51008400400c0070256a441e26980c404000307064070100900420f60460124180c0c8840403003405c9240d440b0307010001d0246c000000c0040b0b00c501485141000c0c00003a0000020007101d0080d940320024101c10b11140d01d0744283c003041024101c82c401c5c410080102c248001b80040d0a044a030140100501e0415042610684110a1028199420400000c040c4903000203540c443c07214588202e94581801050038003030040e030084083c4c441d106520316890b42c180e100d0018000d681c401d5000503070a00140504864a000490300204103040801448020030901e191407d8404541c1c500005001e031905c0b00e5803550b0300000f0255616 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 294533210 1250 294531960 294531989
    0xc1308060708060d0b0402041a06040305060603060601050a1b05070312030f0f05010b04030b0c0d021b010f0911060d0f1a090a090b040f1e0b1e0108071503020403020307 74
    0xc19610454035038100c0300c02c8803044c0780007426485481c00d11401600c000e1060b0b035a814003101d01c0c25400b920b0350102400402e490b840f15500d08000da02c41200703c5055209000c0c8400040c2d1641c001d50555504010329600c00c0080b540511175842032a66038001600d80f031160480000010b00c5109140c04d40c00300a076030114104501902c0034007a5030b00c0c05509030100741405c0051261241c400c0540c1c0032030381c11850750222a02d44902c008114402c090090134402e0001a1031340c3c5611841d4100040d1340c4052000308062620302c8003c01c1280d0b1200401040c5071481001c00d1460b1500b076020f0f200b00341c0030741c1c40007440401c250385d1304080f14150076040b43c1441007800606d1319894000c29081c0e01040c0c110003804030b05102e5803801030040b00100000c0020074031041c3c0d003040c0203060024000c42c0403461501c0950f1401424903913a4064110350b03610340c0e28070004080e00700c0584c982455040714460402000c01500300548102c103080300102a0781055400c0c40000090399003007200c81d00030406242001d41e03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 294534460 1250 294533210 294533221
    0xa0204391713110901230d08030f01050a0b21060616141608031603090b030a050103170703080c0c0a0503030c0301090606020f070506030402010e0405100608060d11090c130806 77
    0x2c028042c0710341207100b208041300400c442c40b105070000056018429001d48a19401000100011090007000c2c0150501008000001842e03070705050607150100d41a00c1d80c1a80c40c94100506d10440035140c0400000c50000b207801c40ea8500a5030b0803100007024030303041c40c001203a20120300765802c0003615031880480c559003859006210041ea158070b4001c504021a082c91581c03542c2e4442d098602602c4450845503009142c448ca030b45d04040e120800215a4030704040c100b41002d00000e00042e60045000200c0d07241d84103100341110441541500d40c2e00007582d4800d044c2d890303a006400071680d0780c0a0211040005541407008520130210182c10710b40b2541496044021112150010b50556112540010000e00001110003c58004488a540c1c1e6900d034401210850002c1d03020302c1e0020b041c04244a403010f81c003c44442941e0241da102242039a5240411555242d01c22002c1c0102200c0d04e043d00c400d060188070150310840080309039242881c00000b4403089409544090718a8218000303012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 294535710 1250 294534460 294534473
    0xa0302060f0a09020a0b0903030c03040608011d070f0819020c0a0c06020105010806190b130b010e03161707030219030512030f0c0d0e07080a0204391713 67
    0x240c00c8000c60004010550060f030215111905c540138100380c01c8030100f2000300c5139034200200c0e0b00700d4680704142c0c1c2c0c9031139070749802403e003900c01c2c0282e00901800101d00c00303910151480c01d503c52801e40c1e45011007070b6150350303090313840365030243c14210300503c01049124003400900060080d10a0703680101441d01e03960400c0c80354a5070940180085905050040110300b80c00030700716420800c01c1200901c10b940170024030004040d07400d20307250400081c1d140c180f40e4814a40c40481161001e0300c0d07890300c5600c448101900c90350f1a40c1c1d42d25036554614000d12214050360540c19031804a1011075400702d0311303600020300c1030300080084c2e480106001801d0041041c2844400104510144194218100b940300c00180329802080c800e14114049000341d1100860741102c89600d03054004e440000391520885512684018400c3c2d0043d402d0041158507220701c3c400c0c0440c0d40068404020341040001c250b5002e030892003c0d480d003000b08407505400c0d80003150700d415010702001ca03c45641f078100d624001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 294536960 1250 294535710 294535741
    0xf270915060b04140607030e130f06060f0315050a092723060103030f0507110907030f0c02160504111308010203010302010305070215011a040314012711060f0c0a030206 74
    0xc03806940248200300000307408c00a0760701c05d10030842d400e0001740502c0304002c00600d40200d9100146040c00c0d000901c05800801040d501e90055074140424032405d008011424040d204040d0011458a0100030503102c0d54400001644103058010207a516030a81000841442a0070345488405c0d5a0f051400380d01d030955580b15100440140c0b0885d0b1464801406003412000d0b00424401c0000d0b106040101100d040719040307600401c2100b040c14080c8008008084003441d5285492600100c80c4071a8000940d0242c600302c02c0f00c40001c80ca052400b1b00002e00034044e01c03884100007d00003d502c0c1c90003080004003030070b0000700058496146000042c10344102a140701c044d500300c9010907414188071002c80d8103481e06800303014103c06009004006503c16584080d10103446201001135030700301900403803110301c001c800c0321800c507000312120f0800c00301c2031b14010180c640c0901e01070601e061020241180c5199402481d0900c121900101d0510302040c0c0100c0c0140c01000c1000b1400d0b0403483c65 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 294538210 1250 294536960 294536999
    0x50724020d020c0609040f0e010504060f06030206030103061d120a02060606030103021c0c0510030204030c270c0309020d0f051e030405090903130303090f270915060b04 74
    0x60110078420200a5110307a203407074056001d9600000e02c12030035217407600300c0f4500c40c10b9540b0411003d0440390343d4500800c0d00b900d04a07611802c04401050f0300300749024090a40380c00420745460b50b444d40d5510310040c010400280d06601032050b0340b5180b0311003407100081400c2107903030481c0d41d50180035000b0305201e0000c20301ca204460510040c00580c49041c103070507284003480c200c9143d940711414814803242d600c0d8407456005070200b4050a2031907242d000741003102e01c101d050f00700b001d894004101c1c245203029484500912849081e80342401d440d040404036074094100090f0b041d1290700804ea000510007003c0c1da10310411222541001003c00c00000f521602540b0031f0141300302c00b44450f84a200e14405c481c4511945d6000c079103115001d00440d840800740407074051300ca6a5a1401525480e101d204103002c625141c9130024103081203550000085044034202155405070202c088014042480242c03180c6641c07030303103500d454800c1c0e01c14035010340032180300c00f62240e28100d01c81c41011000540c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 294539460 1250 294538210 294538213
    0x608071203020706170105010309050715030b04060b0301060203091e03030307030204060f0206090304060c1a0f04120809070e04080702030f0c040f110d022d0d050c03070806091305072402 82
    0x8000d03100c0e000170000c550540e0024600480c148841c5e04140f443c11000e80c1042800f442c0c116003061240742c05a1100c00c00d01015501808202d50300e1450b180240424403619025030820007042c610792034164010034210600f01c040e405998011008a40796800c100c5039100425800141030280caa04600c0c1036a001240b44014007280c9010705115480c0d026501c214070070710a00d081640d0130401c20320740bd0701c1101c480f18010b030040d1070030503038284031941e0035201501c41110007a104002d0620a01c0980e205045040c020b0402d0741c45e0a0042d403050030010300580e5078a07424400100181e80c20710400703000c1c94420000b0140721456074100000c40d210008120107091814140182c1c5c1d000c0703581981c2c00107205030001138958034241104d01e094007804805010060b1020b0004028441e100f01506512050000820241d81d130008803800030b1109840c80f03c04595458005216071400c646031a0380400000c000c19050a030940d078052030710030540c0003240950302100e85200ca03640c4800c900c9030f080c0880e10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 294540710 1250 294539460 294539477
    0x1201060f09120312050705040b03041a01050d0b15040b10030c091202090a270303020301030303060b12060405090c0a03060e0c1008010902130302090f0612030a0e130608071203020706 80
    0x10380140c0161103909002d1080d0380ca4500003201b5a002d1404c2d01d00622101e180d0580d80d20b0140f6005500c43c0302c10110249031045003001042c181041461161141c1e4014060300b6651104c81d10140e00c520851540396003d0703121005444243c4880107900340b12141d945002c10240031030300024181119682040c001031802c01c2d507a0300503981d009819034101d2412f10001515481194204500952142112500080c80e1142404265155005604aa009070340c1000141d48541a14880b4424443e1140e2001501d80101d4031500d4140d11072900034013908100c8801d4141840824940c0b807041d88141d13400796031a10440540b810034841103086480440354010010340d540009061200306000c6c01554035800724214040b29444074441c00903640050080c000c43ca003124249070300d10707012103215000f0250340d0915094070100000755400c20107240c8a41070003102410501c82c9a49030030756a1510b1503120301001440350028080c02c03000d80085180e4800e02c1d041c42c100a45490515841a0104402c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 294541960 1250 294540710 294540713
    0x60612060b0603150d111c0b010e01031104020a0221070311120703201605041d0706050f040f1412060f15031e06010f0b0c060a050402061201060f0912 66
    0x2c81c0c1402c444ca40072a88032035465401e040c180e135840038080700305401004d00510000100c643d08680348542e44210304d000c071f984c0e0703c40201803107540b07007803200403d045603040141003907141a8002d0807850442e48101e81e44462100181d0f0f42c00e550000e824101c0410018104d1b041c9a8049401400410b4003001030060701d940c0507480100d4410660007404205040601e2010102071150880b40e80c43c0f100200c030b4201214811142c1d041405d480781900c980e10f4000310218542e2000d00101e840180781001e01582443c00d40c09586591000200c0514070724100400b24826003000400d80240c002c0360b41455174010200e042c0103110b580c0d000000041d601030740c200310b50328000c036401a13405240410390381001c011030740100e0700e00580788402c140785001000d52840394090004d1183e04070307030526080103c486c2e07480c22240c10b43d110301321042c45a600840d00045019403076030030454009202170300251070991102c4a0f07a0120038203030405d4000940c100500b0856a170300c40d5000015119071001440001e03000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 294543210 1250 294541960 294541981
    0x1090f09050c0708070308180d0801060315030503040902030603070501050c030d0c1205090d08101d13020a06080709090204120f020105040909030207090e010b01051b0109060612060b0603 82
    0x1144108640107868400190610380c52030159004694000880d9807142202d10b80582504402c0304c000450580c03110350041c001c5070001d54111401d8064076500c0160342801d00407030281c25060a400e911800c0804000700203141040100014500da410050f22824402e08060802906e0f81c4000d041110600c400c684150010046611070080c0c0c42c40011f0ba00f0b082d41c000c3d030312002101000c0800398035207410800040e0020990702d2960b591955192201da591588950100c0a540038004120600f101041c4c03021240310340f495080302244115800403980d507800100020b10380d4021b500050100f00c240001641c0080c003000182c483d41e80700707600701420107001c01c0302c1d50715100e0b000e4a21010401400c0070345e409102220094900e0f0309042c40400c0075424040d544802030720466850034681825078000c3c80c1c06110303824030108165145854010600003003002416110301d00d84440d542c400410300003c2240c4110001441d0320040c0084680300c0b4284039084132402e04000b03004042c100304115640e4503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 294544460 1250 294543210 294543239
    0x20a050c09041709010e0414090d03020a0e01031a030105010303200d1707030902060309010c180e06010f121406011101060f09110910020c12070302011709100f060f050109 75
    0x481c44540d51300ca81000004079200390384180b5913500f02e86021903e18075907440340301540c42200d00b541203a0310124202c200f10101d2090110283c00228403060141c0207600c45e8019003c55400e0381d9864141c5c0100e0b80003e42110020b038011402314400d06a220141881c948581d5034410201c800362644070b01c80880604494205010180c0b42603031000022000c0b40a0340c440102282c0180003aa203c0c0f900705c842178000d1080780c0846001c60b0051110b0046d40038019108030654020b02000d00d000d803200c1c0015996001d000303c5100902c4241c0c10000c1004402c0d101c0e0070b150150407101da030302034140b00c400076000c40400b81144c0d0343c036410588140310940342d10016504840c00e520002640c041014140b004a0144c1102c55510600e003210410900d07900140c0d900f0502d4048800e01c00340541c2c101d1559640b58140700003804100e2240070b0105c40220001d001e540540c540007035401040c103150404c403c40f10102e00c0300502d50341c5d4480a200c800c510f160800b01600080c20311441650070b0844100c4401c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 294545710 1250 294544460 294544493
    0x50a03020c030c0d0504091508030a0309050a05010e0c0a060305091e0742020a02100905030a14010501060512010911041e030210032702030f0706020a050c0904 70
    0x503000a0580c458a1040084441c0c2c841c2c180705403211400c1d48440288954440c0c0708980104c2d003455420200310002c1c0898604503241d070300c0258034020030098143d001c1c04852106070707007a00071000d070103000c55400e0103482400c00090001c2c04d040c15140080040030f110907040340c010549031a0400c0521040000c10080c5e0300c001100c900000044035074082d1070100190828402624203c03581c8012802d035a40d080003500842285100e031140c40c0d0000f80050403581c00080050b40b1580d110005030412402801e07880106182070102c1c0c5440e800842d141811000c0b08a40070000307040d40b802c2411082c4a19405843c3d1403030982c2c500740740d44903840e40c0f251060042080e125500c411080460040c035044400034174000c044a503031100d41d50100384c00c0c803c6510069001d0441c1015109841d0712038070076403103a1505104015000401100d090701d05081e850412038243c410101881c03102a401c01c10ba10041009500034010030034649000c90030b11489480c03c80c007a4108505000006102941008045 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 294546960 1250 294545710 294545717
    0xc0e0306041412072d0803040318240e011b020913140307050c09010e0f0a3c0506031f0609061202010e01090501080a0c0c1b06020d0807050a 62
    0x80103040c80d02c5080000010060040e11070001e45401004198035511242c94514809800f00100d05840b41e010030714540c1c002015a0420000500001d00850512024442c03501c1c12054072610b1f1248041d120100d086140c14142c410302d0007048042d404042e8030704008082c68124200e405090b003090f024408614024820140580020844940e420151700c00a030031829002c00107005400312904c962003e2000d80302402024004c04e030384c0c2808510f160403a0b01c0485e4590312940c90f2414540244e0024102c00b03001c2d03440f10402d81c41c0280b01c00c00304101d41d064000d11161060704c1888100142c1814001c813200c00c1c100402c001c2c1135a004105a0800e50702900c84a00a0003515108801801940c1014241500d01000480c4101041040700c03461032003030300d44008001e030260056410003024400c680c005544600083e032030300b2907038001c1e00811003e0f081c83d581c151010354410b4600386201a81512040100c0010004990304129544aa010605040c01070303040041004009200e500c8500c0c090 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 294548210 1250 294546960 294546983
    0x6040e19030c0f0b041a0405030409051e010b030709080c030712050313080a02040606170105060c010f050c070507050904031715060a020709060603020a200313090204090c0e030604 79
    0x780350080361541036642c0c0c800550301200c00603107451030b01070384d003610140c6684490381d903410b10f16080d8034091030099401c1401581442c2c40d0054040291030300074900b030780082d1601e0650360f00e01e003070001513030203410f046005544070700d402800280300b6030155120640d982e10040204c52580c4000c2214400e4485002d80340720001e0746820002d185100760b44c0c5415181000210000740c244000c606020310364400c880601c882a90340e131080300c0e40054a00c0c249050036200c1e00400c1b507031601b0f40041c68200840d400218440c8141d94030241124012541c3e10502000054000300300242800b0000c064101124039a40e11304103520000c02e0300c0300d1b4200346118900d152001c40c004080310300144440c604d004081c10342d1049880c070300940b03503003840c440d4000c0e040c204000410418024001c1d01e0760128980d90300c02d00603141030109820346c0f90030703d548820341c002046400b6010750400c485101400c401400940d4851070b00030b500040799040c0111804010300346103008460760b07011070015000f64100321124807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 294549460 1250 294548210 294548213
    0x1021213030c12020102040602370c0816030203010c03021e03060a05060403051b0109050d020d0c1509060207060306030206071b05031b0f0a05060417031606090b06040e19 75
    0x2014900102e001d0500e0040c4150004507940c150001d0043c0c50159082d03401c501041c110311178498a01d2210800c04070401c480d0102020b02c1c81088401e0700303024032030b8000b400d0303510035101d42013015189900300301880d031441c28130560409000d20036040c4a5481c04601d0903022244034500211840345110b010400040070a01da907642c0b00e050b9015200060115689544d01e14165541c0c8180da0600c8890040d0702600d02519801020450700300c030005862680e40300c00b55401c103c070115814000f03d60301e01071004042040890348103804520702482e200c200d4058200b0030003030314155140d8004020982080e2007800142c0740c00341038500d4180d000d042d0744d186040c003462450310406283c00803601807007030b0440d10904680d04241e510200e4025070f4a11404c0c6410801d00c040b01490740181d64005a00300010072011480d40361038141c0c3c40e0004c042e40e042140f80b20400883c0f040b5071101356200741d2542a00e0b418414419500c60308102c00b180c0400c14612611043ca03141d13500d00c2440000612184c000e0320 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 294550710 1250 294549460 294549467
    0xf01150c02040f0c18030809040e01141503100c0507022b1b08010b030a08090312030a060918030215091e0706020f0f0604020f0f0301140702010b01020102121303 71
    0x103032955802082400302d5104804103000800f103240b18000003c00b1580c5030310010340e4281d40704003540c0e0481c540728900700080c000d02014114041821071550b60341c040100003035184400880c0284000410038481e01e03034100c02c061130040901141042186496041d000c4c168000045480899040c1e50f485000042d014640d9072a1203003c01c40d03040c6404403080d00c005c20150109501e02e50b8a481440440326480e6480c841c2200c0000310740303030307019845443c19001040500c8003130180352000404503075044012201c201e4240c0c00030b030355001c000c0b501c1b418188005a2140070790142c113003818200c62000c4855440c020340d1441840084101242154007060103078501f8030090381410100a00c1c08502030b0415900355840d140c910a44005002c1c055030342414010108610b040b1159200041c0b043e52030f641c080040d8100c042203c150b100c11080c0c5e240781c05441c00c0c003442150a0000320003070480c1c6040f0001070b003034840071a0082d04591042114031030604048841c6504490100c5651041803040c1c50250b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 294551960 1250 294550710 294550727
    0x414280c090203100602011b02031206041d010b0907030b0d030c110307030f0c08010c050436022101061211130e15060f0406050a0309020a0807030b0105090f0115 71
    0x4441c0903000004000305882001000e508a038001c2c3e008200e04d90182c510b40f03480144401042c001a00200700c2801c4800b040969950000001480003500070f00b03018002c0f0441080d0074019403181d465078071060720780c5030424a032a0f0001650905229200b00700307000440c8000c01c02c400505000b01d02000070700740030302c128040804074000b6080308c1030702ea100d050001004c201640f040f6000c510302e1001044d9503c040c00707000d4110a00d40c444504040c01c00e2000b42894003240d5003a410501108400203200095841510801404100041e922810000090360f4240d10301322000c1d0072034580b0010004a40d11486444402c0414180090741c42004440703450385220309413001d001c3c0600c0b00b102003030101b180710199009800940310002d07581140420b012660040c1d00401e10405018002008201c1c01000106525405441c00180700599a4000348580c01c0d16000340107554081c2c5000c0c810005960308540c00340c1400c07a802440d40ca04820300c3d00c045503050186180070004000071144490058404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 294553210 1250 294551960 294551969
    0x306090216080a180605070b0a06140d0305090d11042313030201090803010321090602030a0813020d06050a0e0f03090f0102030d050f190c09090b060c03030903030414280c 75
    0x4c00d144207a03681c1c00140f050300150026902140c1e0b0801203648404580310b030700220359540203000c00b4005d050f4104000020b50020580600c913080061840030b0b903501210801d400e1152012840516000e070602040351040014118000c20708425a0306072014201c980b13030300c40500c1604001d028024074040b400350191100c0100540400b000100070031441100070481c110b44000242c003030f855074060480d0b0f40c0740d15100d10340158004024140c01180b00320b8115171700250083d80020030300139650100e1103e50b26020151140366448060140c01221401a403c292400348020001c051290a905440e44640c06100c0e1040b0848014941c05034020300c141d401c1c0503c12075003000305151001280040300021104880000c0510384481e0100103c0d12864010000595490102c141400f01400060212010311680f1503000e02401402d540300300000d600c2548154051510b80c01c141ca8103c031070881c007002901e4503070015060304501c0b00c3c40500f5901040c1e5440c4440500c98902c0c188018110101d800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 294554460 1250 294553210 294553247
    0xf04111309020909101a0708090907170c070c1404090206120a05070c24060b0406020a12090509040308060f0603010909020f04150b07020319050d0306090216080a 71
    0x1400681c10384181c0c081d001d119410741e0902c10aa132a00790b405036440050042261034144c0480713122007004200050140139114a09072490810003100003142100111000c4c000a4030fa51039924400c0c0807600c1190b042428500a80e04001582d41e45480452490003100c3c020301d44041040f2503603a03030340c0190710300a40180540740d8072221511908941e1208490724280c140c28580401c0c89248034800c0c0855280c0c0201c1420b207031007085042200c98080c8507140009017612254040784480d00100240000c118070340082084092902e840c0ea45000c103503280c0307030520900c06000c020b540c940904c401e03803166040c60168141d65075000012030f061010080035400c18404000481c0440d2243c1c06080d4183c000c8071030b2001281a032081106440007101183d916864800d07080000b42c0a10020700701c41840201903d5000045801840c1c0c4070700c00410940e07480d48006900705186415100d04805000404030543c07400c291411145407000c2c500c40010402e803000142c07189003612070079141601201314803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 294555710 1250 294554460 294554497
    0x90f0f090b1501020307080a0507020a1502030403140105090d0c0c030827041b0e01020c03030304081b03070302030a0c060b0306010308030a0b010518010e0105070b0a0c0318020f0411 80
    0x101060708030000c0790900d0b40410760122005280d8000810b0310303540345d4081c4030280f9201400f80d003240d294219440403a0014040035000c22403000b031a1003880d500107070394010b68a840c0345040501000f150340101c03450591602050040c000341c08141c803014072460f410031700c1502d181c030700d41545c0880c0c00340d001800414021030340c622603148611000710310400e01307906e47ca548000300302000304550b0380c0814002200800b409116030300380985504e0410560500554030801500400f03e07082d070b4012038040350400070001e0340f41c0261f409055021040d50300c0340002c6042c42425980a03545e44107441d9064140013140c1140803c01c1000d0300a64811813024054488550b581d20340768038141c100703680e0f00c40f4141c10f00d403000500303510070810364210f80d1724110044201c3d4800700044d1207405400d031200341008000c0041101084001c02c1450194a40020000d420b11506000030100e230315220200c24002114080c1c038025035504005a541003004a0340000c00e0590040110300c148070b2040ca1400040504 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 294556960 1250 294555710 294555713
    0x80307171315030c0302030601170603101109120303040807080f0c0a05010504060b04140a0c03110a020a0507050409050d3005190605060f0c01020d1b0207140a090f0f09 74
    0x6854403040440780d0780f07040c4810080ba201c190107030302003220350074005101c800c60340b4048103102d500190003441c042d064850107015803005209880f40c4041e101000a8005004442c504001c0d041500c0c0308507440c05541581040d1ba1103482500c01c030400500100404550b108070307032001c10201d541002c40c0c030003200c405011390310b030260180c0f0341103c040e1111072400c07411010328205409a0718005004224005456503a0440240280032505402c01015a43d40c2020a141c901400804110605d030f0000c1541d19114580305182c0595900000c0c01103052440c006e001810020b10307000407113540d05026091a01c64034211440040c1c00003800550358201e84107110195403075100c2c90148258100200f840051221020166060340c032801d900100100200e80640c501a0003400e00715882c000050310b86500c8040c41c0b0140c42d40c010b01100d200c806065950f05042c1c04101c1800145002240300c003001110b10300040c2040c043c0c1c40384881c00c40d2110b01d0200c0c040306662000c1000711521380c0401002896 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 294558210 1250 294556960 294556979
    0xd1b030c0317090f0c060a12050c0f04080f0d0507080a0c03110d23090604050123070c050316051f09030b0702060412080907030222050702030d060f0803071713 70
    0x3004c1460107020a00115070a12004980c80d8050f1503c58140702c503070310783d800340040c200145188000c00080c000e038005c11000000800c01045071f8801000c11360500c95049081007102d9842d08184581001203e0010300004e0907680e5803a01401d1522111006003402d03500c0c244801d50388c403014010f2402c182c101030b40020008202007550801e000c40d4031400340b0741001522a01c82d450380d0094003808100315a41c45038845a103d40d024186030014003e040310395481c6600910022120314804a80c00d0080d8103040000d1340b4032051400440450b245400d003c03460b920610564248051014040341c0d6003507029142c20070085a00c014882054504108001e45801c0155000c80740c1e51680c840601001d1704ca22015406020a1006080d010f450340e0300300300e9529440c500c00d01d201d42140741c0b9816008801e00c01c0c20305c120000e4000c1d503503c009441c0c1643c121a00c41c2c0014403001518102403250b41400030541d503000703501094048901c400c0306284403c5d40a4808150100081c0090102d00f1226 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 294559460 1250 294558210 294558223
    0x102010b0411041d0f010927080405270106030f0b0a14010e010801080d03091713090e03070503190203130f0905070305091b060405150405030d1b030c031709 69
    0x281040c0f9007006440070803c0051144d800e86082203d420000010b208000143c0d02c03e9000d01a01030840185030b24186010102c0f0381c691506482020b40800e007000541400b070103011501c007010307405901d4a4040441c2d29542c036011b0054204041c1d41ea0107001c5c00110700d90020100050041520344101d95428290104900b958020743c0010038004606003154042c0301d0300303410384e15158080c016540e00c4e10300890003001000c1043d6107041900107100201c180080050224a20200d25110034905064000095860b04c6c019240c4a500412201011850210035600d4055101c81030051400a0742812851409400512024151455000240c44a40c0307a2540100d03026a0800e1110382d0700c00e5426421104215890000c0d50442c5403600c540956048800c503a180f802441107040c02e403a00c02041a03040340600501d2400000a014809447d0811007040c00800919101c0450807a01d031401c070600c0d104590042c18020b0000c0700d03004150082c0d5514141c3c800c0c614607041c0d6440c064031183c0e80c504 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 294560710 1250 294559460 294559469
    0x314151305061917150c03160210020f0c010509070605040324020c0a06050a02030601140901090e130302070f060516050102121611010b01021e010f05090102070c0801060e060402090102010b041104 86
    0xc02c0c5e07035012075a00b0703070f800d0f05034800d01070303d80f00c242550f9451544010041180c02c14130304600541d0030f5948500281c0c8050044074560480017600c50700005000b07821500007922901560303200d002d0411107613501508840c00e40b81d0052407084c0710b410983d480180d0070f00f441040c03c032540c004035024034440c00000d01d010409005410520003500e0b004050003c03444291141400203821244041d0001d0344640108280101031400d00400340d55005206036030b03401910070f040b050100e06483c005140e0b0401c8410080e10503a0410540a80350480180c400d210315042d101640094065090500c0703401c0d415104074805600404104d460310b41e0b44200704610703a51800340421a405419000e4503c14071640304802010380080c0110405a006c5081c0d9243d06e80322500190340350a890340d8942860b003d0240590074010000d620340103503181119881101303820245080e13150400401004192a00464000c1c40544005a07500d1101d40102d01411001c0065908203041414224031180344100600485 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 294561960 1250 294560710 294560713
    0x5031506030d0801030b010308031305010608010c0212190806060d060305010c121b08221a0c0c060105010302070c090c0c02120703080304110109030f030314151305061917 75
    0x38078448800d80b070079402800040d112000c00c200600000f27044000558200041120300300070f0710015640c00d404c0d240e0075080710046944403250740328203030b404211106420b60300d0f10041d4202050f08125400d5000303030f1000b80c400c00ca60500420b5140e210a0100c480c00c641c0050103018880e200e0900f2800380502da19003400180c05032180316241d9902d0311030811120203d0205846070741840c441111048800341101091607640080c0492040710190303896456440303107014000000c450a92481e000c003006000303c548140400c4483e8620b0740105005066600134200181c851249007031103d007040e0144c02104403540f520499a052940041e40c41804901c212080c408402c1c5950307110743c03035440c5488018100e81e0284045000075500b603450090841041c90051985552900c81d2807041250b2401070340860340d20000b008901904046407036200e9aa401c0c00a142c01c0701f00041114000ea000c0140c0302241c1e110049800d594660b04030b6050340c40103600801c1ca6036100d100110301ca020400005050703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 294563210 1250 294561960 294561973
    0x5010b09070f02060a0f020d02120115092105030f0c0f1209060403030c02030a050712051006120308041a240409030c0f050703050105040c05030f0604080a050a02070503150603 77
    0x2810721a030075003580800b80780c1c040c144684440c00894090454800d01c801c00d01d400344241c01c6070003154809052101e075450a10000c40d40340180c100c0241007020441008c1102e4907100707000701c4c45600400007401c0da07508810310f4102c2d110b041482c1903016125103400007600004015010940c002110304540b9112810354240f4400300c0d4455440d48268030f061a04030005000400200e80074507036001c1c0c0c80d4009003e41ea05810035944187c01d2209680002500c3e00c50141c40105100d01048941c414100301c5104220050401411034144007494400408210100000608004140248020885442450f0809070074002202441e820a808104160720381c82032641245103020f00500c4000398058450b40d181013002d44500d16041c0140c0f4056580e841907850000007c0c0c0d092003258485c6004140300300c01039040000305402c1a100303003805541070f0710010910004c120103004880c0c0081207801c01e5580c0c0e80c0004010303400c0400c181d0107a6414010300b0000304018000f001c1062003004114281d801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 294564460 1250 294563210 294563221
    0x18010612030215150d06060902030109061a1602060921030306030d0203030c03061018120611120609181002180108040c09090f02120f1e06061507020d05010b09 70
    0x70b106408031203003060004000c1c40701301103081c061000c201850180001090058031051600141c1c1d0080c0e020f00da0b03e40c1d0390380c0c080111150586203240100102107440b49844050700d420017030b890f10101d019100e20700010f40d0f400755680b106000c1505006040c052814003090340c0070a5265041120618040c0c0242e8100d045420305c08000c482c03154a001a0f45411038944d80140543c5009040e560810f100004c40180c40080c1c613224443c00420340703e003c1142e00000340c6401400d4400b400441e050f402c0e810f12420041d082c045441e503070310400595034081c1d60303a140d90303801c000340303c002e07148041502941000042c03004d4207400411841c8010100c06801c0600750004586a203400c07103000c1c02180f1303041d070280402800b6800030740ba82809480329a1100901d40c0000345010081414511254899601c1d042c00c11001e011005004106c84004640c5a0740181000e803544401480c0503c50141c41107050340134880c5006846456402606c564000900341c61b0190080c0790000d0710a1044081c00300040c0d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 294565710 1250 294564460 294564493
    0x92218050c010f1d0a1e03020a050603060108040201210c021005161205040c170c0a05060307050909090f0d230a0f0e0d1209090506060c06070503180106120302 70
    0x7582d00d041303075101d04003022000041d0780142042c241135640030704c5000000401710302542000c00b01c1c040c1c2d00a4000c0c0203265104200303a4001d186d21013030050a00748204400c41e03801800140d070242d0207080440d0b0502c07912801076504003031300c809580d10519000201c00700720390006881c5000030400004001c1d83d11005103003034000040c0c1000c5000104652031a42c40d901c0d2a41010717802c503210b03400700c1c2501d5450303680b02c414428a4030420314480e07004001820b251702d0030a0401005040c01e54900c0d10714248011b0081040c4203424459018180b844082000c040d03082080382e504000840a407406603801001c0200307000002c8403900d2481c101101d21070003003c0d0034002c803104c0541d5030319805c0c0101028001a161714943c4080154002c0000b0013400120703000d03c5a19107144100d0f80c4c1c8401590a1060101c02c441d809007201e8050340040c800c0411402000882e543c01003000e050003900c0c2c0d551410500361001603410041c40719401c006e400101e2080c40e404600c0755600c2034003614001c4440343c0007070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 294566960 1250 294565710 294565727
    0x2150702061902031615200d02070201020307080f0417010501050d0609051906051812120c0d0e070314010507021005090a0c08100513030203092218050c01 68
    0x107507110904002110b0000000c8000741101c01c07203030055a003441c01400c0ba030103c070a00181d061703801601c96465440d01007a03501c255124240340e90f040301109503401c82c0d00f80b41805581100e00056074001401004d5a00070000da51805600130030312030380e401500000ca00560042d2041124480418990070121030040c000c50303051b00c0300a010018442c0090301c911000e04095041525180904640410007402241082c1035050198070301058a041c010025080d407040c10004000d00d0700510242c41380350085404941130507000e5001e07001c0b541c03520701e02040148192950000200e00d410f1501f0030307515000c51076004036402810480320300e041444201c1d00340c990842d080401a00000350700b0210302e449501460b040610385007203a42c0b500195881d4894429160000c061a600209001d14141060301550758043c514840c007004070703507450350040d42d240240402131f80329004100056204007050300d00c0c1c007442c00303940c03c0910450000b4100b08a041600c103005035a0341c0101c050200055006100341d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 294568210 1250 294566960 294566963
    0x3060b12040305090d060f090c060903030512150901090609151d09030d0f020d180b0c03130f0602030910050c0405041e09140d021513140303090703021507 68
    0xe01036a40d615038048a40ba8001414203a202015018240124425204920003048100c00001d020265400c00da00010f84c030364000010001600030506c00030b0340c01380c240c921000c00700d00c82e03141c181c0301c03041010700d188220081613401a402000004010b160354118104680814604105605000301d0086c0240d00764003c030240c1c1ea403007980e0301c00100380700400b1903449907802c025603080c4810341d008031b800d89981800448404d500400c40c565002820303c0743c026618649511490f400c20503594442444070001c0100703681134804400203100b02119041c00131400e900112040c6026101c0c0380580080d0400c2d035607110984200d8800c0c41c00d144a92042c0c50040b102c6500c00ca040c2490502000040c00301c40c104880000e0000c042c01113196100d000f94241c0e02e1096220550303820860107000c1c580318402e010881150701814041002464040380316411501180b1002103130281410440841265614842641e1200208002c810301c07001c5204010f8038801c6480d5030700e0b07103804000c400f214018441c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 294569460 1250 294568210 294568237
    0x1216061806050705010e061509060405160f0201060b0f0c0d0c0c05060a0315080114150a0504111606020405010e030f030a052101030b040201030e0d0c141005010f0603060b 75
    0x2007401124040c1c030103030089a100c1c600206a0744010041141402416107107056844a0302503405070600c0c0c070862050f44a541603c040183d071a020031080840e110040c181001e220607250400d840350700c01c1d00b2207005055101c00003070351007800c0410b240c45503110712510021401640409540c4c10f20411207404182c0d00f10311406141c13802c050400c000c6501c44000d1505166803541c0d11018400b201d02a00002d041c8440006080106504d02c681d40b44402082170303021302142c1000030035554a40d075800041ea041981c0c0010001301100c105040b52140f4034440c40e030950081c52110400075590000c200b501c40030398420821020030700603d5911404c1603562055904140090455244618060216004c44401d103d810030240c86c90855100c01c282c20030340b911007001c4104010755030103000c0c00e0303641c1c0c42d06c60041544410314080201705004502c401004d00701c400e0720711001c0a0b0100000d400307403045a0030820043d651020b840704200414416000400d041c4000003480c0c1c51500250b40300341030b40c0203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 294570710 1250 294569460 294569507
    0xc10180b0a0c020114090a02040e06041a060402280e15071e1509170301050d03110c0316050f010201090b013003181401090e060d02121606 61
    0x401c100c090480081403900710740d85c40e20200d5100140f00c1102c0d0195040e0301c0500140707035031030041c0001c1c0c44620009514a5000000303200005180d161034401d01c80d00d0418090745030b200d110005000e4031400c52003202d001d189420700e8140c03071080b0080042000c2d054440030019180300c1c05112441110b101c095121100910148003c91070388507840058920004241d11214030795036503059000c1c8a80e000c964510303aa40010420006045841858440f000780907070308541c035140c0010b10000c4064402010009454080c903482d210401403044500c030020b003602d024070040d4008081c1500c5900c5000d00c6014414803440c3d8950041c4240c2d082950004c0c1c00b43c500345c4c24000074940d00005160b0f061101c40b17140300c40d02c00c2c0384003244484511620a56a5007d00e6003008207500d00f882480c0c0003500992100200781800b40e03045a03080701224580b003403281c2d46d9981e010018038001d082860180d000004243d100480420215080b8048416450b1407032a0b5900c0350012500092102c102010000410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 294571960 1250 294570710 294570721
    0x6081806090309010c060603021207090c09051e0315090a0b010509040f170729070f08011e080102040b0405090709080601140d120210110705060105060f0408030c10180b 74
    0x19142c569485d0b00440780402d81903540d5000c01c400081c00003061a590304219001e0100061030700032000345009a01d407050001d41040c0004000c0c440341c00e08a840241c0e10001010162410701aa041442e1014042e000510f49004641c3d2103102e41d8008803411000d140c00400c0c5440d2982180d130013207401012482810315181c0d541850100741140060b020402480300c0740018500415451483c629105500000d20032074402e5011610058406070600c40f00d1200c2011640d4441c1d445411104160548810704e0030719410500941a550010740003940000340c041507859a0f00014400c40f04e0075282641c0300d560380c0004640401c0d03140558001c98010380010004181102c0900d82250030040c00440070551760344e60540440244003c80001d40c200803261004482d042c4a400d410140c040300b240d14011040e40c41d1503c401c41405aa0b00c02c1d00003065004030520740c00280c0c6c01400561007100d40d01d29a4a01e003556421902d078041d0b89103400d002410500451508080c3c0b40907602407401002074649 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 294573210 1250 294571960 294571967
    0xa1802030402012a110d03021b0a03020307150f091a0307030e030304030801030203060702070e0a090f050a08030402040f0902010e010c060f090c080d0809030414010c0c0608180609030901 82
    0x381c82641044000e40d8800003607002501c02c036446600e04018100e0076400d0b4540381d001011400c0306503105400c03450740344010a070045100401881d03089000c0155a01e5400026140d0840f604007941600c114080450002d00150000c0340c42086a110654081c2a040086680100b5801010000c914060300424100c0b0610095500090700b4100890744046441c102c03072640e01304032400c0e8006020030004200f507042c20310070160030800510103484005e041480c0380d42106409084038250540e110070b880b06100c4482405a1050b80c0701082c2c5800b10158101031440b500143c50a074805e03898824401000b0a10b48542c400c03859040e101d803240c0c02c0385580150b0301419800c505841d0561200c1040030140305520500300c0701489032003076616490900c2030359442d01403224080c106114071541031000b400000801e88007110110720300e000c04a415100129401c66400d000104101d082403008101e00b60041c005603c580360b448171550383c5a120800b866503e00c41603e00100b00c0e0401c000c0c0c038000c0e512 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 294574460 1250 294573210 294573217
    0xc1b01050d050703020d0f1b260414030310090c050a0c1e14150f04030915030f020f0703030b0904020f0112060305063904090c02011b1d0a1802 63
    0xda41c14014142a400c06c04402560052543c4025165440340b01d10352400d0340300f0340f01485020b580f81011445820b0040b0040c0800b20034115008000850002000c000d1034001c412900c1c0707a0a03055903101c2c03d141c00b150300c8050b158042e42d04034609042e41c40007074038403407c2940d0703044040e41c0c2d594004090589a2103400802c2c203e04007400c24200c1241c2c0302040002525202403460704004200ca89000e0101040e6088003808192042d400c000a00c00401e6021030200142c1d40a807440c00280d4140a01c281c0003030903211206a100c0b400450f2120f83e812041015045081c040e4405010440c107001c00c22445140454000b5400710501ca4207a84035442140302d425841c100c0100004d115440380c40305864400101d51060b0729010350702680500c01c6d580d120f000e0000c2441d0300030004269000c2240c60250165003d60300c00280d603102110300240c400d40084007010705100341c044c407809000c43c0c010201610b04031400e0034001448803d41c51814644c2400c400c07242201c0040d0459400741ca03a07940a5403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 294575710 1250 294574460 294574471
    0x10b12070f0e10050a0e010903020904061e0f06050a090e121e040b070c121a070c0f0309031211210c0d170106090b030403120e10020c1b01050d05 64
    0xc40c8070319030b41560702c070340b0300803030001480da266581c0302c9003401c000400c1c407441820080d04000e40041d0800050b01c40300085a0402e03130216010504480d144c8003400b18824842852901d0340c1010300c03074184001e07140d2200c0151481070f01e404502c541c40e5140c3c1d400341d41080c15100e9195000a01c5407054140940241407114034028443c00d80303070b02c0002400495007085e0040e41102d000040c6e92010449544074080c02004103290198a0740707040e8a1722010101841c0c07c4541416043c0d0004241510403c07401c2c55240d8054410f00d1024250704005201008078001226080040e00c2c0000c1558010754050445815050040490030721400804000a5441c0c1500080700d00602c940c00160b03d0600c1540c540d0181981c400743c5030034618511000001c01a070040f0b041c00040e4a040c4403036280802203950007a090b04062203002c50310400755006007900c0e10491900e000f00710138012908156001440031100324821146c0840c0c1d00040520b4141c0300f0301e0703600c1c08240100445045120942c00c02ca5100707 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 294576960 1250 294575710 294575717
    0x3060619090b0408030c10061d0a0207080403110312091c0203030c010204060c0c12020631080a030917150a02090d03030b041a060412060609020c010b09010b12070f 72
    0x1c1c0d03a40c5041c5440b50b00242c2000005800c0841c6101481c5c20401034040000580d03030041c0b00c0c00703280100c041504684020400300303105038800080d800c5400ca03011140c82c56070201c85a5940d580c1d0781010f50240102d0038031640b0900440350030001013421441624921100200004408480710400b000f1442900f042260580001e1003140c4c1940001c0c40500020b089030703211481c543c441031400c2450600a50006084010b0b84281000540c49a0007551403015a156410080d072194240c0d81a5140c80280c40322407401c10158041650400424183c0c0800d02c69141d500c40307203440b0901d0700000140704900a400c6d50220400050080d01d8103c0703a40c0101001900603c1c5c0400c1d840070032222140d80100342c010940711001c00030207003840c2c0b080c00707214000007000c003002da44100d00040b0580b146108080782091b550715910140101c1d684428000c002400d0110765564202180e240a061203e2105110322054400002c10514050031100c1616072002400f01d9540c40318001ea41503410180d030707076041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 294578210 1250 294576960 294576977
    0x30c050d0212030403060b090705130e19050a2301030209070c0c08060c1b0f1e100513120206090d030207030905030d12050705040f1205010207170301080601060503060619 75
    0x10a0303018001000a903006e041c0210b142d800da00d05000c0d02280140505040050800020054450452104003035803141c098403149500c6880e5034815051802d0448124946003005002d0640d4556028000d910800c000c4041c000c22030780d00e00c082900c024030019400c4840f16002170314051082240349156413007200c180c10540d032070b040b00c41e01d00841107403542030003080015119034030301c518403204005400102c0201540c502d11803c06444090304d0b11200400d031a122000480000c080c03080c0d0320f0148503a02d0030402e51405129030081d8414800054138401d02c419181c003081072010592500c11841c14008103160044003804400a41c003c010941c2044610300c0e0200b019501031007000100c0500381d98038a02190648842022070718080d00e00001e01c2030400c0100240100559041e003103c1a01c000141241d181d810710b580a88102c0500829050401d141d040010303d0000240d03040e503d0700c00840d801e603030300c688040c3d90a100507607200e40d110606001c22941c048900c80314401040300c92808603030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 294579460 1250 294578210 294578239
    0x51012021b030a020322080a02010e0a08121e0309060103030c150504080a030608010c0c02120102040f230103050c03040807060608030c10270311190303020a1701030c050d02 76
    0x543d00110f04020050700001030802800b4840f064030001c0c070205141c039003900351070603080c141e0362003400d5002410310989207a07200003036a80062010081524400395029047c0754141c841d0580e05c100421074201c0078031101c5d03442c0300b9500d0082e04d218105080084c0b130301ea42991015250200300080031103101c40d8400c815207808455000c3d041c0a944101111340d201c106192029040d47c140303401038140c0c1da150100400569038007030300c102c403416016541428a01c9a040768a03002e4801e54001c0583e000301c1841c00510141c680020008207401c208040003140640001101074440a4802038100301d81031022030003296501000b020302a1103400c0008519507180c0301c950943d0020741486040350405466009000014003440840c0e0f4a0100000ca611450b005401c0ea108401040542080032410201c1d40c141403c22400640028107010001c00346542d2030000c0181d0b01140003c40050460904131790107a00c40461107050b0be5016481000c424208028070a2041e010344062380c0c4003009111004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 294580710 1250 294579460 294579463
    0x1404080a0c03020f090f0c07052508070f050a261f0b03010b0907050306010921030f0305040c06050a02150a02070b132105070b0702010c020106051012021b 68
    0x15200e110300d6400415902d1801080384182c04400c07294003c0c600700040000b1000d240c10541ea03c034124070f0500d910352155040507441c1c124240402601e820101084c0d91409060400360b50403101c9040488014503295038410384c85070b4881c4141a0403000400082c855841d020300440944c00080080d00c03280d0000c805114901550000b15418100074036000202d11002d40c040e00e001c0303480030780084c460024030001148912700000d0440c020044080041040f80c2e11664020004100c01c800c84440d05440800c00113800d448110101c012900140740d2140c80b40c028060144a2504200c100781403a2901c54262500c0e40540a41811130003481c410b00b0840305100042405036081441c0161500f4851804500452000d40f0448a00d8450030041c4005113400c0808100d0603040d90414100d00711510080e179240c0100c1100a01c60280c00c002c02607060380c158004024121294000d200080e60b072814411001410462000010140e2030082c2c2c0c03500030740c1c0003404a000c8402c0c03180d954034084903016 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 294581960 1250 294580710 294580723
    0xb030601141201051201020405091305010b03030d020a02010b0f0904020d1103030a1d04140a02070c03120203030601020105010b0901020307080306061318060902090f0f030f010c2f060601140408 85
    0x8090314030b00c000042c07140d820036468102d249a0070000851600e8104000907503500001000c41d45600042c42110342006029007203c3d02c0100c1c060100c030740b07640318040d894001e50401c00d03640e40150300e42404020079140106284842c4000500103c6d5147c41d0303602400b200c40d0408205940601989036002d01903102000184441452550760043d2800000080c3d1503800044801c0c0c0e20560030040d103002000524100306810200c0d840c4016900c03a0031380382804400440745e0019140e01813500c0d0414403079030080011807048000340c3c02008503a8a40300c160303800340148c0e51042d00681c0f040c00644000f5203e800199008280103004d42d0400100c0d01070b4039148080740d00084200c030345110b4020503d0005020f4003015004200d0107500305107104001c18241450b070390700d1a200d44207034a11489151014880c1c0404c0d441c0c09002400f001d403041c0d1000c0c040c0c5800840103440c2011181d11010540440ca000c480751170003d0014040c00e480d40da004503150769900c0d03110780c250300c010000003a4024040112 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 294583210 1250 294581960 294581977
    0xe060f2806030f0c0905240d0f0506010201050906160e2e02010203090a060902130509030414031c0e031509010b010909180b2206090204240b03060114 66
    0x41940c100d0600740014159030034000c030501403d09000079403440d641c000c3c00c880c1c20b035403003581c1300520314681d0401c01001c0c0c40210600120604001500b0320300c0601600000030100c150306040c441500c8450049003240c6003210420480d410801c041441001008503441c0034030804d1408034880101e1200281d2803138004481e11132070341e910b205030080070354249103004054850b078002141585070840d0040d40315240e40c0c400818503580d078411401155210341d051041c032206460b04110b10301c0c0c140d8440e23680c0c4c1d01c0f501070000c1607245154044210f26000030141030522a82110b0011040a00801c4d01e02404001125615009421645c41e001414004551007520514000705030400b00200241164025421600d40b083c01c0c00c40640e1549038038400c28074000d6100d00340501a5a64084030148501c54241c001d04000c182002c2c5010300c180345d0042c50081d4001c5508200b10860f9540c1d100700c159808401c0e41c038030190300340104400d041080c06154024418140603040804501c81c0803110380c44400c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 294584460 1250 294583210 294583279
    0x6160509030708030d0c080f0f0126030c01060f05040b150306040902031903030636060b0705070e01050103091509061401030605040c0e01230a08030f071b0e060f 71
    0x713224030250746c4247c4241d005250400007086a05050320030200380c0d2014003851350310841481c8140e00d00c2401c2c00351819044405015203464540c0c41005a01801461051807410b44505e140891a4036140c0b181c84000c1e50001e0045420f140590300811041e000100034503400790b0748800303170f802684050200070204041444104054807951a003c1c00719a0207411110a4801c1c0d15400080c242d041c02044841c404403040a0380303804074403040940034003101c1d00710030b807a0303200822040c003001030000d0503600344d55040404513251380e00d070030046044419295000c0e0540900d4203183c40908a44d41c8070f012003034007a0340c0100d600841c425070018090300030303481101e0082d40d42c0100000c0c0504281170384041c01e0303400e580015a505d08040300019501d00d041a007440006250b80f410b02d599007506160090507008292a2100100400c110960f00020700586260340307008a0400706211301000101074410401d084c104644440040c00055031041e8503117030300606c041100c41110b01d445454105040c080f4007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 294585710 1250 294584460 294584471
    0x70203120301090c0e0904030c0501090507080d021e1c020c060f18010e0f0f1f08060a0b090307093201051305011d040302030f0d0b040b0306160509030708030d 70
    0x140325034203c542c849004c0003005080d0020494581d1180030483c1c000d0740600d400300c5240d0b080c1c00d14034014450410000c016204040300012000c0c2c010489004c070880c5602a910070340310407098412443d85001280302e0a070000f000e074000308410391905d50b50304820361040700e15205031103010442c0d0350b021050282a010011034540380388151001c08040041082c681640c064070610301248984850300d160502c50021300c1c0600c94a5103510300803a00040325130b0405002060280c001400f00c000036107807107001e8103130620080b400d4038a6500702d0f031038084050028181145010550001003100c44500f024088000c00030344840d184903007003003030706244a04002100303501d8481000030303030072450f00301e100c0907420032004002820280c152080d1a80b10405109200d945074903040341541710740b0043c002454030205007080306090592046038505e0058600b0809180325008160780d5502c00c850a50542e00d0700c08554050307501c168040c000b4a031b000b03412201000c0d00c6c2d428050541c0c100c400301c010300c81da0b210b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 294586960 1250 294585710 294585719
    0x60f021e030403110d0201090902030a110d0b011803081206060c0d020d02010b0a0315020a0509211522021f1710080304030803130b070c02120c0607030311070203120301 74
    0x111000b84c3c409030304441c0944852180c1d030011f0318000c464842c5421460b404000503040c03030403c1d0000c4100341034070800d5540d01d078007010f9058010090075245500051130a522140c0d00700c590015075041c0d076040a002810812083c0600c1e0f065030008001c0c54000c04140f08640c5821820404030404d040d15070050040041d8441d0b00a0840e480f040b18544520b9000d034042022030500d03006108000030148000d071b59030f5000d400a440c1481040d03182c03504260306811203500c83c4100350041100c1c01006080c1c41d03404508061f668413509041d078a5800706041c203c040001c401e8200b0f90010b9130f51010700140c01c04401c030200e5900348441880d06101144c540740e200030101800300c1a01d40e111060220031101c80e818003410a50340d0041e808000c103034102c00000301c3c0d034002803250802c0e003180c1e0000d03032009240703000c1500408840301c001040340a141d044201050010020928078001c080141c00b850030003a00d0744044002d00480e1200c81046c8904108d60390140c0c405108621046168528641d580d5141 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 294588210 1250 294586960 294586973
    0xe04060515010206060f13060b1620010e0d0c03080f0405010801170304050105130e07170906160f17070c030207060c02060d0b03030c01050a0b0406060c020307060f021e030403 77
    0x5141d07400d0454001d00100085541e500001e1001c03c031003980d444c4001400c46c020300c070040c80340f078100e4144410f0100b5880724031460301000f8a6000d00c0303400407001c600c00c82c42c08407503c008104015808038081d00c185003c0360800d43c201a681d03500940540607603903500d0b11000c03070552114882801021707002034280540d50f00b003091a801031070f8013503100401081e001103254580c0598020075041200c00030308940e50340c0e405001e04002e86040c004030f030b115081405014002c0005441c40003c10446030740062003005000c9401031080c801042d0030f20889c110004101c9061514030300141c188160342d100741b1580740550252a10441d1a42c86038002000d007810003030b1404050307900032000c104402840100589030802034594a0b0031005010684502200c006420b50041c00d0507502151320300001c00032840016040b402100070140d900b000b0f00c5031600800c681c85204404041e405034011902001118416903004900c2c0381d840c4160740402e103000318240410061402c6190080c0c1c1302103000d00c140181d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 294589460 1250 294588210 294588241
    0x3020d1b0f1b03080601020a060c02101406090a0507120203161107030512070c030203100b0a080f06010e10260d031b1d0a0f0e0f0705160c0e040605 65
    0x4a03410801c0400342c40300105084200029002820403081c600070405a9000f00640701d1416070015080c042c880b40b00d20004c1d0b07222030341da00c01d03800356080c021004400011b002409001c2c9101504903106030780d030320b4504409440040c102c101007041030071007040c004a07944082c5020301c8403820b04440540200c1d80080603251902948045600300e800d007000010030001e402c40240c81c21489094407559142040e00d40c02103181e202a426018210020103945010750081c412100115034180f5169261554a0303520810184270760b500b0340c04000144000550080c160782d101c0c00c4a45c02078072147d01c901c40c282c141e080c07003ca52a400b043d03048805016520901550490000c1442d00300609500401c132424002d180d02071080038080240c1c5507042c40b02908007010860070f0080d001e1084c866840e804c06224613038912580103100b02ca034010985146500300101d028841d0766840c2400d02c0e0441c200d4600e5076280e10030072601801c0c00f440008076a100b000e002032090340590700c0020603262501c1910700008c3d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 294590710 1250 294589460 294589487
    0x60f09032503061e020406050a030c0f020c300706030b030a120503090f0708030417010e0309090c210603010c18061d0402040b0703020d090302130c03020d1b 69
    0x44140386800704078a0400900812203030008004900580c44009021940b07661000083c0300d18000280401c030320740c010f0b000703003001380141d40c0c100861042c250040740d0380c400a500700c0380180c218400840c0c1c03d00e491418010490704200c5501220701d5952017034040e4814a2020a01c02d811002d400c20160750984901c290080c4240c01400740c210040d520003c0c500c03180318500080c40408008540c40e65002c00690107403800c1101194421910396824a660b50814810100404c1c5407112507454407c040c0101c00710b0b26684002075090001e148104401543c4c01030008070400e5061020650020700240414001080414000b0840c14580141400c0d20091b0386c02201f407015003400d0384a944050244d00382103d40c0d41ca02102c10807203a00c2190088100000b41c00ea00038000b24011441d00c91b4100282070052098084415442040740d00f038580705000e01c8060340c0021030301480c9000092a80141d41c1d0050300c0d02d4010700d40040700e11601c0440320b0010344406200c0000d114251500e8001803030180d40c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 294591960 1250 294590710 294590743
    0x40e0603060109060305030307050307271503020408060a0c020f1002071709010f030b03010f09051e0f060601050702060904093c0f020d08190f0503070c02120705060f0903 75
    0xb0303800c46d11565928403028061100f00500040000e4800380b1400c4015010071260209454400940041a0300c108041c0a584224000010711440e650b006c1e200b00e4084994960240a955407550a40c800901010036044194010f18110441401007440032100f401140640186c88260754100089a81152500132200082c200089809030780c01440d1114498054030f4003140c0d40003040302013405411041c40902d5201e040c8440c82c41009008a03056059251407082002c2c0340840003100340e42e42d1300325120000103410050214000d540325100520502d4000b40480745003001101c085001c6400d44041a5642d0a042e070018038088111210740c80448000f4840c4608921500c0c3c44500080c41100f000b00150b20b00780104085444251901c0c4d0380300e821440700c540b01d1115030706031907003c54481c0480000400404041600d030f405607003a00d000740d0582d82c80e02c900044560901c11a1088914680c0d0b0600c6144800900d07980c0b81002807454110401e0303100e03101ca04050515181c03117078803104400306c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 294593210 1250 294591960 294591971
    0x30603030215190e0f0c040902090f04020a0b220902031902220b0c060f07091e050603090a02010e0607080316030204050301140402031e06071d0402040e0603060109 72
    0xc80e0380040d401d503044a49500007141c1d83c030f4450441c5480002100003995041c00c26801e0242c0c1d080c04203a521800c0d80e603905444817402d0359000c120482e658001700a601903881d00105055a24a80f002035009102406c210091170f107800c02900d0310340002081c25400303040b0070030003841c800500c801000189480c19081d0304509140202d50207881c115000c0304902540490000003a42c0c010b560072032400009002551415280e600036091940000459983d51268001081516201c144804c0c454212682c0704031100741132640081050485200d00600800071070404100c41e640d0b072006600410054005140460842c8005001c110340c0d220382901c00d240620000020900c0031089a61040e61079403245024021200217034020f004e00d42043d07406602c0c2c80c0b1025200380e208800c090085000b28115001100940f00010b420065446940f01c15003100700841d150500480462207250000d41b1001d410b00550380104089070001d5000815943c0740c01c0500c601810709104107405812006000c0c0203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 294594460 1250 294593210 294593213
    0x20f12041703010e0421080c07060f0212180f1c0513060503100b0408101d0a06050a0b0303070f03030b010207120f120504080d050a0c1e140d0e120a0f1202060106030603 74
    0x42d215002345000c0d40103600058071000c0192641c0910041c0510100440d1114a07019020a1480c400c45007101040007040c00c1c0890702c03000040541060504030006c24012070303049031911907500403a46240a004081c042c98542800240d0408080c200d26955541c80f49000c8081000222a6a00000e222801040203200000002c241080d000300e541c2c80209a94802010048030318080400700c0b10540220300b08034082241c1ea8204601071460246d0520203021078008250700da00c12004000d045061144d08040000d00980040d030302400140141c07a03640b955114042201d85007047d0413541544090108420407080c1c40025070071b41e400c2d1134258241030600300d400d070b034a240320300e9800f052000100303034084643e00c50b0304070310002c0ea031000027603182100d0130126003004000083c080381c6c01c510703000e0340340008000000c0511a1701e400d940c0da0b032010072041041c04020007242e4807a074900c3c007850b0415000b0410085500042c2d5101d031078820308001d040c040080c10101d040e0080b1040506010b030400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 294595710 1250 294594460 294594467
    0x2130b03120309070317091306050603060405100b041d07020c010507031809060830090d05100504080d11130611012c0c04020f12041703010e0421 64
    0x40001c516244001c1c0c2d280c8a000015142c41101d40c0f00030507400450300c4403110406004007030304540506071210040e43c00d601610800f50344030380c00b506070815030038000034007186865004550000107004880b0001d82d04c41c04980e95036442070f000705040000022105107101201255282d0245980c4050603109008400090140c407a00340c000d001c000b01101c814409050001c081c1c030041c04014400c00246984005113501d030f0000300d45d505004140a42c0c0304015000c07580485600702205041c0c5490110703c2400c100c8030203051607081c0c0b01c03807194200c02586040b40b031080502032070040302d140e42c944000d64140010b4460151a0034402502805031020706c4070740507514000d030354403424000c00040d03084841a0050010700315140200c80541420040e129240b000c56110349070003020340c0d100202400502c000e900c40d8842000c611b2204000d207065002c1e11400381e942251240030080c15440341080880420340080e041101001246020b006c104004180d1020b14048030021010700c0880700d44019 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 294596960 1250 294595710 294595723
    0x14071404020c0c090a0f06031101030e3f04090204170d1d0118030b10170a030c1b080303010f0e10151206030605060102060117062703030a0902130b03 66
    0x9070040e00304d5000309072540c0c0190820384200b2815903080154a9403401e010655105504030103010914100d0034140e000700114020030781c50010040d21026680e2001a101e0003101c0071101d60068000c0859907608801c00c40041c801403403110780150f151030400300b04d207030540d103211042c16007a80440440c039030841e00720711035100c1d8001c1107034400745c1074000ba801613440c1e50700b071440b84509035110f00d008030400294040c09402a4101c490301c25103562182c1c1001c142d290440000d03411079201c070071000c0000c5e101e20b070f0030468a803140c21100d00100b090a040d4661403039541111080b9000800107101240d034070000d840041a58003103851a904103200d0b4210742186d50b029408031910458003d4881d0f50240230040c41c42404a81d0070020148d49040400003445d09070360031070041c003651000203043c40da0f800380c00411540502c05000c03a0744540901d5581c4460000c9109000303080140040b22040b0280051072140241c40408a640c01c550b10401031044070000d140300036940380507a000c03400e07280001c50 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 294598210 1250 294596960 294596983
    0x14270303070c0f0c0308071401050a2d020c0d09091116020906010504080f01090b010b13090203090c040606030903090b0301150815030102160c0902031b0307090314071404020c 77
    0x100f842101032401c00180d428141d0700050058a000a004010030055480860380a50748070000c00803500e50301c03520fa0a441003a450705003401810b034400400e00c0001c1000c180e20301540c800062410792019410350070041110194004290010020411b040c042c4c05403101a80d80d0a00c01880c00e003030206000702000200001900590403039001031010b0b40203070100d402925003041103400c034851840d900c0340600b540c0e2804603504172282000043c01c1d2031000c01d03179074440711064030716175003a051081c02b100a4200401c0300d1079900c00d0404800176521184101400341200766004102031850b418003801e41d860030350004c001c2144c2000100042000d03540c0902c01c501c3c1300e00d8024016200e0200d5000321014903042c103540355100050110318400402400c4008d244204002c0c00070315502c000038000c0f400b080310031a002ca110194000c0c2860b41110040d5804000da00300000c180e0f40380d46549405256240c00c1d01000d17070007030380e0620010000385968680180215015440c4c070801148241d11007540000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 294599460 1250 294598210 294598223
    0x61e021603060c1215140d0210052809061d0102030a030c0509190302120307030804061d06090f01060801021305010c08040305030d020702121b01110114270303070c 72
    0x182c080f1554410701494240e0b803401c482c144440b0010444400580c20703d4030a0313060303903a1400503101142c00d0074881034044a03001845a0145e43d0101403c0d900303a8070068104101e41d0740d0048e00b0500c04591048040c2941d00765651250150030120041e0000b4144005117854071400a40c03021282c1e03000048a00f000050b1401040001a80c0025a200e01541d80000d40c00280d1001c030b03001c0c601c44516413030b040f80d000701e80c1c511101220f025115124403c1400150002c0c2d016000100420450340096026203410092111002c2d44140c80e02d0500744d064405140303e401003034400454000134011500500b2a140003140b4140032013030207036603907902849603c0c103002c200141d83c800d0125041c251303402960000141c0750750395080c060403402948500802c80c80360323248a002060200b0002580da0441c4020b13090380751440c0c6182c0055441024009845502c1d41d01c0b41061162560982d010600441c0c618001502000c1e1508039025006180045c03608207510510411940c2d5501142c030084442c0c01c0344 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 294600710 1250 294599460 294599471
    0x91e0103080a0e03010f0b09130314090f1002010509060c040b03150103060b0a030b030d080c0307030902120f010501051512070305071803110405011505041403010b0406061e02160306 80
    0x502c26107a944500400c103500d0351a0640402094510360448000ca00c81101d4501d616510089160400c41201002500041d20350180c0511504440e004107508200104041c08200c4007200084000c513031011aa00140d445c2c809001861808000303150700305007003070340d2542410f0400002c881c85010042038410000c0391031030449450b034080d6000001411100c0186076aa16903050b0140242c000b002c4814001c3c8100381144031810700c0b0304522130042c0380c05040d1510390f48414400728050120700ca400c2c0c5c2c0c0300081e0b9242500880d01080b040c10644046400400c0e07543c50310040200f903600b03909200e0600d820400c43c6000903103440701c2c40c1e9441081ca0400169545179a001100c070140c80c40300c0040761890b010000300501042c0c03014000081c00459051007181e8031195819003503484ca0320781c41d01041c410700c004c1c001d0742d400a40c5030500503006800001c8804210000a081c2d034086d521107804546004031994491070003c04000c548401ca000074807000983c03c20444039044c0c070740700c091320642d500c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 294601960 1250 294600710 294600727
    0x301180303150f0f1509051809121308060f0606033904090e070b0405011d060d020301030201170f06010c02040e072705010e041707080d0209091e010308 67
    0x20310b51400504180d440700a90140c039241448115041c5008052600800d038000d1500c0600c5400c10307000707494002d4082d1050301e03406d5182e45c1c05d000c07003c0c0450001b03000c0e442031031090400304400343c1144444840018032491510b00850704200000d04221000d07020301c0100101900c494085a030401c500300040b0351002407a050b00141c480410020710740f803c00c0302c25900c81550510337015100b030760308a9008000d81100d218038155039081c54869600d01030030a110400c090346c045d00142c000c44000d00000c00c0c1d00c0c9403010002d000b541c0b0040707615004942c0031005105550f4061180d4030704118080d019003650a001c1c900baa80803400611007070402c40220058811074541d6004110a01d50310307001c43c1d01c501e441c2c42001c0380078280403e207061684002c04182e801144a07000e150f0480f10200d240d03810715140c0351122010607103200c000035202901007000c0400070b40790301c000b4001c1c12000800182c8901103001000031072003014101c0720710705017041da94401d45000c3c01d94560440c1d5004203416a98ac0b5007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 294603210 1250 294601960 294601991
    0x1060f0311030f030a03151d162303160804150504060207080c070510030923030c1b09060a030206034c1502031615050703020702040b0301180303 64
    0x2043c51814080415090b0089800d50042c400342c0c840c5424a5100b01d8803080c3c0e40c51015640d805a4600150003000701d80790360765904c5a411400100e240191030070f506850350b03130714500202c1d510070150080001040642e4010558031011141c0750300c1e01d010541441c1c1c903001000140c04280c454044e540b01d0100e410011305904641e051070f408411070351183c40c00d400e100d44440862040710b00074110401410300440c82131007000f4806074003440341901504a00e0300440040c64145000f4414402004800362001c8200304800c82001c9452050181040541c20312200020241035a40900c0c2c0d038040500050750b4810580358000c214504034042c900b407000051036192400c00d401c240b01c10f24601c1000c0c3c80341014031907810b4901913540c00300381c0c1540d84001a81c000311141006006820501c201490707410302e07180c050525806800e004001803849400a422160103564800229500050b640111304042c01841c0645a00710000c1080410b130071503219040c40c0404000b000c050303a408020000b0703800c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 294604316 1106 294603210 294603223
    0x1e0b01150516020a0e0f07110a24060306050108070614070201090501080901090b13031b0510090203010f091b120305040605072402090a0801060f031103 67
    0xc81c003480d28001d20041c00708a07800301358043c0004440c0b030310341c28180c014000c1040506160500c02401b42210351101000c1c1c0c030540125040e036000c124207401681e0005e81505c0c01000250032000305070000c000c2e5402c004c12441ca040c00200b0341c03540019403401580c855454a5004101d80100282540034030a802030001c3e0300c7c0c20b024000f41d4403507030324550810025070010a9507034a95403200381016080b00c00300c582d0580340f21030405159000c442009101c030400ba507441c01400a80300c4589600c1e03c000d80184490300e6800d85d9046440942c8804900d01146808214034491460b00c00340040851480c0480c0701c05880c1c011030700804000c001804d00e80e01d522454a850715218090b01c0f2900490001d892500303010702c032080c9054807203450600481507000016520182001080071060003a0042122a031501c00144520080e4000100c02d5a420142c1c003400d8400b0310002905d8041c = true := by decide +kernel

theorem cover : BRFrame.Cov 294424460 294604316 := by
  have h0 := BRFrame.cov_init 294424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 294424460 ≤ n) (h2 : n < 294604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
