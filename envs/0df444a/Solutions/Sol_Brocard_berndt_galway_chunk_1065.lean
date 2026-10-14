-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1065
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:05:18.447757+00:00
-- url     : https://prove2.me/submissions/39460490-7c34-49d8-ae38-9afeea293f87

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 191366906 ≤ n < 191546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 191368156 1250 191366906 191366927
    0x6050c0723030a050306041d0a06050714030109020d240303020f16050607051609050117070806060d150510030201080a021603031d0d0e030c061e0c0f061303 69
    0x1081d01400035450314060020940b040d165032810b0081d100d80c1c903500070500400c00c21381c1002c583c44504850301d803003031001710b400e002e428010700c8244084e07501c6040c152840341024a40319850344007080100325003015035010341802060484042440b015401d20120304115802080000314581c80c0c080042540400ac00390141e00f1440c050700e540710f020051058102c00f1807140501a0304009062010400103005400400b420101841041900d03a000c14004113024040c0314070004208400310840400040d40d503040f104400020045a5103600520222609814045070800e413014045006600c01d4080c0d01d201e28036103201440311b83d00c2d5000051002c800078042c1e8403124810052074145446120040000e9501410080340c007a11103810800118500809080f10380141d2606068256000030502e442d400e04808455403d00c0c40390406c401c9209643c2042c000c4c2c64806008100c0300c92900160103040c4280d02510f008903541003c40e0700340801155a007150352103401c0c85508040d000045902c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 191369406 1250 191368156 191368193
    0x90b03150c0409090807080a0503011814190f090506090d082401050d140406060602010b0d021302040f0815070801080a02010c060f0c03060801050f0402060f0309010906050c07 77
    0xe2450034060032034001403140e4000e5041c0241c8892000301805101001c4800725603219440359611160f20300010305d9a0001e001c1c148040d00d0300c144140141103180244644400e89104803040e9840d055000403580c1c2c400c03c054100280c56840301ca407024131601c100300c2c10740d000388040c224601d0310701c0c000d0341070540e000310000c2030000600034020908154401141c2801c040b10400501e25031420041c0e541e4010740001080e80c2d820b004c049a0703907034808400c55010343e10500381400304540380d0005034240c894002103142c111278080b0700b5801501c0c22030310039048890341c0e0340b0052505481d48418070202c6800e030015142c981c01030444d1107580961180c1c6641c000010702c1c14130380e19410301c14110b4680344a03403400790400506034204000c0c40215032111591050030350040001e8110024007070050701c1c42d4808c481c2c1d03d51810001a102105070b203003052060f607004100c1490300840d418080019040580864140e40d13130381c0c41c1c26000481c2071040328040c0030800700745501d513003182c5031240142c410f019085 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 191370656 1250 191369406 191369443
    0x603120309030a030903050706051302102a020402071a070e1e220e07230105040512120307030204090b0d080316030e0303070513080706020d1116090b03 67
    0x1c01010008010fa900c2d0412526011074a00c4580c14101c4240c0900c1d030000d04190316040910080300014002042014402e4440b002580d00300701095942d4600500107620110320084000200030302d05004001c0d480c402040107003007100c15141e548100100b940c00800e5000c00714140021580c004241c540b604404445404541d411035407043d01c51101c0791441405045501d0365041070091100c0c00643c0c55502d010100181c041c6da1101c0d59031003440d03104110050030708001890003074490b083c91a00300b940603160203140c5441c00c070601111440140003424103018109902c1049442c1e0f034010340c05100166800741c3c13a9405c220910084840502a2500c1040154941c4000454030015030f6030014100101545d40030840c00c1c00e40140400c0040e01d4900d000000802200a4011000c0c1640c20841e000c64580c15807551507065035018117000740d00240c2c4c0312000100e405481000c80c00c4118120800303641c07116880074000c541302162500a540c0e1036440d008513580e603080801c0b82c000c1507515050f01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 191371906 1250 191370656 191370661
    0xa060305070506030601120912120b0306010b0307090b121b0310140f0a030b0405010506010c0f12050910030603060b0a03020f041a100c03080f07211d030306031203 72
    0x600799180994420980604800300015625038007545415100008404003840b100c00c032841c29110418058401a0106519403100c805161251042440368440580101410390030040c6820461304020041d1003045140c5501080c1c040000c006003000b01c1500640911605112145410001c0c18042100c240401407007004000c0d0068050307642116084400c070f02c0415018808503440c25584100e013504000f00c02c43c00003c12500b403400c41c1c861801000200b2680d00e4410044036140c0461201811206020305124081440b8140c1c1400149090400c54a8900d082c1d000c01e0320544100c0041011aa80720410818400305024070b0002d8241241c8503d5401e00b9903000074030031100090312600542d660005050210410ba40084481e40001c10354901b800c0d02d10f01c000c2100c0c507601000c8002580200c081007000540840160150b8455120301c401c5440300c40140d944c440f158aa03100d42d007030720341020b80700300b94510b41506c01240039000956546d20b8180c0c01d043c903082d000d01c5100d0f60350b01c08104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 191373156 1250 191371906 191371913
    0x70806100e090303160e100509041107031e0302130e160e032808070c080f0601050f011d060d0f0b1c080c0c0a0b030420010206070f020708030c0609060a0603 69
    0x2105da11071000e01200c01d9880b5600c2045400401010f5aa50059030501c942c118480e00324010384550070040b1018404040c1114a1000b0303800b405c1c00080100d026500100300c0c0116154040d41c80c0f06c1c4034940142070400f00c0704142e0320318009601c5580c2448007002440210703441850051079000160070710406148038540400d681d100b449909046030100c106426950015101c080700b4000d81182d40c1d00d403034617198140303800d00d038000c0d00c116074180c8603034541c00410300400b040ea28101e0300000e000d100d00c03595402c015208060044a104400350844400c41c9050b502d8030040c00d40c0358080c0d4400a081540301603045c0440e4245d02d645403081d80903261600031750741e0740d40c1c3c0212450341c02400c00e600c641c0c42d960000e140600c01e521032a03004100b0000459a020010301440c8594001c648002a203c138140d00b02142000403aa9280107070400c0c00081c0256000b1003207482d01c01100d104440050341e0f038402c0d103403c0d6089070f141c3c144140c100000748040c07014100042500111058800c00042d8910b65 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 191374406 1250 191373156 191373163
    0x1a040e0a0b06060901050403060f052e03030804020d17030603100b0d0201032007120f17060f0607051605100906090e0c09030d0e2407060b060705070806100e09 70
    0x2000b403441076100065449071640b01e039051340d004592100f403d1050480904400005c0c12041340d0705c0d41c038080080b1001c5101202c2c403900d20f0f100c5928400500c2d0460031510112103a80000f00160381019011801500041c40c00e80e1000d805052881882c1d280d0501d0f034101403c000500c1c0204560078103045e2401902c0c0c0e2601e01c8030190b640d090a00080e582e910b0b440840381089078001310384a500001c180101072165008280400e03141070b6a0f0006110f0b4203080c26902c80c0881c100102001040e0000644103086c034400400b9000300041c03441d8140b450690f9024600000521640c0b0310f0402100c00b00000d09110000814243d01d5007040c203540c50030540020098195442130011044210011510607840750b0101c0708280c401406a031042e6408460141c1001c4802c400d243c0507500d10360184c2d800b1141c1048014004000720074043c5801c0d03043d1540c01c050009505583e92000c810800400040d00400c4681c000307009003000b030169440c00605503686503078940d0265078100c80c03d4041150b20390010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 191375656 1250 191374406 191374411
    0x801140d020105120709030f0c0602010518060a090201120f0b090601020601180203040c0e010801090c150203040b0d02090405100614071a25020330190e011a040e0a0b 73
    0x10003090041c0e1740e50190440d0080150303880504a070a465541c04140501c001d1389030161280b035002030140340c40d44004d103200600c1600081c05c00350050302c02b043c1d8600d442d80004241b9801450108512070385800264211004d210b001090a07640d00542d4026003041c806003a4445004d0028180301d601d89440e81c001c0c80344c9440140d01c21940040010100312115031003202620b03544240d07808a40e1100c150301d00814038850145d4401c940e0540016a01c0030f000304203443d1680c0c9901440c1007529011200c1c20a800505801460720f409208150341603c0e2446102d110b403082c01c44500c0454940200034081f1843c80c1e0340689907003000c2210070301068110581c24130700d821417040001e0580e03a0304280c2ca8610301040c4c5210b01d189584002c5200345500101929201081504180380004142c0030650f240b0042c2007401c801078a00d100158070144004018070150462100100799881074846550859884404180c00c00c8424141c008041c24144100304090703800000500d800c1c402c6446071012079500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 191376906 1250 191375656 191375677
    0x3130f030804120f05010c0809011401382803140c0a0509040c020f0c090412030203071413060e010302030603060a02090f0402030405071e1503020a05040b03070801140d020105 77
    0x500032804108204d80c91056501504036008100c1a80702c480000c140c00c030240c498561541c00c01603200e025408001d12941201c103500c046440400c80034a4600240046c00b1010014480000428050070100c000500060689001407d00d0500f0315524070102003403020380c1d00400d46000e00f51a4501003050741d8a4010280900c0b00d500d031042440c00322544e10501c1892a001401d1090304018540c000440c0c0301405424401d561080b1004001e022441c641180d000d44401031140314042160300a60056810680c2c91400034214100030800403180e1b4400411840806a407400402440b58001d04a00011a00340f9065246040c42d0000996510010700080d585581c0024151615500c9104d00c82c0140d00250095482c0d291900b000740d2036440d40d00c2804c440c0e11288109032803000005100d10181c5138601681d07501c02c289510110000c0d0404800b182c18007400f00808521040d0501c040e5204410580d43c4450940c1001746540110300307128040390054007901c1c078210050b84c0007030944611108 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 191378156 1250 191376906 191376929
    0x150804020d15090c181406040207050a0206041e0b0705030706050c160f020405180703031d09090d1404050a0303032a05030906091b0d0c0e070203130f030804 69
    0x11142801c42c0003060030a00036801c58500381c800000c10807618600802c642c00b040c1811403090701c42001405807418103d800b0813040312140015038a2804d980034043c01402002280c040702101c4c0d021548503840340d00003015144507400c0948203000b1103880c0c070018000305c020090800031150785460340ca014084004021a840b40b00041c4082007003030031b851500d00a660254a00c4160f401c111302c01046d40e00080e4041d501303200010b5042c0301001005040e0840c224003c008451854804440700f0300c4164108242c1c1d540d07218240055594004200c1c0200700d16005004400c0c900e60010301001a030004142c4595800d0008104545d641200a000c0341d1701414042071f10640f0080716008042c0c3c0040543d07842006070940041076034810301461168071152f00715140b5440e00070b6041c0e9a00c149210300e000001517074182445a041c4030003000d81c010301c1003228000050702c508500071f181c0300440c3d56034010ba0000ca22035003100150510741b0000d1080f8a600b8025604644440d44e0900c03a81c016012f0005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 191379406 1250 191378156 191378179
    0x10050603280312021b01050105090c12041103120307200607050a1e0306080601090506030d05210a20030910020f040e010b07060e03310e0c0304030915080402 69
    0x6004a043c2e56444285990441d65040380c801c0c1c00041080001505000d50320307180c0003182e5400d045030303003a000d410241c40d91402c03d900c0d00540f00080c040200102c41d000b9551000c44a16181000a0350f180700010380e0198992a10500c000c6c10b80300c20011306039580310090001340d500c86020500582140322450007ea5450080b4026a0801029413540088103003800072000541d6150340160705070360400303041d2105a40d0703900d104419110b0075110640c0c103801c48106401554003a10007411500029160614400003d0849449404080b40c1c000010341e200c0034040b03509104600d00342e41424201c1e845030300350f04000322038030741c0d807444201e40440040c1c0c0080e0445071311052a0a40c0d005018680c0d170340d0b00560f1908010050b07504981000c50300703a03080025007000c07290044140c8540072101202e1020300c1c9031030004410411000c280b080300d02036082402107100c0081c10040c074803d103074001c0312603070303c0c2400e24000304000482d610401d0484a40303040c42000c107a00035112604a40c04503104040d01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 191380656 1250 191379406 191379413
    0x160e010807090b040f0e06012a0f080309071a070b01050f1207080d140a0e040c031b110c01050901021222080609010c030e0a060f0b0409051005060328 66
    0x65120381110400d0440850002842003140c0d2426040c6d900e2441120505e44420006545030034450807860543c20fa58541c0401c2c07000000d11910f506070040d009281e07901201e842e443d0b4039a00035102c25803107401c08482030109005004010301c1c116201541140741104a4807880865030381030240038030581580c0068804d50340c4401d101d205203003101d0150346400e42e45420311039450781400d074a02c01003030707401e0003260015403510f065950950603a1a02c8026a00e1041048018420a1100000d260ba200c205041401c40720050b03407a005020303241c0c2c0254001c40084d40d0701e07000c02203001078100700080161381c0031030f43e0118031a070b409140800c5054031030552101e808040e046074483c811041207009000207009070001145405138200701d000700201e02000d04200c090311056002c11416a00903402800001c4041d44041c00100710320500103484421840001d0645000b04400e03501640104034840308680d035489107036000720040b40180200e0305140001083c00c2032801c1c6914890740400c01c0303901403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 191381906 1250 191380656 191380667
    0x5090609030102041a0d0608190605060103200702011b0804030320030d0b190e070c0503090a090b12010507020d03050405010b090702030c010c02120301210c060503040209160e010807 80
    0xd8211094400c031002e11021a001761a04120705050615080c07820000d03100f0808a2941c0c0180303201c803441c440c6004540c0710240501805001141010340c3c810310040003410485d103071550019501000d559581880c0001481652030450000c02020142a0740c00000c0710762003220122545802c000c011280c1ea282c030310302068410300b1503442c00c4c000000d40c003c19410a50000020b06030031200c070015030060824503840c06510b4000e10040038400c2000c61060f07400f410030100c0c040e115070222481d00f1401d0021442c918116400280703410f80340c01a404d030928105407000304d40540030008014a2a207118001d42d1034480c1c901d040103042e510804102401f40c207401401403c2c03c0600701503401c0c00c1041d0000d540b80c0c004808008903500c0c04200703a040d18404103414007a6041d1000c240c2c11a401c04410447d055501d09121140d0f10000001c100026906800c03000100016100d6503180d1030702d070044c03055200004240d019070130301c84019101e0503500300661500c081428644901c0e540e60790701003500c3d07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 191383156 1250 191381906 191381909
    0x303090218010e040201030e0a050d031e0204080709110a050a18051801060f020f0a0210090e0a390c020a0f081c080609190b1c030810060509060903010204 68
    0x61044181d0300103c0e21095100003140903038400e0380d00300078100c504c55403591900c4c0310100c010820b80000f6800110240b00f030308841c45103070741d840448141c0c26024403190300702c0c1d0180e8040d40c441d42251100708440c8005114000d032044210907014908121144000d026208240081007400800d00e5603070381603a003d06040c000f918020303204902c00231640c0da6400f01c060702482034500292a03004080801840801c1c6200c1141c05200100090b80e250b500700255101c00410724001c100c01c03440c001400030f804440c883d0082030481e10014900311200d240203419040c0d1342031015000c865079100e095544901c1f207001c00401c458a41041104014800a00d05c0121a80190604003505c41e0100b4059804114071035201d01e03454454252a2141c107090f038142d4030071601036038005107900008001d0304000d1804c00c1054a08000000c40000300070000b1031039640016110700d01419000c2003401c16812001d200e800034444518101044c0c68a00000c3c5640300e0991094020500420a070342640ca09405590 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 191384406 1250 191383156 191383189
    0x60c0a03020409090f05070f050604030b090a0c03030c0507051509090612060a0b0117040201020604020d030306090908070b0f0f06042424030603170c0c031501090e0606060703030902 80
    0x10200d50603080c115440c0f5405c2405070fa0a000301a03000400c85c0411020000b104c40203002c0310705051442d296500e14200c01081955207015003002d00c40001d25600203000994400c1d01d07100716000e41c5003085403a000541c0c0205000c0c05114000c2013800d1045400d681800604a9a100e42c07036071000085102411280d0391032010380f003070b2001c4c410b00040641103d0642c0400703a031082e49660000141c150048019500640941c020b0340118015040041c03060171014045d08000c01d0f025914200315003196501c6100381e500c404003082d08400c111900c41c085403c0480f007089803805040ca02454100d6080c05411684615900e9240419809040c015105140c60344141c92624941e0fa01c10178940c0c80c10780341d410181c0d4000710ba1300c03040365000348a1841903980060800507081603180c60301020740c1c80040c0c900024480d40c80e00321000e540c104200e505d800111201da20f20382d49000380c82804e41c1c0c40e1464241594101000b0071680703403941c2055400d0b4035054035012555410a0000c602545024120071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 191385656 1250 191384406 191384411
    0x61a030601020613110310050601030b0a0317071a10050108070c0b061002100e01050105010314011202010503040c0b1602040e070303020c27010b1e07021305091207060603170408060c0a03020409 85
    0x91f10107003a07501c0203204800a88051050308000783c10450012814000100308840d581810282c1c003400d04c01504800d84186095501000700348510b60003040100e4550341c07503139041390060016503442642240c10110342c1c24881100601507960000a45c00204010700030f100a00e0b00f1000756100700480c120202850a041120207440b41c1c81c1d5010742400d000e8035003c20b0030140c042968601900e0982d0403201640600482d004a075801159154030240c000e50340003049a6000c99140190780043ca510340310f4408011074014280705000546400d0305078103190b82c10507281000806d8003c03640307440020f02280c607059071080d81040061848048002c0c00040038480f000440e50802180c018001c00c060403400000c01c07200d41c0c840c008244584600250080c44ca030071840024038858010030742144200d001d0303c0c3c2c108040442011703150403c4a007a603c080d22210208240250345042c1e001694070454140c0c9080d0034001240d50382c070005480e00500790000103034500d4151090b41510007600d100d0106 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 191386906 1250 191385656 191385673
    0x83610141209070b0c0d030510030b010801020d06080c0d030c020301020706060e0108060c0f09040f090b1905010e01030b060d141222060212160f06061a0306010206131103 75
    0x9011034148101c2ea00a060320600f000403504030206010703112400461801001c100700140c40c124040c00003c1c0c22189545000040400000c0c0d06040060183c084d0100040e10307a002e4010220039110309a005001c02d82148449003a140c1300d1000c000661501400c00340c0071a1041d10210380203108901e0094551483d041f40411545003690713a0f5030484002d03008581c071545864852140b2441034001d04241d802c0104110384a504281e00b0044106921240008005019172942e4503001000c42d16130701c2902950603170051454180c45043d0240c00c88910043c403960466a0302c0d5003001d4043d00c21441707002071150600400c4410b40f104100f41d021401940d908140003030300390103a03801150200c00704118004100680d49101e03031180c004c55200b41d0042c4604813202c80080050340c08240b8441e2614014051a0045604420740905180c420321000030101d240c4004680015000402030702c5080c0d04106000c075580c1c0c00a00903030003842c2d13080f0110b40b0010515102c1f0304100d40c1c501060700343c001c0c5a80b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 191388156 1250 191386906 191386927
    0x6040909030c140129120609061f03200a03050d050304020906010c02010806040e031e0406081609030b060d0501141006050a0203071b1208361014 64
    0x5400d2001e4400d91500d40001c40d881c441c01d09030b40c0f001e040421400960681768850300820030140c0351189020b40342e95600454504000d092500c02c5550140c135600c80c0d000d0245004c150b0002c405000d007007080b61844039046581d40c04810210345000401400e0464280c855035640c1e86040c802181d00c4802c44003800f0389140064403c2d00225800d070b110301682707c0044c1055000c0c2c4801c0d99140e078140e4401c1c905588000c20040204408100a01144002c0c0a80340c002d03500c1c3c0050380c0c1c450700358a0000f62640e00d04103004058420003810509007019041d18000f07030326040702e02001903c0d8010030b08080c954810011a500e141094000360096007040c000112b101c8a0301000340c022aa041020f000c4180c5868003aa060304c103003081c0500580c820000980441c5000296600f00e007034507285914115910703c1c00c44120030400c1001e94100714001400568507200c0040480d10084d010717450408003d000703401c1300003100d089141501900b07004803040303d054402c040007507001e2803101000303454000528 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 191389406 1250 191388156 191388167
    0xf030c040b0706150504050c09040e2143020f0d030507052a010809011805150108010912051303080c10050606161b05030607050307031d0705040b0604090903 69
    0x40b4071031070b18414044c0c04545d908141c0641031282401e084494581240901440002c01d03500e0703110b5485005d18071202032028400a40c00c021459040406034a520361485210200004034264160524031841d0501c240704441a0340400035021286d00c240444003400800e002ea82075204007507008000042d440d04041c0c214001d484424020011212100f62414201000e4052a8610307201202c100c4550702c11036100d410201d90000c000800461740d0500980e00c000501900c4004907400d410520134040526074107800c0600501e03510009204441550b2180f8183c9000c080854040210028070103403070044450112008660002c16656146101300005031980840311100d8546030420f80400d500385040c1042e10320762003258070042640b10565440b1030f646100c52076490250100c01000040e540d5090120070311400603600c80d55076030300d49800d00038112005244070004a10400c0d80b154002100062841d042da0307816103000400c0300280b00002d40c40d025030f81c0410361290405140804265102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 191390656 1250 191389406 191389421
    0xa03051f0b030604020706020405090f04020910030308072a050c040b01050301050f040c1205070f0e01050309060f0a09200103060b03010e13030c05011503020906030f030f030c040b0706 81
    0x50541800012102400020425140c825010074480030710106010707140c25402007028a1103410014600395580021451307a6004444200703603a0200002c00003135061480d291980002e10381e00f81080caa00795a03002e030442c20050045010405075a4083c0c04101c004c5026100700984500400d124203807928149640d0b1001d500428029070900000c580194019400c1c2d82c140e0700010003501da20b1003034409000007030000c890b40030100001110300081000091041c1d078000e035403961b2030381c06105400314040c201403650000d03181040800c02c1003101107440403030010b40000010a50150f2610b5824400019240e8404003803d40781820f040720402c00c1036006a0041c1c0002030324148100b075500c0079541c0b1180001d00c04e002d061107040c80003d0454403002e984035105846410076000e0456030f501c41e02d0031548204141d00d241e54802d04c0c203005500d4a2441e45612150460041003000034248207145c803400303158905174a01c003000c004203210400c55030540f406000c0e8150500d84588041c2058400703410310 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 191391906 1250 191390656 191390671
    0x803040c03020445060f06030b0103080d05130b18070b04080102030108060105040507090b0705010906050c0903012004030f050c06130906080102070b01050d030e130e0f030705120d0609020a0305 85
    0xc901c0e55210001348288840c901e0300d0101c0c00e100d003600643d100c003000741200c4240c513061030b41e94a2020000618801d21a806580201040d648442240741c0c0c2d8003c540e4040c040440b0550380100300070004149803880c550100303002d4201000ca0803030f01e84140c07414050b078116001d4200007042c04140c000c0154060760403a80ca00040f503010342d90318002e102c02c40f08251200070008801c84800d0113601c81d00001800c045120f0f40000810640c1900c40350100e68040d121861769120019a500700c0c0e240034000c4080e2164208007038114041c0700d66102040d84680c0c4002020b10544444050a100c0140501c1164100141000d6664150220001e07070041e02801040344440c83c00501187c06c005c148281c844141c4d00c64220765259082804201c094007614a080b0100b02c83d0744d41c40152074441307424440511801c0900801c40c9006250180c2c181802c4000d8045240d2091080502090000a1520f0a11111080d450340c40c4d10110412001e000d05800020855000080322102e0303590540c003582c4200072 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 191393156 1250 191391906 191391971
    0x7080c0103050a0e0d050c03090d0c08060609071e0207050409060603020909070605070611090d060b041409060402010507031e022b0905010e0102010207020d1203150609030803040c030204 82
    0x88201252046a60005040529602c00f05002c110305002e1b42c010071340700000d00b00b243d0030700041c480000c2d83c00120030380c2160810603200c020031441c0310410426820a00498444166103040301005000082c40d40c02b60058407196003541000d07034000c1c0846005460040c000780b10142c1c1a0400c01c0107400c8911080340a0f40d040350005001030300c04034031801611001e5a9091401d00192211b030084d2a2910b00040340000c100007640856540000500c00d007071140341d000c40c03140404c0701048100c80c4070400f00301d4481303800000c101350400d0101e00164400d50900781162108641e040c04c550300c4285a0194400151000d0389880141e000500070010400004c045521230901003680342011025020100c0456800c04003030210350700600652102c80390600c00142090600d40009030710140e405016200030710142001c40842d5414000c0594055110003011002450100b00030052407003884050405031010005c1030811245415500003140c00030000d0117140000c9501d4a2000b01110400303000c030701d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 191394406 1250 191393156 191393161
    0x204060326040305060c030402120d03050a06080a03050f03070c08040b120112030806040506030c0d0812090f0a0f020402130e1504061508270307050124090e07050307080c010305 78
    0x1141d41003200d080d00d6002c0c01070441c40c0c603003e5103031055410103081203a100f4541721040c00500001c107c2c240140c1c60564011443d424281140c0c02180e420b504880d829401c40791411006c03a801c0011910030100d41d04160b42d07242c1e21907004031801142c03a100101b40e40c400103000181030f4101c00180c06501e0b0456040310503030340c1c0d5040c07001c980b0a040c030004000c9541003001891610381a440a80d100c003024043d0707402c84410380002058140400c100300c03105800414598071804c040c4c0301c0658001e0002000344940b000f030701e0b506a513814550400806800c00710103a4400c646994058030219001007034060001500e40341108080e080403120312990010b12903000c40c9501c0e140c041d1a0840c1c09a030070300040c0c0440d050049510780c034000c00780400404904c500440e0980e8800f42010802e0b5040c01443c1ca5003c04c0c94030900752010020200c1c46041c0550310070400b100e050b0107a4044a02c03e0700009561229a0007a80c144a9680d1103281d050142c044001103414000c2800003034200b099a00308440da = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 191395656 1250 191394406 191394473
    0x180b030d09090207030917032a12030901200304111f0302160b0411030f0706090b09040b041526030f07021810090f0e0c011b02040603 59
    0x1440d8240d80c50001030980e2070704200041c2c541d402014840c1c024170304130b0155500c0e0075082c40020b0024100e01d05591001580035141d65011014080150804500e00b00b65100401034035a40c61000a41e41d415210000125459607000d5200003003401d4820502440f0140030300d407406158004450507200c00310101403041242c82e080c0c0141c021107202c80e041c02e42c10b40d11014101c3c029000424001202d4841ca4031807004204901e111a20070f9104030440d0341c04010358002e141c100680c0071603d040c00e620580c0184141900b0031684401e030f400580c0d2050311022403100107009090541c00c02504503150800c1104c03c0e429100ea03040039618440600d141e11004210b408045580a55070280039800600400202c0341c5514014451a80000c0c50100003450102c2d41540603a02034806a4602d04214010050800c0c01c0c01172609800b030481040180321603e41c01a515142021000da042000100300f0100c03410720182030094154024100704802c6071281b0f03000c088015a0143e01a1101c40080010f850 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 191396906 1250 191395656 191395663
    0x21110102061308032206093815060a08090606030d02060411010905150a030c0c1a0415020d0b030c03061306020705010f02030702030d06230108040c0f180b03 69
    0x4a8000781c0d054a208020b80343d5562641014081c4d00d02c0810110350500083d2070b691024800178010380d0000b4013160700e4034040c0d00c170048035040002c4043d01c12414400e035400ba2075132004c55903250001095695039040d45e42e4514050015070a521000110b0aa40c040d980a080d6500c03e100034821038050392124400c1607512812000b804006a02510000707000486022000c1c8035110113041ca40c4019840b0700003c0d140c101100900110340e000421400341780d560601510b120a0058148400038041540b210110000303690030f6102d00400710404901040b00105904401d100b100300219128000f80790300308054200f05104034440d114480d007070348243c900400c0c900d0054004054030700d81803100b5034504000e9000f4a90950b125561002001000045400203521a5030994040c654503203401050804480b101d40120305d5213020346400b040c0c00023017442c0ca050500c1003401c12004980d1245002d40245460307030404d00441c00d00840005811700002c500203803a08090b607007404560400d90900d0396 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 191398156 1250 191396906 191396911
    0x90d08070503131506080f030304030905010c112202030106032a02061306020903030715050a060602060714090d0803190b0d060f0b040501180c1103090f0a2111010206 73
    0x315008400f4080c000100382c20701e4480848100d49002c641195240d442e0b40c24001c0e600c070b0100c4a07410010400042540c040c540d8400340c00242003014000c20a0b460f181f10103540c0d40e40d030a0140101102209a0300b10420310301149645040c0150340d03d40c1c407400e00038083d1114000a10108203500000d1814903020b0128040306407640d402050300c1c3e81d072503c01a1001044200549066034200b00941c41600c051009241a500464500700f20100c290f8484c1b00300c1e0f2004005206062600d00300f841610f60106569410851030300d0101441c1620444103440c40c4070344544e0751713403010b465108881000a400c2c040d601c110305180414840005e107415107016076121480c2c5661020591042000103021548880c980190455001851600c1900481c0071a40e0a81001c0000784110429051035051800740c0d840340301d04c0386016801112542c106070b81e01d0090080441c07241c075506011071000d8441c0c440d550000c00100c0303160491402180300040e50b8008564082c1c6400c1505400c800c460750001a02a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 191399406 1250 191398156 191398171
    0x60602070e060904030e060c03040311010f0302070302060103080315130c030e0303071b060f020c072405070213090503070b041505041a0a020906040906090609060e0a09030e09090d08070503 83
    0x144136940c0780d404aa1001c000b03141507901003018000b00300d03421030400152000d10b2159548617a450055800035103000028051101054010440785001981c0418014112076200009036280e850707550105a070754208041d8aa0040e407800c02810b40d03100d140c1c01ca808138140315241040a076510001041d2603100450745140851102c40d1045070108102d49005071280c01403400041c00490180264142e9002964610250740007281c01c3c40303136800c8076200340d86aa518505107040c082902d00f01425038095170501a00c03d80020420f000a450260001e0032402d03030103810307207aa034103041c80e090340300c0802680c066a0041c11504441f02100940c421140240e821111141c2c1c4401d5050540f01e48060040020400c19000c5c005640292104400b92010304507a40c404203c031802c3c19036840444405902c00e02003203003800750030030981a0042009803c5542c0d0301001c1042d082500b403d0f0b8100303022180c110f4112400904206a4a001180d800146202c03a81d0710350036506d600c03404441ca070000750380c0c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 191400656 1250 191399406 191399419
    0x30902030703140c04180203060c03190f02070503030907030c0f0b0d0213171e031801050706200304061409030a0c0c0f0803070b010608040c090506041509060602070e06 74
    0x2e0000c19203901082010b00c0408040303402c030420030b1000c20b0980e8100000f03aa4540d404e58a020114601403043c15070004442c401107086280803031000580c0186006031a80907695204103c00700380480d0120b074040c640150171299242026242c403540c8000728032095038001c118410100d51600314a8005040365100c54110b8203050042032044005d60010010110100343c04400080808107107101c010039101100c00391644030302d607466505041c44d03107410100c0c2e00d4004010008100d140011500c2e00f0500038604540c42e043c103880c10308014546221480f806c00402000b01e000541c1e03000055200324400c00c03050103010200c00400442420544032510160804d0140300002c51003004491000740c015800e40c000e0380d41d1100014802001c54102d004c058100086d20010301000110590041200f031030718501c03500d0b164541c081c84d00321600900d030305c051700d0341e0201d9020703503a0742c200400c1078490b0100c0060345c40c0d0700c1e80c0c1d9070001d00903441840090702a034040060303540c1d421a0700611840000d01072 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 191401906 1250 191400656 191400659
    0x1f0b0312030c1201030c081009120807021002040902130503010b0a18090b1303030c1e0503040c051e01021c1b020301090f060b0a0e04030c110102010608010c0c0605070309020307 78
    0x58941a00700420050b89034009104048500300402542c600940c045c50b15904010b0600400e20b0802141c9402e00107001e09005000000514440d01c0d842245044d20f04050f00e9101c02100302d08040300c03840066141070011401003115002c83d401032103c4c09101000390b07400c9982d10f050500b030f207502c80d4406501820b40e0a040080607a0103001075030320100c00c003000806444a984c0c10818050030b444101c031007403e5499100405030144548a400d0a49060a80b51119038070807020030326080d504d5404c104400030002c03a04000c01000303a4006040c0003041040083c3e20a1800516140204159401440703802d1990b030f40f5a5450041000c1100d45d5a90383c7d0300700d00c014690024150040303000301e070103643e075a458002185008940101075842680c1c08204d50094808200b02100c2c540c20100903141d4070414030000a0b04030b403954134010351149c211a41c1078401c2d00143c0c0180a40c0c0c1c0095040d50921070011002e40e40710000000840c0b0071101040030b5281c50900700e003262010b103002034040c1d00c071400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 191403156 1250 191401906 191401933
    0x9070305161e0807051b060103020405010801050105060a050f09042307080c040515040911070501151d060d020a0f080f0a030203091203041809020306151e1309051f0b03 74
    0xc41c030744c3c801c8503170903c1c5141c21400c0740d45140316125048002070a800542c0140118942406410300500840c4024402541014000780e0503105016100081c040c2c0001c040c0282001d600540f504000f00078001c000584030221210311080158481d13245040040d400140f90600030b002d882d000c2c020740c2959a040c40d0520040c0001d040c1ca1a160408041c0e09000004900407240130308811a541e10b2145034465100e4684982566541d2604000c034200c0031106014216100503c0c0080d1646064002e60315110040030504607511401c001e504065102d20110b800201d1071800c40c104d8403140700710b0701840c01441c4501d4850a001c54010300507007013000700700e04a140180c07401d5284111a802d90b45055a6031489080b240040d10a44c2c0302292222034810071361409000303c43c0d01c810444c18441c0107202c46400a1100340c440e081c50040382e0200300d550140c503100c498011035020400c5804201c802ca20341030455803102c040d103080c01d0b903802c00241c07444482005c4c0650911180e0181c028060f400c009032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 191404406 1250 191403156 191403167
    0x70206041e150c02010c021b010518040f090605061212030105010c0c0801050703150e0f040b0c040e1504050702030708120703020d0c08060f0f15090102010b09070305161e 75
    0x3002034034129140c10368050052203a00c03440145004a40000035000a01503000e1305123481041a155040c0200310004443e03600031003102d07042c0420046444227400c01d0b80004d03008040000f243e00e0b5080c94842928200a8194003240c050101210900500c5075003240c6150748417002c00d107503980380c502400108034a5000c2c0c0702d81040d0078401c81c02c500300e1a460302041070868034101c03000000681c0743c0624102c100000a00d000150007c11100d031100d08e41508a40505003002d000102009080c03400140c41a603501c080e0f401808252210300c1e554140100071408003c000c1080d54441d500c3e02d8042081240004110f807a407550020320182001420011200381d030b07100034203070340c1410340801002c044e0007803520411859031241e0b04c45d0002800c0c070800b80000070315460404c6010702c4104d91750307000301ea41c1c500070076030000302158500b6a211b484400403805000304401240d00014150188000681c01d6045548508035142603d09007220035003048440540301c001c0b84603072040007144a12a00e00c1790 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 191405656 1250 191404406 191404463
    0x9080106061b02040b0306090601090f02250602040b130f06090806040305090415081e070531020408100e030f040608070c080c1b102c0a0e070807020604 67
    0xe000117203080c090000b0034148081113a0700302d03007908140014800020144244203641103041c204500b00038440f0000c81c400e61040f410040f40100c2d4100c00c60030030407550111809040042d01c141e8031034102e10741400325107100340614030034491880d03001300e981807045031240c3c1100d01610041c1055101e40e10190b5959222007200c94006488551085240f80c00019500007090808020041306041800d440c440040c0114103c413503800c015020407480d52110140d8807c20307030985070745407121002c5a007001c4041641c2a00000e1600108000a203580003003200c407101102c541042c4a54000c01e88516100d00c5241d409191141d020320003400020311910009600500c07504040802c014542c4600b18103402040b404a00c03503005080c2e00e1003020069480069642054a180d40b030000d07108000780450b19001e440103041c9480b040130420000740d0050350341d6503400152210b0782c456115035070f10b071000c80e0449034030000c500060b020a040500c00281e0b50710603604601d45c0051454001074064507d4441d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 191406906 1250 191405656 191405659
    0x3110303062211040b09040e0a0213020f0d0c050c060109050c03040807030c0203151005060c150c0403060e010b040c050306101b020402030a0912110c0f120105040f0309080106061b02 80
    0x35080000040110f24000b4009801c50b111000d8446400b8410401504c050007520032040d08140c44440043c1c840c3c4d50f1441c0281542d084c05030322108210b26210700742c0030b603007480c100060030030707811405694011008102d5840e00409407070140c0e8980500406481007664a184034420800010b030109441c90003601140d4440c0c035080c041d029594000a2910100508200102d2200c1c0140880e081420012400410307082c1d407032074206407540781443d4a445c00036030700c8030508001c440042d06d803900701801c55001c1d40e071042c0c0c01c100414500003a14000e1140d207428034002c520301218605603500600540340b10b200001d0403022500400c0300e084411408008200d650000185540c00069446001640c481c0c4060080001c003680c50741450101c04120140c0c1d4000d021080242c181e240704045507888030002c1c1542c2010081ca10319000c81d0004080c2001c80a007075113048181320030044003040f07107a81d45029964900100d41c49407800707801c0341d006100d1480800c1c81450240410346038100d03030a154600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 191408156 1250 191406906 191406911
    0x60f0203030a090f08180f10080c070204061503020c0105060409020d0609020604211e052503020a060e01030c0323041403040f180203040309060c0c03120c031103030622 74
    0x111039541045c641c10954602000441e076040e600c4260414041c0c0588608085411940c2c5a0f02e41030046c101b0030300034145013000d910000d200c105545807500584014070011540e013504206180000b0001c0d000714826500d9942020003058051510740201c00d020744e00101501a101151b545403c002c2c60107d20072604402d0610000841c0e118406400005180c2859620207110241c90944882c0f114001b82100c4050110ba0020100c0c0300022008a064408404d0314141034040e602036190100f180d100950040304c0d2840860441d034056210b0f00150300a0b20207212100026209500f5540c181d130050f410f2422a042c100107040d1340f2142c1c1501b09001c1c0b5441202081886a024155405600289074130601640c0070050b1904103010f400070000050411401e5060a641c024a094042d10034035040103000000c1d40144290442403000a6910400c2c01c20b80886030440601424005902600801d080c1c00548608400100807603200e40402481420b81441c020213007560540185410416141d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 191409406 1250 191408156 191408183
    0x906081806070207031514010506071104050703091a010509071206090615091a1204140703060506030c041a090709080f010603060f02130501050c0c18070207060f0203030a09 76
    0x341030085500070705041d800303070100b1800d50030214112522860860011840c120760040703404075400009054a200320382050b961090750816500108039003905541c49440c1c80300b841801501a03101d01900c41c803034441c500d108100e404100103030b4142446019080f04010f40000c0d2218403c03010b044180140c0390002548689900c50701c03084600302e0308541e120b4030f810700c0c111604640003681d8100a1a400b1448011740d003803400c104866010740803510701c40810001c0460100710401c001040c4201010741280c01c450780e01d0030101c000d0b24007960380030b000c0d00031040481c0700d47c1400e0194070f8944600b01c900c00c01c031200243c03d000c414071004041e04200041e940002c0f803618828896148400c202400201e0fa0504606054080f00c1109518880c50384c13040003003205440034000e41104807003003428042c0c1ca4580b0400518107054500030032651040c4001c2c0505d058524251400d409480c0703d908440610b80c8400003607a98000c42c10010016a0092000408070302c0c1c26000001c801e403103002425400c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 191410656 1250 191409406 191409451
    0x190f0908100e070e0403050406030915090c0f050d0506060904031e0302120c070f060f0209030109060e1203010e0c090d1211012a1d09090d030b0102070303090608 71
    0x403840854008201d0345803244a952030320b0821440000d4981607021004908160385e0140042c400d80c4500c10034036803208206c20a01c03801441426064900c80c4080c05a00b20a2078035046212160007149074501c40e02d040494141060440c0d50040c9900c00001c0902e6140c0c00c00700480207800131710032810031680c0d080c07060482060208100309030245460268842c0e4140100e0f0107603e01c020190300720020180302040225240e403111461254110350005a0351210300c401401034851943c1481d019030804007000100b00183d8805640d00c0c122005586640655203520310706480284a14100b0640800105050a840c1001085561700c01000c01511002543c0c994015981841c98400852035007019050542c00078040d0000207455400042011019101c00040d401c05440b4813070300b005031300380305402100051b00d480148000010269000b603c1c0450103196500340c10b80541d0002030034890307064160b5000042081c162581074543d412600d0404104a5038603000030403d0a04051159400006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 191411906 1250 191410656 191410663
    0x6011d0a0e01020a08090714060d050702010905071404050c040b0712030e010c110616020d0f0923010917070303030e1509030903070806060d030f05040806150a0b190f0908 75
    0x82184c9403500c030050310380070452a0411100354001256070a540030100010b83e41c00707044070b44403c145040000e00c2d840e608422401401520070003041441204000f1450520a07500b100c51031100703e505100c590b40d51041c1c01c01c2e81c000c038072440407000d0b4284240c1000400c0144100307503480c020b11b40010480f2a0201507402c0d50040f00c01580400c05107002c21150b0881801850b5202e030844040e00c0c4031000b10a002503454002492920400c031000e03410440a41c450104c0400505000b290441103c0c0361074001544121101c4505021580010001942003125948617404034841c101915042e4a552000d074043c00000d40e0029203400750307030407003540d40c22400840c9015609020046462b102d49100b818980b00c0380340c01494140c0c0c454410010655500300101900c2541072402c0d808080e00a1000d407058000c941000f400c1d80074031400c003d64040800c0f154032500b04101d48010041d0795907200b1340000e10860111041c0303480c1504481000714002c40200307000c070700d0030b20744100d04c190b07519460f03400d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 191413156 1250 191411906 191411917
    0x7080124171f05250c1226010608180d0f0302040b070b041e020a05060901050c03030108101b080f1b07030809071403190303020d02030103061d06011d0a0e0102 70
    0x16007580c80c420302c0b1241010700440181c040704d083c2054281e280c2030314040d1203802403403401824540c841e01c500100c3c6200d142542c2801c2c07145002d000e4000c0721180c0d03904800000740030380c8000464900001d11034040104022910352080c03005062150004002226214001e070501010b040d000c010000d00e01e500c0c0c00041203610300403042c0110a081c185441e07038003486020500844640d200d000800940e4946001400300c0380b0465000765900d44e10801600d86009044d0103000d10700007c0300000c0c00f41000f01e950315a810510b0801c0000d08503000e601e005d81130602e807061000401440014518100c1c03e0621500002c0c0881401c10904440c82c00d254141c0c40810201c000400c2c5209100358024200300382c01c00340100204550031650481e002c03958461035040c81500d04a510f110a0092500a604894400000f62804c0d0340d0f0350b07141c8c10500f01608072810883c00c10505041240075030580425002d041c3c8402410300c200100350549854032400029010070b80c810317900d074480c4410740b100344018034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 191414406 1250 191413156 191413213
    0xa020a0f060b04061e05060d0e07060c0507061806031505030115030b1501020c1c1e03021005010e0106030903020102090d03230a0e04020c0c0907020708012417 70
    0xd84a5840c01444140c80e0140d2040304400d00a9055000130703102170900c0c80546400303440c03450f201c048000c82074010b410189042601800b0b18100455855400506482858050022205640d5450800f16640200f4001c1c61079455034105050100ca403094010180d45100300701d045c000e091319200040c0c00c582c84000403810891280c0c604000708614441c84030350040011210012040131000040e4481c1d81c40082140308040c0321a0141010000c4821444500c0d002507000c40c24080700b601c5502440582c46080e805881110015085e41c5076601409050ba404004407005507481c00100f81d0140411450460a6540a1100110035120100401d95690083c0d48000c100b8411441c65440d01d00040213091801c0030401041d42900d800c003001203003001c41a2401a0750f40207200c8502c1c2008440890140c1c002c080034148100343e41d00140c60803e60342004000c0000c1540f80c060001b85c800040c1601c0c03004a008a0300300561012085032080400b9440240ea520541884240700c1450710ba841d5203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 191415656 1250 191414406 191414411
    0x20d12050705120c100605090a020703050d140601030b0f031f0f0f0605040c050c030708070f02030114070206100303020c1e0d060207052103040209061c060e060702070e01030303020a020a0f06 84
    0x300402041101d4248000e160008015243c1000041850b44230000c0445000316000540d00d000c2510503070032100d00c0101c1e40c0040150000111125020460039a081070002c0c0c1041e480c0000d031710f003010814070850402001040c00c4511215021302005403000c900a003da82d03907664102d01c4456000e506111030701032200081c02d0b81024100030445500c503420030304105050101e035450040002c100d40c04a90400b00103501c9120610b80381110410540000b9003650030089850105114008120302030344450302610060f43e58001b29001d282d58078030000d00141d20015050f907260030302e04140501401c0c582079407800d649091010646880340d4000854071503a001400d00207105090044001c00100100613441d01e030107100c4100320300d00000e440644240c0780c040c0850056134461104a21101400640320008001400c00714020030003401c0c0303518035005800018501d07520103d51541900c03009403c44840c0e034215181200250000394a210a500c03944003480d01040b17288070308403c200e02c01c0b42c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 191416906 1250 191415656 191415667
    0xc051903020a1b0e010e09030409020f0304020f19090b0303070605070f08090111030103060e0c09010902250209040b070e060328200a02192904020d1205070512 70
    0x4540c015240d400c035510603083e0700d107061145448403029281101c1034a00854030a40310302000301e09510440c2e0040b542144000340c000d4040e400c0c040958030590007151800540e419850910075540d050803403a0b00d004140c1841130007001c3c0c141d4440c0740498000fa080b682048402d0303807108100c501c01e0311002e02240700d40c00c025076180e0740108074541c0008080024000702507140c00c0017525000602004104a881d0324980064400410804007540c0c8010303c03240127543c1d50007542c0001c1d4000e040c0d040002c1d03060726040c0385804202b9a03442e5816805041840c031a80c940c0c860801041019006404025000e268010181c0d03503a00590b0007240000c200d141400a0003903070800b008498408510781604022004001281403603801481040a80c07140d9950484000100d0a2046031070215101220042c24035082c00f904500c0c10041c980c1c44a0302ca420380040c50a0342500d0030040b01c0003940003102d128400b0020305102d8643d50b40c007110b410042c0c10000155a210b04005224010075034800d004100d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 191418156 1250 191416906 191416913
    0x603030c120509010801060e0117151206100b0309030d0203191d0d03050a021b0304060905010504031e06110a03150b070218090a080c0601060306050108090309010c051903020a 77
    0x42600320780610706140e031a054550700003030b0011405204010034000c26000074070959009581918400000d509403c243e0300d00b07001400760f80e134800312a00b0700580f5030911101c4009400260340d405180d20340402240e041c501201801140d00c0181030340c030f6900081c0049010b01031540090350043d00354041681c080360b044801e0710700311005003038294030450611800420000000c12076081c021301c02e01d0046242e60b658080c001c041d02c034400da03840c861f81000b01c10900a20300840980140d84072030b030f00c0c4a140390f0b541004507124080e500000d1b05582030801d01d01101c0005000e02c202c0300c1d120300004511415a44013501c0f25030403013061309010903150750601c890b1010050040c4003a040d0740c450181403007003c1d000320340310f601d444001e0b0250b24201404034841c004200001c0344407a500489155598a01000240e02c41d0341c203100b06000319041020206041d8014448a031003191802e009604000150b001110301000141c0d05032201e009464800f01020501403551410300c0c0203130000d214510071482d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 191419406 1250 191418156 191418173
    0x40030506013524041e0204150303050301170d0f051c0501030b0402040b0603090a02010e03070503030c07030c09091e170d1401090c0801031b0503100501090f0b06030a1d010603030c 79
    0x300800c0f44901002004001000c003131214410401402461000c4100b500c0030400611443c0007440e1301090112001041581c8000114140d074414802c0710150b021980b00c0580e22940c00350180f020800c040c41110340c8910500144c03c070601c4484210106048000f1444200c8800781c00590305084042d0801c01942094081d603900c17800280d44882c510301d07110040c0ca88030f08254030024108105074007522003c1ea0204110006040001c041d80c0c0e0b500ca9200c01035a44403500c5c801220007195070f4400007607640d83c40c815116095001101035003a02ca03030080c014100807519004503003600100c07014a6101c1c10500250112403019000081c0d031038042541c151810105070b1004001905103034012a074079038003040703090450340e0010f0707800d1078402e503000c00d6121200030341c2000ea014400c07514207162180040d000070741250400710f01040f0000c080c7d092581501d02440710390380c22090030408100ca8000f80d0307000c2c148200041c03028520080b031841e261403d50b551b540c0700360009403801c0a8441030040e080c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 191420656 1250 191419406 191419453
    0x90603021008010b0f0f0403120c1203230c1911010e120f0a140304080403030e09060a0308161709040c0915050a05400305060135 57
    0x3030030300d40c410750715005004030140702d0740d80c1840c0c00120100e04505002d07040e82c103440185501c400c01c0002052103142c00ad1102d070302a0402d45540040c1003000000364000d10400c201c5881022109030440728007a54081c5480010384120442c400401003c4100031507802c425800021503610703406080004c80d00f0a003911109042910135400501a903078130800002c00b00c61000004101e803580340c2910301415941010100c0c042903038100004104401c0160400050050b01d0ac01d8076000079002166060040f520340840c2c0c001c0c2c101d821814280045a494406020380a01c034003d0910301d03850940d100c22450064421040f0740750400305684000749018000d0000c1c98202c1d24101c0005898070303064000202291a904040c8440090b042502c075200710115080c0c0100040e001c800580a2080fa40d110b40c401e48000c03240e0313125140d80302401e000b42c0c1901e074201c98010000b04420307401c04490400314811034441011030003941e422080b4001110592003000e45140b00070f00503000710400802c0019904 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 191421906 1250 191420656 191420689
    0x715030e030304020f0604030506040c0f09050601021911060406090311030f030f0f040f0312110c03030d1e060611070f0501080a0f091e140102190f120609060302 71
    0x10611111400c08000050b00c0c1e1043d0100c0f0101c0701030600e80c021a102c1d01c02c03a000600303580900d204001c144801842504101d403500c3c41c50491303546d611250a4121b843c1680c0d010b0050301705540c80302c013103070842c9071000c4a0f40c0274030045085206144005026540184d100c0404120100c104005020b00d03141c089880c89820741c0030700410030781c01019503201c2c490940f800880c1b0351b000c1007441d0303080210010740d00680590b001c012510360b00d0b4103100c011241110f18000000d6600202c1c911424000704072007e808901030002c1d070400c1d244100b0341e130244c0720490740150540801d0000c00302d401840d002307070303c020106a1a806a00c0d444c1d007044d6400e20006800c41c9526040392401081180da00040300c1c3d0303100c614204d00040396642031103104050007103040c02510481d0031084017208413003d0740200500510920040818882020520b800d0b40145001224003121861030b806910f4001c55101e020001e15142c080c07034290013106010101d503c42d401c00d4403200d03901e1505008505249030b0600f5010035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 191423156 1250 191421906 191421911
    0x2010509070f03030c110405041103010b040c120902040b0303030a050907060809060a020f0d0c090f06090e070e01180e071b1205090a031505070305010510090317070f05071503 77
    0x3801c040e0098002e2510004003040384440001e8140904134000102004c002801172102d400c050600603802c0722a00e40042c8a075182844400d1b072454540304a100d0000a6103581184210042c1982c004040780d0b13405a0300a070711440c10103180c1e50140002d510900c0c000c4c5000640c0d00f0f142044500d00851500010203202004050081304103000038410342c0410010805a540c5400c10507291250042c071041c281c030a400d051884c3c491541001c0040305643d0692040d207002070740d55100b12040b02103486101d00c840407680104040901c941d000c0e018064042c10101a140644941359811018030b0344981066801d20051200d41c65116041002421107080c500340f410781c00d5160003016503400d07018001400301c005168601515554001c4005681014980c2100300303400130010301406003147c425000911309030011601d890202034060740e500f10340d0340d1005801d055036240c0354881209205100c0184d414400d403000168000c5600300050b01c14070151200030f00c3c00001c0d0300c5504240005009060 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 191424406 1250 191423156 191423159
    0x11030d0501081c1b060618050405060c180f03071206020306132c0c060f03010806010605130b091f0f08060901050102190204021b0303091203040b0601120605030105160201050907 78
    0x191312001d219050f0100c040e12928110391854500000c190680c011025041a00c0b0f003e52030350201c3d401b03248103a004400740e51071681c6001ca000b004d440756540801207140040140346550800e840355840b082e4002d006c030341c022621014050100c1e400400b04840403900002003107070500300060f12425031080c050703042c07000c104070712010030403400e4100c2031041d80c1b00f81085000060004000354140c010010388026a0ba84000f2400d00c0d2640c03090080a0b154800d02000080483c8120700b101ca0b101c8220b01c06100c10703820503082c1840ca600c1b5002e196800a54804440e905454260844031098895160001d01c500381d0140503001c03da00800703440c400d00c9204010070259370042428418000c205441d2184240c1910008000340504140c080010228520254500030000000c601030040f0b042124810905402c421180b4801102c00404404d111000308070b055014000600948a61113404103509803900702080c2180e500b00d402848000d075802100e80d01b903070284a042d4001640001401c80c96 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 191425656 1250 191424406 191424463
    0x60b090a09090213020c030414060301050a0b030901090203120c060f091b0d050712150911010311071208060103060b0301030f030804020102190c030b07050a0e040c11030d050108 78
    0xd18688104080d09840c0c01c0140c04541e2049240640c0000454086449001e59110641e49402600515445141201c901d18161a08400fa681211002172241001504141d80e44003d9000905031180540d261511040180d80901c5100000500000f44948a500340811949403034009004412812944410b0200c22a40840d00c2c8024039103040d0100034440307820300800c41c9100c0000307000d0102e009188002c5140e820600d00010035501a541545800c1e007407071b2101c8101c414403d00117000d50300010440d84154041d40011a00e148404c03e42400c1900d240c55030500700e41038501c404001814241003000e190303094410603000d0040240340d41c4c1590305590741c0522142602d04083e081c03007025400541168800c126481c002902d01411803082803140c17808503018a0240001c96030200c8460005221603c55405d40707c64900907034074284030002600134803008001580c000390030414a0070000349445002c01c02460311000341000055291701d8040030714241603482c80003502c0791131a9102101c00c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 191426906 1250 191425656 191425669
    0x1b0f0e0a050c070f410601060203130e100b0a030f06060203160803060d050a050102031603141801020c010c080a0c0507030c08030a06030c03050606010906080603032227060b09 77
    0xe548101c0288400b003174513010009040601003d021103e8070204060444101c10b1751044200a22208980460347c07611000d83e01c3e401013064024240881c50f10801c80c65030312841444e00041c9070388000f107456881d01c44404076640b042100c04007085c4c8909052050410a1140c000140b8284c40a1340c1403910000103203950780c0400001504001001c000f2804070742e01e4040541030654000115810b00c1030906e4514040e4104640b0758204540014080d40118040e002c0c00d00840c503100001281caa0710724000718076901d505001080300d5175080c00040c01211007403283d000d0800c1c6580712900140b522189207000d940b01c108065082110a014030b40000f03400100d031080e62a44020100c0c0c9a0766208500301c001e080c1580b026102090380354001041c03060100d2000d001e00c1e0300ba625034000548400003a00c0780c18041d104650554000c22501c55416011940066544051048200855036501085c8249030fa031040000e1401001d848501307601308039200b400b00031700c2c00341c0c2c10342d041c48110400a0f15 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 191428156 1250 191426906 191426933
    0x3200c0709020c030c0106080f0705090c030a050736050d110105031806011401030f090203060c0903010603021f020f0118031202130f1805131b0f0e0a050c07 69
    0x5105401183e01403800d807061041d80c0d003210001c4004c01081e6901c20340d5540c0e456408600e9801401401c4003c101403c00300b01c194841e01618200354a161110441040180b030000c146c1000c100388040c417035a0080b003480da9994040c00c54050500185950001622012115030215104207049511503001904130721b80310f01d21001c2424015165515900c0600020200840400843c061240080f17200720a08410b00041c42080e038040204c1885002e0160459070410000f9606600001c00141c01d00c9810340107100c3d44030302a0012070f070580d40f94081025181c1d45200035191204031402d045800b030f41080740c1d400b01c2c123200c4008c2c442d10240e142d040b103009049040103000c111172074181c410081115011038441c004c032081d540b0301c600d41e981c0300311100d00c1d158001c01114104240c0860b0000c0d64a00039203001d0a51241d040e00c18152551740c1540d610a5000c5d6900130030007000e0001000c1c00c6251521008121074104241c035458084205400c44074010031049803a007081c05860301098506c0d00d040e1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 191429406 1250 191428156 191428169
    0xa081522270f0f08040902120106020307050a1e080f090906031504080702061902010f0c0203041a09180a0902030601150e010f0201060503010f090210020a031409011e03200c07 77
    0x820316081c1c200344003110342001011303140703a50000e03000654401d9030f8010452619480f120b80102d9072280b004076141d200307203107000d45207900c036540d91808101000389000411910b4803c1c2000160310b03a58240080d00815a5500100000314542d10b050130321070f03030a560100b403c074090180c50242d11401c00000a0141024200d0a404034522085454420440f11540d81c0b096401003141c0032510001d000e00100122007010341e00340092a0301450002040d1010b641c880800c01d1246a03941c1820b1072160046082c00d90302100c0b09c3c0060300305580c100e401c1409070004d0300f80440c0280b143e0060518102c8103912144618000314a0751242a0b4400e8440c900301d9800d103411803161008842c1280540a5504250b0b07055107462421221100ba940c054803900b807081d114a180b40614034400c0e611590500800703400b148414034903c0c80b4803c544001d146a07201410500240d903a0165845003003044005010003003903850f0385500f4082c1504804d226016407103134004d13140c404180c0344942c82d80407510030b00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 191430656 1250 191429406 191429423
    0x9060207110405540d030c020d030e070518180703020f0904020d0b070c03110309090615040305011d0f01050606090d06180c0608010b0307050a08152227 67
    0x21800b1140d1510b59041d40c20f00424102604910050311841c1c1d91130501c012064417a61090b1504107019010b42500448583c01415900304422000d50103091540c1102c40300e4098454045029030700d83c803408280200041d8224402d203881356403d200b51803407015520300c640c0325450130001039407240703080403403074100b92600701c0c0544a0348045542110030120040c59000002c04104000764031007140300c40c440c0250b03619880b86c07488595580e00c911401010070b40059030400050f0581c02d01d0640004892618401c0528140d90ba0701d0716801c440011860100d052a503041070b0321100002c001c10811001268020009810810000351480c071807200664000d40081e141e030701c10f0184d00da0040940311411203c00342070040e545050402180315010b644081003000e000400e1502c1c030386d0181c80c441c1005850342c0b46403465502c1d00b50762120008109003641c1c3e000d098903103d81d4031250511014488241e56030404024050f01407400c1e95a850204000d511100340380021030008056100300075600031051 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 191431906 1250 191430656 191430721
    0xc050102070906081b22020901031109030a0b06131103010f0e190e1618050708191a041a01080601030207020901140d080309030c01150b0d0c03020c0109060207110405 73
    0x1c00e0f0031506c4154816200c108450071100d45aa15400400010780f09076001c10040400c601110042e0180080c0240c05600114001c00003e20340d26680e0703004580103281612141625840d441611010039481d400d810000c0010081003901e810380501811b290700b114440303450606100518030b1004120222015200d00840543c094184251004501800c4550868644a0640d40c010024941c14200315900e00f500180b242e920540289024503103240904a00303c45040c500b001900c0d5044074110741c04840094110260b0b078612074841c0c1c0c945602d0782d49402d0341c601000074048200050019060600400c0104016034420181d641034441e07242416072100c0008000c5101100500c0b03000f07000004c00002e22200003400000740c01c001c2c0c400c1000703202c0035010210381d03003002556205600701c07030805000c601c00c84445500308440003021490014102491806240d0030355852000c10799840b80d00090349024002c502ca0880c0b50300f20185e606010900303180001e4451034005800d803403084090300e6070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 191433156 1250 191431906 191431909
    0x6180e06090424021804090302030313030e040c0216062f0f01090f06050901060b07080901032406030f0204151b0206211f1a0f070c050102070906081b 66
    0x60050703050415181c03140503143c21529070000e5114120b401e42c1d80142c1d14a4003500e1901c1d0160002c250b5055001c3d40c21a04c443c0c1148048120f01c0c40101c1c1840310100c580d0000351a24440e0b044c492505034010030b030200d051009a0382805d80c580160040000d03881ca160040e10394220005003c02c034200303050300a00c0304680d0807410014407800d000c5155090002548c148a410050089158040c000130000c0e40c031084900c50032a1014403d50405044c14007550010a0b0314034050a2102c0d01810049400e0000c201804e220b0740924100308810000c0507000d0000303561500c00c00080400300d110840c5001c0c06c24101a92118960107a4010042d103010f010f442080080844003110b40d0283c80d0075121800452030700601645040d40245112000300020046044603580302e0381004448400d1040900b010250903000502048110038605c04100b03080c80301610340c3c000c00b1240c0c0101d0350205c0301428107000a003011100d901c40b01e415400d2403c1440724000129402d420030142c0c1c0125a5651013020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 191434406 1250 191433156 191433173
    0x100e0411030906010f080c030709050a150b1306090506030c07050f010e0705011b030c08180909010b010912031d0f1f12090809152206180e060904 64
    0xa5015590000442031111a00b40065503d041c0c80c0850015401039499011150f5100100300b9126070582c881c500c200f0000700035030710054003c02e683c0d0010502d204086041000d0921a60240440e5940080d03007041c0c40b0b810b0380341000a0507051500702c3d806894900001c6c010302000d40703000749480002a511040000400c0b204070790380700352002880b08100030300b07041d600c48403c1e10900340401c22580351145001650300c1c1003140d0641c9a100e4154010a0741c80f170507120741012180d050405560002c41800da03440005013407007a0300080010610b41c0c041400140316811542c000c5000006032980300000940001098804091400c00340400c08041c000140c0199034026078a03030488042c081410550110618031245d4501580703500c07036242035600140040310340310100603003403010501040d5118a0301b1450260b0000901d0441c50510800b84036070100581100d000302c07281c850b440820400c3d01d41200c90a0203e214000d14000842d281030b034400140680101801e105140e10700c005004c1200c0103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 191435656 1250 191434406 191434421
    0x11030118090c0605070b010b0306011b03020c0d0b1b04060c030528051201050a12030c080409020f07061103040b040f0212070b0901030b04020a050405090a0b0409060b01030f0902100e04 81
    0xd50b0404015910342010b02617500c203107001d5404101140010841090703643c200c0c0d00401c0180d665003440040c0300007090b820310307070800f0883c11400750701c0004c001e90fa502601c0480190080e4506c07540c40c10010400340301910005442200550240000c003c1190080943d14045805003171841c1d840b05000e401071851510403c20400c0340c91030b8200c403843d0030350003000780070f030182c4961043e50107980764420080c202c3c04078070801e500400f40752a40c000082c8580e4080380c9845c0306052860600e17841e0342812050760001d081d10b4640050119640c001d0259074001c0200f84009241a00d286080c9621805004240100701400d0201680310a5007152241d002d00029251214269003046458500c50400e039446000e90500003400c1c000e48401c20b1038580b0031211005001c0e15001d01d040c0c03411082c030456620042003c60140d0b0f440c070466081d80c54500a01003454401c0d5030024001c0407040025040364290100c1041c40d81c900000c00005858a500d89001c0500c02c0c10f04800c00001c0c440001c0242000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 191436906 1250 191435656 191435663
    0xe0601050d06030812070807020f030a0f0e0303070525180b01051b0609011104050604090b01020a0501020f070b22080c010b030106090b030d1107060f090e040f03030b041103011809 79
    0x184100482501740a1140220394036a9045010348078494100d03a240c0d002090400d9913001002544078142c020b4980340000392407800c01c8005001c4803c0040e00b16048078406442d40c2d00302408801c42c14900f500d002d01070441c0704c034200351814141911f90200c5c04a4104200c40c04ae55050750b610640c3c007400c240c070700e5143c1e20038140105884100d20551103000136a80c58180c0d42c00c1c4400c54481c0750452007918259107001c2c00007803c080c600a402405403154540c52030540c000e026070000451000e000414021502c2c1018980e2400180342484c3e183d00000d25403550601c1c91741071220000340d44118107500703e0304189030a40300c8403180010b030b00408100c3c00a551540c40c2c010009080e007041d400280c5684022000c2c0c0d03140501645081d41c034081e514031140c4d0150480001400042d001c2c00001a415016250214420392a10190403040c003007550141c07981808081d48108040d818081daa0301600256802d00041e00c3d4080c6946050006029921468500c81c800c000044800d60100c440280c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 191438156 1250 191436906 191436923
    0xc050c03041202040f1a1e09040b07031e0606080604050103030507060b310b04020c060a0908130b09131a1c0f15050c12062e09060e0405010e0601050d0603 68
    0x54896080c3c941b4074040300305501615115070b1300c0310840f40c545a003800300c040182c00b044059a880ea9a0013200c1c0008001c181810b640700400c00b0134a24080280c1c7c0000002100000c1842c148a4054201500208254841c60800f001400040d5000e81503420f4198000c10111300f100d940d00001e8032420244100c5915021080c2c50390301101d0200800106814640000300700342600c1c0c2081c442a4414004400c1070b6600a40c042042d1506d03a51104d6940d0f4019100350f811308a100292079012101680190b8401d000864210558680382c0114110307c801500d041000b0700d05000785100c0c000d15023a80c2d51003060b183e102d1901643d6184101c2030900d81c0a611882c0c0e801c030301c1c5801c48001e03a0ad0400d040700e103490b00c40016100c0e5004812611005000245040650f031079800300031011224401d1038941c15081841241120004941008101c2207600c0d41e000c42e904002d8000d0a2182c1d440c900c920560400004101c40e040c04031140390440000c0ca00b035552144da820000340589050340c0010107400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 191439406 1250 191438156 191438171
    0x2a120207180b01120203040f080307170403080603010e0703170a1112040806010b16170c16080c0303070c090230191a0f01090e01080f010c050c03041202040f 69
    0x450707030781c0300b03802c0c004090701c1e244e40702d240382c0601600301c3c00111001031140c2040404400891403010180d507010342035160031010701c28464010108510252400c501103070548003030004918082c044c2522080702036000b090918a142ca81213000c0300d0141045400d9800010507000313080c03041c80c00c484c13440038810450343c1e44103503040340300d181e580f0500c40c01c0014081c00d000420219104000c40c0c940140101d580d072040102031b1280340c20f079000c5142c100307000c2c4401c00980034543c1040c80007101c480500f170110f4103058648501241010281800144640c00c20465540041c00c000b0003803040d611a004016190f203002000822290516900f13802c00c1566806000e51030490110400e12a07042e018601d40e4545042610314117550700340c5184030b603801074540106d42c1c1d400c01914000d60f240052500c0002c4c140c1d50821001d59141c20b803c980310a800041000011010902031410902403d1a105141080c1459425101d0103a409281010380d481c1030010195596038204040d00300c601c240c00c01114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 191440656 1250 191439406 191439449
    0xa090512071101080702030f1c1d06090f370b102301030924020c1e07030b040204110c010903120216020603060a0b030106020d2a120207 60
    0x681040504a407a07456150341e0b040c0315442009107500840c01a002035003010440510000143c10140f9506003590a401c0039640ba01454040ca8008e42070681c0c00f051007a16030b54409041000040c0326401a0b403045c51350740d0300304d0300000384501e102d1060500d5001414507d91415485200d62040d049202018507092041c00780a242c001e0049010790882c1300002c1c0c0d00c1c410000b140da00c42c3c001e0314112440e49404c400550190b0007840d0310074814158810000902d02c00213400e000304110510031030340e0110b60321484480c100700607240e20b028001c450700d4031100990015580c003042e0100401001300400030408540301c9400c0b584082d4a0403200320b4854665050650003019440000d40000701307101e038101e500c005284201d13100380f401b4206c1c20240f5009602400040d60000e000b603034001640c0b400000d02192054040c6000e050310b540a0072008981c94401003a00c990b00c0030240c105055000f103142855a000d20075040315521001c010040418204141d040a0840e8450080c601710a079020f03651 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 191441906 1250 191440656 191440693
    0xf1a04030203040e0601020c01050304030e220903020115080703030f020f0312060f01090b0f0a0903020d0602040f09021201030f03050d0c090501030f0e0303040206090d0606061d03010905060606030a0905 89
    0xd50380f01561a1004d130b42d03800c004a0351044050b0300d907030118100308049008a0b1240e003603c080701e18040c01c1e200f8115102c182c0d100b40302c00050907901907642d464214000309030342030081c039a42d0a404e0300b010f807001d418082c0c1c803600c03605148001018071240314216100300d4024003400c000066008140c0c2c0d02c0c0c15102801070500d4004940142c1701d440702221280c0c81350302600c142000d035009100d000d41018144804040b003940941030748018800c84010010040e650b8400e03020b034082c455100561100e1800b000e51901400755045890341c58014014007a0030180303a000681141d4100e0041650b821460605403030320f01c640c84c1003803181c9051042400070342d6040302815007201d0f001c1e0703001c001d840056105882103401c40c2c03400072100d0b00308001090140c41e000b406407008040080c03107607410706815a907040844400303a10460201e000c2d5000481c82081d8600c40d64240e020950007405090007940d038141c1c1340d0000a0009210303200204c00300d02d2410f0706500c6240d60b0f6600c40101c030800003844590050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 191443156 1250 191441906 191441909
    0x314031302040c0519030b0102030f040f091d030304020f04060e0a0603020f12120a1e0206040606060c151a180906011203170a02250203060705030c04030f1a0403020304 74
    0x2ea040408203100a4881c400b120020501c1c0c015055400e207024030120080c084143d943ca0442c8400c0c0004001181d05000a000070600d00e000310b01120300c2c000300342040d10070762160b90141c1121343c00700010f8004d000c001c0b2a842541200d90003401d141c030000240061800b60000316a200110f4104404c440b00d540c0000152802100d003010381c05418810400d603002e1007840e8850382c0d00500c4800d400703d8408405000f003800a070900c09480308901420412001c41c140f1307048010b90000c003d03c024061248101e1018150a150010114107140c03601080d0321801c2411180c002d0313035100000d0000c07840b40044060040010080c070089a4010916030180c0782c207851200150250000004034042f014480c4005d044c2d00d61640707051140c098040c200030031001030103003160380c0c3c0030000d0070414005a010350b18003c01c500780c00f80a00d039440c010b152900380020008400c4c01000c0040c05014a64002600e045903489804100174400c80e2414110100e001140c18001c010a50240002c058000c0060f10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 191444406 1250 191443156 191443159
    0x100e19030506061306050607170c030a0207150206010b03070804060b030706020d0908010513020111190804060f09050901090207031707110d0c0b0a090f020d050f0c06250314031302 79
    0x120060003131000d41c0115001d620580e03902440400c1948002403403549444c02e015800c003206800c00c0d0182c0e08403030030355010900705001a00301c6003003806000203454503400c0c9a582e40c4000e01e219030402407568080e01c000740184062202c0000024100111a000600061000340075a8809903030b031000a0b603110324654000000c03c26480b0041418081486101d10502510701000341c0c046007500199010500714140821501624004c2445c1c0c00e901070210b06141d11881c072942d03803107140030001000d904100f84d2580c1080340544040040e41d46129649043d10041c03840181c5d80c140034501078414091505041130000285000c002d81c65401078164140c207510802036034201d01c035407102164041046040104074198600104040032815407040f0340700c600c6200c03440b05c03040454001600717004414004403070f0383d80101c102c0b0350300ea401030040c4000d4030000d48425080800142154013104918404640102d100010b090305052141c00c82c82c242e0b48003148003542e2800c0c1b80b101d844a070600c0300300c140d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 191445656 1250 191444406 191444419
    0x4031a131a09190804051c0515191503020103110304050d1103120f04020102010608070b0f09220b0111010b03060c03070e19150801031e02010504090e010b0a14100e1903050606 77
    0x903401f11200140540d80e60381c00005070508980010050056110203050b42413100003000c0b44070501e01280c800d441d00c4801105051a800d1700e10301c00101529543d13010b031412894207006102c0007070400585100201594140340c8000c141702e4103420b2441c000e10071180034480342d840a0002c9240c1c581c05143c00b44d4000c0e4000e202580e1134201d15a43c42d211481555058101040010400860031024006900c030080020a5402900760011140e2003608401c9669595070004550b5568100c00113a19100e61a4020301c455440c0d42c001945035000280280c54140300040042d0810340f14070000011000001c00c1c4039464140c4482d502900e00080c01158001029030300c20130f40c080e00841c15141201da110380b2900ba0340d81d03d40c14944101614034412418080180408a0395425600450943c0340b11a800020720740141e1040040c0b1003443e034412442d0016440e200d480d00d448151145c4c0084a007801c1644034800c4d800017042a40d04041c1c10880c6500440c10701004001e0040360301030280404036000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 191446906 1250 191445656 191445679
    0x30706030e07091415031c0c1b08030414130c030b090604110a0302071b030c0306060b13060f120204092009010f08181e15070e010f030b0604031a131a0919080405 71
    0x56000c0c1000d900135004241d0062104014811012041c1c800c0e01e50080d20b5202070a02c1c40c1c08400c29100cfc0c601981d80420340300c00c000860380c10b0201b41540e2000b4203c4091007003e44011070f01c8020311030403041604054000910f0018008001214a007281c3e005010390341c59075403130821401c040d00c80d0000f00c641c0303402c0c1040000c543c03440341c017620500c882840c0c2044606142c50b0382607500842001031241440324004500f4000f4000e44046c10041001080c00b1888407120341065207000103103c41070700140024030052a113640d1005100a29289a04203051951240f03500740704401c85003d070b8660240304064550301540034610201c210b05210004440f4200850040807c003820122115000150301481480c00d562050036842039140c040d040002e1103002400105004d584a0303041030b11040715103410082c0743c1161985051f8000d031161020700011400b60742d54001c60303000140ca20720104800010910000d000e020200400b540d400b0200311b80110303882c0c61405600140300d164440c0100e00c12 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 191448156 1250 191446906 191446943
    0x110306010e091504051506130e0d0e0a080a02041e09050d032901050322050f070503061306110f070501270b0115030b030706030e07091415031c0c 64
    0xf40c00c0c01940d02c00c0140100a090744000c6074405002448607501001c4180c01c1c04101d40c45214110102c1841e80140c00c0030103c48601615100394880c603a8000c03a11007000304440b20012421840c100da04071004116603140803228100e042510745e004601c1c6d803824000d5400c10000190f102241400b17034030107000c2641212028409903083c48083c01ca40849401d01c00341e01e40c4100001c2d5130043d01500c2d1250010483c43c032114584000d610100e80e241d011038101c9560040801603c4003c1104800802281c40c0001c0c52110030101c94100500c00360300c40707001d4500325900c0e0068600e03544180d070981d40c841110b030030f151b17010705400015211580c1f510840e8484003003000c0d8098a6268012005028991808601641082c8900100800c16036a074400307480603a4140015002000035540c04543c2c4088030089600740651a0321401c6103034940200c5401e952000c610305a4003401c0c2c2c0b00c540107000308450100b8181400000c20218560b41c00e00d800104907000800301c5205402400c8403002803900e4507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 191449406 1250 191448156 191448193
    0x9210b07031e09150e0102210108060c040f030f030c02090f0406051501020d050306040b0904080d0509071a0901021011040305060f13121404030b15040903050f07110306010e09 77
    0x10f50250008880400401c1241c5050f0801d0441d8a00940014502444450402500010584c5003131507450754000410ac0b1200400a25800a42c2480c4aa02e010702c2c00182c00d011440a210080040000e0759945040c940101884d819054020b01310340300c58581032094081c0300c6001c5408031a5140303002d010a400b0200340807041080e400c1a0010200c00048050941d200c0d0402415180e00a8440400c0305041d15034460950107188914031702c40d2140b40000c044000e48600404c1ca01c034551141108100b20408243c088400101c80040180c0d01c11036000104c0c1880e1071001001c042070b0401c0b0000c07c1000060000304120390040e4159040d035101c01101107030030f90083d00c10700f04150109640d01e0200321414880e41310111641080c0d401104001c155003550f411641c004d40382d821658080202ca901d00b100e41000301c00b0100c50800204d40b69590150050203000e2200c89588000f1500708100400319080c5515848000d049a80c0c2d503a5441c0580c01070038088502100c503004401703480c0e03c3e00c000740 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 191450656 1250 191449406 191449421
    0x110a0c140609031c090510020307020d080c040b0a0201022206111f0506060c0604050a1106090904060f180615050a03050705131404110109080d09210b07031e 69
    0x3403010f1481c2c00c003184042d4225906000b030303603041d496603503410030300240040007072a604130281c0c42c001d61030f40340c200006401e054400800b4824032200108120046420302c048809842d41c0000b40c58981d1050001207009008030503d03a8a5003003020182d48140300b510860703104444240d602d10035002100480a500c454041c02415000391058100d18440580e0350401130b88900007078400c03400c21800d0642079282003401d581c03d980a410a001c40c505009511402550203035040d25260314120b00321011464010008102509059580c0040c0c0d0303000540e90010788101c00003e07682c050031b40d05070502c540140086440c2d071440e01c0c0c0d034030030000e0350f42070000c07891040b6a002000303011624a40001d00410b20b03036107003e80380704e25038558180c0c480013808406180914065104292900a081c00140010034141c1000b01c055024400d411142584882e4203400d98002480d141001c41400102c2101c409690314000c0100f01440300304010031b54168001c21001007070031303086c4941d03030381c030540320812182074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 191451906 1250 191450656 191450671
    0x81308070f0521040e1501140703030b0a0e060d03110f070303020f0d0e150315060c0d09080115092a05180604030305250206130e0606090d0f0303110a0c1406 69
    0x14080000c0c461804503180446c03405060501c1d007c542c212070107030415640320170000c50109568502e4500c580c02c2104404010f80a400c0d00c1c00386504000c4001032003104d8800000b01040003003c06001503000a12046050080203c21901100c1e16071401030745520900740d905445200b11581e82020b5445158a00341100c0040e20b00d403210680300307800c00e41c51341c00180321a03054a070343d00c01c01d6000d40b684070080080c0c00030000a002c101a95004c01010760b00c882d880042c640c1e04140d10400c1c10480501c0302c030100d444d006400102032405813140f185803800c41c8001c421142240250b80c03080c41e0000b00030034900403034001c0104100c0d81b05042059078029401b002c2c002410034400501c0b0020002010348034502c5100c8030b00840d2406900146060b48000840400d1462660040101480c40d100d0315070000030880d00203080c0440d6a01081440820a001400c5001504d0a1005041c066448030503c1d40c61500c0719590b42c004000050010625a81c04442c0c0c0128a0026032802401085090080e0003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 191453156 1250 191451906 191451929
    0x617130f031101020903030412111005032202040c020703020a08060c120c070203010c03060513050402060f0f191d04020a0e04151d1005090403081308070f052104 71
    0x51528122200441062000b01c00c1d0743c01c0118501e640c1d01000a0402400f01500106e070b000d0003450702c540140c19180250740203c42540301400301e641c018099030744c02a2800d10718801500c1a0f03078907940410340c0000194001d407406003d0031800740d02007507800a8a0003a142d81d07201c16503640c6402e2703580c0c3c0c0407a044202340c8000c7c000c000c0c1070783e208480c9642184000f24040e0034407c4130f400180c00c65841d0ba800c00c0110303540700780c200441e0400e81949100c030074155208100f030b8680307030700840c01070710a41030840400100040c0002c0c1d81c0c4549400c0e6a98050302c802025420081701038003502c00090501d0001002204422039100c61400d8003c580441115550305011141c84030f003408054888500106015080d1003804a1803a0506c0524070315a10140411145420221882c01c83c240b400c2d00b00a00961b640300411000c070b41c00650f170176045100301c5001aa09001d4dc1095507607401803500041004000c07042c440c0074014002100c40689201111600c05850384140b800e616128a1044072049007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 191454406 1250 191453156 191453183
    0xf01051503011203030c0c08030f0103060c0306050609090901180605100b090d030c05120d0b0a0501030b0303041e0b0a020c0f0609010c260f031e0103030c02040207110604061713 78
    0xc0c441c0d0080e4403c5000c2e801e21521086048d0703640d40703442d0000c55001e00c240707580f100104223011880c010302c1511740c5a42000c1058909050204600788650b50711140254086808210f0281d802d600c015030a462030b0311039003028402894a2400781806442a60f090300b0480400705a40b40840b04481402138000c10144504103036035001d81c0c0703041000340d0555040c06200062100f11074244010510418540350008840d58a14100083c401303580d003200f81054501019407400740c0f130000c100c805482816582400038100c048020f00305004a801c001802d890204040c0641034001a00b954020340c2100c01d5552181d1130002d000d035030300940c0a40b40c002400000c4610114100361818003194002d81c0007000b030b1307864140410185078015401025900300c00010445010103506800c800e0b030035800c244102c81d51440c0c9005000d1106060042e00c20382e400103224041240b00c8200c0007203447c000d440591a60741d203c0010b49600c8045c2c0091400030021400985a0022506c0303082140c0d51181000143e078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 191455656 1250 191454406 191454413
    0x1005041a150d140708010507020703020a0b070203120309030409060608071205091209010309060615110102030708150111060108030d060906210503160807151407031e050f010515030112 81
    0x36000c01101c1014081d4a034040317550b100c28045e45114444075002003803042d256105002812045030301c1084d8400b000d00c0300d00010780d4007261040e41c040f034401502d030301c07620b41d400094154840c070f6001d1040340b0726060340020b0082c2c000155a2040109451310745c8605100e15009060380d00458a0460030340004840c01e18450519001d404900070615000079040c0480c1e403804200d03415a0041c401c130300c1e14041d90454682d844400b24922000e420000c1d415402e0400c0050400072000e0620a05504c21080c844500d03445150003c00a100c0f1008403216942e540303c2c0942c40754061803e46000c10f08008020801c3e8441e8003030359048914201c8070700d14000800c410382d5000203401d00d0072181d5000400c0b501140301c1840c003110a82d180100646640d60b0740c64a0000c00b01401002403400c172904040341080404032184680758025180e040205130307600c0d11040501c5080200128080081c980014008400744d100851350603a82d0685924941d1041015258000c1c0404d210f101c4802d402020b490000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 191456906 1250 191455656 191455673
    0x1106160801060813150f0908070b0903131203050702030d0e0f040216060c0302090d05010509010b18041b1502060a0c090f1703070605180709060b04171005041a150d 72
    0x2c0340c0d0390307030001b44e24185503010405aa03510b400076104454042450b00903c610003208681241c00345c402140340c84030020107400c8418061040c1c00c1490881c194040078075010350120384d5030550013010703503120341203120340239100c110003180301401502c40481401c00c900702031084442c0700020140c0d0010348a1540e65501c0500707910414041059000d200d8080940c031400404e5001034403880010841e0301d80b44440508407002060440c1c810700c9000d40d4141c803000c00d00881500301d50003013070040c85446842e9a5168894481d8440e103082d0300f890050780d8500f0303404104030f4003800500f003081c844442c0c0790388215098101400340c0e1500185218080140607460400c2098208640041d00d0a20381151540d80c12140100c0c0c2c2c0e4102811a103a03101c41001040c40307400090400309908201085c00e080c82425a8000c074021081e020b041640c1000d554481001840f48030003000d00c0130b01562900340b40000002c1c0141030b0b01e1010030129408100c40f40c1d12108411a00c401c0030305500321104140d01e51504 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 191458156 1250 191456906 191456933
    0x1090513021606060806040308101202061e19180311120c030a060207110a03050d030e010e01050103050d08070e01020a06020d0b18010512010506030309060a1106160801060813 77
    0x1500d403400c4006070006440c50040300c00421721075015000c0d915107420060f103143c1c2c00030300c40d03c81c03036072640030601c02d603040d400040450940503516180ca0700344a0b0146d03110601c0b031154000103a0b4000c1030305c1c02001d298042c580403d0000d540e80740801c81409071214070034400c030301005003950364101c02030003241001c0094060980001c022101440040130121f4144030700c0000903640103400040000910002940080c8119000e5400d0701807940f4540300d890301c076600741c1014400c041d200c10400400220940180f9002c04052000b0001541c0d2442d241c2d03515045400e0000c08038001e113000500c128000c504403484000706030082d01c5503041e00d1343e45000a600c2810183e00282c1e40d01d403603800f103450b44036280c142501004000d060a50421080017401c1420028418090381050100100f0b91801720550389100802e56081f5200c0d1490b010986007044414000500ca10601d01000903981c0300c4490412590a151142d5007942d0f2260784c03c4038210402c5556150200c420b01032080000c0b186126502d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 191459406 1250 191458156 191458177
    0x1407021203040b04090204061d18060607080d0b040c050a08041226061207030c050d06140a050406061406070f030905030307050f0d0309022d040e0307110109051302 72
    0x20b14040d00c40d241d070420380d04150803c15501d40c0c0440c00b4400c0c240c200c05025014292654220105191003001440004c04a00724a01c020503004c0411036076140d040643d01a00d60041c00d107600c0c2c41d0000644e00c004d2107a961040d1145007010000010940144101c40d1020065998508d45640e00d8440c01c14007541c00300c4d440d0411039503034a41820100c23500484800ea0b054500c6001103828000c0800401a41d089040a05904200f60810010f51410095400c80d001503804c040b0f0588542030250043c00b003a0542c0a003070000104020003c030081c0d10142c81184640c0c820032446840e1217622a10986d070240c815006402008400d001c80c0341c1c502c0c45000c5610901d44041c000b6210804241103400c9124100c80a501000488080c1c0d0814090070100a9241c5010401000107800007020b28100310301403604003060702d0310160481008100345501400161050000c00008083c00e550b9912026040c0c0d80481c900c10b030f0402c90f610070304104017200c44c002d02c50a240f440b039802420095002d0300500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 191460656 1250 191459406 191459413
    0x60103030c05031314280611100203010305060417030105010c030507111009030c1a0901050a03090210050903150c090f0a2402060c2506020d11030901060614070212 72
    0x4044030300c4401440b00600221245e1943c0c021000b000d04c1000c2d07460104940981c40618030100b68000c0480c0b040040794001c3c07070180602680c00c180170342080601c0540f0840b0600020012060020028915003e00d100c0c003c0503180720075040b41011385000c203000713150003e810704240308080f0f0b115002406905008114000f5001e07212400290a891000c1002c40440c1c40c114042041c41071309141c090044c90b010040c4461030182d81030504052144410540c10f0080100e00d06243c14482e60002a40c070340c2c098000918502d400c40d001d00940c0160b17848600c20322a03410111011940441c2c8503005001240d036890501c0e1401007009130041d1604c0c032054100c203241d0000200d488240c00c0403000101c0300140031010301c00188000382080001412014508800c0000d035121070850300740303140680811030800b194040340c0c2c031340000070348281c0f030302c0c030480741c0c200280e03181061600001180074501290082020681c1c400c42640c844112452023450b0410500a040160030840d100328006200388058 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 191461906 1250 191460656 191460667
    0xd0209040515010e010509030a0f05070b13051f3612030e1f0f09050d12020d02070b0405040e010608030a0507061406060703030f060b040315050612060103030c0503 72
    0x4602112021241e980051184442c28412540c100f22155046031080c6009441d194103100400e079110f00e0304000070178080030100b809040c1b140a1107000054410103c0310755449804004080050410f03010b01441041d03d004c141c07000c051012183c4446082e2910346e404510710500821500741715402a00703019807486042c0070031103286031040703202034110740c8401d00c0040c0450400400c001c2034110358501903041410b0541500300c1300040401090384510b807408144044c007000311146001a48456080306044150f601001071501034512114004d0307086400c40c100c03048049955a90b04c1c8140c0610000801c418410350400b80c10050302003440c00004900300c0d68450955185601c1180c0c3d800c0040c0d408140e103c00c10400e070264801c0701c11003d00030001e0381003900019055114026004017455030f2640175520b140070701e0300418000c00440f0607840e2200d9403820412403084101031041c06c1d032031601001030305916202c501005801d40d101d0040c50982c7c02c40d60143c2e0300810749030007038070030f407005000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 191463156 1250 191461906 191461909
    0x30c06070305121305060a1806060b07051b010c0206070206090603040807060f0b01140706090b0106110723090709050d06020d0e0d02030904090212122502010509060d0209 75
    0x3404032911a41d00c031030b9a01103a030342042e11948041c10100c44030005200e40d001080c0001000382d00481144000150302201c50059000d04131080002498070382024000552034400c40082d040c1607000714140d031810260b6005031420701d00e40324801c03808035031080420005030800e0070281c02c09900c00350540d4981300c403c01c0000d401e600101e034212030400d4002036040400a09000320070416000e400148242d0b001200068000b0030a0030400c07814100104042d01801701076000009442e40000102d880c83d40c44107001081c0b40141324a030446486a6200024681c1102d03444400195844080401100e0084200010440080c104d5002c00003116404243c0e0b544030500100d155114000050355284800107040c1500e520080b84500d941080c5100304a80b50044101c481c403840032607002519080300d10000b60090b1048240079654441c0344503c41000504100a10584150211404131000601d03008481c031110355030002d0000710180f00ba11050704051000d00303c4030b000007401504140d1400b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 191464406 1250 191463156 191463169
    0x207031b06020f0a020604030b0a020706062d080316051006121a25110a0503030105041404030f050306040905011a040f060b040b0703261906061d030c 66
    0x1011140c500c80c6140d810841c4035010425101d0035407640d0068860080903400150942c09244005000318164500007262100d00c2d03411200c10342d9001d101000b00689800007803003030902044030807101d00c07a0200366080866220080710200c0b07461200451804420740079900b0a0740c0300e19412112885141032100c2c0324506801070402030030300444108050111030402103100c10749601b200d408602007101344040e2100703020210540c01d46084043d070b6103c1041d41c0880b0300400c0300c81c2052007400307000760741c900300f01d0003000541c12540b040344c042c444507003988000d114610081d9002804285040382540155010f500a0b6600c25001080021003a00390b44480d0f0a45050f214400301d1000d01903030303295441c03a240c8198002d0241070074042101034104020b1074418895402109d902a201080703e134200741c400d400c1c3c944682c40c40001e07040030707500101651050403400d6412850358140f40b2406121a011031162204036040c07542c814402c4001000c0b40c55498240350b486541501613000b40351034603120306 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 191465656 1250 191464406 191464433
    0xe0601030f05070603020c0d0c05030d060b04050f01050306090f04061808071401020f04030f2604060e0907050304030c11040c05040924061407020409080904050f061e01020703 77
    0x10080d0003140301841c0380c003904220060700004c042c14418088884c2514001490b003040c07545c9410640d40040690a0513465402a82d070000043c0d0b0a103170000c5105011400680101c03001079400710b22102c4240010f40c0c0c503002c1207855682204540d000100541c0000d1610340d04035000301d0000801c5450b510542c14449608002550100c0001420070f00300026425025103002c4601300031410b201c0b003410000c80c54861440042c2041841c00817900c1442540d0101420601c0320690072640501c135060f820100390000d100b010003180000c5500502d6090010340207201c1d141c160307145440d41e92190341c140e070a02141401941c031050090b001d41401d4540744601c00000c0400c1e101d441d10389183c08405000e840c0e0150b042c003841e2042e0b80740d05240c500404000c00542c3d026040101c104808408505224040c0f024041d510a003403030042414480c200c8000d001080e001d0310144912703644c41001600114051320b0701303504203842903a4030701c1489520441020300342d03052069401190303494a4103c04200039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 191466906 1250 191465656 191465663
    0x30f0324090a0b120a1203091703010303030c230403081c0e010e0d110d08180106091e1b0e030f100b10090f0b13080d0f0e0d0803040809040e060103 65
    0x44040e03489052510320700c3c8034500011240102030200f8240d807440c0380c104c0410041c1b0145911000e0640c1001000002340880a0070300078400e8607981d5a090040140c0014004040440d40012019504044054901c020615000f09652400c0e141da924114151300070805000c4ca50701b01c030540044d8070f2080c0074113003802c9900000032481400c04440c507410107001d60703200003d004105282e0202144085545094a903884c20b020040303070b55055100f0042c56a180424505510309030000c41c12800942c0800d004040d04030040360b0f0809400303842011501102441400c440340c21802500d00b0b031280e1444914440c002c0d050702d098605103841a8078081946021039005902c940d00b65241c1d00701044860310601d50743c60916003280c9041411841c00500340901c160381d250000d03900303009000801da61401000203030100c805011040c80f0003451250072170000d9000861004e0507003064a04260040c44040c0c10090b0185141c55540c0c440c0f1840d4003801e100c0380c0080d2103402051010a050110302d000703601 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 191468156 1250 191466906 191466911
    0x6020708161101053f010602061e061c0213091103010c0806010c11061e03090d0504061b020f03010908030f060301060f0506030601020708030d090203010b03030f0324090a 75
    0x40520300803041a100030a03850400c04103019444045002001380707200d1400050241c2880b005134007540602c041302c2e00c0c5912281c3c05e10700c00081d5060340098204c0c4a1202d03000c001c4810700540103820640d270415203840341d0000d520410030307900321103402120442a1000f81503584e100f0078101040180c51240d142074401d00d030150051100c5007420300504034045014075000c0121b141950003c2c2c9034400d034080103071aa400d030326401c41c02c50301c4600c00c4403208003507001d00000c2c1043c00c82c80c04c2003a40c0b0440c0c0b00c2030f05015200c1200c180f50b00403001c1e201070321615201c0388102030f940c100c0703000710039905c0c241070f43d103d20301d41d4500b0480e440170310a0400e01402004800d90b21701d0048448052004080d0095009a00d001d104004034440300729450142c5d0411610300743e8a45821004070314001e40780d00905041d0200203a100381c07074501a80102c0000b482036000303201c080d450380c1c109030b100e000d00000311035898400c2000551004851070b081e1b88102c5448200301ca541c4100021030f1525004403005220540d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 191469406 1250 191468156 191468197
    0xe190f0f06080115030f08040803030c0702010e010207030c15030603060e0607080f090309040902041509050711030c0706050702030709060806010f091b1209051b0117010b04060c06020708 82
    0x1400e5001d10005001c940c0d000340200c0300901088400030ba034511000e00750301c980c0181c03001006500000c440007070016104a81e220305140c28050a1903020358400c80c00304240071500c11455002161020440c1d801c0f500c0c0001e041c1ca400c90119201000c2c040711810150b4030720002c000202607100c0c0340c0703107040507000030221454000d001074488031001d8100c00c3d81c60b070103408008aa61000046402400045d107001c03502041e00d1000c1805000c145608162044900101294021041c0e01440c81101103549a129600104050586a12401d00c00565070f800038242801a0b1b0700440003001d0180c4040c04031641e40340e44140391800c8030034580041c056900004010000b000408440d00c024100c1e81204118181d80d030040101001c010709454800d2012a2403c0c12072024190b014102c1e82d174002098801c203000144000380464101001c6a000c034110905804403080c030b60110303905031282007900d949420b0902001796807910240700101c2d003a40c4c0030061500007900d41d10241c904900c1080001550300c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 191470656 1250 191469406 191469431
    0x1090f0b040e070203070c060c0201051213050d140d0e03040b07050609060a0608030a14040909051c02060103120c050327031209010203040501080a0204030203120a020105150108010e190f 82
    0x40b02c007800f02e80841d030040c8001800b19442400100c111541401e0070300c00c0320010300c01030303a45005110100c100c4107030b002d080042200d240c94641c840e90344280c0950703119000d04e081c140d5114444e00d4192210702c0d4107011030640350704c0550004425481d0042202d085c1607541d141b07403081c1d500c001402c695030f4000c80c09214008000704885500000911003e2003820b040402d0981d482c06500d14000c1000400b400c008814811081250060141450103011800241c2000c0c0c1e540d4801c580410061640e01070362183c0740388081900703810fa95202c41480d00c0312088000444400000c00010b0310103002c100850104411400e42d452050050f003880c141f0116000400c050030a40d501c526000b94a208102516a50381d02208560660b43c00342004906a01e45421a400a010310b810080d05071103655081004803c0c2031003c0d0240b401c00c0d50080c000381e03503812040c1407880030080086010802e0795006028690b8a2000d40703511000c090703400b10345107522a003024141c1c0c4a080c98814080d03610099203240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 191471906 1250 191470656 191470679
    0x1103190e03040e070e01030920031e060c07080f031509061005091507080414091f03030305090f0d0906030606111b1804030306170619020901090f0b04 66
    0x1503904502031801c2c0740c83c0c0300400c00c00c030750001d00100070812100c03c0b100d401da00988c0451401900803940b40d440b068000f8000d040c00003183c2c1d42034030912603002d03a000c41082000c1d0f09581011120090006030700c030100302003c99080700c04200e5844109001c06003120024101a500c01d03035003c41c80c0c0e42c071803040d13206000e4000f03005403103940a504456004886a81c2200c1242c010920a03100d04202015030410240c1d64007809000a04184001400294019410000c088114421074120101c1e8072000c0e0003900c1403c1c1407610403002203030003404001090013580704a0344084048152022540c440081c0d6050150342e03040c22001c940f81000922806a02d4440d0f8400307801c0c182443c500e51040d01d0f0440303a5902100c903050075481303450302c1d110350161100c0d44c440080c4070440c40050020b00301441c1c0136011340100d008116000c004520190121000001c41c50b005590a1602ca05080c000010540181d03109100352418001c010b800000e5201c2d04180704402820551400e07900c560815084448 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 191473156 1250 191471906 191471921
    0x603070e07021e070911070b04031809050a050603071d0402040c0512070206041106040e0f0c040b031009201c0e030d09021c0203060c0703020709020412050c060f070213110319 77
    0x1d0404082c0010800900b2032381001e0340180c1c040c1002e40409174400404502140540c129061550828044c0441c00005801041c000e0302d0403001d440328161034016030014400750f003443d0031b0a50000b0b000300c0d002d410954032840321040c0903e0428a00040c032070b228140c02c7c0d402d50350500107034021820002441581403410b01c0c4c0d000c08440e8030b481d29240c008030316090180030340f21090f0380150b0008145e010322802c080710002c04514040d50f860340303800780400030a8000b81c81425029420303d610031901d00c1c0c105c0185110210075102d0f8a0600d04004070020020f0101100842095640c1c4003014a2a800304060082400c0001c030100300c000091040c0920100f41104014070500310914510040e903010943d07a51180100038190303164001400c2c204e1900380781c1e5001c4483c41d880010080b031078540c070300d005151040c000c0f0115841c0c0340c0814240b00a034411541c031001102c40502c461001441c0c07000c1c0b4201d885450510214540c20302c09480309869000f940ca540111228078070681c0a0b6210340034994 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 191474406 1250 191473156 191473181
    0x20a0b011406040509060f1206010816030305040b1c050a0f0f020a0503132603041209080606060904020705031305090f040203030a0f0c1502180402030603070e07021e0709 75
    0xc05000000040b4500f40114002c2600c5911a040003c60f20b454000f540060140c0040c810542400200c2c0c1c410746850080c01201c8142c0039402c6842d000c201c2d540303000d004030303549507481c64130305450040000115041030744a80d5000d4150036036038003040c04034009e49025840c1804002070400301d00c05408110f0306254003d000321401400071030601c1d40c106090300c4e8409030210b8051409452490200508401d103201101c2002f088058620720300340840c003030340c4030703e01c164803854a03820000c109403107401e818800d0000503880320b8001044d9042ca000900446003002d400507007440d11035901d49045800004124041d2600000100036a240a041140d0000110f0f40744071740314101500400d46034429822407a00703000040e4004255a0b12a4032904001d64104070502c18442c00c6045034070180d0b0010b400d2180110003410030051500d4280b0849006a400a0052080514007503001a01050052000c001e40c000e4580b0302c1c61966660300350000c4414030b20040c00416040c2082041140d0b50f044110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 191475656 1250 191474406 191474429
    0xa0302040b2e0e010309050c100c05010504030c1202030304050a080a1103041502070608010e0103060b0a120609030201060504152606070c060f0605012304170c0306010501020a02090403032406020a0b01 88
    0x40461070101e8594542234041d1455800c1c42044041641e50080d240001400c540c0707418100000c0c1948102e5102c4902c3c41040701c1c070302007103580c0030880c0c0c0ca000907a0040c00a4004104000002d2508801000984464146004801007503203519003960000d030b115129131800c3c2100d110145a06010700d102801c1242441801941010049003c0c500d050000400e91039541c2d451059076601c44040c200180159527007a00b68940d90319140d000340008050860166003090f40c00705070740c5003500402150f000d408a80c1c0f15001d15041000d00100f800c40509188641c540e428140c01080601260f80b2500c00c80c0c071350700340381d045902c0c200085030340c00d030f1100141c40d10f0210305221981e403208918010301d036080380c00408007040c03040c081900c1c41103901000411144484641d0014070209200100c00011410b98140341c6c0e0f240c00582e2030b00040d0304000d44c00380e00c80d0009400a03009501c4203000480501c40b044804080d48003103c40481c85802040240e8072198031903041000f403002c2c041c003500400041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 191476906 1250 191475656 191475671
    0x120405070909050d0305040507050a030501020912030c0d05090a080d051b010b060d020a090902130306180317040303060506130e1005221107060c1d0a0302040b2e0e0103 74
    0xf020b80350340000b03800b0010542c8810208062210410000c006004010070100007036070b0b68500315000390312003015240103040703021680789070b82004001e45485034550390207004041041c4500301e07055030003c68460b074000d06600e030109503a4000c20a180c03400c1042d07118259150500b05911060702c3d0303103001e1022143c3c144031082901e522041c09a440614200c038008d6210007082d04280d0f8041d0703113500085510303072003c42ca00005803c0d16001500712801600100112040300f01410301091541d90054049030b400c001c0c1a4015544071b00c0320364001d000e4a03000540c940c07100009591580051b22a1940c0c010f442414031010b01d0016050703410030012010110b40c00c0c80c15011420710051116001c1c1540d0045056074100342e12608500007010300c09030368035660145484c016009180011070040000d0000d041e8640c1100e8020f042c510b160301c018028108546580e082001401c044210789420818041c1d2540010820010303030b809207903101c0a4400518051180200100c074100840303070405040c502c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 191478156 1250 191476906 191476913
    0x305160609050d0218150114030112110a08010c180905070f110c120a14150a0f09060f0c03050c0703080a0c02160b030105090604090b0f0a0f02120405070909 69
    0x907058100d6900303030b400a058031038a00000c2c860802804101c400200803408122034050034040303045030003409032949900e480ca03141160f442e0703010901400e2003130907034140000c020550900c19001c0c440303402041418040d032103200f0385096032400b00754a400700e02109404003a1850409101e0042d10380c500f000c004a02c4c0402c80100b0f442c420840507000d000322881800804074003032046018480c1b000e02901c4401c058003d10540d80c0c07802003c140c400000400d605500c080002c0740d90800d4040015540c40a170f1640a0410020075007409001801d031f6032681400d0002c0d45500600c220f180145070300082640c83c104028080c1c1e00010039044508208100c17400000345c02c9004941c1002c001c0c000020a1940760406030f2500d10100c0d000d024500d544d01c030000d171100100e8000c4d0306855083d1481c0b469500c410052006031103410034000c11565190002605402d0881045030707001100c0000882c446120440c594100d9200c0070f40043d20409850400c8140441009001c00501c2000c0c8104006183ca45 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 191479406 1250 191478156 191478167
    0xc12041404020f0919171606020303091b03010f110c06010905240a0308040f03050c03070f0612060509090d0206010e09030a180e070509030f0c03100c1407060603051606 74
    0x403050b2117081170342c0300505242d5503040103002911031004554961000006e205680d03030000002100690403548001c6400c41c40441a68050601c2d4401000c0709140b402220051468640146030150b41c0c40203910f4440c07a00c0d0141d9401e654100c0c440d02d955a410400700d80c1403135016080016a1410715040c000201809008081101c513421384103248070038500b00080324202d9a60014020f90004140462918541180030f81142e1181c0c00f102e0203000400140758441c4254403036441c00b0030b9858404c02035640155072a06141607640400200103484000080703070284140c83c420320702d6114420088103650108205400342140915286240c1f5046070420350324428801c40c6e00c20480526181c400481c4402c1000000d45014128186c0c0c070724054600400b503810440416100744280300c005019100045100218280c020780038044000070440f10202914001003103e0402841c1c98401c00c1ea100c04c58050482e8610aa0f00400c115113142001071800e08452020083c0742e010a038208240364101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 191480656 1250 191479406 191479417
    0xc01020a030e0111030909010902190e010c230609010b041a0f0607050f030d09030305060603070206010b09011b0c030309062118050303100f060c0b060d0204020c12041404020f 77
    0xd1a04d4600110101001400c44c00350380803140d04450744a00202e00c04440c2d402400e41c003503280c059401070b11010302048815070302c56105540031503803802c180c2c0040350b4031400070386141c90025030010103442d001e02610319201080320020704607551a00d4454603031801d40900c05181c1807001d40003000c0001500000d03009065090300520428001801c502000340501c11902c440c1c660030203582d241c0134041401b01c080e15202c0d41c2200000e1038440000d11915007241030300d004602e180c2c01494141e0801081c0d4a01d0352003650728506210030f03901c40b50122440e8210989006120b206a40840751961801800c9401c00390001e4080c001610010383c0d000e00200d0208c1c15155034550041050000780b010002c1030b030501d01001c2c1090100104000f80340c80c0e054102c0c0115566005907854099641904a9030748003285402030034030402d02c000c218a885e01c00b8200e2941030000344011301d48994400e10030315111001850b03080c0311601050400581050420040300303003106441c10341c5400b10081a403c0b042c400c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 191481906 1250 191480656 191480659
    0x7110c060f22060806031c08070c02120d02070e0603030f070b040201050f04120c05030607050405090c040e07080910021207080415110403110301061d0702120406110c01020a030e 78
    0x810600d22204180944486420b50341c00d4401e00a519403500400c551300850b038080c068496192010090350288260f0042400d95039600d81c0f464540c22412284501142010390b84034a120800381e2401c401404002c640070026001400994681340d08141003100041480f4883d070400c0c89080300500646080b52a10350f800b0501007199580c0b44016a20350044480d0342d07000d000042800314000d00803201c2041c04900840d941031a09649400300741e5116030450340e0385d0004200b44410031160802c1c041982d01710318800081307820251200d040700101c07101202d103540064281e2080c443c5241c1c05200c50640c00c00303211010b5251065480a03804880c4020b40b0b070a08010768040050140b10091210304407408003a441408082d1090700d030384070f258220703001c10b40301141d03500150b51322071905100760b0007200c1c00c1503189080144494403080c4c0750a4010020401e600458030040b0301c1c0942000204003411342d40d254611408a074640e05417130569902c40e40c03815548410345a43c0400d40081001c00e41000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 191483156 1250 191481906 191481937
    0x20309030c0406210c08010501090b040e010908041203110303090303010609120b150120010b0a060806090705030402011701151202120f0603010b090a090308061e060a0507051507110c06 81
    0x910b404407174400c40368006010f5529000010542080c981c0200c0841407045800f03201266803035946c41e08035400010014240d58007000108480c6070039034010b042c85d81c000c1c02c110390004151954207081d80c0c41101c900065420020050180c1a0002c420501510000c0003007080e20b80c0c55130b100300300080040c0c0941145008950086821b83c17090301281100c0d400d003a4400c031420003205255002c1c10100300076070b00c9101048000300360b840c4150909441003500034240140c40d201c102055804d90b201a200743e041107120003000c242000c9884880b4000e1468034410603145010850040c9900306000ba002500d41c010440c03401c00001d641032140d0002a06290512141c8601b0b0009005002e01034503d6046445001048144a12039004c0d1070b50a029032148019541c40404000e40a000680c1103410074090405e544405e050450280c00da001040c00c120740b0300b400d5512071504d8142443c0494104415000403c11619840500522200a51001000d4280c1c045001440b50300409c44501400306 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 191484406 1250 191483156 191483219
    0x50703032705011e0b0303070803090a020904050f01050705030403020c04240611100e06190f0e011a010806010914060f0a020a11010215060402031312020309030c0406 73
    0x105040940190030034040600d5150003454908a4083e00c600c2c5044820100c0da441c10b451080136500508a8000009000e5460f03c0c1095540440503000a804a000c0344101485540140c880c8800c0c0d9001c2c0f4080c50080c0030141c0d400c09072070300f541e00042c200010032506000f48400079800007000000756004542c0418050048200e800203c00b4024000c3d2095260304270000300e058100007000e600d00d069001f540c10f1300861f1902d4030142d03805528104c0b601d038024170005581000700d800d5518210700d92040443c3d482c01a4050f4010749100302072058890359110850308841062804032004000c2c00e003044206840e00e1000604080c003d40300e100040258040314032442d641d001d04460700200c3d56002282c49d440b130705500954030544180d0440d00500032200941e680e60000440017a11030a242c0315164030341d540c0b400e02c0301a400140601100300c81c204155000542c080981c0075004480740d00842d1110310943c205440c006440b00716501542c6401014025104600603614040c00019981082070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 191485656 1250 191484406 191484431
    0xe0603040212030a09030302070b0f1b2e150302100c030e0901060e090903181e0a0803030709091a061c060e010317120403122408060c0a05070303 64
    0x21142d0264454501000400c014200c0c3c000714250152406075003155201c6407990356010041c490b2030320b159818032041c0300c032130000c9804981030f0100480c07003015580c040b0002d5800ea442c00140011504d00074040e404c0c4200c21492511031103a01400c40c7c03a428481c580b45070003090042115003a068100314265140105060103188442d8800601810904580da5100e2008001c46c450000e15841620b0540100300c040c0d40001c01d507803581d69203015000d02214560308200f10041283c148040c2c5100340c40100380c3d555a05009003000300a007001031039681c030340004014040720868100754425441c281d800300c0110b0340d06221100000060f22060f0f035030074408200350940400358405000740c1b400d041000c41d081c0302211a15040724402c807e5070824046914400185004000c10001c0d0148001c0c00940401d100d03140c20300c0d03080a844400195254030400034070100307600783c16205803480c1007001003000c9102007003130541c44420705d800740c0d0402900d010000c10910407014054105901c84c030f011000b4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 191486906 1250 191485656 191485669
    0x1b2108040201171b0708040501020106270c140c0601090609150b13030b011d07081608060a080f06100801090c060302360301050f060109030f140f0f070b07030e06030402 74
    0x19003404c1000e5a281c0d0654075004003c1d41c01402024015401d00000181e0600c00000541e2036841304100c03221300e440169007107001801c041c40c600040007203804041e610f0b402c084005000140402c1c01400309981407021a0b001c3d5680d55100045140c5003445130301d141d100b995071410594003048140e40d03640310142499a07400b6141d1b0070180004051000000340c0140c81000003520050085034120581d481682c01c3e0707440001142d01c980030b02c0d94580606481446900c3d115130140d801011910500c0e21485844e281c042c2822009185070700c1a028001141140b0f140000102220720007800043c00c1ca40d9204244074144c401c0c0000c1c550081440708002716070f4840080c0315003032842c85e034080700c5649641e03244241ca15080180294a0600810003042400800910544d0181c503a04200c1d440c40e030741c41c40a0f00000405403582c001c0100c45c501144422710000d03034048001da00410b090b850f003040c918204681c039070000d44000303003c00400002a0b040603841c1d142171002c0b01c10b1500d9a607a400803421 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 191488156 1250 191486906 191486941
    0x1050a0e090102040f0e0106030b061602010318062405040c05090d0303061e18050907060c0507030506160801091a1c05010c080907060905130207031b210804020117 72
    0x160031175828000300f81c1030902189581254403540d0180080500d0038180040c40c41240010139413044204a0b800155010303410185070b884400c14414584000c58a44500311071899a5585040e62030328240c01c20803881da020000902021941040000030181d005000da120700c10702d0301c1c0146d030b1450103281814025800700c4014483c600c162080149800c04000050b4910b02a980003c0486130300c0141d8490180320311403041e6100781c01880380c5810001d065581d500f505030111001e22800c840800010010303c611401a5031280003204101040320000c0c2080105801030035034145461b016880000c241c4402111011050b42c2c40c5203018000441100301e20f40711b4101608941c01d04d0400c00c40d43e03502c50340152051f0304c80d00a0b540d8141e2151812104280c851265680c050301e06039045113260042d031b00a00003284a41000c903204c40c6408a000d6404200300c1d4192000000101c0a920010202c00c02040c07500742407401c1600e42c546507001034200004a8800d04000e200f4030700040340080d40341031222 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 191489406 1250 191488156 191488169
    0x40306090f0b011d09010209090714130308070618050d0f050d020c1015030218090a02090702060a14010b0a11031b01150b03100e06010c0204050411010806010801050a0e09010204 78
    0x18100d603194410080300e0f5040c107455803101c0095031300003000b10030180700b69100784000419844607902d80c217004403842d0110300d03140344003200c0c10006401d440c1d5a204030440118454103d10f42c56440e2400c0050464000728040300c042502c4407112000600041040c021042c0e85050202004425003000c40d000d029000b080c80019100059515500d00002400c0c0b091034500d00092040807107c2d8010300340001ca510000b03410094025204e140555085085903002a82400300c2c2c0100166800080401c0001d403a60800b58110100340140050390340111508209a81e09155295140c803240c0c46840c802d050520040090320310f8a0541c141c81841101c09401c221700501e9010012120014002e181280c42c80d041c0107a4500f000031038541340c1d02900c4c0318005440fa420742d140d242500701600550018040c41c1006000d804503401039803180b00d000e004501440c40242040c090b82d0001d0003850f40a4503460510107603000411142e51015410710540d111680911040c0c0c030742c4030702e0720b0180c0640d401a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 191490656 1250 191489406 191489423
    0x100e1036060f1406030709150608150a0b13090c080a0504020d020a0f0f1d0610020f10090506060d1218080d080f07031806020f1e040503011d03040306090f 68
    0x620b490b001d43c645640100000c030309403100c5a5071032050500325101c852502a843c041320604103c0140281c2d1490740c0702810200850704010140000386810200c0c0e00b04080707420000c240c00001450740b0404030044c00c0c4001c000c2040d041458030240c00107100070828105183c40d070b00001e0854a6181030340601d6035014011150440c0c60b08040045c8481034060f280c0b10f01401000090901c903190004440071418401c010a20740b41c00c0c044c4104181910421025407080c541e03000c00818003081041602c004201002410340058588a800c0c040302902840c454207900d007244011905407031500c0d1028100342040100e43d8820300400b1034200c2c166002c1c062500410b5200b1203000d4001c40303058030030200060040c205aa914801750300312111141c80c0700307004030041b690b080020300c1c1da40140f07000742c0b50610040c00c05401001000d0010000c9180f004807880105081080381002d015030f00d503421179080b6901d4620800800e00d50b50b40243e100103800c4545540111040c8820003910000d4943c101032039 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 191491906 1250 191490656 191490671
    0x3120903020d0e0402031302011b080a02010912030b0a05010302090a0b0712020609070b031b190201140a090b160302090306161805011d0102100e1036060f 68
    0x1c1e454030525120040851900000800546024401c40f84200c155440d0048881e03180d400441d40304060284480d210103458000c10007242046c000741000c180641d0022505555038078000c5c5030f048410310b41405060130040402d2603550307400300300030540b00c00b03190040c0c40f80c200c0c1c0005040854194030666026100052100921488605030a0042815002c072840354032071907089946c13000e0782e10030348441d51820b10100d008820844801c950a420680c0702504180e020242d0941d222000001c00015070354a104605147c454000d00035482500d00d0802c128a10b040d445004000c0d070001c04102c0f001c1c1027040303050003541c080c1c3c0c182c0b1003441380a000c41d291413400800d106030480404441002003581c403040100030100082d040c5094a5041c0d5540503007070a0381d8482d0344c07c03100e841c0f00d0758194000d40c030341da0358082d40e6403042040d540f407500c0040188480b152103040464003a504130300e0414409403c0500c0b2040713a210782940104181a9045400d07145081000041c4114a90121018200144c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 191493156 1250 191491906 191491913
    0x9050a0b0403060b06090303040603050703020912060702060106031107060f230114031b1905060d06230f06030a180c030510090b01050f150a17130b060904031209 71
    0x54025680324150400c0300ca5044c40421001d4002c0000a075031640c4200001c0c00454031036045180c0143c454200036080100f60701c00a0440c1e041c0021820352a40190100251194100400c0c0e00400c13143c1001c000d07961001051030384c10b1080d40c40241c040c5440e16420780701c01c20681d1081c00d8031000110401d00caa1504901180748a100b032250360301c014a0f881d0100020302d40810b040004a84040154040800800601c681c200000f000e0075074080b08035000007880c0d00d442e0014804009030481c005262400e15000e03103006000c3c2003166541e0711070360842849a480714039440800310b174100c0d00c140d26036544006034030250840d841103030719161440508408100030b4882d950183d910403826505200021a043c100302c40c2c00c8003001e0050041c0e0030041266080600b081c07082e9450140c42d42c005a44003900d1402d4550000121000040303500da59010306a010400c031503080040700740042c06010050300c2d4902e407000301034403152050b480500030404150103401e185e40c0700140100c0070311000301d0608 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 191494406 1250 191493156 191493179
    0xc06030506010f09080601090f0207050708010f0606090f170708070b19020307030c020603150d0503030103021011030414060405130608120708070f0f0503070b0115050c031909050a 79
    0x580c00703804070b0111009014210300070007211041e035055034000c003101c1c0e203070007041d1010b4807500e607880540e180d0070812280400d0050101070b01078148080081644001110020704591090340043c042003800340052040f40c1035101902c1c100c0f91551109100c5004d0048494200703280f41e4400c2c1514032481e08002103c503144000340c040104c100102100f14040104140e0f102d11903120001e00040c003a90505c0300600c2c1176005190040b01000103603000d1042c89000c14417451052405480c241d0022004100710710700044100081c6c2c603a131402c02d41500c102e00d4600da0328002c6004502c03510180085d12801c030b40f51082038900402000b0040e1a6440315510724000400107030055a04500440e4002d22102d10840121000240e010440d146442d145458001e60750b0101001151480c50910391030740459000c0015240d0305014060011203540f414500c01c0d21000740b51014000e011050200040c0c403000802983c0c04565900000c0f85107042c50a000c46034150b50740c10169012100900c040341c40c44201c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 191495656 1250 191494406 191494411
    0x209250e01140a0c060c050c0115140a1a071e0614090706021002090d080f13060215071110110c0c0d050604080a030605040606030c020d0c0302190309030c060305 71
    0x7a207a11201d031680e0105180ca51180f05032000108184072880000106507034412589007a0518109003031480d044009400d482c03024180304880d2466040a1204e22000801e94035030001c01c0320300c0242c89180c1039401d007110091a441c503a500d2404601c2e034003805404080c01142400f00c07600e000c9180e025140c140d00403c6280d5104100007a03c200041820f0300c0007520320242d0b41960018100e2900c41c1000b01c01075803149a94582080c251070107400040c00481c0a820308a154000303454039030348070a6601403100d1069109104650007041e601e54084e10b00e038000364201c42e0a140801d1035920002d0206e01d010b0520f4050240b135842c08403040c80501801016003800b5680c00d09075402c00c4280030400c10304080f0f4480150285e044200403c0000744400c0c01031400d503085007804580320741e650700020304541d01540000c01094590348800101981031040d07040701292410f0001208485850003950380c02c80124221044091150f8074040c5401084007030b0041d0b910080812181d521100018040c0400303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 191496906 1250 191495656 191495659
    0x30c030314040e1603050702011a10090506071110170408030a0b0d1b1a0a0305090a060f060302100507051203090f07081606050309100c05090909060114030304050603040209250e 78
    0x14800807d00b4a48103000e80404440301c0044035161028180030071500442d13110001707040c0300301441c0010382a1100c03005010030b07c0c01404440c0c8403007081824480d103c0b4001c1c0600c0200451014540000203c5c44582508150450030701d0345c8036507030320001c4801051002c0c0600c1c1c1c0111a01506402c114101000d0320b0314032603007200035407041e540d070184190b0240450001c03121000c061101a007001c0c403075480b840d072103650803044a0640401e0744520003124a60b080040f1442c3d1241c80030310541c2048414120011010300c3c000e45090010b481d0a074882c49804c0c4105c040c1c0c000000801d00c002404c006444c071030f00f0418192071105545100745542c42181840186800034400e00000e4400d0041d0103403842240340780b02038030b080e204c00c802a500034076000ca90308050040c00c0c400300005403202c2c6490303446071000c070004050550410780072a1030f101a4000035031196000f003009100e19168401541d41080d03041d1004401030316000304802c00502a080903411071641c1031002018a6881103816450f15030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 191498156 1250 191496906 191496911
    0xd061a12030901080c090109050a060f09120f0204050406020d06080102030103051506060a03111902030901030e070b12130206070c060f0306030309031e0c0b0c0c0604030c030314040e1603 82
    0x10340e040090303102e01030701d00ca4a011a42c0207001910740d40d440401002041414980800751a1300c4200181225200d42c0007003000900309803e41e041a0f03007000c00d401c040d003600140e400c00e10140b44d0350910341502d1144024083c1e5126400702d4200905501505c24070001d508050000701d41710341400b8000c0d002440305480714400d208103050300b107401003d85405036501a088624250340390320140c014016280411814010030440c0a00c0140d0f5403080480840c402c0d80a541d0310200d80c4001030540f01403286481080d00185400c101030072001c0d0444140e055079001c0c1c040d42d45d44580b0f08240c00b49003840040d4005900040313020401201024078000d40341d06480b00c02c4282488101101181c80700d000040c01318942810130300c0032803000321000000c250b251b1004c1d0340491555566074101e0100341d11072528880c0128011129090030302512400c24410750342641406e103591036070503001909110150038001003568205c1026140d81c201d502a025014004810b0300b0100108909011b02107a0030300082e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 191499406 1250 191498156 191498179
    0xf09012c090a2f091005060d020a2007060f1b08030105090a0603020904030302090303090a0305010b0f0613140a0e09060403091e15030e0106030b06030d08100308090d061a 75
    0xb00c1118030030305000003404100070140012410702203084d00240c603403450420100c0c40000c440c1d0b1103200402c0c2000c5044400350b1102c20f484000741c00c1801d5448200034030303501c80c2c2012089041c001a888101c0f03a0703c1c079021140990043c030980fa0490903010820701d00e0301c1b07024654144860f24000b107048410075688003001d0b42d5040025804c681e03035400001d502036001004a00030030700c00e4001e0401d40c00018252460b0489120000340a100250320440b081e0751520344004191404266a900d1070300140d94540c500030000d84030220b81a014011600b00780d150025001194031000000000790251008829843c2420700030a917540f030301218210001400c2101c0450711080c50b00d0f403844550341100e03051044604183c402c604e042040030003901095a40c500c41800120b00b40a008000c500604d400110750801b48145801d1014106100042c406020203114460b4681d0300c5500440b608272602c01d4644008900082022902e2400030f044241000346002c108248040304c040d6109040f0790720740700c13035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 191500656 1250 191499406 191499443
    0x51005030a030c11010e04020304060f050105030c0604151806020f061b03040b06150403060504050f0c100503070504090c0509030f01060503070605030612060f0a0b0f09012c090a 78
    0x7181a440d000707000446112041c80040c010381e0324407aa007681414400110104000071404a8204450580d0400d44070240a5400442480b0f078a01400c3d054000d09052480000466590311481c826401000d03294000b00303142520a03010800d540b00002c122407a203540da420025599900340c141c21115008600110700c07192941c0d41c1c1c6085007803134043e1907410340ea160744400d42c1034540104000c0c2c004c900340b4031001102e99464000d1015610680c4000b403a0b061604000c0e2401d007864131444040d500956032500d45642e0080c0b04031500c0f10a2a019541795a520000ca82e1401240d100e03881a500b08a205000c05c0c0d0808090305507500c00b83d0403a817441c5d0040902d14261f4002c1c1c4a6a901070308110f00900406100c0d03002194821000340080c2015850b80045514114048500000070071072030040c40030381c0c1d50a004015204604550b1541e01c4001400010044c80c4107100e181c513480f095200f41560101c05450380f40301d0310403a000100c028941000c2c003c0d00c400c1120707000c03145600011030004c0303c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 191501906 1250 191500656 191500663
    0x809060c040e04031d06040f08060a200705010e0a0f0b07080c041202120a03030207020a0e060102030f1b1507030c030e0309100908030f1908062209021305100503 71
    0x1250081d00e03110450341c0301c985083d070b1a4001031003401103c6211740c02480d00d6854802c0100010b00700480c284241900e44244103040280c00707409049000e0070406440384200c44813000400d00b00d865042517566000d5441d0950040140d0341d0a40801d0090310b4801c0244041d081000740c07221b004403400c008965924004460404080300c1021600e4014002440301402c3c602d810b0200e144041c201c95240340c0504401842c005040101f24002500001d50108608190360000c0080001c603441400ca0300307000c00080c0d2039006401040c0c8400d034000c600c503446403001d41000702101a8090a40d071542c4074140303001031000c2044440d200800d0601d00e031070203501e00c02d200c1d510882c21020095410008184200700a140040c442c0400300300c0c04030004100c00c0c0c01400181001031005101c3c590b518000454512210103051840003402100010408107403076000252184540d02e00d18120488801503045008040c0420081d420140311000d100c07d500c910340c411805058030030410b0389565500c43c1050340c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 191503156 1250 191501906 191501909
    0x120521090d11010210090c0603060f0312050306062203020102120a020714030304080d0f021207020607020d06060f0801020c010501120201051b070b030a090b010821070206190809060c04 81
    0x700710240011260100d070000300d4200140c0c1051056070f500320200f240f00d1003910144903007030303c0e0991010010000306805120700c000030074100034002401c61440d1604034480f8415501c030f605100000000902c1075881508444a0140d09180f190b4403c1600220403e038015a004c00ca016114090004043c03040c043c0a40310110003030b9000f09566420610f10300301144030104100e405100500001c1103044007841121909100c80d51035140f84071a01c0002490608400c40003054500100003820142c1c032004101d61802e50141c81d00b44510449280032001819542e00910392040c4c16000814080410340050103481100d00080c405640c075082110700100550361b00902107070007040f9040c00e18510f80340a50004690f9001d42d60015550f000350001c40d4001c03140c1e05c140c940e540040e1410000c40500f400d0140515078010403261104a0542201c0e00e03a03050b20148201d00490100c0071941c600701150b00040c01651814609501004041c1c4849826540031012380110700001d008500164207480 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 191504406 1250 191503156 191503159
    0x20607050a0c0614180d0c0602060910050106171003050619050c030f0f09010207060c0903030f09051011250f060f020d030b030f0d080a0e03090a091512052109 70
    0x14035002c170242c098146200840d94050300103541100701008181c600450800401145d005000b05280010141d41002d40a2000c0c0062038640300c0113000340d9501588010044a1507044e001e1aa00d5181c0750318071100403540028154812801005a450307a00c0c2032000b2504405103040c040d50300c1d443d8500f415408200c17040794540da0240b00180c41a0401501c2c01c1d040071804c00010301d411040d0f1103100c180c070038500710040819412041001010342c80941049915403603d0007802c03890a0000107462020613500200811800052001003000c050061030111034030722545000030448164011580740880c071400b10040208000003d03140d0003407005c0d810380c0e43ca603406000118080c0d4010703401481c20180483c0c06204807425a110641d04001d034407188416a00d924202c1d14111289106460320505001803a400c28455600f0a840300d161800540314008000b159402068502e0102c0328001c1d0b12040c00700300f40084943c00d22201040785989403140c4840030b00c80d4a6942e80e40c041c2c92003440b80c0d25 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 191505656 1250 191504406 191504447
    0xa0f0b07060b0d050d170f0601020706140c03030f0106031508070308031008060906190b060306090c0906030a02091008011d090705120c0a080d051207030207020607050a0c06 76
    0x340000c855602241d4240c000034902010700b643c1d9100c0b6840d101319101e0200201d0401001100c0c0740414002681d4081c0141003071010a14102d00000d440301224803806081c000c50800c00c0320007043c0601954880300010086a0b200c2c900340000e030305010001e10446003ca4540004818503e040503800760541d1405002824518070b560f46032030035580300400c1001c010b8810080400d405400707101d014003400b00f000c028440f03400c0000c19103c2c0100c60104440105281221144540d00d8810960342c0c066001c5450051584d500990080ba034441c40c0110740d40103a0001c100f00e0078080950141c042d40400b5030b820004946064000d8030400000e024945580c0007101c5130a14204461410713139071090310502030301c0d4550b41d107101082c0c6030100041160b02c1c58019440c01c2001c1d00701040c0c0d1074000c0c80784000401300680072060250844c4283c4140c440050b00d2840015840d5000390100c1d5900c0b5800751889984da001030905940701c0810b40e00448003008021000070304039100710040d001028011018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 191506906 1250 191505656 191505667
    0xa08150d170f0904060e040c080607200c040e0a290412090302060a11010e060f13052404030e030a0302030d0f060e090a0312230601020a0b07030204050a0f0b 69
    0x715103140d08500c01514899070204001d40c003d80b078074017030070004100c4040e4918603410b0a00e0309008100c125080544d0a074042d408120f9603940c00148018298046c401d9030100403468180d250600c44100b5074a900541480e03042070240900280003440a40510039800c180207084c141084103400103203110000750074150206010401600c2c0b080300d00030301400d211461660701d6001c500641c000d40b041c0c40104002d4240084048401c1c010801c40c5034951019000c3c918049500e5000d07000c0c00350400aa8411503281c000803c041001000074a0b02c1800c09090a82c1c4544186204100202c4003100025858412200581000034040c40042d525801031418210040100c000a01941c0c400c507540c2c58603440006074003c100070032140074801c1c0c0c3c13018080d80c500a0501411403521035401813203903440c24807150070a0ac1d4540c1150340110910f0001403444d02e40800407890040030140203041005d035070f0b05009201750590f0042040710000c1c1d0f0000d1355075640d2082d0343c5c80135440b0b1180504c2c070b107010081c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 191508156 1250 191506906 191506943
    0x507050606100c060509030a0f0e06040902210a0f1d0d03151a0901030506060f040519030b070e0a1502030301170109081902070e13030f0e04020a08150d 67
    0x6600d88a842e80b92440c44410241c94440a64030280c4d04e00785603401c0042c1d0200010b5104402c4003a0340c0047c1081c0801c169600049a8039102c1d074882c1c10b14540e404541a40b155400703002c40c0c004403108146100e03d9081c0590030000900c8500e800388105841c100c8078181a5195119541d4100312000280201e0b00d001e40058019001120700c3d01800000240302103840c20b8505030048180c20b8510341191200ba000c030001d000c860b00986403900c52941844111a0711010604960aa51058500741d40020208120800044454100800c007034010b80030480c80c03541c00683c40c0a4023004440c400941c075070310b01c2001c991a41840300e400041e04200300611072130300045050041501c803207000040021598803000e116802800102140449009020090340d6040015201400d510a40180281080c0f4001c0d800b05c92106002801e00060840044c0d5844c02100c0000010700040d00540d07580c85240c4000702085021101d07520217205001101c60340b0305182e5032000840340c4c007a42c423040f040c44086 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 191509406 1250 191508156 191508169
    0x1b07140409020f0112020d11070209090105012403020f040306020c1005060d030c1109090d0305010e0121030c080d0c080c070507030b042f040b1009051e1017070507050606 75
    0xc00301412039020090800c40c0e0a103845010803084800910781c1e02c2741c180c1e01c10400001030181c0441e041c1da040030010b0000010030ba0603142082c07001c000f03950011960360000e1b0040d0080c07a0011115007000304000080c0b0000d40c0007030038206600816100314801c8079021b00c0442d0300503140306401c0307510038803481c0000c1d020700341620520303000d440c1c00d001e1000c0b6203000548421040304c04a2080c1c100d80e503c00811505402078034003515034448030f04000c1d0b040c41c80b003d141030f24480f117907890b0301c240780900400d1501400c1012841504160342039629111006100007910703001b08420001941d50001403a17007420b41e4151004160300a0140dc1c2c82495510746844480c1c0c060000d036244c090392000403a00c5506a444d2003c0740501450001a403d08201040211010310445034090680c00d00302c1169940e1004007042a241c080b80d01d070f0940c00310088040c001c04c0404e00c00a40004000e4825040e46030440011000100d11504014690395901c40071a118003035990010501d6100d64049421450b201 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 191510656 1250 191509406 191509427
    0xc0406140d02030c0a120c02030d240603020a1116030f1406090a020f0d0b0a1d12030a0507050f0301031e1a010e0a0204030503090f0301021b07140409020f01 69
    0x40006401c010090380c81404981c010b540394001c43c000001d942c1909600420400d07424045d901e010000559019806034480c8520001e00a0141d41c4140701c0700e10000d02e040c0b2005d0004020b8001055644840c0050001d50060445c440403818101d0b0310306108000054150610790320342c000c01c80d460314550f22480c00b02c0b020481154818941c26608801420070000c1c0c500c10640a4010800d100310341c01444134040b01c21344994015403070b0014039004a110120720640145e58540002441c40501c0391002c00089600012140d500444c0c08120f151200722000e540500d840d41c2c010001d0792501c0130140d48a2060201003503482c1c1003440104040703908030109601704610309040d180980b000d03030b40700c2c103804c829000004002c0d21200d0040c17141e40300c8041003c3d032210000d01e0031807416045403103240da6401400c840354450074002c2000e04442d00e00390166146423200c00d00f082c0d98084070152040d00e4403010700483d000d0500c1c06a0b0220203203443e001c0c00242e690080c024401c1808188011030724807040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 191511906 1250 191510656 191510687
    0x40b011a3108030304201e131e140c0301081b040204170609010c0806010e1c0f0804090b03010b0a12060608030a0504090f0e0d08100305100515090c0406 67
    0x2950700081c08410510040d44030340d1280541100481c2003031a080510030f100442180220341400e00703c00542228001e0400b00d074011500d0700c00c2010b0300a5460042c000c0155844130015000032040140d0030070740c00a00401e070030b80040301c0c1c0c01d9881006100843c0001d100d801600d6000344803d20524001d035400020600c4082d00240c5040e0301d0340301c001d04180001c01c42d408194040020082060f83c2032052440800081c030741107802d820300300e000174005803501031280d124405c2000b000c3c9d43c2042403802d514140e503200b9091b1440f15000d0502e004141c00c203200d90301d00385041c600601c8261906204007841c02000600c0741038030600b4441a0320421101950442d00156a0100450129003c20142001c455950b0301c480c0c0d81e86c1070000800540d03884040c1c0703201ea83d00380126141c202c500860704030036025046c600000b0380d68655100aa00e212a83d01c040d02a0041c0010180300e51000d411691040482c0b5003c11010b1840e5000d010004204031801c42c5500014882805240e1103886241e411110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 191513156 1250 191511906 191511997
    0x1e160302010c1a041101031523060d0c0306080609060702060f0a0b040e03041a07080306010503070c0b09070e010b0a090509100503010e15060307080c041104030b040b011a 75
    0x6207030070001e81107502a83c0555040ea003441707800c08a580c0c10301400003003402d6084201059860303c0412164848000803944401c20b40700841000741d200c5009485103002c8101d02804880f9007204050024061809403ca0078040d00b0005002400700255560207020568000d141b10758520f5450310909401404c1481a56111400080c01d60340380d001e11820a40c410016642d85d03032400c81d12002c4800c060304101c1c1c100c0da0070b20040c00895851403d50394808400c0c24025601d94400350308484680740ca10700204105800d00c00d008006100150110070b5841041411829903241c0018041e41c0c0140c41304000007600c8544184058141f0040075500f06103e0881d200d042c545600000f42940c40c04800303e600c075842003c3c00b0004d04480e0f80c43c143c03c10402d130068040141000a083d89035456050345601880c1c0703d50034503805404010468000b10380103466101142001e04c0d0032100c0f80001cdc03041c040003e48900050741e141810300c0440d40087c0e0280400309079180b80310080618502031000e00030200340c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 191514406 1250 191513156 191513183
    0x3020306011707090f080a0f060b0301091a0601020607032705030903070b09040b01090e0c0f130b030601140901091215060b040810050c07062c1e160302010c 69
    0x30500100c0ca40242481c0e01c1c0c0800300c0742040d0700c459245d89240e0046401c1e074009908100030070107904071b143d0815000440482c50f00303c51004203000d8261400010200510010205c40d41c00e01d24414500549090342035950f01d496620003141034503006110010490620854140007040100d0080005c0e03200e04140c03410301c0243d0340000d003000d03441d900220311003400058540442c030b401e12421031050404d003000300440b8100341201008060041c524503400c080021100c00b0200201c00f5941d18032015401d40100c10344980d0b8007a1140c03c2654603501107030400c0801e421420380711064850046069449d10b41c83c505e0021001c0350125480000d498a9180c01c0e11449046030314095800034007400b46206507258a0300445924141440758102e800500c2c00c0140110b1250140c219416160400c0011400800a1001d242640c845032080740301102d5101c0d15000c505c00c04211000c7c01480b43e6030484400840341c445c0750b04c80030510500d060800c0c901205000540c05840d6480c28180595100303580130 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 191515656 1250 191514406 191514437
    0x1050d0c0c200420030712092003060a0603020616080705030d0b0a0807080d03020912010501091508120301030b0c040801090c23090109020d11070615050102060c0304030302030601 79
    0x8004040c103a000704038071000c0c0c0060318200b40c0604020811580c5504130001c0d10311a0544050002a0130707082000303006c040254100c2ca880e0403280c3c005402000021000f001444c824002a00c40f10003103000e03029010010303491450601c42d440c1120f1300641480d14040e45904103222400e031200d0b044404040c28448800400c9080010f0650042562030005000c0c4140f010442c841000780d012184e6540800e80c10300c035104001c54101c01c5e01c41c50303003005030303d450000001540a40109941a10540c60f0100010b502140d6420100100c2e00b40c450340d0000720740302c0c04c03410b480704030164002a500d401000104005002d82c5041540305004c030003064201a00c8101c3c8900b594245103095592046203070080c0820b03c0d01d11454540d002c080440060240c04000105228107014451410840d5004c5002c0b0100c84a9401c82c600d011041c003072880c0d07120b000349041c50041014030182c0b200344c41e0179200130849500001d03079503016041c0c440c4043e043d0782e5030f0ba40450281d440180014100f02e041840c01125 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 191516906 1250 191515656 191515673
    0x50601021603060b0315130308090f0c091308030405060f011e0302131104030804080d0e031c090f0e0a0f0b01021005090a0b0405100e0d0e0910210302100b01050d0c0c 73
    0x103242558a1310b0018800e5023030061020501801c2440c0b20741040100c14100c4030001400800740b40e080d9900c03c25655070381c9284505c50350368280070f0f00001000080000f04007004c5031003442141c03400740c5118540d0300c3d10094444010408640081070318605401e00241c5001402503101028200c8081111041100226000c3d0029031040342c52840101d41400401010301c6054111180c6207030040c0045100400070f9921540343d812081c090755102e041d061070b0741c0b096003a4006010310b4220340003000e50740c11800c40d8582c1c0803249041c00514080c019111803105005a103612401603000700000083c2181c2c1e0402000301402c1d90b01103109254180c000216501741061113640260b000e8100411450080000e46d00c41c00783c400c00f241c0000840c900051f80140102c0d1200d181559000601c1d40c40c250507902005d081c0d00023000600c650000b12400034031417511840700d68803a45c2907520391004807190b4800d1342e400c40d0000d40131031014400c1684090090b48050105542d070305e0030310007804c080e445a206 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 191518156 1250 191516906 191516911
    0x80d030209061b03180f0603010e060d051902090105040203100e0702101503021f051c06050307030f0201020d020303271603081b060f040305131a0a03050601021603060b0315 76
    0x383c1d400100c2e140454200781d0200658040d002d4441e0002207424400182c0a444140118500d018802d000f241590322001c041072030f50341d404011205100b501e40181c40c0e03070b0203500000b20312a031006d00001c100380c10f10b0b0081d00d02500031665000031a50811802c01c404a0340240090114031030300c09110501e03001c0f80101c1008001002000b50340c1d80c05c600602c80c08241440c00d168101d10300c12808000303d5800000c58200712a0350000207580c000344101d6102a02c1182e101540c1449411380101c1030000e2b0180d02203107d0710036000c4036a610781c1690166107a0100b180c0b10580c20b5144a0300800c05d14a9005040c16030106009903880212003260042e16001d4581003550032031808110560078000000d140004451902d00900f0341b8036100e4031800e03402034018030050030444007041d00c0020b0050748446c0c002070600075800b031100d00000b24041040350048503504c4002400e10020500319400419000d50038180b41c02d1890032603082d80c4070a80585001c41e07400d60035105103445200200500703504a030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 191519406 1250 191518156 191518207
    0x120f1b19030f03050603240703020d0f02030603010e0f06010e04081935130c03080c010f050a06081c020c04020a050d050105030312010915050603070206100f080d03020906 75
    0x20708100b40d4002c01002c5580c0104814000d6000140d1010803c522502d81c100c2045c40108042d119520008100d0203406a04191010a81441e02c50600034940707801852140c081a0020800031440034084d658600c1d04075980f0130107400000050100d80d010310122984640140540340c607000402614810030b4000c0d800c0d02000072040300701e8041240003580c2c1481d91034180624041401d0041d901c005841c41c003e8003100650f4040a02d4004000ca04e2441400454004980300e0301c6102040c1318074003070300c01c0a440d0002145440e00161000d10b02e03104500c1980c0300c05000b030085821050a00e00543c04c1c00384074005512603d40c0d4010b403682ca03400200b91a1000e5941c007611000f140300490241d48068021520030740052109900c0c0301c1c50004ca07681150102e420104040000c50103e42d001e1185802058000c0c0d00041002801900084c555001c2c040e210420002959610f4a6100d200003a010390803040d0080b0800042e8240b203500900100240141824544218624181c030210680790300103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 191520656 1250 191519406 191519417
    0x21804080a0c061e0507021203071d030f150f09010c050702062110050102010e07081c030e01060b07050d0f080604150e0106030501030521091c0b0f010503120f1b1903 73
    0x8800d455048c4003010409142c0b151442c1541028100901b031940040d500d100301a54102d8207a80a07030f41000f62000b0400d04000380d0b07003105c0000c10310760383c401d50860340311404448040106c0c1c0f400205200324048400c0d00d5a48904010143d400c008032a8840c2d4461101c40c10b00d6001c41041840030f40300316008200f15045640101e1030400064250b408a00350403103160011801001502404105519046801e040d20140681214070503001000804000310641d8a81000400d445101000402215004500b2290f80c8000700c5012074100d4490140718000480c3d240210f038403400d00340c10085102460792014203040c0c0e00c6c0c01d01203584078001d034010000251103000401c10d1250500100d407524441ca905000b2313441c545600e64840e4071541845c1d5000d031800d0300603024031881d03405450034250f60050102190382044503d10310644402e001c0e091003030203407071060307a202260308046640060380d00021509010080c40c0c0c0e9140c0403581e03840000d945c01048461004030580d03191072003c60b8440d4503403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 191521906 1250 191520656 191520661
    0x11406040c0203070218040f0c0902040311040c120b040b1f0e030a0b01151b061401080102090a0b0a140d02070c050105041d0603010209030d050403021804080a0c061e05 74
    0x1080190349040d0722040c250740080040740d001d03884146006d261052a0f030101e105645452800c032548080c0e003440980185540700300841c06148903001002160300406210b400c0f000d40c0740030001103e06800f4000c001c12000c140f29128032501c0c1d0000200c0d1040108001901107160001c6038680d504803241105980c040072400f8100c940041c0d003032440a0050b401804846038603070b5407909880040c010351000188410518041e680f14028040e00303061110054450380c0300901d4101e000d044500f0224129100800001c601100705100340c649181d401440d14031654900040340c0219405000c1d0350041080b054210308001090000070f10741c0d08044c0c0001aa41c00706820054000401604490304004080001300044030000403c0103981c1604140320180c0d840303007000a030082c4a41d4008a4160140a4596005680080c090821640280d600351280b8113840c081d254a0b0034201c400500c042403c3c0000101103114007004184580300f008006400e24041e0b074007084445114111041040d02d0b0402c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 191523156 1250 191521906 191521909
    0xa0b0318030301030b0117101802040e010b03101d19110f0f04020a09081c0201060902090d17040b0403080403150515010c050a0206030c0a1b03082205011406 69
    0x2011000304030404061411941960f946000d20308042c441c03240c1c5e807601c80f4003000c01e02105114803581c070190740c501001003400301200342619111001d0264480c9141100d0501900d406010706112440c0090260900c46029991000100425000c1c1306407c1d0318070386040300440c41001900d0007965880c03a03002440900380303041303d16040140e401d00d0181c01d0800c1174000d180c0305e00342e0541c0004021100035840380144003044030312403259480481c492040748070003416441c070410880509040ca5000f031100c0f0f51100219801e07442000c0a2542081b41c01d1603080c08500050394182d001d28803146060718003540d50328001d507540c101d0782081c0c41e1110009000c20410106241450900c05142c209000910301581d02c030f05000910280d9505004c03410094504000051010000581d8000d0a140d12410a2600129641c1007141c2500126000c0003185c4104000c6c1c2c07110101c590350580e40d49500d03660302842005200080005904030b03d0080340350200103442030066a0026402000b00c0300d141c81d1050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 191524406 1250 191523156 191523181
    0xd030203120c03061c0c0302040209030a05010603150b03010908120c130303030204060e0d0b0c1606050f011a1e090d0f050627030409230702070305150106020c130b0a0b03 75
    0xc0b02c6172000380c0100c0b80c80000502e0401c0000c11a501142e0042c0c58400000c0801e06014103850010000d51030014040100b101c034801e03484400401c10b100f000784a0456040c14201c520b00c000c0901360102c01e101c07100c1604041041164090505911141001440454100350b40000d40003140403d401040030310910303520a032b03911014441201d04c07030040c02264a48859840010740091300c01d43d40002d07400b051107a0b10310400e03180d980c000408c0117103107821425008900341c207000f0768010b040f40201096243c0500400da441580348000c003581640002c0c0301c1170640b903008074130898010000c422013102069114400c506642e004001520341840c2007010b0001d14000105204446079540101c034061110001c02e55098a00c0c80a0000303122150f044070003071043c203000200500c2441107042101c2d03103a0104189088074070400c11500391000740c0c010500540424010103005921a55070702d00d0740e28040d24008210355a0800000c0c21151440114101c211141c0060b4200c801c0041809507503041c90 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 191525656 1250 191524406 191524429
    0x60d0b15040602210d0e01060530154012030c020a06090507170706030c0201050618100506030c090118140607061107060501080105060a140d030203120c0306 69
    0x424a00b03290038050b00390760b413140107214402e030403595a046900c0c0203500075072002d00544402031809001c20610011241c0c0d006110540c07090221900c0c40056010f04002002c41003601181c150127180d65846004600840201c0d98207140300e00c102445400a0014049403004140c4540c10500700c150503003080c00c02b840b011061482010318048480c4600c0c5e901245030600941d00c010003080c2c5400f2802c12130720b803007525000505004407400542460050002d051070847e14107450500c200381051000b80d00302c61003182d045410035091003450103440310108810b40d10032000c0c1c2031031a5540e10303403000c0740c406d400c01c46444540400005042000d0b41c0c00041c20041c0c5107c08032009900340c1062001c03003280e004148243e00444001c0745520400801d5048581501940d01d5000e40ba18030505141019203003c1c8501c140c25440d1201140e51800c00c2d01e6680150b40c1504440e003900380115040c0800e040400314103808600080c49820852201e4546541c050319100e81c04a41740c0c1081c0d8100105501c00c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 191526906 1250 191525656 191525683
    0xc05070f0b0c0606010c0309090c090e0703150b120103080702040f090302100b3703120f17090c060d0b04060f0303090b07050c010c020409021807080109060f05060d0b15040602 77
    0x2406c00c03c0000d90080010081d03d50140c00418200c900e100c3c00d54444000341c0120b240521481c0811000c10f5042c2d2040d941c40ca06080c0e05602c0360755a00d40c811461080c6034800980b961030f00010f1003c620340c100103002e024805040055080034068003d03046030040c0c50300702e0058014220501141e40c05024103407404c80201d0301b0b10028482c0c0c80d03039601404c00000848254a140004603550600c1c41900100210380009100c1030170f124a03074002340391107000c8802074042180301041c1003042e014028a188210050001440c0415541041212075000140c10707121071900d46400141907111030207120000d00c50054220301803415460064078556498000010072101400b8110104e40000b42d00a42c0c0720080c20700340e0000c140c600104018110121001e0340007a042091a40c0307190b550355095101e6442c540d5035540c1662941400001c3d146240b0407030120f2452004280201c1c5802001003880c0160460001000080ba00c0464684513880c55041a4a031000c1001c1015a8042c0f000700140140c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 191528156 1250 191526906 191526917
    0x905010c02070e040212011413030201060b0703050a03090c09061202101403010e15091e060a050a0303080606070c03080316020307021809010f0e0c13090201020705010c05070f0b0c060601 82
    0x6200f100d0403041c400400c080d1088000d00d07124450305000303601200303a40324016400ca51601d00620440e04049241000714015842c220000541d00d2008003a10321150340750303a61510301529100c088000d42580001920406540070300003072003e00510550703006100d01c05840e41d20343c030240100201c00c10341108090a1010b40000d0a43c5070401e1801c0b41d0550310340d0f01c541809030311b980301d000819100043d2000c0d0848200303810300c1907208007404880365403400f2107089040741d6100b2040c0640404180724068100343d0f5001e040c00005d004244841e44408003502071414402a0785a07004900000e0f4800c0d42c10301c60000c207000203080c480c0c41500142c90940000c40c40d0403013980c00f017508815240e01c61a000328540b408245104401e41050040c000401814403e404404001640702da140d86800c51140d201804c8200c1e100000d405500b800b141c058001c0c0510503e040300540d0a0118004101c0b000c0c092460301040b200310654140780075042c000307000b0307846441070801c0618280e4050700c1c6605001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 191529406 1250 191528156 191528159
    0xa0b010e0103111005120f01031b06020304091a06070f03020d0503060604060804020f030d030608150c0d0903211406190314072c0106050a091511030d0905010c0207 72
    0x19441c40000f040018292007401030220301900840f01c50150001c2e1117a908812024401e504d81000c400505880c062032250720700006444610442c0c0aa0780304560142e0014481000903103010380c00071502c020300340d03050601c0407903403400603210790b11101084810101c818124820703d54100441584400b2a041c001c1c07031401e00c900081e00a0203288a820100b0600300006030071911001c1010b44c1c200310213000c40e65200b4180744003501520240c043c5d034005200703031240300903400b507203030780c0c16002d80000c140c01840c1050701d02208016080e280002d074103000d1002400a01e203001c0c0c080070801380d03c051500284080550308050070804021b0143c6124490100382041e2604001c1d1121040760f602c41c801002804032440326a017014000e80c00b039101591031801e00241c1ea2a0304a00f41c59611031041851075503a01d0300001e941601031031482200007070082e64240486c06d00e0a21001000c1c00909203509541c0000d1090b91556106d1035050145640358010070f01000001d0023040d85258180c0041c00c40d09 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 191530656 1250 191529406 191529413
    0x50f0a08041202040f0203040506060405150607260a0e0a09060506161506030b060f121b01050714010b0f0420030a15030f12030902060f13170a0b010e0103 68
    0x103000724020655850796102c2c5007811591a80c2c045600c0302c241d01e60642d00ca1510b0700b041a190705084071482e001e1070400002549030190954003400d5180d004009a080c403180b9154469407030f5220355041c4007000c1104482d05800c4500c030180400d8002035840f0001d90b400182401011602c1ea404000070a0400009006542c4c400d42566160b1400c407401c8000c898083c1441403003140d003800d0200005190120101c18040030550742882a007043c1c0320300507404150801e001c0c900c0c940c07080f4540142c100300c0103500f65000480489903001414034040f410310040da200d0803920642200040820b0b903507221290f0031414001d414001945084504111002c105c51188828070812010031880e100000002190030ba900d81c44880d480144000041d11951039207091a40c0f40301810003520124080190500428468002c00101c0c60340078103850b08103074a030300d102c0303001d030b00482c400c40341114003941c2c003045000d9041e10580c041031201004127405042401c0a5007100c90681201584001103001400030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 191531906 1250 191530656 191530673
    0xf02070b07030f030b040c050a02151006052808010509240f0a0801090f0c0e010f1202130911190e1b040f0909020405010b090907110721050f0a 63
    0x100350b01810a00780c51411480c085000304400140254000c1c94500354410b402c0c1e1003000b40070320307100e9070702190101d05042d50400709861080b81d04d48040395100c9020302c416071085016181418680781d4080745004031504071400c45244500c9000000c061500400082c41c0c804241d1b508418603070010101001d0b04611041e0101043d80100c1c010040c900aa044a85400070380744000c10380c0200801008a0750b10f0030482003030280c2001d64205203050804a18000d80d0041710707040301d0a0301c1034100c07030f01e28100b16842006140c05003a81e11840e1240c40804080a50040c10042403041000e10481c0c650b002c02c201c020040c07100341c0c0701440780040c0144110740701e0640c0c1980040180c05004001c100c13840111026100c0c40c0c000500601d040720001401051940041249a00c00c03203082c020341e82c0710903020000703024140b00079a00010b0301020922131030180c802c190800507100d042e039010360385403039059081c5401891500713010700c100840d01090100900c4200700225511020303101120441c0c40321500e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 191533156 1250 191531906 191531917
    0x3120610021e030f0d060e01050303130302040c110102030a05071e02060402130221090c0111030304030c020307050621010906060203040312021f090b0f06011d031015060f02070b 78
    0x201ea494101c50a840d0100803c1034800d00c101801e8845d9840c4071424000000c0c00483c81542444c58200002141c0ca250120585801004070075010070503501e56020840508000a121b9003806501004040c13404801c0c00214401c5002e68408079039800e203030000030500103882e0f00c00c00280c401820488070a59000c02c05540040c0c048178140e04101d16128054000c2c030545038601c5901a052244942600c010942c0030310400802090300c15111060006551142201400d480701d900104000740009001e4101512514005402c440c802a120404030f1040c1d80b0074094030f030041c0c000351403009001c00d500d20703018013400084200b4040070740b618001075a80c1c0200e000082c07084031200da00c129068820440303407070206081c1d0031908484140c0d01c0410020200c401c2c00f91442131401000400d044440320b1210300810301a550900d070140b03400c248a01d00c0d00004070f41c030b43c5405a84c070f80690040b4540a40101801c2c051401c00106140081c05841c82d48030107211400d43d08071031003c01001400505652 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 191534406 1250 191533156 191533183
    0xb13030209061507050f0f060115050d06030c08010213050607020315070c021e09070206010608071d0306040305031905060f0906040b0307031b0902040f15021e0312061002 75
    0xc076622140001041110711a45220707850401003552010b019000a188841e4002c03c0103503082800b9082800361228170074003640f040d681e500143d1183d923610850040401c01f24000300018003c0c4c4940d903034180308000ea404000c03903a401246802a1264440c0100014001141c06901d0620541e0210361034000031510038007050844400681e4150040c80000f2405a004000f840401c00d128040712400c4c00450106026291410000396643c0c000203820741600c0180c2c4070b4191960b10340d0b50494142e050100c0c03154600035401030340300c15510100300c203a00951294441c40d42300c0c03400560500e1510030001c0407403442420b142c140051500c0d0740d99807108404055403215440c0e500d1401240c05000c084100a4051040318000800c3c044100901e1151544401d001e2602690381c1503014164065070140000c0503000306020403000c0003d10781403031520f5060058610800304045081554000c600b071200c1c9581001610040710103030300c400c91354046000ca80e8804080e01650000f55900c1c605500030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 191535656 1250 191534406 191534419
    0x10e0703030e0a030609060f0506010c020a05090705040803040e01050f180c1605030a21060e0a270f02040b220c020309030a06020702150910180504021b06010b130302 73
    0x224243d850740d10407180a5900003509000ba40d0f0705140490003031280841b40306001d890a00813450380c6d8030801d0781c00f10148d001010116101e01701800c0011a81c00640380740700b840001c10000407004c90500c00360000f4000f0701000002e541c90b00041c010300300c109060440c440e081e02d80543c0203030f82c0c0c0c010400342c1080346124203646072001c10300805010031106c640a40684004a11118400d5000034407001c00d40b601d8414200c143e100b04d205406407241030080a1414040701e0001d04044e1259100300304c00c0318504900b26070390b240341e080d02c494a80c00d50403c0e1450025020341c0810340c1080d00810410000984007141100d45592081442442c241004440280c40c1c00d02c0044851003001a0b652011009041d202c8045151030004000e620058089008a103280c4668030440000130680eaa43c0601030003107003404c0900807045071a0994030100c01c9009003040c00108075512144003404010b09800005000400080045890b00005034080300d0001410016030400c90151016081100d40c1a11031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 191536906 1250 191535656 191535677
    0x3050c011809021632070b09090604150308030718150e0f0901060908010e0303011d13321f200c03070b01080d080411030a14070512010e070303 63
    0xb0031525100c1c4820240021207030040d0820100c102900141c1e4500d503217104d6079442d00303040c40002d450300f10a104560f0700200901c0300c03456601344009829030105005000007850503003030291441c0799a0940042d00c07442d40c04420460001d81101d0302480c0c0e181059490b844441c40d0883d4000c6401e0300040740b008120200c10002000d80716038030990007000f001801c06c44075603141c04000300761391914481c1400c1582042181000d0400220440e410b07981c0640b03034440089808159041d8000014001c00c1007480d41c65004c4000c10606522511a03540000f42024028404150303005540c9401600396201e80040e003040000c501c141c0407422188684182c082484800d88460044003042a11a891031741c400080c0e1000485000c4020603035103210764500c075940d988842c07066589000d40400907000c501c0d080003042c04103000e0000314021000040c212440740328581d982d000380100c0c01c03c111089500a80c002c1c001854200d10007200188400000c02c400b4540b9058540d4488480c0702c06810300080404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 191538156 1250 191536906 191536927
    0x2030a0b090609010f060f05040213080111090f100c06050a06051201060812120103080d06081006080132150a031101030c0348080103050c01180902 65
    0x4911225400038090612898001800c82c0c541c1011606080994a4000c0c0310050404030b114000903986070245120780542400180002544801e07801000c0c400240e60004a9010900031009000c03c4022090344581c40ba40600c400d4422020f042d62281644174001d511060b8401654040c50307130040c40118140e110b100043c00242032a070406900607800000c10f60000c24150000c10885030a1402c4030076401d1070480116080c01002c15a0785151218001000454002005846c2a0b02c0304140024030640d0350680602d8006855440318516803220f0341041050001c0c40f0300400180360181c40d4002d40a000d000e04108140100e41c003c17503040c1100810070a401c01403039010360030b41c044c1030b14400d9038a0b0701f0300e40035180d142501a40068104000400b80d24880d001d1160896003003800c4000c215840425410b030b4502500302504410004403c0405124910841840d403440a80314606070f0f5045041c02c0e8105900040014148041001c5120800d00b001f1401c00031502d6000005894840303005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 191539406 1250 191538156 191538163
    0xe041b08070303020c100e09040f03140403140c030c010210050a2403050c030715031e06090b03010b04090f022202040f050306130804050f0112060305070e070809190203 74
    0x304644210300c5000c10210416400048000801404a03001c903081030045004503000b4802c1d001c000c1c4c00415001c0810001901d500750100f407140320f410301d469a9502c148104500d80c000380d00503101d101c0b0440c20014000401e0015100070340042d0003a1900780503c0380040e540e04d40100041c01c2e07403a0b039080000c01110080d4450742140c141e01c03101040440442551503030742c000c80e0005440b1030007940c8000b003062400060070822614020110391810002950540c0208070001100c0d61809001e21a41103a00451107020301600301140001140b6280c0c50034142190903607080507010320b01d050403040c041460f56a5105409a0442d0105280281031001c4991002207090b00e015480c008103002c80c12803258071540003540d030141c0c100c66040e0340301d4403162031700600350a018004090421091140e41080d50700580d50705410f0401002c40040f4400710000c541850348252425040b100c414000c0d0905e454806810900b10314104801d0700346454680e48400c4080c281c0c43c0000f00c0005041e08544090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 191540656 1250 191539406 191539409
    0xb06061e0301030305130617010b0f090301090305040819080f03060d0b0a051602060402010c080d0e1005040501110c030405040902150d050106090b0421062405040f060e041b 76
    0xe440c0d612540d513442d0140c01c640110000701350f0340f44421804076503240710300c0c88031801422881c1081116464108074803080e61192184501700c803002c10a42c50b030b0b03480901482c0b082c0c621a66456030b03a035280c080482d0406c0416811703102040712400760700d40481c0380081621a80407410800325980c0d110b80d400602c056070490002444151017808105205240390f205610541c030303401d031000b8070845503001261070700d20442c1c000340403070300c00405100800c800e50003400e070b08030b001800052042102c0151500c0d00b4650032180070400c3c1c4440400081140c20302a228400030010b1000c1d0910034501c404680300d000302d00486000d0750f5101c0d1580150f40d41d0000c1d4440c031040d0082101c0d075503d200c0307011501510f000d014403408a0070480f00000c1103640707002100c0849191003001d550294892503401044030254a0a42e03400f0340341c80901d8009100038260300000c0e01710a80d03001805103084180000e40c0c1c0d220b6601c00880e46840c004001504074407414590180e071100d102202013122103000c00300c0b41d256 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 191541906 1250 191540656 191540707
    0xd02071a0301052110051b040323160e01080c0d020105040e0c040b160b010e090304030308060d0506090312010605040f0b0d0e030a0314090c10052d0306040e06040b0606 74
    0x20421005c1c040c03180c0368030550284003450000703403041c00300c4030340040c161040d03210090504101c605290a80b400c00a81c03580138100711000d6a9503c0c0f03c07150700e0903600d403d60300123411030010b20004002c0e151040000380f01080059a200307002003100d4002030814001c5104001c2000d5540c1c0004410362103c2c02250b02403d041d0745415102c0d100190012101c0d4210a0116107038002440086003d2644080079403260a03500e005519041c1565000c8482a102401c5a40c11150543e40703400010000d0000c03034401c58000b4001c645070799135204401004281a0300070014480b0400080c01284105681581611540a14180c2c0c42900007042c0c0020030040003142610b000114211001070f43c95044982e03812810b00c0104141d841c0c0611207a22118241c0c070580d80081d9800f1503465043c01100038104011401042041c1c1218070780b0440515003d4860002030300b04000100000c5181138030035a0700c032900b441300900d8140b805680e04407500f0300240c000b622400000c1960307170404d4144a00d0007407a412 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 191543156 1250 191541906 191541913
    0x40602130b090f03012706020f0706090c1406070605090c040606030c120e0705040b032a0a15080604022b0b010908120702060f0d0e0d02071a03010521 66
    0x1900c412046942d044100da46104102da080310b580c00d0b20701402845441c80800189500004014040840c0c44940000031100590284144400e00814030041e01c030580c081e43c1c0100d0090100d1614659481e4242c010201c1030140302ea044400381c0b107540a0b2039845903c0074002403c1d8a6000c0800e01e8000313180201607215040401c082074965043e00100031070412070f201c1e00c0049140e1501001500c3d00f41c0c2c1c01c0030071584141801c0210b132515400006001e08060260740e1001011081076031200300d007541031100281669101200c07070809180b404014500b42d0703111106852441801403180d13902038196403069401082c98155882c503031001d0007400480700604100c00800d120740d40c000e001d0081c0168003280308404006901c0b4008540d03650b80c03400f011031461030082aa42000789980000d21106844403041c4802c0b0b224019a124070342844807158000c1c0703a04080b80c08000d2801e07071a500400020000f200205079201c00c000103490545d43c048a07668241401c2030b008251400c95400007030507070701c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 191544406 1250 191543156 191543159
    0x30022b0501060918171605010501060f0305090d0f09050406030b1005060705210906030a020d0c030e120c0a0506070503150103050f130f29060d02030a080304060213 72
    0x289210042480340304200a1100700d81d80e5405804840720b01000740d26041c0c1c003c0d8040e0024002c1d111200310034100c0d1050340e003858035800079031240c045d900c10103c40b240c0d915401400069000507202c0565041498180060f1030b004000ba40c0311000010944140401c48034a9101e00340560001c1c00a010041d00811049580341001e2000020a0319405d03840c2c4942c05000c2194100b1794101c81c3c070190020024801501886c4000f5600b0900e0b0400e0701c03401c442480340e0500c41d550140110302548001074003586030b01d0081201812140480000b206151408a05291070300c00403c024000c5405040c603251a100b02034003003414411111130040c150f004000420802c0c07500300010794040c64032100880741e02002c01c03005404880080c1c4005030040c0d80c840c0010319544040900648417441101841c04181c141e07564004141190000c200344801900c9004182c840c28040242c0d00030b0044641c0c04042032643c000c2a150b1507180c20142507500e0020000e8140201601160a00b0000340b0540d0f4071039 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 191545656 1250 191544406 191544469
    0x7170a0201090b070b0403080c092214061c02030c040e070e090706050d0203131407143f07080c0406090507080601030b01020a0213050f013002 63
    0x50112a204a01141e00c00c500494541405010760344503035400390f10036025882c1e580741034400c0d40000b09842081b19003040180340a494440402042c03034404480c1241204031021250166080201c40f5103010107914104050360f0ba0b03030f1408010000c4d100421030214141400030905245440c1d4050340c0044c2400c0070442051400640311003110448920500d480c4c90714002291140147d2081c4400150240400605020540c0c01582c200c11076030a0f40c040744055035034a0202d001c121000d01441e42299600b0081e9440105070404800c1045601c0400703810f60703028100021000424a061504074a4040402c02c03d012208124440000c8101c408103951030040f140e48000305034000340203d041400014400340c036401028007945c85a101c01c00d06a0b41c82004400034a2040501c6046124152003200540c0321b424451503421182c2101081501c5c0c00419294081c0041e84102c00c0954022103c15006258580d0100466002044204980040d0000030781d04029603584480c081340c1c4c0c06044448 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 191546762 1106 191545656 191545663
    0x105010503161407020d051b041107060c050408150405011b0804030e0105041a03090d0c0f030509130203090a050105150a0512030c0109080a0e0316050d050717 70
    0x82554680011345541c41b11481565036402560480d00680c0441060030218203090700c2c24008110b0f2845480000d1154410141141d640d0b900400c450512070000c40b0b000700b894004651040c22100010015003e0a071411100e0350b00c0d20824288211990307240c00d1100034076454203802507031a03440c250b40f0480350500b064100202080045031403030051414810611500c0c000e680c680c5854406945050328025810003400043c80440c0c3c0083c02c42d5000c42039540e8107107041a10f4030a158041442d0304801c0c15024030082c0040208044504006200602c042c09840217018644602d00b40906090b52802200d0b00301d02c04160500981c01c04c140c40c040341c0203001040342d15191000d00500e0131240701c003408440e5040b002a0904149510480c1540001d02c21009046285004000803410101c28030840c1d02072070042041c00300303100302070020000501e40140d02c5507600320190411a103 = true := by decide +kernel

theorem cover : BRFrame.Cov 191366906 191546762 := by
  have h0 := BRFrame.cov_init 191366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 191366906 ≤ n) (h2 : n < 191546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
