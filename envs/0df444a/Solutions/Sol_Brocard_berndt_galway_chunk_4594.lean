-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4594
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:07:19.964137+00:00
-- url     : https://prove2.me/submissions/3b7be58c-14f7-48e0-b45d-d9f4bb295674

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 826079136 ≤ n < 826258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 826080386 1250 826079136 826079153
    0x1051212031018090515040f1202030c01060b19140403060b0411041d0a0e030a210501080d080105030106060e060724020706060e1b0d0b030715080604140a0b06070c03 73
    0x701c2d4090810b4031b80301070140604480f03c0c0011a000790a0350103000d02c5000141041c0d0103820241080e1058909004403541c00909582c11680090500c1e0000f01d20705030354000c406030705d501120060420a80805540801650901561002410341651082d0009560f150380c1c1014007101c11844a90795580d4882b8000031440d00d02c0c680049510a1040000301e6429440c402e01141640800c000d60400401c0d030b00485800c545510030700b50203c841c06844503012082c1c02440d0207043e01c3c80180800061088000384040b1059002c28480c2c0c0c1840c8041007829080003d00005003419111a43e5503907a9042900d01e6010050b20400c0a000ba900600082c00071503007c5c060140c4540014807501d596610700b810410400d8900c840c0c5400c114100e030700d020000c00c00030700c8050100080444c0c6000b07081e0000b414111180c1c420460390788020341060010b80d011300c10340d0740710300100e0b0100081e5003650191550248000c0c00100300c0c03680e40ea8440c1460b65640181d0f01301c5940195003400031500c80c605040c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 826081636 1250 826080386 826080401
    0x181503020d0e0c0114070501020c0a03090515031504090303141515030c0315011404030506010323100c050d1a0102010b0d05300703090e01051212031018 67
    0x70703414904000710b01d0004011032070b07400740d0030140e40c0c416034070038480301c400c85641c00860704032640c1d0b50030404103e1041c4180840402c1030b001c1e07161059624901000c0c481c0f00d2000100002c0c80070001c008008860104003c0c421506005682c009225503080c42c06034024600801035aa600650100300141d06490243c0c0007031004003034401c090702d00300f04107110100340010384403595040401d00004244d04030300c81841d46402c0341407401880042c0640104078844e80f00c1d820650710781d006400184240a801201c407046e840056682d60354840070044034617181d01100310041106501c80000004407440385050b41c580c00b0440400b0004a00480071041100c07904070070103409035082140303015403440c024045080a61300903024040d101e0103202010030403016001e00c070700d1522002005490004500020302140c0d8480d0311400c2d441030800c1c0010101d1b0905900c2548a01021408041c0600010480060000c80b82221310340302e0b128904540905c414942141c880d440d0000307032900d54a00240c10181 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 826082886 1250 826081636 826081657
    0x19141903030c020106050102060402090405070f03060c1701031e0302011b091701050c070f0c090906020304052803140706020c1f0b0a180b0a060f020f0f0d18150302 72
    0x11008500003da00b030701c402e0302c20180541c000800060142c10015034442d4844e11541c11f80d03501a403200b150004040e00c1c2c0d0010b44003156508020b01050760028881402000c01c80845a000d61441e9107620305004016008040071810781c3c030540405000350409021182d401648919403440b19100400300c0440384212000a0302c00303a07084404c204103129090040da4034810382481c00700c09407a504003c41c007040c0101c40202000d400060340010078802d401e0340501c92070f409603881c00c0a090841c64103400d50307215a003030002c94560f940108200303540c00c4443d95250501443c02420190713114010300941c0e202030f10503800003d0f011088000802c49005440050040380e01d4020100214411280820243d6400003885c41082c00034190b1100b407500107880c00040840d007200200085960050141d1000700401c0e41c2c590300000003078051003401034010440c0c0060600711131000301c05a40340d06240c0c51340248500e445441c411800d221001d000680044152500d1051000c0c200070000d520103c030780c0307 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 826084136 1250 826082886 826082891
    0x17060f0a0f1d0f120a0f05160b0103080424081501210603170703020c06070206130305060a0f27020d05010903050a0807020c0a0b1303020301051003020102010b121914190303 76
    0x18103203442000140c0d041342c17075550f40c1c0c001000c00c80320041d500360f84075040e0707011801040306e05100081c90909030503000e0b511880700c4541300c0b032406151800062a80180c2c402440c030120003402d01d0f43e405140396500601071400721505150500040c0e0b0f030600b13619030132004000c04618481c03564040341c00800460f8402c1540c0f540700350585103441e4441c010302c4002401a08a0f41c2c1d905c4440c44c0c180090080c0a00040c18a46030482d0b500d92216013481036802200d0319002a020003101e10400c3c4100142c503200c004003408031700e29500359400700303159032040c2e40c071600742c01c44542040d5201d07895122850350b4044000c20490f400750401070300070b410650b0301800055210b000248100c0c0301040e55069040c0c0500307120911801c218074003200c1c0e0081801c10140c00001d80001001d80c2c2c003406032900071160920026071076401c2d800020709580c0543d0010340208008080400ca6440001c1c04408a60140706042503624440ca09148038613920350240c40c41e44141903c140c00c11007401b80c0300c02d203207200341c808 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 826085386 1250 826084136 826084153
    0x12020d3305100903030503150907030605090a06050109090c1106040516060c20010509030d09050f0d02090117010b13051905010b0a0513030606060917060f0a0f1d0f 72
    0x2007086000e02c42d1114800140801020400a03014401442d08042001e0440040c1c5079000701041c48804115100c600003503c0c1c001c208003e0905c0030b8204c1c0c2001c08158140840d13030802001a00e5a086403180c100c125a54051108a5030321509428000c03a0080c000e035880ca00305820840e543d116040380200e040000030500180c43c034041d10101988031380c8401c0e280b010f6075000548450f81c0700041015410711404000404443c1d03014496040c1c2c41d8440c3c1c41e4000f40d541804240103002c5208003003c0d024642001c030340b80c0540d54a04089045901d00e40c1c41107140c40726200e4950140210860751900481a44505021107000740c00c040d2041942c5103500307040c01000741a03802915428801d07040301d800100709004da503d201d88014405803408011050040743d480c6e03118400ca88240d481180041c0064074144481c110400740c40064840325001402c19061425802c0e04580010300a80a01661135440401d420010303004120105042220034101c9407540003d2526a400003104500a020341c800c07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 826086636 1250 826085386 826085389
    0x604030b0103200f01030c030b06040b040f050d050309061e07060218010305040308010510020a05070b0c1903020d0f1704030f180f05011b0519170a12020d3305 70
    0x83c0c0303050000000c1c100c40c0d9541080c8010b4004001881101d0201a19141d200f00740781c40e114002d00c010304080c6d681c5943d443c6410081c0c01d0307180d41c07908118840c81c044042400880d00000c1a0b406410084842e243d0b40c2190504c10320740c40d102805540151540444d00500303002540d03001e407520300d4041c80030b09540000034004400304e80c811640180840d00d00b8005110360300300300c48002d8610403580102e502c601c1c42900e4031881c0c400380703a00003501403000103440240e030074083c0005801c0031083d003400c0e825407040c1e0b42c01075142c01c002c0a500042016881901d80c8c118441c54600001d000000092061420503090007000d004030304007941c0c0803481405901c20000c16421580040b21205038442560904080044444c210464034861300d15030884072410101e40207006c40b5042e0300382005a8208040280381c055915506804003800d15801030104000c500d4114500011444503002c1c0141d581030700009010081c41c1c450b1041081071691412a81d980c501544014550414007200b00c040300d54410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 826087886 1250 826086636 826086683
    0x24020306010917070902030a02030709050105040b120709030609030309051b060910050f0a020109050712030518030709060b09040e0d301b080f060604120c050604030b0103 75
    0x222128005580070604110800f41610a0410340c07075194162501030380e59503d940e0980c1c00c04e0301d005581c43c0d4000140f290b00341c1c01c19407901c006c0400382841e80c18286842c2c4240140e02400c1c1032200c440c24813000284010b8401c01c0300001566010104220707107482410028000d0100400440c1c042c411208d458a403a81e40806441500c4030081c03055240103401000d00c8002d00440c1020800d01400780800004c026000b4040c1050046560002030103001c03605000340703818840d620941c600707404000ca80c001300346d01a08132144003070440c020740c1c4005005008a440c0c104540d114085440c40c010000c507000300d41c071b4000e1614a10440e0144172054482600d10748401013038402e200440d03207030322241640d4201c0300041a220304981d501c801101c400d039072002c802d46800000c8031000f1008030400d607800e10b030030000703694110031021102c910300d2030000d01080f0305120b240100000f41c0b41000455080150143c41c402c080c1030050856a10b0703603568688203003c21401e00046034441e0881c5810344e65071000c0d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 826089136 1250 826087886 826087891
    0x507020a0822092717120703050105150d200a09081c1b21050703020f06093a020d140304030c020f04180b09010c0311030402090c0c0a240203 62
    0x411902048440d50401c410507100c41c0c0c0f02c01c07517400900c9441051006480300c05401d80f8400124031068600e07041d60002c0480341c1c142c11503846410703010815134200c154007042e00c400502070880010529075020340c02445101c020a80b042e5504000360000c0d02c1640072111408544a1404580948010281d0480e002e10765418a00c0003450380743d551041d414441d904600a180a540180075981d41070060700d0500c0c2c101c240000c042007001603003004140c2e040203a0760202e020b130005060305080006466464444200303445040782c0380d00d00c6090944d980b51400d80300c00300d08850480b020500504010b501c60f03401041410215110070405064010081c0c1100e00c26585541c0354000c01d1102c0d801c008046011000302d0ba0001c0d940c2c0f000e50042c0394080a61540380c0e010b02e012200a00c2c10603001070070344d039032a249c200405080c44100240ba0003041f00b80c80e0007913812540c24080765a55000c61800740600b03070344407009200d808201c506000d00014014088202e408917480b468298008000a91005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 826090386 1250 826089136 826089161
    0x30c02150a260a0b06040f230105180907050d05090a05060708070e041a090f010e100305060a0b0607050706111b0f0f1212030133030507020a082209 65
    0x502d00081d25082d11513000300b482900052020b8207140c1c40b000b108020507001d030014000d2041c2e00c0400d51015900300701511007640d0034030700103103010a401e00d0b003840203c01103006400344c1d1900b80441c9000b4018010341f003402440781c0307007000a864200c8440740d07180c00c5040f055815000b81408900e600f8030964090344175604a03140d40100300701001c144001030810880141d401c0342d9400e031072862582c413030003028010440034006100c9075042050180da01040a800041c41c50840401000061408510554040340c2c0c0d4500003140702d816004074885100d03244008141340203092000c01c40c00e0b00044071078411446030044072111140301458100d2018001902540103034182070706a0b2a1408031952a1112000791040e01e146040011141c90a61032079102113020502000501203000d0921001000d2550100c20450a46409401400780e070102070141c0c0c100b544490001d00020700130010451110348c0000301c503030780e07844450389041100c003a102950a03a80560b400001c01842a00502800c4c0c410f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 826091636 1250 826090386 826090457
    0x10e070c05210d11030a050901061a03040204020d0c20010b0d1112030a0203070317040b06010c05120d050604050a0605030d180e0108071d1003020607030c02150a 71
    0x1203005071801c800301c500c0c1c00701e41140c0003004158001c3d0300b6030044071301e6007901004003a10b03410210040c00c10384400230840d50f443d078501401000315180f90041c1d980c80985501c45580e0301d072183e001143c040d100e581800c0b0041414122035040895000b02000c500b034854290800207450306000c1a402d035000501c0e9a6488080c40340900c011810008002131102c00040040f80c2d40604d0840860454004902a2000d82c001051110516403c040076029140c900d4502c0946440d081e0f54a1400040141c0158100070f001711444041180800c8084040200302d980591950703480301020002c1c10007200da140c0564202404500b160720ba40c003558003940c0d0300801a001010988200312890010781a035982407442c07103480001d004100c1d4242502802180c03000c4c2140034100740240030345811480b0348070091000281041001d000d840c0600c1c040e20b5048039016518a07030b03818111244a42c2000207075128486000350b207480e813280c2c0001d0a00f42900d4a07608060700c1da0440080c4681d01588180c004640c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 826092886 1250 826091636 826091653
    0x5030903030f06061b010605270a090c08031c0e0309010f050a05130f03060516021009030915030b03010c0c032f0d09060201050a06180b040f090605010e070c05 70
    0x500701d100b150390102014180b075043c80071411111440c040741c1190759515964600c018029420030341140365040079003a6041000c000c0d245000b00030305e4070003001152540d640e05624401c02c07014041000081c1150360441c0d0315411401a0f8550407400c0a11030300010345020882c00c00031902009803581101d05845000c4421200c1c8000d90303455000c082c0c00340030000d0810000c9144461110740382d0182915043d0340d000a404c51a1001c110394010b0700809481440e5020642080d43c001400c082038101408046200c40092030192044003160300b00c48043e490100050000c0c590503400b130620072038210f009011010080c1c5007542c442e41a0315018000644000d24910000007062000741c0d20b5480140e82d00d200c00c8040d40043c1090175800091001903841c01c420066168240103054100c51041010840c20380740c001002100b00c030707203261485c0311519101d1000c0340742d035035a020701c0d13039061903e00c184030003019850403c00800d024040c40741c0440000c00810316103031144100c894001d510800504066 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 826094136 1250 826092886 826092901
    0x170109090803060d140102040b0304050606030604020328140616110d03051f03030809070609120308040501110f071b0e0103021e18040614060307060f03020f070c080d0503090303 78
    0x2c5080d00e0301905d01091071103207101386200034401040103001842105440e800c080c94007c2c03c3c001c0290069210754807081c03e0001507a000311321550124060f600c0400250300700107150701003084c228009007102e10b503003860084905010400a02c5403085034800703043c04010f0711003a41d0b02c09407040801010352018020340b2003180281c0c08107421030f000d201a61f400c80c021500007a107402d1140c10490000b1f160800380f0100f5881001181e000e400346040c0008514109a9000010740a81002600b00500c030408101400000c0d80701c1c5100176031003036465a80d0a0044035040c000e51240208886844098038030b442c046141084903019204000c150105603483d640800c03010750020b41030140300007003070103826404ea5292180803a0301d00d40301c0d40050144c502400c10300110b6140c00ca003403a0740c0040804100d41075501007100001c0e41d0040c01c0c25400c03a000182c0842c000c0c041c0c0d45030345040850000b00001070222486c1ca190440e000304044440344000d10200329a940816075120342185d00500c00318204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 826095386 1250 826094136 826094149
    0x2c041205070204090f050106050910030b0a050c0c07030503041706010b070303090206130e100501020309010e040c21141b0a030b01030f140a051303023a17010909080306 74
    0x4142c00180003003400040d076154400c05100d005012541d0303a5482004003c0b50401402c00c41e4410341da8401804041c0c91621103d80ca600d00074103038a03041d40d40da40028a6100f071102511615012901101e0001c0d0f16403820035901c0c1c0c400e001d070f4182c504800c016000c807103400041280c16215072413216418010030381d400350068045040c00b00d034800018003040807064140c1c80350328024042d00e0300e50701c02402c18450b26076001e50240c1202e811500708100c02e0481e42d80061003085c08010079100040e40d001c100008a5191b4210030045855820466a0000f50512a0808600b000711850408803c4e1501542256089102e807809111101c0900c0001c8000e80a03501884180ea010704000c102d1108180000741100c045120182110f4800c0052160b0107100d4815160b02500001c4a44102c58841e20040c0d40c1d03a101c002007115000200407000b041e03c801d40070306100d0843d49007615000000d400409026450f11030341550344841d040f400051500128000c03074191136000070700c8601d90b483e0701c0207000d02d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 826096636 1250 826095386 826095397
    0x110d0e0118231f0204030312091a0405031b1f0e190309050913050124090510050301110d050c040612020a092c18070501050309010f05012c041205 64
    0x41c28002c02d0f00c00e00031000399802050049040d00c1005a445056140161070715440c92588610300d89409800d50000301d800c01e4900c00000980595401c0b5a6a40340061440c0309171b0200300c640240c1030a0003034241000044040c803c0c404070390310360012595100c030320b802c40f50b40003c411341550048210240d508440c0c00f803500f41354040d103011152070340c41d9070102d4400c05081d940c0c0c1901e44510344034002030242c203200b14900342c0d0000c140700c1602450b00c0145254040c403400707800301c0940d588000c6206003c101c2040c030000c01000e0020301c9441b4034403281d0241034010410310181b45060000090101d04080c04071000d507180b07525106040c0c00d68804000080d00072a040d54280081003001081d8100062310382032300300075102c050903001c481c03000c6d81c6260000c026220f140d560190b06d001602c0c8003800704602040d00e20a2030070544a64903488010f0140c0054000201040e14107800070803000801c81d200c00c00000c0f40f8880050f859055642030403e4041120042c040c20365180011110900c198000d11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 826097886 1250 826096636 826096703
    0x60902091e06072a030309170105010506180a090c08040b0f1306020a0c0506010906060207050306090d050a020709050f060114190f112d0706020a02060d110d0e0118 72
    0x906000d031801500e03411013043d082034000c113442400400c071a40403c176803200250031020023441107526100108410340682d1000340a000d00d10a200041504c0c1e42c3c0581d0001c003203143d001d002d004080440544056819030f8180c03400203201001500c0310b01c600c1e000d580907401040700c4101a006680780c01000390002080c8408015a00300944003295081001134041d2840c400005030b940d02d0024081c2c03400c0455881540690070103001c0121603480450340e2080c0d80300d10304000e607644918070340481c14042039402c910440707440c010a21481d0800001c585100e19403e0700d4842d10100b103400b5080c0d10b80510032413000c0126060304250f24242c402c0c001444c1003801400d1822590200030b00203802e11080d860240d00700200581484011030180c0c000400c4c01c840440907241e003505101c0c0c0251030345011180039008040000e0f44d0a0300c440554094010040350142c410744911108005401a1401d882080d06540c2000880c2030044008000710702440c0d0b000c800c0d14a0300c091200c003865410060720404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 826099136 1250 826097886 826097933
    0x12022101020a03150911120a0b03030403030e0901060311030402040c200a11060c0304030b091011030405010c110c090901020706150f060311032701060902091e0607 72
    0x80019000340080c00c6210360544000c07441e694005000c0c4469504c83d03004890840c04d008420303051041600c110b683c075007421144442d290ba100c0004c1000350810000c820b0301444002030010605900c80c1d030b20201c402c03048501c50440e9030b907110214140c0302480c560211110040010600510b030980c401c20700c0b00c24034146665010469074940c5106221031050101c1600816031020400120b0070351416040b0045501c0c40c14021120003c99490049010003480d000040010590308001001002010b90400400340200d21485d030171b08945800a403030071030b4190300f40a01000c400f0301540e100c4c00c2041c8090000c00010f0504001c0003d0b1080182021825540c01c002840208416005102c1c400499902d070410f40b61a2441c000740c03c42c0f207030b80703d5000c01d884d007540c511000403005d080380d030041c21000388c04130001e030816903100303440c0000e982c541e240c1d41c40c0010024050f0388940141035114001c4540300d1072a0040f402428001c58003a02d82a031202041144c00b0000b1580407070801c0012004a40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 826100386 1250 826099136 826099189
    0x1306050a021c0c050705041103160905060310080d39020603090f0d0e060313031b051f0905060a05180109110f030c0f090702010f051015091202 63
    0x3040031840b601220b00006944040c1c9405000d07041001c0030007031400b9201001848500282c03643c541c00040c000c0d54910f041190503114107445000e4a03005054020a020742e45d051403a90000010414414004c1e00c0c02410300b8040c00328040c40903044040c0c4452074405028582410141c10910394240403202400c200400d03401503103920000d94401d0306880010710150b8007601a03a40b4000a4a00800800c03503040c80c10f4006403211002c2d00d4210758001002c0341070b03145030325054071003860080465486003040e04180c2e0a1000004020264210080804a4102c2801c1400f0113032100c40b24043d0059102401140345142035a000590120030964010110310503004250301350380311b040e8252003501c44881e040e003083c036000054a071074201c22401031051604003404075401000b01201244218082c3c0d00045103070f4000e40007a690a8484181008249421149482c90344054001c0050601c802c0c00740e80310300c0b40203100c4101501c0c080d0f042030026401607400c0028800700d229a80c007545419550 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 826101636 1250 826100386 826100413
    0x40b030a0c080627100b040305030705010b0d1e08090607150614030312090c06070302150a02210406020d02161a09060112080912060714090d030302090a0332031306050a02 75
    0x42c1002e235100b40055641c40e5a10300700300d804e56401d211424441c1005518200004009000345d040700500003c0d4a205020b1605100d000745c0545a01203401100014410081250304100840c2003520000c041204a483d101c6081e608080001c06540640c802c0041480c486802e14180d54408500d03801c8800c940c3c461400700c1c00d42c2d0040c0f0011800340c1d0040002000300d10b203c441007a88800501021030505490040c50101b84d031844007001c944442c1c00b03006c5014824640c049400049825070255501c02144410240c511100ca20644500801030040c488a11425640387e005e00c0500008004507424020002ca5840c0c1c070302c004442c40c15042020b01c416854041d540104180307250042c0c229441c1c43c0e54003a05060041044103403001c4100701c0d043c0030391b0302c2c01c0c5801c00c0e99426140c0180c44a10040224840400a42011b8021ba900304040d1a401c61030300f441c3c0302c949a42c0d140201f2641c5081e402503959002e42030307010300100181d000c2440440e2151024241c0481c05204a601c3c4801110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 826102886 1250 826101636 826101659
    0x40f050c16170c0709060509190e0a0b100503061308030610090302101101050702010615050a0e09090105070212070c0b0715050109050105040b01180e0903040b030a0c08062710 77
    0x100f401c00c50341c012207000c116102403881040f000300026646043d03540350034041141c404100d005c1107202c2640da1100c0381c080f90b030100148013125500014110b9541171406009600207400d2050350f12912511000401503035030040c0800e100c50384001424115240c1c04100700034444110280c3d000c000500030300002580d96082c1640030f461040d103d100c920b003008070845013076541c020b12034410743e030403c90104020750741c0e480542c01c03078289843c1c01f5440e80c002460071100c410303101046550040408041c8828000c0640c810340c0550525000c5800d01411402d01c03203100d01803420094084076400d0010080e003c80c60f40205a0305105000241d8040d195401c0c5200b01e40084c0c0040480c076995900600030b505040c072035441403203000d0a000c41d903000c8402003103103070594900a11140321059408155050002c101740d80c094010503222680f03a140c03400c0c1361f00041c4440780e03540c00041c5050300490880c1c20b181d0b40d6200742921801e13205244c03580121040d80b0000026142d21900c0c012aa030001c4d0408104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 826104136 1250 826102886 826102897
    0x32c0d0c3933022b1403070c061a031e150108060f040602070618050609010e031905090a03051b0907120b010207260709020a02031c060e04030e040f050c1617 69
    0x1513581c2c50650315030310700040101501c082c2c5802c1e4a01d08100707001076a60042004c41c299540994082000c00d00300c01020070340c074850751080c0e8051180c600d02160141c5002c00301c800d8280208210307140032049280d40d90b51440e00788101110340e00200041013a10a020848031f50080c06102c02505c3c107110f03546c540040b076000c0d00440b6122011311100d941000030501c0403030f8201c41e01400070b100108455410030303241e201c0c10744500401019400303541c45080c010800e0f60ba090f1001080310800950b00d01708030792105000c1c2c0b0324083d035545601d8443c00a00d071603122280261020765980d5012a807050720400140354145825056118042001664800212060400d03400c036986040303400c001d003c0c600c0d207003804c1504003000360790041c002c0701030b820303400416506c0c0100d10b010594038403003410850303900500e40e40d005009080c411404001c14540c00c22a0020041004c2c0c03410854000c10307040301421540b01b9102002010820400300708500c100e01c0251001c1c500602001c0310001000890244540c8003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 826105386 1250 826104136 826104193
    0xd0e0616090b030a061706040c06030b0612180f1605100e0904020112020406110f0d080c0a0c06060b0322051902040f020703032c0d0c393302 62
    0x141080108000903480c4260041140d0302f070a200c2081810001050742c0106041100c0e0641d008001901e0b00c6001c0310b001601688503402d651140355000819921000c01498480480d001c03054000342c00d00b80300c44c0407260002190b498241056445041040e0100301a10917810003844014000300700d0002d2004000524982e12280040c48070f0380481402e000c0350b0340311250785810044032101c1030754100050701c0e444008541c0f02e03595013550410680341564103800150407649808008206074515000460040a0a0301c4865130a00310207102d80b83c01018800081440d0880010311f8201d5103d0660081d401c0d10003000810a07900b01c000c640200d07000300006a000030f4965211448001c000c0306508001a03035076941248009504000315510b008010420040043c012448000c1c002d40d05061006512050b0110318030315200071810020202d040b5910480350480a0006140080140c0c80c1c040d2a00ca0b06c480001c40c04542e0300b404c040099162a1415030045081401d5541140071002250501 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 826106636 1250 826105386 826105393
    0xc061a031005060a0b041401050c15090601030b25050307020309060d0c0314070c02010503100503190606152313060305150a030b0a200d0e0616090b030a0617 69
    0xa0038410802c4011007903000d69105d43c0100418002e07211401c009072909102803c1071582c0b0111183d050b85450901d044100d80c04c5041001c1c0202d410300410201d0403240540201580c9031900c4102400c900d101c0000ba00b84107003d170808020941c011000745512a40a0055030b06200c00000440c00075404003111880240c0d6410000982a415115214100014003a010300e58903000e44058400d5049090203030611001000080207015501c0c0984058000a02a0350500b280c0d0600780d90454482002194901d0402c2c80104000e01885000354a10381035035940001c400100130f1031010039107411a4a1001c040810080745004400c18800d4000c103c50f40e03001503a460f2801900300905038030281e1a01c10345040c0c1c8104003040c110b40c5030f950490302501001911078107910608048656000030321000c1c4c0c00101306420080d03030075802000c0640c25102600c0f00c50b610005044042d81400101d400418407c2c402480740c4182a0003442d880300e08110005000340e12851810f1014101006542c1c10b0350 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 826107886 1250 826106636 826106641
    0x62101111315051c02040b1207110d090b2107050318060402010f03050a060e16090e010e0408032a0406020c042c0c060c010c1704030c061a031005 64
    0x76a4010410014425940c514140d800e01910042c0184a07040c0c540b440c40b11000500031000c0301da581100d0040129024039907a900c2d1040300008544001c88881e00451000d0ad84041e504401190700c84100301142c5d5040213203403c05484803015041540c1d000818030b2214016240281d40303550f1035024040030b484094030303440d0505508031617050001c424801500028203200050f6000421406c4c40809030401055603902d02e01c80b074000300300951050380d945a1050034418440b00d89482007a01140503940c5001c502c1d103d402e80080154288183c18281560100140c045180d110241d41c10000d60351284000d074202e404c40b807400c40d05a40c44400049c0000404201c1d1940411680560701c80a4a090100d1130300b00f016910040908104031019214500c0303d0440c0240c1400901d401c001c00a04040d1038181a01d503840c004c02040c100302c4041000300b0000000e03074081140562107190f0599610810a00640c0d45802034a01d40034000c8104c00100b03610340203a0f038140030740e0300000e601407000034151 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 826109136 1250 826107886 826107907
    0x1e020304060b031207170903150c03180f0a060903020a060908090a060314010501211119020703050339060f060604050a0902210a02041401030507050306210111 70
    0x6204803000d10013100401140f400141100900040b05ea060200140c1781e440e074030013080c244004c0c0c1c00c82c20f0610034840e04100c0303542283ca0165000300002e1b20300c0460303190001784030b41e540d180310b251058103130f8041c010314000174030700e41c100f40a04d074417a1040e03901140300b50765660103a0b050040100c0c1c0c0000049103511546c241340c07550500805580c6424071514a410703090b820340310030600800f0304114481215070300040b00e2600c00c0b50301c00ea86210401ca080d061070008021900f200e08400301c0d5030b10109804030000d10010b0688192900100038501c3e14400310302c00c1e03414a00480d017010300884403820f1498a0120b401082c517412035003001030304440c40c1201c0e001d05500d0300103050600c0f40328140014412619400502c105031240c051006945280d00340034482c2d810b982e101100c0c0c84402c400200710507a41781b07401403c00c07944080100f00c2c00b110701c20015070503280111692070001784244000b90491400c0c1c104034007100603072800711505082080d4a80d095070842c80000681c944000340322842d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 826110386 1250 826109136 826109143
    0x90f081305100e0d0201112e060b0705030f0304050c10080906071d1509040203010305101a090f0a06080d181703040605030c0405032a090610031e020304060b03 70
    0x81c40107103420ba0f0318502440c000360040141540180c10007444045000e09128100501c0400504a0000c07100c2010050603007000010760745041c200ca54108440001c81105600c25180d0080c0e0040242d824a65000310340c030500e4200238002d030750074400e083c0c000540382c480354002c58240643c1d58030100c141c608a03542514180024101c1c3d820810003022204400800c441c1007000c2c0300c000c075900601507003104203840b06402030300144d540c03141c8008000010400300150020505ea8604018400d080c481c00c542220160004201d035000342d406000142180d40ba186250380c010311003030002408641302c050852402e10552034080100300500d01c00c01c5401d81400c0d55000070801507004003003c0086074800c40e00c86c0500d110f42010301c2030202c0450700c0710508005440c01707004090100c03200340e200352000030346007061900804130110902214080506011100e17a1080402410020800325010b9003100106a5038400040b04a00c942281c502002c2c0f5000850056015410219546031600101410b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 826111636 1250 826110386 826110409
    0x1003060204030b01140d08090d082502190e0a021c05102306070807050f031306110d020c0907020a140a020f091012170703031d120d090f081305 63
    0x800d8540e011031000041d102411101604d2341903554203d943c0491829514a0140c812100105204500c1281e0003030031002401110034000c0784e1100c0c402ca0720b103031070a0001003140076030504030783d81800090f54100b0580041400c440e8482e42c8190071201c500c1054115030041e85ca07811003070100e18040009040c071218842d600c80c1c81c2581d42c04202c5a40001482d030f40f0803400001d006080100c1c1e0700c0c0c00d101c014040320088055002c180ca03502d01e8107800e0a59100310a019040100741380d0507551010010005d04000000389540040114080000811111002c000c241c0411441041e00c0e000c0000e8090b00d5030042d4801a40040c048680a8410004d5164400d500e00c0c1c020781840040000c50b910744d062010841c2c007144c0107050300d800f0300d040c40f813a01004103c000c00d40002c0040c4007410160b00da400440c1483c000504070780549901ca0310a500ea002000480d03c0c60740d410300071188080b1890380301800d071501c40d54003801c1c0d0100c695190f000036007040300035002e802c3c0307070080402080c10b02410045 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 826112886 1250 826111636 826111639
    0x602010b040b0a14030703150e010f090201082703070c050a120c032402070305070501050f1311040e153111040b03011a0a08010905151003060204030b0114 68
    0x1050b5150108803245003512603d80342c0d40115041200648090215030040c6401000c8280460000c0940c40d016201d800000e45d135541c82c2100c101c1422005120b1100d2040d03050f92000d120b40c40359800c41e03540b02c00e600d0f01c00310b041d440b14402c210b140c04201300500016100702c05110340390b890b03c810810810415480407041c2c00140e80040300041b0400303426002d496201a178240244042001d140ca0f20302d2050f12401c0661000a00009040d080740103400e846104134000e00c8203686441002c030003c842900c5106401c031034000c0034000640214401c0d444040060400505101141070322450102401c1d02d880c507040081d010301ca81c40d0b0101482c014540c1c1d501c444404d00c40031400001107040300108003c4c0c0b0040111024400d03c0d0f070303240c104201d4404000c0c0280f01d01210402946292140c00b10b0183c450f0305e42d200000f400d4101070040c0b0390502c0d007000103041c1441c3e540c08840c0031010700074000c003c0d1000f41100440080d904d44041c00255003c1c03085401c0640c1401403980e402d070025074485 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 826114136 1250 826112886 826112891
    0xc0c03140f0316051603030515041a01230712180302010c020d02130603050601150806030604110d14030a030f02130b18130207020108060d030206060f0d0605100602010b04 75
    0x1000c120808000c40360000060405440b8071242d0708011904c50190a00c00c50f40320800c0c243c0301040c981d150f00710038041c9204201500360745402c413040100312640414407085002034510036419540c010105880120034403180c2c05120f102c130600d2004185e06c4110300325150b03d4449941200c3c0e6900180c2c1000c0a805040e608a0103030940c1c0010b04003c86d0b5010003486900f09c04c0d0300c08119140c8a40c0249081c0184506001c4551a0716129881d000240281707101201c40741114840144144035440c020a00035014100613200d940f191441800c900700d07042d8200260300800740003c0d000701c24441610b1948009103844204074080201a10b078501803500c0110f0042c05048444908220300a00b282c400103406559010700c100b0113010800052180c69000c43e01c0e10390400c8200140d0010300c40c03207200740e80728034460b81d6040c20072070702030303100c60340503005034041c0c3d0020320603040c242c400100101c801444070342d031480c15950310815a40120f0b861210301e01498010000c5c03d070240188000c000303049030113 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 826115386 1250 826114136 826114147
    0x2040e0d0f08040c230405090c01021b42041a0403150f0b06040803030a050c12070507030c151431111203070312060b0306040b130c0c0314 61
    0x1c103104001540074845203a403a10800e0b00c440d040715605030301c8165018101f4409403070590066525415030707240641c0903024111482d454880101c03207945c00d640340184040042e014040b00545402c2c808091108580010819200010803c0d130020110000c0c800c01c1235900d40c101040c0d541150501252060015000e00091000dd80d4a4040c814a5003510f40300082e0710440941c5040904520003144c0c0d00001d0000b0089207900b80070004522400e030510044c0155107a00c0a4180d11340300d0001002c100040c0300d00410040c910440081c95040c1c0a817410303680c142481e0b114107014042400654a0300b5540b40d00c200e4514a001207507950040d441c10310242007842c075240158451034100000e0042944401050080002c400550401c81201510601c1084180b1141650f2580851021b07004110b03c600b21041d110b05501a00e4240d44d2194040b0b429619001c1c24403020b0407a40c04000d03800000c14001e0091403d883c81580c4a1076074982d22608500d07442d06010b440300f50004443c10f540c190801c070303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 826116636 1250 826115386 826115393
    0x10303080718030c0b0c01050c04030c030b04050309150403060518030405040e031204050c130902060a0302030a0906050c030a11090a060f140d0516020a02010f051602040e0d0f0804 79
    0x44654031000a052800c150703030b400305a580d03180300141c10003840e800840c64045441240741015180c002c06050003001586c68a0304001c0031400b5a00c8000c1200344072100500000300544005074000b07225904407410415410000380c484141002c4881807954080b50070424001c441c0240358000c00c0c030b00c2441041c54036145007280c0303d210324003c0074001c0362101e04405645104004441e0204403940c8022a03074101454030b55101c000c22482e00348944507c006850030074145107e05416154000c01c0c86217000886134054001c1e41008015140040d43c8210742e50205601d4050b1510075034509114a80d2031405020307a804864030001c10f210542010f0202e0300203910340d20004e03015140103080c044840f40c0c2101c03045a002400d404c45d8030008002160404003842c186c0c2105000b041e0a01c1c0305031445206042c202d0b82d54800d410b019000039155003030041150f0040e401000f0a032601070502443c94803640208054544d494072500381c0e40e101400c0b80003c40e038020f6143c008a8101e1601181904007602c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 826117886 1250 826116636 826116647
    0x120606090d02040e0c0303070c081203010b030103110609030f07030303051b0313021c1b09020a17072a060b0a060207060e03100e06062b060e190803100e010303 70
    0x6070001d009a0750b6507509408040300300b010510709040101140c3d82d89140d0700d0142c003602c54500c00c2c1c0034548a800e48001d500b010000a0700c1c1641e034000c0c1c2c028150380c69901c03070070210180c030f000c0c03d50000c0c010405920f00c3d8a0034050341c2444611100200749292543ca0020300b1150001c1000030b03044022082010030001b02c01c210394101e10700001550119455000198210005207006569585800f040310300300305203003214175000100c50030440d102a83c0e03a0710340d0080e840384000060014048a40001410100c4c2c6003083e0810000e01d40160302607007007003140014001c0f034000200d8640050031302104100417070241c02d4010f4400e075000b41305586032002c01303903039041240182028424034406284164504000511021001d4101404101d42054204e500e80805842300750141c401700b01301454101381e290300315414681d8103180c0d013020900c40e103440004051030300d0b1401c00c40c09661850154205100c20100030f4a004425844c1d507410903407050a00a121039002c590311305400801000881d0300b05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 826119136 1250 826117886 826117909
    0x90d03020c0d0c0606170a060605010518041805010203240a030302060f07050c060414010b0a05100f051e130e060102031e090a060513171908190512060609 68
    0x5003080443d41490340b400f40e0180c405504109070340002040d0342100c4d10320008402c1e840c20b000304003c00000740c48100456907841000b0141141d004078414041c52800c26a1280c8020243d185e854100031403d55151426a4001e88004001c01505e441035008110065001c0e41c00880c11158251110b04d5030380e019498100c010000c002d11070448002074041c0380141d04a4141584050940d0900e142c5480c0c859080c003003060b045c19080d868903413907202504100000400350ba000800d41a54001c80131404c407215084100901e0070800b050008070000901202e42d100031507031650102c0d4840d8001d004c180c1000e20140d102c05000079601003440180c2c1d80100848a442d480070100c442002c800f450512058407800328108e03000001404000b8680da0300c040a81040748076041d440480c9541c0e24944440305c3c4a02c55026115041601c200488503500081e42c0203040c4560002c40c10300c0354000c05008511824816800440c10014540300600310990801c1d0344004201c9420f13080c024083d01003510318041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 826120386 1250 826119136 826119163
    0x106030209011e1d09040c09020a1218140616050706140a0902090907060e04051e0f0106020601061706040b04060527100608072304030506090d03020c 66
    0x18040c01caa4402d060400d1402c1c140715440107143e070106002001a903400404e02c21600c43c8402002851800348a43c41c01103411a152070001400d00145100070350182649009103c114070041070306580d5070198441d0825542c039607004001700c4c0e04001c600d2001103a0f485040b0342069007045031000410306c40c11a48034803490120703103c40940c42c0650041071544030045c0c3c07680640c2d00308000e6207925001701229034804c0d10705010984070500c0c62641c61441d40106004603409141ca440c5c14245640515440000c11a80c14080e541da240c10300b13508801a103080d5800070014005020480d0104000da0041100780780048907200403100f000e44050014244c141308a4a0300a6440c5030b42d100d41105001c0e01c0700400030005000c0128035441039042c1c040d4403410025003400015403d951081e024021104180c032882e50b035039100c00c422182d41e81e1604030b280703d07100c40c085140d0b05410203101403c0514482c0c1c009055905200b080a0b28114058104400f01801008508568540070a0070001001e0b07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 826121636 1250 826120386 826120391
    0x2c0601050304060c170c1b0309030d0e13060609090b0102030405010c0b13080a030b0a14060a0804050a0b0114040f05070e191503020a091517040510050438010603 71
    0xc2000c00c4a502140c030203040c20a44d840000d011000b0892401803001c03488810311280b4040c00b0001f079644a0241c103011951507040a407605400500400d5100c0041a00a04010400000007100c40032550b01d908000005502410140050340722881030101c0070509000650400d4a0b00000a0580010307020060480b42805c01042442e40210480b405041d40b2030360300303074841c151600010010040300099501c1418003000000c1e03101e5034901c1546009001030201864600000015a00c0e8900544200c6640c030600c820b25010910803000c040c0030707021809100c0c1424440307408001c04d44d510540c0812803135160400348011281c0042c2682d04240c0c1c162402e000d65074062425180c1502954400c810a541007010b20b4041545030b030050031041025119103038066111104401c05103c5174211001050441c5518607001300c80403000d5911610903402c0b50b500b00704074035041d0141d450a540440364001e0b00025210b01244074180401c40008155041e50340e010034440c1000303030402c1841483c05043c1d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 826122886 1250 826121636 826121651
    0x20a0909020112051513200304170a0309020423011a070203070b0a02010e0f060a020d090f1103060610050708090a0e09100f0e0a060f0204050a2c060105030406 70
    0x902440304041c01142a20302040725140041400300500703072400100d8421545219601d170b0900280c492540351446003004440c0162068070707c00202c4e40085d005a40301d03000005400740c0b00e40780c0c0300140600d08040d42c0114040c038041c41440213580019040b094440c407002d00010800e0820803120b4110b0b0840c540d0340040b07803c0c2075400700c01c900c580c0e40c1c0a50940100e10022414040e86002000e01c0e1001e40d008108940c0d141f5a0342d41c8681c03d95007007074510b400c400d000c038580e19100d030080c08898074070f940009140c0c421070303403044264540e01204484030b03400ea10b0282114030301030108560081040d1084a8a41c2da901d030024030601c04c18800030100305000c05c51080e940c0710302014001401c06444400d4060074045020b0b581c0b00004000300f484182082c114910b44102c5001306829505124010003d00c1d04c9580d0b0400039105602d442d581c207035400d110004550350f900d50300d08020481e00014085040780c05480042000c60300d03005031f4100d04408244245642e000723080b203074001e0700b2030703000600003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 826124136 1250 826122886 826122889
    0x90f1706060d230703021e091302010315090c11010c09120c0911070b160f0539070503070b071203020d0f0b0102060f040b1f0b0406050c06010b07020a090902 69
    0x260140808122001c50f5060401050b160010342c00099a0080305c10b656806885003014400c02036058a4a4001da40303040030035400000720314400719040c41414041821101d01c10680c1c00010760f40d000e44041a11032100c1034200303030803140b071415000884000b40003c0d0181d040c064518100e511a46418038803400c0303d08140840d8103082c02c05801d45140a00217a000303100d01206a0700446000e4a4812105000c16000050061180c01c419129200c0004a01c400d42040e00d07541c20011034400f01081c0311560004c1030068954105407040d4940c8151407546108918600c0c0c01d85a8000502960009500b0b000c402100360a54030040d900c2000c0c1a020031440004a01038000e5003046003001d410a80c01c0e400d5a5a2900b107408820402e03421209603580710380080d14059410388019003180300078004a054802801039062200346089024402140da41507008182c0d070007079005200240b00810b2000000909110b8240180301e205001030429115800243c0404024405c0312001607950180c4000c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 826125386 1250 826124136 826124153
    0x50a0e030102040305030f0a090801050906070c061803050c070b090303040302060928050f06210601020705030a1a0106210b15030a0504030806030316062406090f1706060d 75
    0x6194445d00303407601c80c8031018180e0302d00e41002e00c046000c5003540402243c5028140700b41841f9141d5040100b0b0a07480300f00c000d8940038a01c20741074801b07544404200c019a4401403440800c20310940c0e4240d81c890388010b0786410810107411004a00c203080010360382e90b030b900100756406e070b079011216140c1d1001000002104040b1900d821041029101e0124198854000c900805c8810944007207441049140070001c01d849026000241c03400380e00543d040e04859480321951180c4180111500d250300e9100003850301c0c0303010000b200c01511a86d51340c41058007c0c0490b6006010380d04040c4029403030211410b035000148812100c045940300e042a08656408540034105041c4a9081e503403402c0940da00005010704840950100d140f00f00455094200042106c4109190a60842040000c0e41c0c60344041c14920400c003449219100041c820032254601c20070003840c290b181c035140d0303620b23144501c02901d5044e03015500c00d08050301244100b140c04201306500c0f08080398035805d041c601e490031400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 826126636 1250 826125386 826125389
    0xf030606100c12020c03070902030f0a3c0e011107080d11040605090307050312040b0306060910110d081e0702010905010c0e040b1e0126040c061e050a0e03010204 71
    0x10040c3c03114060440d07030081504522000158180d0b45602d403110308401c140d00c401d039012800c0c003228034002080010942d10020409030001c00e20942c8034001d200c2006810380c2d060f02c0070401c0c801660301c21084030b00c134401d10a004072040300900000582080300d440901900501404400c3d00281d1800c0e800800e9200103c034846403a44941c41c0c54031070780000c2141d000b94004500034410f04202148610740003401100c02903031190001c3c50310341000c807094401d0300081c1040d500a50148240342c200e99a60180700a00c0c1c14507500c10071101c3c8640c288518016094a4400900c0038034401e20900340400915240f0011a0340d200c424540c440384412401400302e00001740c0503501e0003000400c160b500142645029204843c03c1c0b0008260f20204403001a910103038020380300740c45141d143c50703500030300340d101d00d072450030000303c0078014070380800da2404600311004c03980c00c50310180611440b50070607041400c03080c044d901051114569100606035100f401c4100c0140100000c0603c040d6409404880 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 826127886 1250 826126636 826126643
    0x12030b040504030905010206090c0a090902010c15020c160e0604091112011a0324060616051e011505041104030804091517030a08070302120915060f030606100c 70
    0x15910306403c00804d00901405891300500408021440d800070004103010505030041100d10050700d01204c0360014040d06500301d040c010341c1310210010501c1e111603c0c0c00000000b4003daa03406603188032a0820080303030061400e0700103c550034000d01c9400104150b22000a0b500001c1e0302e0300d0303170230040120f0004844159010384614004110020190454089420012004242a600c40d000c05850340442111001c00041c1c665444428071843d260b1030f42c0110014228034901501500c0ca10f407094030000040c0c400d50b02a0740600d1804407600031b080c041d903200500800c4a04220000f0f619010382500c076a070700c2181c6030009240d41102e0802100c0c003c40c7e00c40075881c0e945a940b0200b0002e00940d038410b00c49800e10610000b5100101004076a5006c8050301951902c81c1201c03094607460405440c040406600b403058a021a0b0a1030360140100c8490006180810724403074844104030f4002e11260244100f081c01d00402d880000e80c41e41c020740122410240721116620450705601c0ca150081d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 826129136 1250 826127886 826127891
    0x1020304080c01050915030a090c23060703140408070e010e190e0c0414010f0f0e0c180a030818040608120f070f39091a0301050c090109090c0c12030b04 67
    0x108c1500c002d5030045070030a1250a0621020b69184814070203000d605100088681c90b904190946140c210005d10090b4442e0509401c1c401e04c0b00c2011105130031a80001280707138001442800381641d40e0b01c44600503c007401e43c1c1c44107450040c10744040700f0301d41061250111f8a4107941e00e10b50009005411600c440a0b108200400d034500c100b61410b1403c1c4669400c003504000d01066000307206000c1700a8507090040340b401912164402e0120340d02400c2011390144403419a41031343d030b035034400480086002d907100540703842c803500c0d08044214948854a104501d4041c003001030480201d07041d88040c11240c065625403c844034070700030b9845401c1c8001c00b1104144c1070755040000c01d044145607107031040500c445035070703200c1200212070103042c1000d403482c42000340c1003214581d0b64101c040d0714031440500a0b14400f40300d010a00355030007034400c050a400d01240000c480e50344031808070000e0820480c140301d450032504020305a10806040540a200e110b03180281090198000a4541c1e8016008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 826130386 1250 826129136 826129141
    0x1b0d1b05070c0b0f193f0c0c0308150a09050a0b0405010303020c1203090d080c07080307032c120d1214040b0615030906160206040506010501180f0e0a0b01020304080c0105091503 78
    0x3840d05d000c0c007a4500c205991701c050259451503184546007070701a503038446412340902a241902d4048009000c064070148505a607100c0e6124002c00e50f000303080741940400c440c00c10b1002d10060315802d0018a0149141000401c003003a800641504103c205552064251100c014242c0c1544180002184c010700b940449408000b920300041c11011204819503440986078114031784c49100c2d441c40903000600300785641c640300300b0820349016403d440d00d14008035050b091011a2a01d5030815503031960782c00510b180c0f2070345600011758990741c80c000c0000700704074021141040a000000380c000fa0480c54150000b45141d103d44422000c044598200f454503450a5074141c2e680c2c0e1022602d000a1b20081c070110301c113050001034902d0103035611801800301603003080011107015583c000d0445010701c2c5504000b402c4001c074501d000152184a80d207141c14a0854960001d841004141904541c401c0104001000000c94140e100c0748007413030815981c034004000202c2512450701c4104441000009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 826131636 1250 826130386 826130447
    0xf0e2404030f110604180f02210601020706211d0a0507050f090402060d1a04020c0c0f01080f0f090c0a151202031b0d1b05070c0b0f19 59
    0x14031a00b15072040468103c0f40c00c01405022076401035204905083c000c0003204c00c2e0b2241c06402c036416846002500508040340d04c0150b800c404210241d000a00c055441030085559040c031030080903210508122180d50a040c00c054891524401015422643c50103511005504030511f01d41d94880c0030121140b03041542801522059a84a854894000c0180360500e40c14245049072003150000c0c0054100440410001c1c00f41071221595520300148a0a07140c980e9982d1000e0854101c20704000c01e1165103140511504a1282141c1414080700740200103024240e41c00312580032156081452598950750107103441c100081d8441e03640940400b0003c907111035500d248109481712a070300c5038000320311610740c801240320030f450250504201c40c200d0000868041d00a11401d4081100001c1443e414000300208001c03144220703001800000303500301480302e0711144802030041c614005140090070000c080d041c1c8103035080b012440490307050b00c0050702c1c09a030016001c1902d91034607079610001c00c40c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 826132886 1250 826131636 826131653
    0x607050f0a1505010f050f060711040e0d2618070302180f0a0b01050412020a0e070305010509100e040201110f010507020f011409120708040f03030c030f0f0e240403 72
    0x704614100b42c5088000545040c0c0b0303051003000c80da8050b044101580001007444550780c010682550f000c141d04501c03c86035111446001c1c140e000d008013910f0805010b44ac002c1098000d90102800c2800c1c1c0300c90b007141d10700a4035810341c1005030810380000400c2801d0100c0d040c01c5080d880a5030086079030030100986040000001d01c691094550100c0319542e043c109012500c600b808240003c00900c0240708140e2036040e004502e03400100084081d56890803501e40c41c4101306d6000b0002520b5500400150400d02c4443c0d40040e000020345100d241002038490a450740100084e041003d1414201144101402a00c4001e901140240280e02d1b11040281d13880c460100500e1866281080302e144001a502c9100e0142000a0150051420b40c80e12800103421108040d184804200000110b0603001d025070700056120362035401345e9a2050034058601d10000787d8180034040d0b55450414401d91021384600b111400b2119208010300003689001015181c0c40c80320503080000401105022418 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 826134136 1250 826132886 826132913
    0x5061309030c02280b0c01021c06050a060903150b0f0603153c0a0506030a140130231c0201140a0906110f13060503150607050f0a 57
    0xc0d1000c20700a044c4582d90102d16040a00c18421071660181c1801450700450051485007102d00c005410141c0024420302d0158221074140c6066a49120802550404450348801008141042c4082c07601d1134650000110040b2401130196079aa507050074569959550300405000180640e52680b44c02500e2400150780004a0340c4140e0742c50003401900030b000c4104490100c03c40100c81080c0c203105802c0800340d10b64164040d48102c0d040c001040945944020b10300c5100007110205031000301091042000030b06030441011810540002c50040440c03181c60050202c55400354004003419081190105141c0c2e0050038859504000d002c44080d000030740d12280d4210b801e0140c070b0f4021100c2081e400c90341d400c03403141742c050b4020001070b05202c00d540c0000902030180c0c0020030810341c0d43c05200916846580e82150f0201c000c2080301120b5100c800000280c004c0e410302c1850740c1016038045003031901002606204090000d81a020000184480c15070f20030544200e6007000c0c030604c0e25103050b010300e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 826135386 1250 826134136 826134139
    0x9241308060a0f021303060902030a0506070f0f0513030b060f100e03060606030f07141e0307030b03010504020a09020d021c0207020907081e09030c16050f0f06090405061309030c02 79
    0x18018007030008450f5200301c0c0c5003003800c071031401c04152869903600040c002c5078000743d86c903000b026440000b1030800d200b603500c036500590328a40045c3c0c400c0e1020b802c4260400e000313020000709010f00d070088043c5880c610103907138010000700d560307640e06800100a0144941c00b01d4000d05416400c1451603048041580344480440030740b041582d0341c105200081c007003214018050016030380410003082c0158000300c10210300320762151604010704d4120301c1c940070304130607091809400030803c061160b0503c50140001401c8000384260306260b00010131601d614000d507102e40741d002801ca07084800c29411151481e54400c3c0c0c1d0180030300400402d500075041600c1c164040c0d0036650004821701c1c0714144c01486034907443e0486031400340c0d07001c800044200c0107000004602c410000100c0c03114040246030340d4000d90a40700c1c107110703062000740700c010500070f240d190040000380c5230a501a5900800d458507400c042d500000ca81e9110303c002008800010b0410580500d00031280c0203141c0d006440d141110300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 826136636 1250 826135386 826135391
    0x8010902090402190f020d1e03021c020301060e01080901140f070c0c0902130f06081314161802181c02090a0203010503010501060507050307060911131a01020309241308060a 76
    0xc0130041230701e20029401ca20461102250b00f0317089a00e0090307010785141d01901254076448080040310380c0032a8020f030000804180c1b844084150b5603070081c85542e200c5007010083c0103030914080015650745018220f5100594a40f0006407801d120b0300182e0040d039080020240c02559400c1e10400950082e04c4d040a214013209000c01c0c08100c0180c0e9108568142d9240451980d5403220403038014412101190580e401000f0f04040800030450f01041390369541000741c01901e00b030344041d0500090082c041e510f030b006114820400d10403da09601c028000d49403a0a58404541d0010441104510095022070070006202d44030030f40303502560580e20140c1c000c21090743c80d07840030b685070301510344002c001d0b030310400c010000580c0076008903056903c03a911034101250703502d0000342c0140045201c040c041c0d54500269030b1041c400c4642c454850300a0000c1c6140c00c8844000c1054001e20aa40768243c1c0503491440d6030707001081d800c4401c0300c0c0030080c00d44801070300c420304542c4411007a41c1e10050f490 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 826137886 1250 826136636 826136653
    0xf1b0b12060a0302220902090106021b032a04090c15022406040b150c0c21060103142b120605011b210e0a06090608010902090402190f02 60
    0x1442c04203201500c1d0010f004e07950542900d40021201c001102e0248035003601c468403000162501204140602240d4010b862a500d4042e512103000880e0b1070114030035403052501c1400005003070700c2c4805042084400442101c100d001103005010340300d8000700228049100042c0c1c903161883c070795000c1c1c09207a080d6040c3c1081c10445e150042d00b000041904110802c01091207880c0a42c0020700e01500500f040ca01400403901096468018030302c107048070780010f10300060030302d09016050020a5402c0b041c102d58908081625603c07a414040107105022900c00744050b941c00704084030442c2c025842c815103800c0d02e880fa0480108c00054410041003680e800e403401c40d45075003d10410b42c0c1041e999040603d003860f4020720302d0703925980281c3e4400c0403515480618012005080c984103e161107070710071004110207104003044640d01640800c40d10aa080c8441c2d54007914050458200f0440981c680c030503000010028440c00b402c5880b4810400c50207080030790001041181445180c007602c4900 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 826139136 1250 826137886 826137889
    0x303040620040f14042a0e0d0b0f070c0b0c0d050702010507140a09120602043623390715090c1701050705160f1b0b1206 53
    0x42c042c42c0114402401481c405105801441581d0007050500800124840e80c6c501640c074648204d01c80144020303402100c100350401e41000754003aa98105403250940c500090322070340d00c01c04000d401c10402d0400103020881c018425043c0d203540e81c0e0401c21408640c10501d291a0859000d100001207003810000010703c0e85006102d85841041681c403400c4403401c6902e041e5510340c1c0304544c180240040c0c10310102d2400c10824007051000c1c0705103c010b84d41d40c103080c05c045102010030800045481d9202c4150303600b5013840d0840d4140489007102003000341610108a41020195803082070b070200080030460a6140c2644084c0bc1c0140205402c10080480c500c3d8142c0d6501d030051041407040c00c00100c000201c1d07496000003044407110300001d64041d19604c50f206548141d025000301419048600e111362003e00c60a6001011414000d14105a1160710135072807a450201030440210000306409100d01003051010003140034600c561380380c3e1107003c0400c00380c100000c0c3c108480d0700400010582d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 826140386 1250 826139136 826139201
    0xd0b090420010915020303010302151e0d2a0908060c0703080a0f0207050a0309060203120c18060309010903140a0525170705060709030b01151103030406 67
    0x180390424036820305100310740011240158a10729080c10481011030020310f16810b01c507201e0442d00d00d94051903413549135004000c14001070100b0214104010040c581c8990700d0b0400007990701c020403240f2034540801c66400f1000384010002c1c08800d0f80f90958440e80b40d0f0240401c1180703000700e03032200003007d80c64004140d506c0d0001c4940e40c40e0641e040200c0d4010a0080c141ca9a000000103008113510f824060030307100341d13003120104071203c0e0300c19102c4000701600a00000090404d80c8000c504041103039081d010481001b4095945100c000140c40b1000003003101101825280501070320380d2402d081039400c1c001c015460080c1c0015802d18003004800d415581120810701d103583c3d034181400f08803164012011918180e0744102c00031400c1400010360410380a5484131a4001040c0c1c549183c0d08000d41090402401c0e030040000e01d00007440040d0008840b1819900d004000d51540400c070b44054038414121101501030b44004010441044402c0c0c02500902500c00c590045829011681c7e401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 826141636 1250 826140386 826140391
    0xe0102071a1b0405040e03130b0a080903090a1715011403010b03070e0a02130e071d04150612060306060806041e0305091e040c0908010c02150c07030c0b0c0d0b09 71
    0x421400c200802ca50305c0d140e08244d9203910300e181902e1510501031441094440d6660088400c00320116200700300d0394002c0b00003940460214099441c181903400042c451040300c1c0914031007200b1070340000030303042800c0000d803415025801a804055845248200e40b80c2c10030b0401d98071a41c02d21205184c981030125080d0215145200021096198059264065001710401426104c1d801400140710010030500d02c0c010803e540f10a209905040604150000e84014541c0074505004d4200c1c1075840740102c21086420901d000104d84540d489208090006a80054006414204003181c801c102041d03c5018610400d42650900d1100191709210f01300c5450240108205000446447c00c3c41c070f800400d401400804a0f00900740840042c08586c0c0307241c901c000240100805010080092189140c0f2024500081c403a80b440c0d0440204010802010418034080100d40c520405015020780e182140c1e114550030340514094004c1c2025810281c101038460b400c081000500381804681c860 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 826142886 1250 826141636 826141681
    0x20405130f090206161209050904060c0e060703030b09063c060d02031503070522021e0703090e04110105030601020c131d070f180e0102071a 62
    0x2000c0d002441118001c004201d280c44200307440d0160603005980e80d2000f00415813004180340488091410890381050340c8000820178800246030600941c0d95444009a001d540900081809851903004440f90095050007030b0304a600460360208264141c4c002d50849001612001040e9072001c0400c009070300210441d82e1112a20200345503044a045041d00d8000301c0c609440c3d00783c0c0c2c071800100e02c2d207170300240d081d07a51240c1c04070900038251100f0705176610b404411001401030505040020b0fa08651890a021050704100003420760204181c064800c0d48145420203601a0340320880640720b6440203608500003480301d6000f107085418000328501403034001500d200040100c100654484d8000f1301464150320545210004c9a909c1c003141b6813990700010b40114a01c1d8410321810010314962900c0000341c0c02c5101c00340500e0a20002440407140301c0e0300100c3d400218268024001c00b20284800415400041c0510034031903200000c418142e075552003d48075507201200d22410940380420300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 826144136 1250 826142886 826142899
    0x10612080a02010e07030605060f010305040803060f01091508160518062109030912010e0d0c0309030606140906012c0103150e0103030206072613060c0908010f020405 73
    0x50010540d01005040200035030b0000003060140380c20003916000c02580300300c81c00c0f0345841c00c002103400c0100d0641248042030030140898109a60f883c0402c4c040105010700035a403a51400901d40e00c40d15940000f86041e40e0544c081c02c5541000900051040720131200c00c0ca030502104e80a40d205004582c20002e034503081c900703000c80410402c0420b61141e8840964038040d444040c9210003031a00d0706016848600045543d502e2035410700c6200d480d0162000e095034944860180b01d0034004c230b440308004072685000050441285019034443d451031304040c042520700600420401080c401d40c40c0b60300c03c200c5a8002542d01c4400440c1c1140f126079058020f4460b044034041d1140d0070005842e410101410701007600008c40c49460030392101640220f04203400800100203145d018050305030030034034070318104a200341c091100300c4103e900d90030300c25030502c1d440000461140d0600f80e00202c1642c01501404040d0441800410f107111074080c4030940c6d403820000010080207442201d08a92015104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 826145386 1250 826144136 826144169
    0xc070e1b030a020d2f041a090a080d05180d080d15120309180b0306041106070812191509050c04080d0504030614070801090c020a0b010f06110106 64
    0x550003190409404044841d40038032050b40150081e0060f014003c00e02d1003c02c00601d544043c0103003c02c0030b0f00700300d000d03100208024000020719084404135a00c030a18010323507501c205030218071201c5c191f9110982c50300810040e0203c85500100400c40e82c01521070403201110702c81c040000038800048001c01c024000c2000c0c0018090365041406d030302a5803400341044556445d81c01000200200085000560bc0360003840580e503040d001c54000381c49448200035140001000c665074444c060300c05040c48501c804012101d90700c0c9007c4402507684500807a45030a00010340545151090b906080100042c411595140040d403003a00c101d0200203c50780d4040303242107010001040041c2c0b41040c04c400410001c5524000ac12542683d42c00a40c0c84030fa856240d42000003c8602c40c0400c1c9a12010210601030b807190b0101c48203040d00c1014400040c410b5801505920707200300c1140041a9000c960000201d4940719050304d421107040b915151714480b6802d40726400c85940f40078084000e8444880d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 826146636 1250 826145386 826145431
    0x1110706051e07081e0a090302010501090603110108041b15081503190f080c0c010807020f0d050f160602090315011505030603030d0213030227040314090904080c070e 73
    0xb130729508441e405184901d01c80410139100c6024a044600003803844e12100e020040540c244a450b0040440b40e1080004601355a00d1403603000c030f0110001d040245140108007403000754841780f0070119240a014181c19624802501030707501a401c004045034019000581010555001e0482c007400100948070b2000c080040702074402c001102aa803220b211940c0100041c1c07034030020801088660018840030b00030400041c100c0400502c0300b001c542200c2600101d200000621200c0001c150424540380c4400142a00035800f442d290103458002441501c4180308240e40141030510b01941a07401543d444501c14140c44c0702881540c29107881c00c400d07201100e00c58005560000350003425a403410380001900030581c1c1042c44a0750501a00039801c01c00c6180c40c0c035034854010041b40c01d2000d00c0c2c8a10390301c1141c0f074034001d1010b0140a649039918042240e502c0172140002130050210100b0704050500030415000304040b62124420380c0000b250b01c4d0440c881da80d2103452103240400d00d80401e0798 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 826147886 1250 826146636 826146647
    0x1120b151302030a1d030c0706020f0703080306010e1f030c031e0b210105060a1508180c030a110f0d0f03030908040e151509010509010c050c0301110706051e07 70
    0x1022507000c00d80d115150051484500810f40c00201c17400029915022005040780c01c1542c1d941c400c006660254060a200d51030210f5002c080b290444500c5450f0b0742e075400140c0e0300030000d04d6541e40c402c45030040c110b00c80b11020901b00c00c400d601c0e90104010700701494180d085503c09500344400c0e81c0d5021030300c0d100803543d40029030100d0000d8441c1610058010105c000f04564225400b23090b5120410050141044d90340d1070028400b04241c1011078002d06409403086101401c101e010360500e0045200100c1308000c0301a200ac005000c41d101d0071400d0400c402c0c3c1c03103640e4010904ca8500c58180c81806e180c180b0001c2000e5402440503600c0340381c10b5078268028920030108984042003844006204003154540c644503000d103442c2800c90540c08400c01803041814401d460b4080b100b4019903d46990110070380307080c12020f080800318240c582c10501d25080c040c0d0009903042d13080c0907411941651071400707030900510818083c40b1740d847e100c441c0140c1c07000c00640050800d03002e00002d40b100707200d00c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 826149136 1250 826147886 826147891
    0xf1b0c08030406141003051218040905120418180302070b1615060510020106031e02041103160908030f030727030b0603070e010f092301120b15130203 66
    0x40400007040c84c0005903960900200b102c482412041d2840c080003400003d0084052503d400b1407a0740c6880440004401c420401e04079641c00b85131743d8041a42080410015401040c42c07102d0b500d9199685d6540000c8103401d8401c51020310303402e0038414082c545411480030710a0782e058024000c290309041009035940c006a03120141d0283d00030240002c144103000d00c45010500b004046502420b103014420071250104002d41103a251400c10000708004002d0076002d01048002c41c4050505400090054124010402c500c81c0b000828095400b01241c6003042d0010f96072a43c1071402c2e0756840c0c440d200c3c0109110050b01c0e240c10030009203850310814490203602d022251031b41c0498040100d0648103800c540080721440c0c02c2006000c030034541080b21400034280420581e4940d810512045c858600611034040095203901003c019401071402d580300e0403001154820140d030f913880e00203200c10f423800400d4544210840115400e02c05102203134400300c00140c42d003c500248404a80001c2d13000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 826150386 1250 826149136 826149143
    0x7051e061b030703030c1d12010209060d060e010515030c07080c030a030f060f050a0902090307270c0f020303060f010e03070914010b0a020a03111207060f1b0c080304 73
    0x40040d840e60490090307222240980c1c4200568a8600c1450301900721445c035078a60042c08820340400c00f810b014400300501e20007058414010880e445510180a4050b00b4000755001704085200441d104440d0b215008569100c0045c0800f40d0360340301880310600070030014910240e42080001d600880340802410402e1180b090700b0701c0e001d03849811505640090141d40006500c40254070503481c61800340f20094603d2100d48407103c1c2c60038001070b0070a0071a1042c8110540c0210b4101c20556041c00208010140005210849031111071820715008020001c040c4075072420450725103030b5109d00305454042c62035400a524648908040000f075144400685041080c3d003101050151424400b10004000c1c520001c03400c1c0c883ca9032860000503050300111201da90500c07455040710350000ea061500c1d901818242448148868028104650180302003080880040c0c0d000400c56107500522050600200401c61001200009102c0c41c05800e00c1000040b0300b070245402250404000310b811511 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 826151636 1250 826150386 826150399
    0x40b1302030d0806210c03071a0d0f020702030109080a0f02010204120b10080111071e08070f06020d02040303050c010c02010902060a20072c010b19020f1b0a060207051e 74
    0x5c1844d0b820f00994551404035900c2d40000f28206000e0500f00070a401406074401c41500f00c43d41442241002d000e001c984001541d1191394081140c6003660440b4142070700a0300034005800c0d142040501da50200362140c0004500206080351540b0620030b071400d6074146034441e000700401d500e81140c03c0707401503c410b03c8808440d10008545109100300d0703001e0b41d44c2e0340c015525683d6030300b022602c2c40000c005290080800703080040000d140002120f4440e03070b01c00311001d40e9402c03030b00300b40e0004d0094081da20041440000d000c01810b81240203415045c030010001d00003070020500490a0b682c208200941142c0c0c148040304d17029014040e40c0c02c40c0098044034020106400640c2c0e441e0185983c000a5585604a452560814241c054641444009600401c80d515000d9032151a1060302401c0031103441c0500c150405910a004800354011a8021105000c1c1203840c01171304d2014400c4040c4c46040700a82c0081d00c140040f17040b030100d0318005c2c41e1440c421070543c580c0c1c0d01c800d00c80d00303110351161 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 826152886 1250 826151636 826151659
    0x605060430120f050301030c05040207050f070920070b0c0d2904140714090a050405040303050a200306042c0607020d0e06091003020d0e0105040b1302030d0806 70
    0x511104110141ea4007070380b41a99481e115030b9000e4060b031008145a02004030410040c0082440e030310b0003000301c8405850040c1d0701c2d1a203051035400c1109540f010000b0380103108002034102c4940d0006042d011501008a0004842e00301d251240c1c4110a4020186003240000500700b0700c0b588050102120b540e00d01050000b884001b05055000300d07030030300201d01c0255001d41041e080c54400d8181490340c400e040741d002d081988000d400d20b25048401002c10500084202d01911084041740003400054024010b90505140140240c08221081030000c0e2a07d0081245980d45115480c035038081c40c40d03024a162030702d105000240c20f1400001c170b111040001c1c0c5404407140304030203001e00b4000303502030581c0d4142540003d003013500c0305401030f0400c000b200e00851941d82c1c010842c0d19041007200e006032407c0703e40200390301a0040320381c280000351a08103041c00c40001900070300c1c403545c843d5040d14042e1303844051036090101111000b03501a070022501504207400782a140b44c220000501000419 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 826154136 1250 826152886 826152959
    0x10f0c1106040b04090e0f1903050415020102031f05010e19050612070807030506090613060801020406091d07051215030d0903050c010206240d12080105090a06050604 73
    0x591041d845080700c2c2100003005c02600c091031003a5440400d861002d00014044d400c012039035044c41c000c10030602d0150040c900300305800352084038010004425410324040c1c40c018060300035081160307100d601c600c0e5000000312040c5015103580503074005843d0803da410301c6c0f0061005000d464061400900307000e00c0c02086d5a030b108009002a07040c0e4281c541400e1034008030007855202c018094005050911080c421180e584a010701d07070107031054071100c0c0c44182c1c811041c0d02510459100201030351000401040361540404050290b80d24005801b0002010100c030b100d00610407106400000e10600c000840f000d41e10080e20380200c0f946940519403c000782c006814008601003c0002c40c086030360402c10400300380324013508403009001400441c42d003075901c0011440e1543d550f55642d00e41d101d04000e140c2e1102885c3c184903030000d908000441d42e8000181100300280260b5216052040020300002c52600a0006844004c0e00382801d00d80303000580346d0904689443c08030520074164009190 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 826155386 1250 826154136 826154149
    0x504030501062601180602070812070e0a24180803030109140109021602010e180c031e15060d0b0d0c090b010201231806090303060a060c02010f0c11 65
    0x1e4500000c0c0036001a05000701d80402d10514807904003da411300c0b00b901c904e42103142011244980050016a503080ca41c500848144160490b2010240510042c80401580020480481d00003600c0e400c00c5c40341c03154603030b11940c442c0c407018500c2c051070450309110031807242c0c210000c000c1103107408035403d6072034802150540c1c00036040302c07121540d246818090f0b005405882070060030350440841c6400a080d071078045a02984101a0510070b01d003a1a00319078844404040125224400b411140c0c1004280e400f0300d68015100504100350050a400d15200c462540502541f071380010028240d180d1428040d4035000b90b80e00400700c513901c0000790480e4684050b00720440b40314409522620b41458902011107892004d658110381c541001d6854181d00d001c19150003100005081c0c03450381d28500001c2401000c1030780321405000c0c4001788407000300d0010285014440440c1d280c0c0715107403611300450342d00700700d50ba01034005125140705082c0d0900604084000902070b0560041c000105804244c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 826156636 1250 826155386 826155389
    0xc0c0d03090f06030c0906050406020d08041b0e09010510060f0c081303030e12010b152a0d0305130b24041b120b030607080903130f08101515050403050106 68
    0x42500d407917125000541c0040e62001402c1c03075080a904080c1803407002036030f400c4101c0d60601840000008501845014803803201c4524404403418200c6403205004900c406007607510100d55070804000c60400131614007488140c5050343d9503a121340c145444101c0b404541a081994a041c04001c0002e100740b9000f0f000b000341d8065110aa0302200d0380c014808038141483d440d51940c0d2601c559218141c0d03c8213004080900070362805911048031070703002424181d8000948000c0c0d07500051415220300007061031140c0c4c50441c2c404000640c1e8100303c0942c242d8001d00d0080841141d000042e0ba42c01c1450034000b00c03220ba50304412078404175680420100c0c1e0701c1c00d800e5681145091040c000161f440001103410041d0050300b80710401009012030f40d944405062001072041e40000200e180004005468800d00800007140e40155603401d034058451060042c06002d00a1840310204891240540c01c080b00c11403e0f40310080d0729003500724824000d0380c00b170350702003100030030002001c140240190700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 826157886 1250 826156636 826156649
    0x30111090613050a030c15090b1c061e1505091003022d181219021819060b090a03030e03120f04090c181514070f02150c0c0d03090f 58
    0x14046d814107800d103980c00700031440c107410005540340c103000c1050b015003075900003600001514512501c0d403a116002c0c1680d40c100e01d040a24039503584140c5e84200d0a50000c481d0b46103001c1000c88084841281d1074800c0130010341e04804118481040709200754002c10513807041c0e641d2680b03d06c103602c80700607001040c1c02251090502c045140da054440312108810300c01d1040310740755140d500d0b44a10a4070b412085110b142d491402490f070201350341300c034114000d0100e91482429139600c0e003a40c0c02d000c0b4040800c2e00700072942c0340c01c42c0450802c10880031500380c410700030a181c68141c5555400c64210079003502e4180c00d800f0343e88441d00c2504408001d0700d186070780c1c0d0000c00c0d180d40c1002d4001040f80c8885c40401e08010411407112442030340c400499003a623545d03149800c140b420b03036402914106581e4952064000d8006221740c10300c5012204100c103684200e41000d05044d0402d440e1b0514003a4049040a5030010700401d2118034006140c0c9a4280c400e013452403109540b011100200c00542e03114a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 826159136 1250 826157886 826157903
    0x1206010b03060f130c020d090f060e2b05030a02071203050304060b03010f0c0302030406050615040306051b0c010c0210050606040b07050c0603090d0206070f140d06090c020c0f030111090613050a03 86
    0x7d11724940042950024042000e1100d903640d2038480014984182d080c0443c0c0904003083d004600f108420140b0b952400107035907460084c00d141d02d0890340d20342c0b002821800601504d000410302d09081c0e41140100d5815948042c03c1d03440395280c13100148418080e145e850b66030389940300714904580c0148180381c02203480044e240d241a040a400781e88006001c24440c2215030803400708244920152020b032a0001d00008483d99403010b582c0c8140c18144603100c050501155160751880150001101082c05174260385d00c052644075005d040c0c07042603802550002c01840284900e00c8400003400d0f20030701400403030b00403031070b130001142041d40291000b41d075036041042c5102c0380b250100007003900408c4c3c0345803e080b03062f0000c50051580e2100601d81c404060002546884480c0302c2e0030241c00b61110801c2049201c8507458041c0d9900924144240900c404826295075443c040c4100800c4000101240d031420281c0380c100800c4d540283d24640d200e403c0d021003c02c5689404c102440618132500c40c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 826160386 1250 826159136 826159153
    0x10e1609030b2a0307141b030f0307022509020d06050a0b07031403040f060513021021060e0606090109081b041b14030907030b13021206010b03060f130c02 68
    0x321410f0110000399580020410074890501e502c0340c140c9101c00620180140c480d0301da10481000c0703282e0001010060300c004102941940c415600131800b520380b607000c841018280300d02c9411034400c4c074202d0072080310540d0303810009007005800805225149003000070380141c40f1700c0010200e900315040701001710b0340845d0104c100743e00810042615114550200d0030f42c0f8084c3c0d1b80c01000300d00190003c211a84400104440b410030111a450182d0b0042881c2103080c0080300040c000d0780403100c42c2d1514082c024200405010070320540055540c107000c0c7d407070255a00b10030f000e00d96120360b41d890704002c2c00501c0010010024070000301880c0400e122202a500210300b0041030f03034a80c071003101d00c03140d0054001c20255000100d403a9080002c401d880e80382e0f41d03448841401d0913001d50000c0e0803182800704002c2d0b0b40d0300d50442c0721a4035100312202842d180e04401280d1f41c803802409121610001080419198130740203080116030040240701c0c60402200c819540700760303000c0008400159004600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 826161636 1250 826160386 826160431
    0x112030212070c0909030c0b160806180a021e22050906100e030c1c05190b0106031e0e0c0901090513060911030d02030c100203010e1609030b 62
    0x160001101210368420b00b0103600b52525100c0c807480f84214800d0030390740c0005404241c020451034140a0300b107103910400d0707e07140c4484680070844160000020740719500040c11460300002282581701203075044049a6070301c410340c1c0001d6101201001012008030380b2030790820f040d60028030126010088900e458450140420400754054010303e100b818424104020380d101c148982542880c0b81c41c2c0401d0581502000c6030030f15413104000c580282c801003107949010f407050340d049001d0b8803d0040ba090461440b03103405000021400041c044045038004100c1c0078031a402100d003081c10200710407070f1a000ca410010407681d61103020b650a8014540941d1585090001e01e40180300e0400240701a2406010100c414600000000c1c0070594960740c0d03c0a0140c50315003158003160180803102e0b82a078445d000381d56074100314000d2545101c2c0c101000352204582c000d40303040b030798901e5100289842c0d00941d0200c01400c06041000c120071940000301140c0900701e500d014001a04002c1c9646034030300c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 826162886 1250 826161636 826161643
    0x100f030e030403080d09170409020405011d0a0501080c16061b020a0c05040f0603061107051606020606100315090615050c0d08091608030d0b03010e120f1201120302 72
    0x24252005070304140010404140c021003140c4031071050749800210154240351400d103249402d4106004000d0218020410300031540c01001510fa090321020b01350304502280c000c040c0f008500f1a40c00094a44007001254010854145c22690492480f824002d2100800d0060f0880c0c080503103003281c58a0b02c45a000500d03142c09621602548050308002d20b0f1170305d4684134200981b082a006969500c0d00030300303401c010f80c0300d00083d40d070186040c4110907551122541e1a0070202040d80d0398044c4288640d98541004480000c590f00740d0040c04080d51444100090841c502d1184014140c0315480a03525807002055200507000070103000805030700b00216a40b03c016507180da402404003c004040c0020b5000500c40d001c808a49000309455803507001032414455060700400010848140100d008440440541000052070700d00b0000c2c0d0075180e0815003a10440b040503080ea4201300354150403504004010300c100d050f07100040c1d103440c0701d44c00c94055800d0b0981c0f0020602242c2150b800c101036060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 826164136 1250 826162886 826162901
    0x4030b09012306010225050a030b010303030b120703020108070521010e01060918090302010b06070f0611070201080a0e16031115040f12020a0b07030302120601020118061505100f03 79
    0x1002540d280f428600203507960340014942c0034410140140448034000c004000f1014002c00b804140605075a03250090a51200317000480100e42002119101030400980d06800c0b00c0400000380301d40c80c950b80040d030380d80342c0107042401000f10421020745003401c91500942c00507a0083c41c048150f25042a420580806070882030801180300010070040720b240e50300040d0381c0f02c2c40f44002440090345c681070340106075202c0181e80109000c50004c040c403005102a403c4140201002d2054050b403989414880c451800000e01040051010560058169010440103544641200c814014070107410b512511198402c555040345040c0a080d00c1c1004407813901603140cac4035412401e141c2021f140b403d600e21140036a98800d126103004600707540d511000040101091403035135a6074445810000c0203540810703030101c21250241c0c0482c00d15403052090551040c04160a0914140541e8441d0b014000c181c00003002144c112802043c3c0340c1da686100001d4003142d0b00e40c01c1905c1c1350f00301d001c1c081d217004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 826165386 1250 826164136 826164191
    0x506060603090304053601080c0301060b0a05070f02091008011503021014072001030b01021f0207020604090f0c1b0203060406050702150403051c15090902030304030b0901 75
    0xa0041c440d00341c0000040d501a14011280c101da000300f82041c02480520400d41850501400441d06180f103071b90880003410380f100902500c003c2e0301d45200781421780b01d542c4241d000011041118410551103178014149842c031801c1c000d60040e0b51900001e4889406694000c003400c10700d0300401610350300f40714180c02c0ba000440d41c00c105c00d28580003d5007a003c0d007040d070303410701510f030320784142c04191002105c0100d5484004500410400d450081d8030040150007a030100b4a4407100c04210f45c00021075481c42c0c40a1110110104010407045000e0742040204a03000403081c00701041d166000c0c09010080121204009684106003000401b194000746100c0813201050380d0440240c3c81c0070075170707503030141c5c00040c040744944490388101d152146100800440c00d122100b40400c040d4401d000300202108100d1444c031495400c184c00c8111a51007504036044da10402d030070002404c1640141080c00e000805a070f041650303949880702c0d00b003400c40789400580d64801213146111a103402c16510030360f5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 826166636 1250 826165386 826165399
    0xb2e110f07180609061809051504061b1d190f08060604051b0901080c040e04050a0212190f0c0302060a111203010605070311010b030a03081803070507270203090307050606 75
    0x243c00c903044c00e0601c01030380443d07106c0d48650002e02480030800c0341d405a0084100f85441e18545410720000605030f01075480b0141c07102a00c001c00840c860550040c0c8058401c0004800548183c100040080f0f052040700e07032042c1480c00011140203211050000b0304003217000d0000c2d45460b4003000110340d0001c00329502c1c00c80611484d04048a800c0a481080900f0309011405444001c010071881c002d952103070700300c1d5a46804000130000042032508400c0d20a0f04c0e8040240c203054041c80c0c440c280104100c035030b81c9005891001040c0c62014181c0801c1c01518030400d05a280d4000c81d40e039506c00032229000c40e82c0c0c0344030701c154207000701301c8013030050305d811000b030b0655040c00340c010818813407041d0180070003400302c4070240b060380b007903118020710500202222031800075482d001e03103884400c0b80c1c0101c4a440c980a101d121200220454111690080c09080c1442c181046008040c440c0113940000e60791800e0307000c1500700030b0302c01036008551503001951240560328001d4030340480100707401e02812 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 826167886 1250 826166636 826166639
    0x30709020f13171b1c0f120e0d03050706061d19090b010b090a0509011206051b09100e03030a0c140a02130b0d0203060a0b2e110f0718060906 62
    0x300040f442d01c0c06101d41c0c00c1c1510044c0d15107000038403440a08201d005c0820060142202000100240c04003940e2282d410b0340000c840681c0251003114260110315000440012010006072180c8000c2c0521480707020005851034513807807180325090511000e1406050072400340200710300e2501d0301803002d80d1030610038018441075a0341d42031070607010312510000c404042034002050341c8140041020300740251100045681d5244580349017085988240c0c0d0f86482c000210364195942071840700000d0418220390b203080d034100d0a20564103050384a02041215001104c080c03030b502400180090f822070341d1001340f20005401c2a08001c11110b402004030351002640000503111140c0310966164155800200e000003540072035504e40105600a6041c000c1c0020014219420741c0100e01c90b0205450722001c0020444524003120441d6a224010040d40c81d00034107807512a90f4000c1403500e80800341d4506480c20208540360081c4e0707810002043d21454802d410480013031265800810320704c1130502045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 826169136 1250 826167886 826167929
    0xf020321011e0f050d0201020a020d080927040b1009050f071205070e12030c0304180c1b06090c030219140d03050f09060f1314060307050a0e030709020f13 68
    0x540044c400c8070700944540400d401503a0080c0204c000c40780d0098050307000202140b614004a51081c0055485041407101c07010588003184000d02c401d0b400000c44917800e403111b84541c40c48000050032084412031030070012850041c240609801144210078091071414442c1000d042443d00700320050402c1c1ca040c0401458592001d0135021000d4180c440c4c4003821541d0040608505c510540030340c091000040000c0c030540741c0c1d1a41b003402c06a8940800942240f60402c0b107402100b00a9a000c12800d00c0c00308020078807540c07100300b101d88070b40840f4100590f642d000c2643c05500362401181e04002a80410490712159100340300c032501190b0b06410642c1d0355a024000e4055440071911960010070401420b407a11021a0030030600300e528203484030410203c0003151141c2d806015403500c81141d03248840d00300841624040c14051b11007509100b4604000c850760105c4440c413580c14800c2ca440000c80040c00d10060845c48681c10440b613a42a81c0d104030b28000c1201c0d4031008400c0029200c08882 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 826170386 1250 826169136 826169159
    0x30302100f050f060f01120c0c060f05070c1118190c0219080d020d0203090f120403020a0308133c0f061202091c0506150604060f020321011e 62
    0x2150120090100400100c0d0b04a0000f00c51820071f82c5031115402076181c11085150010303116020500c140d83c00b000800e400d0311780550b21040450b0303030b078103541c0e001480840500d00c080101602c405160f0504020303035030701c8000946d480d400c407110510010003c0d0701e0b1070041c50b00a40041c0010540702c0488c4040407028640000050b04070706c008035030084c0364031035a01101c101607102b80055440c2d042841c101d50725461703201d031180850320030302a25289203c00e003c295000c490300201405846451502c55090a03030156050340400340c001d41010684d0402294160504070000e01e44a407040c242c540505101c81e40f10000100340825030300100075400c042d55003441510100c2c903000c04541914490030340a40181030b5041e50013456440c0748244030920b91034140759079005504541240d2600d02c07000c4002401040040c4e0060010881404414014a16009444070901c100c0b45400900074000c0706a100310100103a04490580040140c0c10a600300c90754445425100030220b1480c1400c40c900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 826171636 1250 826170386 826170391
    0x5220609141305042114090f0f13020903010e0c0607080c0f060a0c0801060c0f02120307170a0e031902040518030307090911090102060c030a090c030302100f050f 71
    0x44a50307920012903a02c4800365a900c0c4288880240310b03e0801d4034184890b102d42d441a40d410001c2d107102ca05489108901a0815846250f411031a009040090101e2600c43e514860740041004c030280d6550f4a070081c0074090040f000e9001030715105050f04141c203603a80c6000291059000c0c5116060903038680040742e10301c41e4030544490b40d035401e41c0202030070118002003d00749030245000b0408007181c1604041c41061040d5034400d040e03030303c3e03440541d030720b040032180580641c001d00b42c14001414a14146041c0c44521812203050081d96130390350b20340d48520039011402150206c0c500f00007580204551140610460150060020501d410600f4404450020b485a520349000c910411001d40185c0c0320007113088150b940d0f900c1c02c5880a49264110b215603407000e85007250303c0800300384071810381e254000142d000c1d01082d20380a2410300c544c1c0000c1c24034520b041c0d442d5845c0002407810100d813001103200f03030041e0144c48280f400e030504450074000240c0d240ca0400b41000103e0540c1e1595a5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 826172886 1250 826171636 826171649
    0x3020309040b030f0a0308070206010e090616020f0a0305090901050d1707030924020d0801081e0c03030a080406060504050606090409031103180a05030a030f0c2105220609 75
    0x44a0b818000003070301d0035141c040c0500c0d00b4040e240b0100c00781a40702c01181c1c0728481c60340031031f802a40c0c0c3c0e0140e03400300101210b404e0040d82004001c240c0884c0380b40307034030022010684125901c0b0450710700e41c0303414402800c2e0114045a0300103015015820b1440e91300d0b005140031503040c1d0404004e6140c49244071455440740c03640500029100d820940601c6201000d0080c2e81d100f01e50305949002e04000100020380c02c00702501c20b42a0f1208502c0c4152440c83c180c1d031600c00500315071580c006003000c0b44428500030040e80d0041034120702da19141000a000702c0c619035941c1c040c40d8105800d089044540036004103000d1400c0004100f003a88030403045901204040c0e03400230303a801d00340c02c0840f0074009840c90041c050000251159a1468a03050380c1000a0100c81702c41c9416556820190380703075803c00c801004200310302c40480c101d601031514000f000d401403001c481b0195800038052203c104113104400456404180a20903c055219020007080c071081003014290400c00080c0c0000307031510510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 826174136 1250 826172886 826172891
    0x10b09043c0207060f0603021c030f11071a0712020105090a0809061323012606281a160602030613050a2a0c02010f030603050f010f0f090302030904 65
    0x780881240c55044a10b0241c0000707041111451248004002e0310040c40240e200741d101c800c00040366410204140d500c0740e4942ca0710040c00582c100150ba10786000714003031002c0d01032140005401c410003281005904c140c50207646d5288a03600e0012a10400610907404681c5044104010600c000071944425600075460366210400c450026600380b04e02c034415407084450701c0e00096002d601c44103141e522001c031000d4000b156060801103031000040441c0c4280c00d90b098a06016518600800c0d40d0041e40c09042c104010007881c07000544070b803800d01070198107603480c0d2041050a111980348010300c58140010340c504086500d584810040f04400a0042a40040030030020f0f5a1b05004242c039081c148014001403400e4410f150007020300c1030408041e86d568140c041c440c0f518083c03030f08000141c0c5448014403480960011a100140000e1840905035600000b2010440801810112101d42800421074408006840007075804c002d071199040c0c4d04003188400042d0f008000c1c2d50b1101004d41d0b00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 826175386 1250 826174136 826174241
    0x10f21090602040504181104090b0411030a0206030408090a05060909180f120903010c0905241b010b1201020a020c090901020909070807170103020d030c050c09010b0904 74
    0x10700a208030b03408107034058039060804a1100d5204508800c1c64080d440b64884e102452003804181c0300c903c5802030640d0f41220014000421501c00c01409460180454a483c1466070110b0b0b111b078810b03a03007500c1942c000b10381a0880c2c40c011001c00003602c03044c0c8100d0704024441000c02c0e6003d00280c0400c0014208030300c146060042003008050a00e609421200000b078901c1188542d5444414180d000f03500b0010380100345402014881c04840c2d02074480365510913102d6181503d400030f0403205510b45003c000d00c3d072000c1d804400d496000039032803000145880c800001c2003c01d48140c1c44030041640140420780100e60042000f540003c8107548400e6603540391001d03140213100310401d05600085010501ca43c1e150702001003841404503444000d203800d21001045056402480006e50140c805100080080e00c40c009154005110f041103645020500c4006a0039035001d030030180364403a02050340040f91400f4003e076401000a0101c008005034810350b0451060082c0580f002c2c0504d04044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 826176636 1250 826175386 826175393
    0x20d060b030a2a0b090d03050a030f090c090f0e03042705010305160f030c0b090117041101410c0f0604031106090a02130905010204090b010f2109 64
    0x49140b0290310200310501c00c403d41c00010000120ba0b4444480c80051081c003085540f1000c04030740e40844000c1c02040c4140c90340c0c1d400c44950707021203409800c054030345502e6050b8a506025107001c2d6031043c80c900412900b00108a8112955500c05801c041e082103481c0e10981004011501038900e0105404000038540d0075409400b000002e0f00b48200c0c1c6000000400d00c07802196001c0701d0215428515a041c0c2c0e110f02c944e20b0b0a119000180800d980303010200242c070b65481c01800c4412041c140218048030003520f8071b00119080f502920207940c140f030481c840350f0b8040c4101244420b010000300305840c109469428900c407001d094800380318141203201c560301a200a03503c02d800d0030801c444001155096140d105da40c255411070118180d4402c0a12055011605e80d10551380b42d001040d40c800c00d50200040d020724180da40e405e00c0d50b00e88e90b41001c50001c0c0010300240070301d000c002c03d0010b107040005200081304c1107501c0800011445004001c1518015080d048040e50804a048112400e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 826177886 1250 826176636 826176643
    0xf0c1d0114030a0f050601090f09051504020c01140a1104050907020c0a150207050a06120c20010204031104020309032205040c0206040201030c11030a12021918050d020d060b03 77
    0x2002401d106000c001c00c01c505031140c00031900010750500502c07440e11814010b43d4540345500800c1caa280b1075501c1400400195404550b120f0300040084610725180004542240d1084c103254486035140d5800d102e001134034003c2c1e240c1001ca847d4007002009140071800c2d400d40181e009003489000500c01058030240300300507a0186540041a40001036980c20210445401e003c14a00140c0100003000903189000d0071441d04030b170929100c0101400a6020140082003c0642d650a000c90454049107240700800e02c500c4501c000c1c0001681e4604504044201c0000004224440e81c010001c00c07181910110903581804c140e030807054103200c40c801c0341034484c61042c1c000a0304903181400c4040760941c0010302a02450003030703e003045106520b001c2252403101e00f000f01d280a510411520786402d218801080c141c0c855220014102120403015a268105a10020000442481c0426801c1d03001002c6000184002c036001908081160702103003200401000140040d90384100c0321030241c800f030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 826179136 1250 826177886 826177907
    0x6090604050a080a150c05090d020a18140c040303020a03260c0406080604050609011703040825090b090f090f15070306080105040b0402122802040f0c1d01 68
    0x201a004040c0d2560003032540c80c01001000d44800c804420130116105c074500c50724000c1c031007980e0b40030300d003006074000d10400000140041343c10000c02180061098144414010301d40a800c401080524004038034000204000c1c1603440c403860200300420001e90001240b0030226814100040382c00001900c10f4a030402902d660742c22034007a07108020048010358014800d403440c41c2c4620780951030b12002e12080b070790110713007241d00000a00c00501045000403d15803a103000601168901900c801115050154180403804014050f149481c444a07403140c400011b0481440d04001c901040c27000252140c501a00c0700100c028004041500c1a40901c03c3e9003e44070007104441d0900f41c5520f80f000b41d038030102d4000001034508800400c0030381c0d0600855000d80d400c5100041d0584136034080060b51500318003501d0741c0e407080140d50104000400c410003400369201c0d400c108010080e00611050f2040b06003103001c506e1130904110b200c5234100b4050003000e9107010014104000f030740010380341d0500780c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 826180386 1250 826179136 826179139
    0x40903090609060216260d030c08070305090601030305160c08010603020a1d07031d0d1205090a0b010b09012f01140601080a0b04200403060b010323040f0221010501140f0609060405 79
    0x42c102c000c7c24803901074002d000020b12030740c0d8610701ca5441910441c02c880c0240d50602c1150806401000400e01c00c401500144490f0f050002c6c48c010299508140c01000350f11000c4580d44030041081940380280d0020010718000c44000400005d80c0e0110324404c2c8014908011b0695450702c1c481d17032017001d4807204540b02250044880c144660714000d0141c0c00015454000740c1c2c1410000761803000003080c03040107298020310410040c0d080020a10a58122400040c10000c000c10360f0201c281680008406100c044110f51294210b800d081d5425218030000088407100c004080c0b100781c1c1d900040c00b541c40440304800250110030400081c0182511626501651071103030047c03c1c18135000401807086920031a0100311241002c0300640c1036600e896503e05500841c42510448820a903a10781c1d4402e2203501d80001d0410720350f00080c1e07003400521030f040c185c40c1c00040b0400c2801c1d0911039980540100d00300340d401ca084d91130001c0c0c03490610040c2a0300490001ca4001e24544820040d60041c100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 826181636 1250 826180386 826180393
    0xa110403120507020a03140609160303080c0d110309010b0a030f02010503040219140f0a14120a0f06020a03050612060a0905030d06380403020d050c04090309060906021626 75
    0x9484c07d02d1b510301c25101042a85a0080070081100c00c040011500c9017505007907440c640c101d1454406640382a4014a52041c03400b04100e5201040510f01c074a40c2d07041c6080c04103030388038105501240e0846480c170801900522a034982070010441d0140e4200c0400d40c24070b010340e5070b5510340c40411500d15944d107203030110f02a0342d00049066000039043d12800c0b80203640040d800d2a80b02e0401202e440e4511038032403200b044e003014180301d04283c104840d820000f042150400354055031940206680d11105a5030381d503002c22940c07a9180c0c1030141d1504064102c0e201c514848080d400552140c102800354402195100040c00400a09200ba11140c440c07925080104507507510300b1100f1611040c880c03a03002c40e01e07407814401003c6000f0420b503072500446e5102e0704240c01d66081c0301d1241c00042e000e58941c8540564190965124020410031610903928a00d0300b52500038083c005c074140b03411139019504010301814424000381611800c603000c8203010038020349040b41606074204501b007076400350300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 826182886 1250 826181636 826181639
    0x50c090d03020c011b080d05061203041814102102190f0f0f1e09020a200c1c0303110304060606090e1e0405071d01050301050a110403120507020a 64
    0x42d00400e81d44140f030340a0701e504d022409031030110091501061401401080c003800800c02c40c1d01254001540484060300d45c0c0c030440319603280d0514640065208401080e211500c25041e250140030300784010504d0792601400e81042030072a600500030340900e211010100001c41070300f09915031036840080d005001c105e0340e926a4035000003c2c0300e09016071080b89480050000742558041c104404489000780b03030707400c980e00701984172640c00340400f08918500ba0300400800d0301c5000e480140285805034481c07841c0c24595503036508000800301ca0414241d0008411800c0c0d60320b80d0b000c0d0042c41d65441d640c10000011618080e8020301a010b404003030928044204410040035034050425107c03280c980302915540d400841764540021a0700e0104400d00c0210314480151001403690094450001e907182c0544030000390032120b804401c1000702c814200010005400c00b8811107801032800d00c800d01450f07404c61070346442449148001000d92156081034003a1610400980d03034541da00074640d09086 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 826184136 1250 826182886 826182893
    0xf02150406121109010804030e031002040603021b0d051e0705030301030b1e070f0302030a0f1109120c0a15120c0f180f090b041d0105040516080c04050c090d 69
    0x110514840d000342c2d91810885203ca420480152815010142e590031203a40d035503601207480c42d400c4980d8a4052050b4614481e2141d4940042e10140800c6e9400513100c014034004885034450140500801703822000c100b402d00c50f842821215011462643c01000b071000c0e890030162841900f402800b0342c0800302c004000c110060300c04e5801403107202e090034600c1d590202c045c40c0c0500103503030420100b115003d801120314040d4003e56808882d032000001c8440d0300048803002e9845190a2502d19080090102e20301d1604142d1043d01c0070000c002080c200c10040c0100303403031440368010341607085540301050b19514814039118003807107100f000c188200020b03414007418101840c480d040210b102e09500e4000903803100c5942049036158511038100ca464a410100240000039080782c0194503a079811014011080090b000154103d000040f280b800341022400d010103c4241e011864000e07504100500f0b00060b0703c800c1001c01c1310001210344600d01000c03114400d004250360000c4020144e4000e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 826185386 1250 826184136 826184147
    0x141c12090f0b07030c1709150604090b0103030e04110301080c010e0a080307210c0209070f02212503051804061d0702120a08040b070e09010e010816060c0f02150406 72
    0x2001c02611403450030108070700071b40100e0800701c40302080303a40701901c0300744421003040c4036035040000a0000140b035462606d946170400001d800640215511008107034090030300d1b12940c80c0191100d04841e0031175041c40e01e4140c2b1112103074040c50410806031a8052295030384c02c890801031040c03400701e0b079407940f80703262581c440c054914801c1030a800585950395006e018082185100d17030700074565001c0c0da0b580e01c1d0a072100c04541d200d505c114400c0e02114031907145d812040c2c1c6401d80c0754a01060301da000804031643c03501800c03091000d07040d00716046000065042001d030340c2d17420181090411f5204c00c810108006101a6219a0241400320302c403420303070200340031101d0203090183d0070780c1c52a044a1400c0200e501c580080c010001d540c0350300080c08592207408058000b40785140420403034680d400051049a400e030805800200e50346d004209002042100c880001016011240321a00d401005440c0500031300d80540442d003048240b2045650b5801407001041c00048941c3c2c4494444000804 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 826186636 1250 826185386 826185401
    0x4140702160501080702061305031605060f01060c021003110f040b070614070e0f0607080a18050312250501020c0106470d020304141c12090f0b0703 65
    0x1552100c1c1d040429654450002daa1264005400400300da44600c140e211000d103141e401540c8034002403004942d6612003540e0404050b001c0c400070005410300b802c04d26103852047e4040c0c400e10007003c50360b0340140c90f507a8401e51034a01c2414000303100814464040b4040c41640c0d011074020500040221b100101407010b8030b552030007031070100047c0d01d00404d6181c0700e01081d034908001c0341c8190000780103450581401c4100e001d024019500b403950542e5241c00035001443c2c000c0100d00c07030101d00203032054542d00741e90040404a0041ca40d1448000c4c181b074980c803c985500000340c1104203810380a01440c1b10303143c0300940c00002190765400200020340240790310300410851410f444140d00307281014200102e2080660b10716405040b04241c00061400f08001c0782e1070010405001c4140c18009a102a52141e4025500407440390200c60700d0a003050b403035807a919485600e9078078030350a42d23602544085140d110f00100007070b8502076041001c000300389030300018800c0d84550204030609a168001c0b1a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 826187886 1250 826186636 826186663
    0x8120c04171203012106060608040506070c1a090a0f0506090c15040b0304020102102405013204030b09010213241808060421020705010e0f04140702 65
    0x10058605100c00c0c0c0c0d169002d1142d903a60014003031006001c0c0d03a40c01606010403402d070418001c50344c03645598890940b1600d07070008001c40e6541003000b00b4484d050010356031096480c54000b010050642d9201c0206052004003400744090745d0010305500c0003040781c40c560039089042e4500c100d81a29203a82c0e1594200d40258140c0141030402245081c0911041411180c54041c0341c20305080116100040e00010820780c110f1280c02501030400039540b0482d00700c41034100703890310401405900c021400c0e455921050401541011403c0c40d60140880c5580494101406d451065030b4040028118055500045c04004045007408541001503005111004000011482c210781c3c07400403403081e80c1540070340c01c1603003034440003014054860841d203244440c25a529030300a645401c24586817800c11942190403e41d01415000b176421808a108260b90046c8010081e0906100008041c0c5030100031044c044c040b0000c2000d41c5070303a581c00049042500c542c05e40e0452401d400000d564600801111 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 826189136 1250 826187886 826187909
    0xc020303100b160b04050c13060503061614160c050d0b0a050606190e030c01020703020105070825060f1a0a030602030a0b06130f0509100b0304050703020a0902040302010e0301090f0f08120c04 84
    0x108940723241402200100c5600501405175596050607484814004590b0082001494410043c10040c0000a49422100c80d0611948505145046405041c468001038880c081c5001c0100008985502d140e502001d14100400c1e00e8590002103a070ba40500c000303040c003613110b00b2006d003000c42d0302140101c00500121308951840e039084006a80380c2140c1c0c04060b0001d1070401ca44004552068001c01414001100d109480c51020010500d922a4104100c0b4117940b01c3c04200c81d451528003440c0b8480c1e840c0344081d850020070741e00207200d1a003030744802403599030040005421820540d01c40800d207080500425a5601225641f1a0800c96070084000070f181c00003000c180780c00d003800542d1240d0076019100c1840c9042c803002102c9900020301c100c032148100035000c00140c860024100061070b00310300c0582c0381c60a40c0b0014100000a0a0706c0740039070724100480c404190044a901c0700180c2241800d501c040b03d034101080c07640314201f00b45001007020b0041c4510141c999004108a80070150f08 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 826190386 1250 826189136 826189159
    0x20f07180501090b0f31020403050d0905011e033209030c0307110325150302070f03140f0408060708060f03061b12100602010c020303100b160b04050c 66
    0xa200849031101071690b002a0055000345c15820915028003444512103481206034600700b040040443d4100701d94044581c01007010010448104100345038030b00c030340c18885986414240001d08500a0010800e484001c00000d411482e000f0b40c016000342c2480034450103486a10f01c90200000b0501080484910248000952000d00441541c2c40c001c3c80401546c41c05c007140e00d073303214104040d4000c60390500800740b0f0920740002441950781c00052035111055001d00d00300d6040c0015640191010905004002d40000135a0040780404541c2c0e15007404802c0c4a40000c0e0000c0341d004089040d24580c07400240881c0d0348000184940c413170300241e52803540130b40d1400c041c8440301c407000c9a1a0303010b60144001c182c201c06840045c0c18200c03000b0401030300f4810a07c0d14000f2003041035a000c1d103614001c20050100660a001d840340010042c0015451410000c5d0b40701610103451141c0702800c2d10202d421980e800d10050f080c610300d5004440720880e400e19003041c5444580c481491807141030103158 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 826191636 1250 826190386 826190399
    0x3130e010f0308040308181c111012021318021e070b04021212040f030b0709031e05010609060617060415090f0b031f0c0201180f03020f07180501 64
    0x8405050b240c2c8015550b081c18519981d040e0103400022900b0501d01c0e00c0c2d10070340385a403100d1031200a808440141401040500e0a251381808580c00d041405094030001e90040250001e516503d0f00041c03030001030b5241515203038080b0906182c1c10020342c401c1701140c0014070780c0703268001d00310790080707800c3d003606601c01112000c0451040c03550042c807082c0140e00280251030070090000340d03101200d003944c18895030204454803075800b43d040140450032000081c024407041d10f1407527500218505084461a0941d01e4200012825200c010303400d13400b941901003001029048400141003010040c0545610307035401070101c00100c03410464100888002902500d003038052075001402c240d4400d1900c505196880c805803500c40300c51444180c40d00340e545040c1d01d0811080f02c003a403906954090141c2c2e9055180180c0305801c5140c011a0304045043c4080001e11141c07031440365110400c1002070056107026810042c902da41c54160b40181480024034981580c01825a4100c0d10703c20007181e0f88624 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 826192886 1250 826191636 826191659
    0xa17041e030f0b06010c1e0b0603010c081f0f0f05040c02010b01080a0906020913050619080d0503250e0102151306111620030c010f03020d060803130e01 67
    0x30002d80840003500401d0045202844141c0d040441803400d40c0300506039444006012001c9210388121a03843c2d1404c50030b001c604420b0030380101c0114024084000d450398000c10440d805030654040d1001c080c0c4407c54080e0044465004044039604510f03001c1d62800e1014070f002040c41162702440c00d100306400c50300d2040c4a0210441c0058590200580b82c548280000f0548400c04070b480d1a070800120940f980c45a07ca00c44100091801003503500d4988140501801d91038110b02c038803440d0744410300043e0310103d9114156485071504030303229901c00203420070000c1c2c0b864002c46a0080c82c8c201400240d8440402203150b41c0071780885941001c0300e030084201142c201d031400b90b06440c0140850008940381c00c40d103075608074803400ba81014001200f00ca4040481442110986411040308440c1c1e0381c081414114504100d02070003d0340c0562002800000030140813002301913001407140c1c1d07500469808500a05512012070792581c03013840e03c1c0c40300d8a44c113001c2d102483c0c0d600c4000085000401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 826194136 1250 826192886 826192889
    0x14061806031c1209050d021203010f03080f0f0a0804110307180c030b030f0c01032d091b0308070c0b03100b07210513080105090d08090a17041e 63
    0x18000b0000d1000ca001c040340219000c07580d000070810250030844040d05a40500b0034000e008002034210a007031048068a04100e0014480030000c00b0300042088451070044c400c00c40360440c40240c0da48044154408261142000c0100095004500c400c0d00b641d000303d00611640c800c0c2c40000c0d0f4481024109503881c003032071040126200c1d90710709c2c0c20007041c129041401e08440504010885410f9030780000c0c288606c9901c064841d5020680030065582c3c503025204a001c03200480c04040742c3e49600c206008861001d00040c1262107900301010441140031444020303000001e01001d450b120b01d800e02d4542d003e036205a9640b5181080442ca544881089a026240d40c6649001c09894869482450b8228090544030804109000c9901501c144d800c03910401040c0d8409660b94100c004090b5000c2041d0881c05150703141108000e8003d40c00034842c9960009400d00407420f5460409091600c650708000600c001380300069690910507110240c01500c0c4400b041e80c90a429030100d81c0d2059080703 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 826195386 1250 826194136 826194139
    0x2322050c1f03061e050d050307051e0111040f0504020a120507170604020c0712050109151e0b0307051201021e0a0f1e03090624181505060c1014061806 66
    0x49090400c0070b45440900d100900703204005582c103011032032b15510f0a20520006101d8070340c3c0b079001200c940340020300c52000391000c0b40c454035052a081410b00c805088050040f940115400901d01c41c00e80c1c010910142d86d10078002c001d003d107160030540100420f0044201c051401d002002152551070706009480004129000901056142c04410801c0707820028007503a0310b544e95100c0364003140e050b0701d11601d5090550b2021074040ca0030b20702100c1c82050b0f2401c100c082460700e0180d210079a0040380d140121401190904000300401c980d9600900c0b070002c20380c0d45a02e500d20444911410744000d4088810b240c4c54011108002800595141c0c09503040c0905151409d00d521030401e0007940304111044c02540e0004e080f8100984c141a80d0b41d03080380c10414191206810040c01018061850f512488130400b03100300003e045007000104000e004440c0325060201e4240002001000390217215101c02c6001c0c85807000c3c080110008003800c1d07034030a00400110b40c80c841c0010003000ca26015540 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 826196636 1250 826195386 826195439
    0x152d03050c0919020a090512060f070e06130906060306170a0602160b07090302030609160302040c0519030501090c03020a02030702240a032322050c1f0306 68
    0x10302400b0444103110081a541c0c03450607210705003455030403900c00380018a00300d485541c4050304213010840c1450307402c080f6100e40d034810410071894400856180e90000c1c0b0b40e062003030b110309049000880a024501000d1041c0b0465030b4009804070503600482c0440309942c4040000e191030380e01c1c0d0161030076924200d070216840080080000b6806500500350f107520366080303046201c03190ba1500b1081c0c0c2c0a07910000090181c0c1018000e610782480b42c960015480706c010400441c508a00e01c61010f500e100180c41143c3e10a20070030f05030b01600c00c85d4061120f01860510306500d41c500a0014102801019030407803a0030144000030f4040d200b15040c10286070002c60401a107603080190301c5216102d80208ad411070a410745c03440000001802201c0c0003510f02081300c000c1c0341006503604e0459811010202403010921100b480d07130107515070b0004007058807101c0003000b03804c0031490078000078035a1350880d000c014042202000401c2c200303103a1101340d81c18429a50348030042d40c4007010b61400c40c0941070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 826197886 1250 826196636 826196653
    0xa142110210f030314010303050c0d0f140c0a051f0b010c02010e190510110c0d02010f08090c060301030f050d0305071e0e0402030c070b0717070e0301152d0305 70
    0x210900310b1a641d603482860b01142030722004680381501802a8011004500d0204400b8800c080030302815095220920f407070480c000610400804544001016800310240003c0c0180c0d000014040e6020003a000002c450010000c42140580880e60310910b003041da2405800418961142070075607021038059540e050f848a0204c1044500c00700c1c1d141710340c01d0286540c1c00184545402c0d42d0000b03528480c2d107030760f10719800006030b03141800c4420006a00c41c008507030340400140e80000d0502800c01c03041c5032100d070965512411030f160111010120350310a40102c000020010400d220551003842402582c40100c0c0c5040154296002074036400d01080340d0b604003080b031307103510030350524544031614200800d0105400442d080368020343d41c0b002c40341c01c00541a01400f4020350041d070007a016142400301c8060103c22180c4460000d020b00c0204980c081007004169006d41000c544c0842c0c110b00e0814a07940d40320642d0403440d0300c8102176891400d1521001030716500d2101c40301142c0c1c20601420106 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 826199136 1250 826197886 826197893
    0x515091f02030a020c0d09140906061219060f051002010e0a030e0105070c030b01030605130515100b12090d020a0c0902090114031005030615060a14211021 68
    0xc0d08018410795541d41e003403040c1e411106040001c3c0c40d00e201c6c16183d1841d041e003020102c031030b45820b80c604980120780c40024003005481742011500308403802440101c01c1e446820100480a4220240c014120305004001c02e04d18510840b4400700d170001c0f946801d1240c01c1000590980d8030700d14402c240e40d0040b6820700c010038014001c1a00d40001450180d10300011b507928100ca03c0d4a50300b0030f440810640c0f0041c03080100170b200d41600155215021030602072640e40355030380d40100300a203111202d80710011a00c14840c10305130b407014042080e15591601c98642461408003030499060b4854415400780030308284c00845d001c092036400640d059500da081085642c003070b61117031440b43e0402c110742001d00350a101da02d01440c01000d039038444d000e217a4506000c0500c0c10002508000e41c822203a24044400c1c0c0d103500c11146080c0207801c0c00c48400c0394105019105024031340030380109221390b41c801d01602c0c0c003940d41c0c24810310300700c0b0b030915081d510b030400000030034503280280801e4080c000f0b002c40030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 826200386 1250 826199136 826199141
    0x308070506073b04021306030f0c0503010509010909150903021b090112020d080903030403140d17130201030605060a030903020f0c0603040b090727050604291801030515091f 76
    0x1004e40f026260105d205c60310b071540740844d4401000242e680c0c140f2107459115016000510380caa00d8682c0c119418000000c3c180e01040c4502e041080e0b4890444040000305841122004116041000b01c951235003406911003071942c50b400716292000c90540614540862041e05075403c181c0c070000340c0841a42800350920501000b51007940c801d02c4030f5401d950f403c200030300c050f61040d144880c1151411f80d6a9140c403100d68208018800109041c02041c0c80300c86035070f54040044405030a174040c46000603001006260050381d00b0001c0001e031108030719096004000400d20903800c40760301c525850801d41e2211304c6d00c840c003030b0700105c100042008514a80e0105411070103c50540c1d84050b82c0f80640721103400c0000e2a11010884004035420154551040d181d0003007007540c081c480d10408500c20030301031002c032a81d910351012510380d40a40e03032503102c4035544007001d424021030703070b56113a00b46540d07110b601440c100e503420f041b0f1000562101e4080b80000c9059121717105c070a1055003521103c0003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 826201636 1250 826200386 826200497
    0x30305040b090117040c051801140d0305073207150f090b04230301053304090b011406182412160e0f19030807050607 52
    0x1000780ca80320704040303c681440b002d8003a40c07250060600a0b4940300512113540540c0c040c00610311050001008072051100300850582801c03544903480c03100c5864291553b000e2400080c058400f142a030342c000303000d40f0101e03c0050910304aa8a0a1464500e140b903589410b4080c071400f0203403007640c1550140c06142c130800016002d041c03198402d034603406c3d00c110700c2c0c000c3c1d40581c0401210074407083c1c0741c013800301210303413802015070090186207859010201c002c20703d8042c180148051004200442140483c598001030008005104002c490f080100d6881401e002d554041c151081300c003000c0b8901501107800c1040f0f280c85251002c9403c100300400361550b80240c4d140d04444144030007500b190380004026461111200c0480343c1840411000c0040c0036a4650060000340d12210b22507035940514041c503d103003183c80c40c0e441105e0f0207284880e00180d41c00200780c1c40307010035440200708001c500c1a210b0700040da00e8a54904001d11300903c6140c3e94515010b00721030984082507110118084200d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 826202886 1250 826201636 826201639
    0x142a041701060509040f1b1202010804050c041113050a1d071b0302101518021c150603140415020304051507021609060807051011010204090501031a01030305040b09 72
    0x40c15655440c04104607020445c2d0864540045624950800c034020226590780c010f01070350081380e13908080510307a142e0416040641881030003c000390401608012a00032000c015009202051291030041c80c2c5410410350144511020304021078142000c4405000f1204807001d00400c0711a003486c1400c0c880c0c40030b001c08040000340244082a104807662149a4a21980c01000268140c5e814881261560011000c040e0350f200000c00c54007075100c00002e54111900c00040c0d4901c465072040c03c5c85134580c1d060103003441c1010b0300c60615421203441c01017280c0749034905100e026100322085040d61801c80e0010003c955841101c1c8075040c0d1a805581e01520840031602c61034a00000046400c00849104005070b000000c084141620702c1840c0000b00700d1001c05201c0c440c106581c0da9180e40d402c0c00b51303a000d160009170410003113209403003040d88505040000c40d600c685603a07550020301400d00054451210504d080e10034404150880760480341c150755843d0034542014542d03002d41d0700040489 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 826204136 1250 826202886 826202891
    0x1104030521301905060a06080c18100c0b0f160c060b04111b030304020607020f01020307080c010b043e0724050c12040b0a020d142a041701 61
    0x10b20300c0e441003802140921455070107000c410b403002a030070003900e9004200034000c1d00c05220400416801210864001d10328084030f54540880f503481e00d1415580a01c0c0d42d5000900b40d411040168000c035a410400f03015809058199035035500801c0800c1003600e2084402ca988052380112a1280305200100761151030041281e480b02c00020f02511075481c0004004800042c8480d0b02c0c1c2511a02040341400c1e01010750300311301d00358000480c0d0740030300c44019000d4050803054148170ba10900403248074550010020ba00d0b40710803171416000f400c018001a010702e00d0080c00d00600351003100c0c1d95000c1004100382c0c0300741031103e40a042e90110418100c2402c040240011400552030b00c0c20746180403418895a45078a15040c2e42c20155003000c0c000c200c600304100034042840720707824801588190407840700c4c0306130b032207840ca000c009200d45038031104014542280d91140f42d0229202074054640b00e0b21041c40da01450366001c3c2c04409400300e4941c440c1040208006560a442d40d8000710304148000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 826205386 1250 826204136 826204207
    0x30c230a110105160e1005030118090203120702190b0a0e0a09020c150a0509030726070f170a0509040b0604050411041a0306010f0c05101104030521 65
    0x10300b940c07010369000d030480034428203074804558171140c0071900d100b040322021003816502d140a421880107010302d21800001942100891180390490544a580901102d80f149020f01917403c0903004201c08900c1070680300350008120ba01d440c0d44100740d03200a5510707407401e80c0010042e210050804041c42c1c10501d03d590026030040588064241451024054101ea8103c58210400e030000241443c4100c0d1510f801d001c02c684c000015100d5440d800001074543d0400d840360000c5509c1018039962040000055100401c400a81c03105520307403080141400b96040f07465039a94501a04003034100142082c45040c585103019040038603901d401811447c6015290b070080384c01d0b6242c1a0a0b100395483c0081c0420684404024820711a0900f68881c1e003141030510000f00802d0344009000b080080140b17455050110920a004668000c41c2c8208445100c5581300303207854006100540d068007892191005980c901201440324030307401103940c1e1500700c3d071ba6066a11112640a2401d01e04646d80340e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 826206636 1250 826205386 826205417
    0x10206150d111f0809010c0f1805090109021818061c0203010e0f071203050703030b22051501032a020f070f03120e010f05030916090903030c230a 64
    0x700440810720843e0540281034800c101400c4968003504c502281da14090001c43d126a2240c4000000ea2051400003409083c2a692001c1b5400e01d03080140d120150800000b1031240c6540140b41003d211081149500c00e000d08202c0c2c84540c00020844041c0781c10000b6155280030100d1040074100c80d50103d0b2070011a80120b4211030036011709040c40d41c03242440005143c0d00b008440000d10702d883c0942d83d42c08407964010300c2c0d40140310004003496212041007105030b0fa084500d01141600940300640400d61031280301c05000182c40040825070406625442c81d44603000c3ca01c100c0380f901010003000b8180c0d0040745840501e05c0d44901c00c50142640b00741c0021418807a0303100500d8544160105c403070860411403c2a0300381c42c011418032105c021440002e90300f04511000011203410640e072030383e480030181c40c240b030214010819412461000820700c0745640d4401141c407406a074042000002c00481561152110703030903242c100200510200d070380030050300103081481d01407030132004d8941580b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 826207886 1250 826206636 826206649
    0x8030f030105030106050904030c030305130f050c01031523040b090907030c0605042412090813090504150507021c021509010621050a0f0309030c05010206150d11 71
    0x81509055000020041141c1e140034003070b0b04042c05084500c11040d05250343c2c090700f5049040401810306894500091040040e10200c4a0391a0400740090700b41890340360180d1244548042940031900d07101c15003414500100150003a40c40107040d2101590070031400c0141c24002001c20ba50154030350520420988178205424000c5042400904082d41149170110501d0580d070444d0003004010f020810036002c255115003e1040000c40c400c840903070000c070864038007503402c5d034000384141403009000400042c58002e042008003400d03461442038640144d06d050341c1e400d0302d01030720400100040b550810300680c000c50b08036034980110ba030170101c9003860b41c2c552850141100017681002803030140e1510140c0d00c0d1580441c185d4000c01c030b005e08240c1a405c0b000340c0d845e5030b5540c0318003040c000713030410804024000c8038070380040884014021500d0024107104140c0005c4802082c080000546540002041030042d9041031a54205a40b0b04003845205880801c0648544000c00000c945984828 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 826209136 1250 826207886 826207897
    0x4050a0207020d0516080312010501211506120b030601030b0c041505041d10140102070b0417070803030f0601080402030a0f03111605060313080d060f1a0703140d02040803 75
    0x10800f0b00105e02110620001c10303607240d440485a130708104911408070f00c1e241240350540d00c00b42840301c0401c03180c1e503107014924903803441c0006e241c1c40d00041c6d02041e0300d60460a4200c3e6141d82e252803040050701c0d9a07009950303c10503850b805a011300e0040c00007a040e50340c00e6611912051a1030f04081d92a11020040451750300c000010a1000409110600100c5d5406a050940940c0080e15041c2080c1e0441c070303034895102d12101c51000b00c42460081e8401e00c0001c0040504001c3c1d0380e112611030b072a40c21181c4035410340b591a0710402c0000280900c010003924414180710343d400d0460b40e642d40055036080c80086c000c03603140c0240f0440d44001901c98400c004c1d8a4003aa448214184001042070700e0040e07103400380344050040c007004128a544610450317500c66040303009000e03040f4440c50702000303030701529510008150600c0f0000c10214030100004e070885102502194003100d0552221826100307014019000858002902d195081c049000301200b40300c49400601c0c190750b5000c01400c58208 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 826210386 1250 826209136 826209143
    0x1a1f050f160629130c020a020405182a0114210103020103050c07050c0607030201020c060f09060a05070e040c050d1401080c010203030c031f17010212090c0a030204050a0207020d 78
    0x19007184410340c203e058140300034480c1c04580550580160000108025030364500740d080d1980312072000210b103100340000111254090300500450504011020050f40d00030306500052085c13001d18140442a000414510348000760141402d145e1440119031130321607030203240c960000030008510f1002d098004007001241d5000000065411403000500b40c83d0090000ca450080502180020074000b24181e280c419040711000c1e5181d841e4507042c1d0281c042c2c015145024000d01d0200400b00c541104205e11803919002510400c1c0c5d590003c14084840949807040042e184145003110b50070164485074911245040c1282803111485181d002c0e503810540300c84207a0210300040003454000c0010445002e0309001031415031030500403041c61804000c0103c01242a100d10020780c44405000d480c02a007214034510a010451080c134a010350700a925002205101c040022200c40c404034440000c080d0043c0301b00c0b80189160204005003402a14503003156600708508030050b40d5031036600804911 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 826211636 1250 826210386 826210391
    0x50f04030303051f0f0915030f0f15140c160c08011a150f160b0a02070b090606010206180102090d1a0108010603080409050901140403031a1f050f1606 66
    0xe004184c4080054100403010702190b000c2c00521a104221070110140e4510301000140c88418122120005907154000b8040c07003025000d084c10702c01e0008804070344500580c1c4054082c10302190900444030070420407141074032400c01090100e005c0b1801030040d011243c640c06003004058031020b21144103503001941d60b80d0740300601c0100314030703e240042400000300c0300304d40c0101c0c581004200d00c0c451041d4000300c900001400c5c0740103810030366904001e143c000180c440c04d8030b0300049000c02580401002c3d11010100340000b0b442c03010000f460f80c442c25042e40600381c980c980034203034807050b00d0340d00c0c05858654081c44002c046071508150055510f02070340041000c009110f03014110b0040680001001c0e074140b40041c07010494402c100c030100c460b03141c800a10f96440084031030040201155002084040350240b01c285545500080d40504180c55204145030408080024080c0031411282074595103400409909024070040e04032b0701500d4041a1404600b00a1091030011801d412202e10380e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 826212886 1250 826211636 826211641
    0x605190309150c0809120304050303010603090215180f030c011d0406120b0609105a0f05090f04020a0803030f190207051b0a0f03060203090f010c1e050f0403030305 72
    0x6404008407042c80d452005c80e1441e40c2049e0303c8060300d91205010350000e168503101c21000315213a0020020002d2112111162540d9609a007804920300703400ba058810384808440f02014074020401075801c00b016103e0300c0d05403003016000d40c1c80903400c81e0400e900075954640091500d4102c2e00089005201e0503004030030380340c14810071000346c00280c100595a583c03300188420790b4524004052380f41a03608451107000c1c080c1c4c03403560505e0035000d14680c60512101c50510f2600384941d03191000c031096881a00291900b804800e00d000c0c0713218403640b050880011602c00c50790601c0302604075002601d081c1d82d00e80c6410f0f60760301d16842542d40000c980c030744d90100000d580301854503d10b0360750250429850802d540e12172075a034900c04d26003282038080103890042595900002d510041103241c10002182d60b4900785034000307420407154090940201114003007500d2040c45840a03c508276114059014020b10301c04803038640020145080c00801c00050201e4a07008001e00002c40c866540840c0c9031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 826214136 1250 826212886 826212901
    0x12070e07020712110406180c02010c050a0c0f022407060c020607120f0f0f0608010e0c150a03090204020f040305010e0c150c0709240605190309150c08 66
    0x24100a2101045402119061003500d0074a02200c1140341c01c240152072421041d80020024100d9520400c0030904624140c0751815584c1c0041070050341030f80082000411040041d83e6034441c28840c2e00004140c030b071042000036556984249040d0001d41a03c5040d01c0344290140748800020b07510022610126900702004954040c4500c2d403010341c4040c100714204110003409161081302001c00b0940c03039110018408910342d000c2c0e5045d010541d02400344240c040c2101004022600a680165090221001100e0703c0003584d841c0c4004007901c00070840d8040b1134034507410f40250841d40c08142c0c58028910241c1ea80d4009060304845c8142c1e1241c1e62442e52600360b08440c0541c42600043c4c11009412540713139a0b81c140c00d0151590101c6a50b0342d0740c1c031404024141000d0ba04110086450a22110514801003002c0c06404e40700c58014003d960322014192081d00032103034150b0500141c04107004107a0720903003010028500c14a80030322108100015541a103005800030f4001401d00b10401944 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 826215386 1250 826214136 826214159
    0x1b0f0a020c060d2903060f220b100602030315060a09030602071b14130506041808040e0c0c03070303090807140607090501050f04170a020d0501020a0201151508151207 73
    0x1404480c8862003c0088910040b980303c0200401044191540400041071980500200d481409005408d004101c03103501d484040c1c030800b992038070401c18480c0300c041803050001045034024400110312015000040c020001207501c028418001c000d5a0000007001580a0018258203403003041c05018a40442011503064030300d0b80d01c01d4861040c4001244035a0700da500007080c10320b600290200d583d54031100450094001d0440080344103034104124418403040c0303030183c0241c511f90764900c0711a0300c404d000b411300c070b0007840301c103004a8008000280009000c0c1d0705c40c0040c188600c1a181c00d0503000c9e1602030324a221007400250940250302040200755101c0c078040c01600d800d080c854108841d07502e00d00458000c1d4010110b4000c2d801b04420440b40c0d0402c1001f2605500800e011ba85848524215010390800300441e0003546c00c10340b1364002a503040c0f0701d140658442ca0b41c0c50116505128048860841c040c000811648203c0e4201c0011740700c0128040108099200409080d4640003c00e2079 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 826216636 1250 826215386 826215431
    0x6060406080118020f2b140a11040f0305030c010b01080f0c2503030218010318230a030f0207052d2202120606090d080a050d021b061b0f0a020c060d 65
    0xc6c030b107000c04003813207030050386000d03500030a1529000909004004107012184075a40110b540c2000b4000000308020000009015006c0f850000703021030315035100107544840e02a51141000354543c00000d000e0b107541406041c480c4406450f0400a00359010307011003501c0c40a405900082d000100e491f081c95451000360118042131804200006180180c1036217154144d500a2051481c0b100f41c3c08140307070654004100039034100680d20714090620303015011424250255000d4010b00400044500d40319449c54007030307010840006005a80c4c0408503070b110401550042c2c0c400c90070443e5080d40e003040d030044005043c030a036005035507941c0000d0181440380010b10081c0705003000c110005c101c0d15600400c50350203520011854a0308000001a10305015140004101c0b6202042d103c04503d401286c425082261400b615000e40302ea040c8103006140d84407101d070301500200003280340c1c405100e0003031040364070500c1514001201040012050360106850780d003440c6d01e41d40400024107c5119104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 826217886 1250 826216636 826216717
    0xd030201091e050607090807231e030f06070c060b120a0303050a0b0306060a09020901051e1e07050a140c03070801050108011b0801031211030a0c0b06060406080118020f 74
    0x40c961f868042129070350714060045c00841414500d020101a80320755807441390ba08000c0a8003001c0141c08021089020b400c9801c521134030465104104d00400031a80074010001039407000010005910748402401f03040c00d21340d400c0901e84101d4a500d074000d03c00c05010a01ca9600487e0301d05240c1139107415200319604143c440c4e0401024800740b541d820089204a51003c00b0140e00c076601140141d5080c0542a03298400c0461481078851a0359400020964202c016039140a9119601c0400b082402181c0b0001c11070390208900e440414440184010711042100840c2c0020701c000d0f002ca410102d441e07000342c4084e034640c0c006110b500b0303080c050034441d16941a0f982c424044100300080041206110141001241281d20500184035a080811205007541101e40d58502e13114002c110072205841501d6010f442c0011503542d29050302280c1c00c4815554941c10141d003442104000668000716101101364200320540030182c10320040c06d0f44280b803022600d40785d60b1210b8020650851004c654 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 826219136 1250 826217886 826217897
    0xb0717010911070b04060b030d031e0504080904050c0904090534060831030f090b0a140c06091605010216061b02040e0a0309050d050c0d030201091e050607 68
    0x202c1c950b0004141c0c0c049513002605154a03407a9400e100b00245000d41460790140214105c041c001a05a0820390085581011500c00c0c80b1101010b9000c0300c0701036030010040c0d041040152030618043d003150b0342240c120641c2c1444c12440e080040c0454046410844440d0000703c50322504641c58003513014207100300e2001c0407030449240c1045440b1005c60040e40207001c110030214080200a00404601c594200311004040030b510b2007051501402801c00c40009284180c14a4064070a01b000e608843d84170100a05010f03141030255200b1894242c200340461040c450000703502010001580141281380103000120041003140710705d00f29507008070b815076120030003060141d20b910400c0c0040382d032503190030510541c5420794000074420200d00a540241002148a807171100403d24400c0c2511075150301c1c21413076480060260002070188064215000100c101c4800d080c2529044001d41c4a480001003414496654003650041c1904189804000d4510081001810480319800035003d0418 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 826220386 1250 826219136 826219151
    0x1b0e030c0607030e09041704030303090618030909022d030103140a080301030311150705090a05030a0818130c09030209091507050a03060b0c1b060f030f10030b07170109 74
    0x182003580c280808074005c500040015050150008480d60b0070300001c00c240da6196940d0400038082c0c9440c3c030042d550306181022400c1032454450145840c16450f48540001d1841c046515000350040302071714845c00b2480d8580700007055480700c085040d07a40c6200381a180d5041d42080359a4501e540035456107503200680070300c0481c10800c00e1701d0460360b240c034103180348000303101d04c0c54101440f02860800800c200d4017806041740c1c020b0043c088010082d20401140707a0b803601010303a120000e0700c01078a819800c01c41d007544250314044424070a4000f40c8101404120001003030205e80110f681880000c800c060107008614100250b01c0e0801600d800515034403080124945100a0180c024414040000f5900f02c005020b81c00000040c02251900c4d1745a01b2001401c90b00c40c4140500c0250700070102120388480d00c0e24509942d14080c00d420100d05641d249241c01c1c84284c4003800c010304141410b1000000204809199489030a05130749684041e802c000008a01b0f00301038100c50051410441c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 826221636 1250 826220386 826220393
    0xf0506060a0c021e040e010b031b24070c29091e03010e030408010617011103180118060c080a020903030a2007060504031202060708191b0e030c0607 65
    0xc81c401ca40e901100d14041300a045413041c421100c120495a8100b410441001141c0a066100b9003500700c00381c0a03200d07107194284080b0040d4400408181d44424400c581440c140f2050700c0c0d015600d94040616403402d4120b454900c0c40010f00d0b84030752903800c0c0c1030400483c1c40c445408c8061400011411103801d12205030000341c0c07208003420200c54181c0c40c1540e050384a070340c01d40103003510120007400c0d0303039580c0c1e06c0300106406440c05026010603841c2040c070142c0121720502c5206203541e141003009003151a598686420f252901d07404207059900c1d8148056000341c400403014800e031280340700065440c11840042c010a50042c030752424184180899030044d14003004603800141c251a104107030203040c1d100c0b50b90154007011010010b115140002c100ba5803c04010010749001e00c0390b1152411103078500301d0340c40004407002c1e00000c0450000c101c404402c0c655080f41c2c3ca145100200b00340559942e409250000c07150f0036400225008440c406c941404c0c040c1450b403003015100e403031410300c503600e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 826222886 1250 826221636 826221647
    0x305092817030c040501080406060b04080c09010b03060108071d030105010b0306010e030d0221070c080706140306031203190c050405040c0c0206071704180c0305070f08041b180f0506060a 82
    0x105d450f051103040380024040017199030100c0043c090740e421440d1150703200d0f070400380e44010007144503000c1c02c0341c03000210700c9802902c166445650169250070071a52040c004a1305481003d0090404a0021142c0c1426030346c2800b816028266144045489240c030320001030044e000c070030000340250003207010103000d240d01041e10355551a880341002140c0504010a00b024815541c02030b05071480b0100110320b0203c00700c8d0910441d80d156840240c8100080e42a4401e4841501e0f0540d040d440440480c0303c00c0c584201440e404165240ca0700041100c0d9082d40c4250f91b0207942400015000080510551a01c0d1050103480d140510b40008120407903070208803e840f80c2c0c980600901c180b80c0c00c4150000c0303070000f01c4000e0520aa40c1c440c03040c1c00481c2c41c50280038001e0184002c281018001060f19100e2032400f00503664594078503106031200c1e164801499810106d0080364604414082814000e0b140c903004203005401000507425034080001c0219003010f82014071407a401c000d0b06035900c1e4000e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 826224136 1250 826222886 826222889
    0x50f0a1208011502060c0903100f0501080106050a230f0d0b0105030d0302071703041b090501030605150f12010b04090f05010e0106081e030d0501030f11031c0305092817030c04 77
    0xe0f10711b146d0b14020000000d2404a4140955001d075040110780060074209410690484031104d0080c00401e40f28010040d2041d1503000390001461900d6000814159940c095081c6040c00341a200500620b4000b15a084544400030b84045001900401c46070234100710080c0031103001c5c070701141800080d40e25960300700380701b1083c1c41d250900803010a0070720442c1c8080086040150942284180d80d070385080e1b024050034842a1005840d000000da0b8462500c141407654620042850040c00580b104001c60700781c2d101c1c0300c190344d036584d1007035900191194412440550b02441c0c501448a0032441c000c2c0c00c1d1150400911381d1a410704101f040038180004001d1140d02c102411140100d02080d402e510b18003e5041d462002800d140c000014040001d6a0380910380c090250141c0a1100c001850b59030300c0c240c040d200c102a00520607001d060f01c01d0788140e40001e208404e031800198801483c04002000324018000703581b8545200303081220180f840002c08110007841400c42ca0440d50650300c0d4041c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 826225386 1250 826224136 826224151
    0xb0402090606160f02060c011b1d2d060a0e03010f0204140d24060501120e0303180a120e03060a0504050705040903021f1a0904020d020607050f0a120801150206 70
    0x2084c001199a00310a88007080944030082158402c1c041501607000b210440550200d00420b00004844c12460946c100c1c20324003030000300400c108001403003030a1440c68180795040071010304440c0c0507600d02005101032049a6142d284550817401010b003100c507060800f840300e600c10003003000180c100000780d000c0340500719000346d007418042c288040540800d40d0100b181e040c12240342c10740310300680d10520507100203981e140c84070348106082c041203408844c50200c60794018400541d600501e04443c0c0c03c8050040c094413034000399035071030b0b4118282420b40000480c01c03030400a140381c20100401584500000e80600c020308003501da0a032940c1c51030040502a9407168901c4060600800032850146003c081c8420b030024100c080400402c001c04120080040e15031601e805481c00c43c0ea240d006a0300284840e06e039920139030800205502580c001c40312801903617146c010082060140c865203034003072004100351840b640002028040160000400306014041c041c0c1401d60024003d07a000c0754 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 826226636 1250 826225386 826225403
    0x209010905040510232a0a09050604030602030105190b030c0310030212060612070803030c0a0e0a0303030f0f0c0e0910050a0b13050103060605180d0f0b040209060616 73
    0x2614101503041a03a0403008001003170074400c040824050f2407440f007515001c282c4104500e602e824600c850081850020421003259080d1008560070700d40008040d400d510b03040c10034506980f200454415040741c2d2082d5000b65000c00104100c0c2001d20304000207001c842c8906081c18107000020b513803408083c01014518802000050004425030807500141d6002407002070340c1700030380103030640d11039049a500b8010070042211a060380b000281c081c00b0b4600c0e03500a1030443d41c540e06074440d980c210792094410402445050780381c03519081702580245000e5a004030340c43d52840b41403420740700c141da41c401860f86448121502e482e80400360000c40d03c0d044620710310703c3d204c19442506015407508030652080180d207001074141c0d8110300516152100c0c02c10f2a0360540e8500064040ba240d82c400c03100410030801035004840f2588040720440c503401003440d031014160380c4030200c03014030342541150313071500080030310042d0310348911125440320f02100c015140810f00e070003260404d90008801440c281 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 826227886 1250 826226636 826226641
    0xc10050d0b0103200c0c0913020105030618011509140109090509010b1c0b1e070f02030c19050610030c2304050c030f07050909040809040e010e070609050108040209010905 75
    0x20722075080b030040d0380148001d9001040a804103088541d00c8664445020b109810581b4118104442481d10540c60000044605800da40041d50254002401035a000c8900c0da6980103030882c800740d45000c0d041000d0300311007540c5842c0f0b0103400c40c40103800a4462000c5480300da0500c0c1c2c0c0c40202c03401580d280f100c010a441e00c0d51035144d409001000400303540070050701840b0030744401800c1e0003038015018545000341d0b13817602925040206886403084400c04001000140d000380120380d85011b0400c0342c070440c2d240c502940c0649040c142610030b212080540100614240042002919080440c241c03499045500e0760351800c461100c540b050f580151200541404680b103005c040101402002e081404580303416040b001160f0300403920701c503500c0c4104010814041c465416203131244405070620500d61100d4a42080da83c06c01215654031546495410003154001c1c0540b1500031031100003814450b05000c805815040c0c1a000701c0d0402107050300b0400503039a40d0075400e04652030200001100d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 826229136 1250 826227886 826227889
    0x10c020103090b01030b07090e24131e0f050709090e010e0316020913081c1d0f1c020a0f02010302090a0f0302010e1804030e0a180e0c10050d0b 63
    0x4020b0004058181c0c0007020000040c02a510b1341144650b20907a110b02c074a03034640d0307010310502c90107441c804040b14904005090224840854010207000200501c1d005a504640b5805a0710015101a02c045026003076600d84c1c103041c0101e41090484650a0000d440c08884c000d06c1e0510742d104100000d61140d40101d660802075001c0e40d2821a010166503551042c0d100d19a00c041441c0c808a020700030003000110030140c5400c1950810b40e10000582c07030201128024504d10b14003080d258811503030b0f20b0511170304109040344040010007023005448600004510030f41008080a01948032000306a2524010795012801c1194141d00080341e20301c0505c90700049000b0300031141c480d600030300f842c00040f4086410000b90000c40f4402d80e64018064164800d201c110800100901c0f555100c0001041c0080d002d12003501c082100603103001a00c55881083c10428410300c803115400c90b40d19a09181e101805000c0c01c0c200300019128082c020040040c0200f01f449241045000e00c0c0d0b8a242c0706285 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 826230386 1250 826229136 826229141
    0xf02090d050102090906010e010804260d09151e0207050102210402041a032a060f0c190f080a0309050618010b030c0a23030109140c01030618020703021e1501120809010c020103 77
    0xc0703180510036a450701e400602c9003004080111041e05c007900102950301d3f01440c1409120080024500b080714a250502e1a04002c1d421030102260995001d000c4c1c2d1418800b144040b80044594400c1803a89061070700500080b01d2520311135280c0300e82c9440d00380006490003e40e07103541c100c230100759100c0c9410105255096041c0c08403000da203c500007541242e1501c000002d0b00d0a610180b041e2002c580c18109009a6500620f20080008005100300b0001c100340e2000740180460a08001c44c07042c00039500e45041c61002c9900c1c4405403551280320028002c02d20a002107020280c00400c0b0740d61071040080d80700c04151041042c1d50651005003030300c2c107100c00c032003100a8002400074068448103141041e40045080c9980c2030512030000c241483d58400e000b140112602a0748810345481d00f000301201940c450751040d019446290300880310000c049500220340ea401502178820312520318007103500b482040e0b2054010407111041f507170102c0c8504040312001c20003424030b032202c5213091005030f01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 826231636 1250 826230386 826230443
    0x30b03070b030709080607021009050118081e091318170a11030a0c03030b011803050703020109061d0f0a05130e010c02010e060402040f02090d050102090906010e010804 74
    0x2058060604002010465600654000c985a4a4940305142c882044030341c3c0344421240c4d00016440100707131111007205a807040c50018003400012408513070f07840c47c2c02c0324041a008221000d040000704544104d20b0003003c15141890000d14514040c0350f0000140c503201046103d508840d0b5989141119208061280021035405003a058800c1c9007030414141c070703400a0500c0c2020490040c0301c08034404012040342d8208640303488108803102c49480c203e0091940807034031814060105c1e111082c64100224000c0294443d200030802241141b00040c6100b02c0e5600082c24424011106203102c3c1042103203035441d40003610b0f07100c0c00102d0440020b400c03265582c030440e00140c10300100f950080464001141c0d004c4444001e101d88920201e04900300c0319800c065400c1900410301040062078240c0222400343d194680250414448400192504518001c01c4980380c2d40013941c04840e0425440c07080d401f0009090500b0b02410340c0c0700107880c500380248020410603030458189915107203031341c0810 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 826232886 1250 826231636 826231639
    0x151107060513052e110c100f0f18081c080105010801180603140f0d0f200a020411120105090606030a020a0c05010f0e163f031d1906050901030b 63
    0x81c901c60380444c06808480445020700d940e00451210a100741000c180c41142c0c07515a40d550448009114000c440b00c202c128512001c000360366005641520f204910303903001d4000351b80078008a101c5040100090b41945d03001e00700788500309004001d04ea030004100707811140025289140d00074400c101d88024481d40d000213240036420740c00f0046400740098843c0c980c40c59441155020340e1182001d0303500b6044211f401000840034611041018600c82e40e04120700f4881003103c049000c0c6a001406440001000465800300440c90480441f01a41524010b100564100541e804d100c8045442440b0050015008076000a8a4111648655100d03030781d15400c14001c0040200718090300d03005d840d09a10035546441901c036807510b4001c82031480011910401d458604071414000b88045490111807a092003150001d003030507400300f41209802e00d05110f950380d45c0c05104104800c5565000c001c42003805912400d0380c845491400d80045000da41c15070130000d403a981a040100d0243c040030520f10b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 826234136 1250 826232886 826232959
    0x30c0804030b010e090d020c030d030c0c080c06100603050106020a02060703200106080c0f1807020a0501051005130911090a0603230111070c1e15110706051305 70
    0x19200f803e656020340100403020903981101c000c101300702e07501d2230300c4d024295040d00521040c2c1407590080d0f0200108800130300b041c203035044050701d4260250700070000c4810290082070400c886035142856000240c00c11b42010440f550520200070b40d40c884c0e1000c02405420001101301c2414000e03d400c00440d140301082c038258080c2512103074083c00c03070380c03040c52801c0c452070050441c98030304140302e0990520080c102141e40091501400d2a01402400c10300070b60060000180100300203005040c410380b0311880802c06070303103403106007c80c0c83d400c5c0740043d18203032420481c040010554200c56207641001c032031602080d103850071090014074250b40003d1400308a01007841140d05400d540300c0340403901e40002c00c2a0410701e00412111f12a240c00207164400b0003005011417401c50060034465250142c014122070348911110908108142050012030401049501c102d4401c10060b4090711507031038500e040920342a00c90f07401c103206000d039601c00c3c0c1c03c40c5002e00100d011070302c3d40ea41004110301c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 826235386 1250 826234136 826234139
    0x80703020408030d090506060d0314031e0a0510050d1a0a0b060706240305151e041b1a43030e0303030121050c3c030604030c0804030b01 60
    0x841c00141100314086800d8003c001c001005498001c0100d4a0190583c8a929080b03c10b06041c07803070780d07000034070200303504dc81c20240c10300d0405583c0c003036440342201100020703460500001c0d07441940710a501035442558030310a010005002d501c15203140102002d00c140303458072001c1003140a011000f11803900f290000c98021300b402100e400450a02c409100d421034102125044141e20f4181c0d400050078030f80c401c0b0200c1110b84850401ca0b03078000030a00784d4101c0c120345110340b42038528082d5820b90709070105042200840c890701c04c20f83c00812131183e91001000b950035148001d40221494030300b280007040784d020f41e1814014210400790480c80602c040710211103003001c02e2610414010380008094040349546414004102d906940f0004405640919003480540c081001e06c2011a000d0050301101540c9444402c146411003076020050401c0d0a0001003e1013034205655100f1101c0030b400f4000d54660714042030343c0303800c540c151401d403180c2c000d5801c1c6035009100b5940004c110010b40c500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 826236636 1250 826235386 826235407
    0x1e09040c03051606090b0408070b030910020f0d050601030c0806010e010210022107050913090f02092a0403110f060c120304060c031b08060a030503280801060f08070302040803 77
    0x244802130b200c66803140d4540e180c07203002410702400b4034000c1c2c001c0360344010400c1c04201d040c3c10186a1100650041743e2441e801040b400c001e0760401546080d40f450040381310842440fa40c040c031544110203180401100c0c0783c1c807000070710140c00a451141030010325107003088107900c24410b901d081003a480095642e040040c000c2c03400c0b00005041548100c00741008180030740c0c402e0341220341e907604c018492070341c140302000160020010050b0846035840c42e022140d00680b50003951911803480e03030300720b09c0e000b100800c014085180002c2c032000f0070120030001880000d10b5004508540301007035070140055080b2070003048007480345d1440d621140c41801c1d41180d000200200543c07103544120070070b108a100c0c00600341c00382e555954482e8200004030b050a81010700c580c040e1940410001c0c64051420303078980b1440e00315030280d480f0701017000d1802c5910001282e0004410030703858aa20741a0505d41c58400d0060060701041d20000401180e0b01c0480d001501c80c0c1c058401610b0b1070340c280d0360340300ca04c81c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 826237886 1250 826236636 826236673
    0x181224070c0218011508070914040204051c0b010b09030304171f1a01090311100e04020a090f0510020a03030e1c08070210050c0702060d1103070507111e09040c0305 72
    0x30600007480d948145c0112580d00c5881e103103026121701d4489500d45410720010b0400c002c2c00d09001908180d00b400000f5a580e43c2103a160741900126021040c02c2217141082c901c0041c058000044c80c0c0707010059841e080e100081120304a600284501405c104404099410002c440754900d207500c000c400c20081034001c5901544400312402a05451080340c00300559000d43c8900c00a0554483c0f800f0360310280c18040e100d01c1850842d464a181c0155071131000400300d8000a1007580040c0309070390b050000b02400f24000c0e0141004803014030325410304070402581e64428031801020140c540050340b12100e400c000c55040040010700301d00d0341348810040180b4000c0d003240c0180040c81b0340d81c0609006691803044a004400c3d84203468035040c819000e10081d54089a000c904c0c00c0d640d01c400108540f15503000d5405002c5a030380d925030301e81043c1000404001014480c5d8482c005800340b1191498507200d8503c80c4101c10384e501c0029640c1c90030070038400f2640354000b41990240d02809004030308241e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 826239136 1250 826237886 826237889
    0x412080c0f16141906020d020c0d020307060c15020d140f0103021c1406090c0a0b1303030305091608030319090b01030303020c12181224070c021801 65
    0x30300c00c4a1641c4400c5211581c1c1d1112a4a00c0c40c9401625400f07001c84294001400d02001c2c1c0074240d00d811650400306207441c000d042e4080030050700034100f02488035070b060082614500040301c002c00303105503a80000352034030300c03d1003034400b031101da215408104550141c0c20007035200c1e03802c5c04544031b80443c0d2a81001c1c0c40340020031100040c2e01300008000081ca800c100d4162030300a4480c9020150700320031400d50644084c01070703840384c40a001941682100b04001032003039541034003a0101c42528800d201d0f01c4070301c40d005080c81000a100c406500303444210402c0c2180e406140c0402c42d41c0380d00f01003505204c9424034011b68010540c801044080d0004001c50090b00c640900d41050080394000300100d601c1c0020045c640450300e80104003280c4244c016000600744202a03c10f581c1240115415a50002107850105a031180c1040507914041d0030415912035034802500d5480c0c05801c000e442c600e8410244004c040310380e80810b165034803a00d09100c00d29030150180824004a81c0750481c0c0301402d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 826240386 1250 826239136 826239157
    0x2a07030c0312030c050c060121022e170703110904022a1f090302030c0601080607030f020a020c010f031e0e160b0a0e010e06030a05160e180c041208 65
    0x20811010055031040c8116250446c00380050202c903401c018410b0300051814081201d080b0b180c0f4107100c05a80c94140d4510312507401d00c03441c01070001c2d142081c040140d501e1203440078051800300380910aa03a00d0601ca9110740c0501d17000640082c540102d111600a404125411520105040c1e02c0000f1a018034120051030b1040c644250010071103d540d5100d11105003403005807905041c0c001c0340015080004514864011f503170814210b9080b0514004099101c411113074007007020300202c9601480f4070f120000940109510b0001440b6000c4d40d02c40c0f0700d07901141004035104221052501c070351705c546219601c0c00c0e4440c000807003c7ca805000383c06250410070240c0644140703501c042c2c0b41000710204444e00c1c00001800c0c6201032000b9a0031140301e41d1000d06018120031103100319515107000b144110410840010a402c00c0840d00c1c40c0030500d01030311428481d19852041d4543e03101031156641a03000d45204016035074903a005291401103901501085060801c600e00f001158005803401280 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 826241636 1250 826240386 826240391
    0xe1e0403140403052d03040302010813050604030903031214040f05070308160309051f05030a0207060f05041a0c03191d01020705060a0507081503030c1506152a07030c031203 76
    0x445c640b107440d0180c10394100c1c0070541c002c2100704015406424110342c03203590710013150740030001c540b202414424211030440002d00c401d2424004c241e00190001605100d4403000c02c280c0b24005004401c01001400281032542d44010340ea0401104000c504050750b44100100d0b00d8003030b4260b1480800403440000c41c085480d0078000b18150406030304082c645180010440b034014014241503441e9030001c4c281c0505282c003084510302181d294081c4221520b200c490000d01480c2504000c5a40803080c003020200341c0001c81800f800c40c0e04403040d642c100304a07410221034050522882801441442648030111001c207d040058a10660180030507902079000d44103242d031000001000c0f14022030303040022035001d0340031800301d03601c004200b404000c0140480f485c241c0098801d620707100700440c101d500c411030b03d0104205400d10050000b440105a0007113410325401c640c000b000c09001d00b421030381e00c0b80180c0c42c1401c2c6a20400c2544002c3d60490503030042c8540701e04064500100440c40f100110f030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 826242886 1250 826241636 826241683
    0xf0e070f0b030c030604110d0e0c010e0f03070603050601031401030f0b1608131a0406060311010c05330718153f0212010e1e040314040305 61
    0x14801c204491180e0030340c1d5070f601e1841e5204410070004080c2491040340303020301130100c8080d0316214410f9241018510340101140e0361840001000c9040d6514414001d0084001130852600c0009041e030a40380340c0d060100b080c1d43c2e036000413001045240710403e0b000c80810000824802801c20244080d8044c0050100c59690031215010448000c00401d0000d83d16400044541040303d40d0360b01124814001411081c40c071042e00410401d050f1000d480c219511281002000820a078100b6509802c1c2004c50584001e0b8071051b480b098186000c10300701d45810044c0b544041c805441814403450000412303080e04101600824400e00a60000c04000c1c0c41034000c1080f54440d18411981202965a8020000103204a03110a5404030590034181035403c040c62100d0790b0070400e0b43c10f00c200c8000040e2100c1c01e03980c12564010041e404041028054800d012508001c2d03001c009007030500e0503c40d407035030300d0b41d140482c2c650305508019080c058004c5004400c001e0045140c2c02466003000030f42241c41e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 826244136 1250 826242886 826242899
    0x510080f0a020d1e1d060708090a1a2a161103010c05030a060801200d06171f050606030402100516060504110114030a0e070f06020a050d030203040b0402010c02040f0e070f 75
    0xa58104002100c00d1b0711440c00158118414100e80782c1c07003001402a03802021803503440003200825100c030152002101400c102c11350055803405009080100710094600c003418002941c20b2094001400b0465181d1170440c0510080c11481445c160707000d8000c01c0b2403524840d00415940007640c201d51001e04004c0c0029a8990500a00350681029465110001890f8030f114506622000844203a9030b00d0360303000202801d0b5000c0d06111f0034031120181c40c0c511004010840b003940c880b080c05000328076181c10f01005807910b5017030340d9100d0380c190bc0000c2d940d0110442962503004092030030b0044540b00f00b8440400503a600401c0c010340c400d080018141c0400d40064644c4a41d0750f4041c0b4a40c4001d1000800140707081c0c00070601c01002c5001e40f190307161104039100c0c000741c0b00d0f040b140242e0b001c16481e4041200c1040300f58201d40152404500b5800c01d95941e9a1005000d48003074100084d02c9051806d6640310307800340c82c10805c40702003009410440140c19440d84520701c685030004040b0400016207 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 826245386 1250 826244136 826244171
    0x2b0b0912030604050402130c02060108010c14030106031e0c0306090c1d09060f0d140d18062f0c0f2205040804030c080c03070510080f0a020d1e 63
    0x25003004124003030071a503400c014840280001001680c0c840010020340304840030520903403d0038411386c1e010300660360400c403110342500c0070703c100d400401c640b040c0c1c4401e507113200c503090301c0c1540c40c14500030403040b4080c480076000c0b89851503400e5145d460b0032030341700182c1d4042d40181e0440e41c010000348401c80d80e8072001e07203080c0c10090000c0140000414030454500d0880811a030007000103100200b624400070100b150149a4a003c9411146e10032040911100400180307a000c6036501d080010815070b1104902400d440b8410749083c4113170814690383d008103a8001d0800e410481529048104101030b0b29035580700d01e003c40320b002e081102000e0005044c1102d0360201200a03015800340d2032080c41456009100003071043c3d80d522401c0c040030001401c1058040001d102c800d00610a010040c4100b40c1171159a503c41440341c00214140002c0300e402c180c00e03990003054680303503426507910742414101070b10910107403061061801e12040010820903190103000d0042c402c0c100911040024003186 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 826246636 1250 826245386 826245403
    0xe0f01020c010b0904020f12120705031210030203070b0703090e040302010c0305090c0a1a070503030907030606120210081302100c0c231012051005120a031d2b0b09 72
    0x4100e109039844800e1801c14000b02014030901c442250549e04000340b003004580c11005c4d0885494000052407500303c2d030500e884a41102d00840c0c10404a85542d0003c5ea403071300148144140c40801041d000141070041803c0c50040c16512500e00262a092400034024598a8038040c04030b0326080209091590002d02840944005415001c5590604c0340e40450040c100480b01500841003040340300041007031001d5070142d100c402c02132400f242185440c2c0306640d001d07040707000c4504103440c4c1c00b8050f03901d076001c201d648501c5040c004250f4940c0640c41c0350b000145003001c1d4100e00009034036208603500c2140150424000c42a95014544960390703040e29203100d0103000209030080103031824a1600da0080030110b401820840402c1360f41841c800140c5404481d005a62413176a0f134100090700f0407a28202ca0608020040d0514440355603010b0600c08008208070000220240c008480d42c90741101d141200e90720f07a1014001200941c481a000360142c801141c03120282030200c0e24440740000c1541 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 826247886 1250 826246636 826246639
    0x406200906090316030b011706090a020603040f0c0612180807020402130317040612090b0a0e0f0106030b101d1306090f05010501031101050705120d0e0f01020c010b090402 75
    0x20314000180d8204400c40d00800c00e5030b503050143c1211200009600c00480c0c000354407502c001e03e220340c90804a102e1840381281204a650400000c00142200c0400c40e04105a41110050b132a5195810071040007121104018100c80b000030f030110302250000b8400c6c0b560f8a00f610140710006180013000b40354100724500038240b9405110080c01807801c0e401800e0074440c44500001c555540b5100c0c211032540b00c001401403688000790500090360700858002c00d1090ba1300040c44020f9040d038035001401402454464440e54480340039001b004e0510103110880c880c00b0080c001c083c0c80781400039654030700703841810034654505400070f610030700040000d41444000c0b0b00c0c00040d03500e0600350041740350030203c21030b075482e42c80c2030001c0020065070007600c030b05001b40c0001416604500e4801e0101d02c8104103907050181c28805400007880000e50030301054801112140c641c8900c0640c5006040503040d004942d002c2c084015000c448154058219040d0032030090003500848401d010f8000b4060390045d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 826249136 1250 826247886 826247951
    0x1a010c050c0603090c0616022403041b0b0f031e04030c110a170c010e040204180b03010216030215071d010818060a06440a06140406 58
    0xa120310b02e0110060340e80000f14078161040f41050300001942079104071071030580c81c007030f0720144030940c148aa0305440c0c814010840c030700f194040d103191900a0000400c01405506000c2c520040700e8004041c101c0149401041551641841042c110341500100d5424501421107141d07082c0440c401c00c411801560943c4499660315856150783d511004224002600400c0c043ca001a0844841c86038048a414003c080c2020030030202c0010700180304054607038030850062005210840100c2c03142a2012500c0200086003500e10700800c0c064010315070000411901c0600c0754041c15004902c40310514400c2510442c65614204183d84c0441403803004250361824090402e100d502469003d80c000c45210f120f40b028002140c1e40074507004040710940186034581d04c0801ca800c0615510240100320b501c81e20143d103036019496002c50209004480d4466494a140140c030390301440750f042800d400241c10700c01034061580664000000355411105ca83c40c007409070103034500344042c00e000b002c04000d00c2c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 826250386 1250 826249136 826249153
    0xb0d020a1211061e0c0f030a050703030e0a021c020406030215040602210304030807051612181211120706030b09070804050c010503090f010518010c08012d050301020d1a010c05 77
    0x1340009422071103404240e80315000600103000300400152400c00c882e070383c030b00b0f07691956440e004054412060b402040c90b4400300a20005944160a50803c08018640d80080c0e814900028000e0300d00340d8000ba40010080619001804958005005aaa0303680888210505400909815411315030505c00700304010f0020500082c0f00d8103505801c0041031400c0740c100549803080107096004100d00b180c1d0010300f0f0400e090031035000740e02ca4003624031403038030710403058a030110860160b404580300518038210354249000543e1110380701d084a440d070b0011185030fa52034080250050400345001c0c0d205500c1c00c000109a6841542d516108590140251900102090040da0603400c0a82504054003a400360440c02c0b040900c60b0b10f20811401c0065403040d0410300c1c0150848451428440401150200610003c8c05401c00d00f50b4226100046150290740d919000a250005410441d41940005112201e255031500b000c8103207020071018440008002d0010f44100d600c40310010860742180d0325 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 826251636 1250 826250386 826250437
    0x60518070816050f0c06040c14010c0605180f01020a090f05100e210a0210080f0f0703060f260309010219061404050307060522060b0d020a121106 64
    0x403203482c5035520b03041c414100044014074000d20f8012084d40d124640c0400c0400c410300c84c11101040c020105a00d0103100c0101b524002007800b40d60340c3e4040c3c1055240c8011a025007580106e1054050426058034640c407503942165002c2d500c041c1d0100c000448840340402c1d03200ba0716a840c0200d58004141091440181d841500c4c0301040c0060141e000308200c48000100045040103001101c050007c3c0140e4080c0348104010046410385040c02c00010354100889055509a45600712580ca5281e078072a070385081c400c90146c402a000f02100ca4491180010212a0f04441243c1c02c40141d080402100040e0803450b40c0b400340018a50040c1d20660041070004050b000314401140109004512a201b000c03200c2c11248090701d0031203090340b0004114050244500c2100d40101c0b491040c4444000c02a1030745c9054588104068115913070340707101c0b02503941c4400c030380783c1c1c003035030142038035030655580d0386080308032407a503002602d140c182901c00340c0d0b440c5044421100c400f041c80d494005032901444 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 826252886 1250 826251636 826251661
    0x20303040e04330c030609020d02070204061d0117031614011a1c15060b0a110604030f0f0215010f05030d02030c0d080408120a0c111b1002100f0605180708 68
    0xf540c030a050b80c5090101f4011014001010840001c44015070b64043c0d0384180001ca030001d074001c40d6901800760a0301661004c100c51141112018111040707803c9004582038114851005094034242d8000d40d984104a09600c560079004042002000301e130000c030190b0203000500b100b502d50300419800401c002c0b840c0e181d420040c0180144a18260114184800d4084a1080d08114054800825890303802d81d40180b103043d8003140ca4000d0442d07070605503006400c40051200304010b2003e51281c0c0c00c40c0901c00c00c0b084111aa12145004065035a4008404c402c082800f5444c02401400b47c030640042c000412100c285250800034000410041e008440c0440003070000c885200e07080007041101030700103000601520f180c000000c1c0e0100400b0b809030500000c1648c441d485c1d000203240a8590700d13003540d04100404142d4401040c002100b104030f00340600b42d00d0390311869140c002d060f40c00c40001d5000380241d403c252880780010f00440304400041c1011240440020440ea0016810480030b4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 826254136 1250 826252886 826252901
    0x7150c0201060803131415030406090201030207080d05150102070303021b0d08030c18120c040c020102040f0f0510020106050a120f0213050f010b0901120b0a03020303040e0433 77
    0x1032000040642c0c54420850455024150031100a200d80c0400d2028140d00440c1c0c4079900811210090032080d03c1e4003044650000900107810107680719821003e40e40a6011a03610952004404c1e523141196081940241802c1e0342c00118413080c00e0f88510194000038401050702c0c1c044e0010030300c0003180140b02c0000d410001d46190040d07940304d2100d0000d8902800f8600070a00c04040c00d0721980f150003000310400a003040140b24810201002802600101d0440e800000a440c049a901101601a80079220359441f148010215420021b803400c80020b0703050648508441d035150580f034940d4201d0907a03196000f030380e40c07005281e4001c01c0b00307100c1c02e00e000342c1c03c03071084000d610640c1c503540002c8c0b2a54143d450b50341c03c40740c0700d4040040040410a40d1409400c160b0980f5040000440000b0240000d4250100090344e841000541035030362030502c3c500650b4000c04030383d5180d07241c890429800030191400c031505441c42000e40c0d0300006460341c2d45148105060311380203034281d0883d804040d02d0407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 826255386 1250 826254136 826254161
    0x606031f110316092114150103050f0c030c0f0108132405060f2110050a05090d03090809240301150f0c08070b270304181103010515040e07180b0715 65
    0x51f008041e4040401c00c42c103500030b43c00382029218440e02d5264070303810040202c2d0864440e400400104685607074444850000b140c0078a04040710341c1c0c031404203d030104003806008d04054030f5030481030490202c5100144108441120601c11919402c09200760044549104c035444000c401904400101200c0800032680c624030131218010070084080e002c65800351020740307400383c80f8801c00107006001c00140711144014501000601342030b8039001c034079004584e9918440c031085072280105c000740c1d100c3e001ca055000c9803090f03681d503544c01c1031240004642e12004041a40c0d9458031715540c1c002c1150004885c1c02100c480e14159181d0303544070060500816641180c1a000141c40d075540010040c0b200030047c0f18020343e82c403030074038038850140340002c08800c81c00303410880c000d8100207088081d00e044482c19a10801141b040344543c1c82c8034040c64000700002403e00e42000400369200e6480040d19400c0e0384030800030b0b911114820000d00c540c03003014110101d02040001251816400316031a581e2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 826256636 1250 826255386 826255393
    0x90402161a010e070206151e04150501030506090f010b030402060c01090b070201061505040312050f0711090a0608030a110f100218030606031f110316092114 69
    0x141d64140d01074036601e08101c500e0100c40014003560100c0e00507242c00c20264002000507203809070030000790280915040d80100305051641d0031184584560314502d81001340180007002c080c11050110045038483d040c00a400c046c0801e02d5810070428840c0540160800d2580d541e003810050881a40013400483c0c1000701080070040000c800c2c42600400da2081540c0c0c492400c25150090a5440350b40100f011414128006102c4035040300441d012298070486c2d100c600744c110315059610703004000940c869050000740390400c000000300000e088103070840d80d03001d154895524200413906a4001c001d40f80c0c0c01049100c2842e40207084036080b80360480101c0d05114206038080e401c02d01c40f402d45100c041d8000c5585000d49a26100301c8908000680041c9402e00e4604002503803040845e00c215269004000450400112904102c5c1d001c4251950181d5074144015003100122112148400082d255000400c41100060542d07442c00004071007586996031a85601d1803005865405040e03d10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 826257886 1250 826256636 826256677
    0x9080a0f05071712060102061e06030a0b010e01031202061b0919090903020f0d050301050d1e0c06020f070b0414040f0f0902010f0f021b01211b030e03090402 69
    0xf0400340d680c01c943d10800e18240d484020041801c030449801070f2a040c10b540003030040150f8850781840d004030685c12601c18415940755040402d040406181000c0c01c2e0509030b80c00845c3c09080903035018100c903c2003080000c0074903491401c9842d08070684005100d0300c600711111120109140162600d44002402041e5800c10001c0c260b110703254940c80745a0407a250104502819018849100c0900c0b400d0040c02980c294600002e050f44014050181b151039481401020700910380c06e00000d1010405140c2e51130a200c2c1410381022040b0701c030305c1c0300502c6012541c01c0751030000316044086400a925950a007810200000b0001e503000080c25041960b078482c00800c3d013007501130054410310001000801d9141c9000040c03402000f81054414441901d040c60306050740040c00b821a00d60710307441400240200d0f00100d030540040c008001b0b00c00b2040d40c102c00d00d0301195000240d034403a59140300307401c4140048103406481c1075071110b0f600c0f50814040040a03040c5a0001d18810400104404004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 826258992 1106 826257886 826257893
    0x603020a0504031e140c0a060e03010905012301050616020f0d0f0b10080c0a05060c0a080c0309040b010e0603150a0504020a03020d0f09080a0f0507 65
    0x1a400980940020701c1038090350069940410002c0d1540b950042260784003840b114141ea44002e42022010b05200005e0444515107025044141c2c2d945440c4d41601c000b000c076140f0a0f015522171000760006042841140d030201040c650090240e001019403003620b401c160086c5000d003c0802c650300c0103000c010170b010b4003a60304075455220400d440340400c0304140070b244018116040c03202d000041112030000326204424181556000c2503a442040359a040c40400f0240c00c40182501406681044401801041001c42c101c03a807141907582c41c0210780d0700c070f24003541c210340008c5076030b0103c0c0c5014064031401040910f05541403a405400003000f510024003445040c521503003401c11140c9441450b6030040c035008104541343c84480001801a51041d240c003038140d843d054800300045517600c40c3c5130070280c01149940c200384c040c10066810803407c04e03040301400814410103001 = true := by decide +kernel

theorem cover : BRFrame.Cov 826079136 826258992 := by
  have h0 := BRFrame.cov_init 826079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 826079136 ≤ n) (h2 : n < 826258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
