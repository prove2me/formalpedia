-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2939
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:11:27.923905+00:00
-- url     : https://prove2.me/submissions/7a9896fa-8f24-4f75-ae43-4730766fddea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 528417266 ≤ n < 528597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 528418516 1250 528417266 528417269
    0x30c060c091a0708040b03040f0507170a060b01020c0a030804080c0303090d0803070521090f1204061803060e0f0c041109130f110d050c040e16030609140702160807 72
    0x50b903030030000d40301c01445444000c5070017401030300b01d14176a030381064900007944240c50b40c0140c420b07005100c070101e004800250344511420341c0b20002e144c08080d94851500502c4808116815403007010025072140c3c8511040302c00071070060000035101c524041c0c120741401e83d610318141c801d0b08100001c0b0784607507842d0080c5c0100741e00000c1113900c0e80d0340c00c6015900380c4a11502c060003051400202042c100800354014855000101030b00d188c0301c00d404105568103100002d1400b0404144030901c492481803a11104080c06101a001040d58907281c990889450702c621503444d41218003280d440130010461b2031803240c0155010080703240d418612004a00600c40a0b42c856076039040d034941003050070340101c1c010081c081d43c100445035202d2024555a8090f902c03000d049400c1500066032200d032241660700302c03098044030942507501e48240c2d1904140c101740e40c10505a803590003007001506481035a544030100f103405000c5003080380c0040e01c0c01c06484498040f0591501c0c0a00031000081110310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 528419766 1250 528418516 528418559
    0x6030d080f070201020405031615020706051903060306020c0f070b0c0709051503010c0504080c0603010f0303050a110d0216080303101a090d050c0a0509040c050d0f02030a030c060c09 80
    0x501d40e00d90b8801240a4440d542c8050b03414400c540c49111101071024018040740c2e280402007100c069202001c1c0e07200c0003503110b00e0340030500078021814402c0c04081c0e8490050400d00d800107000b0348079603d0380c04070b8110b0440c02c80c00d13074003c1c01d40040c07000d8200081e81c0601001c2c4155400c00f410007107061798032600c0740114800c0544030f001066600c201c81c0480c019422008009201082101034001c2c41c1d6005842002064401c10b1120203043c240001264181c0308804110b490f52402c6840964403984022400c4041290410702e00b00d4031a41030203120f00310503040e0f0150010840245120211400ca070300302c02102d400070818040c1416082c07100c0340c00c480b1030f240040da50020340c01c200d2090740605004203030414203c503101c404021001ca069140d40604461140d0300300d840d5024000c2146044400504c00300026806100038a8000e01018041e441600589503400e0341d81d02081c01c09150890480c081041c05220800300540340c007500c8444c80403883c2070380c0060f00d089140803408c40401d1107070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 528421016 1250 528419766 528419791
    0x180d0f030f1106091b0a030c0b180a03050102030109050c03060f01032408070f0f0b0a0c0c030c09050402010206070329040603052d01051e09070906140906030d08 71
    0x8095107030145810b10a4a0403090030795890340380140030386443d1180c10860240d0307109a0751010a03207107000961030095a030861241d949203030078803170075101e00e5102102400411500100030700c2559200c40000c1c01442c440e000158683d454699100113603a0040d1411282e8101032040200301e880d40c50071140e0b045424a0013007120801c0f0510080d13200c0e44500e0710542030780c0c902004180d60200040718002c40d0120220b920b80030390f80d44000303139000015014241444608101c5140d4007803045070300c2c0401a00801e01803120541d640d84101c011841030b40031040a54070303041004117560f014070041d0351040050409008041d042c500141014400140242401c04100459500350711168003000103194000c0440d07034204148961220f400210130480a04d811030040746881e10758040c041c550150304030980080002c40103002c11005150024503800051003014000111351110303000761002030095515158051401000b48100440010102c0f03000c1d40c0080c0804a1107544103030101e0740304a411104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 528422266 1250 528421016 528421037
    0x901050708071a07090f1401170703021603090e1005090109020f070b0a05010315060e15031915110708070602160c0e06090702010c02071a0904050408180d0f03 70
    0xf52004002040d200c61249002e40104804c0f290000d48901c15191286000c4454690f585401100d9081d8660a140018503584682038204000c2111b150042107034180942420240300001c1144103110340e0503000200341c60030411074170b60000040c0350080350b40280110741c28204004501d2036076040c495295144d5001800c20301d01000413003601c40469000c0b01e42c0403107040089504015007000e0009580400118501c0030050f180c0e032241a04880b4504103080c01a6a40c100444001d0301d540d2980d901400345082a140d000c02c0c50003107000b054402d2121010b01201c1100c030340c04680c0c402d075249050800030450040031400340010340f049143d0110015940301c001c00250a03606803102001000d04d05001c101150142c00e81d51b03181d208000a69090720955a641003c81c01e0b0707054240e03800d01607048184107000059044000050b11030b80303081c43c0d61804070343c00040b8040707402c03c44050720120b9000c9818064a2020041c0103005802152624040070041e03c038480540c40f407000003020720003035a00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 528423516 1250 528422266 528422273
    0xb1c0b09100501180b07140d0f08040303090201110105160e040b01020309061e16050c0405010e06092e1401030506090a02130b1801031d0307031d0607030c0b0c090105070807 76
    0x5881e000743c191000d0a58580c0c6c0c8914049104c0e00d10030081005600a440c15000c400748190789046881d8403d85c0e07407004907140c0d61030650042808000030303810451070002e501c411034030034042c450155406c400d10341c003a0000700000600210303000e01c0d9240b09605000440c6441e03a800010740780781d514100c804960b038084421039503011546c400303001041b81c0408607046074131900b08801c41d03000c1800707101910081e0744050100412200c00340030311801c06070306034003182d0035003030128407158010145600030401c2411091900001c200351681100c00240642050264252600309000411401e090500080c1804000101000030042c0010021580881c244a640f005890318500600388030404554645103240e01d46491218070103070700d01003800c01c00300e00c412601c0003851540040c081809141048030301d6808443d181c1c0f10300c01080d5104d610000c05c01c4d01c1c0d6201001040d40900c2901c1c1e0316800303281460b1980c031140000741514410744040c024814a641c000781110b0081c2e9200702d046954008030f18 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 528424766 1250 528423516 528423557
    0x501020a0611162d2001140313020111011413030e04020a031a1801050f06040509150a0b04060906051c05180f030c030906070c0b1c0b09100501 63
    0x40f51106448181c0303408091100e01070f400c0c00c03105519905106007240c0304030950783c0c1584885000708400700e0250f0010404103491240c45041c1c0051402c81c22a6401640001042d0016100303104d1001c03d241104046680081140041c01c03090320080c090458500c1580e0182c11005006248001814074401d041512070700030f5220f44080103004646071186000001c3c010214000421984481400d4070006440d08074020142503105643c5c91026a00306403e0200e220301150307800d81c10030400d106c0030455a5a01140c036210f004030440512410610702d0801c00c01c41215441800001400c00c070600a9582c00f60183c025180c050926654903040c0c508089110b4064004494031503281030103020b103484a85100d00d50b080d0700c41040300c000a11105040361030744688440741425520030856503159081680190440d0340c021402c2d000d003555a038100d0310b0194820414041502c0803410406140c1c0c0d05403181009403801515002c185240515003108054051300800e41401504000c0b00701c00d407080d2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 528426016 1250 528424766 528424777
    0x10b13090812070e01080108011515030e0102040b030f061002190309090e0105150609090a050c0f0a181203051b070b04080f0111031e1504091a100501020a0611 70
    0x5054000e6503d400300008084441410003540064041e0b80001607280050040d035804802c1e07403c04543c9545842400761018854601a109050725101c40f0400200c0c00e01c051720041c107001d21802c0d0b992400d02c540b440c1c4014000d020a100c0d8002018810050b0f600082d000f10100e500c054441c0c0012103418141c818018942c087e210721410300000030f10b00001034005900601d20000c0c44001d0303116100400c03040b0b00480d045660001501e00014441c5410390300904d8204900c12405413408903c00b50100c0749500c224846408912212a0381008845030030b00302c001810a1921040600206d580c010b10354403c0c100d007414001603401911181c51014000c41d0300030f10485110070350300e5613a886116210310038032032400b00551030003003080c5034a00c6040450344a0742034100e10b10159080800448a0040040d080362000c02810001c0651521035102d40d0701d801c0e0040101d04840104180079503000c0e1001041008640d107400341c01c01c801d0341c0002c2c035094829031007c408155000d0000c5040014040c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 528427266 1250 528426016 528426037
    0x311010c020913050705042007061d0303150a0308091908010e0d11060105100507060207061401080d031424030303040f1703010311270a020a0f02010b130908 69
    0x100b0082c001c3d19800400c16950842c0f04800340c442043d65481040201d5000c120210a0f0001000881c0603070010070004205451107000006500c07079503801021405607400018101690000051242c40c905d565501e04004c0c00440e00074030b41c2429035441c2c03282c03030203102d0100340145540c103800c00341c0c0489004a0700142001e84020400440340090080d42c40c468140401c0c04036823601d40780124084041106030580310042c01410518489141c100c4030740d07225020544007141d0a010040024500780103504000d400c00810b003003a075040c0442c0e00c3c00c200786145440c00b458501403007082c8040d901c94813543d209d5001a01c4208090b801301e807402c1c0110820000980c0742c0000810007081200c03018088001d02d001e1600c902030301d83d144841d0703c0d4510081c0805450501c40d4601003d803481c0010155048820145118190000842c540c0d50f44803000c0e00c6c000c903080d030080703062200d13540d001110340380f422410301c000d000b0f9080c0c03000801d800302540c00c1d10318250754a8403000c0091021410464085114 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 528428516 1250 528427266 528427279
    0x5010e061b010c0f020703200310050702010504150c0c140f060a1d07080304091e0c020a02041a0f04180206280c030206070f090f080a060b0117010311010c02 69
    0x303226420b00030240c1010040114107011141e6401901c00540a000d681c0c1c010584003505841400c0080080000728405070705105d043c04d402401c0d115401114041c1c8c005400101d5603040600c0c0c9611292900880880d071907191401e0f0144403a80450300b281d619400420b61000008003030b04450500380c80183c01116032003010306108485010b680000c2e0404c2000644200041c1e00d8040307107031900c01a210701e00c902c4d44188414010410a50b000380500910f80c01200c40550040c4640d10642c1c0f4500100401b40c1c0110406c1800d508050041403a01da4503551042c58481000b000965035060802c40507000b246d56000000019000d00c0380d0451543d0000c1030907454038039008003a07030b0030030114411000e03140c040302c07200d00414010040e803030b200d907815000f9107644d075a000301c00c0318803595050801e002c0040c0290005047c0741142e140f0000b6040e9900900144405420503406852034000a1410060346a508206003400c2d00d6601d819268412510b15001428400403100141c0c0300002a41c81030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 528429766 1250 528428516 528428557
    0xd030201061e03150e1f06050a030b06010305010b031b22030f110a05011202090f061c15030302150c070218040311060c190507080f040602060108070b0405010e06 71
    0x218841042044910a440c20f041c00558403882c00290f80081700301d01d02c10741c81030407058a82030a00444541c1c030784294000080080d030b10800141321326015402a18200d140d81d06100300703540d0600603a4050402c0f294041d1650801c44886213034030b4181c0d103114000c3d044c0441c0b1464843c0014601d03501215480c000901030fa9120f044c0700c070062111080444d00b111050051000074102200383d0703070031140c050b1170740711401d004202d003400a503001d550f03000d600485d2040100410780e1058041c012a0304010001080c120b03528031410111454091001410280c0c4101000003d41c002006208a4400300c05507900f5111034034005090f001f09600254894048000019404d00c1c021038688150700980d103050f1006c0c2c055011940b24001512001e441c81020800c2502c0e100c441c0380403003424000741c50319600d00407440e100e210a5400040c0d01e03640110380000e0030401240d04001e40750240c1900400380c1001f92510300148980c1c4540c1c41294103100c800d80414061b5610101a01c91000d082d031039144195 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 528431016 1250 528429766 528429809
    0x40209070c020112061e0e06031911032d0114010524030c0d0b060306011d01091a03070e090c22081903030c260612030d140a1a0d03020106 61
    0x1d4488041c403440006c40242d00081c000301c071042290140001030040e210217140d104868922802103941a01c00ca078006600050a842c100908000080c2d2504445039905039240710350900300501d20b0340300d00c581c10025044000f549840c1e003141103c0c0111170100964110450040ca000c000018940708900040100100c00c1960001400040c541c0b0300200001c654030f400304510f030300080d980c00780010742407020702e001009404030b0021032141c141800410280c2c0e540401503590001176101c0b07800f22012003030003a01c0e034008074807081c0705200325041c944918102c008294180502c02581c03000312042c00c0741090118208108801070107050003601e03500380802c058040c40d54045002100081e107040558602140300380c5180000034507950110400d040c40640100304c2c10005800c1e13a5001d61802284149140104014550015000e03808907036010a594032548001000f0040c0d2041070514401c0f215014800704811106c00044541c105080943d00b022030041c21507400c01a00d9041070030740844207 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 528432266 1250 528431016 528431039
    0x1603091703061005032511070303090302100e1503101d15030d05040308250b0106091202010c06090309030b090309030c040c05070b0a090203060a060518040209070c02011206 76
    0x703a02c1c161045000744140746002c850f20701c030450300c20382c0b1404804018071480c1c0c0784410540031141645014104a060001828241092684200c000c1a02d000d0204118200345040d84207441080c00c1104c41070201c18040b92030403c01d41110444401d0003c005035203803070202036a80103890f891074003044105084100f6129007000f95013142e802c0c4000c071002e2100345000074403600200d2a079a138640c140303071030343e52480c060303810800d0001700a8561808541030640068460791505009001d0324034194908400540083c42c04d070000052120401004000b50f6082000d0a5034540e1003000010a0800ca013811650002c0503000102a00c102809010380d41d0b4002003d8080000118141c40d9503000802c1040b04503502403031000081182440000c0204918408046c0e00484c1d6283c003080c0740b4290390003e03051901c1141e0710304409a0701d040601190610303601c0c5c44403640303e140030b4241909194000841004e8020074100070801c4801e4a00216441080380d140d007104c1a940a111154560010341d26 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 528433516 1250 528432266 528432271
    0x100c05010f05070503090f0c100c0809090403050405010f08010b030c030405010b100306060e1207060e030f03040608040b01050d02030a0206030a02090d0c030302121c0515120d080604090305031603091703 89
    0x221441071f0120b80031b1070400802c1550030880014111b80400038101401c1d40e1290004006554010b81400071881c0c0da107804c131480d445503100350f959954842c140000035141e207503c03400c000c081090300c400520400c0c1d80ba0702103d400107503602d800c54582d0f40b0b0385044c0b40500b44040031581c0206030450f0740006181c1540002e019512640c450407407420b824400c1c0000101e8000207094594448401005054040d60700302d41000806001e9441c1ca002003812540f0750f600c5540210700141101c801c1009014004054a015240403200d01c0310307000300754000035a10304982e440130b4403909000010501c22141c03607044847c80c80700580b94003c0c4c04c50505150819010030310017034015000705080c40b10078500b508120303801b41101c0a10b07c0c08812015100350020034000780200c40010400c0c503110315a0740c0301d1428511031002c581c010202c5040c5590001e1a8906c0034103060b000e9810320440c400042d401c002940d9000b9541d80c5100e40d45990381104030054103540401030f00d21007640440d1707400701514000461 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 528434766 1250 528433516 528433531
    0x7030806100e0904120903050a03080f07031806050c09040e03180d0206040909081303080d0b0609010507020103020d090812160c030f0e0103060e0903040305010b0f100c05010f05070503 81
    0x76901503007000c02d981c49001ca028481e44080301600180004400075218072166085250080c031440e1139560380d80c6072000c1c408096000c180ea00082281000007007014035400141403809012281001d000100300d0344812000904490715030001078600002c00c8107858010714010801e114101c92681550707240da00024040f41c0d024000180b206117030400149409050354007410013850a41303000c04034002004079800840d00207400b04a0050054410302c0c0c450042c50244106c155030710b0380c944c030003000c60303801c0700045000741400d01c00700b0343d141e81080640d10a590282400744c0e8848030300103000000c2036006c0c0010810030010408540351083c0c910501c1c070608035810490482c03480d010007580d800319040c81c0100090703690041202002d00c100d07189010310b1010304010580544070340c03e0b9154648102d0b280a5594004142002407100900600361403050641d50551000c0c0c0c00c1000c0b5000c2d0101c1084032050010f00c0b5040c40c1000001d500a88200e080510100301c142000080140550310580b9606c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 528436016 1250 528434766 528434779
    0x501090902090112020a0b0d0f02121f030506270109030c05120408031c022701020d091d060d0f1a0f07091a0c060408030604050c0c0303010315090807030806 69
    0x204428a4604007a02e5031381c0c005000b6540203151042c11a02ca900440040c41400d8883e500c12501e41c2d0180044d1010020200d240401442c0c401035043e16101d40c0c118615100f04a41d50170800300340c0201e445508001002007048402d020340d400742d24110440d0f01e0312407840d0304e0010041e05141d80b20300500300b02072040c07040d034030300c10b0495550110078000c178003820005800800c00c0d10901100a01c1d0340c08034002402c8090300380300c08105126071611507800d00e00718294400f50f2400003582d06020400303540c00c090a0102d0b03d80e09042c05441c6d4a040e4005200c0b1507008440450b00130b41c0c50410701d03900b003544114543c02c000c0b07243c94916140c400d600c0c0d0013780c0a44110101e160303070b03100e54901c6e48a601260380d061690342c600303402c0080c000072a0407140005034040101c0ea61304041403040c10312460007015000e9072420180103210403108000c181000381c50080c40750202c40400807013182e04507900807004500d00a0649c0c6680014171032000b000700200c02c0080e4840425410800442c4115402c4400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 528437266 1250 528436016 528436019
    0x14040b0307140301140112090b270f0a2d0302010605090c1204150b120106080c2e03060906090516020c060d0e070b0304080d0b010c0b040f1505010909020901 69
    0xa02c9240003c1c091001ca028100540c405107500c0307001c68a40c03449802e200072440403070769140c1034200c0100341c0d43c107120309038004140280c044503420050380c2c030a0071070000d00303560f12407140315915a50707164002040c05d22800103255142000c03100b10844201e03001c0c403203051061645000390080800b8030805010707800702c3e40001d004080e9201650341c0200d1640c03000340c0640d039995401c40400060042c3c0c011090340c1d140011141c0d242d444602c80c924000c840001155814400d1580c034181484814a00c50000c0c41c41c840e8400c42d03445500f2000a5a1074014210204e89141c20740141005401c514029441c1c074900003614403203904034078042c0180c010404040d01c060b943c01c0ba01e0b12040300d40c040d08010204000088803180754446c040403900c89090f2114540c90300181c45d05a4815602038441240c04606600a09940d21a1494002003400c0104651070284e4404505200040001d41046000440c500500c12500c43c104840200c8000c208260368488000390010300c0c2c480c40581c000c041d501e00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 528438516 1250 528437266 528437297
    0x30512130f0501051213060e0102091e150a030b0303070b15030a0302190c050a08010203071d03070501030504050f010504050d0201061a0906070f17120c030f060f0114040b0307 77
    0x41070560788182e4455107400f840ca802c003c110200a06052854102000c030000070074914440c2180f464001ea0000da80c07508100200045130a03809415980d420886060500036600c51059082c0c81c4141e081c2691124500300301a8000d0070f2000040c0d4060000040000810140c11a510b03c01c2000e850030b07000f1441f5140906580799009100180981c3c4541e800c00c42c1400004500c003a01ca02c1414541c1c9002c0d2204089200750034661300400d626034001c0280b04880307400c0481d4030000000c40b0402000110f903113001036076410144c4242818503a9540104080c0003040c0f03d0f54038000b4100d0300a0006007854a02540c0d80c03225449548015440d041c408148102003100030b115000c0c40005180c100071882080208540c4000d0041b28005a4000c404001602010001c0c00228429440c9612003010131308500c2800b07801030004c01d881c101002000001e8800b00070440d00000156031a100b00703114000140d1717001e60b1840c0010386039000420b0002d1115141c1005601c84d0040c1c3d42c654021400e900d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 528439766 1250 528438516 528438539
    0x60506120a0308070e06070516092d0903090306090b010816080717150907090b0405040b1b040f17010605030a0201080a020a020111041403070e19051003051213 70
    0x284010000f4031850045112548190b0200c03042050007024649005001e0340e07014641700004417500c441400e81402080322904501c14a01440c0761105607594185851000700780042002442d40f2185aa070240c0c0001d0510450854000c1c50380150100720401c804e00300000c1039002446403a160b0701c10301580c0c1020081011b480c4084034014001051a64200903081c100c0b54500c4580030a02d00c903540c220545100342400d0140510070303e201030310509040501000c26680c1562506003c1e074101000d20002070208090300f548401e42c400406034041c82c4041100e0203100d50303840545403200c1007901007403602420100e602c00e100f03003200030842282e44105041d15540e4150000e80421a8400041c281409940080624800702d1000086100070f0a46240194005402c100822201624641e80a0a00704445c0d80034040e42180c000240c6840d004058401440421141a140e11003000c240004641c45100001e55071141c2901c8011102d500c0010032900020002030b031488554400103000010503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 528441016 1250 528439766 528439783
    0x9060902040b19121b0f031109010f0e04030306030503031e13080f0a05091c061a090a02090d02090109140711120702031501170c030f071512060306050612 68
    0x701d01d1034128541071420b5000ca03c0d50744261018240204c0c4016154001c0c461706000e0000640007a88a504500388804080548511280510502c00052006952140005084600d10340394500d5581c0c503031a08070050320282c2e200a01500c404020b1200816040159030390719185070043c02038a955411650408195540307010384429020081410701d221031900803d0740011908106281032441c0000c2402a6500b0000c0003014032540c3c0210300b005883c1c0103c10801609800046002d1054000511a144080e01c200d466a9002400b88201d44480e00c10103000394008080303000c0c41d80d461400e10003030680900e100041100580009002a02a042e902c002000e8180104000404541c1c1b1010a9010b050103071703490300c03a2441d0305142e0300d911070106010381002c500114586002e203460340e28003070080f98224071035007019201c080c1300300002030510211014039003141010b0040c3d00b0255100e00901c407c10074050304084020050241942019011301c02c199400202140000c0312540c8030805c5c0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 528442266 1250 528441016 528441049
    0x106052404030624030f06050a02030402010801180f020c0706030c050f070b15030613030206010512060a0c110604050a0507091e0c120c0914030616051c09060902040b 73
    0x600003480401c07050391000304814058012540c2642811030607603410000380c5c1c81125080e210040c28400c100d00d50003100d410002007001036046040950010340000014010b443c000c61890800100004d00c0340c1188540c4921003008640d01c0c1d60110040d078446030907008000201e8244009141103600c20411210349001044000c1d080081c0c41d5201c0c0b416507006030038054900000c0c0c0300c4d409507a50074450280556450069014829001e15010303080a9050b44482d10480f03014007031b10138030000880c0c1070340e100e040d0311030004108506402c19102c00745003c8403500e161040c80d04010400800180c2d40000314018803c942c2e40c00c0e074468403035080c1ca0401c01c103070104202091240d859818182c01c40790911191b03007041c2150440311001c440803201007051100c00500106010007689a8400b144203130500144c0c064003851410b0307004076140780c00038041c94040000020b01602c01c00d105109072210000b4510b0700f800001403506103000030740081e440582c0300310314002d149540d514185803515030804d203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 528443516 1250 528442266 528442339
    0xe27160909050709050405010605180603071d0d050d020f010f06050d080c100c05040504290d30020c100909090206040b040f080709022106060c0a05010605 68
    0x18040d00802401c0d01400140c20303c1404d1401092a5841340107643c041c1031903695158a9007802c503c10240300d0001200580107140400070f00c4400381d03010903141c01004803180101c1c0312100c0200842c0768100c00c00c90241042c0202d20b1028400307540411406a25810b00c002842044600c0e030181044400a11569501c03000c01e124038400100d2a10281010b580c406e41655002180001c6000955211809070000980c0c0010144070500e000d2244070b941205402d0443c0f060140e2030b112207a0002c0130b40740d1520500c1360640c000c0030485068074003d00c0501e0040c5044080302584480c04810b2207181100d0050300444200840c1360070301000002480400c0e0341d41c0f51141d49442510402007111102c01ea030803038410000410b1031407410004200400716000c0c230b44030341c500d0080f0541c1050029001909003900410802e0000c40d500c4144800c0d40709201c2031100241c4540340051240e11855060702168014040101e0500c041940020708440d01964004002c1403000d0f00d00c007a021003410210100b51 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 528444766 1250 528443516 528443519
    0x40b0414070509040f06020c060109060f120b040201141c051006080702060604051b03241e0609011b211412090a05070e15010c051c0e271609 62
    0x441200300c40c0785c070600500d00185409003400c074203070034100241c200c641c0c0f854032880c003040744010700500000180004500701700010419a00c0c0410030038003400c044d041011020191781898180001c9402c540b40103400700d0b00341404446400054003003120b900004107805000010890700070301c10319206508071f9000e001b841d0348080c10403006001c0605a50440c0c2440c0f89000c00000c4144001c500801d00a100700610501c0250075180600d001d4540a00504041643c3d4081d00422070700c0901215003187c0383ca4a80f841c400040b03d50304001d805c60009514103550a20521100c860b480e28203804106285c002524428000e45411a2800c0d920581b03c004111881e040308040312141c0d004107440b01035846940c101c0d01c80324944101a00041071120095083c0302005441c200300a07100d09003800d0101003d0095201d45807181d0305e580d442e01c02003010000c4204928407800c6041010034000340b2840006104000388100e1448110350026044000c0011a41191142d00640000c86450761012500f9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 528446016 1250 528444766 528444773
    0x8030604050a0f1d0f28030201090b010e060316051012060e1e0a050c120402030c1302070302123c0d020d0c090509061509030303040b041407050904 65
    0x60100034002e032034030b0781c1c3d60340080d0000410f030241881d0800a40c81d0f402e40c0c0d1104007803640c02c10a0580c002c403890b900c000b00c0e4001380c07541c4401c440010010160400c0210b4001d0405a000d040d030183c004040d019840004a0603108808405004060030b4089565801c0c20145032072144001d03022f084ea00007800c1d41803450b001d01c92403461019007142040864055640c8030b0300400c0c10015944c1007060001402e001c25034801203102981c7c450f005610601030341c00d0454181c0c0a0348189405805038140700c400040545d1410007400f25420400351525000c6401003c04c14000e4100a400f00e0040c001c407110090084001020b98030011000c25801c400000d803510012840c2d29500d00d030b59421107510008401440a001c0902401c1401c3e20000d0307501e966407145541129411400380c800d026440303100307010a8440c12081907200109403440401851018081c1d4814042d1140e820351510002040004004101c0a032038006d500c18907580d00d1030701404002c80d84400460048513000443c1701300042c0130 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 528447266 1250 528446016 528446021
    0x11404050613030807060e16030f020d140a0c0812030609060909120a0207140306240111030d06060306060c0b0a02071406150f0312030114040b10090e0c0708030604 72
    0x288080400750226140d8aa4030b51341241c0100304246ca100d0743d2419400b8417030400b4061a014403150366a00a141419683d4580d0070610b596000f80c0100c000001d40c40c00c0104541d0014001c0703008400710741144801d0301d0720300085c0e4174074026402c060280c0880d0312030b4103030250160b0b801820f00500360981961a1030030302001560062554455218400700207540a030001c00400000341075a0191507024101031303ca0451208801d8210700070b510150401040541e80440c0043d213841c0790401010021080c3d00403035008500b543c00c0e4003035020016a91110b090349a000d08103d80c01d5850600143c0e0b0740e40c0b802c1d2402024024080d18007910b02c070000c2c40b10903455009015241c8501003c580c00c0403201d01091410000311650185c8600d4003000741030a00d02003040020200d4110300a11001806049c03842036404184506407240c903240540310007a40d966000b00c02591005044040d180000400c014907012040c0700b403400180121001ca184c40c100d0008403410303182c00140c1d00e0701d15254075050200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 528448516 1250 528447266 528447277
    0x405031b0a0911030117070b1201080106050a030206070b0429040605060604061d18090a150e0703061104030501020712030c020c180604140108010e0610050d0b040825110114040506 79
    0x6047c0141d00300030a242101030003170001d02c04424001e400c00e606200c00d80d803c4980d00d801542c4601c100000410040e6540f204071500254000c1d40a081070716140f5141c101051901130300760f0603e111003c41c04080e1a071030982d0744a00d004040c2880192500340a0180340d07c128010040011244200c240082400c54003841c50640003900241040d0200040540c1c0254190361004290700201d80706014802e0b00c00d524035458221400402482c034007000c02541e01e8110f4403008040584809850b8107010408055600540d00003000b07569407074492034000c0d1404000c8441201181c40d116514400a200060101010bc0c020b403045000340c812010035100b03100700410365944261290781004581810911083c0281040b600104000a211020900344007008107621034000d44030704100440d0f0b44c0c2e802c501920580013110040161290b040200785031060001d0354074407585250b1010901c0040020014400c2d004003040e000303030080c01c401115200c650010000e1040b01c1800709002d60b1815200800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 528449766 1250 528448516 528448559
    0x7020103150e060919020318010b0117061201021908071d090403120207020a030606140d02090a0e10050421030504030f08070327060b06131a0405031b0a09110301 71
    0x5d8284502c04a110103981c011104200d42148102e220441540240903602a0311400d080c0384000c2408503a50000c031850086c517543c40341c440350750401e14840c800e5044406000b81840441500451074001506002068a0020000308039600741d04031400c9001441c20340d8400181030900a07121034804440d1004400305104a466080009400595a81c01400021440f906000c5002880d1451108004903070703036215400344683c6201240141d80d100309083e070000b010180020004001e200741850025658421b601b020724040900050044128080580c1000c4420710428007807500340880503500140c8005021aa18018089400340a1a040e0f5400001880e00003552500d0740d41d240812006000a050700c4404503082c00c06020a9024912214034250ba94500d00080c1e940103115601c3d0303d20921042a00700c142d107015400c041001c50b801000005c00700c1e0070020030500116032100c1e22005003480b503958124002040b00590054800d002c051060180c1940e203004840e00f651800350701c6c0e84 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 528451016 1250 528449766 528449791
    0x10050316060512180f060708010603020c190f2f0f0d02010e241b07030308010308072f030c0a12080904061e03140102130b0918070507020103150e0609 66
    0x213150140c08020000c0000001c6009118504203050003404181c010781107007003058010008079140100024260407120481c60307a00403851050b05000314000460f0100a10001c0a007449030a038940c107031034a80c103ca5582000f85c4849200c10100a14004e4440300d00790001c5240044202660103000001c40500015201c0c102d486450f425107240040028100e41400c00003240781c43c0500501c01c0c020f40304840d110f00403c8194210340340075250130b805210080000c200064440c007000500360b4011450348000d030048054142209001850944031501107000340b04548c03078582c0520f0603140e25821141855510a003e01040d02c03907500c3c5510100c1c1040e000360301c801c030014280c0364102003814071003401f007540c0d6445401d501d80106400541d803d0291283e0040c484000c2210b003018008049804035094a562200c80c280410107501000003042c224082010400c2a120341000040950a200741c3c0e04106000074150001801c1040e8010581c20102007800195940ad103601020b80064588641 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 528452266 1250 528451016 528451051
    0x60a0302100302131502120a020f0102040b0702041a21120c06010509070207061d0d05010e06010f050603042105070f030c060f0506150d110310050316060512 69
    0x4650001c00d100840400a540041d181007100c034907442103009040945020300600355528002543c400c5102101a4225000980308425500070891400e00000c400000e44d15a81e0711400031300d0300d8000355401da01550408605810380503450180e400d090a00801c0c83c3e204a0101c46410494044080c10348002d1103040b2440e041904500050564400e40d000144003540c10f08062000164000e0038039429544421000d010564001744e61088000d000c480012008494070001507241c11118006009944de20144828130701001c28010b05035200100503120555684040c4141484101c401412640c0c2803e01a1207008a114a6048040b0035280160904c0c5040e02d402510040750f04049020900b111001d204201c0700b802034180144810b07200704558174284003c2125030f1906111116510b10004100711468416030006085100a00c070f07080d03d03480e280c0d40c05240f120050161501ca48a000450501040e004603002c0a682c501d590f400d04280407840780701c00c1c9800185c400080f01640200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 528453516 1250 528452266 528452269
    0xf040306110a030e06040c12020d020d0b070e01050a0905040f0914030a080601030c1e2001020306040f050610030f0207080c060717060a05060d110a0f080f06090c03060a0302 76
    0x15400305000710703803100740d91003038482005001c880407034003007001a41000040001141c40c150403801220740d000c03800d03038500d03005100044601d600000000e511200e8032494100340b00742d0b40c0c0c0c00c0b88510300f00d8440c010b13141c0d05080113541ca4040e100303d510000302c1c03035034003485103081c2504600e5000c00d40300c5001c10260703c659207250051070102200002d0341d001152034540b0369841a1240c0d0840c1c03080c00c04003d40c0054a0005000011310810003840c01030078015214854499202c1d800301c02030940401c1c54840c200107104e0f01039802500c9484c4144d042200140103541d0600c0350600603000201124810300c40c4440c20b40103080b2800e100031b6025424004400403031354980051203c0308040c001ba00c412302c1e0800c406000e001d8010f17900f03000800c00c40100800764450041050a50b0ba00312400d075100c0e00200c1c20613003d4215000e2039020404041001480e491304203440d83c04080c20350b2540e1266035603140d00c8040011045900d29440341c19940480c0d80581000011a00200082c045000395600ea40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 528454766 1250 528453516 528453521
    0xa0215090607142b020721080c0a0803070f17070503011e080307030905040f050402060a0c02030c0a080705030714030606010309031206140442030c090c0306120c0b0f040306 76
    0x1a0925425600310142c03a075032681c14054140034243e45d250841f20f6002031103411003405600240203201840000e029203800d003080214000342640602c01903620320f05a034005203410b2420901c08042143c20b021854800743c2007804502c20304082d51942c2c00d42e8a018400104001c100401d545c884800200c04900d04d203081c801800454060b840b403138a1185000e0900044800342198640b00768901018000107a45150464030705c840c10340781010b8400500d00009003082070b81126140e100e03107402d4000440c0c1c0360101c7c0170411658205d0070303503c02544c2c4940b5450b01405055440341c4c1038100c640080c072198001d50082085900a10300711201d88410b040702c0044130842c0d04085400309a100700b03428545000c0c01101c42d107840000120a24010070400003107c45000c450b558001114461640300b001080c2220300000e40d0002a240b00c0b5642d6009220010050140020002410604003040383d0482c49468040b0f980d0003441c54444510300134100c00705e42c002c0d2004c46d403080d004001c0003010881d02e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 528456016 1250 528454766 528454813
    0x3040f02012c1203070317060f120a120c05060f07111510060c050a081e0409090204150e07120e0f1b0103061d130609050a021509060714 60
    0x8911a1928a0b81907082120300d00044818280990003081030b800003d51000348590070340a030318400f081503101d4000182d400d50800c0034203034008024481d1040301c0da0001504003501ea010704520a07030320f000400c08413800c514102025140790300038000700c0d0118555842042d800000b0b49080800055106119810480b142c2c0400c00c141840700e0501000c43c0d0f148200400030440c83c03c0c0706c606595507a0f40c503a00c40300c03140700180c40e9590100f0311140844009a4045100c0300e01c0b009940d40c0c980700c0240d00300078143c028059018a00d0b190550003482c14001c0c2d84819600e520281da41940d407160011910010355110400a8585030080341e905c1200400803199003d4400010b4848180c04851080c0d941d194103c1803810141001c10420040017010100c017584060403a07540b80542c0e503500d038894076082d103c00041450b0300d40b8501c0014054046524080907108072012400c4040606000c5558003556015a5004408100300070000e03070200d000400a440041c241e40c00d4481d010f03200b40185041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 528457266 1250 528456016 528456077
    0x6070204090f05060a0e1005090a141b030307020f0f0d06050106090e150609060a03021611121209010f0201151e061d0d020607020a080705030d0c050303040f0201 71
    0x140001502001828054141d0143c804d40e0200200d2031603582d46c50b40c600c2110700340c5541070f64882c00700d81025028410b068005401c20401155030340700108440d40c417190444158940011114040140d160110448095540081c02d40b61017060a40c100f001c40c40b80d0000090f401194050b00000088027401076034000c25082c0c940d800d0081c40d00c4407068040b40020701805106000754203409090b951001940c040903800c2d145e4544901603a070b805d4000744246044101c0440c07881100034100101003001d420f0011083c3d80c0203809481007817545a50301d1003c201d80050344428400d410095107d5810904424400d01c00481d4000b070b080d0503140023003d0b940101070312070043c14650049c043d2001d80c01004121038a0a02c80e00341590900d00030503042d40c0c1c0d10310700c00c100005501d0b065541301d0003905d181a800a001111483c1d0321003002d0b50302d000900c20607009004100240c00c409010f84005145540c00c0005140345940d280e030742a880e09031071402241071049403000d034418503500c019141c0d4511b10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 528458516 1250 528457266 528457283
    0x50601052803180b07050f0715021e09030706030b0609060d0504140d050409021b0607090302090a06140609121504051c0f0e0112090501052e030305090607020409 71
    0x201d000042c2514030080382c40b04103040060000e4001030b07285200d19841007082c40e205803250b0b001045050301c0e1040803800b805d4404403e01554082c40103500825810b4010381680c1903e1041680382201c50003150b000b6036141d0031800003080041e02a421403844103000600d0145000c45040022314203030402d0005c0f00d845503a640c100010003000421070700c44154030200812103050460030080c81e6200d80c0c0180c800080d004651440303459181142010b84411640566016160924004241c1a0284002c2c2d2203a030303400000c1210000c1c0c0c1e102d0041034071025282900c0040d0060b0600009034000003101d070300010b02601c41a010b00d0180882d21100c201c00540b5422414030382841450420540e41c00007944c60154885070510350004a101c0711031060341000c101c45d01717110740140c44243d80c16041d42511070416048104120381984524882e80640210340c503441034203622640c035461081804032000b10012414000b2038010030142c400d151000302500d10f85503095000c00d00f60369154501325607801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 528459766 1250 528458516 528458587
    0x4050a1d100e0a0506011517040f030807050f040b070215030103150c03020306060d0c110d0207080709020c030f030a090834020604090b0111120c0f0f1005060105 71
    0x3210300400b801030750712000030300383e4200c181c4807507840d900e040c442c0700844098600209100750060395508654145000d90407041d00d040d05000110103000701e0128001048900080c14190141065a07540700061600e58101400c1c8402c0f03521540c0131038020380e4018943c600082c0c00224400046001e10300c075103407001180464090f0031082da44001070460a00d4014400c00103507884280c04e8a540400e0b4800100b00c40e46081c6c030545a0b80d10034000310300140210b41b66030000c0c40e00007a4000450f1049422141210750714500d0800301d001d038021104c0160410046240d108920038042e40c1c00c400d20312000108409c40380c2d251016135009406c4010150683d4094440780144401c070010010f50b030007401c0c00740200c6a80014458032480c047c030240389039141c0110559034814060140941601c600711012130b80f01112200c010340100303030712100500c60091355204035500400c520f452582c0c3c85c00200382086c0c0e208e075030a014020050000d810414248040e2540c05a018003500440c00c02d50403911800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 528461016 1250 528459766 528459793
    0xe0d0c110f220c110606090f150409110a05090c030f070207080d030b040b0405040b0f091f0b030c0312030f06130f0b01180308090d05010b120708060a0c02030904050a1d 74
    0xd00b140c1c41020135604440d007048400d89072011032a078488101100f148603507490008400032010903c03480381c0c1140c606400941000060401503034040021a010008070782d8400810000c00d20898800703d08401c2880415a20364002c1d4440b0703002074003401510002600d81d140d240c9418810440000040d4852020003884c0c1402e1140c1c502e5217038103540a01403440c2a132100d82c8144806885a51501c0342d0400052405005000380c80b80c111011b15000708058000d543c0c04054042c1ca0301c240e1084c06002d80c504034624000545106808000c00100d040d541c0c1c81800241c800c500400c1d01e030300030380260304511a251052140c6441424000d000088406940000401101003101e0701c210410a000c400d20100750458240c444072042240d4031425104a0316015003d000d0000300300341c014a4030305100c4031540c000300d01d0700d090301e0369542102c0c3c4560312040003100b910803d101140c0981c108000c1100c0d242000c1d044558840a07040c0007103144104840180c00485141e0303420501034200d1048840719 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 528462266 1250 528461016 528461027
    0x30d1205010b0a0f0c050c061c0e030705120706090c1d0a0509190611040e040b070309030906110f07150e0301110f0703120507030e0d0c110f220c 64
    0x141c40c000d10201d0800b0442d050192001131007503941c1c1d091022480c6040700b0010b042240d0321b10184050400fa40390600d04240ca0038140c040003042d180071f0b081151507905040c4c00016902c025130440e000b0b0801d600c032103c042505d540f016500382c8d103003a02c9200d600045082d007902c0e18002d2009040f07807019001e003042c950700c0d1100041c2ca660903440c103040512001d000002400c003101e20442050400010032840c1100050805195040481c4c0c00440e00040e0516402c2d01507203d903005804840710340e55080002c45c22941c1c2da0340c0003000700710803c1d000d000d00fa00c40c3d0664070103040c401c011210300500b0440158545001c65100303a042c0f204085500780131940c84000103503011419002404034880300f4440200c14081c4100c8038002d500b000c1144c400b40b620403903a60042480d0702c5c800f0000381c04c00300b030010702030a26942c100d0098801d081082002c06c4c491070100d2200703034000d094030042242460070084068242c102c2d45074004011004010002c02e800700000c0415811800081c5421440d84041c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 528463516 1250 528462266 528462269
    0x10b07050c0a06020d0f021c03150e01061b050f06180d090b120c040b0408030a1710051309061406150301150c020a08010513031d0d080a0e030d120501 66
    0x38590b800c02003001c01e800103a0010031350064140b1b2251091807038000c0745480f1070710324040c1c41034001c0301d000e07090542c06074480b44d030520006207005503150703c4c2d405040c54401b0078411100011404800328044440306030000080c0d9108006442c14410b030742c81c0796880c10100780d41c0740240780702102e6880c6406a041101c40d9100784941402e20105103018410f4000c1e0040001e405055010400002c0d803000381c000842d4040c01c008050070383c41d0b03522144295582d82203856a0004143c2e0740035034940c0c2e6203882080c0c1b031083c0000080c0843c0c0c681890240100c0711408049591501e4a076401c190000d1a1400381104c54210383d800d2492a1030a8420800240400c1c203844c8281303d400c100501040003003854a907040c90741800d11010121b05480454840340c525400f210040d4038010a0000348500107515003200c41c007aa8030342c50841a819151501508903800d12940601c1c58600030380010209070103040c9904042c208034109004410110382064a030400c403100242603410f10003080358451040c81e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 528464766 1250 528463516 528463519
    0xb0c1c0c021e10120b0d23120a0c03090902161103070521060105040e030d0903200c01020f01111611090f01031b050a140415060c051c050f0d0f05010b07050c 69
    0x31042c8456129820007191254000301300c0002c7c40e46401c1e5a000400140031811500d80c1000da0740c0303101820082a0180880c4210000341106400040d00ba03041d0003580d040b000d0550600444908903a01c1da42011500c4110320b8140c0101280083d180d0340e00100d0020514015020000d40c0b007217031070140d0070240c0580103284118a0000010403034800003003900e4590307041e6580000c8029940c141901c208580c4100b4506403811300910280c80c00740410942c00e90a82030302154052082a2512030a881492002c5c2c00105001d000b0711941c0d1440328540040180600380000b028180d0f84003003001c940c01203402d400a8204200100300300851082d0000c030340301c40115031190300c0d8140000140201c05030300c103282142c400d1100c03440d06a80c50758814459941c0c0440c0d49100740e80e031755001500000081000351440d000324400c41e4000d10300c0c0201d00380305000c165241ca19000d50840c050301b0036084546503441803aa62040441052200c2c45100c0c040d00202c640642c581a05141c01e51910a1210f0202d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 528466016 1250 528464766 528464779
    0x7290610110601180e0a031e030204050306180f1c0f1b05030304031b110105030403050c060106110d0801180222030302060f01080c030601060813020a0b0c1c0c021e10120b 75
    0x4001f007a44040f205500031800c03224007242c08142c8500310041c1c0540d410480c0d05015440c00e01c25964004c0398506503541a520555103005900441240c80e106156490340c6140f1081e9698070402e44940002a00c0d40341c10708000b800d440342c64400c1c07160007500c400112020790000040c041810b400091030880e900c403450038070b4840f0031584d0b034681424a50700d0b42c1e01e040c88404070216003054000c4e420b4a034060700200c200e9029680d0380c0801014000b00840142c884c0c0181184952682c0c8103003401416581503800e01040d440903040c640307000350f100c0039003580644492600068480c08d8000c070600214042c2c1d0080080c0d0501c03144030758000034103910041c02c562003a607015041d42c5000c80e41c01d04640305400c010b0381c0e03540c0d0030501240032603614200a51007000f109001c00d9000d80000501206d020000403100d46c0d00030b4011300003000083c14036002c0400c00100700e0340c00500d0315481094241d41101c4080911107281c1d00840d0300080021082408500460407009625074584910400003604481c403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 528467266 1250 528466016 528466033
    0x11091302061806030901050a0506060a021c0908030a050c16050d0b19020c0f010c020601051f03021c09050c060a0f0c08120c07290610110601180e 64
    0x965a460448009000d00300120300404012100310500103108409460300e0381e68640061818001c140895410500360f1806001c246241440d1082d0b0300710600540003031520501170401032084000c00c0d640d540070845801c2c00814a0380b4280301a08071100c880e1212615000c00100c00c41c2468441c511681c02500604000c1103295a0307102d120100f5600070700b4209540c3c03a03039003282c3d00841e81c000400b01802d00003d00320720000c400044070352110020400030049403840c0740049072508020721445510241014548007042e4018440495071286414010318000b80501c04144000311f20101512042e0b03611070071000e21400388903400b0001811109580750031700e46140603003a001c012580701c0801049044110410070722000720b88020b001c00400105610700501d00301c3c0700c0d03030101104480714103003c0034203030328004030100e040480c202c40402e80c0415982e19042c0895a034040184100300720500055806180d02070000c18041d06003980001c24005020203c40e054560414558041e030313100842 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 528468516 1250 528467266 528467281
    0x1030525060f090b040b2a0c0108130f0f1e0b0114040603050115050a0b030103080403140a060510080f1c0e0d061e0c0219080307110709091109 63
    0x6000e019500d950900508240c040141100c04030039681001000d200c000502007a4400d5040c003400da04020000010310884c8104019a00100101c44501065002c8030504826601840304113500c00794004241c9220030b00c60716034040c000003504003a00d83c00d40d148070110502c18440c0300c0c199940614119088030300c8540e40c1d00c0d10410414030030707032151000030700c0b51003850781d1580c0140d402150898024046400900d42c0850030404070f2140340c0c030903005000001103040c142000da1f03048941118405041a14603203a8082c00180396015040e28014441c20038005038544c0305003030045681a00100b08181171603449444d054003440035034001c0d0710003403000300700a04440780804042d1582c500b0070203612020011844546201400070000d81c10990b0095154542c20b50b4034516107204030080c04030b038240c264207a8451020718400401c501c4200c0040f004201404021600400c03689040408075400784555410710940d034011004031038547c8241002e1000d45441c60310200c03001c48d9a02045d0a1a16 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 528469766 1250 528468516 528468583
    0xd05010603090f060e03040e0f0f07020f12132103020c0d0f02130917210402030607080405070503030703020109020306060910090f2a030f0c0509060c0c03030a0503010305 75
    0x440100155221960b5017500704043c001d0310000c203c5108080e0301805d10741c6030082c110300110b440c0350b4084150000100003910002d41d241040c0c8180d0301401c88400c1d929020b0318a544003401c02d0302e0800c41080001640202c0441071003403070300c06224070300c0c0d14aa20b1034020304018070002e02e24403440124001d08007050b1030b21a800041607044035085581d412042401010308028000508032110042214009404050081402940045a41084102c48003044c054a113040d10081d42540c090030000c3c1403240107c0380e00750824010300c100c40d03c2c0f5989078002032541d80b05007402c0b40103035152108801141000c02207140c20610488042c202c0d80f0f401070003c1500030072403144415442d103900303200d1946e12484d40110980450072110b20b203501ca0300d95010b41d81000014003000080d180001072044180745e40b142e030002c4e9810756640344c902101d10381000700641010b5144c450a00417003c4075021540e04100400c00000552501900e962440c20b1460030201c001c0780b44c528488042c1c1c1440144851003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 528471016 1250 528469766 528469793
    0x110a140603090f0a031701090c0504050409020a1502030d0605040e0c010c06020408010c090e07090501020613051609150914040807030e0901090e071e2c04080d0501060309 75
    0x140e55558481d079803901c00e107140400380c103a01882e0303001e41e643c501c2c181070713110003640c8046180301c0d2141450399942c04d481e000c45850005032000a1401d00c030511a51811b50408022a0700040400489a4407030300c5130288140540c03680303400740e44001103050325110b403409a040101400ca0f0200000000d07448440c4c6c40c2d800c404c005604210009881408005041e030503038014222001c0200440300c00c4181c0034150031218012103c42504480010301114818027090090700c0c01030703015104544410050706295010b07864101c07080d00600b4134000b02000c3d070401642c0102104c000101c1c111141010a40c4500c1d42c030782141042c14180401a005c0b4040035007015045540302c28000d44d1400c040c2004c03114400039040b0140c0c0f014020000241c20800c91300300803001404481520f403480ea860341440381503260040407402518440408228140303201d00540d40e03544082d04035144035a910310020803002011201110f003010301040c1d41c542002c0510400d070150400d03080c20071003000903455a0b03a056110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 528472266 1250 528471016 528471019
    0x14010e03060c070c090f020304140a0507060809120d0203100807060f080c09030d030b0906041a0d080c070321090b1e0c100501030515010e010902090406030210020a110a14 75
    0x3001401c0001c01d2507071030014144682c08021406d42c90139010040d51003900c0a45040d841c000001c50703103000c00700c5c0c4901301950240c01000c0e032138681a0166101000201100424001c00e4030106845000130010460550b40b800c3c01680d03854060402074072040140c020714420744c4550000c0c0419504050000c00b02d08140c10f00a1050341d0300140040075100d8050100e4143c0508482120300ca90907422164201800f154200e815960b0708c0c0c2400200c50481d4611003820b000340810443e5400c2000d071441d1001c3c024601c03a0b24190703185552621b03100156208031100f41c500072012403040400c90034401d01030054901907665501d05600181d0b10b01501c0d8040a80d00841e00309041103000070030440c1d0302c4017000c405a446a03c21030111000401003403101b903e05000700d1809515201403102064103a4070900c1c00c3c0291a400c0c0f5444174000d40240c0130316500542e03584004005079445030300c4040e003030250354014580c108081c9015003145007000380180c050600c20105104d450001041880f00030710 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 528473516 1250 528472266 528472291
    0x8070305041b0303050d05060301050c07020d1406101703040b0a12060e010f08010b0f01020307030804030e030a0b01060f0e030d180b0d06031412190203130f14010e0306 74
    0x71582001075428049404040701036280b01c02c00810950028003a0a4901d43c42c1810819a6146001e240c00d95004951941c0701200030000680103240c081e0041c55054010520000c903048a0072440d8988035055804c403000f03405c40681000310301c0c42100c81c0c60760215480007079800c2a1030980303544164003035481c5480a0044000c104440000554040c0e07000342445003c40495594401c08400d6044082c055200715500b45010444681402c1c00d902081c0981a4000c5180c03072402c2e1000c80b0782040144c42101007204000d02c540d42170350104114102540941c44980b01945040310240005403d080840700380070801c1140411680c020500d40000c038458105102c141c010002072500b400c100b5001038040354400310300c1440c41e0255500c03810079244210a040f900d520740e0060666241382144400100000820006568843d41207100d01030075090300480341400c13640d04002c4503a5403142c0258201c0100030104008c5185078840801e01150b084c2003080a200c01400401d031500d800500e505540c25 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 528474766 1250 528473516 528473521
    0x1005070302071a130f05010f03061503050903040f03060c0807081003030818030c010207020a0e0f06134d12060a080d0201020307081005031b13020711030d0f08070305 73
    0xe00f00000c03518560700e0954100703940c81e201c0300d05a940c002c0364020640003890804030b07000d4941c0607100d524241c8410a440403011880710000302c0c00b910008140000e0b50000f4400011440141e01a16002d503115074004101c18441030320003071441c80000c20306010046840c0503c0303080300e8050368610559815142103081d80c2c0d982621546844285034030082141b000061484c00300d601035026101d8144203c40b11200359680c0d1505c04030448050301d807014140f083c400415900d2919607002c007803813048598080360000f11400d00c140300313003440503001d901c00030441441c80a900408030800031181c9404800010600304101d1072801e406081e40803030424030800041445a0380300c0c1070100080c8844400c0360f2010708204c0000b4040d41055800d0b40100780c0202c041011034002c0781d40c3e04149c03000900108030160300082030060700200f030402550014001c0c944001e20041a0000f082d13501d010304010a080a0b003641454134280021058100304003c2000c0b40500c141c0c0070107826000005454041050b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 528476016 1250 528474766 528474809
    0x1104020a0f080a150f0906062c0f040203040b0906101406031005030a0c030605010e0103030c031b141b040203060906011107080a200d1707080d0908040302100507030207 74
    0x1400e8209540307002e5104c072000040c1500481c500e1005440092a061100c1e541c6d0301c1040d038407000164901c000444200c10b0141c60204228040c42c0f00d000010b21418080341084046012648103590580d0f01018100804c80c0d540c208001c0c403a08181c00450302442240380000c400308111202c46030910030340001000c03541c844102107401018120007410b0322400c121030302c1c1c0720600c9803480c03004681060034000002103650496000d0b6040780d41640328070064507400d40d012980c0904185c0d00c842c003100258266000f103000c0c030100c0c80c1c407803c00c00c00501d5601d242c1e0506d0181d8441c24203c4a1149004004200998a5469010341c21510a081411404441e0404c640c28540b444c0c20990051041d00c1c2c10502b03120720f081c16100e2802500b66508902c071a40024801c1000041c00d001e41080c4d285e031030107c0e00f01d0100c0010240240211100c50600d440c3c42c40300404c0d1040b194081da041e0b403011034140705524201406809070b4946060140c40c4c44400c1c0c1e0082c1d211446442090031414905601c0b0245 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 528477266 1250 528476016 528476021
    0x1021c202406013b0d06020406110f01091101050705160308090109080105190506030a080f030601081e0103150921080705040e070c02040f0f050726060d0303020403021005071104020a0f080a 83
    0x17a503078443c0003951501d4443c4401883c0003800c22a05940e031207180d01c0b1101d03c11061080d241d02d5500107114545801e141c0f00107403016441003a048415200c1c08407480c902c4e82c620320101300a5441202c10540d2401028001000d131502070b0032165007a490082803110346440e40400c0595410344200120b400d5070368000003400c005d0b2889001e403030050005850a2000c6040000714072542c401d032100c28890b29103181c036001400c0c4807156120460b003c0001400402c95900140d82c80a5046001080c19451a41d8110510028007481c00503088116801d03144035030420503150b4842c6207031030f2160400e031411609051484000d4040e1003480600502101951910f0b00001c0d640c200d808000e209049990745220010300081701c0c441300154034881107550a0b281d4442c1007239269071590340e401d04c98a80c40d0130804010441442101415070030040000141c07140140d2002c0303c06140c031000e8603000e0300e00740401c1c00c00090060318801c40c4100001c041d4039421850140c01a042407520000d2981c0e280183c500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 528478516 1250 528477266 528477289
    0x1b0d0317010303120c081303110c0d0c030b01120302030f0c0111040308090108070311041a120910180305030103060c2c01021c202406013b 61
    0xc503455200c004818540c014101c000030165545017080305251903401124031020030b941c0300c0030004d941c9010750301183c42000c41e86d059180800940b10302c0840c51001a004d90740c20039007210b1200d2520303010002e0001c210b140c2030040038000003c01002c0032a40c1d0081d01d92140d43c600245401010500c80f11160096001518140e81050140d66842e100d06001103281c200d4003030b450002d101b10f40000c02e481d110b8041c8640300c4010f042503034141400d01c0d1484c80c2c03904444140074024841030040080f02d0074020685802034132108060481c030b58400645c44252404030194002d03001003070f5945000a0b07408030480c3e0460b030300710000160036446910220340118a01e81c03a030420780c1184002030302604180049a81c1c0d079101f41c00300c030750a80308800d802d8060f1030a17070901d40104001d00040000d41c02035400b50921110074000f515441e424003014880c1c0d001e04100c84000e10010340c010002d503540c00501303950078018003401d0310a40300d8010410046d111411030300c0c58a04008885a0711454451960028 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 528479766 1250 528478516 528478547
    0x100b0405012a150b040605011b050c030a0f0b1602100b010c020310050901060906050d03030b1201022101170705040c030207061103040c0e04031e120c0216081b0d03 72
    0x18402c0382c0750400c0d8075500b15541d90610001e1401c44044200d1500f1310a482c102e81c0181c40300041e080803940c210131241c200325801c0d1114051010b00310040d42c1d09100c1c02003c0340c49040407854901c000e082c1011018002051500c401845407441850142c0019883c8001d25601d81d01040c44880c0100480d4441200764000b9054450320418100240c0c0f690003040c400c81c0c0850003000030f40e5845414000340e4500e48503039a001032242a444003ca4803a0b00302c40349107080900950340d5480110485400ca80c0301c602c001889001180c2c000c9000314100030024010070351508a22020008640f11a442c3c200c1445103078400e5640d40f41e0403480134000d40540703103079075000304003000410070b15480254107500440e821130341d03a0040800490302c0c076160700119010b10707003540e00c0d141a901d07901408845080210111018081483c40c813204c002c04a0191a2143c00c1d103030b01822482c80700031251200c070754994016180681040400c1c0320540301c2c0c0303003403c0c007040e0b4201c405044521075070034160740c0c44000840b0720 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 528481016 1250 528479766 528479837
    0x3030e19180906050c070812060f0d110f0904110910081501050301180506040f0c030209150f0307140d170a110c0105190804060b04021c05100b040501 66
    0x35012107941c0702c06280c42c014003040c0700558400311102c81034450100c00520340c0d4014044105242d405601e401e81c8210b0144c9107008820700c02c0002001e200010030308032a00050800810600c1c1001d40d1500c0c01e969041d1000619824190340d288000020300e80303014001c4114030300190b0300700c0d04400500d0007006000c064450906c0d112a507491020760900a09003c3d42c2010705000d900c40d4504070513141140c01801503d541d498030750b00c1042c481c802080a40b40c001080c240400580d07501134600b40503000706516401580c2d44913061107103046802101a11039000340c082001540e003170540450103a403084451080440351494913900304508041c0ca0f02522001050105035242c02201e4000034507512403c60380e1a01c9140b004541511a0410b0000600705801c0a110021700400c0c0d0a0f03001849190003080907031401005c90100d030455507071504085100c0030302c51400106403152a4010045030818007040c2e0800c1c0900300148982d109071410000304424411070000c02145d01e004400412002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 528482266 1250 528481016 528481049
    0x3010306022a0a0506060a030b1605040f1418060a12060f02040807030c0909120e040e0109060b0a0801090203120c071d1b0a090311040e070e090609060103030e19 71
    0x107407540c3c0c030741900040b1076620910002c22081e2a290140360708695102c039501d02a82c3e0b40c484002c2c010f80c5458030300801e00100340008241008001c07401c2c0003411080001011138403858003006991000f8070b00b010241c100840c140b008540781c03a103100d0141d80c51400d00380400c6815140c400024440c3c550706607011480418003140e07070200414000708490040740404000c03a1602404011038012003001070034031002a4070704889500501195400075402040040c88131000c03e602420b660201c0c82c1100e103540c0d5000b10705d0b050315040300c00d47c6c05401810020840244541d021a5907402c1d01c941c01264107501003415500010200403c0300a41049044c2855502240c0450b001d80c2d68180d03400a83c6d5514100001804040c40091340c5410b06180d0703501010518545904c03a20030000f80030b254009031141c904000300c00080081ca40103100d6480040340a01e000301c40e240c20204094809241504101c0040010075032140b4030804100c1c0031110f03c000e046001032072214001269001c162003400d000074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 528483516 1250 528482266 528482347
    0x23040902070501021e131a070b090c1315090b0f060c0106031a1e0403091a040f0e01030206040b0d0b0d05010e010b121009060e010510060e03120301030602 68
    0x1500c9003501da01e0004030640c00c4170549800c503008210511100307400081c0c040114a9043c1c03c110840600b80b001c50b031610001d52100003410504540421681d40540030294090420001000500d075402c5d1007084184441d047c841964a41c81c4509041580c440c441c440b00c6940700c1c40302e403900900042c04c040e629414144682c1c080e00492005555110381c82941d02000e140054480e803040b0000446440000d00c5c2d0300030003016100151094041224540380803512451080e282e07120b1140381c0309010f441d0751502da04541582c1d141d402140c0d000725040010030040e00c0396020744040e110200101c5031280c10010601004100840001e0303888404a00381605008040d8058519080c03080001d00c0303008031190034402404407544072111f803544144080310f800380c00c680c803041e1850320504000c07450380c043d209203600b540c034150341098011148280400106800c000c02c401c9c10401070700540241103070306120100c28001403101924141d000070301603010070211f01c221082540c0c580c005e120300d03840c04030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 528484766 1250 528483516 528483521
    0xd1709031606030f14010501080403020a02120a020a050303070b010e07140d05060117190216021e0108090111160812041b0603050402150a0212030f16030203060123040902070501 78
    0x810b02000c64030b003000c507007490f005074014501120f405244104440e4607001c01101d140700018000d030114041e104680e00165920a030a00c041909000100b68064441c010040324103059071180344a6801000100001000324880078110740310a6003242d03d030b60b586607095491001a0b400d82c1480400010310900b0340c00c1076405580919800c1ea00e030002220240c501031050f010a42d06001002c820905507806011a44c008144000140342c9250404180d42d0204004800d424010005c0c0da410244051b15560b101c2c01c4030368829400c10003070000d1561141c000100c2c1c030810030b0607003042c0e1003064030b04d0030312100c00d0440d06001d8550b0701e400f0161070541043d41603d1840d00301140d4007000c1c010300103645403080c0540d034025900149079030303007840310600d49138015031000b070301d03841940544030300490f6142d40740010710300c914610300c5200c0ba5031901c080d0340c03503800703440c4c2c8400024140f040c014410303a41d91046000040440980803407120b0340c00b1505020880c05103030300801e4a00d0000807190b00b00441034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 528486016 1250 528484766 528484769
    0x3030a050a0609150302041d160504180c031e05150414010b060f032a03060108060a06051e2218060b0d09211112090d17090316 56
    0x150001c009043e120140d20702550107001d140d0660038900002032000d80341c40e9101c0544030405142a1902c0c5c115078110509044503000482d10319006a141045036007000d000f242190a91282c01d0f0310286034540c0d0744c60b450b070308500001d005600482e903403061500201c0104000b09400c5000c07200c0c5101d4540712a021281c046030304032010510040320a210540500039460620340040c00c0d01e0415890804034000d68200912102000304428024001035204d400c0d501400c0b1010780c1040d54038a0004000b400303083c00a40703032a004000034081003003c294824261401c151041d145103030030040b40710003150a40125000e004040407401d0020303025844100955003102c2d200e40d800488080c40c8190001160814400c9601821040040c900499100e612104c0b01c1803190006110807020250460034030031501c05070f0804991011400c030209902006150344c980c0300555003900c0d1400d1000403030119044220000c18403c00c95005851081450701642c051010203000c8490303103030503400f0701603000019 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 528487266 1250 528486016 528486031
    0x11401080f16060504140310020c07060305011a03010308090a09230c03010b251a190504121107051801060f05040f03080f1608130e130311030c03030a05 67
    0x3030700c01002e005800da024000889115444c2c0e14146440e10b1420350b051174285824540c940200740c21400b22204030b2020b041c07c0e40391003005103250f03428058050200d0701c060300500c04d01c0c010f98000003580c0c0d036002d080701d041d240d1043d071081e154002200132406198180c3c005241d01030901d000c80d4449840041c840c0c034620503c1300e1112460f110841080200c0c8030a00420881030b40c02c116124141d90820130740c8400c1c1000b4841034026403101e4a910b80603130f9071400854403920f8400d0a109101d24124040319650305041401c10a03400d01d031740c4c1c81c01d024400201010074031003107041c8032180c61400d11844004160203050030b05c50000d559941c001200090007140d003c1030744120508074a40c82842521f00303840c40400361444042c2503458221250b001500100681c5d903080100880300541282e000300c10500c940000742c0c48201d40c8481c0705901040350082d2508033040010000b00ca0942d803d103101d6560142442203060f46904042400e511542c42c0034045071000100f40301074000607602480c8150039 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 528488516 1250 528487266 528487273
    0x1270f060e070c2d05060c36060a02070801020a09060f030b01082208070515130809222409020f040504110c0a0506041704062c131407080108070314011401080f 70
    0x6030051421501072300000c100c050070906548150f40c1071503401400b00c1d400900440f042075940300b4800d400ea0b445010b2900000e07039211001c00029400200701070060465007011300940e0103800000303100355801000074485100b0200b5940b07800001c1d030704031102c80d504510303929510220707810000d0744e0f041c3c8000c4c038803000700800001944c907a0400e5001c00550782d000000f949404000e0f0f08110702c0340c20200c41c103082d40e203006041d80078040380341c8580e94a4075203081094111452000100c0c40d0300d1200d42c48088100d00420800c40d031110103200301c605070b0b00c007150001480c804c0c9162082c5140113820b680e0b206441000102c10074010005a180d03c00c1c0c0c0b00f1716200d03980c14200ca201d036845020354031503680800c02c80d01c0c22880c40c03038000c94581c0556906046142d2810401c800148502e04440c840d221900e0b0f45a01049490343d1410b12940c1c004240d040141007545001e903465516544da22014040000c3c2186c8015420029080704541c900488040503c1e543c4802145458215846c001c103a58032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 528489766 1250 528488516 528488557
    0xa0b12010f0f090c1218020916050412060b03010c0c17160201050c0c090c0c0610050105040506070501060e0411040c03090b01270f060e070c2d05060c 66
    0xc0c140e1800c0042c1c802000020300d49614229001001c2c1451484030740034422008000c00344044540710714000408505203001c0500c50600500103580381c0074140140007080400c0a80c50030360480116401c40d4100622080701c82120b003006070050004258096255082c00c002d00505540a003c10038000e00422104400c6000b006a50040d44101c1c020400488401140c5801542c040c0019003a10012102520b076001ca80d0000202c11000480b00d0948402010400e90b0a0072820000141e00c00c503090321041c0b03a035007000f0001e00305005038485e80c3e114004c0010364604004080d0025030041c01c0402034810703d03081c1841d00c1c22180c01d000b02d036140100e20302020342c103003103101c0d00076001d034243c0040d03005000e0790901805a5410310040c5d4000d48001000740c1d5080c01c010300384542400740034407420016140e130414401140c090400307048074013041006401d68020072034903134192551081501c030200781e0b10994a5000c250650001000e000c5008941c1080340080b45500100001e0a101884000c101e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 528491016 1250 528489766 528489779
    0xf03090b0f06180601090303050c0a0b1f06020708061810020703030c0e03010b15160b04080904050f090d0503060d080a0f02121c02220f05011e02030d09020a050a0b1201 74
    0x4001301d400600041101c10104003180c060030003400c2d0f0000fa02c00b510303034400d61621199445d41068910309960070840b02071071100c0000d00038910140c801d502c05010720381e02d0172034120f6541c170b805400c403118012011680d40a000f810805240103a9508000b551502584d0a02800a003101010000810071005640500d03241c1031050f0840603200614500c400c46901c98000541c0e0002e00124100a1401c80388c4c00c0450119101107128901c9202c0d6580d40300c0c04a000c1c041603407030141c20703628140009000d10442e00b6000c182c40354110607601d440c076144e968090024995600c00714010340410030008444c5c0466a010794401103642c5150201c60420f810b016038807a0500c2510f00090039503040000c0c000007045250014202c1025032850001015200342d4001c0640007264043c000c3c20700621130400aa50f0441c0313104201c02d00324079603241600341c0c0980281d00c1340700302c640300c0303207102e80d120825411584d496200034060003018050000e09a00e69005070610b0380b0141125178614081c10000454 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 528492266 1250 528491016 528491059
    0x105100305070804060e070f090e010617030f090d0f060222050a050111010f05011203080a0207150504020a0f17010b03030c03160606050d0b01060f020106080606010f03090b0f06 78
    0x22981d03940c3d200341903600c9880702c000a101032040380c02d080c02880070005010548001c450040e040c8103400151400000a0780c034210f88081d445510740781003031020302c00c2c0d095010090b210160300b010012a0749441181c00159440400704e002800b8a5002d1400824802540d01901301840c2509071640c2001d1212800344001481e881425030103611348a00f80181c3d40304080c00e00758151b2020020456500a18122060b180242c00c91440c0b0340c0d08a50740e10905512064194101c1782a0200314038100807911043c20710b81a1a03000340000303403510007150841d1070310021240108000d24400d40b400f81c5170170010741c074440f04800ba00010b608181e032100c4030389804000c0f0b400484052008518000001c0c0104a000a001c401900c41669401c030005003a00c0312040c440d03401e0300c2480c80c84c940750b041c0758010f04018804214002107a250442c240300c811000202035801c29000d00b001d00c1202c6030101e003180a03098000d4003c014481501c24441c40700e00980340e003030040d0004c4840080c0c0e4458010903022 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 528493516 1250 528492266 528492271
    0x3020105070e031903030e06070c1704030f111c060e15010b04061103041206092f12030d06091d0f070603020d0b06180a080c030a02060a09080f060105100305 69
    0x3855009100c0c95181c4a40050100343d006205c0d08000c43d1000792140780c10306200e400c4410300301140c00a0100400c0207034044280401000200c2221300300703400d5440d001c2c03030b075110154000d200c002c420070140800c0c2c0d03405800403801c1a83c1d0301c12150060403403a0503005418a1540d41101c0d00c100a1804080680c8500840c140c03140c8030440781c1010310703015045940301544103503501035000c00c000c0818500109130a80c0441c9000368004aa41c1302c2c9071408010726a1803070038105c444944890035106c0041e40e01c2ca4040800380032500701c12b05280c41d200d85415407144c40565803489240c644001843d00890f0040c1802d050921414055101c48140c40750700c940700210440b11a070005802480321501a50140146e01d51071400021a1020500070a000760b111000c10303400d40c004440c0c504003600d098980d240c05800160051310f844140100480c3c1e80344484c2e030000382f0680c6c0c003107104400e681c801e884400040a4a80c1207500c00d05203806c003180c584200b800b03894003031200901603035000c4d4024040c160 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 528494766 1250 528493516 528493519
    0xc050f030a02010503150d0f05010c090b0703020d030f02041d0f01080c010210110d020703050309010f06050303090f150301060507031e1d011106071101201b010b13050403020105070e 80
    0x6241d0b5840c8881c0d00003013902101d46d550300005540c2130001052801c00da01c0445441100000342848807141d001c1c0c142d000561200f20440010812400065400b1485480906090402040e609240b9280784064001c507003040041c110505180c08a001315a403c0c5800794402011519140c1d032900303d040e81300e1103958145401760f403049440d001143c2c015480900c50107503420781c85080024411b010010303079109800c240c002820100510203102020301c52004e0000030302d402001203038944800300e52203000316160345202d0401c0b1000c24429445110b0150100c121051840e503807983c44440280098020000507800035a85052014504241825a94946955480307503825001101280514005040c0e40da50400400c42100140c48600704062405110981c0350b40c3e060005451040d402c40e004010940082c10741550350031355003000390b012148070b64020f0b116100580072000125026260031468940c12400d0800a601070030025071145000d14400d90080c841c03030b02d47d42401c58450f4400000785 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 528496016 1250 528494766 528494777
    0x180207140a0b2a0d09050f0601030203120a03060803070317070e0307030609020103140a0c2d050313050f1b041a0f21030706110406080118020d02070c050f030a0201 72
    0x80c0540e200700312030584410121242070080c0c0d00c6a40f51403242e401001c034040c0c2c680d4603040d00e40f08201091107101c900080c03140050100390300d59000a50350f0444903d40d04d070032241c00104003111910a8004070b014043d0801101d0b40c1da0b05901d0000c20340c02070510301c403c0200d503402c0070031101c5105080c5036a4019005008001c13250460320f03840b00400b501202241499075030382418540719440d001042c407071740002c0000181c4000001014042c00c80c000410000480307140059804448540030440c04810700340703440e54076030740e490506014410100c04d0140c810b202d0203202c1413a1030130004400034400c0c0c10b1004090682e200d0703014441070b04c01c0942030411009070b000c1d540300d26041103c03010000c00c50051504489140d0070001605041d4110603c0d45180c01c0041d440b81480401c0c003070310901c2d401d0085880c0c5000d1400b40010051b15041c06401a901d101d5109040c4d01481d40c1c05680c0100510181150380310304038a4040342c1c0c080d003440380d14010074404a40d40c0140c43c01188010807540c068440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 528497266 1250 528496016 528496021
    0x6090c031f0b04020d1802010207140604030f0c08030301170106050a050f22060306090218010317031f0603020c010e0318190305060115030510050607060e07180207140a0b 75
    0x54002d4001030000300d41181e400e015030012074035940034903100e200405131542d1707505d1028000242828116004010090b00440d41d04005495020413241103070b070402e0301c0340c0301101c1c240b03090b401401c1c00d540304d10050300c80031001081142a1316520b503050b40414000300070207079841c410320103509480d2180301e43c018514810750915082000280580c5014000910a4140040305600850740343d40c0050b12a1076a4001410443c10705050348502100e00500ca144107602d559144020504121015541c0d28004008103202c18000c25480c0404180c104800c400181c442100074000c0d00291840030302d6609103c49030035911004800c88400e21590505004040046024031041040591055641c048035040000c003258086c00614042d000603180d1200e80d0521400013815501d010700b042d005810030340c0c020442030f550541111601d6a01074400305540e1070504115081010980c4481406106a911030071907034625402040e19501c6107141d400c2191240d0090f0340d40305070f001d1009280c00706a601 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 528498516 1250 528497266 528497323
    0xd05031215013e0d0504030b06040504120507050c06190e0a0305070b0c0c0301231509010612090f0c060201060801050903030406110d020f1b0d1403070c0b010806090c03 74
    0x1d00003d40300ca81010612186100782606140c51500901c07a000150081014400c0008500c44e25400102c121003d202500702511001c500c00020200542401800254601085410b00c03d1240c62000108002e4031443d07120341803407107402541c100030005104a0b82c842c91501c2c2020240096a400500400d4490f04180c41c0c10f081d83d1202004441c98440c545c5140c48030340d002d0281218518020f4031070401503010b040c1d01c050409000d0f25000c03003041a8040c50003103448141c01a81191464680f0340e4591b01c42014680042c84102c1002c3e0440e00d1210940040c03000728008070080390410f80c02001119a0b03662454204c403030036512082c00390802c0010801040e0541c1154603900a0000724034130309194030001c00d00726449200344088a110211b082481c01d03201070362021036650740f44043d05034035400c050010a400340350a40d40592207404400f00350441c5c400c6e03465802181d070102030305201e543c51740c080640d5105c044800c044e05114011101c03000303040100714849100c00d0500c407030800d80c80c80c15 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 528499766 1250 528498516 528498587
    0x6040b160c031b0606080d032d0b0a082d0c0117040204060b030a05010504060603020a020a0f05101109040c14030426040308070209150d020f0d0503121501 68
    0x40301c4800f6405070960420100d00d09110f0040108a00b4004100c90410585c02a00355024240d150070b240c121611a152402480d020410812504100004040c0e0340100052014607540c2c020022074400c8040c040385003080c10041c1c4082d003401142d195102840300c003031950341c3d8001c0021607000815140c0030301c3c0310011035600746400500c01007000c80c82580725160401180c000311940307035580c0e0700d480041007241040d103d86030240000d49410b5141200c05d1802075641c2c045064000e0081038107107004010310801303000c0500d071586441c00900880303c0d03120a80c0f400340c22a25180b0301c5949441070001c500c80c003801e9200c020454080b11907040d40e0345d540318070214641e207144180460a804040c0068a10f05800410245110b0740f001a16a00c150040c0724401d10000c111080e001c0300340c0b40c0f020301c60b61404d5010076a1981150079840720b205c010081014607441c02d0006081c3d120100f42d61803030100400d0851700c54500c0000101441c01c00800445480031003851041003141c40d141a03501c00138501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 528501016 1250 528499766 528499787
    0x61706060910051608072001080f060f180709030c0509040c12030e150703030509070503070b0a0e030d05070b0f01050117060102011508160807030809270906040b160c03 74
    0x80c14400c0e2051340d281c81d5031942c1d500000302240c7c8130380ea4a25a4889804c400c0401c40c15079800c0c6007100b03051521544003401600c005e0940c5200d1354038007000008903650f01d007841e42c449403412a412620300300044060035000e13080c0030880f00120f00302004111801c01214040c4a00d81001c8403555251501c61101c04c6a20042d000743e04002c00502c040304540c9a04605034142c0c4a0485a156950480e040c01022a60050880211600040d40400c0a6034000824506483c0340c0c0c1011692585500421368640350b6845d1004e4040c000c6084800300b442e08000903041041c05a00014040c1d070380c00304125100d007000d01034640420303012556040f500c5400d00c4078039440780f0103000005d07070815115520b181c031a03a030f40d100e20728992140315a1722645408034401002010403400800084c0c1c19680c500c9018040c81c0340c12030107403403246459100b05240b42036a030646c02e007070708064509007004641c650716500211400d403001955280414480d0f05000313002450090141e0b25038200133400d64007101c109145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 528502266 1250 528501016 528501037
    0x30a0b04170f070506011d0702061b0c190c080a030203030c0306040908030f04150c020307080a030b1f140a0509040923031201140a030b090109080406170606091005 72
    0x1e002c41c0780800e00d018000d1189901420042c041c541c58150b9111a0341451040803003c0d601c0241840349540d000551386130403105101f04e802d40c0d540802039100300c50290008024940c400c9030028001c0d44121040b0119082c02803841c80300d107584484050b5590005100020016801000040d0f1918060b9000c2c5401c650014804102c0300c030385840e00040c54000366240100607842074140f01c2000400601c1c4451090b08010501460310f107240c1c00303500c90060300d60280ca05100028a140d07101e1103940103c0d00c1e44070007444c1d422a0840c826030b00405110104240c0085226040c03001040c0040300709442c09030189a403450b00d0585500240005080014804c4440e540e000c0d802e40f00d030941d001c005e100c04440c03043c000e5444402d4004800350340c1038103a00c40142c0300c0c41c040140890b611f03941018002e40340c000f00a00a0340c3c440440d810700411170400058140e0300003080c0441e405512030500020310391120002d0f0000d44642040001e01d208900100d5403140c1442c0b52004041d00510142420012 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 528503516 1250 528502266 528502313
    0x207030c02040507080f06090105060901050d0615050a02010f06180c02011b0c020306010f0b031602070b040b030103051b06041707030f06050124020d0c021207031103010b030a0b04 79
    0x3903940801e003500e0003916100b010840f020108441a00f032044407903030007101224540207a500d89000704072544204681d49040000010f80f01030181880e4101303500401c400b5040003246140900024141d8000300700316801542026144001f00c3d24500500302038410a80c2140a00c0710306000e000010102e400c0d910703040d552101d200d0030b01301c0d5001d480c0603c250b0722038a40040d00c0800c0e2040600b0008140c000400032540d200301071115455060540c2d0b0b1041d06003401c0c01c400c0c41640d406900d41510780d032000b884072000040c0854803815200180d812a84270303904903080b0300400c0b50b02c4410300c0203140c11a13130171002c113000400400c190804c4854103150001c0640764825140e40791031108c00c0a00c001900c5054031400104042944085100503600c402c180c2e0307001d8400354140094030b4010300322034501048000c842c40ca00b55605d02c100240d441110350112002103607a460850300d445101c166039486546044101c800b0380c02e01051810805a00034050950344c0c2d6240e641d070001c540d83c1b4148441e00d61 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 528504766 1250 528503516 528503537
    0xd090e0f041a070315050303040f09110705060703151d0420031905070f0b07020f0105090409050c10091a0d090c140a0b19030c03020f040303030915020f0a03020703 72
    0x94800382c0180110580ea402040308480500f52690a9106501c0540654001c1108100c620807032080101607500c048c0000c51078502e80a9031602e01e0080d400302900354010b80c024042d0307494069008580c203207031450183d1100c95480622202c02440e51b65440e0304d601006000400040030003210310310700035403414100020410700001c2440e02400541969100441460840c10302c4410405e81c0002d00c601e46864429904120401c10075005240c8020300400c40c5101e4201c850b8003c506031000303680c001d841000302c0140713414030030780d0303509a003900c00d004031a0149000c0302c0500c100f841c03a090703850040d9444640c00c40111613504030380c00040c18492560ba15040b071b40c0010b088060004c000d000d00090580544120f204010554100741d0103001224400c11100400c140c070300c1d010007030260850500096003096004284c2c0a03108116846020020000d000700405030075500021903640280c544000d14105500584128440d5000d8601c4007131007031180d8166103100750002c105040c03084c544030b00c0c1d0b903 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 528506016 1250 528504766 528504803
    0xb1611040f06080a0203010509030901210f0f1506020106050102030a081b0304050f0606010224040203070e01080109060501150806210d0f020d02010b0604180b03030a030b030d090e0f04 81
    0x114940c0c2c12125240d00130100c00d9041d0702e001d014054111100130090340c90a1910400640b0030b40c6c2503c043c0202010305040c0c0101e10040e64401e00201c40b40700340038000e03040d6011401c80141500c04031090303200228000450305620511680007a207406800030752821010900035035411100a00c0c00808260942c14100c41c3c03064440070314040c2c0e2083d0001c02404941c2d1000c40c2c241600281214115401880403040001c141031030407880c500e00c503140c80410740303172400401d04018841e081940e040702150000580301c0c10550259050a008030010441da0340c9885968104003021268400000c0c0c03481c01041c61480c1581c42540080f07a640c1007044500d04226020b030802448a02c00400314600c24a50745440e6010b2000c8041c04103280b008001040d400c1000a0310381c0118040d91080011050801046111580c0014104440101120b07241d031070100004001d08414800c2d03500901030319560f9013515004100d1442030340d92039141013841d90398072030417074125100060083d2414000c1e8035450b50007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 528507266 1250 528506016 528506021
    0x1005060f0c030703021e12161a101d060f120a060908040302010318050a110307030f0c06090f0311060f09330c030d0903020a02030d030f05010b1611040f 67
    0x1404d1194026281c021802580803080c00345001c0081d40f103400121100c0e0f196103410044584c440e0030507881280400c0309081102903208002071001c9103100c00018040e458110024100480350035801d501d00d50b01404031914540501a0740180d00030721840c44000303407031609030260300c00c88000d1f00c22101420800d0710b604040e00c41d07030503086e01e00000000d424019560704d4001c0091140540c0c400900000150b558295103c2e40c94201600760f0290340c00c3c014495405100040056801035605d03000712980d402c02c9425068540b08000114034540c00c0002c441d40104e5008045a8101354603060030510341d02440203507400100d2210304510204040d1031030344c0c5c41421f9100c1c10000c544401c840b545207009064400651f2a1045a217200f052291609451000003100e58813400c0070300220707050010b45026445e000d03100d200203505000303d501e00442c641d1700d9800132100c1882800c0501c07459907500c500902921408013000c03080c101c1407903004049140c501005030081000340c000690100c1d111681e204 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 528508516 1250 528507266 528507277
    0x30c0804121e0305101d04031107150518040c0f0f02070308220503062403030403050124090209100302030717010602070303020114070e130e070909060e061005060f0c03 74
    0x400d665005129544000000d4440a0059a0380c500c48100c8100715006c080c0300018002410007480c2c01c1c01880900c1c0902500b001410b0010b00101a02c0010902030321503080806031105440048400329140c2ca000c2c010101070a10f1500d800500f0700006004440100300c0c440e0520941c400c0b204000f0024407158000c0070801c21000540c00d07000841c11740710b41d40c205a54000391007684201d081c402c08041e03050001940610701c45400c2c100388a4080400d0035030141d0350000c1c049500e000a10044003160200c0410344518207091101c6040e11017440c0401ca02403014020b030000413181c0d140302e00e94000d41c000c5801c091301e0700742011209202c41d41c0e01d000c10000d030040070058024020170402c0607024000e10b06031940d010004034141c40d00700d01c024071011b03100ba0218441c402080300220403903019441181c0000e1a0780940300d034580c403180d07404090f000d0a042222060b1030071030510711244003c204503000d004081e8104400620340010042e007504081f4000312209001c10404082003010401400c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 528509766 1250 528508516 528508577
    0x8043e01030e070605030c070501060806160206090d09270e0d0e0a1404020a1407050c0108010512060c030a0b0a080a11060f07030c03031b020715030c080412 69
    0x420118400040c25541c100060361195409490180002500101a030750301400600d81a600c811440c14102c0c09003900c2e40c8031800c240240c0d42842080c0c110040c0f4600c803141640c080350026207810307500642e2807035181c1c6d035980014103694080c06617001140742607050415110144000d5105400604204d507481c4003c0810743c1c1c07040c070300106100e800c4925109250801c0358000081440c015100030459008030442e4442eaa00044164a0901602d111204082d80b00841a00c4003401c0c601107030b8460084040501140080e030000800b032804450802e084856840075141c1a2a05c40301040341743c1029080f900415150705036040d80f40c85600160300107024903401084084142c0c1052100042c54201c00c500420042040003843d007002411100e219505290004851036107040440007002c42241c680c1900c400b03000458050b076400660395060b184150b204000d408003128064040351208801500031030541000035000c11140015680c4d400d10751f00704200640c07a48090045007507550700810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 528511016 1250 528509766 528509873
    0x30a0902130905071a04051c1e02010206010b07110d03050c0129120d08040206070803330a03031b0b070203070302190804090e1507120506100804 64
    0x402440b82c2005010020002000620b18400c513000c00e18416100300c0c000c1a00440c1236090000385064954494000079812001c84001c00004a00700d820324090964140e005105910020402607890000c40c0d040d40c1c0d020000b00e844041c04002d10007007542d03500040d010701c441489001003075102070060403d05840781c81c4c1204011200000c41012441c0c080205010f400d00407051955030900140e15080034040d81005502e640d01d078030000390f440c41101d1004008140110520801c0d10b20022050b00c1c4a0803194204240d040c081ca01c160b2002000c134a04d90711213030100d820000319004884002e402000e040e01408004480c2e2a0740000f014252010030040e4030000d080c006240c1d0500c038880e03410503e401c14010910140d12002d0560244d80181440c4645d41da00d61017045104200025a042c902c1c0505850340ca01a0700c080c0010814011519986007000d0020ba0685801031850700219010b0b00d0f01026521a500c0b00c40c5100c00310320102440c104040384840301c06581000c1400c80c0400440325 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 528512266 1250 528511016 528511031
    0x3010b0912070b032706040302031c06091b020d230702011107060215010b0301081b01020c090f011406070215070203030d060315390306090207060e0d09080d05030a090213 75
    0x42041d010080107101c0b4175400620a210005c0e42c0803040b40c0d401c07111400c001c3c0d00100700a0035032009050310340c00b45140384c1c50301580a4800203a580405400402078080d070349502c0d24410141c501403580c600848030f504c86401c0200400c420007010704516401803501c001255030100c6014541105900043c0240c0e2103221206812242005401d0142900c04521410341d450012100d0f41d8403102855000d8010f105401c46400d0b0344200441155040024441d07c25402c180212850424080c05405203400c008034000c2141e08120044803070780c50b400380c2909074011440f180010a41c0042108070b174503001c2040140c1c103070100e0f03014460155000e010000805c1d0400d100c490220758584201d40c03801c161901501c0c0c0c610050258114410350fa80001901440703642d901100104103981101003201d1001c00d01e0303000c0c8030f510b038403001a02d20f158003191051b0304810010380382d43c0c0491050314015405030036109180d901c5240a075400c08070340304010451807201c0e03000880d03c0780d1007448013008a5403280d6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 528513516 1250 528512266 528512311
    0x90501090203091e0316020d020907080a0e07050f2103030f06131a13241401020303061c061d060402130b0f0111160807150503010b0912070b03 63
    0x9051501c01058a0900e000070100c2c084c20b0300c0e03001d45000e034142c10714440c0c072810954682c000200303001a80108104400d10b00b5080140c205041690030202091600f03103207803140000011900150f50b4014203000001405204100704984450b60303429280c0b81c0800d44000300d04c01000a58010440400701c60203528040c814003072084862001540b540b410000d088080b2049036034107202c111002c1d1001c0100c82c0280b030038600a0001d240d80f85082d103082c0301d480c0d5100c1030301d01030040030b0390341110302495100444401281d49000680b00c01d40d02c10b044400028002418514044e81984100c0003c02c101000d5a90b60ba52604085103a00070780e0000e8080000f18a001d41c145c50105985460030410401c6100218140c4c1c00e0541c480f5051160240a4601603081004000c100e0f0a0708038241e1111600c410340a078903003040c0e00c62403039940c0710216411101360003042500e050310242d00081c2d0629244a08000a41e107c91507003030218001c0c1030000c1038464000e4000d5100b030104142a880305074440c403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 528514766 1250 528513516 528513523
    0x1e0a0e0717160e04120c0203071712041410020106081207060f151e03020301060308040302090c0301080631112b030806190f061d0a06081009050109020309 68
    0x484048040340b901420301500e541c65482c50b80181d00100c003003400c0b11403d1401c5d602d440807600003030b50511841c9000103480c14a04030b810b8413502c00300161031050403d10002032681c041ea0203034010621072030030743c07110a04040450003a40324580c400490303a59915038a00e824441d01d510040703101d40300028504140005030003600a14501180c00b0848200540b01c0c886000358039002d00915130000a4400c4076a084d2190004040c5800074005c102c0c1c250359180c003021540c444e00c0b00324080c2c039041001400102c64102524101c0e8042c0c4080e041c42d582c2c0c05242001a0260050b103001110303100d28030007805000310108483c0c2d81c1300c0e50320140314586d81c20800040706101e080560030107400310340444c0c00b510000c182803185941410320b55903c0c2c5684000408101828900d400c0300300c3d44040000d500c01121450404a410b962034200301e42910352507810451455010b0207170000c15090080158510034404103520404062010064039254040c01003911000c0c0e00001d41c1d1070700881030003136000051 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 528516016 1250 528514766 528514783
    0xc030114060c0d300905010b060313030e0103060b0a2a0c12020301060b0c1c08070f120b060703020708070509060117040203240a0c05031e0a0e0717 65
    0x894889081002281d0aa0340d929641c09443c002c0048003244283c60f8901403030080c04140c01110f00700301c03d0360503c44c41402030044082c19201582009121900c0d41014003c0780d0003401c1180310200400300e56103046c0c402e0603040000504140d607424001070306440d07800c090b10100c411543c4e8142070007034000c103c0394101c2d0403003d000c5200c0e41e16401e400000f040c01030a03c0c121603203410050b040344c0f06800001d00401080d0700021500c6030001d54a4403041001c0381094140c2c1040c560288000c03070704030040b01d01850840d4610302003031840345000c0ca01402120f00082110a401c030201c3d040003007802040058021190480260340010310510610606100e030201074041030f07030540305618001000030124001905866658109000440c040d500c0500c1215082c41e1054800124000034032803070105c0f1842100e061805510b801d07000302515108001b240d000d10004148240c5045032040118001c20014281080495031090600e0107480c0c244403900c01001c14a14000046039812500b50030500d60 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 528517266 1250 528516016 528516019
    0xf0f0109051603110409231302060f0702030c150d0e06132402040b070605060a060503060402160203101d0a020a060c0501021b160501020a0b04060507050d050c030114 73
    0x50408002c105082480508800410741c070303010030705460704600d080d1075110303e170442182682403c2c06080c801c010140e16121124008400c0d08035507440000111000041c007200035441203042044010003840c10001d804510b00040580d038091815400103107041700803d5040c000010081108000c0644034403846c035902034181c01501503440c10f000034074002003d40303070300a1014600f420012032101c40030b0021440710406031000c41d07550342c5600b2a14601c0d00040011500f0504000008056080c064404421940140c50740c034159210300d0200b00103504207481456020052000900150b681008000c010310642d590001e181c0756a0f45080c01c0b502140600b420469006114480050701d0b0b164086048501a1500c0200504c01c0e1902c103002e44100580e80d4a14012803c0e90028184045800e0310f69500c543c2552980329507400041e41c60340741c0c41c038014005000140c0000d0104615811a90b4442154a452854030084078030320000c661040c0c5141e060004044018004407200480d840f545510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 528518516 1250 528517266 528517271
    0x180b010302090d02010f140a090f1502120c151e060a0605030703110d02070302070609080d351e071e032004030b091204030209011403150f0f0109 64
    0x70b000402c0340400b000000030b042110004c2c41c00f920600c520310408424000801a607034030b9884000041c42040d0310302856083c042d802000280788007004032032095071504c5401800c0010148014441c841d08680e11071b0b842401541d00031154070780074038840d900c9000c40c00d03800300d0060f181c0281400c4800000341128094441c05074140720254105003600c0c2d2080c0140b50210742180011202d4640d405400c41503a0f0031400403581004040c2c000c00d0307103003c0c0c91071940c9402c030040c8e850703c2550fa907079101c3c10100b02080503030700c80444d034000c60591170002c04100c4031400041c0c403941c9040e250b2000c00725104043c01d13202042c0d010740d19403040b00312900030180345009405c5012507401e090411310b800d58a84141a07444825005251030141b401c100260009402c640340d90740c03400d0009034914120780b40885401011402d507242c000703640940d01520b0b0054500c80345a070038442840d69007580c540680d0390510503400415503052140341010310843c805283c1c000c171820148003082107040180c110b042841d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 528519766 1250 528518516 528518527
    0x3d1e022803050d02090102030405092707060c0215070b010e040c0501080c18210106090b060c070b07030e04090804080607080606180a03050a050606031c12050403030f06180b010302 79
    0xd074002d06841010561030001680d50700a0001130789075110341e610503600101100304019040004002c2c21001b201035880034031080f0702a007615a01c03400c80d4001d500229100030041c034050b00381415040c1241c0c00c035441b42480c0c2060341d1190100740b0007d9020444418508042100f000004c02d040c00040c031007804c040d2500c0c100000c4103d128016001c50301c0c88100c9201503003003140e82c1c0403d4101e45400030585c42c03180d0500305808a029109a00800100c1400c1c0b60b6a1511818480203c40c480794500000c0c01e071450910700c201c03000c2d82c4006001d804201c40b000542c00d01d03540c0c6101d695011440b9514090391145028102818150001d040c0c03402c2c04840300c10031041d03407038413401c6816040e403105a09401c032945800007913501c2c000b5040a4a0b91007644074040810078001566802440e0131003c0300c0381c1c1c000900c03606900300e01c0b000b409000501a081030840001d520b4001a03000b900c6030030003144a401e400200001c9034815480300c0416980e8030078010400e0403e20038028600e2003840c00b5450309 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 528521016 1250 528519766 528519773
    0x31b04080303180a0b0108011a01170103240e1506010c150216140309120a050d050313120c0219030f0b0619060206063d1e0228 56
    0xc0c00300800c00040001100d920100f8a00144619030f07616900c9401901c00707585501d80103001f002d142c2d03d1424421205891104298040e9a00440390b41e104540600c1c2a82980d64100703000722102d84503100e164224006078280d0341c0da401092180003080000b402c208940c902480c0750300300e0203000b0314103010f40703020079202044800340074030003a43d919100942c0e02e480812800305919107049001d81010070760780c010380100e0740104c01410120001c88400c0214500214020f03191007404800034a141e0001121340700b031070302a134040d6600c442d400c80c16454908041d155510714901d81951440003c0000f41c0302c3c400c500e800700c0d541e5044200b030741079550041c0c215906e04810340c0e40e05a01802c82007c100004045903240d003c90400c49500d03c50885c84a940c50601960f28842561190b228603107541007882c108158141e4036845180600c141038061440000c81ca011602140d1702004000c81d161240c0c0201000703c00b8000300d0400c0c0c1d8010455601042d4444040c002e603813402c50b218007516000310012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 528522266 1250 528521016 528521023
    0x1401050a0c05160303080907050906010507110103150312140306130207020f1206090105010909020d2019050f03120f1321051015061101060b0f031b0408 67
    0x60840d824881c1c085140c5042203898000d09824041d20b03600410404000c0581c4240c10900401829044504140e160010002c0c03589080700c52a002600a000500105100096840e441001030400042141511000d070207440c60641003691010024205001d005900c102001607201c18000c000e4214244030000949072050aa111204142c011030000103565035002410300c0000000c050300c1c4400c0009041548420040740e00031404e51a00000056000e214020001000d5004100400d2000c82c0d81e5401401d6104418540a46c034508241820988901900812000d41e1044021845180a0410040c0f1b40c000b05664000d801805d01c40c403030300c0f04c0c0300e090751030705902c00c1549a1070702440d1580041105d06070b80504e01d1045034a00044584444400c00318049000300f06484800c2e0b26800b2a0741903e003101e111032003a462a500c10007449100d02030b0711525007901000407603281d65500301d0800541001004020b100e00005c00d0001010030214182221002801134174200382c0740151591300c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 528523516 1250 528522266 528522277
    0x412150606020c01030f1b02070f12020d0b090a0510050105120c060301090c020a050d05030403080f0906151206040b1608040503031603020403150605010e032b051303030f0207140105 80
    0x14035407981b88600c0c40003855040f6107180c4107841119001d001041100035600d00061040d8480401f00a002050b05080483d040c080a500604045002034480c0d88032003035004010090349550144107036030000104103200d42da0044411010103d019410301040000c64900c8404040c03450703001050410081d10f40d10161b90444a0619002545440d500341c14be080c4008600c0c020940d016000a41c143c59802a0156001d54003e079203018031555100e00c80004a10b080d203c2034180d6108200080040f1074114003e8a0000050155200d6480500400e07107090019501240c50100703510070800403009000320b42c44156424a0800c000d801c05442d4075481c0e200150040c084524800246041203009030111001141c0c0b01c00400307858440d00601400910640c09a41d0000300f0746d0158040707915001900000100806519520f40a13541c103010311400303401c18201d400e119003800f02030b1180d410111031500550090f100c503442040b0140f0000c2c01c1104940001000101105c0a8052668403400313956 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 528524766 1250 528523516 528523519
    0xa0b0411040b09041208070c050a0204052206051602010b06040603180b0106050c0714030c0d060603060c0503071e080f060307090501060509150703051c060b0412150606020c 76
    0x2124116040228000d80189403507a600000880f0603c000c002c680c1d80b46003407407119950340d4030380c58441b1441110400c103000c034090500c1d4030180c0e03006c0161400754000b6420061122030060a000342444604450740a01400c1e07076403665510400140300a070110303400c201c2441d0f200070001543c50170300013940e902480c05941c0400d50342d004442c2e40507084c40d010300041900080d0f420555a074030725009010f5072021508074001d01400c240000ca01d0114820340600c0074000340680411030b24002803110000c0b1580080e11025150080007010954901c19003a000186580e0300790740b03150070040034016940740098500b054110f031491000d819072012820b03411034044a00e9a10740d4480c040000d00d0304e0240d402c00c0107100e1a045c00010402e8000300107254144098440f04117096a43e111902140901c1c0d10140100f181000b10255152103d10000c0c0700e10042400011000e882da80c081c2110340264000c11340580c074880703108090011054660f481c401c80c0520500009080400013502c4400700c01246 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 528526016 1250 528524766 528524783
    0x3080a0302091c1e080a0e06040504020a03090b0f090a03110102211506070b010504020306031f020a09081c030203090c0d080909010816050d020a05210d020a0b04 71
    0x5048191094040341c440103030003080741c600365441400d565a03e5030300e11401c0310002c0e41a200b080b40c10500403451113100f50000340b6a410304484240030348821b840d106106902100812022516a569102401c20801965400503a60185140003217088070003401e155601c400786403c00508840c00119103441591603d030203405000900c0c0360a0281c025602e440c00130700b0325660317080c0f0180c00baa642507118078049071550403c444c5540a000c1c903441031207000b03010418950010311860500e90001c43d003101000d000c495107509101141c441c0d82c03008030000448690005100e083c8264440305040140c500d10010700f445045038403214612405641017401419004000980303103c2c5d061255984586004e419910241c0103803601c440f150b400401c0841c4030b50301039030020400110026a84880e000e2a0206020b010f0070f010030442c4440c0101c0040b40d12401c0c0800214858a6203052103214412100c1039221000058601d982482d000803200b004550140780d108001c94000e0011070303007068004811 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 528527266 1250 528526016 528526027
    0x90e061f032915010905040e0312040c030f05070503010501090608150709080a0f0b100f330305160503190b0d02150a020c0301050f010b1b0609030a1205010e010308 72
    0x40754a8200c0000090401d4001c8000c00078200c40301c0d43c10710035415003683c50b500e400e9100c008110880b800c00440c0e03e81940144010318095503289580e0790424001c00c4903540499503603a541c41d0740781400710304959903040040304000c2428240115405000c40c030380d061001d5414085915500c10000c40a2031a040e2000b0126003042d004e054070401410504081d5039400c00c00e42001e14119240c0e500441d15031448070002107000707240360451404e441901001280300e91900c1010b00c1c0f0307107150b5119a650b2440320400c0d03000e4034411380084c860314210350311301158502d043d003001c010f810038000fa26024802d00708100501070030842001c1140a61901c4001240d804420108a0705001104029040381940409007450f85401001c1c084c80d04240e801c0341d08000340b40083c142690fa0558085c81443c2c0284014044800943c005c7c0504030850106103507401040000030745011401e840c550601c0d00300240c54141298890091050704014441c24482c030f5240c682180c0d1040014840070300030034004a10b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 528528516 1250 528527266 528527303
    0x70e0702150a181e02030606040204030203030403080711040f0e0607020a030e1314010b071407030b1305030c01110306031006140f13050f180604050a030f0201090b01090e061f03 78
    0x31202a040d000140e40c858288144d072a20071000e9155816482440b170440090300c5454030f0300886041c0d1764040c0180d81010310316510441b141d008010b0840701c0425030040d440c0c4907129840b62081d200107290b0080b400b048a50308280c104540548113004640040d11503d010035004600e01041d502c0070703205541c40c0350b1600c0346030005118560560003406180700000611030900c0c406041d501d402849090001003400c145203985012512000309608203043c0016035100004100d4980180982c2c240c0c0c0c54461034258a07400c460701044010a4104d002c800c2c04681c1c1403c103c0805810001081086040e0414080c45d00d903184102c40103105510001c5906503584440d20860180040c154040c0000d04200b42004040d0200721800350010f036990250580c041d10020301c00d4003a54012003e800da10599031401c1b503503075a0085a41c402e56407140411000941c1c1c038030009008041000700019420304d80d1510340c0c107004011349002503450f01c03d001c1d02c610700f880031102c00c00c0720b9005c4144040c0c88a41b03c1d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 528529766 1250 528528516 528528551
    0x1106040b16090e010306020d0e2a01141207081e0609060103021c0c1d01051204061808090a06020f1f0b10020307060e01060b090909030f0c070e0702150a 67
    0x208540c50320210794000000b0840d958004e00080d003007881d024001c880f408004d20782d1740c3c0e0034ac2100c030f0301c090500c12000c100040c1c842007102d1120010714014040a040d20583c0003981e015450241200e590b031410080005ea118607641d8001503440a860401200c02c02f00d600da1010240607580728400010220320f013680203504803640c2800b81a4200300207961500c01e9001030a40c2105003003c80c1c03195140e18110808494034110800f01611007034144084030000d00c808043c010803c86480303684441c06040c007800b0b1180f500c2d10324860420199078034045003c0c03040f0710310103911000640d030040404c00703035a1801250055a0707031100b4803828074441c403141802c0003070420305d41c40c2504032981130b0786401c00070b6001c0010031070f05005120511241030310048440c01ca42c3c140c800c1d00c90404091105171b10710b14100a0f12034128810008032414448501d0006415620088614516a005600801c41100540c042503032019032030025140b00b03049000780307800490005061482050b07807200081221601c09 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 528531016 1250 528529766 528529769
    0x14100e030c0904050604050706230a030908160303060b040518040302030d1e0e07080d030f020d1103010312170a1d060f1902070c050f0112020c0c011106040b1609 71
    0x2c00c1c0150508080c14003903190001950144c805014036040860403074069840c500e082d03800d200218102000084039080d003500541c10240070581c0350104900820341c2803000e030840e5190340c0280d00b4100280d180180071544207620240c2d012006020802595a90f2140c0300d2202403c01400001c0380d4a501d8102d0452241c0706101079514606849070012030f005601c00307540416280410413001203000f0520360341d58030b41d100e1218a035100682061059201c3e400c5003052500d00031001d030600b9582c005440c00d44007210903220100001200401c01c1c4418030b601c842c0d02c0c0c2c80c2402c0040c2411080c0c51400042c200081040c0ac0494842c62600100004862506038840340364069400b60305149140001d241410303034032003034524140541c5070f001c01d42d14422200c07082c1d40081000741040c0b0b07041c00e00008100c01d500190502c010701c0f50503000c2800300c5c00245030314008100586018000702001401d0300c0500b1201c2c140e507178018002c103c0040c600c40e84044c2c025641710301d4000100c02c1340c88121a0704410707 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 528532266 1250 528531016 528531019
    0x1302030414031c051806060f4501060e0105250501051602010e0304030605090102040b0c0703031701120b04080405060a030e010b061c0203100909080a020714100e030c 73
    0x42c1c820700c2c040d00f4200c80d0201608070001880350341c43d84802294425101289180d0541140340840c405e481c010010b21500c14000e0543c0404511400c0070705206031a4013001c180b41c200c3d00d00c860071100d02c100700078045da5424107d900465414120020704550861a0242c1404000982039080241840700781c244c0b4540744000541107030709407030001d02034981641d50184000d03601035001041c0e401801744003c645e00000c011400c00e440d6403160701c0902005051541195401c01002c0f4103070441600410043d40c0440040541501d14036008040c10b0313850018030004410782d0014044c0131004c0c0c2d080340c4600e40060750b220b03540e00c1d2402c150410340705a902203a071002c000030381050714541507046821a11705e814000c1016900403820f00240e803044201008030800e0000404030807240700e601a541040303d001ca4140000e4841c54203074112078080700705850243c4081303000e02c2026030412909001c1d09031031410904032282c4201042c5508241280e10741409a241d4200119450400808101c03100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 528533516 1250 528532266 528532273
    0x70c0e06030102122e0828121107090506130906110a0c0203100b060a0804050a0c06050c010f06030305040501120b040f0b0108090a05212101051309021302030414 71
    0x5020804030100d0101c1d0003255850405d00c0020303a08076151408540881d13134424090440107a0340c202c982810b4000b1080209007001020000e07010841440741000341c2500ca85403501c9904101d8102450032540e540500300c0b079400d00c410091117486850a2020b028488900800c851115182400107800d102003810b010401c04030302c0c403071200d1344100c0003580310380245c050f594500c042c140b10301c0990f5001c06400d81c001c1c0041050fa021648101c240b543d03c18001d805969070002030ba41d90410120241d40020005100480c0d140310614080c030030f40481c2d203440042006494550396024040b4001c0d440780c00c0c1880f0088416042300f482e01d400c80800c83c88002c108003c803031004000d840c01414001c058500141d101c40014854146c00180c1c0305035150090018200c14490686e528000c1000e14402039105800344510300b40d00038020580810064a4403080d07c007503050405106412010341c0c1030340601400e003407048000d43c031038071b032103d00c401080040035a0301d035030314286000501407140f1192010320 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 528534766 1250 528533516 528533521
    0x312031b07060f381c02120a030302180907020604150204080a0602041d01032105070501090c060e0a0e160201110f0a08010611063601050417070c0e0603010212 70
    0xd070101c121004444c02c00c614080e04000130007119405100103461280c201c002400040b5885408903505c484140c80140617514038410201a24100106107204030040b1360007007059242005814a08040c01600340d820340103a152556000b03685600140002d007154a60004565000a1603011107010308448030071510042400d182c0075000b135200b4850501d508000360b980a0b00c803021028000e0407030350020410300200b91407030815180495244c1e510410700c0020840800010028017591303001e0b5000340811042c0f2440d00c0c002516010b180021a4455000100c003405140c0304100c000c1e8004401c003044186100b00309005900511440a038a501c41501160001c0c2d44400307240103001c450034594400b6503691b80d48500740d030000c01e8000400750a030071140008454050b00c049041050f40c000c1d10685442240f0580c00512444a00d8000c038280d44602c200824030036400100320004000078062882c001040c2c5507820060740c0c1e0700402c4000b240070b41c00f040465409405465000c0240082d003020f90 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 528536016 1250 528534766 528534791
    0x261608030405071a030414010204030c03210201060815100f0e01090c090b120603070306060f03061802030a0b07090933060203030115090e150312031b07060f 69
    0x1500212001c42d80c603c1072072800304903403544180c42d00c501d50312401801d003541c85958424440b407143e0524034855650911000000c20740407034043d402507029000f4100440f4040b4034000c555001d400c500300a580c10001e00b001903100010308481c0813800214180c220342c80f00401100900b11503413209070001101000407504400c030b400c450381211030f0400104110f21040000362090142c610410324070304010312148140424148203560300420007421303504215120366a2104645841e080300c41d00c0740c0c580342d046c41004401d211718120780108000d180c100d0f8500ba40041d87c0d825040d8801400ca802400c045140301c1d01400460019040400d0280405038a4500e444100c51032070000e2100781c04102d220400207002e8140c0c0d00305640c1c196010310301d1a130030080750b0040000010026400c024880c14005100481704a203c2d00921560410400001c1c50b0300400d481e0180140d84912113000030014001c2c4d80740e030402d802000c00401869561a5000381c10800018603400305401c00203402c02c04005c110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 528537266 1250 528536016 528536033
    0x10606020607080106170402220c0e1504050a030f0c0801090f0201031b020d030506121005040303050106050c0a021014030a0c0f031e020705120c0a1109042616 70
    0x94041e540e0750f504181e0b6141c204132100001840c906a90084060101e005400c20442c51044410788400b5280078201014042c0d0440b0103d40322240020381c00520f02156290035102c40701c10b04080002d00d4189410b24000400c0d038180e620006181c4005400168201f01c82ca5241c43c000707100c894000c1040c1c0441d41400540d021440da4200c0c0040d240400f004000085941c0000544a01e075004105400c103099099009120244c5600e81c4104030500d640c036043c04c10000780307021420212000ca0541001c2c9006002d4401c10b821040a004081c8500031380c2da000080e1000c1035540440e491481d1103100e170815600c0c450fa0620740d80c0803a0000007045150f0030180c20204c0d143c425952485805083e1080403030441c1c101c41a4034660840005036a245034403030750050300440e40614251485a0004c1d4040b1380b850748520b203010740540044d0060001c1c050543e5044c80c41c80c205aa040e03800d8130b040e85d0f81940f50020601801029804800e0081e4400d0130101517802039240d007984050165800d0622000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 528538516 1250 528537266 528537271
    0x303150d0f0c0e07050327010608031c060f050315100b030108010504031106062404080604150614130207060603080a05090405162f0601090b040f1505010e0607050106060206 76
    0x980d1a00c007000302e126640720b041282d124054016105d56040c191841060405220089000d015900c3c9c1c80c1c0865081001d1009010040070f1580100120b03414220907020303201c01c0d50102c0e49103443e07600e040245440c0442c02600301e032101d1840b10402e0782ca0a0f28400080710a80010501420100000c2100c040c1503018502480c0a5283c092a0110100a465507050101c03501500504003141140d0100c00c00f041c0c002c41da145a94005041c247ca0b104814545407040f10180c40c0c00045180c030700d0072500a481210042c1c0b5518030215842011540171603003020142c00881411b9070f002a03150188a80340d070010b00903542c81088159983c00700302004082e034000c407450310300c03c0d031404011880305a4480b100e0b80310070441c1d4590f92400046114410b90850705c1c048843c03d0901c00c00c280c82c100310020b000480c087e0030104030010b07101203d031040c00101c0d00c6051015401c0c07841c20741d45c00454602c5003030a00c00c0741c0c0240f80c000440740d0004082020383c010040b00400541c2007081c0480d045401040031807 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 528539766 1250 528538516 528538529
    0x60909140c031b15070203060a060e0c030105010512090319030608151b223c1403070b07050109061104030b0703021b0a111e030303150d0f0c 62
    0x40c1c1060301d46040580760320510014024031021803945050504094040ca1850000f0030041c605100468000c00d0500404403045c40009035078000a000818035501d181d0f17080400c03200307440d0456040c0300c00a451407240101e14502c0d02c25250004184920800456040d0040080003c82141d40844080c01a00381070107144654000c041903402104004000b140c40b90440850080344003c124480e003800782d0201b90f400090304080c071241030000030648001001048034212591041d8080240060314000e00e202e8000400e01d40882c04607119024004501a50b0303903c082505801840800246070202c4e80c1d001000030000422510244041903002c92070f85400760b042488004e10341411540c60388500e000003044c540c0c2000209580520076409041c0c1c183c204400703401900d003154172262800d20310345011120003010b90404040341c01c1c901c801110441d0309418032250300426900103501d82c040107008001d4244081e401d01079642e100d420a01c0c10070f0f04410130403c03551050901020150f424050340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 528541016 1250 528539766 528539773
    0xf031009110d0c09020918010f0e0106030504020d031d100504170102040b030708040c0e16020c09131b170703030e031518070e0a021c0c05090607030306090914 70
    0x41910381030003580e14a4080c3c1c403900380c00d0224100504200250410500550800c1506103141c007540d03000d580c083c1c00f80c0b500040c801d1019203803080e003086480341600050101400c04085c04010380340d1019034107826900d400c040403950880540c03016050f08541c20b041d44074040c01000890f541c2c00800500030386045d40007062403941c801b01114242d11580c441c081445900b0800140903034462140503400a01c50f0b0b41c6403501940c1c0c0e030741041181506460091380f00800c912113107852034042000605c000000d070f401c4141031a103070104c0001100b0705070003e84112100003800410020000540d0040c001e01c0340b1080041c04140d5001d07a07562820301040380851035038902c02c0d440f803800082070343c0b4a0802060030011a5107020100d518051001c007004200c0c4920800400d049492103c080d2103a13009410040e12848030382c00104c80b0000c1c1c0403180311020320704910000b03810313441002c80e081d03500c080d59400d555224a241c128001c20300d9178043c40c50380c1c2c98203024400700466400360b2020803610324100d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 528542266 1250 528541016 528541043
    0xe30030a0507110d020916050931050f0604020d11040e060306090a05070510030f05090309011704020a1512110306040f0b09011e0302030a08090a080604030c03030504020f031009 78
    0x4e100044500180c0a03610109480018020102d00044031010400750720700141404804000f144011000e0192451170f0105800c0c5155400840400c80d00394065011007400030341400010300c101b00c1000b4090501581e00065a00350b4032480d82c102c041026510f040329692503a40c0c09000300c0d545800d070b529912034050940811500d403c001440101180c200001e440840e14200c02c003c3d001030b01c4000c250505469008009001219101c0c09115100e9040950790350f02c1000001800003241402c9039200704030070811b000260b200c515614040e9040e841c02c0e045100e001d96003d944030001c030400e4119560038490b0880c1400341542c091402854281c034280b12180041c4c5070340081e18030000d14aa0089049401040b1240700c40400c00d2040c60490614209240c803a00400d00300b01d6440400d850300c8200084015803070500d08142e60061203200003510f05820195401003030656900c10180c1010b85806c0440d040d90360b8030b8040e000180c00101240d000150000690010340160142a0b0380400506017 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 528543516 1250 528542266 528542269
    0x501030b090d090e25090602060c1c09081308030a02010b0f0d030c0212160f0b040305060a230103030804030e1c020603091e07150e30030a050711 64
    0x51000c521041c07030301ca0316002070400b208064601e600405252000e000000122641c034031811035034410030f2031946c4890009041c09800b03480c0080c054861101c00d4070400104400c0785034030303500e91641c0351507110102d410780d06410440950700a61300801c0350032142c2c010001d0458000001070841280c182c009120300c03000310f420402c840c1c0000b08403580000303035669800c2c0002d1040c0004e183c01840100308020002d60416510b19205141210446843c00d5031030610414607600c3c1711800500c07a20007068502411a5919070303d9080280c0080c400b181ca6000500c000202c20302d038230310070981e500943e46d43e669407428000c1403000155825008180c90098860f1541403003400a10500d48429450740024082d80c248841c07030f4802000c02402c0e0289100c2e00314510100c81654003c070010343d008000450070907440648080102403400203104520310b00150544a012282020082591000c00c038100074030540c1c02e03283d83c4022030440d140000103042c030340d5540003070180003c24090301c47c10801012540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 528544766 1250 528543516 528543523
    0x1050103051501080721060501110a05030f0f07050d08180c0307150c1217092109010201020706061701151a0a09120506160804020d0b090712060501030b09 68
    0x89541128010041101c1c2155002d013030000e030454010315003008080e10b08005e4004c071010041e200c11010303884540400096900c10140101840c4c0700015055030b10042c0c1d42d040c0e83c0c0c0700b500e080c00e11491002c10205090718910099914042e0030000381c030300c250078001d4004c281c180c00f200c0b0b841452081490b021608070002650342d1902d0000380007000d515050840d8150b0481d40c40f8100c0040180100700c61000541049090455803040d0301d8400c4440708101c0000c0c0c2040004003910901d82c081a4041d2030781e503040d80c500000302e04520304c6036520005140100e0192082281c054040c40c14450002910400202d12001c0c0c00d9580c40200980d40c8500d040400344101d622039000c02201418103906c00c1000d80004055100a60130036031401aa1401e5145186d11510000d84d02074001000300420011800880c0c81c90500c00d2400d245180380c82d50014a103150024005400002e0001c0003070410f813010041c00020b0511169a690409001d14000010307140900049502200e1140800c0c0b0501000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 528546016 1250 528544766 528544771
    0xa06080102071709150d02030412110c191d1b040b07080c150f0609100b12071b11040f020405010c060b010903020619020c06210903300105010305 64
    0x1901c001009212100740d8400c2d420954585900c0581501880010304500380100a8285000801f50301c074900360506405044018a610007800b4044a4161200d10007003422880340030102d8130203042032580310b03650440d0f10a90f006030303803002801c00140b86624080f030794440c03254507103015200c0e04c40030790a842009400381e8480c2000c540030511600307000407486405006842501d00484003608604030301203402c580c01341d40b075003500f01030b0406100c0705090517110190300a80400e5000b000381d24041d01e41031148549404e201800521b200400e00c514413a442d00310405491660b4501d01c0d101a0400401c0100340b407034107a210b00e18100f11000b503075003d8000e0380c0803154140c540d244494010340ba0840a460302d49030f95410480724078000300040e5550380140c0100e60102d18158400703041000082d00e41420100200d110b580140203950424007940380000107000380e9001d041e01c94582c066403d10b107001e60b00808074441a440960102c2c103801110814801c1120b0704e0703203411641da0748015404c03100b06 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 528547266 1250 528546016 528546023
    0x12061d1b010513180213030305040321090e060307052205150f10050f04030305090405060301050c090418050f010e070918020906190f230d260d02030a0608010207 71
    0x3c00c8040040800e036036a9161804106000945030480342900100c0e60381c419041100410340202c0d00b4814003000c000c070070105030314691000c0100782840c0e001401d01202da110300c1440444440000700507480611481004041c050030006c071503d58626a400c00f084100b0711107040614140001b800420400060185440054580900340302c00301c090203103840008009400744101080020004202031006100443c042e5460580b51701c1000100810381e03501406440c03080e8103250900000c080c424044500d00d0504460001b42051411044200f4000da80300c0a003c0b806110300154290a064102c1c801110340c0e00185d50386183c441400d0310031a00755681180480c0100c07040030703005060061600d070b00004000c2c010700c0f000c11224540d1004c00e60940149420650b900400c0010098542022504002400201082041e00b0300030803144018040007602105045036801401e0345044051804815102c0c9200e03603c509400d0f203040a0f6105603804803d00d440c10030001a0400d040c800d54445c140e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 528548516 1250 528547266 528547297
    0x10e01020303011a0a050f0f07060b2709070b0f070311120306060d14090106060807090b220b1b060c040302130c02010609020403030207080c040e0712061d1b0105 71
    0x4070f4800300355900100202d00612104100d507c4880c098140a07043c2e01321189255595100342d0b2401c2410740d0310302944103000e411441009000c41c400100f48200c7c154800010503413a680e1008190f161650981c000c1c0f120b03100c001142c2da030348420300c0c1c002c04116019496098400c40412852039858010240304843d00c801480441c01b07234600b050040801042c002e9010594030410320404000784d005485101c0d03241e40d584001c0002c1500402c080d9480040390400b072885500e0000300c1d5101d4444e545016200c08043c50300e0f40b42050159500364007a24000750b02c10f881d898400401c0c0301350950700d1041c10040c8924000507100392049400c803820350b680900400e100d80280441c080141200b60402410b40d504c0d101c002c12403002d6031003e04002c5010764002d09038289400d0b1820709020620b42c040c1c0c0918103241b020f010030140041c80f10102c5260441d0383c0301c400080d00382a0002d00c0030a0010f0455a104c0450000114001810aa44521040044880d40003210040d166441010107000920300d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 528549766 1250 528548516 528548549
    0xa09021e07050607050d0b120a050d020d0207291b10290d02090705070b0109090309050d080f0708030f0708090601061d1003020c0d0504060e040c1b05010b010e0102030301 75
    0xa1017900034024600a1a40110308003041c10005085100a44c1d00300700c40d036200842660034800104100c03c00d0702c048d80090504583c011000a4440c8198002c00c180c10941041542d078150b1056007941c2d007845c24001084e00c1d8003480c101d00c10000010420140e03680300b005049110343d01148214411943d040d4807040c10a15562928070b01884100f40c12076001001f4225440981c942e400308a108000c1590380d981d1340c80c0039240c41ea2242c1c006030025601a464100c03044002038028010314160340701111001c2c89000d1510381041948502c009002e200300010030a1810441520003842c0120701e1a6035201e0680d4503a1401c40d141481101e841d06254080c5004000a600400e40c0e45800d4250083e9004440403900200e04005003184032800020340c0010700038402c000074029146000458508a0320b40383c41c0c19402869842d11000e0644103d50354a04207804a0285409226655528032801401002824018001d02490200901192640055030001d40c40030007141c1c140d6454120020200c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 528551016 1250 528549766 528549781
    0x2108160309090c201c02013602060304140d0504050406050607030c060509070b1306090b0a02060c1605010c030c02280b090f0a120216060e0d02030c0a09021e070506 72
    0x20441d410514011190310000f6500740071081d100b10941500041480484890805102326485c605004600d080d46900d540d10603010007888030306a0100d4490780c49483e58100400e040b00a40140803a910511000598003a04400500704581c000c5030100030030f507904ca0905c6018410301c00c00800258107488404002221507100d281c01a40b000101c5010540b956540341096104500d4851140d014940c2040840d600400d9180030b8003011001e1030601d1141c0c500a0b50380d44000e408a01c03a00c03004100e40305910307048034030007850302d81281c0240942a82000098010074452914500502980b15144030141d5214032030070560038651100e5200c2c440a84448200c0640a40140c1e014003e40320207000c03411041003054480c4d80903059815554440100280c6010109007104c014441a42d5040200607000701c070b031011030b8400351151070507006540300290420b944099066032201c541c0a002c5002c0364280c1c080c19500b14901131021030b02820680d0b09500d8061140300070102e922090008504 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 528552266 1250 528551016 528551057
    0x90307061505131d0f060f131a070905040501080d0c020301110c1006141e010c023c030316060e010507080f06010c020a2108160309090c 60
    0x1c1e480442001d0720640302c000054102204402650250752110704519411300004e5003034294a140030024040800300300c0c40b4540790080240148160b001c40f00014954540300c01204000d07691101d80c00402e40b003504103c40c20640140e4000001900340c020100d0182000d03c1500d058a981384000c01d403000310750700d080783c0020035401c00f00d030555258480c442c3d0804003e005000c840b20301e500540701000b09041e4540c2103a10b154003103d000080412006926100c4805d540300c032249a211b04000000c4507801610090702d21180203400c00d170044520480d40c01910512490782d80807929405c540740304861450720400d0210240c0381c1c941c2042001c038034007114420300c032000c083c4200400b280c0723194044041402c40700200c50100c0458080d8081008403c0201100c0d80e006109003403601000200d031700440c45503011801075414004a1403045041166160740b02050561310004041c0c1e01c5500003045810100c480c48100d001c541d14070343c04541c0e03940a014140c0c00754003035a141907001e41000e40030307a035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 528553516 1250 528552266 528552281
    0x703081902160f03051209090604090f021503340315090c0306030210080906071b1b050a0501080403080a090303022101060912050705060a031404030807030609020309030706 76
    0x80d445410000381252440840440040c00440000350702541303103091450810f610fa010803c29480300b000501e11945c1c1c4c50002c5600420299400149180c1078035104001c1d0401c214060340c000d15418401e8003960b03141c001075200da4030012070b601d0000b10454007082c01015244c201c521310300035810002c070b00754070907880001d000040d402c0b10000a95250000000c0395810499400080c1d02e561082c401c1d41005880d80f0b030b000c2e005203000f0f525864580398441e140e200c0907100c0c1c01040700c91107091191915200140012a81013122440c4184130301258000ea6907107032144a00400a540300015a0741c003401041e41f243e605500d808403a81c2e0b87d240307010002d0074800c0d801c4003030544c2031004103c6c0241d1107195404985000004200c15410030030060304420082e4003010144130850801c0c0b0020344081800e600f1102c003510400d859014181c2d0550140804000c0407100c111303008100b100b45540449942e000b07400ba92000c02155484841e0f41c0c085e48012102c041695104000703610009803503501000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 528554766 1250 528553516 528553567
    0x20f18041b1805061c330e0901020901020601060c150c0f1806050717040e040f06050c03010e04140f010609060f05040c0c020105030c07051f0e070308 66
    0x149103a01e055001c140280e19010707010005803403048030350840c42d031209000c0c007410b021a0301505100b040708016581d08484501c242c5040d848005800145d01611404c108582c0c86035100b174500031b0790100b55105002980300c0c00c002d110403180032401254061084400d0110107034080c05d041e1b030806200752800b4a403e41b0484070400c0511610046004510075a401042103580d0300a400507801d400620700781ccc2400c0c0c0f030001020301c45020001d8580000413610080d41c8007591034580b1889042c0d108080c01564084807400082c1d0003040200f00800805e40b00c03580c81000100701d140c83d0601c540032640000d00a0003040c0000001060204d0302082900080d24821070448180b01a8802c8131130968100e072f44414a0140c8404c404d00210308902d05040c05484140c60800002c080c1d00c20041c03c0e040ba204020f03041c001d0003c00b0a0031100c45004452055800404464450315602402207450901c41b2035030303154629000300c1c1004910045103003402c494000c14000d0504410345002d9002180c0980240c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 528556016 1250 528554766 528554771
    0x100c02060307030207030f022e0b03010905010203092506081302181801050408090f01020a08030c180616120201090515090717060103030c03141318020f1804 69
    0x10006a6600c0c00461040816541c09601e4000300d19018004d03603000c4480400b55040a0300c403010004c1c03110030102a40c00010401080b8910b502813040c001e154502c10349801d542450146414403105400131805841c10750304035030031a01d0604035402c000350000c600641c403942c14a401c01415201303c0740319400103d001d0503414680d0007079000801e04d100b00744c5028541540c2d9010414007181c040d124170104c8000000902c00c44c40c190381c1d00d203017621940510621034062040035032031591080000480309a0300450442c0e80f4280310408a00c2504082e20b07440101c080300501d03590380c3c00c0403400ea42e80e01045a011001041d0320f5940e4035292030401c900c080031990384e2038015001c2641048402c000c03130510485a0020704003041d05508043d1150454030b9150101c00300c1c0003007918000340d60b504403505882d0540c1d00381c0180c40c0441d004201d442c1c0c3c90072008800714404450700d8040350081c0485514002520b00c0d40244a0803000b640038828075884940e8003805502043d5940310422500d403072000707100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 528557266 1250 528556016 528556037
    0x6280e040905010903090501051c09080405090a02120705040312030902131104031704080616050d02040e06010f0f02100e010e06010314010c08061c030908030a0f02060f010b0910 78
    0x104080310008441552140c2d15003080c00241a003086c00580071305001c1c41c01a140c000c030954100c003600444031a003043d01e9541c50400041c000c505e42503c0150000410701200b5040c40c40003800690415001c260302c82285001140000f4000d9045500300c0790f12406034081c09c60840c0c801e0300141412141640c01201d05110001000e45078402d1501c0540d0301e540140d00c072811404c00340c4003914500300c01e14220f80100310922202400040c103d0344140e141036070742800d00541c40c00f10b032140078181103c02240d0002c1808950140c10001c001d05c41c200a85c0d80e610400c10001c4101d07112400154400050303004481e02c441c07002c401e5080b0000d82d018100c004076503d0704800e06546028026441540e8844401e042905001828003030141004043d140062640c180400001c883c1c40d801c2c51100d44000c2d4031350107a000c160243c00720f40b008080e07000960392036081c000c0000d00210b0038080301c6001030240000248589240b061113134140d0740403942041c00c0944200a0007901c080181491040c04401580c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 528558516 1250 528557266 528557269
    0x1e060908060f01380d140103020a03080304060b090a0b1201050c0d0b010504080a050109140102090306010501031a040525030203160f18030c0e07020f1507110a0506100506280e 77
    0x70210800001131410795a10f902a00600080315030a91100d03c101519000400150b0b44415100068940100a40c0d0740c9840d540703420001031060b05c030701039003000b818010010500b80716800411b81d5a01560302d00072051b1038035009400c0310070450300e101a218003400b007010f40d030b0500c0d070004182c45010305101d0f00c2c03e1b4551340d0091401d880c80008035516034443d80b007401000b2408a03100c162041c0c1c0b5000394141014040003d841d1001402040e04040c2c0d160903000803040300c18880582d50398050010001824001c0c00c03200704109032001201c04002d1a1510010075100e03101710b0340308160f00f04c0044880c107030b0444100c801240b0900380104000340c03981c80f52486480b0959007030042d4860301c148400c261500390607581c00400185420203540010f074403220703010070125200c41c0ca0020020900701e191b0759040103840c00301c10361020304002d2052f0031345507041100c0003a40a028400032242403d01c1a9140b00300800c0b0b05c6400a40314440c0201041a0702d2522621108604521a401e100404801140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 528559766 1250 528558516 528558599
    0x7030203010e0f1917090a12050a06050c04050a0b070602190c1b0605031b0c01020c0a020f1c03030507030f0216110f0109030206131e060908060f01 65
    0x282c0d884002d4108a15080e141e64040010201551007411588010482c98403203030020000505d1200030a10b00041004455903019203007000b900c5090b10b0500380c107200e420881c0c1d58122030041240c0e0540b80c000031540454155064900325100205850341041c00c00105007681c4e045180e0441c0c15940a002880d0061490120f2100c52200d03640c4001003011541006401240f0002000004140d107400c14041a680f0608407640411061040101c03102d80b014503072984e12464100780029403010688071888900494100002c038003c5500c1c5410721a010100a03d9071280300030720b00004800c401c400d00080c001d41045e9400f40150800040d1411615000020390307100350380b41c15416410401c41d80c10401420300143e0301680c191403400c1c10803108400604058490301000c0c1c459030011410940c00c0c1103615068019082c007020303c18249180022030100120f141c011b08004c03078112240400e14200004010b031203010b507140748a10316460302d4400c41d00c10b43e9180720705450180d00c5092045812000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 528561016 1250 528559766 528559781
    0xf0102040303080403090e01060807050c0a050f0a02090108030a021c0e0a0e01060f020d050313060216060b09070311090906190e01170c24040e0903070b0601030c080115020703020301 80
    0x1e0700c86040f0740c541850002c0c140d060a07000f03003024944100050001541c0301e110164800c03110304180b03582d0ba424440d80703441d211b00f0317550061403031003041c40310301c84000d020035a09803540c030940c1c28401903620b0b25015516409010312150050344903030414010312089040c140b64914150801c00780540004000c40d5401c40d880e0012001c401129004201c0642d006000c285054407500c082c110128025600070068072024104e840d1030b8034000359520074840a90704480305c0d0046010b5040b101c15081c82d12030040d08419880520880c0080700207040700d4000d02812010924400c0014030340b91100013088480c42000e04903035001640701d900343c8507802e406c10504001d07002d84c19400d052f0f5032515122100d02e0203000d0511159810403132040f652500c6d030351080e546100c0d586952600c1e084415103c0d01c001e0140303900174000b020054050146480020004200c41c9024420641c2aa0399190040d016201ca46059000203031a80004100790b45158040403454802031054541d5540e880e0006425664070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 528562266 1250 528561016 528561023
    0x702031b18070c0312140720060f060a0f0e0619090c11070501170a05041403040906061719090203010204050d06062313150f0608071814060c0f01020403 67
    0x7244240414980c100c00703445c1c01d48001ea5400e00c000e5000d0002070186d60805403401052006110780301840301e90050f800c900e091400030885282e8a03022a6049000c1e005a941a0207403145000104030b810804d0300c0c04082d5524056048019202c5a05000c018040c0d6402800a0822114045010101c40c050f044c0b04500c0e03903a403604040b4800c40103030304095081d1b0201e414021002400001f00031030050035175020707816942c000b90380c1c0e5490400c17921020602c03826840717a010003d000300e21096640e2110059a03003c0d60346681c525a4005c069009400c2521200c00104032285144044000b076041402410300c054005400c00e40d40c1e10100311100704516044540350785992013032200c05840408040c096000e0450429440c0d04c0c4000702c0e01708403811184040030b5854011460f03041e0b5400d90214014008003030821035660750782c0710092000703605950480000d08429082c400c00c046907240d00d003d42d40d0094191075004030500420202d40e104c20a080c0a9010b00604c00020720428800b0740001c500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 528563516 1250 528562266 528562277
    0x12052b05061509100c05011d0610211104060308180f0a05010e3601080d0c02011b0309090515030f01020a081528050f04020702031b1807 60
    0xa0030000c2082c5224485091030303040d80140001c0c1e0280e078503030540016660031810528003041c4c440c00c225014001002c1c25203041203803000303508000803000480512900824452101040c0c65a4110580890074800c020412110044031004076002511440a8042c0284006280790352075035141950341080744050000c1185d01c0da030005a0034a011200300896049800c00c04403800d00c00080c1c81d0144c1c00100030b000d9a1400340502441558921882614010207882000401101003d080c01442406034089602428035540c0046000d4031b5110080c0ea4143c544051901490140021090100b80d0507002c200021100140210003407050341c0c02075502c40b10040215030403d0a00d840c14500701210241c030f80c810450710794182d5000000c0c81d00003440740358004110021000160b00d658156269070700020600b00380040b084215030115003100d20503603c0c0741305410b10f2004c100890280b404060740541007150460310300c02c01071240400c240c3c4020410140b0503064203008502d8031084450001160 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 528564766 1250 528563516 528563521
    0xd0e060711010b0d05060109110f0408010504060b031501060f0504051201020415020a1a041a090607030e0c010804080c1f0605150c1c021c03091202010912052b05 71
    0x10780c2802160040402500c41292034410745d80c840e42d0b980b20500c18110425a0740085112030104601104d030b0b940780c003010154440d0340718000d2038000c250550f0221109854040104802e00700429140080d00d0409803a00c8241c3ca0080155106051011514200700301000b001c50301d555202c4c1d181c0c1e600000c1100050300e941c10101030204074800801d0600541d030109000304000b8000e100c3d4078015102d4208615031a440300e1522020006d000011a0040002801040810500001c869209486960b000c2c4074841600403100d40390340e01101102d00180d18030f4000740101c0c20b264024000e40300a00204e50002c41209515035203802c411110815840d111b803002c1020b884c00788401e07a1480203841c45103160100f00e08082c0e544c0c80c502240d01c070302c031414401400c2c0c200c2c0c020702c4000521800d0001440304103e40c104001d00800349000103c0746030b049002d024080520501c240304203181d100540c06241c1340060400d0b601c1d60401d103045608a1490400c00d200a02200c3c84ea00010381c04030000704450 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 528566016 1250 528564766 528564797
    0x14070b0702041a0a090b060904021c0606030b030a0b040c050d030503090d0206150f1918112a070312080609071716140403120f0c12050d0e0607 63
    0x290480b00c0701ca0000c1041d150243e026940d19501d1404940c040b0308009000d200c1e0700045611405a0380065500c944007041d001c0301d0343c000d48070401050704006020020351303454844c181c0032909092507031909640191640c6001407020b01d800c5030818001e112604100360f55400241241c0b100d00011800150044180191208200328028180c0c05500290803503141c0050111848440d1002c003d01c150301b200c104001039291074125403085c068003040030444a0b1103200b100c03821b0003891030084141d86004c0520001312044000d8071382022601c10545101440580c5000a5444411498000d40120080080000c410b128401c14000306030f20303510401e245c500704200004000510000a024098000300c080503401d50b1900d0344076600c0c01708908104040798045850740b081c800034481001e40010701000740040318510040c0c0b070301c4954640c0d03103501c0c40600031540c021422100030030501004004500c0315004102900010140d01381c0040c1c0d0910721901649005000d543c240085904a90180b400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 528567266 1250 528566016 528566021
    0x50a09151b03020c122113030e0907030b0310150504050c040504051b12060a14010f18030c031a10030f020f040219030e12070c09020c010207050a0b06040522060914070b070204 77
    0x10142c10500347c81c203110386803009008003100c446a144500300010014503000d0080d4861041d201c4040c0c102c03403e0601c6251003000610720316280c1c400503030f0401d80014180c80c150141ca81b0800d04001803608240ca09010700c009014040c0500c1c112034084202c41c80f07110783c0b51000d445440e030500c000e2aa28104a41446404165600a40d000c0f6110f002020040c0e6080801344500800511b40b000c04010a0307400310700842e016410017020341c60382c00384c000184080c405034071625041c00e01c440f041c2c0d0384030001a100704111520000342803003c201014070261401021600814101070009880e1018280880c4803000030800301d000401d40c0e8100c90415401c0410107011111090214a49454400d444261110180d0704c244040c9a400040c02c0c2d055800c290150342e00203034483c0841f5140203272071401000884003150154080c40c54000094101200c09060042043d40300f410001881030f207494201c054000d210064803959804030140c1804402001200300408201c650580c445000c2e1040106 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 528568516 1250 528567266 528567271
    0x2b0f060f0f05090a1b0803040303090314060610080702030f0d020703030e0d0c0209090a080f12061f0c0309030210090e09030910110a06050a09151b03020c1221 70
    0x1002490700342000100100003460200060304200310318080c04441c00c0d4031045c0c80300c07134110031080d00000c10000100340d00441c1c0981500c4c468038100c03040c42c221144003541e6440451344180d00c40001c0039117524807801803450035080b003614030580e031030701c401203001c02c240d079010641407211564001a00018541d251054080c801c84400140c00103c1613504018610b644011010f80708800b5030010070522402044800c180c6688001c3c00c1d902c0d61074400c41801d1940040711320440041007203001940a140c07a0060f0030030306010090f405041051982c00301e4050001c801c1c02c40520a2081c40400942c1d29046100c2c25014250341c1d4046c80740c2410640703003036214041d0641e000c2d6403080c011507145984106001c0c078040081d10740401d90942d00c50040d440c18008200181c102c510f0801440304100054000d00245409104040e58440c2400303101d2045400725045071740482c0741060580d01042c4070760004d000c002000c000303c1d405480c2c0b1091007000d540c401400c1c00880100d0025019030225110b101c951f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 528569766 1250 528568516 528568541
    0x316030c0806150f09090c090a0803030405030301030809060d290109031101030b01020312090a02010f020a0b010b090a03060f020a0801082107020d1e03020105090c2b0f060f 76
    0x1c6007444400f0640d6071556203091540c000000ca0781e103503510b40e200309403450484024500c1240342010361104a0660081e51224042c85085002040304000002103e004640c888029451a840c0d52036854080c1c011241c010f078010010012001ca910044c042c0304007014615100d128500190303042c403c480c2d210381507000c0c1480000002000411520f800c00500304070700f0300b0042641440500100e003584101741108800461110506c1008500011410079079071003038070740c0d074031103402c402d81079903100c0c030403130005100e80e0040e4018482010360001400d45448054000701019403a40d950105403034540f07005403d020b50115a1070655907000314024014a00350303028007504040300d0203446101102c02500705003d40005084011500c8140000460a4021101000018902002c1944070b0f05450081c0c1c0103601b42130205010b15804512003041d08002005851004503480c00b482e40d0541051003450011440464200842d00c4c800841501d0362090500042c98003c0c0d12214085686000868 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 528571016 1250 528569766 528569777
    0x3060503030414180c030105030d030b090601180b041e05040c020a110a0f080312070503060f011b05011b020f01180b190614040b030a050304060c0302010b04020316030c 74
    0x2005103480210455041e41c900e809082981c10481e0003142c0100c001c10400380c0c4590f1041c0811041828103c040d50603190100c0580350a1800b000044069500b00d00c14a98402c020001040c280d6010391240007240c208400080c0542e43d40340000c841c5d50b006a800200c07010405840c1401d810600c401240103000103e03410003443c01c05020080d07944440c400d004040c4c911030084018160703901a01c840090183c9041c201e00b858a0343c51080d01da1704070703612074500d0020f0300d808a46264043c0341503030701c650405003807004008108401140c221020b1020308004c0b0004801550121b032080c0100622928541d08003415103032001c0c002807a00c01d1016007050264904a042401d09040c014001039040e044030b54080030351545100c01d4000b01d100c0b20420317407036880d14400260b041590310644030740410445080121241050916890390040e07100148507810070002880701c0c6010300310720020303a80a0720002443c410108041800c90344103441401d4688000341a40260765814040e00b41c2008051405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 528572266 1250 528571016 528571019
    0x2d0501050f040b0127060f05040510141e040204030b04020a0806010e07050a11060702060a2019021c020a0b07180b0c0c090a0e010e030a080f0406110a110d0306 70
    0x11214800010702400c0328102c200300c4980000d040c10145c2640500844100b000301550700d4182140700f14130b034400c8a01883c148000200c06414101c00070044840c03021440c82c045035442c08101c1e001140e5001d541d030b81307181d40d450050f468403544003030300103140714404050960400b80100003070700c2c8440d4081406640000014042e0390011004d013a04185d8904215844a0710202c0580c0c3c03904948404207200d102d00c60401488990002d100e0340074202c03205040042d81e03052200381221030b100182e9030009800070003210120702540c65040e0660072051050764200001140341d0201c600c2ca0094000050344034520100a0025500001d50012094100509800420070300110319600c03610a50548240c04105580c981c00705000e01c0880800c02040d02140d45040344100004202c2c170703c0364030000e41c40c00082d01e512070000012504000c20315242c25080346d4480d500340b040658000d00071140703151a41c04502c00003000780c0251081c01134175141c0d04003150a08096516020700e0320790b100109802c2000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 528573516 1250 528572266 528572273
    0x4020d090f140303090d140906120703050c0906190e1201050403030507031b12020c01150f08010e2512050a020301050708010b3c07120f05030c072d0501050f04 70
    0x608054286c840d041c0707041b000076400111415409202005904000006500d00302402541070f194070030010354504000710b440b051f44007500c5000d00798046410510400c14a6006c0300c484840c043c01a5032442d26401c3c1e28901c4012602aa09074280040307169140e000f0710040503054054664440c5903460304004090b80f85185141c8820910441c20900110303d05050628005404807000e4610a400074840359010300425880104140300345c1c010f112441038013182c80340041c0192024421024002e1900c0403c81c0c48082c030b142402c021001e0444004400050b0001040801011a43c059406080048514010b1509640000f000700c010002000014403201010000f510ba04242c1e405040240e410340c0c1c98010101c66010785180d0156a070300481c01c414440c010001d01c80b16118034404c850541105400340c40480c240550f03940491420305c0000c146403440c02c054404980115500e82c10b85210140c038041c0e106d90010652455082002000c00384002401010b80000c854881003d4a150549 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 528574766 1250 528573516 528573523
    0x9121c030c051c0b130e0c120102040b040b0c070f0e06010e0301060e01090c0302040e010f1805093d0e1e0d0e0109080d050711040509070504020904020d090f14030309 73
    0x1c016405260f544d90508403d8a40c64244600012404020000f000c1c0101d415030390360000b10003c0344208207890241c451f072501070003a18211010b4080d01c9040c5070a146000415401120603086140705030840011508064102d1400528807100c4204036401c04000041090321400c0401d802a03040010800610b46141c018504650f4990000a00c40e01820411000303072040c3d502c0501c1c07000810001251101001441008131003050b010300c100c0301c070441e440a0540b2411990b002080d040110419035141028440e19400076200206852540700c1c4640441c10b0340380c0380e030147d440302d0f6501c000211204007044015902490400b4508044c182070208540e6007280682030000c01415135500b5149900990b14000a8881ca005550320142465401016070b001756009071790744000c078003c00302c3c5400d0034460180290440c0010340921070402092001960240412a411541c2041580341c0c612951141e01d0107148070340400800c00c540d81c00c1400c480781c045417405501c0c0d041041800900c402c0007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 528576016 1250 528574766 528574807
    0x30501210308130b0115030b09101203050c010f0e0705221d03160b070903030f0309030e03121201080304051e061603050306010306080d0903060209121c030c05 70
    0x500d4107881c10f948a188004016a070f04034010031108640001184170441d500381c9400d012000d039410421148200100a0700d0310013910f40c0d500c21043e014080c061203407001d2007614118001c0c24410b03d0098401c482c42e0860b0a511061400d40780e03076001c3d10081d103800340b010b400148002c4845000d01e507410114030249640301c88500088039598070760704000b450f12030404002d440c505000e0725290105c48102100c44a030000040b00d500604800290000d4000c580da41c05581d00340d42d911030002c1400342d0940081c200e4140076001d000140110543c9a902005040201e090701c43c1d80e40d8903912000c5090070102c2042c0c20401503a0003e020900c003a40724209641c4105100c0500501c0345c000580c0404c0c6188100e5030301a10300c459800c4000c061541200046008050a98041102903502c60f021a2510700c501e00c5c41c0009031216000704082100c4d0303000760105044c000c00d4041d8901340c4540b0325240002003100302000011503404000341580510078110407007a2820040c0c03408009207031034029000304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 528577266 1250 528576016 528576023
    0xf030c0c0d0f050a0f030e0409110103020309011508031c050f041502090303030c0714070819050c030708241009050c090909010203090c0f06070311030d02040f0603050121 75
    0x464071142484400d04040941d030b6049015142d000c02c450400e0401d05480050503008595040c40f07800d0141042c0c480d000381c06401050042c044400c00d00114080d44c8042e082c80321540d210171141424188980c08c2c80b004124140056139a03d8a4050320b0514010540e200350030646444100802c14100072101c0303600c1a4800c03140e01189070100441700007402030904480e0148004000c02c0b0817206108010200d05001d03c50801200d01c1c031400d01d5036202c0e25409410301a400c081d072a41d03400d00518084504480c403c0b01030320322500c892400320386018600d5104950b40d0380800c114140868902004480d0402044100326a0340740c40e810b4011001302034441c0f4541a81d030342c0f000076a054014001e664905d81c00416070201420000c0e2400e000c2d41068500c88600e001700200c1132605d2403c110b002c214800b010b404107040c0003040d1020b07901d00f0320f03010389a11580070400c02c041c1244100d2000780040c04081c01c01c0040c4c00c0c18164000c04581050304442000080036180040050b0600340c003a800d250b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 528578516 1250 528577266 528577279
    0x912051923030402031e0601061704030905041a04090b0a150e0115050d020d0606090807050f041a0303030403110c0f06030a0f0e0d02061b03130b060d1406090f030c0c 73
    0x440d0304c0800e19185511640d0b070b441e550100b40c00d0824440100d00c9a04a80c00c40e07550304201400207841c4d1070b00e280191001030100c4c3d0003003803c106904013074010500c00b025080e0651000307a100030206007980c0b1038101c1207039041c036010308200e4800558400d81d00010414402c040900742884400840440306004039421a01e003d9900d007044c40c41001140c8104e41c1c1850195126480102400c001d0600e42c00303000080b801c108404100548000740b200c0c22240000c000ca150304024800303100062000f01d072601e03030400e6808000300564904000844c0078034401d03621a841e0001d5911030b1130402ea0308540f010722030501c44203c02115a80c03401641e030003848140f00080c6941084c10140300403c0d50360180002400f80002c103908454010030890310900a10340e042810100d030300b00300d03000d82c40105c4109884001e11084140032030301174070781658416800340019290304640d4031fa45504140b01503181d4201c2c2d101c882044810300081c0000080080824001c505207a0750400c0c4540700c500040c803c41c003401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 528579766 1250 528578516 528578521
    0x40903080109050f131113091415090d0e030703081605120f03040204050a0b21120405010903120203040911090f09090c010f0c06020c070e010f0308180103091205192303 74
    0x1903074800d64642905490703c0800c0380c015146002860611003109c00011800382100400c500111419850b2003544036034042e2810405051040c0c0f041c128032038107650580f0a125011001810180080062208401d80503090b61158940b091401491100c6004401424002c00306490443d00c1965001381d0b044401003039030740d5900c203281c0090041001040d8400b0381020424040c442c94801c0c0602c00700c900c1c081d2014480040c1064000c0d120703030701c20180091003003c1c04001103501c05e80781c1d2000305000e1040e00e107403d64440702c02c070907500030420113485150700203843c2c0064079014544125090055606030111f24202c0d029544841c80d045001d030611111100003502144a05104c40c2816401041151150407420b44560703079144500030400c0180144001044012100601000301d03540301a81a1030600070000c1c55513180c480007429030501d525411080c00060710341500c6900d82906668140d180c10411410b407180020084079401441000d000c00c6d41e54a020580301d002c8a4542e11003559240c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 528581016 1250 528579766 528579769
    0xc06210a051902041a03061c030f090801110d02030c190f0f0206062b0209100f1205061909050f0a060c050403021507081201060305040b0f0c0901080411040903080109050f1311 77
    0xd0b943d0501410301c0703003040c0d03000c1d20805812400303070811000c0ac3d82d03440c1065a2203280300b508031515118240e85c05036007071025194a0105da001154028605040c0c40d05200804030101012452a1001401310f290f030300001d200f0345c3c2d000284040310555440102101c2c00c0050109002c5180034440e000854401d41400443d4508010f603ca04150701901c042c2c1c182c43e1003500f041d8491180c1c003a8403441d0002c5800061008026081680c9068001000e004582c80e840a40b01e51801c40c100f2140c003003512001c0040c0820024404010700d01c24400140600b2005450500308964030504150f081c401c09110520142c0c42c0c0018600a0030300010000c3d99400313050901254500620f03114112041c184000407545a031f15410a9000c0c6203e121201103540b100d0a603044c40340d10031a04226031200501000c503140d84600b920790741060150503091141c41c01da0001c2000d503050390b981900030030142d4004000c02c09a0307100d260b5100070351815640140c00e046050850822030b000e0f002c2e00c0070518400301c0055 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 528582266 1250 528581016 528581029
    0xa0f050621010e0d080a050a0207051b0307180f0509070b04090906020424080603120a180801020a11061617070302040506030117100605030c06210a051902041a0306 72
    0xf103441081200d41d01c8031135210052400354202c80c1d60501d242480c01080c1081c9050081d5001540d0080142c89510030200009509101c0603209951611500c500010b0102c000d0f080a1590040c0c01c80c086008001480e41d881500c0b0054110303803590303108050400011384400156402e442c20000c0c0810710308003d082c288040d00568000c01500140341a00d03050603000e4400000b403039045601d80074040c1c0c1c0d0304002c05407200c21082c90091100e408010150350140b103170070b0290b000c20345039125002c110b480c1c4030032608981000b80c0d8000403464442103450b030110308003d080c0e4413a0100f1201b42c804494001c00900c2031244550114040031500c0c0850041e60094040d140030705005071030039860b50381d00c0004240d00791640110a41e1406800c0b040c0da404d103101d01501007a02c5028006144041c02ca4080c080ca5a002211084003015108000f03a480ba01401c0032900402e0b596502003054100340003441d03484540c2260b13105400e0b20410007040007000220019200f1030048018a899546140102c2e44 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 528583516 1250 528582266 528582281
    0xb060907051c060503030d0902030609012307020a123911270103020a060513270219140310060305060604080619060b07020904060207020301230a0f05062101 69
    0x174503000c0801c3c0702d101845554400c80c2030500840403038049441e980509800c0b24a240800d498540705c0000300000c070001c12800d1178002100344110780d02c40606880f00140c1e150603111140008010303024088460799100160200a030500c0b45004005d02040f009006212108100400016040c0740d004215074441c11807000c11100c1340c0d9034031490090b031180160611000d000491252051000c0401c0d818464810381b80501c908000050441d414040d084150030021080030250f5046410b00c2d00704030240b070002d07061901280714002c110082d6100d0103440ca401d211148442741c40144200103060b107030074017400f080322400d0030000b9003a101c40d004602644103035000000144a81c4003448083c0e0450001a80d102004800401c19140c5502e44460702c3c1c442e40c40042c0d030102002c404140070444075801000040d100400000700301070032030400079064038009040c0c0c10949064082000c1c0040d940112505110110010001031400c0e50008045402020312200210562442c0b80c0000600754403206 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 528584766 1250 528583516 528583519
    0xb150a0c0b060a03171e180d05120d150603020a0503010905040809220c090b0405040f0603120f1205010e0f0915010b040f12080403020d050a1e0b060907051c0605 71
    0x1d0008240c0c449605035440010400420020f046d100f00740301020600351148148048404511031144a040000030f0a403114160380b14094030159500c2032007048010100e45607240b8002c100300000038032540000c40e05901c85800c2c90b00412a000c541648481100d041d0b900310440050140c8590805501d0340c0a45031080781c0107900d600e050b5904903482042c2c0c0800400160041c44003e0700e2840031101a00240b09807040640107120030710a6103001c1d0804148400c2e01e46001464070740d40d440b0302411684004000001c1104c0f40c0c0b03144009948201c042e210851000024045940b40c02d0000003841c00061011007510900b5010844050040c02040c030300070340c020840320f003558540071040c0c02e275407080c425200707281c403c50700004428461200c070080d503a400080007820140342d5000e0005a04a90000700c1d810700902c000f072030000b00c1d03504000ca041d041c0780300c00d020020410710b80120f840b000070b055940300303c0001c8100082941e01504072218101e00e8082000d4030622a012a4007a00003a044079 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 528586016 1250 528584766 528584783
    0x12030e06030a0b030f1f0b01120606030203070215130809120106300507050f13090b0448030c1728030302090d06020d0b150a0c0b060a03 60
    0xe20b04000e4201d0903000000700c054071060030120b825190b035643c0c100c4014031412082c03012011200d0541d07001218298041c1000c0d0b0111030502950011a6465001040030a40c0802032040c0654100a005145011130080c04458241403440d070744841903e100042c071140d0001440c840c2600e407088110808261003009101c0c03591115880d016040b4001c0c12140c45901305c04c0900ca510804912000215400501406815003002c4c2070210480d03c40c08070301d07008000041a02c00070310981c800c05034880c3c0526a61150b5003418a080d181403500c0e09410303000c201d800c09a0390070004403040d000481c502e48011049c95125078441d00c030b80c07001840d800985a0700341c41c14000b40d0240f079414454500d41045040e150844541403001e821103400b0360f850030783c3d00543c000220020340254000c0c03129200090402b200140d856658006a0384404040845592a000301c1c041500702030344080c40d0070000c06450b0b810212190780c0100300c030013002e030054070f107500c0b1038003080403915102e40010284d500082c04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 528587266 1250 528586016 528586021
    0x40b01050702090f0f0912031305071508060a06030b1e041d100f1503030f050421020102010c0f05090607061128030501063507270f12030e0603 63
    0x3580c000c9400c8610500c0031030401700040a48101080400d1805280f0124070308586418200c0ea0307490701e00c581d04481d03074840c410700402c10a003103075514980414035580321103c0d8605032091101c0d4100300e0f44040103060030904680032954401413180900913401344003400b5010340314001030103410f1103076019408645841544c22858001302d401d40c0b010420a209001d01c6108485000c11070348140b003144408248800184002486248600203910582c83c00b04e00b05034403001a4000c18401007203c1b035003140324010180440d6028080d01440013018140071803d400380c550058020320402c0c005620a2500040b40c400700700f055406a803103801549040713034442c41e42c0d1104085244110000e00700120b043c07804c4424540c400c0c0110390603141036969021210706045d44100600c3d440b08101166400d04944e0503820404158042d80b03e04010759a40c900e100346480d801c0001c0d50902c80481c603001740e0141c180b102510402c5c035401107030351105d94560a60301034201120f84401c0c5003040740c0c2c864400004d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 528588516 1250 528587266 528587281
    0x1501060e0102010b13020d0605060909010e09121b2a060901020a1509031805060702060f09190504061d06210106032105090f01032309060411031605040b0105070209 72
    0x1071f05a88590800410140d62900d042190034040c550140ea07000003803030300600c68150200701d010381243c107031030803a00c1c051000d440922040e04100641c244c03015900f0a080c040c0d1100301300359a03100040c1c0749040704089171131216401030f01c01144071070b000340c400040081050b442003102c1c44065400904c1c040040301c441da41140604034111f0300f0380000b8241000e440e480541240040201e404c010080351a0001d039509100e1590000c14014400c081d05014134851398441e489010402c410840c44084181d05040c100400c40e132668010640004410320020400701070240003a0700400704452200e41c0d01c000030000141082c21901160f155400c0150001c101310089860744075501d03e2f4034484074000c6401a08581e0743c0643d000550740300040c890000324550090b844440d18580c10700040c00b203e04522900340c81c9000c1512601000d9015a00300002d20200d068140d0818100310040c0821400103200c0c0808101a401114490703503803030b0410412680200211100658082e1400c14146010b60 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 528589766 1250 528588516 528588521
    0x4050103060501050907110d0807030209100f0305132402070c17190515060f0a03031205090a0c061202040f030318080712060f020706020309030a0906021501060e0102010b13 76
    0x480c4d80e000789007510200e41c0310382c01110400710214082005008031401e0400854070094040e207141c0905601704520180ca440d01156170044669649524134208040c600043c2100d00c0208180184050b8802d090300203006500811588050303004030740404480e04603140b000344140a00180351101076a00003881c5500000700076044000603080da02080c1c100c00024600142a6038010040c0d00034407200c01c010440c5000d61a0403420190a02c01003123107600c003107841c1042a410603004180910405601d01c481805615408034140000c0e0403001e07020794801040e403106006040a00c40e002e11000d680035440c0c0e040e82e00501d104210101040d5603410b010b402d524060b0110010000e10350000f01d040c040001360801100c0185042c805480c000380c40d00d10003040036050754201550200000b40106030213001650013280ba40014540c0d0b9100a8405402c03a841d540c850f20654004400001c5401025041d550444003242005a00c1e29014030040b40105904550140d0020f00320b00003625681c070b980d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 528591016 1250 528589766 528589769
    0xc070f1a07081b1b010302040e061e1002011401140904020d050f0118120305010e01050607031803030302090a08010e0a030c1b0e150405040519050a0b0a050403030b0910060e0f04050103060501 84
    0x303005804d481ca00040118140e225a0150b04a10f80d4582c011441e00d0030304002e2824000c0300c5450345000c4055642c0018036408801c955140141c5d1215201503d0801085015004010083e400d5a00442120101e070300c0c0d03c0c004101a1081480d480301d0740501006100208840ad0444001c02c42c11017600900c070b4a03c2c9840c6e06c00c0e21511918081d54246502921842d07040c0e4903150182c03200307a80f0305420403010b1750045404600f040350f1a29180562400580706001540c86070300c01503210050314003884a0a41550701c400c06d41da04000101d4000140071900c503080d2901450045514000d5041003003103104030f02c42d002c07450109040c000030200000042d0074050303804056103d10030641001000150780e403d0701d02401603001010056014000c00c40c3c0300262602c54000d807404030006446505400c1000c4079070001d400c0d101c404000070150f2600c21140f00d1101103802c14060308209040d00780d226018010ba5090001d00b428241c12580c512145d5124a40020024030a80d0384034074001014260a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 528592266 1250 528591016 528591043
    0x10305010207031116150c05160305010b010c030e04110423040c02340e04081909031a07050903031b0f0d0203120c04050a030302030c070f1a07081b 65
    0x13480029051500c042031030307030900e001801d04900302d41c1410a80711b0b0038017840e2503060901440041c030b5800503006001e284101865004c64800c443d1850411038250b0396000784060400c80116440400a034010350440001541501c4c0020b008401d00c074001c01c0d9115540041d02000010100c1940b03c1c50781544140350110162401c1c8121840c140c4140ea580200074134540802c2d0b0300b0511581d001e010440c20150401801400d806165915040c0d4540d2442c16101a01c81040c001011a921502066911161450342c81c0c000c00aa2541c3c4991200c9101d0341d80c240301448030700020800d030300e02c501d0607600303a80c0006003629554003103c0c03d0341c03006a409081e40b0242d806015841800c0141c0880c48154855594005c1c5181480c03190070f1720b00824004100c84405501480045119107404a20300d016510079002181c6d03403141502c04c0b071314040f00751b1b01c09030480407410410300840b00d010034951000c0000105a6403654500d18050a0a0180010030f804d2403a80380154640803400041c100352003d031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 528593516 1250 528592266 528592277
    0xe0613020d1509020405030304060c020303040e0c13081605130f06060c0506060603012d0810061d040507050f0f120a0210020d0e01080402030a0f05070f140306270601030501020703 79
    0xd83e0456401a4000c900c52503a16130000d010401c07040c1d018800104070140700405691406d03490300131445940e101904d01c55a401d05c0070402c9544a010141d19a014002101c010000f00c003040448581842d000d008050060b0902d82e4030900081c000c0c1c002c00300713070103100405004940d112000109841e1700008140c46601c60280401e046061410490b41070313811031800803010009100708203c0c6840800d0b00700c11104040c43d40058007135014820760844148040c00401c1c01e51625400000781d110f0104d401120b568100c090100040001480b1821600e050350400070802c52000007591685114000e141c020314800101c1d03611100c0402c00c406188d100303d40c001884c1d014040f080f40e40d40d10303000800c00420200302e51904150300030447c02c0c3e440b42c401401c40f15a51004d54a20002444c020402c5540340c0c0400b000f070041001109408001c2d00807513030240a84800c40b070001e50381c0c0901404441074080a40e0b8912200700c03e101c001420006840e00700c80041d40e4a01d04a4002d42c450309080c0d00080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 528594766 1250 528593516 528593519
    0x7050a0201110f031308070b04080702010306090506010e040c0908100c020106120327031b0512030903070b160f050c0906060c060712180b090c03160e0613020d15 71
    0xb07803440295420300c1440b00d126411591016501603074003400390f200356546501408403074005681c4440700c0b071050b0b128001d07030341d10303070900f840094252031071604810b690038280400c2044599206444e6084403400f00e8011950190401e01034038210300c0c80e082840140101c500c0000e0107442a0455072031a0b01581c020401d440e03640d4003c0c030003024201d0000f40080c0c106035200f040380c1100300069000041c2d00909200080da40c1d0303900c246e02680f4014098818048003410840e501d80894607a550420240185140240920000b901c800721802400c3d5401d0340451140506005405100c1400340e0000803540c1c40c81407800e1490303859000000203403143e520040062401c0c104003090302c000d6a03120004090702d4075440c8050b51000b11070301080c0d8809540320103c2216983e2402c1c0602e0f0203000702050141410701c09442402d01000c940303024000e031b000a0040303182940503905da4044940d0004514201e8071450001060001000840c04010b0300200d400c080583c91603000c90b2040210048003c3c105 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 528596016 1250 528594766 528594791
    0xc15180c14060d020a02010f060611161401260708041b0f0b18040f0b0103140708040b04030221180109050916090f08030406021e2e0507050a0201 64
    0x84141c10061500300009000b01c4401c060650064648080340d400045178600d42c2501950485600e46e1242c00092aa200f0940080c0003e00428400d80709120b2100750090900c001035103961200c00010f8100a02c010b070031110009101001c0e0086401150362420604080000410860040c0c800f9034200218500d43d4200c01d6080c0603c0040350064041101075504d00081c89200380c112140e01c546032401102000130359603591041103000b418010000503003504410006040f02c0a2a4121039a603440c0c82c00d1100282e00400807540c400c0e80051403003c2c540d40c03850103e003041d2070031400d410380ba500c02c0c40e170501c0142c0c00005000c5074881e0040908040f4041c0004545980240c40703266004882c040c086604000311007255154181b1600380340d004036960b441601d07850b200d941e0000c0c0380364001090600c0707625414442c400b0701150920f4000f80002e0851049612240c0128400c0c4030100800d01c1490b003500108030040c0500c900303840c10403d9142166000d00703650300052508005510b415000c2c50131 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 528597122 1106 528596016 528596039
    0x31005150a0b25020a0314101506080f040f060e01020906040b070c0b2b1121010807060228050a030509040515030309010c15180c 57
    0xb20801d02c068803102d0807801c0e826114410f81d4000500142c2e5405548000b40da4001d0b080500340d881c400f40742423038080c10040c0e052545c1c0c20000e2500c80444c03901c190100325042500c90818690301d02414421740401220010546101003400340007050050303102902c4025502d00040c50446440300080389900690300401d42d03081c0028400040099107040c050080021356890f9042c0315581c8580307003001f07444200000c4020950421f010324100560000107400045507041c542d100780c403500e03d00c0380c1c500b18400e00620010030320001401407000a100001c45078913034050103107102008942500b031407496554403210410a03a4160124a040c4482c3d14000d109842c2e00d0341e00ca01c0807092009541000b4002002180c64103c52545a1404001c0302c00208091030b000300c40250a00c0c00b4945c0011041811010503c5c041d090340940c44494005090240203c0c84480741d00e68a50001d1030 = true := by decide +kernel

theorem cover : BRFrame.Cov 528417266 528597122 := by
  have h0 := BRFrame.cov_init 528417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 528417266 ≤ n) (h2 : n < 528597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
