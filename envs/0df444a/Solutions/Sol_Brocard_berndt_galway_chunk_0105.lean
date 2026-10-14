-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0105
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:52:21.723019+00:00
-- url     : https://prove2.me/submissions/add32817-9253-4527-9ad9-a9c12fb32f22

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 18705042 ≤ n < 18884898 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 18706292 1250 18705042 18705053
    0x80408040504090812091f020c06060114040b0a020a030e041404030819060b040504050106020601060801060c0206040b0a031506020309010e0f0f220c0c0203030702010f05090a030c080f0d020a 84
    0x600404aa584805005e440c56044015001c5403041480d00c0c05030401c0001144c20b154800012501c0007001407040c4941340000c580001d0055110b9820b007400e039442110024501c80c5400b4680c0680c0c404a40022a810211f0f4040b4141074158400c3d100c404008a411040005942410031201118a160800980400d00c180c1c400d54000a81e5420042d051103980c00b4803040da4513036040f64261a1002404110504091154034010304040c4040d04c0d403035051170002420558184655400c00c40b4275901d00341555501c40c110760041c09014032840d0798245460015011301082c0d00d60102d502444640000d19500200448840440c1695a5000055510100008161300000a5820051a07000483c0c140c680c42c0002c0d50409886180e810000b102c0946034007a02c04003040c00c005c200e0720296140c0103890020659008641c2402c044c0e11400140004486a0081d51691030703100540c500c00109101400955500f0303504014180c03070008480450f22582c40d10121080801a4014450a4007150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 18707542 1250 18706292 18706301
    0x7030c2304080111090909010b031504020a210606050402090a06200a030503090d0201060501081305010b030607030204050312030c0405130603080307110d020703022b020303040608070906080408040504 88
    0x44031100e045040c50b40316510300f800c48100c070074401035040c800a520780d01e6180c407140c81d030360103240d0b440203115801810003c0b0382c17540300711f102d111a6149400f010900b15034805d45c0380c4010b07000200000010394030b07810890101415811040e01c0280c901200030582c0d0400b402240c01c031440140c00d01454900e01700b0100c41c103192440c41003004d43d80880c02c0d940082ca0600070b4000542c066603550740c80c0c2c200005094180701c4400c040d0740c19a80340200c100580d9800c8034200364002445494a1304e07021072404d1580c050714886000c29403500505040102c4940c240e030251054030303002d80484482e2611100c0c004410320054034030140c0007109010810035803038403100c00c00c1d4000354140c01051295699031445010b40090f00d0080118400121807001c1e210300b004000d40304a03103031000700f00b682e1071900440c240412201030707810201000082c00e41e42000360300703080603515805002c41c1c0d6995528500100713455808d943c0200021054400000c10502c034105007401907410021152a15141004000050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 18708792 1250 18707542 18707597
    0x909071203021e01060501080a020316050d0905060106110708010213050f01020a08040e0105120309100302090316030605012103170712021603020606220c0908030f0a02010507030c 79
    0x10310514015045883c40070841c040c40d2602800013041d80c1c0e08040014100801c000c082e1880c880c41401049404901c88550083e9002141421590760b011000004050401a90302602c03511501000291442c0d200c84d0070340c03040041d041a180c00c60f0700c0d04405c03401c2c3c0c4581d43d62128007a140306001c2c0084d191410012004400c14011a0b0303080001d9030382d00800b40c010307a10040025070040010402030404c94090032f0400030b490061840e00000000088850b441d102e40f500030507a0102d04180551010001010b04681042000cad080660303038600100500000d020b0703801c0c141d0401c12032516285580f0706081125901d0f8582c140e0b010b2203029256071007180104024100440d0425000255a15100400c81000d02040245c241103990901a14200000c2c4c10703640500c4000045807000e103128281d80402007650500032400040c0b61604480c1c00c245a0041c40050000050319115010138130000c01001400c0e400a00c482c1e030300c148041e4100c600c4490000045558806100c154010006000305107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 18710042 1250 18708792 18708797
    0x18010c05130b2101080f010606030b010c0b0406020d061202040605030105070219050309060301081b0109060c080f0c01020c0709180305070303020a03090507061205010e10030308090c0402070b04030e0909071203 92
    0x161244042c103c06818080e0b10404a54000701c228201481d003e005480c05015207090500a6108141c0000c0103c04030100190841c003201001c00c080104a4040352001d0342c41540500c070403034841c1d081500e9030f00284000c070712940c500440000d044c00e06007d41c030b21841c3d0b550080d000041100b40e0f940d880c00c1003600e044a02c0d010400445c0e0032a44c41101441c086d0100b2801841191380320f80440c9005940c401d2058140060b0000030001d1704d90000741600030a51000c0300340c0d1640084450540540509090310150b5400403401c0940e0a40000700e003c100e60920006004400026201c6c6000810013440034001a004101c648040fa01035001421080d0719860001540011a00c0e800e040ca045500b00000050805000000071600780c000ea501602503815046080d003001d201c18031940f15148002010301c880000001c44405050060000d113081c080e2082d99038030700e180341202c000070040341c0450200c0c01210405600303040078030003544113086400040140a05150004c64811030540e011005c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 18711292 1250 18710042 18710077
    0x1050703050c07120803010602010e0106080c01030b01090f090506090a0506090f06030a12080106020c010504080a03030e0a17070c081506010e060903120301050f010f0203030601050706090b18010c05130b 89
    0x95694422501c4a0805e0140f0220b58480d410000000d0a441045242c40d203260b0600f0700601400f800410018500784003420006584440c100058418800f10740c0048130f9401c8030000010503054a8201030711801c000c0b00d212007d580d807615032400715907042d00c515070002070300c000058480380c14904540d00480d000b02155032204441d5150007040d1510442900011480301c0108281c0360100191501141d007400c24908007800c0081d019a03802203c5000303801c06403141609920840103001e204403d6421250240f402070203171503044078a41c00504100c0780500403c01c001561030003c540030b00c03039090300346114440f80c440000440300d0b110081c115643c8000e0401280110fa542046440e00d844070320ba010503203c1d0704d001304022050500724020360502ca0840141b804403035020007201d030b1004003424010f07100e61072030821400506000e0310040038000c2e00c001744074200b403468860b0aa10341c01036000703111a25400500301c955000d4090100081007030a0410701400306000003428010106091820 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 18712542 1250 18711292 18711299
    0x20d060203090c010206010501170406020d110c0304080706171b0913050402040506030a030807030c0e220b041104120203250f06050307080a0507030908040801140906010501050703050c07 82
    0x4101c1c1d0040e980c09041d5440341c0c400c0c8807076580501a0303500404003404c291001a1618898400c003050040c0001e128960000c2c1407035110b2001e41c01700c800d000468290036111025410300ba0b41c5c0342d01c507006400e11442016000070f481c6205000c0007240390008100be2450b520313011034000c034030000000d010001c80c3d0b0a001d490102c2e100c030040e503d0001c0c03205e2400700311803c02e801400304403500644080d0080e0010700300a800719802c402001e170000158600040e820304000c4041b1200490719080b140c0c07020381d030901c0b090310951080031086038110820003080111090b1082004503911540b9101032020184020441c0514041c03120f510140013a06543c01d80c44c4440203203155500f501c041030603080415406001031410349035203101614181c20901c2c554100800090f0000c1d1008050800710783d1108001003185e40700350000c4400550003082039807240d131507003546406080c4804100c8a06d04101c000206803071030028880d0304840042c1c448500e8550113803801c0340e00740e000704020456840760f1040003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 18713792 1250 18712542 18712553
    0x6090a030b0709090f05070c08070f0c030f05060604060f05060d091401050103030f030203060a2106060605030106022b2a0b0114010509100e2103030109061d06010c020d 74
    0x1d8410341140c1d86086100d8240b001401c1111aa00c2001070103c0c5004100302d03003d9040305d40c0a0406030812034050305e0304460f242c400003841d07009030001c00c4001e080c0070000400010a151614080c0301d1425210b0503a0350106110032224284128807194080d900c2c204280e003480e07070041440d4060700c4030115844130306864048503481042031600507a9076500042003490703840b20050340e0004185c40d0542c510b091000004801c4041c9000c1c2a002c0060300d1700400e09030307040014510105911100611105d592414080c0c0150024403407800580500b55151040008505084ca8110903280c0c003107440ca2140041207901c07824074007501c504072000414020f256114000a9a4110711071301c207454003981020303503a00e016050500300e01d05010f41400310080c00d41e58007035140491201894002e901c0c04e000700004940b40f9001c5101c0e00120340080c500c0c102210040b005506982c1030030414030865556001d0b0050401850b010400da00c040c2c0c2000c07902a600c2020482a01400100220024001921031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 18715042 1250 18713792 18713813
    0x50a02030904051305160311040c09120302070501090602070305070b03060a051f030b040905031602030102090a1d06010f09090c020a0803010e10051203090402070609050118060f05060f06090a03 85
    0x1d50302c0c2c1c4e983c1c2507070041000b20400003600482d0740032906481c26407442d0741d05114081200d904511031612032000d140c08500c0754070418001d000032100b6102c0507081d401d0194031010710b80107290014608281c04990f4a00000d101d03012a41d0140052040c52301c0c04100c4030817900040e0806c0e900031b01440002800d40d94a42200205440103c000018100d100c200a821142c200c601903000742e042c40d940001041c03022043d509500685650440c0c100214070000740240708000f880c943c801080c40e804034040d007008117171240002e0070215814007074495600640b0029203004c1100c0000728aa0400c2c0103069258101348148416401100e010404599540c1030a420907000604101c1e100820030550305603241ca000020441a1101d50301829006411a106d01c030b4400114001c44e0001480410050180e00900c800c83e0032400820200c0243d040b030105c0816100390580b20f09041c03941303c4140202c0c0c0d104040c018080200b0440c600c0300440c0c1401065000102c24a52141c0f8114000000c01c7c1550b90 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 18716292 1250 18715042 18715051
    0x4140c18030f0d0504060f0305100302010305040501060306150e0c0708041a070501050106030212100602031905040503030301080706121b1b06140910060506090609060d02070b0406180b0106050a0203090405 90
    0x100c4c0d544490034010018504c42500070141c1c10941460140b0070f403100455542c0c0c00b6280c080c40d0101c6c183d41c6504156003d02880d030f000400003841c010050900d0178082e010501994101c030000c1010b40c407028250540d9000310030000c0c0c038250080108110305200030218400e4641c401c2140303410400592103007400c50b08240d0080c00440c1e00014203111a004495040342e004c0742400c500941d1a0602d00300030350724090b07220341030200c25034036046103c00390040c01910020070740107080381d50740c1d80c54007622504c0d5034861056074003140c4c0441403540b5105440c059292180c066110030002055945000c0390519203041800c01040400951100030401c1070103203500c100c0300c904e035840c0d141c10f14840c07070352416822000c8603400502d000c4007071101c0d90341c55040310321070f02c000c032151078440c802480001c2c0684030701000980010310001c0d20004102461603414440e0b409280c040107141400300c1d40f1411018080380050119000c480113001c000c0c0110040d02e04000184101c900b44120310010904a9900742c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 18717542 1250 18716292 18716297
    0x310090605010f0e04030f0f11160503010c0504080c0d02040e0109060903092705040c0509090705190608270f030c060c0406050703140d02040b030604140c18030f0d 72
    0x1d0050210042040b4400b0050201c904000b00c1d034903150f20002c04104400c8407070390410101c485103030720043c8102641e0002c05510030980d110982e003404002d400310414442c0070700035420300300c40007000360152050f6000c40c0d411801824480e2541402c00030f40007a5620f08a9000d952007285000c903100920078003211921426001500640354100506a103070329038801c2c84883c03114114800e44041d05407402c581800400300100b0303a0740320703454071500004083e00203c2d0452610300800c00d071a000080d0110442d4010786101c0710300001c0c0c00507106110f40034056140411300120100710300c0d070500c01142e040141c9061480382c800c1c0021050605081440084035603d920126481c001790006010094000d176011020b6460289003e0000d8800d018140e00038080c0309080ea0000800413000c1c0899403205102401156145d440d90140f501c43d80044e942c80707000e1447c00325229440d121010815000d107000f4000141400a04000500e20a45004155405004090b0314030140c40c0d08010002030005940c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 18718792 1250 18717542 18717551
    0x16052103040308060f010207060806031905070603050a0902060304020d0f080f040e0f01120b07180b031602010905120702040605040c030504020108090c06030402130212070306080c0d0b06060903100906 88
    0x909000f024200080c060511810350449146296a0009000c0d0110b8109007880015945c64000080c2480b0600d00c0c2c040c2c0406a98100c1c00401070007003509415242c003a14100101d80f100403085048800b62440250407240400c04240585041140c15036840e01c01d980400940000c2c0e541c510041d080071006000512003c1014000c022008002641c05004400400c02c1c4c1d6140a40d41003e0302c0c0240d4014201c00c0c01e0901043d50644612100c09003009020080b8102c2651070301201042da00031140d25400141c021141d01c21940306009400711075401400814015420000e03c61707107548101c0049900981d50b82002a481c0c0f00d5000d03e040951041d10001100c1c6030a00024020b80802440e0359843d070001803021602c0d035540020b0300e40240d010340d06c101c01d0222405926000344141600e840c0f07800b0041003023040d91a85500030380180c44407070058480c1c40c02c1440500a0301801c0c0c5c030006240c001c0420003c1d105041400c0640000d4070024111a1400b0710040028100d034103645040c1d0300c8540b01c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 18720042 1250 18718792 18718801
    0x270109060c030c2d320703030e060c03040f060e0904050d1107050301180311120412020d0203160303180501020613051501030c030203061302031b010e0307060305100504020304020616052103 83
    0x501d850030201d204524410b1100179440d860b460701c614081c00001c00348101e601034800c40c1d807a094103a50300c141003d0100ca950301c0c4ca8000c410020b149034420500014051a292415402c00c0c940181c043c43e840700040c900204040c00540702002d05c080c1001c0c02e4411010005140d40c2c00340142d000f40180c22804161000c01e9040040000c0c001070004406640401c540c234549910380b004803401c5981e1100d4401405540b88002a055021104003940c58032801c0a010a100000c400c40380c200c17403082e00c40352005074071084141d090444a10449025030454800140403821030b00366050064810300a0b101e5010302a5041204014203030401e65002900600c01e00450804000d4070340c0014090100025200382d560001703030b5a1074500c80780981030440580403070960740110f13034070050020010150b83c0607a0319808002c0c01005d044038248190081610300144508061080340d001d1a00542203516000710000b40c1c80640714002070442e694070030001200388940d58910340340900010056280e0b580d040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 18721292 1250 18720042 18720083
    0x40b0319060b0f0102010b0a060e0a030206030702101d0c0114040911030a111603050903010b040c02010c020615090103020603040c241101060f051203270109060c030c2d 74
    0x10f081c6102415a89000ea489860340d070303461100b07821110700d403600e0b10480384000c0c04030759040d59a910007904140c0100034080b596802140107025006500010020703541003128030400d80118900302081c0760485800309c2d030b05500c10103082c11001740e15546a442d050740d4500c80c10850344100070304c2c1d21210b80402884a00d205500a411100c0c0e00c04100505041580c2c13a90118a401540001d00b407041c0001c0542c42c5032803e40111041300c00c014410000302c0c15407040680a400541c031450014000c120000e210784142214212040e0005007491466a00b554240900b5610162082d00c22019001c0009461a030b5101500780c0fa5070030500c02c140c00c60615202910440c203800d41c01d136030b40e4100303401030003108500b01e5031808450086401d0540004244092070840c42421a44100c044040032101d401c07132520248404454000c0e61079114440d55850203d940300003011000300050143d00b8644081140a4080b03012444180403250344402d0390202c1003041207070f10500f1200b100c1d400c1502c500034074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 18722542 1250 18721292 18721309
    0x3070c020a120302070e0624091203031303260405070512030306130f0905010204260604080703030207031e0207080c010c0c0302060d200d0f0209010e040b0319060b 72
    0x8121030300e4000607902c0d607401940700e600c40e001d0500d00c00c0750b0f00006036150361061800410100c4140a91401081d0f41030b0b81c41d500d5001c0310340640a070070702c01c2240700350640000441e4420700000c0050018501e0b1a60215409602c03491849503507900c4290340b8541c020348402c82401244100001d01040303242109200f60074401010b00e5440e038005004100c920349801402030800e02c502400010440101c000c02030080141c2e4501510300e49c8041008603000a04180580382d032042d0340c200e410b06c01c40c20311540e960b0b0074040340e005001c104140070640000307000e6005043c0191281c189141d0220b807815000c014008080c0421005034491101084030040c1407156010b64102843c021080d50110b0f1210074440c1c0b034610000f0b0041c1d600140c0f29a00e40007a034440443e07006040740600782e0000100883c2c056801ca1085040b0452400402420349812403003120051207043e1203048044503e14108001050f00c07103005500f40c061072003003c42211110012181d031511640000410281d02c00a001c0201c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 18723792 1250 18722542 18722549
    0x90507110613021806090414010f111308030306100c06020d020309030304030f031104030b180115030507060c0209061c05010e010c02011103100312030b06070f0b070305040c050609030a050303070c020a 88
    0x4421113010710000d920341207846a481900841e400c08031094051011780145111000c1d6030180f450141c40ca19520f03410f00060901d01d0078103903c284400e4403540700685a1000365070140c0c0c008100355181a220b800b548080030b05501030300005090031050313490042a41d00899000101c0d800000400080680108034196003080c1890104502c01c02c0c0843c00030184154000609203030100e00014100d0b0020104450700b000740e050003805840f604200310020603107a400100e489000300700e804900306204456000c03030150001c0036554107442c0d0006000f14022901c10001403000420801d40100724240903440b0b20815010002070b0b19001c03064000e00311100d040c4078468851081061016208e1b000303c020042c0ea4015049881c0c03418054000d500400d031501d491500301b007001c11402c0c02e03c04080f0444420b980160454042a540c00004404a8130202d4008000801c40035051200303080c10720240c0709074a0090210794441f000c54480920310b4000329268800580051000030842c2040c94144004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 18725042 1250 18723792 18723829
    0x3060203040606210201050d0e0304090905160905090607030216050109030513050109050303030a0203090a050f030a031a010c120c06021207020106231005070605070806150702060409050711061302 86
    0x1184c840380c0c0006c02c18800c0d00360045200740c0300c400c00d1b00f440c03500340121401400e15020030010310b001803a10382e40301d10f80428080080c85c400b52002a00013802d02855108919850191185544204c1c1c250000c3d08844141c110900d150341001000807070902c122182d40d8020b484013038a907411800c01080e80040c13034100034100b005aa030104540d4078008203a9421107103454025840356070b03952140e4a0100e09010183c854412001607545020001c00105a4044240e0f01404120b0440c50f00c1ca40c070054400c62540042c0b000044000403e90b0001441100300503403500e003e5214241c0c56407816a0030804e106c40d0000903003000d112046409200b401d00a0120010b01030092080c2c4a1010900c6005c808190140c1c2810414403a518840c4040b40c941c41e500c250704110300d042407000186800b200f182c02900070b9035200410740e00380b10b1500a85200940c01040300c4d107803a0410507008080c000280259091003508880250b9254050060620038601c080d401001102140108800110052a400b80 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 18726292 1250 18725042 18725099
    0xe010b0102060105090a09050a0308040302010b040e030915090301060609090b032406030c1008040614010b04170304030503040605130902070c0302010503090a060e070e060307060f0c050703060203040606 89
    0x9166004203800c0e0443e10210303450b6001e82d59210114002d442070140041c418003801c0001d40c10560401389943c0214040d43c000c11540e002074051004a40c1074001d815034541c028010742070103103030414001104159440c01c0d01d08001210340400c1c2516100d8208401084070f130b02d0244480c4400d40706a640480c4120010000c40080212081403a01c003a4080d0041b0f000f039038000b0f19651000c1024005c681c40150003d0a440c0b22048004d0950400341c1c3c00319070040c200148840e600140b803803518142c4a0643c072aa1030a4074115603170f6a490864048800c0c4c900050100001148040c4060001015139071169903541220100d00b0420100d81e40040300342c5481401800d01154245c400d40341540c1e42820070595a86a0f518034034a010300d4208010442c9081090700302d011900859408202d400c494200112925403804040c2c4450031405900002900742c4460452030380320f0120000e403e40200c050320758094481e2110b8050384e00c122020340c1e1031603e0391000c000d10030f000404640a001614003056 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 18727542 1250 18726292 18726311
    0x3030311030c031902090d141501050906060904060f030c0f06050c0c01030c0203120a1a0105070b0406090f0b07050310061106060103050a020c060103050a050f0f06011a071a0402040e01 81
    0x40b2400301401c0101c0c200700501c0e03c48032410496044941c1038600034804803074100d1a250450040c1d403003c17400d40b0903002e0030b0b122142d40c0c56045205416110000e02c00c1001d640ca40c010302041d0b411642d2890b5100b0f0f00c0d440300069100303c1809103800340d03018102410350705042400520a4000720b40c055420010100040161218040740f11b05480909103070114000903044000c0345540100001c4406124601d03040c844580e01d2a84560150441600750300c0c0381010550055906019500c00500841d100714006000900c4540c8502061803081c030708260900c001e91610307510260100d60100100c0c0c400802e00640c58030079840f810080400745001c1130402c95014207141c5600740506418140754a83d00424161a203a406540801200700102c0c1e69a603501d081c42c60f80c405015100703940b5809242c0d00012044000304c0e036032140600150007071500da481c14020110f4402071404140741040c1c20300c46800002e51091444040001124040f003850615004010417200c00c3e82c4840d2103a0724124000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 18728792 1250 18727542 18727561
    0x40b09090303010e04060617070806010504090b0103020405090f030304080403020118030f14010f0906061a0301031208060103090b0103060e070902031b07020f0303030103051e010209010903110f030609070303031103 94
    0x10383c15a6910700b8401d189440e03074030b00308000d01816041600303400c1080c480ba000c540350000790301c0d00312090b5204542c51a40d0b5403082c4021281e00e04005889103402500502c05402c00e508141c0d00400d00c9021226100048a031031070454105079000c071031201300014200190342e4043d0f004100510f0a42c84d100b806e130719560306d501d00c25100c254010114480c0410b1091240000c1d40013849055010b030382400701312a10710b0030300002d042c0c03802a81041c4401400e041071a02d03503d4103590680f41d204e60b540b8281c03903403210705541c0c070344c0020811810181c80c1e807010000200322201e52802144903080219214003290000c5003007a405404c6a0b0500d807050003000642e0803d03205c83d0450741100740c1041d40e01d07150360021803403032044100c0c515098400040008100000056220010402c08500c21441d0615494150913485400200d80c00a1900da2041c4040381132941ea1a0040c10001c05054074581140b000c2030800404803404645034100140420a1503014010244488040d200030351852130a4141b1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 18730042 1250 18728792 18728797
    0xf030c0c080129040b0a09060807080d050f07060b04020409050601020607030c1b020316060203040e0c070c0306020f09030106060f030b0d020d080307021608030310050904171c05040f02040b090903 86
    0x15050403082c10032984541303494650040c100404090585510252100d01d40b9000d08218804c4103071038440c60400060700c2101103006140081503503079540c5026081d10140860341c00a4070f0684045a442d0460300e00d603910340c0300400040c068608082075502d8850006428200c00170b06201c14581400d001c5510594400100e2413500c058900e420907410305070010030b1801542020f640407403803414801103815500000a401119070b2126130484a95401494507040d0051400040030540a141c06200007807468001d00881c10381102e0007420005c50710006429120283d1104000c9540c0720800c800303603640f60280392140102515501c68107040e03030b800304016803a40034000d0a02c000200c08105124401e02c002451522840c014070907540d05e90440d5070303c0ba402a5901e0840702d00c001c0000981d03081107000f1900c81d58018802c0b0188651401c3c0f8000d40707500a02910031446601c02c042c00e41900c0c2ca205580c0540d01451841030600403d20600081710300f800e14051284018078208100e480f0700008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 18731292 1250 18730042 18730091
    0xf0105090712020c0109061b020319050c01140a050c04051302030a0207080301030b060f0a0303051605010204050a06020312010509060a140d060c02030d0c0305010812160f030c0c0801 80
    0x16010029a1041d00c221035040318500b845030114000645402079070300540050724140c0c06030030304221000140c12821104003200c130011025070000e00240100c542d10000105142e409820319500d4903425030105403c480d220000008a84a698144120206140705981d48a10541410340c5064104400640c559412807230f100c1040380c00000155904401d1f03016184555801000c81d9100c1d40c491824111012086654038000c1500c902a80c010707180c00c041c0e000480c4e030180c49583c40d006403041020300d51000000280c41d1990200400070382078442000580003000c0d2540603580f616003004200c8010081a40158850300c048400c1c000c13241d4403e842001100c03400c0d1107800b5203180d08000305900503c1820040e01d118505682040f103a600880103014182542c00c0030401d40000d000190115002230180450382d034041000c81c0c40700300400e0018650308080c0c901d030207001c5100e540c45100420200004800142d5004410f1040100304d0030b10b0000341039400c0c0281b00d081c041129460001d00f1440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 18732542 1250 18731292 18731299
    0x6070f050d0908030f030907091407030b01020c090a05100f0603020a09051206071808030409020304030e010201150b070203030c0102041413050402010219060e060403020d091418040c0b070303090b0f0f0105 90
    0x12912a050800c2504010009c00009000e505507507110341a06450441c6d483d00440d0404280851641c80440c0794840100020302100b25901c503402614000d0000401c80c2c03682040002c40425644880d0100c0d8009000c5a900941d43d4640c4041c000c0c14090254001130282c102144142041003011401640c8252545000307580b025840650300181140c2c0d40c0840c40900000a0116004600341c0043d40309900a881d400f51180050004908032803980762800103000d6100c4052241681400c010018503000604030b90509070804419400ca81c8958403100c0d00c141c443c00005400c0c20002134040381d11100110070441891b0540001c1d48940e58912b000d004004420110400c015195100c0c50b080311543c1d0031608281390600d00a545c5107456501e50001c02c000110000b03481c1030403032040343e14040c060105004403154140b016031900c0e010b00111803001124101140d2160704401400d00540a650040307400c038468102204400303800303019240306440752810420b41048540324a411910141c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 18733792 1250 18732542 18732547
    0x603070302090a0308070302032a0703120201020702031006151d06030601032a080a090c05040c020102040509040302030d060f060804030c02010203130b03100527060a0506070f050d0908030f 83
    0x500c00500125251303003004100f210081000800c0c50350000203411501c5108040c00c2c140400925080c1c0c0d44030004880d0241542310010500028000c1103442080c00e116000150800c5140c1d0b0000e0308084005400d9407445503142020000d090100d4840c011243c03180c00c00c42c25040301c3c00181c0405401d003001481c001d4a0010215490382d00c80d0b840b0203caa805d004031454414400300703285011280c110a00e0000628080c013141f0b40644511a0100307240d44041401d5080e0300d04020310000e0811410340c4825550300340300019964480c810424487c034807075806582e07a150080100402c071505034002102c03150742c600062000c03a401c020743c6600b03c0c1d01800c00d03000b294400d20040b0f00c2c3d0f20031074440455981405200203440800b05000d54012050103031000b481076125401e1211030643c1c01c040c0f0690756000300140000751031003d80c07950820400b0f418416810340743c0340804c0341940401c00481c2e80a00d0309120200740003041c0255000e170403080c030380091502c4c03a00110f40e5890280030410388421400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 18735042 1250 18733792 18733807
    0x1240c03170a02090306071809051503060106080108120304120813080c070504060b030705030f0915131103010c05030601030c03060e070201060305060a110301090506030102070212030c0c0307050603070302 90
    0x260426407061030100901c603440b07242c000c070315201941001141368081c1c450b06001c2401280181c0c1203c4400d9028500e440c401854010380d80090a806018100403082000c111040e40e1001d025145c0a80b0380c0341c9480d100c95161000c128a003665409107660600030a10074400055030b51805024002d9051900c1940c0e0b484e40c64030100c2c0c1c082180b00c001c0c810400052203000c40349010640e081200c508650810400e5540c14581c0345511048408400240d400c20004540c0540e00b01c5254003c51000300311000c0c09502c82a0740d80040c001e13180425014040000388081014000c3d68242001094000f40982030103c04043e060707020190065042c552149680005580300e540000003c001c42011028036081032070740a4003d14180c001035a060140000080890209009411882004841880c6107a01e4111210700410001e8400e44d8155002c00101e00075907207807488618010307045000b40d070b48d880c00d5003015030ad060070030000a4001c3c1c111580410081e500c640640c2d902c0013490a016945404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 18736292 1250 18735042 18735047
    0x2040209030106080c1009081519050403030614180a020c0c150a140c0a080a050c010207060b0307050d020108040b070c0503040b12010605040803070f03030609021206030601240c03 79
    0x1600d0105a015883c2c0b60001419403070010f81014440070a0300ca00340c0e601011181101c840840e030040d56850b501850b04900040701c80a001c9622401510074000c0c0c07285840d803042c054440c1a541a00040c3e00d421050219148084d452142c1d8001101c04451004580c444c0e9408880020b2003a4051507003c14442c05880c42441024a000e000a2402d80c08150700b00c03140c2000d030070600990700040c44403115a03030250395840c219440a0420802000d0a0851340c1d9514035a500c9240d8000400c0300a006901083c1401d00242c406988581c10114507010386030141480c2c6507440d0703c1188288884400000582d0700a1501504180c120605d8041696450300c29550301c402c00c0001000d07032000140018080c4002405032001da42d80d06c08808480c0daa846046845004600802071180c10410100000604c8002e900c45401d2103400c002c52010f6031038010320201d80020050f101560036a1040086034035040c4527141c05800a403a40c010040c4d0300d0451280c3c0c10310020004000e200711407031036005050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 18737542 1250 18736292 18736297
    0x10c020402040909030504080c12070e0717070c0201020c0402190e150307020a050f0a02010801050103020a120203010f03020102010b1009050d0303060806160e010c05062802040303080601080c040b0d0207020402 92
    0x103107203c082c04180309603c2c0003440b6074803a1040741c40500505d0b18801203494070b0800c0e504101d0030400200b051a04221141d2403144002c2d0252090108007082c0300c403610034100d1260312550058503070070a414424000642001a00c2602d580314600c10400640c440c2040c0c0c116084400c0189011071580075a000407400c1c2815454241880ea54088200903030342d64009001c00009107c1c5040d5444441e04000342e03581c42d89000e0009010275407850043c00f142d480307a4003500307a46035139250041c2d009100602003012a442a040160704080400042c402d558090150b40190750081c2d80554400c01c1c0c1480040c200c035600e02070079204181c0c0b818a617007030500c2504180058070044065894500388072510354002040c01582c00041020514071207110b40c082e03020f80d1095a0403101a1516aa0300082d92069035402c5d0420903000c1c0d04085496901d00252005d00003070352190b01c0304080b83c180940003505980c0010301e400340720b603410070051002200c0e00041c0e4411118001c00076858003604c1c80028044d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 18738792 1250 18737542 18737549
    0x90f0405010b1308010b03030405060913110a0216080c2103030c0304060e01200a091d01140a030f020103110403020405160801060c050303040f03140d051005060408060402010c02040204 81
    0x981884000725181c40302c20014048602d00c1c000003d80705a5130b407826802e0715013800c20a40d140e0410f01080001d8100040100803090300140003203080e4404031149002c5540302401d05002c0d040c003080c00d8500c9a01049a10a2031200c141c10581e4146003040c034680e07802403261a070b40115610b41440000d004008501201802c2507400e03240c884c0307000c80d241540f40c1c01c01c07241691490304010201c965103206101e001907046c514030740c402e01a000c19201d00c4050388005956000c0100185000581e425507000c1e4412480d4031811000c840d514194013826009140c070b41e0b00f880fa950781d11f82000051810025243d94550a09011412440001d00032409000307075030000e07400900303040400801d503d85043c08007110005450301306490b601c0740b82c00c50300c0b01c84007c03008019500c01c001141c0420801589007803181e110703107000c03c196600e66180100942018000e5424252500140300742e91036180f244d40042d003000c5d81d40c5801e151070442040d58a000241c03010f418006c1800b1600c09540b01c0c2c1d011078024 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 18740042 1250 18738792 18738799
    0x813020d140109051002090a0e0105010f030504080417060603070509070f030c021608011407030b0604050607020402070204140a051f060f030905010608032203080307120e06010905090c01090e010902090f 89
    0x202c030005079004003030340c000190350340b040c070030500003140f080c41225562b03040c2d500694074070040311545c5c07400744d00a10300984244e804100c140400110300d12514400da88c030320a003201906103030604505051070b242c6c4c0f581005110b882031a0801c842258081005010b047e0342d8500441e900c4102d4005070700b45050702d200e0032502d005442e808591541c054010440c1e480f00c11585805641d01d4520843c110381d002c0011a0f4003038400c2204104c549408c43c05050b103580010801898030a06600040032a6554070003120601c9228041000c02c0c255449160381c055428140302408542980900c0018602c0b4000c090a1040310015030900f10703c20741c00544201c1e0301000030007006032030b844d02d5541d0ba0801107403414540d0250711182d4140c1d000300451030480c1c0c6c1c408012811600c5000069070340c00000510f01144030b9450010300003d200c10040c8500138030b680e51001400f810200348a60800344a071907140e041c060964810051110316072440c0e411100341b0140141c44103481d800054910000005d00c075071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 18741292 1250 18740042 18740053
    0xa051803010c0915090501020606040b0604080102070b0405070602030301031a07020a020907020102041a1c020903121801031a030606041503050a08030a180c03020609010302040b0d050105010813020d14010905 91
    0x2ca25004900c110540b22144201a1134910740301d0112040035190052a0040e003140d000305205082c15002082000f00062419060a840f1402c50342280c000b21410382e02d00303200d20184414400140941d10291190b8800381d481c541c15a146c80e18a09104141c500341990080c0028621a10a01011408039801421040345040641000740070390010300480305d4030120004507400005542c003c8510541908095104000e280c055080003900020b214903058025030840702d950a00c0040288409481d0519022400840c1c0000400310349141b901400c2401c0d0080c449401581c00181301d0307074080402c95002c1400031031110b40ca1001816544010503c1c410311180c80100401da801a52058060703441c108030b50420b0081c0135030040d940000c0509000c4045c441130015007000c000070b100303141040c10050b14150b900c0c003401c4002d50215200c20005559800140820340e440300000b5008240c11040c003080d012146c00003102555602002452040c0f1198440280c0f8000e4221068554000d025180c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 18742542 1250 18741292 18741311
    0x2040c0201090b070c02010e10030e0303010f060f0804020f09040302010b0d05010b0f090f15060715050405161d04060b0402070506010f0b0703081302030a020312070c0503010608030a05180301 84
    0x78003800440a0031902c10388000001900d031803003184800001601603592403ca00c841e00180b01252100e503920404058980e2401d03c10302800300029030080800d0392400d6085032a0a1008201e0800194284200041141800056610300101311030141c8210388a0a003074a49140681c018a40716110039040406001c4001c180306040d4003c00606005503800c1c103d0761030102c100500c3c45001c0307500c04030602e12030004c62014941115420100031003e00f01c0f501c1c280140e11542d020204807040c6a203040c1e1100108804c200d41408180b4809070701c001ca10f1046801d013040107044180034141502c0e101c880c030000034180301c0190001000030602134011581e46030142001500e4070000d00a1000b640c1346c0c06000542020301008403480b95400da0740f00602c5441e0b00c1d01608862032b40a00590b414454144408051b0751305012041c0c2c01071854901ca50b4800d85480d02c0d1590440320381c0101c1c0702e640340050400c414107011084a804048500d06282d0307c000b0307844e424242070019407040350950318042804 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 18743792 1250 18742542 18742547
    0x7051306030611030106020a08072402071a040210030207020f1203040302010f02151503210405010e0109050a090207020a1a18041a010e270106170106020703080f0702040c 75
    0x540076240160010f002200a041c0709100070301c001c1c4600b5006034480c04880b40850880c01c06402070521510302c2c0f0501c10700790104900c407000401d40f8903180706d0380000c5100c1000b2034421240c000b100101c42d480308030718060700054030511060180a040c183c000814008564915002e0f51049000520000c2d1070302003a5501c5550b908640012400705070341803451a1003c1c00005c0b04004009009002c14a44d551004103600c12488840301d01c0e050721454203044103221a40a8500c4c0c0c0b250310b240b440d0303100da180c00b000420360600b0f0601076050107002d070010b1115886031091f220581e503c44d00050fa54528030320119804400d10780c4054541d0f0442111520f0003e0150010000b41882c0700d01c0524400d051800c0000329080c0380f010100c100c1c0c05125164103540180c041c002c0c0c892004050098002071055a4000104c00d804600c903070b4515a00140519908008400314007440c1c0c1c000908035604041c0e01940d61111800003426461001c43c0e03160a240d405411a84010360140080c480c209802402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 18745042 1250 18743792 18743801
    0x6030108010f0c0507150209040605060309010504052e0b030a150b091014150c01090c030b0901050708010b070c12030201200c0a0201050306060d150f06020115090b03070513 76
    0x254152a400d1890a4000c07600c00c00990f10b0280c1c02c0803c0d18a54090355050b06e0007580b0904505421035211080081c0a540b1003000e144280740d03200020950b4034003440d295040281842000d8180ea4040901d9981420b104060103030000510900081801c488030020303290109208008100700206041d00b00803201075081030300c442e5003c1c0c424108607111480c1c0400f11005a006200e04418401e0f136040c800d140010014141c1e2044480c59803801d80180380351400d49000580540d58000000b03410410040e04085140c0c2c00310440c3d008109500707010070002c04403601842680180000442c03400203108400500320300400000d84041d81000d440d1401901a02d10141d8041c0c00c85640c4100722a0703070440004441d4202d45081c00f4015483c0c5903030041d6416000a0070317140d00035000b0300586043c4080c5200307003520814400b04481d01c5516140d0240d0454410750000d20441e4186020805401c02903e180c0d415170309903440105003140e004010901d0324941e680016417041c44d1680402c0000980e501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 18746292 1250 18745042 18745061
    0x3180804031a060a03120c111201060e0a09020604031202070e0a050601030e0106050306070c030315080619060f0b030c1e13050a03020303090909070f03030f0f02010b010816030b0603010801 83
    0x84030325030342c0e10f040403c00045628480030309880f03035228000c0c5116104020f0851084d2145440c1800409180042020180144041e030030300c2e9074801c4180110404901015840000720b0018017150545030b0115125008070721004292910b1017001c1c0541d1170081c40a500584400e24404c085d52070108040c0c0d014040940d40c080c0441c2c0381041e16032070410180108016a98064020a404e48030203c044615032081602502015074510013521030340e40d440e08800041141d00000d2500341080b034a5215400f1846084800c3c0e1403a005042142d0181c003980001143c50007901142c80c1e0381ea6600c40400380c41110345d0612151010020158203e400d0409001d141c100380000d072030055224014008005014040a036056102742b0110300b5a1a00e5940f9640c04070824043d0742105c0d9884102000b91342d0305410450211f0b450340c0070410440d50003c2104c5000215100078001c0d04600070000e001c04601410901010004a141d041414041d030419043c403900902003070342c0c03981c0d03c04002d4001d0803040c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 18747542 1250 18746292 18746333
    0x1302070b04140307020d08090f030709050a14090c0103050a110304050114060a0f09020705030903070801090213020703120509030c161d0601050301170c09010b0c07150c02010318080403 81
    0x601c2c0c41c1c4003240010903226203e5004d04002c1d0340d400306441e502c0031074121740c002c1c0d42d201600e2100c802d2145ca090040c9002840102c101280301c2c1407140600e001d60307203c00308a40c81e94884004001e4040e80004a102440d48282800103064950a0445016200000c0c01250050002040c0001c01038158040d00d144507400d02c82c4001034a07218108041041d0501c10000426102c1c1c005100f8018264014007202e031041d0206c0b4945a0f01c1e001003400d04205a20803543d0782d42d20740c00b000941c2002c0104610140c22108210301c0d0080c00d5a014101da03410030700021086030b40c2d50000d041010100200c44100310124200e8070000d4401c0da09810000f01c6020b590131024845842c0408a0880240d07180902016180d01c0d007542c1c00d180c0241d12240a0301aa40501c0c40380d1600b12005445901401d8040d20b00754000c150b9aa10454801c3c0c54100030ba4400074003501015a003803802540504801001a8246400709074000e91120074921490000702c05003e03020002000800c000443d14048500c05199 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 18748792 1250 18747542 18747563
    0x6030807051513030e0307030609081905090105030a020a11030f07060e010501030201021c030f110406110718090c080303160206011403032a07080706110109020d060b1302070b04 78
    0x40000742e055480940d043c0020001111030400003a0240000d840c080e94043c0c100c401240d6251103a1080d141c8a401c1901c008d040081c0e42007181c41140ea124240a403036007029481e140903800001e01c9448001d015942980c0d004c149030020911138103054040e03800311002c607a280c08015070f1041c21548003000840f1200e140c4500c0d1224001c040c01098100c0b5016000350100c52080070105407622000300e280820540d41d6107018182e00300364810140b210341038040150b200d13410030101400c1c07582120f10042e0b1a52000004000ca210070b090541c802c4041e9031408240440e85103001080e071079154211040c24000801003001540b184007101204e803009508858160341e0768062a585404d403440e01035090f0f01b00b00156600020003801d68200c804030f40641079208000d0304070040c1400b81c07940161401d42c00012040090551010701c460766410240300800984803181d00080c031040136000b008021548480c91514035079a05800b8980095038400c05542e504401c1c5410b01910400320307030071200318081 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 18750042 1250 18748792 18748813
    0x5011509050904110d08030f0403200c0103020f04030602030a0b09060904030915050d090302070806011a090f03070e010306090203010c030605030a0b04211815020304060c03030b040603080705 84
    0x5000100403604094001c00442d100c0303844031401d102180354903a40201700008600006070343c2900461086c5000f4011190a090925000b2b045108a54844200f070001c03c120031510f2a000c264244c1424090070300694403e680c00409981e070055038400b0b032040f8800700030410208078a401450207004202c81040080e51442e080201300107007a1000f50009001c03080c28045620042003000810b001420290b003003c0001c0c000a082d00c044c1e010450040c0c101404c200041d220410500b03000d000c512569800404e020101e110050040d003404c244611454003000030a40c03030a000801c040c1504d45520022981c40c3c1c14200d01070300e400e400c124040d601c0c10480d80c3e20540b0a206410580780010090891040365458040d82c25001070301c151001640c148090050344010800c6c000d504089445103206020703c02c841000a29040d401908280000070310f883c90b00e42e020041384d081d54000c1c200241c6c0d402542c02d00f20f000b41b00d081051a041860031038048203014161020303209a51003170b0300711020002d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 18751292 1250 18750042 18750047
    0x20432041103030c0601210c0e06040605060f0702010e0303250c1d07020c0d030e01110f0316050f0106050603180102040b04030f050c010f0813050c040c03061e05210c0d06050115 78
    0x1130a0b030161581408230030911a4114006d0320a800c6840104080350b000e894000056603948064030301050a5400100d0344215604282e100500700811000380d410444140d0540960448150700305d0320134650000740404215606d45080c0241212030124403406021a080c8401d220007502d81d40c000d40309074560811540b4124031050880750340b41d501c00100341d00140040d03509180112146010740035407200b034140740404102801c0c0d503c211043e11708440c00c00d41029400c10310360082c4080213906155083c040c640b030b084112600640001007156012040345501402030156070000c1220300000907000043c0924441e130fa0340940c0c01032040d200b0a0154000544000100c2d0700004049415000044d80b01105030148c007021703d00820076074103140c0300ca000040807074281c2410071021070b03075404050040d4000d44c0c155021031803440044002c0b16080c00c002461640c05480c1c00180d5a84040c1d071403240c03800602c49001194406885480e4800c6c031803401d9806000c0034003a03010000441e4014561061 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 18752542 1250 18751292 18751349
    0x90603030e0105030703090501050702070f0506070203030f0a09091407090905090703030e010207180501090b01050a051611030d090602010e030403020a0b0904060e01080307020432041103030c0601 86
    0x25410307216100c140394514010348040c0c1000f040141490341e140d108201049082c014a40b0400307155018281c01810094040c0d0645035542040f401485c06105910040c0c5001048501d07504080e4502515180911800c0781c4441c0f0035040403105505150100000b00081d0900501800480e00d0301c440840d1902c030f940301202d0003180c0380001c680c810076042000c28040c18010f54203031010701c1030341c0c0002d803a0454401d5807000d18004001c100e6070740c80108100c440301d1140c0300f01042c00340381c074a103001c82c0c003032008180d8014441c6050103450403490303010400842c44003000041c44040c5c1078842c84e031104080038002103124880c1078099400d004150f019407002200b107500b40d0354004e00110b911820308c02c494010b038000001c2e541d08159107003804505404031000d2140204100e4006564030503240c818401039402e00440d820507001c2e0342024103a000c0c0041c00c40910204068012440c6941e035003809031298500030000c039058000003480402900c8080740081c186c9d220040e0340011041c0040e002c18154 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 18753792 1250 18752542 18752549
    0x213050403201e0a02030705060c0d0806040f06030b06030606010801051005030c0c0105040507080d05030403050f03150402030a02040801051501090b180307060c030e010809060a180501050f010f0906 87
    0x8a500044110b080085034040c2902c1d041e00c0d084a07042003030b440b05181c0c0e0701000e01c8850610383c07141c94400110b24082001078042c107401d43d091420646075000b41590f4562100804003881100800516280c417154054840c02d11202001d00c0819501e00700104212400c1d03602c1070003070141100003002e41d4010030b080750488402a18007400b8010312203007164983c00140260308540e104001d400c01212007409200e000d94069805040c8071450031595038500081c0000031424070900f40100404a0b07080010f68108480e110411583c1e6030350100550200720803c4407031907006102000f848003901265001e402a200d80c000200321548510b0000000d090081074018000346120800380081c081c02000742600190842240d13221701440d000103401c0c0300c82c642120001640c0c1400040038907500842c5207a110200303091030001030900c010398640340d0307400900502419445440500c4811001c0c6984116103402a0080045003040026484038a40a11410588100000c07000ca030b42c810130710988089 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 18755042 1250 18753792 18753797
    0x1030510080d0516231b0901060e040209150301050f0102010504080702010c0c0806071d090403020706031a040204080705010905031501060311070503181302180f0a08070603090213050403 82
    0x30b01c010140308907031940c4400800c2d00600e0448011000043e2040c80b6100350101c0b000d80755031100400703604c16140c04420141000842d1000c1c14000041d191891b0050542e007992a018812101030741c0400c010344034580e592600001c101145101e0310701000051416200c08030751810041d0540f0004909840e0180c5c0c0180540c0030401000c001580500014050f0b00c0c03182d1811503040d0794800e0308900340700c0c0032192207010640034210a407401075090302100344c2c520102c480800a0906480081d07a034811806650706040e07941d0076480240940e00c00704061500001c10a6690360f0321022106d440b46507501c11a40828500700c80483d9614001c50302d1112a000043d20007032603844c12204402038804000b008076241c60800100000c50424002415507140725140c10840c21a01c02c01d104600c08001190781e8542d2062051442d01e00c1e5010079509001412203481003900c41e1940000e00d072a04540c07200e0034610584000040d02c54258010301000c038000c4892500036040600e14100340c0e80c3c1281e00030700 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 18756292 1250 18755042 18755053
    0x30e061302120a03020c0d23010c0e041e110405030d050405040c08010303051602180c0304020109050a0503030a050c030d0c020a030f05070804061d030607090f0b120105090702010207200103051008 86
    0x1203030b0a04a1034880c0590060821410b08010f041072314002c07900601e4a00481c0c1d46414000c0703070f59508090042c000d1a0300f609c0401c881e68141004198070b8411001c00b00600741c0f60380540c840031121505460103800000c082d50000c00c82d081d0060460b51041c8913250080c0d040011003200079000d650a2412660162145480c040c24401c01c03039034503640608103c2e8060740003c42050144d5a501e0307420f09c10303d07507940e1039036607410b0a00002d000d11140d68040d034814811860144040c1e100402a1122081c190500320340700e16212802c2c0d8218058008140c4090f413508501d014103d5001038660000d502944402c40e401d800d940049a5a1081c0f82001e0148001000b081008521a80c107a840b9030008820010110f620b8000103810180203488400004190392814000102e1000351400101042844103140248460031702d408000140308a601c01c00000e800190018000e40403502c04a90044030610240c041444001400e50b10203a510300080c40d03d00000c00140a00c0800016036000000a10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 18757542 1250 18756292 18756313
    0x14031302010f02190602030609060901050102030a0e030c10020a031e05070209060102100905030a09140306010302010c0201050403120306140f0a090f0906020c0d260105010c03030e061302120a0302 86
    0x11801481041140d0852051300e100030001a8514502d181c82486400050796a047c14420011350010240c2551721424561004001907a00041103410307005040c105022680e1580300046d09240140c10800e4000380c1440c1c0040b41c0c0780c4e0101b4407030800c51081e1100307420100c240c1c14400b80c0c00b40c00854507000c20402c000003c094640003010a80c08001441103e01c4194058103074804e803600102e0442c0c8660010803107000c4182c1002101024000c0c200f4141d8142030100d0001f07640e8201071002a05010182075081c0075a4031580c00c450245401c10070784a02158440801030007090315200d60350302c0c004800e141c0509460302c1d000702d1600304801002003000703e007004190720091880100f03003070302a9912007000c80019018000340110a1440014019000445d0f4018000040404102030342140d43c9101c0001d15078420040c80c10f607131080c03902a4421880d481d065006042010b111241485107000b0841500011694050f03400c2c403e95070030024100030403186544000c4d165005000d03801c0342c08803a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 18758792 1250 18757542 18757547
    0x1030b010504091e050106030b071403041104060b0a0906080c0703051b0102090a09020913090f080a140d0509070f0f090f090602130e01050901030b13050c12030403031403130201 78
    0x100e00e0b10300800310ba0300d1283c2c8040d107004c280030844804031703000d94440004005001110f480c09611240c1d0b420011981e0003e084104a1480b0040004000090500c04a1890f45456001c0e502920544840c9a9180c11094020300403038040c1c0300d10b400040c0c0c0200001c042401c140d0598402941c0358650340c0c14400000031742a21321b8100c41410780b5a44d400d001449159903100e0f0190010252103800582e81e014000a000540510300c0e0071300d06807800c0441c0c2c00002208a41c504101700e030452442a2201d4844004641c0326101125195140602184102d600c078015444540101c2040048890712a0380708881111a485486000c0001200650400c1020303040c0c0c000d1003241d12103181c0081c511000d0307030350b0800f2600401c00140e0303150512041401741144510000f8090681102c0d40d106541c99a07440d0341e4003400080042c40344084030300401e0b003002803c00c11000000c500808507401000c03041c41d0503560340c102d403106800190b407604004038510b4201040302e0143e040e44c01da110b11035060750010b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 18760042 1250 18758792 18758801
    0x60c11060d0b1005070605090f03040308130315050108010b0f060306100e0a03050708061b070f060e070b091318120504030605010902070311030a0e1509030a060b030d020601030b010504 81
    0x14800099190741e0301801eaaa0351a0340d83d032010301c0c83d40b00c00b91158210305000049500060803824241c2c06040c141401000001c151030032240e1107520b00d9035521040307160000b04038461340028a002000000b002c42604241c2256042c0e660100003008050b500e60100301c0d00c04c1031041d0254008204001250076070420340010404951542400102015441c1c089126070f6041e0703100b5100354005003c18448440c0134042c464110441d048228080d0004443e802e802d4402c8010042c8810300e450455030800c11030350002e41c95406400280da03005680e401c44200942d0048640610568408801095801581c400c204001203418800701d902080c1d5544d151907442d01414290510206000000c00078000d405114060084207030050b03115500c503d009840b980110f08940116001408009002580401040080300381100e10071190302026500c06428803407045495014020640c8030005d20082c0c1e0402d03080c40c1015000c403405184400400c0340c4032071080c0002001c90b241c0c080100b00d180b4003900b1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 18761292 1250 18760042 18760057
    0x30105040f060b040b031b01020c01050301060207060e01090312030603060c091202060c0a0804030c03020f04020a08060108060111030d02040e010e0105090a050a061502060f010f050d0611090607140106060c1106 92
    0x964002d100300002c7c500301402c251241c0404a00e002900d03556414072465400c01400c0c2051403e55040c5800a9114a921300401040101418801203182c1c81070300f14a0003150460103052850030601001805000d42e030005440701400c01c2558841244503001a004480060800342d505a049600700701d442e44c003040700d103a030754401c00480308040f5a03c40024001503110740c160b88142451403042c020000d40124074540300c0c504c10f001d0012410b40140c2501d070312203001d00e0501926526100180c03541016285013079203a1101081d05800c652840d8024403e9801802c0008107aa82e180f50341e40700ca9000340201a08000d24134003068070000346070440c41e00070300d41000116100d40c40d615440c2d44000a89111001680041c00b4002440420b41900e8050031042c20302540441c2400d020603070307089404a000703110940d0b52413018014041c150a40d4642c1d0001032003560782d070600d4100021100703034a807003a00c450b518200e00080c100d1b00600e1510324541e0b00080b0020249040c80801c03106030490030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 18762542 1250 18761292 18761299
    0x30506030705060309030711010203162a0b0d0f06080307030807050720010f0309050c010c0204090b01060509030d0804020f061c0e030c010e0a0c050d1a04030201020711030105040f060b 81
    0x581c082000da940402541c0308000c841d00954550b0014200281d50041c0321803032034103640041000101e808071175042400c2142c1c200c41c104c41169000d01d07030740006109004041e02112544540441c10b00c150a00901d14050016000d1002c190041114402c40b00244200740d02584100030b0360000074040c00b0820b60010032030a1450030301007151503060304401200d1100398101c002c0a603030482c540c1c1050100b40030002700d00c0d00300301c1581c042c0d68003a0b0b62142c070003005051040c581ca40408655654000004003a031009071503000b541c0d2180c010b0b003c0c1c0c20021107a4400d001c0d00e2003500c0744a204006451240350014640c0072013084100c2445007940c047c84c401c1c8240100100440b242c00d4007070042034003105101005540d503200840c00c40c1d00311741c112022005290010007040011660f0559a8810780350102c404004c044660b18210f101380040b00203180a8544000c20001415010b602a0521034000c0c0c401c140c202c684031042608a031801c0301c00a204e900d000e601500403071020362109444d142c0c0034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 18763792 1250 18762542 18762553
    0x3060115020a12030f1103090c01120b0402040815010501020d020304050f04060312020c01090801060803030c0a05070209130308010605090924030a08070c060903020105071401110309030307080906010b070303050603 94
    0x1034840c1e00c00b04083c200040082911154002d10800d614440d4800740c05180c5200c3d03045081400e04991224419802e0300d040000c460441d0f1030000d1690710035840210300402c01c541d655904e0410548031810101c0d101034481d5150000036081d400414040704480055010b50300c0c19040000304102d545c900c0e0390054000759111004400a5440c1c0c00340e0b104040c658000304809822580018100c101382d80040c40c0c3c03641031a00c01c22680f1000000d5a42003081202c260b83c503602c0d0742904960314043c2c941c001c1d41c0404602c09111040d0140002800c086000390703521001b44e81c80d680c1c103403001d2248202c00d84d0080c07100d5000a001540c0005440d80306a0091640709035080c1c680c0000b450a054510150f6151000082e68810081c0e1441000010840390038105101c40c030350740010303115006009000d403480b12041c4581c03040040a500100b81a44800441d40c1c0340d00340104510381d00c1d001240c2c0d16000c200014081240071000243d542e0490300c030b1710116842d05425603004c070041c0402070325032905407040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 18765042 1250 18763792 18763813
    0x60405150408070606060513080c0d03051606060f03031205010f03030e01090e0a0b040b0405070f05030910020307080702010b0409050616090801020f19031e0513060518070608060306011502 83
    0x13075009890041c01c069884544071001c4604030000f660031a0b1080d4410b600a040f900e030140c0700e55400c080d0058140c2005911040a60351010700c00082c8d0710f0080049250410210b1680410120402501c2c0a40d03201c04074504200351301c0040790021300074220101c01140c07003040064407841c45800442e80602d004210300f40d072100058001901611401110707525404c030311040313003407510913507005a03403c44d02448241403c10b0702038111144010104100803002000640c1b440d03007040700070f40400400e032045640e4500078100070036041c0240c5d0031500650a15900c07548a02c0c1c180560a04c00c0d8100d400f610142d21012904410302ca21000d00c3c7c030030720144002c0080c00d50001c0c4082c140701401e4052140e504e84020386003415180301d04070510241440d0911100442c02041700b00c00d00c2990301c044c000746a40740c001140c000c00b045090001c1c40c260130a410020204140030003c5100c842c000e0407a01c5150f01d0703c9003a1082d00084882c2901f69000a0040091103070480740703101040302e6401501d440501 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 18766292 1250 18765042 18765053
    0x1020702032e050c0405010c03050408030c0102040504050a05040b061e152101120609110904060f0b1017040c0305060403030e0d05040602030901030f020409140a0e06040515040807 79
    0xc02d850304074200c003a01441d45500100b05000da002d85092407004020038034102110015a006500550b410002510002c40402d8080e0044902620703030b41c41180d0311b80300b015400e940030f5803003805014096414500440c8140985000f400d0003240d2244040301c090350b80c081403103104016241d0150b000c00c030040a014468940800c1030680c0d1020261040c1e5400d0703001c0e1001c4404500d1030108007802001c01c01040084048030724112196840900461800078505040c41860252460390790b00210204c180700400407154002d00200100315014441d40c01e1002c10021500700008064000c80d03072185c0d0001942d01e185031902c1c0c0c414812928000c003039880f610b0361403030050100c8044020940d182c0c07410417aa41c0422140810414514200d85403134241100207443e13004909805042c9a12044c1c6409c1c00d103846e405490103003400840c10000c2412012420074450416214146451314128041c9068800801d0261266030460000d2214000100c0c4030000d01000510544440005200000c0080c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 18767542 1250 18766292 18766303
    0x8040504020408010e120918072607031104080309010509120303010e0a05010f0b040b0307030605040c020a020a08010506011b030201020c010c17070e101b050f01090317040803060f01020102070203 86
    0x140000141710051062054a04001d03120441d10035103090000480c6035540e0815804a4501d090014959454690301541c6595035111a602c80350400c90340d51100c5c4040c640442d00c80c4e40995014010140c0201e201a00c1f07110364055a4000e410402058002d540500001c009503000070700b102c10b0b1903848040c141e0850b0020b8001c951050181010f10828880c80e0003a42d016140069a0040d202c2c90001c2c0e040013480750b8440c0d0188003001000240c90309000c6d901040c020407018100b4090000000402905c0741c1d4042c1081348200c803050004202c1800c140b18452103204107841d05c01a99045900b401403100703411034100c1c21903400f040a1a0103203420700903d01c407852982c0b1080c0030141c2803002c1848001300104070704100150420401070307550300c040c540d05628443d828600c8515803903000a105614111501800e24030910304c030400801c005601c0080018005d0350703136820f0307087c3d62550200320003010750300900740600c00c1c0040703240ca1030801c0500503900c005000040c13901100781d02003400d05 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 18768792 1250 18767542 18767549
    0x3020a17030105030c0d06091b1802090a09021b030406050409050601030911060c0a0507080d110304080c010e0604091d060702030903070e22050f10090503090d080405040204 76
    0x58118016420820540012904544850141890456040a000c640d50b038044940640c13040442d6254030040c04625801040304641110701c0c0341c140700074000b80c0048681c2c20321400e54580700038042d545050a4074401da0305401d10090081c84070610308034100d4080d401010000c01c01d20410505030408040400040c07000741050707200c2980381c500d003815604c200c810040285041c14141400386000074803844205114000c116000c5031218030403003143d442d00650300002050740c4034243e00030540546c0000c11101440050b42c030803444103007455440f41c480c0180d11504040360701000b107034891503009410391118107101410302c030304180e640c0405005681000e1011800c0c076000002e840b004d14070500c1040e034011004d0008601e424043e00229550342c0451055200c540281004114040c0303070500194100d800741c800c1030380c42e90243e042003900d070200b41d0710526152007040082e00441d00766014196981d03404c000034505002440c01400156550780100f110b0300c44041102040381e58681c40580080e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 18770042 1250 18768792 18768797
    0x309010501030201030f0b0918010f06080313050a0b03070f1205040305130905270a02030a03050c0c0f01050406030b01090b1b010b090f01050105071b030b1609061d15040303 76
    0xd540740d0700014013240c00d030749070a2a5a604181b45090300d92208140d0b907070417803221200301d420351046510407030042c6049140504101d00381200010110b50010240c400da0040380d481d150440e940d03070104070145805200d0800c6000b400d10004481d20301611200c00d95440d9401e00c8140303003070300704040011038504407030450202d40003082823090281100342c482e018264541e010440d134200003002800401941c01e0082d040d00702e41501004129040c0008444035602904580b00b03d40e50b480d01a216400c2215411158814200400d00c54502049250300702e00c01a124a46040e040a00031409855080c988a060150000d0f00260315000a4000c0000c0014032119408400055a040742540c0c10020b40034840ca81d814140113503484c0c40300815045407000d08005954001038580307105105602d402d21280f009107000000103120100e4410780c4175414018030031019103810442520b05000030700401001400d4180c8924080410340b1411528941c010003020424900741960011030384141c008500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 18771292 1250 18770042 18770051
    0x30312092108090c03070504020a02010207020301060b0715020a051204020f09070203030a0606031104060c15020304050105040b06040504150b06070501050a02220b25140c0f01020307050a021302040b030901 90
    0x2201c0354031244580c1c00049080182000c04420000a50760304c5282c0201c502c07031640010003080042c002d504449213103501030000d02c443c6a0b05c0304065040d412000003503030340194031040c0680181591003110421800d1362249418422a00e515042d01000240101e0300074483d4407071034445a403903a155910803a5640e0040d6580e14050507080c3c2a15150f0740940c00b4941005010b0101c2c500940c10340b0309031040b81c5810f03020140c8500340f01c1101d03a1040e03585c00c40d06200009000500c80190001841580121800c9080c0c1e242c180511088034006c0b180035240901d0025000109030070b58000031021800100010304084141d19003500b100c0c000d0311068111396001642483c03901c10400c520701c1c00c80c05d5407892092503140444d1440103205003800c145400d000c611a60412024820040146980006c0c0c500e801d2041501e1003959402e90704d0701980b044048120b00212503100200700c461142c0d001e03018010403003103642804480540e0349502010103400740004140c44007a4030103503200b4043d0000114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 18772542 1250 18771292 18771353
    0x304110f01030606050d02070606120c0501090b030105012f01020a0801090b0f0a09050a11040303050711220902030a0210020714090c0414030c060a0903140a050703031209 75
    0xc905060500c40300e0525081440800203650441d060f503904510080d0056038881462400600a042c150060345040d410441e829081c000e0000201041d500e007030300c81004140e155590504640824031031140000d45040b0141e086025a0f800c0030301021070f41c540e00a022000d00c50705401c1e0b0300003090901c0080c041d440104500903c41c0110095880241c82c00744d44059401c01003a40e4420318003402d600e80e501c880100b4203103c2180d010907044800c0c10203d50700d440c0c80e4239000b441944844c0d002d850158003c08400b1441c03800c10b04418588034085080d80b203030100541c407000580704088003a0703818060700c0e1070980035803a2455128040c207655809060a0750a2200a00402c4030010846d8011b00302e0008101e405051076080703030280d0365680380d006d813007082c0c0a0009161600300282d035a00301d90081080400070340c02079004001e60b442100300003410312941c8022640c0384680c0801400b140d0001c0b00070008240203003050003011080002c0450001215120074860502c031071141c00586800c141840c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 18773792 1250 18772542 18772549
    0x20f070506010905040302030a11070308031003060c0201050106021e15010b03010f1e0905090c03010920030102090904030305190603030207150509090c030a0905070905070905030d050a03050406060803030411 91
    0x46000d00383c6848100030f141010b89000355a8090107403510b00f03001c4840c000664402040041c04001c5900c59190740ea08d14080c8503010b80400c1a1004403207107402c00041c00c0e201070060040c64141c6400da130041a03030300412103181e0041c000700c0c4e1048030700b40600006805460f440e0140580a40484900560740c2c0d4034000640c03c10414030303488440303c213038032900000015011180c00811180d00c524049200d89481012908000c1e0006800d80d05620748581c400411144020b43c100d2100e26003858251841d0200c00d01d4240d1242c440d1055001c1d00840000340002c1c003d07400300b0f8000c0744443c2101c1d494028800a00d007140e14070740058003d80e0000000704440e401460070800c1c080301c1890240e003000e0710380010580786040500802c0c403081c004400034000320b8080c1d021204041d04a170072601501d0303031010403200808041d1221030010300401000b2480341000200d20b051500103a480d20324080d1110011801410082c004443e10340c0c8404000510940410245018900881022041c4100b00040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 18775042 1250 18773792 18773803
    0x9050c0403030908120405270406090201080106140f030907050604060305061905030c01030902040e010c0e09070305070f0e0409020d0812060301060506120c0403050609100c090b0f0c0a06020f0705 86
    0x103100d40c0300680c0a5405d54099040c1c1e01268400d0325800d00090300f6181d16442d0450021039800390300c91400400c014414070f80c025110050003030b00c0d04103040c0d8840404842c2c14850b0f42c5641c010000821001d003100170800c000703551201c0e400041c0c0e841d1070340300c1d400a81c80354055030021740000c0c0c42c0c900340807442c9030100c4041c0e0207400e01940e0062052030700c001f20b9103d02400444505041d03540310641e095403a25000a1890041100208201d0006100141072401c44605042c0141d540200088202d03000f8858203015008989031003030f001c0c0c0c6080044585120a404560308a92034952080050f1a4010b80070380c0d0600c03031203a00d41c4442d211018003600b1b54005202510983c104041008152503c030b08465500b45200004030b12a039445040100d07901c12079100038294803900007080090407022480a8070f0748400fa106201d045038030340003110040301d90301960034040c404015240300780142e08010411042040161060780c01252160310403030300184d03d074440c168070026400040101c00e000c1d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 18776292 1250 18775042 18775049
    0x20705030307020a0e040309031506080f061302100e040203040b01080d18061407020310050601080a1a0f03012003100b0c0a020609060c010609090204051608071809050c04030309 78
    0x9500b070080c25000115001445c2c854411290280008281454854010300005c0c54200c41d400d100925130b01e1200c0001d0a062141c8225070040c0809034401c6171021403528020000e41a900508680742d800308040004c01501c8003080c007001c40b1551800b0303207580c0003552245010342e00c1c0c01c2c415850150410304102c002010501000300c800c14170b40480c01078001d00e0050300c40c50b1074114214051000243c00da4468000041d50500c1a5183c42090480301d4020501c2039800380d855005946541000c64280c802c1e00d0140005c110580c41810300d28180181c401240740d1004001040304072070718090040e10445a0fa603001001c0740042000b001c081081b0741c5000a0044010361032a000e104c03016a51101c02d00c8034001e100d020000b51010150307039604203991403050a5402001403903504ca0382c12006048102c003c0b030040742018005180c0c1c07038101e046003c00d079203242c41c0c1d44020b69030407104413005100e0303036107901c0c400c500c01034007141031203403442100e01c2140d4103810155102d00394280504503104541c0f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 18777542 1250 18776292 18776299
    0xc060905030316050a090608150312070215040b07081602061315050a0e04090201050403050f01050f0f06010f0804020a091a040e0c0d0303090c0312030b09010605030108120c01090b0708010303020705 87
    0x1025441070f601070342505c111f60031890030203d152229441d10040026900318a40d0610030460200b500304c08103001450903a1003256038016040480c0410034183c000ca10a40711450000c1c8080c2c0003180c142002080041c1840241e013001c92001d90004000350820000b20840400c07012041c0b0016206403c0c1e03152850301810400d0410345040d00080c01c0c00d0320004014055a194100401107902450030b03640519440710070340e511b8a174030300301d1103000741001c540c0d04030b0200052022483c2014001001d03801a070041e561880c0c0745100020542d64440060002c9820010300000060001c03064403804071100380b9072581d9607511750325408100c150340414821092a40098040b06100e5070783c02560ba014540c5424003042641e20381c01e1480400310a640b0140c40c03884140c040c65401075041c0d001181c82c079001c44482007103980790203080394640000d0041c007081da404010003840190001c000350041003114400490015181d03611307400341c0c500548150340400c3c1910018001c05405000303940103400c00742c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 18778792 1250 18777542 18777547
    0x3010b0619031802040516020c06070803151305131a090c1002030f0307031b030506030304180204050a060f200d110c030609030a020d090e06040c0c06090503031605 72
    0x200c0d0300a10a40350715480040c15580c0000da0080700c414041070b145075800800400c4a0719244160111083c820f0b20440014064140c6406245c685003003550b059030b0300404082d084d5074694080c030299101c000c10640e4800d1441c420b42c851b40510b030003420b100f00c110404d02d0b00c3c0310707085181400440f9905c0c6010b01c00c444440c010000d101c030001031041004070007110141e214900d003d00690545c800c2c40000c081f06040003080000540c1c25820620070080e0b90610726144144860003241140c900341c0b0030b035905400420040160b50000340301e0203103600440074018074103551500026039100791a4080300200315070171381c4d0003001c81d0000d81042c550b0f0800d01500001001d00c00100f078441d8854035990041c840103081c41d18600344c00300900000c88201404a6a09042c880203d60752a000341c20100018400c02d00150f41440c0300e680c05d60101c4080200b00c3d44903860b5502040041c0902c3d10500080004d04908100030450340d000700d5107401d0040024607540d0405480000010044005640500c0300c00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 18780042 1250 18778792 18778807
    0x70605040810050402061201030b0708070503040506010605090310020301030b01050f03031c091103010e2d100b0d020a0e0f0f01050d060c03150803120a060602030a0503060109030b0a0b03010b06 85
    0x85445400200084000100b41d42c817880003072554000c24403055410402480040100004008841c0c000d0190b07846164003666411000c0b2014802114010041d400c001c00400c4000d00440c041c20080f400241a5850380c1200302d10441280c00c04d80c41542e400341500010401418585864440c1c94019000713580f4140c00c00c02020903600c40c0c2d005907050142d07103402c80010b000040040d810040d0f00100203100032440c41110075034406048135040380d452500241221603800051154080c442994041d00c071407035142402d08000c1110008481e0050720825210005903280e448102c06002c0f520304440b65030412604600c0b10380e0000b8103080d10002d2500043c002e55903100c030f15230301043d030204000c642c1840c03542c400c5003d090030301d071250310001c640000400c0c41a000720140c400c0c2c00c820007400c00f40e5610b40600c00140c0302e05200d0340005d40c00070418020081e1240c001558440418185640c5031a542c2c0d6412402800c2225610b00d0310f81d4403039500c20b03141b03404e00820700700381b004840722400c0210 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 18781292 1250 18780042 18780059
    0xf0c040e0a03050427050a0b040b010306060e120a0611040305151b070f020406080a06201603090b0a0504081603150b030a1208011d01030b01030602030a0213061107060504 75
    0x1503005d24444400401c0705603960f030717036025400a0f03022031080c418800c5007040403140d0042c0c4030b0300e1055481141448806d20581d41301c6d12610080b04c0880d600d4040700302d01700c800d00c00d0303d00c140d142510b00c9020f44e0410b400400c1c91405044441402e00c01c025544501d5810501d0420401300e58424100703020030203015a03101401d040d40e40e0302e88a0f070352017599400745103804240c0b187d045070025086030130310b0b44c0001c00d94004203065407102d0092905000d080c0e1080148851030046003003400d020b02c1c1c20300103a40d480d003491900da02030b28071034141181c240d41c81d9038481c0d1b899003082c024400002c90004050107030690030300c400900b40161410315480b00303041d03075034039001c200c440c0c0c404800d50f40e80c030600540e40b9a010000e07000a242c00c00c030001c0c0c0d080d40c0504001c041950901402303408010031404500005500c403402812640c2116107014681d085a840c0c1002e50b1002d00302c1c030001e030740a01080c00510300c14074410005000a413211030814080c0072449007000b4083c2c1c05001403142c00c1c40100200c0301c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 18782542 1250 18781292 18781297
    0x6090a080d0b030c0907030605011103030919080d05090703060e03090d080d020f1308070501170403081e0f04120309050a0210030908030408090301050c070f0308070e030f0c040e0a0305 81
    0xc1c240c00001c9484103101011a01d0180c0901c04254001060000e01c02500d4150f4861015200c0c2a0303681c90b030058964040c01d40d00c4c4407d4440284661140c0c007410030b410b0160303117224043c500c07520181d0b00d05101162031078242c3e5801e584c601d40700d400404040013045424400c0034000d040710b0b4061800c2881722800202d100b840d600d4040d00710507002602e40a121100d50440d640010401d841c00d440b080c81c0158401c1050300c5008030202d500c50150003081a40c054091890000042040c5912a50f916074003207607003080184c84816401c250380300b4a4103103000d90004a2042c8180622206149070078104000b240380c01000c50424180341c110510081140450400017040e0192181050074a1001c801c034024000160041c004580200512081089000082c16401d00c110000c0c8059150401e4a08040c0707d44040100880c0f0303104000c0c00046e014000c0143d0249a5060000e55000c00034007080c1000b0090303094031295080701500300381c58981032150b01014880c0320020410700e14030760b60140551 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 18783792 1250 18782542 18782557
    0x1050609040b04030e0a091d010f1104060507051507030906060501080702030a050711030307030909140c1204030e1e0108010f1505030a020c010c080603100b06030a0b06130e01060206090a08 83
    0x451710100807003043d190816024001c2040c000c08104520110643c091702080740810005c182d42020071211b07520510703000307121100c0c0b4804900e616161408106858591040004403411300034000396200d001c07070f007a840d14462020b030780780441c2c6500c2902d00041182e00d1508203c2c1401020400d018146034000251a41c80c191401d0207940e42c2514284100c109000e2010158184400030f034882c101640028890115002000203200b4500d03052200c40f0503207011914490030032001c0c8000d440034111503501e150414028105041901d002d5400b01e1283c141000d4410035600403000203880c2d65900c140500d0041c04294142c520440c105010240705025110b02401001404000f1032000400c60b030444420542460080007854000c0b000500034010032540d681c0b2038043c0c0d5003c03425211041c0651064040028078003407855540c81d4014004048030b2132141c1d04000288000512003545030181800782c400d40015003025858030800900d0701d00d0003021600c4940200345400009034064042c0c4070310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 18785042 1250 18783792 18783797
    0x111010e0c0607060605030a081e030603061306020c0601060503010f0e0c03060105030414060f0a05010e06030d050309071205070509010b070308060409080c0d030c031b0806100e0310060801050609040b0403 90
    0xf0303008a82802009400c69802c5030741d0602401c1008000c025540f002080c042c40741d0040b002014810002510a501040741c0c440d406d078000d1000180401142660303420707414801c40c001402c18040109240c94120240c100c1c01c041640000103000d41c03441032035a40000c0243c0000790526207808041814103000160600d0305104010000c50104405040d49104120030a81180d03101d00e0700008404050f4029901c11540d9860f210010489455580140784240400313401061074181092044610740e01c001c0c032460701801280d0010551205440c00d061050740603000a1600e282000c0821600c100180d000c441c4408041055000094102e421180d11240803580010039500506280e0150302c1014948219400351405404001c0c0d090341c081ca07512070303059408000d01d814030080c0c1c0f64081c0750a1103030404100c251000980910b040c103480c800000741813a0020845016401180c40c10b1a24285400c2c055200d01007409103070001d03c6180d0f4030080031681a0400d0500ba140e4454010010b03001404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 18786292 1250 18785042 18785047
    0x20f0a050105041a0c030c0c09060409050d0c0c12030302040305010b010201091502070c150201051f051305090111040e0106320c0c0303131a280306030203010507030b0111010e0c06 79
    0x25104d41c0c0030251048600e007a4240d0b80d4030298004601c2d2070b150059080b61003400c40101207080b90030715104200a04d0381c80b50041c0303800c40d2038040650711440c0240044903400d482c00d4000c04c1014108551500ca02d20a0314090307216800c41c64140d095410100c00c1c5411a0b1606860340d01003041110340b20814440e48030016901c459500702010030441c660091480b11002c8500342220640c158171181c8a150700700e442524003209030f080f0b0303180304005104d9154000005041c0c81d09030521980015003200e503107030000070561428004c1106c00e030132035403216801b0002107004110b0a50014400a60500006031010101c000194a4402402d88000c0c007512180c010491040e802030030030045000140080c1100c0c0c8584c9000e0442480d084140600c1460070318400049072207035106d00a4a02c404208038600b41c86600d0109500340d1605000ca15008068403010000003684081c8100360188000b40d401003002800440003401046202101408680c074100d0303503070f50b030320008a005000c145084401d10b5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 18787542 1250 18786292 18786329
    0x16171b010e2101110405090906090c010e0109050901030f14010e0312060301150e010510050c0c04090201050d05010b0d0506010c030f050904020405090903030601020613051b15030a09020f0a05010504 87
    0x10010410705490140543ca8034007611302d14003000024004840e804c84900e806a61000b49042d103a000a036921907181d4000c180c001407540c01400c88158062040c5064645076a0703500c00500951420b9005480c0c0042c1021079100344904400011002d0151000a10148004c07190321543d074071400c00050422003070840450010341e401c5d0482d5000c0b00e04a08841e0070b480e240c1c0c1c00e00e0241c1c2c0082c45451320135012058001000c5000c1c00a6a840c90512000307010b1401002d422b0002801054030102d040003410404280042500e00c40c0c10701914803642300a844d4541000c40d9001c940b4041c041038144004800d440b8006030307220b4541e0062148600c1d00c0c68031a41040302050190180341c0004c1e07807040c00c031010010100000006144656001d9088812944415001c8203000300782d59030281c01c640140446074115400c0c41072089a03d000030340480700340e030007110700407546070410350b140d00d81071f0f460750038610540c90700b50560004120215801400b1515100001e801407040e0701c240d050f10381d8100c1c0c804 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 18788792 1250 18787542 18787579
    0x50a050f04090c030605030708011a06030402030c0d05010207171204061d07060e0a0504020301030206040b0a020a0f030206060901050603160318081c0f0b090408070516171b010e 78
    0x260028a02402d0901c424010040094084c200328007a0310f020388070301c1100144c030300014000d00884095090360035000070384000900140d0740c0003c109076058858004d0803822a02c52080d01d0078198040d0000689880d010301e08044400301c00b2042c8000c440041c040350f4800d41c0782000441e0055840328000070401f40c40041020380d24802c611000315800340b0803000408980100d200c00642d01c00329100407002d5124401c03c8100e020030b01010b034000d0010700041c05020305141c010038840c43c0a0045410030351880c0c2c1d99010401900340e00320f006802200078800641040401503000d054100c0c0e5940c19460a00780700086406407090040c00c04d40c480e038410710f02091400ca4411815040103078140e940070400c481c84c070300703c2c100e4982840862400b52080c070491458420701020460040c107800803a181ca44410751342d40c100c40b1040d40e45008030b040c108800c3c81c500480e0401000c18900174101c1c1c076500324150b420484030700d4810300035034950b9401029580e44540720405a58045400c034160b5040d90005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 18790042 1250 18788792 18788797
    0x1309050c0604080109050106120f02010f0203090627040504080a0e0604050907020303060126010302010c061401080106080c030a1101050c0a0b010602010614040b030703060b18010e0a050105090403050a050f 90
    0x841c1c001c00005004225143c045d044040180e004000a1010564480c0304a01c0d100101074050f0841060b0070001c1300642c45820741046010051040700d04000c0c80c0c0d00000c001d90302c150342e4880c00360001c030b40e5a0340722040048203a030ba060044404002c10714203500c0e0400307940b040720f440c40c04002c0313032208902c41540c0f0802524060700025004102a28004174040d40e40d500c1541c502c2d0110b01c0e052024169550b4560f5012003202c6481f80d450080d903e56401901c40c80190307441107912a80341c040942d6240356a1516500a110500c00403503160314180741d10382482d4030541101c2c02032b0002c4012002107150041a00b030a00300c2840e09687d56400c08100030b00b07100044500611010364200000340c000c1e4150404000d0342d0020101c00e00c0e0b50314260800048500f003006641d00f54200510400100342c0c0303940240700c00c007000f8020140300d043e2030840b0311610030b090708008180748200d414084844020300c541c50144c0030917030703580156040503103000e8114000d09848100f00000000d003201e502c90b5039000d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 18791292 1250 18790042 18790063
    0x60a050609060c0609030a03050f0103080a03110906070605060f0a140904050c030a0303090201020706050a0f031d0f0115080d05030406020c16060507020907030204060c0f02121204030c06050405130905 88
    0x42c1c1e5410b0509180a640b20b031f006926580000c0d0802c8046100c7e401c0d0343e00c14038105e95120000b54030b0050145004e4014001c1100202c0207018184040092900e40d80700410803644203440014030342c502603040018944442c4440e41c01121505000d000e10211011030403403401c0c0403910141160345a280551800030315180064242c00b46c1d0541c101011381580000c2c055a200341c0990310300d140c48082c216483d001d042d0b036041c002080c24481da01c0c100d00030351001c8181c40e014015115018000360500e403174a100d80c444400140c1d9a246c0c0340d18200e96601210b0040e280b18000f4020341640400c000b00300d4000074002500f2181d00003074842400e50108200216000414054014650f8a200c0549550828071040e40541c5180340081d080d541300e4405c623010768040d521340c20f80b058079940b18111203c826070b9040b40c000309910200c6010400030000e401c403202040380d006603910300394600b9140101d102c1d4002e005100052205002c42c0d1380318403c800149c2c03005000000e03080e645041c502e00c3c0002010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 18792542 1250 18791292 18791317
    0x40c090c020c1c0f0c09050601030513060e0703060614010305011d060616200306130201090b130305060a02071208040308010e04080702090103030e01090f03050d0f050c16030b0105010206060a05060906 88
    0xb8001c00845602c40d8003146c69800302007000c0e0340d50030300640544804948840701d0074030030200d000018071941d1003401a8000341c0300b19003c003910303690f8690840300c584d00152025190f50417030101c0c940c0d040c004d45000d003600c0340c0c203101a078040c0550f03040c80a402820383c5206140102c1c40441401e0072080160940d500802520190703554054682c40305022059440e0081c0200b0001410304806170b00742e0241607906039070780c0603041c0c9421480300c19904900c040c030900240b86d40e1f00001060341008040d0103a103d00c0c4005a43d040341d45401003080c2c40c18584401481700040410002c280c00003403080c11a00c0409402405580e01e1500500910501000951100c4040004020316078444404104042d081e00c0b816010b42e15405001c0582c00d551000070603d912002031840742e03d10800c481107042a050030000e0801003518541d0341000745000140041e4401090104184100c0c503103540d00521080c009015582411000326080c1a0a4028280101400102100f49444030000c403400c01d107a41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 18793792 1250 18792542 18792563
    0xf070320010c0c060b010e18070507080c010b030601081621020315010905010b0705030d020903030c0d0c060c0e0108060d150903050d0c140a03051f060206040c090c020c1c 75
    0x207000949aa020315500350f0740180f40107400817a81d4000c1e440c03410103110040c0600107070b181d94600c864080304002d1518080207410b10011000541e100090881e01c5200d100100e40340c04000141498034105034003520349a88110301c014018903a100180040c0c030303c46089a284c000000b0040d403c00f521000d002901407144c11080f6042100c0c070780d00340d4180c441060091103941d03603644065046005005d030141c00354204104030300c05884258010070407800080c1c01d6904100d0064206400c1443c80c803074180100e4021a40201001164492130f10102d1340c90505030b039a42401d20008101c1070000b02614048c000c00d070180740a201c0140c12110418104000a0203407501d90310b001451a00407041044849042c0540261214003030030400e102c81210304d030140d0410070606030403409040054440030b60380d00001c806040e00d090307080400002c1c00071500184450704103850130303800001c000c0c2c6c4407e00e190314140044085580c04908080124003c0301d041550ba51582114100e06441040081c03403020384 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 18795042 1250 18793792 18793811
    0x1214030108061b0a050d0b040902040608101104060c0f05070b0316090e06180c04031509030f02060702030a140f03090a0c08010b0d06021b0a080c010e030f07032001 72
    0x2d1040c4070300d082d50403d070038014804000750303580d00070701c180742c404500240941c000ea010198400300500000500118490a00da0040740c101c030940c0d00710000b1608a88610802051107004081511180340e01103450305290080c02801481106401806007030180842e070244502001484080d00b580c010305a0340707052420030304195200350000040032403c20800007034201f00d4542a17920869025091a00f60300704001003800d00d42c0010301550004c0c00a01c40400818084105d80404400c104d0740003032442001e0801400e1032035044804011507001c4030400c81c1c41d81c0d006c425503446402d14203000300320303016070a842e51150280c861161030410300401042101d05000030030810450107a201c0390542c586425085003682c0b0044849904011803944080c0090450340c0180f00120506608050040707400c841c040c10503001410903609120082940f07030a461003841b405c04000d0440c03005502d004185c5201484500030010044c05210140070f1140080304044180c006080c0c061001b088200030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 18796292 1250 18795042 18795059
    0x203191112100e1b0406080c04050601020a0501060315050105100f0f050403020d0b0f09060906070507020d0614040209090d0c0210030e0a0503040f0504021c09060b180426030412140301 81
    0x1c13a0349603000c01c5418200c00d2645400e1600c240c40c203840511002c0c3c80c41d01c013036106100c05804054003070b80c114480c1c0700c10940410428800c0c07001440c407401200d54602c242e6005074054070410303000f5038442c05c1025503030f041041e0009411001a02c05092050300c5003111101900c241c0117a50000c1d4001c0c00500c082c5080290184e10b10f840b9010442030f040c0503440345c0b0450355903688111003107091035201c2c002003400c140c01203000d00516031004000c6052510b9941d00c01003a105031640f00040c2d4281c407001d003c1140350034019190301030250801040c03000307903c4c4e4005014a00481c4080d005600e51406010960b1294000c4003003560b449080380c40b2180c0303a01c0c0c80c0340d80e0760040c40780540c9460940404100f07071500340212410049080d9400c1e40c4c0565043e2030030005e10903040102c07405a510200d0031425100c1e4030b03c0721010240400d10741464541810400d2286520703503e161001e003000307a000900e42c2641020307640c010703070004100954940c100300705540c82044020071715041400030000181440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 18797542 1250 18796292 18796303
    0x1a0f011e1205090a12080a0f11090a06020309010c020f0402070605040b07020609010507050a030e070906060f020c100c0b040309030f08040503150c0301140a0909030c0203191112100e 80
    0x1841c0c00070801c200da40303a400c401c0d01e403408018028030098601012802c030b06c1c8a044a2038108083e017900207082860b0000050845080f60341c002d0300040041011032039403070310040c441c004105500140d8504010000000d1907241007240003481a5200d56003500c03142c5881c0e041d901460f600c5603040080341000d04191220140865100c0014400e900c0011000f40c018016903016003d03980302c283c209052418168060078030800003412901c58100700043c082854060034004200c1621001241088140e00038204140640071034000c1f9500307050030240035131110492500d5030b0403101d95501600c451074121030755a020f50014042d85103030501601441290b400500488100328110b81101008420300d2418580483e81800d41c07400c20700c010040900302000242c0d041c0c2004081800207a21000c0440490790030340c000385c00152440240d0740440c10b0801510222382c0c41448104441d0b60705503030311004041c40001035405001c074112070341c40d2118100044050450549000d104552064075003d5851 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 18798792 1250 18797542 18797567
    0xb03010908030f090a020603040308040609020a140a060509030d05070203210d050105030a1109091207150e0a050c010f03021b01090204050105010e031e030f0406170a1a0f011e 77
    0x1030008001300d0960400010082d440341d0703000e0042802d564aa403421796407064014000e980242d124034a000040e80c4141c048005805c2d05141240805074540c240700f00c01ca9150003003000c3c00002c0040c90f5840da8001000d0500c2c007941c1c9045603907400ba41c4046424240c0880401385140f84a11035100300c3c4090b00040c0c41e0b0800701400400040c2c0e40c8604042d81c81e1000300c0c01800c2a25101004086420002d00780b03640500003400725565a1080c2803140b406a001e5803068a90a082c194040072840301800781158440c50f00b0028200303090f05480f219161329200d031626050054018140a54600a8041d1622500c2d481e06800740801845001c038013800595000301e101c3e501e0640007054a6000d80d0301c040004d00050000e0008400c00214410031207d03610b0314855912080c01b0610b21450761600400280c80e0030368419101190285000c000c410010300400041410502c1800d0520140030070024092011901480000c00721310042ea04400c22110903603460400d0300140c0c9500e504103403001f582 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 18800042 1250 18798792 18798811
    0x5040503010c0c030f0305090f0307061506020d0906030507020c090c0c0601091a0d020a050402130608010b090904081c0c03090c0b0322060e0304031112010e070b0d0b0301090803 78
    0x5414a007000c0380c0c080d88043c40140492080380100101d203210760300090348916030304100ca1846a1440415145d5084030800301c55054942c100c0c140300c891362649a0340101410b000805404804003805091a440d034001c3d1410150346400160205208106142001402030013409035820250740d9032000340c1c41009043c0c01840b541c1e0001814954901c650f1202d40c44410314002c402810724100001c10412072030507a40300f884210007003519a6a072005088000d00d01c28030015051801c0409890844164400d00e0206000d2142c400e0b03d80310700352000c0c0c4c0654000210713a500c0030070030001405d1480162410080c1c80c5408081e2203000d8266000310b000c1c502801129a03011754541206410b407004680c2d41c1c2c42040b103843c4183e5038440800c2c000c4005482080e01003403e42c0140421461a0082d82c8242c84990158515030380900340114400035151410300203100c49030760008260b030780746203c2c410990007000c0080c00d44140c00d400d6004030340d8200001c0081c0000c103c10300f017564483d0020b0303441c9003c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 18801292 1250 18800042 18800051
    0x3120806030d0e0102210f04060905030609030a050d0f1b050a090506070c0504020901050706020c0102030601030b09060a030b060102190b0603070605160201050304030c120c0b090c0a050d08190504050301 89
    0x1a1140507403e040741c4100164000c1105480841010030000b0f840b503048007000d181032000ca196503000030080c0000d40869500c562180b40b522042524005000e0310b40c0d00290801c008459440b03600000300c5140346010940481c0403c601d084150042460b80c145000040c925070803d048254828001d100e180b14a03680e0500b0507882c0c1d020802c0d244035414008203125180d00041140f030030701e038000e820400e2050514600b0a0607546408007640e000030f1400040307960002c00c10100f5a014400c01c0b0203408269441e803c01d18045001c91890705403400054160008800040e0440c1e108114004882c80f00e40310743c0c0c501c941c841c81c1c1f00141080030380d081480f030700a68201148491199041c1c5540c3c0318500c602014400c0039400644130366101401c00d808006401003c50082528800c8100b4034010550300d90706103851908100483c0710010300030035003d401810807c0401d5849e0602c4c10260743d0201c0341e45907500c10038a071500480c810942c414a500c501c40210080031074004010b002100d0702a00240f1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 18802542 1250 18801292 18801313
    0xa030e0f0705010503011802090607080406090906142407081209150c0c0703080406080a0b04060f05040e10050709080f0105010b120702011409030403020109050402040e04140102040312080603 84
    0x54840070180152800544280010803501c108074500e0a005001c7c100018034054103207010034401e0740028400e86501200003010090182d116030801c0051450381010020b042c1032030410444480009906032269810400200503a0000e40002c500f104441e900c050303403070100f403400c041a5007000542e0b02c0038612400008416030004a1002c0e24110003285410b800e41e140d1720450256080200b17414200c1c0b003903a80c04000199800c0040002d020a170b01c0d1204940380c1919031800765640e120449024504103e01000745900042c1020180c035000c407404141c00c0303030345003115140003900801c12010b24180002d10469580040303403041503070208400e540d0651810001242614402e100d20103070352508000d0300712084240c191040d0042400e1001042078102c50b066640c2c0d1100640d00f100b0986c00018042046680144440b03000b410180d42c15420a07280010301408610010030103408803020f20203009498000394101c1d409181d06c44560a012046050000e104450484485000c0d104019412 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 18803792 1250 18802542 18802573
    0x160503060a0e0307080313020a030305030405061315020f0d1503030908010c121a040f0204090c0314011a0c060406050105120a0b06060d09150f18030c080304080c01020a030e 76
    0xb08044180300d8000c2d4a05610381d030b14407805520003090808904c1d402003420300140e9488501c2c00c0118043d6642c1a2207003041c0c20b100b0708042018001e1a075000d448101e002c00500c0741c80e616110b440e012200141c071051140303212a640c4c8107200302038819520304034041c0703880040d6015207403d40b806035603000980e0751240c1c40c0340d08a400c0c5016035400701d101c1003061035490650350020216425032219844101c80c0e81c90118060701c0070000c40c102110b8010805000000880c07050302d0204005183c144110050081034460344c007818040d01e212121514040140520340008641d191085102200d03050f242c1400c2002c000c0c8428001c1521410f0b5000424240d6000002c83c0140560408810703601c03902c070142000010f0348240c1d91000f05a4444110344040340c0201c10b40c2c03a80b40c0c441200410140c0c1190b104c0400c45503500c85240d03000e4458158200860342c02403110036015030000d09a40e40c0d0f2601d0800e59107902600c1c111440c150b00001d410049158150440450030303000e6402c4414840c00d42d81c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 18805042 1250 18803792 18803801
    0x504050d0c060e0604060507080a0504080f010e0606030a0201080a020a0306050a060507020109060306080c12010f0903020f0c010c0c060e030115081b03011806020d060312170717010308090111160503060a 89
    0x6c00000640501424011650391802400442118203019180c01da5a075481c9007403c000130742415081c0d54880038680341040c14004198020001c50160a01807056030001e000004040d0003401300e80d03404035001c80d0b41030080d442400602f200402d9145182d99034400141503612040040380064095000001c00358064003a52040e07030215409400100711410501054540402600741503640f030352586034030312210748035803000203003c0d13406062400c00e9480d8451400c0414039100c0d0400c0218162000400c90341c0d41080d013030394400e1416000e41c0c03400c0300009002d8001c88a034a020141802e0001410000008100410301c030216040b17036881030000f00b0907007255460f00000c00300b034608007049400203e41e03500421070614a2034000400940320345900881a9010149902050b0440003a0669a8442842c0c0d64081c40790314007008100c8000203440240d00c41888014000000411408101c0e80181e44016581d0020b00445200c0ca100c650f04402c2c280d80b030702c07505010f4040c000104074060382c94003d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 18806292 1250 18805042 18805049
    0xa020712150c0e060c01090303110f3f061002120306130e0303010e0103020910060c0f020105190503150402070506130804030f060515090907030605070504050d0c060e0604 75
    0x2141e80c0700011408880280080800103070030800044002c48495079490007500c0c0c2c0c000c002000060806241c90007030300710b4413503810a01d100780041c40100f80308a00d41c001c94580d11180c5150040c5024140c45448100c0c103001000c0014040080880004030044020070340306a9080750107c4204044460690300c403020310744040c80d000800c1001070451b04200d00c0c01800ca100c03c42000401036880c8622a080d5002138100c4e1307048815000040041d4a0488000d0b504031a0400f070710f50901346003040190090300d4071803008141103500598441075a01850070b55500400700c80c4030445060516800170003a0b03104980c413000000741a62040c0301410a442920002035203c00201200d440f80414136003441c21012040b07c50460800000c000078001c2c0420248a52181d20003081c50704111311802425101d94110f580694680001c100020a00140800440350080400a1940c80700c1508550038802e642009030020003189050003080707603c080c0901110038590355500c60105000c01c11206201f20312 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 18807542 1250 18806292 18806303
    0x4020d0f1718010e060720120106030f02041103090705010e0f06030a09050609010905060f09010204080307050303190e0d0e040f0908090a060503060108071b02040504060b0a09050105010516110a03080a020712 91
    0x1881e07d0001c250855910440c90006000d11250154001b55a081d64020742040741d05c40101d061540445c01d1a01032074131102c00281e16542036203000e00070720f07503201c00600c01c06040045511178080142c540503c0e0001d40c040190219a40c0d20301064040081c0c801d6010440c1c1e184101c2002580703529062090f03107101039112000c0c1000f900c07100104280e60314040c2662059541c2000f0002c1c01e08030410051000b140315401860302da2500c2a450001c0b010140c610707041c402d080c8086640030704000710714000c241c0102e08050500548104c003080007450203032041401107190103060380520030342a008c0c1010020850b4140070007626030108588500003514081d0103d800d140105400600400f145051240036101d05510f01886400280030340d4001e8605484207a0303120480c1d4428144851031380042c0504400a028a51500000920702e204070101d83c81d451504400790400c002c00c9440c90788000c44010715440110b5182d0034080d8096100350030703074000340c42600d43c0010282c4600300021202c0c1d8005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 18808792 1250 18807542 18807563
    0x90b030618040507050409030f020c0a0f090f061511100216080a020f0102030c03011e060509040207080c010906050906070206010602150901140c0a031404020d0f1718010e0607 77
    0x41103858030100707001e0001c444a000320702c808103050b211071244500940c00381d541d01d8045900d8440190400b03004e061454050141c058050205000c1d501c0d082013100c00c94000001c0541c1d503106110000c10f400e070440d144480320150410215648194202c1e1704440310800d0b6080c0e50b240008020803032007101c21081b01c0d01010310b4030380701080296000e00181c001c2030058a16294000700103a00b240e1045404981141020005101003261604840c1d181da128040e65400c80d401e0400c0030349517000c1d805100d03120341d4000984c0c100b0009031006072100d15522100901020995280c0303400500000c0b684010a44a070f54001814148006400c5040321040d8010b4000441c044518448000e4002d0807400e00e992140c4640d0034955030710034014450182814007070f17203449011500500b51100c6030784a654040b0310130240400760f69003406016170558061030700804da44992409034004e000c545c103080c2e07484c40085503046001320300181d0005825026a251072680600400700515070140e03103000340920b100b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 18810042 1250 18808792 18808819
    0x8160608040203280803010e19020304210504030209131407060f030c26010512010e0c0d020109180603060b06030403020307030f09170703050d0201020301060c030309030504030213020a090b0306 85
    0x8102c460404400100d01100003400030b8440c000c07294404c0c2c2c80202c40084008c20800c0d0060410005044003050b01d105600e541440c4e00da50500e88240803a649400038440894548940560110b80055902800f6100d992505441140d95400342d00c4043e06e04420b80c200c0200c0c0d80c0408503202c01a1131443c4c440c81d0002c032005e81d0171401403007072040003000e00c00070b14210a070301549007040307008841082c3c96200a560514081c003a0249400d010405281e051003004804c4c9100455090650102030306d840390140140e0004031005031040c0e020136601d070090711084c138180306140c102009483c041d40c018440e01c0c1c0c2c2c1c00113024261000300c90117030040e0030511007200003030712035212100607a00d070b0300e05013403c0c940790300901040e0240300360268000d0f0310235242001040024094501040114002103040d580340c1003001e0941030b880d52004007010703640c440700c1040501600a580103150080c000ca00d00d0020403031040029805442e0b00404555509000a09628600110791103008060400f0326960701 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 18811292 1250 18810042 18810073
    0x10f020a0c060507090f0801050a0e0f0a020d02060403060510060e1905040207060902101805030c060906030907080304030c032001050d0905030403020301090602070b160503041101051308160608040203 88
    0x100544004200040170500081d2070601c10703030310340151004000004440c1803156400040700c4050081031190380010014016000c3e000c00e00700c0450741c05642d07410a902c8940b00040ba00e1195800061519140c04144102c0040502c040f00503158a07840b00c9410700c00c0c0c0420000017507880700003440c800c3c21544c810303c102d043c40c0c1c000c0e00d80d072441200d010070000d24035070000d0b018018004080c0009465514506074911800b40d1442c01080150050720440d071074034003c11954407030f4070f1400d0701500d0004080f4403005420010200144002020b80761150303200d15200c144031450303120503101540c10004109150380324034102d09041c2c005031a0607203440c1e8800342c10760182c800caa42c2607c05003c144000401360301d007800341041311803213104010b0303450546103030210003c007001d40181c4100302ca0310340c0220116009801c4940103a084a05020084150f60040f41c0522890411051544e080800000d5010000805007900c0300e5a5422941c09521641e04544d0300008172800b82d0b0552100c08811481c03013 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 18812542 1250 18811292 18811301
    0x80606120a0b04030e040f05060609060304150905070608090d1d010c080403061b05120402010c020d0218090c030a031709070f03080c1209240c0a0c08010f020a0c06 72
    0x11500a8840d00c01d981d480c0c40e10600c40480d0181d000c226010303000c4209140611403000c0101c1505d2042105040000114916000f08001580100c0000003c1014071078004007172440e034051014280100300031494125112100d038403800780801d65010120700c9031007000c10b840505183c41d81d1500740300c400460030000c2040c108252a414404050894004103180800910185001d045c010982c10b081e65031010049048100c4a01000003e0102d4002e00a05000c0d842c1c0150b024a0100c3c001092800000c0c4004104403000713522586c5000349601c19801c0441080c800e40c500d034140c1d41c41640400c20715880e068a44d800a0008030050031803400199001e448a801603000021184041d0300c81c600021080c0c55600305468010010600c0081d5032000c1221141030503440c0f00441c03e1090040c04180c10b1141c85105000a10581e24011104075001080d15030514441084928401a5081428400481d4028002c140d42401d100714849a440d000f2142840003a82e1040925242c1d82c031400005d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 18813792 1250 18812542 18812569
    0x702010e191a0c0c030d15080f0d0503040218011d010509010f0e10050a08030c010e07050604090c02010e0303070906110a030203070311010b041b0f080405030307030b0102010f02040806041202010204080606 90
    0xf0321091000e004985010005011840040c850005030021207416079030780341c8919804901d0a034400b2084403007103d408908080d03004100d0400d83c0d26a210351000654101000c482a01000f000c0d40000500c444008103607454035140318000c3e0407503600c41c02030040c0c24100f4001c8072a207100d5100708004410202800300c1d400ba84986c201c481540d00c98000400e0504039600020f02030b4008175101c0c003445001c0c880e8288400e4071000070075003145040003041c0e40c4e020b540b00f6040c3c029030f0303044048a018001e4200860746c02d04134054035500e190401000d0310034007850184e45c002030055051084203200000740c03a0003094040d0011820b2040710ba5041712000b06d1404440078070b549600c060502901d5500500c0003078440b0130002c04d0400c0386d05200a043d4185014842d0030401c2140a22011600110480303801200300d1601290010030840140c1c09000b2602d4415160352002400013841c8102241440c0100d120300601c43c160001c0e00b070124241d01850040d0300d02908100e003c01c42503e0301140c5071560 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 18815042 1250 18813792 18813811
    0xf091b0d02010e0a0f03031d090a0b010e03010f0509190b0406050405070f0602011d060709172a040c050a020606011b05060a051f0810020703030204030b0702010e191a 73
    0x4240c19280821101c0c08968070405170320b10074034014020140c104c101c900381c440b0101c200c01141c840540016109000180c502c1c0c000f40d035078162010060f441851181801070024009100e0f075410f0448100081c40102d8901c0240c0c00744001c030030049440082040039a0340c100d90030709506d440782d844440081c100504102c0700c510800230300040c038481020401004200540000540c25a075030190009840c0d0030a6500047e0864420800070070380000602058035900441d01256140544a0300d02e80141d0121200c140e0340d50410250681d424100e1040c4404c078290f5042c41490200c0c002541c4d0b500501e00054050b8000c50300061280d4444c8070120380c0c0b40000030103040e84120603120207081010540b9420180c41d2140100600c0d4207006e40b0b420392a80004030b006107502c1c03402c03030080d44030340140c5511220700d0380016030002494440d4040d06c0245030080781e03892181c100000c029009100d070001a0300305002c0c0000a0340500c07128040130900980020700c1d0400500c0e001046100210000c1444d4078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 18816292 1250 18815042 18815057
    0x3060f02130b0a02060109050103150c050c160510170a0203040501020712031b02030406050d0203090703021009090b090c0d090510020a0f0e0607080405090a0609050705030f091b0d0201 81
    0x700750111904800a1090004080d43c41c030301003a0090404e03405070004241c1c03034140001000016040100b6400d1030084c14030000740071803408000c40d01c0d44205520300000c0d104004800004030802032020045030821078002c200c0e00704240040d240d220003100c12038000d1a0f9080018120b644e1900210343c0a403192000602e042d14941c3c91521068003000b04400007591400400a0034480c0d003424044641380380000c0d0300307203032818a00038268401c200740001000d0700032000c140361010402046024550042807000551007849005010240c50302ca81c3c07505c00e0800e0f90403451418450801c0b030068221800c000e02d8414921502ea020701450402101c0c14800c14030700d40241e40181c030141c180c02c610799480d800c6000f44a080104150320445c0540c0c8280c43c200300b2500003d20482c211030854006455110a0340d95003418900200f8059200c090301c1c074145800c002c4040e922000852140700080301104882d103c00300581c1c0e0307a2041841d91a070102c45e0f1406003a5914045000900c000e1050ad842c0d01d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 18817542 1250 18816292 18816307
    0x60e060d0302100c05040504150b0a0c0201021f02031e01030503040e090a0b01030605091510031e0b010308040906080f0d08100308040b18010206090c0d0f1407030201090506090105030103060f02 85
    0xf01142c0c4130011070800680301190134811860305000b444641409040001910750801101c174025209003030014081c041880100360469000340400c2c1848100790488640c45c40144170b1400c080d6008544a122480c000403004122021030300601d410381c1e41040c020b5041600b000000d40080c000600310001d648075040000c0300254001718024042e5200740c0f000702c0c0760304003001524030b09030200c480e25440045031300030071071240c0c02c010054085940000395004030b0701409107034030031248081402800c14159030001206200c404c400a0084403105101044559910300e00e4544a040d14244000541c1202618440151080d8030080d00081f030a500d00c12242c2c1e880d82d8080681e031290340008203810022450b110f00d0003440e003000e0396002c0c00780081d1800f80740003008282c403249540800e41c480e0220001090502c9000401292441d61020303c00034040c0c130070030040c4d984003250b01c000c0340003464400c2e01003103030b08044058400f1040c043c0c40321801e59083d40d503030101500c14600b07250b0005a02b409883d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 18818792 1250 18817542 18817573
    0x50d0b0909010b0f06070308040b060d020607030e090c040e040b090304080106090b03120f0313032606120106141203070f030801090f06030b040209090a0605011e0801060e060d0302 79
    0x380a200c141e400000d0259024052060000100e21014401c01c4140b08100101c0c1e044124103521980c0502540801d5071010000303122901681000b0303420120224907681010b82000c4d40c044003600481d080e030410358907040b001030030b485240181503800c030780000460b002600d82c5007602c0c0c200746040162400d040c1c80380001803c44200303a00081c52030740c03540700ca6616400c05022039480d030054411180d10b010400703150748445110103007098030300101d881c900c00c2c107244c41007102c0c07060a4003003100d00e1110390040e0000300600f01d080c1c0d229032040c20100d02440100c0300500c6190308990081c9001d1103c00064402c11800c030074581403100880c0010040c210000b001c5080f255086d51080d260b2140550509429000b100c0d06c0c40c1240003054a000c0c4180042010042a01d50040c1c1c1110f10306401d0703807420904c03410035a0a03040109401c2c1040700100d8040c00741c10701c44d61806050800d03c019070343c2c1d8540480c00d881c66846041c031610210340c0031410341d081092600710082d029004407207920340b814510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 18820042 1250 18818792 18818809
    0x9030903051014010509010302010f0c030c020603010f06020c030f060106030b0d0b0f07080a02090609060d150f06030f0b150906040e0106030605010f030c17090703020301022205030715050d0b 84
    0x44102043e41c48a011000b0100c03002e8040c0500f0040c0da4400040d8190f60000e03001078a44040c0d42c040c41290400c000c205480703926001c40c07155019010b5522075a4902034001111002e0003244050301680d5950100d9080000b905040220390703000810043c0d10700351060b0010040c1c071060380c0e0000e1680710014041003107100d10790b009100c15006d4589030318005030001e0603000060091f4107502e0041060080c0369440e2415205401c900b2982c41ea901c0d035400c40800700400108459080003c0c4200d030000c2d641700325003072407011580c283c0c41c180721300c10110840748101c40c142c24030b050780f18120440c00b644c2e059900c0d000c0c1c0440c00c0c026007038a00c0c04d0385440a103000b80c075003644004002510b611041c031555a103c03283c81d80c007402a0070103009a21029030058940350b5a0310120700700d5155080002c0440304100020300c025034001c2d0085503580300b101c01f1420810721329a100340da00c2d140008009003c1c100010428200e8003d50321070044850b5040007151264071a4403c60441038031000c20f90115640c06c0403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 18821292 1250 18820042 18820063
    0x90512010e010510140a031a07030209040e060405010c030e0a060207060b0603010807060f08040b150f060703020102031806090a110d060e0a0201030c050c100906020c06010314120414040903090305 86
    0x900d81004d85080c118400303078010a00a240640410102000058240300c884141c40041c04160f2960b5943e480c01100240034031000168403e00708413035014100c4010071603a02035802980280600600c1c540d0907000d80340c0c0147c112155602c1071641c0c42c0465026405003103402d10410001c40c82c1d203092400143c1982003a000382409411004c81008480d80142000004c03280504186000e454541c0700e200b4030400080018480b103c03041c80005880e503401944014003080101000d03121112824001d0003074000711581ea000c0340c60109488621080003900c5449a81c010b00101a4032680350380308d808101302910519048070010882100088071402499441901c20000381450100c81c00010142d800d102407444c00e00c1010804942000d40c04210300c0500d40780c1c034502007407440305840c158009204401d00c49032a4020000040200030440350002c041c00484801c5941d401074002c50b540c118480c40c810704039401d00c89480852503003003e41025100c20b000b414075420042d81d9444641c200b009190 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 18822542 1250 18821292 18821311
    0x905010b190206070c03030b0a0503060c090a080f061b070501091a060901260a080c01090302070902040e01140d021003050610030603050309090921130503030a090512010e0105 77
    0x9a828001e2804010905a000c10342c4024001c0741892580900b000c90000c0c805410113032542020790701e58030754824410003014081c0844410703290601000e0f03203035003200d14414803450443e80001000040000c0c1c4c005445e4a440140c000ca4645015217030b0f202d00b0200040032002400d005920200700280300f0000302900405481e00b0b0a16404105014064010308491251408100510440d085000599070025452001407071180f2000e030306510345640224001e103026400109210380c2039042d0080034001d40300c0e40807111241e40340c1040d0710907405903020b254000b0007103000411106201d041140c0e8800c002a1070164044490340100e90320030642c0600d0400309032107106000090400d1041c40091300003e00d420407085040da0344040c0ca80c4111030711148140002c4010462071070b414841c510545002c0040c0000c0002d80c2e2040500b240c0240c03401c540b05600d09000010f00d41408800c0b2031024400b0740d0f0700e000086c140010800989036421982541c3c1d940e400301031040e01000d01c60302d8010240c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 18823792 1250 18822542 18822547
    0xf0115090506010302030f0408030601050d02030103060c0e030d080606090a090c0f080c07050703060504020a05030d0c02010f080c0304150b19150512071209020904030c0b0c130902070c0905010b 85
    0xa20510503694007810740b40c10507204000308800c0c2d02d41c403414550410703440405580c0e241c41d0100101c443e4041c000e0f8034036007035100000020070402d2a51010303420301ca140c1c99080d5a40c105400301522031701c50a4808003c564048000340301c0b4030f0103000502510500421103010320b0b0b2030f00f44174000c5444002c240800b040221224620489d042848103902071040c030079071450180141c0c2e41075200e007804d1200070803680e150008502195a40d50112011b0400030301104d490304c04c1c1010090414400c1b801c1a400700c4c070680d0302c2c820064428410305100e40b24a540e8589183c40316a1030b03100621110352a083d400f940c1d10a0703407000307603101e8401c0000c02d00c2030600c2050003400d14403000f0807408a0032809003400760402c44401c124032850041584100642088600c243c26410202c02503c0e14a1009500903090390030401010b4002c4a203040e418064180d4070000c1d0798070715042e80070b8032400000703140c410b07100d103020400726484e50024030140348215410700e107076592454001c003078071000c2c1c2010612040c003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 18825042 1250 18823792 18823799
    0x6010311040609050402030a02070b040b070f0806090408031e0903040513020c0d0c06061517100e06120f01060303020c031002090105040b0304030e0d031d010206010f06110f0115 78
    0x15019020944405009080c5840d10303245000e08040f1040c032880d40502c0e008000a480d032038955040d14401c5812415403051440c180ca0a030003c0c41d000c0340c203c8045100110006034103440741803e0fa2040001805200f09a2a641c54000c4181c200070858010b0701100c4e5080d100c000f40e04128140541000b01c01141c880782001e0800c00e9015005c000080c081e403051060701301c21480001c00302145c851905040240701d01504015000d4513079604a00294100c2d80e81002c00c00380e001c075114540b046800c101c40150313110f0301c030450288925481181c06015070724010034031600d0500d0000c06681c0182d41152440c15850309520700b0350b400e90740103a0150308600140c90440c02e0500c24000d031007100102c21481c0c007501000280c4907003d24000c80c5111480800080d080600440780c81d03082590090411204407211b18008040d03561804241120402640040880f035000180c3c8034140d030b4061081da540282000f1040300c103980e007543e03081e41c140b0038480300d1000e4150030f1040c640c440e812100b48190382800c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 18826292 1250 18825042 18825047
    0xc081b0103020309060a0504030c061103040606050301020901200c030a08040608010e010807060e01050c1509010608120913060f0303021501050901060507030804020109091508060703020313060b03030d0e060601 92
    0x60004185050500400800201600120b45982c1c40710000000080c00d40f40d0f82403c0740e68000c9a10000e03c0c0c10303d8185510300c0d255448002e10321452140c14207000d401d0b1a0003d0501b80c0c0100c4403400e006c80c0e9842e030510490f50424210380081a000c508607640030110100180ca80801014152607074003000800b840455441100d0601405a1401462465141c400d8140d5161424440c4008203e0b210b01d080100d45e205404490003807500350211421000010040d03550210b00ba59114140d42c40e00000203116000401c107000c0360b000c070041c49418008028144000d41460000e94040d065035000c000c2410315145007254003a500944c014115000b1100003094000f04c1a00054401e08104004011440c2c1c49001c40e26030641c58680000b83c1c0d121480180d400da40036401807440142002d07281550218442412000c6500410841d00191103003002501280b1055030101804403011002c140400c8107030300005c0c40518082c08907803400003042204c030110b07900740c14207e10740d402c02801e1203c1d541c3e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 18827542 1250 18826292 18826333
    0xd0204090207140601030c120602040b0c0f10050601050f0306040b060f1308010b0d0210020708060a09031209020609120c0301140604050f0606030a0b0301090f03050903070f0503030a0e0402070c08 86
    0x40c183d00c000c003903550464440f0540402a0700c01d0031484013001c0c004008220030740c1c068a008090700c200d20743d2a9480d0b00d2000391115442541c000c014410489070310707107004030741c000c0c07500969060316001e240111044251081d07074001045585c0007511128812075a4440a0040008203e0840825102e5551711480203015a445d400381d000c5038100360b4800c8aa50307888690100c4079a04a644c1c424507103844034160705104141d8090469401a841040301040d12500024880e610a9681e138040a8018198400b01e81d00c1e001c2c040c3d0041230034022407110b030800b0789204614542550072144940d84a0700003d09403285900c201c100d4075291010301240f42441d0083d9038012103881c0030114a880c01002107030081c00014817101586c0c0d20b62005580c2a2000e501c02c41009800502003150b540ca0f42c20060138a40c0544001d038040d01c02c24400050302a07204100106480e0020095440e0a00039007044518800400c9210f900a45c2040000009260080040b000701540f0014145c290400c0c40070355900f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 18828792 1250 18827542 18827573
    0x90d0b07140705030a0804060b100504080706050f0f13080105070302120a05040f032712050705010f02030f18060c01050901050703090507051002070509041b050d15050601050d0204090207 82
    0x600780b01500006a021043c0e0b6940b050310329054103207507101d003000000b500d62603030f000c2d80010344441304940c129030210003401510300c003204443e07039560303680c0d004c40302403060090607041c0d0841405102030882c220002061a40c5845283c0340400344c481e10032608695007952607501184d0f000509040e080304020700258400c088180c1000356160070f4070b50307103940d052203030b0300400b000230201e0b407d84031042001d801c8051810000a4290300381d00d038070348003450311000c0c58107403414403a40a00260541c80380d0300ca460b00040940c043d504008050903090380b00d4000d0726404109001d00210215aa158040644040091100041032a00300320010310300311200580124205801c040e0910045080051200200d800030b43d0009030750740078000101d080000d690081a80120008140f0042c8001a20044580c200e00f44200c407046a0700d000304030031424030400081c5484c0741004900603089642e07114551160060410904c0c00020b140da01040342e216070081480b0350780c04140713001801030100400d503c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 18830042 1250 18828792 18828827
    0xb010503010834140306090105090304030807170f0a030605010305060d0f11040507050309160f0611010b041503052107140307080706050103030806030604030f03020708090d0b07 78
    0x30365040081040c2c841400030004030041d505001c1c000a21084100d41406000880c2d03280d5807055101c0d401c2c43e030030145190807039102c1c1c4941d20100704450b906108090184035440e00940c50103107150381d84100c6800880003a1a1f1014080d408030324503c014005004150b400d00c80555607030030214024007240c0550f00200c5c1014a071004003c0340c5e45805c83c1080c030013908080e200724002c50701d2500b100400100c2c622a030b0401d00300414010344c0c0340c124020318060301c60002510030b0146c0036180000081498821002001600d00302003007414054076503c541c0c401490008660250900d0114080d201c02d0314801e01e41c4c045450782002809402d0048948859811070303d03045004041644201500440c6405003004400c1d10485803c200c040048031800382d440040242c070780c56035080060040201340310550105d000701c00010407030314000c242c1034451641038550b00c0c040400b58008070000c0d00440d900300c421010810002c022a070705c000b0007010503442051940d90901c0c04180061000760b007400428034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 18831292 1250 18830042 18830047
    0xa0f030c02070b0f09041a1005030402010f03050a0b03150115022a0303070606120605070201090f1b0314030a0f020a05070e0606040302060d0c03050c07050703020f0103022205040b0105 81
    0x300c0c5980440c54100301c41414030100e440d1030b8110b00c0500280700d5080e809138820314000c10f0800c5103601c0255041d8010b0308881c0000c411841c04400e482522048030000e0018600d094012150f502981c0900e400ca01d0b50400000e00d650000b0220746440310385104c3c080c92001c080700400c6440e0b01c940440c060030b8500e00c0a05076204a440346100320405c2e640300110310403105500c44500e902c080040c1c91415070054020300c0f4403681c6615100c00000815010703990341d404d000001d0001801401040001a80036420204824050325080302c0100b00391114080c641c12000c0c00800302d00702d0309141e810985200e01450307840780303c1500600091821901223003550070204100d8082000410b180d0100c6248030400c5465a44140000e070041c0708030b80000b036005102080d1412a00d1241c0d0001e0f034036803402d031010001500e8440b01c0e1301c228002c100d001043d0b80d10560b030510060400c503080b01d02401040c1409410140c01d82072003240742c000c0250b824540b4898240402142c505801900c04200007820601c0c07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 18832542 1250 18831292 18831311
    0x3021c0f0c0b1e19050c04030305092e02030c0615060d0203070507060e1606081603020706020909010e041104060303120207020a0504021813020a091503060e0c0a0f03 73
    0x2401001c140e0701c05001d014180b40082c840c90822529100c03c0600d407040c04010b86001056183c00c154030040c0418614a0200040c02074082c8604072015241c2684540e0300380a000c0301007002009400c07210b4007400c200d5032084c552601d041103031030151500c0d0350055a00c9000d541c00107441e00600600c00365010300c641840364801e840e80390440d0b0760380c4220390b005130b50703541c0f450002c0d1071501c16000020980340c901705012030380341004140c0c24104898160072082166407413400f1540e408040da041c0d444d003801f0600c6403055034040e50042151a108010150920584000180c2078110991100c1011000132042004001c20380e41501910382e000c5504124483c00c54400900ca41c40361050f0540715580040c528041d5075030881010018040200199500c2080f01c0c11a500c908030208450302038600003c1c0030034010f649000359400f412059032004109450424451050341a0f60070f900181659200c0101b01d08924104540c41154001040c50b0b4a04010307600500407448000380c81304161900640c2d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 18833792 1250 18832542 18832547
    0x5030c040506061b01060305060a0204030303050708060616050a0b0a06030506010e0408090906011206090209121b0103050601050d0203090705100203070f0201050306151b0106050910230d03021c0f 86
    0x2c412018189101040003200124401c1c01006c0700d82000e05184150401c00900300d1143e002042642d102e65414442a190b024003510040701c01e862071035020005001c1a800e074110440d04018244c0250101d81c2002000d84940c1a040300c19150001059181d0350140309000e410494079006083d078159010091500342c0754082c1c24018050564403c0e070079040400e146a2207844040c0c105405010204203580e600d0710300c3c1c8002d48c003804140c0c1c000c8400401030000c080001c1404a6015442c421841c820201840110001d1100803d0380c3d06001c0c040c00040d0440c50b0a2014500c076050540080c042d190522080215907425000c1040865000b004503000046009502c440c80c1c03582800d160b80c40e5104d440004030006c54400f0074075004074001c075080b40000740c00c0c0c000121107100c0b80001c120031a02c54060046000c1e0449500c0122883d0800c200310052120071940010f456507107051341440c6161000911468001c101500103074044440544074000b001d6185031045040d00b000c80c1140d0286401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 18835042 1250 18833792 18833797
    0x30c08010b0304020607020f0612040501050c0403030203030a0507090f030b04031704020f01030e0f010207050715020f120c0304030b360d0c0510050c130b0301060507150605030d0905030c04050606 86
    0x5d001c0c4401181c021b0840d00c030182180710f0040300502483d2100e10745001c1514602c0121001d84031036091030003203040710306180d00311000d80c0c0c0c040d4051860350361065148409000e000d4804410000c5a050001d50704015590910286204440100d0141001c1c1401007003030b50000710f46031440340b9502c00c0c0801640e031080c1c1015190020708000c1001ca001c1e10030641450b43d1851206030950000a072001040400b064460548001d4001e1040c24450f10708100d07a00d0300f44202010751076111160f09000c0d40c0d00e5001400c41005030070100c0f4035041d02da6840708460f50040d122011510309800c8000032920708103a152400d80d04080030740501014100c15165900030204011040c80b41690340d03d400d01c00d0a00908640302d080100038408c0c0c0c2000c0c0004a85644940c4200c000400951408160702520714210b9040751065034410703080c08519100d6125000746c0c10041254555100f0000070700d600d09201d00381d0f140c1d0b2191140d410180c98031080c14242a00c88000e070b886545400100481a640d0350103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 18836292 1250 18835042 18835051
    0x10507020118210308010b030405060103020d050304030c0b040e060d0302070b071502031608160f0509010c05010f02030106020f0703020303040303031508070306090c140904080a03061a0901030c08010b03 89
    0x34060901c49400111a24030a00b507002020700c41d410040008007031110700440340c1d0241c80307a1303519402a80c0c3e50301940c01d0381c00301791001422138110400400c00351801c007540024542c040d0003603030301d019642c1d0344a4110b81c03407a41c491030003540c010400300860038a00d14915489603054075000700303404803070360001d4a0703007071a0080c1502983e007c96480b00f40841101d8440c0f40041c80c1004540d00c0c10000320042e004440c1d401c0d0000007602000000c3c40e100500310b000b00c41e02a00c0c0e124010b1f8034620840a640e10b401040619041040280c1500d0219501340140400b80298490040e070303950628a00034209201c4100d008020b900c403003410801a10300008640c1200d80600c0d002509440c411304401c283d81c2e096000c0d60717031485103503008001d120a42d031003a0141e62054561804803603a414415125520040a050b84000030800041c00700d10b0000052030144070074600003a4440d15a80102580c44044003001007406000c183d1615a5800d4810a15074881c1414400d800d0761410043c0c00e0707207210090 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 18837542 1250 18836292 18836297
    0xd02060412020102040302060c0721050703030c0807060c09030c05040c051209150702010b090f040302030306010c020609100503010e090c0d03030905070b03040311010c0806030c04020304020f0d03050309070f050105070201 97
    0x308590740c120300c01c0d4107a40165078020140d665a501083d40b03180d540703030f403801400020001c0341c1914000c2d4106549402c1d480ea071110240c60b0451641d141a00c4901d00c0102c2942c40b01c40800c0004000369680c440c182c003546980e158000b55034190b0912041800158200a0080c1e2924a4011020f6000010750b10b20403c8034840e4078071076035400c03a210b040110b20400305403114212800c0c04002038064004001c040c1c000d43d05005143c0c0c0f0080c054035a14420744028000d80c1082000c151603500c60100d421041e40054811454800c0c00c002140b006031550340b000b8000b42e8048014040520f0110071940c1003108200100000d580381e40c0001c460401c60346006083c5944d50000c9403c002c02441071000030190041c01c17548901d0309090203019101205500d12913940b90401030243c2900034130403280201c40c050010702c001e044040c00c1c0301c02580003500580e0f009180000301ca11079540e4a42c02540c051107903903200c0c0c5030705080314171901e4071045810951100000500601046c1d80c0041990f4540d038092 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 18838792 1250 18837542 18837563
    0x2070509060d050d02061b04121506030c2714010b03190204090b01030b03010509030301060309050c040e1e010506090c03070315031101170103020a091104170601170d020604 76
    0x4000582d0000c90300c08020311a00849091621403600811030f64400c800c0c00310ba00d0040704100e640342d00d8a00c6180526001d400c094a000408500b5a0701c000002c0050600002043d07501c07900c0d07941c40000035921202c170000d4041456020417428103040c460881396a88180001d04007503100c01048075050295a440301c42c048005141c01003c1003454140740b208078021540c0380c2d02d5014000281c1303901700000d030206c0d050280006260805218061244102c2c3e00614216403d00d40c0031000382803000400d980d01c0c07203040c2000401c0d640314850f00c2444900702008040404150f41e0110705c90306c9864aa80c840c0e490b14040092136142d000c3d0582d0700000350100141c1d0780e900c0a600f50700401c10755121248060542c0008400c00004103041080c80c8000d8a80f09000280302ca600040003009001c02900301100c040104138015560b00901240141d40d9800350505480d200701940203000c07036200d806154021001000640c0000000340e4603440450050300c054240a5000380d174804020300018015001e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 18840042 1250 18838792 18838801
    0xf060e0307060c0201060e090319030b01090305160302040608030f250f03080405160623040509040f060f09030806010f030e030703030204030b0a05040218060d0204090605101502070509 81
    0xd0080701c11141e80407404000c5005a010020b000340345501a40304103501c8031001c01d409880c0041581d50920fa44200c0c20728009642204401401e2003035142c07818486117440200015400341300785010500094bc0040d035062460040006032680c540c070008107074100300205c1d09208412800c50f0b050b80e41060384680105e030307070066004c0d81c00c0e40b04030007420395815002c441d805c25030700450850145000c0c0c403c0300c0c01907215040d12110001148118030119112040d8030002c4100b940709038108020103031200c0e0034583d9030400700d0b040c004220340031620300680c1c680c10301c20450a44a0f40f541150406410031400d50295000b900c02c850140010703052001041010b0880d42c0b003900074a40703041400301030303030303240d10032450090003a400502089641002280000f20110000d03c0b0791445141c00030103913020401d40306001c40507904042c0c16240c004405403081030158075280100b0518500c00d800004403481c100d951410010142d0708080602306081c1c00440e21281e0000d030500c156401101c0008441c0c44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 18841292 1250 18840042 18840071
    0xc0203071209050909011a010807020a031101090614011a040f0b0702150f0705010e0d050307050d110403030c03020c01020d0917010608120403020a0e0c120c0c01060f080d08040f06 79
    0x22961003294441c503207604101c16800107410035a45030124847c1010039040d2403005441d85072046610000503880211900f01081c480c4017441c40030b2503035a000044844c215120f00081c3c4041c1800350595403c400c0040182103040141524410b851404480c10241001440e190105280c89000c0c00402d010507074a095548500c0c2000a00c1c140361f021030b81e288460704181c4c02903040620180c03455464174000f100034403004601d0154604282d6212b91840e560174038141e540b900127503103c2070155650f401c1c0d4840c0314400f10052010354041e46038001c4d59001850300a2800c27070029001411500018282d004e11a0040ca0740001d45009103880d00c041c0c161511002d00600701c5600154061103040200186518a8402401543c0c001c2e1074810496483c0c18070440510020b0310a1602010f0810081034908091200240c10561280000786800304c0400300c60309492080e041440141d412032020003c49008100c0d91003d00f68908010310030742b03002d0b02c80900b41040d00c04060722207920303070110b5900d400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 18842542 1250 18841292 18841307
    0x901030207150609051b0c0307030507050708010606020c040c0314070e03101415030703030507060c11030c07090b0f130e01090212030406020c01031a1009181401090c02030712 77
    0x71880c20042040325918201d04c4080c080c26164100858242caa2071400d156117001200c10318134517a4019864030070513540488d0f0303650014805036680d014084010481c0724080c01403000901d0329600030b00c174114100042108a0f1949800582407505d080b03c055603070361000141c50740c80f08442c2050b003880750107480841c0c24400c24402e070801c00c51502000d1510507880d50000e82c02402005c002caa000c1e0b1008051507901c411500024011a005205000005020790406400c0300b01519000c5071030301c08509410710b15088900300b44142c3e00700040c203018402003842100d0128004585134445400c000c0041008410050300c030b25000b507260008000049425003041c0c20f404d50181c080c00c00c285480c81640d0700c0741c1140c012000140580c565480c003642c0300b8080c004c00710601d40c4d030050a0b2400300040089114010001c5418040410800150ba80003d040d0400c0d0303030700c2240042041284034440307440002050308a50141407030304050f00c4020358000191200305a0081d25080f0358502000c0030764840 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 18843792 1250 18842542 18842573
    0x4110f010306081e01110a080103170f0f0901032009010c061d030d0608160e061f0905090f01030b010315020405041a0102010b01140904110d1815060303050901030207 73
    0x500c01e185422001d0004105118015140c81000b04161801b01c00300c0c2c00e29108002070701000842d80d030014004070700007075004605900ca2400c81c0d45000d240704101340460300141c0803040300c0c08000c00c80c40010f5805000b001d403800001c0103180b41000c80f004038075007030b4010401018100614121000d04002c02507010b40402c000312070540c80c40c541c400480b55903d134091041d00da110740c14003500142d0144d002420386040200281c541d000c850410034604580d041c010012980070f5590011008644c0700e101240f8511700c6160b035003082140c1482c081c085103210191200c90042070002c01000071130302140e500c9042d644e0261140400d4001410701401038029034004c0e603400751406e0b5100c0c14500500f294408040380a0700240185055a001919503401540200c084007100300440d40d42d5107000c0d80074054110341c01599500342412003080c80e0440e4407114144060600070284201446203400500d042246030b9a0180f008504640d801091806410b0103541807607002301e480d030104200c0300c107902c084 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 18845042 1250 18843792 18843809
    0x1202090f1801030201140901020c120a060f05010f0b0309100c021f0501140603100302090601140309010f1b09032603090d030b0114070807080702030d030507020c040504110f010306 79
    0x40d000c000351094800d500c20f100483c04280200d042d0345a4404540a88141860513000b8018508608080c00644d2240b100e507420503001e2581c0d07040029500c0d100708200345c2d0312844001051760516042600c4d40c1200e41000e808102d00303004020460200280c0010f0219080ea8081040440c108069280c41140b0300b40c00703031181000d010f04521301840d501480c121880c1904851100d4800303000c2c0411884140c40100905450010a04c05402c20040298000c2418901600d103c40e40703d043d0038080d0400e4601140300d0751103e034046051049405007900320045a45480745030860000d02500515181c44001e1030011468048040714180f10041042d00d81040380703403903880c6004000540c60f110a0112500400e240c10b158001d10b5200742602c04644090007040c40c035000843d1200c2c50303d40c104410459616004000e410b0058070b081c403180c1852403040e1400300c0e00e03080020000e41841c0c1001d201c40d00581c5030508000101c0c2c81004074103410b003015504180071001d41c8004801419807508420350 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 18846292 1250 18845042 18845059
    0x7080304030812010e0606030f07050c0f070509010b030c0706050a061d0718150e0301060801020f0307020c01030b13050402040b1e130c0503010608090c090408030a050a0603031202090f 81
    0x601c40190002e02010111040c2030301c0d1130381c0340c00640202070b80c240c1c3c0480c0c00910078000a020604686140743c0c02c005181025410305800301400d6181030700321070784102c45401450f81002036040008089000d8003894134001e0540c0b13040b02050707041d4064403101419440c0c85602140200b0600e6009002511503208a400000300c0c090703c081981d0010ba520800040800c1011110b841011004000341d03070703240542048e2000c5401e011244040a13019242d419561408006400e0409100516000da00d407000140c032854141c4000e800d2400321900c3c9070515051800805495841d03400b03c1402481c103403000110ba03240c03400820010038440c0d14080d00142d4040035441000c50380d84503100404004c0f6128000890380050741420780e001500341c41c01080050006100c0ca41c0102c000c268007290b801c0461760250601000501c415a080d2416586141e000060109500ca6030242c50391280b00200305010035891950020004e8002030780010b0681e50201d82d0010603030712801c1c00540c80000901165 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 18847542 1250 18846292 18846299
    0x20301030305030105120703110d031b030206041e0309050607080d0905010b13110904050402060d021801090902070308060f01090509040803070e010f0e01180b0c0a0309051804080c07080304 83
    0x240030303500170b016003071007403103001410120918005024026240e021404040c2c4541d43e10500480d5115800100d0a0181440742c22000a0344e100030414054042d5004021900381420031814031690307140300c1e09161906411000101e07804c00909001c460003900c269541d0449414144400d0003401c00c8443d420307041501d0201445415000036a1034401107640d841c00d2160086000d080f41c0b00713030003880c8042d0818000000c030f616280d84030580c40390002d0b01551420240104c918101d0703200b0000d00b406805020350440303595a000440d0000362050050441c9020903c4d20007808588000748105e00c9903482c8036040100340d101d07117400c800904001e0041c948070305252503c40455042210b400740000e810b030186c05859031091103482038000d283c0d114200074a51401c01101e81400100040181076002035000400e024404001e06000350010060801d550b114074005120301e02030f5100c1845100c210f03040041c00c40c40701788181d41103980521010f540f28a000351690624900c1e40c449540e6000208000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 18848792 1250 18847542 18847547
    0x405060c0f01060b0403030816050708070b070f1407060b0111120c0d08011d040305070b0f0906010503010203010b0f030402040905011b0909050f15010c020a0f03150c020d050714010203010303 84
    0x40101e46010028090a5101c20070a0b50745d000d1444041c00180d01d003004070381500011021892032211a2420529080454032004080d034029171049034103804950400024550240039029011503615000c0c0c2e801020a520402a0041c1e0b100a4580d40d500c5d074503005240e001c7c80304026003140074400d4456100a91284100a8110247c003108901a6108008100e0b01c030b03501d030a0607911518500103d0040d0f01186041005c03000b03104600784500ac100322004a43ca00c0e039500d00c21600c11580d42d01901d403080002d81480c10680c400717402a8014401445401404000d8540c900400040c180e142c0e0369500026000d81a080310103846ca502c1c2550102c0c00090040d0250801640c030f850750a1500d65400459003161401c4803194a41c0c0d40b2000402d43e200c40c515081000d801051624404036445500081c032a04a1640301d180303000341c100000c004004c0080c4506032890098041003108000170800603440302600e10250007005800600f031f00404c00c4040b8420f1083c081180210346944e100d2401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 18850042 1250 18848792 18848803
    0x1203060306060b090102071e0e1303021e03041502070f090b091501050304030806180a0b01120204030c03020609030f070e190b0312030a0b04050a0b010f02060408030c030a020405060c 80
    0x10381e4801c1c205003001c5124041c107012501e95000607401480420319058004c0c3c040c2000140f143c030100c04941d8000361508403040081e0040551041d901c408400d00c0c13802914040000000a08240141031001d00c0c0c5080401030310100c5900e03100d03001480740f0000d0308030300700801c903005002058041e10001c0741903101c40d0300066110409441050b899100c80310150302801280340c445000070010400140086d01c01c49542e608201e014040c0c1c440d0f441c402480e41c000020884a680c03442c1d0b43e5905410096a1040c1044409062280110305d07181c02d5440317003038200030300e40030290098000181030005600c0400042c68041c41c65002d132000340340c030b490b0820205401075900d0f40841c0d03010303158a07100540314460075404006c01001051054000056416030780c0004015207201e07652541c409000e500e80d801860f2107501d8110001443c0243c3c4000505510f80141d4041c08540c401010000000c01c03800449400101c40c05c0300585039550b100080d800f9105d9030b005950402c8001c56050500840001c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 18851292 1250 18850042 18850049
    0x40b04020109050312030c1b010207060507020d0e03031603110303090c030c0105040617150a0306020d0e03030c040308090301090c0608040507090203090a020402070503070b0705040e0601090303050a110109120306 93
    0xb11902d01076a43c0d0101030303a40500e460072050b00d050400100340484044030081401d50741c1d491081c0d00143c0181d845e0380c22604034003001e0b00c0c80c1da243c40401000c1a0305001c040f4910220741050300c41c8100e8032020903644d025404941e0b24940407441d081c41494040d04100c10802d044504407a030364600100c180b03803107203800709489001f40716040410300d8a601550541d015036526a80310803510304d2207410701980f400060141c0c583d07040ea56071962400c0e101d24a10380c3c0654000e0300b015940d6480c00b0344030300484003406140c040c260024030900011049140c100d408a98201405540b100f1517440040c2c010b2400403001071450380380c04000503155400c40101072090707006206a80b003503591034415500703034482250441016004005034000528199020b008408d010350122400c001cae266480310240041940c90002250011904000303184e504038070309500a0080c40d0000901e45581d078050401e02a0901040038800d030b209042031a00c1e025840a103146812100f00d60110112540240041080d0301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 18852542 1250 18851292 18851297
    0x309100b06030c160f0602030702030a08060a03030206190609020301030b0103030305060d03360603060f08070503060a0b030a0501050c03060a06020604080304081b01020304060204060908210a02010b0306040b040201 94
    0x50308011518068042d0382c0300b0f100c2c4001491415121030a480c1c404000c5070000c80e402d1101c074400e8004601548051441414650002c2d40d0b075801919001d40882c20082904d41324070407464040c80002d0b800301da09034012000610103072902410015040103040350340c100ba0002c41c408400041071100701100e540c100c0b402034804224540b00ca0741440b058010950f40075000c030701c40d508010080d09846442e2044520503503040e00b0002e140425141c444001035001000081e204d00c03080c4680b0710740c03088110040c007882d001015074a00d00700100ba210395000308103c410660f00c140d80c501c140c0341400f02c50f2301c00d41d01a000b008a845c4c007031031480307046d082a1440f42c013030281010089206400090800c0c0255005411981555a0766603640d1550340606044160341060304269041c0d61400d001071030044d407003035802503111400c11100070014000355100d0082580100103003441d080c030381d08444114412a140050b52502140750036405014104400d5405108d010f08000520144108070f0340658401da = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 18853792 1250 18852542 18852551
    0x50d120f09020f13020f0c01060303090609060e040506060403080705010606080604060602060c09060c19051204141005090607150c0503070206070c020a03020a0803071202031e090411030910 83
    0x480306030407600c640780000c0d0030400385404249a4580003640f0010705000d15000340c82c01030400320404058010705468090360303440f00b50900030960400c44440180400e445c000c2e2200d07107811801456004250040d80c015940d80c0041003054540d0001c4802450700140403d03a9000300d4070b03100d4001e006034412000010029000700d016460103000b004110b60301070340104080e859405119400350710414416503c264200448000d87c1020702400010681031200d00e8211581410064100441c0441914041d01c0411050049100e09505241c81480c15140c0b4000c00182120a41d041d220319220160700400200c3c00404101c000e40c01a14044401e48081c002c41744040d005940c42d0100352001c001503000309002650192084581d80c000b00d000030b000c003403816aa134010460744842d0341c016001c590000140c103014030030940004081d0034510b10081d440d004a10000c100f10782c2d0b000b4484401528001440152903803141c100d4061140600026650b82c1080b90086a0b5940d496126008607401d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 18855042 1250 18853792 18853811
    0x6020c040507030608070303082d01081b1503070201060e0a0207060f020f07140709090308090c0307060801050607081c0c02160501080a09030c150b0406051203070618050d12 76
    0x2402040e081725080d900800450382159420b58024600405465500340d400c8800c4041c42002c586407000250402c014034000e5050001090520031070050180c401c241e40c09181550f03440d1114006000503030020030075101d4449090890240003e039110107981d007440020700c0b0003a0919801808141d101c0c1341c042104c440b60b4280302c01030740205a03198450050510481000c100c0c924030312071300d005c8441e0070340301815119034034141114401801500025219400c2045240d000c00281e01010740850080c0846031030440c0040c0740003014052140a03240100d80041003282000076554003d854050702c1085081c0554000d005045811008006201c0c0c056071400e5030945407540c109890040e50b509055983d55100d00c005000081011010018944030040c0071884000c240040940e800401040324120982040f06540c0c8941140b4850072600c1d400411103000001203e810700c0d4420800328440c40143d2150450000d040405065070140341c00070040b16900188082000300068000c00c0141b40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 18856292 1250 18855042 18855047
    0x4270905010c0909111801050c0d050301051509030709020d0603020d08030601030617060a0c11010f0b040605040608100c090503030f04080724030b0312130f0803070c0608060604030c06020c040507 86
    0xc1700082c40300c21040180040c0144000c441028070b54043c10300c0c5160144031a4218900031042d000c0c0303000180084018006881d200100e604150390814889080c1002d40300060345482c000e214030b25015500180001c040443c641120000b90780040c13680803000c421b8149800594002c0300c491b40064980800400c1c21642d89000007040c000502c001c144554640c540342d0001c011503018002803105400500e000742c0000d009494040c241c1003008140039480606200035140d80b80c1115120714103154042c449081c00141036403082c4004140400c403074042002c15546401c1351380043ea00341c080051440340791120140104100d420803412210f030f040e6581c1804080c0000b5551600c0c1d00b500690844c4280e900c030742c0240c1300606e4020140c904001105450070643d9014440d000747d90701c4910001c0003013101c0704d46124002c0040318050740c0390804d50303602c03100580d2541c0102170a114a0308085403440d140c400681c0c0155900c40100d0303c410340c071180e001e540c90354614011031103542024006403000c1e1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 18857542 1250 18856292 18856301
    0x20c030903011d0d050304031206090f0e0f03070201140403080c03070c050a0b0409050a060803040f0503060f04020d080d061a040305010c09080d0e01020c1e0a060305090304270905010c0909 83
    0x103e0000a020820f0f4001400c40d150741c4040e0080c0d007003040c1042c602c5010354080c81000300a0000031000502d2a141100c00000c0c0da2010003d4503058024980e21145841c0100485059640c24a008080d44150104008140c00395810240ca2000c01180510045900000510710300e40212a403c0d00b00c1c1e03644040181c1e607000790041c0d010f041414401000681d0080d048150000c09501e004500652904030301c0b890342d00310f9480700c21b040c1201d045c01c10940c2001d000e1540c00101e005001d09452504bd00840c20180c030114000303040002c005000c0c1100201c07a0b0000c00078149001c1c03120180340c95080d0b40c0b050341d000342c0002d840319440c01c100322542d14021019a130484042d807000d0b000e1441d0000d02901c215445035403190560151114201c2c00d036855040d07900c5045c04490360b8040651111060101d00c0c0ea00d50408414035203403001307200b0b00d088008141c501f110800070b00403000381e000780c10280c4c0f035031580c002c8484010300780365001c0100704042d08600e4040401d89d40308088940d0f034220060a95 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 18858792 1250 18857542 18857591
    0x30c030f01080a050c0d0201030207120203091e0a120206070f29070c081605030706020a030e0a08070f1e05010603020f06070c05270901050108070b040506030703050a0f020c03090301 80
    0x1a8030134000056982070045805121b00d00505005040490b03e40f15800a01410302010005810000e80580c0e10303d04100000c2c502585c0740c040d4510452030101051007104940600003900081d11442d004641d220b90888800582c04449041710344114909440c3d110448480c0d0845865841c03890030700c41a084448900c13908455540c480798480300c0c2c035040090380c007101c601001c8503030304541000401c00803c000e010f4684516401aa6481d992000500b158070b42403050183c0c3d000245484c0c08200100c0503183c3c0341c0c0d088400c00c8a14001031400d4400742035107030202c030510070f00555642c043c02810f40c0050700b100d0003030300c107040e400c00c200040203404e00c281c407002800e0f562062014025420040c5903001c070340c1010388022020200240510760a058119080e1810341c2d120b800522a6020600c142801404d11452440c103003802c02c00001c9841c04020842d504056440c0b002502c05103071070b08402c2004071031000441d030754520480c002d80c8a41c07044e0100d5020b907080443c0c81d2240200c0e465440c010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 18860042 1250 18858792 18858803
    0x30c0e0904060608010204141305040309031203021201151101050105011407230a03090503060c0a1107050a0b090103060e09030301120303020c0105180d020a150c09030602030c030f01080a 82
    0x24604894100800600c0150040e074541d80d90310004180210244000c002804c131100d00c0d9013090821904002d003030124078002e10806c40c01c18042c4130004e40c0003004401604c0c0d1080d00e070031080d008194220028090b0f01e616208442c4030400000c0d040c10f04000b59031200380e150381da41019002e50240c01e402c0c0c034401c0c440c0a0000c2d103105604070007010404090006ea502c1014440c040d0b128940d2203000c0c0708001e06500b0300b190451071184c0205500315440600805066001c0c00071440c200d0010805400341980e640180aa00f20092030058014010780c0c02400005010361600c3d6110703101c102c800d80000f0f14190219281800102d81d2030003070f0851610400304000110314507820410030322448034041c1022410b05400784405141b8920078020903100d0340c000c40341002d0018203840c01d5458400500890700a41d00910701c01008201412a5442d50300d200c1c80c2c02007040100300504903080b28586e030024001c94404030901ca0b01500c4040210701459180c1d0318a0300c2d82e42c0b91503000b91283c042c0a0300811 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 18861292 1250 18860042 18860057
    0x50c030c0f070c0603020316080c0a031a0a08011a03010207020609060702060409020f0304030815010c0b06010903060203040503031501020d0507020d0f08070303050405010c030e060f0417040e0a0c030c 88
    0x1042003040182034103441c0c0515030342091010340e0f90800650042c2c100d200030940100c00c100d05858100a103200308540da190513139032402c2103418aa650710030088107038105511100700078000b1000010080306404080c121000040e6120315007802040c0c80e0038014002c140c100c2000d0324a2a0500940d4000c0b5001080a0300d000081000c1141036800320108030b0700072809010004e020704040c80604504184841c1d2940ea80c5850318000300038078401001400104428407110403243d07804400404080d5006648200c1d40d00c4040040e19074010031b500c02032a2500000c1000b04029000c000307103001e0790904d034046d0310910a400040e070b101d441d0030401c40b0002c0e60601c001005498481c4110f0042409403207071a0038140f240e02c2c3c03190745038002c18041e80481c0d00d440038481000790921484038245540d1800b00301901c6043c6016072176401c06021242d6090000700414240180c1808205d4044d28517860159580d5480b03543c070340c1040c4101c0f48a030400e03162500c01d200e680d0003030003042080c103c0ba139540072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 18862542 1250 18861292 18861301
    0x605010501170f07170903090109090501030b0402090411030a031101060602030c060403032c0105100b090319061b0906020712080405010c03020f03160c0f050f13020909070f1101050c03 81
    0x154500014a12000c05c401581894607121143d00b00c540142494005556141184000941041354507031000c0c2a480c6041c0042012a00450b4400c1d0015030488441134191a241424840815445c441d90b40c98001e03ca10b0380d0405811410b801c0c2c2c0b41060100911255540303040a980300d000b14603021819802c0000018000f038481c0c0d018809030008082c3c5410001091000c0f04051201010b0340404c980d5140c0500402c01c10b403030f1952000300725900081d8901060003011076160450354004d04000030b00350054108002c11904805405a10716404d40c000d1009400001d00300d8100d4820314015024113500400c800401510b80605140c201c00d0a51a2a02d000700442d001c841c411400d9045010700440042d64140c1403006250b200d108202203807034100c107070074404000000380d0b2040380b8503041c1000c100003a0716600301504011000301d40c0308110345c0c0b010300c14002a00c075140c40d00d540031915104101d400e64002441564081c01c6540e0035040208014146003220802c0c2d51884a080080c40003d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 18863792 1250 18862542 18862561
    0xf06030901060305030715050906061c02031203090604020109080f07150e100302040810021206040207030c080403080406030e240a090503030108011a030a11010c060e0d0c060501050117 81
    0x1150000311190000500a54a49a007802c1d904010340468603090b01c8841611502064000e198120005002a12031070600c0000500c0300071042002c100782c0e05888100c941599414001c0f141c1c08080d40042c150380e03240201060340c4131801110120301083c0d89090114644000040c1400b51855290007045443c1c00c00c02c910803d1409180107200700110103c50380c601d03444d111013031030040d4416100561140d040c00c1c4000e09000b100c1512140b40f40c414091a40e601d501d43c00c8140e0055416280140d0f01c3d40242403c549100601001801e44000018004100800c4800030402c43d003065604115017505900d550341c9810105510b4948440c003030104545980e407903101c03680c205044030400121170501d603540341e0850700240e1007200d0300e9540f02c100348079026425811710201081100a081600c40c1a521001001d4140c01c2d0941040824860340c0100710650313000d040c00344409011112100360085c0010200c140034181180c10301c0c14040002600e501401c026a00081017016401c00da41d0f481042 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 18865042 1250 18863792 18863797
    0x61203210209060705010624080c030709030804030b0103030314010b07060b0102031306080414010c1202090d08030a1e0b01021002030c04150801080616050403120c020301150f12020f06 81
    0x303001010340d082101007815070b01e0030010300380c00e4403600001c940f00349030800c003000040501e081d11403000d10082c015a062a484100258000c41e07001049450f44c88600b0200c45c00111608021b00c1485e00140110901800c04c9403e0304880c402d640a120582e02c800d0f815210741000e10400645440902038040015541d8000f80c0782414184101c03130401d82242c0100a990b081e551000c030100d07002801b408140022000080c40080300c0c0b80017480b0340b54141d540144020300e4212080329607540860f0301c41042d69805624406d007070b0004016a224208074030074400421703100070800000000c0820034038280352180200441010140c010b440c1a01101001e08040d40c40148240502c1008001c080f5100480700d141c006001c0003540c500d83c01c0e60401202034070b0586c02034400407038110121a4054125486002c03030b000c4d240c1c44400c0015845242e10b081d00c0207544524000c2d803550a15111142034100307181501d00319040001c0c660350542da01c20003103429810503540650040203803c2e112615040c103100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 18866292 1250 18865042 18865097
    0xb01050409021e0427150513030809030d0911010e03010b0f0d080c0609070e07030501050a060507020415060e101704171e03040201080a0507021c09080f01090204061203 74
    0x1c0800c81814131500d9100d217203641e01414a90341d850b15640d1040c0110030007180d4074040c0100042110f400e0804c0103001c0789090403c0101080708150014101900138401e4494401c1101e1003030183c616103140110100200d41c4030180014850107140d01145814040c10850074409090610342c4220750081c0001b0340d50012040d03410110810644003816010419107116018280281c06a00e00f400c500c50765210b0701a00360420035051a0050019035140303030303505080351200d083c56650b81403584049005001c01070108550b492400100160148d0044008000c83c40111116080c3c07006581c02902d4400d01454a117a4045075000058006054051101c0c0700c0551004054140b00c4190b000c400c025000c88400e045059002c0207110842d40c1000003640c12926004040c0540d10f0142002035030740740000111700c4520340002645000e9409141c4610292503400c0030b07141001008040603020b8040ea00b0200d0040c3d107002000a02d482030b404081d044150700d031740e40c1036000d0360440142421503070510 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 18867542 1250 18866292 18866299
    0x3030302030c09061308010605060c0c060d0b060c07080607021506060706090b01030501090209010b03090c0409060608010e0303090d0201020c102307081b030106050a08090c030303040b01030b01050409021e 90
    0x4199607903078410213803c5d180420750100c401300e030070103080ca825552036500060040c81d0034402e081380c4030000718401e0075a050075281c51303484035000385001001c1d01ca0300c030009401440c009030215540b0001b20b101d5081e15070040c115a06920f40b208100d80d242c4100c00c24540d45030078030010a58500d818401881014048c04021907849910303242d40441c0d442c00c1c0d200b1100c0ba90741d10145021828000c0c03c45004201c030031801c500390f244c03144140713844048100c0390521541ea1a4038440c10000c660b44a080506090002008071501902c651540c951041d55a0302c110320440d000c00311064814001ca501c0036850801a200700b1882e10058030190032802e41d20490022000505004180400307200f5104003014ad64161407070600707c0009042110701d10030701044207030410040c44955080b0007244c845480c980b801950f150340b080e03041400e003641348030403a82c0350100005100510421144550580e401a13002d0b11480e603881081004580d8a850020340080495445074a14025000c0c0c0044548029 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 18868792 1250 18867542 18867547
    0x40e09030903010204060f02010507020c0a06121509090203010b040501120b090703061a040b18010b070807060603080307080907030b0a0e0316031206050402040e161e030b010f0f0903030302030c 85
    0x400010f401d80e00260440e0340007c1500b00129070583c0d09002e015040740b880c1c0050b060200302800070501e8901c2d2409030f0340600c4183c488820304200554008000b401c40c09041528403522940b0a001602008600368803e40c28031b200440c6616042c41418100c582448200e0280d00a980d01c84450180003000c00d1030f00d000c7e207800080411310502580400c0c201a004220404c0988010482212031000c4010300903400c000080a50416140c81981903c02d103030013481d00c1e1030251812070701c0da120740d940080545007403282c00820005081c4c05540111f0300c64a8541c902d59401e00701035664045480090701c901908400304000140681c41488000d1141007503030b02e0407800c0368040700c2c1d07900c0c10341c0c0480018200f04c0d4402c0f460130040c81002d000d420101c40a601d014500518560000c40c094424140210408011901a40910940c0b00390b140300f428a4140700c1d04c0081c029009041041c2524040340e2024a01e105030b0348140c3e58452040e0b10740d221502024215103044000303400040c080385008104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 18870042 1250 18868792 18868807
    0x5040501140405180a05011b020a03120e0705031203040b01080307050a02010c03030608150103020a17120901030204030f06020705010501050909030a0c02010e0a030605041e02030a0602030601020307020d060b04140705040e0903 99
    0x10f000200c1c405000d507001191050b10f0304218901c042303403142c1c0380b01150060100100043d601c10b0350b1004071940410041078640d501c261030346c280301240d071103150b05105405165200306141c0d0003861140740200d0002040360f82c2c1751017061b100e21541e2030041080e00140101c000540c01210f81d044940d02038580051500d4072510ba40f0b00c0d0007810a004520448124010821403401100c000051320740c083c1000c1080c86882c00255841509044145201e00c02155070f2005902c02e9064800854000725030380a81c00d06810024002e41c0b00c0710041d58107508010002c01d86007016a5614003692007000118074021003054101c80090b400942281004000481c01b903c2d5600d540c0610701a41c001c003400121030900707107400d01102ca820b1451b044502c03c4c1503118405a40d0228040d840d00c0c1e000000941d403030ba90000100c0c21841a2803000350b20401040e6848280907895101820390786040d00e0030041110b0701c0d064002400012142040021001c200a100d124561b41d0078a803c0a20302040300e050101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 18871292 1250 18870042 18870091
    0x90c030f0507080f0702010e1906090503030106120c05130509090a0506090f01051605040b030709150c060b01020604020f041505280b03090607141303080a02010605040501140405 78
    0x5007036400000090f40302d03041c008000c0280c212980c00ca0880c0c0000c12084030004129a02d070070118440d0244000317011206400d000c1240c0098126943c008142da0340c030368507001c018004074045002010502c0c1340c608007082c054010411070304c40300ca410a00b1451039103407004101e8120790040c1002c00324000c090341600068020070070903000c1d040200141c050b18000c2074405007140c60042c8030b4000e0780d650304400c040b01d64001045400307462154440306e989581e4520309852011107030340200354a40c56620010741565000520f21a4280325200902c09814003100480e0b07540402d0300d0203580300ea20034026580500e860f80c8004680c00702049400c0341c040e92040000c00c003659801c80d481e0111010090700c50f044210b071a40c1e101034407680714180c1c21070038a031210540d1844002d01e07080601000c1d41050301d00403084826154200d0f1610108960f903512450080c195400000c001d0015600700507001c01c440c9414003411307068586025030305100080c102c0410010b001c003d07102d0510f0008500304100c1c00784 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 18872542 1250 18871292 18871301
    0x204060303050904110906040504022d04050a0e0f0105040e0f0a0f0209060306070c0209070c0807030207080601091a040506061e07030e0f010c03030506060904060906090b030a0309090c030f 83
    0x5000ba22a039888000600600099400c0c48401c00025034082100d60103039641c04050701e00f07a400a07180103844a1048d541180d40b0100441c595910b40740e8801b2113a40705004071300410646000344e81001c4420f41d207481c4500b0038101135a60b40107070706103440144080c0c10280d01500e4020740724800c449210000d41e40c03882c02c0601c400320a450f442d915406050550502c04403994206030264000d000d42e2a020100514189050400034412038170200821020b6205e649245e1400b50425841c6903608204c1c5006542e0343c1aa12800c5128000c0c1800040e210103035218000300c0d07110f00c080381480b2144d90030403c00108402800703254002814000c0d54062002c001e425202880c0518261781c3d101c1042c20054500c00100b4490340c8a1081e21801e22417a0341c0c4510149801641814081002d81302c0c60005500c50203008407054201d40b828000040c0c50040390005012285800403c006410200043c035442c1c032035102010340807440010041040e40c1069000300258100c0d0315000075224440541c400c16034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 18873792 1250 18872542 18872549
    0x8091c0207030c0b03010803030f10091b03050105010201050105010c0201182c010503010204240e0907120605030a0f1e0c060f082a09040b030a2607050601090903020a020406 76
    0x181d100d031a040c0108502044941c0281000c1c26140d429503143c40000350756440024105032510b03e1040c0450351a00d404280e800c081c2400d0102800351600c544900d0309254240e004820009003000c000150350350061143c941602c0e0f069541c6109540b442c1c0054410140055107400c50901800d00040d68464035400c1000404240c0c3c100d00c010b0101d110007809401060b0455031003070b48100420811150044100360941c5000c0824201e1081020b0051352170044041d00203800074007250070070009c203600080b84007800003007100400061740c07900140340d0b6900c1485402400100c0320b0919401159112301440c80a41c50319403a524007510719520804a81030b0740c0e02031004a00c00c980c1c0f07507410580007003070164800c100e40c800816801900c100c580311182c407100d4120348034400107403003040d644440e0411408420003a044448442136441c01241264044240041240c503002c16004454403240441e08075070b4200005000990a1008c07000091403011002c8066104100c0041c00585070303405080d004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 18875042 1250 18873792 18873797
    0x60d050906160201020c031e130e16090b03131b0305151f03060509010b0a03050303060a060206040506041e0203010507030e060903120f040303020909010305030a1d030c0108091c 78
    0x38101006206103009540b4042019a4014031116204c0707800002500c0112945440042c0a5280c0308800030491041c9440344400a84078000811100da440c00403034028000a5683d41c2d003182d403e14221882d2071240039500340a00100081207203c442c0041e011000c5000d240c4141d24089807008a801e4000070380c0c4125800e422883c2d66483d24114600d60070b90007234209900340d0f03814001e0a00503401038801c1c0402801103a407000842d09581d000d41c4503403056103003c0d0085200f29203030700340782d5981d030411a032440c4501725002021403450f2011407454080c0d603020b40100b00c161200d603590030901d0445800e4440382c0e40703451240d0300981d900340a401c0c020030f070a441c0000c4e6050140700c01c03030600c0030040c84c010b000d600401c00e11074400004203049034002d04442c2010026180c0c0c1c50110701a101d0402c201364050074880012090000110052001105544480d21032407a5120b80a0324141e0058145034150040710603284254040c982d5a5401941c6905071003000c0003091000e0031920280d0b0342e8500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 18876292 1250 18875042 18875053
    0x6030403020615010c0201050a0f02010204080304060c050c03010b0105120a11071a09060108100506040e0d090801051003020d03030203042109080c0a030804050105180d030c0204141005010e060d0509 87
    0x883c40c0802810743c0c02810070300e054940301c0740e203070006031062090480640400a241c4003010300389100b0340c1520302600c881e00c02e4a5480c0e596443c0181003c14800381500c441c028070060a4541c0f40510964004e10300c10b1b1501c1e03040c1240d61301c4921410000400c0030a4080d1a440c07402e601e044c07240c0040801038402d0a640c0000142e118500541a000916409242d8888030040c00002c00008185506410018020415640d0000458007820b01240a101c0c40c0c41065113815085070031131111010380d18540003c101c260341c2c40c20b0940d6a410984006900405618000004a03119400940d4014014100e185840d041000f00b003507500c5103011440001480e42005221000c801e005110803008210740e410801070842d19100c000f48103900c6510b06029000078000c104c000c170210604c508400080690071700d4521070a000e00220700200080344030344d151040342d80103031003140d8213640100300208e07000d009175043c50015641c81400085c03459001c3d00600040049101c01d000b000d103c0c0064102a02c03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 18877542 1250 18876292 18876301
    0x3151e050423120c0a020d1217070e010c110d200405060f01030c140c060106080a09030e040c050f0705010e010b06040e15010908030d09020a060201020405031f0b060304030206 77
    0x540020000a02c01071036510359880340c00040004205110032640308240381d840d00411401460700d07250583c001e4000c4c880c2d110800502080702007000d609005d079281ca940c000010b688242048a040340c60202080031281c003400213510800740000c1c507910441c8980a82d100c842c00003101001c018000b100c4001e800c1d0800316644c1034440e440841d0201c15107080c0080e00388640003984841c40d0070000c0e0304060780ca040402215204400301090b0048181c0c0855885d1180d401d442d490355805d0081d440460304a501041ca04c1700c940c03081444058040d590003054100180400c0041e145040c080d1381080001d022100200c160b030750050004078850b0000060901429202d01d096070300d4800010311690040c0400c10844181d280342d03507070245084641e07003000084000141c0324000c045c0c1100500e8400860440480ca08640c040040301b030080f2402c42c44a80d640700100e00740e00c5a8011140c00d9001600c068202e25094100e00f42e02001010001c1001078074000800c001c0d8104035415070069000340f0600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 18878792 1250 18877542 18877553
    0x61803030f120e0c010f02011a04090f1217010501090b03150103020f04170d0e0a0303030e030f0307020a020310060b04050904060207050a0302060f01150504031b0806010605070605090102031003151e0504 89
    0x4001c6d0b112240000c1c440100c1014070024082081c2040c80e014640380c0501d081040254525520200e07400042d01c06802c0e2440402000c403a450151120b8684200c80081999070050419008443d210b000b02861642d6a00794141c3c40e105150946050617000c1c802501354488000c09003000d02004005600030010941c00c03a40b400007480025400c0c003442c0c100000c55600c880b505042031b0380c1c06050104610340b031243d1841c61880380e009404410500803090003e42079010402400107402142141c40b0803400087c10011101684034491240c50100010022414855a19980180101401802d11303103e620307640d05059900b881100160051001c0214000980ca403840c0035103044442c5c6c6007140f610071005402c030300c9107000103000b0291034a070704da04d1011030b40700c3d25016248002c1624070079651240c01800c40e0f0080c200c119142ca04110006902400c14801c0c0c0f4030451503401101c030094610345500c414404020b441d900c003d03454408146501030001c0b004441000710740c0000845182c0741c10030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 18880042 1250 18878792 18878807
    0x140307050d1401062c06070c05011706031903020f030a030509060106090308161509080a02011410030212150702070f0509040209040605060a03060908090901061803030f120e0c01 78
    0x281d0a8645000c001400410b80c0402c003d030642d20a01c800c1c3c0c450803414500f00303030901018101131b80c6c4507000285190400a440c5481070031601300382c9640036120081c001d50303403101a044900e540c01d5407000082110080b030322030407105a42c0c06801540c0f18259041c40c40d03801c581c06504020003007911603041c000c241004010203801082503292590301c4a0569407002414410071b040003140400404103101405900d4003448e000c2d1244820802a1194510380025141c101022a90144d460510414044c0c0c10601d40203100e07801103030300c200c031090443d801c103c0f610102c030140510074440c004013866285641d441150081d8059001880c2c0349140c500f02032004d070a16001140100400d4050100503210b10f030785550490b0303103c0c3e400705090b951800446ca030031031107078000b5007003d04250860b17090190200c000c1c20300701820303104401160388503002925085c4018050142200e5030840800100f440b807a5010500f25003403a10490001c03082c2c18180c140d030706135070065030b0301d40040100d414950f0304240d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 18881292 1250 18880042 18880061
    0x706020303040314030612030c010603120315090203090115060e10050a020c0f060c030403080d06050f030a030309030c0c0602160918110411030403051c0b061603140307050d 76
    0xd51031450103580040240d0000d814216013007a020012940350364841d401581410101c404607515507406c0e07429540a0411448150740b035038607104d6640415446401000071041c00e0301140000980703071414200081d071000f80741c1612551303914000300d542d08210303950800600c0190781e032860219040080140300401c0e401000d00f481410406182115000320b481c6001110840d141820301c03d0343c10208503d071144410b000041c0c00b0000d0f001c0100615500a00200c0c3c816042c01c100e200e450350144114509441790716a0305030f000381c1292000070f20a07000202d11500c80d140c03401580d41959181514400e241d0011400350304060441e0030b030409210403000c0148012036040c0322041615250021106501e04058800110f0340c44d102c0c5261516082120b1020354102001c1d034074036160500805542101803115500d105441104905c80100d019207400460010319051230100764190760f00c40041c90504c12003d20088903040c4c1491991000558800c08868030317182d96807641c418008040310252078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 18882542 1250 18881292 18881297
    0x501050409030e011b050607020106060e04020c030724020a030b01020c010903200402070507080a02011815031a1008060f0a030503070308091006060509010306080105040b0c09040b04050a0b030706 86
    0x180030700209074842c0302810104000c1c01e050003000742014000d101e02a007440d02501d644500824095a168158010402c0715100c0da0780c60480000e0908000a03403088100e80e4406034401d2040402003451800f510382c01514a88001001d0030541032102c0580e0041880d0302c0201e69030700080512940c05110a680380c4000b440e00103401401c1d60f4406540c1001440041584400c400140300e140d25190304851425811808031140d180d5030303200082c3e40e2804003a04900044140c0800c80050905401540c103a8140d20800c0b4546880c0100840c010007042079070b01a828601d18031424240c54090f03440e480340d401c507500c03000ca52030000e05101c00c1010b0481d0103030048800d80030030004600044261601c45030725241c4000251245441145000c4a4041c0c0d082c10518103400050840d0f0072400405d03403c0740c00e890078406156503081c03c9089071801c55010788842036040c0007070810031a8500a0160f44001030001415a4480001c1402c40c0d008a50702c0360125528101e5910619040245100416951 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 18883792 1250 18882542 18882551
    0xc040b06070209180109050307060603051507020706050703170405010506010905180105060a030b03071d0c03060102370f0b010e01050d080c150901090b01050301020a05090f040213030807030305010504 88
    0x1a0b010070038038100145403440c1200b40032442d4131800b50131341120b0880d03600081120303103070035080c100340008003c0c5100480d0188075001c40e004600424000301c6118003107a40290040030304e0705000799040d6103d04011010080c00301180340c030f82100080454001d5000e080001694608a00003400c02c102c190881481019000d50b030f01c5204400e000d1017410b44d142900d00507225112000198060000d001215a050141c6000400d81c0454901502d62003d9002207240c0316880c0c80c1c250185910060300d40360700503000050b0303409000c000d4400070720707800c000c542c46100b10314941d0307802884800007568211103461154004100f4490200705d81405058074002d01111549003078001a840c115840000700032000215100b208908180080720760004400010b0580b403800700c1c4250f000f0301c600c42c02110860380c0b120020038079041c1442524400405501d5a5207000120301c1080320452034a040306920540800c942110340d21000013060046111701c5130a83c0710305052a0140c01c0e640160030060003585803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 18884898 1106 18883792 18883807
    0x1050106121401050d020910030803100311030c030c0d060212182109012307060b10050702010c120512190b0f03030714030403140c040b06 61
    0x1a04041080840d00011034000c0b180030f0003015082918407000e0001030500c0041641c01000f100d409100007a80c0f9a9605070700e80c4100c0744c285020518880410410481114810914001720050621640f4040209075103241e82c43ca800c3c41400d08600030000e00c141541103403030316089500011414500200145255004550420442c1c40350650001c05462803002c1303401e869845041e804e18018044c07004440d8002d010500302c0400d4101c00f02070b203454000100802d4110720410b4003240b560781d4001049136620740e5a100c0818400f04214000050703901c0102d4800c2940e00c140c090503081001c0303030308541600650701381559151911090014030f00a20710000e00c1019109424407200c94024180110403840641098040e40103005d00000548803a17586003601c0003000440b4203165407620313928114102c00d610111641c1200b001d507002810280078002c6222016100c0e03602c0c1400 = true := by decide +kernel

theorem cover : BRFrame.Cov 18705042 18884898 := by
  have h0 := BRFrame.cov_init 18705042
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18705042 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 18705042 ≤ n) (h2 : n < 18884898) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
