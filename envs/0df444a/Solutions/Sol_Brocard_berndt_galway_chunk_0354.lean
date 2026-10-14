-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0354
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:22:35.156996+00:00
-- url     : https://prove2.me/submissions/b92adfa4-b499-4ab6-9e5f-55638269c260

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 63489211 ≤ n < 63669067 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 63490461 1250 63489211 63489253
    0x18010f110706120e060a0b09070f09060c0311120306010e0316050d05031314040f05060904080a020c03011109030c1005070f02210601170d080c0f0708040308091005070203 75
    0x9400c5201140d51200d8101c16403170f002c41601c1490986840e50740381c80c46410b01d02159a803014031481c02c05014100c440001d800f0340140d028403400c0050407070041e0305140c0541450242030b42d100045524030389210080d40d603150003c0d51982e00013817101c0800c82c5249000103c11403400a21490b50301c22070703d02000c0010405000900700c0c0d03180410300031409881e008003c40802068160b60b502503d50b041e03c10001240d0040c12501d18041c9000240400f40d03e2b441c0616030300a51180e129a51600b031468180d00d414680300880307500d5803c18890322200c21074100948182c50b010303421650501080030070043d181b00741e800d214001900912100002c148407514003001180003070013401030040640e86070104005248480070496000f03c0040000440310001c441c00c1d004000041d011943e46c20a000701940d4000e030801b0040b50000c51000d90040f21241200c0080da48000c129a41721b44e82d00d80020150800100144208208140402054051030407a021194010007074140410644902248a4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 63491711 1250 63490461 63490487
    0x203121602070806150a0509070e10110106030c05090702011103190f050a02070c0b04060e090612030c06040506130213020d06050406090207020405011a03040b090c0618010f110706 79
    0x4030419034000341d07041050021030f02417000c1c4d0103800c845028a405210300d5007204d0f400709002d2003003002001525503010920107110201110014000c251500c0c048449203050442034065502e4007500200300302c850b01c01c0400300c51068404140554420109900b01c03203003c49254240301042000504a44400000e01000c045440703001940650008443d000c81c3d4003225010085035001071070b80140002035202d6002030000951203840c01c1d08108008000c503405240e40c82c0200c400c1000710b03290b60344020500300070008150490391180b0711341e002e45940c3e031402d840c10340d000c0c043c401c0132505170b06594481d142007d03005042a00d50609200161000703501000c04007021b00d07074a2074042055030b40d50048000070701499a02680300d00352070040104451040e4000b14a00c202010415010019441582c1d4061b0300821041d8945e80e0b00c034016814071614501196001d032000850900444000781c0340c1c50b8100c801c1e61001c90300303010300d907081d200302070000f8907118a07a02c0030f101000b8007440742551000d10703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 63492961 1250 63491711 63491713
    0x70506071202040b03070c050c0d0210111002070803060109062307210201020405040f06120803041e030206010e0705090a14010207030203030d0e060606071a18030307110705010203121602 82
    0x3c160344652020482e0400d42d092400500380000301400c3c08410421078502180c02c03100da0502d454582d0014080d07880710f4a212040c055100e1039034600350411b2100090018140b1015075880da0302d40f40c80d000310761040b079500380131848103900440d01e148540441d4030b41c0c00300c00d8030306006000350600712441074100c030750700720313040f0300c0d204181031496130b54450f15011042560000360302d4a04000402c0103684000720160212440c3c5a010007600c0da528007800d21154000b0f45a6a0303d803198108820340c03002c6400700000246002011408055000076a01c0c121140131003500b50b035403035814040710385100b865603070b6a02541c2c100c01031040d86480c038010500c44105004a6208a9032980400c0c2140c001510a2010590b54071802c8070342c500522042da1f00c0681200c9562410159a40d0329112290024004518407600781c0042c1010703040e80c0d0400d10046540d4116916498a02402001185980304150490203a00000034032540000156000026181e900088540e2813141c28043d00f019100f43d10f0031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 63494211 1250 63492961 63492967
    0x8040212150403120e0304090c2f150123041d0a0b07090510080403020a060501090509011103100e1306060608010e070f05090603130b070201140903070506071202 71
    0x81100c4500299800800c070705a1800d4140600014410205100c0181c1460302107102e100b0003104441c103569000340000791011560504841d04420aa40303264841e20308900d1140c1c0038010340100c4405c14000301200c2080c000600440c041e05828894030000e161a50810b551000d40f03240c2d00590000040c100191700040041140d04540c0e501115039083d41059507030300107018a0002450380492141061108186000080742c0c83c0c07195003290a0802000c440443c0400d4401e2200d480d10540002052241e540c40b008010300400c0d0643c0c1ca58140c2d0310301421004240500380c252132194802c52800702c0c24038a8030040c415034070303c0100001d10014407202d41e00001003e500c102c030080c040b00c0d83c84900960400030801099030000c0c20b80001c0c40001000c18080315441000c440001c082500c009807251500c01009a49204640000302a06002c60401109a60540c042d020000d2020449501d580340c03a44c140c0d84038070840c44068080c3c2c02420018507594081c000807418407505a00041c9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 63495461 1250 63494211 63494239
    0x803091c021305070f030b031204060f0e04020307090816030305031501050c0604061d0a1709030a060606030c0912080412030215090616020f1005060a0f031a0c0a0906080402 76
    0x1115402c40384c1a010807040e0602804090389441114002e100c240c0007414241c00b0810307119481e004510945040000c415124040d01344921070344550740101600554481c2401d182c0500383c4950740c01500154890003000322401100b4404410850b90542c941518544411f2510020300031041846814000108201701200b4800c000340c0780700c2c900420000984141c80000500c0d092807048500743c055001214250215030031a14600004460040166071554403074042030802508807006440305151020000f00c058068100014000b415603400c1002503c402c80c81d84490010364002e01208001d0009124281c1c00340000c04d52030b4001c2c0101c520100461328000e00400c001c0398612983c0c0c0024050248100580c00a4441459076001400c4030500781e102d0b20769645411084044107988600200e010b50300c540c0201c2c8003411142c8141c01c0a59240d0810501e034400f140e003001032005004000900400f0900140d54280403550b0b284450036181010458800c200600142e078172507122501c0341 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 63496711 1250 63495461 63495499
    0x206090a1802040311030706080f040204140a0e1606020a060e070e010b0a0207060e0102030d0b06160c0e0604020405180403090e040605090f0102040501141b070e09070803091c02 78
    0x1070080303a84000c0035a803a411840d203020711000310520107000b540807480a1220f81e412420341075004a00340009041980c4500000f005007424403406c030300758030b02c2d40d060050b13041d1190050202c04c9a0001112080d1494488201880c0242d02c524001a0010080c42000428540101d084100c40ba0700311209940ca0345649407680e802030380602221b0100003210050307250148008401428542031802c40c1150000000c0e40320321508242d1588075640d40b420b02010359620080e0394107000310701c4a140c18a2181e2400000400f214000c1c03044032001840081c030580b41c240210340540b0000f80044507211404210310604002c044d01c00c070140304000102041e4101490180c61181e4003c24000c00d69061503000c190074402031041c0e25141380d004000901c10f990f00040182c80b41c60b00c01030a940d0340c0c0500e1904565a11510703800700031a004a0304001101119100380030f0103070202d401a1a545a60786444950328072500f100705420941c8003540070130301420400030940c140e00240012070349400d051156 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 63497961 1250 63496711 63496739
    0xc15040f0b04090b04051905040f050f0109031709030720060a05090118140111010e030309060103052e050606090a0305060a0e010b0604030605040309030615030611030709030206090a 80
    0x1c40258046010808115540903119032401c1c256410003046c00c202c1002500c0300c40054000411540f1000418100300a44c4900c40d40c13160041e003a00d07400d00b5841109ca02800060b40700398005403404c114000d0000d014001c40c1e00400440c4015031a2140700d41e1080e2100f400d104044051582401091072243c5800340140503039135441c1d4601d82c0e5061480e0014103001e1540840c1903c407440d400702804a03100700c003080800c007442400c04d140f089034080901800740c800629408100e01001c414455a540001180e9060728403900540d008103d00403c0b122034200d00d0f0152490054481c040400342460341d601168000001502080c82d201c40103000c03d50040e04c0354002c8071b00350302c01c07020864280064818822b403060700d075000340101c880100000705030f805180405482a5a9240843d04250048081c0e00c011540030b001480f020002c40c040700c0d10350300c15120694000d4200710708000748203c0740701140c3c4034a440380c40309000c1d14155003e210b03203504050b501503046105201d002c1242d40405a803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 63499211 1250 63497961 63497969
    0x6030601180f06020d0807020a031202180a09050114011404060804080d050414010f02181306050d051c0804030c14031317010b040203060306040b04060f05190b0307080c15040f 77
    0x41580c070101c5c1c0c1e402030450740020a400115002160120002a07224600c0c41c040d20f52080d0140c0c844081d800720b104121003840300c0c2c96000407144000a1051f5868000038101d0780b007044003801c1c02d40144010340325001c00d132994090b406410802803104d1801042a1600705016110b440e041c12072010030801140e0049d02c00352556002c60014040c2c0050034010180001580e440540c1824561803000301007900420500e4071074800e00c1c00c1d00340160481c2d4401c170014540140020311840b03490802c661a2410102c804540101300f000948105024003081d50065526584490703502c140ca440d01c031051404a250100c50740410002c941d030f8005040f0924024004820010000700a8a4491801c461909005c2d901650040c42003180540c0c011481fa50300c560007030380c9901d495803140ba04500900c04100b03040c80c418541010f2004044103001c90030041010481c00308001420b103402c2540c0c4400c0b512660346203600c2141c000b41c01d414140e0584280b200c01c030060b10309003500c1c3c0040502c0707002e1a0308 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 63500461 1250 63499211 63499213
    0x201111606110a020d05250804080c0609090103060203130204021306090801060303080f0a060e01060e120105060901060509010c0506010803070b0a02091f02210309071406030601180f0602 82
    0x449034040c896a48503191500c031590034020b1500b00c0b00b84020391203200c50800201805004158842002c1d410b1400d4000540c85d0100c3c2400501c841c034040401d40c0090140c0342580c816000c15400d42d0400e0700448250781c0000f000300c003060b840c580d40c0302e0195000401089114090281c500d0060300d8500190091a00d01200c60146e0390400c2070051114003180d001110f40ea05003001000420380000c00c1d55009202c0012102050b61281c031030101074030311588030203100c40d400d40001550641c070210881c0c2d07084080303071f1034511210a0000340b03090350000d44803254062558001002401c1c001c03030090a103500c045c107101180700303080e894503800c00e0b13000d134012002d80d08002060405c01c8002d1841a9201460b0f42085050107860004150350304500a24035901c1300c2d0510208038800c4c001c00c0030030828110f000305000400c1d690390078400150401d40d0940b03c1b80c41101804107917008402d681488402c2e010300304a0850b1341d00c400441d076011095805081808500c1c10100d1881b00380452580a8951a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 63501711 1250 63500461 63500497
    0x2010c1703060f030c0607031404030b0114040606020d0206071d0d0b1e100b0d0f0c0e0112020412080306040b10050304050610150305090c040c030911030c011b03020111 74
    0x20082c82040c1c1030491080344641c0220484005e1507940320180d450040c0c040c60404507042d5070003680e40b00d0f44107070b41010700034102103000041c506090607000c800b0a80140d405004643c3d1700c002c01e9035200482d0440354050380041380003a05040c0700b100c2c1c0180e0f60315103402032105041e1201c00700325181c402020690b03040441100b0010000c42c40184c007144011031440c10203013442c100076040c1c1c0c4041540076020080d040021500c4841c149034001e10000c04c04a102005000001c1d040644055032201e207440c0402c0c0c02178a0302e600b00b1027520990b0121080d410f062040002d5a944203145684014005680140e84140901903602c071070010ba1540e140302d40b95a0340e030b401c10741481803402d04020000040d95500744024018035541200105510300c0b9800c001c94913880703400c1540c3c2000d900050641e04141f52000000303805070302d90400d0202c28040c030800c0f0601c81000081c1a01d5040000425011881c0e525030452841c80e82c441801101d4080c2c0700010300d0b406018101c0000d6031140f01401d0070850300b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 63502961 1250 63501711 63501721
    0x20615030c0414090613170a1218020f10090528082103100b030a06080d020c011d01020316051603060207060e010501030b0a0c030b12030c0609010e03070b0402010c1703 74
    0x4000c842d400c030002481803100072070b45542c0c0080e840c914801c2101200c0d00408c1c501d000302e010b04040030301114905800e00400641003c0d1034100355840300141d00c51b00d01000c140030181042c0c90240d6074920541d1700c2044640c282000d0011703010320450180c5800c2c2d10265040c3c00c010033b0340030310809080384001520035106001c100040752080d4043d2340381c40150801c24000000042c0160303104581e2031010b059107aaa6500d001402000781d5400308501d4044c04504c0c04900f80e011640070000a4241c842c0d0b43d98192082041e041d40044406a03400b627882086000f40401b980241202d0711807081c0200d401296071000c90781c0e12441168022035030160042491001c2012074000c4c40c900c0801c0f800208220340c0365460b543c840300720151000c901d0f907980d2942e11034141c2c4690804d440f071a9024004a4034550300d4442c959480d40001110b440070301071980440c01010b4180990b01c00140c0f044001e500b40207054480028112001d00100d061040c10002c7c0300c0011656004401d000780340007189610f0b4940 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 63504211 1250 63502961 63502963
    0x2701060809030f04030213091b0503010c020102072003070f0b030403030e030c061506070c0b07020a0515030c130801050405070303081605040b07030306080a0c08011a01020615030c041409 82
    0x81d1602030356400501035041c2904092041d40c007180e4046824101001a000280c001440b002d880503100100072403803c1612241d4550410485000750020810300c0000d08040b400c034040d001c1c1c0200341000351100d101e0300035501030700c0b520803c0c0014181c80344640d852403080c00701150f561000c241d41401204000905415100d800da0b02e24080000d5894407510b040480d45440000303004412052507851741310186c0d1180d45c03d584900751321001c03c002164803210340c10040e0f045000100d2040b609500003003945d08046521002450003001c00c0c9003952510007000d82a41c10800d86450503c1d0081000500002c0034090117000d9409040a4900a03046007402481c1d80380040c0303101680715600d2244c98003da40042118221040302040540341c2c2403c0c6422030241100394850481c07442880400000c0c030021030260f4045a002e40c008000c01c1c125502c0c60401950302e1103a060160f0816000609180c1000820302c000130340007016903c54189402c0000e0481d41c90301c8901e248a040c103801c100741414 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 63505461 1250 63504211 63504227
    0x90604060216060f1b0c081b1203070c0314010207020d030c14010b0a0b090f09040308010806060f060a030c022d0129130b04051504140702071202270106 67
    0x603a240603030f0f96020130301000d041d00c15121111080307841034400078001e1064106001c0081c04a10094581840c0500001c1060740540c2105c2d030b10524900c502050940c4000080305d0300f1550111081901514541340e489814078102c80920383c55400b0810782c40142d45401c144012180307c4d1b1a189403a0782e49003044102c1148501c00c0c012aa803400010240f02d42d1614000c20884241c0100503030b460500b000414404555040c030740390407031310301c909210801d500700e203001d03051b26442001c54036107640d064200320b402a942d04140780c010038100980d0101c2c0703200350000c10303000c1d88500484500111104000d2020030100090030f0320f0310340440c1c123058061020300035188034501200104402207d5a9215025031501d00859445540041c116154150042d004038400e03400040c01080540350181c861108140d607000715502c91072910020202c070078145078581c4c0c040c0e0001d0380144885410204944a440c0582c50141d0b403100000010315281d0031000800000e6404200c00681e20f549002780140500c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 63506711 1250 63505461 63505469
    0x3030c1a010f0b090102100e1e01021602120c0a060e030f070b03011514040f050a09020a0818030705030c030d150e0703110c010e01090b0709030519050102090604060216 74
    0x4506480100401501440c1c0e0000f520803c01c0c120340e6030501d14005074a0800043e0b5012951403e041009140340c002141c1045c0b5404c45003401160050106021401c1384200d030310303000580814100000250400c481800280d0b0301140407585030380034100c0018842c584644c05400003564080040a080c2003e102c5c190030800030300020080c460070440d42c40a42e0205000388071030b0b843c0304940c0c0c400481c41107140484007051001703803994554440a902e188152140503041c0203808211002a8000301c1d03200704e4480c4140c0360740f030705060380340d01c190441540424901ca0503980300c1440414042501880240a6000804000d644c0d8031566000e62080d54031031407480441c248cc02d2010451204445074081d03000d107280c070f40083c0c400100e1114038040e001c7c0c0034200c1001d40c42d00c02201d03079115056001c40740083c081c03800510f0540c5c0d004800c0700c0040681c000104aa04404110400160b06404401130588079100141c20005000041680c80c1c002f1703880080143d1002481c010f0003442056900060 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 63507961 1250 63506711 63506753
    0x19060b2805030703051b010314191505090403030e030c070603050a060503010608063405030702010f0203070f0c30121a0108070207030c090c09080a17031008010603030c 74
    0x2079441d5844051b2179190350036000480503255441190940c1c4240d100103100c0c143c0400001003030606842c0e48a00030b030155120a960f80c074082031600440c4490600408440c0000e1040e01c8a44c3c03259011005440d212110400910040c491a2070065041c043d2a001d0100c40e0b4000886141c00c2603090f0682d00a0303405103019902d4031100348540305020480c16844000d28040702550042c504004404100700501120720307124818008410943c420025405241190300902c800103004204008034401964584003180c1d50010303800b031103070142c15030240c0700340035101100c800c0f0802c2103200034491140114001c040e03215403039440d4070358114520114008840804000c0307054004544c8000c0c1001215480c1480780d42400211424802c0101e0805107500a0840c0c8400365108560030241c140d40152034040707000d4800100d04140009100101e00d034010940c0c02d80001040d00300308050b40302420341c04000d91179100120b2202001d00030000210301c81e0b0780d000410b010350709041c0c1c5003091202c014100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 63509211 1250 63507961 63507973
    0x11206090618061e05240d0504050c03060106020d0f020f0a06020403030207120b01090b03210c210f0a090308160b0601170105040b04020c0616090501020d0219060b280503 75
    0x9550a0704088064176020396103591468401c00100d4151135580150100b11400001c18038801111034000c0d5000b80e02c13600454a900d01c0700420181c80d0070b000d009800040c6d21485100ca84103200e1802c4521035400ca0040c1c4500a05255009003003010707109080e5030f502d4000804104056040001c500101510404210b01e0107455445000b900c0043c8144001c084d106d1000205541e000d004580e002c480110086c60040d085c0410080317180c11840440c0c0c080e015801407004603000002c3c0d00000f044680c0c10f41841c2c00d4809518451503089001d4a0040080c030800200c00034041c60024040e5001c1e83c0900003491070380b4981616485c500030300543c100141d00b801e5110003180604070320f040d07481c12113010640001c280d02040c001d0050014010641c4206014001105045000c0305c0e200b014030f83e54045103c1d1103100590f81d0310003212200380164001401c41c10301516070303009441d00364030404003c00c1800c03020300010030140100c40c9100d4620b01da8070f075128400380c000c6c0381c004c0108410380103415 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 63510461 1250 63509211 63509249
    0x4050f0d0f0c0303020f09040510080712020121180c09050c07050d080703110d14060102060c040e0c0913050610030c050f0706020904050412170f040201120609061806 73
    0x100e4814902c014241600814800110421003096440248002d0020041440d104c0b2035044800014070500c0c0040c0202c150105030400a99441100650103860720040c02c021390307041c0c280c01c0c0710340c801c2201c060390b5030004008001d98010100017180e00650084248030f007004108412a840a458446003400810019000410114002c8070040070b40c2003903001940d500f00c1c19005083d81100610400c0c0c400114400c000b00581d21045c1c18040040310303c0301d21b940700001641e4408054941c0741c52071806000c100484150b14001d60340c0044080c4500b800c204501c4003089034140c044051202d0940c03120100991790800042e91048810b0501d4103105600021a010b0070034443c51070400180c21002035000300f8450b09804030b40d1000d901030301c100800c1c500b9040030f0b85002c00300400d00001030001d400c00c11000c4040400d003800758801c1d5030480200d880301c1c1c0c01583c1c0d2031200090718180540b03e000c00901122207100301c4006002c0f00c40040f440b166108016411241e4030740040c01c000d000308155038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 63511711 1250 63510461 63510467
    0x702010e19060903140415030506091b0a03140403080a1b051806040b07050a120302030408040b1b01060e070e040e030d0b03100903030c0305060f0f040b060d0504050f0d0f 75
    0x4004507402040015990000742800c0b5144602c0c01d1000e2180e00002070001488510407da000c0e880759141d8040003107480b60010840072282c2038681100244178141044100444200100a014510b080008140c4440b04080002450803502500490321200c2080b081b0316950261181003480350034001400313090118050031b84c0c0900c54200f82d41710b0f26031035141d40799241d48040310054004550465181c1c601844d105139213071040305e000ca8a00940f8012412541e00038026680201c1d400001c16085c103041c013801c8445a080030000040d092090b0301141480c620030f00ca03280140c124048103401d14544403c024010800e00070020f8000c610700700b00e000c110350340403060b1040700001c0c0501141805d248000039107000e000c41040c541d11480c200c0c84074201905070740090b400d035042c2c0d00c06100796039a0204100d070a00f84450401d8118005500002842c6001d621501000800070605030601010320360030310440c1c00458080702c00d030748030140350310f200c400c1005014100b5003980307404400050207400003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 63512961 1250 63511711 63511753
    0xe1806090a03050c07030803010803190503070e0105070606091b03111602040b03210c100207050d0c1b0b04090e07060c080d061502010c09050603150f030106120b0702010e 75
    0x40d0803c4800308004000d8442803060314003c54000b601c0c80c0e2256112070010b91250700c42403440d4414140381c07440c2d00c109801082920704c502940d807280d0740444141401502d03d03074418030007150b081c3c2d9245030100d40c3c858907215078850440310340d19165100690b904c0260440f40e5030030500041150070320501c1d81c11055185200f0a0075416500454080c2c0044c021a24044100f003915184036060510100c09a608102038501c49446400f241d600d15405407254080b44600d240251803a040761840d0340071540a840100440c5100b10340b074902581c00d464481c0b0500c40c164200c2404890300150400c16001c0034010607900060241c050000c0a00c2c040000d030214400100c001d04100300030840156040450380913070010311085101c84200808844028001c000c0c01040d50080307603da00011840381040800e03a8440d406851402007610069007c110580b003080c0c0003198150b4840c0340104900205007002c1b40040e2080c02c41e000c0d907060841c4040c0c2580d8240b81311182c643e00042201d51080340d81440c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 63514211 1250 63512961 63512963
    0xb0103061224050903031e0705030a0c0c020307060302040503100b1c0510050703050603150106021e1212100b0f1c0f050403020c100305010f2d0e1806090a 68
    0x1068070610200a0a841c2c0781040b1150390304841d1400c03040241c1500c01000940c403409000c00000c0b14003000c443c0012a0b108141d450034001101807001842400844d40401803280d21800c0c040b80b03444c011341c0001d14002240d0005000280c011504010070b0a040151507401351030303150140721103440100031030f00000d2103440840007501d00108650900109001091252510040c140402c0c0307855040034016000503101d89010b443380717008d50044105692045410f99040b50f000d000ca04510300b211700c00c0e108072000707141624050f808182d012a849040101100300b600c00c14100d03035181000c9250381e903a240364025800d2900800c044070b00208207000f00da00c3c4a11040b140c40f4200744403501c0d03000030252150b03591492458a8180010b054002070007102c0c00d00215082d010003445060211f080d1a020302c203034001280006005d01ca68211881001c0d621002440300d0781c290034200c000c08103550003d0f41300c003034100c08040c2449103c82c01000100c1c0340d000b0010081142c0c0c100b280000344c2d03600d10940 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 63515461 1250 63514211 63514223
    0xb07020f010507150f0501030c06050a0207090b0f040e071e14010c060e01020c06090c1e090402040e19060c0504031e1b0b09090708010b030a050408090402040602010f0b01030612 78
    0x14041c0070800c4a0100da131030401d00070002c018900400000d40001c03e0280010340b00754080d20b00004040e84590f0480399055100c5e405401c032286020203240c05043d1304140c03a82e0011007048c4100c0303140c9841c03060b00c903480c0c4010000c1007020701c0c041c51900400d0020002c58410700d8003400500c10240300c200c030001c0c0d400702846c10620700040c6040c480002c01c110f00341014a0350000400c2c000000d030004450740110754110548441c2c041c0b00003008076100e0000a0381045811085044000d4036003c0a920781c0300780098030101c0e100e2005c0803c60305004841d00b80521410260180354203200061140340c12091160500313074940760941e200c211100701441056070032162041000010020012032202c2c0c2114012191150783d078449240d00d113a0f030007000016008507024800201140d1040c0b00325412910454005032564032850745031b001a02c0300400c1a60050820800c941c01600c86100800007051554000140c040410300544142c07002c46030761504240c02d2503014086503009100381e002140d4041c0e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 63516711 1250 63515461 63515467
    0x21615080f130f030c0201031401120303020d14040f0c0b030106090b0a09031205180607030e09090f0d0f02010c031a0111010902061305091b07061d0703060e01060b07020f0105 77
    0x54010001c82c81106402000ba01e07003071000780105500314500e9284c44d4400d89080c0110110800745100f8101d0174425216851030300584040442c0c020360086c50f440d0039000002c100c7c4001d541080501da1400e6400b00d8a000c051180c074014003510b401580301600810202c28519407401c84003c254006902842c039006200180c0e05c40c90a001d03c084000440d0b20ad4011620903036a400c1c0584613812154042004105c602c0f0800304c00d1034088121040c0c10f5058940018100100c1d0a02a0b07214004040071190b10500703d480920040421046d40c184032940e0b50502c001f10054002400e41d400b40030703080181805c1850209100e0b003050711300002c0301001e20b0183d07007030013100c02c01e40d02510451a000e5004070300022a01c65107c10710180c1e034107660b01039410714810380354801d0f150002c0e00800903000600354188250070014005400091185117102607400c100002006071500300a603981c030031074040350347d007039404403034076081c000c80b8010000032214904040c2c0e540c010803044240c014403641000800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 63517961 1250 63516711 63516721
    0x2030a1d09040606060f0306030203070b0307090b04080a02130e06041205040f0803030402040c142a030a170108070b040b030a15140301050a02030402130c030e030a021615080f 77
    0x5036449002580091a2000c6410281000b00050020740122400500d140c03485011190103806410110383d80030700100207843c9004100d030083d070406040c4004000300043e0000310030b800c3d0070260024101c1c4801070540b000700d520410178241c510200400c02c00381000802c0011410200701141c0c0103400001007440d5000c210320444881c4075982200208801094010451700b10000285110b0345c0b080c1c500704003103250120155061032030500000404101003001689154102c200d09400940088a000482003601c103441d05603000704810754002010301001d03d900040e805481401030002001600341d031810018003000e07a2155000b002c1d4498800004581500101c0e8000081c1c41c41a102c807640d000e0700c1e04200c0306903407494a9054403942c203040c04504010424402c076401160300a11075103a1702d80c29000800a071014031100390905a40310003001014030180014551f04c2d186501901140c10b08905682c589050742c2c01094800620f2014155019005007060743c21107840742d01d4030215569 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 63519211 1250 63517961 63517997
    0x80a11120417040602010b03070801151203020106051c02040615020d030e0f0708030d061d01141201020a050408190b0f090c0a0f061205240105070c03080403030f0f02030a 75
    0x42c1c0030421440d030300c00140000e40c1c907810341c01600c948404405075170307a0790f41d5652180e003a5840704584040e9030b20019020810b4161001021190900c80d00000c5140380ea01e50010b10080c64035040e05941391008100b510842c030b401c0c030409000d000c848010030419135030403100079034403110580d41d1000d01d03503200300c0d40410321000c01c00340540308125030407107032400d072031325805601c0c0e40004101204081c140000860849184032080340e40b0390301e02c11480c809070f20f0b18021803000d4241015645c1c2140c1c00c1c8040c201072141c00e00045c041404140c81d500d5440d8a07045000b80b512809004500000182602d42000114800905508a003281d41d1074412034031051050b0381013840f4041c56550020f4602c00008483c441e07001200700310396458036043c12003904a49120140d41c01281d42e0100b58820104e00030031a8a2555420a101018505141001d1003692b40901048041e0000c3e5004c55000c90704108055100580b8210750249281c0600c2c0041d24400c00b942d40d002d01b074800024422015030800b890b0074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 63520461 1250 63519211 63519233
    0x11203120e010b101e0c03050d0c05091305010305100b131b111c03020c03040503160f0f0b0d051806040c05030f0a020a090209010509130c080a111204 66
    0x90829810412907201440050080c80380740c80c814043c407015200301100302c0c05150326140c89001103400446000e0321300400c41d284c1200700400c80a020050009403003c04e100e21504034040000d440b1143e40342c00400400183e500c4040508001a04200050000400200703042801d40007414010a4070030482001170400d40700200186116482d041189440d0884106c0b80c60b04820305469409280a600c2c0390641c45600013180704d00b484c09003010b06030074140b0a41c01002d9008020098030704080e1038600080c10004074188501c0c0303140703a8000a0098441c1c0c607100d98000d0401342d802c191280d282c4010521980140d40e2000354032039039840041c90030b503041104085600a580c0540380189003510300a0003079811801500d0282c4208614459541c1c80054080303070741c9030010110380e02e141c0b40c405100043c0d4004c031000350400c02d040c440710b001d07500c4001c140680c0110722100401e0081c4011001081c405000b03250030200ca0030b1401c0310101e042203c0403076050848441d20501d2540c1c1c1c42c00cac1128002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 63521711 1250 63520461 63520487
    0x12304090c0507140109200f0d020a09090c0f060207290403080403060203040b011415130509070207030b070516020904020102070b0309100e0604050312070c0b150f03070e011203 78
    0x460340e1503111340b1060040d40401420f920800300407903101041c40301001182d1001b41a10303003002c0d521415046502e08007101c0e17101c40340300038120b00c40a5128a80101590f8070908101c80228015605000814110910b240038001034070003451407a01c0c080c04402007100c5015107a000421408000285108500c21180075541010055680340d07941d00c2c001b002548120b90580f82c4090500000c80c04400c2d002101a0000000f000d02c103078864bc818600301d00d58007101520301400290540011701b134a52074120b034441d10181c3c000c2c050f80d44c69810104a141c0f0014104d404212003000740c620045d403440225851306030156111081a545d0b440181d1401000f9001407000c2d00e808810030001d9a00011400549100c01d0350a00443c0345803400d280e959941035400611642060119804500d0000100b503031006083c6010004118039845284c3e2000c41901c4130402d036803006030314000c5c40c10311a071480c89880c000d9000300300c007628200004010100600401e010820700101d1082454840c0386005500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 63522961 1250 63521711 63521723
    0x112061116050d090501020d0e0303090a060f0f0e010c080307030209190618050d06020309031204060c030506031c0806060c07080706031512062c010b012304090c0507 73
    0x9541c008180c44200c850001003128140f2030b109001260921030031480c4212103068000b4030b4592003061013900c5c002403031809160188024002c07143c0c1036403444d81070b0b00206100e40303c40c80031124041c0002c0152010541c1102030201e820521030003039a00c408801c0c001d941040038251261601c3d28210301911400704e011740c5c07151320b00d0084101c29a111b10b003807044405c1034035100e0090711002c01c00284070b20244151a40040710841d200045505c0d900115440165042070b03a190149408010314150020750701944ca00c1d07541c04840b10115050b104950f00040114002d014071001403640e01c0c0c44903050000407041150b800f010810f20340ba20429112108002c206480c00145c6841c1c090b41d5800e50380c0329a0300061304210454400380441d031080400c0e10007591a00404001c07688481019154000c050102042c806012082804018000c9485003046800110717a1200c1c4000047c545003109070b01c0500b50800c0b00302e040d0601e444404580c101e5035108004a15940000c000351110300030071101405d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 63524211 1250 63522961 63522967
    0xf0703090b090610090e0601140d0c0b03090d2d030605060406120c03050903070f02030c090c0702040609050c07060b030c030609031905070b0105130e01020d0221040b01120611 77
    0xd2201003801c1d0310598440141a03401e07079984261106551b000030700010103810600040c408041041c00503060690058600c5483da40103039503440c4160417079400350301106008014400c0c011000c0c01600300103aa00d00d419800e942081c0c1150310b1240aa45450751141c41030181c000d41d160003500312800419004010580700c0c0d036180b00291540301442031f00f20000c6d183c0358884115038000e00c1018021044207000398285101660303124a40e500c141c400340d82c14800c071038014001b40c2e80c00341001e224400c9204000d0711840140305100555925030000030110f401c1000f000203c000101c140c50300150042004205250a900072a080403034504030a03406010703e200f080594240040107004045443c810081440601c0008803540d00072900300400004061004210074501081401d440450442000580441803214607023281e105001e0b01940f2600484c0d4500400d1034400711041c0c011030480e441031186442c1c0c2d41e40514240502a0070a5070a4103000d040074801c070b9034490035240c5148004240c1d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 63525461 1250 63524211 63524221
    0x3080a0e09011212080705040504051503010b010c170d0906020c07060206070509010203040b0a1101090501150f030503030604020304080f030103030c0c09020a080c030601020f01050c041a0703080f0703090b 90
    0x42010340038103829005810000000038500203140082d80c250780c111800310340c0d0141d8414100d81d0a0700c007030108410800140004201c694951041c50b0080c400100e010300000044014103007900d40c0c8074903550502c079440b0300d0305000c5060b070500c0300509098100801d9540b403040000c00000c2c482e103100a04a04d1020844c40882100024240d00342c41064086501c10b5440c140225030900c5040340745401604244010480d00b005034000c0c09444005d03003400841206d01008403801c4400c400b0080d2016910707a0301c8142c001310100200c602501c600c8503200c0c20b290854899a0351380c80b014200e035000320b40c004006000e000b4840c05544c030f506c95041640f0f5403035949080c02050080300300010354100004000c00100c8940e2071007107031130103007007911000150f80d00c0406074500b82c0c000410190650095072010b000300c0d82d00780702c3c1c54421548400281d44440c106803070000c10400d0840300181d003107010420300d03000c0398000244603403200034100c848083da47d480c1e104501070440740304020128108101404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 63526711 1250 63525461 63525467
    0x40e0a050402030f1c03050402010c0b1003030e040b1503060402160f060606030b0108060d02010509030703080d0612170a0519020303150303190e04110a080103030207080c01080705070c03080a 84
    0x1402a80214111081180700c04021340e19950040d481651503680154216102c9020f070308200d6000d401418100104a0720f51110001070500322642c2041c41c1ca02c4505108040d00141c80341140303079003514104202d0352940045205441d5440561000c1100440015041e40da039804903518071403c07900360f000c2900c8502d090000081550005c484950400e100030440520900c510721900a050b55880c21903204c0c00244800e0180108041c1d04000d03080111140c0b41e101001128001c0d886130702c21541d9600303081c2500c000c40701f45401c02e070700142010780000082142420314071441d800301c1130182d640c1d00c800d4505640920411421218503102d941c07401079400e0f0040051071040003c1c3e121003d4115102040546920400c0b00550905170b6600204190a109541884044078060000101c40c000b80d07113030a946e500030084180015203548010707c00c05030b044c409a802031200c4402001c0356040e40d000a1301140b4014500300070880042410001c1c85040d440c14801160031030242aa1092000001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 63527961 1250 63526711 63526721
    0x21306050a02070b0711060d0e0118020405010f0b030c0a0504050a0608070e040e030f0f090607050606120607050906070218012606010e0703020705070801050903130914010515040e0a 80
    0x180000d030003080d0300040c0b4a801c040403101c0040e07004e40315841140c0c40d50200307d92900700c1c0e481d480303016903240307261100038600740306003415906050f06180b800112881080180c1d40140c11004040794201010056000c034507080d01d0b04000d61298031074031109030017821650350040e43c3c4913960081c1103000c0021402e030013001a6000c0d85e0700d41d0f075aa4413190710900b030100340e40c0151900326155104120100c01c5404420107084030300020842079180c01482c1c00050100d4105803000c1ea441e40205007440074601d80307800146610100007020f041503251604028089000b4502c80e1405078800013620801c658640c0d4070616a104100c42048242d42c440b22890312984061003291134000210301d50240d1007400051036130403a445800c90400d982d58410045010350080e1204841a11414802040e4050203001e4244900c0c0403100640e00c1d0101840382603035480650b88100d00c0f1901d03000758494030802375600c40341524400c1d00d07080c140000301e00105409214039407100540420260501401007607503041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 63529211 1250 63527961 63527977
    0xd0309060e060402010e12011e050f090610050103180204050f01080115050f0f0a030c03140c0406150818100902030d0f080f090102070c030b0f070908031204050102130605 75
    0x20422003000001441d642e500c0b402e840107808a40060082c20b81c91800c002501c1d41822000d00220301400500b4000c102800c101c80303038100c1584c80b802048510320303404c0d032000d0384080514000c080c50308002c50034280c02c03d82c03802403504041d240c0300521a1904001854811a42d001d0f004000624041d85001a845000e018080195007060241c406040001803282c05440b80202080e07015000c4c00100b1050080b03003004103820442441001006c58501c5556000450050b2128420390702c1c020103d03803c052001000c584030700e00d00541484019400000629a02c05a0038849695240c496a009001c00d0400b03000d4080c0c85000214064210a608000c0005200750100d44c0c10800f201000e4918003801721408002502e1140004e660480c2440b207984c12424003000103181c00c0703958560700120752040c0c01c2600d440c4c6081051003501038400c0c0802c1e0b4005c06034540310038109d0800c41526128441d94202c080709204400204052000a5046030710000c0e0440d0445011541c400000c4c2043c1c0045003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 63530461 1250 63529211 63529223
    0x1e0804030801050603012d17100b04150302010e0d0503030703090311060106020d050a0302070507030605180a02090a0209030106050306100e0907080307020d0503160b01080c0604080c1c050d0309 85
    0x340c40c1056420381e8141c40390b0344074071111300c7e540c8030b2044500e1032100007a01c16003241c950000795015111741e8050004111002504e15203c00700115820b9408020000340210715013070340300d00ca5107030303040c12103064950910b0041090101034001440040301c81d240580b260100006001c082c03909a8048115a4400d031601c105007261b41d6185074441c1424402c081c00f42c0c01c05050818210721410040503080e00f02d040050a050b50ba80b5a90300d400300d15002280c40d0341d5980180010008524100303680003a152000b014030301225408180441c50240c00004a03039004110f03261690b03003c2d0003e00c09058064216041880d0000304284200c40c64401c648003040d105010a00800b07010500c2015584440000d624003e01070b42448040420944c003540d42e4001480b8050008514403088034406025546440d01035042503140c9091050102c1002e00c45c52080204000981e808104030703c007000101c1c0c1201000c04070400704202d06829090051103030044900e400c10190301544003408090140b8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 63531711 1250 63530461 63530477
    0xd14010f061404030318080706030501051309020a140112020304060b0405060616020904080f030901060305010c03090b0109020309070b0f190c0201020303270a060f05090c011d011e080403 82
    0x2200596080b00403184000001d04100f00600220b402025618400840224030301e03c81503846c0c085030f040c12290b4201500103510b4100401c01881c003000d0460202c4004402000100c4ca142c0c0003c0f459070062140703a6220141000700714071a8051019041003031000e607819592498645030250040c00100342d8984901c1c90b2102245860810783c058070410400b0061121290345680c003081080c02c0000d004039032034403040242080416070200914002c00c804800442c2260442ca012400e51b42c0c542c000c00304241c40d0040301008036168185440c11034540000c01070b96030321103260040c00c10503681c0150f03d080d1710018038504c40607100002401c0402060030519030b070003200302c001c40e540380351341c48080c0c010780c03040c00031641c0000382810005516620610380310f03001050004280c103102c2048402d0310603607501c0034505034006881c05000c1e8880c0101010380303064094100040c0c0b21900114a4010043d80341350b4000441e401010341030912a6045c02c1c6440311984920010032203402102d00300d0002d5500c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 63532961 1250 63531711 63531719
    0x1080d090305060411030a141b030303070e04021c020406020a06150b0306010e0f12030702090c1303032102030c04050f030c03030d0209031912020607020604030c020108060301020d14010f 82
    0x46441038192039000703010b4911a1600d4980082c00000310340d8440c0c4c917006e0580500005034000c2c1e1068105445500a00800c004103044601c8a9200c5e8100038000d030400c004004100d5400795444421400440d00141c890007070320b029291420343c184821040c6840001d01280b0f0702e40001c0c00040c83c5d03110310030900500040d49001c4060782c0c0d040c410004000c0050010030703030701d45c003424904090080113001004144c0c078000002c0e03445c1e0380c0291802402d03040015200305600b400c0302499840540009101c1c90320b044442040b2082d00184006420810502e00b2000312010302211009000d510f00003d54036030070300c0107583c90168000e00c034151040c0350000240060b410082064070b04014001c020350b0030407901c00a2800654000c0b20000e906018240040c0074000314165209c620a000b180c01c0381e0700e80c8504d04040d03e403c001030800c009640c060001c0000007603010004888840d8286080011521102e000c64064094001507942c1c007401c02103c250005070a100f540c0c103c5482e050181103c03035803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 63534211 1250 63532961 63532967
    0x30204050a320106120b0a091a0303070f020909030c060a0203060103141311030c03010203010815070813030f0e0d03020a0501060b0703170402180f04020907080c0d0b030319020601080d 81
    0x6102011084140b5a0041204030b014010680000005001c04140200c040000441d1502c0a8100c04a195aa101c01702c0000d10a89803042004106500943c500055921040c481e2030b24403800900c160401030020701001003c0c0141e03041e0307020308030885001c1d042101c1500081c0d003044505500081c03a104003089224013640c00c507030082d03256040c0303c48000c90f19110800285400580103805114082d407105032900c0900c0294028140c500142c660000b21711501c550110016010038100005c00c02402440d40740c102d2071400b5503030325007040c007040f2158500c29103d1003001d160b03542d80040020400828942c0109039004003d200308000c100c195203504810155014500002e40000c41c002c2142000c031000745403031900701e40010a00189581c0d0750a44016038a0125410603984c0704041c288411410626030164214449003000d440c01e00d08031100e000340d40107a0032400e05041d280c00c00500c0940f001e0044803290182d1442001540c112860040c3d0354200030711890355288984010909200c0c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 63535461 1250 63534211 63534281
    0x60904030f0c06020906040e0604060e06010f050703090e0403120501080303090a020111013903060b030a02070c050a08011e02092404050603010e0103030206152404030204050a 77
    0x3600d80c540d003012404801040360307800c2c40d59000701e0750654200200b03601940c592000e08000c2c891b440001da071520b8040300384025078450303a1107868124101818855107030b0300710714a9003084100d4a001900c4690310304088608251707075445121038081c03c209001c145030380855074590072107504106200c542da9507410380740d0301c0c4011030b04858142c00c02c40c5900c00540c424400c4101e940c0e0290000328208200c4240c5c281d2141c080c8205d81d40201d200c2c07442c005440300100400f0404c9409080401a4a290128085039440001e1400310074980c0010300c0c1c010040840c105201419002d800b2120b840d403901c4c4000c0c0200a150180c420421140b0b4440555540c5030080368500d10b0094006420440c20408111540c00d0720f6480c0c08011030144400b00750781d1210710181d0f002303221801d0242c21951540c2406810b06001400f900f035130600d403170303c2520300b034440301100121013000400c0155880200804500540525040254400c0c03d200620400c05070030341102c50a100011aa4649039a800d502410003407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 63536711 1250 63535461 63535463
    0x7050f0c0102070510140d0501170c010905061c09030509190b0702120304090c0e09090307030c020907020a0f06050a0506011e05180d030306031e080f0f0c07060201060608060904 78
    0x1038000d0f0024041820484600c0820703244900f082d17010310040810a40e481e4022203a4a503200750b035403004106042c00b074a240c080300e40503000544410b0309141c5c0000e00004507402032502500000440e19581c14004400d0044070380c0c22103041100141c5490000d1095000303000d501d10400c400c040d80c1c0301c5a40944103500031240074808003850400301c0d80c2401025034500a0741c2550340000e01c00080c500c8500c0c0140781d240f50103035503000030302c075040020002e039490045d042409950051090a0010ba08145000c1009030100c90b00a4940e5540b0400c9103030681c10b000003821003002c0110841008943d402807030041e511040140200d030364440044a03060050000e6040300c0c0346149010102d58020402031402c070268100741c01d02c00c8400030109681e00744032001140081c0c2d80e403c0800521002c544101801c89040071800300b60b40f116160200b03a07003e044040da118040000e5156460002e003000c40f607240e002e001c00c2e50729843e41c17400003900804030782c80780d48007003141240014003030b01e00031200302c0c422 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 63537961 1250 63536711 63536713
    0x9030e090a1a0d0c0e040f0309090509100b0a0503010c111005070c110103110f030a060504051506160f0503071703060d030e0d14100b0607081903021201030807050f0c0102 75
    0x300b90b00708020b00c03402c9442c000e440c02022000c01041004507003002500c101c0c01628205c0121000f45001003019076154440d112841c901000e0104800d40403941b400342c2c49813824042640012040004e64501a507449503a156103062107203c0250b41240c0100117024025003518804201850000240e440840b103c00001d0301c010410030000f500102d103c8a240703c1032400013060302c45420b482d441076101c048034107012030f404410058804102e020700780240c4000e07a01400141400c0f1100032480310f041901d140300708000309100c40465044404041000d4001200c5000d404041c03d00d00d07280d03030100000b910b2060704113200124409003401100d01410024203600d02e014015101260300054400740705510a900300581808200809041c2c80e1000c816005132480300b88410b4a00100d411034620305004043c14011107000c58071140545240403015112103099542101d8110024071455402244ca49600ea001001b031001c0300000d450110302c50012140c0f4041c0c0005480c0d60761310b50644507401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 63539211 1250 63537961 63538001
    0x60c060403081306020403060b1c050303010b0c01021309020c060a0c080c03040302010b0904030f1d060a0f110d020a020907182601050103050a021f020d140d09030e090a 74
    0x80c800c100d1103512400d0f00e560080c00b103c9070b95078402070b03a105a005664440c0c440c1740012007440c0800c0700710784e0448000204600b85019542c0d164680c04140729102c0e00403008149400c11710800e4044900c0150a180c400440e56140c041800007500061079940c01c2e8410440083e2300894284140c1020356111b0702d4405259130b07280044895036000a00803401c5540312210b03041d454882e8044180100d110751a075122400b0540c00040c000c0194510703094030402c0203001100303240c0716802200e105550b0341c500783c0941601400103a45060300d1100100551150090490443e80c0c00320704601d442e80300720b44c400400d4542030000c56034580c0b40070a07c080125462390400c8003d24800032080c00c03039200b0b4107080014041c080110700f100e200341d20076a0260000c1e6a5941103180660144079401e450307840b00440501051030095440d643d01510600f84005100c4542030f540810b0103803081805010400c2c0000443c44c0360050841400c00c04485c02403400c2004210400154010550009c18194480c01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 63540461 1250 63539211 63539213
    0x30c0a06020711031b03010b01090b070b060a0e010b03041b0501120c120204080f01110a08010303030e100606030c0207151b020a0807060c17030106140913060f0303020c060c0604 78
    0xa60188030203d0b001801904107500e1500c0c2884000010214a040c81081c030070060180350070f403411410b03070604000d440c0c003041c001241c12000b92041550050000780141e80d0700008604c803107100e50003150440701071000016800d0f032032100039445244030380240384428070b5410710004203421600940740800c440e1203e0700745401c06a48031240f081011320300b8410501d4030000c01000c0740d1041d0465503003504580d4001442c40b00902850111500581d18a844c05034000c500030104501800014209500c030b07628000a048100016a00c20072140e50070804155500e1002d0300500a242291001d4000c0a0001488242507140f032948042241c44401000000519902a200303041508031b030b112040300c3c000700705603408000c1240036050b80d07150b40c00030f44214101101006880c40300001d400200300014444503600443c2005c90004006080d502c074640c1400240c3e12405d0000c19940640c40d1042c0020800050b000742070803030b03019400b551814401d130410312042d0311036014400c3d103907400382c40468 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 63541711 1250 63540461 63540473
    0xb041b0305041a0106020d03051302010e090405010209060f090405090f07170f0f010e120408100f0e0f0d0f030608030a0809030d0606030f0b0f010207150201020405030601080f0f030c0a 81
    0x694801d118800d2444100c0100302640480e03c401c0e00310b030005038010100340c90702c140c0510036036400681c840c9159070134443ca940000c01500c00400058001c0c2121404101004000d4041d0b0b8541080148016184d41da0208401c41a41140c105248500d040c400801d2120074042f030745510644005024010050030134030390310702401d075040402a26100b8805006980401400044001ca8000c0000704aa000107040700b454962043c850040080003048101704100c80040d03652000c00036648042619802c810075100240000d00b016400741c01f5420183c07000c440041040e01c1d032456517454007000700e40c444804408596883c001c03203003154000c226840003540a4921a0b5104281000712032400c07244400d4001595840e500c5000429120140251803213034500941c4c3c0c0040c02070b40e102ea942d000680000790344500d12f02c148151b006d02103032014070280c401e404440c05000f000d0104d5155594500c2010303610180e440f0130070b085004110b000e60540740003104503a89908084001d01c1a030700e440c1c03544 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 63542961 1250 63541711 63541721
    0x516030c120209030a080c06010e0108030f0409110d09060b0a060309030c020405060303070507030302071811220f06020309090a0506180702161e1502070e0c0403050307080d0b041b03 80
    0x542d1301d8810b514844001402c020010414000b091010300220b514103a580802180c0c10b0300020340e5a00103020841c1d00d50310070020b440c212000f090303003c00d60100700c10543c101c5218080402c0c0145041070029070601c41c468000c9101802e080d02e4111103030350b80f42412421503501000060000358651003007009858641c2003542c1000004040d2071901e0615600d0924004044d441100980c02c02e0300c0810a09084202031041c401c40450305106c810340030303640e040b040d1241a01b50001c01854840300d940c40c0e4600c50076940600034043d0341c0b40419407500300181d52604407514440c0315140c4040040c0c005810f5018241c01400c2c060402a0344214481c8609500c0e080204240c046100b4a0403407141c2031804c030107050050107200100000402080480d0100d07204c2902321007200c84411403c0303503203168009982070841c0c01518180302c494a840031a15028403440e4000b03082403001180702c00500c0310800003031010021244c0e04000b84808003003404281e031200056842e0780704070a12031400150003a048 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 63544211 1250 63542961 63542977
    0x15060a090f0e0303040c150203120c1e0d0204140604080c0607061b030e06070207150f2606011101050c09010c2306191a010302070f0507090516030c1202 67
    0x70100d0071980e426191895500f04880588413800c03001000c2114001884442d802e144075880134520b410f020180035030380c0903000b602180144500217040380705048100d1741112807192074925641d03560440d0190f54065005070160038903001c00c10366000090300e0b0860880d000c5841d240b016000060b440d00030000720750006c03181a0340254403400e20445005001034a0031044c000c540340010b11986070030314280b60800c01800c0c1000e41d40160024060f00000e519212048601d5107003c04c9107016612040720b40342c00092005d41c2c07208201080c900040252050544220400c3e07803580e424280c01a100b6082c0c4400f581d401810120411000085510800c100c48820b800b0701c0c21480300c840300c40740a0041c03041d94000550150000c0c41030059404148076000705201841e9070510002101c0080300c40d4594115005a062580c00a4900101710705c400310800e21981040544801e590384000030400f8000840304080405540e980e001000b50092203020b5903030241d45d071089102c0040380a100c00079070200c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 63545461 1250 63544211 63544241
    0x50a0909061809020d0c030818030609060f090c030102040e011703070305070215090613030209060406050102060c07140f0106030302070f03030203030403030e100f0905011a220b0405070c020315060a09 88
    0xc5c0404911411031010080d0b2143c9146581d51500400c100c100142404417640319411a506100908500103441030f004588884d08001e280c68184e866480c000390304039a5900341d400482d0024030508000b072200e040700d148005000120004072005926803240720001400300c1c40a005082c0542814402d01c40f403014604400391610030301100061040d00320482034000a00c0e000c0c0c0c01e1003142403d0f00000d40107103082e40d0920003e410440040e484100042039040c1111000c0b40707141c14070061049548480e4024400e44000104000300903019107a240000d070054401c3c002c0002d0440c030281544001c681e01039010f1404e649959904034064a00150302c0065072250300304405c00c40b183e6101d903440c00a010301c070005400300b02d46002403e41d00c0c1c422610038248500f980c1c0360302644809070a65106c1400700c1c4c0c04120007141707884040c020002100c0c03a580042c40c0004000c5003903007241d18411294000c9003240c4221007544420310142c4421941c05410a913440000c01c12a4001d80041881c5402e9035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 63546711 1250 63545461 63545479
    0x71a040608130611030a0c140f0f0910020703030806010c0803010608090f1603140105040201170702030d05010e011d0c09060714060a02030105090a06080a230d050a090906180902 78
    0x1031542c030151204c1d500c40402c04580042841030303a461a1140d209002c0c228109960811000c2054480c24060440e0104280394001546082407408404490f80070000030004002040c079034000075038811503030004901080201c80840c2c025070142c041c25a8070755110702d800d45540e00f0410121690407000d007001d405841022000c200c042c0044c0a280d000c0100c4982c40a006441c500300544010f05441c40c13032a081c1d02d043d0a110150340d000305280c9a01c05090604180d0780c607403003012880c41c440d6441e03508105103820f002003030044001002c2c070304030780102407072400e000d0321562a01d0100f4002e881c10480380b1000c02c1011440c1c1090009058614001d4010302c80100036a040b0900707160007100c203580041c1d8000014406803800b030803019040048940104001d078148000c01c3d0f52286910809007000d28007900e6040c400c140c22144071003c0b80b018081c0c6600c2d80c03d603000a00160095504038020488556000c99441c19a20911048880854a8260003184803407090028900c0b41800c0e03800040300e07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 63547961 1250 63546711 63546713
    0x1415010507050a0819110604030309021906090302090c03091506011214071413050103020f0903010f05040302060112020a1a16030f09090b060d0e030405030f0f071a04060813 76
    0x188040c50b8401d020365406170f600c60503060324210344078210b00c1001c103000311000883c2a5200008990364019411305000402c540030340006024080c1c551640b2045c1a54000c02041d400e40c860303400c1d005c5a00c20381d00c05d102074840351f038141c1c4107000446500340c1c15400040740c5c0000788196403070690000b0060401742c9070f40b4031102450b0140c030b20307408502c1c4e440c0c0081d46c24031044a03409059901c0140a900c0c0031818070350158181044002540701c0c5604058012903440034110310b650454005d144010000c00030b91040c8000390019080c1100c00360b0260203030320300001d0f086441050600c15103a00804440d8000c0c2001a01e810010130b1030854422034000740302c150614200310b581700f10b000380240c640301c084074510040201811035981008401c1420501034030050b403640025240e20402e2800c02144010030302e00000c2c0b45006640c041c81d030521482d000d6880000380407400c80000c1f4400720a403202c65480f48400701c4c07013010008601090050030002004107910903c68540c0105405081010304522 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 63549211 1250 63547961 63547963
    0xa0b071e140703110909010903091814090604060b030610090e0a0c0303050304050f0304050d02120a0c0f170303010b09011206031a071d010504050d08041a07031101141501050705 78
    0x150b0004c4032601003800700c000e194607081d00c00c20b0380042d4440083c8000e10340756400030261540303803252800340c0c68252201c8858014a410600e60000359000b40419441e001865640d81c1c60180c070203035180c1c1e151800945c043d003004600148107481d071000c02c01546240a004000401c581c01d03014034940150300000340090400032211000310300036900c0c69100e04080c00d00c10708080a0007200402a40200010882c5449852085141c2c5804070f502800c2e0818401c5070a007001d500b200010b02c0784503481c0c070102c1e0b6012460200b034140d0700c44201a403a40c01010080c6903880c030003801811501001800b510b11558490030a40705014203544020608595a9035101184c82c8040a8101c01d050f59104114035a5400802e400118030f52240a544103040000044c0080c0b18038025030307024401035042d000c00e0210b80001c40d801480842041c0e030901661141104003600701444c100c1c0000d2000454042058050084600c3c07610701002600303c40c0c40d05600300201c0026400700e603050120601c410300100340 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 63550461 1250 63549211 63549223
    0x3010608060402090a0905060403080c0d0e010f0c0905030307020f150703050a1101090c150207081b030d090b120703090602120109060501090e0c1303080403060204050a0b071e14 78
    0x3820002040c040c2028410000c200d4001400b190099160000c440041040002c1e00c03900207402d070810f5455922060088400d900c40d09210303040b0306040181882c9a840154094015681080020803ca0b000140100e0310040c0910070241c0c194424400c00016280240c1c0e40310521400410101910300c9180300483c99411241c42500072950209544007281e4200303401d5400c4603d54402005005959698060000b03518002e00c51500b50750f4000c4154903000b00030020140030300204a40d000780f00c4550030000d14a0520103940070f401515510b02603140126544c0042d250b1001da9982000561070013480c2c0a44018200d60416449150000100d07c1a10007010300f028118241c0000c0e60400110b80280c0359164403403410418440801c01001206560458010b0300c409240c6a9910010316804910180c0350800b170403041000400008111841c3e00920882304182d03420ba00c0345950b00102170b0140103014003d04503420b020700b4924080c0b804061101d09500c603000c0c0c0040039900012140c5000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 63551711 1250 63550461 63550469
    0x109030203120301180912030e1e03070218070206150402040b12040204060b030c0702040203040c1a030405010606030204120201081e0a09060b0f01020d08070e22180305030106050d020405030106 85
    0x80c2c0020041c090034244007910000b44c200c034a07041c425142d00fa9039032003c10041d25440020150703070b900141a9190309010b800030ba05041d002c9801100e1000d200d0580381ea00001c012403003a502003040c0e4014070038240c0454468503280d006002d0b19620b010503901c2510700c52034107940c880e6081001003018032454001d42031018680280302c00307a141c144140802c80d00c2641011800000500405c031501d451002201c2c4000d030b041c3e03409070301d0ba10303203140014040405402890038204a0b100c0000070142a5014502c40c501520091101c0c0fa99000150100c0c070039406224010b5010b8180980554002d00110340c02c400002c0d40f09145003024040c411600780b041d0340300c1c1170031900c462842e42804290f001c2c420034002d0480382e094040005a0010b55100003140822060210500000e0103107401400e841c2e2a0001c040c3c045505044c00c0f200008242c1d6040f04107a0b051841c0400e0805800780c03043c540c2104039415101c542c616400c1c4803040e581a04945c40400000d60200030118894031700f030040d82c0c014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 63552961 1250 63551711 63551743
    0xa03121214180705060a110a0209040f0309060804030c060207110904050d030e0102040b0d0c0c0602031f0b120f090f0a08040f0b03040b04021012020c0d080105010201140a0b0109030203 81
    0x80d0030560b4075402240410900404181e00c504030600076591640c04070f840084482c20440d039205620b070306e03503410f0000108019502a41041c200400d000641c00410a550300c0780c0c4c0d40c032000640302e00080e1441d0105407070117800545000188000214685c1c0106501c0340100d111001514030000000c1c40800c0450b0101c604e904620044e10386690940034080960198000075420541890301c01e0300c040c040e010403007665540b00c451a4098a0064101d4024150020001d43d5a841c000c030b130758071140a4000d1014000d504842002803220611020b45119030807180240e51207444151a90f11000c07006003c8514a01408903001d040241c1017000c041c4503845039000d0768442d8600700c211504d041e03036a400440b00f441c0170002c20000070b040c01e440320745c45503040f501001c141e0402d00d030031502c003401007009032a410b10005d5003290b103e400207100e00024085940741d10050380c0b508012426221440c0e0703a580d040c5c08540102d000e030309041d00019012041894002d503400d03640d40010b854240590429034032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 63554211 1250 63552961 63553001
    0x2070f03020f0105091b040f020705030a0c0b0109110a200706030504170c030d0e01020d0e0307061b020d030b0d061d06060103141609051905041a0a031212 68
    0x8040028010503034086600000b820100317006c40e4820548122910f19107100c0e59032100d6030b06500c030040d410b542c003498004040340d440307050512000c0c01c00d1040450664003c0044400060548020b01840034192000c029143c00c0004120083e6038100240c20503404100c40032416908551003000741310000e2089aa02103624245400c207411000729040485980038420420105441e00c000122840d100603030000003a191010500c6a009010700b00e200c40c2c01d0350030300c40540e0f6034440000280500b107014000422a5036104070700c907100400d00b4030101c00507030008500849058000d501042c0c0840c005070903845404c0031036a80108441c1c81c01444c6850b070000d00452400a4001c00c1032a070b00804c20f00301041000b41180400c0345e40e003001000c4001410743c000805125a1140a11600500001c0c002c402c201e00c0d4070113030102a0b80781e80a094004d5140c0301584040d48240320b6103500a85005d4000550729040d0b0316000710b40003040300001c0501941c03a04080340e180e1188102d0680e50800719000c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 63555461 1250 63554211 63554233
    0xc1507120506030a0804062109060e06310f05010504060c090b040e1b1606050105100c0c14010219060b0907021c050a02010b060712080603030403050a031202070f0302 73
    0x200300d40000d0320303041c0694001301d901d80c000303a01c0742c00300c4003540c02e18100f5103031105298080c211510301068203030280038201450602001f200c5d4005c0d1340c0405a03030054464594807902d8000b1030900410560510440362080120140340240b40c0421890186403e114081700342d4494a094640594048070515920484864139951083c40d01000d0017860042c00d1400e4034043da8156403140c054480031044180e0960081c0007015034040312005800c051020b9144521410702100900c804d208590107644008600240b1038442c05402c000c0c5030344110300c51030b064100f55a045030103a8030452203040d40300d100023030051024030032000d064681c45401c0105000c7e1000007440502074010389860113540c0004140428882c03800541f0b16080c1551902d6030300c980b800c200c02c90140c0f14a40e000340e004000000c0d480180182000d85900407003650b1555021034484c10203143d56031013948806071046d0402848138001034030800150445114070355015080082c10380342c02d1107a4428074000c801580c45800480307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 63556711 1250 63555461 63555497
    0x6040b0f070c030203030c03271f060605070b27010b011e050702090601120e0303090c010c031403150a080d020609030a0e0609040207081303061503021003020c1507 72
    0x503a1190307007858035070880c1c4003990b0045e589000103004224481c0c03002c40010024990003801654001b10400420081694200707640d80300e0824190000d6080c070007945840048600e0b000301380440d680c69890b246080aa074817030b40241c039005011031503000c140240c1200c2da06402800c811882d41800000150140854005801010002e10301c0724200c62052010019a402c0000c1c4c0300020340540701e41e041980d410004995058603500051540c1d0302d81426038240010000c05148034595080450b0000c03a1141d0041d40c2001020310010002000902540c40a4141c035001c0d5030405101000b07450300d0044917000440042040e040034525a01030805c4403442d5604000031500180300d20701440ca400c1070700354001c0c14581c482080f14094000045d052071a5100c0e07038110751845422100d16070329140301074603c07550164940320030342d115428600b400060400404448003203942c02042d02d440c0607000801500a90030464140340c2e14080c1c004508140c5d600900346510a850f0359803440420004041e1301 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 63557961 1250 63556711 63556741
    0x7020d05010b03010207081b06040c1224020702011106010308040315060503030a0305090606010815012a0308040506070207080601050f060d05091f0b1302090d0606030c23030705060c0102040806040b 87
    0xf8008c03039032007602488042005140e207501511480d00c18580508a00e00340200c2807020f00c0020f02e007148001481030303810006c40c0c6c06094001d1003662401070031140715081e02d550341002c0c00040d2400c1703420082000010048c4110b070000301010344010070503c0c1d807500068259002220075201181d2101e003000480c01051004c01c1d0b02120900780041d20f8182204d03410503100c3d640001714144648592000d498060b9003420801501c680c644600c0c2c02249454010000201a43c2c00c0f2180d2151001240c07020380041100b00c1903480e00e5005015907840c10b13080090b04240000c00c0340e0042c1c0c04001501e00c007101401054480c8100c0350080c10044404501d409402c120b92640740b2806291041980503942c502d20400c0c422100803002603180c1080b2400a0805400c01340e0060a95161101c00410007000144ca68119050440e01900c071020301c102e61501503a28010480d4160050703002400549402405040c5680c1c0d80800142855115595580350207400da0b0181c0d00c20401400f00404095a2446 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 63559211 1250 63557961 63558007
    0x6030506010c030f03020d1d03041d07080a0b010c05030705010b0f0109181d0d0309050c0f010f121d0c0a080c060a031a0604090207021801080307020d05010b0301020708 74
    0x880b00540c420348000f019000c89503035a10070550002007a0b0700450b100d420900340c1c450200031a0710380d0340354a40e9042e07aa601c035124140344618140e800041e901c50302c2d0f6030303a4440d150075215002c181d030740c20f003489005050824503981030180304982007000c00d40c10070291114038816000080d00c00000d60400450482e40c0e403074035042233a0882d0602101c0c2c01d03a800c503100004030300000301d03860314919490f80000d034000c0c0701d540702d501c56100200c81d481d506402010a41d409001134070120440318040c0308004142003885070114810140301c2803128814042000d400201100025107407180340e04259155040c40201301c856403001d03032062220718242c00340000074200708000f003c0d1218a800450600d00902c0700f02c00506a852481c6021020070100c8142844001480f0320354807901d07020350b81c000703400c400310590043d04e04002200c034405076682400c0c144c90700d40c001541040c1d055420841c0c041e111400c11a1195207071005116540c0b000d0010f401040c1c45074031555101d4082c0c1c41460611404404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 63560461 1250 63559211 63559217
    0xf03040605042d030e04060b071a06010801030b0103030c02032a1203030108071e0504061d0a0608060a0903090302040501140312090105030a11070b04080417060402130c021905070603050601 83
    0x100c0e50074a90003e40d502010242d25082808000d921800040c0050119920016500000140c5042004000800f107000002d8007c0303407000e15150b2800449800600340001424880308800500c0400d00519154014620041c101c48500c02102001070710f018441080440d044201c9281f80321926021040010780b4001100031425036240c03645841d9181d00d54030030303001e000c40801400c8015507c04240800030b0100500b041c060f0a9940340d800d450940d090b0001c54049a1040110344540c0f12805100200c6403107000030310b599203c0d8500c2400034081c102c400ca0a00c4030301d900c00401a03c40d40585402010f48210b61240010320307000341800d101c2c02d00756060807444c003080141040ea800c0019a60407040c07413080043d031032030410044e002d036110f10000548484881c2c1e041000300300710f100c01042035660b80040311030f58017406d40c1e130303103030f40701000c0d034000398050b40d180e6800741428180d6200c0d0340020700b544112598201ca030000e0f2105903c0f440c4080d2116000700344103006103500740c05001d801100a107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 63561711 1250 63560461 63560513
    0x1d0a23010201090c030b0c0c06150406061b06020f070c0306020a11070e0415020f0c010603060c0f02070308160c140405070905130509011b0201020403060606020c01051803030f0304060504 82
    0x79072134005a03a11400f004041030307420400b0a03207002c0c44400b640d08082030710046510f84e0070400c3e505260343d1a92480544140d0909802052180c4518686190610351aa90216184003941c8000c0030350400804014525820b00c4000b02042c018071001c40294012a00140d491151300c10040c0010300140c0b190046a2155808022181003200e60941c42504400404000c010b00e04c00d05000e0701c81c8503943c90f0001ca0214001500b00380643c000800c5a2140740100000c484202e002d0300e1242ca000034000c0542c0100d0710030000304400c00c000f81440b40391400c2a0140c0c078182d568605c1e65207502d810442007208144140f10040c14507108458002c0450300700030200c2c91030480010800c0f82d1040c4070304001d42d12000810443c3c0801d41142446441c550207014050b00f504000a0003900a41b00684082e070030101c0014902e400480d07282c140c80c1c01a91914a003030034420082c1142c490781064540c040c4020081c5404401d9440f0180d8002c1e4460400860307141010305000646610740307020705131414415 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 63562961 1250 63561711 63561713
    0x120a020c070b12010e040f030806131a0907090605040b070807060c050a090503030316031a03060c0a080f0108030405150903060408071202070819030e03070e040b0c07121d0a2301020109 81
    0x240c030f0003560462341840c003006560346100c0407692403200f45001650341420300c204000304c000c0c2c0e00511b0543c03981c00c3c1c84100c095541c0500460384a2054464400401c2c03040205016250344a0700070481c9601868540b840d00340c40e980d07090101e170f142014280000c0c80100c2c40078500c40c1c3c0804913034010701e4120002e40c29810155601401e0002c1c60389000d040c5551920b02c2c2d41d01140781c4c044010a85001000e40b503a1789080c0840d059180c1c418007606000500c00340016501118a2482c41d06a4504800444c00c0500704002c0c02504d01d41c1740c074420ac0f0250140120901d80d60204003440c4a188150119601c3d011189407260195040c980088155003095405020007140084ea903241c078400c4c05152032443c513803030a040c0e80742ea080b103808503094090507002107a94a105910107006512520154031165141040740c4018001d4120080c00e452880b1280c050040c80b510120501c40e600c810740140300c03003440d000500813114552210405880c06500b041c280203496444640c111809e00003031140da262 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 63564211 1250 63562961 63562973
    0x50607240e07050f13050702060106021603110d1407060905040b0405040f030e041401140109080a030906080403140a1106060315060402070311100f0c0c020303120a020c070b12010e04 80
    0x7280921070140281c540000c5481d603c0f0303007a17105242500d25080000703040402c2d0094a40c0c000b405800054460080d040d070448041650030340c00c480d0040060344100543c0c10070031043d6a07004905075a40302d0002c620441c504c00601c082001044030b91108000980742c0810702041c0c0d00280e4096100d6860304040102040751002000c010a5151614007405115080064000d100b0b001e403141e1400380e04000818443e0101442c0c12040c2803d0300c1d800080d039a207440c01542d0f0b00b0b03040c50040015000d5281000400e01440d03450b9040f40c0711b424050050390048004060755000a807049001a85d003a070383c81d0428009200481c0c010301c0a40140c0f01111528444046004c00580500d0203243e0008501e400e141c070421f40440c0841081003070b00c1e055030103081c17200080c101c00030b9200007440c5000300501c1510f0140f0303d110300c2e250380580914200365641c1d04610034440000e19680f0102c0e0208403050400e1010b000c3d5001800414204c141c440040e141c68103c13000051b0002d10580000b0400e0001280c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 63565461 1250 63564211 63564223
    0x9030e1203040b0a090509010f0b070305030603030904052a04050a2705040b0417120601080601030902030304120c0f0f050d0507091104151e0315050607240e 69
    0x20940380144004800d03119249140709582c0181c202c80004a00c1c820304030b51041c4a5421208201d03150109a46c848039420300540191007040190079081106000007170081d4007840d031024004003624206a582d001003020360f1401c50302c006800c10303402004403011007050712211035132440428550030710307040c07e01081c070f025142e000c3c3d02c1c900700d00103008040680303047e141e012070000000005e0113582001d10300441000800e84040b41e42217804140e0324110038071081515401c41e0707000803941c0710f07460301c03c0191000f8602602c1141090b80b607400d02c201580301040200018280c8528208490003941082c0c074500c84c1c29040980482030040040004c45c0d1005076000c2500e404a0340e403144c0e5440d03454024504080760780080311550400ca14400c801800c1e00141c41120741c10a82001a10040141201c2c1d10011a100c03c411100e00e15800740124070031b46c000c0901030b09245900b140301c0d03203880c0007039003541214500b1140c4e0012020b1111481d14440b01c4820040659041032107261030782c001854580d8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 63566711 1250 63565461 63565487
    0x1030e0c01081b04090c02030715090201050d050405030c0615100201061412031210090605010219110d0b09030306040b0114030a051302060c0a0201030c110303010b0a0c20030706030903 81
    0xa07081d0f940312142c2140a10031a401008102c070200516000c2c0003001e5101d400090040c1c40b0f059241805680407105c501511410710303416550f00d45000a01c00106008080207001a907a511003030160280b050bc04100c014010075003c6203940302043c0d50410041d0358865a5141411a410008104a055404040300050050444d2501e0040d403d0180f200d255000b8545801c1044000506112004a80542110544c2c410328400d00415841c1e0006995689039074004034411101c560074880403032160104c450703400c04024a114005280c075110490340030b40503a00300c2c0060700b000003070200a2900340314030f4110701030a0070103c8543d00f40d54000f41e49808014080900541c0350400100350b140c01118202407103038024810341c1c0359180b68a400d50346200003401203004c28a40800080291301602410b0341d40c220500003549141e007403014092042d0020100f000920440704000400100000308810200c00302e42220209403000790201884e015003540303c030782850b260564030707400710798031001d50029a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 63567961 1250 63566711 63566731
    0x901020c03090d050102090d0c08010c0512040204151a0c070807030f0b04020d020a0803120a0b0f0f0f0d05030a0f0302070804060e0a0302061c05182d07030b0601030e0c0108 76
    0xf500321810914003a201350a411603101d00031500a00400444400c44001e0740c00703120003080300c08a80781054500780f05e202945d0020990b860002401894282c1003151034035100c07007030a0581d80c0d8070100f040c101c154400c5545403001c0b0106044038200420003a000c0107203980700003041c9041c0b841c2c403054940e21003504003034056071001c00040d0554941003e44404281c1c058908000c196079865115141d411180c1030482c030024000c00f28501e500903000340085071400910309807082c00c0709400c00501106207181160001c46168914009030790703101c014140325000c0d20165665613541c09005040c103400b10800310903d4410712030300b00454544010b0702c0a485003401c0c002410120700300000d0050390a54002035004030000380c2c4891031481003070300f202c1a6a041c403061055031903950340c0400340380343c0c1100ca0035503501171401d000402d9106142d004c50b842000102a092900505095040071000d41081d15030a2401081c0300742964107108000700d44290070007800343d410391140000d100120140c420004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 63569211 1250 63567961 63567979
    0x5092b08030c0705070314010b030a02030c0105130510030606020d140715020c01090302010606090b0910080c0d060f0f090513080c0f0a0605090c0109031106031003060c0905090901020c0309 83
    0xc1e140401d802c490315241c104e811140386596924180f000000d444004201650030b2480402103070800042d0f42070240ea008015140c0d00103898011034007074024440e8614007038400031000a0607100c591410002c0d0f00c490340c0c04981103050240103441c1c5246441030078104002c05c2c281c803c0500c0401c0c00d0b2454213030b00041e5214905016101100a40145094114a9468280b81e0420540c055000c48100e4030903490783d20000e075403020510001c0c00b45031501c0380c00607046004000e09911904c046607000140682071424030100d058203c080324071076000b041d40080843d209114008151a0319002460004024405450040c0d103440b104580b10340002d1010070042610b92000301c062140144403a111403c4940c081034505001c0050502600c22000f0350044d01e102400325481420300c0300036a031300815103100c01d12000c010300a140e40000c00101e800400180003000040041c0182c494a418560300c1c0801c0609000800c6440e920180c2080002d81c810460b05400341400700644030305040440d08084 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 63570461 1250 63569211 63569221
    0x90609050d0f0503030a05010512010905031204050115060507030801050f0303071202030d0e07090e03030c04031e080309030c0105010b040807050103090f02030607080109151d070212030705092b0803 87
    0x102c4907111450003416400040300304200c0f0b030200d40c030090499908607032395003002d1074040f507030b80c2240d6210704041c04581080000c1105200e076288000c0d00036105100008078800602c100010301c0e800d58105400050b030024124050552082206000d0071088500400503a04400003a643c4c3c4070f6604010880003c40c2148114a402882603664110700c1150502c00496a680303080c2e103402c014010712400e11b181c02c41600c448a000030550b84200c10407844075181505645488885030f40e089810802641040c050740d00007111040070f0345c01511640001c51311441400541d500b56641604018007005040c00204001000000e070710040303900a003400a2040d0450405281030290500044d40500c00c3d1030500c594645d20420450484240700400c00c44008007500311183c40384c0900c101ba6503020040079681c85040c402240c960000d1542c0120f403425000c1191090580d0030441d9200c0111b1008503802d8a94180503c00740c600042480c01032a40c4c1c0140d84241f0351440e80e400020340044d40200c0050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 63571711 1250 63570461 63570473
    0x709060f090807150206090102090904170f0708091e09010611011104030803011d06030a06180f0303060810050103080a0e03150901020306040f1a192103020706090609050d 75
    0x38042e208420595803001c0c0c9504180884030080140a0018401d0030300203810b4803011301c00ea80322450000e084071025140c9403034464a07071143e4619041c0300300d010406c0882a40c8044001c0020f03a105210054a5290400810030f0300c01030f880003000b810b8802282e2160070f5854103150780c190b0700d1500b4842c010504c80300c3c0c0940108200308814058860001c0e001c02400b2400c1d001e54100d407034200d411483c1e449041d2a03101c1d0306034145c0c0c2c220f8241d4000216035000480300e0300541481c51030750706070a150004580f80c031003907840700c0032090300400c3c0e40740018081000184a10385090311540c000703002a52660765051481d206c0c2500e0b480805c400b005039444107650501c5201a6889110307801401380c10980d0b41c0e80d000754008d9802511642c034045d0000750004d0280218221440c0791000011880080f000b4808030880300181c0c8022010100000304000010800d920050300300b426032010740114a2070064905a01c58003e2014421511010824694040c51303203800d941e006d640d078007850f048516201c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 63572961 1250 63571711 63571727
    0x100e0106080a05010e0d02030f04060e010c08030a050108010c0203090a03121b0305090307150c02040525050d0c080603120903011d06040507090b1806030f01020a020607030b0102060709060f 83
    0x80c0c600400d101002030000541011090640381015195102c1b40024281e0703a910840300b01c4c402c461001c1c0400c010707940c001e1980c0c0d070031440306050007145e220255468904650003100c01c0c800080d0380384014032440409104110180c1500d000031840e250103c0e001a95059607480002d280c044217074640303601540301e51035080c00200e1503050715200361400d00e405000f9801c0f0000250183c401e122002500d000c046d401d00707020807042e880d50350040006400307120107454003c001800307401c0c18800014100302001c500008190003a907505417500248503109003902c0102c80381104102c0120140083c55030041000301c050085020038580d06d2417040007181c0034103003074081c0d090440000401480400000701e92980f0942c07186003542d00c0035445002580c00c07100c1d1600499041501c014200054005624407107800903c010110b0b0140080d280e156800e80c1d00501c1000d00507000981400a05a05400b501c01d02160034005070204c3d2511401c005c000d01514801e1404010040e0b0385041418016106 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 63574211 1250 63572961 63572969
    0x120705060703021b190e070e0604080309040f060302030309100c0b012301030515060f07020901090c200a060b041b0f0f05030f01030f0302101503060b0909100e0106 72
    0x241510340c6040d050194540d20078005001d01103d01201307003c0103240c200ca00c2544042c540001c01c1c142802c0c81d10381c56805500611000c14460750741d400c0c00f0075a5640e0040d0005082c001c00559480c40700100b4007050b02d22244000c0c680b5400c043d0203100690f00441aa15052415601c505c228541040205e544104c1084090407071a190320020500101d8060040062600510f07201241c4021100440440b407046175041000b20f490b81010f58649003000042c0312103042403003400e0416015400042190740281d000d115140d42c3c90807000d1a0729000303841502c00036001400004c440c841a503400e0344600000c0001400ca0742d0b030381c1900c5040d135a51f80c84030040380212802080c00305d4026401405052040d020702000c2204603008100b1a486101101d20481071b03048400990307461030303a91402240780e010301101507000302041114030900ca8410704000300745524007d0762640c918140801110044603106020700001010001500070000d403096042445007000a03000d100380036028010000703508 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 63575461 1250 63574211 63574219
    0x3090307081809010b070b0411120f0706030c020307030903080702180f01030b0901021602100903080d020a18031a060a050307080c0301050f0106081303020c04110c0d050a0e120705 79
    0x1850038503400d030020115a0b584801e49256683d40d0300c42c0c41c2e0610790300070324000604114243d4005400282c580c1e180a800c020b0141800091107144010f41e800c00c03809002c0034070366a1103044100040d6505000fa1004407200740007035480d000080e2002400d1204078000901075400000300002192903c04881001e0803024001a080b41010008090100c0d000e1100b5102030343c070040410803408041c401c0740d084684041d804100400154284a09075000c01160818445820000000b242030324005103462900366a0050760b540800c4006090380c0b0043d0080c0000904e419018000600d9141c2d4407012032000e800e84201c15270b02c0200081d0740140301e40100c0d0300341c0100400081c1105c000100e02d000000114004c0c82265a0111149200e0209210303203030010b54403d001c03130a449015203c0081150082c81a01d14902c980301c003040947c2c40c0c0c90010090880d0000311180c0035081070200c409001618680140b8220180c04020816051822000e02c40c0002c030312002490745c81003201301d00030320000d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 63576711 1250 63575461 63575467
    0x406150b0a020d02071a16020301020702060c070602070602030307080a090501110a09030605011502070b0706151203020d0201060501120b040609090602030105090c070f03200610140901030c09020309030708 90
    0x984003d40790210800c811015201d040008244550f5a040c10344401c00f10707204a0781003801403c0d0503200d85017080d000740d070195420080803000d80c986400a0210001c00e8009041e042e140c101c0007444c1c0f0303580303078440e0301150001d100780280e0980c488003094100c1c0350304901041460755400c00c10b004110900e44400c1080c00000ea42d030300190810310071011280a104d00b0446aaa40d0302d00d0002105800401030050300072100034020b82003030300302800004d401341d82e001078900c2d0031360344450030110160001ca0403c40803080210815604101042958405200030711043d450880040c00615889528294540c0c030b84864070810340b1183d001c41c009050302d00040c040e04100d42040c0c8000e41c428014036010f50550400078807920103110403144c1059002c50a01d28000441e00d007110100c060800400d1040c100a4516040f281e0401030b0a00841101c10003420192904045a410307204c1d0240c80d600410b031100041000c201844490811100c099101580c0c82d550002c1007811486400c4009180340004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 63577961 1250 63576711 63576727
    0x70813080d150f0843030515070e0a140411030c09190e07030906020d0509060a05090106080619060b0301032f060711030c0310050a0b01050906030406150b 68
    0x30b19010011516084520801503860300496600ca58000c00c0d1000b0100303040c10344c00244c06100d4200c01c0f81d040340c4a07242146540c0056100300314050750380240c905078420807680406c00c1002505a8114070305040808070002d40c0804114460868844c850040102040145a1b0340300c80c0c1252401008107410036580389000e0b006000300c0e800000286018a03c0c0740003c072104000c1c2d9a8160580c0c13161448491987c0d54064110098101014103e810036024030140c08070342003a0007034030b000c0c66512020f84503a1500120050480346c0040a0f41401ea040144c10000100041181600017201c14038060200355145082000380c0b501e0b40c04a041414000000001d020302d00082c106102c900d9410002c003804800224030b41218500b0b099540004200100d0300081e6070300e2591112000d02a083d14851000301e000a07042c811003010308180e268a030800c02c564612030740f140d541d800341c0908000707080000319404200c45010044c4028466031fa0781c0c00c100c0c0b1145000000307100410118081d04c4d40e440304 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 63579211 1250 63577961 63577991
    0xe0112020406031a0303071a040305040f09090204050c04140402030603030c0601080601030501150f061d04060b0d0b030703030c0210020a08070c32060906070602041d0c03070813080d 80
    0x9802c2080080154000c1d04c2e80e031a0100c121000a600308404002c1042a00302a402440000c0c00890a00008202c0051000c82055600c0000d04451100188070354441c0140015218001d26182140000b003106100701504c0030509818000151401070303c0ba940e03003010901c0c500c514001d0740000e00ca000c0000402801c0010440e041e00d12440080c8411807a00c0e041da40180d0701800b491007030401204040c00340d00d104440c0c070003800c881c0c8c1320b0911041114401041c21101140c1207a07004141c005030080c511071403030068400c000790070740007480c400c0c1c61601d008080d45940d82000f032003100d102c070708000302e544200305083d149a0000004c80c1e40d940c0381d15000403007815a100e06507651b01109001d03000396026041d14500030316003005400000101d48100a03480c0c0c458101694000b0003440341d000499010320281014104002c2c0c134541449030002c0c3c444d0051001800d0032150340e010001c100e452a484582c0c2e94018004201c03406c0000c89c507150000080c050000366980c43c918009064000d0b200c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 63580461 1250 63579211 63579221
    0x2030c04150509010f08091524090606040501050313060c02150609060904081e070c0503011422080918060406140a0b18120303070e090112030e011202040603 69
    0x904000e0460041c109540140c4550044010705808502d40f01d070b20784031310350060a0313607070b480801e03401540c0503030960151000010304159560030801c0c0801c290103008076603e02281d0f002140c00c6891120034900440044e52500c550b000d41030420001101007032804158411100025900010a12008040000095903402c0c01100d8403820410540450f80c1070a028980c140180c074003610f86040742d034590304d50803d242d11110341e00d290290a464182642d20381070024100f0240305600307a001b07181c40c0a04041c00c0d11646c8420300a800c40034810b03c0b80781e48400051800858421420050b039110604100c1c0ca10301444c0038807a00022000003c4583c00c0703050116520540c0c1c121b8041140d10740318102403500680c0e0090403030700110540024020064035074050641e2803e117044440408040354003050841400c421380720b4240d0f002000703000a1a801881034010b0b200262400400d562504003000180a10984094140702652880d801141d101c0c080c10301c1d490844420640d40d455445c2c000074020701d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 63581711 1250 63580461 63580469
    0x20d0308040204060e04051902060409060e0604060801050919030201090206040b070210050f0f07110307030506010906081605060a090b18011733030624010905012a0602030c04 77
    0x1618010001c12101824105c4038016500000103042058101a014541c1e02e842c0500380e03445a010301002038200c0844c0902806442e46001c056001d00340700e8284001c0d500c0c07680064540307905200c10021059000500d00600e0070345040c00384440f040500f400d1380140080d44010750000300c00074002c140c0b2192180100a00d920981d143e42680600c45801c0b1520300461884112402080000018990685001d083d800e8040d802101840d2060301c0001d14082013540300b107803580c0000c0010081501180301e07140003840400081c1c000840c092118049034116405524400c2c0808221008030620846954000d17110700c0121030b6881d0310501d0b6a80242c074074070035994005060088640342103030802030b07140d0180382c20300402c10500c0901da00c84080c0400b0f0151800344012400f040c10300640d0200146c50080c0c1c1c50f801d00d603518610040610641e2030810903c1810700107254010001a41d00c03400c28038100b100c40d0300b181440c1e07484040c10000c00d15803a6025040b14000f04c00d102c440c02c2c03601e0041040b5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 63582961 1250 63581711 63581719
    0x810090f0204081c0801050f040e060108010e06010f0b030c030406021326011104050907050c15011d040314090402070c030503040f050a080607030f14040b040b01170c040f09020d03080402 82
    0x48508025190b054084540c4e15000240d281d0300401c0319003844c44030340d010364a00500201fa100e42142c001840c0038002d07400103036143c1d11140e80c858000d43c28883c2e0750240043c129a02c6080d0b0400075061580d120280000d405004000300090034000d595068138002040c0d25960b540e010340c0e602e483d8460f891110050f804d541004500c09036840014814210b043d200c158005007024601410441304100c010040d40a00004000701d100341c10040c41a00e5601e1400d0b1404081541440c2e854028040307036041024100c00500d0511000c660004840c0c204151450000c1c3e0f84c44007903c010802a01807568010480e000e10740010081080110107481541c090819060314207564908001c80316240d4407810034680c1000d0041000d280c07003600400ca00e40309a500100f002400c0f8142581803000440e401e65a2990b4501840104000301c4e140500501012840e890f07030785d0300c00360116101d00b11120444c2c0311b2555000880603001d025042801d10340c1d002000d80c0d2000c091030802a110083c201c4040f441 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 63584211 1250 63582961 63582973
    0x14060405010611060a0b01091d15040504020102030d091103030a03050a0b031609020906071e020109062a02031203090d02070803070309031b05041d010e0303160810090f020408 77
    0x1180e4800c080150740e242d2040d005295603110941d05034010004a11694104840c44401250a0083d804212a06c0d27100f101c06114a1802c01c11842e058000c084107140706600701740030300001d43c4e030000903203900c0303441010001200303c001c0c50031014554200d8101c50305400086a0070398941d07051f1b44041d00c105880c840074008046610101a00c0308941e0004a89240350b1260500540010340d0140141c0100906110319006054940405080f201c54042ca6680d4150086504650341701084000030540c0b41000041c0000c0c85000744840320080e65071441e640c0c90341d5510029584d00b00300110803800113210320307680c1e401c002c642151511a28015100540703d286400141040e001080312021900340d0b803000f00701d41c1596a0f50001ca050f04144055408620902050070b9845100e69103c2104810b05210010007a065582c250790a54550b5000d5400c240200214640325119482000c0d4407440c100940d507a500b5400c4141c080301d45c00c40340ca183c2c54044003081340c3d41a58003c105403400c243c1140d00b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 63585461 1250 63584211 63584219
    0x518030604170c0c0603010306020d3801020109080c0c0a06050405031b01030b030706080601030b0909030702100512070804140a03170a020708070b04032307030e12011406040501 78
    0x194400c02038030018440c0c2e6009200000b108100800b83c40300016000aa07501071070742c280000e0f80c81e04287c005503982680024041441c0500d4070460f030316003282d1210003c910100040440010510b1105003607200c80603111492503a101394066200e4980c415105615100030320760035669407102000d00c5014403009070010650718014026a000c81340c000303000f00001440701e14240441e00000424606040d210b000710711150341c0a016200c05803c0560790070049183c104001002d0b0307566070000a004942c504103100d548040402210401601910b00d2042002e50550446191180001c00c1000545041c240080142e0144000d80100c0c003880301c20f0306c1c11014500564aa0382c0c071903001004501c6010b96820344006808142d644029800d50040c1401c00940780e034606640004012503030b1103001001c00c007c1507048803407000d180d010180000c18502c0040071071002c9200340e0303001509003e40180d210700c0943d80c0c00350303030001052840002e002c1200c0c9108285002c031401e07030320359210324100300001c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 63586711 1250 63585461 63585463
    0x11e060b0c030d020702041d060a0b010903110402070515041a0f0609060d020a2c07050c03040603090f170702040506030d0c0201120617030c0c01050403022101060312051803 76
    0x1000c0980d4500910f15004980718a40025070003680b04981003900c0f030141001c6002004124803100300e03000050015442c0501c40c0d03004079040074a6075030610000302024008100d00680b4020461001d85005039030314240d090003490071142202c00e00c8034242400c100800c1003020004890783e0210714614282c261603442245140c1ca0045803200d812010710b400140c803d181508a16123898005000c02d42c149480c1c5280c3e280b0300c40b0410110016060034032114000001500d02103500180030b00e001c5042403041d0003044d40303d100394440c00003099201e070720b0030043c00140061f0f402c2055201c503091118804030401c900445d0000d50080e48281e02c0c00d00000da080c107000c01d103028104110354a0a645808650056481c82d00701d00e0840c2089940e0078010a41c1d08101c0c0300c0402c0022048000c640f50510209428901400e0242590402c8005d100c1000143c440f4040888428540d042106121035104a0540100b4440c0d00140021850b0202446003d400000034003000280307440940c89400404241 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 63587961 1250 63586711 63586717
    0xb070c080702060a09050411040e060a0602060403230a03050f0a0603052d0610030c0f0e06010f03150f0f08031c0221090c1f0c080d0905011e060b 64
    0x10300450810050709006141c410000c0c1180100350400b404c07000d40360008102214400807144010b25400a000d1000085812030b550740020304075000e80145003051402511480041c00040a1003840410207558541003c0c0c45000990807044854070743c2c1d81c0c1d00004000d000b0540c1e00c56141102d24010400c00f0405004104c260b0703801400a0020100c00c403042c0381081d084143c503403080d0807112082491142c081c8046800380d4184084130320f100f801d50502012811256210035145503805400b04400031400c0c041d2503002070242000c032050101c0603019000381c0380c0c64400900d6070702d0100f804038010203034501c00302c1520444000e040e001c50300e8a541c00d45d28407520520b40d0007038041d00e884982c07a060a4004003c3c158030403941c0c090071444030180d064002d006a036240c50b33541100f03007605120304203c12001800d41c0700c00c04d070501d00417040002400250702140050500100041e1b8443c0c034ac0d1450300000c19a942c80f0000b044030300707021040300041d0f80310608012200e0b070803ca80040d04001c0c610517 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 63589211 1250 63587961 63587963
    0x3051006021c080a0204030b010b09030d020604050a060c052101181a0d03110703060507020d0e010c02010f1107060201050603010f050603120304020a0b0a0c02040c0906050a0c150510030b070c 84
    0x41c0848500030380c40650b242c960042c480d282131034007000040001004c0c90107090090428800300750310340000004041c100f001e144c00300d10440d40480100004141c00140b0701c04000c0c0c010780c4c0007909851200c0c0481e003610414101403428841243c503240c0390031b1888203081c12200e4182c0e084083c504819000c03801e54400074500c0816490511907408246001100945114400d0414000c54522003440c0c80c240f009990055a00c0f598030420000c011b501445404400c40b003c0ca06001c5040922001a03c0440f089801a0411484201030040540940000400344131140d00319058640d540500030302030007080300c545010b5403e11014290002060049030f0045200501400425001c00d00d41ca13160380000b03006980c05078810500192503441e103401801c64000580e81c41201c0380090040c4400e549520100100b0840394440805c10280e201060383c40d40116883c11550301541c500b00042104460200c4650315171034902071060100307981c0c6c10b907001c49201e40032000455982c4c40017130700d0a2400d040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 63590461 1250 63589211 63589243
    0x3020c09091f05060a1a03041b180914030c0a050712050601060f0507020907030902180601091806080706090f06080f07050a0512011829060c120304030305100602 71
    0x20b0421a03444203400c01c650010005d0f001c880c2113580d034002084c031151410400d030344a2100105201c24010700141c1c081400074038002ca5003805280040c03c1550168607052070726050354032100c41080120f0315442110b16100541101d4480320041c910341d031280d00f441c0086842d44207001001400b0801849440c10f081e03004006802268a0100c0c1618100c0c802c00a500400c4000c02c20b0300700503030f290007070f950245909a40c0080c60400602c184013200c0405c0e0010402241c01001b0441903a034402614401e545103442850382003098003a010001c1c1c4200c1c0c00280c000d004d00c1700089180b80e48151b90f502141c4c1080e450400304c41d03480d80290b07901c9105903051283d10080c00c000520840c010381c01040c0c01142032400d14940001d0080340c0080311000e0304051071320b0002d103850148100d8240103154000c0da90461858481808208181c00c00c452012440c0c0152008103260b1500390f801d0041580000284050944c2d0f403a20303140040091404903800d590340c05891202041c16840020400d04c245e00040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 63591711 1250 63590461 63590503
    0x11030a1a031908070b040803060109210305090a0801110717130510140c0703060e0102120a050408040e07051c0605030c0d050708030414030c010f1407020301021603020c0909 76
    0x1031402842d54460441a03030011010028100081c0b0080211803207580107810003600c13410060001070924041d5171100b81e40c0e02140322122500d038480000d824500d40d060402d45c0d074664416000c14403010156000031034075407810414040540300c3c1d10045c64424031942e140f0102400c04003000515000e2407140452020840d1018015802c10340c452200c40c00981c102b0b003194001c030621a11451340070710011100b940100d0020010400c450007040c8110405e0b43c000c1d810714208080324080c010f001451350110070f4031000418103100081040b1000340c6000c01c0020385520b8200c801801981c0700110441400d00722640030820034069100b00d100341e80c001009840320544030300400020a04c110801d035941e016441d00029201c4040000304000c24900c20007409042907402054181340041550f00d040c08489544400c08643c0015011340d0343c0d0740c2a10f865190281e50000c42c0c020300a0106182c60f20780400ca0000c14190002501c072001c60085038010342590303451200940700c3c445a40c080080392600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 63592961 1250 63591711 63591733
    0x1614061903020904090f140607020304060e06030c070f0302070311190902030a0e01061205071509031509230105070309050d050d0e2b050423060d11030a1a03 69
    0x42d800800701c6803801400070406940a407506110a543c401040781d25000b48031494140c000706100e5194070241c0390015500b050314102c4041d1840e13a001c0c0c0e4041c86190700000080007004d104041e0b03070300b99812103e00713003213440c442c54065540c00c80340c002030b254902d12503041e0b50140340222030242e019818441c0d56221914180b0fa090184d040a0050707041140c41d4005011203134002d114101c024412a643e0750103c4a05051103410b00203d81c2124103010303040c003c00002d058200c8104011254042e0240e40328003030300c8050270000c110700c04004041100c40924841180040e411038010301e0f80d150000c0000d903c4924099040303800044005202c0e4201000302071206004a028082480702684046201001c0313031441ca003440c8200c00c1c0011000b005000c0b00c00394034805404020428050309045142c1030030008124200369612040d04002203615900842c103031508010740c0c3c114243c80f0b50034403011044121081031034004550201d00d480c5040b20084640603451200143c000c4d026026241c0b032604 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 63594211 1250 63592961 63592967
    0x306160507030e0d0f051c05070203060714130f050f030303131506050303040b250c26011505040b0301060308030a02030403050405180406060605030f0718050316140619 74
    0x2444602c80e80507104641d4130380814032020000340d034103224201400c0c0411120100d00c0303007940c0c140c1200c01084000d000c0d0b0b50040e20005041d641002440c101025081d1144001d500130384980403003800e908903414800201145015001c4043e100211031080b0103043d02414144c0d2400101c0c1c4520107031541c1141d0380c02040b00004a000402142c036008200b00d0f40700c3c404245580c1c0b02e9481020380220000300f2a01d42c11003217813651000003801001038540c2a1640f20460b000f400d45c092480c400c00110a452140201f080c06400f0060300000240b0a000500c004503004820742d03c6501d010380d0402644200500c1c0c188902420750364450856410358603503034030304002504020012000d01c00204808580c59448461800030b07510505801031062400749403d00903a0f00c00e6022005101017801846502242171415960280306490320311082e8400d40d0152642c0070b01a0300c202d400d03001e072041d0201c004407604120000d07200301201c4006052440030a0254070b00c1078451a402c5d0305001000e00d0301c0b040c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 63595461 1250 63594211 63594227
    0xd030503150a0506070c0515070201051b0c04050112020307170307060f06083f030c07020109050901090c0908030405010215040309050405130501050601020a0b01060c0201050c0703060b030616050703 87
    0x9800b6010709265519140030859582c02014162001070b0018001c00461400500c406c0381d5010800d0070509100040c0d0010b0001e0250212a000c80036503980081941c0204108001803000014024410382d40c0d601d0324031030b11a10301c1c041070307000e405590300102e03007001c0340802000244400d4005516042043e11030400808a00305103c0d001d41d02c400c0000b44004080103207004051103035210706031184203616004510104990303114601d0f401030f040515039070004c1059039804090f642c030095a40401d440102c401c144240c01c42c5901c240c880307001141e50512a40810340b480e07229200e9080203a107038040d5540c2c0340154071404e8016030000d02103189804101080303d070031902c241404041a5107900c00107007a14000c036101c1c0c0070030b12105590b409100007401040c5d0400340c00e0001c2d0410505540301c0700c5004005000755810b010188480e0030440e440340c01281c0781214240103440c90305072a03242800180150400c2507100c5d02c0f950000c50038180c04100b0690914200340c0300d42e03203800f01c83d0381c09480d145 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 63596711 1250 63595461 63595501
    0x80c090315010602071d04030203030f0c070606060e01030b0109080709020a110303090115090b0a1401020a0816060b010504060c0b0a0905030a0e03070609050d0209130816030e0d030503 81
    0xc000c8410328800e00c081d1000481c0a4421900a0180d880c1001d1500001c602c0c80c8400c58079403095a0188400301c1d4001c0b048a800c40c3c0000d2040c640c513030340c00c00300c000d4a101e406c000609a91515000160079680030340c06642c1032038242d80501c020040000115444000d50150700d806400100c81008030401503801081588594102440000b60070307038215045410403075034005d45944844080008518100722200074004a884c10410031200d4004240d82002c107000f05100007080450310100c9038000c02840364640e5000511544e20101c075100d1611000200d18119403140c00c1010480d01507000b1030980c3c1c10340f50240d541c00001c080d2070301c42d10704240000c0d15950100da5140300700004a04144000d15001031940c41d8425000400810f040c40c0000702c0c3e00000c104003082c01d043c003881c0c0d2883c0300b4003050340c0c0407202401c1c0d944580608414200841500038600340c000111034129040050681318142c0c0240c0310300050b50f0584c000e00281002c100e800400060082000a00d29002000c52102e06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 63597961 1250 63596711 63596713
    0x301090b0a0b01200307021306180903030b0a030c1404050405100203150907080f09010501060e060309070902160b0105011812150509011a040603030509060a030b03010f050105010f02010c080c0903 86
    0x200710f42ca200381c0110350a81513004030540001800b101541482191104034494802080181a11b03080d48184070886e0300c075071900e807191102030b4803040c03511941190306035000082580107050368910b0080c464038414420040c1c0c80d201c0b42c40b409070b645041e100e001c0c0301301c2c2c000003d0a0303d0b80300501550002d610080120007602c40d44d058503001d42c1c0365200c09034890540d940b41c17904207040000110904003c01800081c0c260304080061025580c045a1456840346c141c80081c1c581c0c58200340c003400c04085400207082d882c400700b41420711803c0c3d00318050a4500400005134542d803a200111080030381c0c01102640303440241350030001d1303150004203104801d01a00011014206074140780c01664400c1c0c48080440e9111400100f001181000621400c07800f100e0400c42945541d40140050082c0318020b44603e101149001d9030700e00030b81040c4072030360b0010008c001e440039242c40c180c000c4c442070284500140108002c0f030300080c014415050103480ca0349500009681312400a030b40d80e40840502901 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 63599211 1250 63597961 63597977
    0x2071202030d0c06061a0304060e0c131517010c0906020109081b010209090f0a060501020f060c1b0708011505040510140d06060f031b0308090108041e050a02040b0301090b0a0b01 78
    0x1078800e042d1035440ca11010445580d03624145801c280c01600c820a10b0017002d038100d00040d52f00ea0707490b040d14019004144501083c00e200700c95501030b80b000154032030622220001c262174640342c019448202d00c50b200703880c0c0503600b58642c40220708840c00c0c138100078111b40d02007015035058000522032020042411002602d00342c0d040e00450f90b481d034161398610740c003007000041c400003001d180a00380150000384000d141060f1007070743c6107039180700c05000d61103d0500000e61000e40011216024103449406c0c1c121903005e50754054007802022582d49106903810644408a0035292900a040c000d41280002c40c4d643c50410440115040724000071945c451000c489480c0019000d0007004000e0480d01c0c4000c01451039818903040440100f044980a401c640c00180b00041d042c50a035000a1400e107880c54150341c0f586048511094241c44c0c5045440c104404a01040b0b000a41d05400c503200752410301903206020149400d90f000f040d0000c1c4400c5071100002c180c1c2000d030b44034410740d000c14908180d07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 63600461 1250 63599211 63599219
    0x409051b04061b050a0609050d0f0e10021e0304140a081005060303130803030405010501050d0503030a320718080d03051f0303050c120405211606030c02071202030d0c0606 75
    0x11030174618800484056448000316002d0090038001401c42c401242411600c20a000100800d100d81442e8658420400048840c0169208000011160300f070401c0c045289040d41058a5407508944100d000c0c801e0030a1103064a4103244000604031003a0780000c0c5400b06012900307a000d003900070441a094401480030911a040c00e00c015801015030401442d920300342400d042c0d0960b0816080f03503019811841c60100003410001c1140d5204002080006140d1000941e1002d03180005080c00e005c225000501c0215151203204503000385030300d480c0c4c0c40348001440c0710300321714045074410140300380c10100100c1002d07402074000590182c1d83c09041d43c0d607d080e80e00d5a503207151090300b040e0001a170204521180b103400b088502c0d031410f0781000307031800d1618000c009420038030741800c403503003896084064540da0041085000442c4d1503290a003000c594039000028010302410347d20038010301c10301800103102a0411085213000d500039001d0400b000c4030300010781c2c00040c0c6000440d007c646e81c1000007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 63601711 1250 63600461 63600463
    0x1050901030f1b030f061a0306061303050d050c060702150a0b030a02060409140a0207050c0f0d050604061a150405010e270a0e030c100515030109080409051b04061b05 73
    0x292901c0c03031130b45000400050505440e42204ca15030001c2024052100081405d01100c07816258041c208468095840501c408040b80301c070b40c6a440208148180c02d24001d415422001402d05c6080d0602103c01654580c0003ca0b99400b800c011000c400c0d080d90042000d86006410611400101800b210540b85181d80840e005501c1a2701002981703564000034010090f134000e644d90011515103041d814070f61300742c4a103501d03800d400c0c0001d8815450394002020585039444880c040582000c00d40d1102e290030f04212014003160306d81d44c0340c900c00d480400900303441c200c0015820721403100321007404d0a007460010341e04040030302081580042c81020642c60a0851a0b05001090b01d82e0f1301b89601d42011803000e07042d00c001c00d0038100e02d5002800062511000080c041c0c05140380e0100100b0070b5212150100f5000d8100880c60b5019420b0810301014000054000c1003110f0b4860810049130350717840c0d50260b41e00341c165042c040402040108000c4d04d40b0503112518000c8281e0100413500c1c107181e8502e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 63602961 1250 63601711 63601751
    0x109030b0a021306080106020d18050d15050901020c06010905060a050a0303020c0102010c03020a0f03050406020d0e030304151b12020f16030f0302040f050d080904050f0f0604060501050901030f 85
    0x1d5a038640000b4120403480444000c03c00030f0405003400b40c078a505081c4041d44a209116100c4208003040310030390301801c480501d80d13009041c0034040034424551800c10b00a04100700403400c4015017801c0c081101c030f00c030501c21607444524600180c0381d941d0070224040050312002c1c000a600210f04440412203942d0020144011840390b0010a14a55440300280c00c3da00036414800c01d02d4410701a400c40c880d00804807040f03504451500040582d22490600000e0160f050b005495526146921025140002c021030003075006241d8860b02403603990310303942942e0180c1c5240958551040c0060901805603108901445400b03d0150800b81c1c0221307022010740111450916201d00030f8400380c141500402507100d1240c00c0c0c50103516160400400c07080300503082c800d00e8020080707540c0c00d209112207142650001c1c18010428807290414030300c0050300b8a410755100101a48501c08103280c0d241c0341c400d440c211441a100e05080a00040054008040c491040b803026910744480051401880c541 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 63604211 1250 63602961 63602971
    0x203070207031a010303080406020d060b160506010504020408070e040311010c1d040504030e240f07020111010204031502091c03090609080f06010b0f0c1002031608040317060109030b 80
    0x41500602c1c5040118011140888440100d15144014808640e115002550180e004440583c0c2c4612800404004000551221442d0240403c0703042ca510b000303882c1000f8541c0104212035036030362114100310482c40340c1e20901042783e01203402040703039000c1d80340305550181c02800e00040d9003590b50b01c0c1d03900707640d00164402c00041003400c1c41c0d510306901c02c0c0c44008101050b14204000c0c41c15650140c00002103145c564072480c1d00040d219000c940b1070700856000082f001c040354550072100e021507012340212000300c1c041848048030a00c0804148251000c41e0307004400081a007035820005d400a51000005076044440c10201140d04000034048000721486940c4442d0543c0c98001c004100c00e210303130002039903500288840441501e0000c0e00e10b0540da0000500c50381d4418201c841e03581c3c1c0c4071f4100400c80324001e4084080900182c0e6001c0d6109541e03441c900c0c41882058402181d094408031002804541390101f042c510040c40c8007150341c81503040c1004041b860700c984a60850020403a4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 63605461 1250 63604211 63604213
    0xb0d0b010b0304140c01020d03200c01050a0509120301031509020301050711010c020d0c1202070806090c1f050a030b03121b011b02190302010b0409060f0606020303060d0b0a090602030702 82
    0x60104124104e2144184060468040d0031381c8032071100002e4903900304419038010591240004070340c19002c1c0e010a80b9050342d5040080d40d894000e00414080d0100300c030711a80c1a4500780014000759004103001640d40e4402e400705195a09507a1071107a89400228040e222a54818114005071401d20400d030040c2e1081d00c44010403d010761581d400c0d6240426482c0854018200500e5043d412482192080f9802a044680c41e008024121710781642e035408010144511024062207030404150345171a0303841550300391000c01c090705403c01c0006100010b040090002c00a00c2609807107640b094412030001015286d404003d80c03006d282da90801e0b24003d000c2d4601088a03c60440f091040c1e141c1505124941400b41d12500e0000c0d488862a480da004059100380d90f100c101032003903000d0142114001c10802041c2c01c0340c05d01d81d0040c0094085010380034503020740451345e18000800d41c0d104c0d14005120070b90790401642c4526450002070414844680c49200103000100a8000b0310b03c501080d034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 63606711 1250 63605461 63605467
    0x110f090a0f05030d0302030411040903080906010f0308031611010204080c0a0509010302060405151204030918151206020702041109090708010302010507060e0a170a0e0306090a02040b0d0b010b 84
    0x202040403240d01988204800c01c4800000c00158401040203100c4442c5400d00607104c3d40c481c01c0c840c0001a0300c0b258294028600700004d001c2641203800c2c1800303180510120343d41c60ba2105104d002d078842c035000140c03090b4804d0000507000030381d100a040f00d04030985004402040d040c14000c1c00c3e03070040c1c2c0000d030f002e4021030040031032414010006001807004031001001540b540d00480c0480c4524000c80f0f0040ba040a41c120515a004084070714034116250b40c002a45007070b050042c1000c066002d01c90a00c4028504410b0744030143c000c03003030704803135843c01d200200d441e00703607100e0305900040e40846443d0380074414800565100d200c1d50a00944410465035202c3c0303210f0800ca100c0800500359001d1040c0e1390b00500141c0d901c4820b44481c1c943c840c500084024040c2c500c0c074604150311900604041070646015a070340362040103095103844503203500881c0155481096182c00b412500c82c02142d00a01000000d494583c12031200c02c80e0140982d0328004442d1900d0307400c030009803c05e188002e000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 63607961 1250 63606711 63606727
    0x131202030d0c02031909030b040b0c0f0409050f0c030708061903081303050c0102030309192d060e0106080a171201060201060806150d170c101407090302030d030f110f 73
    0x10085288290520303140541b103003550b840c06003032200031b00040c00d691040800104880f1144048405058007981071a880b0390751201c000303010f49421a50240d40703411803000f0504a00020050b40d002d490f264440a000e41e0750f14050040b91b1a03402e941100180b2118000000720b0150300041041c140b41d80c150009150075410414503041d0108031280c1194810410408001c0b0041141c0b110b8815a5a03003d151811504152420b0845000d80b40040361510f018099041d8144555038410380c0b207009c0500001c55070300780c100d08881c014400c0c103006821a060b90341c0050381130521a250960700c0403d240c2000400c2c201401071240980050f000750307668400911141c2420088190300c0241c1c2201ca504810088001c03400400c0e2402005044124115840c00c824108000343c0b403104540104a940107101071104001802d046c040c030741c411600300740116160f1807007034108406403900580108072030b9a1441b0103c00a00219581051180d550030319035030003480a400801e85003c0c146805074a54a10b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 63609211 1250 63607961 63607987
    0x9051c080d06090b0f03060709060e0102030f0a210612030e03030403050d08010e0f060604090f09020910030b010b0a0834030501080d0f1e020a0206030a05100e131202030d0c0203 78
    0x1000c0c29129500c0b43c410008e40c1c6038814240b0040c0c844900d0301120501d080c50041c0d10b1401105250001442d010600122030390f03100c481a00101000380c0d48040c8003580955140403074015000f2012581d40545004020901401441c400300a002d41202d24040c2d90f62940d50400c3d03a82118180052000c03030041241d00c02110305aa00310141c003d46900a0801c0c00c00942c60340304034428004880e440c0c0b090590926070651000040a070090120340c81803a0440e201d4070a404940811500f008440c030010541000403c245c4100815030f80300c0103e5130f103603808240390030440b424149542900c24600403101100480620301100d00e1600d0103d9a9418110964144011310034008200704070040030b5038030342c1d52001c002040714070010b28072208215080c204900307241c4805806508100300200b07101e6407800d154031107481846036200125050380c98540902c2805070030740e07400281c48020313030010010800c40c0201c0010540f00c0e00480f0b283c08103c0103041c050394607407003624000d604040780042481c95 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 63610461 1250 63609211 63609229
    0x80607020610050a05100309060c020f1203060303040501180b0d02090a08010b0a05090711070b090f01050304030e061809040615060e030303010b0d0204231009051c080d06090b 77
    0xd044525642e50340d040c000490a00d00191040e28807a52190200c101480d005e03078001c0c040d2641110040c0103100502102a40d900b4060102c00d10764821000701041118000d4150f0340a040020061854180340c10011968603250070f95200101c8110300000031207015043c01000c2200040d070001d0b0311075104208002818280f54000001c40e4180840740303504d540c83c0328414060351800c0320445400e40740d100b01124000011501c5800e5841407800100c0d144805a0140008000031110b250030102040011222404140c50090200311610184000c2d4075018014264401c0081041c0700c296034100d0001d42d90780420b032030a6803410380d90154920411000c0c01c0200290500d8201034910a06240201c0d0341d92005104851030030038040350307a058104164040340c00a140c01c40b002d480f1509120301041c0c100008510585c452482e070200c00c510340307010300004012108001c12011a070000b00307031690707001510b412045403802410800004d4804103445484050304019030300084020002c0144841c0d10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 63611711 1250 63610461 63610471
    0x190608010e07120c0e0a030803010905090c011b11090112020901090501061d0a080304030507170d0c0b15150406030e12070f05030f1c051308090f0109030605010806070206 75
    0x58441c10422214680215056503034000300100015808041041164010202540f0503413104480c5400020320a4110186050740c40210080149403103007022181d40e04d1102d4180d50100d0192440c00110b0021580c900c02d840e4000d840404110f50071400280c4103820076085040440d2a824548080d800c25801e0203014120f1140b040005504040000c0d106000d01c0e90742da0128101660203840e40d03150020140001d10304d40f0101ea40f038a071030340380040c0c46814034041d1215034500050304600307007080050010713000220f946a6079080d01c0d181d120030084c880000c0036a503510100503846280394a1300120071030b0501440009984490412400400340d03094a4000010395000d0640c0040c8556103200303e481c0c065100b414180c440c8030510304907045000307a107094140803502180b440e0307a100e50301134002a0303c100314000700550756034081e2a18031030040e00781c09040002c0a2101c5401e504001e001d11900030014107250003420343e65075030b10b815103809801078113440c1c000e2000e000c01c45404010b44c80d005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 63612961 1250 63611711 63611729
    0x10e0a0c031a060c010b0d0605041209030b06040f1d0d030c020c0913150f0f0c020303100306020c071703070c0f1503050402040207120c030809160902031519060801 72
    0xb61060720b0029800e0044200e95a1080c400001c22080700002544881012000640528905183c9081100040c5070486080d20f0156a0813406c205682c420028202942d5000a416529403540c00501c0007c15280812411050b07555803803203042c21520720000c1d258035080d0000c0600300551034000307040e144803040c04000d651210f01001c104c1da0702d40148035880a0345810071002c100031810300c1411110308085a00e406072910641c0c4071405240c0c3c000b1450050801c00502c2038031746581003281d0340c4c0700480700e8200c213114183c010310004165400034076205840c0d404480d200f980f50030090b00c0001c0311108034a21a4400601c1001708484540078100034298219000c092500d0034070a60900c001c040014010540c1d5000001c08565a0347e0682c1c2d081034011702e00d201e510040b07507009001040c2c610b0041d0049203081e80099805140090030b103510710039502ca4460b0252504110b540039400280c0703002881d0f0352110703400700d803901d68600d4040903001300c0a02280703461030000040d00041060b0070110003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 63614211 1250 63612961 63612971
    0x61603020c07030813030b041a070905090403081503190b0a05190f1e0b030f030c030a081008030c1b040b0d0b04020a03080a020106050315010e0705030903040e010e0a0c03 75
    0x9030007804a41001140c0d0084400c03540e440319000d900d40a21349a42004000744242e00911091000c0d607a0340b000b94012212642105884841d4280c603244283d114007903119001e41c00080000b841001d6194101e22020491040d52002c880007a00b8442100d082100398050400040c045c480e000c40c055800c883c41001c1044541055800300901070000b5142040da42c0c0c894680321104a4654402c035822094200d0804074141030070311240c0074103039440c100f0703101c0e02c00e8142060040d0408400c440e1104503020046241c0403428005032042e042c010512569030104050018220300d0a00007402607036648070192a04105030050321060590101c001409146003800440a035102e0034000c00c401034000751400419980d0707100003114561580c0000300540d60200c1c002240640541200085d1078044041d42c803150122904d040d03a0440034031515241d034046002003a607287c0075000454015007113009a0740740c1900c17140c400803030710400e0b444180420801820009000200c0c0b1400d1000040b615003440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 63615461 1250 63614211 63614227
    0x507090f0f0509070b0a02070f0909060b030d1b060204150c020901081609050c13030b0105130504020d0303051801020705060414030a020c040b0a030501110a170705030a110706090506160302 83
    0xc2e84c0c02041c0501d9100c0540044c0959646000300560750040101c81e10a05080382c503604101c3c00ba090b5030740110380e080e080100c005003d00c0d0101c0c1c2c4054147c0c5e15625600f2042072415510420781c440745050390050343c01c02c8082220400103004070f03071121042d126120f010701c5510500402181c164800ca615800c4201030032a000020081740c41115010340700030403140c8030012910740509c100065020a00e0f49010300200f0441441515070486100310303810030440309900f04030019510210340095101003080102d9001038020f80c0100c0e00107010a5144c0644c0001c40551401c90340302c1d0805460962000e42040204100700652405802c0d015001d0b50519020040c06580e424070341000d40d11072901e41c00b890ba070507241c0200700030003950001d000b403100003041c0e651501240d018502e80300010303010f400780a05403101200f40c2402026039507901482d6030740303080181d00107100440005510680802c6001d011404034020044170901903800380540f401e000c84031002c0b000e210284001803500601c8440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 63616711 1250 63615461 63615463
    0x5011712031b07030314090604060605060c100903090e0f1005061206010e13020f0309070b0405100f0504090c020d02010f05011409040503190918140408070f0507090f0f0509 76
    0x2000d41481440c0300c0ba200c0c030310340c43c4c1034001e07005041c000000554802d040010b103500000701c840c051405128208003050300c0e9410700c0900e00ca004d103220103560120068040e40d0380c0a82c8101c40b000c2c040e2401c5102a5180c1c80c4204410206485544100704c10348240140f40c0361842aa1b030081100f01c0e282407030101c4042c400b0410b13460041001f4103108071110500300e01d440d0180e20100e00c1c40000700456503802528001a07072900f0648803910b05125031540801c08010b03410445065410051607103d0380107000c0320440300314440705401801c12205000001d4502154020b8518503d072540151028611404009007151081e08920080e541840b00400000d8030901d50410320b19000c0d140e1040680c0c50b8200540385100b070079514510401062410143e0381d501440c2142a1034100d01e1451425511008581c2078a560002d07a401c1c4444017000300b0b0029030040d0040c12443d00c1503460b03044112083d2207082c01d007885036001628050300c801018109604611a503020300001010410050900c0c003805 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 63617961 1250 63616711 63616741
    0x406090909020d120c1b03210315060509010216150e010507050f0106030b100b0d0e010b04050103112701030b060a0909030507021e0d060b0109090501171203 69
    0x100e0306459440600c40c0c199194054900c41540c0c01c061928090b410f13203c80107125000c10031003980d02003100e4242c07080c0302d914401120222500286144003003605107181600b803c8003000c1e04028550b50380c1201040400010480c0024603136501d0f081e0f1200c0103000060700b041009892400b114460b07080c1880018100310721181c032805c0e2454140401c0950b4030041c4c4513403049001c003519521400d02c1c00481e02d2015044141507130310801c495491a01d428404415514240c0503c0484000034400300c81071250a13400305e5100d541450001c921090104046000c880e001e80050300c00c3c40503001c9000d43c0d82064503084070680031351084002c024400c042044116481030100602f40c3ca440b0000c5007240d6163b81e1001c020707080401007000000d900707203405000c6910401c0124051103500c1000c0c1d80110024400030302908001d40402d0004c00c080d40c5500051900c80581c0341031108115012407403501610515000c0d2100c1005170b41e010200c800b20724076103015600f07484030076036040040000a101305501 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 63619211 1250 63617961 63617969
    0x1081f051017011d010603060c36090903080105040c0e030715030e1005070e0105071a0601121103100503030405010912060b040c02031305040e0d0503180607050a14040609 75
    0x5040302c001e09661400780034105070801c0e900b10f003d003414446071540c41903002d0700403203104580801c038496840c5816120303141c21040078401103401e034440803100800090020700d0100c04900a02e88a03403104c001204031000c0100940000d0a040010f111500341480f500340021000d0501c8400d501005000030340e1410301e030007005443d101c503850381138106000c0d41000103112031505c261103030a10031100c50401000c0c2203540d000042c1c1c160000d800c540d40103100b1038840d2504002801c0c40d4188003600d400820380c014000e2810400003150145600e007892084828400d6050300307a903545d041c6030b940b102c1008240e0b00320605c00e0304104020005d580c1c0100d6590100c0b08100c125524900c000c0c10143c4c0100100c186d026001420441e050108070b601200900807000d0795880100c419884200344000c41c1d009004507c4154000314002d08554002c03005954002070038075851003142c11415516081080580303c0101140c0007051242840381c112040407020404515038506080c5040780003452000580f00d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 63620461 1250 63619211 63619229
    0xc12010c0e0105161e0c030b0a0b040501150318021e030c12060610020f0106030804091d0303010504020c0c1216080c0108070e01030f0507050c0106090204051e0307030b01081f0510 79
    0x25031038920071410101701007550781000446c41000c0d500d08040c56004400c440380700103145402040030080c5441d1144505843e02090a000700300d49400d0305800400392401a10060268032546400503510540b204000e2406c40080b550740c1080c00c402d0520703040c0c4000c1142c3c4078608507400c8440081002401c10b034081e000702c607402e200c00301812041c2e0030b00140c3ca00380010b40d42032400100500041c0402442254561441080240128800b030200171941c402e400120750010401044146001d4014201c58000c0005030746009400900240022401003800312480e04902c090080e0340e411000041c0052403600041c040303081c07070320380000e00c0140d0040800301404407051000125900c00d5100d039000d124141400c0000d4100352001914940000171a08455800c008000c10010305134003c1c1c80450310050003464018100506070000449002c90327180d014410301c44004082040721000d40d00914110000e08015002d1031032800b0030442c0d180c1680241c1d41400c003408002500718505c8022150046 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 63621711 1250 63620461 63620483
    0x105160605100e150f06160b0606040914010602011d0a0b070302211503010e07031103010b1503041a07051219020c07090c090f0b0702030c12010c0e010516 68
    0x809490003a03074803500421922041c020400c404c3ca8a000048070000604032248025807100c002080214480c0080d918564083c402e048000580c910504582180d0000c04071070800303484507005001c13601e0b000d15004080c4105401084030a40a1140641c031030b003000b00080b01110b410701c04564540038804020600403081c800078500c1ea1007a4180c907882b2500320b60035032030740d40301405082000009071001040a1205a044901464140705880703d5980381d5000d00750207842c0d0b854501c2842400549580c0554070342c1414050381c0d80d010f150129010700c1d607011076200d040500380080e000071241c4071140550091014803050540040036070f05001e082459424440d07962816901030320849410100c0c0307044c0040f805a1400e48003084020950f11910020000c2c142035450840c0c007848288910b03d0705509080051001c0201c41c001010072500142c1140c4038180200c001ca0845200c410055900da5903035001e071108241c2c04418401442d001b441c1144c2811aa48001c100345011960020900301200d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 63622961 1250 63621711 63621721
    0x1030b06011806110601061e08040611070b0a051f0510030e0d0e01080a0203010b0901050703020c0a0909050f0a0b0604020d0b062a06070905010c0203160902040906050105160605 78
    0x8281042c4031124104a0700221660761801500701c0405661035685801030200220300c8030f104103090201c40c1000000c90340742c100c25030300641da1400003030010358000303860310400440240f0510041c6540ba00c00e108000c4a490901d154004844014002c40b800701e80b050000c0700c048444c4007182d000e45008603440f25a0501400c0c0680040048629003903440c015114115601c9810894103501800c080e22b401000b55900036019040340310074040d80b04609402d20a040807548a81c0203410860320900480711203500302e00c00540d100d819a40011402c83c0c44041c0c81080200031320854809040700001084a02596034031404000c600802e4940119408201da007001c2d89207400250000030040d0446990f501303401c0081405051005060f10880411b40c10800095800141c031f512940113075072158001c178200401110440c20b5034006aa1511902c03105544101d41c81510784014820b040f0700603aa24a000f540c0070940f02c1030361025040c0041401600810200262a041801d500c140c00149580d10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 63624211 1250 63622961 63622967
    0x60c03050a0c05010507020309040b0d052e1e06060e0936150610080a09080906031501090b04050d0609020d080a0306060201050606030115030b060f0c010209040b0d050601030b0601 79
    0x1d42c0e60241482d800c04041c41070040d0003000400360303d0720a40b020301056071503030b040c40643d101030701000700150b02040c0c00c1d0102d4000500100c007803602e000d0140c4034520344d100c4207000380d8540c181c3c451035042c00c9011170a0380307014a1081070001c106905100108080d1080020501c800040002000f150300e804107201020640440000005005502e440c00030010305c0501c0e42c42504628210b040381da80c0020038018a490030341d020203042c0581c0e880741c1c1c5590b503e032500c000c0d01d40500120340c580024000104030743da41c00f001c4c621491405a480045609000004001954580c8070f4000c54004001c240403e840d681081c011154001e440469812aa8800b1484d10450741c0340103401c5000c041104007007990326030006400c0754081d41c0288143c2d201c5000b00b011034482849400c803050380001210040c41c0c029000302140c894001d00c600e0600300150941c0c03020f940314402110b03d503540025109298079192184151066090310980300c07910751a5a079030366408041c0400342049041c20002081c4ae84 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 63625461 1250 63624211 63624227
    0xe0604050c1902160f0e060306040816050c1e030d05030903070311070504020307080a0b011d04050916060306061b0302070611010b0d14010506010c080904090309090c02070f0f060c03050a 82
    0x1c220000c00c1c010781d59041209881c2030a00980c0301100b01440801d5907231400169842c00365800406040c80d1400c2c070b00c0000c00300600311600311440c1c010f1002c940350ba55180c0c80341d030143e68110165050703141c001008141c2011040e0b04900c040c080c0030310034402d4101000080e81e515540c542411a1025565105180303090455842144d0160000040142e441d030b10030180c50080e5541c080c01d104090240c001543d501035100c00103400441d60080c0d5015501e0242c01141d001011710041d14465901910060590301082d0448408652180810030200d5440b08c409601020820310b03002d096100c0c3d5130001e44234800c5100e41800c02201d442b004400800c207601c1400d2140700204000d428840500d0080c003104040702886040d5440c00780010005e502458001d0308882e4040c2c2034925148000d800c000003490710301c89c16000c11a1200000c07519410a01c5404a640c070260003c0180614100c490440d244542d0020811003400c0301d41000b00365003206c040710f4030951500f011600c0300d0641c8021240b0b11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 63626711 1250 63625461 63625483
    0x1609061202040b0c01020c0709270f060e16050a150c080f1809060405040201081b042126040312030209100c0b070e03060f04030219030201060e0604050c1902 69
    0xc070f40051100c0a4100540c02040800e400b101a210001d80d51310b14902210180182580e0181e10001c015140051044082c00440d105120440c1580059242c4000b1115607419000e070a501802c5c0000c0a21700c003911050090004075504500307107080041c2c640c40c00c200f5211703034014001d410700c2550400008505603048140c011102ca42c841d44540010b111094022044034020000b031000714400c3d091a014162003142c0686031002c09031604104448007940201c4448092007040c0070108600404071810b03108440e0841841002d40d00ca42032810041c0d07220400080d40302800c0003803880d402e991406442c01c0300d41100030313201c00d8001c820003038010f4410051050791048100b0882c00d4126001442440b4072800394081131030039034445009a46661981e050f0f240e02d41e0008000800301030b03101d0001d40d485071081c4140c480301009180c0c1c41c0004000480101c006d130751940340c2802110621a6801c3d804541246c051000f401c1008281c0164490420100200070590002601150082003c0c450705 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 63627961 1250 63626711 63626729
    0x4090206120403050d0c03110712020f01020703050903061e0406020306040b090403050c010f0507050f03090703080c03030406050603011b0e0307050a081516091809050102040e010e160906120204 85
    0x5442d1502e0014000d5000140c88020213141902400b04e03d8824030a428000c41e400d800c0e185000719940355802d150306181968030461140d06218611000203001a00e000ba00c02d4544545a21114040500b81100180884003004004803090b5810f201110000c2c0c201d0741000d0010303925103031680450090100c05488640020003441400105580003004054046403080200060418101d004080c0c840a82d154000a58107112118480d001e101c021604241c0400848114503581d9841700d071140c0003000d003960103401c040700f0041401254001c15500c1038046000f000386d0030001c0c1c070080610b4a00944a020403c81c40000600e6441c1041014041c16001308007800c0c1035910160103907201c03601000b43e0522848c0c2c9000c10328021407800d42c01c02600460315062400c9007400c40c144865403620110308840d548544540c40499401c3c40104090101520f8884080d8108034801d00c1a24001e000181c80704c0407000302400e10b41d40101c940b000d4401c82e14006c202075880da1004406030040e90002d001e6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 63629211 1250 63627961 63627997
    0x5010216111305010b0a1101021314120a0807110d0f050f0c0303030603100213030c0305160b13090f0e01020c0a110307060512060d050105070c020a0b0403030e04090206 74
    0x510494041880c01c0742001c44020b9581036000807100180d94080c422401c0e03201c1c4c01d002440b40381c1e00a08000c101100d14200050410064400038030070050b05600918202c0c4100011405608142d4906140d003900305004101d54034803940c0b140700c18800c0d688041d0002c21600402e256030341c0d865400d1480d40d50049103251007800c513410019119030222081c071a1034441c00e4030b2203c20b4180801900e02c00c200003005407541300406002031010394410211039031030104161001c80010188150756024501803001003a076406078441030284007540b50454521100c0a00410101403109580e05041e2440c144010800001d49507030000078081b280c0c1c60000c15400403540b900c20701d00004070b00c910329000719050880c1c0e00000050544030340c2e0a0142d400000e0041000440224402e210b032500410058891740c103004143d2102421180117656900c0004d607001814415864241c1c101e5000e000c0c0002104e280c907146580142c60030701c54540d500d025a849400320400c0d5590001030303603029110252003030b203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 63630461 1250 63629211 63629213
    0x3021b060708100614070f23030304050601050406140d020303091c020a0e090a0b041b06030f050603030a0207061805090c04061d1503090106090f0b011b050a0206030405010216 77
    0x30000004443e0301148900a06002810038420982d0f42840ea9248903542c1c54805681c0b40d041d1201a40c820980d078000d1500700c0f1880c24481400b91044202d0307400b01454a070b0400d8a4858201803044e488148100e05040c0140114003943d0f4090480400880c1c1155241e4010b1010034118008c010030150300c40c2030400084100029940542c1c0040d10803110701c410640c54010080c0b000d007080c0c0c1c882e030301344d4022050b203800280200e0401f07401c00d014036001d8a90b043c03c440e420f10008590b07003240300042c4e100c0143d40e9005c041d078001c01e031700804114090360400a60300c0d40250340d24264410081000309030781d1002d200344101d441c0701c0c0140c035001d03085200904e4680c0d99420b06034018400c110000d0300f04a840f02960b034446c1d090740265200206008603030707070442d0500b500707a81001d082c800465584840c0001c0c11180c5120b007018144010f4004966005203800140030038002c40c00000d4070591102400c0c00166020940610b5a607044030020380b29125424802e00a00582c0118462002400a108 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 63631711 1250 63630461 63630467
    0x301060915090203070917030d020a03020a021603080307180503030409020703091703070807020402091906140319090f05030f092b08031e0c04170d0503060103021b0607 74
    0x81c04004042446519542e041c9500c124031080b110301d0001000d040c01440091204801c4078541d00c5000c0850b810038080401d1b02c0c00702d83c05507a200d408641d002070000d00c2c0580500c1350711b8601031803001d481400783c07940d200c41503144070041100041207810305404c002e030305014103100050207018003180c0d1601d8561030010020b501c20342c019004185c442400182c0d20602076080f4039401880d00285041400e156209841c0ea040704004030307401602440044003580b649044000c0c1c108020ba8a481034503c2c01d507000d09465040c114031088034008004225030003945003c220070889482c400091007100c01e041c2602902c030700e80402003850100156008002d484280601480c407011140d4030a11079000e14140305505003100003400c0380c0d20b0a46503101255040000c1c3d41c0c030402404804010559424065800b404116680980004080b0301440b00c1c00340000ca0803004104000140f07400b02203103401074058000140f000b4100768000500c0c1d1045207203841d030348881c80c1c490003c40c4c0791030070a98030203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 63632961 1250 63631711 63631721
    0x90a02130e25080601080705090a0902060d0504060b0d0c120302030403020d08120105060a0c02040522030207090b01090509010b0705010908030a1b0306050609040b040908030c031015140304060b03010609 89
    0x1010072242c000000309440c0004103215048440020062450034079020520681980040c02c0c01969940d6002100140e280c0c540101400c003240040064640741a1610301c0481d401c60052600420b50b90305088000781d1f55107410703810751f010400407907940b1745145030492071480380f504001e42240c003102b510030400841c07402030406144035212042d1260703218000e22065004d401142000511160119030150409611042c0c100007414401260445080d90300041c1c240090001c07801a84000d07000c02520b1072034820460240000d10b0405038042c40c00703001802008042c0654202c5940c00a050400c02c01c0950201c079580e40d00503040c5449241055001780102a0300c080c100e00740d40c0c1c03000e4010119110340324000c00e45400600103401e040c900d00c1444014405260540d40250342c0f040030300041103003400918401c01d1000c2000d1395a10704440103806101c0154230142044020b600e20000c81a006441da42c1c7c9800c0814140341c89a4981c101340e4054800051005d4042d442c3c1000858107002503000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 63634211 1250 63632961 63633013
    0x702040920030c060417121902061008330f161e050a030204170d140301050a0603050601020c0a080609010e0c0306060d02010c080a080a0605030303090a02130e 70
    0xe0601e1440950706054a840340f10440c0780c0e100c002084207000040c008896100100000f000702e4003020600b12405e40f0541c00303551000191175251500b1400f070740c2e040040580c05601e40c4120703094249080b003559510380541c00881c9189202018a4040010b421034a020300030319010038200600300108801c2c14080c050b556203a051020b810381440381401600304291140088000b411070b44160002162250000c24695007010703000c00c0300050310800743c0f610142006805000c0c00c0390a201000241003508603011341801d910051004200c00c0e17480a5902c800c840850601248580d0340000403814515815601907000d0b90f00c03c0041594a400034805200b41000002000710364102e1099035580c08080c290f03994564000000a101e0f414005010394002d441814100c103a080195180d0741070303800000084d0001001c040c20407002114074000e82d4014a4241e02451a5003484082c5036220b019200001c0e01444241c500120340c1003850348888040041001510100c00c555040c5500190a5041c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 63635461 1250 63634211 63634253
    0x906070b0a0204050a080105060108070806060403050f0325080306040b0f0301020703080a05090a0f0f02010c17030405010c0302030402060d0518031803010c0306080304090f020405090c07050708031c090807020409 93
    0x181c0030400e01014030400d40110700507103400c2f03141d9131107080072103603003200608140e00300740240700c0000060000c0108a0b201c03001d54000c1c1d0380380c0c0304890f512421180b0615052201400030120703c00410306050450741c01502c151800f00e0145841400310319400d00300c9a01e242c042d0310010b80101032640c003512460140450450078002511011441a0b4070028035201500c80e0090001d0580041c84010744090020310604000280140985501080f840c0c0140c2010a10100200b0041080000e1140c02100340c2c03141011401c50410790003158690040890001c24a561072010600744041c40400184030340c07a00707040320356401904944c42280c51031700c44914029824128040711484c001e024050545000344019401d29107098407000c041c0032020310208100d82c1c05c000116968540c124828807958210081d980c8e29926850301528000e00c582c010f194075042808100074100f40720102e600c6039080d018021505501c0d0341400c0c40e017481141130003540140340c81c50407410003a078100c001c60300c506104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 63636711 1250 63635461 63635479
    0x330902030c060903070501121401082107030e0108060102010e0102030709030c08120a0f030b10050a080f0f06040b1206040c0315110f0d180c18060f0b0906070b0a020405 74
    0x414002207000d01040c1a504d0b0b000404c0500241d407080002580c50681d084010404800c48003400707441c81003c0e0440442da0b0090404182110000040740a1102e54010f0325894009a624000c0c045134000e40c900381003003007000c0828606da100b50070903540090104021980ca082c1060082c10b0210349104c00c480380e40c1d60b1a030001d01500c010032900c0108003012200c0c1d10b4888011012640d4801c0400684103140e03841840a00da40c0f18405400401c2201c0d80714032fa900c1c0102c80000e8845000200001601580841009002070708c10124540104d4140d40110b0300001c0d502c00984421810740c11122284983d00030003040c860340b08044401c481c0299440c1d00404182c0c3d440d20143c034411070b811645c0c040f0810003400315a0b0443e000f003285191a1100052801c4035403a03480c0480022282510300203029281070101c4140d10408410f803484240c41040340c24507200c885280c2e048280701d2030340a05004100c1982c141c440d81c00301d07100f040d840ba074034038420b10701000f03032900030341041c01a54001c0c2c10740 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 63637961 1250 63636711 63636733
    0x9040c0203070506040f080708030f0f0f071e0c0503030a09120c1122050a0c02060108010b0d02040203040503130f030c05010302030f0f0a02040b0c0715020309060733090203 76
    0x4021500d2280d00800504801c0d80c0b11b4541e00015400e181045840303131030030000d12012842241c0914040c0c0c40e0417040ca81d0905142c0e0312070b0300610000d03064072003908030082440007964010b549451400d502003410420314a130758030107030343e5081700300340c080d00d80d0200104010600717070b481e400b5041003440780042495001d1071000c110b4170407031b61020040103203c060410504503c0c003100c2c0030107880007000b000c0c0d5000a107103076141c055034801e5940c0c00d05141c40e900615003840d01407042c50b02400e40000208400582c0c080018240c01603084007a004950020101e000d02505004130340010070791041c51070050740e1300c090020a100780d520055995080c120408a0158824021640141d40f0305403007407140d440c0d0541a103100e2202408007010b00360308006c0000c1c4462008050528191038901510394076142c21601460780e41c1d40f040c00340454100704040d4656a0b00d110a40e96925001440d031080ca4042181180000054104200e0091501a040440c01c1215001a0301a0f0706c250207481003030b404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 63639211 1250 63637961 63637963
    0x314043309020a0f0f0b0c03040f030809090105031606050310030b0103030c060501090c050904020c01140a021308070305061906080a12030b010c0c0902210c0c1510051c0b090309040c02 81
    0xc500512902805502040001c502504094000c209032202034900c0e00e81d58072014ac6004600d9402100c008401241c0081c061418403c0c460040c0026409001c8200d2035003001481c40060303001d004203120011010901c02aa0aa40c0d400516400404041b20b0358490402a0148002450440361103003840004504041240071354143e10f0f0482d12828200001c1c607041001035040b4010b0591250368401a510304003a210f280340340192400c100042c9ea843c5020442c80014070560010b1b0807a0b0f011500804c00a040003502c9a070103a42008050000140416940050003191f40314000b00c0c4922044d4006000402c40013404003841c5440c100302c40c0300524010b559000300168007504031701800104109030025a0001d04603c1e40354041441d91103440c5810004040d0140c50b40c005100e404075502c00340ca030b1b0820800d004c522a4500001f214500590070035010170881c000c042c029000300d03845182c81032001104003102d43d4010041d907041c0c0782c140c1070107641e504100000752040c2e081409070303040280 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 63640461 1250 63639211 63639239
    0x32d060f180d02060c0c01090510020a0e03010b0604030201050c07080d181403120d0e120a1103040e01050d0201050c010903020f01050601050a140f07020a0b0a0e010314043309020a 79
    0x80540140113a6a1000000e50b12a00000d0300e5807869502c5050301000203009004d5a00407255080700161213512440c8010000c5a41c20b4203580281e1522040031110380e502e500b950304496091900c1070341c81c0c0d8450b011030704046071030703000619500c11102c0074060f4036005200c2a0304080e050000b03c00c3d2a503503041a403421040c1c2d060072601038002200c121034040d03250004080f0040946004104074511a80c01840c110380d580d0800501c00000ca201800694000b41018502040c03600031410942401d0300705007009010700c54107101344442d0b40310100316401201034a064030741c0c0700c00070400d48825050181d254580550f130a50740c0d500e42400030340c1ca98001c40c103075801d0700101d513252440003000d00341c0000c06a00041460740380070030500002e401680c0e800205c40244c001e02c0a940d450303101c04180130746103410710742c0d00324141414a400c0030010322246000c1c9500c944c0004040006c01000d81800700003801c03c0440342c5044080c00c54201000070240c00a088440c426515002c01c0365072040320600d100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 63641711 1250 63640461 63640483
    0x61103220302070510090e0c091e0a030b0a05100906060e011803020a060c0b0105030304031e1a15030c040506210f01061403010b030c032d060f18 64
    0x58018408810440c405406031410148240101c0f96443d80f82c00000e0441841103030344200003180018240805988040b101c2c1d00700083d40703281806c18510304000b460500a1444c52083e0400006000c41c40342d03140e13070001000b1504024100d1441c14141e2000010304411540301305141d544990025844440b1b10a46040b00ca05684066a2100300c0c001141c0c600b503081074001220314007401c0400540d07035100003540100200d0302d811346140350701c0c507000c1082501603020f0b44c840e4100f88810000320b40e240c1760701b0155440314281030341d010025182100410030284120f40c5404400001c00451070304048202c1e1144030102e04a906e00200d05c400c00c42561011924950001c152020903804804c005512138032250741c0c0c1c02a140c100b01c00500440c00c5410b1a400024481014401030100d0304082c400c11307080d06070a5001d00001c1143d01d0120380e40e0408860800da5042c4c80f02d420751142621a000100e02003000d0091b5010b90500909100030300d4000c1c0c5000104a1346011448103c2600045149800c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 63642961 1250 63641711 63641731
    0x80d0f0e04020d0603020901060c1b0e01060f120e0f0c0307140402030601050c010c030b101b14010b040204030503210405070e1503010905010c0905010309031b0204020c100603061103 80
    0x28500c00c82840041d40119040d400300079180c040c04401a03a400c9030b140d01801c4a0795802000d6021400c1800082d2440d01160558820007481071084805071022241942c2c8241014100d011241c4001c0f9035883e82c40d600240c0702840c0c003942c2086220042104400d4510300b070105e64558015004042c1c50380880c0c8102007010003810110300701c1c1e040c40c0d0051980214141481420a4030f00c0900394251000403034030200182e9510808009850700a0340c4540d0615146898010201074480b01ca0f03011088907009021400000c42d18548e500c000d400445005102500075500d6958070326280e680ca4000010510142900135840360507244100b030124403c54201d002010040e182c00d0b00c030010b000c40501110040e003a415009490340d10240100c001e0030740f15000018080044081c02001c0035203d41000b1704040c1415a80f60200341c0c4101001010f0030041d03a410700680c03041c03000400038071910710840110b025168150958409960200d421213014100c148118000700015481c0d922080703a40c6815 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 63644211 1250 63642961 63642977
    0x203030103110312030a06050306070302030606032a13030c08010903020304030b07120e06100b03070f1d1801080f0102120a1508070803071502030f010614040915080d0f 74
    0x420b6038010b10010a010160644000c1d481c802103005590384201d400760700d504d450380030401c46800d0810101740d0000a0345000c600b0744c20100c0000b6854400a00443c4941c02c05113030540c80361a101104540c418000d0455994428001040412501d641c0c4400d64400508481c0040c070340c5010302550394019856806189806d0559481a60b00c0d1405055401040010b1401000e600e460f071088010054500e4020f242074070b085442940985866000064036071000c2c0140300107640c0045540114503010b04000741c1c44003d0040e0301c0860700d0741014040c0d0001d800310b144140d059241c0303c194180c0e0300c65030076a00b0200d00340800310300342d20580020300d420403400c80c00030b083c0003403035404910318081e03901d101c410b0659140c00191420440360060500b9410025104040049000000700b819004590944c1907281070301034025095814418801445240300d4141585260f0804807170240c054410100421240042c0041d55204180030390000b610400b480061124042c41d4148c0c6c64003213581da81c00c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 63645461 1250 63644211 63644213
    0x105060301090503190e09100311041a0d0501110f040e13080a110c0a03060204051804120f1205010f03030e030102070b0105130609090b0703060509040803060f0a03050f0f0106080c010203030103 85
    0x343c80d01714070490300030455000013603441d030b5644842d2580640e0f07000307010242003030030350414804d02d421050145128a140071904803030926400c1076080c42c44001c0724004103072045401c059001d84030824005220351000580c003419030300084094000d45422900d50355140d030302c403016509c00c05100c1c03070040c080400034030002c06500d124800011414482405542d07041c4d0b0b1020224a00c040550005c50340b054000c1001e12207410100c0f48480400c00011800440d810552a104030262014202c44c04110421225111701401583e111019a4000038104259a52004404040215400210b0010b542e0444142441ca014001d903440700790005d000e0307101ca91a1001308079010000d4503010301941c0c4c0720a0002120b645a2003650121401518040c1d62071802000060403a4800d4000920403410a001c0c00301107088501980c0c0e0022040c1c892050303a03141d040014441d81c0b56544002c4c100d10035090454100c001c045954415a92900d0003807101546078643c0d50b80b55204d5084450050b403041c40100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 63646711 1250 63645461 63645487
    0x30403030804110a180e0610063e01090b0703092001110d030e0c040c05030408130b03010801090506060a05011d0d05120a120207020a03140115080c01020105060301090503 75
    0x683c141d0300200840a4640d44100070f6040305103c3c030b10b00700300540d2030764144c4e0000c00038455651b224014400790078a86003400c0d00a000c032002409442038400030503408040a05050514000198600f40414a040c071111103940c0a8100510100c032440c00190110780194024060008204da021104038200790301071107800c450710701c40110181000415030010104200c10701c0f048900c07000c0c170780c0c3c0030812685c035008072072400d50415129402a850300c80c003511201d5001007075a030440e034009003680d078036507408440004052441e003003044013070000030001800100551041c07140a2242c026107120f42d6584c000c0010001c00c51140038041806e1a01c01e80c80b02d601d15101c4081d201c5d000340700307480c11071a94495501d89000c0d200d001e045203000040c0441d0964000c2c01c40680d54000140940c903003040c0d5808502c080b00c0c0b500c0001d00c0300c002c00c0d212020313021083d0845a094400c2035500c41c9820b13541c2240340d41d41c0103071518403400342d46004017081d41806c042c040c107203200750008021464500040094 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 63647961 1250 63646711 63646733
    0x706050402041d030c011505150d090c0e01080d0c0506060409050307080a0e030708010203010f0e07050d05040501060611070806010303140d0e070315051009020f0409060f090c02030403030804 84
    0x8903032140d602d800401800444100f0240303420109030055444055000341d060860301c490103c2140d03401940810061981c1e50854120005400030f5050388848504244a01410940030b0050624401c80342c01710b800c441e410b40d03083c100e400150495400351a1040e0541d0b2461121a018040c3d0304240005807980c02c081d00300704809445001142e00d07000e540d8803a003030702c0d4108803c03480002c1e821032505c1d0150310301040030781c02502440e40214030f107500d055107a10800c47c0c240b080301c8031104c854000408403405141550f030070034480c06003440140380500e44240280f40502503100454142030502c0850a00050540141d5600c80c1c02400564215101550710741030120664a40300f40801000e4940c5140e400740b003134885120001040c855041d843c10350a485005400d4a041924200810800840140c2c0103421502d40d1440140c1d2801c0703a05880d034151003940c2009841600707000e800149030301101c43e04011114442000c100719101c41c03408984a1107039100203000508280c003c00c0220b03200c40d60b5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 63649211 1250 63647961 63647963
    0x25060c0f02190909050f0106051206040f1a0a0509160b09280303020604050606010305040b18010e070e0103170f03040305090d0b0901021308060702190c091d07050d0807060504 77
    0xa050a12a6260099410b403901c0c0e0f101110541c00120122030b19100234001c59001d0a400c8a9080c40268039074401591814010806004040009144014090803038200c7d01614046034000c040e074034040240c0400360009440b94a40e911902d01c1d210200f04c260200130b010b50f0824201240b5007800102000b0541000b000101d4600300070583c2005a0b44400803440002c52003a0040c00d1a0b107014204542405801070100f030505041804100015910700451580301384400c0304c850342e00180e408041e00401040201d02c559103d102c1e00440c21207642e84045040768410303c1b841085005222102c040d500a40c0068000c9003400d2021400190182028240c072000c05800200070100b2500c1e01c510b100c03000d413031b40151650700181658800b1106080c100152500304010051800c1040307000350380e10103042040410040f01c0400c8020800b8002d4540000d01001c181445845004004150f01e1284d1081c0043e85105a88001135242410701c10320310800e4001d001c407400c01480d600c0f110081c102c0100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 63650461 1250 63649211 63649249
    0x91e06050c0f07030f0c06031406040203090c100c1401020a0e06030a110d1e0b030d1103070605040b0601110105010e011206200415080906070e03070825060c0f02 71
    0x11102407850002c02c4402d00450080351030785c84800840c1814041034503160411420103060030080009655080c0c5082e030004c4c41610b006030303030780d40c0c00b0405410130301401403c540c00620400356a000e181d2220b00a403107580a540280e00c0c0c4900000b405080303200381c001d031034017042d03014498103010301d0000050350717000380c0d180c2c00420301049144511149a210944290780c095035000c2408414800d5014540020b40d19002080149a44070020369542d0403204034400700300034450f02480002c414010303100005e520810a0115003030900e44040e0f41070084a01034009084002450350b507a405000307503070403a03042044d00707139140e42450182005c40e2140207042d940349071180d000e8403040030040320104500c00c0a0740c02984880c02c080c10090400316000a190401184400f44066003d01164441d0824014107100b5820141080441d0420f03013a50710000c2c081c0220040d0300d8114041840340101c02210801444074161500c0090710700c1004e0103005048401c0303801140006081007140081c070100d801c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 63651711 1250 63650461 63650473
    0x90504170705060106120b0d17040302030703080909060603010e0417040305060f0709050301020a0203040b0d06080d05070b0703051501030f15060c050d020601120b07030207080c0d091e06050c 84
    0xe205640d80400070403151684040c00400910303901c001d21030710408445506101c18a4144006040c0c03040c580310141c451440c4448803207400c0c807901c04440042d03601030280c480840e9207003080c0c01a0342180203214010f013844800100940342c54011241a1105c0209200240e15980c680307207048882ca20060400800400012011410810186110309800c00303200c5943c0c505000e0003001d00d14680e100030f01982c0103100c0503905980110070349050381d00400324992644401c0d03811401030003c99004140e14000d0108404030307258040d00804455000703204c3e46240380c031404000c0b411200122800081200e009007800b0f11580301c0c0d045a45215903d03800419940c074005220a0034204690040c0042038000000d9810400140b1028481e080d580c0040c1c10603624084074140344c104041070060450441d08000b0316068000e03070580c2c909540200010352940703612851103980b07120381d0040d000420204480052042d10304c0b0b50f1184d03003940c0132030200f1005241204c10707202d170303080001c031815140121 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 63652961 1250 63651711 63651743
    0x50c040b03070c02040f1b0306140105032502210a050f07030903021c140601140105070302070f060507140601140409031106090a0b0a0b1e0607300513090504 69
    0x40e001d200006e5020b80400160100c01c045030700f0503810032501c54024107003000001c00c40e03c40700e81c1403e9140750003030908603525603a0380f10784800c480d0f16111003000c01514050500119a001130741400c3c1d91444407041d19080c2d010307400071426015001580700054000c0100e5420401502c0c098840148a82000b54405841f03500084004003280840c440c000140d030859418807041d8064807000c0c0030b40c00007510780c550501100002c0c80945640003030502c1800954001090310030454440105003003400700d0252520b401005152f948003000965103d00300c0c40070600c2049020903414101c507403a50454a1000c43c610a010140c10307440d01c19414042c10311604c03860036606102080c0300d89800301c0900781c916400d00e05580c107a40e010b41003154951900181c500b594644000420004200c2003d504100035010005156442a080020440444100c80303003100c1070f58411002d07500010f00d00c4410009018101240e040c002d00b26a8005424947c0e0b040010843ca9800142c2083c041e0b050f85520b030840e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 63654211 1250 63652961 63652969
    0x10f03021303030e0316050a030f21020102071505100614070b040503220f03020105180d030207210809040e01020403080c07050a15020303160207090c020c0301060504050c040b03070c02 81
    0x41a4825004510f055a5013034841c9020f01c1240c2100581c0b8252400480c01c3c20040b030f1400c0164080148416001416602840071441c041244526411030780448500f071b000001b4041c0d003001608035040902a55076050001c11402402d01c201918114030031070070b2402000701d80299005480b012807031410000000402c07094407a41d84118022002980d50719401d001c02001c8119604882e170300c1540140040c03106034041c01015003100e409280458540d0024401c81e00003210600c0629800a908600241055000f0580e04200c604003102c52811030244150014102403d07040103100d40020400071410749469400012203285031400182003503103036030311820b003640300c15000503d070345c0600340403c0a0300e410f56201018008200c420b482c0b81c0141c19020b5038a0001411540301420794a07000c0156a108001d014001c0490b803500744100c4c14074042c06501c8003644d032103940c02035003440001300f001c0c1042d00a007070088000796107003890b103484d00400000ca50005401e01c401c001c9154031031405665 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 63655461 1250 63654211 63654247
    0xf01050d06060302030411060c19020303040909110306010905100b0d0b030a030c140c09241012140412050d09080d0b0405070e031905031204061407021605010f0302 72
    0x996140141e482c03d0038200700c460308101d40325071f9110b00000c10074481003070b0001c1505040c21112a08505064245100007400c600894110b070402500d0701904900340070070300400c00083c4034103030b0541e803060340c80d92080c00690740c045480b02c80b44081c0110030002c28000c0001000c0f00c1280780c074001204026100049e0914003100c1c010b50009417454100010301c115140e800d0420f5000380c00401074104814045040384200900c403c85103808240000e00c5440549480144181c004150705210302000d84007408610801e0a0001c0540c6042c0c504049100100c103032a00030342d004002510804845942124241e00101c0054441601c900c044400210780f00050f00f0111001d107800300710345040600f4807003201c9008140c1010050003140916103500e02184a8404100381c4106c10310820103414018514030405850f500c3c4a8400340c100000d004a4cd4010104030100c08011405612034403000ca82d507522b010303502c0c81c1901000c0000c10040d8050707031100c0c400351181d00f0090308258603650f00905803a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 63656711 1250 63655461 63655469
    0x102040e190218010c020d06050103050303090d0806092706090109061a01080f100b031003030f0503070906030f1107030804020310091e02010201020903030c010b010f030501140f01050d06 82
    0x10400303024429140c0c40d2865040d41c06050050840c1065240314481111804800080e414001c1d02d203020410354441c01c8411203560b80265050101b540d417403401d60f03903c3e84125401000c50141504c410440351291200a0181074020802e01e42502c0c3c01c0c0808040900340d41d03090f0b0080010310365090220009200c0b40c1d21900140000182840c4070741441015034240061841820280480e0482c05030707040507211f0380040d5048902600380d91443d0200002409541011000d07410100400c031f8003014140c254000d491207542c646a5840030f0080658050201351800030101d00088024403410b48680d101c4900c0d81c0e00f82d0030124110140c054400780a6104180c00c6d000120840c0801c000e606080003100b21051504030f0811240147c2d03201c6101c1d140c6c1602001528120b50f045500035603100750140c038004080202669030f1880c05903043c3d4003d0501501a41c04541401c0120188074024441c050490f6080c50604407003050750000c0040c7c2c801002d540c903042c004148003040c0484130500c1404064 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 63657961 1250 63656711 63656729
    0x130b040e120415050307020a060902010e0301060f0302040609060b030406051b07030201150b03090a0b100f1701050609040831060906081b04030206160501180b0a05010501020705060a0908010204 85
    0x2c0c60518244960400c12241d000041c400100284011180d001070781e40207568025400140d0000d6600c01207590044070509503078107609242021424044c20004142100d1086400304203d0355a0814801581d00506c80e030f2641c0442480060080343c007582102c0e42c400c00d00c007600326082211001d1795107a500308280940042c2c0d51900c08107100000d8820707540140c14030b19811415845c000519640d1401e020b000140070010f14000700e41e0701e05103800c0740700150070303a0701203500b000d41c9400f50214542c1d404104215150708001c0410b02e14203180380c005000c0ca030001c184602c1c00081c1055480740c1028160007010300b850b003c1001c56102c01005485025290b1036443d01603c502d0100d00420b04000542501550451100708081c0010043c08840403658103480c56074441c4c80f00101e03003407100c0914402901035403d0800b10b0340704004000410340703060310601c0c1c11521510713001c4d000f9045400900445016170300000c420300c0241340c8100540001c1d011450460429a1a0800c03107080e6000703a4400d50007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 63659211 1250 63657961 63657967
    0x3040509011d10051003020a020c0a09020a260f131a060a0b0408070e060114070501020d0501140901060503090f0a2001080c0f1e0a09060914130b040e12 67
    0x2030300a00c82551508034007880210540340741407000040c817800a030410201419400140e050800d802441450080000207001c1880d8903504d615000103580400c0c1744c00c00081e9207014003805420708850310040700248c41080615a511072900b0800054041d003003145044500155500003428404045d00760014081c192a00d0f041078401d102c00602903805c150a089000e00052000a4001400030104c8802c444000040d450310401a180c03192200c104158045000507004240320341500288500c0c0300c1c510302000281c2e40d03007500780c0c0a4850301d0704440c0d0007100d00d00104600c5102d00c024581010050054a1101001035030440c5490380340320301244d1302c04100d541c0c403801c15030b80c0e15214500c2c4002c0c20000d06a00e0284400300b040d01c50401c08803044500814002c020342040c205a03840c031004c076104184e642d01c0c0003901034841103041c070460000844170a070105011018a200c0082510058001040c80304104158001b4000380101c0a0f04181c0d03030300508400241c00c0042401812941e0f8282e0b40d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 63660461 1250 63659211 63659249
    0x4060f1b18050102190b060d02090403050711040c0e0927060a051506071e0611030f01050f0105040302040b0409020d0b0a1a0a0b0304030c05010218040b090106020d050304050304050901 81
    0x2a41c10705a10103419504040008101c3c040c4084c4546a0640d0018000c00c842d61500001503500c10801000303900400f0040801041582040007458501d0288100c00c000030802c100700030545905070b102800103074440d01c10403594100152859000441e8240a146491040c0c410b01141c40b00d40c61701c410301e648100284800c460080c031031300b600061204d410701c1c0100c032044040740c05886603000052004a0464008000a17000881c07550a150305c001e0500a9580c41c481403003042c0c2040d203004101e0b49042c1300001e0640f40110038090012010707100d150605103075070204001440001070710358100c4d49440c2ca000042e50345229002d4013502c900b008510b18140701601904a4110500301e07010348946050480c0e40c0d170340e0004500b080364540d01196540384e44070b160481d911030804100401a60010401c0d40e00d01d8090b1005903000d12080d0b600f085010a140e0411004080030711404015030012086268241c0c0705000540c3e00a0280c0d003141d10b8140d8420125000c1c0e40c00b60f1001c810034658a10a04e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 63661711 1250 63660461 63660497
    0x62706050109020a1e0e130207050c030a150b061c02040608010e0f04020607030e1e0114042417090102070b0603010911090a0b040614010807020d0804060f1b 69
    0x540504541c00c400c609050400c038003c1c101d8030843c0c403c5401c060718144004100c0388220446224040003400c0f006d07c0070501d0709900c01a4000c800304807224041d40b040201103040002c1d05404854111403510000e034540a10300b401080c0c803046143c2c0000080000c0d00c44c44902c1e080ba41500c00c0f20001c0181d503986441d60013000040103130881c80781001000180403000304230f8103003660015012160303165240b80340e28090f504024455040c90700030721030180ca2801c1140400506003010030a0300c50404c500b0350103030070f90f1051055018030b040203c0c0340c078421544030f400d103891102100014140303c0c2402c40940144203008100325010a400d031f4000412504002e04151241e4202009500a102600f03860f40c401880d2600302200b5400f400541001950000091300f101c0c0e1380703c078081d10800c00c0e1500d81c140c40000000703042004c0d0201c0d401c00c0118003503500c0021043c4a040f815641c4a4150311940c4c0c864029103000141d0030f200350b4582c91100203007a11040c001c900c1155a40340c6411800c02a40b20f8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 63662961 1250 63661711 63661721
    0x80a0c090501150e040b0a0509160306090207050307110a050a15020d05040311010305060a05120f0d09030f03050c1c02010c020f03040f09090501110313050709180201030504062706 79
    0x3ca40740703010b0300c1c8002003540000c0a00300f003201c22140852a1007026000c5080015543e1100358046a03410a0100034040b4440e0069505c5c415a000d00029842d1340010082e88103c03040201164010413520012900c01d01891024140041a540c070656407080000e000080f10341050310b03003410a11070340c40f400303804019007000c506042c20414202031075038440d00321004602005034141a11400000c804d0b1340c1d062060000740c403000308a04400340c003a02c2003e80d5030403a406504494881c03596229426801942d041080701e030b100c03800401c12406664100c41030342221030140c0092040034050740000f10300583e44000c1c941c2c2680001030b5856080b1009282890128031442c550700200024080841c1045000064031100b420215800d030003071034046d0041c140c1502c10f518580021007840010311140d80149041400342c0704903071010b5281c030300c0300080303039800c40032240d244bd42c4201c0c003001540a40c0010340e00c1406404002054804003881400e19985103501c426503c0c0001e102004000706c038419 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 63664211 1250 63662961 63662969
    0x8040e0f100f0605030106033602130b0f010c0f050613020f010f0801091802060a050301050112020310060c1103060711010c03060b161403070803010f05030a05060601030213080a0c090501 82
    0xa0b100600d16004003c1c1c024403040c02120704054449242d140e03000100803000c40b1800181c2414028514081c030200c4440d810270714100d114401c01802c44054a030305006103001440002c144400d2250401b00540b982014014202c0f4100d4a43d105480483c000744803040c41550b1151040071452403070310402a20a104560441c18460308a0403c01ea0583c1b0180307603070641c0c0345008005403d0b070b02c8030501e500140f0898002076001c1c800150743e060840d4008080c5041320f02c00c0c4c0320200d01030300b600d510740107900048038460300e000c40700c01e02004f03c98454107000c68820b01400141030701c080700802123820840102c403040040f410311355451440c03003024402c03500140b800c0e00d020420141860b038901087e2142c8150410079001c2220303614148405846074401c8041c190044030390341d41080c6809000c80d0024405c020038640400d00000d064100841d461040541c480301505050ba100b01c015002504001c1c09129190070082000c1510801000340440c1280146c0c0110030320751034a981c26083d02d00c1600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 63665461 1250 63664211 63664229
    0x605011205040b04120207030803010b04060e0126100512010603021f090e0604020c0f0c1f0e04110c010c080a05090703080403030f0519050c010b0105030105150708040e0f10 76
    0x10402c0007086040054035003190780b2040d2240711040381c0c54100d01e44480c0760000713810403400200024041c1e0f4108010400c5480c680c0f22090102007000c01528042e205c1e03403995200040c210005090040070600c2598000303001800101d0140d22003003c10200d080030844203140380c0d0340c1c140a0044d80ba10203400c420030341c0d910740502100450000014040e100f584a2401d0b45002d07900400c81c1d690300e6030141d8100c0308610040f0b075529403a121605948958500819000301440720a80c042c031403444004003480c6580b80c44440b441c2d441e86081c00010480f1041c4440d6442003801851003444080c05081700c07004071565040903506003d10004101d44020740f01e880d1a5001c0c0700100001031000f42980c0490343c03d030405001c040c03040030094925100d82c0304040c03401002c0d0b030702d01540e4540000c050440320055200800040d400b1000540359840217000e05070340301810740c40740780d100c410207002031006070700c50b5150900f46980c070b499000031110181d400d00c500340e0b00d030300030403a0740440c0c0b0f40c2510041c03c07494 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 63666711 1250 63665461 63665471
    0x301060f0b0909090102090306041b0803041410030905071e0504060e1b07061523011d0d05030d020c150c030f040201030912051801140d020a020a0b010906050112 71
    0x31855900d20441c074481d4055506200001c400c0602907051f1000d502019041c3d9641c0c3c50180703000e25a8105018840700204c65034800171072010000004d0341d050326416140c1120100e80002045001002c1c003105d0b0b01095145e07000039000803414401d0038014440b0700800c0701ea0040f10744070f05c0c41d409800d42000740500d1502d40c01300305050715800744030f401584840003850701054207007109441c0d120710345004d0700d0107060182c03203c40c140c0d221001c00100d5050892000c0f04000455200e881d81c94292402c90005007146048141318a030712009641646c4001c020000114090740c42504541016412041e02d070383c04210f242d5640010303ca42907a050322441e804000380b61480301903c150101030081088031400900007411640a035000b113401c16082000c0071045414084010300b180d020b191406c54014039142c0c120501e5005031010840a1014803a040c24041c1c45d003403800003500107215480440c800c007800c0002007441c003800d99003c2d0030041800714045041400240c201302c42c0d0400d82d0b122078640 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 63667961 1250 63666711 63666719
    0xc100503160e09040b0c0d020408030706050903120c0c030409110c07050901030b01030b0a0f021206031006050108010b0304170a090801110315120c040c02061602031c050a2003060301060f 82
    0x40b00d03c0d40d0081d8040c202c0b590315200c0c520404054001c4840301400548002004900300c0c80000160160f00c3c86124180a60b40c0d540c03000d0364581c0643d5841c02c40804204020800c003075400c0016100624500e4222420980d60302c0b8841c0556080309100c01500c50005500c00010304280410800f402c010381d0781402c2549542d444855072203051001801d030318401c5010a20024040d007004043c1358140c0b1041d521256100b17540c040a800c01e030b84180c030920405007003e4195400d0f0245104640c4140c50f034650a070f20308004c0880c1030307000810031114907800c02444001c0302c0d41900a003072210116038a003c4210300305a00c0b40d0031a00b186103031111481e01841004032502e01c210000035010000d6400b01c40042000403250b02d481d01e03c0c0d0b409a481400c21000c0b1501b075600040d81c40c42140d1203002c040604100020a030713104c1c81107000302d06042e4008240c180d680f50b8207821464010070882000103801044080450714642403d08004c03900030004107102040c60240a000b002d8080071b0a8590040e142c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 63669067 1106 63667961 63667969
    0x5060315010806091632070c0905010f05101106181b03060c0a140a03020c060f1501030b040b0607050c0a0614090d02030c100503160e 59
    0x40000308036113081445280075900c03031801d20b070000511050484110603a030f481103d40e803078408062001112040c00403a4040c40c0034010548031300d85464419955030031640260205810140180004081120150b003158803c03100c3c13150301c00c100031069611300500500c010346070290b102000325003000f805000308030200c51001d80f019407a010141d5019481c1d000c24132070b056884400003900300c9062500501d03200c49070341800d0700c103074940140e40d2a003070780f0044e408000a9000f00d04016200402c104090308182041e440380d0080c40d00090103a18488490103c0b41059101c3c40c2d0b500392501e4540c040d00001340040c2040e955940141040e82e0740302c07040d030410342c000c6801ca84001840c074410991002084244d1801a00d002d551404004a050f900c0c030043e80d160242c000ca01d016075843c0800f07171079041100d4940c1a128a0400780c1c4440d01480180e00400f4094201c40b02001962 = true := by decide +kernel

theorem cover : BRFrame.Cov 63489211 63669067 := by
  have h0 := BRFrame.cov_init 63489211
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63489211 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 63489211 ≤ n) (h2 : n < 63669067) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
