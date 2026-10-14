-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1619
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:53:57.59452+00:00
-- url     : https://prove2.me/submissions/2f2d8b46-bffe-460a-a5ca-12afa8a8dabd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 291007194 ≤ n < 291187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 291008444 1250 291007194 291007231
    0x90103170723010c020f0c060315220c02060f01080c0d0311010608030904060603060e0a050a021e0a110718050a090503040b0a03061d060103090303111b060c0f03 71
    0x1105a0104003660b42d6080d12182409000e201c81d00038200c0200580161040301210b0504800c00079a1402000b0007900c02420360300c550b99035200700f014001e2425880140220000c41c503001074100c88140301d01e200d00104450100740c00184c00d02e44094104080b401900b40140a1410002114001c2c198195160780d1048864281103861040c079000e01081942000d01c0042c01c004008091702212501b1541004140e80d10750b010b5080f542c003803150010002000303002400c1400d1551005900204091000d031808a182c0c5008040c0d102455a080d50900d002c50201c20890340180401120504071006280c0c250410001404107074003481e0328404a62140700140113803d00c2d420075540c05a02c6801c49031079075165400d070701064000c00c1030080080e2070702000140c8a10796480d0142e1000041c0398a148646401004402a1046840940c01e054461072100c021603007540040030200c81c54107150080c5881843d54034180301001d824050203030720600500240742ca8981c2281e07004400b005e0031494a00307 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 291009694 1250 291008444 291008453
    0xf0108041b0605040306061d0112030c02060406260405061305070e0a0504150b0a0b031e0a05060312130501031d0a06060e01061716030b1e0f0901031707 67
    0x800709640d08400c10702107440051140d810102600940344a030105002e42901e92080c401172100300500020745441d0340c00104845414444401e01841c00303454040070b0110f86401060a690255010304000340005421039100121201d001000300381716144c2c80c01380d04094907603070340e201805401001c40701d082d02000810058204035020052907031000c01d042c0340c070700b1181030402043c003110140c131501102e41c44081951941d01c918528000000c180c2400706051800a4009410080074070941903407420000300124140d44946100318800d4070f0100381c9180c02d40501d8201001c03094408070303030b203000e2000c4140051680b0b85001581c0c020718000403e0051104a084190103600c05603010740102d0f6140824842150041019941348402a0000740d99030481203d001780d0000e04015400c00c1d11000c04e85040d9040c0c084504008a85408924403502000066011011581c0340c00f11040c85000320b00981054071030440d50010403920018950325588030440308031500e410484641a00054100420 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 291010944 1250 291009694 291009713
    0x506160b09060702010b03070803030a050c0c060a0c0e0a03150513080304030509010314071718030a0c060506040e0a11060d091101080a020c030904020903070909150e06060f010804 79
    0x5410280898a40c1001e099080e10340509075044401942480000c2880d8100010000c044480484c0114076554440c42e00100820003d01100350840080210f00e90011003044800e004e21403080c800a0031140f9504003500039104907811500420300743c181040841c180a00c5283c2034800303280081450780d100d02c0414a898600380d0b004017120b00210600007856071040180000352000e0700c0400804680149044007000220f42c80c40000300c401310007141030b0f118641140d41119459007400b02c82034071425040d045400070551003000600128014090206034040c0325000f60f01514104011030b40521416242e40d10290050100030403404450303115280c0b44200d6564048200d004c1005414500d481c803d4580c588070502d00142803500410645580c9200721108001c1c20f40096241410600034800603410030701560340d240c01100e40000b2304515070300078458402e105120101401d034109803038004a074407010034484e042c0e00a0041041a07100e082821828400034248007002c1e5881d0316003030040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 291012194 1250 291010944 291010987
    0xb040501051c0c050c061e0403030b0111060903130f050d030c030212030a0515091504110909070513091b050d02160c080c0108130b09070902030906010315050603070506 74
    0x20185860510f0f03400a0744074001d03240f00620301d002c0d5809a02c90a50703208104841e2290284a9040d00c004030700060301a9010718071603034060424048900075405400d0070194210360500c0d260b0000100403110030000303548080070f00b509803d000c1101d0708050200e9402c0343c01120040030301465803911402d2600070840010342c81ca00b42d4007180c1e6442c10031603840c00740500340d41c0e24071981040840c8100a18000004502c29014540d045445650690401029240d44044124400001c1141d0205d6860381d00b902da120b4083c07a26035030fa881c07031000482c10000c040340c3c4c0103440300c91804030000c440b429090305545100d091841c02d240c40703400a084a1000344154003c201d8036208082c168020041c604003442c1c1140c1c0403d055801008101c00195a070000c11118140082c01c008490b1000880403a50545c104070300c50200d416041d190f007001c8080364401c0c1c8254490342c0c040341c010010030800110001c034002d440c1038180b049003440c03c0440d039a20b105005aa10483c40810603800000040100c0da12 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 291013444 1250 291012194 291012247
    0x108030409050c160305040608060906091501030e0a0b0106080c0304080d0209040e0a0b06030d0507050703021c020901030b0411010c05190204020d0c080a15030c180f0c0e12070b04050105 82
    0xa00d44c0c4e58980030b452940584144400311764640c001400501d02007541c944924130140c601a101c0da1940b02001c0c04082500c421414960394001003c0c511504101c1c0b41591445030030064a6035061002c06024902d00405401c6901c1e400c2003044001a1140c0c180c400d02a01d182c2c0160f00c542c60100000d024166404100d03201e84508a20103003484141c0002e40c1c01020140c081d0b407064811440d0480d81c40c898068054802c2e88110b10030001030070300041e88100928100c100c0244010207500151818500f07910503240c0250700b10a000600c03c50445800206009003002065500b4554034640c45124020018040360344e00c1c5c6a94043d501c444c2c040b15203526492a00b003200710010580500009401e96050038028a0414040d142990410398a01680d800081c4200b92500d08920f414040c40300014a03012192592404e000c020440d000d00130004213991100c400582441082c00b9040246000c030400c07607480440e0070444a00000200c40c2034520a10f03040b903a50350b490040c1c601016100c8a80f10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 291014694 1250 291013444 291013477
    0xc0c080a1b080d140912090607140615060901080f0907080111040806010b0705150c040b030709051e09132a06022a0103091a0115030c02060108030409050c 68
    0x1e0402008000038032003208808010000310920540e407042049040b2020082d41d400403a240300b4940c0104040c010b2204010035845c50180783d80e5075000840050100300758581d00c03d02c14006155103002d0b00141013401136440318201003040000800446010740f2882c00d030300c1e031000032518007481405413801401400d0000d00c1500501020400182c1c440c2c07203602c0190103224004504504034900329150079800100402c030034040b902c41725a0800020303080742c44c107040400c8009151100140594070450080e1140c110051428052200703080c650080c8a818070f1005041d4240d681d10300c00520741051000312904449841d40c41d2088411200400d414007980308030301d04030010408100241c2c151680c070382c20785184440d020803400603880c9109403d110102c00744262180781d44a940005c1c1d1040c09800941944100075508001418081c0c0007914801c500121030040c1c0d9800d402a591280200c4c4000c2800358941a94503859005500410140302e44505c01b00714110004030035140140742c00054034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 291015944 1250 291014694 291014747
    0x80f0a021207021e0a020307031b080a03020109021008060d06020f07020909012a0f08060a0302060d0507032f09041506050316030507120f020d02040e0405060603010c0c080a 76
    0xa0360301c0940050660f04c0c54456120b882c084c0102107420500e59902800504c1c0003401d6540326071805e0100c5100d04085d039204000000c50340300402041c46018002d800005618005005006226920664800a000c60300e01803261544948003000c0700540c20007001612151b01d031400c4803940c440d0000295000c000b00b400d0003101c20040d8082d541d60b00c5205489204409850301c4200300201070507203840828400c06106514900482c0802d40c8110024031884006803030b64001074064003c210001e02c416510380400404603058462a400b800a40c00c88500c264401e8154550030160384503000188200030034080355a88482e040104100f40104c021003417580c0703c4000500e19001228020200386020390030490301402481518003e21480e80c4944004070a26000da0203440c004d82240c011542c03c20006840c18018800f0f0720160101c000e920a0303905003424001d250040103044130b840b0fa4508080985001d170003d420030703159544241b880c0c1d03d840d02140c0c2a07941c6940b1241e9082d88030b6504092 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 291017194 1250 291015944 291015947
    0x200c0409080306090106080433060803031f1202060f120405060a05100509060d020109170a0201121a010815040504060203070206100302060417100e030702030616080f0a021207 77
    0x50b6120761002d0325011256a0784d10000c4400c40400c1e01c0151a5000310100c0e0628403c0078807280300201142d84c00c500d924a402d0800f07104a81b003581c4500c07031580010081c4846071203240e66012025080007002070301c96051041a40300e2000c5580020300c00c50000070080c03018241c61040e12501e0102d412002d4080c603103802c20725201c00b42214035141003480c00c13000580741c6082c980720100395800a03110060550301d010522010828208059040c04581c0038001028100e08041c07041128014004d060803141a200240c880c0c610b843d40c0c60841424810510131607a468001c18500903400d1800e0b194585911090fa1201161030001c29046030400041100f4802c05800075801001d09a0803102d041d9244c509898041485001c0254000000c110070003a0102d102c000c541c01c414000262140c40b540b02141c03d040314440005d85a0302c4d0404108070007985404d00a0b16481500303040705810340f80309000020714214005142c0d200703d10320480440c0d0442c1c015416199030203070090790f284e8a810401c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 291018444 1250 291017194 291017197
    0x5031c180c0302031203330d051f140c0703050403050f0304060e1c1226010e07080906060d06062112020d05030a0b0111031605060a0c200c040908 64
    0x10903030107845048110440e05148400b00c0e445100811422042c0078240c14480c511f40f00d6081080030121a1030b00310b101c01d550381c103552011280c450401840040c01c5401607203540021800240c0e840361800d151045c140e10701c29030f090fa0214000240d80d41d51000c0f840c0c2590b440c003550b0009401031041da14010300030440000100140d400e42d8417044d900039041d02c1000400c1d200c25200e011011500c081e45000100750103442e41d444041810076824034030348555410840480c000040340781004090040040f08540b04c1c1c4150050107d24015001d450b01300ba402d0355403000034000307078014520901c48405104080d072201000e060000040070301e4600ca0003c1241c0c500e8041030a9411420000d202c1418500016400007450042c1e200c0710306568030000c80200030142c2c0c1e10842d050041910f110041c5c00d00501c001c080c1e0441c698001c1101081606181c2e00d042c20050403500414513005400701d5040c1c002c0342c1d0306d1486240c130008580102c00b0607152810030036100d1809400c00d040a00710000c0014000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 291019694 1250 291018444 291018449
    0x1212030a0c020712020609040b010504081504121716021f0203190c02070b07060603080318010507081b0325030e010f02070b0c070c030b0a0c11070305031c180c 70
    0x1d0890f1016a162008220880c80807500250300403010480c001043c00d00e9042240f5003441410041d0605d580d4002c42803c081c142540c594110f01c03503408020400101940e40c1d00250024a4100d8490303c10361a81d440d13280c0060041d4030200c1c0384108a405d141d1003041422a10f050401072404002000185200030350010341d4017002d80410304040c00481107407031094214103501e0350300a0540c00d02d0441268841d50021009445491329250003001050452006601a031015001200300c0180c5a407218215a4050200d03010001c160301030119006c0800603004417030345180c2125542c1e0319050300400303800840440d00400c107010040000f40e1290990b00c850707441d10050000b40011b15448660784124031540100408068114000c202d991080001810000c1d1245201034004c6403652180c0c03007031690445501a04070303103a220792803207581e221302c500d402d090f00a001440d1803404c5554458503402001c4041500c8155a000340c03a4030030207900401e401400c20044440d1b00c0c080e600f80035502d55502d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 291020944 1250 291019694 291019697
    0x90a031e0516180c09060c06061e0f09020c0d080a020c060103080c010606050405090a1d0303010b03040c2103031503150e0610031203090809090901140618061212030a0c 74
    0x1d120100b900f645000b43c0d1104d0149550b2107088174101401911000311400044ea03806a4414002ca09040c41c006032285011300785041c0d071203003441c2c80d1441010340b0746030f004140054014050540d054a00251402d072980721410203840564821200d480203000382d0010300c6051060000000034044aa03004110412821000f40401754442c202580d26100341d11441d40c00003030b80c0c03000446000080d03010346626a4103200300b446902c06c05400c541341d50030a07002008000c20020900c420004641050303001460001c105110201c413a4241e400796100c0301c60040c0605403075400814080b426600c0b920080c0d80e001140c0c09514460008a5005002e0910144041c0c070945010400c1c0b0b0300540d80c1c500880754030101c609900b8030920006c030003a20005000321503e04060110151540c1c2e00f447d01c40c895503c20b8000154150041c103200340000b4060304003802298542d660940c0d44400c100348540c8090244d071a611040c03040c5110a2800d03c20245003020100c0200c2840b10b02c40c0035030040000301c0d805 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 291022194 1250 291020944 291020969
    0xb040f060c090924181b050307021902030a1502040909080912070503570105030630010c0c05060c03190c020f0f0a05060a02090a031e0516 61
    0x3010031100ca44c030618101c03212001c1c010400c01409180b60300010103030b04c0d0300e0000300340648402c07002d520450f072480b00c00e000300d407001c01041413003541000040c907038244000910381140351a40100762a80c441c2c4030302415000d61004034124488598044800074407100c1001c009080c0c203410007800355005110f84a1045c11000182201600005401c0040e0b0344010013070509070070348010310140e400d03126000074107104508001d0501125412168038907e030341124041120700d030101c0b003501d5005200400c18103010040c014004141c1302c0704e0b8141c01007402c0025803407211003211004074000e5400c0c2400000d641c01c1c9021681c980390b109440e40341e0380784242c0c125140c944034120b5800f26804202e451031b1003100c280200310750311302c2e9503040403040c2c56039030040d0382c80c084c0c60405141c10001d043d4411101580103a50340310410208002081e80144000c8046050910400016030b9804240c44041d003440c0302105002c110f9416a0002e002265202d02190b140380d8003008400c4400c0c2d8179100d8840301525 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 291023444 1250 291022194 291022211
    0x703021003140f010608070c050705040518010f1b140c0106090207020a060c02011409040e0d021b0409020307030807020a090204031a010b070f0209070e0d0b0603010e0d0504030b040f060c0909 84
    0x1d8440149040e1381d129151b621250342c1e0361004450a894101e02a01c40f88904200012030b9100c0380b10700b5000d5090710240e003401c210800c0c20f1600703486203880580b141070710f040c82030517844150400d00c130208449031420514440070b8500d40c1d0382900030140780b03100e5546031003030000d040350070303a4010004688256142020142e5841040c1daa00d001014080d002c641d06c40904849612580300404041400400c0010300700704000000d807030031654650410159020f0821080548460102c0c0644820201c50a110342904c65000c01d807611082c2c8001800340102091a004556a030300301c0e400074040140c801c64480360340e070500d10300c0c4001c200b2103016144071580000c500c4003412030807658160b40202c6171110b071441d00d6090140c080b50040905081003200800b9030002d99510010ba0b86560080c044e41195040ca1020035003184d000c1a01c0104650058400e0007000d03400c04255421207400c0320001b03985694a042824204d10784480c02869a0b1510600c030801a8124215a0030345443c070340200003545 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 291024694 1250 291023444 291023461
    0x12020a0b0a02030f030621010b03061b04031203180f020a0f0617060a0512070e01050306010f06111905100f05011a03091c0206090d08010f0504020c070302100314 71
    0x104155038640142c100b04552604c416004000b10b4100d600503208031128a030615150411008000403400565100c0085d66100d1504008440d00000c00304c00d0141604010295000701e071250307200090800c034130f00f1490b5840c00d010780c0c00706000348030301e14040c2c06141103803611000001d82d1000403481001e42c0e440100c0e055150090540941d95583c80350154500700384072800e80324400818542d0302400c1200040340c4c0d911807100307140b078034161b07107000340381040c00c01c030038224a0314050304024042e9000c2c0004001140e030b4698407038215145800d02c1c0e81d00505072140b80341440b00c845014030784141842c1d8948100321002070800000d949240c020040c080c002c415000c03c1e07840030b01c180c0f200003a10b481c2084884621100075034100c070b2074100305e450117426840520314108107447d068015030000000c003c683c00090102900e070b0110703441c00d88820340c1003407807520440c006070146601655004c50f460346210f0342000400040d64005100110021150300d0041c09005810880c210f10b04001c801b2800b0072 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 291025944 1250 291024694 291024697
    0x20a051b0a05040b13020d0209040e0d0e090a0608030a090e060f030d051303021c200901170c090906101e050906061b01021e0c06060906011812020a0b 66
    0x2803038020301210040b89480c00b000040e1503c03400c0a5844900e02641c1d00d20f11103c1d100401d03c8410115004d81c44d002c2c000208412a00c04442000c0070350003458010040c0369200415400d035410454111590b80c841d10ba0710001040d2035040700c1d5070361000203100c543c102c0d0050000310441d40e00e1318952900307503582e00500001101d4480c0c403030740541c40707031074905941401100644480819020b28444a0f030f56500055000c2072180001030082000312728000521000301d407088182d04440c1d01a050350f40c0d400000c00d6074210140705a80d035000e8110100d0080500134030400800203c010139114407414000310036510303010181d07003482e8a050606400a100102d050714442c4c1102c1c000041c0c40158a000305210801800812140d8404820010f400201800046884104107204001601c0d00da1000c030141c02c0140412101000400a00c903215104000040e02c40e40500141d80201c00c0b91a00401071f105031034000b03130036505142c1903040815812042000303003101034002c544280d20b00c0d5403484410349070f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 291027194 1250 291025944 291025993
    0xd0c02150103120e03100209040516120b060f1b16050105040b030709170703120926010b03030c06150103140a020a020a170a170603070501111606020a05 67
    0x2124940c401040071500d10841c000c1d441c141820700243d802c82c0200002d08258004d520000c0080c0c0c0403e180140e41403a10602e503001c1c2e44003d80c0140b1540304100904002c50a02c03c1103612500d89040c0c20880d180c44c1c00f40c425884110509a48030340c5a0544002c00e1005079603a07600700d125414044812003841101241291010b85079a850716040804c000c100b94002060381c0144000d184000402e4500c95642c00d0351b42c01118043c03c1154114580316841282c640c5009003000482c59044c4500c1248614060303102174500b002d5406001604801303400b401400314a141d040c04045450050101c000c100c0511548c041341d0b001509401e600010340444018940d18050051000d000500301100c42c2e0043c0100c0c449801268004007203503544240280907002c1c2041845404508801c005402286a00c0c00b01800c40a000c89882d10001081d66411139204980c10450220351b49019864140310f46179151241510211160f522040c0296071011038200403103840c85141301c80807002013a51088904c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 291028444 1250 291027194 291027223
    0x50a0b060f071104110c030403030215010506040e0a06031e0201030e120403030804050c091e0702210f0c0708010603020910081902180a06080708150601110a170d0c02 73
    0x8059481e120107a643c1105000b180c0c100342d6a901c18001c1c41a02000f91551395002c4005503603650561400034180340c114610200c03601c2180005111a40e01c1805490036602c0b80410583c0301c1d95884813100c00307802140d01c0600b4100c0051249403403010104140d20045000303880030b0110381010500c1d035981e9201509031425410b024070060000a1050703582c00d0700540200100c80c01142d0303d5000070314081e016600d001c2c0c030020361540d1140340040c00d040240c3c0f18469002610b803404207003408480350740140301c500807911070008443c001504070009560b0a840001e00f202c0318151a182c140c0d000301006d010a0b0b100710703041400200000a80300014003070340c0c20507014025010504c4644000e08000d00d4081f0780c40f4074a020f48454036504000c49604c548441480824403524081c0300504041007600014620b810400074030b100714540b042c8094001d002031910044208000c0041410561070340307402003140b462061a1114858440040d01d80c00b0300c151010403114041c254140c1e41c0f113503910314200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 291029694 1250 291028444 291028447
    0xd0309031e0203190f11154003030507020309010c0809010909090b01031e0c05151210050a0b0c12030c0909040b070315050906011107050414040507060f120c0e13050a0b060f 76
    0x10020800d14544420a03c21350341c20350290351210522025620071030f8080300d1201c8c841c0260206065040c007402d60000ca45001462800e800000003d261b0501c08401400980c000140514564400da5014009207000303e0200020001ca10f08542d03000020320065075604181c4a800d403051500380108107410303a201c403110382c1282c03131b06003800390442d0f103403030380a8601ca0305012151201c19442001842001000c02c0b0659144c104410000b015100b80c00a5035094814440d901080100042034043c503004262025101e541da2001e41c009071142c4466a44c201446070244000c001c86410b00c20300451140d02c0900a0340f4840d0100060a02144031b00b0b54032800441c042010f0394007d840d07244403201c090003a0344080742c07903c001c101910311040015411503188810801402018440000903041034603024590105801d40201208100c00c034002500c1d680e080d6000c0098003801104441c501c010b0b000141d18080131050900402003103c000c0c500d28181070f880340c0c1ca0701d0488126040070442c000080d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 291030944 1250 291029694 291029701
    0xb0403030305060406180c0f2f0f0a05030c010506030a030e040b1f020f0f0f060402010513080613110909030f0c010f020f0c0d0309031e0203190f1115 66
    0x480181c5800f9161542140d905e01380031a450485007006032100b8511000841e00d103140b00d10040507091215015810003200036025840c82d0450f10003099065040341031451000d000c640d150341031461299403000e4070300c18480d01d07104104012005c1c003030211461008118030365460040c940c503200d20100050004056480781890b501d4654005030001c003028181c52804808000038800c038010001e056800b40c1e011040f07400c07482c0300c00c22440c0040344011014080700009142015a15140944001d0601c00c000c1132084c01d506610032084000c000703034402c940d40750802a1270640160b8552406a80303030301c1241200ba252b0300300148014001c1d41c001e0010361411018a840303140641091808014a5480304030051010000c6d00280c02d00d400c0c981581650340c0550807207a40303000c4039500e1140c18582000d81403808030303801009882805100c00c016541001421004904504c00d240d40040c51000108015410951203802d0b22451641c2d621004810b81540e46030030365580b07801c0718440e00b030440030000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 291032194 1250 291030944 291030947
    0xc0f02070305071a09041d190f111302030a0603020a0e103b1812030103020108040f120806190810020a0e0a0e0a050c0a080f0403140705060a060f0b040303 68
    0x5038070032600c3c00880c4c50400158000242c07d5942c0300c4450a140001c1c55180e5659500501c200c002c003404814046c030081001d50781d10540c03030394210300180c0150311a4454081320380341d96a0602078601003240031541e0b40b0705540d982000700624001070703000e1203041300c010889081101406000e04125030a41001d03038500882c4d04400a40e110b00c0c03c8020444040300175078440c0d5070144c0f85202d12142441115451301881410074002d00c1602c50741c60358040400c800c0f070a40c0c4241201c0c1035980a21f400545551181800c40041d060024000e10b10b0a80001c007030101580650014010701d400c4652802c002d4031540c0003034a80b1014025854107030024800801c415006600030500c845003824510054414000080c036101625805000134030f8008080081c03d000b244100d65000c2200c101031420011511002021000c004040300d514541e80d0000c00c0c00d040c0075100b001c212141e4144030560b1a8070b9842c0181c0c032030b101910181d42e010709025022a6a01c0c61003a204140d1301c41c0c100d86414503245440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 291033444 1250 291032194 291032219
    0x411060a0219020f1009050427080a030b060403030206060405090c0f0904020409060509071a03040b0f090f39031c09050a121a010b16170d0c0f0207030507 68
    0x10100da0005444d10070095648075402c800c80c001c1901e03255009864640014401a5440310080c034041400040c00342e159580340f801a40c4038550010281030321506040300903030080500750320a607442240482d00004142e03000a202e440f4078420b490500054032040101991a4010301c034003030f400b128085507403440b4241302d9800350740680010300129004e2100e4640900b00c8030192901541c54000c164180101005406103202812100040b980303182b40c140c8500720051030107490008507000070008070380c0040040000d10881440305065440040d4441090f10002c0040800d0b607030700c0321000c2100021614514000c250340c40d00a400342890068009036001505000100b107824083d5848000c50316454500c4240d002d010030a01c0400120545d0410b001a0140d04003040e0b042c0d244540140010b01c090400e4521559030210741e4500c40205183c160800780699034004070012000c40c089460b0b00282e00000c81c520070640b6004042601c000d4200e8407a411070002420300e520400b810080e140d02c444 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 291034694 1250 291033444 291033493
    0x141014030a06051f080303010311060c0a05011401091103010b070201050c07080a0b1b030601020706030f060e25110a12090314060f0a09030c02040e0c0d08030411060a02 74
    0x2000e84250103160341d2003208031481a900ca8013020070209048002d26040f11855014004213001542150b00d0f60740c44081d201d0207080228040d04010420030501607040201c8102564040000e010406003d1140000d42c00248608011a402c2a001c8091091404101c9040c0d0308480c07446031030035a00c8d40056809500ca0000500c03e440348402c0000c61141c1802030440051251600c00f015007403403480e00d101706000303c0300d55a5580042060204d10303a0002444012103a0506010504101c0604d88030f00034200340c1d100c0201906501c040214140f0810360322040c1200c0d008540380c4d55548800304551900346840e224140d81e10041d07403003010841d001c80b41d0680c0c01052a00d608155103035a40d00c44000ca0300c050715441c2d030740314030140031213900448002d59001111340360401403030307001d5100248040c549680c0039004550362240d1b1964640144402080510301070310440c1203025900c0d0002c545e07441240c0503035005500c510184254034060085070a0310708240e0080c0112446441449800028031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 291035944 1250 291034694 291034699
    0x606040c05190833090a06080d09050a09020c0304031b030204020a0e04050601030513031d06040f15080c18010c050d1805060a020304030305030901062403141014 71
    0x10310018080b008981076103a14044540d46140490500131141e180081036100c51050b03081d03000315101844015140748003142c00d41124120910349580c50240000c08030341d0081011401000a0460b0303440c0c100480c4d10880380140c0305d00342626625170209040340075015020f2444e400401081001c14402070b03440c5541e030416840d00e00025030b00d030b00003002c9034410900b00011840036090b407812032809110340c80d4080b0013070800380250300c0c081051001c0340a6450b0000d0a21501041002d00418a40d030b61000700c8001620060355039495004119070304010b031148841000342416561986e070b108100160180300042c8041e800e10441d07000c0e0189803003a00e508181000079544050000c40c500304854a034956454030361413208801821016080305080d0001802288204000076100d070b0b0000c12202100c2d0507140142e1280c885000040c00b41126a1206104403820b0703400201c000d004101490b03d1103810785003004000d6181c0120380400c0401c4410901101d86001c08100109027100000d1200c07e00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 291037194 1250 291035944 291035947
    0xe150106020d0c0606050405040b010329240301050c040503070605120105060702010e09180c0d1505130b040303020310060c0309060503131a010302033f04052d010f020606040c05 78
    0x2120041400c23500d04880580d07549079035100420510240440100d40a40800d41f001c200e0b1031080102446100003500c50014a01d4030032000c42002c2e19020482200d01d0014003c3c0038500b003a14003103150750014014903100e0300550500258160085040f039025030701244e841c8080e680b83c107041007515040001d00b03038180200114004602ea5030010340c548220b00341501880311440800c2d00c1890400034980c0640102c40821200c0046140d2140c0030030305222038003003c070f00c07030b95680c40c007112400b65281c001300310202c10301c240020150141c000d1440f602a19410402c078594902046498031400c1c08040c01068103d20f040c0300903442074008650028404200c640c6450803a910201c03c1c00c0e8100684000c040000d006208514040c80802001000f044010044501c040075040303600301044035010075101112048030b00c2803030b80d905440040c6070040c40b0400984100c0d45c00d01c040b2400c3c0601c0141240b035403c4050031036004101d030740c141300c10703039401058540c0d203040a000040a80351083c200340b010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 291038444 1250 291037194 291037199
    0x11b080706020d020a0207060e0f09061e13050415181518080d06060c03080c03060109090f020d0e0d02070605160c060908010b0d080d050601210e150106020d0c0606 72
    0x1190000b0704017107004d0307801051078616201c0010698401c4487c0248030307940c100c122403000da1311000c071a070f0070240890b00e2119082d0070526044110014040d8240c018403c01300601d0301e4402903100500c01c60040850141c05410401c2e40c00480300c41c1e00382e21024450946005000c14030880b040074400080d510b00090210010141c000c80540b80e00049038071882c00030f6404206955030103440f00030140d03410f0030f01c038680d00c0f171f500500280e9000740046001c010200005030b481e881201e1810091600c2802041401030071510070000e035100d20f062000241c24610341d25898100010706101000e03407039002d0f01d0400d040000c100d5050380949a00c0740c0c500c21020fa12000306208440394002071074240ca46118491400c80e035982036520071549680301c3c8999910031004120010220b03071052411301e40004041d0f03241001a1280c0308400d450b400820014010903c2c0010f903644144c0b0000a81310841e0032903459881080ca85406c02d00440005800251603000d919010703840d10840c2502c550004141c0d01d8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 291039694 1250 291038444 291038467
    0xb04060809010c0c06020d061a0706060801060e06061602060307030e060601021209010309030201092109081b01080603032a15060604030b0c1b0d080a1404020f060906030a0c030506011b08070602 85
    0xca20904540d01d127603000864804001e0140300d000300a04842000380240341c43c00c603c0068804000744218055080000c04c000108990084040d100d41e008060980300c2c2802c0390014000e1007400c0c100d4602c1d01c0340c00080390066000080038921600b020096516000765200118043d0a500008409640d02c030309071031f40040e43e00b00d4401c415803008140b0b11543c2a85500050504aa55214000b5500042189010b581c0c0d056400c04c040c142c20f082155003a280c00000c01c3c55031044004074441c5202d0500c16541442e000c1154021030310482c402c481c0306400d0b01d62940c0095000341e94241d0f2080c810041000003c070031950301036006440e110303030ba4101101403014070404051454000790582101000c45000c90301301c0b42642d04420b20140410a00000b4048502d6040001d04040e10825840620f101c05075203070003c075014008040c0410782c030713810581c84510250080c2401c00c00420b042000194065210b0074411280f2121394a8484054000d920307040708a6211060030355010360204810034032034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 291040944 1250 291039694 291039719
    0x21003021c14090d0f140708091c0b060f06031b1b030307030c080c0a12061805061302090303120a090c03050a050d090f09050a020c070b04060809010c0c06020d06 71
    0x144540751103400d24030b4a04681c505041500c07a1380300510401c203030540409548880c40b55448599030001d80c1d80e62515003081e403c2401400d081e41c2c0d2021f4100c58041e60000d85061080e9002e110340c0e0140c0c85170721500100852003c91003400742e0088014000601440c1c10b5103414010303101710003c4d80c1d28044034034a2a00c00c0060b40b0541030b0340781c4e0000060240550303262041e800c4964651030800c00c13030b0512105000442c815008944204445148110300300740c0c1581c0608000d010804001e0072161810807a0809420210f900c10320602c0524030140182075640202c0b409940000d028500d00034404c4155070044030301602d0034000ca6500c600c0c03100000d125a4a50000e54028801002500910b281452920760481d52800410443d1801000700400e03c030200000d030388072280017190a90b00c24050100a006490a44c0c00c648241440004c07200e640400400c140c41d0740341d907005200d654500b4550309076911011070900203441e604c64400445c100f640600030304940300d40007041080d81d0310000c182d030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 291042194 1250 291040944 291040961
    0x10203060d1e05060f011401090302011d0a080d0f0905030303090a0f06230f09010c0914010513090b100207081c0c0c03050601060315050f0d0503041502100f09021003021c 75
    0x9054481700140421040e034001000307440805d01e4194212130940d0b00003042c205910965004001c516540090325558080c220030182040790102c808070ba54108004100700118850000400c000070408641400c012040300c0c82519480300070a04100d1690710882c038101020000d032a502c0c0c0e24899031003281214081081c421182c40140022030078420380341c5441001c09456445240c0c9011920032085800907040d01c225100d800d1108495002c0b80c0050f20300744506544d440c8180c00d00321011030780ea90554840d451122054a40017030303500c51508160303038890280c02107405550000070141c1030352903040c85a10301c0600e41d141120f841e078807913078840300b401643c2e4000b01c80c40d07003041005209999052180c1d00d4248005144800a68601400728602102d20b0442034021001030750000144032003001201d00070141c2503010045050400d04c0292900f2613144a40354003801c003031072014055620302411068940061999000c0c51400509400940c8001101c030018070486058409000d501d00c41c00a9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 291043444 1250 291042194 291042211
    0xc070b03070c020f0d03080a0b040b0d0602030f10060212090a08030a08041b050d02120f0d030b030d030614090402011110020409110a050703050918091608010203060d1e0506 76
    0xb410052040203601804204201e0090b0746200d20710b40841e5000a0b41e44e00400c1c4007a000502c0d82c0b140021401520710141d04031f403c00d41d06115841004181c1c0c0c020b502ca4101c0150300800c0d5202d92300d40030302c80caa0b5071043c100141d0083c110082c40705440c200511805400510369070f021030383c5482d210b0540c0c1002141102080391802008140601d80c80031507601490000703001c0513075040c000003501c07404000381c01030302418004800780e0440f00304204000030940342d0b07000c44a40b01c04900004029218405200d07000307000c0c00c404102c41034082c2c0074120039960030491804900030320f0001d201c41c400340184107070304001b044d002d02c404083d0103001002054000250250340c0d0f6040018060540c0c0d441c05400303041150800044410b01d50100c00d403801c49034507190080d81e40d816040001c0406d04030300185a1806041c4c81800441400000d4000c003404500b1881c101880c0d840741e81d0b500701c0c001251840d41228941c1e8610300003071068140c00f0840074221541e40e02090550320380c40c2c6407030340450b841038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 291044694 1250 291043444 291043457
    0xd0f080a030507020c03100b1801170d0e010c020909120309011410051c110402030c0c0f010504120c0201021006062601182703031b02010603050705060c070b0307 71
    0x20345a0500840758410340030300007000c1d80c100d0030001c00d40c0c2d0b901050940542c90350b103010866160761020812010b600680c2020345155031554103003c4050f41040c1c081540c2e100c3c02c03461035040e501a00d00f0f146030160503140c2da0001d250a400303220042c40d008101d14664010340e502440e00380b01c0540594062640f8000004000d000e0821500b180c48001d020382c1c0f03903801d801004002654078144103a074204a00183c0391414100781c58151103c117880340308c031a44031740040100700f05a400400581030350700c3c10000f2905035502d0194a01d00700c50043c0c6018040c251a000100403050142c2400320910b0b20610440b4002405121b890f0202e6000b500400c000601d101000c00104c02804101e81700e104000d8501403036545407103d1401100e95100b1040e1a103500d8920440412050700040007002c40a0420580000c0061800030004c1c0540800740140315402100400c00754814880d10007542d60100060040d14107140402115401c884070f1000d10b8419a14042002801c00c0c02450042e8100e4031801c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 291045944 1250 291044694 291044707
    0xf26013b0a0b010804020303071b030503040e0f150f060a020313030f020102120a0207061b0f05010b011206030314070c0503071401090611030a0e061e0408010f020702100302090d0f08 80
    0x65007a00d001210342e904100c1c1c800184400f41e0350100c11511050741c4a09200500940f0b00e8200103840d00795131018249010100d00018904030890401e80700c1c410155401c5400e6560265001800000a24054101009100c1911141007440c010951204a801164100b40e141d40456039810030741d420032101201070052020842d40c04108103130540360050348035030074070041900003583d46120b840b501003002a6801d43c00714100384004807464454000244110051180c10114041c0050b1010680012054072801a40f01000c0c03041406a070303815941d0391400408040782c024550060101524203200c00c20000070240d07020880c200c001d00a04c800100380c0c40046001512088165201c141030044040400c00070a9000c0102d4610000c5420a00c92001c0500b02150302c0e0f00070317014010072100320f40400d036000b1004000a841140c2c103400c002c5c05840e90805180c0164015141e009401c00d2603860b0381c2c0ca03100d010b03070080d103142c41018003921101811502c5042801c010725205131403541001880 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 291047194 1250 291045944 291045961
    0x90307020d17040b3708070c0f1b05040b030c0103020318010203010e040b150904080a02151801061d07080a020f0307050d0e1c0f0207080a030f26013b 66
    0x81444411034840c0a040c010b4024101740b500f581031000d10041000041c0000c14481c0100604e005440e0401003503d1800c480b0300d05240800c880400404103000442d0000407545814041c0c0004403201502903d450096040150f000e90402b400c0c0203100e03081809001d0f0603080900c060340c028440184002c8080c241418134440c1c1000c05004140e5004903400c00079081c1d103500c02c650350402c5c0c0c090303104e55035030f842e814003282403030182080490007140ca00144040b040310300d0340d00020026900f0003044030f9543c03217140c0030301080002100480d4448820014007820301441c4120741c4040414000b40c035040703040d480c1c0d5110743d008480060100d030700070410214113401e0f841609e040801000040544c1d815081d4030f41c2c0b1807400344281c4800c110742074016041d0b0520074082007009220b01340868141c4210b40c900075040b520308801c0d960010b600c8903d0410000d52020712211160006a00700040c3c0e4209407003201c00d02503445c00d240125a207180f03440b0304400c0380c000720700c4d00381c40c440e0b040344090070178000c0e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 291048444 1250 291047194 291047227
    0x1090b1906050604060e030a020904110111011a210607260403020c090a090605010806040204150f05060f192703050337020607030501060305090307020d17040b 70
    0x640e504041c60030105108503210002180e041c0c0d443c6080c08902c04031110000b07450000d0851000b504040764005110401c060303028a210320341802d0322041c010188800e10325088803a45e10000e146894012802203003420100c0e8120307680b500050394100c00d80420b07a4a1894008140c8a00000410510749507000c1500d03110b40d2185250404004421070800d918000c0d80d601e10120803e01c102c01c40340200d2024211a80000d0070075620001c1840301c0d60751240c07003944601e0b00b1a8240d00507401c05c800c0c540301c8001c1070b106070140c90f507070340a8401c01c0c2c1c00c0c40103100558101e0501040d00100400030000c100000c10b40815031059156202c1040c50988540c10300f80d0740f500944140034000502d07044c40062030200980e0100c590562440500316a107550425014204459600c4c080c280440c80044030f81e80401c140f0f1150501e40c4080c0082d036a5a03104500304c600454104519400c01e10406005203850003034030f60024003c0007224074212180e24154056881a803000300e140700e0000308409006030204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 291049694 1250 291048444 291048481
    0x7030204080d0e041b08150105030702061501090b04091a090907030305090a091b03230106080a0b030102030a02130b070305120403030e190605090f120a1101090b 71
    0x542541014076104a49607601800d007000400c1c80368590b490b01d400e898961100c01c01065000d2034440a8030031420180c030315107003510b030401d00d1282c100c400c201c5540560200c81c000d000c1075001303085039600c0003001c034942040c0c0c444003810000e01c0803000030b090071100041d0028104100000030b004249544030054424003600403030041040000b00501008046031543c120b030b4160411580c0c8070101c00004005040380d410860089141031403c0e20041001529141815041e84080041102c0424911803200f2580d180d400c108603160010b200051080030300f96044006154085011281d0600103802da80045a408101c00d50124401250040842c1e000e0700805940c28101c0c5021942c2c2c5004000c1e00c40c20008000d140301c980c3c040b80070940b20b0341c1710348007450415007941c40741c007804603451040c00b9030300b44142c82040c140b20100740f61010105003151514102c4004040b010304140d000c4849030050708526042c803481c02690701ca03081080c010040118030800c1d4240192401c92800c041c1c210002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 291050944 1250 291049694 291049697
    0x9130b0106211e021e0304111908030912010209090c0a090e131212020f130501020102030f0a0b01030902090a050405070b0414240712030f0e0304091d07080f0607 71
    0x1d500000d02c0150403d000301c111940060143e9604014292100280d215940404900200000700000e000420403640300118044400e13400c0004040c0b81c071203103840540501c01103034004110990041c54000840018018100000b60600340540700203481c54008407000c861030000002d030070480981c0410608040c10014101003621700780040c0b042d44001805400501d44420b5a20b9450f000c1c0c05603515059902030004150b548071610070585107940c100c0c8503c62031309642444041015070040c02503e209001e101c4140156a4981d0301485c0640035100071941807560f54a4880701580340d030076031103100d82034481c000b01d05820249015860501c240c1c0c841c80e0f80400a000c180b0404170b03482809005071301c049070000f448440280744036416550070281c5114a0303100284140030011510302407403590703a07203403010002250b007042071100352903403d411100140c008101c01e220200e0564001e01003011054007192062482c50001440e06285411441c52548514190406904d0400001d6801043c9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 291052194 1250 291050944 291050951
    0x13030812250905210d0e0f010f02151909050309270115050f0a020c030d030b0a09020c01020405060c060405070609061205060d0c140108010e130209130b010621 70
    0x1120020280c1029000d401d200b0301500d00c10f036451298001c900413009003c01d06403015650034040107441c0401000c112030052120315400800396000340c01045c140929500a005204072921080c0c6400000404002400315040ca80220085140c4640350002c4d10460045a80340154010003408002165402e040d5852081c0c001c000c0009a405460460b50031183c82c51150f894101c00b5a6103000d08800c44100043c0820400040c590018244090075015130588903800c50740b600480585103503c81250301b080c1440420007c00f01c0079130041100c00c0ca42c500041c102600c840c0000e0850340004030303c89050744840140000e102c02480010018122400c00890252078144064014100140c0c00040b40b035071000000d40c151188421845401c0e031200310304510f2900c590b1100c980842940ca120300140c541d00000c0784440800c03016502a0804409254640415600300601043c0081210006e28901c1c01c080001506206a480c080c0c43c080e2500582e407403080700d0760100001d02380081c0182d98203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 291053444 1250 291052194 291052261
    0x190204030c09090614100f050303070203031213170702040f0b100e040b0a0f1505070308070302030619060302190504050a030f0c0e0a0c030e150604050702030c07080d0311190513030812 81
    0x4000048644600e8228102c100b0781d510c0c100c0700c1010910011000e8070308030075540b00d01d058000130310042c441c4d9031003260b04005004000900000301c695149401c0e8111081a43e4074aa05d8001c1154102c6208001c002280078030034000810354003100c50b80300038a0b854a20005018481e0440d00c113080011f05850b00341e04000554500902d083c7d80500940c061660000100c1d6443d20380c4990031410381a92095003030082d5896200400a60080c81100c100740d0b035100748005201c1c40b40b4110f508590f1300429003480c444c103648a540d4000c00d0030904a80002e00d0401c000703015001c1d00502c6c1d1140c20314210001d01800c00560160603225034000c01d0350690405070f00324601c544850307959a0046019a03000460743e6500901364036600c104a811071441c13107000340000390b00000040d80f151407070b02640e0610101d003440050408500903015900300410302d00080c0002d26201d4005440c5248071031200b5400c041c4e03292600303c0c20381c2c007030608001650f03aa80100074110740c0808802008100150640d0402d21 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 291054694 1250 291053444 291053449
    0x30f0d0c0305031e070804030801053f06070e040c0f050d0923030315010f0c110402040f0815010b03010803090d08070602040608190204030c09090614100f0503030702 73
    0x4a1040d402000d2040100120f0303403610301c0c00c9003002842c1c01c0da00351010305d080c02103001d01800d030103c0d4110001698000086640c0c180005001222503842c4070144c00001c40c0c1d030180d060480028041c3d0f00b50320400060102845d81005150b001340f00b2910b40114901d946030522041c1c80d030142d000c10900810b507502c200a01d0384003040b95103d249140d00002c500c0724038503290303010140544421104810070582078008010120046004040400d0080b5885030807030b0056658020112002020440c002052004180b8440090b19038100003080107250540300d402d04148480f69802604880c0e021a0380b0071504950b0900350360141800703d0746942150314050403160340c1e109900850f40240b82040704081045444020b41e0b410700e9002e041591201d40b07990307005001010484600c5112103015922030b401e00f8651003110f050f0f80d0000300c400341190611020394040c111884c03007200c074540d445841c0c040f4205c00f409140c2c080c01da485c81e2943c030310f441c000041051030120340019200360000c02a190050303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 291055944 1250 291054694 291054707
    0x1060509010f021204061d10020307080a020f06041202010513120c0f0602120f010603140411032a030f010e07030209040f0f030504031205191b0c080705030f0d 70
    0x30800340b03444140c0c00c054000890a001c04a03803402d108440c081004031301030b6007140c81c1019080c0b42c403200101d60380312041000141d4244611000258108000034400314445400030a0070001070300440d621a00d19010052500380222410345103480029080c0c050580c0c280900c2d50891340304032664610044e60b880319114858608201000c1c062a031192108101e200540d901038190440300c110746400c01c2040340201030034119071403c884083c103000880c007140203214130302d03826803140c0300c68000383da83c0e0382c80c1c0076841c40f85207640340c1c1449542c1c280f0f070f0400945541c1111034440900b0468100c003500c4141881c00303d4410754070802c0d07410f040c000d003203001000035404222030301140c06880a44460500e60016050a607015006000c40b619240900d90020f00a208880c4108054480008031010440f080c1c00707150011407400c803080304031036483c602c20348000703078103e81e10380d400c64490345a580d501c80381000310f5100e41070542104000704080e14042c0220800d04a1942c0a07118400808600a009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 291057194 1250 291055944 291055957
    0x15120c010f02010b0405040602070308060d0b0115030902040c02011d0706050304060f0605030312010602060114030d0c080d091a0136060b07080306120304140402070203010e01060605040f0905010605 87
    0x10003451611410748a8401d4101242401d00501704209500780fa0912202a50107100c0035004249a000401d02030b041001d441c025903a0054694055a4240451078502c1c8500c404002d00701500d030607034080541e030b0320300c00c0c8404018250000030390100c022521032110200070006c182180c01014003004503640003000c9aa0050380000006010b600d00d2089500419040d04455010700c0042500000045542c1c1020f068034441d4080f14001d80e61a4178941c00000c0c11040640c040e0004940104030034051010100901d21401c0081e040c078038446002800c80b00040410b0340d0120740c9011051049820780b076058003604102c040c1c90010724a1103070080340b88000504020703489543c01c04842c5441001d03401000030306014015507641d2819810203045640094698510070030440c0807002ca040c100004035001c50320703864214080441280100402908030000c241e806540368030005280c8031080c4600005804103484068881d400c04014816546180e0003070b40c4040d240c10b0050043c19042003d0305d54 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 291058444 1250 291057194 291057197
    0x612040204090507080d0210051b07060b060f0901080a090201090326030c09030c24160503040e07110a02090408165c0d05060f15120c01 60
    0x50688461001c580182a2903a0180c40fa0040200100740100082078030300283c603442c0c1c00c8030340c176001020504040f0f400945440808140b00f001044580e0b00480140030401d0050b000011320b44012008507200d90b01062201c0c3c0300079000202c40909603000890b0701d402c8030300d071201002503c0540d40040c088170124040039048401014841e0346000650380304001e0030850b034003110345034149013101c0c00494102c090254400d00a01501e03440b94200000d540480d0182d49030109a46c203045070006000c0e51000d00f045048408225405000c600100024802402c248004420502d4401c1e4018500c0540c6d003020a6640c020818880241c0d541d550890742098000b085283c2d01d2000088510b258420f242c2d000700403181c0c0032143d0103962901c00500c030b041032403103130300ad081c2c90b490101e0300c0a0310704d46000b200311180c840d030b108035a514007030088801595405014175440b04c1160b2180351a2020484100780a40640420040007a034545031081e008103060740d0381900d181c4140000c1d511180c103002181d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 291059694 1250 291058444 291058477
    0x302150705030c12031e0f04080d091703040302011514040b063c040b03010b03040203070b031306060b040305030711030102131202030f06010612020703050909071115010506 76
    0x1c1c03220600440d100d5410201c101d4811440c8100c01c0d4642e90800c0341d40f000a404100caa0b40030200f0005c10342485044000c5a051481d9981d6940e211185c01c030420101c00c40d41e881c807510001600103e81c0030358005040e0456500d920306854024292a4442c40d41a03242110344020444070328038544600400800b1034000c14607a0120012424500407081c02c0c5081c00310720030000e00440c085441c0200508400d00a010799030429544064140c0305038883d04c0c0d00b940c001c000402c5038214240c003a60f0010701c0207080e0f407151a41d820345495107800950381a03400c00311401d56501000114410385000305508001d00741018a15180c1684034014228003824030107241010410580d002e6048400c100900303030580c2601d50b190f031442c102c40b0304561401ca0180c41800d124400c0c0c0b038030020702d00f03048035159540c1d101508201c2a224029402c20b201c11030030304c4401d020a52140d5140c00180740b03d00398a0b130319030313048110300200d1918000e00f8040006000f4402e400601c100d032251411106840c2041e00801d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 291060944 1250 291059694 291059707
    0x20d0302160605010b031008030310030221010203090303010e061f0c0c08010515030f01050610050a0527131406040e0c0405010312020f010b060405010f030209220c09030215 76
    0x8414140300100700414036032400d00013190007000300016600813021412011103090301d42c0c0559030b481c0700070350705000e0302c02044800700014030b4841007508134840d80d440e50600c2a580d4400385803c4e6001606d41d80c3c0f2a40001c4014045428208030386235001d441100c1000131485100304642041e1402c0880404009080c41c0f41d80034412007004c410003c0c051703c0f00030891403909954036083c5050042e8030301e110703008000c2413045841e0140503c902502005040130f20f401c5a9480c151019480100303660b0a010050009446117180220f5001c070003812815035080301e64048042054068642c01c15040d014a001c4c48060400c00c040030640c0e000e00705440025403000c00c01002860542c2800d080b5a105042100110401880a088680c0e240454081301e0741200e01410441c2038a8200c54010f0b0403960a0004002c0b0398400c80c1480c0107210103003401490304500c0b5010590342986256500d0101c074511045142400c600d20601c2c10005c50303490a04003003030171075001600c0200b400d400c0d000c800d400410034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 291062194 1250 291060944 291060967
    0xf03030305180a0321050c03010608131a010608010b03040b06120106080106030813050307030506040b0703020405030a0f020a0611190c1d060a0b030103030c1202010e0a0812010504020a020d0302 85
    0x400051000314000c5551454040c900241115101c0b85d0a0701400706800495211102ca0301a9a0281c1504101903081da800c107402156403090080088100c0403140017080c011911204945644d0300945451200c198100134001d0003101d81a40407803404501001000081503a018407190042d00841d00381c00242c2c202d05c00c07540982025001940194a409000000c2002a02c000c02500140c0b0020302c18040da00c000305070f140d4586100251064000b00f000400240b4105103995001c9814100141010348840200c0c0c60304008041c12580b00c3c0000590406520b043c90080f40280094070b010745120401e14003050302c03940b010500c800d010520105d001c1c00c000c00e142410f8050b02200710b50007a510701c183c840c0070701200181c4405006004c024000300d0001164030861381a240c243e1945100c0140039a02da82d41d070005000410b007155a2013081c00701e8000140700a03806280183e007480d854485c0da441c01c10000ca410303400948940e104104507441a40c020412100c00351060074010b8540d81149803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 291063444 1250 291062194 291062221
    0x319050c040b04060905030d0e03061614030c0a02010b03070f05010e041b080a0f020a0c08030603070f060e040b030106061b1109010b2d09061b0f03030103050d090f03030305 76
    0x800b400744080490f01280040d400441340003156404c8040f41c0b50720b0038040303040d80c3c04100c1030581505a002200000e80400da2400d00701e40c040c504c0d291640041a0407040c902c1503400c01d4a100d0604200010040f0800d5824081e40200400803000350407298900382c0c6400e1a11498030840b0b050118540452809a440c1c3d8000d80c1082c059407040c008003400c044009010100c21510103551a1070f10b6152407803120240301307540300b880e1152a0741012050307503124941c2c40c0d04020aa0740c0c1c1846180b01c04030b0021034a40c2807000400450f2134030010003440310b041000b40d501d403180d4540203038500a820440260320500c50b81c1e0b804581c00340110040c07003508000c41c1480440d038425411003008000041c003960b18000510034880001c02491041c0d0400d0000440c9104214001d84200c1052049800c9403508500400e000710100440300c5a0684084a4a0802000700f110000d150404401001808001c0c810100c50881034501308203250b0405144920001c030700c1c000a0101940e500015407901340400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 291064694 1250 291063444 291063449
    0xa0e100c02100204080a0311030c030a1b0624051804060e0f0a030c02090906060307170a0510061401020708100f0b03060f040c051002030d11120f010303030b060319050c04 75
    0x90b0306560712a1603e202c1c41d079031100340004500246240c240041d0444002c81a145900034107400b079450500d040a040390394030010462004414002ca041400051142c490304442c2c6201c02c2c086030302100d504122590078001540040d0050280d14078803107444e0f03410b581c041d0340141d0103040000d68001507000e40d86000c4503507003190749a02c500300040c820b041e0800f01152049108130346c44901039135400c1850303171280406e44609826500c01c0340e0510500541d501f10f40498101d4004a5082c600e80b030f2142850724850000102e091540d42c0402d0001075a002e80400c1612403c0c00140401840d060082c0c0d503400c0041540041c1590704c040c1e016042c1115009058070781c000508a6007281400c011003000c40742c0541d01114529904d810024079400c08844a1034100a56009141003602c99010074014141200c2c90f800502020170100c0d041d9250340840c0ea005110010401041e9815841d0140448444060461140c00144208010900c04a540e180a00140c803400316640d07e451050b015540900d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 291065944 1250 291064694 291064723
    0xc060d060b13030b0630030f040f090c05070201080a0e0a0204140a060f0f03030810050d030f0305090307020a0504090c05130b0102070e06150f07080403110103050a0e100c02 76
    0x140c2d680d20514a44016401d807030203001e500700c01c0d4449104220242030491940d0f000045009032000b0071448500f00b03000443c80010981c0c0c5032001c80c7c2a280300720380c030541005203a01e41e00708052141d24581e00c01c0d0f150354041402d1207842c0845580000c0c0002d0001050704040c0c503154115107090400510040383c02690107001841030108803092158039800880359501030a14101c000951400c00703441205c12160100d5107a6a29070642d2421985040001d002c40320162002c0c10004d100d8545041c1034070228000c1ea507202485100c2140182503400c06000f25001c1e03801440458090395541c11b0040403200c00719030000303c0c40001d140c404a5072842d9400030791b1021103031810001c034510079000807040c20800d030f0985201541790030311044009026141e494100008011030a2480e130210003c001d54542641114100b5104e591060120b41c055081114211414001520740796014022180c105000e00028841003080d601625074842c0d4440a0741038040d112016480794600078032030f0030544201d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 291067194 1250 291065944 291065947
    0x1202030705071509081801020705030703030e1005040612020d09150b1801032d1514010e0403020c060f0d1b0f0219020409020a05090a060504051005030c060d060b 71
    0xc10400761041d080403030142d6400c00d2989154500003000d11a80740c1c40399002c1e40380b5007040f14080d2040b4406010001a50545c82200001308107030f0b4040018200441c400d9441c0700710050782c142031200d012001c1a10f6402d003d0180014042d00d600b1000183e0b41404407440182c507048901c2c100800740c01c03403460150000300e064100340088840358001d1420b466007503904803040c100720000d00314682001d12000d4481d0f401c0c1070361451a10301c03031030184000100325000400410600d4844410f0034040f00d00d04055103948509080701e00f00e1203117040b801821110182c4507503250548002c2c0d00c514002c1c0559204180014081084002c3d90f000e4483c0748000ca8800c0240b10380350300f040051000074080d0300c40801c00c071109103d4560300c0020101c0c40242902c0758002080e8944e800c2c04090035a440c3c0490344121140804a401d417101d08800b445086c2c4440c0214801d80317841c040c442140c00160180710b60102e0180103200c261000203941c1801d16050f0342160782c1e90003e82c5108020b0420340c2000324072400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 291068444 1250 291067194 291067201
    0x51201050d08040e0f09010608030a081824040c092d020409110c1513060b0d021f0809030c150c090a03030207182d090c0f030b0a2703120203 62
    0x11703030540345116059201c001c2096540300e4585940c3da008118514000800340ea0001c2d820780d5020b00b0036451105440e089842d01203400c3d848480d00034504a00f080407240440400c82803007110440b10006203049001004100ca1340b00600500301e0000c5a10658205082c140701ea075580303e41e040741c4c028004400c1c00c200328003420740e81080c0740d40049994020380c411a86c000213641c050108890003030494000030b41d0011816594100509030314582c00b90310141c0c5031410300158a5020202c0140f2281d441842c14014401d940544407460103824981c00390300501c41915020000101624103082441d07090150b503031a030a81d0b507080e1141e00c4403103410940b0b2250020800d500080d8034030a450250140d0520108403483c0007040703da00e80050300d94405007010752854446100d101304286c1c1e8800d01c001c106d001c07940c0c41302c25a104042c1d1040c1c060b001d2403035040003444881c0c0005600103204581c2484545041a0072400c40c200780c0300060340c49180d1018080803d4015601500c02c0030031050259160300c0e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 291069694 1250 291068444 291068461
    0x12020a05100f030e0d080414010207050307030c1a01050303030720030406030509100207081818010b030105100305041208060112230c12040b1e0406020c0d051201050d08040e 76
    0x103200001c02000b190400c85000c083c0340d03004c0741420f04911507039070300c5286d59159119035010f0404c088103501e465508118600c01710b0300901c000d040c002e0098035508803442c1140382044002050384804c28074000301100501060b64040112034022580345804880005104920340c1d2a81152102d41907921000400044c9160541c01941c421414041916540000c610706030040e40700b44800144015810840362004989440001851b0180680801440a009144104801001c0e08040d021100200041015280507a5010800b070700e40e103001d000310f08290390703800d0003803080320303041010700000d01c000561692007000c0c00a4600b0342a00c05004480d0160400100900c0c00000c040300070448200042c907401e00c21003140d02424910154260617075480c1c0354109c45081c0603040e5580030031404840480c08035084c035540e019038019980140e1340e18121804500c1c0c6108070600d1418840207000d43c035807094801c82103070304642054030746c41105540341c0790110143c842c5070002c1819020f10030911440e00e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 291070944 1250 291069694 291069707
    0xa0602012c010221060906030613080f0412060b03010b010f0905061b0604030f030b091303030b040209031515041104140409080d0c2d030207050a0c15080604020a0912020a0510 77
    0x41c542606c1c040c07110f8440ea410301d602d07043d0440d040c0031611502c200040000b0402c0004003184814585013604050321001452034481c043c01c0e06a51140e20713010520010b29083c4070b1501d1940b02400c0000741081040030280c0303042c41d5031180d81e2090a022510285881e258134024420840903001e03034200c3d24141c83d01034582e12013200034a002070324000c0c0c04001c038102000854020f0121344109240070050782e03030403006080300d0712205422a400f408441203d403020060079090108101c1e15042e03d107456034005c1d102c003c015451030311036800c00d1280090a541603088800340c50020300c2c1d900c2035084030742c04a000740000c000020140240064090942c01d015403001006184958504403002620860042000c43d44412484e202d041072161010607070103076000b0240b940c07084040e959141282c0c5c4403491000504d0f440101241c007014544080154082040e65001c08100d404500f41b004050b0000e040e102c1c0c50290206900742c0b15071407000e648c1c4084910004200081c6003c01c002070201004210 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 291072194 1250 291070944 291070951
    0x203040b01150c080306090411060a0224010b070f0501021e030109050f0f130c030c091b03020408030304020108040201050c120a020d0903020d11060d020412020a0602012c010221 78
    0x4400c00d10b141c0151107807181c440542e840b13030080001400c44d2540c00c00c2121008001c0c10882d2541d941c40884000da0f00c0311005400301c481c0c5900600314014181c2980c01e0390b0345600d91641c214498040042c80303903011030401d4408064014026080c404100c0c500240280f003190381c13140c101800c90546901200003280118103a94580d081445682c4500d94110704001c070503605000300700021000112926850130001c4411809444440c101c6603590710b0b01a10085207401c03d40c182500c4006025064042e6100090b20394482c0c075046103894034003040075072207020243c0001c0c100203158010806580c030138001d482500d425581a21b814464162550101e5400a080040940114100c1c01481d038010010030089030f802030035a64070b013661035550b02500f41c0103100d40d40e4030517020b000340b504503002e0703101902c0503004650320036003043e200780100421950349600003411617040400c8003030b10320784900c100040110a105000c00c5020f00c038100501902030700e1001a500040548400d000341158507001c0d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 291073444 1250 291072194 291072209
    0x3170c10201e0f0d090f0b10030c03030e0a080d0306210c0e041a010306060812210405010b120322030c06050702010c1707021207060e061602040203040b01 68
    0x4681c0074000d005003140c0500c00c400e00203015081a4101c00b2010480208048402420300764500202821070700100c3d00d035000151519001e002244007040382c4040c0d820b0f0003408070010411072529603a0f40c0300c1c030750034203000003010440256182000c64031500ca05501a050840c1602c41606140300010002c0165215640b520030300380c1030200c2405a904418070080350040100010b071070800e49000f0180c01c000c0d0080b2040000c0102c5980800c906c080824082c5201e25400305089103441c0307101d8a001c0309400c101482a80401a2030305c1560f0003080308003c1c003a81e585107656603449042a900501c40e800c103158110b050503141300603145022004003c03041c804103201045002401606199001c103000c0145036040e00070050048038020009400c0307071841451f2180c0c100307481d0b80e107010040c6000c56052100e100b000c2031007001c5103000c3e5900080b03c0103001c000d144103440d01d040280503240c1041c0300340c050000081c80103102d04400740726005190f0040c10555680c20246040c2a44071002d108018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 291074694 1250 291073444 291073481
    0x50a0b0a020405010c08071b120501061e05010804030215010f0f08010b0d02010c060e03070305040602060609091221090606191202040b030a021305180105090703170c10 74
    0x444203040c0d8400da405070307201030355003005441c0141d9441c2182e45c88014103031a804c0310740d0202d5400720b01c13171481d51000d09864a816038840761140303001d9081d40c070550411005d44010740d034818103140804e04944121102442c210301ea0340c0700d504040e42071001080c0b80c0c01e00946039400100c1c6040b003401c01d40b0201c0390811201c24426076943d4040e82214085514154060801d0351210003540c8121400c00480c1d0090340c0010711026002900752443d800340c0c000f10b0210b007011804000b406d030140801a03100c681541d00a000e4a0800689a101e015503d08072502c01030202e14950020054483c01600c0d01007901450401c0c2400c070540d99450a080340d10b1407040c2c4d41c0002134484550035500c0e8904442c581e4041240303100315642040041c001c2c0380c180d1074042c840d10a50703002582c2d407003404000041503a4400996810b0000c0e51100001c4a01c1214515030b040c0401c0c01480c0e0f0000410000716034000c400f0340e40c184c4240b11035025500c00c840d4080304920804410440d1107040e41d0184010120031800030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 291075944 1250 291074694 291074701
    0x40f1d19020a090c051308010609060902030f010608130807050708061b03070f03022506180b16052206080f07050304020f041b0c06060501030501080d0e1c050a0b 71
    0x204039824000d034000c0d00014440340c20088080a81c0103075413502c07a10b0030080c1c1000c83c0300d0600194411684e1040c00700c0da4482c0ca0412100da114030502d000340c0f04a060070340c50761a208a0f07000d0800f5061088604010224001400c070280081d0320000380355202004550b01c000c6800c011f5510102c0780a003410a0103907070081062444920100d0b00540e4010003601d0940d40c2e180026591405007400d0701c1d05254081059103100c44002d03403820384020070b50080c2041d49813076061400440707900c44640729242450490010204802c0c844060b0300c181d031000c09205202e072a0b0811a56801401441030514609020000c0500c0000ca9510140d800f56901d40d8201d80d1030301c000c04180310041d40c80d01c01003401080410f015040c0f070b50201c501c4480c054000300760301c0d240c0442039190f00c80e0980301100003110300b00f00c0c01c00c00259000344001058240307402d121a5050005081d211201210054144a401d0304881047e80700c42c00b650425440704400403d02d10400d003172031610b868400004955644005000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 291077194 1250 291075944 291075973
    0x2019150e012a1e02030d0c02191118040804030b16091403070803040b0711030115060809011e091a010b030c0706060902181906050315040f1d 62
    0xe11100b0310a00c600c012031920204400720007803a40040990801c00501c00c1494107403c1266040d1148400c0c0d40195074400e203107050001128141e41c000340464114046500f80b10500355800700056070480ba000a50113020b030001101d010446c3c644551007003034a03082106012919000e001241d00945012240390388500e032100c8546083c3c08601c0104090410600117804002c20a403102000a001c0741c840700e40303031441c840c42e54102d0760002c500c8c1c5000041800400000503402d0352609401c2d0002d019030200b00d02e40c0c81220089008100070840002c2c0000c0b00131909400c0a042e180414160f4485001000945005031888180c15120003ca0072686483c5030052007055048407156082d00d41982c5803075581c7c44481c2d00111003680e8164442c3d00200b1200c0c4284004d1130b00080c90560007140e14940c0051004102c02c100c2e1144a100c80e01d1310400c801a080022640c0c0117101256220300d20566000080040c101c02040000035880e10010541035241c020801100c4003a140440d050b50000c0e044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 291078444 1250 291077194 291077201
    0xa020706111e030904051f050102031e0a260106200a03030e0109061103040c0812040b07031214060307051215060f060a0c030311030103032019150e01 66
    0x10801d0710740e0b002c01001c290100900c495144941c038210140c0e4500015240040c00b038810070303030348480402e00c5603e1880c012151948001d004080a00285081c40c0342803c0c1100f05902450358a01596000030340302c01c12038403800d000e0004058505042c0c08800c0c44d03803e0150b61074002d0084c83c0200704031000c03d0140c0c0302203160014a40c295000208904052681c2c00c40141180481b03044140d0b40b144940b400041090180c4018581407554140d1a441d0908140424000c19801138440b6000011322242941a410490b0180c54441001680d11416460308444044101510000042c60045020844c214604426004000c00c90403501800e44a40c10003d5035801d48800710b8140c0d111040802c0c0440035031000c00c0c1c0c80a401001c8000448401e0042245580141c60780c200180800307490380100f542520540340c0b40134154444506560441d900508111100d04611140225602c40349416078401c001a00556082050030b00b4001002e24042c24001101e125400781c0034101b0529a000400512 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 291079694 1250 291078444 291078467
    0x70206071a182a1026100e040807150221060612042102030d0606082e081623011e05040504050709060305070f0203030711071203050a020706 62
    0x4060411000e0740740040a00f010412101d103140b034045480359055644007081119002d015448009089084000308000010340c4500b0002d41c1000400f841075558980c61000c042d1100041646010f4035141080203c83c003030031074000d0580144692184907241f140d0090200d0001444103890f10002605003001514070440760035812040a00c1030b06c81008103c00d001d0b41144c0209000010b6502494407100700c60307031103554540907900000d20100c08188910800700148450300e0325042030b081049034ae41c40f0f07191900402c0762400100c0005140310344409000e800400c0c1010884444518044c142c6401203603502c01e000c425130f50420840380f1003803007800e8040540030580d07407030894058140c0d000a590440840f000c003081000d0101068a03110f510404d406040c0545509608a29000009003920b01c010004010007501c2003030b0400d040e40000c00d507030700310100d820300d1050300407036090740c506c0c0c00007a500200340400c0884031301040c507030400e0061000c03282903801d0340c036140d0721007409070b07a03404646 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 291080944 1250 291079694 291079741
    0xc09040308070e04060504060902091f0e06071401061412010605090105061c0906050402040f140f09012406090f0303020c060904140a0605031908180105070206071a 72
    0x4000100890700c03071070030f0301244640103200150564807100410708940b51600900c2020b0350026040e4003526010300024404503180040d95204032800100401140e110b00d0164026100850350100300540c4145442e0500d801200070845a5075403681340560403030b0302c0011400b41240104003407081606008072816288050308100083e4039010512445902c0890000d6110040d445548042c0000e0f010344613015000f00d0010800d801e0078010041220640b198510b600c0c2d2070443c06a410346501404242d0004a2440a18407a9901d10b42e02c0e0142a008131000103001c1140c40c00525030f0710710f80300d003c151003142c0d480711106503d0314504201d030030403804080c0c0982d1150800e0a503d2401c2802000d44040103840410000a00031003103c03042e80030b65408034103984440b4213109606003042481619400d00313031120144403960b1191b520511440c000c02040c160854003884182e4005c5084030040359010302141d030350701ca140c2800040c08012414452403400940d0100c0c20000309500581d0f08005030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 291082194 1250 291080944 291080957
    0x4060620011407030b010201060902090f0f060409090f060b01020c010207031b1211041406130b04091a010e16090b0a02100608010605030111070519080c010903110c090403 75
    0x128a8060080c101440c85501190b40381d080b9a14010042401d4a010740720329280440d101c0c4828001909440080c0c1203141c04500c10300001d445070351103001403440c01303006440c10401c80708464003041d6a80700d25003007488101c1c1800f100e0400c1200702080200154003600c3d0030002c04498a00498456100d4110b060041e444940140f020640d0020120b00721965004050340700c50740c540468040c6071030314038280c0f13205281000c0801c2d035080901900b0306210318062040b030b480ca0303c180081c00d01c0551485101805079130302c90325045500c50303901400030706400c05400614000c42c4040c1109140c000d0055064070300c42c100100300c40343c6030110030342000f22203910307401c101d6418074680800da90806000141184180c4084084201d9544116405440440001f19a8500700b10606017514002541081000001c00800c0046a804500e03000210090381003a0001c3c001030400710300314024070144420952811006204042d0050741c1024900000400d0321140185081040741c0e50604903005000300c3d40d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 291083444 1250 291082194 291082217
    0x60b0402071a071205010e180106080303150103090b010b0309070906140d020f101d030a050d050a02071d01051305070f20030c0d0305010b0f040504021c1503060b040606 74
    0x2d4202030980c0f0401c40d1405120322064111000140c650a901441c100d69980041c0800d0a030790b205030440304250003000340002440c024540e0f907644402000f603c043e204a07009034034160b2080e0004010141c004041c8055941c4803001442d1a51064034603904074414107070001914081c40c060f0800721112420390311403414125007800269220400304a0f40003140d1441c81001d0760b14102c0320515a1a9556591483c025000080e01481584076809110307a004003000c40010340b0024007841c48402524000d134484203050000e0b490b20f4456040903111414404401c07242c80d5980d00e40e1412a40704558082c0011010120841216000c2d07030560b0005000384a4035120901400000304c00c0c910740a10741484542510f017540c119001682c08100d1500700c54004079416070326001e0a405000c00306100740c078151415503180072902c141d2065602450700032401000700540302d2240003003580c00581c03d0015414161011038000b4540c001280d016152106110490401d8072605082e59025200d80001c4034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 291084694 1250 291083444 291083483
    0x8100c030e0d0905150c01140a0b040b06030a0903110d0f02010605040c27090c08150a0b070b1009020c010912051c0e030c01060e040308060d030912030903080313060b040207 76
    0x498100d607a4480000700040300000d40c09115148c8c1050b1180700b500001c0c20a00785280c1600c0340c0800345032159081030b207112660754403402101d0304910140400120004d041c0381c240c450b90742d50050281240541c001880d2126001031440d4101a41c5070b0003040015103680c2017008482586010300c0003e40301c450400709004006a601b2040710365540c0c1c03000c140d41d80c4d8210030709513001c15100500040c0c3d00010b00030104140b00b029442c4040850381d031482c0b0703030500f440040c030380c003030032030701412500016001c0390460105c0c081040282030030700019940d9a01025807180031b001c1c45007048403411a101e0390300c04c40501ca107090310400104941c42645200c00403d100c0041c1401c0701d040360540c082001001d803000e03000d01c201d200500b0300c3d220740c200728981814054040b000c024051805059640d0342400003a0340080c5820984505019005080485003000c03036021540c2d4100900c2c1304d6002003403141d03d41142410540743c900c01c00b4103108180b0101d00b848244d02440a008058000c824051412007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 291085944 1250 291084694 291084709
    0xc1b0206072604140301020307020c240a0504060807020a050d0f020c06160b0a02130911090a060e040e0c0310110f040e0a0e0613080a030608100c030e0d0905 69
    0x50080d030b801c41a070706a24506901c0c140d40c20741103070110800050b04000c00884101c1c40701d45200100c000b10300710324151002a484100012603503200e040400c90304800001c603226200b0b4004c941900094403190342c0d884c01380081e03020340245000710b90848002010684005901451217503c800a0450032803d84825582c1c004d13024681e0040d03008081c1012499290a0060003541c06040d521800d08026800c2c05280d10341e01820345d00c0c1d0b044c010040d085121400c5441d91b003c461140320001000004c460114202d40a481c0500d40d05c09001440068240e900076007010b4400d80445041202c0f03500e0b030000c155100ca16120164058005410224143d0380c560312030000c1c0c8031000b221504c1c240c22101000566400741e0805e2103400124810702c81c81d405d0030300c1b69a20010100000f40118100400002c0d82504418002041c03008000340300706c0d0030f601c070340c004900408000003150c200038010708041e17000d40543c0308180300103840c040c4403c140381400900d02180c0c00310f507298110820b080c4010722902c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 291087194 1250 291085944 291085957
    0x80d0c02060307032004090501150c0209100801050f063f160e07080705030903090d020111100501080d140d0f06030804030807020f0a050f191d07030c1b0206 69
    0x44c0340e6903882000e4001402c000c40b801ca12000346104c0e1303603030f410f20a400003110010303000b00d88094083e00ca8088841d030005190030717105404491191041e900c00e081c50b9001d40b801e40090005508003000c0c04800300401d1012801440212203080c6016071041070700109030888110f0103461641c41c01c00c03111a031785122412485c0740d503910665916280c00008503404030066403003141c0b002d0b01d140800c12001d910002d85a0000480d1405c5407550609200b02d55a034015080351500c00d10b00701c60030b9021a03008080c91401608460250303011102c0c0c140900c03000f030900344034028131402100f07054031aa521a4160b003001e24400c24109040208100540004203c108048000c0566822000c008980d01002804c002c61050062039901d900c0d5106003c0111650088076010700080b003000d0200d5a1482400500350703209a40994991140c0950102c00504560003850400c0c015550300d401012203c407180d02c0364800c2d46090004019074a0110f07901130300c04000c003080d41117000700c40740140b50100040070f1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 291088444 1250 291087194 291087197
    0x21e07300f0e0a0e0f04140607090603050712050903090f150703110705030714010e04090b220b0403080412050c0a02010c1b080f0f01060e07030b0d0b070507030801080d0c02060307 79
    0x12100d07151131514030300a105640c1281081c000700d0801c010005d1240c2c2017032445803100050281401d101502400d445c51601a00c0300340f58507240040d1949201e030032030603940d07528485c00388001e080c1400c6050300c80d840380c45200d0080710302c2074444c09103042c800710f58003040c10200a254600f070a592805c440740c0207996581121405249000241e59604004070406400d5890702021145558400903007441130001913540228101552100428050010b035035000b4007003601120040c00c0450b141d10400d54034000140300141c03680a00c414590b00c02e1005d4485c40c401c000b50780740d50340001c2c0300340c41c1801080c0115400b03502c43e0360082c0040d40309072401454a4460103110b80214807014650f2a440916001601c455005584c4243c10321010032101c0d001c1c02c0c0c0d1000804c41e403030900c4c044103641c480c014151410b16846040e0184c2c2516040500d0300074a40054456942e41030400c401000750f40040c001340c00042043c0001304041d82c01003503107141c60845480340800400d05600380203198200400010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 291089694 1250 291088444 291088459
    0x9070504080a0501021206030c01080c0c03130f030302060105010930061a03160f050d230a0611090d06090624030605090d020d03021e07300f0e 63
    0x5514808000d0b00746902d10550000d0b0f00c41c00a040c80030021380006140c0c504c640e11108100100c0d98112184940008050411a0b5203038144080c0c1444c2d4480c451007100a2842d5400024100b40100e20080c1903903c80d034240e942903641e40e8011641d410300c6020740c403e0484090030744010041c81c285040110180034906030000d1416440310011036024001c43c0d640c400c00d10740415800c3c0380030b001c94207110b850141c14222039400e00d0800d8030301d01280e0280d94010503041ca001130510041880b841d450009407107191428915200056450300e10300c3d81c04a03140c80c1010805211016403038250b03500180007814aa42ea41c0068440d8806025183c40565034079680303c10701e00403550040750100c41800c82010f903c0c203451443c0340c860212000100540425040714441002d25030b40855402801d8480e4540545c40380701090b4680c1840a61228680030b040e000035070386007000b05001e44910b80ca180136402018604281d000380c450344c00c000c446000000d0400c4540c0600c18040e601c07920404002420b80d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 291090944 1250 291089694 291089699
    0xf02041a09010306170105150415050906060405030d1d01030b0d030507060603080307030606080f010501080106080915070e041505030304270207031806090311060c030d1e0b0a050f09070504 83
    0x1101c0d44175400d41e040350aa51200300704034030160410b004a550700001d5404200e21080e014030040c8102003405810b1042c1043e0380841e2503641d84c0c00589015080050070781d8080c40741444068200b5503084082c000a2844c65850342a5600038802e004081c0006405400f240c032203550120341552024004031100380d0b0300d9001101040b04c1d080034501ca20f0303854500085031403c00d00c01900d6020300606c540d003503d075003c00500c8142d9010255030704550280c1049030043d11000c400b64148a803006441c0c1c0c8501781c95040103001c9038450380c0001060001d82e07040003403018462080c648080c0e180078464240d40200002c00c10500030045900721001840c40b460401d80e00c84c550841687d112000031b800184002c52140071581010507094018806424504030992540ea15080c69900309060a44224000700d1003c0740e03130005004464100034040000c20100c01891101032140c411010707800706440c40d0040351481070800c0c0f0054030940c2c40040050b02c1d000d110108001151038001e166100700f02061100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 291092194 1250 291090944 291090959
    0x412030e0d050408070b07022110050703060e060d11120c090915100e070309030c120c060c11060109020702063006090c09010c02270108010f02041a09010306 69
    0x20781060450541d5283d41d160316003281503141071240d8012043d010340420050780103960340d003041400340c50051401003203480518030250030101501030180c0c0c0b0906100800c180f15038140d0028054420380c080a08a90b10750740180a60081c072401d004100060141114000d450031071301440d072604203002259101050003000c0b0304400002d0303441405550066541130f400b442c50040c1164458030f0000040348103850304921001461024000788145035460450741d040c1031040301040d9010f500021001d0340300140e800024520440480103680b032610b80164540c3d103510a01083c512703001d0b0640109126420705a0f00002075002c0b00080340c0c8040100f0040d04000e27031500c0078103070345840c1015640c4018025452456050300c0202042e114400c4101000b000c0941d0300141d500003070307082c80c000c5164101c03880881d5600d90101e1442c20010030a0740b0a40c002010b0300d885130705035110440244001c01d00d00031154164000d50040d5000808a090302c40d0564050002070080500305140200710960780345007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 291093444 1250 291092194 291092203
    0xb180910050301230702010b061801050906160b060f031e03040e130309080604080304060518010e0a0204180c031502130b18030d080a0207030509120a02180601080412030e 75
    0x1340c58016481d903c0a0040101182100c0c0e0120080c0002e01c100c04071000054000d2040c11040340c034403613042c0180c0c2c1c020b91041c0b080c1c4190007400f51809588858034020b9a0714140c4000048402609100014219082045411750301c80300182c001e0009058110066805070101d03c181c1e2582d22040c000007640c80006034103140990014101004078000c141001001c244658020b11a154071a900744400106042d00b120780c0690800d10009958403202407000411580c2c4d1040702d41e0f9802c00d0392100c3d1504011440c0640e191088804001e4031076505141000b0107980e0f4800381c20365642107030070401301d900c140340005140803521005150024031000d80c40e18040c43d400031074060001082490060884080c92615075000314010045e00400381c0340246990300081c0032402d880e401003001001c05008109a80c3cbc1c203170004000c110100340c100721446d9692854a8160702ca190504100e000c852811801c039401002c06940c2d01d0841d90303407521103280640041c1008010143d440c815161181420312 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 291094694 1250 291093444 291093461
    0x180b131107021905130c050d050606070606061814100c020109030b040503070606140f04020904090515160f0e01180815073005070c08070803010f0b180910050301 71
    0x1010381c0c3c6114100b034103000e90500801c00d9820303031900d804840301c0055009001c0d180200700c80e0001282540e245400328085002c1c040000303201c142841e02c04500b0715040706514503184804007040d400255a551494090300d50ba200e010380001f0011001c100c2244644c01940545006041c817014081d603a0b0350300501c000c000c0380c0a5136143c00102e035041c100f000e14068840105141c010f80803000079a0740c00144400c803800310580c031480c4d00244844040d11035820080085801c20252642310101c840c4980200700201d80d8814107006460f041c41100d80200c886012154059540740c020103201401507844400c08244c900102e0890840060b205100700500f0340c0c0700a1512402101d030070005005030814030301c1007080300d0400b80c850039500700c600038001d1400b1000da54000498591a031140648098030090b20150a480000542c0b805000450004504039024081c00446280c0d0300d810b00803083c000d00410f09004100400001101e241c00e100f455000300449200010303051b92003002a08480c81032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 291095944 1250 291094694 291094729
    0xf03060d020604150e0103020a080609040212120702151306031a09070c030e09011d1803030702070e0a060b03040f020a0504020a0c0501051807031b0302031204180b13110702 76
    0x5144d9070805543c80b40e02030355182c0b000c1c01c5c19401c00c01c800d80d005d014207500500f83e03070013000840b0005007075565000a40e007403054a40140c0e40c44405044030070199500000d4280c0c09000400000c0030b0702090322048400300e03203480991f0080241007101c00c4020740405665a01c071882c40070b0031035083d9918012403e016002d00d40780e44465105901e000b500100101502c0d92040c400c5600401418141004000390030070280282c5c8a1680c6041c1760203880914004544414030000c410040d02940004a21b01030751045144440282e641000401c26220140200c3c00f043d88148089400501d103041c8140c40684020009103841d912139001c0f8080b60044401d00d400101d074081c0003c10310400713209031074008003003400704d403001c0406001c100e5803040d071407000810305840d20b034400740c3c0c41c3c000002000c0a541d0040c282c1d81c10813280e000303a00d090341041c0602008000c14851080081c0d03000d22440f00f607510094480039080d00320b4484000240450603142e1550001002048010b0381e40188000584490 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 291097194 1250 291095944 291095969
    0x91003050403120504033e1e0303160507020d06110417060f0c07140609070f0605091e0406030212062d1b0712030608060a02040501050f03060d020604 66
    0xa410002c080303443d11003010142901e414180004a80c0c80304146002882c0c400d2804a110310408044180d100da244503a81140e9141d103c50300d8500c008600702e09010795060b803c0c00c1c54a110a1719544900c415150000380048040c0740314030281c061009801010b000401c4000e00c804c09440b600142d07150440034074030546001409202c8108020288080c0d01e00e44402046145800c110b24501d200c0d000d4002415004041200003c005021046096862045c001e49240c0c1c03d0143c01280c0c2c40c0024050700043c5140f41070b001c2140c07407281c41501c01004000300b200400c0001d1451070b088600c6100fa100b60072a8840d0f50220140e01d5041c044215032088100601141c6414000c808480610b8840f05004801c99890340c0c50030500c1c8000c950304103403040460b01d003042a022001c282c1d8441d06d0b0b030003007007143c03424600c103e600e400d0303030088041b1540102903640540e07507401c0d1034040303115501400d800310708284030110003894054051030780648040c109a40d40b90664001030100d03046640b2a4480d10b05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 291098444 1250 291097194 291097201
    0x120e0703030f0203040e130c030c06050304020a051e010f090b07050a050d14040b0d0f051e06010504060210020c01021608270904020609031501090903140c060c0f09100305 75
    0xe21054004005610f0320155007402e042140600080b00302601d6114502d0110103002c06102c607281060000350f038001c6000300110381c3d03814054000d410450701a403240a42003800034513402e11040c0404080701307560b408003083c81000010348415051080210400800610114550342a0801403c045028000401c400d015a05e019460502c0c0c80354040d040001d50040c003102007803800c040c0d0b0300b90380c01c41e2140c940b10700038864420f005203000f00941003e2403c3c51b00317021030003219000482008110024110f55a5502e400644041c070a078420400141e11803000c0c1059070300c4a902400140e03001100241c03400510030341c44421241c4844046d90030b1100003a005407001c642d03030704404a00f4404d01d080600c0081040029081141c001c0010740a100001010411694280805500c00400000390783c2c0a50316a0031100c020031104404078007084c4207420070b0540c25004802d07035400000703500013040c05130385d8510b00306880e40044c1740410102500b80a00c0000b40d8860041450400b0075680000d0300d0314 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 291099694 1250 291098444 291098447
    0xe0c1005041707240e0603010e15030a080a0507030c0c090e1504020f040504031206090b030f060f0105120307060207061e02073207090905061006080f0403120e070303 73
    0x42600ca48042198001c40d000c2003030078068500d8100c1c52030001813111010719000d4082c0e52901e0340303001c1c4960100b0004000b0842000c492482c602400c1035014051100e80001d003892742e40c220713455010741748400034400300100e103204100030883c1ca44a40341124061200d95030b00085d84255401c10317651140c9805001c2001007040240c44095080100d071a070b113a00b03051300030595000950b0308040c05651a10002002c3c54021000301d0510488600208080d507a1800c2640040c00d0100d2040d119000e00420801c1c0d107580041c0ea50700600c050b036003180300c41e4607000130019040a18544000c4a01040c80b080c00410b0742e40c0702402545000d20310201c0c0d8400084000f498100004165005581c0f040c00400e01250008040242d0130b2a900c19184c50034506c680402529000c80d40d401c2004d00c05ea840104813054141c1102c203c9511450841d182c03612459412104400540100e00005551200103504102c104102030381041c02814079071521040240340a082e540a000740c07042c540c0c4030100820406 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 291100944 1250 291099694 291099719
    0x6081002070b0f04080910142d04030c0e13020603090a030305010605042411190c06050304170904110307031401050118050114040b0712080a0902060405040e0c100504 73
    0x740080301003c1ca0328169a440c1c400e4040e409005025124051301070032031a020790342c43c09080c410040455201d54000e01c0801403e01039045220f80e00c00601d8440341850000340075101543d40c08011041c8050800c408004086001880c051280222021540250700d034000254001d501c0c0d44050070f200000d034100030317054031010303031040c803c120081000308841131300c54454120b5004403011007015400c400c502100d2143c14032500c05003a014140407440000690a0140c0000e0720402c800e000f00c0fa03407440c0985440c08100e030301511801e620002040459155802041048001440084c800380074844200e1150811510140403d0740c41c00c0b0040029000c00d9190700401c4246046004034001680c0f64a0041da107105d0706050194100421090444040a440c0905006400e0340c4c2c40b001c03a4209080c01c08880000345001c82c402002042210540e0b00481441e84d801410b8245058588820b000041c0140704905000e40240c41d9288102d544818400c00c1c400441c0d0380f42a04d41e818000803800c40b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 291102194 1250 291100944 291100951
    0x30c0b030405010c140901050c071a0a020124030b092a0906040e1b150a030204300807020103090b010b03060f06270d080408031b012d06081002070b 65
    0x921000f1805225800c00750b80c02c8951b0401d0070710f070042e00c81015400c46443d01d420303034010700d0f5a241310410354030300341c12002c02800c0c400c0c810350300a00080c042c0040315a515400214000c0c10750340c1000c018408280c0000c00c3c01d406c29a81c4080304d01c0007890322102c0840640c0c0070341d0300d00ea0f0365840e0700180e02031030b0401d04c1d20780010080b1030030010311104001d41070b925000e00100306408030402810481c940d0720850014684210801c06a0740c1c1c0c1e042c000010020340c003900580442600d080f01c000c0106401000c2180c0000b1204000d5070443c036941c4030500c264014200403030405440d02d001c06c00041600e80406e00038110b06403440c1c1c0f41d0604000b084090f004900400c0c1c01034105000703030041444400c0421100d0301d40b403008101d40f881780e180812031960020402070b14600001138000b500007400802172260a0003000c02c00045a9880011420b0320708490f44482803506400c095458044060740c000c103c80d2807450b0000f20180e64032203150805415221400c229940814450300307000742102c56990 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 291103444 1250 291102194 291102197
    0x30b0901140f09100503010e010905070e0c031902070807030807030c03020f090d1e1113110a03050c090d051e0a0215070519050d021209060403140106030c0b030405010c 74
    0x31454114046a4505000110306224400340804600c850100404d10380241202a0082c040141d018070494040d18a0300000c40d10344c41021400a6650405451a4002d90b5400c00f46451900c81c0282040704542c41c079820701d144ca41c200006400607022034010140c081c4651644040b07440c0c2203070060100d85110320540c1c02d250041050303a8103400041c040321503007a0215080301503030070241850101003022000904c1d206000d60014801d202800b00c02451580c0c040319100c541401ca9007802050f21090188411243d00c28010041e049019070407030390388020701c0040385041480319000141c070030b0030210041d0307050b030881141c0b4621508801c03010200c07030b40c2d038900070013404141d6030100b04c4940301070000c00700030b0a021884404200040c4031001c030704110f100904c901680541082c1e910f686140002038050700c6036034650342001001300242c6003803031001040c06082c64503648519000500043e24840e481d540c886020001445494201e006401c1a003103940e00c900c3c01d40707886c50848502004010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 291104694 1250 291103444 291103469
    0x121803020114070e0a0b0d06091e060b070c050405150a090b0a0b040302060f03070309050d1d0307141203040803041214030903030318100f0c030c030b10032703030b0901 74
    0x44d541707410010100300da42c070f11b904603a03502141c42504000c141c590408401d060030134640d059401d4440010241001202908002003561111844102d1060a8000b09030804030070081095107029486142e0082e904141c11036641c55000014540c403200b9001980c00654460040406040c25031945002d0b00144c0c00f82c03442c0c0b81c110b400041490245001c0c4007038000d0f002000540841c46a007042c1c03201c41d840303400c4902469115102414085800c50442074000e0300810b94001480c000a60f1000c13079150071810403103000c0140c14051007241244400046210030072002810340030800081008003110405400c03000020714044201c0000c108011030268000c0c80400c4050f03a000c400c4903000010340e00c0329028009004010780c2450460070700e0a21171841c140042c0c501d01c003e5000030908160b15501001040041c080a4003200d0342241a01c2d0030101460030618034900a52040c02142e85170051b940310928103241d0301640c2d01180108074002603c44d100390324603091500156001d85201d80ca00c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 291105944 1250 291104694 291104717
    0x1c18050a05090109020a111501062604140a050a06051501050309060a090f06050a060509100f030605070512090703030909051302040902060c0304170601091b12180302011407 76
    0x35203580301c103005040780141e0000e42010918001c00e100c006001444081c8c0b90741d40100406940252024402c44010485004d80584400704102c0803048031320507000130800b81e0300d039a1141840d004c005900c14071203206107030a170401700d50b0421901000a02c0740d800420189082c81c200c004481042d110181400408d100f44041e07100c001c1009684a01c40640000b8070307802c0b030b0400ca406d40c00c04000141890b03160070203204039a0380540206c4141c81040d54182c0f1162900c880c1909030300c11500c11240c0c2104c1c0c0040900004559403c215041119498070030305140e020380709a4041c0800f603540d54003c0c0e1003840200201a04102c00e80028141d4a104002c0303841c02a150a185840c03083c03000340b04580e82c112031000c640d40e05080d20032607818101140e4849407514120305003004941010202c1d0700c1090000605100113004c0e4080c0381c020710a60031840e12403400c3c1070390302414010350250455103440132442c4a910a02c034a40009010754004542c40d28090f01c01070803044003414040800041150300f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 291107194 1250 291105944 291105949
    0x6040302030712090b12270a030e04060803030705040e0a06050a0303081e070c030e090403050405120f0328020d09120303110a0201360206030601021c18050a05 70
    0x90300c251a07041040c40c0b002c100f200c803048401920981040300504c0e030200340341400740f101d98103441c4505111044a2000104801203505001d000070744100d03070340d120b840301c440064800c50b0702003112a0b0190001c500c19460781c5040e0308580085400e0000503a000c2030401008218041031900f00c1c129403002c00050342010086031840410740030203411301c4400b80208051010112460b014005420101c01540c140200014640034031564168001440c419807030155282100403d402103a258469510341440e180c12b00030740d603207c0b81d0401d0391409140c40c1e40c44c0c0920305000421030055042f070b164003d940700c3e0309504d00920440c4c1110b004c650201044000c611b4002d00f580d8251881412003a01c00a014a4120040d100310110f203903030020013007520700d0086d0b015080607001e40401101c07140b051001c81e440090007185070486901030401d203030303d110150410400454100e041881502c0400b1041000ca082260030030326210006110501406800c05a0303001d02405803004481401d10107250000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 291108444 1250 291107194 291107197
    0xa090e030d020307020c0d03020d09091104270c0804020112020a080105060d020c0109050705041b050301120f06091104050703020c060406020328060905010603020309100905100608031b0604030203 86
    0x110715922a400004907203524000c0042501d6014000c1030901e1a180521b80251140c52280300c0c81d001c900329400209010045000d003244c41d196003402241012310b4050701e8806070103c9100b800300b00c0c41031f0643d81312070740d1a405200741100c0306440d1005141450300c0010814010321800e00081c502c1801140000c60b8010b00361030451700100c0b6403549035051400110000d202e11500c480710340d0b00c0c4c00c40110401002084c0d81c000c035102200c04001c003820030380d0001254400511588001801000144080d2030110a54000c0d14046c40ca04041c1c4056940d50400712013001c10305559495140d510027482d0320b054002c03e94060194901581000c0c02c22003015901c160140c00203150503004030005450510a01c010000c8111a2003c8681d0308d01580001300102114028001454104000420481d001b030007220b000700c0c00341e030092500348842c05209008050440c0100d540d2302604030500d0030751180b0b0241d0320207032030580d0280d595161403004150070306d048001c118205c0d4204400300004285c0110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 291109694 1250 291108444 291108457
    0xf0e0d05100f0e010e0606130504120c152c01150b07080903060103120e03060103020a0302131407020c01270b0a030f0203070e100207032004020f0f07020a090e03 71
    0x2400420084a5482c0c00405030154510240042d80b0301160303020000400200076016001c161600c2c00410303241c0d0340c401d003900c104a501528038020301d03400d9460544600007860004e4041c004102c06c070920b290a04040d1100b00812804040d4003501e05200340d109104030703807500c2607541c00800c02c032241610151001c04840c030402200391000700e0f40a0520405104440c200480101907842560b10ba2402610031800110b0307800000380c82d101514854100064054141d1f40c00420b819001d501d998200580c0100074011000b841b6100c0c0d0303d6a0081c8050a5118082c84e06070b0041c11420f030302d610006045c0c00c0da5040e6401c0240c0c0e100100c04c0318080300c071004019610059020740d62228000b0099010304109070004400c140f000007045816540010a81825001142d0b110344a0f8032100003241c1c1e403592400060040d1800d0b4030380a402c03034051900b4140c403040c0500003508104442038103009507000180204001c8a0025002086141480340d40c8040c00c882c9074200242019151559601d02412 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 291110944 1250 291109694 291109723
    0x6060312032c030409060608101502030921010e0c03100b130b01090b0a0309060501080d0f030203130506190e0d12050403031118130b0607020d02120303070f0e0d05 72
    0x11180b5615a08080c0121006482ca00d10140030b1b00790303104002050100200e402501c03d501360400440c1d01074100c4451303010300180d82d00550500d200389040108030512500c4401d443d9443c0a04041000003e00442e01d103030500901500000d407090042c103050a519650300c4400c5803400c8600c0303c2503a074800c54030741101e101c504c0c002400c2007101e0042c0c038010440d41010760114030101d02051039940c9a003096500d24400c00d000d000704d0341c0e11421244d9408411180b14003258a03120714a41d0a4881d90144d80d201603071942e00d440015498a03502d040c05c01c00e031038240f0420386d500480c01c1410138a0095007140d004041c010a080400c4003402804041641d1581d0546511100468280340c842e401ca4900c00e001d075250256140c2007031550110079010075110034001d80740b600720404090300c00c0c4503051110718041c0000f0301c0c0c040f0715400c0040b0300001d44c400720392000d40d4030320044560700100055031003200c0648803491010300180d8058a180c00582140340b05110310118100001d50108005541c48840e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 291112194 1250 291110944 291111011
    0xb01020f2e06080f0619020304020102030a0c050c04060b30040b2503021206091506030c070b0907170313060807020109020411070b1003080f07060b0d0606031203 71
    0x41d401006810240d101400d90b1285503150040c0070310100307000380141c00e06d641c2d05401284802850703040c1c0c001100c0c0070f0301580050220344000742c050b40c41c03068210f01c290251110701100b50002006c4980c0f0b60420043c010000c5140643c0181245200382e80044415a08100283c1c00401034a9840000d100414018850001c41c1c0e00c90704ca401d400301c808500071003800110b80e44d40401802034101300304000c140d18854005c91700d0707810100754007402048410000001303e0001000e02420b40c0c0003510801c14003c08008003404902d81c9040e86009403181800340c80c4181c47e1590068604a2034103c403c510b070400c0080003c0c144591038444110340080c2000580c0d40d07680e290903401440d0340c0070f010f504581044440da69844000000b00076081c800c00f038100e00360325091080d80405290780070003811688101715202c40c2c41c8110010305074007032081c1d0b008074442a4020201e460750b47ca40e0000c075145a00da02090041110b5001407441610662404103c0d64036103514cc0c496428800c1c4200000c0e8a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 291113444 1250 291112194 291112273
    0x6061801110f120304031e020d0f050c030406110601091a0f01020c120115060c1e020a031b06031107050601060e0a03021206060a0501210f0f09060b01020f 68
    0x280103100600355054140c0712030f050f00d9641c800059000b240d00b20002100c60781491102402201080400c01e402d40c002c040441480e14103072130881403a0a0700301804000e0001c3d07004508104001c0000d40895682e00b031100b2a0910303031518240040c0c001c02601401c1c49403106d00e058111080c1c6003a020111a640e031040c0081005074282004061569003100c51030b601031180e0300301504585000c540049600b11910307910f00085441d20346242c0010580c0000d0500c508084505803c00f8107040d000401c45140180d89554103c090b04141501454a600041041003941d41521581c810181c4103445c09246c000695a11902d038034050260f0740031b21442004204e080c5e152110b0a2002d503a01514041200244c00c145507611482102c13540e00c43c6c6019031004c551548205500b110181c0c003421080c282403004410100034003001d041c0d0500c15682d8215814188030319004010300715000d141c000420740030700c2d00024100800038080c5085607204441c542000410642c08481500e03519040990b50107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 291114694 1250 291113444 291113477
    0x117010c0f0f0e040603020904120e12030304021002030408100608011103190518030f090a08030918060409020402180a0e01051507020613170607210b1203130e06061801 74
    0x159031b410203034100310b100c4108401c010100078800c00903600394031103501200d011420844074100d400075000e126001403002c00c0050030608100c42c541c40503401601d081c5a01c031154103240070400e2022506075a1250710400901d4400c0c071928806100c21710740980b031481c1510440290b9044000d621001076610000981803001e60780c1881030700484242a02e944800d00c24503801c56802070400a8858000e480001403409400000c64001d003501510b11801d081010f41c03502e80ca180010601900940c540601c400141d54520042c1450345084e0030030f00c039036000c2009200c3d85400d581c00c84111b5418a40050200340e4890040809104c0c20010090f919a014404075400380110507154868115800c008076480641c5a540359600345510f0848540e1340d51400202c400f8000035040c5046000d04000105049540d80c0008103442e0000c3c001c00c174202400f04a161860340102000048510204814031061164030046d0380c0010302181d0944c10280a442501f00e000361781d01a00e418000c107201c039100c0b240c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 291115944 1250 291114694 291114701
    0x5060304152705060604050105030a0b2d040605150604050402210a0e0f01050402100c0201170703020306030f0703020609191205060106110f070e0c120117010c0f0f0e04 74
    0x902031954006a50b810716450240c40c0111440103c4490203100002a0681040d11031541210001070080a49800b40d032a0350b05030031005000081c0710a101d81500d00c002c250b02c031020030000c2d00c01e85100c00381d16060400d0703000c1700d102a280c100441c403a030000003a1941c1d08400e8078103172941143d0040e03440892000100c206c08500503122640f000e001c041200b240c0719944021551071509042e0b5881020234010719080320000c5400960080980a40e1800603100310041342da605c3c410305044c100780340042400d092200e0200c4040e800683c00000708002c6007814070a95611901140c014201f040c11680020304a000d0800c019002c2c1d25500c0725820b110f40c80c0400d600060031010303543c0340b64035001d06200c1d031208400d001d100007043d002040038218402c00902c404900c90082c01030100b19080c48805145848040d21241007080180b00c90800c04c48156050f0b4001d02c06205000b0341c400028650500b9100002844001d0100c1080f41600854100c0014003e0407418941618480100f40009008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 291117194 1250 291115944 291115961
    0xf03030c0203041208040608010f240e04050411040606050a090e07270602010501120b0a2d05010302100512070c02010215070e121b040e010f150f060203040506030415 73
    0xc115110313080014401c3c0b08005100755a01030340d62a00720fa88030710380310702816103d20410300c0102420040c03c8081c1491040300c5c0315803065145c5485070040300c10000d0140c9000303584c11703070b007001e0015614141c615091040d4070003420f0505205080a240003000741901e6124810b5000c001112400641c5040c801c80700e00c54800c6481045207031a5000d8500030032000d00d5400f41d00c0241d842c2c1000070402002d1401b4002000b54000d01c00d00c1c00c0d50f0750314441d01c090902640381410031241c84840d404070413011114210b281d0b01d8100009130329851801000300040c590f840d12002d0120030082c03803014001c0034462a80c0220700d410110a034440a2004034071340642c90b17500641a1694400f030000c02039005400b500300c2c2c0c00c111070381050046442e00d4940c4820b0704000b1901e1880e54402024058101078000d01da03244505000016014242081c25003611009a0a4098480c50b02001d0050440c4149c8001c040c20340e43c0700540c00c0c10305241c0800e84900c00540b020346242107451012400b610325070040d904 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 291118444 1250 291117194 291117209
    0x82502120d0908040e150102030304020d02040b0103090b010b183a05032701111f1d0a12030e1e1606020f010621061503050604030f090501020a0f03030c020304 70
    0x130307199604c0d0340308450b40c44141c0e1054800000200c07095034a40c80041900e0180e9001400d0305031402c415400c210050500c0349400d0306058507800740f503004c115100ca40c6070090422245c1260fa904448410300e001100c103245031485520849001c0424031514490703503040001d05000305101c60a1603011581000643c0d000410714800000e020b2041d1400301490f5000c03070200c909030104031204c0001500c1003004603c6a00c0258000c544c40e42130316201440400700381481400000e2401c0703000300c0c40c211100e80703c1980070040c0d11205500d000c00c880e182102c030400f443d502d0108000418051031688600e282c40e440c03000c25061050700b49444109114003200e41d140c4500c154980c503a0360102940300c4804220081c42d552810400040001c1140c0c00000a070014021b00c2d0010350701c0b90340342002400591001c1824811040021000603000c000582c09a8042d0312555415260314100800901d5940c21890440d00710407601800200721043c0f00001c5545814041481c200c0d510081340f4600582e4400c10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 291119694 1250 291118444 291118447
    0x7020f0d1401020405090c090d1203110c3405040c0314100519080606060304030201090c06080f01120b060d0519030804050f01020903120a050910082502120d0908 71
    0x12075450154000e00440b141a541d5059554900d07400c0e0069000760082c1d04d410142a26541c400606440d070203401704501070800040c0304003000c00a0031290805545582c00d40c0c441481b8101e4000140140b000201e42824000480540e003080d0446035010740c441c8900441d2242844465039019800c05c440c62607481030b02d0041403030140e18a0308409031a02c1268000d0040d0404044c540d2510f82c2d4060640e05000010f1074141c940800344083c9600082c01501155030302c00079070380060b10301d0441c00c0041c4034555401c1c076a0308060059200c060410390010403020b0000d02100c00041d01421555031101e4102e03501084d082c0c3c1c606005060441c05001c2e595100d803400030020401d0342000010f4004c44c003900413110201d0080500310b08074072480802d0340e450750041c1e50a1519411420007000741090b00c0c505039084c43d054002054a002c101d01c50703280440c0d1908c1c208001d81040000302c0303411000e503032040b0030704407540b141c00380d00c400c80c601c05411801000191850442c0040e0003806405501000e0f26 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 291120944 1250 291119694 291119723
    0x71506050607060b0405010b03060109030308060f04050c04090608010b0f010f0e150403170c1518010507030506040f060501050906071e050a1506030302060f04050f0703080901021203040807020f0d 86
    0x81984c448a00c2c8034901c0c1c5400400c02d62640400c1e00d101c0c10040e1141d000c0079065440980705c040700102113a62014a08500030000c2d101c0d4001da5020740d481c0451b42d0b40302d500303114120060302ca040d04174064981c03401c10041c24590300c0c80004201d040007800d120a01c0f104003039085440d0bc880140b000c0e040383d000c03507414465000715001082100d0107400d1003407400c03c01d010700040c907214801c1d040c0060382c012030441245c00d04071010b00d0380000c2d07480850b40580300c10048190075900c048400801080c0d84008000160a0500401d250341e0000351040100d14200400a410f9010b00c0b2061405017401095042c20018400b494800450582c0e1070100744010b40d180c078654400101c00d085030141004091403406191600803003040d03c0c0c0c1340e005800c10740d598210011005074014000c7d189442a1502014521400d22917003014500600c0f0321075545103d0400a89002c29100c542c120000b4100100400b145810307085e9544c40b641102c0e10310b5100c040038005140c4000d89400178200c044142c02c0b5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 291122194 1250 291120944 291120953
    0xc0d060602060907050402030f070503090a141f0e0d050a180803040303030e0303010b07080a2d02071e12020a0b03180d0c0803043c05150705071506050607 68
    0x1d20403e000300440e0b0050340c0341c4050106901007075404e0003403502d151002c20403007801040a1580719110404898004002d61a85511505c0d0b000341051542c002944500164903c482a000310000f0124240300c4c9403444c186490f0307520890003100041200104034405542d100e0103c9003291b00c9484010321400303031110b8201da142d500c944401c401280c5071100840100b035021055038122020190680e051003829143d130320751988010361b50703001c20098940074103042000280f001e02548000c0080780300000e0b445000303898520182c00c140050b501c0d1107440a542800c1c1c0d80f0040c15999810040740c442c110500c0484d106c084542c01000c204003000c030401084502c0010920780030710b861012102000130000e030541c1d034405c00c13003000f8084900820008010500b40301c40c0c40441a40c410201ca4004c143c4c600700b5240558203040a42403c049640c0441485410412000085854800a0354904062001520701d110701c1800a0201c80a0103448440c10842c4e40700900070030018001030b90761a000c1c41c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 291123444 1250 291122194 291122203
    0x1b08030306030c04060312031104170a062f09130507050c07060306030816050a02040612020307051203040303120b060d062408130c03020d1b06170f0c0d060602 70
    0x11800d00030303c1809000b01c0300d0301d454010310381180e41104843d0540a1512404c401510041d006482544c90400001800e140550380380c500050407080a40400c010074075101c41641d001e00c24400d10070b2050038000c81c1c10088481802e0f03101c0000c0c1482580e4400304400702d5864a5080c02d247c5496250200700501d603600700c0c000741490035810040e036030116101c0e00b040d001c542d502d0202410131401484080380401416200518550164048420b01504c40d40040c0c2660201c2d0402002124084440d00c1141420454000034040442e14000c21540c0845100d50364081c40c44003804001d102e01c884103042c02c85611064640c04040c1c03580d85c0c0c03407048007540c0000d03048503c108508429003518200b440303181815075280980103591458583c0d1038018180d2004e4218050584800a080b031000005135205024101d006210300daa0754100c8501449810310780141e40d014074144440000c1000912101310300056101e849400300c940f81e5110605014100d0242150031454140780c002d0200c1e14680025 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 291124694 1250 291123444 291123451
    0x604030c061205091207020415031b051f081305010c0f080c13090b040e060a150b041202040f110313140d050712032306210604020d1b080303 62
    0x841c1e1103007807804041c0710401c807030048071207004035007005d0183e24412911600401105000a0000c07444040c0460380c0c401d413032140c1c1d008441d074400c80102c28405041c60740c0010014801100d2540d0740b2170909100d54500e02284d040c1a0401050a001942140740075000e5801e864009008003c054000500079008929140c803160124448070002550800440c00b02c501818110503001031407482d0820240127840c01d40103281d40700d600c440d60102c682c0c004001e218403400e507590b00442c10b0482010161702904030b540180403900c001304814040108603105e0002c4d46641a140080d039403001c0c0702454014140f14002c1c3e078a440e40001401a4200d941c900000414000c1e6451146001a01c0545680e0301e16001d02c240414001c0c0299001304000c807110305d4017510b05040105681546150780003480301d14080c407003003200260040c0700207400e00602103600340c1040c0c080c103008911002c0e800c0380e8800005000921421031403c91108001d040e1809030318980d8040030000c421750312820b5503070310790b00b00302c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 291125944 1250 291124694 291124697
    0xc081b03070f2f0904080c030a0c02040b04050f0112060213032301050601200c06070f03080a05060a15110607021b06090603010611031e0c2a010c030e0604030c06 71
    0xc1c403081c0f904044030014811004048503c0c0a5281400c0c0096004028030540c0c000c0c1c0c05000d00c012018003031001b012040d00b00c2c0e4850781701c47c50610400040381c1c040710131240624506000c10044401a41205040d610410705500744c4449510f8090080e01c144240c88d500d85082c200008200300004258480d100300e040140f01d491140e50000030300700c3d00100c42e8540041e07a0558161517469a140080c00c1003000002a01c640744c03101c4d0003041a0303a021950480b00245110070840c140340c3d10408458011010400900c400d003429400558008220300880790140b1182d00001c0d10b2900a40085c00c02c40c0e407890a60340c252400090181d240da80e40304131440c0c10748116111035110314141c000c41c1c0d01e03a0340003058641140d007041c400b00d074001d203000c002c60440d2004000b4142e89644801d184070148601c040101e69035680c81c14041e0403d2a0703a5205460160350400d24420724511407035000110b002031030a94200415424101c1c2c0e0032081042807504408009004403d001d003001040081c0c400304d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 291127194 1250 291125944 291125963
    0x60d020a170405101a0a0305210a14090402070c09020301080c0f150a090308031014031b01030c120519050115090303230c07080106080c010c081b03070f 67
    0x4040074a4109000c950052080c1c100440c182c01900315075021030b2010744000c1c040c402c2a4241d80200c2e00155054100380d540f42e000c0440780d210209d0141c840c40c05200c02c5481c0d6030400750844009442581d00100c1749501560100f041100c0d034403140c0c107448003e0781204082140702d40c3c44248000a50084c01503001d0b900810340d8100c047e0510058400e100032019200080011a2004a0401d50045865141003122140d400170118041c0d402540c0503c0503050040314440c070340400140019004001c550080c0c016429003007500f101c481400071045000e08001c240c190f02e100c1c0450324107251a03851501c242c500380c03c1c0030480d128845542d00100081804104030390700d4480c900c802450784001c1500140c02c044081c000280302d480071040c036207881c1c0c5520a905804c071440a030580c00a600d0b090059010700820091041c003409414000c00c481b5003c1e0108560b48070000301003208003179026000c1c450000c0c0e82c809001076121703041400300718442500c0c0c41d40f12920313110003680100700301034030310040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 291128444 1250 291127194 291127217
    0x181f0504090b010e090715030e06070311030a09050c060703030902030705040b0d060b0a0e0c0721020a0b0c09031203070e060301120b090f101d0307110d050705060d020a 74
    0x400d0300c114000305420403880001a03180c520300d810300c203000919004076400784880000b040c1c810669085902425524003185003540100150300d4a07a00408641c201070801680303c25040718142200d4004004c028049242d94443c100189400494554660841d60000b50709043c554594050803030f582c800c03816500001d9403842000252090703501e0059001d0618803805001070400d5112090b5031201411441140e0303540c13006000d8020041341e40b00c00c00b030800601c0c041040300e0b0040d082e0304004041c4400003a0004198000e64490718000020520070715040400d0150b049642a0340032400014111000c00c0002e0b600f5110580041d910a00442d0a4104040c505c2c0341c400f054074140e649a20344580c00c0c514503294924514000f801d2204e003405102c00301c2c400c401e814044910388100c0301c8000f0440314040c034010000b1210a40030520690414060400000c038120525089204103e4003001c29002500b092410031038540d0096900c584c00041001500d10907030064020350355607840302210200c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 291129694 1250 291128444 291128449
    0x106090b01051603030b060703030b090708040b060f0d080304061b030b100503071b0507080c1804030311041706010e1608010504020d06050306010b0d11070f0b06181f05 74
    0x141003903000350100e0020311001800441d0345044805180c00381c9804141c068035580450362a90017070b4000e40020703450700d03501003440c2043c00c2c800f90404d91074540380f902c6240540340d4580015000e88038503c201c1942e60b8a8509949214407178000507003004046699082520300708006142d10242c0301c5540d26604556030f40c1c00e0103407080c0600000080d184000c0800b05100456035603100034006d01c00c1c03012401108070800a254890132441d80b0130b0004188444c240501e207460020b40c400103e10440b03140300c4c021841d00d0b100440070341156040c24046540b2219003840d29450040740c22000d80e5032080400c007c080350740000c4481c100c401142c2840803d45800500c07501c0052016074000100d04940d004014509040d802010340810030400044c283d0703290000241804001e0380303c813a1240001c110810b800d19a40300c2d450b440c07600964542d01d400c02c4c03a900d404023a03070b000c0c01c09001100190000340b03140c1c0724500301041002d800030182d9134620302502015203544034001021200c0240a401003004d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 291130944 1250 291129694 291129701
    0x1509010e010506031507120f0c0309060b0409031e020705090f0106080708010302030a17040906030f0507061b14030712020109121412150d0321090b04060506010c051b03010609 77
    0x141412844107900d07590540181d0f8030b40c00c1f07081c0704050f440d5120722200d0301c0c2c40c01d403090303107550960341c0c3d4041000081414540183d03120340c0e032190711032450100c6900000750402c1e0703001e81c0e01e0180356242ca508141d00e00140c1c1801402d90116411108450801c81c542c44081c2c8064107131103c80d269004581c4510b9400c80c2e00003401d0000941582c401a8020003094171102c0b14000e403004402018900ba44030b420020613290305900854050f2001044503040150500060002d42100d01d403011490850440c8110481400310000e000c03406102c3c07507600500d034244100c51032a60803004000f500d00d01141c1c002d000b0300c0a280f0582d01c5000c0c1c1c05920842500c100d00c0740410650410002d81010b0591070f404c070180c2c3e006052440241e00160040d4a15102d4000200317403103010f0344461a13201d91040c0340c0001d4181c00c1401c10041403504100ca000a50809a229002a00143c0000300c0d40c0c0d58000595403010b00e81c0d0080c1c2603209580041c500f00c0c6906000501e020400e070002d0040503601d000810a9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 291132194 1250 291130944 291130963
    0x150503160504153c0909020906070f05010207210305150604090c0e09070206012103120908071a060328020105090102030f0d0501050a05240c1509010e01050603 70
    0x218469640c1d442c03c07441c81211280500c3c0a40e8554154404a20107540c640b103007684000428480c0c4c500d080f11810750082810300c02051207600075460324103020005513040c821120006c04400c0c88543c0d81e402d1000960544000e55031004c0d005203181b4801c0b50785c0e02e40880c02100e00703002074200000544a244607c00031504000080d00c10b070300b07060030048104082e21a080d041010040c140001d401566250a4028020341c25600603080340d504242c4698001c20b07142206030284407031421160001381d803144c0f045400313032506c2c0c02c001258625807030100c20340e20440102415100c54000e5040340c4c0c07040c034000310780200c80403800c5421a01c07241441d601c00640f441c810f00ca80d00c1380c804210015500440041c212600144143e03072804280c5440901c0135004003941d4890150f80740e00500160901c0484a0050f000850f6400b04003003110280f1445d41781c601034500b001000c040b0f08030465500c10451441c2da1101e40c00705181c145420350301d542c028501420500c44541c240004100c042c1008a0746111 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 291133444 1250 291132194 291132209
    0xf1305041b1e03020d0f02031807060801140d0807030e010207050d080304120315080109050d1d0103091415041a060d11010215090604020103050916090e07150503160504 74
    0x75141901c1141800d01201d110b0b09041c55000c02020620a0042c8584818007400c07060040e1203080c204030b4101509590b030fa001000340e0000714140900b60f040a001411602220200d10351035001c040812075480c0d083d10b0003007240d00701249031010140c01031902110042c0a90172141300690b56020862003019140e000f52050703600300701080104101c030a0020514209040c0482c42107904a41049804e000340d10444082e52345031407a4041000030701015000c0744180c513044200c40c001204c1e8111071a20072543c82c0c10705698445542c10041d120882c010282c506030103544000624ae190703000d020504480441d0909404503e04040c040001c45803405000058100020008541e83e6051041c440700903590540c880c0c402c50710b98001101310920304c10782e100300180c1100d0400307200150942d0006000c1c1042608546011030405034400d80d02800c81b0010800411081c00c48090f840c1008515000b2481c10800282656059900080218003c50602c1010000074080d0b540071036144c0114040e500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 291134694 1250 291133444 291133457
    0x160f0c0201030b03011805060414060f010e0601120e100b030d051204081603030b1306140d2a0f0902090904030e061201060f1205060d080309030f1305041b 68
    0x4003651107a804030038007200282c00040c103000b20807420b003000394140c40d044503a54000c03801c00c401c10200040b03a004c030742d0300e0600400781c60404d10320710005002c05014a040078090743c0d0001c0c4440e0b110b00242500480c0c01c000c20040845084001074a48007496030b4450800d0501041c90103c1c140000d41c000342d41030554a2a040000364907104d00c100304090401d840c00e41c03050143c20841142040c01407003c5120792030024980c0190b005000408035654220b110040c81c01a04000c0000c1c900d0440c10101d03000c07159903500310030500d002c04282208034110004078400c1010301c41c402c8010010750045c0c0e200082440382d040c2d0750b4652041a03100704d080c15a00302e00c007030b0081000a0b01a03c00000c600500428990800050510380c4055040c00d074001000904c41044600106400c03880c16044040f03580d0050101d0325108000c114101c100c071200400314180040040e10000080c800d94000c11b0b034002c69070340c1e5608015116248131043d400b689101c0c0c4e15184044004010f00c01002110004503180c98 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 291135944 1250 291134694 291134717
    0x121609050121020913020a020312010e0f0103120c050616091211010311070203030d060501080903090a180b0a0e1017100c050d020a030912140f031005090106030203160f 74
    0xb280690813940c045a0001064030a90703c16003550300241050300c0655006644072085460102412070741a40300780380d6009400e080c09000341c80703810352a0540b5041024800f20084c240401c90b00100c0d4207002900d01e00a100520000006011100000d140c4642e03e82954a8951940b01d0b520442c80c00f005040164000b041030b80c1e540203800101c0103031b05c0141c6d094100707107458001c01d09561213402e10b241000d58a101c24091982c10400f02c1390410941c6004600300030031400440c5642070706019040703c4070744428049402540d99008001c10300c50160803103210680c1d4040c060040201543c1641100800c45004035004494a04e4081c0d46030410004003440c01d24103040a00403c00a8045000c01004001d10180441c150004207001c4100d03580010701c07400f141c00c00107a840342d1664002c0030440c401004080c02c00c44281a5071403501070714100fa0b66600e848c0f078050111006a44036a4100f070340e41000203070158141e0301a61003082c1d500c0d01d500702c0c000344180c111690b51400d08410081290203069 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 291137194 1250 291135944 291136007
    0x90f06010813050c0405040303020309010f060b090607020a120b0f13020a12020d050106060e0301060807080703150228020c12070b0c0106050306011e080105010e1b1216090501 77
    0x9907201c6400f030000d445019040c01e01003010b840381220b041c0d000c660000280621803409110f103440501d42030740c08000d59814020540c0d2184120414107210304400700c1e40c0d000350343c2c1c7c80701030a0082204510f01102202d05103072843d14041e044601301c41c0f032071305080051030b0041c400440700d080550080035a00c50b241810300c21004d01c5610740040e07030820f229500840000d4400d2080c10080c04068a520000044080800d803d441060700140400e412a0030100655980007681006030395100b0302461424042c030300004007e014040580044440100414034504910801c6600346501a07080d10b550710130250a0002c90301c0ca0040314180d9600103001049480a00310180000c0d8880c40000f0803495a1100000c0c0360600a80042c02640200700c4c1801d07102040c117512900910f4078400a01066160002180d1030500081c4210b04222484584942d40e14030201102c0113400481102d0040c1d09064020340d4488520070ba0000107e28102c4010840398015650303a9074000002104048003540c1c1d851 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 291138444 1250 291137194 291137221
    0x30b03103b0d0804030509030708061605210403050c0105010603020a12021c27110420040506070309030f0b01090c030e28020a030605100f031109060303040b1602090f060108 76
    0xf0345c10868240408002c540e418012a4000c081b00c070010001030901c1400101001002541d000a0002c03c00c62040085244407000c03c4905000d2352451140e070391307428103503003500c11100280c005520740000440d040b90117a015040c886a00d07951007000c02c000f00d408904910440002262051aa14041c06244c10542010b983e58460720340c2410b41d40e002e1020380b6161048e091084450003982080403825013010312440318030860306100519031045c8041c071b0001074401c0740101400b0740c0000604506050007034841030015540007104200000c11410242d2050030280a041c0b8103909158106e08018828001c0c4040d03a04100003a04043c194041000a60030b00c80511a8007011910403081c0941c3d1850f13504002180034210110303480c500040480b8003071606411082e02c0031009007051000c038038555445078000c041039500c3c041d5a00e402e00001d255000e254041844500000ba400d0410079080120041321403003a50746141c680c42e902c1c500013122804032481400514050300013900b40907100c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 291139694 1250 291138444 291138451
    0x406120b18070806060405070513060f05071205191d0f040b030609161a0f0a03060e010602070806010f0b0f0a170f04020f030a03020706030b03103b0d08 67
    0x40214441030298240c2410311a0b41c3e4408086504003000f0000c0c9403c140c000d180d801070183c0f606510708201c2c640444240341ca540103010403c58509400c45465009004030390074140c0041f450b0a18689480d4001c0a0f50f000f15070b8500880340464000040714029070309c411141040d06c2c1c0d52164032034858140301440c0211414207600949842d150812a1400c1c030009014203c00c3c009000318688a2165101d200d01650106c00402442e4080c84981c10904050b9030030b020080130403e940e6075100300205d003e000b0a40103840503681100001440030340000318181121104030079900d81d613990384000000c00f440e600c240f881c00d0390100701c50401e111014000300140da01600b4002182032280352460212403049851880d642c07003180c01d000540c500850401d40b00b1500b00c0040c4984c8034255002515076855100c2d103001d2544400c00c148041e0f905101c1c080100304651401c0001d001f510101080002c2c3c81000100003441c00307070301c0701d07000403840c00001000a0ba0300f00400015007407120032281c1e100000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 291140944 1250 291139694 291139711
    0xf03030118060e0406050106081303090302090613060e0108070f08060105010e010908030d060e010b091f020c0306041209050603070c020d110d0b07020715121113030507080c0406120b 80
    0x2ca40108040d245464528000d5019a400040d99810321001410841e0b000e4100a0400c104040d80d100090b80f280d803440c15a40d055510310f4a41e1909400f00310f50480100454580d17505100380410504810487d01c0c0c101ca00b05002c96a240d5500d098001e840843e41c0501081c50b0454801849a075001e42c8801031a40e206142642d138907691203500d00d00b5038209146e03444540b0b858402c20006585c581040501401d0b0940c2c82ca4600401080020200d0b001101d4140308003003098014083c01d402880041caa0003406015a8807034074041c984a000508640c41f4000410002d0a0100d11420031307070240ca02c214850f48440841c00010303001c10111818904c42282c12010700e2440000c6510f45500302d00c0d800744180481c4089003007a1001078104078064200801b9510000300901d9041c0c0e002c00c0820740040308501c00103031b00568815104591041c501c198031609516000001000070000e944000c90342c4401c00c0e13441d0b50011800b00810303034a851066051008482d107519010490b8540301d117030000b152 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 291142194 1250 291140944 291140951
    0xb0f0306010521120309070f08030a0c050705060d2a020d0804080d090f030207140a0902030a06031a010f08030a080403030203060325080c06030103020a0317070614090f0f03030118 79
    0x12000400c0c64250113864541e04040302005008482504024000c0a03201c0510740421032401d04211540d00d0050f03501c40e008026044c00e000b800e00c00e0074840c0e0f030040c2c81b01406041e6182c400712440c002900c00308107201d00a180130301e40e800010300c048415103038228550340070300800911080111240d403405403046c0e03811070303007000049200340061161300e0696115840040b076109141c01c3c042d00b00b21441d4060764104041409080c281d070340700c903083c00603a41501001a100d882e80c0000800a2a040d000103241c00e540750b0983c0180c184281c06c0c1c038102e130119002881501c4d10390600d00c1c0c40340112000c0d040400c00300008100024081c0d0041d691000000c1e00f100c031001e1112807a40107241d00d030301c21221810720070102400540c070144074500d40c4103000d40d1078910319495580400d030721500c50310019146510b00b92078812005030344002c9a68040d0005400d011410aa418107281c26a0588481002c0e100e02c0c0d01c8003000c070710302098801c1140c0155004c1d60650f0310b000c0c00c0d4001034003540c07045081c00f41d9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 291143444 1250 291142194 291142249
    0x60a0f030b0307141014030c13090f050f1308090402180907050a110105101403030706020c0312011e06111009110405060619032a0c060b0f03060105 65
    0x608114240c000c0002488007001c515441e42400b24940010099904000810b1b800010050a4000f182d82040210310402c0e500c68a039580c1040080054011407809405d0902001e82d01071a80c0000e80224030414512446858051048410151410005220a0060101c000203142c584c0c0035000d1807c00c604a100444c400c0c0d00018802c080840344040410b402040025040e84d01c0310700c1c0a04c05590308004c01450030480c8100c103500780a481801d4940000810000f1192418001c1e1102164400e0f03055480c0c0c4014013000f42c03a81c100c160303821220000c50000040d121501072103140c0ca000400da9920039a4200001110b08910711202c4155602c101c042014000c640c40c0b013a01c03ca00e01641f5104821802c50b01048183e1b070014220910600e01030040380d0450502103141055588a4280090740358403007110488804d03c480f1170103203c10400080c041e0116017050b08408254458001003101c0509501040303120050703000d03c150598032400c014002c03414800001038030a61040401c80343c040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 291144694 1250 291143444 291143449
    0x105031005060a17100302010210150e0108070e2d040203030c0a0602130e19050601031107031707050c03160f05030408150604020304110d020f092d0402060a0f030b 72
    0xc1c0102c18180c00211312044641d10260009141038100d00000040302515103141c0000b5a00d1194060110580e99104c1c0e81c00d503020b20310601e9000615a9103d00843e540e540c0038441c0c0c81d0400d034407843d040842180001007048186212020907000e01e83d00710b91510440210310303562240d0040c41281c161000300000d07101c0301c00400c10310210907c030746009695041c0e1031881440c122019802000c4d1102c004007405011801d4075441010f00001200000f829501c08004070b000d44500d012512125400150500a26030b01c1040501c440c101810350703030f8494a5014086469105081c40091560020f004610b81c411140700c181c000ca0b801103440790300501c8a9155581568000d600c1840310303506c6080070100c1c0100205100380d00c4038040302c0c110300350315298848103044041281c62a201d0f24030040820215940c04101084007800030b00441401c3c034004020441c002c603c0c21400d101400c56100d441900e040420700503119907170145c1250b00740300884605440c58504210346c2020306880d8105a4140c0c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 291145944 1250 291144694 291144697
    0x6061b0f0c0e0a2703020d050703031506120b090402240912071703030f0609130605010326040f06050a0c14060403030e0604050601031211011103040302010b060304030905010503100506 81
    0x30820030f40300181000041518291003c11040151034242c0121205400309402244c4d07070180700d140d820001d65840552904030010701120003400c20b19040800003054807907205214048d6169010020041d400c010810401c1202c1304a4000354001d0094842c40c0349034815001c1504500001c181490030201610000b41406400c81c0007190355500440d01041420300301d02880541504007c003840c6981070020309112100d20050400d401414210041151101d150400e03200341504418104142c1d40c507131410040282519038907a010161520702c425000012100301c60031102c02a1400400c1032030188155403540264402c0f0003031040503503003140031600c078200c404c0c03900d80810064207807840e05280141c11503003041441101c95000000700300000b07100145c0c690540390001c00034170b00fa2800c0b840441d0350030305840d0b8403421307942001d81c403003544107103100a58040c5100f50000d00414080c0010300000e0b000465010300050682d020410565000300011500810040c4101c2940394480c00440c000f03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 291147194 1250 291145944 291145951
    0x120a0818120a11090c0f070c0504050405100c050a200c1e0901090e0309011215260d080a0b06250b09030c03090103020d021201080a0606061b0f0c0e 65
    0x22034001c0b2210100300b1800c80101c0140d54011100303440741d41440700052041d070091140188002c14006010014040c1d50380304c800080100820a10040c90f080c9043d507250340702c500101800c2400c2102c3e00740c802e40982c09440c420141541c0722002c14201c000712490442e40030715a44400c2c002d00402504a484044121000c0d00740004408003840b0014280260818140e00490358a46070245070b0340147d2000c0210341403a1401d03c0c107210001600342c40030004007540381003c1c01e410003d850014454100c8124050500c81c0c144846c0b01204140035002c0c0c803007100d111800d001903031810004110010035407205851200140140b4101666010709030442480c0740300c4090070f008240140005c0240003004241d0000031800918100240302003216503038001c400c0540e06240d008159041b001c48030780d05542c0289400c241089007943d60b40e103610303103580e0f007102d0a13560396041620200e0002d00070108003008040260b01000c41003855245e001d0300c0c00c50641308451840c031401c0700013100d0500c0303c0200d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 291148444 1250 291147194 291147229
    0x7171015050a0e090607020705100305190e010b0901080c1f050d02040e01050f01031b031e0510080d0507021f021e030901030c0e0306010e091204060507020f120a0818 73
    0x100b800c03d001300301d1824100521000865010400511041e02e134041c0f280350f1008107003004511a2035a918480454592580c40c03040f41d4a001600030100c14150000c01c101e41064450032030b01e9032120103580d1038000345442c042d0010041516501044286c008040c100c0782d05144c540e0901194031800000d0ba44564041560b000c0d40400500452801c1c410a4501d41001d0a04100c1c05140340c40b104042e10452007000309241c0c0d0340342e10368800d44403480e2402c03205040d8501000b41c8c0c030380a00c500207a00d0700d901404407548134a5841e010358074019401c484a581d001031180323004456114400552801402d14a4210b002c0c1c0030440c503c40e003081c5a8804c20750402009942c5664100b4001022558030401400400c4002a9074410395140403801c941034501385402c0c0040b40d91107a2240d07207014030301c4904183c848400030f80001d01c150311401a0561500c203d5003140d4000b064001c108a2081300510062190000c1560000140c2e1032001050f0448041c013106c240622a13200050f11024980803c24 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 291149694 1250 291148444 291148469
    0x19090507020a1217010902030702030403050f012c07120602070602030f060111010603080f0a1103070c05040b0609130b190807030501140f070e0a032307171015050a 72
    0x8102c0d071060710280c00b0f4850324083da0900071054a1041c00c60041c40380780003841e80000400d111900c00d000f00c801564001d02200e000244603000b0324020310354055400d403650440300301c01420a01341c2c940e840851403098010311106080120000c0c0148a00c801103603610341c00c201c07142c0007802c2c40c0007851180403208260229460454005880c1150340031540c545a4503281c030900c0003400d0803065500f5980c49600c0981c0340c040d00e880030f0350038910302641d04515101c04203030f08081000b99420f000a483c0e080c0c405102c0c1000c06010700c07015014000c20b0560010a0500380d80d451a04c0798426a01c864000707120041d004159210154448026045076806030440300052050020902559406031020100c00d103851414002d02c8200b942d0140403503082000342c1640410a99039180c03001c0142d030b0001d60b241c2000c460449094420090280122850301600300002400c04091034911010400c0501500200030f14442003802011049a00c4a009a0300c0d68041403d03103a03a01817070042c20030980140c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 291150944 1250 291149694 291149713
    0x6050a0504050f010c020a0b040c0f0b03090f010605180a06051e12030a081602031e04090c080106050d02130f060305042a0510020c0405070320030103111909050702 72
    0x194140000745040c8602a8104207900c5c1040c3d0b070002c0c009080941140c0040616103d91401c52409440340d03000c15905420081d001c5004d01e81d0f140198003414541d0700300c6641040d500815420381d0761900c15250f0000c201a014100c0189500d486035000540100c0001c10a0701c0300b0001d03110450f004080104030740240b26620440c00e00da9058217103240d442c0019800d000d9021002450341000070031801d0410803500c01000c3c05402041030364502140346c40803000000011990243d40d4004d842225045414409000c3c0c04030700590400c1c1c1a600c050303481c6c1d40b0b080b0110320007001030750001402068100b605075001441c40c0100003940040c0005070b4002c1100c1c00d2506091000c042c5da4030301c83d0500f01d0304802c818082c028480c3c044040790000d98604a09118075038041e403e000300c480d0010b80140c100307810010340a40c0f550141ca404603510343c03029100c80c40071222102c280800d00000f81000303010225400b540c50983c130b40761030703001e1440c406441860300c844001f03003501c10a44041015a001c04040c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 291152194 1250 291150944 291150953
    0x90b03210d0c03090c05011b050703030c17070b01140609060f131502060f0c160b04021905060403080d02220503010c0806030a0201110c18090f1207030809070306050a0504 75
    0x40b0b4060200c585024090459a81c8400b1984005882600d05003e44031030003209122000303503070790301c01d0f0341043c150382c80669070f81805031480061510888850405104600840758440d0540d0180c0c0c1e00319018000036820810141c01182c0b403040780d9640712105105420f40b40d6a100000c00036142d4488130240ca90030000103602003901550066000c1800054214810310360009143e54460308000c0c0c06070142e1501da41c50f40c2d06200c1d002251408264030300c01c003c107014858043c240218826503021104850030f00414200311101c0c0100c5a00100c2040100f021840800103001d280e05a4080140340a039041c0701e492007a10100b00d40d000b1251241010480c910b000e03c100c146045d00c13820080480c1c0341c9500040c1d02d51410080090610006041403001c03200100140802c3e01006000c80103100400da9450303102c004101c40300450f40c0b050104044114502007042603038850860070f128201035481d50192200d550007841005d452244c400004040340c4140200350140f00c1e0003c00003040d0416041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 291153444 1250 291152194 291152201
    0x40905060d0203121612031415030a030c1406100906050607112103040b0c010615020706051e16061b09050d02010507060203090d0206011e090b03210d 66
    0x40988500400c5010740c0240e140407070340b6607203041c5904509075144100000c0c540f0808403584040d00c1000e10500706512190554420000504c480400b40f599075a0907807145c02c500d01c040007564040c0c00c410321800000e8040c07000201c1a52041480311810200103018514207803040301e070180e50010411080059446503c1254090300003680c0080c94007e8580740c0c01c0c00d40c20710880003405502000021075869540080b0100762041e500b0503640d403256201c0140d01550800c0640001a52800e000001c0300f6621408c1140b0108464004c0c0c0f41051420105035650b0b0416031805c0658901c03032002c5154032212400410300841c906d040d00803180a2410010100e803038020500010b14620700b2400c94480d00401c000048031030495980c0c6100000b0301c0100c8060040e0f0000410441c0040140401d42601140b0420000e2895003280c22030303aa0b4070507004084450080da004a0b2500c901c0c20b100301e15550f0400403a1000150032208500f4404001c400007500c15004c0811040b40880d030700714003012a00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 291154694 1250 291153444 291153451
    0x40c18090509030f0c01090b0103030819020c1b0111010c0906320a170f010302030d02060c090103050a0b030313030b060604060912020d0b010f060807031116050c040e0102040905 78
    0x440c20400d80c0350264900e95a441096410203446602142c460001c40d825000080074a9124034540d1465035a440d01130402d4400b910281d0f01c0301c60542e508402c2c01d03081d2007503982501c8041d00a1000c1d0070b46011481c40300c08002c0034181040b15400384003c0c0c15030b00f4000c162540029685805c0218034101c0000c0c040d4a9641400212004000040c000110318100c0840710a5284107030035a1420300305800c0d120304601c00c02c0c0100007960882080186203011504034100c0340294160399900301445c83c101e07112501141e100f000d0003400d1003503080710b51095000d99440200c006000503800b404000103451504241c808100a02034010148200b20b00c1c52526500100c1c183c038841c2c00d141c2001801b600d0070605000719100281241d490340259a104a8819501030f0003480b86541540c5400c1c242404980901039027010584050200e160a8428860582c68910044202d030516441c0102140b0116a003002a100752280d0803150446036240d100340d800310a00b11000681daa071811240b101a950003d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 291155944 1250 291154694 291154709
    0x8241c1104020a0e01110f070609140a182304080304061a0607030315050a030f060605030a02060d05071101050907080f0604120f050d02070f050105180d1d040c18 71
    0x500410703118581080613902d48403c01d091420448264501e1a0b24050707580d009540075108002000880b43d400900c00c0080d03801c038890400d0791440f540d05200c43c0d102d25101d0000351840600703c081030300182d07900c102070002120b176107480b440303408141d010070400c419201640c07101000018482004007620441380c034020b108103020b10b88801040003450034001c414020703040c55201c110046141020b0400030300074010041c5850911038581c24400f840021940003255040c0c507202c400700e958500043d501d803c81d071f4018612803400d0450440308000e0f00b00500706605000300072284103200f050a014680c802c44001000300384551030300e610f2614144001a0b91203458001d13405001c0482e07076100c2c00d50042809030400101110340c120044901d4400c004e0307000e034003d10104800c0c04102441c05100c00e030790f0040300280201c1e156000c2c03401540325069090007180d4021001070302800e020740e140c00c404400c1202844a8050300700d0100f0300703507108885000b0000360102e0701000c410760003911400181200c1c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 291157194 1250 291155944 291155947
    0x120a180f060e0906030d0f02070305010504030e19080a030509060c0d030b1e1513030804080a06050c0313060c051309020306010221090906130e010b040501051008241c110402 76
    0x1c074011945406c00d5a0b031080c00c10106d0f06101c410b0307500800070b00b401582d108008100c3c9207040d0030002c1c501121017102134480c4801803200b0307107810508109503060742d04120140946240c070f5501a0361503849481142d4020201348286a44918280051190b02482d0749002c40c5004841c002c0080760360076000301074002412800100c9039034842c4103140c101a889242e15580d2012510050801c40c5496440201741c400002030110303640401082e00d48603144140300c14022a16007040c981c0c0756000880302c040503003e200c48800040364864004d11015203090802078600380711403180c0140c018848e002810010740003c140085541d0400400d0518081d103006541d00c070840c0c290781981071084a1a042c401c80041c0081000d80d51130124001065401d00c07820451484541c3c05603001c1c100c1c00d001d0a10a83c6840000207075410010354500302603400e41d41ea10426a40c0030b04030801c13441c10454400c011851100703c85419102d80694480c841c08140a50a200d05036103400804020007070706c594002c500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 291158444 1250 291157194 291157201
    0x10b030118030c02060706020405030706020d2606090709090603050a0215130312090b12071403010612020c011107150f021206090702010b13200a02120a180f060e09 72
    0x501c907040702141c590480d245c640e18070082c2042006800350790000e40d810302520308001080d50b00010b1175070003141c0684030500e00d903e429003008100d0300215001c0b500f6945400002d54240b420786401c40d8070004508021201d29100c0b2610f034101c4c0d00c0b0790400c480f00c0c1d00030341c1c0c86800d5141241e540380000c400ca01c00f2525003a00304c080c0c10b540c400709110041c200c01520000140283c000e21454002c2c01c004801d042d103600e808a00c60524000a45244001c650100d122102c01402c1804881c10380d202900d51825030403190b9480c1000390711020881c420395607523240c611142e108280040480d2400355000c8190030390111020001c5803121074062007898070404c940060400c8028040c0d0340b00e003013201c2000740d591f5440340a9000d8a9800529a4451417080000f11084880c0d03200007a6450a100d074038941141580c40c0034414464207003500056030061341803040301070003200104001c00c0a0f1404100d5641030100c92640580140c01018040c102d419003401541d5100ca40398000c1c60080b1858206402c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 291159694 1250 291158444 291158447
    0x40b1615060f231c0809030d051c06060816140a05040305150103150b010c020414072309122a040b100f140f030901020714070f0521030a02010b03011803 67
    0x540c00301060654a0040f0400130901c101c4605440c0042c40190680d1210141800020100d610040603008554502100c20310b140b030310f900c182c406840c401d4482410f04c0d114160803400403180100818104207014064282c2941c445006d1b042c422640e496542e2542d0861500a051074030780780d0004001d0b2000c81c010000b040410491502014454800180201e807180c01290003a007072810194000e4141000c0306000048020f00600c588413541d01d21850402c0000c00280ca4540e0105442c170742c41d418003001c4144c2c60903030f42040030402c640c1c046520802d03984203031000715540c003807414213010500c14800320f250406000c1c016042004940603460100010009003019080c1681ea90400600315000c3c0c041103100011a403000c407200d1099512403811001041c003075400280d0881c4c1503c14001d0f003c140c4840011450b0907034007420750050b0100c5c10300b002d10030080c11100c051410031500540807e1045020f03c010030081d40daa90000c200d0b16a400c0505017518a240c08050a0308050b000350000309 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 291160944 1250 291159694 291159709
    0x220e0f04060207030e0603090a0b070302091e0d020907031b0c080304120327060b060c060a05090114040506102c090304030804060f110102040b1615060f23 68
    0x691107840140c490341c8034281110400060003030160000c90001c184400400002004092640300380a2a045551484012002c1c0e006505a81d900711001c2041700114280340700e90500c0c61240901401d000480b070350000750100b0810780f40d0001007542d030f4070b141041280c01c0054400d02605810b00c103051080907034036900d0b40d100040c00540b0001c0102410100f40c1e1094004040c82d910560020800c40064880807214040144c000c56903103103000c0481500c0d050503010f4414020202010f40066074030005070301c0c049c103c010081d10095580d2888500b010000d03c1045010b240900001c1580c4d15204010a000d0f84181d08204100b500110000c0120f44400d10601d81044010b514000103842c1c0d04034036440e6004582005101c2c1001080c0030070010740c04031a01035114240c3c1e4648440c0005071003c035080340f0a40c090744501c440304001030101c2d22208141544a140f040c01c401c6416400150100c0807520b142e044081d8400021a04011105440342104422310782c6291a00780e0001c5c010005041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 291162194 1250 291160944 291160951
    0xf080c15090a030b072d0512090703021816031116020111030a0816211a0301110307030b03010218150408010507050a09080604020d060b15220e0f 64
    0x551100190505954950b2200d550085910800c2c0d0505810314140c05411351503005030311040c0d0008820581d42003858011860b842045940720940fa0400d501c403030208c561001040c0551910404400000580340ca800b0074842451552280d086800c01e5000a0700e425641d2180303004050070444100720035000c0302e0071101c0340640b420b5843c1c3c1842442c40141d84c211040c00c0409190300011070700d0b42082d030702b01a1440c4102090806070340108102c80c015640203480c550385503c21120340e2400c2c4282d0140360710484004030100544c1d4800c0a041d0006802e540d850030310700010142c01b20a000001c4c0d05030140d001a00021030096003032045020988141c04034144c03406201e4001c407003488001038241c17001c0342c024100c03c170000e000da40341c03203d0040d00d03981c020320100d0002200d010f4002612100400c045001ea540203044041404442e1078010186c0500b00100c2d90000c00c0c0400d03240d904034050001e16180d145121485144c036919120b24003042019880103c417030601e40100070400c24218101c50f032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 291163444 1250 291162194 291162229
    0xc100f0509011a0618090a0c0801080a0507060302030705074b0b040f0804090905070609060818070f0e0402040b09010501092c070809120a050f09030a0611040f080c 72
    0x1c45c0d98110307120f5402042c80340c113520f40000b0f00c03105004455902c0d070011460003030a92907a130038903682d0703002d490350f103030514000070f09141c00c461300a1004510a800454020b20b880c98007501b801031540300e8005482da011413041c2e0030300e10914100c2c0004a5440e526089011254001c076030309405403c00300042c510141d00400d8029030700e00080811040704003449240e604103154640304d0752075103400002422041400d89407880303220300c0065210b00c64a01d0200340c3d000707a0340d04001a1a8031087c80b040d0a181c204079010390040450115410750a5100c80300103060785c2d00c1d00c5640342090300600c001c952840340316a02a0600e00c1c0180000d9801c020140c00f00c07032208031141120070424450059003951201035101442804d07007400300c0140e0288000d03004101e5201034a00789804c2c0d0103032851501c201007129001c45c01c144188a005503071000942290300010f015104901082d60301d1104a61401e1b41800361180b001c20240050400840c40740e0180c0301580c010b1102da00c0b000700040301e0910a074107510 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 291164694 1250 291163444 291163447
    0x6030d03020906251707030504150c02120d030e030c21160305030a0506030105060a060f02150a02040f06020d090905061206160e0405040b06040509030c100f0509011a06 74
    0x541c15110324003192290704020400040300d000c4c145022121450310181942d400000c06411882e070a40181261081a030544500346031a1078141c40421a0229068031810311040c0c00b802c0c030258581c0b0421a045804520160038000c88441018045800c490801e480541c0180420044180c0c005417242920b59140c849120b4030840000030303d0507100701809000035503242c0c498070003015045030165004a0110758144199550381c2d05050032500200c62055000150202c2000b000340991441600ca000b240b040c0e481101d00c815120a00c52000da94000c503150340020308104841102e03854102504080c4003034154440c04200081c02d40c0c1d03c501503810401e546001046150780c84603149054041c0c800300b50f0742c4615110701200310341d4840ea50811f02190130141c061506180070f00c1410f110701d5125050740070541341c4c0001d12004207001841e4554a201c00c11000080d04420050882d81482c0700700c0114020810171214026542d0180050000d07078109003003140c8000d85c5154036404404183c1c1d466 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 291165944 1250 291164694 291164707
    0x10303080613020d0212071d09480304030914130903030b010315050307301103070e0c0d0b0604120804030c0803030106050f13210b0106030506030d0302 67
    0x54051680c42000d840601d03c002103034114402c49030003034042c8440e01d590140b155aa5003d0589600741c04207411003c0c14003c000e406290f181c040951030300b026610b400c4800e811607402c0c04a075440407000c001c801c5070308980c602050140380306100c002c0008a2507aa40d04609081d80c01401d800140d001e581c1108101c2d00012040da01d514800203004000408144160219414081c004011051071140040c0c140950500f4403444030b06c13042c4c01c071f0700045c006003a160316004451400070904402d005041207203840c0c3c1c1c00000440d851081c1c42602420078481e03c20320340c01c109482c000c1954000c40032030418104110301d2070007076802c1d500116181c100102d036514050000a41910840d00009102e802200100c81488403d41c050320946e8030608010850380d481d0070a06aaa0009101d2140000e00810102007075001c0781000e4100c4407030303000c0124078680c1c0f5621494690700c19410b264914007811000502840144803003a401040d06040c2042035050120100ea1204914030751320084c1a00050034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 291167194 1250 291165944 291165949
    0x102090303190509060d02090306070912020105030406060905040506070e010c12110a050f0106081006030222020d1a031009030e011d040905070e0f0c04090b041806060501020d05040506030103030806 87
    0x491302429001410305580d4543c500c5031000a4200b02c500307a0003031140c40f0000350114061102e17142a2140c9030251a5005201d60044849500042088403266124240000c0e48880c5018a5010b1482400907029520b030145000b010722f050000728030304001d868080d400108840c100b244000702182e2400e240222107100f401031500401c007600411611034032400350344c1c1c2030065204800743c900400c2030b2045001d5180c6c480b800e84030207000281d8801203020380075540c68064610308204a001440250030400d09034441030031107c110300620703513284650702240001d02e81846400f4400d01080381c2000101a2914001e00313213080241c00a061201d1005001b05101c0c041400300d002d000028010302100c11a4030b460b070786810040c440c50685e000d4100c00715840000f00a02c1c144a02180c1d1100c40c1810b103043e80303440c05040e40811440e007180e52030301008030400d144400303801d030240110b4011170400e24041c002850034001001b04010443c040c841805503079500c3e0110b0781140c2c1c0500c0d010031151102d000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 291168444 1250 291167194 291167197
    0x309100506130221040507060e120d050304020a080601080105041a070c030e03030c0111070b0106020d1d040902060a0c1506140d020f0d03031e021c0c021f0b030d0201020903031905 79
    0x180c001c0d0130355075420402004000030300401500c00702d83ea03100c0203c00304401e012805116407500096604500d9840c0c1c0e8030392180c00990791180c0000c017843d07680b940e00d140b150f0404400fa0841200707039464400700800c5c45152201c8012050a10003051541d1618140c01007044900100c010700300b08076014162001d940400560794003100080080082c000d21208000c3c0300d03480400111540d60402c0c00008010303001243e42d5140c4900c54a03800c52096000c15aa9903000d134001c00954490b9075520351502580f2060064000400c10742c55500c040c41981c00c00900403580007040070000d605001d001d0020042c00c0c0c01c1c02d07100041c1900c200c00e0216141c400120f608e43c410b90798580111041c0d00d51420325506401000c680d02c941640703c0c1078010a1043c000a900c9034042c044604420101c06a504c01d07801c2c3c0c40f80075007104c10b205440008094000b00c401d448800d0402c0d148080d212410140c00e032038244640c8007000c8ac140000c5140120000c0480c0e224002c8149000c140d94210f041c0c81401c5002e43d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 291169694 1250 291168444 291168487
    0x1206020316050c102c1b040905120c0703080a0503060f0a0515030901090209040b10090c0504030b040c0b030106020d0306080304140d03030b04020d0e0c19090b0d08040b03091005061302 81
    0x403008206205e040a0607955074281c4140f130105071200c1080c1c045c0307041038070404038000c0d0040007030507054041181041260b0b2000b0724944491007000c40002c041020b003401707010750000d80c0d9580b56130381c1400403c0000301244c4402480c0708107804d0804000a070355404034240c105002944e01916980c4022400b401402d04000180d000304100c000c200400100ca08007500c5000d014078a840300c05d88492100040340c4601014002107a0204020b10100e0050507016610a20805082901c0c0da141c0301f440040350800ea2000340540d02c0b129100301c6441e00341c06200c029042000045080510700540d0b42203010101804a000781d05d45030781c088c03e040c442e81000300d0503100a4010f566441c01d0318810801004000400d2045001d180700c0c210b000d02d40001000e0b802070304514240c940c2402c0c100b403c802040b2020685511940340810100015142d46c0600014080c180b11940ca92408500316030600d80d9845000c0161480c1c03030f04100341a03840d092560210f0074040380048c0c03900044070b041c6e04502da407035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 291170944 1250 291169694 291169751
    0x70306051215150d081201030b0906070206060d08070c0b0405040608061015170f040605070203070213051f03050604061107030c0f0201141b0d0201180b0702071206020316050c10 78
    0xa01c0d106c20785d6010380c8507048a205011950f002d079100710211740c65584c01e5030440016001500810321520b012042280d40f503000f20000ca1030030f0b0040c0c2d940224403030258400f0301e010030081000c0155161074402c3c41c008008481c064211443d04e030b107204803580290b00681c020791880c0d402c00d400541c49000010002d8829400907c0706080c0b011748212074650465045982c42d081c100010711040c03020050303034000ca9002e4506807240c05002040409490000c6c0000100340c0c1402640c0140308501c103240c002103000e403000c0d0400c0e0410b4207201054400780e00c180c0c00060810403200e00025480034000e4200c6810103150510100684012a031010110340701a81000020038a10b81d04010380070312225040440c02240c2040d070303100405038265a019100300e40d9460321483c15401141828900c160f000415105480590b6110b502030501c42c500c026043d5151540481081030000200e20520460011418403600304240030441558440940f011554070586583c01c002005000c0400f405400001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 291172194 1250 291170944 291170947
    0x90f0c0c0706020303041203060509060111010b150912011803030203090c0d060c030e01060f0302120c0414010608011a041502010b060d0c1701030807121106070306051215150d08 78
    0x5811000b135a90700182d41c1038400f0040481c00c4007225020f0300c00c0c50f0864901800030080b99488000540d075801516404549554842001d14140d944848003c00d250700300400c91911880b000c010300c40910300784400800d6680c54160350201036211003046106195240c0b501580c1c076510f0030350b05810030540c49080d5801090030b1000c0350070041c0d2a041407040000341e68042095041401070a426a131aa101c0c41175041c485100c02e2002d81041c1900201d84280718040381c00e0951520082000c8511408d00f01e0740007402c03600144040c0780d0110300103005050950085400308000d0b062503000703214038030401c07010500580343e050f14107000790820b00c85c5410040c81e4648030640890007802421800c2e016400107600484450106000c0f80b81e0503040c0c07074000c02d805040225503603511780d0404000342e4030030a0000480400305c00b0402041124861035041c2e401081541c03400051000c08032201041c003140d41c1002c1c1c24100e185c048130fa034981e480400344a28080709003640b4045042e5054125018024010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 291173444 1250 291172194 291172199
    0x61b0409091514150103020c010212040602030610030606450620030403080705210706050105041b0e0d0204020c0706080c0a2f010f0e010b03010902090f0c0c07 70
    0x11031000d11229400300d9000f070103076400c8006070905041d02155010b10b002003407003500b00194801e5019002c0304400c08001442c0c01c015517074041422508031421121290000200140344c2840184050700300d901d41800c0c03110508204024040c010b0608001c03040000540d0080d0f00c0c0781c001041030b5500d140543c500d142c092a042c6c1020114147d42c0030321404a2900c40c00024040c40c603040c011403601340440618141411540d50070781942c01400c0548141c800c2090303542201200c2c00b5002d41140026085940e900da0a16100081c1c0e14143d10241c0700700e00c1c0440ca020079a01410301050508501e00d4104450a0141c0000300c24600c8000c1c080e42007440819041f041d01000291041900e50136101c0600c0c542d180559009d440c46040341100c0004d000c00300101502030390352402840300c04848601030740240203541d003a003120407480b003010003141c07924000710100c6400e1040c051810803d60081c007d102064012440c1000302900b41e54120b00440001400c1404840035190080c00540a0341c07101c95 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 291174694 1250 291173444 291173453
    0x503040c0b18030c010e0d080a02030c030d09050606010509010c0210030f1d0c0306040c14030106090207050309010f18060507020d0210090e13030807181502070315020c061b040909 79
    0x5084942e00740680704e182c58502607580540c0c01c8a03a850401130880f50800b215544289494008420310700940c4410b000340350451300f082c8040e228101c8151400a4802c0d0f1a081035490400090a602c1c14000200410b02650340c1c006200050260182da06140b1413445a40072001407031510480c00b0701e02d02e00b41c64401d60500350004d0800d0001071030101c0316542008820980c540030192401807501c8000e0f0410000300d00065214400410010700000e0100d030740d6400794050742c1c80854100d481da000017500d1081d943c1c00c4002c185c064511440c2031484403505400b007010381040d17401020140711011807803c00719542c030910b80304002e034003078599811500c0814001d889503503240240d51103800a507002510301150a001041e103150180d941320020740f03130030005540c0c0300c00001a24845480c1c950300072400c50051f480103108810150b00178081203103181040740304100b10b00700107001d442c01008a004900300004103a42c02040c25030380391003082d5110a40051a00c920391045518906150340c941c24403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 291175944 1250 291174694 291174727
    0x180305100902190518131b08010f0e030a14091e0109060c0b060103230c1b0307020a060f180e0708070c120e0d150b030c0108010b0306010503040c0b 65
    0x4610a030340708010720700451100d01001032a4055660818808080040013050103140c5d950041c4c1c5050118003580051b80b00d512000515102100e80090b0125082003603100034428112200750b603800c10080c1c0603000006640f03d1085079162010020403076000003200c0b03510401c480480c00c0091802c0244580f01d203542c10058a40e4821b03c2c0407480903400001c0d614002c400100d02590302103211546030b9900c1c001900100f807051006014841030200c0c40d035880d41c0c0000031601039460180f40741c0e00ca00450050b0b0040610003034006040b03800a0245800680b22080002c05a42503030500824201d41c0840c01c844d00b00d0b80c0002010303000c60b08000042d01000c086c0d1494011303130b00707540d4901440c0d40300074058880006000303005081440c444511100c0030b1003140c1400c0612002003403110452408e456110071141c0e4040340000d025070740c3c007000c1110319042100c00b41240b02820060603941c5401d0038a410303130000400f194140400000003c080020b003081010161a602000701d842e044407900c1c2a207103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 291177194 1250 291175944 291175961
    0xa020d03050f04080109060e01050108070b0d0c1119110303070209010315110d1b05071109061c0302061909050312070509060301030b1f0f0612200307090902040e0103020118030510 79
    0x5510b01000840ccc2580003090076019546400402450038100480d01c000800060100c20100600d80304d040c03160010a03c1850450007000c20601018812070500314401040d440c0128800d91080003800016111503141a044a4008181c591409400d045690280c01c418441d00000c0800240203042c058040e40140012603150700054060741f0740d42030541e003500c5283e43c00b400340c2420302d10031040c42c5082c1c904035601c00c3d006403900307035080d10305880142c29510096040300903030454000c020205044500051007040c40a00a00143c1243d86400f0f440b84213452407401c407400080005003010303004504940f5291800b40025a0700e41c0d4034200061002410b03140082c0071045010200001c0d00e000064101355501c800180003418540700c01a24180c4075221811011520340d10b20117401c4900c101c446c80c114020501041d03591408010080c002c4400e900444001441480180860940035083c98156942030900e0344680700c0034810301609180341e620040c0b081c4101c051207161a030742078211524 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 291178444 1250 291177194 291177221
    0xe0c27070201060f14010314010b041d0c041509030206071202100b06040b0a03060806040b01180c140708270f010503040b040807140d030b120a020d03050f0408010906 73
    0x1580d25034150803400d0329541d01c20040c1500c0ca0740d400b80700c55001e1400310394003014141800200c40041e03a9480c10380751070990040e0503110010408002d0032031002c0d103500c240154503a01410314641044d07140000e004a0042c581994410212016450300401c80a4051a0021300305a2508103500d0f20850f890b24010030400140144e04004507002502c0c0a00d00d40764000038599820503091086203c0c0c2608000e4080703081548030000000d03522030601007680500e0003013652040711342c14102a01201e042a000012415250240c0e0740d80c015800400c440b152070301c0ca0480340e50383c00c040c18140118000c09020072014499180e1144020000c1c1c9416280c08000b5941e206d2181d024900541d881e001c00c88010300541917960009002501550090000900c2074a0580c0b014010209081c03800c0110140803000c02d0351239030140000c0c81d20132401c1074088000001000020390660205d01c004040240003030600c14003096181030301541000b610050311200c0002c000e2080e00d8104980070340440d5401c01c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 291179694 1250 291178444 291178519
    0xa0807050c180f0f070e060c030706060b03040f02040917030a15050d110d050a050601060906030b0901030809010f0504120506010e16050f0904090c1e0506030106120e0c 74
    0x200300007041c00124418000200201c20700d0380c0b541e1911107044d0000b07101a0400140710340f00100c4c0d07074800b8090020301c061400110340310301041c90410202c03245034000101e289014010440055954914a0b880560554001c64410140c0c5010400900d14107150280d0b01c10100400400300c080b5401070101458070142034003039550341c0080c03120044c1c61400183c24030f907044020f11a207003418032a04c07800030311400c2140d02115481e180d013401c0101c00e03007140b800500b80704010402650300d40582c1d07142e41d50844842c1c1d0154074650742e01850b84104521181031250b00c40403500040c0c09102030b07034005e080343e10422510319118500a40c403003009004400c0406182000f086020000f030340f610100c0204c0c1c0d21048d240140422000b1142d030450002d06501a8480418400090015080704001c04003800c0400e295102070722810381ca80026044540a16424001001100c0d44220950414220040001001d4180c0e18502d4240070165410b20b4000e10311820001038107031807800600440b5114030412 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 291180944 1250 291179694 291179719
    0x80a0506010509070e040b1c03120b03010c050d05040f060c200d02070611012304030f0f0e011107120b1e040201090314031902010605100503040b040b090a0807050c 72
    0x16183c025162880040c80c114041c41c1e9a08180d44100c0c0f110a0080c580c072010840c618403030b107251204104c1240014880c4981004d19003031401007200180c400c031300902100051040061040c0a203900200e00d041d16040070030244140300c1e003120011500700b1401c0c4005d0a11100140c0650f05c1041c4c01c80e000c0450f0500c24502920114006240d000c540c0d0141444902d04142140c00340380b100031200d219580d0f00311101210410070340008204018803170803852440c003803c001c0c000050212454007130041040035070710f40d154000e203000c18060b42400c0c50310018030300030034892030000d10390009800c142003da01d41007880802c0c0c0115100303c6046660030401150308110100442d800c1d80d0085c00b2a101e00800d20003d503400344205080c0b801c0104403402c02c0301c0c400800a850310220101c10250b551032000348214240003850112880742c600740381c3d00c1c42c00c156a4141d96220f0040c00034008581e0003000c01c0c58000240186000303250044001604d88106003400b9484e2280f000c1c01c14890742c41040d11 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 291182194 1250 291180944 291180949
    0x30708163e06071202030c0a110f01030203091005130204051e061503071b0f030c050706021204120507050d06050603010b040e1506010216060507171e09010e0901080a05060105 77
    0x821008000034148070304080c43d030fa94442e00c180301806041d080d40818418074140c48030420010031594003401500300b55100200c14000740e06000902c030f60400d4010810404400d000141d910b0741e02030820301c0020701c0d070340740b00f0020505902801c000358024103050074400e0000d0102c10500c1c0031050703d556807159407102000c00c0012041c2d0310340103d010f042800002c800c240101d440c2d842150720400303900c0c03140c40d2594410131640e40c0004d08401040080d161070090010801840001d030060b40001c00c600b4180d405100d810713000d24425500007a6105003030f00c04110051040000a000c090480d07444005145802c1001d00b01c1100e0444c000d40c604044481c4920b400d005040b10801600c0160425580c66860018802801803034503040d03109801c24480b0407003041120400501440c2c3d07405441d09901d1410341032200d01509108500c00c0c060196500608100040c40040000054400d6850300f54400580e4036401c404182944400c000000260014020601c00701c1e0501c5130080d80c4c83e60303884404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 291183444 1250 291182194 291182303
    0x3010e160f0e01120c0f0306051605040f0509180708030304030e0a03110f190602010207050705090c031306060f030309140306240105040305030d060303110303060303070816 76
    0x612102c044500303004004102c54402c3c291600d50080c00c2c0c000b00b0300d49400000b051071130305074021680c1c29642d5040244070342030340c02400700c00110381c60801e14051500b000d6920810300350148502c1a807810010422481421404050000c008425608a590760b2990540c0381e0300129401d1700401c0e614401e03c85c00f031408882c00410341c3e47c00300890043e20010000c0c08801e40515504039002901500f42e040b000c1031001500004010320390016031f44400c02c0c0b070850b041041c00e5110724010102300f0180550b040040041c0c030340c08409400c2e48443c80003039041c9180a0400d5a000c00384804074200301200b495030151f0541700352450002c0e64003849540070207055a52004039400c0e00d040340100c000c04001c40d41101e2104000105148c00c40c10652292222811544000c008100642d61041e00300205030308030340c204031600f0441000e035003141340c44e2000c41c0c0c0760300c81c00b08020701c0c41740009403080040b100c603521804034941080080f1071480300f09264030004a40c031030351614101d41518440c0c0d0700c00400c56 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 291184694 1250 291183444 291183449
    0xc05090702150f06010e040f0b1c020d02100203070c0b13081f0c050c150a0c0203030f07050d06120f110607030c02240d270201050a0804050c03010e160f 67
    0x2220000720350f01c0c0c0000c10315407940540740f2030400400d40044003451b500d034000c0c0144104c0306c1c00000f5110508034104003480c8171582060079106c080800c98800740c0d541c40040021241c040d1070b03005d0459030286049056215440008158100200d400700d4031595400c080d0840340980c0d880c004c01a503c5503051307507032103c00c2000b50f40036a413030303c3d86110540160381003001482c0d020f00700716007040c0d00c00150b04c1c100790f0010003e104900c142e50401100101602038180d144540e07002552031424085a4440c0d1000c000304081d003804400660411260f076503078040401001c060601505007180340c90212807072001030300c080e80e2801c10f050085203d490207604592400398980c484145403d00707503082c802e0850b08007524511009030008407541c8003e50744010481e4501c83c0d80d00249400d5440148500d40006002181c0c200a01200e0000181d0704602150703502c242904240e5550340e5585456468001d10541b255015406e0060300c01d444a0300140c0340880e4031905260700b02040d12600c454254a0701032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 291185944 1250 291184694 291184723
    0x60f060f010e0d030c020438040903020304060305060a0914040b18030d0f020c1e12030f01030602070624030b010b032703091012180206091002030c06040c05090702 72
    0xf115080024003590500c10b8151002d40b021400310201d6640b884403c803203034000d080082c0243c40d05401141110100540a0310440b020042c6c0307040c0b910025a42c0c011401203106043c2c0d190040b940f0f42d5620a0880024190b189040c0f1102c900001c90107100070090303a0444204034402c001c1005141d22150000d44078003a03100546c03c011060a01c00050300d089500f8464442e403c000c052020401030103100e1041e90000c806101000f60b00c07600c1d920304140c0d0201c1040d4680d06105000300c0d0f0001100d02411660001030140e00c5402c0c0c1e040078002000340f040320100c2418038419100000340090344440c1228040c0c04c030111181c0c1e0700d14a00c107161004549403140c040d041b00c880c101240380003c1111252080700c049034189080c48006c100c04100f1800700c0d202080c50b915102c1c081c005240a08604107001c01c050790708180c07980d400304286015901c41c540c811a560442d110301e1900c200152061100300400f01c2e4101c8c10b02c0c0c04c00c00300c00310850150728090003602c0000f030b00d02400019000400c4405 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 291187050 1106 291185944 291185959
    0x405070804120306140402070516030606050a0902181c0f0501050a05090d090b0f0d050f0405010b03160e180303070f0801050f010203090d030c05060f060f010e 70
    0xd00c4042c1e4200b6043c01c400b4481c40441030883d42c0e1154041c2d03009a02c49002d4500981080c2039480303262400d07500e403800003040c00703116000681103c200b1740d02e1441305c540b44c0b0200416445a010182d50340f00320403802c1140c0381841ca01c03203030405600c0303603103441f1885003a5689044650707a101c0c165010381d1500b041c031444102610a140c1c0101c40c40c0010001c682c8116806040c520051044641c485408a00d407007092102008480c50f08484100402c45440c1510b00071003040002d41e820303161076107015540036850600180b2002208100da0446001a180c0700140c000800020500740c40d900f0318210701c1100150810107180201146c0d12080c0440318610b0000306500c005034003051059204403808420780e41c020084030b0910307109448500d29800c19041c103036024010388900401c2c03441081c040090014040809034000d40c8101c8078044000001c00c01181e00201c04058a5440170300c = true := by decide +kernel

theorem cover : BRFrame.Cov 291007194 291187050 := by
  have h0 := BRFrame.cov_init 291007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 291007194 ≤ n) (h2 : n < 291187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
