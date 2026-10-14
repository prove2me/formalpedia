-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2684
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:25:58.743103+00:00
-- url     : https://prove2.me/submissions/03d6e37d-edbb-4e1b-944d-bcc727e944e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 482553956 ≤ n < 482733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 482555206 1250 482553956 482553971
    0xa03020c070e0903070f020303070b0106020a0c06020105071e0e030d120e0705010903300807300b06090901060e030f011103071d130c0306050114040b03100f0305060406 74
    0x10b1800d03503620300840e03000c0011070030040f190740d8650742894480000c0c0d84c03510043c0800e000044011031198040c0400344d000c0c1024464900d45051021410b03000b080a690401041091880d4480210305800078000c00c0b11000e50320b24881981c44111040c0e056405009000c0340c600100d801822a0107014441c200030010300c07101c0a6401e8943d440d6000f80c500069251200f0800300307001c192401d055041150103501c0e44c100c400b180c151100050000100494a60000c001189800c85108403d40085140d08114150b409000080c00089240c014045c181e039194510020f80b52107040da001c0b250007030b10321007465845402c0540b0403002c940146210b846400d0840d40222010300940d03424820486a080c05c640321607030155540030008078550b10304841d000030940503030744003070003c0300740340303040f90000346591500342e0080a80b200c0d40c01c1641400b01d03ea404c52a0a0140c60454007150104a0b4850f140e490710100c01e803020403260320000c02c8a020340b0f004010b0060120301d1902a5200e00410030035003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 482556456 1250 482555206 482555219
    0xf0e0d03052d04050402031906082404020102060f0c0f13050f01050a05030a110d0207110a0501020d02030f1e1903060e0c0304060c030605040e06040b090609062a0a03020c07 76
    0x426002c50300145003102448100a10f007001c2c0c02542e00110155142c480d4411600c0b213120494403a0380c042c4515501146803c2c504a810107809a9804010aa03000c6035141a030000b030f54880c806042c01400b245800c0000c7c0701e034090142602c0d06c81c448854034035515141c00b20300400070a018000d0b0b5124080308182983d07158003c4048424100454481c1801c42d504d800c00400208081d0303c48041c0104200b00b030881c010312601c024500d241c4910807010410b0100c40a00c81010761641101b41503521014070481290380010a1798004100064442c6c0d44414030490079000551100b080d80c001040484c24401100c2118040c01504080359020030440e0740d140f0041454a400781d07050000380030208085800302d4400d420620300000941000b166a0759218042800c4a1140c480b001c465000202488204400284e24641055144008203640d0a0104216403207000182017281c0708005030141d1004280c0c480e10005001c100d40b082e4603224610307070034017802961050038016070b24000e410010503071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 482557706 1250 482556456 482556517
    0x513020a02100b0d0b0a05040303050a06060c17090a030b19021207230a03060323030f0a0c0b010e0f07090311060a120906060e090c100f0e0d0305 64
    0x400541c0d40109007819180030403400400c000e0901a400001503031041e000f1624014145000d02c80f100400169480c050500038101c0f08090030300d011700e5062000412071640e20543d80090703d0342040700254244600c01071000284280c1201d140c001039811000010300c9400f01d4014400e012090741d02100607140c1201d0000ca1080100d1522200703042e8001c40c15080c4600007001c10180d50402070800310480307a1100c2c060303822801e107210005e03403520b00a0040040c62000342124408c0c0244010081020b01c500d6034880c040c0202454010b5004508841c8031031090000c2500309400005d607201c6075841d200c00f543d440c041101c1c40e101c5520060003050b03071b0038454103159040702c0d040700c04000c40004071000c020300c4c0d034041c0c100b281c20042240d24942c03808406200d604607043c03094400003541c03032428030811b2550000400600941d0800040c14200c1c2d1500c2c45244600d000524003081402c4018109485c10f1480c1e00420380c015947d050b581041680160043c090074100a02c0c1c060503100010a2150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 482558956 1250 482557706 482557717
    0x9031605031e0a140c1905030607030e1504030c060c0e0102100e07080304090e1c0507060225050105060103050c0c1020190e0405040809090903190801051302 69
    0x3059486088940d00b50326040e40b00c1d0005142c0207082d00d2220509480b00c0c0484900c44203418159081441a81d4071860700004000b4691120b0568041d0707140740c070303001030b4542500400c00e40902d40c5640c2c1c2c40c0001c10041c00100021480d0000791141c0341040d090050030342803586401c0341c083d4507100c480490345010f2070700002d074030714141e004142110004015601814950005000c0c502c200ca601194000e0188003800c09001025400980e800320445114a050441c80100c095071168a40b15403484c0d9101c011150072941001015a0720100d01151001d40c2079500d00f80f0b0f8034800079081d003408225040d00018002c200c00d903420710454039074103c0100c0760312800d056100283c2c420a2a01e040c0c8900d85c00c10107019010342e40c0d0301c4c14a01c409200d548a039000c054000016a8030f00581c040305500128003207003413038043c0c030100800d1130250755958052141c40309462050305a41d0000381e00c900108110340e031104807424161010000d84101818000c400e0140901c903d036a040f00580c1c48a503842600d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 482560206 1250 482558956 482558959
    0x240504080a11010b0406060e1f1e0c0b0f04060605090c1213080412060e07270603020a120b060f0d1202120307050d1b090519031709031605 61
    0x5162001c410341c203541800c1e400318103501c555242c14001c04d07659618810807000305500c2d10340e0b91540012504222030074980350b174481944624020b684401e281e01ca1101c0c071080d9900107600394816400309088e1904a0300440040000b0010340c104251111726068407402144a50703410701207540c0b12310400c9020701c4103c0da01d844210091052404001c04280c030241c01101f1a201400000855150381c0c0207980b1640200b2110102403202c5001c008146c856440350b13003404070160604608200711040a0001c0401030181b1030002c030710004161030280d202070011035006050b40101c540d10702c1203544405c002403051711421400c84c0000e1082c201000341285001004041d0302c85034056a60345415401e8440781c0904500c941d441004801d02548021406415240c4071036407030b03d4070b03060284107581c041c1480c1d51060420141180030550404c06030000e03200700319200009140025002a00000c0300e90000d00302c0704003100c10f1505441010020940c182068084c1c030303981d840d412107521420341c6500c41c15 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 482561456 1250 482560206 482560223
    0x50c04050f0a150333050c0702040c1719180b01030f0812270d080a0b040905070f0e060a0f120623191406040b01020316240504 56
    0x60318440560f100c52002910142c1c0703001c4103510307034a400440401500c0580340000744020011075904004d802101310b030184480034491031078801032002441c011508000d00031604c1d40312106405005240c0789402c0003911003500e88618141c40018007030303001051080110740c504207800e40345003001045190b02c2c542041c80903074181d00e5a5141d4035403107903d003020f6541840c280110a20001c1d800c001500540d45031516485075400c03034214050070394000d450321000b540040ba01e80203064004917200e5200144a03400214000a03030042009448848002040740c0680c80c0041100c44130007101d2400c1d1002c90301c600e41c26035039a2091002c0c0305018010710b072104142d010200600324100c801d06014a2060b0070100710340c0c4810301a21840004c4c00c000000104003030082040c80410104803e120ba444041c00307008001000d043d085000c5009001c180c016a141d034038941c8140d00801c01c481d08130940300c503c2c03003000c5418100354081980a0307034208503c02103151030034032020180c003405028640183c0302 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 482562706 1250 482561456 482561461
    0x9010b0d1401020708070b010e1302130c0e0a0b190207060912111c0611190309080f07030f0f09060504050405060a090c0e09250f030906060909050c04050f 68
    0x8022840000620715070580d90204440d00c0007074003903405004807a220340304041a03541400c000c04e00b800c00003881c9801001c00440c00c1c2000d40d0380e0081c20240105030320f034009030781c00300407008031408414001e1480d080089074000141c4136215100400b009050011700c8803066108a03400ca07115400c901c01e0300d000070384184046c0080003040d52801c035440d00c28410425100050000301303208416241d51070f00951015070240c400c1c0401360060b000300d514200c01c00c3e071901403041c070081b16080a02c482c031010541d0703805100041108143c110f40101d5054074090380c80c2e187c90b140c01402a81c030003690000040068030700031412401420702c6010342d042500c8032410b090a0009000003031000500782d41d40000211710016805000b8454091040f160b076071080c40c1040c51f0400d2000c40345003d002c22254502150307641804000301249941c2c150141d2600321101e003c4084101c0152041e07550103080b89142010004400c4581d40c411440359101e40c00340d44181d0104070802003110b00c106c0d19540c1c43c402e02c0b0300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 482563956 1250 482562706 482562713
    0x150411070b060f060405120f0706120c02010903050313050a050f0109200a03150b180a060609030b06010f0c0b070801150302191101020c060a02071109040809040f06240809010b0d 78
    0x1009050140004950348030303c0c0b103804542707005001d50114011421804200c1803103040da001c9d00405186071300080c08000c600360780042051200404d4042c0e45c0d80d260a140c0200a02800b2514103244c21100301c600030070203c9481402000d014030708807030851070041c00d103a904a0b030740780010203140014541441985175031209500100b044e0054501250350764580343c0c080d6659a111200355070104500f411a190841d2103000300c0e0455000b04040c071070b048204000085003110100d50001082c43c0511a04903280d2080d10701e4034502800900785116a1f00700459590300001940c1251030300450b4003104030310310300d00358124460201101c04948400d45c50341d50030f90151100f405803c0341000014600481001384509048040d60404030841e000110041805501400c421a8440441342a074a42c01c190f40c54a05a228007901907000b984c07210221695905030781c0c170003402084c01d20b1040d00035031f1080081c00c3e5200b1440110101040000020039994541442914032000c405000304440800d00e0300c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 482565206 1250 482563956 482563969
    0x4060203061908060c0912060414070b1305060708131508240f1309050606040b0102070f09150509090105040b1f0b090a1703071a04030e0108150411070b060f060405 72
    0x1b83c0c4140c21245030750a60a003010b04002da54402d1780511030310614200741026590400c0415400026000004e000254074200303c18640b2046401c00c4400c4c6954003420714055445001e040c0d0f22243d03540c5d00d0b0070001101041042603481c851010f559134001c1e6642c0816041d98581414502030ba00c160f4034803002401d081c602c914002d0294000c0801580c4100200c00000b03031089010111080e0b000001408140c1c109070081c28038183e001d0004e04140c0303060540380d02c20505030348204410076869229007105080805000350140201400440c0603203804210b030750180c0000e40b01140c1382c02c81c420000301d04038419140c1c0e002a019404529140b54071b48404440150400002780d5031103200050006602c0032928a004915030325a400b0715115039a505144507100720a840c04a0800c400c1e40400c00040d030b100c0040781120340c0c06d081a080640703070701141400c40102074100c25081071a010301404800c4d081000303042218403d20740803520b0765070a4144184030100c0724550341c0001d81481300f4030280c039241c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 482566456 1250 482565206 482565217
    0x30103020607060e030c070f0b0909190e15010501020c09220611210109200304080c0a030e1c0203123a0608010b030a060b010905030604060203061908060c 68
    0x20100444c040a44000b403034156482110400350540c00100300700546445034481c9001041c5944015003801080f202160101c44000c0c1440350110b040511042051000c2c1d021286081c0140111145900c01c204411000b10080c0119405841060318071045440d04860440c800d40368450146c01d0841410400d4840f402c030b500c011603241d900c1e000d1550ba480325204c0644203001164110f411440d8541800c046101300682101c40b10504225030100841c40303004400c02c0440c0000c0701aa5203540e64149210302c6d005039002d440382030080100b50400c0c140c0c81500c42000f008100c40e05103410082c2c6102d064400b083c030100941540042501000e2100b41d44007030320042450507000008400c84103070300705100d620741d400c0f40c207020f0304441c1005c19003502c2d00c00c038006800c806000300014402100020790f103014400c401004191140e42094030750f40318004c540002c1c20050100c1e11182020b00c2d104020b50021602240110b04154040c0c1805600841d08400c840810029003000d45801c1455200c0754803c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 482567706 1250 482566456 482566463
    0x80f04050c060a0c17040e0606070503120402060c0f0c03070801093809010207030e0d030c0f230109050d0503060a1a0909070c05010506040506010f05071703091b0a0605030103020607 80
    0x1105008070208012426420241700c1040c06956521b08007207c0700384403134002e4031a50140c0030034007100700041c40c00001c030b842c1044c1114480382d0590340d074400140648145800e854140c007504680489845000aa80a042100b14103580301280c55051035422603180480c007600080f030040b24041140035140d1700e007040c0c1c599106009019822000862128403081d0b07003c0d282d50394000740c0c05052560009030580501c0044481c0340c202004d07a14020141c2a2107040604a01519070300c0908014903003040c5103408111240548080c8840110fa90003442c0d14bc2c0281d941c1d02801c0341a2403840d20410469204603402400480752034201401c8101c4821220301020201d0000c0050074116035810701d00c3c034400d1085a49074000d00707450307141260a4940191486008504000c140001680c00545000c101c18181c13800903113810481c2801c0c8a00660031070f0340d842c128800000e0000c4541c1c00f1a04030110041d8008030450304000105001100c0e80ca449030307000045080c801400140382080040049500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 482568956 1250 482567706 482567717
    0x720060f07052b0e06130f15091202040c0e030105160e0402040e0f090304030203150a1b1b03020304090501030503040503060c0306060702012106060e0a06090503060403030e15040302070303080f04050c060a 90
    0x580c0034009122421a00a90260481c00c175041102c2c0041c0b040152521015142c10a084c41c075044c01742b8085000c00c1e8009119030340321440000c82611500c035000f0f0400005009006d00c0c246202520010070045c041031000807200041d40000e0f0605d4000c4070101c5038460b4000c0150b6031010039410703541d0001303006844240410000000981c2e41040405040740781050080494102600518106d07911032250000c501803035010840c4580d00261188400350400450310b101c400f591504900750b10494011442140c6000000300034400c0010240003907400035001c4a41c1900c800d0003504103408100c0b4401e0b440b139800c004440042d442000c0c00e105c3e1144c0144880081c034a00b030341039001d840c0709411050015503c1d1610503914a02151001c00800380ba00300128801d0801001c6034507030200400c0074044c5a15052100000501007158404881c00800741480a04240c03900a484840701d100c140e001130b00200c049032180340c4850401d40203980c40340007400303010104000d010079500301c0743c509814800d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 482570206 1250 482568956 482568967
    0x2a0806030f01230a0905070621051303080c120402130e0f0609010b06160f05070302030303010b0901020106150219110303210f0403050720060f07052b0e06 68
    0x1424020444501c2c1d0014000f8620001510450303102c041c01002c2c06541414145402e000c0740000c10b481041d9407a40c035002c140c0440d81c1400028019500c400280c25920f414108810880501e05100625200e0341c0c03034041070f0312036151514441c020080400c22412851000c20014074001c0860781e4420605d05000c5a4400181d8813203003040128041d0250542060b4108a50b54000b032113407600004e0203c3d00b860400d401c2c000c00e013100c00001c1800818a0308d0301e0302d0071818003e003000144000c56004048039902c1da100c05442a054001d142218095824084080742e06180c40c4104010000e242e402480703411407003041c0300d440c084000804e407820102c0c6040744010307490a200602c101800c00340091035800308000390101890005202c81a0b00b1226030034040001d6205049032007803a08814203140c6021490700c00e00b02e600e602160705921a40c005502d0045520003000b41c070300f00f4003440c00d0300c102044026060301400b4560440c041c0d0030180780f0110036800d015000f031090300180030b0252810310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 482571456 1250 482570206 482570233
    0x702120a030c1e1211040b04230402070f02090709030c0b1c4224080103020f061b06040302072405120c090a15032a080603 54
    0xd60010940200203038507000284101904140394050142007400ca24081c04070907a4010302000c80d2080603184244c4401c140500301c05010b06907009400680c84050b40c0343e503190741900d550907070002c0803446401d8400c5525060714051003a01d8281c0d40241034030000380320070760070000d108900404101c140808000040080303a542540309020380380d164005607595402d0441e80c01081d1403204400c801d5400e007954550b100c1e505075003c0c000190003920a1100e500481903c8000080101760301c8920351515400103041c05200400c00c50358001038074030340c4d040d4210307183c220f0b0070603402d0001075000b00c00c5858a0000c2e007010300003040760740609100d8088e40030340c0d18042c9040c400103480940060344807060910202403503050160401c8910200e4811114481d600030b041d50244402c4003000182d20740004441c0420a0116454120000c10b45407070303252503294504c20006134410860000740f60601e20410b2154000c580c08000041c402e41c010004000c01040318013036030050509405000b441c4a07032022 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 482572706 1250 482571456 482571493
    0x40b030a090605010b04080c03070f0608060307090c02030307030e0303070c0809040f020301030f0b01080a0f0318050607150e0312010e0702031605060417040608181903030b03010b04060e010e0702 86
    0xa001105e0f5019030310b51078000c420381780403205401d1521907046041e041001000058011040307849506049081c0c1d40c40b06d001904044141d80310030780c1e00f070400041010740b41d40070006500c02d40c02d07514208501005014007950701e00003141d00c0d5010503d07007019400850311420281c80c40a10040004c00c03041c6414800d182070b40c00a0380100e9225242c81c070b48000300f024213051140940b04141c010b2000150944405410003821038016003805505280485c441c03402e100003901904014001c1984c0350110f1401d0246901c90f11202603415281c8856130017000e00110845041c40a080b11b071406503401c10544544003c1d025000c0425031204002204d162002070301030560f4640a040503240c0c0c0e14180c00d00c542c40d52501000922980010041030182c0c46d00000620f4020b11482c000308507034804a41c05a19056600708000400303210204c1040c03c01d5416040300a0481d4207800a201054804e000d01040c1c1d401409048089842440180404810070b84002d0f80803101d441200e900c47c00c0421488071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 482573956 1250 482572706 482572709
    0x3210f060308040512120d02090f041a0901060302031605130f0b1b01060e040b130803190f09170705190c030201020c1002061b07050727020a0203040b030a09060501 72
    0x10210b60100c1d04206911300443c0c111030b540d150b54007421a0302c4440a071200c0e540316152145460743d81c0402d0000281d103803402103468014024200f001040d01d0904406002821100c0c054400c440d50000401c0a030711038001d480c0a80e600b01d070108d441c00c8810070155003076081900d1116040b040701500040074480902c3c905c2c01410a00075481e039850390211101e042c040703010340040f056070400008014141d0302021956100c4e410980400481e10b4006082c18800c00401024100c0c1c20040284805042ca882428003a4241c144041121441064540c0c00303450075018041c201281c110315021160340c800c002081c01c0340c8514260303640c540308100d0070101d1009015042d41c03060300011081c411941c04200c28004c00d48103c800590003d65140025504c160003008242d00c00a1403d030764546980d10701c180ca6505600200f55a94951541a2041d001c0751020100c129020208174040280c0180d01c00c031a840b00710b55010718070b000e00b45a280340f52a480600b034400c51581c1c550b0020082504d9209550 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 482575206 1250 482573956 482573963
    0x906020307031b020a1a1f0305030c0709110910050f210a15090b0103020904020f0307200601140f0d0f03030b010e0f1c0213050613060303210f0603 65
    0xd0850101104080726520311400700055510003c0700c00045080148820302a600110014800d80c0d0340547d0000342415841c29803500c045201c4000c4204000070029041490300c840c100c6206542c0d07003002d04140d50601007001d8001100b009890170074103140580d10465070541c01c280346060148111544076501c0580341166100301044120070015032100444d800c006107600c18040e90f0444a1511415801407166101040d52410070084d540d01a405840c88080001c0c4210340780c0d01c22031501899540700302ca210700001e054010040e104014019804003c198240050540361f007010402001e80081d03668069015204882401c15aa142c12600c18020312804880c0c07098402880d01a00352200036680d039040c040e87e150305589036155141e40c100800b00441e801e100103440c5264002c4480c0c054031000e500500040c910300c9050b80c507500074900801d02036507030b12000000920f03a1411101035010050002d84a8101121b41048800d561741d07500c1884600010a04a0488100102c8490b83e000303d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 482576456 1250 482575206 482575211
    0xf0507030b04061b05030a0e07081902030609070602030a081e01120b090309030a02011b0c0f060e06070c03060e0c030f0709060b0f0304020105030c091302030405240601050d090602030703 82
    0xb042141c0c900aa00b0a10310742010a42040f00441002d030090200420014080744d82e08107076207585504205840c02018408281c551800c0c0b0b0a810b50518204224181d01901c44c43e40428044000001e40c0300071140103a02a5007001d030300b200221010003000d020669643e0602903105103e00480c0c02040c000d021401a600250200c0d02e0066461000144107030141e820a20050311651004219032954682c240390602c01e8000b03604414007840c81030072002e8008090b261002c1a0411006040da0580b1170644984c8901d5102101f00300b03041c49100001060040c1c0000c1c10000241640c00c41c484100d144015107448140c105c022900e045100d00d09280b207544008005c000d500c1e0b243c4111009880d2000c0841d00e0521144c45074a08ea12000e0f100074100300b400000030341d0494600003a10360090307008200842d00d203001d210b010040e40054409584038058203040b100000300000351a20004482e21000c0d5082d41d43c4401991990045100d5200e2145c40d4840c0c2000240288000c510510150702c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 482577706 1250 482576456 482576461
    0x1270b181e010e030d080109020706020f03010308090a080703020117090312040c0f0e01030209010b0a090b040801020d0f150303030b0d14010504050d02060c040b030705090616030815060d090f0507030b 88
    0x503e145425022a4000e0304a8040e40917103071750042c1c0c1941929401003001d82d44d4515841c1c810000d2103102c200030a006000720012042012910041580080032203804001c207459001f0305803940410f20000f8041500d41c2d00b05000d001c86100040d62007409501900e0401c030b07900c03590380203c0c1002ca904480e6030075001000e003c040d1074680d40c1c030302800070408080003e60441e4042071582c00c044c00764114a05002c2074002c4007a12031600700001d440060745040d242e80d512071416000c0d4128a82c1103018509180c10100300210744d115000b0f04020034100d400c20075256450075402001002d095a400404011016011549440140790030b442c081c00006810b15240c1052070034802003c0300c8004641280051004008058013a40d0591f2110a075445d980c0d103819000fa92075220b000c418a802c1880442c0d804684181e481c00385410f58060340b030b2705a0b02e581e043c03050400e03481c85034040d943c009401c0c400e85054171642c1e0720440110384a03144c580d1a1010a44a442ca408240c1cad108482c010f02c00c804 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 482578956 1250 482577706 482577709
    0x5010e0112180213061a0c120a08010e0a0c0e040e100908030405192003030d0c2321060f0916020d0e0a0512120a020a0201270b181e 58
    0x1071408130190004007007090500700386103d44401e000316604c10f80c1c19000300e44002c5a034014040049858081c0f0420341c0d4482c00c204005e805544c00344141090003230300d440051500c12032402007106620103036880d03040102005007040002d0400141d0308910384980380d801c20326002c0c2480303403801d114064254552a0307e002d1030700b145060002107041e2000843d403603c0100160741c20052a100050303480740031403801d0b606004a03155000c4c4600604c5000d09103240b0421f0140c100c580c02c1d007030007444100441c810300b911468010303034812440031002c1d040c0789405803c039050105080e141c2210004003070744038442448001a034584000c1c2d654225130314001040d810559010815081302d22103601b0326070b10a05804000074001d54051140e00d009101079a41284184014840c0000454007272400c15105d240e400c41c0250383d924400030480c08151034503085401c020580d01c014081d0050900754070056400d01e4000303105034000c030a0700c41108003048030804050b6107004240908942e15070b803011080c500d400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 482580206 1250 482578956 482578969
    0x20705030c0a26010e1b010e01171513020a1707032304050c03100501050a05060301030c060c050a060501060210050a050402090a02220e0106080106050307080105010e01121802 77
    0x546a521481c0308120030050080c0c1d10462000c503028540110000f0a80340c07400d40e002d40800080b0f45050301829520100c103400800f80e2480c200001e0303903090300350250300f401510b00c43c0d0000c054020889098002034404c4016014000304844058960f0014401c1c0c21000380980c1c204001c10000300d1911546607901550454190340d01044d01e143c00e118500d02c4051002d04240c08100c00388884001800143c28041c2c100800c1c414844050102c4004100c4800028018102170007024880d602c841800a402c9c40c0541c2070702d050700d80240e9083c0c0101d141c094151003d15010004891303c1c0107003206079001c520710380f18060081c4a503402800302030202c0c6c2c10443c129030004000c100054a820240800742c1c45045507198072400c8450010703540c54500c44001c116a1100c1440000340c1c1444201007400d03405408994100d41d01d03030300d8154003641c0f20781065038030340411525000002e00e060700401c1190f100b441040e0000b60181003036688060b0344440203007034a006540030001c2040c0354104400310309006 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 482581456 1250 482580206 482580223
    0x10020f120d11130b031e040f0201020f0c061b07120b090c0d0f03030b2b1205040509070509041e090c0801020a0f110c040c0206070f02060c040303030f0e01020a02070503 74
    0x260403454043d010a110040710410702840030f2110002c0300051140125084c0c2c00d0054991003660461407074649459010f180c1c01035400c07401401a801c1e50290140e0001c1d40f0480e11000404850622490000508104400f08000d205034030501c50002184403c04108002140c0130300d16801c2945492125140b40c43e060315400341c080c0d200071224101103030625401d000b1441e407500d004170364a11984006440da01c2190400300f241c05500600d8243c5208910542c265503100b1004600348140605c802c0c0d905004a00c90503801411342e400048550b84103030b0082045103c001c00000c0c0344c000980d40d41e20940141d41440d01c0700c2e603035143d104c001d2080e1000d0090051410314025854100c11807802030200d001015401c0910400d01c0d40c0501100050002d2485408041d104010303921054900a5680809036109008629081c0d0780c61207543c80400c0240c4640700403440d0924140ca1035900b18000c00400d10350000c01030381ca113014403400400380002d100345103160380140401401c0c14101420103030750 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 482582706 1250 482581456 482581481
    0x15090a031b0504090309170a030815030c150a1805030309120a0b0a0603150e0d05090d06020703020304230d02060a1205011806170615060d1113091a10020f120d 70
    0x42c8c1e803110009a12201d0341d54802401d020000e00f4a5166010910f052a0312040340d5120303240e54801441e014074000030b403051114a07911000003031a600f607500c08a0b0440e009158050304104000801401c3c0603030070001d860550b02c21a08840031a884001107000b095601410b295101e01040007484840c200c2034410601c0d414042000c14004d541e210355402040c00b0500501002040c0140c0c40d540300a101e10429401c00d0b02555111042d26009450350700500943d80c040303100c031410345a00010b807442d810a2100190501000090b9502089030319006500302004112100c1d0401407200340318001c6900900300e900031024410245070080c41950165000a040c5011705a800c50360007000180482e00104681d185107940d8203140c01040382441089030030141c0d60b080900070b050300321540f4004e1400e1005000096412a01c1d5046081920400c1440e004261f0001e00300003828078010691841d200c005004131003130340301301d244000d04254110318071060b041c40c0496400480c060f54083d801d4103641 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 482583956 1250 482582706 482582713
    0x10201051504180b090c04061e0e0c04051804060e010207020d0f02190f0906171e010213060804140f0706050705030909041115090a031b050409030917 66
    0x104210707541e0444441e08919403203251910b08100c0e6241108081c100680e8000c07001c5505490440c020b0755030340d0040041b2901031850403100054144a00d0703090b440d00c42c004500311560382d20340745801518050180c40015001c00808c00010981d6401c94080807592904005014900c0e01c0d0400c4001c0f0ba440001c0211640d004004e001c005907245e507521180c2941c4500300c081d113540305001161003050451018040d0359900100429040b00e42d403142c0044560302202070090030342b11164085c51403203284500006602c0500c491013510748481e810340301c154108000504050b100300e125140e0300d00d2540540049100c2074140f200380b0509240d1810020000c40080c29202000a580c5949081c5031051904000c400314184081010034070880d034410748014642c0b07403582081e0030500c0400000c10542881200060109009545508191046c0b40e600502d40c002440c0b45458031081559003200405480300381d81000315841c0e0b075505c1400c460754080d90303078149a2400c006610100c041030342c5602c41180d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 482585206 1250 482583956 482583961
    0xb090c09060a2109140708031c02030601030b030d090512030c1e0102040e0f01150306080c010e0415032303033c070f0905040207050316171606050601020105 69
    0x312500210740c20b41e50107161640c004070400840794000b00750702c4410002681481000340900c06416840d550210341ea03000c0d144080d5485490694034030070300c4100d024a034000307070000d1030044065004d954005010b050109040d140c400001e4288000d00071501c000c038500d10130910140c106050f400d509581110300079860040030200043e91845082514910301c0035980b07007411106000e40664008110882910b0070724100041076000d0020240102818014000380c04140c10b803190092204803042203024001040c46400110b4040d0a200c814503003241d112813400d52401c54540580c001140140b0642c41902c90102c010f0b01210703910b807089029036100b0f0061101c0070301b80009410541082e001c08100c80c4051402150a41c00e40010300c0c10802101000c0200f1180c100d80414140081d40d0303155980d840c3c441d41008220f0040e0741000d003159001b4040000c007501d0914180f0b030081e001d440410f0b04020400ba0010080d400f04044014001d1000c80701020020700780a84c982200b4240024001031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 482586456 1250 482585206 482585209
    0x405190b070e030c150307050c030a0309121803020913051005090114070e012d020609060105030703050c130608030a0228023109030e03070b070f14030d0c030b090c09 73
    0x5c8141a009440000010204210700d0240041f56401c02c5c269040e80c0d2100780f03104001d0300038400700e0b0058501c80d000d111403050851046000f07003104682e04c1805141e980c15602800100310006001c050014020084040841e10400031002d680d210008013040624018007020b007503942d4910000340001c88181880030a035040004260140002c0c0703848000088803030307003680c464030283d4000c030b44c1c5644038228040350302d0f40811505d102d86650303011201643d90b03400030315998000500c0050130a41044d42c100c80c280c600b81c039035055422019240458030b6901c80424ad03045074480007444015900220a00b0380003500d030410641c0800c51072402d4049103c00d40c010402166903119060182c442e12a10004840041841c692010748814002c016121240c500900080382100b2803920070712481c3e00000c2d1f8510140c04403803041d40d000300f02c000800303d19683e8100c44524103107641e0f4070b40800e000700c5a511034030744201d1120320b0031603402013000e05003102440201400a00740c1c901d031603420441d00c5c645 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 482587706 1250 482586456 482586469
    0x1230040503030109090c0b0309060403110c0a06050309072403050108060705030a090c0e07031a03010e150a0b090a05011502010606050a050c15010f1d040b010e0405190b070e030c 78
    0x111030b0b80040c003060354005c81c43c201664020702d03004031690a00c040144903000c907001505500c1113100e500c03002168100c00d110a9602c5e400d04094980c1720300711079010300940303100710b0195800c091400200c0b00441d0711160100480044503001080100429032081600b43d41401854010035001e005401103040c6410014564400200303034420140d10b8040100c01c21104000c40c05c001d01c4040504040c0d030404100c01006001480c3c0500813420504590701014036041c0b081c0210f490241c00100310402010f000c2c1d00c41d400e4020400c520305981c0366181400c2d0f44a03061014412800034500041e95810030f4103039030080c12812201d200716890305030140300c040d4201c0112001c10b6240d05009456800c90380010307103044400600304006590020000039001038a00c81e080039507030321510606000140da41e400071602421240542a101800c00400c0301e0704800460b143c0150180d020307614410032082e550300c85a03040c0103046982401e4103040140c107590215014003a00b1040f80940b48103015400050b40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 482588956 1250 482587706 482587709
    0xc09070c0c12140607050301050103140603030a0c050a170a0908010c08060438100206041104090f0b04030804021014030a1a120709050708060306160212300405030301 73
    0x1d50803940b14540080c06010b2410350014510307002142c25914110300020080e810030700ca80c6001c00c1c2403900e42e229594200f00302ca441020090010742c02c0c039444a00440d0b449403003075002e4585005010b01c2c140813032244400c040c450440008001c5c0d0720a9a039400812114155005040591405849480b0950f120326002e40201c0100d0700415003030b0744540812902507200c8524140320352120004a499200d10b210b5100582e004c880c52480f62203602e00a070380320703c1e04071002800c20452188000c43d5103815840002d1450017542d0145138a81c280d40c41c1d041d50789080c0c50036004903c0311001c102c03c43c0340a0b0042e075240b0b0500c0c5070254010f00301100c0c0700281c2c00050440f180700b5883d0101c0e01c2251006041c00c1c0700404000f460004400c3c8a2a10b030b5860f41d038140650001c460400d80041c05090180d14194040c84029008101e907a84141000070015903130f40c0c0000860140ca19560340120b0098080c00b285034145c00842d01c0840c1901c180d8811407001540303180342e1601c11040001080e004819a0b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 482590206 1250 482588956 482588969
    0x30114092206180c0302270c2214030c10020c0913020a0b0301080c030703020a0302011116090605091b0301260a0303020307021b03060106030209011101060303020c09070c0c 76
    0x844541c0d25000003e4008052480030480c03010404030280548981d64004a0b8000e0b1a0103025550780030740400e50b80418100081d4684c00000401c1c80c1c1540a001485030030034441c1c00c0c2c001425000040b0422a01907880580e00c003081d1002c07e41280b4083c8803048504104a820708000b1448100283d244d550717540b0468851000c64002402c00c4408821030301070207034000d00120032143c443c01c13441d900c1e41003070245841510502034000c100c0c0c14001690f40c15290000d01c04180180707546e004554403c01000d003a00540150292039100c0f104c41e800c864050001c082c0c01140c06070422045c0009124000d040148075100421140554000c0300100c0b41510340d07040080c40c0348403210743c1070f010a040600c01c1d016640b003490f40341c07421301d1740c19805140079200550a848032080441f002002805800307000c0c03a4940c2100d0010480e9a0207030f8010b100064040c10400c001c240070801d03903421210154010f80168000402400992030203540307007980301503241055203070300b82d541d01ca00f8124502c0d4000c08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 482591456 1250 482590206 482590261
    0x2130902060d060b0304030f02010612060504151b11072414130e070809071401020a021201060617250e04090c0305070503030c031206040b0a090203011409 68
    0x2a040d501d034803003101d41000e0440ea060207015a100da07000c0d100d60003100e00340e00142004d24818051071041c0070720710403540d66603141d000c4400c207602c03400c0041c50042e0049508420410a249104696015009003589290f91112a0b04180304010b49004030207c5200c5c881d820080062000120405520400040301140c500e14450070b040b0030b03540158060b80340000e1071800705800428800b0710b04240192901506240c0e55512002c805489880040d180428950490340060001c0c0304012003403d41c0150500c12500c1c590303200d80204440c000c2c00c18500308103075101c0b003090120b0742e084001c00d1b500010381c180101c1c842c5000106124060100b0001c03802850700c900300911414821b001031403440200510800c00f03a030740c0e17143c60001d1004500c030444050290040019142c5800700507034182d209044061490030700072000c08011010002e0180b94882e0356a490b039a0241c4500e40448003420351300c0c800699a506000d52038007038941070b0303041c14841c2810508014801c154400e10b1007030703032030700302d114 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 482592706 1250 482591456 482591471
    0x90501060e0c030a0b01030905060a090c15081e04080a230f0702150c0309041d0708030c07050607080a030c030b03031314040c080c030705070803161206030213 70
    0x10a000d40031580c003107051505070030144034a0350350040080d400381080e400108149038280d0015070503640c5440000c1d0154002c180002d1400c19103800000505100c1c28000705c2040c0ca5100c41c2800c503110209500028600f070003002455a540100d41c9003859046200301c01501c1d2585e522000c5109001079071007000a5061040560720b982001c1801c20f0b42c91121554580f011482040c0c00798118010580c800c420120131005100060000c5400460f03c10024500d0071405806102c054403e6039030b804000403802e0500d101c4020b0501c10840a042c00780061640c48003e820210301c3c1601680007184600002c205040001c1c0d10641205c00c1247c0ca030401061004403a4420340090440c0d1035459058080060081500b280d185180c5056440c0258012920119201800100c2e10101000008601890045030521700903c01465020305949041460540255036001c1c1b030380c2041d00d80240205224a400880ca50058500c030740701c1d064010704004061940e00041d00e00c042074400c140580766980314 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 482593956 1250 482592706 482592713
    0x506070311030a05070203251202120a050d02070806070807030c05270a09141506070501090606031a040c051201020d060305030711150706020a11011d061503070909 72
    0x4807010400c10020390341c4480e610749000d00680e00841c0128801d005592820280351404600b5403035662101c1144000c40c1d0800044208100d00d00303000b6030b401405900013010340042004020000c0e4801c0c00500000802d0310400380ca440210341005185404c00d804000340380740c3c0804065405521850041640c80f010340c4140d8480c0b0480b100700c1c41205031150f1184051682c4400e4807034240080da41140d00da0b6542000104482c0c45142640040010340701242c070002c0c0c9120740820500d00181100d00c1c10303a941d81c1e900d0861f85000e008850700c5842c1c41042040c00b101c0c030601c2030400a40d4a00c21142d1030720303a9428a0346503c0d401a035101c0c1502104000581401350306032a04541d0034030082200076100c1c20202d82c3d98020200481d8501c80e40c0e446842c131410f0035400f8210130b0400301c9085080c07130026558600079402500031b00c0d0401040454110708400240581c4c1d038101250b18024100c0d03241201018109540241000c01401048101c4c40749910001114011070305c0c00100010503940c9403a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 482595206 1250 482593956 482593967
    0x30c0306030f0506070e030d09031101050909090604050601050f1305090c03030703031e0b0310020304020609090705120c0c120904060e09061e0f0606160b0c070201090f080705060703 80
    0x1007000c1c0003004000788620402070006512405050701c0e444401501400e1020140d403540c0003008200000c1e8564001c10009555054142d0207001c1410901c1c140101d0501144011400300c980350000c0c9d00c81d070700340800d05c0020f2104c0c901401d0203942c6090300f60200d50115817000180c0280c40550b135645c00001d464640280f004075041480201903e660b664241002005080c82c403064042c0051007503481104000319100d480d55041d4050b02811000400410200c0250001041030f41c0182003006103181550361584042d102d5055a19103986501c654000d8480d100c0d001080d5030303000170080040c08140350b40004c1e4018603030769042100703541e01840d4000c600500713210741c04800c9419518051100c042c80c00b09009114a041414000007582d460110b0042e900341030320489400b04600c8086000703400c00c0c1d00104030844451046000702c5c0031503620381c018410b04503400b4040040200d11001190790002c1290002c28081111600040c02c0516032034588180784503c40c030500c2d001512004060103034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 482596456 1250 482595206 482595209
    0x702090c0d0f0f090309050a051f02070902040e09061003150f020706020712021204060806010f0e03060403030b0411040b0f160b070806010908012f041a07060525030c0306 75
    0xb03080c081103804821400103444031107402c40c04251a07034000710b07035410400b80a00032038000519102da03031849a00d0100d01d84441080316000c40c00341c0c01000c00c0c0c22507140010070040181111307507a07049c0b82c2140e456041c0b050141c1001c40041500703c042020800c3c1c400000041012058002048510015408024450180c00030300490000c42c910043c40402070340e1081e100401c1d02594000021500300d0f0125100300d01605001c1410f210200c0d90551160045040100c460b0400108141c40200000d01e0b20000b11022000251074181c8203015007407900803400040d8080c00318600b0035042c0120140d03a40143c9a8254805001060170030040200b4107841401a403c5040c4041c5403c04903401441d40300d0440e4002c1c08150526400a28058140309000302040c1004441290941d403001800710b503c0c1c0d540780c01101050038040032860b1020b507084140f00724808010300342d03101c0d418544403080c1d4400400741883d0f5400414141c0c095800311002c20400341280c50001048031202c5410350040955 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 482597706 1250 482596456 482596481
    0x31209030c040911030c0105070f060908091801060216032d0803040501020306090f01150f02030c0f010f06050301050405060c131a03060117070c020904390b0702090c0d 74
    0x103100002042c80350444c0c140194a13416030039691030302c00c8440192020301ca040c0c80149041e0707661886801244150303100582c4907105800d21441d0804440004001d00c10030f14440004140c0c1d14010843d041d010001d45000c98214802c4123140740c0b96803203540c2c0303401a811010b00c400348140c041d4a964490f0038590444913a2000b0304031b840381400c2c14094001c1d04121001d9005801c1d40740803a038901802c000180c12038a60480e145203402c00d000044a800c01c40000c8402540701c1400002c086400c14012002080c11355800050310700d491605420544030154040c9000b0f924010610010500108000e9803105542800b50b507105841072181100041c2c943c01a4004580308000080c00300840c0025806034a090380c480084080300c4044c1d00c00d0701425038914003c1500c030300900f07005080c5a01440c0d40700340103180311420428041c641019481040f100c07a84040140c42030030502100c5401d000d0003800051039460300700100d950108514040181c80301000c8940440e070704084c0e4a00d0303000800070490 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 482598956 1250 482597706 482597711
    0xd0807170a1d07090c0c020d020f01030e03030112020114030705160f020a0b1b0601260f0111130608010e06010509031f0204090609051e0612060f0103150902031209030c04 75
    0x10640b03080d40d1a03241a01603802d2072424203405051103031041c60200380d52a00240189407a00c0320303908100c030000c1c0480415060586030b4036408801c000900c06075000300651100c424040c0e410703200040c02d501c00c8a0005040710b01c00e0050001060307000d016600780302d01004509003a200c0c81c5c28060003040c43d15a0003507001e020001c005c07a00c01d039000e01a0000d21840440440c1c0b00c0c258400542e00e60509000b0003c02c0658104001c0c03200030000440c0c0b13012840c0303100f61110900c1e05079004e800d44a0f00c4081524401000a0042e0800f182e1031004008001c05d161841b115410000c80c2030300c5071806000641000808642c0e42c100350341c207020385e800f44101001840350b80e461010b48107020f50410304c500e4201034070f40350000031454114050b40744503600a190440b0583c1011898800c12200070344100e030010300d00c144154011400700b0000c1e00030b10344648004d0956255140141c40c0200f2000131424072401d0900401c010b80b000109440c505981c2d203185610b1b6403440000c24502550040000d07030060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 482600206 1250 482598956 482599001
    0x601020d0c2a0308030705040e06030f060a052a090913050d140d0e061005040b06090603130807140733121109030c03010b28030f140d0807170a 63
    0x7c0c0c1040040c0100c4188411021107542c17800c040513220f0780c4503411910385812900014401c814240c0c0310710b600403d40191000b205402116001e102c40e04080d09440803540015a01e08924020043c20741c810350810b102c4405d007a031561829103c03200c2212041c18800a8400320740c0d8140000b068952684a041301008204454120382d95920401e41303184540d0205480d01040030300b0140508080782c0d0028083d03501c1c0c007810070140112948020b05c11424400b0f001d00000001d01c1c0200109039031405240700380c00d2404079920135410048194054007100450340060b4404c509e00e0422007010221208015240d03d0603100d003076500c0c480ba2403503d1050b914000c00441115040c40160101c0030080e0b048506824004060508a4100c0d1306202d60103d055805204114000310007000500880c2100184140e9a50381c0d008091400100803103c02030b0704494402100410002031401c072070145032148080c148000090728045820f5641c451124515000502040b09500201012055000c0d01046031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 482601456 1250 482600206 482600221
    0x10b160b07021207060507080f0903041a04030602070309090e060415020a020705040c020a0524190b09010605031f03200d020a090203010e0c04030305040605030601020c15030601020d0c2a030803 85
    0x200007c50384180800c120101040100c400424114841c852560007146082e0030074a880c00a1203095809050041d0300b004040000342845c00545000c0d440307034803161241420300103210290f80400280c0c50659000c90100700100700d4a60b0920240c0b4180c42005aa41c1c2c40e201d4100d0400c1d885802903a0000c0c10442810302d821740c005241c561443c003c9060307403040b1000e480c10303001404003404811000410400468140258071400318203203082001c0004640e010400450480c0384242e00ca040818800320030401c51042070340414000c01d49007803040b118a411940d403401014800160b215a845d00f900d040e41036500c402040a103110340040c030130002c0c43c0daa403a00c5000307175009004144101c42290041411000c0443c2520241c80e1b064880c1800c0a0805008981c1c1c2d8000400c100d0461280b18254105d544403014980c24001241ca0140c0d030301d142c000c0c006031811807240d20b100200460144040007055040801c00042c43e900c0c0c5024206203d40714204c05010742d6604041d000307140000500100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 482602706 1250 482601456 482601461
    0x1d0f12160f03021b0603040b0f130b01151106130305180a030f02040b10020705041e1e0b01090302010806040504171602030d0903200630010b160b0702120706 69
    0x101c16484e2000c01e030000310030081c800e8901082e02c0046c0001355850105806400c403e1805600810421205013840502c1c0c441e0180340740f00381d1010780d030110210017000510354000034000b00c0400b014014a41401d12000c1060130417203d10015040000200d58a041c0f0265194018040d842c010450000c070740c0c0b60704107070803000d0401c1d42c107d11461804a01000c0c604100b42c0800210802c1c0e009490218a040203100103004150450b5412110030125498050064414050340c80034140050b5034403002008018103c2e0125544c083c1070000315101040141e038000304007540705200b6940800c007500c480c500a01320280034912040c5013500405c42c3c0030070300c01c2c003010701c0f44083c000c5007151000c041003d4140c92020b150300000d03091107860401c6e0b0455a15907440b005903103802422091400c880f003104942c0039040110301081d07071055840c1003003e41d401c0c49035150141810481d0289001c08102c1c03241c090401e480002070013030550800141c1e0b094000d020300c0e1044285811203039907442c0c1d60b1410000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 482603956 1250 482602706 482602723
    0x30919050a08031b06010b0703030e100c3f0e010905060408030919110603060d020a0609080c0a080a1205040306020d020424080105120708010f1d0f12160f0302 70
    0x40900310100c4113100c0440080c0c90350407602c600c45080e140c451151011000307011099150030582c810b20035050600e0081e88540c2104514942d1648503010510040122030240c04c084c000c0e008a81030340c229112003421130030a88076040e1050003d00c813110f5001c41e50151202d00006402402908100424440103000952065000009a4031307440c1800880c00e0f01c194001342c015246a4400c541040c2900b840d000a640116006101184c0b81d80300398002036032541e10f42c0002d8001800b00c401002840b404100070801c50034212858000203040900c0d481da0350400200140c080140c262550303165500800444015541051065584003500e03550003020b5032003441380c0042c00c33100a104440000d02da404515118981ea1388800c017076480e080803c81c0003030b2506c50303a8000f80994040010300c00c400344260441c80d0162480070401c400c3c8180070400700c018190112015400401031400f07002008940132014046540203642c88403542044403120084e0f118008041c004401002c2050540000d4200c6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 482605206 1250 482603956 482603977
    0xc031202160c08010212010611010e1c02150c090918010501060f0f020303041104050910021306090f06080a020a0e10021b0a0e0a021e180f0d05030919050a0803 70
    0x1c0301075070341c41e400750807440745c0c1c10f03504101b6407102c0040c0a52885240f101d0044110800040b80a0190b411010305021004900700f00c03503828200c00c0c0b4032554042c00740c110a903800c0c0a0000340307803400662910a44c402c00c105035101e00c001c400001c3c01440d0b1452980c850040314002000345684a00c00034200b400d94805140c040741c8005132926a4520000440380308030760184a140062002c00b09100180c0b10190202040d8090301c1c4003219010ba0340d10241040c481681007071950785207010b102928040c06500503101a1114070028403010360040c2c0061b810228034000169038060388102250005003c2015607405220169016103003580000d04005050101203501d480c5068542046940c0d03007944583c03001c40440c500003c06038200340c2d0103850015a0203020302d10700c0c0602c6c8000f02c01d80c1e1203a01442000790341c600c108003803400c0202d80c46031a40d205132420301844019468150381c0e40100c501c60361284070a8010018001c1c504103521006150180110700b8150302d98405648a400442284 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 482606456 1250 482605206 482605223
    0xf09100e0106080405071a160204020c010f29100c06200a02010b010323060406030804030f1104020a051b0f070b18030106030b1306060b0715050718060c03120216 71
    0x4076040303031810707660020b4640002c0602d180100c14108c16400140c0007006980c0a9420302c41441e83e80300a000303076189042c0400b40010182c41030035413054200201c07402c1a50940c0e103c001c012003034071103000c03801c441802420101c2c854030031850503c02422005010600214015521130b2145542c24003500480c22241c00900070560510011001c5810030154120b0010f809800c50308040c0710248110340295001d03001040d82a1280c503413042c0ea43c0a03a104403805040211103006005e1410016a05e4100840e0150710740710318a8801410b40c0114644007030307000c0d45401009041e010800c0032a5182c1e4810301540c40c2e0a0f83c1d0171901c0b055400121580d8080f09001d420760142c0c1c9418890f880030f90394401e04a190f86d844415071016101c2e031500c2c0031a11159240b001281000c2d0305e002400d9841d205400100381c03101800016001d4030070203403464040c0042c8407600050084c075140030304281d07900791a00e40c0658540d0304048803e10f40d91480100b4281c800a2100004541001c0081000d40a0f8042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 482607706 1250 482606456 482606459
    0x19080a0314070237050d020d03060509060f06091801140d0218060a0b16120309050606130b0d06140106090609090209040e011a090907050f09100e010608040507 70
    0x901003040b0b41440044c4c1143c2804500210300d00340c1410400b0304d006441042c0c04004c860210b15200700101521030341e00032908161503c0e410031408445050500c0c042c081640b5101c0071500a2502503e65403080d5510710413446030b0340f2100f0984a040e403000707100110205540518032800f0000b13001d514052022184040444d0800d05000388100c2e07400351101d444442d1111b0310344031400024002607403240317032200000365070449040502411800640e0103592110700e4a08240d00b03500526614092600705000c90300401c101003489644480291003021030311090f0882c98000340a5440d0303a5a001c480a486003050000d1a03000766042407403400000d800c0d0341c0705d003002d50314101c1c58400c44001405c241400e00c0b00c00b030303550041c007903030b030300162000c29040c105031032041c04d5511b40c08880000880c680e0302040c02d860138a0a4a4000010b40082c15240f030501000c0744280b01c0c0f145510317000d0882c102c04549104030004200d0000c000101c40d141c1e00c0e50f11440f00414008007520252a90301c04c4280 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 482608956 1250 482607706 482607731
    0x60406060f05150d02030601110f010c0207061b11062709010602030910140d050f06030c01031104060e0f0306040f1718011b120c0203013b19080a03 65
    0x301402290301c51000f15060a40446075200a90f000130451810040304c0040031102c65400c02c003c4611844110011802c900750b250000c7c90a4101d80c410800c00c80c0c13081d841014220740000d840080e54020705011a400088004240e8070310403d140702014a403441e00c001c00f401048018403100700c0b011078584101e42d81c0e40c9800c07070744c0f4080c2408941e40034203034041080a85029130199114003d5404078242803040c11f82100e011034808895240100700c80308208030080c50144a6208042c40909040000640d10002d010300c0340030b01d003d00c005000f4103140b200005d9a40242488035550020201e419500d400c0c90003245002c01003904413614409075000040c505003000503034400d00c0504007450500c05a4000458914105888101c005941660208049001c800710050320303a03195119000c000c0424810703d82140c0c040b600e000b030307003103c12112020200b904510312640c401d03082487c00d82c0310200d603440074245040c1c1c1490b1031000b152244020208681c61b4041c002141c03040d10b0030070200310340d102c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 482610206 1250 482608956 482608969
    0xf0f050a1d0609040c0b1903140702030f0d021312020a0b1206090c090d0c0614040e0c07140610030314070320030408011e050108150105040b060c060406060f05 70
    0x45031180705000d504005401c2d801e003030002c240c0c4a0b001d00f0030580307402d9440b00780010a510480d2071408070302502c03000402181d010b00544050810030001a4524584403100a41380c1c0240c002d800b903403650000d4006801504c83c0c054414880c05022240040e6640e0340034072009545c40340342203020f401042c000040d111301100556569103004543c00072146c0d00d900420629080080c044c4240c14814030000c0081c0d103c41d1038554006200c2d000700880c16080000160140c14480152403000704e08110602006841d400c049800210b00441507444900c40d25102c120304448420316002c9110b90000c00c0b140c0001100b50100700c9009444480c24200c17404104c40c100e1050b4031000e03010600507040b03085180c14594151600303130142c400f03490800d620380b515103003591803c10038420350848003480b070070145c0382501c910b034010030154000704070340604011450b40c2e41c40b0503c1590710807a03a80c0500011038484034110b400c0b4148603c140c5116103060702d01440180003a0290384480721000c000401c5030305185 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 482611456 1250 482610206 482610239
    0x50108031303020112090813050a050d03170601020304180605010818060402090a0f0c12150501090b09040908040602010c020c1522050d0b04050606100806010503040302070f0f050a 79
    0x740018100504503001550300807495211540340503036908800c00458170324805403c03200f550000001d40340d0301c0d000402429501c0c03900301d68400e1040088801c0043d400c40340058280100003600309071940c40c41d005030304601960340030807658440070050a1010b1800da0100e825528240c0394011a521660890210076844205c209490303440280420050300c0d103458030580c011061400030035031840c0e00174180141e80081d510000031990034608080c00e4060390044ca80302e04000501c03007940c81e05e000c000038083c071068800d45080c00070001e890700d02038031640c00500c80560040c03045991581e07900c0c0003e0080440c4e08151006000741c443c14416886c012681848140c840c0c406c05003040b184051036031564000304111001d00000c100c0004e400e8075010300108039036010789940e40326481c09050150400c0f200524061141d02030380d000c0c4e104141c10081c00c9030429000c0c60043d442e42d036680382c00e1345002c3c6903030404040c81c03040c0c04d0002201c18000c4490f0080d1403060700c100c011983e40b100b500300c550288 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 482612706 1250 482611456 482611477
    0x301050702061608010e071d190504061212050705030d0501031101121509020d0605030a0c290f0d0207050610150503060f220618061202030c10030905070b0403030305010803 76
    0x110b0085281c7d40d03c183c010070480758005a2124000311000c00203540150400300300d18102d95504401c0090345004d201c1e140041c820440750701454001036498400c4005114003200a108002c11210140401002512080d00c07088104105958490070854001e40340c00002078001080c0c81100c80c04c81c1d00d203010b6a40c43c40c0c51078440f4580c40e401e0030094070207900310040707040c070480d91100c0005142e80c040045629280c02030015184007403d0448116031160116184010301c50b4900f96219042240700480b07000c0e2404241298484040a0740e00000e440b038080d003e0003510440060022041c4903a03500ca0840c0c40c01c0d80d070110356a41c40c2e2030a40c3c090008444060f40321444612a205ca401c00c6101d400700c0003038009010311051694401d2204032402034010289039040d20262002c516802e02c81c110140074207003074002140c001980082c3d03903900300702e4031a40100c0e00910340ca41458082c5d0030007081c2540c0a400e9590803034845505032119041484164000ba041c0030000410003c0441100d412000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 482613956 1250 482612706 482612729
    0x1a0903060a1e050f0a110403080f0304210807020d030b0a18110d0e0c060403021021020a1106150d03030e030909090d091e091a030105070206160801 65
    0x15480c00d00001401c41025010b14284454851480040c862092a1240c003003641441c211381040d00651040700c18040c1d070524654010081800030820349029500401003072032a66035290340d5803402121040958003000c4500c503e00c9480d05042e50000242d0348915141d0703003101e100602050040f010740307407a1015903801440300c0ba0705125a42c2494603010200820701000301c2c044a41400498a690240301c50b44841c1d59141400300140070309010440c40d45034222086807d0a0441e000140240d90030303242a4144404c09002d807903820310307008080d200440768040864640d80701d204041c1c50410301104c4001c240c0200700025680c1c62034540340c0c85003030801a103002d041c8a19a0380a80c001d0286421088482c803003841584010341d03541066a01c03444c0c2c500c000d04002c6c2a03225000d040f1490a07013090141101d0490842e80e2110081400003c503041d55101065069040c0350510301c40c010030812603095401c0030200005940c00103010f900400280d1002094a03400d5201201c0f0700701c003030044000305c11 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 482615206 1250 482613956 482613961
    0x11011a0d0201050702030307021c0c0801090c0b07050f10090b0a0c050a051c050717091203060d08040b0a1106090c0907031d0616020f0f0a0b0405070315061a090306 72
    0x140f141024004603032020f01200d02d490415000031325210072610010003001c0b8409120001c004281d00c800008181c41c0c030080c00705900950b51101c200307215004551075183c0100d806410300c803003008411146d40030541a03640d5030229065400c003500001c00c05840d0807200c240480c43c480c1607882026420303040e079602c19051803003c1d0801c44032544100c0840e00016051300d83c40580c06000d1142d94040e481d01c1d140c2019414018208404800008041c0e1100340c000540d03025485c400003044036031000044690501002071803030044c4150065400448403202e02150404800d40c10a5100d00f409102c4400c880c00c0f5030701d0030400c1c2c1d41c0b03144441030749130007212207004110118000d800220b901040c9600c4941104d028540249c54000c0c221450400c80308168541d1401980500c142000e85500c880508917090020103c0d03691070913603400041c00b07490082c0018060140c1480410061a80714030391640121524440002800c03143c02075125003860000c0a40099080350304580441101a015041c1903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 482616456 1250 482615206 482615209
    0x15030b03120d0b01051308102711060d0212041b1211040b03010e0d090503121b010e0706020d030c2a030905190e01170318060d0c11011a0d02 62
    0x1d03c0360340b42682c14803c00303001480740c14803204030140251803010020403850103004c000005890100d0540b280b1703610300340c0d80c105540254825111415800c126130b40708401c00c5030041003180c072912410000c510300c0440d101c0d01800000c8a060300031801421008a548140308160004450511890350020a41190400000c2150302e0804480000803c00143c18500b0000329003901c84503400d500c000e8005a10380c114180d0001c1800c00604070540041c0f20110000c01d00740c0c10b5100300e020754a5084415512041818425000918004490400d0341c00ca1030355850040d54423007109210101203030420400c3c280c50381c0308000c01200c607034504002030203544095545181124107608140c3c01c03c6401c00c40801e0ba52034015112044040042c03800c142c517498005058411141038104210741c8100300d28a1807103c20000c1520703440c94000388a038080171000000034065104401c81000164103000c1c0e0b91a80980100c103800c1c03044a50720007880f079004003641d240d030910708078445281d000c9003004240015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 482617706 1250 482616456 482616461
    0x61006050d0507120c030b0a0905071706040e070608070f081014010c021c05010615021f0b0a0b0a0e0409030207090c03060b070c15030b130504050c0a15030b03120d 72
    0x640c3c03070820b0b861846001880005549041310950702083d03d4800403000c60034107000b040010701440108010600b40890000c0041c01481c0100106800d600042a40b41d0754030760001c101c0d600c040046a0390541d640001910b10003040b03440801042c40ca6a001e50141e02404195200b640345402030102d49003454000040260184091810000349145807001601d641610905170b0201d9400e10909034124a001030946000d0341069040b5008150303021001a000600560384501c406040455400442e4203040101800203181c0e60014100c640091411401070090007000340d1035488031606901c41c0c06100544031210001001640315000400280041340c0c031491071200c01f0710b40426026516140e090041e00402c80036100d5103510141000b0309600c0104031052003400307040501c0000c0808001400420102d1001c48400e92100001002c00000384440781c20340c58028003440744142c403a4524414485005000c00200307281440304105440d0004441c81b81505803807401d807409002c96030f007130007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 482618956 1250 482617706 482617711
    0x807031403120108030c0708030715020c0a080d0b010e030613080f0f07050708190f0b070c050607020703030f14180307050d0605091e151b1605061006050d05 69
    0x4541c0420700c5460001045070002c5030084c40346000442c3c551002d501114204190b69000000a9008016800014540182040300310080c1080145c6400001c1007481c14940e090400500b50707000001e041081c552954000d84c0c0e0407000380e83c0c0c0b0300c005040406155407024103458500700e2420001c15980007480030002008001c1c1c0000300c850500c019103610018135040000c049485403c100c4d02841821030401010090301d20030546150b401403181c4850071048105c40c000341450240d8000203040301d010700c5421000030380c4a01290050310700124000e441c3c27040c90004400260300c1c04010130409124442442d4160702c1c0c01e5403140b4007980400c5800801040e82056034143c003c041300042da50b5070f0200c0b1007080304e000d40004500e40c03810000060900c240812510200116000e01c0004600002541e14845000c2c144003441a15481c3cac0144106442d42000152240001651050b505806101c440c020303101d942112080d455003242d01a01c00c410b0f0080e070001030010702c21101326400c190001c80c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 482620206 1250 482618956 482618993
    0x2010e0406080c100302030105100302220b0c0705010201111b0f03070b10050411040302062b0609050a020c150c09060307080106200303060d06060b040905011e080703 73
    0x28925201404141941c0507540202e082e600200051156400d154043c010b060140d803504618640c101000512032031444550b5508055002c641a8800140717a07100c84018000c1c0c14040c0540b030340d61031402180790300c0020b800d01107000d031000004075940140100c80c6809010703001070b414030482600711038440d4030300c28041c1140d20510b010103010010600c000c164190040c209410b0360318202d421005541d10b41e50000340518076001b1005544041002a2030959174100c50059888820485000c40e01c1c030003070388035207900702411010101c0901a41c0b01104888000740144150f550704a2540220700410a814155400004508550104050625911410180003a410264010042003554004580c10310105001c0310042c4600364000f0040c000f460b0803480492008400000d2042e12404050f18150007400c2c001c10003002c02030540c01003800740c030792821195241d60780c422190000d040d0078031501454138854001013031991030300c0219509440718100280714061031036480300c400078070344103501 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 482621456 1250 482620206 482620217
    0x30106030b0f10080d05040b0a170a020d0f0603080405060702060f0d0f1b0c0308060a05040207050a0303270f141b0109080f0705130902180f060604140d0201 69
    0x10002980700011503004251000b4070162038036141400b464005125004500c1343c5c0e0058050b951803e521104642c203503200e00e42140d48491300e000003500c8814940071038204500b031070000c010341d0700c03050750141c007501c4c85c121000e1200b8042191031500b2a00c16000c007402d8650100800c0c071013401d00704005c00d10948041d19044c54450400024021900706540300c4408035121011000c8115050181140322001444001c3c1d12050120000e0400c450101005041c0083e41c400950990390f04106c0200404000d0810340d035910b1503103811074883c2010001100803a00d03007042880002a91004500405982c020b1280380204a850705a45140740310022604280c0c0300c01c013101144014071003550000011410f004202f45c80b00000340983c6601e400a104940c061660603d2030900040e80b4000c03200e059030309105540c01150918050100144040e4000404003800a8507088400405103d5107114101d030b203d541314001040014030691180000100c044405003055140440f0424091813050500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 482622706 1250 482621456 482621459
    0x120901090b0301030f051b010e010e03070812040e0708010f0e0a0b0a08032d04090e0a05011113120308010303051b0723030102040812070c030606090c030f2009030106 73
    0x140300d050b60090700101c8900110440b800c0c10001c0400c0398014212424152201d81c00310200000c10b402c0941d40200c2c104440380d8074070112030300d05202d8a00500351140c00d45620400c03038800c0240d0759200d48100e454040e00c440008000a03c91880705058910401143c5041403800b809071110a0b00a040760b80710590700c401000b515542c40c1ea40c0401040ca903406035844996405910000400b070800040030310307000900e00c0150403201c501b140e0503111107940020b05024010000d6241c02451400105698070b8410032100001540c0040c0c01400101030061404940381e241140a02640760001800b0503160001400028050030141c04948034080000310410001c110141ca00708959100e0134030390340c041c1d0307064120310004000844000300540c0203524242c50f1502a5968400c0c0058400c0e06400c085075070002c1001c0400320400841c0c11040034045941c039002084014003407a41c0605c0420702d00034146020b6070080c05100d01102c00c03074512188468400110401a40c8010340035680340d5a02d400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 482623956 1250 482622706 482622719
    0x726010c200c0d0c031b030b131707050105060a08030906030a0e010b130203011d040b010608061809061e04120f0e130911090907140607050f0c040c050a0212090109 72
    0x569008a0b01596100c40c4c010f1079420418501c081d04603070348604008080061011805040205400c0450401300304041c00309800d22142d51018110030301420308002502e1030501805400c103d0141c10110b402000780307584c404801c3c4e40c078864441c000d60410000c3c0001000c1d03000d1680800c542e42a00400820051000b400040302007901081400b904c550100050240310304035a032200d641030a02c6a48421803e058440c035500c01c505100e00070810101c0030009402d51180381590200760b03d044c0d104012428104101074590f4822149480d030460320b600c030707040c85207819650a400317113170401149080c60101400403a80700d000c1c2c401b081c0030720a5448040b00706480301c10491401d40620800010128011314022018604e00415144130baa003281c14003030a0700006c980c85080b100945010781c40345041e140819410301400380050481c1c0183d8402440c801c5d0040384401011004440410040c4a0340100b941d00d40509000000141d000c420388600c04c0205a0040c01c404005051210780e90765a0782 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 482625206 1250 482623956 482623969
    0xf04081e0a0903150b0a03080d11030f06090f0c3108070f090902010816091212020d1805301c05030105090604021b0726010c200c 57
    0x4540ca000110340480400a0040f45513807140100800c14043c4841846400040d40503141404040c000c1c0d00b001441e000c1c4501c0c942d11081e10440c0d90b4900984919002900c0394030000c0884003240990310440005500017241c010b0035101d8020012500e05040c004241c0440b0100100410ba08100c10120010800f02000700030350001c0402e0b0006046d0241021403401003a117403640301e969058140590140140e80100b0039951180011b01c0099140c000070a0407038485605501026006440d101040140225003034100d045035915001c60f000d0205a0302c0845410714400304103074110100d59000c0c0b081745440383c0401c0202c50b8a03801074400c00e1b1840c12080c48920f000281d180d407a4410007983d142e41d40d08180030b5142e4046810000d04561400001c1040301800900c060720403030303000442c0180301c11801c020b104d201e424101140c141503150f114180c06c0e0000400001907210185645005030b940501604405841d01d030b60749a425596070040e954071000343c10b20008180a068280c100359181c0b10b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 482626456 1250 482625206 482625217
    0x60b0313050106180f1107050d12020d150303021608031801020c040f0504020a060c0317040609140601050a0b040506070f0507150203030703110c0c1c0501090602071a0f04081e 77
    0x791000076000e844e40c2c5548100c0d06c499202c16003002080c00b4401c01b003180859030480c0c0b06241d091075041702c2d501107a44002031241400c2000c06c540b400d83e164078041c5580c05a00141c92003070b000c8440741c01110070000303003104143c40340036002c1c1e008100c0e40c03014100041c0381c040c2d155418011901c3c08070243d800501941d10079115641e9481d540c0b400c12007985071600e0020000c00d01c9007007055003159140c0340200036441040c10b1900ca000344a002c6402c01c125644546010b94108604444a030546014151a00310038030501d44079014100d40400c4104000003142c00f1218000c0c200c03071030151980e4541616040010040d200c03030041c0800000c00c40035116164541010380d9000d5680e0307203010706015080302c4100c1e072140182c8034140720400210000081e1002c040300700f26075241008c002002e0301c1912455182c4018865400d02c3c0604041007031940103040d00510440840445010344079402c0b007000011907c568000b21078101040c04034031000010008118411200c4104440118001c1c2065000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 482627706 1250 482626456 482626499
    0x60915030a0b15040608220510050739021203030a0c03061401180b040609080c03060f010611010605090f06031b0a0501111510031104060b0313050106 66
    0x700700200e2114410000326200032680240c20756000c1070700d90b001c0e0085008190901c2103071408203101a141403007140c0703040c60700303580b014501000e854400d49030040c01d080800524140404a0401805500000f4105c0441c44070072000c01d041c2d403c010302e0544030445280041c0c41c0a40f201d00542c4036400c40e0403840034840b00442c0d4038101548074108075072086050b04109850300354144010151000c0046440e803091a1443c1a00507602d0154402d00d4580d0201003000000076000403000c1e00078120074221028039040d40e07205445d0700d05050f202c200c02c842030b0001004120051058502402c4440b0071340b41365000004400c1d4440c00411801201a2100c07510b44e24008100207507854104011800718000303800043e0414141004a01d9294260003500d05101c591458401e0301d242c10031800031144082604a8410704191001020b450041c1c0815604040c20525045050034180607203402c45100c40b28241c51541c98160441128400d068111490b5480310400200755103841000818042c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 482628956 1250 482627706 482627749
    0x20d0e0a050d240203100b1e040f0f1208030c0c030c0109061a0a06140f122a0307050301060c0204021c15120f2306010602210702130b0609 61
    0x5200c1415422440c80c210f0740301c4603004000300f101e4029078100b494200c8115410b00354450342c4665078102c2a9011005582c1902c0300441c000440780c13401250101205d28140302c0c0c070902502d83c0c0d40c070304d41d05501c003202034601102000840c050580200c02030a1351031150080da82859800e819035030035152000c00c242c40da55103c5c45030307042c401403c014460011004440308550f192170001c0103000302032501100c040030440801d840703205840580448011040c1069070341c5480c5000d1100c80342003402140302d0f121701c040c10302141166074902c1c022039000304a00c0d21164150384c80c00320101c2e41610300e240c040b43c000e0b40920040361620143c04805451605c2000c0200f040c0095041510b0341c40100d51141c036005035202120404540948108030b01c05800025030107884161484c071840361a14003000c42d0345445200f0000034200d50104400f038458480616a0780516a500148801d60140d01d601039403180601118810303042040d484107514070000340c0342078185400040091807010048005000509 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 482630206 1250 482628956 482628983
    0x206070605090709061d07120b0d1202010b06071a0c0408010507080a0e010b060714010e03070501021306080402100f020c0d06060905010e01180e1f0b0901050a06020d0e0a050d 77
    0x2c44c540a040054400b40145601040c1c03016403081c10910090100d00c00d000c02110740d02150001500005025203024100c9948111305184c241d03c0d015080b41120010f504e042084c01e51481c0c0401101e0a164002401c1584481c0c2c075030044865080280040404810402000903561001e015252040d07016448902c0c403071500502c1c0000b031741c040003142d02e0140d25000b8030402540d94101070b1402c481d04440348012800c4038240a034018058200c800c00b082c440030406104008054000b0000101c4800d800b5405503a200c0017943d01083c1510000c0d402400d02030048107243c07182e441c02e06070401c039104991801e680540815032002c2d60344d1060b6009a00c1c0c00003440421740c1ba00941d0300402001e80e00000340d40c54480003e1843c03180300e1200d028507844104500201100700213813000c200f45c56400800404904000d80c00416400c0079090250700620000115031a208507000200c990315000781242d102600d2007280e0031008a04403940c0900c00100100c1d01780c9495034084202ea200365060070410b03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 482631456 1250 482630206 482630219
    0x7020a050c12150402040b090c180405012d030c2c09030f0a050708120a050a0b0609130e0f011e090302100c020a06050408040603060b07020607020d02060706050907 72
    0x354000304072a0258120220303030076a450700090100c8001030190b0b40c81e509526a44001000350085184950780031580d40240003103c0100d0b4000c201e89200c1070808042581003400b400140c4000348503610155a0802045196803407400d88a5a961204104102519240d40d106c00b00c01286422640040e2640c84084400360600012801740d000480600502450082c12482ea248209051800c03464008a04a8203550150080d103522550019069848020011184540700c2c003c65900e1813503170400d804504c01aa007485044505640030b800300d4038100141092043d07080300100c18684840c0d941149031420b090a002c554000812032001154607902010040c00b00f4001c04200c0c40e10514105c1c4500c00a81c001842a1025010b50b40108a1040484080c0d003804248040a41250b0812042000708a0403070020416500d9a4034100301003078403840701001e14010601d0007904107204010320409403811109a43c089171004245c0c6203000c18a560710400e0719002d881201040d80904030a0102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 482632706 1250 482631456 482631463
    0x200d0f0c050307030c050c060c0f0c06160f0c030806040b0d0f050c0306160905010f170a090b070e0a030609081b071a0306010f1218030203031f1203050307021507020a05 74
    0x17040d00c500d0321500705094541243e40310300300581546071030800001d0305004d6401c031300240c4180305c2c5008181d49451608070040d80404444403264400030302c00041d800a468001c4100c0302003e50503603100345040c0e98042c148002010340c511070550000d80d03407414000041c8802d41d50b584c0c1c2881040a4281484810f00741840c0000281c0002c942481003444000111f902114200440358240f90040110907030301001d68a4500d18110304040c08884070810649205130780140380c0f0188201d51070200d07903036524800c90340c0c402440e4100358001c5201000304046255034200d001580c1c0299806440c01c3c088403581e4403884001c40f240642c40c1c201d41e0702005071507034034106040104404200d01e841c62801d6000200381d8020384c42c1c0c410912038542c0c500444840c00703601c11003503a0201c01d4400300c00c0e005d03410041e5481c0c1003220100306514540c070702d005c003400f40d02c1c081d40124ad80d014a14441c062899030280c42c2c50704020031300c100314410b04013001e034012a6000014011110703074002c0c0000404a0405a08 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 482633956 1250 482632706 482632721
    0x30f0b04060305120904140103140f0601060c1b080304030b0f010801051303030504030908120d0b04090f030503090c2d030606010e0f1302030103080418200d0f0c05030703 75
    0x1290345010703000c0002c21400700d003107850380d209440341650b98030362131000400602000b0b00c1c400341c4154280010040103402c25406140f07015017402c54908503100c01c4500d9445009000381c1c00002c00040d0300800107946541034198241845d01440803164a480300d091031a0403030b034000c1e220106d4203000c3c461400c0c1406406c5000d01828002032000c0c0c5480b0428016a4001c0030008040650b5000080c003814402c06030003028025000607519402c0c4107030010b01044c1c10a40b4070a01040c80c0c000003034140d1405114269000740d022140c01d9040240d0344080e509500300404410b01401114481400d0750b90340c41083c3c001c010790000300303d841740d480c45c212100d22080b0300384e4030301a60100301480401e07a001300411518a408541258040c207030480030405614042020f2882140088004010424050054019640d03c0a03030022401031451903682070f221200f40c104801c206490b40107800c0d0301e4100040c200ca203c0303524085054814200048111402d04c42181c0c0000c2e004000d0201071a854000c020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 482635206 1250 482633956 482633959
    0x305010609060e153009190b010e041416210c0905090a0203030c151e0c030703060308120f01120203100e0a0c2301051206100e040c030f0b 61
    0x1811903190f4082501024011510113810320301090020b9100c0700280d5500520b2035041202c0c014140c000081000d41100341c0f0880b501740105a0701c441c050796464071034802917400c00f136020744076442c01041d8009007202034010345041c1046030201c1040a810000c0132840621a0480c528092904c0f1100c1c3d8010122040c07000c54060282d0000c1c04503080e080703440c0a441e8603c100142c55212245103d01c0c040e142d8034002e4040c04081010a492407000c11044038106a026070201203940302450500c100b001a55418a02c4052001240502e141c20003d1580034190b0705000418544940703031a0340503041082d1741803401c0f41300c90802110400c0d1500381c5004040d0104441d02030702c0c40c0da0019483e41d211200900b80c0030341c1e8100c01600480100306400072103410904100031070b5250801c40e29004114103e0341241a24031020660f65441b800884203844100945440b89403503881c01c2108241e01185090100140c070600f88805948a200b00140341d40c05440001e2440c454490142c2918140d40071203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 482636456 1250 482635206 482635217
    0xb0a080f10140601030b03010e0a0b0a0b0a0303050f03130b010e1501090b1b01060308030c0a0e10120c14180111120703050a0504080304090509100e1c020f0607030501060906 76
    0x4440c2d40920041042d0088400d083c045400250030340070074018401050382e50000d10400048038248400b031b4036580d024405c44c1e5801d000e00d0901c5c3d4240000b0340d269201c000c002039000c014200c00000f060010719080b0740c6000800b00340b8520354980c0c40b0010020b030410351189074506c040c01550711106400f81903044080c00c10180345440c0c80e5000c50309014400d504040b40481a541d981c80c02d1003075210001940d440881c2580720f00742052402d82d260020f003580e001140f980f84c0402c40034a050109450b02c50403940e107100e40314440e03000180103492010410014400442e600042640c4072002400b803440ea580d41500b40c11090700001001010303041543d070020f80142880c0d000d0707084444100d882243d054140b4035034540103582c0c01c54083c407942c0c3c003004a40c040810b0100c3d401803150451801200d004048414096a29000808680c56940003035941c0d8448003e009108803107900f41161038410740143c5400304030854400d8100401110044002603841006100d01a00314611801505117132030300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 482637706 1250 482636456 482636471
    0x40605191119030504050d0c050924060903010b03120d1d0303010306051008030706050a11120105040c020c06030a0c140c122506060509011203080414010b0a080f10 72
    0x1001c0d00d44a002c1c0c010520b0107428540001454020021100200703c007070484030758400942864858001c41e400343c94800c3c0d00c0b0704080b80b8440308200141405a50003100550b10a822000304901c50b4030010300180c0554036020510010786c0d062240c030b01401901d175011a070760200070147c10708407000d00740c02985c401c007056418805c45800106482c103580d48020002955200d000f043d400d0b81d0f41c0c55002151a00c40010030f1000c0140303a0300518041c4150700e0302409880322801c6044070f1401360150403c00444000d004015900e4150803103202d0b034003580140c8103400740900108035568422103d03410b4298603561404803140c0d0142c14209422802080b460402401881040d00c03410b1041d04001c1c1d6500118801d40c03800024400001a91441078800124660700d01c2d0100103050b85201d101c0c41410140c0000400444001074091040d0303243e41e403904030fa62103039a980ca41c88608a90f800d6659600d512580b0349846054001001c7d060080040c81f041c0190f00390a0320301200001c1442090341020403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 482638956 1250 482637706 482637737
    0x1b0f1306090b15071b0e1f0902040815150d0b090607020a08041a041203120b030d0e01030518010603030801180c0c0b040f060f0b0f0f1c0c0b04060519 66
    0x10b03511001e90241e0800e51100441e205d14440c4030f580c4c2c0003001d880c1038100c207110b00a99400c040d0101c3c00c000316002e055a65481010404901503131244210a8101c1e800c2004140c1605d403909512210002448010380143c0020030360b400880c080440e1080404024080122009c20240340e114000d0310051112045950750801c06024038441c10000038501501c5402c0c1c000d40c070043d076000c4c3c25113140341d00251a17141002001c10b10300d104550040f602d086608192810082038401c200403c0340c4808483c0c00398400114001c0100500b282c42070450060580da00c0442806800d000310301039514410300b54188590070400d9103045650045440c42c04412a001a400c142c86009180d00700c0030302250340d0f480307080c6034007200c0c54560000c000501d029038000d85491030360301850b8040010344c1d144011a00700f000303000d40e060707521020580c040341c81c04407a01090000b1402d005400d1090120801c550b039200042c504641090700103201280c400b040d60f003e00d440c8110001001a001c0c41d103510307200441c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 482640206 1250 482638956 482638999
    0x2010e1207140615100c02090c0a0e0307050627190815040c0614070f0b16030e03040902070515070509010e060909150307032306010e091b0f1306090b 66
    0x11001401280c29207045c5c56891b0007900f141c0000c1d41c01800810071440d010444002c00c0e40241c85c03200125070182e01104160038001400340548801820b12840c1c8030550805401c9440001c00a164101c2d4010100c0d900b03444180400407180a03411300c00c030b182418503100703038108409820741c0611a500303d4100004076520381410000c4550b13a04146c3c0c980c020300c0c1c1581e0070340c0c840c000001e000030701c04143c084100300c420003505101c1c0e218100d0f101d402e184408011026218041e501149550023884148400c40322940140320035445001240d11102d18100c42208605084074420085100407480e502c40b960841c400340790400049a80503e01214000060300344400500050501807840d440400a0784041103118003854000780780b030303410140c00043c11030a14a61180403030140581000014070515107401c49009988590240c65009800c20130301c0c3c00601e021040613440408403c16004076240e10700480c0b10082800408508942801d140700151042001c070180280c40c2460000a46502d42 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 482641456 1250 482640206 482640241
    0xa05070c0512070c1d04120203090d230d030f050a0b1e0103291206070c1205040b0301080a050f03030705090411040803030f0702010516170702010e12071406 69
    0x2c80a5070703100e06075801e0524140d1305a40202c1460310400c030440341100c011520303842c03046124214a50161124840881e101d0040e030710b6058100c55000003200005580902c03041c42120083c86028500068016070391a168441c4565000300e0790356480701d00c00c01e020340503503507201d80300c001c00b8000700d0135500c0440d04540d0f00c0080b10300000c804100c03000c001c0e0320030742015803155040c030400106107000000c514900007003400414071070944900c2064250001042d580d01c11003081d01c0d10810704840303865204401045041c2081001010000410804104800780d8083c001500041c5110013140c6070003440c001080c0030449207507106108000001e0750100499503100020760300450b4020b5201d40b01482801142c118055601011040040039400540014800d100d240d00a1005442e01c007856080010402801c0c4002000c034100581e4402d480141150050740380e01c000100368100040341030401f00001c0d0140503503403000600f4428040080c100304910310825000c0e000b18100218002c6007000d15 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 482642706 1250 482641456 482641483
    0xa0303080702010603061e051b040303050d11120f0915070513050604030302030a090b041208090f1005030601261317130f0b030415020c0f12030a05070c05 68
    0x1800003035109071003901300d2002164400414000d07040c842c8500000b4400e4050390504480c42c00c3d00040e122500046210f402030043d181c0c3e94130f40b60854500b2a0660b10a40c2c90003540c544501070482d803c1850b03c0100030380e24200d484000343c0d08021408070703616400a03210f0740182d445407024a0803d100782e84c8980e0800e2440c00c0450b40c900c84002c1c42100c0c6403941d030045a0000c008a40041415004001030a900060b55a60585580c542c40c0740d00f9540501e010b000d07400d03400c1103c5100011a41e200900244c68002c0083e1030000300c6030001501c20106c100b12070700080021040c40341c82e5070003550020140c2d00245410b141056001c03818514400014441007880220040c440305101c2d5448450076800d0040c000155101e800605407031110040d0f200720034850071400c00014110f850301c4262805070364010252200030450140c660082d400c0f80c108600c40e4050740d0a1035210280801c080d0014600c040c00c840d40b00e00d4280454021140c00401d21010f11100c045079900051000c03c0107641542c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 482643956 1250 482642706 482642717
    0x501050a020d031a030601090b01110a050705040f1d0d110a0b04080706110a0801060905090f040b06120f010906140f0c2a0a060c02011107112701140f0a0303 69
    0x4054500c0c50074102c0c481c806a014000d100000c00c0e41c083e03d0704009c154580a88038401854815915140e031220350030000b0303045030400c100901c40791409030445e0058440b8200d01141869848403c8080f0941d01488488150f000c0e009401440ba0407140b903003c40340c0304d0740c046e188581050300d4041c58004010001408003500003150010000c0982c40300342d41380c0c60010302c6038031255100c1004e00750860a00500011807820800000c580c54a01802c0d4070618580c01600090f4072551795080f1910f0003e0300c12a4000321051014000c0007003004071041c20000040081100350003030400354125444400f640d0a042d00100401841c050b12100d001e13002903038491555500c80c04c501e42130000c020010b5070440151180640e15441c50b41c0002d200381e603e40103c03000c000000320284162701b2140b800010110201040c0800008141c000200c0800d4440107082e04907295804105501c02c80c04110000c0300702801200140b0085400b02c0d40c045c1b03440c1d8141d40a20242c2c5d52407001079610b88161000504110303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 482645206 1250 482643956 482643971
    0x30f0c0a0c1508060a03080a180509090a0c0509040809090a0603170d0c02150105040e030d15170f15060d0c0314010c05030c04050409030c080301090606090501050a020d03 75
    0x80006524041d000840001c0c41e40e141c14100c81480e82d41c520030b0000910050200b8040d150a40941c002c90350300141c410718119504500740c803088014806440317070007000c0c1e13400103a1351a02ca0303200780325240e4600541b80c10941868999081e2015401c103a00840c45134082100107400042203a69190003240d2181080e0f8610304024043c001310b030002484010f102460340790321144040600408040200c0610500d41c00c0103049035260b00000030728828048000041140b810980c0c025a0940c001c102502e180050454041d004e0314070500140d00000c900312010010b11600b00300b660f211203480d201030100154500c5482ea510b401203d640d943c07880c41c400108000d40d544011901d090b030780c022018400e156a03410164500800707a040c828103035003001c0314003c1c4c60384242c04603407007440038078103203810181000306000c02405d0303c01c411003d00c03400c040048086849038026500a01c03040002050305401d10100408107140c0385e1119040c4042401154003980d001f04580000030410300c0c0005200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 482646456 1250 482645206 482645227
    0x5030303012d030501021b06071403101d0402280306020d09060e0c0405100503030403120215151507080702040b06040504020a030b1903050607080a0209041407030b010e03030f 77
    0x1960b0060036030354410345250000204101034004d00448410041174602d24016589420744411044500c00001651001154004003c45015603085080141c40b03034102510785040d080f081c200c1c03030825192803054034104030852078004076514015800a40341100a842d445006110780c42c81e000c001c15494000c0344440c483c3e46a5072005001c290015000c2c00110308490401380c90b1115054528005c0d400c080004a203504201142c00031904080d00541c40d05285444400001c50700d0852041103000310150091680062001580211100000c0c4803000f1196070402000340c4480900e142e912009111f52404100c4020940f2006901070b1000701b13448081c0400165148078940205d6402071001c03400e041d8040d850b92125000d980103880c1c141400c4400300c102500e80c1190304c0000d04039800400050383d20340c841c1c025941c000c2c11912001d4146510080010180c4555500743c900c00881c04007080901c580c54010301d4030406007030800c00412400301d000300303440744500c00800801900008409081d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 482647706 1250 482646456 482646509
    0xc050d02011b0e030a080d0504020103060e060f01110120130608100b16050d0c0203010f06050d03180b040306050405150709050d050c090a1b020303150f0d060509060117070503030301 80
    0x1c07a48101d807581e0741c4018440c031070024230055500381d00113880c00f4000b040c580d0040300d01c1401000010031390920007900b5001140c03445c8082c40e2030b440035502d5090840700d05146034a0031141c07502c160342103615031040e141444514021f690100f010041600300b40101d201c50031f02210213941805211326503d490b0074080d10301c1000c0b00f400081c1a48121082003240035481001d00080c64030072030007404403404444031401500d6580c080c080c3d00890340842500007078000d26031020348001c03520008503060b507240341064060300940d2040d00d4294541082004000c418000300300301074110041e100a50a106500030b203490380318000d60f8066007a003030002080c01020044005403650003840c682c0f040c5810542240581902c0042440860305280135001e15400401a04d2089628405141c1003046e14010001c101da1040a80b6402144c415000c1c0040b41d51802100d00c00c4000380c00505055143c205a4903945980351494403a940156109105664000c800c6038111251000720440e4541c490000102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 482648956 1250 482647706 482647723
    0x61e100c03170f010f230d020a030602030112060c0c0b16020c060301090c02010606051c0b060d09060c111207081803031303120e21010b0a060c050d02011b0e03 70
    0x100640703081040031500003550505a910400c076185009581d0740c80102e043c1c0100c030311b0001000d691550000b042c14481400c0080301c1c001401510380340d03520b40b143c60480c1d1080c2c200300c6028004550340c03030a108a90103959001445448d01c003203803441549821251180207010005507000c1040c1d02c01c60140700b04104410702d98018501d640d696560702000c001032048000c00005035090940004400b4010415280380b00742d008008201c207910041340c0e900402002c1c0310268048418081c0711664405403080c0c0090038860748000030740b41c101d20400390401c541c4c00d021a82c560300020101d4081c070020300075580080c0e0301c001c085841e40d5440840720303814400225507603010712020503100c25020418444004588c0140e4102580b511044402c5404001c0c0145858000b007082100300540000f8820806166885800004d00030b1445c1002880b414039550210000450740c40c1400b0920000b401030b856192418002006480c0c242c6801e42d00d074607410340258043c804010f05000d80d944051045d101c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 482650206 1250 482648956 482648987
    0xc040b04150f080d0e06030117070b070f1a07020c040e1e250f0510020c060415030f0b0a06081003020a0b0c01150f090c0504080109050105061e100c03 66
    0x42596032901c100292058140c803c10040c2c0c81350b24020140030703010741c0f0b070007418903400b4104500d03680c01d00000c4031442c080c10421001c41d01c00d040c000101409500c2c0503110491280e81c0e40b007001c08690501d00243e000300d40c040c845165065051004650300000c0c041a01c21099602080841c142c07030480b0306081104906c101070802408441a0840021a49014a190240c1c81101c0b5404522407141d07400b116006001d1809031001050140c2d1a0104900d032030240d55104461060310754201054442d003003070f030043c1002194401015501038040c024207035076102644080200c2c04922001900d5040b0912508050041020200b0308110b82190444050b640260040d41c10f070395945094209540150500280c1c0d500c0d01e801300389a009811680b504841c0d0070800310407458141004500146070348614002030110820001900400c00e016103619107018000008141c82c029080c8000b0320300301401040302ca8201070b8841410303a9208001001c80c0064900074060502c280340650302441722000a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 482651456 1250 482650206 482650241
    0xa0e0102010e10091e1a0f09152a0a0912022404150503010306050c0a02060705030a02070501090f111c1707020301022802210703020a120302180609030c040b04 70
    0x8080c480d803140c0c507007070502e154600a1540c4e40c0d22540010040410340301c070111508276452816450242110b513981013007000e0080e000540480011002c140c01042d1032411041c0c02081c01140030390420301200003400e0b04c914007902c604060380000c0214030f50b5004506840c850a40c0d44035056451410761300a400328400a00381c01c000d03800301402c290024801110380d1810710000034856040c010a450940885400401040d200c00100b40e8903900024003420026234244100d101203807007406080503050040013985078400e5141040c0000c2c0e800b002c84180070700000d50900304450001040d50143d1500405141034100400e01e40c0c208a21444502a40c50b40c000b04a1600141440b26000003414050030042810321410000740c3c0c461141c91030380d2080310624111420444500740051075040e00c2441660701100032942c0f92619040d01019030700000c5e50100704030001040d00c09682d01365120840d03c080c10304c85c8410010fa683c0003110601402980c035075800780307a40e8603950408001070748240c005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 482652706 1250 482651456 482651513
    0x5060d0e07090911011d19030501110403051c05040e0a05070e0328080c03030f07020601050612070c0f0203060903090306060d020f0114120c0a0e0102010e1009 70
    0x12400503003a110848400d900650724001000c441610038101c07007a038002c1210501000f11001034a40954881882120446108450002d40e42e8060200c00244100e00c16800480c00c5062140c02c440301c601c856450311408000074408500c0004440030007520000240c44c005070461004c4550b4084c07640001c09080003203062085001a0b070700014840c2d4681e98401d40f60310941d004040d41d803081c11804007031540221000c2d040c00d58000c01c1c0704010074010300106103050100f1003001e207190700032120500300d2100d420900043c0b580c14040d09004000803141c00d03051140d1081c0005c5500d601a040e00d0510010781c16030001c005076903c05150540d00141a20401e00c2c025216a450340d100c8a4214424000c140001e44079280825450034210b4010701020307500f6104400554034a2000c4c010b0302402041480180c41107030084007030a100d01680350ba20b84d2101c52482c0c02030720910303c54000c2c1e4156410302e4446050800300081c110040c00055a0100d842c6406003132400d181d42c100201048543d007071900303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 482653956 1250 482652706 482652727
    0x100f0204080c0405010b040b0705071a03040308010602031e091c06020c0706090e040f050f01020a03091e0b0a05100315060609080d09060507020117130b0c1e0706060506 74
    0x140044035a5501514140102d19003000100c5809004807a1104d0042c002481410690700241c904c0d284618202c406091326111281d400342141498a845170b003000040004150780f1441d03003801000540001c1d401d11007080319020384070700212006850703400d02044514180e660441031000ca82c241d02c8840f0000c1505040c075602961008410f022a40b046120010300c180c4181780380c10454590040d01840c540780c995030001c05a4800078151410300c42c011030064803040070303c000d000103001c6d91070008400405140480402c50382c0b4401054410000240350007160041c1d4030300c1d40c0502500d00c0010701d540e0381c114980126200317400250204860242c400303500c0c0c240382d01075800c0e01c1e42902c03201a00c60703681c3c0314540d5a20400e0031220008120390300401c101402007014052503481410004032052000c0d44d0700c840d0300800c03161007401e6100c000307040050100703855a050304440d0304241d6034948a550032980011070000c1400e40e403026000a088014003000d91301100140500508c2d566980c156481b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 482655206 1250 482653956 482653961
    0x61b033f111c055214070804031506080105181507022401090501090915050a060504021c0b01112d1e07080a0209060f0a081015050306010807030f05100f 67
    0x61000f100c1c3e404c070160181034080d81c0c4000003140b0004d03a80c104600010307140c18000c5401c0704030300300c07a005004d101c04400a00500741100c90135500e800c000803050301d81095542514409442003000081c84480800d003d034000c40e61116045030407048400f55224004200d1804080c14a02c2885810805151310100c0d034182800e412520003240502199884034102e101301c0e14100001040c0860b40400003d01c05056008164000707095400065115521000304040e680500030f90150344030b002440e101d980c83c986c858250003001c05c2c6001000702400b2004a40d64003400c00740d4000032581aa04400c000d00021408881500c0e0142600c9903950a40c0c80142820281d21404280303020700c940104e049280002c1c0303208501d170020640b400c41e454140920880d1604510801e402402d281c002141d010300402c1031010030109030500040c04030411010446001550700300078481e8120500400c012000082c184043d25040b040c103158a03060b900c0c000307260400d081180004a800d04402c03280c56081039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 482656456 1250 482655206 482655301
    0x30d09020111030c1507181503150f12140106062604081606020d0e030901120905072606100303030501061b033f111c05 53
    0xb80c0b40e01e580c035101100d102e5143c0c05141840d1100c0e901041e1001d80c00c86039104070036002420350510f03291700398001e18140d01c091a16044610104040c010000d2001d9140c0f28261450f21a120007400e000e09240c4a5841d00840c2c0c410101c241d05400042d0050100c00b141200c0d11540c0c0304000c1100d16030314036014008400c031401c18000c4c417010301042240c250003602038901c0f4a91048459180508030580314035054103250302510002c0d82403100b990040c0303442c8101045e80c0d07841f5008540321030f04c95000401d0310040881d11601c10f07052070400c178001040029a0f200f84c6240c5030040034180800d05030782901d60741c2c158007101244141e50034000d1080b03180080c1d50940b4042c1c4e0b414441a0b0300e81c1c50940c0c40f40100a540503401d4400340701000820b1182d02a10341507071a0907010303860a4100c0b41402d0035030246030008190b500e041c1081d00c0b11a81240300e499805c4041c401640d0074803540c7c90480361906031b108600000961074400003091003546444500140809203d241d601580140d64000c0c0300000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 482657706 1250 482656456 482656459
    0x30b060d090b06100c03020613030519080a0c0e09041104022104020102010b040932030c0303010519050a03030507020609090103050a06050106030b03100f060503010204060f0210060303051812030d0902 88
    0xa84d2606100e481c407481c40d8241454050f0028520b503200c035076418980b00c2490400794200141401102001c0c460300c1141e00f501100e65440322150f040040d80382c03084071600002082400740440400c1c0c1d00391103030210540d009800800c41c0800105a50108000e0300c11148105082e454a02c9803140028403004810f006900070383c020058001ca05090001f11044044090728100c860b00d4886c5d11041d4180c000d0b6800600200403104454a060604e40307190481b080c0c80500f03400c080018030403414201c004240107800f4029407640c052814000c244800f800e0b000180800070000780c150207548404044540f0a8000f81444040e580e40f405c0a503242c980c5080111800f908000001818034880e0146c1d000d60f03140100607006080c88022004010021242d083c201240c82c0e45002410381d40a00c064070041c8440d8854041405c1c031f2000c000d081000581e980c01030340f0f1610205001080c2c0c80b80c25100f040c1c400c0d113a8590110910701c00110500708514905903e803000207000b0383c00003070680103c400c0070710 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 482658956 1250 482657706 482657719
    0x31b040f0e0a060f050c1c110a030915020f0a0f030e0d031413081b150412020715090302130209030d09051504080a06091a040303062103090501030b060d090b06 70
    0x4444020134151001034403d01c50101044c0300b001c0b09101c1c44180010303c070403010800120407214048248440e0003003042040031907510802c00f014842105c050704510060000110326190b80780724000c8190013954005810000d040003d0b04c00346002e64480350000807840100c4480403a003201c000c000c2c021119140c04049030120114056206603140645925031090207281060862050810718442220344081144a000240b43d2000300150f56140103030300420020a6113030060402a2406045500c0301865080002c81c00c111a03501c8586482940e41c102c4000524a25902e20100640039941d00d0680c076016058050503000d80000c807031411180c0c10342e4405141c0d103803004500481c0c01a4424103003140c100e80300c440c0000b80c1661000c040d5501c2a21080d00c0c01d042001034078420881210124082540c807841845081d90301c00d0300303a43c60a01c85110483c06545036070001c101a0f42440303001c0c18503803106081901580c402c81950051481180e0400200c0c3e810300b000e1682070400c0d03030300d20700809 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 482660206 1250 482658956 482658971
    0xc09010f0203192f01091a1509062d04060902040305300307050901030b120d08041425080a080403150f02030708070e0f031b040f0e0a06 60
    0x1070010050b92003a4099040302124074040361025600305010103402980b0380886410300342200c003007801c80c00150841c9000000c01c00380c0b41c81c14809002c2c0548003a4071280d04a0f01b0011804180d03040c0c8401100296080105511420080341052808140407c15010501114040400810009040b94900f140c007804010796443c141d00491290303000140c120f42000d0040c520340300076020400034078038280802c3d03001ca0041118500311a0410f40d1404c0c005040015040010b690601074807200b048121040170401540100b07141d600d23203480c0716843c2403201850000b014415200c1001e203943c00f071042a0790003942c000d8032922541042580e400c1184000c3c0c4404680014006081300380c071580061030a241c41d055896003070302191405415000d0320344030083c1605016840c00a14011069601c0d060301c60300740800f000e00a0590124014000c403213804443c82165130003d90001d0481807144c18204a440f89000301e000342c1101c01c042d1180c070b410641150505200000c003848814051341c0204202c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 482661456 1250 482660206 482660237
    0xc070501021c1a101205060328030306050301142403060106230a020a0215220305063304060b041502071403030a050306061b03040810111206010c06050c0901 69
    0x13102ea40c4100e40000b10b280c804401400056841560406030003021500e01c2c00c0b00c00c0e044e0481528041c021624440c107040307a2410541c00d8000e2801411086009200c1444000006207008400600f07085110b040007811111100114102000c50400641038030704130760312000080e02c6010102006014400c8426110301d00b401c80303800792100d0b44125400f810846001d80c00b0040c0042d46004c0d1038400150030400c1406641002c00c1502607140110440d1180e0f07031642c00c2c81810144020440e901c425000201b60780600e201e80c0b000104151760a0301400f99116103000714004041c990490070000e14005008500207000820400d45a101c0d9070896003150b48400081c00c401248030400ba4141d4420b000421074580a240a507a2203030001d40081d04004240c1044014144165550025900009400d101e002001e00030700e54408908127040c00034190b000b2400219200c2c4254410310300100c00b000c2999030b0303c10186407400d2900400c0a0003281024940c0e500d82d81e010114840c08a0782c150030301000f4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 482662706 1250 482661456 482661469
    0xc0b0123061920010f0902100e03060a0e0304080601080f071706010b31172e1b0f0e010806101202130305210903060c070501021c1a 58
    0x40030942d406914a4400500d00380c2d4490401e404031100049407042010002809214250034421100c0d0702040b50070341070051010203c0307440e00c00c0007080328100da110b104c2e440009081da0400c510305070004081018400040c00c60245811086041c0980d070000145600001030700030b15491f0100a641406995142005040e1b1410316040c055400c0385c00100030180030309001d02003002d4003682810760182d00d1a0344030102000c201038501aa5400c5500740142c03840d5003050b5030289500c000500c00000900303d01052b408410044030214010050451400726a075040f10f1005242c400784c1c0710207c3d030151806044006240b041100052910301071551962144400728081d540c05080340e44100e10388034046840c00c0c540e01c0b480031751036000c014246400208a8000d001180100c000d41440c48140c0d1030303407508030300c401040341000b00184600159550081160380c0c000c0306000042d591040e0910301035019000744028108c0e000107100d41c078144002d00380c00c070310010040c8080c0014645400703c00c1000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 482663956 1250 482662706 482662717
    0x301140d0c0308030604020403170a090e070c110316180b0306040f120c0b10060201061205071512050f01053d020a1709013902010c0b012306 62
    0x12500000781c003040403032801030056811071409040503140c941c0304e0701e80100428001c407250084c01c10002d2691240b070b5001c0d0b01c100241092000c8c00105060008000b0aa10300d04d031000303840781060480804c40c0e56401c01003034480002c9805054501c1e9501c0d20039040d0078207018500350015003410b40f079402914002c2010385c0b0480c1d20075941304141005468400d09200f41707100380414402c40002103004105042c05191040007003d2600d81d650b82018402030a48000e50705c640071442c0c101100c08006600841d104d02a1070182600d20940504881c046645a81006445115500c1e000510400c4581210360710305030745040e540c40d581200c0d44a0074013800313034280340b021720360040d003800d00305400d0050303d040e4a4098482c811039144420342e48072126480c0001840301c441a8001a0a02540d40c0001041d120f0031010310f055210700540c00f4a4140c480040454020000c0c1c4e9803614400b168000d14480001581100f40c1d1821136848030001c01c1d040d200000100600420903c7d2208145442d004498 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 482665206 1250 482663956 482663963
    0x2030103030f0915031e0f15081b0d08041703070c1e1a090910060f0207230409140a0209010b0705072c090604020108010f150f180801020301140d 64
    0x490b138240c0702c04100c0041c444208103030264031202c4003040da080c00900800141d0201030000044141c03030f601038040707241025030007000d564019410a004e00c1d40404ca05688600064030703075090400f01880c00e140306211f580c01140086094203e40c40003250001b018284a902c80c035072101c0040d4644031100c0b1001c02d20500210f400003001002e10485019002c403200f840b0351800c07840e041c1003c100c0046d030b084404540200c050300070071004020041e8800c042080600c00c038009407044504028031451140780c0600110314081c000040d20300244c030790b03500c076030101500b08502c0d40c48048194a2203864503509201644914175104c00480e9021201080300c1d07030594060300401040e4508512411414074a81180d40c00c0000f030340f0060401c0c3d5050410510a115a101030b2a403443d10744009001c10300180c024002e4404245810f1056101100007094403a40b603042042610094243c202d416124070b060709400228001c200045000054018505075034490081801150310b1500b8402c1c542000032018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 482666456 1250 482665206 482665229
    0x100c030b092a0f0c0d0806030d03091e060504030e0a0f0608090a1b0602100b060403141c020c120d0804021c0503040b0a020d080402011d0a0e0a02030103030f09 70
    0x2c0c0301c00d91448080c0b9a07900070800e81026881540c00124120b42018080c190341074000519044802018402c3e04d0180c4c0d00c505110304a41041000700b599641707590301410502d40d0f1242c01006005003225140801a201040c90f204002c0518100019003000d03602200807695510040503103140588200041d541c4041d002d10000d450030008071403480e4041c0080285004e024022804100d009814225504080c0c03103a451311031801c0f900030302c4e1002050030040701e08c0c80c210021109646940444003101c1e00242c25000c20030000c428542409110142c0c07003071040c8504c0c80c0041998001c03c011070030003401c031000c040d00f445803160f0a4540c1000300b892000900743c54001001850095025101c4d00715500f13040916410740c2e55564559806a0001c652114000c24582e0f840d0b03904224200d45103096183c40f40c035a040170f500280c5056003180301c0041d003000b40040f01c5081d0b110030b03194900030007110350000160b040402000e8025442800194002860382a40c0810103018203582012500c601100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 482667706 1250 482666456 482666461
    0x21b01060509060d150c17010b0a050306090403021e01050610230c0a05070902250b040206030a0b06042c040308070f0e030d02061f0614090105090a08100c030b09 71
    0x1001307000f6070030b488110341050700c15000c0c141c03484140c032543c180e0700c405032541c8900c0b0540d10007002d42004168001c2d12010020008a41600d5014080c0d030342090301601d180469458034507049c0c0c00c0900311301042c0e00101c55038000400e0030005402090190801351810b18100d24560801c030340c5810072a0f5441000f4010f40c40024040705020001c0540c0c4d00e00d403003555100d860680d239650603da220790003410115004108102c1001380c050401802341b040020501000320503584812002c14000c0001c1e10035000440014142600c0d81c0180f205444c0041045a86d2900e070f24074501010081070b41c1514419801001c0304070344000701c40c001c0c0216016200d420f19641e038500b0454000000a0800c2d007080701110007241c05071010041e038800b0403034680103403601d46040100076100d55101c101017000799021103001c028140d003100b0502c01204482c2c1c0000e0707444000b00c006030349600c40c0c00b1005801031002407000505134804102e00140c901d800740140300342c900004040b0255142411540e0b44528007401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 482668956 1250 482667706 482667709
    0xa15050d080d0e06010303080702010501051c03031a041104080622060506010c201216051903020306010303200304050f0112150f05030f0a050606011101110706021b0106050906 77
    0x6004042c114a0300450001041194942000400c0e4011404501000305110605030203002d65409040c017903942820800c16186240343d0542441405400c3c075035a056008010b00c0c03141602078035614007504c24820f14146103c00c800c250b001e80324441c0c1c03d0082802242c000700700c0310361040f0414080541140550200d4a843c001000040c014605002110b600300740041c00c6900100c403260810b01843c0c02c0c00d00c4a00a014008070000401820303038005074a00302505200035060025602c056801c20405584e4031020301d071922081d000079525100301c4000200b0541c3c04907407800320310b080321210800120b845585550302c4c0658014030b82d010301c2e000381c000d03040d510454511440000206000c28051300410000c046002c098214a5801800140901460604101c860221180d03280108041d501c10340314162924000343c182c0f130404c00034a802501d2003078250455180d001083c859155140000d142181c002e41c000323064100000030a843c010158503040c85a0800c4071000341030640e03642e40c0c0a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 482670206 1250 482668956 482668973
    0x60604032301020d0f0c0e03070b04060e011202161515060e27070215040b010e073609020c06010b0c0a05060103110a150c06110d0906050a15050d 64
    0x6407124a5982485111401d0400340035040301042c07900340c00501000f40f29001031080b2190f0a4180c0039a108040401408500608580071500f941c503040760aa541600100c5030a4140480040c8450002c54050a042d03000003004d6040c9105841200e140c82a000e0914103a0704001108403001203000c002301301060290000c201c0d803610040c1540c0c11100d41100100c041071500c010303004059120002c01091580401908406281814070200e80e45030582e5015500e100500a8104c01c01006005c9280c540c0220403045c4048164200c2288907160710b40c21410050301540c41c2040304101120000c0c82c46910b10843c5c0c10070740d019016000680c01d14840e1811a80071203003880003442040307400c0011800910080d0302a502c0394400688050312801005144c10b4a078009504000ca020003410701140c004405200c01588828086130b103002451888502d030184403265000c0b607060825403000c04c00c1f6603000310b00c81c81640c80308001c40c041411080030000403500070a0b41140384a000e0502040062 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 482671456 1250 482670206 482670263
    0x170c01080a140a0506030606011701051e030d02031213030e0d020f0a080c090a0c090314120a110d1107030213020403050706020604060b190603021c05010b070b06060403 74
    0x6002060301c0000190000081c1d0b8221102ea003d55a50020301c01c06140901c1041d0b00130400f46085540300540c410401500881845a10320411088100c1c5810100b070315184404004000c05842c138148020070069165030201c05010480191030000444030358010100c10040d0303816030359a2100e9140c480a00c2003500d079501c0141d03408400004203074078643d140c02d828030180841c00d000e000981d030b000c0203000200c174000d41000301c501d040c61000080d40303a1108030307081102d420040e68101400380c411814100f2460b815000e030490b41c0010801c0c1d02581080b412020132940e0740c1100c3c901003400d135088030707181c403684881c010382e42000c80100b0141c0703040a0301e50007045a00300018035156803540d0344c600d0008180d1140d000b58200c1001c00040c0500e92040481210040d982d00789100803070340d00940c1e4811140101002d04d9404140408150039203050031130031910b9072004100075616200240c2c0c00340c0000c04c00302d4000e12410002105420100103640440b41d009080104011101400e1071080c1180d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 482672706 1250 482671456 482671471
    0x206040303140c0d05070c0510090201082a031b07060b090612071401020316030e01090801020703050703080901203007050c0f0d0509040b062b200d06170c0108 70
    0x5001007d00820360600c004061440e0307000300001c00175064030000d41041300c020006088040e11143c00c1d80c8604001c0007818600e80b011031142c1d665a51490909000c040801505190311400700e00542040301030303804107640701d00880f01c6c000340d591007108100c100c0f100d0618044481d04512803c01c600c0243c0303140b0001c164414010f40b41400b48010040308480700441050700040c010584070200b550700305003141c01030680540254640710094030080d19030300c80c2c010000c0030002c50340c00248d482c40f800c3d4880500414940150329000d40b06001c112410b410464418088800c0382c030803880d0a40030b0030300413030b00c20403e403000180790750b98041700b42c13207a4001c80ca21203d140118815082024014031420301010840d440b6680c85064001c140700490b06030001c01e80c002c0d00204180710507002001c803180e41d01d21720040b500b40c01c0c03450f0180d0040680028402c0c07010412210b201b101c11640c0034400350594030b05990040111595681118210240146442c1001e811010f0049403c1d4400e000d0140d020f5003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 482673956 1250 482672706 482672717
    0x6051e041d0609210a17180102340c0b0d110406093f05030408030d050f06090103020a0b13050a031a0a110f0d06150206040303140c0d0507 61
    0x8100e010707a4100501243d2a001e9600010b103004042d1110620409695500c000c2d42d83c10205090005880c07000a085035140805400300003038a5180d04091f100b0782c8008031002552140310301d4000001c05607100d1b0308001c003501180c8040c1520203200b1205510a5045410308180e545800b180c0c201c1076010740e040b0070401d62544080c203600001038000f00002d10031507031818100c0b0301c2c01c034013031148905110b1188485032900c4018201200d0403810f50050705100c0c20303081210320300d524040b8554400e540c41a88103020101b0340c00c41070a0550300c0a40b0407020790f19161107039a1000308228040d00c2c00d000c002d6000c901b644080c46441141c8002e0040c1080c1c00403c82d4a0607250000079046055030b9100712120040c612411a00c0c003403464990360040c0c0c7e8840d0502c541d6080545001c0c4501442c80145000178001c40c5050030503089422010060801c104918151003107070500940b112001c0320185c2c0032900305007440c25802c0045400510441a640b412030400700d0940608000d090050003220402a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 482675206 1250 482673956 482674001
    0x305040515010e04050d0f051c06030b13020117010806040b0414060c04091a0a1715070801081e031b010914010c0f080c070605130b1906051e04 63
    0x40c0035034070050280045207a1007000785000e107483c40c40e1a61103810082004200300c84818915085000c1d194116284421807919000c02c00c200b00003040d4030307440078007035025160034054206503881e040c010032070003030781d45564031b0301600701070036160400384210441640844001000b00711017444045c3c0151080c04058110304014804c24500780080e00d0122140da8005003c1144d18018820401c032011b00f1225580000c10400010380d420f040f0f842088441c44080c0c401551051003400985400303011000780f5001c9041c6080c2c02424002d01340584042c1d8881c285003215510160001c980f482101000218039040308c400c420a000a0b40c016100c0481d03403580c84c40000268004030840c1c4e5800b0041c000920407a1546000344404034698a20b801c0c0700d10070040c071201c014a102250803080c0c01030004940d43d1290034080709001a01c0b031026085070020000e00561011089150151004108040c80740340e484408000e00307500b0030b070b104240d05582a00426003078245904440c1e510000e0071a03054004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 482676456 1250 482675206 482675233
    0x702010c1a0f060f03070608060303040f140102010c05070804120c050d12090f0e180316050c2409150d0207030206010905090a0b1f030f06020a02061b07020103050405 73
    0x5084111a4165900d001030400c4002a0901080c50340200f040b02d014141102501c0440e440392086d0260a0400610000080301038030200114ac00a02d15050f040711815034403200005a00c8502480034010f5007071034080000c941c411401c1d184015000702030145032a1030500307001074682880d2070844070f824420500140d076035254824a0605030003169640350000703c0203001003020295403c180da01c0c0d54610000d02032908044511544044100e42d213034415030032041c105203540110703048281460030b07011702101088808141034400f400182c9000701004a5040e0301e041c03100407410b00001500c003d01c1501114900406c407896941040745030700e0f150080340551700c816607114007026805680910010030481c10341d03200b10782c0d211034040007809811000343c1e188542000060042160f510401100c064203058542c400b900031640000403519441003032400c403000c2d400c400585800340c01040001008024441000ca890620500322249130894035070055000b00f101902c00d49041c880c084024045 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 482677706 1250 482676456 482676473
    0x1603060b0c060a0608030a09090504060906110a1103030609060f0f1314223309060b030109051c0509120307020a06170a0c0513060f180f03080702010c 66
    0x2881c0ca0040545520b01d8440400802c1d1506a1710114059100300460303004a5800090350f000c0c0c2c0c01e003070008166070f1240e0400c0b07806807000c2d15000c1c3c40b0031714240000102001c0c80e030042260383c1141c0c0b6180c1c1c0c060780d4942c1c05516400304031185500300b44186c0000700700b4900f900080e546420020034045200e0440404100c48005802c0125280c03a511011621100c040e00300d42c0d5403080704940800c0c5861100244600310307a4800b41c00901100e140011802c24985c000702d800146965100d181d5011f040300030a25001d001c00003007d59045207000c100a00070f08043c00b64000490704440102085000d894140090800343e00315101040401d000222031030b0343e25801c840e248100100113546034200350041103600c00c1198801414842c110308851000303100752410560040e40d00e0300001d4101c1300360340c040d141d0f8885d01e00c42082501001c540030840383d030030200841c0c01c2d50640c7d03210640860b94000070341c0380c0711660003021020710341d40c002080043c002c140181005403061411060540003940e0f40320703c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 482678956 1250 482677706 482677717
    0x602150f0414150106211b080c040e090a0c06030c0c0201050c0f0304080a0302060f0403090302040f11030702012a05030114061303080306042009091528060c08031603060b 75
    0x101c8a41c0040064511100b1004011100103400c00c0b2030f45c003402c0008500c61520785285c041c824150001404270354200203540042c00764031205422460300441251303d4260b045001c560901442c400422141e01c60b01c075900052913244c03140000103006400545079a00607001c403410034810380250490800c014000342008000200060500407802d203406410502c0c0200441e018800030320420000ca0b50200700e075400c49405032400181d4403400d0200708054003604504150209000044c000d80c1503056010300401c030b0b000b842e00040f20070170304000d91132035000e90081000910244014001004124040300071200001d040300d00e4020382c0700152803104469030042c4d945217004070400506082ca40103110000841840c01d80340c0c1003800e000311240b8001d05503501d000e615900009200028005d10b4002c03011030091445c190039902d401d4811350151000c401c120f503454401000111180110701241d195907104044600715038030080882824408058600105500d60000103808032100d4020132 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 482680206 1250 482678956 482678969
    0x10b1e210715020a021320070c0e130b01060305060d0308090a0f080414010903081207140c010903030b18040f330e07140d0309030503040602070602150f04141501 71
    0x81034902d0041110300c1d4450b81b0140611030529000c46413403040c2112a04030318036a1129242c0b41c1710241001101d80c5010b42081c2c10280a0000344440c0301000e070b110520651090004800d10307070300c45004500391030040e506a90041c030000c13111000a0b00448600d03a00002020403200c980c1407030303259681c024809280aa07540354000a0510590079440140030041000b8280114040c1c995501c0348018070a503c1c184d24980c220b9008a00e4452142145088412545200648821440c454580203049400c0101c000c40d1a110707092540341080300000101c1120021500c00d0b5a0b03560b281c00401380860b180c110741002d94071040c202c181e10701ca000c007581c4000c41c49000728440848031050302203400410f0f40342c030140c0c8520f104101d503c4c0c1a640c140701c00c040c01c3c2e80c0c1811500c458a41507030683d6a6400003002400007140215031240d0000c2c00c54101c5404d42e089510156207404807001c0401c0a5a200a020308544005800b1482800b428200383c803104044881d44e51084400301e008007402e80001c0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 482681456 1250 482680206 482680213
    0x2d03030414010801060305090604060203070e0904030e0a1a0d0e0304030503030f01030209060909120a021002040315050c0f07061e0c030501080601080304080c090c041205010b1e21071502 82
    0x21030165034420703c000d000d0300e43c5007001c00030307800c00c0345165a0302c020062000303000b9500000003078803c0303219401103142c010014110504604103840c01510311078110b2034450040d03016003030010701400003010b0308140140c441c09903480c041104c42c280c170140801d44082482c0348400c000000015004200944c89121100c150105c2941107204004002c0000b600b028030809610080c0006540081400c24014804000095031481e6004040c0c1c00c0403070b00100203640740c0c4081000420f10060f280d45546507981c10004001c05c2d942c41c0d01d074003c1401801ca00d08003a40c0d050102000241440e8804e42402d0a0308072200700540b91010001d050b01c4801a020001a844400410002c00f00700441c81c09001c81d03c02542c1072500307080304640e566080c8100c2500c20b41c407240120b4a13401000c8111006041c1607070625a1701c0c4cc5a08040d03000c3d2200c5000c060049048440c2800c02c044c0d488000130b00e41c5c100405004041c10102c56080e02c00340018000e0038207024205c0005407540c0940790301c820288142d0003a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 482682706 1250 482681456 482681489
    0xa0e0609030a02190812031509070e131e1503061104050a0305010f0b0f030d0315080a030818010b09061314100905130f021909060f05040c09052d030304 67
    0xa15050685800000303c86c40001c0c000c0c0000108015034188803a141560f104030720b5078681030100d07040c10080807001c2d041104010301866082043d003004d50688000580380307050291208210382100c9081650074188031500b0b00501c0018441e030000140c2d464003c1c1101c1c01c0c036849000040c00d80d001a403007160140e40d030b042450200f00305409042d0445c90219107002d00c046c82c1c0e00100c0d480300b41d0300004c0c508040d03039940300e07080341c10000200c40041c046207400c071101c81c401c5160140ca04041600c0300c651070701e040c00328031210a005009500c0c1c0384401416009860f00c0e01800e0004c0858508940c1030f8007030f140c0188410a1901c0da0032a8490502d44030000407191410940008a038409070034030021401c1402c0b40c0003c10607072607280c0c8204e503041d0355440b80c034007082c400b0540c001d445400044400b0300740307080041c0100000e104507040e548221070400c141c1c1040c03801a52100003a214140c1c0001d415180c039081c0341d1107031455514031a1a002c410718400c07007140c002400c550041d082004072007424042c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 482683956 1250 482682706 482682719
    0xe0c0903060a0608151b0f0403051204030515060d140f0a03030f1d0c010c03050f03070e0f062b020c03040801063b0403030f1503030201050a020a0e0609030a0219 71
    0x4109480c0822550700c0c0b40c94204140c04659110441c40314801c042c6c400130b40d0703428214002c4200c400a640003420782d8402d03448504802080c1e80f0a200c01e0b1002c1c4924007070342114042e86900c0c9130059000402683e861940355031120001c015444036261580900440c42e020150144003a007125032284c2e0300010112000d60201c01103030202c81514035417402c2090284042d15000171b81e26002d0b0070908040c002980300d4501102c080c85160241030380c044020080c080d0b990b0300903020300080c2c1c3d0205c6040801440e0740003880840e0007004000c21224041042050208407412998001070410700300c098502001e04c103000c0d10310380c416404020107a6641e0b104020103180070080d2010302d1549610030324580c00646000e0b521910510002a0224028003c01c0406001e61f01c2803d01c4034000f01d090186061a01d4812481c00340ea20055000d54202400a21143c656100f04e43d40b148050301c031340d030518554005001c4150800c415040c4c051083c0c101300c0015989540d40140115109010404110306000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 482685206 1250 482683956 482683963
    0x13050924010c21020d050a050f030621010e010506101d0a08030a18051002030307032703050903060901020c2508010e0a1709010e010c0203010923150705040e0c0903060a0608 76
    0x254560100308041c0015407c07180c0c01403c8039402d101c0e0000154582d1551000901c0c8449420700b071600c1540301e81c51901070503506410403081910000001c100d15603480c401e001e40880280425800148400100845035588a910216095003d400459003a40340d88a4615503030000420402040d40701c85d101202c14040d8640e00081c2c0000e4034051203501e210b0102079541d000140040043c10717264164800e801c0201c1d410041211601e00001c55242c0c00c6013009403a030b0380501021030080c01144000b0700c030060140205c81910b0700d603000801000c9592194030340340c85801040c0c02c0729400380000010315031400740118040292481d0180000c24054500701d5074030000c00e203600c084c8101c240b10030346041c0c1c0c05c86140a4075000a080c040e0100c40e9610001e8014020b00000501070b080d803440b02003000d130140c2c0180c2044150002101c201c80322101c0041c1d40c00030121503510005a00300010310800c04d8594000341c10541043c10141440361041c00241014400c803000b1181c42d80c0c2d003208000b005800c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 482686456 1250 482685206 482685223
    0x90c04020a02011a0d0c06050f0d0f090501050f1b07020d05070303020d0f0906021209402a0203040f080a1a060306010b0903030409060b13050924010c2102 68
    0x2214070f420720480e06d0344c0320009881076105040c01d01c9000300d4104049024181220b000d5038800c0c81c1000210349081d0b11800034480701c0402d0751b096103090f00090390314202c100c0f030764040c4054290f2010110a0f0581115269200b14000c90304042608001d600194040160001552098015040c0c0e04084040100905c888000510030003031a440100280d81d008641040a10000c00c1d045999001c0318010500750151045080c5101c6914000c00301c01068a0b02441d6020404903001a4107181400c40b400c29074580103802031034112520b0f0511914406808610356408aa0060324100340d80c5044000384203840368081c1e1030580003101074400f0441c1c060505082d01f032000892a4803801d104c03001c00d940e0401400303041e0301d01c11b00040c03108039584d00b00241c4004044080003480400d460740d102d414290080120b60712b8801e003007607010403145480001c07075101c2c1e411807100b40f9002d0300320044642d0070340138503510300d040c482406031100108006501301e40520f9250800b400d010480c5c04002480e14440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 482687706 1250 482686456 482686459
    0xc0c1104091b0e0601051303020d171305010305011a0d05070306170a11060408060f060a0b04060908010c140d1a130207050f06010803040509101205100b09011805090c04020a02011a 79
    0x10080f408000b48605210310170f8940550700f42b0310030111031034030383c4030780c2c80084501d00c85040100702100c810f84038010900c103070707103080c2e805212990742c2e070544003100492002d205586013014041259800016031140358441644e00d0003040042d66400e0b0304600d00d140704140e074003640000300740724140300700340204418800068a034a8a828908004240c94810180c010a969800d000212340d0982e01d50201c20090300d9919203260750ac550360176002e041d00ca0903114880c681e5003004100740d040c038040e2214010945031a10498603060fa96601e803401441c2c0e00511414403e1403080b14041500ca1440440101d110300c000184c0c0c4100c541001446d00d00112040c18071540701a005200e0144040700f40c8044070300580b14880e803915144802c40b42c40c2d0443d0840e448480c201103c40741845400510035020170000742c8104031000034482400403040c000d024503a10460f541076007030a900c0442e4813080e80800303030390280c1c1c140c00c4107140081c1c02c0c2d901c00203030400184c3d1280409020015004000701c0041f50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 482688956 1250 482687706 482687717
    0x23060c1605181602100c020c0310110a05030a061206020d050a0501050307090902010e030a050309010908070503070b0a0509031f0f0b090f070c080c01060e0105040c0c1104091b0e0601 80
    0xc0386441c9604400c1d00401c404040f000d2508602e2206000300412003050300c2d1400140f09032200b15a00030764803880d01410704d10074424600b02c8524042d043c0f01e15500d07d031400700e00f64070340084108269001c3d070000e07110700240c0356148800100b8400340314502c1800d9215543c09a075030102c481c51041510b00c09008600350500d000c1c0100550354001030362004850508002007000e102500041e54000c00340c1130000d8060051740e0a480810001000074944c00009803a540c40c0780e40c888141a6451243d8000c20b500341d800b81e4006e22191003c3c00203402c03555030714900503203041c070341c1e40c0440c1c1400e1150401c40075071002856009100e01c0280904001d107200c1030380030820380b558940043c40c0800041d210955184105010403282d9119010301140141c00c00c0316503a0300c1c00a203001500a02e0f861140c50549038001d4004611460a40100000038615580b02010590b45480d0041d1010391302c20815841030340c3c1c0d01100001140d50f5071078484010b01743ca0b4421040e25013590700d001c03a800141003504002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 482690206 1250 482688956 482688979
    0x100b0a020703170c010509010203061f090302060d09210905040c0e09090a050d050c0c010804050a150b0d060b040509070f0e091002030a02030709080c030723060c1605 73
    0x550001c0c0da8022a03030008480891060101c07580310252107541040500c550a1104200c2c0c60744054005500600007903840c2d00404002074881003043e171248001900140e6000c104102502e46800a410380c0f1802800003d6860206e50305c00c2401c101040e0150099800380500e83d800c00d402205010041109440520400d032480400402000c10341402900c2000c200f00130400000b0100320050f00c42c2e0b800421103013045044100907000d40c1221075404240d119501076280d241d44603038641c5001c0c03944480100407040039560b40c10519050124038071040c0b41d580c1080c481c182d64654083e100e6602404000440c401004144403d0b101c1c0149000c44a40c460001040044144040007046901035104620261074040b034440c00c2560110102c0e009600110034049041059801140074120940b606402c40795904482502e40c1e05101400d94150001d104c00c10147c894a51400d400c415060920800d1420b40000a01160041075400301c180d0300c1103c4241b046a950f114080183c07504981f90a00ea9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 482691456 1250 482690206 482690227
    0x40806100e16051b03130e1b030112060e060c04060801091122090609020d1d1903020111040303170919020f040f1d1011090904020303040b040905100b 66
    0x1c1e41114600c010440f001840d42080041c040220144001440589642d9080c10b0f0452502a0180c0039007102c0c22040c5000c103aa2102000d4451040506000c0340c0b42103038684860380100440c40f0fa002e49001d505e030706064601d030000303015061082010381c55041d01e07a800c2490080000300144c001c400c0c6a4039016410104984001c162003940f10045400341440600c0d000341c00b2440003503401601d4880c1040e01c01f140c0744881760050466003051100401c60a00f8003805006542c140c0f018940b1940c00131091014a410780c2901060074074028000402c00380300c07010b0341c5d400691081d071054002071000441c043c4076402aa00182c1c0100c40c1e48001c2c00a507402c07040e07d0703051215030040248140280e100114071512590480800c00d04401001c02040b81d10460025218466020088031030162003450a2207191511680b5054400d00b90500c0c1040200300901583c490060403d81e4548004d11002444010300c1c40100081d2544400220362400d00c4c1a880070b008072039810084030290203100d00d8140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 482692706 1250 482691456 482691481
    0xc15021b09070908060906190504020a030b06030312041101090807061e03060e04050c0f180613060308070804050a14031027080c100207021e040f02040806100e 70
    0x290142103504414603110400c00f610148155407002ca0b060240a00700544e00384080782d110300c031f42803021070381142070000c0025400b114411075000b036110104200600c04980d8040b0b034541d00c04000b4085a180050b5a009d401c0a07040c03c413022141d140c20710110440959010040c94002c10b91640104007007428160060484401d80d00700e090120710380440c10400c03600c60f80080004000d286250026420242426911100c1c504ae800340154030f044404803a60501c44180e41d41c0305a540c3c00c08010b41ca81604004201404400c505070031600c80f100072000c075040800a0898510500e0250b136603520380b13418030850035132a0b4010b8400f80c2c1c40e4200c0520b651404078601d02440a07804000900c0050301d000c008042c1a200d8505404036215a18881003110050003040740d0f000705c00441e000000106101c07000e03403140c004000d4211000b02d00c0002041c1c0000104610520020720102c0d80d0002510910101d8006030301031a044d5000320140403003501e540762080b0150110700b40305030715842c118075000036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 482693956 1250 482692706 482692753
    0x6020c0a06051902091c0507150f090b25061b050c120a0507060504020102010624030e0109171602090f06040c08070921060f140108030c10021b06040c1502 68
    0x130f0075801c1b6006008010050111030050800d50b421022103420040000b040320507551500004182c400d807000ca0462403200555401d1001500b041e2800e22804e41c510a85002c0c11004652250f181c00380c0703150410407410082d05103846945d4071a142d1070306010803498054040c0020790040404c005c642c002c3d60b0f07c04216810140c10040224994a4a04c0101d004201c1a8410100c86805140c1008400c03030008c060804602159010320103611089425822a5500c4078000c1c002d81d2038001c18082401c055024000d403a001038194100c140e4183c01046070b04404a4000510554000400c4040c0c603040c8110004d10020f0300e070003180303807034051b40283c07191943d4001c42c42c240728a081084120140090281310065001800b404481c400710003c01c054248091612a501407a100220703d014001068034036807001000104013221003000290001c5d0b006800340c940040181c0c1901c2d0f1990410010140114400d030360030440c540c90500100c2030880d840164400315009131b00c990090f06800c048442 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 482695206 1250 482693956 482693989
    0x30f040e16050f3114010e01140318031209012711150403060207060b0a080a080706020a0504170d1d24160309080c2b06020c0a0605190209 61
    0x11502c5080011381034401403207030091106503400010105514030b038889261060300003a00d5032140e50288500540d090b00940d05001c6200805000007000c41185101c1400605244015245081003d841010101034100c3d9004010f0391100300404a001c071080300e450788042c885a401040c15001c1d40e840e801d0040030002c01d4070a002c8100300021284012048600460b4000402c42d0394000c4c5242c000040e0000c800400c5c41a000624001013449002c503114481c26840342c0032b01c0c0381c0030070b60340c0c0c400c000d41140200c2000c0003814040410071000c0480d4081c0304400080c000e24003842d410340000d002c40d0503411005440020070341c051505884050000184403040035200e80c00c481e0708601d801403405210f200c81034402780301202c942407603044103170b44c01603400e4003054484844031042481103041c41051350880100f440704030131004c803288001c2001c090744110750241c034155a281c085807504d0a00300c401e450301c42e941c0080c08410407844c0075814800c1e50028082d0b0a0481020015280145100140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 482696456 1250 482695206 482695237
    0x120c0f0b0909162705030d0f0f0f03180303020309070b040b1608070c0e070801080303040f11030c0915010815010206062103030a051905010e061002030f040e16050f 72
    0x410905020700c181c44e603c880c10000403114481d000203640d113994114816507002e80a110070000b0840d100310442c0b1907440607500c2d100010003601200b180d040301e08000c40d00c10141da4150701c0c082c19080e0060441030f103000e82d402584900705840f82070700344203042c0d102103103407201040304010f42c01d07440d42a074144400c04100142095290304282050b13200b0007400400e80b01d81c9450208442c1102c0c001e081c0129183d589150107a038840c000d4542d01e10040d1805001d1006450998000440306000c03180b44070300c05426105003c2c1c54001003082d030301d800d83d0089178010050b0290844d550780036800641c460b014038602003051902400203074862030060f080c41d0203101030401c40c142e05041011031040300300c031510440340c0e280f40508582d070042c441901c3c20504290b03049040a80c2c522a4040e060580b4a2000038114680307402d41081001e401148010f070079400f0500c01403440d41030f0710700940b0090040d40074160541c0781101e01c00c040e103040e01c900c0c3c42c01c0c000103000c901e045039000419100d02004c1000c40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 482697706 1250 482696456 482696491
    0x150405060c2809080607020a1104020702041d030a14070f1101050f0f0a090e25020c031e0c180601030b0f031c08060411070b0a06120c0f0b0909 63
    0x78a4144403030032540e070b8410301d0203090051849034810301240c101c0310300c00300307454803910360350380c101d8442013200e20107003241c416142000101c0c9001d6006200c00c0b4402040041c4044440100f607081e86446907021155030000316042141c65001422003003d00182a101031a0828598031203a2142030f150f006024403c51100e08981070740a5000c40301d014202101c100e896200082c2c201070203500030003034200052031009000420f151178981c0d21f4020740400080e90146010001070901d000600c060860441c8162464690141c4080c040621055403d2550350114401000c000749090104a54035024071900003424069401005600d600b048092802041c044080381c001407810000e104080c0c1d1501a01c807045441c1001c02c2105108000503884a0b0f030a9501d50041004a8094a800001a01c4200102400902c04070308407507220300c8030080001c010f0b072a203084005005941030211480a120701040c041d00903581d1f0094001c1109281c0245070410f0000400c0c2040d1014100d00c517400d034180c40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 482698956 1250 482697706 482697727
    0xd020706090b010305070807090c0507030c0303110d020d050c09030d0e0d02100225060903030e0402070f0305040608091903080a0603080315040e01150b07170a0809150405060c 77
    0x700210701c0d034100409112075610303420025202c007224070440309144a4220001013601c9580500d240c2c100341c9844803400c08050380c03016601420310005c22030400d80e40d801d00000c102e5441000e0135044250207401a112118844450304507040640020718601003800340450719a400141c171900e13401e0901e042c0000c0d0840602140c9203207041c0d40001c0d40a02c510200154044d80000d0b041502d040c60915004800c2c001d074101c0076445864021400083d00d18642400480d00660103001c81d0303400604010301e00402c0f600d5a0101a480c18421000075500017010802d030340e0b2200c4950b0300403401c0006450000e180d961800300f1031200090090600c1070150000d041241188d000c04021a0012080e5903249091246004010506c00b0303600c1c8950314003200303201c0c400790511580c02090142650159903130704103945810147c001640803604102c60288150f000704018020f04030310005612000090b0401803900360a00d80040b100c1c409020b8000c0410000c980006025900200e044100075540c008405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 482700206 1250 482698956 482698961
    0x11010f0c1d1c051f0f0510030305030705130f090203011d1003060522030315060309050c04050c07050d020d08010909024f061a030411010c1e0c1403030d020706 70
    0x8449080e00304103003201410341d003900548006006105c0c10059030f51003445545c3e04207030b41d000240000d0400d0001928840c060300051400301319007051004000c0e036520042c08484020740081681603008401000f0007070388540c1440104005003500142450402501030301d07030255100c098515519034000c9100308000c0504c201c00034030340004000601c0a07900700a401742c02c0b50280c0d09060801001c001404d68400d10070319494980c030102030180e4031105810040a050058000200c2c02c00c00c01c0540d000813410443c40000740d4007500a01400e140442c1c000e03046100c16441505440e08150007007005a44116000303d03068030684e10520146144180c0c0c0000440c2c0800d05200d074521884c0260310105680e888441012030064103102c05a2500380307100070b00212210782c00301c0080610100d03000800380c82c0d110b01c03a1881854810940509501c1c4c013000c1d001c130745c0a540a01210388881c5401e0100c5d80802401600e490b48050f55120030800200340d17281700e460144020b00340e01049040c200510768 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 482701456 1250 482700206 482700223
    0x20304020a0308190219031704080f0301090e0709020a020a06090804080703080702090c090901181e090303111303030806060903150a0e061608040311010f0c1d1c05 72
    0x2211191300e48024060103000d00320040c89450251003040fa9031031610217029101c1130801c3c0d0580d580070321042810040b06031404080d0003298080c40034401c0c04ea0060f200d0780030b18000c0102c8080810310440700d0b280c0b1802c1076940d8000b4170b05075004000d601c07011500003441a1f0410f610400000754080c1c2411314038810f010355000a20315010310f45001040c00b940001900401740216090245510b4401601c00b00340302d503210b134079007001422f40100103442e02d040d41518241641c20001c40c0803802030000c0b42c10000c0e01c592002c541030366104001d0916030315101d411070708000b070b000341403421010b4000c0c1c02801c0c0c3d40348401010010100001030054840e01c06580380100064120740e248510401a40010340c0201c441d9801d0f40e141016203000000c00241e010300070f0b103007400e00213400380b4020800c89411200400560a019036580c20001080092085550000803480c00148200384014000c0c040d024040d84910b680080c25500c500c00d41e05c000c180101010300703541c0d0409a54451802c542000d000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 482702706 1250 482701456 482701463
    0x105310305010f091704030c06080705070605040b040b07020105010602031c0b030f01140c070c05040e0a050d0816031b0e0d0501050f04020a17100c140c03041403060118020304020a03 80
    0xc1c4000000c080d000c84d0001c8407414803c00f201d00100032041c090740a02c0c0154440030b030001c103d112003001054028040707690462480d19000c1d107085a1741e1a070320107541003500c00701c0b00400c02a0410040c417001c084000d4004c1c20a03c024080c551400c3c0d00250b9900980c00940d201265a510f00d81c4102070076170000c24000e07009019a02c0c070002c0f5044d214001c02d8071001d01e11410351020300055640e000002141d2905030b0140c811400b1034103000c2840010544611541c40600c10f9240b10300c0030420400800c0c1d8a040c89582c0c00070320f440d00c0048d8900c00c080c8003c80b1418581003050001100e002904090302d40c429070305d42040d031150031000207082c0c4c690001029180d5460300c007c0c000200c1421840038440d80c02030700c1014800b03039911281c0c0140e41d80c200303001000c0d0300164141c000741c40c80d80d00040100c500d03610b0703d605814190310740341c0120341c000c10303c01d0915407000504008241000d02c00240218080f000360109625080603080c0e11070160034602103d40e4000001403c540c1c0d2000081f02541c1c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 482703956 1250 482702706 482702711
    0xb07031508010e0601061b0b13060902060c0a03020c030106121509080406020c011d060d05100f120b06010c0b0f1f060203221a030a0b10020a03030b010531030501 71
    0x44009404c4e124007085c0581800100651000c0e1120031000204614940e4011801c6000b5550790788000342900d58600b0856070346032a40110405a65004054031020350484007600800746d6514000c2c2c41d001210013214084e034100f100030030600100e1101c064003950094036080440303280f00590340040003503a000a10040e070224010400c0c660004210b0281a02078a80320641408035503406594101203c030076600c200100300101d440390040d00255045820300304528030b49926001007212082c1150400c00594072101c4030707070050104005049400035003c0c01c24111216080c0c6485612000003491145a010810080780c8102e000c045100300b000428820781c2c913402d4482d00003e403698040740300b00c40c2580d40910600c01040901b0040f808a41404944071284c0b0303031031050305000d03800c014620078070b9640d1180a031540c3e03141d04280142c0403d465015002c2200030f0300c0e010781140c0710a8075071810007100384196541e442c1448a2460071495690506058501c204102c40410329030ba0001061b070350 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 482705206 1250 482703956 482703971
    0x50d0209130503074209050a150c03050115091505040504090b04021f050405010309030e060a030516110a080706090213061703090a050d020a0906080a02010f020a0b0703150801 77
    0x10000214400c400c800c01c00044c103e440b05d04240c5c0d2400b02c00c0c5172841c20400001610320b00e14005a2040380098400c100781d5804081986454014820310080c189681c2c0e11148a411040d40c03610411b40900011458500100707019040181041c03041c1c011401c0086410a80c640d1240c02101920001c100042c001c1c00003541a140078008000140c034128000c1c280d82d0030b0740c41c4031407018400721841c20490340c03064209440c0100440c05801c082c40f080d0107000e0107041c00126a19120f0042c01116100c0d1004141820019049040611980610713001c100c0030295458000340701003807101d603554003c402141c480081d41400d2008003002d0100940c032140c2c003140b48168600c16040001250300200c0d0141c91507000c540c007241c41c1e108080d0402c1e44840c50450078002482d1802083d22590f0001c1c0c61072480d103803103e05c2402228150b8110110690041d0703000e200310f41c1d00211003880100544080c1039515401e41d01c0c0070b038200014000030240754554130b81a10384410003841c4401001420024891075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 482706456 1250 482705206 482705213
    0x20f2e090501200a2f070801090516080d0c080d05091c02070e0f04030e030a0c03020a05060403030804020d03111e010c0c050303041719030c030b0406050d020913050307 74
    0x30f10500d50319000680741850076620418990050f5503603003180e0346501c29455081c1c9800c00b81d44240319054081006090005031981004111190142c20620300000e1992000e040c15450f000e40d00761400150006ca401c14004002c0101d201506814281014061a401454401041e01400c1c58040b0301a00c1d040c10481c1c5010b0000c0c00000c0c0e05403060034000400c4004404076291030242c010003d040852074042220020440340c4154440c0c028504030100c01c2154001074240039200c03500ba600d4091440c410310951038841d0484004103422140a03250620f5650003501c07400c0001c1010780304542d188107031000c2c140031b9206803421f140c03207500382d480480c200701c1c844e140810091080112580f829011025690003210721313030145c0390080300950455482d131b9143d418008a00410002c040300c24000c0803240c20900c00c1c00c0c041207241d17440204945482e2200201100c100c03000c92440b03503003440e1040050f43c4a03604201503250b0183e4000d40517aa9007104400104c083d03140003030080c44000342d00070070b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 482707706 1250 482706456 482706461
    0x60306020f0d110412140a020a12140303060109050132041701090b041415010e010e070c030e04090303090b0408041d04081206010c0c060806040c020f2e090501 70
    0x250714015010882d88802102a41803400346008003180400003e801350007142d09044c0b46c01000701100202c03010070300b99501103894444030303501410200121a11203420094080781d014920342c0801d0045040d440d01100003011185280314443c10721141c41c0e100c942c284150004000048403401000304000c0341308030500140e6100d485043d03c0c20345a414003059402044c0610300ea1950005014200b030340307a0f0348850b04400400c10420003a403044200700030380c560b140c440c850b0082119120302d000355071501c1199142030000034480e204100703c05c1c0306400042d8100c20000c0140100340c40c00610024180350580081a484002520a80c040c9081008028124009105869203d50500305000300c01c28510740f482e00543c1c1c010709820b0706000309010080c0d1490080e40c4030005261050403003a99845460210010b81c000c080003900075010410300d82028000d0782000c00e0140300400004e01c100c9001c98544c1e0000e180340e0042c080c1d4607410f00c0010303826030300c1040e6a03d184000704540003c1e403501500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 482708956 1250 482707706 482707717
    0xd0b2d0618060a051909091a0703140a050c09090a0c0f0212031f0518040c1202060d020a020f0706030906050f130f1407030b1b040303050d0f060306020f 67
    0x1c1011071049040d000d009015216016580203425100306508001c10450804d03d1705940040f0000b20300d40000311700010f40a070414260281054101c8964001c04910300040c000f403000c421700d41488100121414010322860f8001a501d000103a40e0311003442c0301c0b11910603001c101d54000240c20034000c1507100e40d4031070048a801030702c50003003042d8a41c10690b100d10601e240340c00d054505100081d0001c03c41000400f035001c6480042d28019240d4002950303010011592905800e1050304200800c508001c0840103003c9000611607000e006500040082c0b15000c01d40b40e0054010600000c03441c020400850350482c10030507210f069440c0d0368020000c11b403040741545c44505000114021080700706440c0c2c0900091404111070a02030345a095103074915900071640d090320710480901050090200034042c600c6000441a2424442198414030a002c07280042c030714420401040001d0300f00080345c090500704034012664650001601c0020070316076102500040c0001010090000303004006c16 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 482710206 1250 482708956 482708959
    0xc080906090601081b180c07050d031e0b0a0b030c0304050706050307090b070516080f0705100512070e03010204260a05100b06070c0b07030f0203090d0b2d06 69
    0x412558828031082d07940c00307080c400c804c081d400080085a17040c400480b8841e134001e010744000851207a4030514804c03000111490200247e012030064100981403044c90349078a03c501d0700340300b100c1015500402c04104040740100c601d0b07071205001c0003500c0301c1911400402d500440a41c882ca040c54000304154400ca6007240c40d40107020001c15218003500540c1c2c0100311175503548410904014582556504c80d4105580901c80d001403141c0440741148008060b060900c0a070034250020420b45143c411150022881100040340c0e90384c40c5a4842c055805020785e100e42c00d089516218400d80d00803040290b8141c00d54000503000c41c00c141e60031007402403282d042d180c15125030803c450190b2030b803100000042c09500480036242441400b03411070740d942c0350004c02651400b0030f03e80e070f810618403265200708001007010903940145900109005d20140090000e989061140170004044440c50080108895901c0000c122403656044030050441055200341c40c4100f02e660074801040c0c82100c01a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 482711456 1250 482710206 482710213
    0x8010c080a090f02010302031f032306190207030c12020706260a020d02160b0105090c07050a0201140d0207050c101d091b18040f020307050901120f0c0809 68
    0x64038803901c91184941c40b5400124010403030000742c3c01100039500c003601c1d107c40001c0c1624019038030240002064000c6101d448054548105c0030780310140f11481002c602d030320341c02240800130034030000ca004001203540000016a50303101c0e0f2406842d11070400d48080c098185110f4400001c90300080d10809440e03940d140c0c0c10240081c04180e481c1034070407070f4039101c404080c17901040c203001640d00074003450105440098141030504003040400708a01c04250b9101d010240104110b04004c0645070300b00c521084140d1500781c030b545a4654a49801c00000d04100c00c61781d1900201001009803264036501c0d000540d40c550f114200b0b150342d01e6658000d80d02c1654094004100940900610000343c000399038551014001300080200c0100000d0071500e0500300e000c8051059100d0030010070740c04040509292880000c0c0c010f204c103c03485541e0766030809104105101c00103400c80c00781c5000d01401d02c1d0a1104895590140d0041c141c01000b01c680d081c10010714051090b00300c032801c2d1080f42540c044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 482712706 1250 482711456 482711461
    0x1090e0109020322030f0309060b060c1c2a0203010b09150916170c0405120f06090a0c120f060501060302040501021002090f09092b02010b030c130e0c04020408010c08 73
    0x14038141040c8400c4c010f01142c50104181c00c414025001204664021680002c6162044c0c01158441d480f01d0010580743d0455003e10000d090001c0000380e081c080c2d490400c505104000161074803125014034203060b1002180900304554094000e050031001c0604001041d0808007026003000a007000305501c035a90712000611401c00b5020a41c074445600c0d510088441c01c07a0a1f030644e540380152103205000f4040001048c60380740d000c010903a003203a8500034061441c04080c000d00341400584155a2a0400a0060b020540f202c800f1802d40b08081c5410503100c0c900d1400c45070740100c40200405040c1032a00000324140c041e0b0103001110000c0e0241e5070030542d2401c6041c224816851015842003021006100c41d080c20b81509510801b000b04840911413020b102c04a151142c414403101c41c0007031060900160703428000c6ca00c3c0444180c00a081c00310100c030009100c0308028101c207c0903684c41000c03035040c0314104510036440c40080c200b15902c944904416010700b20f91716003000814000d401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 482713956 1250 482712706 482712751
    0x51c060c0e130209040603050303040309082103010608250f17010f0902030c0d0609060f05041407030c18230d080304080310031b09230a0b01090e01090203 68
    0x44028004001441c04009442d00c542910003900240c03c0c1d242c2041d13852070080f00044003000114041d50080d1240d250642c80d20b55145d10341450740e5000e00194561002480201100300d0540303066440700d04180c0f14035521040c0c07105c51822a296800700003a0074509000c202d40c0c00c04580d2410701c956994040251403c000401201602881442848401c05d4810424a65664040c5800c804e04000c25890004840d42e1001665815000641c04030340c4c99004000202941ca4400c0c01024103550520020386008540611174400400720818991624030b2402d50605c41d185940b08044842c410407200c4c5d840f21140100d440481080c0384c00c1c6c00c1c000200481ca071910303010811307035594020060303440d560780d654481413203420140ca0141c0d00908046c01100040341120f03102c0c0810011741d0b85580092500c0184826260394081130822010024080d905c1134078030301c0b1a90b034800d84122003c10180462401250f6580c0b0300e038004000201d030030300003040b0500b81c0d400944c05102c0702d140b8144906804071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 482715206 1250 482713956 482713967
    0x309090513051f0908030109020d0609110712021c170a060b03130206070f080705010507090f1403070b0a09080d02030901200f1e070f060804020105070606051c060c 72
    0x7000d0042e034002c0d10040301c0340441811040d1901003101c0086080b42c140d50314400f40c0e81081e0400c1c000c0d00d8000c0349d205000c007960f1048100400d07540900380140091040d00b60313440d10a07008060310405070704600c41281c0c3c0c001c01036510420b00220521070076008100d4010505201c45111465008074140810340c18803040c00342c0d03400c0c0c0381c0441d4001d285441c0d00c0741a0711502d00746078040381c222406008050108240101100c2c203d801200e9407031b40c1e00c00030301c0d1070350860710004c192400384210341c542803145005042005c01500c1c00301c0045081c141076100003e151000307550000014680014403610420380c0023050000315050103040341c040340d10b620f8003a41c50f40595003406001507599000581541c040e61060b4841e441c1400990f0240003820320310508100c030340514a03910000038542c50640c0441000407600402241c00340045103401c041009011850142c00070b0f0400001107102000d0140c02e501c0303100100b00003031a007034900c00040750840116680d60700c03d42d011450b14034416800b50240 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 482716456 1250 482715206 482715241
    0xf03031c050c0c0d21021605010c09030506060d020619020c0307080a080319091407050a0f08070e180703050706200a02010f0c17040e070f0c0818030a03090905 70
    0xf42c043e1a10840000d000c64095500082c5088042403020f94400709030a144001c0c18442410f10307281c1ca00800342d051150a4817030158040c01003040345203041010031004150760703801482c215080c00341d1038114000107481e40255400509401528010200c0b030a80029030401c10902c25004e40d11415503500c801030312024039001c040d0034040100001003030b41ca82d010310358141c41e54030074000400740702c15160710002155940310150383d0341c0700c0d4805010a02d820480c80c0f00500740610340050f203030300300001151920030a100d9004059004404038000071900b44400c0b80c50b81e4203804660780c041d641d041c080e0703551303c03140304001c0031031b800769042c0045287d07603540100b40030030326802051499016401101d0012690000341d0412041400410005d0146440c101a940030000c03207a4945d0305103075100c000440050f14280a20002d45038a0700880d41000c04090003540090380f00d0380328040003490320700c8801c0001845a050040e940003100301074105942500380c4802110410807995607000c4207103000c001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 482717706 1250 482716456 482716477
    0x3070b01061403130f0f03120506100c020409030c1205030105040c050403030c0b0603120f07060c1107121106030c18040501080c0d0c0b03010b070501050a14040f020f03031c050c 78
    0x3c10000c0c0e088541080c07224003440c8200b040135004411600c2d0380e46103900e40c40c0102c0c005106020303007241403602da001d5140c00000403601080d0384002d40b01d000d07003080442e490003800f5a071507130071007018540541d01c55419183c11001070b081200d500c07080280142e10901a03d413155240c40e031503a0059100d64103803819682d240e142c09043c0b10568541c5003080310000c0085a05200d5081214140700720040500402030031b59560303640b104594034141060790740f010202000c01c001390300c00b042c0b0712000081d4101100c025542d8018030748254106040003614203036803aa00180000180031308242203030020581c0210148080c911180369100300b00687d00d0a205080c03481d80040c40d090054608081d00c000001c0c42444180032107a070b106410811034000760702409007100085083ca003881001c3c060391b070340050840403c1000c02140c100454040c82c028101510040443e0903443c11511090f0034881c03508402000c0726110a5040c2041c201549510488050300b410328010800304000070064605031480c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 482718956 1250 482717706 482717747
    0x3062e15111b06120a0b0a0609050f030a03080105010804050a0506040b01360225051c02030a05030c0a170f1b0301050d0201050304050a08040b0307111605040b0301061703070b0106 79
    0x2413981011102000240c00c0c0d540321560360f017207070400c0d42c3c0b1190035000504503a22203112491800040240b000108404103000f50020800b41d40000e601610707950540d2000d0802000d2906e440c2407003440d24a41c20401482c42c4103420510040c001c0c504c6045040340c803500c500201c0ca002c504001c00068105450902440d00e004124000d1217020341c020303010790a1034a080c0d07280510f041800c0c0740c481c80c0c0e0b482c2c240c403c1e4114030050303007003201d884c1c1040390070090700e000943ca48058100014544c0c8401444102c0041000c60404121032040c04c00303008540b4581d2204059040001d81038100300ca0540304203ca41c4000c4810303080301036291055034101d03440140070302401c8000f5001903c0c0c0b17600040007183e0324024040900001030b14017001c4d101400c4c0c5025120b48901c4c2240f000790080b21502025840c90740302258290702c28524840030300966109540c041b42c4c40ca003c0010902404080e044400c140703110380c0d1600c5242c036000000d0121540901e8401c031031a44d07510000d94900746180c1c00e0b8502d80c2c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 482720206 1250 482718956 482718967
    0x90614130e100b0d050714040c08010f1401050c03031f1a0301090513021f020c0a0305210c0703030309020a050a1d04030521060301050603062e15111b06 67
    0x70b0081d4000450000050505800c000090340c401341844c849400403503060040050003030740e40c24244907031004030202e4280600c840d41440403151034400039205003481c0b40404828107a659200b8015294200d074032030120b03505d90629191040e0304050480441034000c0c48100b0005100d2000d03122a5201240000e0481c51a400c0440034400303450010414050416410b2203200141c0300c1ca04a80c1c0540481c240c0710200e0154003000a0030200e600550034402c603042d00c0b0610100d04013290916000b2400700828025900004060b03801c1e0240c0709220181d1b0092090000a054040d01b00708a1107100326406039100380ca4004000d555100c901510841200d44240000140380700d4a00903000f600a060282c103000301d040003042d0682c050b01401d46400004818003429080c24015240c1144c01280500505c3c1303410380700100202c84c0c1801694241961604191114524110a10248c0507118041d500700c02010000b070007603885164030101da40328642694003911030007402c001130030f03000400c0340d843c04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 482721456 1250 482720206 482720233
    0x30f08070f0e0f06160b01061805010e01030f0b0312071a090601150e0a03060b090a330e160807050703020705061812010c110307050c19090614130e 65
    0x11540002c50b420013410016690300c0441d41c0307422003040d4406c66621800390304100e00103080d0584a2000714a00c00785400038080c982e0001094030032071500b17290002d080c0351400b1500024180300c004050b058001c2058200c94282110000c0001c2805840d0180950105004500700180201c419001c5600320b0701c018003604009000700c0c1c000161520344039140d050303d080003c1001c5926031003291820b9484000c01001d040c51500e0750303031040301404200710140080c654a80c044481c00c42811120b0742c080714000e02940044000c40c09400c4c641000c0352a86000001d00c00b4540101040501103500080010200c52140c412a081164568044c0054614240038403800350007070f803880064040c0c100103c8805440e05e110007400e07101590008215a400303100c0250058016030801451604100001e901081c000100710648480940d05a0740910b0b200b210025112240c0d00541140c9080400015240700c0c605940920000201c0780b8a0b04010f443c044981110110204005990402e0700800042d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 482722706 1250 482721456 482721469
    0x1208060111030d1505030d122304050a02040e070807060c060b030a0309062c15070f0c03020a060503010e07031509090b01031209030503031801020706050103030f08070f0e 75
    0x194060505401a207a403480e010300755000f04100001c110b41d03c000c50024040c1290090004003c10390150010407034100b401003500000c501203084140e19180000c00720320407130010208100700d600031080b2600b00307442e1a585440e00c07504c083e880b50b414110700f001d06020100340c0304103ca18600c0101501d91a1000555100d0b8103070905603030890f80c1e020050b40e0382d01e0601072840003611a40d545805541407000c080e188081d40001c2c5441901c0704144085280071002c009910310808a50742c4401c0169010b104d50103110742d071002009805160b014004001c040e00384103007640d2003181d01c401c0003a26228121032030f000c240710302c11441e44c28030080f40c16240203038044904048a030800440054032204188256010488106e812402e503500420a200702d4007201504200d4510301a440300c0c2c0341d902e500d940c80c0005407129586440b045480e45001a00b54100c0d8880d6921038028400c030341e900d050142040010f52001ca0108003c003002500e4540b14505503090544a42c40c2c01600d0395169003070101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 482723956 1250 482722706 482722711
    0xb0a0c0c050414060901080c0609040902040f021c0f0c0503061c05070b0a09050402092b150203090606120d0c1115040501021b0102030f070807150b03010b0d1208 71
    0x100000311500104054480303001d0071220f80e928050f034140030304007402880000c64050307201c401c480c0c00980443e0390540d6454115100480200c40c0428030358503500000d07000b46150780300040b16920001c2c00070892070001620042489012004101c0b40c40d0317040b108070070780b0288108140043c50030800a11249800207851300c440c820a0401c2c010458a603541e40c0c43c11040c0e400906400300d002c152101043da0100d03618002d400c0070344095046c51503a00c00301d050f20340880d9403103004c00107c1d80e0040c0940e00640760200d1481d04040309070110070050b003d220003588152007003000350094100042c1c80b4185001030035407144502001300a01d0f0302c180c2c022514541510740848a40140041494281d5900e180307400b44146001d603002e69883c909800a450310705100d0707000e03000211010070740c0381503a0003100751401c44544c0d003001552410ba0b442d100d0070301e12a900b00104010480052100d5003d119404004003607419802044051020401c00000c0341402074014290101381d07501410f8075124610312034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 482725206 1250 482723956 482723963
    0xd030605011209081204230c13021c020a03021c1806020901140d0b0414090706080604020c160614090303040302060927070806010c0503160312240f0b0a0c 68
    0xd0500c0505c607014452000180c0701a20f0b110507810f6619448040040200750042c031000003405243d08441c081031544038141b860041c0d680e408aa624444040c0350700c0244501c2001c5d4086681c0ca1a02c0340c0034000750040b2680c180c04036036a40b04450036409612074000a813401c00941c0e000c00c00360b41d0f41e1030003030351001ea036180c10080900d030b030321b0800100c10025084140c004400400c01c40c100c0310510080b500041c2d50303451142d0034907050180c103c002041c00c1c815aa00c52402c24103581d43c04000c00c001e44101c2d86139802030712410b200d017441005a002080b09498403592840ca00b08120b41400324a40150801680d0503001003104000500d4004000c10342600040c1a045003424295a80b8920300b03203400040c5070452200c02041180c0742e01011013503025401b424256100c030071603182d441d660301030840340c13a0304070204201c10802d0600889101180010820081c040307a00400396101c19242c1c03000c1c0305002c0b881030003808214824070381e02100646101010030380c104041d402040b15030b90000300007907 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 482726456 1250 482725206 482725223
    0x30d05070b0a0c021b0f06040f031502120406020304020102070b0a2303190b0a0f08071502161502120d14060d120f0c12090509070c230f0d030c020d030605011209 71
    0x143d1b4591548805000106000103048903030515508101c814007100010204d01548100001e94548104003030942e00550410001a10303640c0398070040c0e107885115041044000320100c4c000130b10f03642c410000c0c08460181e085902c59400d14030221009030100380c0d08000c08525000d0385241502e82540410348039200200085140c80c1e8030f0110100c0c5203a01e400001550304804820b1280900c41480303070000c0a00c078070080650000c0f224904075451014045c504c0051102024110454800c100d550300903100d82000079510300d00c588910340103002d1340c1c41e400380e000300350000240c2c1880d01300300c1c00e10326640048403040c0080000800301c8004403500c5140050100f101011320105200c004004042051500c03030400c3c842c144410406039003002040d100c1088a84c607414400240750071050040c1e8090000c81c20f016039a0074010f641040e502480013030340707403144000b11800c070b9a050b0018100d00708250255001414981c0781107090325114001c440c0400e40b1940f0142000c00b0325171101503001e0003082d66 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 482727706 1250 482726456 482726479
    0x3070b160c08031f0906060c050d05040323100e03041e03150e031309020405010e06180f0315090a031b030e010c02060f0304060507082202130b030d05070b0a0c021b 72
    0xd2070446d0381a4004400190054107102c0c1000000c1100400107002030811906046c0b03540e03922800403e1050520000341810011151394090412100c501d400f440c00062148400102c01d06940e90410312504050040081100d004c48510030020002d032504101d1410f070100d00e410180000d06480d00407144107200400c01c4100f40004001c800010303102221f40076076103a10b804001004c003a00b5251b22446214204080114282c0301910018003482c10749412491401d0b800000b0304100720a525403c0003d01181000606c0c8004115022460311980350f050013810000c000320245007000d20010003246814207604407030740c018408e00c0000d030702c000d04440c50000c03901c0e07a00f2580e4000ba02e0407510b09865030180014240c1101d440d80c2c0c0041340e041c42c44840b803200503140c8210540300401a0040041e088044840070751508680c083c6c110140440d0216100503400a04660003103000381c5030681310f0804101c800e9054003a440b0001c00325801032252111150009504504107230003658000042c605 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 482728956 1250 482727706 482727719
    0x602071e05072310111905011b03020a0f03110f0a0e031e12090d06050c040e070302120118060312030228090e09010b0303070b160c08031f 61
    0x303014000c288501c018051840c0341c180100c02c044940102415141812516101181c85101d2001603800c064a02054003008443c0c5450030620003906103070212030014142c2040c080150850b15041c1600c61105030395850442d4220104d0041036110300025400d00081d80c0102c0c4240c01441c03401110036520b42c0f4004080f07001a055600410580700883c0f456845d1705000e1a041c08840107001002c109003001c5540850482c0d1a00314502407001042004649114181c940ca00b2010400340c0c00300082010741081543e80741150000e11556880741c00510014014500c24001d5804e6401c4030104a641d59007003001d25240406280d203001d520f0f0ba40d078200000440e042c601c03a11446695900c00607a1800c20070001000c60f2018101001049100707100b00c040150320080c081d0488050700440181900c0c1c0c001c08030b014140078524154103120208900e014040115032880c016030a80c00700350512a011681520507090444c4090410001400010190494a501101d40140d46500c503d2039640790300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 482730206 1250 482728956 482729003
    0x20903010f090308060102060c04090e011b020c031e030304030c050a1b180905070603150905100f140d0602160501060e0a05100e0103030f0912140105060418060207 72
    0x80615005502c8002010078543c0003e80b194200d002840905500e203007050100015114900c2a20359180d070340d001c885d140c117034203620030340d0005103500151205135890300d0000c0da0f416003540703160300c03c0c0140106580174050344580b5050360a28607004e03500f103075100d45040d6440407507240c003554940590710401c000110101a96003028070b1903a101824103041c882c8192817020301c0c5240740d540c94a48411400411800904641203a8103440e0204034040e0303015200204400a9021503506d6081405010906680d401d83c02c0c02c0c0c031303070017940200d00c03543d500c80c0042c0c00744442e8401034202c2c0c0000308800c0403441c90340081411140c20b109078002040e1039520b1500b1149580d00c0000000750200903c0311001c400c1c0034694010500c800c68403001030800340c4515142030184801014011100d04841486004001d0340000b0701c2d01003021a406100350134020000d003550013032050b85510f020001005482c140c851a4038034481000c8040b48066140d41c0c400c0254040903081e600e41c101e02c06001e15503512007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 482731456 1250 482730206 482730221
    0x15170c010c0201120e0d030609020c031e090310051b040b0a03050a1b0e12210913051302010e030609030a11010f051801180206090121050a090b1f03080c0102090301 72
    0x5c0100741c1000c514000800710f900b580c00c125a19801000b50030128803001050b60901d11050fa04030309031000345200c030231192250316140c40e054050441c01c01e11006055000901c5441f0007280004c201c03200e540107800a11986c05014080e900c14002c14903414485d83c072540c0d0040c110075000072092040a4030381d02c80042c0090301070008082503090107043c100810303803110321200c80004003009506140550207800074121880c1401802154021040d500c020076820a5000c0d0030040005041454040d40507004001040c0d005c00d104c0c407030700c1b0b0240c2400a540f47c8103080c0d80014604090c02c48004640d04905445401415929010004035444151140780d010b034030b011050590082d00c0d94140c2c1c2c20360300041e0300040580700e88420400581c580d80c049481d500802d1038040031032107a0300c00030400e10051602c0340b10f40300e20b01402c0004c0292140d00444020f40104509006079a43c40c001e600d940d20068041310140c4104c000400c009025100a000d880d45044005401e100b0f4184c00319003100e041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 482732706 1250 482731456 482731481
    0x8070513020d24050406051c0f03180f080d0f050d091b090203060108130b0106030f0906061e09061a0906070510050f160e01050309190615170c010c020112 68
    0x3d010040110b864980f041900804094810b0003000004407048150034803481070244c00840c20020407010544540701100c1d8034011600b00303001040e2030700e00c0071070700b0242c40c0a680ad441c41901c0600c0c6072a03008550040c0b89928503603a03286442d1484030300101410b1a141c040310207501110b08011101944180707a8081c24600d000140c0380c2c60100001851a10b01074240b4540b4441c0d05c07184004102c00d0300780641540e210f400c01060000f09500b44800420150b00050492840d008000c138084c1c5400e103d41e41d120445908210103c1c0d11a005401150600c1c41282421030314100107a18a92038440500441c080040040d030521140361a041c0c186110900c035100d01a99810400c5641c014140006410028502c44291500c1b103150024000400e5442940c0c140722011001449244c0f0802c9076410890368481c3e990407106440c98044090060f10005407041c1150140c04205030a070140c0c2c0d0340441e9024801040200e0000c00151100304c02c1c010281e04110f80309007804424920303805a011001d84 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 482733812 1106 482732706 482732771
    0x6010b070f02030a0c06022418070e070804030f0e180c1303030e04050a0c020a03080403050d0203011412030301051809030702091003060608070513020d 67
    0x203404070003541403107540848002c000c011420401140c506400321154200000b0503c03a514003800720011600241e8400104488101c0301c88503a107242640c1650a0240c641104200d1914200c82c0c1001280c040d0b401c1c0010035a1040b41940c8540c0e213803502c9940302d03410100203800c0072205003e60307000030920008501c04080c0e4004451813489a408407050303599407880c0203010900d020780d82da445a0310744800500010403e004601c045000d59014000c090300c950380c2560343e880007810a400700101840a04001d0b0f07110303c0154082d0142c10010760a01590303008100340c0801210540607660800d00c0100490744031310062481000c00c078803c098550f612101614a98007420030b0195010700a0424080e002070301d840c0780341c140c0307024480501020f52036005c040ea52300003034800d59410240509209000f5022580a0708140d0031020300840d41c007040e0f908005040c0030148031000c5200 = true := by decide +kernel

theorem cover : BRFrame.Cov 482553956 482733812 := by
  have h0 := BRFrame.cov_init 482553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 482553956 ≤ n) (h2 : n < 482733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
