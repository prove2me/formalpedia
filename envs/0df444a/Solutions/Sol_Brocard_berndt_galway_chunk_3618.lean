-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3618
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:11:23.944483+00:00
-- url     : https://prove2.me/submissions/ab453193-e707-40e3-ac5f-9449c2b05118

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 650539568 ≤ n < 650719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 650540818 1250 650539568 650539583
    0x1050102150a0f02190e121b13020d090b040b090a081b0a1704090f02120c0705010f050a050106111605061b0d0203071e20190b030a06060e09060d 64
    0x2160700e6042c04800f29400080c140e624290944072000800c6801504d581d841d81ca10b8004103038030111032320f0808203c0031181d070070344911403a102d4a81da4280203002d0201306d541c0082c1030400880c20030082014080c403861245264a0454843d100500d5407000d0658004103616810492080790100d2882c42c00e03800e07001c00003145e0f402040d541d03c1c00400204028200c20b034003004a000e02210025002d04102e21150450440c100340780d0701e8083c544900050420340c24540d0019441050002c290003514490380000c1c0d043c031060074900b0300400101401d1141800140c1d58464120040e440801d1001e007400750745600200319030030041040b074143c1c010203444520041415020010000500040c0800354194000d50340322070b02c1c0c1c1002d8059120b6941840d0744044408405d0001500c2d42034200c00001081480002017501d441c049a20001c1d41c4100d87c03a520041c07000007540c6808040214070405c4548bc0c20f00c51156248803d440c0302c407108031402e078000e890303000048850404000c15200240107112 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 650542068 1250 650540818 650540827
    0x24050f1b07080105010918050705090705301e0402041d011d060105031c031112040c17160b1612230415030f02040b040b0d0501050102150a0f02 63
    0x280301e00d440c00c141e2240b41680d450b1030040117080c1c21446107110721017001e2501e000d11007040e074440d500c4d0351140c01858480c1c2288070100e10860b10070f000341c900c003188031546a030000380500024140b000110407909155144100012011581c0301e684100010302100b6060303240c0c0b81c0d0382c2000054404040000074a1800051a04010009000d040c5004004040d00401e441d03004030720904251050308034a010b64403075a10783e07c00b8240b200d10024010f506140020320001c0ca003d51041c1c520030140c0045040580c1e034180001e00101c0701e0384808071080701140658494000e409603443e40180c0c0b4041d0000d29500808100c108540703402845440000c45a0801c000c0d25030741c1d03d841c00f10811040c6000100722002d6814098454180007050060344800d903420145803960100c5401504400103003015140d60041c0418802c51b01901c0c090031444121589903a140c0c1c0000885030018184800a5414100006002d50000c01e04501010044141c0c450503520030410801803c4a01008842540e0811 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 650543318 1250 650542068 650542117
    0x120b0a1a09191404110105040803032a0c0d1205151c0602520c08060106032705061308040515070201020114090309040b130203040c24050f 61
    0x89580341e1600d003c1c50701030079402c0a0610740340c505d16242d8124103112040005100c0940c002003900d500c10550840203d421412030040a01d042c90140c40e0701c00d4032408a6110012070b00403c0c1c00c0751071403c03075070750304034503486681c103071058540a6450144c1005160713458080ca051154114105003039014000741303449140e558490890b4098103e6444072035a0034100941082c40582e104c103103001d4003020350002c4040380c03103210004603041e01c4108080030b0000f4020810608854400003410103000791240b40d07944100c090060003840c45440058940010402e02c42c121020a010744240c020b4001c10f0380360360b40900c0280301100c0a030151544e1006000006595840341d80040100c180c0740c2d0b0041d2120407910000e42502c1c407440307002d2042c0405004008005900000303850301c0070401c80700803805000020105040d22680904995900d000000300000e003c1e83c56980c3c41101c0c910155541c450000648296100003000e100200145042240544900c2a00085c0c440403840b10381c11084060500c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 650544568 1250 650543318 650543321
    0x112060e04060516020d091401020a021003020406030e0a0b01030602070c080307030c02010e121b0a0e0907290f0f0f070506040302010f061d09070e01120b0a1a0919 72
    0x4407022251980c440c010442d05681d03052a00e0010382d0540010b110042004c0c134068446002e50081c045220164422010380c0c0c5c0c400c00546140caa0003500320b2400c03884140d0001c000c2e512500070707040480e081c0301c2e00c184040e000103054441d03da04a141e8039010303400c1d50f940e0170203944681e00940360040c0c000c4001c14641c80078002043d034203200b80c545c070912210300e1001404129604580c640f240302da1064501c0740340c1c0301007015618100812401010390740d80d9000110807440b070b6049041e8580807881044581e40000601e001654410000c0641e040000c41001201208964104030584401e0049410050a14010b040d46200030602c69041182d141c1001036660400401a0364540c04102400280354082c840c06407041c403107071414003486040551404040e088012269928a01d01002030440c0700309001c0b54003e014602030000495941d02c41c540b2541c40c2d0450260743e200c4010b0082030720039800d4494050b600842366181080c81c6965401c02c100c18400405803581c150b614043c87d00d802c1d02c603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 650545818 1250 650544568 650544571
    0x6030a0519020415080d0e150d1d0706120c12090615090510120f0506040302030c1203060a1e081e01060512190519061a01030501140112060e 62
    0x103140e0154807128640100400c0d07440b0401d0401080e045600c0500c5000408101d20300c0000c11401c0070580b1403d0071020801c401411091800351103804100314081c519581c002800b01502d80303040c0b003e0381424400807a02c4410034492580807580c005080d41c0e02806a400006100c9583c0c20070340d9059100c2542c2406840701e0342c03000c0311882e544a00e66007144840e50721401c09401040b80401c82454068941c0c1c02c01652070181f014107100c18500d10007084a400b103c0d81d4030704c0c0c3c007406031449800d080c600650350703800062102c40d035030180010910b040c64001c410382c6c2c401d15004084014070f41c50071448444801800d555402454031a01d00410212420408031001504081804044940b109540c03800c441590704800e220741ca00000700c0e40203060000700c8c00c41000c40c401c10b800c4990407602e0010314014440c040621912106000c0505201c2c240d0f210480b521101c0810301602c00010004500311202401541c44459540c81600705a511038160500b40080c0400c00151850700d400c01d0a6078500c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 650547068 1250 650545818 650545843
    0x301060e010810082802060d0603170a020706050307050c0f0c0307060302120f060310060b03060f04090b04120302040902030408040f05090103080f030403050f0a020a020405060609060f0306030a05 86
    0x220280380105503030001e0300e41e40c08002c0f030702c0c000b10860400c4505a115800880d10641d801030981c06003022110040581d02e403240d00800b0f06640c0c1d0804038800004c1c240a10084d0b411902035a01000d80e01d80c88002c850342d4044035070141c00780c01c1c20501c4c256825040a411001040070034407441c51040801c00608940348a00001040014200010185000c0c05900000c042600501c48481e844602020090300103200c000483e5056070740d500400d10b41403400c0c02010b18282031030703000a26280c00c40011400f5420a448212106510900b88001e541444100a0016034000b0029020401000005403040c0240c600545400e548100390340691f002928103842c40000080c040207580080240c4000408003070310491019850f6403030365603407409010229400d2000000010381054811400c40d58941c4542c80301644400c12050300945e20f40c95900c08a01480c034040104025160180c10350b6218034008040c0c628000c1e18241c070803155080030300313915090b100d507500e0348000540c14002e40c070352403c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 650548318 1250 650547068 650547077
    0x3091106070b091915021e040e060f1f080a022101050405090606150702030109150e070506180402071b17010b0d020f0d020d020a170705100c0b090a08030106 69
    0xc02441560030446600d82001a0011481040000900307903a000c8142030700f00b002c0187c48020f09503864501c0b0f001e47e000094106c000003030102d881d81c01d0944440c02140705607005004e6402c41800e200d03034030311284800c03620712004541c07022440303100718031965110b95440c9015060003455006d24212440c02d2044280d0150007100601540c200ba10810381d1103600c50001700803605001004ca0741440d1044101004402c0c000764501c15500c00b508020001a4060840b680c0288000700c4100103011616509985000d00e41000800d0724043d0180c40726400c03100040c4030030003030840c1000000d41c4203080c1101c0000001002c0c40380c582021400702d004110b0030060300d01000d4085203c0d030840307600760184c2e40301c0c048201d400380160701ca00e8451980c06500382d9000c2c0e400d03c1c0c9400000c00070512200c000b940040c00300700204035903410701d105c4040502200121240d25464208121102001c0b034101c400080e5079941c00004510440c0b1010b822070f103900181d90413000700da1190300c0303207a000342c10510108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 650549568 1250 650548318 650548321
    0x170307060e0601050d0b070c05120306041508030a03090203120307030e10060b030106141626030402090a050403110f0c01090501020309030604030f02032104021c0f0303091106070b 79
    0x88000e001d1440a41c120601070100d542c10301000607071281450501801041210300042c181a005041c642d00240d002011100c00c0e2180c1004004964000c0741d0440c096828058503208410741c410b1101c0a4030030050245040c113240704400c9008040964080e81e0511800401600b126100401940182400c0d0350101312000c014200700d1a01760074140120902d0310384041000140225000d680c159901480c1418503024880f1084145014114039a00414040c0c40c0c40c4003003048452503490800d80384030320300b0a00c841e1410581014002200c7c042d4000407032070001400f2101a5100b26401417190900402040c24200041d2030900004000d4105601c0002c00e4403056804c030b541c86c8000c0409100130352504590101080e1540400f90004041c40140c070341e00c00c0a07034003d20544594003d07a0030f02012807800090001285102a40e007a40158030b01540c40005207800104072916540041819014004955086008140d01c610039118080501002100c65a82900514401303000700c5182405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 650550818 1250 650549568 650549573
    0x71506030b091c1b1406010303080106020c03120d060e01060507021309021c17070b1608071709150108060a05010e10050424030b0702010f020f0f0310170307 69
    0x341003000c0e041d88402e40c0a684081185036584241001c12003c41c5041e19052a242c0c0400081c1003030510000c08240901710300500300800050301da4120380c0295580340b0700380d0f03844000b070b622684101d000e2a015004007500164401041c001041200d20303500d00011b006540d0003800c10b151030207800480004400003a901c05510b02040d0700c080003150400304000e105286e60002d0b55460075071600720125092840900b040c00405080505102c1120b0300381130f5110080d00d880f0301140e84c102d4444600100010742c5c440118494904280f0031031780ea440f818803050348107405012a00000346681114800c0c880c1c003020901d0f500d0319090003051400020300150400031070010540300c1c141c006203050017034078080105403000a00448110341040d01c0c0098010001402544840101c0c0070010040c0281c038000810454049070390b5104001e02d80c000c000c0b50743e00c070100c5030a034841c1003500d03a165081480342403111040c0f08011a0422401400c2c141d1042e1f4030003007089100e044c02e11420b5107420200301b4005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 650552068 1250 650550818 650550833
    0x207031b1d070906020d080604051302040f020c060a200c0c06130501030515010e040e03160b0618010f0605030a09061b0e04020c0a08090613080a0311160e0a0207150603 74
    0x43d044a0000e41b02c90030402000900c1c0c40001444c00c1d109580b1480440c4001c4004000b55000319006003050100b1074801400038065809066920000e2050600003007050301c0902c101404001d1895409511040407400c1c0c1946400244968490340581c0d510329400b030b960304008262105406588402540c903001c00502190030003041d4180c1e0100007400000c1aa90007010203040d030400300c400280c81c2c8040d68a0f039103580512030007951004c041403100c106011072441428860041101c0011b82d481c060220501d5102081c464580c42d048141070500c20f03d400b4001030740d1b0200c1400e00015554480c1c0e1110001c0e250010303603041c50031703244805c2c40c1800d550014200f61001d0060ba01036292480f4041100d9542680501c003401c241004500640da581e90207049803020041405002145502d41c00c03a1522811095802c43c0450784449540107002c0c0c0114880c9054100d503001c2c042018079180d10104441c2c0c00404c0a0000c0750300f0007442000540c4c1c111b25030b035034241000c3c0004440d401d5103030840 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 650553318 1250 650552068 650552087
    0x180106020703030908030903060a02360307061b0f1a040f031b02010903020609010e12060a0b0d111e061c0b03010b03060703020f0d0f02180406060207031b1d07 70
    0x5206c1d0001c0050042e561400108160000c00d0b1034001666803441c640c41c55281d80c0d40034030078100c0c0c100001080e41c0c140d40c580c050302290300044003a91075007079446400341c03904400500d404401000300725150010400fa41d01562803207006624154050100c07080003040800112400c0b510080f1924032030b818154491010384012142c0e80040035440e886030006080d6169034403000b40315107030000d649056030344584c0c48103034241d0010b0b00710542e0a04101085858080480303c0c900d61700d1510300305a0545ca0400701040c10340350414041d0800c4200c007014040d200c0d42c04403032038800b24001c500340e01580d16508014011100703811a02201c1c0000036004005840c448042d0310f03c240c0c14a20203012698020520a400078014200103035038101c41d144203d82c5020302000450b00c1403800741c1d25506402580c0040c200c00ea042c041f4042c4401d11141003004841240c01450010b030f02c01340b010300000f0840e6000301403044035500c0407010717181c4c2c80800a80442000d1641109680e643c1e0034448030a030030a800c0c1c0d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 650554568 1250 650553318 650553329
    0x130f08091c051b0f04020c100e070305010c21020c072d1a030c0c070801150302030c1e0f01030906060312110d2c040e01020310080303040c0b091801060207030309 71
    0x107842c45100d03d4000b40c16512070000451099a000a0401d4026030401034041d401d9480751b0140106140c02111a80b1407e0300c1c84107440650030200181886803080b030055699114510165803001c100020f848002e420018074918a2b01ca450740200345c2d071402d180d2252203461601810035032000b44034109400000c0c8ea9101207005000d0381d0070704155003030880a5940c040d01d000304658403007e0329900185000303102c1d40002c82d00c1d46491842030700c81e44080c0301d91098034002d400301d50016801c0e42c02d1001e4103001c106513410788901385070700c6c188600c1c0020311400a44414034003c40c030003a043e2903510480e505a84102c800c402e0101851641c1d40c0c0100007606210b00d044094a010f9030240c2003e401c8819a0741d21000c54070165085411004040c40c002c00c2149000d4002c00c211210300f10850f00031361064913002c0e9103041d0300200007507120002044922a640c04108850035524000b2201403036000f40d4040c66120a500e20045400d440f80b202d00741c000c0c803280e0700801c006031450a01800d04001034004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 650555818 1250 650554568 650554603
    0x60b0310061e0b032d010305071401050c0d030c03090618140604122010050601020c0a1d040609020310020a03050f1e07180906051305130f08091c05 65
    0xc020303c40345101030320b41c01102c402000c01c0c107100303100124419070403c00f40c1c411041032400c00802440740c000f64903402d41e0403040c540e66959804800558042c01218903070303107442d844040c00303600c030b80d100341c001c941c070600c45040c00b150480760780da074039010707182c2031080341407407100c0f0000c0c6c2020f20451111050141d001e44c0041c05c4141000d1704d405400c0d0000800c0d540a009a4030001040c80c2c60f0060080700c01240074003a14050140705003400050182541c0700f40c010311910012400604e05000d04070b088070010f91490000b0000d201520015010041043e1003003503540c4504e00158a040c48107960a0355188030050341d031282c044e0041d04541000d01745814400d003460420559030700c41841d01030f8655032030320012002d644e401e04c12035030300c50781c194280707608d4104010006083e20290000003d8410803100161900454488903044a40440c2c02d0702c0003031100d00200b404500da43e4070908065001e5030314580380000c9200070400807844a80c249024581c9403c980d01480424008045048642c452 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 650557068 1250 650555818 650555879
    0x190801030309030f0825020f270a110f04080613020906091906151704051c0c06290a050102060601030c030b1c0c06111009060b031006 59
    0x10002c060564600000703040c00d048281107010700031008240c8040c02080345101031003000310407520800100040d82240203409143c03040583e40b814050707100344504003d18241c1240032884902c0c100f800050038981d80369503281c1c20503080d400400300a102e85c0d201c0050850792145000301d81841c00070004c1c403c01007140c0c601000c4005030313940004242c21070300440d0170340465112040403100700d441648485540a141c518000745030000643c0f007d000c05440c0c5c0341c00b46051011000d030002100300300c0d0020300503000114120070610264031365a099000b00d00d001c2440d9078407941c905d400c50b041c260480f80c2400c030311000400b4020449202c4a4915002c0e2500b641a900c3c1200103503031410f0140115051546446181c8ca2542c8030341c0c0040c904510040494039400c540401d50070580201d008140c801c01115000450000e0081048140d4080b440000300340d4095526605e00081408000885801b41c03104142206650704002d141a80850f05a0008146241c04030076544100c90508200551a2010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 650558318 1250 650557068 650557073
    0x3080f0c090103090201051209010506040b011106010e09030d09031206082a1203040905061c030804241416090815060f090106052706091002010f020a020319080103 72
    0x90648481607800e00b400708282010740300583d598010307029860815003850040155642c015001240145c0040c0d804000c1011030000448256001b2111843e0a0b03110318010002d200e0508800d5a0100f0102d040d2400c014600001005948080c40243c1c0001c00c00f842e5560b0300d5000d849800010007207034000340500d800c0c0c0d6040c1c41e0400301e018030035114030400e881c20001580f01d42e03410030206400c480c140d07039071035403200c0c080300c0201001c5d01c005015030b00b04100d07000c042c11107070780642509415803180550f542d40c1e07580354049100d010241c1c044820500300800180f030228002d4100440c02140010303034a15080080060146e0309000d903a04000b10040304001110700850040d80c0940c100102001d035681c0c5d88082004415a000096000301d00c82000040181d882809050030600124442c20707150990315290202060441d40030303500c55010499a980c1d8a09240c400c81c1c812098000400c45c20302c3d01d04c059089800608c29203016810000d49032800440036401d0310340000e00c60400f60700550554 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 650559568 1250 650558318 650558341
    0xb0f10060c120e0a051215220b040302030f040e15061806030405071e0311030105061c05010f0507020c0406151b0609080a030e060f0114041a060408060403080f 70
    0x124042e0007030085031002c0e901e01e91914031640e0050f1401400420035024850702043d9503910f900a140800d41054001c84c8000f6490042405405000c8558040516098441c6103c80c040900110706500c410009842c20901480c060401443d00c0703000d82d1054a04041c070082118000944248200c4081040307142d41c09050800b040481c005441d1140c580d5640c1c0307026490010960090b03911085914521190819410b22036029280b24042d0901000c144c002410700342c95058a00c154410001c2c080c0f0507402d10003c42100c0c903a40180008241110011a90001c895054400d000140c01510100980d0304081c0030301c00c010034580410048807540b8000080800c50035270300101c0e412245e070048905100c1607030015400d80e5003000c84a0303a9400c110002070002c003142c0441c108036000780c0c00090902030703194501504031a0811510380c0c403980036004010003030440d81450080c02600910800e129140e00700a8405899040b0050020342002e040241055800410b10903529048004000800622 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 650560818 1250 650559568 650559593
    0x50714010c020307090c0908010e0601030605071b080c0d020328121514100c080c10060803130e0907030609061e060f0801022a0106030b0f10060c 64
    0x1546104051110000100d69903840060701a600d40b0840d44081010401c640c030801a040090b201e203482c039550380030064203031040c00f00c00382c2c000d4101c0030040001c03601030f030812503114082e45040441d501c010108c00459200040c0709032002907010038006130307104c001c00651124000d140011030802064010300d6450000c5d91a0030803803480001e45d0f0501d042e004090564030407400310030034031a001c0389a07141c44100507544034841e10384d031aa0409007170301e0412003a0449441c04035611021030408a458200d01c0703a00c000c05070034943c801c40c88600784040c034604c5180301600a0402a5596401c0342400d03009040040d000186443d002c0d60901405080001c0c0b040b0071280d2040004c0b0b5204690b04004000345029a298005045200c03090740c8000c0d0036500241c162603d0011480d00740740c5442c0c00c14200d0041025074a040041a07420b1641f1110700f07506910b8490240b4004240c0320388a40c2c076440090b0080d070303019064010002c1030251414130b40c1070410250155150000040110340c40380480c0808 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 650562068 1250 650560818 650560829
    0x6180112050102090310270305190e0d0303141b0d05150a030f1704050618040204030f0804031103061302010f030e062e05030d080a022106010201050a090507 69
    0xd10540c84010854290192083e410005098400c1901d1861404014000c0d030241c11210000c000c501c8003480c5000c400d03c03a801a05540c4690814005007e02d4075155001080d0009100c0080d036044141c0d40d4126480d00f0b0075220741da004c40c1250740712000c0300d0544d601402d50740700c911002c070407902d44500200549036904410036000c512034030b03aa0f10a00e1445440c0314502c1c0c012440c0003001c400e12501466601400d8031070120000f40c90070180900b40b00b4003490040c207034858420080000c0c541c030184582c0419120040c4014600340e5170707582d10703115184803e4007102c00c210702150420034449001d6510407901c400f50701405440c5820b01c00151500c004020082c18400c284e10800c42d00d41c4242c2c0003040c03011046007103035440c1c00c01d1440e404d00301050040d12000c210041c04d61017200a11051030400711340014000708801c100c075003070546c3c054100420003103a03942c5c09e01060200644540c901028074000e00009101030908030300081c2503440003800042110304154044001841c00950b8038211075 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 650563318 1250 650562068 650562089
    0x2090d030f09050409120818070501120e1b1002030408071a160b060f0312040e1f1203110c0a09021309020c100e060f0708060f040c17061801 62
    0x80a02020b0300e00034101d0b00308a03041381ca081c01101c100011101c40108809242c2c58100c4269246803600484d0001100310701d0031038101140401039075006600002c0082248500454650710a07034900b807400000380c2102484a1034480008064180000da1940d2180c8510141d0b10341801d05024580c1c404140c0310714418040e0307594604210301c01eaa001d0740c2c0c0980300704552031712441890a080e102ca4000383c44c041e01c503401c540c0038400c192600207006003000444200f031a08041c900400b201403140000d240d200070350020302110400108a0f07400300c001d0404401e190200709002d040c01024580341c0e0012500c99481403022510698445040004803000381c90056510b0041c0440c480e41807000d030b44003100490000c00d0003680100003180410010318061420170028400c0e45890303a0b211402d558055040c103102010a14040c031030b03100c850b803045010f04480c000966841c085000c54008801500010b070144a004a15149641c106900503800b01e07112400b0003610b16160840e200c0c180319904090 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 650564568 1250 650563318 650563337
    0x60c05061612090c2c010e10030c08030c070b04080616180b0903010e1f02070c0b0f070b01092003060a0905100306050915062110020d05060402090d03 66
    0xa42c821100d041001104103401c0c00030440ca8503200012200034000d1003000d1010078580002415801183d02840c000000f010403240d00c0c010841750344e2a000350045020004e10000840400d8126000000600c15032004550360b030105c00b501401c1c041c4603081101c0700340040108201c0351000162032600100310850070190514444020703034641515008240c0c940d000140c0006240d1010070150104c50b03070540c001d1048401e92450316445d000c500c09120003a000040d84820b801c00315a001c1d0580c207105d00a40720990792204103000641d0410030061120401c00a075040411221074203203401445005410710480c0c0031060744507542c552036040d1004103840840014001e075105045075004080c5d0582c208007604201c000a14404245e000c10344445080801066400c80000744001003060780d005824984d4484074104001c200f6103a44000d482c0c1d0613408540940d2105102003020140c0c42840140e50383c0c1401450340c20703100d0041c58980300e1403050000140310b84a04000410555041c0f0b0008081c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 650565818 1250 650564568 650564611
    0x31109090a1e0203120306060f030a02090a5a1205030901111f020903100c020102031b040b1219020c0a020a0e10050f01210510060c0506 60
    0xa015540714090600428600c03100741c03640b40e4207900c1c1c5034a4000e82c00c2d92540d42c43c21318003d09a1000f030303c030260880d01c2007101100d00200100590b801c2607c1c85005450f00003d2400a030580c04d06420007071481051001110309240141c24084036000b001d020308000c600084445503e070506002500201c1c07010101c0100148040041040502504503401c4448001e074244a5a41d805c03c01c240d03808510700208070f5900c048005150580f40e01134042001d0307054145110702010790401c107021901803082d9009038035401040c0c0902c1e801c140003940016201d113440c0b011210a0301d520311049070440410441031025400da401181d211a503080e140510980750300b03010726001c44040958654180c400700f11009460300120301c4100381343c021039000c9505911208501d01241041e61061500e042d101300410150820039040540d0711014181282c48031040f401d8040c800039801422403280d6a64020080100c540c0c0d0303210800b40401c0c3c0f4050f84445955500c03103031b0303940010f88004211441c68400d4240c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 650567068 1250 650565818 650565823
    0x5060a0311030c03070b040306060e09070303030b04020715090210051c0c020f2401171c0504051810090e0d030e0c060f030708010501050a0c0209061203030c0d1503110909 75
    0x100300010741110b101710b0342c410701400d1641060000321200303400e1600c00501080551040d40c01001c45001800901d86107035030030707001002c00000c01c6801540038082c1002040d038090500301c0003000c0c00000b0503503458910400c03141508070015241803040074404110322561084080107544000d10700000d540785448016490301d603010080d08100d01c00c004108108000580e425402c80001e40951145a600c41030064401d81e003030b820f21052366024080c0700610009040c1403e49000080c18140d140c507480301e02160558601c112040e030110800c200380000f0240c4c0c80c6241c030050290740000c01440d0360181c4c00949030001c90164000b015141d1412070081481406160300c18039000313161a69403c880081180380e50030494100c000308495500000d240e50240c0300700d134248016075071521104045507007042803948003d44503030342044803003031070380c500c03035400c0005500030807141e40010b403200d1004035a4416599007070600c0c0e5402c410400108005054580b12460b0450100c03040240b55564043c041e1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 650568318 1250 650567068 650567083
    0x50c03040e190f110307050703030e030310060912080343020118021f1b080301050a0f030206030105010c03020c04050708091006151b0f0501050f090105060a031103 72
    0x11031200c441800d000030002d02c99010030302001c52075010f000000d014900d90080340c00c0b580701c003010104108006482c0d14400e00040020300d1103400c00181c3c1c50391002e40d00345076400440710035a50070001403041c440d4941107107044004003002c0f500da648419803507032005407900010b007205a400050807a400b020b07a2200011840c081b58000e4a0800300c134080c82060300c49a00c0003501c0000d5440c0c8086000c42c001940440800650007410050140c211005803050600441d46104108082c580b802001c559454070320038030351802160502d80301d5060404000814025a001c84d24041d000700c400c000580303e07601940c4c119202401d020390948001c0c24203030304040841120136401840c02082003c1e040e00860710302e0003559520b04503900c4909400c442c4085804501501a03403d21608408190501c40c045a1034101e5145803070380507083ca103a40d40b6911803100401140c0c0741e5190390401c02c1c524001100c0039880805800240708504060020031500301084c04058540010680a04542d88003084600c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 650569568 1250 650568318 650568329
    0x60d020d05030c0d0504090507050315060306041409030c010b0a060f050310170d0305160c0b040804080a051f020918060613090e06060402070506160903080f0702131803050c0304 78
    0x588211004c03580c01400355005000d0111030303a18141c0071440c090301c50030540744143d283c0391940e902800c40004020643d0001000941c0c019100c43c0079040408049500300d01175100350703005503202c0503102060303401c0d5140c080c281e50003100554410052150310100d6512421024100b1a03541d41b40c048100b8039165480c0c0192141c80c4542c000c802c1c80082c001151150000181d9081045880da5801700d41d98041c100e4070000011a0004410040380000003a10380040c41a44a9880c05558080860070808a0320301a1841d40000f09440852810750a14120204034007004610389644240041c00d055280c42003140303101c640fa0300294403621400300f107480500c00520104135080c0d40390a46806071801030015001c500910000c2a03883c01c160003510ac029610a000d804136541e1404411050030400704408204103e8000000203e00e41f000100100e07105036007030700d95072142801840b01d21a651604016180c3c58410544440b5a1419144000c2d40c1c0c03500c0c0460781d541904c521390b85180240d8204 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 650570818 1250 650569568 650569573
    0x50a061e020a03080711160b07030f091a0f0903190c050105070c031101030b06181309020d020d03051204060608060702160b090d0b072a03050d0f0207050105010e060414060d020d05030c 81
    0x400c03e0003007080548500e41c82941d501c1c00499000cbe41c2120040c03410712488070420f00b008824419004258041c00301c07000c9890085041851500010389880c88288640d04111b03283d0034000b0038443c8044660700a09001e003042e81c503008a40d903690044942c00d20020306681654821198544c0c825042a0100b0100070155500c91030f400d201610905402c0520030f1050005070454064410180641000941c0080201858230320940900c5100c0035900400c07020007404205102407808464006c50140b40503100004400381808501c0e4603115001c2e101c14150752082c0c0d500c90048100005180035a000d134159a80c49404543c00f240038160032102c003c02c40c42a55041042c900d90140c4036002c0140c503028416030649945400e4850088482405400102c00700402d03402e06286802c54a40d81d554006d00600d042516100e19084a00a801000002141600b84661441e00d0301401c0700454034011001c1d16400c1c440c000803400846864020700034281c02c0311100c01d101081c03081c0c50104a07020203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 650572068 1250 650570818 650570863
    0x1324030b01021507033c0c051b10180b15010c0c031103062d061201050901140a06050a03020f01050f0c0d170f0f10050a061e020a03080711 61
    0x4c020740580014800d441e51030300200029003000690300c2c5500d01480c1c0311481d81004009882540010b8140000b140e03040c0076040000100c60406042c5103245400d0100c060000c000c540e0b030252055440d03130204058a04260010705020800007e03049801c010b101d0f04003202e150420006a60805000c040941501c80c06c074000400d000b00391804000b8890f04a0a880d000e0392030140394203044008001010505104e80d0101580048007000c00b40c100b2401000d0014841c58203150306e094030012601040d099440d201000f00f882e40c00c260454002035001e10a000c15400c0070701003000d00b581c520019124618002d08003016900503412190f400341035914640d65610200c05103030f55115962015000a1684650f150140311800102d41c0030790500d84010384251112a041910303007001034141140079000d410000345030380d1205108001410f054660700162203424189c84a0190803446000030340d00b2901c0510002640442c40a901041600f8454000500c041109240c0241c4140e400101089200c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 650573318 1250 650572068 650572081
    0x9010e0405041515090606020708030a05030a062103090e1e04020d0812070e06030c030c090f0303130501080105030706090b030408041203080a05180d050c211324030b010215 76
    0x541d0000e441805405020081e542c7d0f20403613454840d482a100550130034800c4070b901c548664001c5820012106d4003007100c03522500b48110010780704000000d9100c003145035034201034100e440c0c0b1008114843d910392a514080500d41482c2c0a103200b01500f800008002604540c4c44a000701c007015000441a03803210400d80450082d030000b40c400300b001c01c035041000140381c909242142e1040488802e001d00b551500d20b04401260058a4601e81c0511100c204a070f454900b04081c02800304907074011021189840c002400c0c0340c2040e001303c1d009800c848020322281e0b8000075294100c603a039103200b66481c1e8640c24440042e004076000108400a82018001499800300e01300d4000d040000040196480d0310032500e04c0c01101c107909504541082050010781c03802440a480c0520400b000e580c08000e504050351580000c00c07145e0980050086030070416081a01070301409010080c0e2420302c0c1f000c002d2240d4803001c50800c9080c00b05500c400d01f55199903c2032000d84074014140001d0041c40c10b020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 650574568 1250 650573318 650573351
    0xd0e0312011508180a02040507020a022d01090806060d0305070602030a0504060c0518090a020d0f0207060b03060411060f0d020c1b010e0d0f030912030f080c09010e04050415 76
    0x10b00391140007807a52408502c10f40c150011003c1280360b024010310b4000b0544e42880058003008101a06600500a460001d0b840f150004890f050038050386240c8690300310b1603403003603400e5036074528104010020140400c1342d0001c3c0b02900410100d4550b003800c04140b4044880d8421050020002400802404243c0c0d0075508602d0051384140000e0044a8035400200c0e003e02a031041c170b440544441c0c99041c82414080e0300903402c03c2942030094070744071031504010103855400c843e1081c8180e000950400f8040740303118014491108501a10705400e0a0b210b0172035281541040c40d01c00e210003e54012903c0c440001c6a9003c0d490b90000d42d100c544103101d50340c0304c0a007600000f0f0201d50300e50f117602d41507205204c141c4840034020306100e00b038401911604030380169544103c05001030b0190100340001406060791302c151103075843c1c030820740ca102c500a180440140908141550a222050f41680c000e007805070a04401e550018103960b581c14003400c1403c1151100108a18020411011103050f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 650575818 1250 650574568 650574599
    0xd02090102011a03030703230c061f0b0d0c0201090204060315051f030305030a060806011e06030b0f010e03070f060c0506060909062e06030f140702030d0e031201 71
    0x240c0081041e030308400f40c0380004002d8244100e81c107400800140000030b01034452819032401900c070300c1d02d40007a000198407440e480071005c440550700c000d003000029000d8024500202c1c8920b159a0440391502d4100d0095004100c213901406032500401c00200b4402d510110005030002c5c02032010503524100f04d040c00d21f80c8408400350380d04084c00a0398519005060340c03407440480442c0c050b018516241205e040e00084c0094548586900b0001000903040040a001c0d216034694550135645c3c080100488400d240d1084051604101400f00c0c00d5895101455600d14203003800034a0555480000342000e400d44c03c020b01d29640d0000100d5440d9100050108a40c0300e481191480e880701b001300500708008407610800b640c40240010813460030b2000c0c401607111100d42806580720010a07224510900d90022400655281041c20038501d0380d00903451800c094200c0c10447c0e042900000b03440b4410603101921072a15490400c454178070420840c1c1c90070002107241500ca58480008110440c007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 650577068 1250 650575818 650575837
    0xf17040309050f0409020a0501050d0609110418092102010f0608011a03060103050607110f1002030402040627110c120901080906102c0403110633060f0d02 68
    0x44492603c509401c02d403155001c029002405c1c1404030f842c1030011a00c9612070001c20905a84540740041c180c180c60048003041c0555001d0181c60302c0c03c017041a08520140d001c036900b136905107205007010424003080481403060400101600402105050703000d0181030040d03203103c070b00c2c1c290001902e14065010000004c2190170f039280d08528642015034424081c0030181054101c100482c00c80c40c021002c005000c00c41d282034829200c142c0e501e090800320308190400d1075940000800c002c6140c50300c110b00250114100012040914803100390100c006605c4440003e41e40c0c108420f103500b2a2400d41e5504d11f1000c1c01c40e21310003000c04c803050460b041900d003035000c9507000010540101010a2840c41b80040e0500750315118544038885c4201005000d00e60306851034843c00010066250b4031a078803a50090321111718900c44c0c2e1222500e4103500a22084440514950302d0700c069a0050514907800c8140260182e281c0006e00042c44030301c580307811300080310000105503800043c0c0f90040c1030041d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 650578318 1250 650577068 650577079
    0x9090f01291c0c11010e0c0904061401060512010b0309030304020f0f0a03080417010b0102030f30180309100c02040608030a02150c0f070212010914010b030106091401060f1704030905 80
    0x130038080c40a007030703801c8018141c00941200300c4000440c108228100c0c2d000f8062280441e89260751451602e03402020382002000032030008030300e036840401c0c4c0c00e2a40100340c0800e180c1d14514200c03c2458690101420080c803e1920340c0c01c03e4020350b50441203404a00006201003c0699246010749465103d44074212910104114503a0101d10600c038030410508103030051890942c80d1007480c06c059000005a510107002c6201184204010316484060399240340b01178551030906003420003000071465404c0120b5442003203160b005454061072800d031002c05051200700e042ea1032000a01829a50300410614440030605c0c00c1040d80c0000c0ca041369004e0500b00c01c846443d40301e6507003410700c11100100c80c070078801c206150041c14014041c2c2e0006441c48000070f8005810784c1d480918000c10821500603a440318020116890203109040007811104410061400c0e030030b08102683d0342c1403140e0401d0045100c0c441104502031600f0560500401c0c100d24164036151030080c00c8541036003d25030159 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 650579568 1250 650578318 650578337
    0x90c0111010b0901050607081309020703180303050f130e0c030420010507020108040819051903060302090a0504050a0605100614070221120f09090f01291c0c 69
    0x42006100c0e4414010b00030b00705070f0b01070382882e00380180703a4000c800441e042081040080c00c503a00581c40580900540d030405a03131b5a441d0b0900424030380030307881c440e20190501641000040d40050480c3d2111000310321254488800d24080c00c032121950340311481d00e058400802101c900745800031031107940b05030b22045044c0c00310020b031490b50f0120542c1f10b001c0b4200708102c0000d903001d8035010fa0b00902c50140540f6104916020005464581c6c02c1200803920100d0341c4030003241224111204103000e0320301040543d20b145c000641790720000c0d220142c1a82e540021500f4010144119905690007003c10b0019003480c2c41c401040c5c41c2130388220070014051040e40030241c1406422100c569070001c100012001d11581e40a44c0010309117101c1400303100701d82281e8001d20084002d01600f081481035641c54020f0402840840b0000404071882509280014007610440c0e507484004a1920a0005111030a002428442c1c1c0300d0f00500103500a5090440101c0ea1201c0d0460002c51046070ba84148a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 650580818 1250 650579568 650579597
    0x6011214030c0604170403020d050d27051215010b0304060c090303020d030b21060a0b030609070306020d140f04060b0f0d0f0c090e100606050a050d090c050306090c01 73
    0x5070b0148408144072604044003007004604492070100c03000d60f000e000d485c80c4c1684c07613002690060004a0850740f50f0441803402680715000f210240b054030400c28650f00001d030305c022a2001c444030f800b48602c5010320100f442e120800401010b205480c416a803420a945c42d11060101500700b00c40444069040c0200c090200b0701c96404001101c0d07054004100c104191034060b0081c0411150030380d04107010403007a210b100604481114801030b9000505003600341110520243c2e03150381c20b10317400b0317a101100740140740c800040c0d01d8085941010340180c03a000c1e05080e1801800b0308400c00c10028000c2c0085c040e00c21100d412040c00b480c46103c0401c0b0005c00003051182126401710980c0d48400586490404074200410201d002c5100d500d13154902038903040b88a0440e024000d417503840e40d00610540d100101140704e43d101615090a000d03052001c4500014840c2c8151640685810345443c0c03041d04000041d8000409801d008064130303540d25140441c1aa03500320b00c009180090040c2030a90795 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 650582068 1250 650580818 650580823
    0xe1c1220031201030f060f02030a0b18090c01050c0c0603151f1d040e0a0c1d09030d0f091a1f05030a06090f0803040501050708060414061504030506011214 68
    0x1402c0d80d2a005805a0b0780396032600d60000607081380640c0d0b01501d0f9004030000810501c004c6d40b01d05040c11002a40c60b0048050020020203005400b20807038180303080c00014040001e00009040003480e0041c0c0d100250b0b1500d0341000020380440e03800030008001c1c80441c5030201200f802101c1e00b5a01c110341802c00100711407038110170311450400310300d402030444d0021203085210007103130001400c003140c550741d01402507160100c5a81c00b654400c004032400d116110441b00090426040200041028205203100586901ca21669204070aa41e00300d00c4404088a8000f6051303d60400381a200c545401c800c611250101180c45820b1544201c0303c480c14907000301000019290050000e00c4440600c0e6103a0000b0500c80e02c0c2590314555001d00100004c1641000b54402c070320410001c02d00d41003110010b0200d01024210710f20590038280e1210448200102055000700100c034803098004807110b00303904030300ca40e8202078064005c17400003203028509800c0e230101d601c0c410348030f80c2da01104129002d074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 650583318 1250 650582068 650582077
    0x908070f080d0e01051302060a0e03150105090705040317210403020109050c0a0b040911250201081e060118120b060306060f060a0302030415020c0c01110105070e1c122003 75
    0x11b9040d42901ca042c005400d0180140400400e04d01344407940b1704114000070b1401c030400f501107649030101b400501040c140703044101d400165609190b0704190855841d22800e0b64186a001c540b10000f051112100d06d8908c2e030b40341d1100000710512010300306424000e02910301100306441601c11a149800305003800100704044a510124041c02c20303003400320580143c104004100d002443c00c0c010164540070031001002d030800d0f4a4020092246940300141c404c0384001e041c1025400d280043c3c480781c01200c2d440503030100c024a000021820290080300b01c048998000b4410034900d203800e0810803400aa0307481c000d07030040701206c610759103000070441102441c0c915503802503001d120b4850803a00036001746820900c02d83c1c1c0c0884103024040d40004980003180c0101156008030030040c070300e5800c0b90322086500b40d0390000380024509200d02500221034402454000d00f0120314481c65072074010401003085500400031008121240300061014458201c08030724210a00c1d544802402c0c00401ca4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 650584568 1250 650583318 650583331
    0xc0201050603060603160b1308030301060512151f170702010f0506030a0c0b0f1c09060c110705150c060a0e190c0b07060207020a03060c03060801060b030a0908070f080d0e0105 77
    0x582201c2e0600041c00b5550b002030007488c40c1d14280200104071070f1400d1000c1c502a0241d55122511210201d403005e00740380010f00010385031801100e030b0550301c0e100c1030000001142c0001c20001d205240400445118907007181e8011408520820f02041c103506401c003000c0c1c644503480a11203a250a000c2540b20207048400400034080d0030801c11651000c4405024500804810141009a41400c0d480700c01c501101d45440b4581da070304000b08112851007110440c0c1c6051030550240b480b01924240e0b1040300d030181e00d10480100f0b0602030342004840490700d4400400003034503001d080500724500038100303d45001c40749004ea0410051a0808a0100780300c150300000341c00d12240c03605141046540c071848095039116001c1045ca03001d6220b0160810003540304030400144c000000034000d04994403030b040211140d0500c0c10420040c140b0728152038000c44050350004e56815a46001d031014407031650700400f52a1440a00002c0c00f040d81d014050350518004180012850308506500322882141c11 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 650585818 1250 650584568 650584603
    0x16050c100b10091d060d0b0106030507120203070e040b1903210c1509170c070602010c03060b09062b0c180e04110a09021c0e0d02031206130c0201050603060603 70
    0x410560b00c1c021400c0c1d8105d040a0705141d0f90b418a0f8541c4000c50304244c00240c00300b0b4540d000d00c2a8558081c80f00401e82580780f000b181142400c3d90300614121081842c03521894598001c0c618565840b065034481d00d0710704d0007414036140e40740380003040049081e10303268207040c00400c40c40d402805894280c40301540455003c00d44441c110001c4020524034106503041a1040d41e4204941d04010040030b24104110081440500c0c0c00f000a0070340b0100e8400501301030a20a040144011032410340c0d1910b541101c41070f4070313501c1405400088110740c00c00801c000c09075003168040d4041070341c040810010513685004840c19000103104039034100c1d00c81c0d00c22035088a4001804580c00302d1200d2108103005002615080d40d4030b800c001aa08012001030400c0900c0441c199100920301c138081c0c40c0000d80019140d41c0261400103522030107030201c0798403400c542800003105590380c4180364040142701d40c010801c200c071152009000b00011109680a40b15040104240d4030b0001a40241001000d28 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 650587068 1250 650585818 650585849
    0x3020109121502071110020d2a0501150e0f060901050603040f23061b0a08070c060c0305071803080319060509070c05060a110316050c100b1009 63
    0x428400d480580d0000d0302c420740a071075000c5550080703000405540b4020010404c4500c655401c104503190038a6204003035601aa90000540e60000c0141c19640140800c000b00c14221002054280da940f00780140294600316040c40e40b8614208508151000403564000541c0c2c0c074400c02040708026203615600009002c01003285181400046038001c0c450000070045802540d101c810014a02e120703811404458a80c8030324000c2c3c10081c103907004400c0104c1b40c0c1c0c00c0c1566564240c40c0d2064001c0001000240000100c0c03a900644483c01d8559005404211a5801d281c00400411065641c14002207447c082c01c0b02040c0e1001094098940001c1041d103075031543c4680703015a00d520b00b80d00403004c0d00d0700c03400502e035943c407207842c0c2c40740503941c075021241080f80c40c04505144004090484031882c0c66004054140c0d070341c064952180700c4001442c0c20008a2a040c0c481d4042c00e4106810b03441510700c0722109685603045031480081c00e803510080c00d42c90180503504120035010b44014090140e2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 650588318 1250 650587068 650587079
    0xb030f070503070c11131b030b0301050402060d0905070f0b0d0c020c0307090203180a0b2502070302090a0207230d020a021302090f030a050a0b070c031b080c0f0f0609010603020109 79
    0x484d08100000002d141440684c0a040494147c0d120010010504414000e48001c8190503010f144a1020700b00c00030051840c0680c0081e42d40d001d49480e5000c400e40e00d42c4481c04000b4204440e40280c256500b2810419543d904030940303da009090b01443d103030802c1c0c40203000d01c1c00019040349982004001e000752508091003c1c000303400080c190501e044040ca100c260700c3c0410302125100038060000180709244c820312146003050810880c2007000f00d11003100280c00d0707022550005072941214607011079140c2042900c0a4020600050201c0c140c030b2800e00702d070301c03081850607100d09000d100f660021001000160384503200d4181c080e400c0300b417100704074484000342da005000029004010010226080005c070f40307401c2c00010125102e034000a880405e03c40349409055101c0003a02e081c0120703010303594004044140022504141c250b01401c13200801070035409403074444030346408880312040b11050702980c9604146140c006402a44007050038003406000b003100b42c0e50180c48125801c1c0c03410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 650589568 1250 650588318 650588333
    0x30c193c0503010b0f1806040204120803100f030b0408090d0209070c12030c020304050f0409120804060623010309050f06071709060c0316050d0207080319060e1302011403010b030f070503070c 84
    0x7c0c103860b809607081101040100b03a5009140300540a0000d09860345845916101d004d09983c010708a5025405010000600702c0309140d68020390000485450b40124070201d408503240301c41c0294040e50782c20401054580c000510000d96000d85070b0300d00352040403041502290030b0001c3c104016002000140b00d141403240030b880d04103201070700c002001b100d162142888403038100c01c83d00000315614144014000070740a500081d01c101c072110031040159000d01d000041c040745126040c561141074000911030306003c1c00201400d142d06440c220b1904460003070500c02849070501d81d000a1802003141001d000482510801c8003960040c5180c4030411074101d0f411810f00d14000304007040000180200d003a00250000e02e200c1c407119500c3e410044802003010584000c1d0220b031381c1c50020200300704c40c64030119503045003840281e103400d52914001202c84450120280c0002c840c0000001844001c8000a500c00d2480b41d00325107060302c0740c14007160b440c4401d0f5401c1c400160408520030105101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 650590818 1250 650589568 650589571
    0xc180d021c050f06280c0c020d060b181605161e17040617070c11030705040e0f070807060c03050f04090504050c030c193c0503010b0f18 60
    0xd40d007190710110800d16200c0c5007602c2200c2510b182d060100300c050310384044602c02c5071403032918102031003501d400e0302c1b0040414401d540d02070300c10308183e200700c001c2c041c07944c0c0a0002c007400580001050148443ca00c104c4090036a02e50903c03011030fa0440440303901c035100ba11354002d1080342e00407403242c5640340d02c0800c4a44038510050350184070a600d001502c0d1754209002d0721520f40f241a00c81c1e1401c4006418610442182c1d00c840900c00200100caa60081d080c04e0b210ba40400c030700c1e94010848000c6440c000007900a140c21918081c1203181a02000a8a54000038100d0458a030680c40c1e1108549913956881000d0214031800d03d504000f80c060780160074070100d20080ca03420555150340c818243ea0040c3ca058840e6007020b1140421810180f20b1b035451010240d030202c41c1c42c03404078141d80c5624514030581c810540d0040f4504403100c241c3c100da051906605401c0001c0302c4803150b42c003105030390314450700c0d00c01c1d841c100c0c080072241040030810980500c0202b80050345008140ca001503000c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 650592068 1250 650590818 650590823
    0x102030906040617060405040b061003110a05071b030f060b0f04050c0c060705090a0b0706060e0f150915040c1e050a02120f041217030c180d021c 64
    0x502009145854500c0034000610540d0790368130b021108207015480a00014007030501990600c03040001180c500e00195800030015265003514806000d0201d00602d01c075110903244500c006a20b0501652000c0901080f9008202070807000d00283c61601d101d4800d8800180395a8450960a012854603171140007180d002410507140f803410b410004003110811102c15440305801304501c0180e000c2000b42c99804a0142800c1c4d00d410030040c0058030102031803280200149001174400b040040701d400c2000202802640b076411030400000420741d08200f04c1c0d4030100b02c2d40314552805a8501542c0d658000c040c1101054410546171007408041c0148811075070520044400c1d410503101c0300303181e8280c0581265265920707508c1c0030310700904103a180b00c144d156014003480f464144415440884085580b15480b0041202c0e07036240044080014015010383c0007004401c100c0d804040b000241005602202d03500b00c822013207020083c1c0b844002a002c0d4100b01c9007902c45038030f6034244007641006070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 650593318 1250 650592068 650592073
    0x601051302070203030d050a0f0501050a0510090e0703020301060f0c03090302280e06010e0a0f0b031012031d06130504020c0304083003040f0b0711030d05040b010902040e04020d020102 81
    0x5a82d070f00802d01d55481024400c0c18680e94008000d0240384c1c51203144040c0f810681d0900055151070300007100e07074000c0e0040501c15502e41d02e1810036039020702e070540020450301038103014501d0004e03000b8000350000d102c0c0e01d002c280b03041070490034940315034102e001c090380c5034842181e550b065400707000480355019000d848030025954020068014031070340000a10300e5041301c4066203020000102804004c90701036020720310b184818010030707002c0300e5000c099850710f010031a100d0b92000020040d4195a42c130800b00d030a021803007181856031000d005071070003009000802141c181c0209109081c496241d404020b01007000d410721403032030203800400070b80d448034080303d0415444410003424400c0807550202609484003511050592020010a285180c004c25600710302c0c003500e400755030814901e001411100524000341189000c0e10803004050020800c0b01d0310b42c0001c0348010002c003c01c0d1000c0d90088070740000003410040600841c1c050360700c900c106480701d4803240d083c0900890165012412b50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 650594568 1250 650593318 650593327
    0x504060e0f010507180e0a0203040203240603070e070c0222020f031512061302030a1a090f061308090301090206070c1403121206010c0c0b1305120601051302 69
    0x145001c014030107141460390000240b80c2815980685184000301d07482c3d40b0410f0b43c0c4010401e04151421050f030141b10700c94050f940750b546200203810413510050030b003002c0101611080440f0381140b40c1c9845820f0a40848856039158038840490b2101201c540340064002400440141440c0c40b420701c01150780d203400e10548410600701002d80e0881c0ea1074003c030302c45c04810403001c0c00b07068100000f105026070360201003419006420383c4982004080c102d440c581002c1f0b440840d242001780c1d00049400200c05005070a0120324143d0707495094a034550305e40704211001142041c04a002402030210404010100c2c00d40c0d40e079007845030016110a80e1556860118001507194400108030172481004040784141c00c1180003a030301401600030714000c0d8042504181d03102d29038001c40d217200490f48015003669443c0c0c00100c43c0008044c0d40200035441c0c0b0300c0009042081d03900584410180c10224654160b01d810a01042800c0b1050800c860340c0036000420650403e04160400307044101c0016103003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 650595818 1250 650594568 650594591
    0x90803030114011704021c0f0203011805011a061603110d030e0f01090b0c0306040f091101230f2a0a110402070209060f01030f330f0603050406 63
    0x660300260700c00780e050311415401c01c0666902c098502d0021003245500758880c14643c0228100a051020303801e00c0c481c0b0840c001c0c0a10581a100c040401e0b4010002d202e01d0101e418041451580f4041c00c55144d0700b0301d614001c00380842c02a00c101620302900040c246400400000700b5000da083e0141d003801106081001116424042d01c5200c0050307460100311090803540340362418030007501c09030a50749048101c2c0c000525100c400c581040300021200c0d204e80b07a0000080050124604000c4801e2030b01e40c2200820513441c0100818040c00d0302c8425550030102d016808041524070131880080b001c1002c42d8018840c02d024240c041c1030400410361411b0080e907000106014601c901c0740f142e0040d4500820414410300c1c080340400103a4096060148940c049281000c000d404944103e900d0300040400b80d10a900c1030012054503071080c8136003501e41b104010f5042a245e00a84030b984001040140d420119410000302c036500d41544400c149070440440042c20064400c41c8d02c2520f803000c403182d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 650597068 1250 650595818 650595823
    0x31c0306090e0307230a060f14130210050a0813060b1503010905070c03020c22020f0c0601050d03021504020a050a080d030e120a03021e030103030207030501050c091c030908 76
    0x16020202006540c4c954031810302c0024031410203114444c481522901029815010500d03550b404e5000c1400b080790b00c076210254024100100c0c0c2d9001d902010307410030080b01c640f4508103142a0003a920403501900a49040313800b0702c1068003100104400c01c02245080365440c01e01e6070700d14080c43c030025480b41210300041840d001c503507006440100110042c00f10003910301c0350a8101c61507003000200c040403903401a44813510311255a00c80c005804150740e1614402010f1440000d00304402c554800962a20752250382040d803410300389120b6000045440d0800360210240d0030b4258004042c000354859840e004000000c0c000c03600003101e0000000e0503220110f480d006400070308043c001001c0004002022951420a807615680c000751000b510b000300081100c440207458640036a43d814031020035410a812041100072440c4004000001d01d0b90114000301940e2040e03000348a5a04d440b03050034000c0c06101d0200d40d111041d0300440450300b844034000742c0d0043c402d040c12031980d40e45000203030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 650598318 1250 650597068 650597081
    0x3020a06050307021513060203070e1002070306050619051002120333012c0a0807050312040e0609090f07060f110604120e0303040306020c0c040f0b031c030609 70
    0x300419404428072021540601c0004c0c12442d58490b004070514218081100341038091601070040e917400404115854440c018503500000c0190498148140d40c91009503075442d1440141e8410b443d00300860307800d14040490211f103044080003001c10504000403c4801c0001400040541c4107000281501215040c0550711841040410543d4404007422502541000d0f8100264001d58014a2000c5a800500c404a11443d0171124500000180303001d030b11003401001c400380d100c10107140001d41104001450010b03a5002d03025103140911a101300c03181ca005034001c06c0507480100000895504024903116403001d40b00781200c46018803240c1060801c4140c0d04241d00042c0c154906d5401250000390710f0824100701c0000781254507258446070400c0d000902c50300d082204580300c030304103940e041003590701554101c10215500d20030480038941d1144044d600d68003071810490704603000d11291092010081000c0e000d01002c51605c0207914400c030402e4250414103682d40e0012541d00320074425031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 650599568 1250 650598318 650598329
    0x70221193005060f010807030506180f07090e1006050703030b1201090507060f0c170903120a121e0b122a0a0627030803251e1803020a 59
    0x80503441a0950700c03030960b02c000385201c1c06898181c10844540e680960071907030003078a92070002059110640042d40000c041d0b529050342692200601c0004140f940030349005012549603213888541e0b40b008200d410300c04803549402c0c151408020081a8010401050614403c1c9400a0303012903040c0041d9080e214a00619401d07075603042c0140410004000c540c000c1c1c03003281080c003a20003030810014a001000c47e002490350600c003161a03c0c3c050340c02d054841840004040ea1040200102c808259070013082c03179100001d42e031200300900c8282070722642441c4040403047c1142511260019406400c208503c6030300001d01c1345440c58444001c0c000d01e441d0200702038240095a100d0a42402d40c0030741443c0e000d1040003000803c010460300087c100300c4503605440120800155444000c0c4d030665203030310140000340c1c00002c0240d0482411040b214010002803100400044900f080f00c0351a07586400100c04c41c05802e418101501a1084078010306000f014030b83c940e03850364042643c18900340d000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 650600818 1250 650599568 650599637
    0x60a050a11031905090c06091201020f19022b0e0307031e0b0612340303091e080d050702240703140304032f010903020607022119 57
    0x5000d404031030350060f039420000c0c5d04004c10f02d166084000558521941010700e00c14550502e02c03848004082d0140c48a80709990150340c0c0b81c8003c01c004100018254807200018021405003d41c01140100d0b40123001031194210725403074641036000c0c2d40ea03010440505500d8840c01d03070000001245a82c903286d07012134400302c40190391128540300e403810300c02422141c8a1000340418400002000440c0d15502e0450880c064140200196030906100d11540207100c0d900c1c038030008418140c008a40f14102c40440944180030388407521440315651903806001a60740001e214010320758030034409812181c0c0010007105103000c980c4e110454601450030751030300407003020840205043e0000d03050b425400710151a14550301c0e01d41c1d00200944d0206100110b000c0401d1040d4850820804021014100000007080840c6190402035500c4900302c2c1d07000f00501c56211072003102c0c2102d002258240010048050400003400481c41600d40800a04003c02c2640340c8100384000d44001310b41d6031810749a11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 650602068 1250 650600818 650600851
    0x7020a080d083d1d04050a080a0c15140114030d20100e1e100504060e010c0c0b090a0c05060a021612060c08010b22152a0302060a050a1103 61
    0x484c03001030b0b045960711003c55800810022590124220200c04d84c4440002e07540c00300c0d00d409071404a4513180c041c16201540110200e0b08481d64030116100c100d140c0a50200daa86241c2d8030f4000400e007200a030990040300c61945a2402007801d440c40840040e43c401200b800c0d003415a10f040c201218034502c05407550500c804c020700070701c0045c1d03061445003a1108804105491640c5e280620f040161290b03644500040c2030040960001d4010203d000081c401e40c450340c0b000400f48107542c0000d403503c41d01c10011440c00440050a00c0c25280e0040150140398034010400020f5000342034480154068458004800034040c00c0301005000400c401c501600c03030a0030607104031540074010f81c044c403500d41c00621030411104196140004100748440440c0055503800341003003295408552a600c010403180e809603040307542821401d10040ea0380f40030003214403002403e010b01030b801401682001021960140442d00240da0080c2c008402096040d0780210741641a4400c413543c6907440076000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 650603318 1250 650602068 650602079
    0x22502040e19020a0f051810030c06050903070e010515030a0e01020327030a1d04110328110301050904050f0604030e09070e0306060613031707020a080d083d 69
    0x13101c014000c805100c140c0ba03405c04010649012580300c4860201e0001c600103a42822101c41c1100034590081444038042e030745220241a680207080503510a0044400114003041c80c660950304848004003800403110120b2883d80c3e540d400a0300c0a212503450341c1031990740c00c4013400210700a944d8984d0b4501020740c0303c0650410380d450704100e04079a0300208103082240781e001c20040341201100700c110984000220015004101c403503030701c40404001100f0054510404541042d4001d0a81034544c10030700c04030200c4046442741440c1e1031480d10103100601890a001102c5a0b20900ca50112100c071810810b41501d49281194101d00141e004c035042c0381541414444c854000741c0c241000d9480c8050f07400003946610b001080d0600454000c15020840306180000700020740d002014600744034258078491341154000380040e4003daa0404000400a00c0001d40c000c81984507a583d07480c9803285c00100b85080100740011b1070500840c0f0007010704200d00900c48101286c485034402c601072808 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 650604568 1250 650603318 650603329
    0x210f0f070c0e01170115051507150b0f12030304030305100b12042a0510021002040e0412081012020f04050915130206090d0507080a0f060f022502040e1902 68
    0x150714195904108441c16014481e00c40345080e0787c0105c0320b2032000158842481e2140c0500500517112010700b01104603000c0450380602d501da00b0507540022401c07402024030084410803c0da40308240e200b0400140840e22a40c086504280083c1100c1c00c11550b031303030802105800c641c219100c806c912900b408100a100404941d208407246810360800101120600e040080b61081a0040c4117006640c00802d20030f000c0e00704003040c4840b085440e90b4861400701a040c50441c2c00b12100d1480f40b05a4420f1070141e40403078401d00d0745a1301100c90504141e2210190b01100300202c0e080f214481000c80b4a035a0350080503c120a00c10003880f00412502c100020720f200a03080e110a40d16011400015858401c2203600564013503132140b40132000741c5801480c050060340145043d004540e021070400400a60340c28613a0300840342440202d00e2003020100b244219002d40c0558901c800e203c0b06002200414a05198002013000900343e0340c04856030309100c802170b07510030a5200442d00000710301d441c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 650605818 1250 650604568 650604599
    0x16120e0a0f091a100f020f07080c1201020304051e0a0b07080703061a16111503070f05120103061a03010c180e0f060904062301030302210f0f070c0e01 66
    0xc1c000c40110f03d140310780101d40000004803c21007003100d4000000691070007005000c01c40e40d400301c12074021a54070114141c440200e116542c0c4203c5d2203da40da40a500140240c9000e250010f0281210382c40e11001600c81e81c50400c1041442d000e0000b0034004034045445240c41340300180c813010b1092402c0c820060499000703401064030710183c2c1c0515008020281c003134900c454071215450018100ca403e110300c00100303801d0030315032051002c1c50180d200c040d071001450181c900b585a83c1c9000c41c87e41d8069034540244005680044540c00040020070000e8001c880c0c0700910000d20510507000c0c00c082804d44581d03150b440d000c10503c0e81030070040c0074602e003404018094608a44058189251418500103010700705e5440f0b0391400c4041000e104080c1c0c00366a07041400b05c0780a41880b00d07940e83c400007040c24403080d40075000c2c010103441b4905a600c140f0100d2000c8001092038801c0f8019889a82c3d040300c404945542028816a400035440c0a4800050216503441c950598903017560b51040d1402e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 650607068 1250 650605818 650605841
    0x40906020c0f07081b04090b04050f0f030c1c1701060810050105040b0d051803031509090f0705060a02010609150f060207120605040f080a0801060e010516120e0a0f09 73
    0x40707803c0130041c8080114030345541c038000000e2000d10494004c0001c000d40480c0c60042c0c0325070070400a2004025001a81e0b1040784c03915421703900c043c0b0406600645078001d20748411142e03008200d9150b4040745024103404608400e0410a00701441e8441c3c10b03101a2090300302ca00490195018028a4074488040034002c08003441e0151505041c0510b040850007100c0d640350b2400d031100701181840602114103100007507210110317030b101c0c50203400895207500882015409580706d82d000c85e0781c940c0301082c0403074200c0d242d0000380840d510305000d01000d030744424003040c219513840001140c111001d005542c4018010f00ea850308a6040005440000e41e41358031039000c2d0360000604000300700da80003480c5605500310400160307540c2c0e01d04040c1507000003031800905d220000640c810300f044d0405030445c160740340c55991303400508800006549074031406401c00d580046618103c00052042c500c0c4809040f258130300039901604110200d18101081d401ca00700c0003100308030900102202d8030031024005d0307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 650608318 1250 650607068 650607073
    0x30e030709090302030d020310050907020c1302040509041106210a062124050708090d09120b090106080a050f1c0f050703090e0a1508010b0604170705040906020c0f 72
    0x80b6195000307582d0f8400e00700b985e54510f4010002445415022000900030003005d4204401c0d8a42071200a40762089101090711800c0c0640f05001d83d04100d02c00d860035030398050498541910b581c0c840700716000265174140d1344000b08100c102c0001702031420100400042000c90354090410f22181420786032160004c40126000b0164001e0244908034840c040340c3d0840404185071b0072450715040d8296035101c03420081401c1c0003e1000c0740d40d0040312030348607134001c005407001e068510340212000302051041c8801c862141190b0008074128a03405074101c0030900002540f40c0e9101105800c20078040303c00d41c0c842d003103d0024407000c0000c0c4500b042811050380c1c0d006140d1034644016010910840554080050200c0c2d00170415000c0c03034040015203111600303a07000d41f42801103a4041d00b00700c281c060700f02070b048200141d040014001c000247c4070081031350f8100390406271917441d41d01400c42115218411168006040c0d01c940c030514201c2409407e0141e91100c00000480c80d294030030541c00c541e40d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 650609568 1250 650608318 650608331
    0x2010e030c0a0e10081617160b18030d020c27040b0403020f060c0d0b0409110d15020310050f0108070801140d1421070c05061c09030e030709 62
    0x159a055080025242e60b00e221040d261113414507040302030a40d0f0030800c60361141201817006102c6404104c801c403000f620b040440e0751200e211050303c1790b41c018504002000b02400038032042c43c0c142d0203400403403001c0402241050303102002a01d4010036004080150304085104440ca00341200440315448042144000d80501d80d0507000c0c0c030b01c00082000e44003420700c1010404040c42442010030381c1c4000c0d001c8400909040c40b0026865206080d581c80d5036151803108285410b25015400146400540d1000b48041c20010303c075a07503014081c1213406820481d03546079000c01c1440030310300030b0a41c44041c03442c150604050040303048040044905000340041007250250780b00c0e02c9a819620051403110150200c1c0c1d01161062010346001800c41d05818195202c0f40d50000784001206081394038144408420b503111005485003000142c10b03d00f0b441014050350600b8001031014030081c4a55007180b600c21141282154008581100003400e100e8281e03940c1d10701080000c000c2c3c0b014502c01c2045 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 650610818 1250 650609568 650609593
    0x1407080a1b021807080702070608010b0a1407080d1401050306060d11030f031305040c05120c0f04081605060a1d180f0a0c0f270801020a0c02010e03 65
    0x26014803441542045000d080807005075805510180590390b024006070041c0211000305410781c0300483ea910b002448074000200004d20008000040b14030076141c00003d40d00300f0b44599076982c800b401140c28440e602019095aa144030003d00700c15006050031070321040441c955030192213101f05403002c070700711950040c00282c3c0c022032441d0b00b00104035078030343c3e040388645006108c00b0950b82602d41d141c021903a0b00300c903104002c0300502020704c0000d04981865110800c000460340c2c1c00c0032080c0000c0c000d04c001e0a21205840205403c020234105031800c00c06d0310f680781c4001358400d41101c1d115402250761400c1c1d110000200c0800f510088030003a0400703212100040c00900c04e4031110f1984402e904144015440d2130050741d41414180844100754a008403810100b410240c0719402c41500e000b0440744518828104500d0f881083d03034804400006a081300c10340305006182107030420000c0000010350040902c0203042949082d2a21450001c107800050068002102014001d810044e01c1001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 650612068 1250 650610818 650610833
    0x1d09010f290a05070501060e070504030b0c0405090115030e0721080702131d0a05071701020c0a0506100515160f0602033d0501110a0203060114011407 66
    0x107550000011601e0080380300c401e0004038611512800e262040050340c0c07140994004020103daa0081000b880f80035a104102c0881c0303001201d45400051041c00203000052442841642221a905035941465115800200e80c40d6081c2d001f0904080341c41551000c10303406014020140e1131010180c442c0780d181a007040f50000814030008400260750003004100300d801d0342602c02181e0060048854408a1880c60340140000c80c28003805041506d5030700440c040c0002c0d006805544040506416440c000c004c60f0380c04501005031005540038098289203560030825661003d0080b0b000b41460305002003820b5509003190403050107902035008a03c451004841114441d55034101203502051042c00e215a58000c3c0c0a00100502d00000c2070000c0010440d150424021219007001c2c0030f090030034008034440060042d45500030351852010031040d8059448001d0f403480540c15141141e0b010350005c0c0c00c004090304074610100c0c0340c0c1034058183d41e210700103404c000d10200e5030a00d0044c0d01e0300c8a0b01c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 650613318 1250 650612068 650612099
    0xc060403032d0e012d1a09160807090501090e0a062408010504270c05031006090b030f120a05121503010c2a050a05030a1d0901 56
    0x141815100d08002d40041c00ca88100740140000da912407990740c102c1140362015001c0f0307200c000c15641c01c1c80b0860760110f0421003001c032444500260450958043d03044040a0a600104000503aa01c98000c4015460b0081081d220305090304604d00d00e03180d80100130b81400400390203002000044042800181d03000701540d019120700e08a40740aa9540303111400150a65401802100203243d1844080801800440d01c003129140c070f40d404d45d603888509100446104251815401c003901c0c05411040303030840104004140580880341c02191208007003450410f01454018550759640c50411281400c1c1c41160081c0d44110080d0404a032a8034056a40300c8040e024024482000144584424018400c486e6a6040b0300c2d00b103000c6140402501c0c4410041c02e01c500c1c003035401c1100100129100c1d002200e2420710010001c0304241d0320090403c00210350b980211000d03c100c00c0c049010a900700050324400006980b681c816151840c8900218440381c3e00705805414660300520101c7d883c4075125 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 650614568 1250 650613318 650613323
    0x110a0e07090504020d02041203020706030513020f06160203011b0e1206040803220804380703020a020d05061801020a210f0f2003060d080906210406110c0604 69
    0x4d81c8070100d4600c014001d10855004c20700c00791055450b80300f01030300070607179a00300c6000b80c5007084903940b010180080c8440005e0001e5005a000c00662b44d01c2c9002d0b13010305011440f10200c0008091a40d010038216050b05070844040035602e05041c141e40da0000345040810740565440c440144c990785929514000904004c142402c040001400000414400f940304100038034507103070070161030070802200d902c40c0c0940b091180b5860442c03d6500c0055a2500c444031603070860700780302550447c4564181d00f0507281202180144060700015949048020510500500c041c000c7ca0070408292200141400d04000c0d003a401400b40c0424503401c44500c0015108480c40e6400021120390807600404504004403a00b40c50001804110307180e0394081c50111050071440340305600c0c110307458031a0380000c45c2e035076500030424404100028801070140c02c8007403000d020541400ea401a05065490104c00f00c1014481d0600400043c0141800341030b0070116103021240c503001c0b0301742129480c3c03071005002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 650615818 1250 650614568 650614571
    0x7081507030203061203040902040303090b180402030a02040308210106020f0c090612012906040e04170702060a0c05060709080a0b181905071a0315030a0b04110a0e07090504 76
    0x40e0306605d5400180242c000880c0599541e00e4541503000c0c0250010b000640000300c503a4000314a642d01c540846100540104071030742d20400703100400002e544002c003814025038090100200092442014204a40c40c03c2d01c100c00000c42406980305030807059220324119031004210099001021403141c11404080d41d100c3c220b42e540728013003251100071078010b0026618040c250200599139060704483c0c85000001d4451001c44e000420115010388d000d5601480e60b410f011a001a021080c0490780003900c55541d0b04100d03241c0c00064480c1c101c20303445408a20350142e07407002c1103010b002456210845003044038000b800c08501c5030352500344550042c048504170010030703018a070b010f503400300701c0703068404032003000f400f650340090114422a0220303000c0c4140540440d074503200c0d12400c104801000a00d904540d103010040500001c0541c0342c60305802014205400f041d03100c80003900c90f9004400c80c80008d43c401c400d010b40944140c2c4400c104142c0f003410300ca0443e9104141d03d08942003200d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 650617068 1250 650615818 650615821
    0x2a090b070f0b16090f0f06030b030715050403030201180809040c022a010210020c0d050f0405100804022814060d090f0b010e011206021b0a080c07081507030203 70
    0xc00801c1c680841ca0081c0076039211000304580c5450f0f4242683c0c055095503240e03640b0070742e0f41148100031907941c00b078614003076100c51040c0603451081e4441850107000604031045a940c40c42000d100802881e00500000c500090070f005064090061032501c1d07a0b00c0681c0d103d0200a83c80b0a8413602810030010310640d1114070248405200300b2642410380704081c106840e201131120b1490502c54545034540c0076000382581e2104100e120310942d00c0040407000a02050b40030000c003110903500003c00c2c1c4150074414400880c05480d801c0d5000e015541c15158607845007480d004001d191403e5076074402c04030b414054405000c003c800404412101e468038240901104e0304001142400740745900303503620f0324120b06001400103201041c040f841c024000041140d80b144500c40002100b4020741102c00040f5101c000040c0040d40140280c42804414030000b00c2824042804c004d5541000d440713052000c554000100c20501c032140040040f1002044882900d0f5400300d00b8003002413489003816070100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 650618318 1250 650617068 650617073
    0x7060c0513090b03010b09150114040b030f0604050a090c053001050406151202151209010c03110a0813060603080703050c0714030a02040e03040b0d2a090b07 69
    0x800d4840304425212800070301074a900c514002003008090040c442e42c00d00700345800d5801c11008290003940144040c2c9581c202203801507505881d40428040d41c1142040001103283c0840b000d18018803070b80e2080d43d42420518100310540d01c01618906105240490b2a03000405140c4407004840d0250780c824407519250701c803000001011219a2000803084800ca5000141940964032881c818002080030099001d01c80c4000e041a009407a689403100c0301003400742c60000c0040340e110b911402e8031031500a0180200c5440e072019550f404a40e91142483c01170603401d03005e108030582020200c02c0c2005c0c50b40400806550010b069407160700e44100d060001c0c002c50740c020b9005582c001203d29a02d40c514513008184e94410701003082036006282010072000804456075800c1d0b40700034014024549a50200001408030048070441072100300000190034005c40050326103c51013810019404403c501003007940d00f02c01c42440c1c0170007210107050b085517411116510640d0000c412a13900c07a403042c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 650619568 1250 650618318 650618327
    0x80705040504110403020a1d01060c08071505150603190b03240709050d080a0806030a12020c15030105060406140708180f0301060602060c0a021c09060f080c07060c 72
    0x5030416a00541411030303000d040c540f01c3d8010411a4030aa403d0903c4950b40c4d540725001c184403100307000750202d01d0b00040200c14800d61003600c600d40124110b40c80e024490792500080310b14058103515658440382048220009001100784d04c4a084d00c82e58550720b814100d15110304052150142040d944000003100364408100720504034000039184d030207001e1b001100c5644150101c40c04c80018044c6500810345050894050002a902140850400c070004000303407652500200225098420040800003080d450303990040c01070a160003410340c0940440c1403145520b00103484000c01d040400042085440b50412501268152700e40700071081d20501d9002c555200d15400038004800c08a034000c0185c2c9107411030303800c4c6401101c5041500020b02d003454242e4000c0c1c03013550050303008100040d40c815548401001c0160b064410780d218940440880046e02240315003010015a0226080c04025006481500020000d007081826032038082d0405101d4420340360014007181e26001e900484078050b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 650620818 1250 650619568 650619577
    0x150418050a1a070c02011b0201032004060e04050f0402090403051c0f06050f0a1a091203090102012703181511010c0c020d02040218030a0309050102060106050415080705 74
    0x50341e010385024241840381440310000864445100300216050700d00407089184502e0b4180c482c014031502c505c0031110110360740b15061341410780b03500500b040d50704012900c80b010000c03c4403040d103407400d108009254490304010240120f10b0314080c807614201518001380d206604503400744440e603461804540302c0c00741b413a070610007a1100403210482030007900b100d800f0f0742051808005203543d400c100642c024201420035041034040c0700034009242d009000d007030841010059649460100c201046641d620101e005000d9000840c1824040d0381c28000c84c401299046c5503d1011000001d0340c00000880e000010103110015117004e003156407201a071401403070056061010724a8010018101d02c0d51815040382c294030700084250007038054440c1005090f00601003c0c40f1440e29800e20000b58081a9034560314880310480f0310f07a80e90100240d20705140709039101000b60740740000191400506030048020301c0b100744802c0c8804580c0b6001c1c54000c1a43d071801d42c407661070361041910144103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 650622068 1250 650620818 650620823
    0x90a0b041d010506031c050306010e010311070b011a0906040603050603010f0c020c01030507020609030703120902041d0601050a0b0d02031b1308120408030f030a0605041803030b0405150418 83
    0x7070101012484600651141c0e02c6118243e00f619202c980300342d1200034101420a161700804c01c14004030340c003544140c680104402043c1400a2a00c0b2000c08071a030300c0d00408c404684500c0700d60014800d07652542e4110f9031070b00310060001d040c8100c0100240fa0381c010350083c80105503403100080e005580c01d4015070445035034131a0800000d042140c1c001d40312031003c181940860704110105400500c005a0f00748078442d01d002445c00c000407554200c8070629a003071504070b5103882d00005d0016a94134841e0b00c0c540c04d0410326010090084043d81810080140d004620034090030b081048000094011181e042045080050352640d40d0340e00d094482c000c021221141000c04140458440081000142520038845c07ca40d2a14060050305138103200d10b002c0c1c41e007250400d0024050f1078080350081d54004d0380e00c8078041143d9840310081411500e818044104101a6581c40420b0681500c5454401801907074188800d01d800c0c403480074a00e4010441d0b60280d5643c40f01c078030a00d40c1d0162581c40c1c59a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 650623318 1250 650622068 650622101
    0x3020706090305030603010b100f0f1106100302031e0601050103240b18040504020619110102070c03110102010207210507140705040b0117041b090c0915030902090a0b04 74
    0x1c803203040c01081c0da082122030031702a600c2d00741c07004e04620349101460980c2d003440e6280e101c1c2100c5010100c0c0e0554454880806100c00007808141c01c0c01d0a01889200d0302840c82d0190b0485c0c51350040620f005507001200014101c8004556100140441c803581510303001e007000b007007502d001484407000f4802c0450241d2502041d08010070010f8a40000301807480710001e02c41c05400080f404c201c11100705950080d800a4200300c507049070540445504a0014a030070301c2014124a0780c1480d09a0344800c508070781003814008203204102850380e220691f01400e00c02107003448081e41d0f468201d202442d9001c40b010840320341c901d00c0300744103000310748255a00c50020500000908807440d503c17a0240201031041c4d080801c0c00d04654032420050070a41510a42d0480707544840d165141250400440b061920381000c0d03010403504e144d8002c4464080301c41d036450300700c1403401d101e207407000c011000d420b0f040604021202e800340c0c3c3c0d60b04006401a400e500005940c01031500081c004118007000d00c10000b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 650624568 1250 650623318 650623331
    0x90308031620060117070503100f090c0f060311090136092a081302041b0c0c090b060f090a05120f0f01020f0a2615010e030a03090b070303020706 64
    0x30707140443c000303048503140b010054a18601c041d10a486000074028140c15030712103400c12001e000c05402c0000c040300c018000003084040e0b900d03401406003082e004440d009008000c02c001c2c955051050240c1641d2400c0e88600b488a4407000904c0e40c00351241c078020340002010650303002e00e850840004000d41000d02a4811650f03403007450090120048214250482203c0b0704014080f10003003510408120369800415554070300c40846421048281640c0040d0f607400507503444941000340a0304040d090701c51401c00e00307481ca4a61403010031a04914052810100100340c01d882d001c058480c0500c10080703141e100e11904020911001142c2d010300d51290500d1409003c48902090602c401c054410076030b00c14400d201c030268241c0c032444140c403000c60010040556158071174002070340031000020400c106891a0720400001c42010740d958000d4404891303c6412542c1c00100c1760700550800e601a00e15048a910041c0082016119001e4002c0000171184201442641110100e40e488071041011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 650625818 1250 650624568 650624627
    0x5010c2307090b06040f0e1012031106070903020f0103090813030602120f04020a0504090f0b070f0306060e10050a0908011e140907090209061201030f120903080316 72
    0x141d080910400d40e0241c903050181d800707814000121003d841c035a1040195080c58660030035011507008000021400d030009001c034010b411803081c0c00d4400d0103583ca400b000702c08001ca80341452000f6011005001050008200684a10350407418100007401c000418401c50b08004020384203440c0c500b252441d07680701c04001c0012070741c0a01040c0c1051507414481d5940c200c03005034092802e85019501118490742005035141c241c22080d005845140e903284d4980850784e4a08407448192151030215110412600030550b051041c80c00070034031032904004c0004168081801c01001d01140b40411200144038990180200071110044c4030410007000410711100c8a1801800030445035a8810b00f0149040c5038a5039415003a80102c4550740079000c1d0344c0c6441c403080001e5103c000002e8100005128200d174401d2164806402103001c2d4165590103465442d00584030042e4683e1642484404074061000c16407407400d90743d00c200d0740b44800001149141c01615499038200402d00e00000742c4c0a500794 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 650627068 1250 650625818 650625823
    0xe041d070e22060b0d051006050f010306180e01240906050108071b0314221d0a09020d0c08030d06050a0b161112030c0d090f05010c23 59
    0x8651500c40403061503100d01546503400380e040e09400350b00302181c8800320b01240e00f580c0140085200200040b00e07500c81c542d03440d418102c01e21807072601983c0d03130242044203040080114180d280e00b441c040000c1c6040000080341c41c4280c0e00d451030b11a0344c4421340341000c0700c00d41c07104521000c000400744c0c0e02003a03000400306508440c0500307055075050406c001441d501420540e0301030400303500d0b0303441d031f40c1c0d0701c1c86078981b50180e1024150b040208102c108072000e0600c8004042800ca0702c40d8030008082042030f41800e10001c1d602c504201d16244c103152082441c95402c1980010b40c0a10124a080d4203000141200c2e110000117081e802100078002021a00000202960000b0000c10320003e80d60707104014003551244200007080c03100300a0b04035600d52158090031880c2c400d020100e41940940080307080c0c0e10b01e5004928585d8030004840322002c400300f010040003000d900c1c121612a0400c0c80007010740d4400c0c8030303a41c144800c0b1a0403504200455034805100d85540200c60301d05401c0403191075 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 650628318 1250 650627068 650627083
    0x709050c0f031311090609161205010b07021807140705030d1a1e01210207121115010f0905130609050c12120901080403020304030c060e12031201060e041d 68
    0xc0301c0821204c000c24941c241414080d12844e8000c00e01c2e0350a43e40c007001340802c14041c802c0f0108004d0804403024425a26101d0b880c042d00f4482135654413608148140400c80582c0790003640c1030b580e030307004020019900c42d281981d50b48048511a8072540c0ca403900614602410f000d0082ca5402d00001c606540d00a55500e1542c00f801c42d51212408103ca4148032400071b410540344c0041c4840c400c0090318800c0420358207581e18100c03401843c01d0090b0b202d0001410b81540c0308000508440c501040b61401000300c2074a0748098800c1d000c2c294174015402c00c2c85d00c1580701d14080d0603100d00000c0c0038030400f42c011031601ca40010081c0a1102c40b46400d0341c89004900b0a00c1c81507280c3d005030980d29000113401c44503444041500d9140240d5540152024100100110f04511041101100280e4000e55243c0100341649032600c00c0e00c0032808021010609121121a40d40b090000c00e40030500381c55924111406d9041514240d04004c01160240107000c40e900c403050844040407130a0140020b029 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 650629568 1250 650628318 650628323
    0x40b03070f23040504050d030b03070b040e16050a0c0210140714100c171302220605011b02041508010c021005070503241306061d010905030709050c0f0313 68
    0xc5a2501d03511042004444099802401e1b0b80d03c10212450840d00a502401c6840340080c2250221692078001003403641c05900017480140e07a8505100006071241007a4150003014140706081070300b05200285a003180c1d480c06441403690b6100100e1a50003104e0601c1e042d10841989036444480d4207120203030348403030703440c0b0105880f0707100b500444036545204418a1920f079503210700c482c0c0394000400300c0105000e81500c549502021000700103070b03140b026500d0009180e81c95170408141c0b8292440031108154006410f01592080803482215400440000c0f940e04490000e40a000eaa001181000300d0b40c00c0501690701c0d0840d1400450f80000c2c440311307440440381080c8100d550b0800308840c1d602003a20300d189520240000b541c000401040d0072083c1d000c028090305c108030b80d100c4502050390401ea000b80e011601984000750b8600f5020b4840b40d54030401e081141c10a072920000c03036a1030032544121031541e41e440d0003250003846c081007165150301c0e40d40c0c0019289e040020ba00880005d84007000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 650630818 1250 650629568 650629619
    0x3010306020715020f07060b0315040c0e160804031808030d09060b0a0302100c11060301150206060907020d11011b021e0d0806010e0d1209090e0106080c040b03070f 72
    0x200f00001c00f4a008445061a07200c0c0154104403c6654100c054280280940c2c0c1c0b5001e44c0a80082c80400c1100161182c0c0c0a001211520383c5440000f2002000c041c10141c04821800384544006821503022034015503d0b00d41040c02800404c191000815a40c01075480c40c00009280344000806820058510380203403010000910f07043d0400aa02c142c501c00250402e04110707030a044513000e100150380003809034642004074031108000170784690090304a20703040540305001f46c4800d40d0400030070380e0003a029076942600b404d001c01c001e0340d14442c0d00c074080d00700210303181611910442900010204071903403803100300c01e0350305602c00794988001c5c8800f810180e11014187c3b40744c1030006890380011303e440d2190b07a05500d4000046031045507001c40301f07801c050351000210014000100318a5400141e540c0c200c00c0c241800b141c0c1c401e555500c2520009681040741c14061140c02054003100700c90304450000343ca2441c400880e0410605500c9462041c00903080000c0c0c82a0110300d155217030b40411078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 650632068 1250 650630818 650630843
    0xb100f06090506180d0f060e010b2b020105120f0106110312012106110306011b0803070f0905060d0f050703090507140301060e130302010c050a05180f040c030209030d021f20030103060207 82
    0x2030015000300d0414007203903130140c2f0300d4a2006880548081c0c44103801072422914041d01c1c008c12201415050b02c5050b0900c070140e00402c652a400b8a108010300c1c84200a1444c11680e80b14140d2483c0d018080d40c2184084005000082d20356410500881c0f41d120b0420300441034024052266504100c2d200c50205004512031114100c0380c1821100c52680840e0040c214bc580941c110740d0010641c3c0c1000502103124004038160790b860340a443c1c04003d240c400305034840540c07610019941c02510400906003004915800580c020600b101600d1000c0240140c4003423240c0001d001d4070709544140200160324003805031800741124400c00440c003d030001d003c88590000e044030680700b5025000300190f0300340810b403815207178005400202e00c001000049054070690014080324409043c00c0046640003503a00054141804041e00710704241c0050140000071100502181154501d01c3c1003566907010900004c1301420381003000300c140100156102c0da16131400000950001c40f040e180418280d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 650633318 1250 650632068 650632091
    0x50d29030601030b0c18130209010e010503060307030311010b0d0c060e0604031a060109032a08010b0105250606272d06030b100f06090506180d0f060e01 67
    0x3441d60480b41d2201c41d1008941c0c0341201d1400c01d40102054098402c460050120305944981d190151004d20310401641d5803540e00001d030140311440d28031414403205000300041598003089102c1140e8042c01c100503010000320403580105030000307400b5880059601d82200740a410403914082d00d03215126a41200312040401107180100c2c800101040f07036030410303002501c1d202d989081e000381040c1003441c503c513142e9079284000140462641c0020110321403280f12001d82801b0340e8001c1110000030004100b203100000c00c0c07171007005890f082c00021580c0c91900101c101c4100701016030000020000180c489040c1c0c400007400e524000541c403000d480d034681042c00d610803a026038440c00a01100030498442440140e010600310300301c81603076000e00001180c01344403064460310601000c1140641031411000109425411007010061364005c20b0285498200031508007030800c40b860f0410400c2c200c009844440b4030100280303546070320603d0300d080141c640c00043c1c8403c0e000c40280212880710 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 650634568 1250 650633318 650633323
    0x1050115050c03160503090d060b030c061c2d09120e010206061012050c030403030606020318090c04050310140114030a02120c03070311041803080402040c050d2903 72
    0x1a494205550001c03c600c0c50300c15800b0f1348000b07141d0311130f9055074200a000d500003010311018000980e0719988800f0700b400d1901d0144080100c6200482c1c0203410b001e003c070003d000a2030060300141ca400e9550030804440e4450918021101c09030000d0411817800d1001d106020b0302213114122018800014060003030350085419201080d410b03030080040381e0f0341d01e007046501d807400c4050509018005c0c10361803060030b59028147c443c48286404913503a003030030300c3c0003012510542c2c80700045400c10321011103203410002c0c00b605000d03021150441142c441c1040e0795000d11840d030003164103125022903580d0046c41600001003041e046030520980d0780c1d80c1d0301d1001140a42d018030b6503264001729a040011b1400141594050704c0b00000c071344c01c1841c12000301b45851110b400c156200d0080c10400c44561038140107200704808206001c0a202c00fa84d68040c104c86c0c40504000c2c4078907201e8125500842c03198090b5401424010028003418000001c0254070400341e01e00740c00d1101c420038003c1c2c00c60500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 650635818 1250 650634568 650634577
    0x303020d0311031e0411040c031409010c210f0509010c09140109091a0d140d050406050d180503030133080c1803030a1106130210120906020c0105011505 67
    0x400c01611040e0348544c85180b0020008008455000d00441200030a03117442c07080aa40c9406600c0000c2c01e00e490303010f034944551000b40b55200603030500031100d03c0b0650142d52a0346000c85901c1c0907440d29503296484c0d010f007801c0401c8294517031504040004001c0150040c01c400e81c2141c545003d5140c403450000d419450810195000c151482400c004d4088641d0102c8940903282d006c002c04600040c000840544400c8000e1b140c49100d00072050711660117022101c002c00c05810a02c0c60279160100140c803d00a04402c0a12599280b044083e03a40414081c1040e166210003a2642c80d0703161030074484c00e410f040424088065190300c006c00c44450201c010958650302d81c407002200da4518901040680c00b18540c091b92040701903202c0c40640301040a0104c0c84425103d40010012140d49285080001400c2e1103090621680000258844003040c59812000745071400d006000d06424402801011000070645480054601807451040d07100b50305036441c403070f814181e0a00c0d002341240c09015 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 650637068 1250 650635818 650635831
    0x6011805090105010e011209060509190515040312060803180402032202191508061909020a110303040f03020706090605030c07030e030d08251202220303020d031103 72
    0x10040040c0544d40c001c86080811140503d00380740d00310b10001240081e12003041007102c0c81e5440d00c051240b10502441050008807903a105e812000700070307440b115910400c034008569822840c1012800307061040f00c00240003440c104050048590340c9820550b05da1100711b0038010851080c03110851032030940203e074052072561000f000120350415202c40a078500b41003caa101241d1812a086145802102c00080c1840d06500300c0111503040c01528100b4000c0c46140b08046684000b40c480c2c038840c05c001c068960030340e00180c450040884c140ca80e194080702228961002108000400c0700b0b19600300040c1c2e229500750703041c2c40e50303405059401d1a40c2d4014500030500510000341c900305040c000c5c1143d00c0c0280740005d000420080444c4c1042409004007000407000002c06c0262403102a030a83d10f4101b607444011521048940104001c082031991640250005806c00728500000d103441200503c40d040341d504a9a20f01d0040d50741c510449411005c04c0c2044203c0c440850140140c80c031550 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 650638318 1250 650637068 650637079
    0x140706080a0608151008060901020a0306050d020d1b051903050706080112080f070803041a0105091302040515061902010c03061a030603071701020703200a0f08070209040b06011805 79
    0x8145281031130010050100380140304003980021014803c0000703500400070740c800141e641d07038885001020b0302d40c40d8000e01e000c0c803811000c95005031141c050070045280c00428a1008180c1029030051044081c1d001300e40c40305000d47d4007070004504610b07040c1201c0c4110115a280307641c5d200140c5404000f4400c465103821401401c5002c100703204010054411082013aa1502d0000e66654040e50801c0c0c60644c3c0c520382d030180c0c5885c2c0e141c6112505000d02022124444240b5140d0008809120b21060082c0074a03101c002141c1c00b10400b10390303103440c2000181415210401e60104c0b40b039902030942c0e82c600643c240b0122103052030080c0f0941050742d000100030030354020b550118244660001e8800ba8061046002c00a02005410f010660781c0702d00c400096916441c60030020b011500403500612021400302540018010015082103d41d501422640c0350340503600f0401500d004d690b03400f9422002031020881004014203500c0c0c415542620b808200710401240c03840c015140d03004064115 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 650639568 1250 650638318 650638333
    0x92306030c190806010b030910150b090a030b010902120a2003150a140a0905010b0306040905031e3004060506040e0a060b091f12060207140706080a0608 67
    0x5050242c0540c41503007000c46010000e580d9041d034a45400d100b41d0111000075004400d10030305540604c00042042ca20240620080303044a078070f00071208044c49a007041c560300050140c5542c548002c524019500401105465a910312101d4081c0d0300143d1611004118200003c1c2c0c040d000e40704d940c9051802ca444508080c01032904c003100c40c0d10181c02d00351503161001200080340e49850001e40030344403003495810b85098035000c0c400c250038140c102e100c4650502c001806460040c078140c95100f4000c880c0403c00d00d440d800d0103811889038010b00c0082c41e034960100ca5003c0114002804403c130444588803141852568084039008400c00170245240ea4401040c003148050308401e40200c00100009540e0a400710842d04c0d0000c040b404642072030701c0b4124a2100c2c600305001c5a0301900111004c0c030414189801c1c0b1042d43c40500420b44800000d41d402d00c2805201ea040e90b50103035000311100480e2901d468000d681d00454451800098032140001c1d078450450b025010460340da007801400d42 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 650640818 1250 650639568 650639593
    0x110304030e043812070e040f0201030209060a090e06010314040201180f2c010b0d0911040e030c0606040b130b240a080a0b010801051c06020409230603 66
    0x40e022280e00c0d0940c2010210403280c2143d580245000300e00444070390366202d14042c030140502a96030444202c0301c0e400980042041003550036a80d07a129602202c011008102440160028040e1003c101c3d0020382c0071880740320894010080509440d581d00d10302005503640360045050303409018000540c00084404540194002d8400301840301e840c00211440d5902c42a51543c1440306500100c17a0002e446842c4010700351005203104803036100070001d9030a6040c1900360080c0d1054614800c409507032500600280f162028003144815002071003403284201c050718841e500c0d080328071035825602462020a1003803074288281c03120300c4001b4014017070182c40c0001400003085211840d40d00310690000c03001808041c000c40500036202010610349139610341c140205103010040040f20305601d8400c02900303980e002103e02d41103d1045580c101e10510f10580014402900d41d4000c04581c0045130105840a254000c0c1c04a604032130460107010802c2070001c0f0036034509581030b640640050341c2c04600d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 650642068 1250 650640818 650640821
    0x2010c0201030b040f050a090605131101080a0204081905060f190c09030f03020f0d0f0c06111b07090c170604110c060a05011403210c010e1c03110304030e04 69
    0x1030010000c4c00000c142058080d008259002110f4000c0d116907640000c0c41003000351312a950700300c0903545004007500400d40c0c2d480010929403403030030f040c090b240c40000c1d19440e031901298098402841660007052019488400700c0e01000c000f11000d0045d03100262482c000b201000f07200d02460081042d414410780200c50060030021402020049070360008808504503503030f8203141900c00c0e0f008050403000b400c14942440410b0b20b98804104003c1040d1200c00c0c0c0c0720000180c00d030f0300860000760403020048074071480d21900b00d01d941011180c034480b200e5000040340350b90894080050500060b01d40f8881107843c443e01d0361024403414842c00100c0c84d5400c0c90380c4036460081222401505e0404040060741c40c0c0303482112201801a10b0704014011155001400380c0060300c16001040500400302c0080c0d12010004e1038034055200209030406000c1c002d40044034120400819100010300d082d5417010040a03403001400400e0810307608190340702c110030440348116050b54030b40100c213031000100300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 650643318 1250 650642068 650642081
    0x120c020d1412010b0c1507051210030210030501060216062a1401021c0b01080f0c0f0a0206270304060c06020f210a1b0c0204060807080619050402010c020103 69
    0x9801100a101d08410405440c2040f4060316001ca909600d0701038000e4507503c2c10703001d94032a00024450310b042c408407580004c1540d80882c2c1c41e14600c0d80690f140b480d0500040748c0c651010f5030220b04191103012143d0150b0202d07050311001e07801d80385115400300b0078243c602554070070b1074001014419000c0350320b030f4610007003072a05c0701c0c3d10723006034510b07905071140030b11054400c0b2001e1469500043c11340c00d0140401c0e040404006242040c4200d08050002a1000300001d14030245058260002000d0b0f03101c58085850304500c011906407298026007000b5a20340c012226280d03c80d0102284000251120078650241480f01c401103151604100c0111003101d040802100d0864082c469070303411342210f80141040c0040c8800761803074540200104840311501070a030429091500d5440020380c0700d000e24940b060072030760520149418041c400b0400070481c9621420703150260302c1021911803000709000f8015184004407103810302119110b142120010f40d00240421001301c1360740010b501a80185 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 650644568 1250 650643318 650643347
    0x70b03040507080706020d081006200a05010203070f020f0c060403030f1e030b030c0d0803011401271706330a030c0501030f0b03033c0901120c020d 65
    0x1c8000b682d03515010307454400c89400c11005600040181d186007540000780c40e0b4024203900030480c25500d08880034041005862141c501e90140c01c1c0d850101071420840ca400590344080219920300e4004401090211b850369882c0c01406a400b21a42c91007000812803500342c3c0090144c7e02c0c5c5441c5075000d640b16600c407015602401100301480d020140b1a880040c14807280d52400b084404c80007081500b400c440300481e0b449220400e04a80105208109681c1514070111440001011090050f1a10401801d2811800035034088600103981c43c000040119010044810194424004260344400c022074a400358403084059201c0941c02d6001346120550030910b03048191140040030441d240216041545c000650410801095034076100701098002d0b859420006286281d0000b5160300c50003485100591901c0800800c840408804065680010803200c45c154107901501080343c001102540c085500041c0c0c03101445200d01418001d010755a015004e0540c5a00c0d06031000004410f54 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 650645818 1250 650644568 650644573
    0xa03111c0f050a0b01170a03050f132402120922021908010b070c03080d020c1903140405030a140124151704030e1c12030609050108070b030405 63
    0x5000490300210711101c805000300c010709002a002d040060800c80d043c0c0c0004000c144050105289080110301862600c1e45450f216503260303500c0340710311101c2c0034420310f214500e03158810020b08a05070f40203d0100c124041b103505122003105000380e03112441c4078580d4045231000c00c0700d0320b050701d4100051006d400440b262007035144810384000c412600312100030346505030258001104285c000c0000c600405418015901c0c0c402d483d542e40e1800e403841d1000605048010415440c0450180c05551000c0c0d146400c59445001d009010a2141c030301601c00d602041052910040d400c20749400c0354182c480c06001405c4560687d9100c200614450040d00895562511841031000389044d200c007100143d45542c681903806c01148005910705480b0708021f10440c80c40b40110046003104440e803003070301420442410031034400803c001400315100865003040b40a0b0203401c0141d1313400c0300c1d05880c1c90359400f0000b4588458034001110000c1c000c3e80303030507032000748100203420310070008640c054400c805 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 650647068 1250 650645818 650645869
    0x181003080a08100f1d1503031c1808030106230a021f090b0105090a0b0a15080a05040209060d06021209030304052e0e03071b090b0a0311 60
    0x6680c0603039007140c03808030300040c02c800a0000c00c000c0c010800003d03101c0c419980642c1454000d12401611903504060803000c030450019468072100d6605840307060000d015240c0da030031180781207154211464500861a843d0454061038a10221801e21000f139000361840d1440c0d007803c1003a10800051405000d503007610044902d00504400040c10a0740c00340e400a15103008407000f8401c1c80c1c90000d025030103842c43c00c160600441d144400d82c5045600c03d440010f6540ca9800f040f6014000c602c483d07903005480030400060001d00c45007214100003607542d611101d6280c910010007511000d0307801075030001100001c10010315004400495252140724018130b0030000036070100c0b0100007101c2000d450b400c04020001402030901541100a80d4400805000c0b030203004020704294100300d811500c941e68900c00c911104c3e003002219100d03a00712101162601c034542d100c15580e0658091082d083c1d04120070b01c40d0301d081c50038000e0180c3c0d070b1006008100510110520210104401d94000d81100c547c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 650648318 1250 650647068 650647073
    0x608060112180c03080a1106160309020a0803040f0509090a020a09020f090312030901050f0f1302012a0c2907110a0e0402190503031e0d0e0307060c030605181003 71
    0x12009008510900801c0e03102c010100000c7d140c44224440595240c10040411000e02c0c1a1005403840c4a06030800044000103070003c290f039084140c204c44c0e0144000600460850101002201200d0040f40c4400440d0b803102c03c29600c0b071040f01002034000001150074080210700340c001d0071401c0c103580c0b8060700300b001840c0082c1c9047c1e5041c150310313004003002040c800180800c0c0600713039204000f10307120013190828652030521440c008000303421038007004081ca4216807107020001c0c1c10f40001000303040180000c82d060303408403400301001c841000108400240086083c022180446107203125034801c1c15950000c51520362010000320740848200000040035642e408002c40070346210303100d03650545007034418010900c01500d10034041c007414000c01c00c1950303000011540083c901552100c1242e04c0c6001f41a403602035500f034144018100200a868080b001015110b85801030350705005001350f4801c280d00f103a001e402995000070305a65100b040c000e080e055141c21510818505040740d03501d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 650649568 1250 650648318 650648333
    0x1051911010b060a111009080706090809120d0e1e0607050c030d3902040e0109061b0810050306132105070b06010206071d031f15060806011218 63
    0x104000b01040c1903e14509011000f000103413424140070408000c1e00190361100c0d02c08d4000c01200818090700c0b1180a82040b9410050720602e22000d4002007407508460005600c482d44d808203c0d000030f00350741008a0038503044202800420244000c9044141403c040c0710840d4030040080d2803c1c42000c44079241170310300f0005100001c0a680d134440f41c54a410b10b0030f032001c01004400c02d03d034208034004c10503280d0182885505c0303694100c0b40000c111040050b5140504201d18014120702d02c0c0a03020600b9600d212601282004aa95038031342c96502c0d165502c02410140c0101e9403d40c3c0b00400040001810000410106010301e030310001070820742ca0740c00c40844600703440000065001c20420200070b030644015400500900161100d450203040c01400503102100345508080044840c8050342c030184402d000300b418103010001c2e5101c1c2d510700c10000d4080d01d12510200303800b54900103280e0b4440e4030320343d008240503982c8038205030103008101e010340700c01000d0086080058900d54009002d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 650650818 1250 650649568 650649577
    0xc2903090102091507030503010e1806010f05120105100e0403020307050d0315170a031404030203010e0c0306100b0a0804031716020f12120406140a09020f01051911010b06 75
    0x8800c005607484110307106100041d0898021200743d84018402c8500094104081c0c81c1500c8a03d6001071480d541c000214010038038104020300c99004510012855003448182003044c5ea8041c1d070403001a0b600000f00340c1c01c07140b0468140d502080d806074180b2182d00007c0403150007030b0007441128203160f030076248c0318288950b410707002003c42e42d54000303100410034076034200c0c00520b141e01c1ea2041e0b203003c0c0145c05445e181200e0005041061b2501c1c005040c14901065402a5401600070030800402c4100c140c0d54070f481012480c407a104050001703541482d18241c1409030b0b400f031182c0609102c0500340c16595264003400c2101070004040980c0f1040c4c4403d0142132040c0c80d040c125025150f08124003a05001c2c11a5203581250040602c1c1c4403040300d080b003124110175000300800001d45c2c5a003081001401181ca030045811501c000348402c01250f900320080103030088031150301c2040960700665051148812208151490382c0d0088030840c015240c0880100203400003042c080040b200140780c50b8071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 650652068 1250 650650818 650650831
    0x140603010e1302120f060604020c030a0e03010e01020a0923060717191817280b0f01030507050a0617040302012703140a1403040c030605150f010206040c2903 69
    0x4a501003105c080010401341d604103e007030f64214680000c2c2e17071000d034403403080035202c5c414842660310b44421500c0945c440010360740d600008545610204400500440c81da228207a00700c400c150704030403200b005810100c1d299000a01d018505961582e84810300104000c0b070000d10036040c40002540c24207060b402960440c1560703040c3c2041c0400300145d10f0414140c20450180803141030040c1110400a00750044003024005e42c13482c09207a03240c01340c100c0320408008007000d02e84014400d1900510141074140d034424400d503040203807520308bc4126915540b0400b400100350003d01c04024003c0c2e01d0141e0810701a10000c01e400c65420744840e03010355403c4102d0316a4808141e00b1040c15802503100e0800c4401300c600b14645a041e507030091501241b001075500469001010804108504610030011540601c0600c00c0e490018040780864000502813030043c2c100c028200e07171962000c40d000d1700c1241c8c8129030301a91400c1c12800c4000c501f4503950400b183c18141c1e40190380f1105039018512948 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 650653318 1250 650652068 650652073
    0x3061203091d0126010608070807050120060c03090a05063111040e10050c04030b09030a091802092112030f0403030203190f0e0106140603010e130212 66
    0xb0b107024034080c412071518204260440700b03a801403011081240542c0b42c0b618401c601c1040100c03401800380d00410040d44155400c0c8506000000c00c0100801c01c00121502601c5081c000f04081d0301e20380d0980400e20001100d80c00800006001000090285800500e08011510307034241d50340e20b003443d001c01965141d81e50f040000440003503a0040c543d4401000e013441d9003111044a80e603482000300c109040700c2d17218a450b06850751f00b400040003401600d15100006100b6420041c1c0c08401d140c0c098002a81d5514200b00002e1744003400104446810030140c0d5904042850880a0390706075941408000b0540d408018094850ba2910585028105810010000e2880185c611490581c0c412100340c1c1d000028810440442c4890745000d6029405007000740e680d41e0354050030b03860502803202e0169003c2c900200902da0320350a074081c4100151000080103c03980300c00e20070340001c0e01c40c010180e00003030400040c40076260241c0703843c0d0401090002212440c06541c0007402c12142004211140e5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 650654568 1250 650653318 650653337
    0x81314010b0906030f060606071e031e030605031e01020c030d0b0f0a0303020318190b0d0b0103020f0f090a12081908060d14074707020d0303061203 65
    0x280b400c04016500301104800a020b920a181802600c0e180d00034002846150045180e5041c4162a45101500440007910607024029464040e102c6030005041c3e000c8a02d910780c000441d940070703108000949a0040c010320f0003200070141c00039034903403140051303400c0d5400b80b00308200e8010810180500c3d422507030300071511071242c81c00e010901c03d000c0403241c07146200030002c101280e00401100d0450700204980003459140b031003c60042c0c48914031400030b210f4050000100b906d40107016002108402c4020f01440c3c05207401141640031f04400000001c03001c003c1a00c103810081c00a111410001d00745943d5965181280c8031064500c0c0707401d40c0c40d001c0c0020030b802500c80712051601d020760340c2c0c10301950710b00b082c2000c100452488440200010940380c90242911000c100740801060a6441d048400c4000481d2502c0030030084400c0b0b0000f000344c40d00c0450300822441011028160b10136240c1401403e8080044440d40600180d09141d81c5441c0804c1940030b0b4890903141074065100e44940 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 650655818 1250 650654568 650654591
    0x15022d010b04020906040e04060b0604030b04030f1719060902041e06050711060705030903060414150103321207030e09060907141b25080d08131401 65
    0x25601d00d0309805114600c10818900c43d40e440c4001e480c265158855075180a0742c0320304d8031200800f0711909440e070214010600200b00f00307a990010b03126034072030754540710a00100501074543d102010040a920340241d000228901c41d481040c0c0d508042c880004240e855407810307607000300c0e40142c01040c400c0802d072510170f0b84807501d00c1c03145000f40702078507100c1d2500c0055203e036100340c0c10701d210b42031040741c0004050b410320000304142c4120100080c29191075040900e03222a90702d03a021100c54050007440c110003c00f0103140e038030340d049a80142469441c1034140c404605a03005003d4001c0e4600d4090003044c4410b4001c0140c0b00c41142d0000d0000da40341d85a08001d0000480500414880c4801d80100219621002c48650f0002d4003810318103205004200d65121a0007001c0c102010818124401c018840000400001380c250009152444483e402d80b0308041c01d00070300444c001030b4012000c040745e003481003401d03640c801c40c0c20204a8541d5069652141c04029140720321515a455811003000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 650657068 1250 650655818 650655821
    0x3070207080d020c0d020f10031a040902010210151d070801050f2206120606090f02030601081807030b0106030c0806010f0c0335010e060402070c15022d01 68
    0x1400340704008110038042104004d6980380c50020450181005004001c11500c5a140c0b00300c0000c0001e04500c048a0701950090051034043e03400108801d084050035201c0c145031054071001c0d40c0680c003a181d080c18442206000e001a13514640f441c0040a03400249506800c42801402d1080082070281d4103240c0c0c4000c01800b41a00420320590104503403c009994903e407814111085007085000217051422800050010b9401410b45e40d41d070700320100412125a00540903505100c00c100040300d99441c0027130403400102d882c3c43c0440c40c224041408404800c80c1c024402c16103501310740c034030380e126680e1000c00507082e40100042034580f1078014000d90011000d0b80e04c0802071a00807284c99201900a103008200400039007400580441c1c0444080307104560302004680c55403c2c0300d07845042c90880803441d004d10130415214010804030b000740c0351a001302d2315000e4000d8600c460441c200802200d0f441688041724083d0300c0b030701403004a41101d85070400b1601201050055090341191802d50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 650658318 1250 650657068 650657083
    0x80705010609050c0910020c0406260c15030a2301030302061303080114030a0609080c0709060803070210023909010e010605090315091011070209040803070e09010b030702 75
    0x210403a003800d00700441c0300184c8050b908003040403668a4108507078003030244d04001509454603001810308001062240503448401c00b0b4100b044c8a00204201c405038068a584000c01c030307198030103880c039429010b80c4180000b03507802c412408030005d0014030103034070108001091040d23036410003d900d004105050b01840044e80c41084a44200c1040f840341e900106960814010384400200c404d1941e00e45403020400b00440300c3d0301240030070a404042c1801c441640040c880d40d4400d11030f2000c0411710380a51b004100840300c140d402982481e0749d42c2d0030010441c070b44840800c11881040185114480d608400480248500f81c0540303d100d134500808031030112100c0380714010b000b140010002c0c10091400d0310304403520341c54503d0b207403600385002900b801c5014070b800c0c14041009040c44007090f40800c0c11240004940300401c80c50001382c04051180c01070701001380d40300246c0b00000340802c0c4c1076001558010752178545400e240e003c0c040058643c110a811140c0c0302c490101c1040390b80c9404004c0507 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 650659568 1250 650658318 650658329
    0x203241f09030b0a0203091203100b030a060f050303041505031e18010b010c020f040c05040503030a05041809051906020d0908180102152206060e0703060e010b0a200a0807050106 78
    0x9506c0c0d86011290f040e91a605903007210103035000040003031a01001000f0031409080340240c0665a03003070010002003d003000380113a00c8000b011040014442c90000215022102082e40c0441a900d802c1c0066500b40c00c01001a5001d4092100c03592031030a1040b2a03d1051540b0411030b4001c203010340781e807802c40b40d8540003181804204c601400150303440c02125041e00300d04440101d880d040310b0f03404441c130303000700d0b400981c052001140007081ca0b604003002d00151802000111458605007400009540c40c90b50003520340e420030f1941916071a01c2d8040d02000900640d005440c0514810850f4202c0c1e841100682cac0500c0c01041d802c89081c080c2d0849040c1e407130309200505101012041c51003100802800b80703001d0829030710420261074032512000c9030181e0040030401143c1c1e9600d00c2403c0072102220840b0009142c5907001c1501c00c1d80b000c0313040c142c46001c01c0c000e060504242083d184008140d502d009815030144000f604074000304607006020b44601c00180d240c0c40d45107806401e680d5550000b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 650660818 1250 650659568 650659571
    0xf09050a2c0105240909100e0a0308070e010c0b0723040515070c060503180304030311190b0a0207050c060706062306030703020904021308071502010203241f09030b0a 73
    0x990074000c010000036083c46800319201406906d894120900d02401012510b80d00c40c11300d101852010701c0490503135925400ba8031201120354540a048a090020410aa0102c1c046140c400c0115501d521025804502c604103006070100c0e821350702d544440f440f48541061200010103201a003081c00c80624003e035004249030402c5001d64481c404849180a103508005012000922440500204100d04000d04055a581c0c1c1e4584c10005c0c01034048105141f064030550b029080541901c1c80160041758001c00c402c109619403c100318060351190380c080c1e0f128464203136114001e90740ca50003400e0941c0300e8600069034500e04507200038803c503020022000c0030501c01d0b10031101c2c0c650f4002c80c3c0c0d004489180050380c8003e508009402402a007842c042021814840030070b4081c030010f0203206540c00c8200c10604135542d03440c102e00b80c0c8000c450b200c207021116080c10005138210242c0300c0620200030f01d841c00201141d810311040b160110350020004561040420510a992407066000b10a2400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 650662068 1250 650660818 650660851
    0x1e0204091416050c120c06070e09040c0501080606040512030904110708070204050a021605010c03050a020a0903020f06040810020a09060f051209010e0a060e010b04060f09050a2c0105 80
    0x12200c41282c1d803200c1a1060203070000701c0060098003030000310b02c00e441e1070032116101e03a0384c00d00b01d60351070f0012104c1c4000702c1c0030003004081d10314125001c144240d500013080001e20b07040c00d00456101101402658010700188400310f0780f940d447c190800c407147c105000b1501c2d4807061f02000151503c920100a101e402001902c011482c604201d40040e501528046880d4131405441802032042808845110200700e4080c0704020b410b40104134074408940e014030040d103500c0006012407090500c1c4401152280d0410401410000d0141c4034050006041c1400e240c2d581030418106110003840e00202580068620b500d5500311300c603903020b48007518050b4803100f84114003908900c102d02c90000c00d1030038000011410f400235046448204c8500d01a40d49403140e620708078000d4809000250002d50800c600a0340505081c07040e08119500001c115217014a4000700000404003d4109081030391942c451100c0b400c4181e1644241254080302e00c0440003e510110742150f5014110601d211400c0a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 650663318 1250 650662068 650662081
    0x31b0313050109080d111e0606030d0e1e061204050a0c09111606110a0e01090b07021c14160501120b060d0e15040b011502031204080d1e02040914 64
    0x6a030420310105410564984650765103c186400100000d000c524200000b494220341c10108d542401604103034110f54249010031403e0720b114200d036003d16044030040d03103002c2e600444114194823103c0054001403400c030440d2060352491200311020348480d4010700c3c1010810452500c00c070010842910104241d4004403049120b0340308004040e40440301c5009603205001703956104180003240400c04c00d0742d072424520007400300493d40030306a000c100c81020024100d100d03a4212503c05900400500c024401064011104e0080142c10340705803525a2207010706880401204503881c02c500d06845640b172030103000400c05100d003646048914100040e00100d1384852040e6028404000c0010407500d031302000c228034041e0362542110809541806200a002c00c0405142c113032455001006c0300303507076265001e1f42e5911803210451003840d20580001d002c668050081c25a00f80c91440c0440c002402310000310b0b08000001000003020f174001000c02c140c040728031810801c0c550210b164489850301e007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 650664568 1250 650663318 650663323
    0x5030405060a090318060e01030c0513360519090203120913050a060807050a061209080903061e0a11030a09080c0601090c03060e060918031b031305010908 68
    0x14025070301c2d807501c0300d250070f0805000e090f00e40007a0400813800394105070740c1c000c014030302c82c403080016000c00c0ca042c0c561800c01c1e220340110346c900407040251542843c640300100403481030b80d84103600152440045a40d65900c01038035121091810000410181007101e40c42d501240b00880c400030b564604a1010016200880d000201c60702e00c01d2640d448241d03003804a0511001d05800810075441c0c0003c00c000003150398043c0c13080d200114202c2d0240d075182c40c20300c132132400180910b80100c0c18021410780a40d0050700000c6180b031040f00c0341404c205000e00400c0c42e111080da0070740f40000580314485240300e5440782c2c3c90703405420584180300d400c521140200140c80040c1404032050780f588450350511030364108580b19031003501c08403002980e56a00510003807608244c16030019080220000d0110591000340d0f000301030041600b00c1c507803140c010001c20403031120b80703484280c082807140912003182d04521038280d60182c0003441e5101d4541c0c03015001e1000703541056041c465000303020f102280d0300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 650665818 1250 650664568 650664571
    0x30108060105060c0c10110115030b06061e0306031606080a11031e0c130b040e090309010e0639010e01060b22081002450105040f0f150503040506 64
    0x10303205070701b5122410000302ca210344400800c440742d6003480fa030032002480054500044a0107a18441c07941c0e04d40300104445849914000100203c00841454013940400001e503000300c0e00404840003209828104016490160712010100d0140020050110707003500494130111070603002c0d1481c43c600392000441c0300c15046200c4886214080000350550401c1040300c40c0031100361200110300707545010882090344280110180400c1103000b0800420001080d10000d0700e050b11298040c40284090120700d4000e0b0302d202c06452411425a0507080b090400c1e44001c024044054081801b0354410501303560200440082c10b030300d468010007041003070b002902d100c0307811000000603501400250700104041500007020074014a082d001150040364000c101c074801c03121001124100071400400d4100c42d18004c4001380104030300b0b940b002c1c03903403600f14031013001c05040c0b040c00c050b240c0c01d61040700b15147d000421b541800480c1804407540403c03c00d0280300982c40c1c80e82c918a0329555040c2c68410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 650667068 1250 650665818 650665843
    0xf010915050d09020a15021b0a030209060d060e010b01180308070b04051501080309010e030c03100203180604050a0203151009020a0915080402010f0e0d12020c06040b030108060105060c 81
    0x41c04a0354a41c00807954000084594004118105040c2c07242c100c3d07100150500d51880240c0720344c17112510402c0d0340c1c0c6012450f07210014040240c1d6869a024001408030052031164411034030403038400019818880e51040c1e85003280001a03003241c0720005070020640c5245600340403518402040018440400c072141e241c2d0205080a9545651078851f2030058200b800c4118040030388004190030b20004042c080b1000c0036a47e8031903010918081c181c41d00302c54040150960071001981c0d03070302820b540040d6002a2031030700d81826100250011400c0407400c5d40c0031106a0001c0265806503d0100f001c03010711644d42c119610746042501d00d0000d101807521a0008990b0041880c00740d090107a0b01c600001d00c000707010419148007080c0010500e59080310201d0204200700c2c614a5207034803035498158400c038003034400d0703140c801e654440310350061903010020110310840c00700f190a6140c01300684000e111000c0420703141c0d418141c94070700b030290503000b1074055002400103814090340003c0d520602c12 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 650668318 1250 650667068 650667077
    0xd151a0a030c180207080301140f04050103050316080408010c0509030f010212040f02030106090f050a1a0616020a0f06020724120c090504021c05090309010206061005070b010902090f010915 83
    0x200380d003e640d0042d000c1c281c40940100008000001d2192041c66600800002101c02d004412002e03000c00044a4003030101800305d82c41400107003190f215047d82c000205004440d024102a41c81d240385007510354400302d06001403000f007900c0c2c1c03003800d0420501c0029241c0600035401d15030402c02140b90150001c0016040340b200a0310b0000b5903c0c01e51180300a8500e40d84144103c4140000c80c034080c0805946644441e460414a036030742040002c844030013400010417503803524400d00020024261201403da074000c14031100001c4101094072402e004100d2600584512460100b032500802103800e070504500030b9280061400560140c18a119815200400596021584801c0301c88813180e801c00d6400620010b90301004004104100740d82c1c00044c0c5050026a4a90300516141c0c018001604e0140c3e00400104103945040d100c1042082c070145009401c1c87c0690f22100340c601400e0341309151481d80001e0140c00c90618600d4001c12550a080c0100801e02c0c0500440c1801000f540090800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 650669568 1250 650668318 650668349
    0x190804030e030601060e090c041410170112110a18020c0c0405090105090609070501050706021c06140a08031303061d060f01090c05031306050a060b07050709060515070206090d151a0a030c 82
    0x194003500c01005334603082c0040c54099a1100700c03a0840007407079a0142c0d44001c0725004a061840e01e42d4101c02921142d900e0102801c40c1a40241e020f5004403081c4c1520f4080c4082c400d10a480303074402e0620030441a000400e89040403023100e4140100500008010f8001354014003a0340d8200c4122050b140c1c1c0514010b83c2c862020201c1c1104900311103200b00c0039820710600084084149007408907410044500514560b07446110760b60700d2003150003c0340c0c560403140b0200301048099000842007074014840c041508000e1011074140442103803804000b00080c801840f2243c02c1d84524500200c10b81003441c80c600300340c08060b0440001c004000c3c001a00c410008101401d580c1150006201c0c00d100715850790b54038940b058840109010341c0748414a04000010580b4044445441c941c19001d070300f03441c00720345809000c03080d80800040d43c1c010710120740c03550004050070380034606125500300c001600292039100d0700443c201140c503d40b040c094841c003407021920451030384084035107502944145 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 650670818 1250 650669568 650669599
    0x1c031b080405120c01030501061704020f062b050708091504060e0a0506090105060a030c0603021809160f0f020d08040c030c0e090705010203190804030e030601060e090c0414 76
    0x140704607000143c0040e6000c950b08122080081c0f1024126800d0f00c0600850b0380365002214a160340040021108080c40301140c050b0408a10401a1500c080c103418500400380b80c03034030180d00040390440f051440d051840f41e000d4200d07101d000d0300842c0602d055051800e000140396500c3c0d40d02580381d0300c03503444080403504000065200080c0b81c140b401c1580d01100c0e00b41010b540703c0c8002c880184455082c103000135a030340307400ca01c1d04003079a80c03000080450a0921208034001d400000310b150b445e041d02d11100d503065a40140f031621405c43c0300c41941c503815298800403c94000c1c0566082802003107000003815540202e419402d2442c1481c11035a40e564900b4010314982840d40041d010509491000c2130003203034400020f00c0782059104032602c890781d45004a80c2d1341715031100c103942a598690001802d51040c141c031074006000f440c3c540c1aa04503c40084c2c04d0000aa10500214140340074905041c14104206a4020341054132507040c10326000440342c01c0a0124030003445004140c5007d00e5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 650672068 1250 650670818 650670833
    0x1b12150603021b1e070906051f0201061e080c0117220602030708010609060804081803010b040e10060902040b1213050706030504030908030315010f020307020306151c031b 75
    0x3040800303c01201e68403480f000b20f441d944a81d000c0f10604070300804e4800f15600314a401024215000a0810b0720841048890742c1c2070180d040362500300715500d034240010300ea1070758545104101d0607402113442141c07403c1c00c540d140a5210301041e050001060714041ca0050f40702e0b50f02c0c0e218413070820907030b1542d80c22046100640c0d81d01e10018a8a0320100c03d1100560b071240b034480c1a1121074503503a61043c0c5900081d03619070340865009007102d20412a40d00281d4030603940c50300660000d00045005000d0000140503504001203107035141c3d020300140701c000b40b540c1c001ca40c0102440c1408519041c1131900306542442025901860206884041148200c8445000840c55001029580819140e0300d00074041d000075107065002800ca41d80104094074080100c0e40900e6060b1a01c0f00701056850040d1510b188180d814000d6020130320207180583ca041c000701f88105480684001c8031761070941008800800211694054620f860300c00340020741000c5501705500041412840c005124504204c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 650673318 1250 650672068 650672107
    0x308090117040c03121b02041a2215050a03060504050a0b04050a02010306050405070c0b0c04080703030e0907110615061e0c0d050901020d0503040609061b1215060302 73
    0x4a03850300790800c01c01840382d941600f0007a640305500c101442c90000d541101c1a0011180f0030410310746a070aa4001803425602c044000200030301410a07060600c800180041500d070f03074602807001b4403801e0448101251081c500c115440c4000c203c0c19508100100f07560b0000303400001d1102c0d03601c0000c10240070b0100002600c06521854032110b03490103107050340d00c60202c11800c901081c1083c10100304c0d403510340034061040d101640c0c0d450021350262207100d403406005c0c182c5030102600b00408620702d101800b560000e107001b615264004020304040c07141c0c030303803005001501700106080c02c03205d402d0000c21840c1d0486400c00007003417414018000510070340b01d440ba11071303002c90001120003000307042040035000c3c4010300030982e0b13616030103c001070314140328003102d181c01078011404080b0044c1c020405181c01c14041d40001a108200355149800c0f2241c01c01d4200080b0149a0301d048081c0c3d0064444406c40c0b10f510040c412001c0094040b1181d1181c1d020784414150042003030080c0042840540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 650674568 1250 650673318 650673347
    0xa020c01080c0d230126060c031306060b0c0c010809071a0d150611010c092921160203040b03060d03030207120e0a0e010f0b09030322170c01080103080901 68
    0xb0506540e51740300c2c1146d050009002c80f088400d03841c50501c49000d0120310039210305045540e1f9440e694810140d04140d030041c0c04211002551030b4008075045c0c0100c1c02801e480340b490740081c1010881b4400240104500500c0d2003d10382c0405010302c441022104010300102d003607100981c540c0001500f15015115480f000d038501780099100151007a440070040303010031f010400810106610440c201d50802040c000c0c01c40c680c0441000c00020501079005008801c400c900c1e072401c1210105030f21011442c1180d00303841c402c40364410300101082d00203560002c20a80d00042d45010700d0b10182507010701009200c035100c1c100003010b6030709040c000d0701243e04455002c85940401c506118000c1e008081ca28a401e0082c40c122801203041a0090340d00d5068490f4a0b0a04864034034003e03601030f82e5405449625090301043c8120998100c000d0540f40350040045800c1c1281402c00c02882d51030b25840c00b20185650001d0756820040c0d81001307815041d0398110b42150f5403440c901b00161403011108404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 650675818 1250 650674568 650674631
    0x30b1507150207230106030c0503010b010c12030f05040c0e01060f0e101b05011506090e01182009011803030804030e03011104061e0302071a04170706020a020c01080c0d 74
    0x601c61444c00642c484000c2c1c91140701c0202030035854406150880b100380407030301d0206074010704140126102c00500d90840301707a0700d004140103050707900d03c0080c0c4000b07031000c40c0d452105110500c1303650101e2081c01d0244c00285850b089440002d8801000060400c60284c0944003001942900c1c900c290041c46640304040c1d0081884450b5141070780c004c100082c18001d50b41c0ca4101c3c0450a58400c01e00b40f004c942c00b400c101007640c0d080800008044484a00310181d4541d2001c145a00603020040e101e101c03000d0f4200903444412143c0003500c103109140600300c1030a880c0d00b041c8002600400c589801941618040d01e040044a010034010a21015107081410b8081000103010303601481140348c051880588030b00c1500c01800940c164021054010304082c0212a00500030021081c2164400e000b01d900171810041072150070200d6108010a1712034680004000c40c2c0d0b5901004442038000c000c2c03801100c9842c200e4101031b0180030343c805070907400e03841300e01c0c00c05404210340141e0f079400c1b0184074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 650677068 1250 650675818 650675873
    0x2061204020a0503031c0e0a0f0b04030807031503081b011b020f0d0806060a031107080306040e06071b0204060812030601020d08070203030403030b030307060507030b1507150207 78
    0x4101202580445080784240648400858542008130a507540184000121355031030009548080c041c001c940a0701e90240b01d04140340000c20207901105d140b040c010070f610b0141c0d0500d8140203003070341402401e400c10305003491410000d0b0740f42c0800ca641169007280c084c64032001d075030390380c04603480901041040641c01c0c0343c034841025445a000c0300c05141290201d840112f0845136564950410341c7c028000300c0c40640008076181001c0307004012a04940c1380005404806c0c0011202c40e400503030003a03840340340c00301c00c014460501381f040400d411114401824289000c00008005003040003503404000310f424201001c6480d00e40201018142c10415220324103201c4852a62603001100d401e4014881d0312150480d007405040d9141c054022540034529554403502c0960250003051080c5416100801c0f982000c030b0322611805004415030f076030101e003681d004010020b41c06180e180c0718103101c50800c1024000b032031071104150100c03041000584c60354850300b406070054140d01c03c0501d03424400d80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 650678318 1250 650677068 650677087
    0x90b130b031e040b010510180521060106020d11011a060904060506190f090f030305090111011812050a0e0f0a05090a09030f0e090703150807030302160503030a090905090102070206 79
    0x4e0841e8141e603000d4500b20109502090f04440728080f44422803c2020080c000b44068107002c0b1700030f00e110216a402d42403c0880300402840c0240c02d83c040320058100a010f80d59895210316210602e1a164000f4848560314811948200c01c05680b990301c5141c0001e501201a150368200600412000b00582e0710f8003040000c00c8035003004059140f001800444804c207056002d4900c01040c1c80c4841d8076030030b800c0d05558080d111a403102600f18140540100002da07043d03400d000c0e94240c089900328072034000b21036141503d1020350300c0041006110b400e001d13002c9080e901150102e09280b00f00c030740c440f1600161010400c807056030f41103da04200362000700119101c3d80c1e006800880d10070b980720200b8140012084500c1c1403048455135012011001080c0306510907046403074019001c0051400306030751010414601041d51303000f03c025030042e1a4181d4020003240c00d910041a00350b000c1c0d482d00c4a51107006100c14482e002e940601640c034400b02c0c0155200b503056032280c0c0c0d40034000d01c3e81d400c4d815 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 650679568 1250 650678318 650678333
    0x11412150112112109060406091a24120c0118080f0d11011b0c060615020708071706190204080a1a07020c010f0c0f08040b0703090b130b031e04 63
    0x40440ea030309640c0e501c131484442101c0124458200039018008a445941d6408054024450107507030302040319007581c00d40e1041c1c140c4140180e8220103102c501440b03048014401c41e0b4407c403400c4c420454880801a01c1c0404181d90600d09024078101000c0480783c03040c0d550304041508a000144560199440c02040006c0e0400c030700c0d60152503007404c403d100e0458034207840300c00912218951102002d1710883e030044501d00c429504c6a5804100203440e002505030f0074a40282e9540180d0011108100407070060080e00c0c0509510a1b000341070740344040116a540002900080c400307001103031103001c803000c541e064502a14945043e204001d101c1d003000c106610309210a0580d5480c07607408194007030300000301c00e544000e0685442d07084654402c03007510345041000c800d5850990800b404000039446000038405054252075890f00e440080c10000c00d0402d080d00302084040b4104001d46e80480f00040e10307000c80d141e8034a03441e520b5846040d400035034460070740d00e4803c48030894140020441c02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 650680818 1250 650679568 650679577
    0x1005010c0c03050615150406090626070815040e150408040902040e07030b01110d03230a0504050f060912070312021c0b0f0109051905030f01060501141215011211 71
    0x100c0d11109101b0754848800ca0f644035512a110108884010410180d8090076400e0090070755113503107404081022460408807141201da000024141201704a02c041542551b406200300580b810801662010350307142d603518015400e5256280303070800240c10000100105c07400b4180d0310382d096494640e6074512503042c001c20750b50b10020070b0414070b4483c01c55204070360022020104c500100441e20440f0029401411311000d00c81007000c0e01003c240d0030103011a20a4080c41e036020b00021645464180182040030404401d406500444144000d40b003001031015204040710980c190f54284904c2e06070b4015070f803484030032070440c0040f42c018560b44090380350304407a090780c040030b0005135410717810406440342c1c0f032140c40d01042284000b072100d400c120070b203244c5803145030102c040c003980c0303038130009180102145c100e5160380c0d1203410510095078440032681441d0f00d03c10006003090f001040000082c0001804074002c060481400c9042340c0c482e03910000e0200e08120101701320900901c80081a610 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 650682068 1250 650680818 650680861
    0x71407140f1e19051002100b04020c060f0712060612060b0301121e02030a0f15020301030305091918020406080f04030f140f1c0b03061005010c0c030506 67
    0x204000c501000d4200b00d4041e6407010b407804202c040b0032689404210324098144120070300c0c200c84860205058950400c0360328040c8158004100a2100380c0d02e00c001c1d528903e4507103004a0061150385d45580c8000303580d40d0040c14490320600382d6990041c0807214070160000c0398031600d0424400094058129480c4a0402080380082c00640d440342402c01d03191200b803255003680d4040c10b2400002c2800c211400d2280e1100c48150307a504940340d00024a000040c00082d9505144c40807200c0812440d10003540c1110384143c41541150300d1500c025141e0301a80007c1401000300c01040410382100c4001c40000e00414400d012081710002d44450003500240140d03404142c030400416a034449480c02e00344070b5a8140d503503021400c00300c2c0e01102d05071113512103020840e00074020107500c81d258a0140031901e00508040c14000d05440d403200581d00c0c20701d900b034000d8001030244400350183d10075007070a8410a007001302c0132400f1031420000424040c0c0c0040c0c000e0082c94184001e15240b07070001e524882 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 650683318 1250 650682068 650682079
    0x30b0105010305100e0718030b0901050624040506070f060603060203060111070503030306210a0303090c064806200f03040b070c02060d0c080c07020f0607140714 71
    0x280c0381131000e0041d82c800d000c1c00e10002084400645d656200300384440007280428000c1c0c0c500c80e529511095010810307580001c0b01e03511041080500e08102000c40850b00d440ca000050070500c610818841e88218000c09005e200e001910700b0600000707000105131681c0c030885c2003003690780d207081c210b009400550300c080c002034050011554480000031003205440001b4040c0d8a0b50302d5080412100840c2e101d24020f4101461040121402040c040e0520950207610b000c203c103402c0f132508424240c1c1c5a04180103200d030070525071058000d005403206020701c111401002d13034000254141c2011041d2409050600812040728041040d15000204200c50740c0b100c65540c10304a0b01d85003194060030740b0501c481081400007a0210395964070301c5800403d1800d00d0324840106401003440c65002c441c45280c40e94031070104602c850340c007414450b888100307150088d0078070040d540001c400400a030070940c0705c0c0b80c010400c0000d1003003400300f00d490f00804000301c0304030036519001400711482c0d17a6000d03807041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 650684568 1250 650683318 650683321
    0x1603030e030c0310052205030a021216060c1806090509070206041203020a09050a06051206040203090a0204110d18030305091b040c180b0c010510060816120204030b0105010305 77
    0x40c280040c2d4040c4025004000e48860034130b000d403242c01040000d004030b941c071000d4290440c211048204031000680a540036641c1c2d001405030191524211801803680d50500b00041c10078802d9030301c0503401503075000d8070102e4403604400080303950840d0140710046c5052108000220240c020040004440c8107070341da04099030301c03050180e8440070b0869000c0d000b00c00c1d83d200502803510a0f402000607200504103610255210b101060000d003440d000400400c0b40041d0301ca5100140b5101d42c1d074055000c460551461030001030302070b00c4080c5644001d02407034807100b40d00080d042c00d409a55182043c00820082103071218003a0090601c5210140c010a1504002c80d50b5442d0108d100c1070080741103940c84040f0a600c0e4103000003080c403400c01000304000c1c2804c104100c03403d10591001401081300e02070321460780d14070840c21504090045002801e1036002000701a40014403680d222003205141e008a180302c1c10290384120a527040151b01c40c0c40040c2c00710400040c90342603410380700203907010000c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 650685818 1250 650684568 650684597
    0xf0504060902070503250f060f0e060405070506130b0307020705120d090b0705010b15190806030a03030c0203040b04080106060314060d0809012703030807050f0a03110408160303 78
    0x403849124800f5101c5e80003000300c0c81c0f60950b00c400001e14000700326601e060241c0142c4070754405012000045990607218401c00f9914100350088409038041c0310080d05680c105559090360700d00c45c500c201c5008150229107040b150030b1110740a0020401020b40350354908d0b0420f4000d490b100e040c0649840707450306061f040e043c0c40000170b02c4600b42c40782e6210241c007141840c50302c90031500444021903241d03486108000b01c503219034081524208518488544800400c039600c030440a040c4105000c003c07400c410001d0650300000c5120b02a509400c0000c0d541e09141012410740c4115080040c842200050008502c401544080202c80040e5010440718200380c41c0001208002c3d00d07a564006407002c242e2021900c04d800810395003005050264071142082160b90f04106814102c991f0503640e1033080051641005071a94000882d103001440c2900300e2244070b60a000b00841076007055501d0701721800c1542c040c0c08075009130420604664100e01044048810010940000c800040440480004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 650687068 1250 650685818 650685821
    0x50f0612030307090501120605062a0114220f050a03020d0804020d0b2a2515050c132601151a0f0418051614160b010f05040609 56
    0x52105544c64540c0c4034549801118480c0c0c40480380c035007082c1d54030800992680c48400800d03a0014015603c00329443c0380400e41d2199100c05800f0030a45d042540f9030100c1c6c8007032500c050388000c4180207a800c402c0c40c019901455207107140010b000c003544030301410a0040001d04040890722a90844410a203908022500d00c0029100250803404101c01040002c1d030a00d1030030ba100030385511580403000d02126420090300c0b2140d01c41c40603280081c000c0020849119003040c2c1c8030200284a100348400d40e210700031090138060a4a000e0741c2d5401180300110780c00100c2c1d03949109241110025a1200e1803c101d940b801504042c4a8a05800c6554a82d4040c0a00101c8031030114002c0e40d000e240080e41000011458010540004c01b00003001954a10b0000b400241842d00d204d046400208460101100c4010348074803144142d0300000c01030710f40d201c16a041d2440410039401c0d211210444001c0c096036004600600907201c6100210300304429500d200300b00d900c1101c062003120740d105007890 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 650688318 1250 650687068 650687071
    0x9051e0f0d080601080a0b0301230615120417030a0605042a0509030f0304171203060a030809040e2e0e0d030903090807080a031e080f0712050f06120303 67
    0x3400b060103000050090760003003001c40d0707000e40140c82c0030480100d008002802c5422690b0040040d808482560901008108185a11400546c0d82001051025026180502410106c5202c50026100040c20005581001c0d410500d207940b4580d200d061140414014140341c0c01078a000390315003498100b619108203683d44950074050740d400c8d0760120046044034103900c84014140c040c441e5403009464440b00300014030040010480b211032091b18034142c40d050041e07903074030101d4104060052003110381d1501d840b10304580d40040f08070303a00c812040100b40502403000c1c8880450140301151807034544221544132800d5100c41101c00c1004000c04c41a00311420300e45021115070190104185640c002d0784814425406030401e8070240e581d6140301c514020390b175000605030f80c00c40c8a03088201a0880701c4aa00d1035800c12014100f248508030003045000010140301c40000c003103001c41c0a0394061498801c8444c07001c0c40601040ca4021741481c00a10103403150b500460151400d03d04002c400f0056a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 650689568 1250 650688318 650688343
    0x30c0a090306021201231f140403140d050f09010f030902090405011a01051305100e031f0f0605280b0a02071d04020d150f0204120309050102010c09031509051e0f 71
    0x7400c01f0b5034001c01a4030074161400380d40061110712a60511100b08440281c8002c510031000074016000801d8003500340703995803201d181801024012202c40695800c290f902d001ea0a10707040800482244045000d08031084001c0e401510040074442404019000084000220400f010781100031100445070351080b0200391000710300501060065150201c020780c4003091525050303184040040000c2d0400e08804541800d01c43c80740c85101c2c032480f0f01c0c05500c1254840103c1044400c2c40c0c100407030f0854508400c00351142e120b401e80040c0c6007044070081c00c06001100f0095032180100c0c140070b0341d9074030766002c1c2c4400c4103a5a4020640801c0b8904218806d40d4050440640e02c6c850740da8000a134030b5031120b04100302d51690801a40c2c0d10300d5202810081c03038004902c2e5049022420007034070407109600f10341d04590522551040403a001000700003129030001c0c0980284070f41e44c2d100b2000b400390940060180c045c40c0a8250601d41038040f030b1600440e0001942c08402150b2690381e6102005a20b1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 650690818 1250 650689568 650689579
    0x909034103011412011b050a11060106080114031e0102070611030c07021215251701050d02030a08030903030f0a06050306040b06130504050708150c030c0a09030602120123 75
    0x2008a9410551a07580c50304004c9000450044548850400196002d100340800140045821350031a54480540b00c00380d90030102410b07155040440c0100015414050340e0603131b003455200510a80c0302007261840150075030142c4c80c40b0600c1e00003140d010358445142501d030b0a08040700c071125006c0420440e40224101c000f11482c1103001e038240305407180480c4d030000440c0580c4691009a00d001c068041c4540e41e58460103000c0402c501c65129444910300481c2c0401003408001408400c030002400d055500403901115150007500c000303890118a058000d001c0c002c0881400f10980c00040550300501112000d418954bd610a031203040b5442407144a6056010002140200b070364408a55040a8090b1608404c1e0210414003000e554041e101104c450b07000b40800c01c180c2c003060200040e83c184860800303845080138070b031900c0c0724000039244c0803615900240340012103002350014001950b00c1001952110203e134140440190244641c40c900042844040301c0401809012076640030b00814 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 650692068 1250 650690818 650690849
    0x1506040b071212060e0711010b01200705060d02030708090a050c2707090303030f0b090f0703021b010b041802131e0908071109010b04090903410301 65
    0x102c0e08018100c900c00079052010f220b00d881a10781c8580603000207020450a100b0f0f41c1e0801306001090100383c1c0d200e5000e564074000205802d41c0c0c0c072082c0b91211003074003a045107030382400120003414826a48e000d95440980043d06070071041030b54015601c5440243c490850b07903a200491551600307680c0c030000305103821600095409261500caa109940710b0b11690745120242501d401e51001810b403640d8011450410003041016454050803c0c1f030100c0b8501440740400c0407000c5140c901d001b45c00c6125203503980303002070301c2c03644030798180c0e10b500308010300040a1041c0da4040c00e008110f04400d1030b00890030205240340b25502c1035039400d407555000d000c641c1e004400d42040802854011154200482c00c103586a810000070300801c03141501800351542d40d54041d1800400c401d50b002e12050203003400d00c00400020207100151002c42c1e00303000700820346010b6458101c4150701d02442c140c90456849000b0084c4840300040c1d01d40c04d540e458000045000d4120401c01c0c540802d2141801e003810510 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 650693318 1250 650692068 650692073
    0x50606180106110a0c180605010914040b040e0616090f0b090105031302310902060f132102040c030509100207080c010207380c301506040b07 62
    0x14403141001c0324105441d100d002980e0744440811680c1e10920300d801252401d40300d124443d07c00c1c00002c010900f062580c503494000c81d41100400085102d00c0b80390303074200042c0b84d5102e58004040b0b003400f54054840c80d1402542c6203011003400781ca05e50000d10700304000318940c070340108e61506449801903440c0c00d00061000440c0c0c40d5000401182030130360407418110058030f500986184507840180b4130400143d03203022134405035265400d90035220f81049025005602d80e1002c6401d006010204203a03120300c8140000f06103500c5610420300001c2c0c9403c3c2c070242c2d001c1e20f120a407045100303c0b014046101c29285c110140c60741541c242c0d190781c010703001610b90300c80d2030307402481000d110341d00507801d10f20304515250891b00070420699501d518915404070400f41088909403a80c0c5540746840040152100b89081c42c00040456880700b06c001500380ca0b41c440c400344400d8500f550080210008450300c00440b0740ca00035990008251008403515000d464844169810b440c03c041c0d4907410007800d85c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 650694568 1250 650693318 650693327
    0x30322170316020405041103010507030218010c0b040326070503010311040504240603060614030c0d080304080306060d09030e01020c040903080c0d061a193f0216050606180106 77
    0x6d002201c200414210504d1b03552800c0c0076440c4a070034140c4005841d009102203103070b0005068014141000704c5040c000c00090740d9428450742164040c070300501503900840301e02a81c402c00010500800d1000801c202c299540b100065040e02d00c2034184044006081c018001500c50a84d0010540303c64500f0407003404943c3d100808884403070b07540100d1170503580e031076240880340e89800440c0882c007807901700ca00c1800c0070820b6260054081c0c4041a9401c9152585407640c000944014141503000001c660303596500000da031301070340d00c81c20108030a10051401a044001c00400c060141c050260364051070314140c41a030780256015107405a56548003160f1440c43d5018460000b8402e50b01d940106032256a07013004c904262049900594401e0750302103030000e03002040003103c02c011443c0d0100542810b400f0b0141b94202225002491400ca45200015030480903012016624404a0050090b0150500c9038000034003400c29a04c40d5141c2c07030b0501c001400c120039210749035607007100100002c600c1b4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 650695818 1250 650694568 650694571
    0xe0f0402040b061b060f062b030c060204060f09090209030d1b06090803010e01142b05120706060b1204030c05010e031201170c0109050d02030322170316020405 70
    0x100744a04d000620015266110341d0304050341d0056101108000f8003410090410b5040002113070803610550391128040580401031301101840045c541c40d500405008500d03150300d040c0d1048081d9240c1c0e40303520700281201c0000b89014002551034000050003901ca100715800d0b004081c0c043c001c0aa40403405581d003aa0071400340c01c3c3c03248554120004102144600041036200d60312059880d494421301c160790b0712042e00300394200d503801c0c22041c01c3c0c0d984d10a20460301080c581000c0b440d056046114012581d0302090203415400b8180d038241002400700003c1140c544500c004000003038598a840e2194050081c0d07490754540544c02150109000d01c4100300d40511420000c50311070070051800741583c100c0458100824074900041c007014644182041800700104028080b200455000034000c1a03036208041c011503101c603011056403400c1c8216515503540c625508440c0d49141c86170b250440f0940705030f0501541a80c100c1508240100c1140c2e1182034580e034601c420394140d000c000c01400f0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 650697068 1250 650695818 650695841
    0x504151803060506130606020d080a0e100b10080103021008060310020c03090108130201080412030b0406153b060d1b02190302070b130305070315060e0f040204 70
    0x94104040400d850600d1280c00914854000803c880c02c02c0c605002c2d00c482c4040e1760032880d900340710b03041c00b01503400103802000ca005840d02c1d480d83e840da0403140d401001c001480700640d000d912500c5200070007035044032810300e0782640c40090901040300304030f507161300c20b00009600a030440440314400c0d1180e408207420031402429a417501e00080d4515007282e00c07008900c2011f400100c2c07000c08642c0c0007103519a004c0f10700d0928900702c0304643d000030000c10005100a110301c403010002144180310340d10141d0005400380082011310303198407040c444056059a1000062030300c0704c0340d41c0240c452150301d05c02c0d540304100b4141d4410042c802e800c01e03400c1000c030b001c1d000003090003207084114090148914941501c0d1603910080c44c0f0340c40080c03c00380c1c0440c100003810b15038501240000d40c000780300e104961040c0708807512008052000d036200009684040c00c548120800401481080504864106120b880410466036210078180e402d65089500c162844584000100036003400d4220307142544 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 650698318 1250 650697068 650697077
    0x80f060105131a0c061f050409020f010c1415061906120e12030106080a052202121e0f010e06010b0a030213030b1006080f1012050304090c0302031f0501050415 70
    0x54030750000342c94000c044403540468503030407006d071002e0401290602c01409080e01c00348461200fa030081807840c95074000c200e0401103000c00350b005001c0e411502c2c60320940164152115201c8000c40000a0031054411a10880c81c101c070125041d603118211f002244c2c0b086c0c50302540d8541c0211201d00915039400c042a1900604007142408140d402c000c602030201030712a00700d10b00300380d44d840c2c08070ba1005001c0c0602c3c01072152990f010947c80040c1b0080b950b41250090b1404901004050030320464000064032102440c010700e407802004580340140c80c0c0d4000003000b02990b8100341c4c0d62745042c28072660902d040c08100d070000e203900c81d070010900d0f000a82c10304200c15990b665500d04070b0100300c80782c0d4a0041032070410b10607158850910354000b072021a000c060b0381011a078021035111548140035140100c25082004c228003031060324000e04100f041080444034800001d0f010398001c456014241c1258403901440340c00c8690040180ca0041c0c3d9404d08040c201355815200d03003803541c0c00c101841f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 650699568 1250 650698318 650698327
    0x1f0905030301170f06010e0c0921010506091f052e21050f0f09100c031a03030c0a08090301060306090c03120819050411060307080f060105131a 63
    0x12000c200860080070f540b81c169152a402244450900b0300d00e100030400c54114900400071304100754865030700411045a0b00e559000314000182051031954140400502440085009150107601c05031290b913007980c80030f03200d9665429500002c045a420042c194100c1c40040c040341c1000300c01241036990519000102403d200c1c0d103040328200740c00003580010700400040880c1800c400019403043c0c0040030030f114504001d48022001c2900070000c04408200300c3c0001c01007041000310000c48480030300100030007440c1940c024060550444405101c4164081d80c44117070800204032000791a80c0390191640030b241d907540b081142c0c000b401c100e40c5592100804004560180304d0f00024600c074200403003200c0d03d145085081d0351749103458032041c00a41401c1004031156020175405034102d00b40009000d940c0e078903002c11640c0203005d195800003000b1041007110b54010002c40c0c0540007050340744c40c40740e541c1070044a00b441800340350111002c070010108100c450340160540b54641108003141031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 650700818 1250 650699568 650699573
    0x1903030c11180702011d0601090b010311030408190c021f030b1002100507051c0906331a041211100f08100b03060f040f0c02010606030b060a021f09 65
    0x82e07128548907580002c50106200030070384c0912800011202c00d40c081404032858901c001c0c1c840300c05200392240683c650581f002a42c0c400d03800aa001007510450b19102c0c00c20b4209410203030440d89400003038511a411055059004200000031141c0c0180741400a5000d00082e501c5010b004040a040c9501e504c0840526500d610845181000f143d005101e1081d4294080082c1c0342e0207003500c03092000400c81e01c000c05610120003507a03031804a40125501c012450130000801107a4040d00070483c0d01c48124100f03134680707892040030501c0709005500079a1641a00c00310b102c501300c86041702c062708000402480301088803c2207098002c243d001202e10058000c85e01e9a08904000320000301d840c41000941038100240641048081c1e51010002d404c104008240b0310015290901c141150941d541c410307511500000101420a4414000500c200d180a0301038109800b070b04001c241005d01c0c02d0003d0a0040546010b128142e0080018160b604184c1e51180a020116101d55480340c880601 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 650702068 1250 650700818 650700829
    0x14040b0a12050c040b030d050c12040303030c0206070212160c0905070806100504050120030c150105031218090603190c0e010e1501211401141903030c11 67
    0x4010700c07028504041c2162400d41d0800c41c221102c40d02c518a0030002400d542c60000b4400050119811305170b0b034411070710758040c7c0b0b4000560810310460340c0004000c82010381c16041510740c07604640842d0081c4d01c5001c0203076103400400500c400381c40014041480810601000d981c90103001d0204064801d032283c1907181030312801c45a07500419803e5042c40682d0800c00c0400d21201c107185810303400d1031705160000700740440c509006507080c4d0b9016862046080c052080718089a101c01c1203512250549041003042071013403040c54072901446220000300a40207084074583c0401d000e0b00c0e043c0c08400c81c10008042000352040b50540304a07840f507000e200780071a086215900441c01a9801840c02600e000580c1050700a8100c0030246020b10000007842d411555400809082c1041c1000d44511a4040b182881c03941c0c1081d54105200b01250030b070742403400c9041e2a0111410b0310811031000074013640c0c480c461240b001141030403070b080000c644030300c02d2401c0783d900c034502445011046038001030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 650703318 1250 650702068 650702089
    0x201020a021f02250c080d050a030203040c05100c150204050607080d060e090105010e061e011d0301290f010801030303091a0c221a0708040305070f080d1814040b 71
    0x50416001003060130501481e50003a00c01070080100a24914403054001004e0340a5514000c003810303004008141041100c445030070150401034800e44805184000081440420700c400313643d94049191102500cbc0b4090084a0980d10702a05951a00c10305940703240d20f80c0c0c80030112a8503590344540100b16400081712241c0281980c50002c40e55505042000d85c400d1005406213210701d98203500398041c031030038001c0d01c42000802d0814000d084000b1f0b0805924007100703001c00d607065213045d40010001d05480d21043d40f010030007a0180c0c800881d4424098400c01c100040c80c0813401a000400000c1d120750003000c0d000e031090172a00352001601500700c1844078181d076292044940481d008100c0702500d445c0201d800170340740c14002d00618114840c203103030041d11442810220001002010310820380304a50086070300c107044035a065940d41031310b014171046010b80406030103802039029050b4130a0700201d030166445200c0e41c11240c948409180c07170a102119042c0c0054460103000119a0b408030102d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 650704568 1250 650703318 650703367
    0x2090c1b150f040201271a25050703120c0c060908060a050f070507080708040609030b0f0f270105010b0306012d082703070209070201020a021f02 64
    0x1c0980c2801d00e00c10040318a0014001d0350100c0520040001607a4800c004048a0341c040c11182d0100c903071081407085071907543d04010300c52603000700c038801012000d1000b040840d111000b1500522002c9251b120010300b080d1014209521002060020541100ea02001d03042c86050040c48103410b6074815080c8440c0e90b01c148003080c4010020803813884113000080c1c0c405c010a10420030707494a1404080c0c02075010745903c041280200f041401c20620500701d55a5540240c4515169036442d800100612450b00045030031341e140d20089030b60340010100d5140220741c0c0c2e000c407130583c2d42c443c501050507043c0b2401a0f002e01d00d403203030340340c0c0d1107002882241d001e400c0c82d0109540e00d29000d000074040a400c410481030900b40704104020441034008038550700d11052801f0b10098480420f45006a0000044c1c11080580a1201c0b1324036a400001030200c14401d1b01d40703941c1c590f204101a07080340190301100d00980c20040014055422101c02d21003043d250003401810030308880300c1d041c01c42c80141e140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 650705818 1250 650704568 650704573
    0x130312020a060c08100308030a0204030c08010617061009050712020d0b0108100302030c19170f0c0d02030c010f110d02060a0e010c090303110a021309020a051c02090c1b 74
    0x41d00a002181c00b40c00720440c01803c0c880b81c03a00300340aaa6140c110544009044010040003080181031580c04507801180c0044c20f403401d00e80c0701d84c0054024a09840382c1c804140c500400c4800f28000403c0581c031441d035000a01800350701d00034a84c0d010380030060a40040007038002003c1c960b0411480542000a1040000600040c480002504c108405004540c0c0b41074140410001a0760015a80502e03c42c160f07100c140e071408048940a0340151608035181580d151034030b21003041c50003c0c10410403070410048441a8102e941480310440e14514043d402d41c200f03c0c0c003400a5406441c3d0300b80002d04c249411450720714210281130a080c040c00201c00160000014802c00c100240208030701203402200030465000b6110001c4d040301c56500c0000c0520000d8030100c4c04003071091100d500c8050300074150000010818091400a002c200f10880c402c03000f29030082403a0520501416805006400d0b1002d2a0115020041d0241000389942600c1208102d20b0840c0005081d5030036050611200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 650707068 1250 650705818 650705833
    0x1a040e04052d06090c13020f0c070303020f10020405060406050c16080f12030c1c0902040513061401082104080d081806090304060309030c02090c130f0b0f13031202 72
    0x580b03810044090a8041d00f58001068200d80d99120400502450000800180c0e24044031b01046802d005001d0300c0d0846026004d0000f003070540200c0c109c565030300d907002680c0520040c240054100c0c00f0394051680c004005110920285000c1c0008142840c140c0b01103940c80700c16200a0350311014250030218203a0000166802d0a46080104052034500d2400c001c0c15403810765040b0455003d003600712400d001d2201e19800c40003800c0d500440700c89401900900c840d00c2d0541100c1400d84800300111805031815101503d180a100780300c07410390b081c0300003130021101401440ca2150044200341d100440c0c0812000801c0d00082202c0e4a00c4121611281680d141070345900810300300d4a422a101c0c2c3d007100040060110000c0300312000c0e90106e0500140210013418111141500500002c0d000f00108040c0903034201018050000410828807040e5a070b40c07169025a061000f80c820740d614051b0a2055a03021107070100980140c400405182d100c2c0345c1d6a40780d00803924440075141300560080a0b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 650708318 1250 650707068 650707153
    0x3080405010e0402070b0601030b12060406020421050706030b06090405040605061504060c121e0e030c0d1a06150a050c1005010e06010c030201020c0f161a040e0405 72
    0x202810360900c08030f40441c00c0013081d445a0f1080940100b010381010381d100e48171480359031841d80e0f001255001c0b60850790185085e28202c00254000d0290441401d91100507010541003403c08070265648070700501401494508190050141038010b19886401440481d005032581c0c0306a0b4400c0b40504808102402c10b44140308a10302e81461050b03000800f00414461342e908040001c1356980c0c40104003400003688801100c403401c000744009100d4044101d2084080d030f210f508e400e03000394100d00350303808011260304000003061150b10003418100c0031541d018400e886d10140c0c2e0387c0700b00007600300c1c00b180019664541559200c00007201c0800c001050500b0760780400c115a1a03034075150300c0304116550400d00070f881c2e10b240081c1a0380c10088074103d4001014404c0d010b55101038000011540841e52251906032540356241c070075580000c0709500000c5924060006001441280d840d00b0302e000d0600f0b069a0024600500688a5110f441e030341a80c2e005843c1d44174800783d101034003900104105103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 650709568 1250 650708318 650708327
    0x10506040c0504081203060d0209010312081018020c0f0d0c030905030c0603010e060a03051e100c0509061b030d0e01050717060103020d0e120a120c0c060b06090a0308040501 76
    0xe001000b0000d0a1005100070900011000510081d18202645aa4440300012110b0081c181c4c02900000844000020440c28900f0300d2010307503090310750100556841040601429031445801180703001c0140082401d07403154014002c41502c80142c45c0e030b00d410201c590f454580120300b003000246c4841c0504050540c8106800040c1c40220301406001210300b0010b25680418042d00c8180100030021030466a2040e01200086a22405907001d440207000e0f940c1e017100381c00030500c54501803483c104440310598894950070000648805003804545001d01c00103800462150802c0310560040c0f02c070560301000640080003c0d07070004903881c0c600045e101d0960b280a0444405e0140d00700d0f9184841444007507013580001d00303290060721900540b407800040c20042c01550318600500040040c074003440c2c401480c0c41c03040f58a900c0310301240c03000fa003011101c0c041d140343d00080d40b0890f20800611660800715003020b000348042c0c14045041c00207000d000d03080d8400c03100404005410051541c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 650710818 1250 650709568 650709581
    0xf030c1707080304051c0203010609240f120f062406031a060d09021e01080106090305031e36010c02060d0b0a1502010903080609070f080601140c01050604 68
    0x31025050582c81c142180e55280140d0051310b201c0c60241ca07600402e20084190345101301e130020007e00103a030351610341c3e0307005282d4000304414200c40c01040900d0541c2c0806550b080390121689440c0700c51505460b4a030005240c03c040700e45002014240c00407a200e4007400c1c4803103401c0c0c101101a45501d00505008420703a42c40b0006040c1450854a007661030601407030000035041d20b60079514030000c42c03000300400c1500002540800700040802006403060304160460b0700a0300c40c214541d1301c4400a44007681d1511009000341d000b003054012900350803010300b5400e002404018106501480310320b00884500c205810a1040308082054490410780c100011420a09180090314115008100c5d24490000c40e9110aa110005042c06486007010840140041c502c24107004582600c001c3c0030349603501003900090f4101003c6200303803910082070b0307000d09040c0d2500d020b40076810b807040c0c40500c0300400b0503040c412422022036805031042e00401c04804031030000504d514000301040200c910 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 650712068 1250 650710818 650710859
    0x4180c0518040b07030e0f160e01080304181505040c020c090f070c0602070804050a06050318070e0f070c0b100f090e030405060706021c0905100506010801050d020a0f030c 75
    0x40700d1081c000071811120300d85401c40303594500807902d00300241c00307586042e50000c4d007040240b003030310105210ba21401c103140c3c0c19a400d04e88600c0032640d9a5510315541d0099019803142c08040c203840903040605c81d800450f0140103110b070124826078901c001022169098020310158208260010981c60451003003680315181410407091424506401800600c0e8035500414180d4009600002e020051090320000d00004101154003070f00e82100400682040d150350003500200310614410040224024040d00c2609070b48500d203982d02d0003841e607424400740c1000c0034814090320b864041040b864825110b607142e00b00800c1c1c2c2914015851416070130079400f0590131883c00c1101301d654003001c0101c60884800322110307500c441e0709003071050082c8038404480380000403801044840140e290840c1460502800c29900e0060749030036213609039181203a4032800a4000d40043c0702a1034011030b451079085c0090020f9481d50349405481849081e150000d03601400d0b0060104108c2100c144103060511 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 650713318 1250 650712068 650712109
    0x1030506090d0905120708010507110f0a050606010e060706090335041227050f0d0309050907140304080d0b0105130b0a0e18060103060b0c1b04180c05 66
    0xb408124024090b10f554020148034403440110142c000f04100600c0014040d000020011405d00344c0c1c0140505500028004c564051500881c02d021000300d020005180c1020180030942e403036500445820b0f0400c584540d000c40103129460103c2c03214460031440a11071307100e4140b4212810601011034034208152100403000800303651180500d205074030b070401d0380035003404101d03d5880300544126514070300d44810814a0f40c03010110a490405800c200c07501550b89200c8003240005109a02c0d041d9800940403601c400340800149c105036640c154040c0007444c2180e007400c04402d051140d94001c1d24152a4220301007610200b410f0107105006954409082192800318801401c5003001d50500c200e0b0303221400404c1d0346200314003803186640041300040c48003401101c1e442c0e402aa00030141c44507800246404004500c014815048401c2038640100138008040d401d4204040520300000c55500140c40c1c0c0744040d12000940ba09413046d6104280102c0c049092005000e400c452031312140d01c1302c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 650714568 1250 650713318 650713333
    0x5040612021c030e030d091a030603031b121b06070306181808030705031603050105010e12010f050f0703050f0c070b04020a081015140121060e0109050103050609 71
    0x142e0b40c0e404542c0401e00040b15803a1203a82a00301614080c440e001c145401d8025a941c103403215501091203001e5138109003002145010311071000c40caa000c101d582030b030594402c101815040702000503130b5161294070700407503906042240004410390442050002482c02c0c0443c6c429081105000f69944051035190420209180400c0019081480d6910b244210b0340d8403c03c501d0344030402202890b0680107021207a490805e48001030155004451031407402c8a030f510002c441d140b190003994100c820594075400d882d440c0204000c4003422619444409641e1107806452095081c0620351061001c45503140d440d10344a0070260559400900784030444071080c0c100031200d41d100080c1d8080641120724248170780d1f01c5e4408105000039a0b00001400d200e40c0700c0004400030b50340c00a680e090192520321100503560b444001140ca0504482402301d0805050640030103200c43e8854130104034941c0110360381d075450340e83c0ca0f005042a081002c1481d2200e00601c1480020090302e45c2003c002001410032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 650715818 1250 650714568 650714573
    0x10e1203070c0f1103070308030402130903050406050f0c07081c020a03141b0a050124080303150607060c020604020f190501051c06121101020d2f0a060605040612 71
    0x1207036108004111007041d14010040c1300d10324100082000011341181c0c14a030b00c9081140c040d8000b154102d20580c4c81c64003010038000d440c025500700c0c69241c0c0b03030f8500306400d01e802513071103801c0911350644040c002c0c41400002031007007200d0f42c0244919400f4001841207022181900d909450720f61040d54460b002200000b5801152410300322131191806448204511026142d45080c3d40000170034800c1f0240300c802d20406611003d0322814070401c1030390061179524401000002d0b4411150035800600002e90711440400b015041050020242131404546036203100848001d0001200141d1056041100314100f210000c6c0c6003040c1150010301740202d410881c66152134a0041d80e041080c00b05090076815451400e295a50031103040a118040d00c0d48103c0a081441100580710030f0300c09452480c43d5400480c4285100d0f88a40d2203032010b00d00880550807840c0119044000703180684241200d0038000d21103088140d21502c0040b8809181400304015030702e458121003601301c600750343d5800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 650717068 1250 650715818 650715827
    0x3031103010602060c1c2a020c0603041e02030607030507080c040320030709061805011e090504080f070b07110309010c03031817071403160b040c0b0c010e120307 71
    0x9005c0c020418460b9140b440e864201e24980086035800c80703060614215448155a4001c10780740b4429040a05100105a41007245d81d88000740c20240c026504001080106182c1d001000d542d902100b074409002d102035020070706d0440c0866814000954440901084640c0400c00035040841c1800032030520341941c840807a8200c85120034400718808001820660301d00740079010040039034401c200144c0f503032081c82c0e800040288a840b11094035060000c15081c018408103c6084d41501185260a040240b00d50042001402c01d440f0000140403981800d58440003c091007441011a50030a081181001d00100740110302500c507a0010301c400c0e10b517641d00400f183e41e0550549008201c499020704040d0a007201e1160203480380c940e2184e08511008100018583c4178031032a44000c0440440000c2a1240100c24001302010b102d807007054041900c008180d82c0003030089003c0b0b03a120340d0700d4100a10315480000303003013030b145d440360400346100c03000384003103020360480308142072452405038030080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 650718318 1250 650717068 650717071
    0x3061005060a0201200c1009080712050c1e0118080a1b0c090903080c03040506010b07020118030606081207050d0305090a1a0a0b0f0306061c1a040303110301060206 72
    0x600030400800d000310224401d41066510b1022410302d401d110401105c0d4420944c000f0903180b500e841200940d5141c14814800c1c05407641e044182030381002545d64401d03c1510386903400c1070411000b0300c40440c036401c00f8440341e02c2c3c45420840240e80b506d80c1c02c400ca401d44001d211001c040840c00001c000201d20717100e0890348040814039100000150100d2455040e000d06074000e4803071006400301146c5c9800380d9101d100780f40e000703485541c40b030742d0740c040d00a5043c801154000d125801c840c00420520b040747c80035294042c814140080303c00712599a42400c1740903a8415100240c440748100050740082c40700c1c660040b124468589000041d0301c03159541d10b10074001808140d034407000240f2a01c1d06008001c10031380c0c00031100c000c10021824800c035040d800c0ea80d0968161400c1c040313000c54a03210200340c0325110060080c040325078441c1c0800400c00c0c003840401d4841d400c25041280001c2d1030301c00000d600300d00b5007080105402c0a04005080320320844d401d01458801f00010f010954000400380e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 650719424 1106 650718318 650718329
    0x1d01080607020c010807140c0105070801050d0c2102030d11060105060a0c0b06190e04050f030405010815041b031e111206040e07060f0806030610 64
    0x45465038420741d40c100160780841401c400035405624203503400ba0803070030000c04c01c1804400700c0e00d4a5206501c50850750355507000300042143c00c186034601401c81541e800d40000d58541d41c0c48101c45d40ca0080c11000700002105505080c89103448034000e60b0b01405403240c3e00d4031060042c1a852103408440c02c0741c05000c00210700c50803d4030030b0703c4100341c2c00d40c0c80d0303001e5070210780318a14000c00141c03000c1d4020050059240604400382c071000000c01c051004c400641c9018203140e41804880c61069400d601304200400981c0ea120324035603000084032f1000b01c603071a400800200108130001c0c4034440944d000202841203601039121956044c1c90b8601602c081c3c242c3c00840c2e0407520703801600c5200110900600d00c500028540d5141d1251024000240c0e03500240100d619241d0b15038400c400182c0582d400c40c810b9940640c0d0260071071012b50041c030302c5003007000d001c1c250301459010f203 = true := by decide +kernel

theorem cover : BRFrame.Cov 650539568 650719424 := by
  have h0 := BRFrame.cov_init 650539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 650539568 ≤ n) (h2 : n < 650719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
