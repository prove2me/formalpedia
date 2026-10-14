-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3686
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:23:11.035744+00:00
-- url     : https://prove2.me/submissions/224905e6-444e-4b3f-96f8-94365583238a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 662769784 ≤ n < 662949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 662771034 1250 662769784 662769791
    0xb0604050a1e09020d0c031113090c0201150b0327190f060e15060604030314030a021308150a0621230c0901060e01080c0a0905150309010f1e 62
    0x54940b15120001c003580503292950001c9405016617456600020341d40455803020000259030702240c481074041d6807410309020a03400410401c16020390400301d04020148000207020700c60010704c2d200c03050545c006280c122000300400411400504d900140341c446c582c0c280804e4030315403811560303820101c0c0700020140c1002d40d4041c200200100c0003200303030790f11030b4080c00300100030240d155803081504009100312a0f00340204165080040031a01543c5d055903482c0758202402c088045594000b4201d007072250b90030840c3da000000e41c508180003403c1c0060140403004140e10103a075a5140c0900b04680c881d00d0b06600700501454a011042d1800c401c1c2c072640400d11080c180070b802c0410407400264000c0000c2c080700900d58000c1410862240c0481d410119079894180c101e0b81c082a803411240803c6004004c587d50300045800741150504601c0c214800c943c5500100c0c4c906542d0005240b03031800048141704031503600b801901e50500d07400c4001c00c0004000203441a0000c081d0040c4a9815034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 662772284 1250 662771034 662771069
    0x3030314070912330c2a0212070e1801060911090f01140a0309030206160c0f0807061503021201151716080604050d080903040e09160305010c02010b0604050a 69
    0x8200458407240741100314a0420504640940a00041000100043c18448450200150b103562155001c0111441b01050703980c1542404115080d100c0840054030445500040358566640100d11400c43c404290b0207030ba0215003c2803d460543c4c0010401034100584041d52900d04c600340e4144002c05c6a80da00d080c161440160340d900000380203001e09860004200d0174840e0141c0100d001944213900f20350313060391791244038002c0b2095640391000294100f140c10011500c0f01c80030461080c00b070405207291010550f145411200001280c0c1c020390302c0701340c081095203400e503030390001010140001d10481402104500c95413009005110f901d12200641000d400410000508008140c000f10300c8202d44411f4900c1c2d99601c116000c07031303285c0b0800c5030410307005118400d540e000e54030301c1c4019030405007415a010b20492004040307131f10300c3c40740d002e140c0f001521305480740c001180550000280c1c000b07902c20090035103a400c450b00b4003d84d0304000401c2240c13541448042103510b0000c681c0c04603003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 662773534 1250 662772284 662772323
    0x3080a020f131e0b0306090a1113030b010e180d1d0405010308040302041b090605070317160906020c1c05030403231501050918070b0403030314070912 66
    0x40c82c024a4240c45440d00200303d1645058121450b4220319800781d68150341d81a82c807949100c01c0790a960000900000f0941603540b940294140108418265090850040041040102c1540150b40d000d01c8540100b1110401c40c101d00c0c0c11a4503140045181c074118048265214005140c010030270040201841030140700940302d0344a018014000d00c1b43d541d41f41050200b58000340000c3e0310551901911141450000d00700c18447c2269440c3c480001d4903104060f41e003500481015000d001c2050307184a09045c5105215210b000c03800c403104107030700d0317641402400840b05030006400d540c020803106202e44c1d40d000303519021002c54201541440007515000b41140903d0f80f00516400b40490781405845a980e0360030102e0034030f41c00300e641e14540400002d050103801c4c03203000d810101c0c0e0f8000c981440d044403146100c0721842800c88142030350380d0442c040560b00c641c1c425030020783d641f601000c1103028001450b0700001146001d22616062070258840c80c0d10f0810010310321000c43e00a4030022 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 662774784 1250 662773534 662773537
    0x122a02010e040e060a0b04020405090a051003020402030903030a050601050405033013080c040b01094a0a060602070b030406150609050102010e070b0f070510090302010209011b03080a020f 82
    0x39070180c401d210441030038a80b0b41da5140140c4000c0310a50502684521500742482541c040310002850903a8685809405000030800501500f40030200c103803010001d40c403640000e60007100c0300d100450f80c0307280c960444012140068051410040304000c00c0199030350014000c1d5801035810403070348080e0708d00c00d09a441a9110800c23114140c10118210007a241d01500481c101c4000c0c41c107031500d4880380c0341000b00b00c2d1180c420312404124aa201484070444506201501c030885031400701010744264032415541c24000e030005001d04e18a900050305250810049030000c5a071281880320718201a0701a440388620300440d000a41c0220014052050a811503483d105008800304209901e4244c02000340780300d070003003030f000d03608140340c501d00e40c1d40002d000310481d401384100c5070521090700c1e44440301c4d5002480c08c2d00d2030701c940c00304d80d5540d01a501c034902081d446900016580c99022001609860f0008201125a80e59078014004a504032000310342c802c00078400140e8136160502c0c0804103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 662776034 1250 662774784 662774807
    0xa050609010b0d2304030f090f0e0703091103070e100e04200102031608040314061003030f051c05040b010b04060e091e04050d0e15090607060207150603122a0201 71
    0x490248030b0134081815000052891f1901080c4c0c1c490b012a5200c0f011011510007910816072030000400011340460701c41e5208410551203580c0c04205800f640e000649801d00d16004020800c00403c20300265805c009017020043c0000106909a85030907111340c8502c1d015000307046000344498490208580c4284110391287d0a50408000c2184213814101c0c0e0303541081c08111041d248103c902d031b0300d1420000d086c1c1c0c420f907022005024018119601140e10388003070703030801c0280180ad0010503d100e441c007144a07030faa041c507000003e4600c1c25081846450302e060f40030342d040c00c40801061150a0740031050b04880a000d5640d50b60684401c0d0b6411488100350b0340d0a01e0004040c420301041200120b822412408180d503010150045d0b1802c00203681c500e0728070003400220402c0020007a050410140550038040c0f8401810103071180c44885008440003030020000d50f8400c002e0080208004640640120903e04100c1703505401401642c01031085542d01241091084840e045a208040316240f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 662777284 1250 662776034 662776091
    0x80d0b0d080901030f02071e061e1a060c060c03190905030c0708010c050a0c11151207050a0e0f03010905010e0f010b03060403020307030f02190b0a050609010b0d 71
    0x2a01481400c1c440c000c0d8008141c0d0500107400c040d040c000040a9000741c580007500316604041e030400d030b8114400380c10b200c24401c48030b45448901c448401c0ca942e11480c80c0030540070202154203658004d14410311587e82901602c118424805100d11210000340c0f00e900c11030003240c0303990b03d4440200768030201007a280360020560414841c0010000c0c0031014080305c0c0641411030360343c0342d00d85031681d0980b60a11501c0f000150148042d83c0c109110710716182d81140141d168401010016002c81c1d00941450b40d6122410030001d07081154046801c0055806806441d105051402c46c15004110255100c142481030781d0b01e51464020f0b6400b0740c40f1741315055005d402042403800041c4c5058403a04607000c01c0c6559441d00010030b16a05012403000d01c900c0d0f0650280d89026003039038050b1100c50640383e5400440c417070f5803002c0c043c0008a00d40c0e10007241c043c0f40c07000464a044c080c0b4005036040203162074018010b54004018007001802a40c0300e0981044000c19400115002503d00a031010303071140d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 662778534 1250 662777284 662777299
    0x10f0c05030a09030317010803031b0c0105090a02100203030105010c06021819080f013303080a051201050f0a0b0a0e04061206060e040507050f0f090406051602120304080d0b 76
    0xe5220390480b83c0141101d1280d11181c841c3d422400c1001c4003031000f48240c65950b0420000101c0010000424a0000c0303140c10900d410542429255401c6030f004582c0340303a007680801140015441c149003528070601492005615543c10400001e01c0100c0009004101c10f4011480b007160005d521000d103150b80c40130b400405800906c3c02018081d00d043d100c0c0e01150301480699070344603101070099aa00000201d0140700e160f8404000c1441c40c00a40809201a080080c01000190600000704240e03a0b0700d9035500c1e103e0704000c0c1e108500d468103902c80e92290200f400d124001d51030307903214441120029240700352104044501a14441407140394168007a181c003101264003115a95030313510380da01072042003000c1910780034562500310054074050455801000c0070403e51070a0040c840851300058000c128940315100480c00c4800203490403240f81c2d031074404000295400ca828007420300202e10003404000c036075001c00302c00c6102c040c0000d0982c00000454101d4094941c10150710b1480291449 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 662779784 1250 662778534 662778547
    0x50714010908191209030203030702060c1c0519170f0a0e030403061407020303071403060103140708060102010c020d0903061d071d15090105120c03010204080706090e01060905010f0c0503 82
    0x280e4101c030082c1c0100c0f000b0b40c0c1c0310f03c0b01c04605c0c82449000300f6260f01500a5140c806907400300081c682000c0c00304110f40c03084403001d01c89420b03030170304d40d49000d171164035040d4680c0c4025218558440e900300c1420104150016089420015048907641210344445001820703151100c00001030003682c0e01403002c174030000400100b008100d510440000c13840401900031506c41e04070403a141c2c8000e4540d0f100241694207110b001418590045401c45014140000c444940994110004504643c0400030409034010855035580a004024001005201601c40600c1d00701c00074003166840c0c00f000d4021551200700c4d00718144034280e121074210080040342e451643e038500a500040d108600c1d0081100e070741c8042030303d01229078440c0801c043c1c01484045540e080100340b081d840c2d82480b086161b40f0449401103581c0c3c03028030040024041d05070280c602c0c103041c0754010f010303a101a40302884950305032004000c00c4d81c0c026410b00903282d003441c14003040940b200c0308803042d0010107000ba11a00000441 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 662781034 1250 662779784 662779813
    0xf0510050102011a010807050a02070e150310060b190e0307121401020a0e09150405010b09012a060b01020f01020f132913030b0108010e0f0a050714010908 68
    0x141048030026402840b82c2c603401586510301031a2030442c640407030400750210301007602506c094020800280704031001290f468844100448058400352000c4491555007116420140010480d01c96481424002d00b40b5041203032960384030310042b001076201110003a60107603129024011040c10f00031308641009880d442c0d0940c00e004050700850703003402081030309000e21070180251801c0621035120301c20403400d04414007200482c0280b400314200401081100d2640e10340c480d40f4082c03e1509041c40d2510919000946000b02d4882200c02100044c0c0714501c200c202c16a1102106500c80004180c1c06020320041c0c2ca0710441d07680c000595400070854800c14000480508a04120400d5100c9005c0d691030000f01c01d811801d6180100303140e42c0c04040c24080c440002007000000c10840d0103030b416901d0322050101c03202030b00800b150381d4480680318401e12040002c20043e07101e580c060201c5410035503541e640c403c040e100302d80c2c00071585a0a21641ea004203d031f00c006242074810f0310130b1400c51014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 662782284 1250 662781034 662781061
    0x1112010e36070503121c0b06070c0501080606120103060e070812031b09060d0b0f0d030504090f0e0d03111902010b012012090609100203040e0a0203130201050c010f05 73
    0x29a0000744640400000c6078076000400034041100440d8003454080d26030400807064401d11006c41100d40c03181c00c1c0c00c115480d008010001c8070b0049003016840b506200c001052414040d10040c0f00c0c01041c8240008100100700683c11261301a0000811001e02200c1d035082401580c0003000a02818110b020a07900c0c12000390710a2180e091407003842d0414900e00011030041081c0550407500c103200016103000564014468010001d040009009154000400c40100118201d001507408a8100b0403a04d8074000c81d003181913006400d00c0040e10112060343e403500700c040c50008041e240c4004d5940d500b20300f0102e900c1c03005610780524100341202400b034042c104e00070f82d480c00030340d9880e40c008581031120b05a00c502c140c00001707001482c400200400c1f10b40c000060050340200100840c03110380c0c0d81c0180c250b0f120621038015545443c07900c55425040e1070010110040035004008010700c1110305601c50050b10f81c2424220f4031200e1001169004201e80346c0010b0b5100c4c605414403c892240c0007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 662783534 1250 662782284 662782381
    0xe040201110732150304150614090601030605100302040f05030105091f060e01030c05091503030301060c0c050a0816060c0b01030602030a1b0801092427051003061112010e 75
    0x202d8140300c07c0c00c2105101162020710407440c3d88460702034588002d181031031076a50405414036003c1200758540c030018414805400c500c002096000900b0400c0c0130a43c0302600041c04124002c102074036107402c203643c5404459203401c00001c12500148451150307948810054002181c44c8160b5603103c0c6004103035240d6900801f4480c00c40f03500051402464080d125440c50009800b4508691801105442d5000e00e15800c58403d0400100800c40c1c0e21185108002880750000404c43d00c503041d02c010b0303030600303040c2c104034100042003d1075804200c0c010b480504503a0b0040d030050381c99807403400400080c0349420b082c41c90034040b8040004807552248409041ea03a180900704122050001800309487c6030100d186400ca1a03900c0401c84d400925070314501c50402421502e010105a81e4620100c0d8000c07200b00d182c90a1042d0140180400d170b1161503061a02000030629001910303950100e0b003c01445009811440c1c600024072100b48d46c0503195501c9130f06584c403040104090715500c04410a40c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 662784784 1250 662783534 662783543
    0x30408121f092c0304122603010e0c0306040902060a0309030210060503100b010c050a05010615030908190306150c11090f0705090303130e040201110732150304 70
    0x405001c52181d14520401e6010000c061a4440d40a440601403e091200d0885107080b80801d110000d120780307041c18200107003441110210455040c56500320403100580110358200c50381807005004503003086c406187c001c8442c0801e180c49036152000900944a0588001c0d0820307800700b69960802d030141c129072601c500c42d4098914a1244a281d501103800d64880e00c1c1e4503501c2106500a0000280d11450300c0c00c2c0d042c0b60660500b03e268403100d10740414100c0440700b40e95510001c200c032188034603582d0044c0c0718a04d000d100b080111788a00085001d100c00010310980090a480787c00f60183d805100103014074000500f5294403001c010700102e4241e44146c0d020701d0604480182441e10b0440c541c07003600e10f84030400301d945400b802190540c0103051400e402d0300c030070406c0c11034454004914000a08007c044c4142a161a2000608201d0603500c0b6003610f03800f01d4410302c51108240c504c540c10003000e107000f001c10005c0d101c03260101090710485540024802103441070928200d0002c52049005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 662786034 1250 662784784 662784841
    0x2a240315010206160c02040f020304080c010e011b320406121820031207050d0e0915060409060602030405011b05060103112710080a020f010503040812 66
    0x3001a030300c07030b0760407508984420310001c0182c0510303014020700d845603400613000090302031301101000c00f05d92040c0c4003510403440100d2010440c078024003600a043c8000002030104a4907880ba0040d0000500c220b81c05202140b48058401c02c0003d018001c846111759003480200070b400ea154030283d004e4068880001c8080c2950b03010400e95004049841d0260741742043c0141094541191407070705140c0e2030f01c84418510341810680c3e4100b090385010342005820940d150240d2820310b1402e03010080c41b0040c003008486100c40fa0741c1c1c40f400c1540c001c0001c1f1800034607000b10300000d0894401e07500418541440d040000c11101d900001410942c1d4080e01c42c1c40c0340200e2280304900c0001c0150700100503070b0080c0010700c0010006509060703940c0c00940810728040703000c00c02c4911a07050b5401e01250342c00d2281041052013040300309100510000c005800c58500a802041d44800c010030858140900000801c0801031800125840204075952403c03850414011056461203615640113a0a07103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 662787284 1250 662786034 662786071
    0xd020714150d0f05010906050f0a03030f02030c030a030c1d0a03020f060909041406010503160605090a0b03040f061b090e07091511070b0f03060d080c01020703080402122a2403 77
    0x46c200a418040b274002000c0c000d900d80341d6a02200c0041c001d600d10411804140310a05a010303042024000305481510b01064211018000420714070705111903043c601001c6401341c019840341d06071201600d80617103003920000f1203c00407a50920442c1d0526401c403032040c0c2084140720300010f110765000300715420799009990350000c060703071024011003038403003150043c030104002805940201210301c405402008015911070080440c0e8108640540c2e0399101c801d40101000018415181e00c0c0352503480a11741000940701c0105032074010701680e503040b01179401040d821809546501e0040c044404401070940c05640d00611f40c80407a558203485100341e0101085040041040d00c45e2800c1d25159182107590300d004110242400030403d440903001080103103007054080c0001c02448d0f00a0300d900120741460300c14410b0031440808a104241c00007400003005400010101191008034140d54400d24101400140d0249084080844c0c0741a001e900f51081a10040614803d01511140c14410007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 662788534 1250 662787284 662787289
    0x10e041d03091e06043003210c12090219030507180917031003050d020d09080a0506040b0a0e10091101020604030806040c02030409021b0d020714150d0f0501090605 72
    0x303c001c440382ea8400b0052200748030106006412814186c43c01421800d1020680020071810f41d040f8410f40000c0c49005541c0e1345499041401891000e031200304100008907024010155064407806d00030491f140d2244400355921070340c600d819000101e140c603040e25500c1c508035680300c0c40c62080c55800c18020410b4014581540b160158842e04170a900401c0c2d1000003045030340d60b00040c0070301c501002c080000310201d03008006465a0303d0598000f0140789003000c001404041a0703038082e038141d034064030044000480200303000d60040c0d84104100120748800910001401d4030084d1900c1e60310840141c0d190406540c7c00070a040743c0142c07a0280803402e01c2e0012a15a101204d010b030204600c80c0100b00d5600303041c1c0c440520030946106607810300703488080c4081a6806880b1002981e080440008212113060051491154140c00108410392905504140103503c034440b40740312b0a620100c803141200d461003103808405c201c18081100300d00c00c13003280d0010902800f860307100e40d2404201241b9030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 662789784 1250 662788534 662788579
    0x1508010608010810020307020f061006140c07090b03100207050304051215041e0c26031207050f070501090f051e10050a09120c030e100e010e041d0309 66
    0xd0f100000980019603481840790041d510103005c04085100c2e0300d0507035013041c01c18801c04d8001d0349183d0f800c40d6801e2601c2802091034070542c100d06c141d00410810b16201c018001112004c80d0104c28005c18200d5840c00060704040d0030002913091355000264000c00c205011000b80259002125000c1040745002c94003907648404c41015042d6a410501213030214401c0c0110700740f541511484510b61f4000d665035104441c0e52036010700f051882c034600c0006200c108000c0c5552441807040103600340000301c109000e1998001d81b0f55000c0c13210004510250b0042d81c400c69400b01c0c1c000c00240b003810780c10724100d0404c41c0d9043e0141c03034034011415103400c0180e80c450b11842c0b80500000600795120a21500300040c40013411a084040c0d5507a17000d00000c81d407505c0804ca071b824985520025569606014183d40c49029215212341e0000700000021a08440010000317402803801452414046002c02c00074418282840c180703044900010f950f4510000050075511019500f00f40209214500400740c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 662791034 1250 662789784 662789789
    0x120c0306010f0e180d120f090c14060304030230031602070b030115030f0912081909080a050c010f020c030408010b030111071502070f0309050f0f1f0315150801060801 73
    0x11600041900c80e0407500c41c40f190000078400d40c10000b0580b18280d1f448080f20035000c401c40c1e1548801508010640030359a040c032a10009403400d038514a41030380c0003901c030f070200c0001d0310900451030040c040c3c0810203900103c0d8a00c1404005640781050350113031207456080e40300c0b80018454400e0101c0d00810307641c1940c2c1211f17210450303490700142a00b0260003403c00026929201540d0310301c40f1001c241b001c0c08030020b6210945440d030319410454000e10312031002e03031500f4600504041d40d00e40003680480440b80000301074075002e0b4840308007031426400740c6105c409c070380782050000c41d0b02025204003000420440302a90000c00c000c090640600d400d0390020700200c42daa03034062040c0004203003415980380240200d0358005180102780d40e528504003041010550000b003510030280705e54145502001c400d0402200da02e0845031541000a08500710718113102c0030030440031002c046580c001e4200f12111510803e2044440362250041a040104500d030980080c440000004821380220182e42c107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 662792284 1250 662791034 662791081
    0x3010608030322050102180909011509020d0902030d02030309011a0a17120a0e04060e0f0c221e050a140609060d09050a0c0b0c030405120c0306010f0e 66
    0xb55a10500e1100404038244610354084800707000140025100f8030003070000340c156280812844a8a00602010540003000e040b40350307240c034542d1490561a0541d100c125030100c01c0160b61107850760400e001500040500a4040c8501c584100c402a0040702451150100c1d6000300310700700b9041c04000b01d80d12900b45443d040010072070140802207141a44650181c2514101e5040d4541c422136100341d0381c090b040c88400900f084a454640f890301b401481c4c01421041f01c540328030f0504280075650a1809004d5809490000407040310040c840700603040101d621458020303815036195041a80403881510b5406003400f400400314007032811440d0441039072081301c20903014014260a020305a844800348544c010307010310445a1120690245186852041024114201d020724203000c941d441500180c40d551f4040c0440101c1580c00415201111b4044030f20320311140622160908081ca500380c0d09406004007000441e03440c3e09011306400310b5144042c9510345648124500140483c60003c600c4c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 662793534 1250 662792284 662792287
    0x40c09051303140a090b030f0105030c06090f041d0d020606040608060907120602090901121421070204060801090b0708060607030507140c130e0c090108060408030a2c0c0301060803 79
    0x35400800d000250440d103a0b05d043c8040880d03100c109608a582089a102010f40d0701341005011071709060007003030030984003550400c2c01c0c07554510010700c40c03910740101580035682e503610030f0002c403d1850050010540f150295001140c050300003e44a005c2210140c3c02581171120000e440440021824401c7d0505030243c0503240c01c1081c0c1d00c0d240d0141000030358006402307001c100e456035034094509000b0300d09141d0210400c0141d00d801624940221186d0b20241c005560780c89040708034480384600c0f90b044450301c4d6601c04851000400915040c0c0150030b1541ca030046800c2086015070341d060203032685883e551919941c482c10001c0c0c5100310386006001500601251000841c2c00c0300146070307a00c2c4d403010f03034070002070440126800c0b00d8101e00c078100254407400c1e0000c50303c405001110a5040588a0391515810b04403100d68550300a0700003052080000001600841640d001c000c1c503c5840440c0346184000818001403c11030b8030420125000e1038080800c00d14052040008841d552809107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 662794784 1250 662793534 662793557
    0x2040c050d0e3c01060f091a13020703020a0501150e0112050d2d050307030e060606041403101517010e15100506030c0d0b120601030803060f09040c09051303 69
    0xc5015000c4041040f4060103283d0406070940c20a000d40005425010580350055203030490302c40940f4180c01d0091450b106100b8200c00b5905d68050f00c4440711200c140243c0d4400c032030326089140c144240c50140c03581d446e154041c060140c2d5241c6980407601401c0c01500f250f40c0318405458501c405080040040e40032603e0b03ca1401d01880c10520580c05003400c040d8030042d4403860900d032981451550300011400001c115001d03415204030241c007016140105101c0c0b91000220b00305203da40280c0003448694541a4100d5804008081428001480a102019010001c20300100d400e0041446410000c1c9580101150509c10101408034446c020031803042e20a02280c1483c1020303182c1c6085440c4000089556110400154003500702e501c0307669a52104542e15100320f6450404580c8141c0f1030800030030b582100042c4031030640390402001580c9407515400039082c40c8081c400182c01c504284108020301111480010884d40b0000051065940704c004a006a0180071802000310308000d03040c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 662796034 1250 662794784 662794843
    0x1e03071a28020714010b04060906050609060c120c010b0a09090803060d020127050307060807021537060b0910110f010203042105030c09130902040c050d0e 68
    0x1d08210401d921001480c00042d81ca9251054102e0503001c10f0580d111110b00010b81090b124a90080001c4881000640e0505000607064170451041601c61180820a040900402e0010940c803800301013401d80c1d2225204500fa01800d90030b0442d074421242c080000450b68928003030854816408030020303141d60707a02010800c0c000c6070140243d04000500500310380031520900407560840200201030034170b514005c10146800d01a40000041207500814020116000600302c3c0140d059801154510342e80c074221a0400441c0750003c0c80340d8a641b010050700c0c5035418942c422a9480312009000c2c0070b81b500c0c0403111503c10312000f40e4201c040040c0c020b0502e4443c03070000010840080c252a000100410003909a030429181079030358036008055004020008014007140e9080350030002c1c01c6181440b00180c4500407030307400703a000e87c1e810110001d8882d01540511012640240f0400c034000030f42200420a400140c1c0b408070f074901d850855203c480000801d541c85c040c00c2c203203800300c03507042a84 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 662797284 1250 662796034 662796091
    0x909070302161b08010e0a020f060703030902061603030f0b0a050402090406170d0813030906031d060f09101a06070827010e0103020a0906111e03071a 66
    0x4031078601e0b880780d12600004402401140f0040200d0300e000f1802c42c180003081c0d0031258048188400c1e640417011450040e103848030700245144044642c9130f11500c0b5424140d000d0070319044000e5105000051303481146004400c00e0f032003d4029502000321000311800407007207581b09904160300c040c019034104a540740c190010311600710040c0020803996902c0f80c02d040c1c0c5c8d01011508419a401c20b1744c001d07d0166000c0b804543c81000c041c44401700c0300d055100a0142442d5020320070400d611001040d40b400300c2030307000c41c480368455811150759240c00c0407050020982559166100d005440200358a454070b03010b1074002481c20600d246a2507414010062a175111207001c55040d4402c1c0441d01c0d5984c01504010940010400309610311822040014100700890060310b0505105010072041d076544600d05e00103681c0c07103090030201e408542012a203480b580d5509180700d107403d10002007036401e010004d40a010b126916520f290102c1448070304040074121848805840000e461010000e007090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 662798534 1250 662797284 662797297
    0x30201260109020a1d01170a060e090d0f080c0f03070c050a03020f060603070501211e0c0e0d15200a1d010314070305041104050c0a08010816050103090c0512070602060901020909070302 81
    0xc00006803d68ac461402c031410004a07214a446d80100c2c0704049001d4100d20f02515144492800924030324104240980500500c2c2e000600120044001103886003d600f1320a0200e400500301c80e42c41c0300c51320b0700035581c0720290f02d011510701412307011074214100010b151064078016100c580140d03444100d442d0a1a03402c9450356665503c0d01580e00240e250358202181e00e069941020400d0902d0450103030002202c00c440c2c50080c0b0780f0a102c40045980400c0860501902600209003103480000402d1b8646a480d181601c1a000046110711150002a03003118048501c0341e42e0348002206006400302c1d900702a00c0e0340b4044c0300707070001802c40d8400d60103d54420310464101450700905000700d011600212141025a1000164141304640240b4240d004007001e10051846c03507150314010305141800c4c480d8505064650303601c4010030111350408000760102515508041884c00a00c554070f0005100340c0002d4002c5001080e1388c4141802202c00d40301002d407100b074003a140c0000840017944a00d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 662799784 1250 662798534 662798551
    0xf03090a0b0108070602011802060a05030a0b0604150323070809160f14031605040b040b0d030201051b0a090e060d0b0c1308060907030201260109020a1d0117 69
    0x8030000001412120740180a800c0c1c1c2001442d03100c1c100741000c1d003140c0040c1a00c041c20144884450016900d1104990b141d0540d40381007a1031792900059040079189168140d6031103100840d0200707030204400c02d81004140c0b41d50342401200140d031707481d00c00c0e030126002c12480c102c010f07400a000d80740034440407034000c0c40c002c048074490146224451142001d40c0c02034640d0442248080180f03203048241c01c5a00c074022006840d00605510201644203c0c1d881400d000c3c80d1079824600031952290300c01d698441c0d01900550b1085150f2600038001c1c0402c84d4140c0030110984103607101c09030320f141a01c2041400707480c1c2200280c280300c01900962001041d555102540004610010320310701407090140140c0d1200c07989031350b11251020241c00c00c3e50451103c1e07500003400c02c001400c00003040b800302c0342c080c04d01c1400310001d502c0c102400900103440e040140303500b07000050016502e030300030840600306540d54440c02d01e43e04140c40b041f0056214403030001c0d0204d4803500e0380c1c06004516540140c0789 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 662801034 1250 662799784 662799793
    0x310b03010f05102106050906010224060102030913201303060b0d050a3e1e0a0803181c0b2d0f090601060c030f0c2312040b0f0309 57
    0x2410541c132140342d014184810301039242c002c10070450514204458010500340003030120890b41c045400d4403020000c00d464500401d6801140469000380f00b140d00c0424050420702031220781c1070400b000b51070b903030584400c80e009001c59209442e042c14103031406070784501e0002040c10b01d075407510001750291a550940c00000c001030744000403810003c2e0030466210b0710f0761440520743c40841c840b001030b01c1e01e40ca0095800039840304081c02c010301d50984115508842c00390b01352030540b60501010344583c0c94035800050703041000c105c00d41e0010142250501050100c44c8541000f400c0c4660b010071540226141c05a407006500001d1851032001d80c08952113601881c4a920140300200d8040da072114404440083c000380075000c001e019100d9408034000c0020112545405401030a9410f202c2025040000c0da17185c1310070013445920074400040e04040a02101c2000120106002c00e00c014580583d05c205035841044e0312544013510101d413445006181444600d60090101d540018a040c009005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 662802284 1250 662801034 662801057
    0x12030c0f03032c1b010507020910030219090e0a0c090504060f0c0c170405010c03050318010f0b010e1002070603020d32150a03020d0602310b03010f0510 67
    0x2642c100f4010094501610070b66040c40700e5400743d080145520440510b05000144490540d0700802194010340e419100601140c1e124a5802701c0880c503904001c2d444090b0b103038885a0503103482030b02070664036600010040420300982c113039903991031701d60000c0c0400f003600c1e000c00c0021500d500076540280201c00c0440c00c2d0381311006410858541103092004124150000020303c807410118400c0011500585450305041c80c0000c0d020800c118070017000c000c4008001155003151030010301e4001ca00e14001c1c44142d41800400028040000c8600e0008036140b020582c5072400301523402172081550050305201c0d0a00c4d8044020f5807004105103401a214130442c8418050142404654130361805144821241090b2102e03540300701929080c168143d0b0280038078a940d4603001901140d40c1200da51000541c10319140c0301034011020103d0070400c51445010348880002e0881380c0c4031401d010705104040d168500400140028059000030700003d6005004034100307000c6c000340381101d03420301104611 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 662803534 1250 662802284 662802311
    0x215240d020d08030a18050703290406092a050103020c030403020d050601030b06060f0919080105040b040b01060f05030402100519030213171906060803121012030c0f0303 75
    0x242e112004403002c200010420408a08503c80c00c1500600101480c0c1c10300301a07116169200c82c18000640100c50819609803107480403070b1a240c14003e000903905291a150a08000809042d03100b591184812403420030780103114500f5030700c0504400d080a01c420309001c0114000d4010710300c04540c03484204000300c0507030350b962076172100e0610a80050003550f040d0302e00b00010490140072a4040c0300c05018015082c041a01a24854a8180e03504200340c8402803824004007003950000c041395103410103003c03d004120310514811030150180c46d071076903039610040792040544480b150002c1c800b840480d0042c9014000d40e00107a1035450120706014401145115800382c9600036030101c1c3d8001240a102080e40285400030130004280104c03071400b100c58a0388644022850602c004040c190070307010452241e1022014003244000c880e124500c40071005900c4105450042f407c80c4001d0740083c1c003080000c0d038141d00683c1070f580c0e41c02e0300c1c1250341c07002c2c10441000f80403002e140c9c032407500c00080d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 662804784 1250 662803534 662803549
    0x1b120305043e030c0d0b0a02120103050a0212030c1902150417010f05100509040203150106030207021806060a110c190e0601092102040f020f03070215240d02 69
    0x154200711000c00e1250b02e001841100d0151107070300d280243c00429205500e541c074002804820f64004500b400795945c1d20407100c00900c684030916a412001c08000300500200043c9214800c1c4260f0315010319600903440340380e980c06240f030100300c10b6000503082c0c1c41c600007106413500100d1002d0010081d18500e100d94840726042070300040102074081288800d450300034066458980e41a40e4100708030304000c1e00700305000d40719000300c034004d145a40100b000c40d20100000f114081c8840362483c03555849100090203584204400e031300c554105156031503102c061000050003050014101071820380c0501c410364202519484c0450680510206110360b40c5480341480c2d0f012200c5880354030407504210100c440c0c003101030f2a040c1082412502401034017880c2900240e1107140c01101450003a1520000380900340081051358100c0c00411071102144005016500800306a0262407040903096818882401d0803a5004441c1320030566100c25800c0700c1c14610b406000140c01ca42c1c03404c00c282c000c160700c1c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 662806034 1250 662804784 662804843
    0x30e15070225050f030f070315060509011d0403050d0e0619050906190609060e060909030f030403050a14031e0106022118130c1b12030504 61
    0x90020641041121641485090754002c07240c400707081c1402c080300140307a001c0d450b4090a4001c0041540009490f6010044070842041c08012503074403176103c1c5070030200140c43d09135040483d814620041000d26083c45080d050710380035424403d195245281c440c2c05003902500c140c3c00d000007009180010051801400c0040c400c000c0100914285907200d500022591078034010303440d01e0041400302d00388000c64155044030020442c80c1c0d228503e102c0e40001045190711502200e0301c1d02000081d442d221500343e07441058200d400d1000c0390b58401480c2d89a1160341a0140218810000100040d00880240198400da0300e0440e0a040b07000c140702215038010360701c0750720408003503048440c50205a8180c50240c80b0910280a01d20040000307101c4812844081c5140400301003015076480680c140207008a0800600c03840d40034440304001300c000d256201c6040c00146180b41450035291300600310039460313a40000c8456010301c4002003100206000380044031509000c0b02d40b84108004e0540310a103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 662807284 1250 662806034 662806063
    0xd020d050309090c03280219020705030f01020a02030a030e030904050a020705010b33090d210e0915150a05040f1a03070f0903051e19080f0703030e 65
    0x1580c442e01e6040000d28103000704100e859190410401c110b845c001840c80c1c4405c090603074104c0040d02021070480c0a80a030302c038524103014116580541041e40002c2e0310341199000d80640700c000403407450301403c0c3d01c901d01c122800740c0d02c20421200b0301d900c81d03440550529648001d4074240185140040c040d10010780702c1403e203075004039040081c00030030f209080310818200d943c7d13180440c40f00022203a009400004080e540d0311010f600000f1038000e401c482c82380d00001c0204016284910b0041c010881441540300303454500c040c03107007001f800340e4020300b034103140101040c100383c0e0b551542c2c0e5007903038040395038075041841d40c603144031b200b208400030f840155025140c0640300d03404d01d000140c603414580d20101d1486041400da24030a10403104498008020703240000803248540801c0d1925580c961001303006100302d107a1201d211031942d050b003030780107211000e0300c0140340c4950f01046103408001001d00501400c2142c0702e500096a0700420780e151084c10003180d03c2c03850035030413400d22510801004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 662808534 1250 662807284 662807287
    0x40605030403080f0f0a09020d050a030f11010b0d02100e130609151824080a0311030304020a0504021e0414090106110d03090c0e1501030b010903200d020d0503 70
    0x8101500000c1c099800202c0c00c03070f02c0d1064913040072217400000c400b80c2822141c40d030f911410025500c0c1c40072007044558200c82207800012862400178410700c00b00380340c80001403180b8051102000103000c1c060101500500c1c0c100d82d807115408101100301042136410a2000d8820803c101d5124055003031b442c43e440e03820014201d4034284508060385c1850003042105914540140301103212228165100d200e81e61000410042c4c140c00c0b504660b2140030202c144010b4901d001030940e8000a6070500301d40700341d583c000940c114180050b600e00041e02c000754046204201032085060941c0513252000d038088104029681c020200212540310780c108000702185408486001e05180e480c95004007203603e0b00350a103001d0a1503c40d118200a0074a004051b11010800306101195482c0c1c4040c01c0c1d0440010b0f1a420040200814446400445808241885004c1000c1c0d0700800f0310301c0072641c00c00c50311460414039804401c1090022000e00342e11203c0c0c2003541015031100d42e000c0b0a128403940055 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 662809784 1250 662808534 662808541
    0x4150c06060902070302060a23010803091e03031912020c03070b060d02011d150a0507170a02070b16050106030803010f05060717030a090b15150a08062404060503 71
    0x4410350720076410049241e8010018880026400184d199010000820000391503144140d40c1000ca008001c220f400124000004659a6808002041c0c00c0004480342c40546c20302005119901010403605c0f945a0420300900212240354420202c40600c0b6103010344c000309416050000300d030800c0034100d84541c0045025010400300d1000a5041003044070802d110b84d0907980020003c9070204c00c071840400c0d0790815400592105948200c40d000c5500c0c07007e03200c00c6400760080554000c01e800b6591036603c00d042100805c4903074102c86850000350702071710600382000780d1503049601c104e007d107801401480d03200000c59000e1248030050351080ca03031b031a03403940351040312066990b40d60492880b0740c0d01080b1620004519200b0704003203c40e00045507440c0d54503900c0e840006c00c110103016241d00a10400c01807a503103041e060502460301229045030100460503003031014041c0c10b003240302207001580481d5203460001c0b04142952030880070580b03400000c820b402a5a04154401e0700499804403c0c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 662811034 1250 662809784 662809793
    0x30714040e150c0a02030702030607030f14010b0d090215040e07020f1f0b0102210913330308131404090b04060c030204120b150a030f02130204150c 65
    0x9404a841c0c07008000c0440c2e00400e082105003034805445a603001c10006a0070310454000c1c415242601d8008050f1002860b01e1680a00034105407000126058a013210610b00004512103541c10b8406c07201a5038240310707021024400402c07003003905a0b4405180c1400d240340b0380c51603000b0320107040c014444c1d5080d8144040c02910f494024001e804140d00400040e0a680c04d0b42290b40034006468100458000001c0c00140d04080c56188206076410b152070000d441e03400c03581c005000c2c01c00259201040040b511050310221140d40e5101011403900c10360140c13004040b5103400d00d4405c0303141c05440c200c5959a0b138085c80340c4c1c00040303984400105a107081040c6a0b103981021090142514140207a4200b50b480000510004000400d1540e07a140c0040d640c604c03c2d410b0318040c00d022800300b1102125030a190040d114111050400880c0302d001358404c90408000c00800c607540301492404808665007000440001040e015200d0781e42400001091034500060301e0000c08152560020782003035040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 662812284 1250 662811034 662811041
    0x19350904060e010e071409040c02011b0306120b04111c0c0f03050a20040c02251802030405011118030c042003151512010807060c08031503071404 64
    0x402a240ca999004100f40e004c0001c419078014524580400c040030003503a0410107003c0e5070301a941003031a0550303180d4030070b405600060b62042090b084413500984201d048065078010702036114600d52030b01c0c0000c00926004151600284113184e034400900050001c500c00680c001c806041c600040e0407035400b809242c8101c078029103c0c0c0d01d00191860b065071103903a6103c0c42e10000405691080100c5420300c07022455016421400800c144405015200000d6842c0c2e002c400c42544135107115010024130000007002c50840f860702403803540c4071044440490094000400903211552922038106000e02148005c01c58130710320343d0030061544091414903103010b0250008a026501d0039034100b840700d50940303c02400711b071440c100607070342e50701c81e50519004182c07000c645401403441c003034440e95510001c0140c401c040c50b0f0350070b08070a43c1c1e031107501d2542e80c0c2c014800d4001282044003483c0c0131680c541c004540c8500141048080340b403020000c640b038075a09502100142d01207800384025882d0600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 662813534 1250 662812284 662812289
    0x80109082106010c080a090e01120b220f030c081201080d0806031903170109020a0f0c030e0906010e100302090f0103091106160804060815031935090406 67
    0x107014000c64074060001034551140210058401c20000c5044146c03d0301c102e200030701a14102d01d5130455560348899050211404000440b15030610f100040c0c5140c5100b0020507940020701c05200d00607000352070703080c0060010082a41002845c2c0c01c2000070904110081c158484050a0303c0f050350700d807405103400e00c0c03810b401e0300040210700030502c201c960340000e1600c2011012083c00c006506c2603c0c040c0c0c0c02c40300a01d40c40c0003441c000b03000011440d000307030f000c0c213203403001612012090030040c4421903c404949100070f0103c4c0089001c030071281018454542d101c1010b05000e01010444030024503064448501c890000380c000440040600f800d900b0b42a5911013820240105a2075645103203101c208103d4250003058085020440c000307890004076a5203800140c00d903980c644950300144075101c12140c10201c800c0c0444610b50720706000941e6011144003c0032402c5070314840d07441300d1069403007800c01410040740da041014400c1e81d0019680c41081c2071690300e5a64045070041c0700c10f8603103e6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 662814784 1250 662813534 662813587
    0x1103190e010516060e0c040f0b010e01080702060403030c0c050109050a020310021c020309190524070e09060a180501090f0207030c0f02030307120c02010210020a0f051308010908 78
    0x500c030703c01904406070001480103a00c41008a00807609080c0d0902c0c107901c2c4000e0321780c8242824648943c807401a072105030500782c2a41e0f1064518900742c01910404415100803005078400000100460700c81c0d4090314201e070759450302081c04079007500c80b142500c071180d0041d252904007050703039021464100800c1d01c00c80140c50303056040c10340c0b45030403134001110404036558003500080020303100c2500740000c7d0002c0e0021102000b0010f100d04103550780b0704420340f04200a500480140c0d0700d5005484090b403003002c02d50f481b00c5d5100304030410710110b0803003d40601d4000e549030784045060f11000000a484030b041e40000900382d803605480c4419074401d403104020f5075104006a4011030380c480d00950115402000310000c4034070074404a03144d071082100c0681a030798050480040b680d441028003e110303000341c1c21140341484114162040344a82030a0001142c0c84558098225004101400000d508001007a1005a0300d403c041d09480201108686001c00043d100011000e46a400d5000c40c241 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 662816034 1250 662814784 662814787
    0xa1a09070f120e031c09020a030f0303050f04110118080d02100b0d0302210409050705071a2509030c140a06030204050604030b0c1b0d0f030e1c1103190e0105 69
    0x10090a504e038854542c2408242610030080190545c13203821420140707501810891500355641031420392090b041c0030442c0041d00f4a804a8011108690010700680c3c01c0551a0280c155036170055030181e00c1001c00b1159003103d050000380140e014411040d40003103580152142e8848100450308441d0300240161283c4441a485000720b90f0001c0e014145070881495509100c0e40d030403050384540140d40c00703541d00d581400c0400840d648d00001408140348501c04034103004850b61202e500c03074401203a21100408452400301c85511744139101b407032684020306240f503007640c80c0c0d00c070034140102e0340d004144212540c030242c890301d04142c8200b0b4010100c603c0d045013410304000c0003800c244581c0c40050408451400401c60012111f0102c44d84050130003500003001c840840010340320100900341d00b020800400807406072601a00840c40f1100040c1c010341704040703c00f4290f02559080460080130009800520740c012034040000f0494400d242c050004603140052005000c404080c2c19141009030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 662817284 1250 662816034 662816051
    0x50903010e031204170f070f150504110f010e0604030c030537020418030f090b09010e0d0302070815191e0906150b040503190b0a1a09070f12 62
    0x840004254015500c01001646400c2c1e0740f500c0e004900440c6c80459443c0f000180c4a002c102c0d5030b140b4203644c940320b0740007505041c0b8210302d10021a00201c3e809000b112114041600c9071500c114426000380d0b05041c82c0018056003400300b0850f801c0b42d0412100302c2006001441400070421034404022420012125003a208180c40c442110500b0f401c14540c115000400045640b150494880a15410b03038101c40d211980c00c0c02420342c54640c2e01d5402003440c05a010440c2c0320300c0e10032281580010384a080200c0f0b00700061020441c08404103030118007034a0f50105c1c0071030050021840048100403005580d0411011400104500030340c10740000d072034129010107152070340c0c102103003031441d4000001d040c030410704000c0041c00688511030181206004003098a20b19800a042510015002c0f2220410100008a0700042c035403809040d50441000040080442c2e401440c4050041c182c0c503503c0c104148041220681c0c00e6902c18003288450a03803884403a440074507804c00c114644000e0007000c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 662818534 1250 662817284 662817307
    0xb030f03070b130609080a08011406120414062d01030c030f030315090f0e030a0c1b0f06120b0d0b011a0c060c040317040303051c0b0d03050903010e03 66
    0xc81c5000003409020742e040020114001a800000311940210050008458a01e002c01780303584120707486404200c400001084562901100c1d5400301c1004c0c14152800316910743d1103401c800000c10480d000c440c1c001f400c003082d06042c000c0c4c9000e82c04000040c8610799031405440000d2190070064001d841c01c0000400104103d01341680880e034020342d8980e070074071040c1021800340c403071403250075000d160b0183e001516401a6024489c074224141040111880020001c0c1d100c1c855564048002000d103480c0f0008030341c003016804010200081c00d400e02581e2060303c202003101daa40440003003405c070f20075000207030880d00510210700e8045441110f018800d44e120f00b0202c07410f0040d41d1112410340340c800503400003802203848041d2610211500741c54000445021540706000445191060f000035170391000d5010309444c2680c2c0c0c9a142c0c1402d000d410950700b290200703000c002e200c01540710003803050708e9100c0b9282c0d00b036003c0c020394a0300d550758a02d00038542136903c40703200c03040c0340c3e84100b02c07040005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 662819784 1250 662818534 662818537
    0xe06090109050901092a06020f060a02030603340503010c140a20061b181c020d031101050c040e0a0902180a0204030303050f0603030d050a1e0902040b030f03 69
    0x4031140e20740010151100055140103203401c0a000782928403c060803c900000100240a101000c04a074050300391520412a19400c80c2d07018400c0d0355000700040b40303039015a42c01850380118080c01311030400b8400c001c1d9414240d001ca4107020204202c05100d00380c0d8501116400c080e0000b0750080c04141404180180740e0b900c2400080703821040420b441103040d00c40d400b001000151103200803602524070b01c1d0b40b0b4481d5400e86481140f100070a0200700811180070070350300840f4013a680040090071400502003061007400c040000b098040c3e065200582c0d0740007070265258000d41d140ca10054098505608568001d40400701c6078200348810403400403100401c80d0321031003c807400320311000d052020940703c40003c5141e00c2001c00b45400c1141490307440d406001220f001c3c1e40c061095331144000d11301000c4007030b90762503010342003004101450406604085d400281d00d9100180c01445080c601040c0b03040c41c10a040000d80790f03101c50095207010b008017009040220013402c040071844040750340d81d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 662821034 1250 662819784 662819789
    0x50d081b0708220506070501060503010c09050102120c0304031718030105190b04090602030f22020f010c0c170106050315390f1909050a0b0d020403020a0801150e060901 74
    0x300b43d0300c050f0a83c04a030180d042c050040c83c0250000d902c0d000b031071802d03d000e44914001d4601035031900d002200303401e10035000741c022600180c0140000c483d007100311413540e612258041020348001c000000c00034445008008144800002c1d51352181c041480181078640101201c034484e80c100b505000c1d480102031008544440204400039180d42403802140c082c0a02da000904024400300c03c2001201c400d1802e14414440c041e0403155401040205120000e0240d601a42140e0041204103881d40550326551409002c0c407400000181d940d5041103220050640040301d80c1d45440040265080030001000c4001c0410942102403504105085015041440c40d040750040b4860089001003108540007580c01511101e680d80c01c1c1d1a51400e41c141c2c0078058601b9060070000449980c24410420714007a1040108100b01c068544800301480b50050036043c074401d41d0802c40003006030343e003101c0600181028000855118821703a603520301c0481300e9001402d0110401b042141540e82e10695505 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 662822284 1250 662821034 662821057
    0x90b1302280b0a020f0304290a082806060f140301211b030606050901050303120403201518030a090315020f0c0a0c050d03050d18050d081b0708 63
    0x100d6040c00300f001ca1a200b2a2020142c0e940400980800d1406040c1d40c0052900416510040b4101c40b20103032440038403403421400c0007d5041d4001ca00c00d000c40d622500c00708000011060840000c998415085540741c2e0f01460200b04100706041e0030380d0300800314070040c00d40d01d06011306661600815422044144c01d0302c40380c2c200c03800e8044d810801250000341d011b511200c11001001e44907c4c1c2075008001600a1510811140000250601d400000c44040107251291000c0b00d0f19680e500380d0703248841000100000c44190800180745104108840012207100800951410004516510041032101d20a1150000c00040c5101c039000980700c0c084070b9000a201c7c0c0c0790102003203050700a0040e0990031222060001d00c4001d44140080c0060516000300300b810304403035448041044a07056050014040749040c803000d5500c60659000076440420f9100f40105e40d5803a590703841c2481c00b1103e8503004154036005104240816507800d4100c500084851780c6080000c0d1a4650a40106580e00704c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 662823534 1250 662822284 662822287
    0x6120c0f061902010e2112100b0a0c06050112081b070e04060c1205010f1806091b02150c0301140406030519170f07020d06090b1302280b 60
    0x80c000d85a5000b240c2200e040c085207074010041c2c04000038041c20104881019911902c24251300703107101c00d120980800c1542c401903207020701010a1014101006207032200c0241040c000240b4030200030010030800c0721326690711070505520325250702119010381043c0c1d50203003c01a64000128010101c9a540c40404181540400170f00c100a20700001d503009212182001030a000c00c100d1590031640d545401600c1c0c105210031400d4450040301c90034231070345031201a00386c0c0401400c83e10034100c005507442c8070004208180c40f00010320070354411500e401c13208480c3c401e103c0ca000d981401901c01003031000740c0e0002641040341c80c20b01240010300035054000c00356030036151580e071658090001560b2041c162505a4455040c0d10742001602209840f10011040c03040a4419141d0850320701c41400040c56080480d2038003400070007503003540e048400c2a51072441002040310082c00174811042102101c0500340144103124110343c101d41c0540c0b1030180c1c40c4540f821a20700300308a1040e210314500d02c9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 662824784 1250 662823534 662823559
    0x30c0b030c090301061d09060c0a0c020604090c051b0a02090601030b0315100807060216030605090a0b0405012307170c07020604030b010f0812030c0a0e031b010806120c 74
    0x40074901ca801c10302a07141d803a2800c0001c00448020b2000380200810881c8041030b0340e44c06035151100d404841c01f00f1a204100180e010080c01030041c00405030000e00b505052944030090242202c02000b0442c0c045040403071301c2c1800c203a0f01882a0554803240c2c000d080d800d4000e0f804076032100800740106050544075000b1a0260700e007004810107401c404603002c1018101456299158149030040750301501540300c01044442c0006283c90410b81640f2201d0f000e5460350f11010300a100103024082c860281d07503024004503080450a07801039004000008444d41d0000f181144440b03040c00300400340d40031100b007240d0203820005400347c1001c00040084c441e541c14500c15482d20031220000c0d0301107c046004414804510000390581d82900802e40109803181c40550b6508801001d94040300c2c01000002c5190140101921441000741402c0068000ca940041d0820308200181c80c19081030b942280c17031030769202001e40d030450003d40d000289040c03082c40f140e840d0300c942503031180500480d2003103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 662826034 1250 662824784 662824801
    0x6060c0f150902130b01201525030b0a05010806060327100e0708061017030d02040e040c0b1602040902211f05010b031303180825030c0b03 61
    0x102c501d42d54010b24407808210380c0190000148008454540020000840c076a042d042c1c10b0032868154451400a01c0c0c3c60a0654403034003504001032005844154181c0f04080d21a00400724410f00201e545000c11404e01040603c5101081944068100584a02448400d448580c1126000001000741d0059109200202e080754000442c02c83e02511400090541140440e407280e101c003410981550340e0950f4441c1002d90300c01081e140c1e40040c40c0c00303450401903000010480011290b00c001a64100304200400200b03d8001c4c4d4460310100010710f0802003000162650756026141410070b1701d080110203000700f41c603858061402405136a5400080041d9902e4864400080d26034a0b5a103014141c40d42c090380d00ea419603211900312a11501001c400b070f542c1402568140c4026032901800e41e51410010b165003200d045040e41440180150111410f1110890002402c5004000c140700212040036001c804044901160002107003070051000407110043c2c58111000301040a4690711035201 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 662827284 1250 662826034 662826041
    0x6140d0507030b011d0c0717030a090c0e040302101109040e0a080f070b090a02010c03031107151e0b0d0201051308010e010f05070e0307030b070207080f0303010906060c0f15 76
    0x41d103e41000740002a0445032481c40c1c2420b00032540122070303542c90380507504c50640281e140003002d40780340c041c2a560744210720000c1d6506c00b0304c110000ca50b100c0984c130b0703808034500d0941011081c03103078a00400c8181034040002c5803411080300000c200c0c600d10303801640d696004081d1120310554840000c603288030740170400c40c0c0f61a40c016201a0baa01d00e0b801aa607000d078046107040741c5256600000407150780300030510500a64044e11003269107030440e0b808138018880e02000d0316282400307000210106180001c1552400d441c4000011001581d49208014003018500121420b08000d142007140e1920020002100c0e030a003041500c405a6400426101c152904404500d41c6440680600044150480c5290b1440308208020300c4c3c4408108541041e0300504140e01075100701c208000090580312400d61100080c410381e548991644400350404540c1a02c0343c2c019400400140064582481510005e21281c10608034810542c1c0d200b01160a05e40d0001d0082844604c9640c0052007540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 662828534 1250 662827284 662827289
    0x4020f091008030c03040806010e070e1504170c1203090102030409050604021b10060f0305031207111b0f2b020301090602040e0a05061c060209060909010611010f06140d0507 76
    0x507aa04c469941d988155690000c4c40f8014043c411180001071290b00340107a02c0c05640c80d5660441c03000045400e0140901900e08801804079041200044403d56480038050410030b90b0050860900b100381082084403c410403d24160010003060034543c1c0c00104440032030f08080400710703250f540d1400140003030047c0c0004045c008050001100b01080c00706401d0501408c072035003041070380d0700c0702940600102c00b400001c011341e00820005190401810b000c0f540f0111501e0429450440d498220f401c00d207026a5030003158000c080c7c280690310f40304146041c05a020384242240c41400c00b0814141c1d01c20021310728200034186c8440e410341d2402e4200b00700079a00041c00303642e59503031003003404000e0004884080140e803412010650320f01c1d0068003200b0903103004442e002c0e1000c890711080c000303600c030402c02980040100072610031038644c800796500a045c0c0e5194120651035002581d400d640d590711076031240e6440d0850910880c00c031007441c0390b200041528030011250003458424031301080354 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 662829784 1250 662828534 662828549
    0x31409281103060c0c1203060607060b030c130b03010506040209010203190207050306041208090d08060418050105040803071706030a0f05160e070212040f0b0c1e101404020f0910 78
    0x10000c000e039100d004e20091100a0840040f0341c1d01030084e00212006010036100d03244d02520801c85000402e130309820885080740000c01b038420440c4000d0014904004090094102d961a190007110526007842001c0c1d00c8141540c0c06d47c035080160b40000d440748100e91706049101034030001c030b20505108010030406040040c08841040c141400c0c180d00f040100300d074040000700380000140412402007444070b246162a100c02445031a50070802000d413580b00d0824100070110300b008404500c09000e818003035402081040d07643d042c00c50006000407810780828407011501001d1010981300001d29550300c60300210303c00740d101a00c0c50207a0804142096040010010110218814840b000344a01a0ba41c5800b2224480103062944865000300d11696400300b00706c032810804c0140c00d00041820480040c15211103507410424014940440c0c820b84400d980190340c03400c0080b105108803410606842c00e00c8401b0b01c0c0135030000e40c1c1e0380750014041c5d010307000d5500803d4211119909a0002d08240c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 662831034 1250 662829784 662829793
    0xc04061a0f04081b1018151101290a030c0b0d11030a0501140a081504061d0604060b0a1503150801090b100f060c0f05030f0406031409281103 62
    0x65003034000462400150f481c0c4648036514840840e58007131440c0548072040c0000c6c0801e00d5103002282d40343c81d40c1e0031600005111900c546401215001c2c8142400c043c14107002c443d242e0701c101240f40c25080c441d14420b02036001c490060020620410108045a8030340134000c0d5907107094441d84004d4000740200c41c035201400b009120419846d5000b00f0f0589162404002c50103e909040141400c01c0e841018207030341000e82803455459035900d10ba81c1c024041d40c1e000c10310450a50b801844c0c10074014204031583c01450501080103981d0041e19600710003154004002400c1a202900d0b144018100340240350b602d4020003410341300e520f9044000e080302c40080040c0461800c1030200684110307100120b604600c100812840000e0303169400381d604c0c0f030b070303810544103515030382d560010703e1403541075071107120030f21981008041140040020300401d55001c030310030b40580d420000312000030f4001c070074640110000d90300c2004038904180a048940d0105c01800c091400c01128540319661050380501a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 662832284 1250 662831034 662831053
    0x6020f120411040516051b03190503100902130603090c03020a0b070611130e280605030c04110901032a0c050601090e030f0d1d0f0c04061a0f0408 64
    0x402c00d00203401c1c14042d981030081d41d69010b054442e00e101044c462001c41c1040c05035942c80300b51503040d5000000000c2c00c80345040c1007c0b43c00b03404002d410429000150000003002074988460f5400e000921407400d00f503040a040d00e8650100c2a40d81c0a124109603903080070006200341202100d000350340140c00078104d1070700e409004a442c0c2c0181c000303440e03560401a0b2140bd000308e0400301d803400c2d048101002c0d0344504028501d0340c070010180c2360009c1d00641d201445c0d81da401022450401c44040107000814a240c04181424071f09011100c500c95442c010078150001030740c3e412540900c0742480c3c0007a0024000000e1140d90303051103e1800c0d40c81d19440d81135200340d0040c00c40a0418058021101143c0c1e03542100010b46100298543e82e542041c000740c21801056005030100203030f507050100b01d2403007012072008101d01403ea490f2959000100801090307505001c941d9001c3c10940c1d0501c0180d0a10700341c2d80c4019011700c11440c0c5a20001480b041e2041d2440554001d0214481924007051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 662833534 1250 662832284 662832293
    0x60c0f06110d06153b130c0f080702010e15060d140304090e19060c0302041e0501030507050c2107020d210e010c02040b0406081603050607020304030c0306020f1204 72
    0x10504d940840200d9036851481c050490070088002503900e00410440a24010082c0102e0103400b0310140d0750010030059440042841601034100000540d559201c501903511200609048001e8811015a40f400c5000704042c440800c45c0103082c82800304000c4241c480ca400f140c003c0361440c0000e8000d11244180d6040804080010400c48654000c01d011203d191050b09131a03101c6142030380c0340032082a209d540052071581082c45d099485060040c00c042c6c0c0c84140480e20900c1c2c0740140c605904021080c0700c01c0d0781510800350041010301e0947c0c20404d100c6215035541c040400b4884840d10741e44108883d44440c0d00845c2e06180d4040c01004000f070003031030200040c41c120443d5805000321035a1880c0c6141c4503c1030701d404154165900000007405400344402000701098041e0066203d68010a0001d4104042c808a241859402d00041e245007401c2d800c0c0070f00074080d80219042000108045204002000107494010000503600d1140e4480c24985200725403c0c403102010801c204424007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 662834784 1250 662833534 662833559
    0x402030717061609180f02040b0c030c0d080601020d0c0501111204060b01080601051213080c0d1d03121305030d0e1819020708070605040f020109060c0f06110d06 71
    0x403590f461407a128049212401d6901d81c0c01802009501141c0d840800e031080c1e01a0001d036000b07900d00b600180f40a41703419100410343d0182d0140c0703800380c0c400212079003191410490030407007000a01e8031060a04190000030b445072101000d0204006000340c01106001082d8040342940310341d042c080f40c2e203d40c6105e05401501342140d0070358040d03151404000341135000c0c82031280f04000517504e0390701c0c00c03001427400c561250020302041c5141007041c1443c0e0004044800400700f885844008041c0590b070082c1c01420400f40d8410360200c1c9140c0d42d080401510000742941402d2007481c00f5a8403190b0b0040b120310765a43ca940026414801c04e140280c5150304040004030048003920759a54501030661400140e030701c2500c51441d4000103080c0709e0350001d100c0d8082d260350380c81400140d281002613146e82d4182c07202038170140c0d00c110040611340110b680288040000f00700c00d05142c00844599100e11303244150501d00500840c2d11240e104001c00040d0b012a074459907144d008001581d100e02c3c148119 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 662836034 1250 662834784 662834791
    0x110d090b10080c041d07030602130b04031203020304020607050d1e1106242709120909060d02211002070206190306030c14100809060609040203071706 66
    0x340d0491038081400d00018400080580b518040140580441d840078440100140c00d48401410340504086000c0c500602030030000354080e4801680700c40404042d072001c50702d140c2c059865244104000c00000e001c802c3c0e0341601040b01d040058507039a8a00205260f803080c0040100b05020b0398494400690b0801162100c0581740c41c400b8044240400e000c0d10307101d03015444c007103240e40f243d40081c405c10420440f1005000040c0802308524491001003045041d00c1703030030f001c8075408002d801508546c100381803a034860b141e1001000041024240c0907120311840c2c900c14000c0380071100048042e100c080941038140c0d406801c0f40b902d60b90b02048074216195100541c80c440c09803500a440d2503080d4020b8513445a00100001c3c40d0a2090403c000e400840701c4002041c10f40340e050010100b81d450041a006200c29080d43c00400e0111040102041f50841124113000c2a203060010805000030480d6020605a0700d00006071254000645050000d42c0300d03420540d04c802c400441a480802c40310700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 662837284 1250 662836034 662836043
    0x1030c0e07110a020d060204090e01020c0f15071b140303040224040b0304061404080c071d04080c0a0b0a0605010207050907020d080a060b0714160b0a0e0301110d09 72
    0x381c8601108941240200c102100e6a0b070020020101624140c00229005841042d00500d0142d4031600032041d01d514100d08851030b540440e600801d0007043c008040c0b0b0f88601d1010301092040781c21092945e803c05807d5a00b0050340e0b00842e84a002e60018601250385c00048450640c001d14040c10756035401144c3c220700508020344820001480350190560800012405606041c1407943c0241c0540004005590581e140c03009540d03003082044c2d50380e02850040881c1c0f555040c01500103442c09003180d0003040218201e00085d454a0000e804d00c41d0801c1e48805c89503520080410414901040c0000143c05892403074180510300380c0c990700c8001260420380070b6032100d0350703140100040b400302103e005015810070b0212440031071283d40074a500030f401540001e61103455690500d081d4001030720490b50b2980c00d440d9640501c00c204160344040d00604406c121140c14160121500d000d40304044042c410b00c1c0004d181c00d960290072890f40c00410007a042d446001064202011b8001d040d401da8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 662838534 1250 662837284 662837309
    0xc210a121116050705040c0c12080603030702010342060512060d050a0507030b2211040506060702040f050411060a02070614040e0f01050a050303040302130c140301030c 74
    0x20104081c0c021000c0481c000c0030710360700380702c0b4a00452003040515181142e050041e5080841c050b5186d200d074040c0c401e03003a51070343c640c420640f41183c103180a0207500307000d01a0701c008001d0190b40c0001143c00040d03081c80e0100b44000031324400059513503d550518422180c0d03121011011803448100f6828018000c080b42c02c0c159540d000f904c0a10444190a4500010000082180c01c2c25038450202c5881a0103c884408140e101e0030f080582c10340045610710813980501528002d110068687d4080c2400710410b452540d641703510b121102441c810f40255250400142c2c10740e10700050300c000a40187c400c7c4042e98100b191003000700390032102100c2c42c9020b9102c448540c18000c044c4e456400c0c1b150000c000c00c0c8d04011003980c03280d2049a121000c100e0400005c20030440405200d4081c4040708007185065047c80108410b0440c10780026000f540203000400c0542d40d803a00f003c0d19000316640000d41c40d0702014045900c1400c61030300c5600f08000000000401a164840f0307000c8404d44a5004e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 662839784 1250 662838534 662838557
    0x1122d150302030c0f0a0b040e06010306140108040b09210d05090102030f15040204180b03010c08090a030810050a08070303030b0411030103061e0606020d320c210a 72
    0x68250403010302002c0d4060b40a18901042030030300004101600c2030003010400c03050742d240103400c5954050703007000407441c90383c005000041d60540101e4018104031f08842c2010161500000d0004000a001508580f6400042035001d081884013400c02c240400f551a8511030f078209400c12940802c0c1001422840c00c00002c100c92018800d480c01044601d000e04c3c43c585625482404000e1844841c40d41305500700000996205132540a00d80214981c3c004900e002070381c0d08141c00c40710110807210030b20a2020400078005800708140c00400d40c1400c00340b0302903c07404e40280d00040e40350042074100e0b40c0d0341c0300868606000a4100100c0b4400d503814000008400300f44001d9074105007225501410600050000401c5c6401610100540000080c0c4903001820001c0558a2951204000da00f000d4861100642c1c464074503900a007080417a00040c00300911105803103404420751038244a00400c90500c1120140b05080000701c426600f8440d10800180c040ca81c0d500c9030398000302040421600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 662841034 1250 662839784 662839811
    0x10215010b0702130e030310030b0907180207030c0203071e0603060b1903090215031006030e0304091808070606092a080601030905031315110a0201122d 67
    0x528103a80c9500c400030308040790ba07030a000e45118038104441925131a551510041d9030100040d42c490030710000800c400a1450400200d0103001524030303915038100500030b10039001c008800001c00c2c1001c1d04010b07502c91070384c00c00f1111a101c041000f03515000c1c0440000321802c060605542c1d95000c02c1006170b06582da40000d5049485034803034060031000a0021700000a401c181d407a15401c210304001c03c3d00d0143d80d0004065000c0c80d101411000c101000344847c444030030310a44094406030500f00481c0c00b0401030b203039680c01140b1803c000540c40301c0c6414026824140e40b060758a50000c1c040d03484102500d400c5006e014640030300c2002c907190030740010a1300c04032141b40341c0042004240804841081c80100d66115000303190a05058440c0f400c7c42c0000c104200070490303130784c14034910000c1c00e0030b2240c0052441c1c2c141c0a00d004111800c0c400005121022445191050b82400d008504005030b80f07040c07024101d1070b11500c4010b0094043c40d041c0c040800010040920025000c002708102d0401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 662842284 1250 662841034 662841073
    0x30d0c05070509190516020601050a0308030c0d0204030f05030414060405101805150d0f0b1815090112050c060a09090b180c04090e0307020916090306050106020c0102 73
    0x201400a81c4030190402550800e1120b11380c10114002c400b141d2401c10101e20000d071001980c00c4a0034285070061001d600b6818013034203016210868003a914030349140c58480c058040903003a070241c00e00c0080c0301d681c2ca600302d40c112801540d0181700f41605000a00b0055200e070064429a41c101401c0514a070307040c40d028080f1804c0d60802030064000301082e08040310603000d03800c0e80740240040d0f2507000c91642e5072081001e8200d41c2c10311300c1903038540140c03001c8030640c1d4140058610310703401c04805141d035903100d5184407401303030003c000301407543d40b628049000e11042e40c0b405078120400800108011440d00c483c105070b90b0095045801070105902406118403c01d9001c1c8002414034a0500c01d03810503411451080340020980000070007203211b5054078202c25500c2034030704035002400700a00c0009018481c2c1c4618088042c6051201e039801140300043c0c0109010300c0d041e103410f00c428006002c0d54a103005180c000c2010051580c498801a680d00d441e0300c1980e0152054460651701c00c410000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 662843534 1250 662842284 662842307
    0x190c050708060f2a040906080c1009050d08090405010e040203011406010f0311070b070e1c0b0f0604090507030606140904050a08070c181b020303070806061c02070f02030d 75
    0x3107424640c0c42c1400e0100031030040780d40f04403165004138540380d6610722402510103007002110005038180b0300400c5900d0190000005801841120721003002160800e00c0f407070032100305440440300c0050a2030006200d200e01854254014078240012900b0100c0303c410070f01c05c620030342c001c0101d03013000c04084600c0801261510b0002c1c07040c00d46415864401d400c400f103c0e061344040c9a0802c01c8513640c030703104054121a8080050318140340384444e8584800140e00419002c0c040044101c29515868101d80f001800c02045298240c0420103d844030391000d0143d0340c0103820b5905030340d100d20f020005040b05108035038005403040c8044002d03250189001c1c2c021940080141402c8030103680305d800c19044240c0c00e40342903001010001d01075042c10358040500c007403a0800600c0d00ea8407003c00901001025020742158010300c100405e0640090003180c000344101c410a44821409101c0b11040040c20040089a400811740e80100441402402c1c4520310842c00e494079418242c804a400744c9006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 662844784 1250 662843534 662843551
    0x50c012c0a020f060c0c1804020102010c231c020c010504020907030b06070f020409050d170a0c0215180109030905120309103b040f110d0b0402190c05070806 69
    0x111280f2007a0f262540041c082400d40c00255490101503200080e041800400307954128031460040100b10341e421300c00e4070020341e141d050401100c3c103000c600c00070741c00c00ca080304401e09000280c0440e115a2009140004600224040d5900e40702c040e0703c0c81c003030b220a0360228001c40b20311020a03201760290055003000580989030380e00b00fa5030340d2500d502071802040182d030420f036562240c0b80801e20a0001c02e81c11a000d45503c001c3d822020000300300444010304003070360350345004a5a040103030b0105a0203032404c505610402182c48035090030741c00b15031010282c601513180003501c504141d082500403044407811902a00c01041c850364094507407180b0b036900c541c08841440785407003950003411481e5a2062000e404081d102c6101301c1d00030b8820000103d070b2000d248040c079511031464180981c582c0000001c0f070502500d4000e0760541c840c0d02440260b500c446450352040610380d1a242d042c1c0315410340c2c80002c051080001080640303908507010003039a4034003402c1d0001c039144000154090141041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 662846034 1250 662844784 662844799
    0x91119090f020a20210d0f180f110a081e0a0b01030b10230306060a1a031801020406030501090f09020108011403010e030f040f06020a021008041b09050a14130210050c012c0a02 77
    0x8e41d40394200c1e1403000c0d00071682440c1e05001a00f49490f0618454050901200140041403e1800e40d0748281e00c40080003080e684540e445400003420304030368a045070303800b0b00402910b4a6000c04001210102c9d004030040c082c00c00921003092881c1090f140d07500100764252402a1074110500c80c11441c24010740c1061078410702001d0092b01e414004582c0519900b07600d10f1440d400b2100c240c02c0e0b80c01603124800103a121001806030b0850f903c51b12131001c800c00010001c101e440e0380003818041051203180044500d136190f5410944084d001144540364180c25aa618160284200750703a0b0894007a4241c406001c4001144003400043c007112036036001424480d41d280803c400315041480144116260144015101410341d603c94180c8094003a681021800c0c1c45c10700c2c20319040301c00e0300140ea008240e041041c01074024681c05455606501915840d44201003450300751071511a4510011903903280a4601c20050740905100303c4a005d00340203d50800b0407002465600c0034070b0b06029501848 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 662847284 1250 662846034 662846081
    0x218060c120c0a050312040b06010e03070302040b150318191a06011106040f290c0702030307020901120c090b13091119090f020a20210d0f 61
    0xd4002d440841c4407441120b4054410340e6030242150030000001c088030702c0040500c03040101e0110115800700007071034680350f0302480304000390740c64000f40310203401a640c440c041c803071584610501a01e080351080210340e490502050b001a02450111010414090800c0030f2070941e200d01c8031134041542154880611124905028150b0440506158140040c1d845000907000c0140900c1c1d101d94000c41004188000508201c01c070880d90030b50703500c260740f1480b00400c64110020303a440d8102c40481d07402030300e890052000c64038500c00c5120103507000c4404000040e03002c1c0c6034001f2086a0344a6001540680e990300d6504040da41400d40950b0b010000d400d8000340c1d4901070340842c41c00d601409001c0d03081400f803000700e200c00328503000403034001d20030840c18880c03200076004068400ca01c5810851510f03039140001401010f4180054800710f080416644a841041104606075a81c0c1c42ca4400241046a04140d00c0c1e40191641000181032510007602d042d201d00c17402a102c0e40040c0210350312003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 662848534 1250 662847284 662847313
    0x512060405070902030618060d06060e0702100c0f080a090c03050f0d020102090d0b090a060e03180901060906180305101b020a02310c050702090906060d1707060903030218060c 77
    0x1d4004003906c1e04164500380309c1001c1101409080008c14135411580c14900702914002d050440d58130501d0349145c00d082d055002250301040c01c0e000c1076000d20300a207441c1c5501201401030000060054440b0750002004002c1c8007010074034503140e2620780704894100c00002004e90903030181c4005a40d00c00390440400012074251003a0a81c00000d80050700c19402060343c5100440744150a000709c00d500c040342410308240c0300859840d00c2c0d4001c0710001500d41c58071000400c90501406040e0400034070403940710f128880d841400b800356901c041910000c0003244945070061162100880341c000b101c5001000c3c0c0c5001246081c44950003501400350324500f502c603594218141c0c0007507101075100c099540a5402c4c503120311009444030b540d0302c954424003801000321340e40e40a445956581c001038140310040e0f40300d10a03240d241c1d07800004030042c0340c01c0c0d901c458054055104003506072802c0c050404200345c1e00d54010070248813406600c42c260400b440078002c182c000c5070113086141c6d10456040e0b01c1305 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 662849784 1250 662848534 662848579
    0x17070302091329031203010909170301080c1314010b09031011030103030807140711011421370b03100501090f0c0219050705120604050709020306 64
    0x16400a010502603610b4541000d040700d50034030503194004001035004911820511100b209030f50201d0042c4800c20001c0d410705218441803260302265a9900031100401c9424500612468003802c8465100d41c0d4520b0305039201c1c4040180180328100d803040c03c00d005002d0b03100e4984c41030310300b1080c821181e080c0138101c0d0304d40d0700808882e6890700c00c04000c030001d0500c43c000e590000001c1d441213616940740d883d01801900010b41014203000d020f001c07550b00d4480140560340750310b40210b102c01880059000584210450807404280c0c5800020b203d5a55441c10b080004010680000150113550786000c030595250440184d400004449410800500c4036510344406410300b480c00251200032000081c0c40d243d00503000d00b510340e4548004104600c82441405507031549a00d05002040b80404004d45600420b074100104c00d01081e80002488010089203019000161104429000b0084016903400341250300301c03058450b440d00070448480600950740140006880500b42c099450080d2024 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 662851034 1250 662849784 662849797
    0x1005120309040b01050f160b0609130b040c170d0f0e0303040612060905041515050d12121a0301180335070824012106080111040e0717070302 62
    0x1041000d12a00d08072000e108000c0161303c0c8542540e1f003c02c4c10520380010f414600804051240c18100100058202c560240c5042e0030381c051443c8079990f42d1403600c00d9441d4010b0300155a076034003070200c40c0d840c0280000c6000c3c030f1900b140c4a0280d8200e682c1c01c1141c01d400c041d04030a0700745e00244002c001c414000c002209281081001c0031402c541c0724900f00e802c9560481d000c1c2c0e1011602c14092000e82d403548511b400b8000c505015606007401c1402007400c400700c42000074942da00080da900d000c0c45c41000c03030340c04180b00120180101c101c0c505000c020f09690180c0c5510a510703042215101d04480c2c1d5205000d568152261030410920f08901041c403440c800008012124a2205c88040401c007074540344650f1107525410418200240000018044c00a210850001c0c042c0d04480d660f8000c001ca002d0121421010718240002c02016405006560300c00c900e55801c26028200102c45103018009666014180500b1656110000c8030740208000f5000540000800441c7c001413280c2c009000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 662852284 1250 662851034 662851037
    0x5090d051f09021201051012020409020904051c02030c070603090f0b040b040b0f04020f040f0902060d09060e060408190c1a010f0b070302330c031005120309040b01 72
    0x400c1040140700315100c100100048a665030b450300c03500c0451030a540801c0e0641ca0b010020480c3d8a0b24086900a99115001d030010002182014408564554000460315079000c2d0051450707003414030709a542c82180368094001380300f5040141000714400419150745001e107a008141a40c58504c0c1a001400da080c0c0c25520180308030034031000304038840705450250f44242000c00039440e10381494003038114080d008040e640f48060500015940c0c804511900c180c4c103c500007140c00f003c00d0840010003000400940281d804281c00c3e020b140d055200241d1715002c7c0000303200117188200820744510040340d0050803030609104988550069100d501d0031600181080e04a02d01646c4070743d043d418644105000302c0003c40010300c40741c640c00d0491001807110303102d102c0c1040e8095402039110041403101714003400100a84800020460325101d0b40d030744003007449074114108041c400070943e10440e10a0200c0105000009260818841c004001c4101c00040c0d82803002843c100805000310944890 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 662853534 1250 662852284 662852293
    0x10e1501170c07050727020304030203090f0a12061406030d0210020d060b0304120f050921030f2701180b0c0a0534050604030201050706140f061201060605090d05 71
    0x140f00f0011500074217000d41d16040b225000054a0240300310500340806011f00600c00d02001a40000c00d032461950210703049080450301e5008a000c2d0303411544491a0b400003e50003070140007050303001150110412280c0306407551481c003410707680c02215843d480107a005980061024170154003130280c01000c1c40001c19050b42d14079006010f50000c0c1c4065030020b100c0e1140c2001582c00807208104685c1c581030450810a40100180100640100701d40792101da810f50030544c4c2e041802150304021480050948401191030000c01c541b40c82c10780422500c1d0311807080b141d01d42c082c0041d0280081c9221207107100c01e0500d4a00f0b20703150000070003145984980310300403000075070500c103a942a091200c0d550091a041c0c1c8644942508108074010354081c0b4071750107000301c0c1c49010460b01680d40a08040d55904607501d48a40104211030f40e09806030100703002d1019410300708a03150701480c41100c00e001800040d02c0301e03500300d850758495000403820801121495082184450328014003480644 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 662854784 1250 662853534 662853547
    0x50318071a04060f021b0103020a020c03060703090c080c10110a230d050f1e040915060f020c030a1407050607050309030d0906020a0605060f060d05010e1501170c 71
    0x10060030300c00e1607a210184101040c180700c140e50200700700800381c80510051074003030350a0390758401e0000420041c904264001460503540c074000c00200007155000b904030b929918007240010010074082d1411540303a00741075800207044000050108803400000c11084176401d001e18141c0d41002400b100d040a4011111200302003904601034441c54404650103078022002c5a4115080c9200e03031100006112050018040c8040c40c2d0341035030410699031401c41c0c10100700c28040c4000340143e41c03100c00d901741031490727241c0d1100081040c80e04903901c0380c80d401c0b046014002c0a0381c56055400c1d41507015400309480d0008181684000c880c50300411f0103907400c558555010075034951210206989a902c000303007958080c01c04016110318003c240c600300400307604000b0000d440f05941400500b40035108d070007140c602e079190b188114007014002c0c407003503076059800d01036000b0b40300074410001a81c0b45040000c2d851142c80100401c0795405031f64107a1420f07100000a2405a80500001030009042c0301d007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 662856034 1250 662854784 662854799
    0x17040e131e030e0a1208030c07050c09090307050105060f3f07080c0a0b0f1c090308090c01090803120c30400602030109270305031807 59
    0x11000c040e4042d0707035661000702c1014113000794043d10364414443e60355030710b202402003801941580d401444640d041d603510303910382c144940ba10342e440c1542a40681c251041c4898144000000c015551260740240050780e11101048a03402a291040d6041082550079034410502001100904c0044045040010000c8000e800900c1441c21a500c0d50394801d101c20303c4000380c00c101d90642200115a9403451703a0800008801b14018502418000140441d001c500c0541d0b03500c540c12003401c614402c201450350b5043c0100410400c1d101c591a6004100000c45c030765100702d62035410340d0940380c01146001c0302d60408042c84030740182203100c4543c0074422b403944003000781035200414a44440c10001c41001a54084808901030082d8113005172020f811180075851204849840204060400d40ca1250782c2c01176502c600343d40c0004001c3d503c000700200d540303001031340541808a207004184034055881c1d104000c0900560001502080382400010081c040c0c0e20001d01d0282c10f90b0055078500741d6601c25 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 662857284 1250 662856034 662856083
    0x609010510260f071214011112150303070308042f01050f090915031009030f0305091006060f030605010905090411150c070509060906090121170717040e13 68
    0x16081001d80c0009040030306c0080070400800e040c0c10002000501d10040e1b4202503032242c81038810110402d88005a804072400745a010741707501c040c007501d540300c075a0325009100c05401c4a08440a9007041100d080c0307800800301c1c5054500600c201c0181e031212500041d07401d0380260220008910040104009945602d000c0070f010300c012100c41d2400d080c00d9000c040c1001d211031130003e0a54505518100441d070b0009040494945a041c0001c058554410290401515494814404e13040c0030300051740e568401000c1401008a580410020351220b004441061081c480e081d4848408004a00410080e1641032450380b40100052035007201d000f001461038100e030311b0030555500320f5542000b0714140815855800002107444000303901d8071a0014603814810702807900c904481d14602a80e103913010310349007030158000b08142d032001000c0104500a03440b01034100e400e03901709280300c240c0c21491003e87e0160707524112945c03402d41d1041c600710031518049405440d00c0c9201c01811945192000703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 662858534 1250 662857284 662857289
    0xc24040b040f05100813020f031605040c0c20060717071a19050405032110060f21181a0612070b03100510020609010510260f07 56
    0x40a16201c514126050044541541c4458000c044161a062010307a1114115901101402c0d03030401d2031582d400402c03040740520342c3e00da405108000c01d2410003080801c243d41101d10440d000c3c07194240c0042d003101e504184907001003042d4810040c6400640380e46021441c10040641443e04048458840014a601040c0305450240300010360f8005e004950520b040702814001d0002d10500340a125201c4440c05d5039200e035181030b5a00e002c542042420700490355425a403040070400081c110003c038520840594400c00c540001c00000981a4090665103440c0e102c20745400005000070140000c4101a0241502c1d1075030381c620403101c0f84244901e02050080c01445090320309013030b40a1240b01c12001034002c9100b4101c5c03441860000200080e40c009441c8048000c41c0c0303d49461030700707122444003500807507801606003110410f003e0f0300040c00f03881003000c54001c0c0440e071140005002d031140f85008240d4007042c0308242c4000459120399072003040c0c1910007115540c9902e014424103183d000d8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 662859784 1250 662858534 662858549
    0x80c0112051e101503050103080403020d050a0b0114010215040b04140a080403061b02150c09040609020a0e032b050318150711120702010e060412150501170c2404 71
    0x10030081c001c6100304c44200b0000c07184c5044c204240e5056440d81e001c24080ea02c0001d1040d442441032a04100b403c0c000c0d41d40c1c0b16440480d0380782a58544c1c1007000c9201caa40102401445030b2400d03680d241c0e01c00b00c845405150860088010f544840d02d5804403490391600405280c03080c00b00300390004d010f10f402880114000e000015402c490801402c3d460303c19080000304643c4141c0113142107994030641c0135040f00801c0c09860b5110030a10114001e00940d03484601d2031031000c629800010303084200480754001c2242921908964040c0a0010455407403a00c540520b60302482c000d164041d40c000e44d001441200355620a0b89080752682c0742002e60101048803503565400e100216400c000c100c14000c100b03c0c040d00c55410a00030071820b40c042d642c4080e04020850f40e40740e41ca41c0782c00c82150080c043c0c200040c4482011801d040003001035046c0c003a4030213441d0000014080080350350254410300760a0280c6030070705881040058031802c0c1030004400400800d0001c5030301059000410040c502d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 662861034 1250 662859784 662859811
    0x16020109270507050c120307030f0e0a02030c06040f09020706020910020f060105031516090302090408120a0204180f0b120708060703060e011502010f020301140a080c0112051e 77
    0x100740c0d040030342d640600010240842440300d4000604c0c003040400d100341d1080c54070f9480c0c0d0b5039500c04602400c4101d0200071214908605840d10010102d035a21030381d402030b021106440d15180a12401e80328500c541c8006050030321044c0120321554009005070390042d0005400c051044002a015500354401080980e00c03074400c400700a40c0900a0500401c0300701d001c0c049001d480070b100040318038010f100e20388484002e80024030312030194070840007641c4c0151000023149018500450194070419100c8001d186500011304403101034002c4909036200402c00403010715071146507001600c0318180d00920301d500c1e40030070b00041d140e1a03041d01085036843c2c000c104682c50710b4841030500d240603190008140c00c0003020300607450b00446d92411901d054495900700620341c40124018100310745883d0085000000019440764485144500340e0030445d240e8041c60b5a0f00821030740ea014110301c41c1d020030301011000d84850b415612240d48260a2014651021010120b150000c0000c84140703103410071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 662862284 1250 662861034 662861099
    0x90112140705180a0606050f09040b030f0d05040f0f03030e09040312020d0b0f030f0c011103130b04030203010b09060108010605071a0a1d011a0607080904060609080f1216020109 78
    0x3041e0203000c000348403901f046844c002104000078410300c54000e00318010f503120142a64136840403c190040e150000c000d40d4a82903c0c3c1d0b90040c440d41c0720f407042030440405005c0120b410700d0903681030300032668984c030340340004086001070041a04005005034180190100440300744400e500081c0301a44444200103203201d118410002121f1200007024020303802120003001c00d11700060355404080c005d0030170103c0d0f600d110f1456403862203820340307407007111110450004440851501a0082e20300c218001d000a10340181801020101220481d001807100001082039034020401401d41a00982c0c140680e680d982c100c80b006144c01356407200d201680c3e050341000c121b010076500d05100ea1280024498070840507041203030078240101c0d03d031060000113010750820200030200c0301070381c401400610640c1c1c0c0e101400380182c4032511507404c045c0a1049141440c03503021a818116a44a681c90342c1050b02c0c4051000d044090007500702c0c1030020360303200480d051000815044844010901042c280301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 662863534 1250 662862284 662862301
    0x8010b031506061803030f040305070e07031418010204030507082404080a080a0e0604050c1203270402041a03101203020613051c020307050c09011214070518 69
    0x60000d049038481d5580789062000035522542220a49030703901c01c01d41840c900d2440001d00318800c214807541485c000190005c10480c0124090044a488000d030200315510b03414160284e800710040500455189030010710072203010b500300515400f038a0001800c090322035941074a480115008201c20f0f6101e01784c62b1005002c08080c01c9901c0f60003121010690038203542d8009140141d000020501030448006401604241e11038540c8107007400484585003400e043c0940c40312090010300e40504070450f00041e44a000000305c90a0359051810b042a40ea001c0101c1001d0208034401e05501503002c1000244507602494510000340c500d80b1000e40d6170030325152000300c0b00c40741e521900070358030b035003501201003a008640940e00c085215282740001d541807405500b00b01040c02030151102403013020001a603030020141c042148502e04a0f0b50074200c000c10049038074024032071500c102e0404158200042c81e254611181c2d94802c41c00c44100c80d44400c0001c0020980c2200314440740c900305c080105030b0f0b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 662864784 1250 662863534 662863543
    0x51b0d0237091a132706020a0806030705150c0f0d050301230d061e060815010e040b04022205130201030f050103171305060c2a03060a1d0708010b03 65
    0x945980d03140c0c43d5180c041c102040d20360303084490b01300009aa41151413031140380d200c1c41c0000c8401e0084400c651300c030545002d0713000b0b4201c0c00300140000d1600c0001340f00c070708002070300c442526001040c40c80d4058000542100039030220810720445d02945051481c80070b8100000714514500d038944503107030743c1005243c2090b800c40000d0780401c4c506420741d111240d126010542d11003034006402081c403003010500342e075428051101c070414041c600040011280f4001c43c4801d0080c241c4c1d0b10580d0141d903110403400900c0010784000d403485c01d404012400529110003000b0195440e003041c1401c400d0400103143c211041180c070a403801d0450180a406c540e81440344224500f4070800030032440d41540c940441c440c030140d240e0111203400081040e140110b2041c034400503c8014151030b550081e205509880d40c2641c1c01404290a101940c20812507052682d41000c0c00060003c1c485075070350100c0c0b80054604401413050600045a80780d0b102e170001c5c0040005085803000103c3d81e03001d102d007070510b032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 662866034 1250 662864784 662864801
    0x3081807061407020118090f14040b0a021303060c09180203101a0426150f0403031a0306040c0e06040b0d171209010504051b0d023709 59
    0x45800140090000580000c0c12202070a002d125141c1c584440b440140e6042c04410f14682d64500c481c00c0014418815400100f0404810203086c05144010340f000070a81c40700307880c000d090702d03211000224900c3c0300d6405022082030381d08a00510550300e44038001120203000f0b810001409000d410b02c440d0042d05031541094542c0c6804502c1c601d08040c075006610054055501503c40100d06d50381c4001c804000d0304e000d0003089410503000078501c80204240303403008003901024041d400091003100c0300c0305040c0707120340403410001c4100c0d83d41d41c0d070880003840d49030507400b03085000d0b0340c594041d62001c1104a02c039503c1210b2049549040c0002e41518807802400c091040d4102203404c00035031961000700c113107140d010180b1441564042201c05036030140340c4980704008946e02c2000345240c0705402041c0034500070401c1d514165000d600100b03006c0e90310445d186d0481030f90690b003401818560108804250301808200019200103141007005910311078074010000304d8a01400880901e00c608903c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 662867284 1250 662866034 662866081
    0x1e0302010e060c1612030f020414130510060806150c0a1505070219051c021e0607080c03090a06020a02010b01020f070806011e120305031e150d1704030308 68
    0xc4c802240d00307130090742c5200e4000811184039100d41c01c0c03240740079411140c091012002d00b90349550b1280c0752581805518402c1d91300c02c2c08544601807100b8803e11495008810510026036641e00303000c1d01761802440600a1034004401011203c10200313003c010301a07201c00c0c00c1c041d000c0c489440c10601c41010031542c0d8500d0711480e210a00030116000103200c0000314942081c9280c100441c2042410000d5001d035082c40d0782c4c403041c26100256404a0024032a40c04034030200000c40c21403003c0c641d10001142d2420104a10340003182e240002c03100590361040c1e99004545107000c29544181c103030303005088104092b03074403055068443d6030140200c80b03000d8050700042c659a80340c450002e40d902e10602c0740710b810019803c02c0d42c015100c41071000c0e0240c4000c0f0180c0d0f45180c46441c0003412580102c488600341e2908901401950b00c0481d4801d01607a00a4403000010141c0343c1007094441460b0300c110b0301440407180c2c003141106103001810055010b91030b0103d0900e041c0034000b05a00a201d155034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 662868534 1250 662867284 662867287
    0x3030906051e07030c0215040b0601090f08070911090d08250f11030a0503030c030f011413051f0f0306050601080c040909030c02030609010b031e1002071e0302010e060c 74
    0x503902030078401c07650f00201510700450f030240010717820381c103040c249100b400c2050300400c200b2040c01940d24030640125801eaa515400c43d60f070b2050707001a040700703006605898004880801c04200c9a030045a0a00c803090340781031030310703401b040028014003005a0440741d4620214409001d000d000004001c14844a008034020305050fa46041c00d420340001c1c0240f0409600088110039103042080c00ca260340e001c400c4964a051500740703102da64100f140e41520049150001113800d0440060741c80c152400940020201c0a000511501500004141c801140441c200d2403019901c070a01c20b0004100f03610072101000d023542042010f803a002080381e0b05110805c0c0031b03c07240a8480048070100c51001000040d18540d9160440d0503410f41d404c069810720480c41803000b21141035201d032000480031022038030300500b0a204141003005a529070105900504a40800d4007115001003800c6840755030440706218500c4081c1914280b83c05040e80141e41d16580036440c0e04007040019000104051050f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 662869784 1250 662868534 662868571
    0x11e08070e03070e06130b03030a0c111005190e030304120b011e14030c04020c0607020f1609050c04030219181407030209150301080d0842030a0303090605 68
    0x13007070800d00503020600070001e8403400b80c04d82d610b691200c03008040041c00d4030340e115110341c0000c0044802400c1592000c181901049880c54039084520500e021030705d500d402c088014021841d40d801d01d403001814410083c2c0c0300c0065507001e10040c0040d004600c001d00d2100c4090401c000200b5051300207012940784081c05090603900c2a01103400c60742035074507242410880a01090a089280080d142c2241c00824680c224441c049038551107442c05508803500744030381500d1140e560982590342d90b0b00d07028071082400f922982d03400c02d43d404a40044000d1819581c1d501003010802c00c3c103c6608010400681804070210710300d030541500c0c41005061101c01c81c100810701c485c0304080e1510061542c0090144002c0d250f06000844078100d16107107a44941c0e44592240e1502807440341380ac0040e0400002425082c07402019130200c02010b030020121455080c42c000b16000e0800d4060b0f04030a60b240550195641001018510b5200e43d5000c00c07071001d40d243c49401da0301c001d01824822079010b400c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 662871034 1250 662869784 662869799
    0x10506030705120a0f0308150102120901180f0603050103051606021504060b180a0c080c03060d050f0d030c090b0702100f0c1a07141e030402011e08070e0307 69
    0x64809448048902850f00d42d4805a000c0ca880d40f00e0200800701010003100740305254020032068862030700142d0b80000c1403000c1c40120780741c000e1800020000041440100e003594031980b56500d0340c000034550107028a842e929002d8264106e6840800066140d10061040040620402d176800659842045c2131604220002c0e440359200307144a0015280340001034103004d481c3e041002c040c4c80103803004c03295121200010007844012140440201c2c141224145110f11803124944207140c580c0400d429a210303041003024a100e2804151981d1040b80a030070000c403014484950f6a058a40b8002000c0025000107003015000382d101882e0440284601000340c2c5a40b060107000700c40700e02d051a0b0315180c84000340d8002e400710001612006c41d40859130080820034039940c0c01600c094a42c0844102c0b00c41c04449641701d448003041c80c1d444200b00c80300030350507200c02842c0c0062050504481c81c1c0d171814107921109648000c1100021100030034040746941140c400408003806501622071706080c600b8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 662872284 1250 662871034 662871043
    0x70206011206021c0b040b180612150c04090605010c02131d0706050942070803150a0504111b120a08010e06090115050703020a23060901050603 63
    0xc0d100d608203148918804200301030381103c00e40340c00030702c851641c000c2d5840314200424902c195140103600d0001c81001c41c0c9860072510090000c1241001e580e50b80b41e0727043c050408490804201d0b544109917450140d40c403100042c500c2590750501032920307039151010361015a0256407005040c08a0342c080400580c175015080340fa00600c803280414103541c2c2801036400c9444203041080103016208001c103e940e8080c00901e803510741260503034441414a070022005a401d007c071450101c3c6842c458210350308100e1200108094107480180c00c281250b2a40d03000740c0c0c0220f4455058001a058120a618181d81d1140240c08192020055101c88020003603c500c103044803420b01c1c6220500e407010500b000c0001b481c045003400c2c0110384807840315001408909080c0602c4c4505400a00052164288650050304030340074803d01c501e0440c100d150550302903100c0d420030b404502a2800000204541d421282c00c0380b105407120401644220308501d0030070b0005031400074942d0401051103601e940008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 662873534 1250 662872284 662872289
    0x806180120220b19090905070f0c0512040308030601020d030b0108060f1c060516180902070807020a2706030b06010807051b010902040b010c0210081302060f0a020d0807020601 77
    0x300c4541846180c110b00000d500b0364006a01408000380401c00300000070b2210103884001e0300d0701080c0d69200d850303000035a101115120000b03140d800350100014891408000807601590a45003580001202403100e540036030401e13a810301d000014441d07656030400c40c038402001c661a04002003820080000e1810380003030009841494207800132070041c0e44410a425114200118010202c04603284c4000500002ca800542d03114006030f0101005004207548030310000420070200c8400d0030000544002d41003140180c1d4407601c02d0180200507101c064204010b0300981e00b0110449160f1a48544400da101c0f00400d49179040440c10000101c40f24103440d0000c2c001d09017901d665590410440300b40c02002d485400c2009001c3e40c155600c40c040d4440174841e8001e540501205100c04019101c0110f20000250080341d6031100e41001841214420f400c9010604400c0c1d07844504c1c2c00043d000e80203641c1c1e4896000e0006000d01c00e080d010032030004000c000c1e00f811010751804000280d00c41c181403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 662874784 1250 662873534 662873557
    0x80109021b15041a010b040b1303060c02010501080106050f0906060318030307170a110901080a110f031009090c090b0103020d1e06140f0d0c0806180120 67
    0x100d4059100e0641d81d16030819410078a040b15965a0700c0c507240c01121200f40d509481c49140d03540310303421140e50136801034160307440712074001d00c1c00745401318841031039120109141805500342e44c0407000031041d004501d040003065002040130750420340d04600319402580a03034400e81d40d00e40c40312040d446040c100c070b44c003600c210303550341c0c03a0303038500c01c1610816031000e01c0c84819010010800c50859002440d112890500f1081c1e040b0543d0381204441c226007040348401c1040c50103001004040d03219542007070340112814004038415010704030344c1d07400303401094608002c000c020040154003d080c0d55010000c0040c00424400c0c103030681c90300016a505805030302d0388a80c03205103d17032640e4000e070115168541514020821420090044000c10442c0300c44042c141d414000c000400003280e2010354140c0c1030003402400c00e403500740d007009010300c04030000712180314004100059040e018072800c0e100b5412109010f200c0c1c84c0c60502c490071220403e6007081c0c4003185040c192441442c003029200d115218 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 662876034 1250 662874784 662874787
    0x111c05070b0c101a0d050a0c0602030307091502070b0c07050102010b04020906071502070c06030501140409051903120c0e01110d1b02030102070f0528020f060a0917071802030708010902 81
    0x540c0d004031500810358504d6801401040103501003180019002c165117000c2c4034590051034541d0012600e81c84162400ca000400b130746024080c1c0e1140000000301d40d8014011100140d07660b40d143c52254101d2446072059070080a0100015602030080c040c204104403400c5150801e650005546070040100c0948803801203110406503100d650304032010281c200b6500001103540d104020081e01e003d0007410340e00302002010340c503a4100f038010040017070717400400342c00e1240d500c000e281c2120601072420341c1042003c2c20f488a01d8003991207009110f0840e40e94a09070780c10204005030041207040c40c801c0803036000c9209004103644c0413020403400d0312440c5190b60480d4503800024007a000b9400007410800e5042680c0013000800035022035207221202044107103036200520038850425a68002e9041030300200741280c0303482e0240c0106250b6525040900790706880d51003062403182c0343d030340c54107440e882490107000381c82c09001c403aa01411040d00c10361451a2205005000e65010301c41c51009640 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 662877284 1250 662876034 662876051
    0x114030a1704080f060c18121b01030b19090c1407050a0309060207081213050418020f0a0e0a0c05041205030a080a051611030f2a01050103120c111c05070b0c10 70
    0x1210142114a5494042124031009c03907080c00e8090012035128088c0400c0c03411004101c1c074100301503911b032145140d0200d100410310381000380f400b901190b4041c5040004000224089440000c00380041e28081c800034510811036150141801000750084000d42d41320210802c84080d0010709001c400101c02c1d80640c40740f1044004d10f44910f01c03500595070003420302d0707240001ca4002901d102078a0307000709c03102034640e6054000d105009071940207061020400000184140e0132a40041c4002c00d0f05180c00e6207000d507951015a1900c10540c0101e95540002400f1080340790b00460982e00421036036420452420130744070000401100d464420103103d030390b10001409010034421360700103040c80984039075200700350b1010004c0341071b03012190018003641281c407031f148600502c1410305807688600c0084c5d1040086d0002e80b040e22006404a9003c160507821140700c0d190006803e00e401460111018840c0a601e07102d4200f526640000e00118428044e001090000151310402c040000d42c0c0001c2070f44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 662878534 1250 662877284 662877289
    0x3030f070f05070c08011a060f0d09020d051207060c17130203160b0d0e03090f060c03040801060603051509070e0d060f05010f0f0902030606030114030a1704080f060c18 74
    0x1030f1043c06011004032000020b440a419046a103010841c103c2448244405008008003030050f003425041c001014402d21a100c441503200400d618002440c50301c078910f095440a00d0320318114044140044040340480402400c0d001301000c42c680d40c1012100c030200409002c1080da00101707441c005544480043e41552014003180c00980c0c0c0000803c40b03426110210581030b0b0f030040540c0d102c06440c040411850000100030f0305c5405800414a07440e046841080228a030415401550710303000801000410700d10074071441004040c1d588004c83c01e40b900b80c04280d42c01047c420f5a60092044004112126510250440410000311541c00b14540701e41048030007006400c4510101a1034000042840c1a1090614048503100e41d0540d13a21910346403014180d00040c0c4056401c01001d0005004240d080000309246940103001c586404440b620348540d160000012954881d0000809200d501c5d0280420f00d85190854018820742c2069015000244102c00b03042c0010800c501241c252903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 662879784 1250 662878534 662878537
    0x18020f0d18050d0e0a050306011503051b21010e0601120221040506062103031504090f0f021309170d1d0106060f080402100e010e040f020d0b0303030f070f05 69
    0x22900702c0110340c401200d002019055105140c88103114907a4040002924640010171a041e100201065400e0a104550540c041e08000e0030803600b15880b0340d039502c100b0321030002504001c400c21045000c00c1210304c01c440c4241307006800c070160402d2000301b00503090741c11103409000f0f405040b40040e40ca01011400c0019a045040d00d00240341441080c441031100c0062110f005440440f444004154441c4520101c4084400b2400c071039001400003c251004044400c144e90344090000300d5242565aa81070490f650f0380b608940419541101400350306000980b2030070302003008000c01800141e40c48100300301003030175200700c0240c200080b0324020125541007d85d0a004035818412800f50101d007490281203a4091500001c0180300b01c1e0b1040342c07250029034051500074100380c6c0c0c10445981704607040c0d180c0002e0355060003c1c1020458494566200340440321070804d0005842c0c944070101281a44d01d0380320440d101c2d07841402481005440828015048001d60800c441da41c1904c20081e01ca6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 662881034 1250 662879784 662879831
    0x1201090b01081303030f060602010b030d03050103050604030e011211070c09020a0909090f02030111030a0b0307031104020318030f090a082410030203030f0403111503071b020307080718020f0d 84
    0x1b81c18500005600c40e015045203801c29412016252001340e141011001c880e002d01c805895684010301241c0400d0090140c003e40310418134003030315008207041482c815a000f10841440c0360324009606014440d00e00c07680000f5110414080d8902410340800409595440c0160b0f42e450781d0702c442c0103042020901118201a40c040c00034072500802d0101c101594100f210380d5014a4241102106540b4021680006490b031040514050302100000d1000942000301002038520603210000710180007000500301c40c50410405a0b0b0f12103040702402a00c9000380e029258a03801210381d83c58040c2c1200212590140c500074010b071650f62018031950700c03402c0fa80069007500001030700c1800315007258020300503a4081c1d03d032410b0040c0b40d682484004220001c8250401d01c051001c03402891040c0700504403581a0b1003042ca44198036000030b802d08040c0d40c0803c01590108004111503607051f40c04074010f200c05001181020042c400d19106445140550b04050b50344d41c003558002044d5603040b103207 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 662882284 1250 662881034 662881061
    0xa0e07181404020a110f030406080f07050301031103010221071106090a0204021c0f020306120f1f0902060f030406060602071d0c041d191e0e070e04081201090b0108130303 75
    0x191070784640b0140d201d602c0b0b4022180020002d00004bc0014a103114042c092040360380d50754a543c1ca540c403208010240f51000300d03895502000582e008030818040e9202e00f002c01d102000090414101c05880710500c0c1e402940e0940082c0708200d46000c0c041054400340750181c2d03000d6540e0800c510101c00c0003038031000a01480d46013900b44440010b9a5014502c140d4040d00c40c500c1c03d480c20164180d0750306114842e1401d030750190360300e520007041c01021484d40325075540300420b20707030115070001c1e1715500900300305220040084104001d00c1820b000d030390020802c0d40050121a4186214080503004214860343d4082c00031010076103244114085400400d007402404222407030030701c0c10203105001520300c242c2e207210f503200c407004261041c4502c1640e101e250352010342201e84036040d500500310004113450f9038061a60000364241d000b0b81ea01344614828580e882e81c0304111842c0205040042e000001703c9443c0c002c200040344d81050b8104d4024102241408100c141c0e80707000c90140006441440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 662883534 1250 662882284 662882293
    0x20307170a0314090d11010f020f0d1d0303010e1512150601020102040b04140a0302030609070819020120070510030f140603030a14090a0e07181404020a11 68
    0x200302800002414005000d07035003d00100400c0c0c07400e00c0000c07030250351060303003500400d154141d81401000e0145141c0c4c40f1b040040b03803045811130580c1c1241c201e40354501203080001211480800580f160100c20811302c0d2107900142a12188140d99000500402c140ca4480b000032811201100411421080b4000c0a0000f9003020841443d00d4600404182c2d140650f0700d004116158018000c2d0307001d507240000e035181024507084031424022010310701c4070741007c00e0000c08809070b142408414407507032104004240051500030010710f0100c2240580c0c8464403001210401270780c2c04032952542d224200d4400b4401e1203607070b46a81c1001d01c50b50040d170b881461078449807450750b05a0890708040800400030440440b80d41542c1d5034191080b00c0c2c065060b00100801e241d05c41c0038000d890140100003003402d081a4809010400c20101500552143c203e4002044441507100e400a2103c0070b02000b4007240521b0701c03086441068a400440b40309903000704050451500c0b44e02c144180c8040303001202c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 662884784 1250 662883534 662883563
    0x10b070305130f080618060a0218040f020322030e0f03010e100c0e060715150e0c04090e0c030c100c020603010e1f0803070f06020c060a0b10110a0f03020307 69
    0x4000c911200c3c0b190708880d005480006072a40d0300710799103405d01d0100703101801c890b640380008c1c14000c0d4001241000340d190384c04e84641403521284240181d242040000503640c2c28141c10806c50103a081508e2881055451020720000c0d0f0b1042c1c01c50140207040d10308078041d004a100183c09400b00110b103036110302c21070300c030498881900c1d001441d01e81e0703403a102c1e904800103090500950b4070507a8030140400348400399160340d02200d9400750303400600340000182d100b91951146094103205035884004864042401c1c081e0b403c0382d215050700d014848004090b003d00280c08a600c4030221140280706c6d15201c2043c2023418020f0000c1924140d0042500d5a01c0d81c5034104d5554030103080c0c4140c40003811050000c0e400503d400c1013041901e03070000041d805c10885594180c0c4800f296042144c12540a00000500e01d000700445801844062400b04049800406000f94289401d80c6502004500420782d00e41074004030708036403015080700500e9540300181c20142d00d10311a03898008d0540340c1006d01c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 662886034 1250 662884784 662884799
    0x6050a020f160201080916121b0f09230a09020114070b0919030203030103060c050702040608010b010806090c300403090f050409080307123c060608010b07030513 71
    0x900b1054801d0304c40442a0702c4145100340d07590210080304284c0c511101e02070018460802c40241c0ba00e00c01d014150f001c00c1520b085030604041a806420b03801c844110030b0200380207901a030005046d112507000c5c0760510705d82040b500c420000c1e00075401160b5800e070410559101e2042820501404010a50b5480c00c0d491711600c000000c0301c072413626020300b40041006030a80744401c00d601d40c2681c0103500f16420340c0c4070040201441004017040c80030030803141d401a00c840c05044000c00c840d100024403079003078100162080b04001e04251050401c2c03002c1006c060246425241101164035440d0024610031209400c11000861640d2001d070043c403c00c001c242d803007010345080d41d031f541d9025102d507540c1d007003404180c5480e880e000300030075070030310001c0c90707984c41a031886614580050b00411015402d45440c5000c4d15a11550a450920348842200003400e168a2410503030f118003040015510f40b003001864445c041c002c2c00b2018a000030300c041410f200c0c20a0b01c8181c2c0103007401d102c0c1d01d0782d1180b5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 662887284 1250 662886034 662886067
    0x40b010c020915090c070f02010f03140c0309160b0a030c021e010e0d0e09011419030c0f0503070b030106140c0d030f0c02030a0906122003040201030b0a0803040306050a020f 76
    0x403040c130540400b00000c0d0352480d0002661481d5910100385003a040d8168015036500040b522040101541d9144d004038405440c110b4600a9180031130340e40d0360b4202103d280b810100034884549000314242c03820440c0c40302090444140c45039900d0005104085054100c0c20840c8841503460121001d00b5100c003040d406510011150411404407901032400341d505803910001d0700b00c0594002d0b50280100000107100c0c1940745400c10003041819414a64041c040d05003007117804c191040000500140541e804c400a20f5014003003c500030120719182c0b4040d584a4481401860b04212002a075017600c1c5013428140d1302d0462000c42680d880340300001000b4020180000e03020085414a9800f004d250b001100b01d8682034203540c3c507110310b941441000c1c3d131801882c1c0b00c0e4103813196840e020342260f640b4031400c032190403960040c400e40c2c9040c0307400010155002d032108035105007081c50041003018800401c4130102d95204101099170b907204c11448009000320101890f6882d00007031124007a404018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 662888534 1250 662887284 662887321
    0x51c0209010e09010311091b030405060405070515180402070f03020d08070503061806031905060f0c0c03030a0f020403021003150e01140d060609060806070906030b0d02040b010c0209 80
    0x9845108070304102c2c08000c0a2682803001904102200c030003203210b03082002050340d1100c0551058030064280c1b8003410000e610842e010b540301d410010501040100510008000f490211342d03a40b05420b140c01050498418060441d011070381c4d003190152940c0b1242c05640c1d1040d008030b00070707400441b5410041d448942140a1a000034110300001344c4c410300803004c1da8050b401c05002041d40b007c28424003903003403d000e05190b80c5442400306102400a54056440103640305002030b1100741081c6c1d010f54003e41c0064031010701c2010911a17003542800000940303a000090040201785055424840c400034455500b001c0d4000145407400450346405400840c0300d101d0401c800712182d59101407000148400f030244640c291040e500428280c0f80c021052410b0f940a00400190070b5550110481100d0043d03001c921140c20100801c0350300743d00000c0e010020100c1741000e01c41201c401000a41e050609e0074000e120ba90394040c0400281d108101404c42c40c0e0340a080005a41040004840e03c42c0104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 662889784 1250 662888534 662888537
    0x2030d39030606031509020315040501090902013c1e32160c0f06080714121308070b0a0b030d090b0901050306060f1204030e04140106030c051c020901 66
    0x1090020f141c0d4400e1251048010600c62080f0105040c5655070003c0e50014003059141d4071018001d0f001a40c45d445200d000341090240042c11072040e100141041508107003456070141e0b00366a0a0082000320000c001d40002000071520602520300c1c1540c52107000d0040f021440440007100207425003040e09044e054079459400f002d40c81112108100c566010010182400c1c2d05010480200c40d004800c4038020f403041e40c40e0805192542d4082d2003200c0c3c01e50200e00010113a201307004009412a100c01211250b00265914000b202c06961400302c4000d4103140080f020110010280303c1007905607400941c6c08203041c59a03080c032010074409059034000152280c0202c4a02042c00b80c00391800030202c80a42a00c5828901640c0c010744890300001c0c4016041401001031074191035080c030040c900c050f030140c450611400d29007002409001e1400c51240628544403425201000d400c0046046580620380400c80c11444a4100c50500800a04092507601844015500c1030301c0d401403e5030381c20a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 662891034 1250 662889784 662889791
    0x12070c0e06101d01020109080c07090b0d080a1409060310080d021501090f18030c110f0906040504020a170a06050c0909070c0206070b0414060703050702030d3903 71
    0x1c1d4401c10003030510210300440895100407480c9244041c141d811592180305000005540c04251138a50199200c40d4040080c1c0d0012402405410401e100d00a0008001e0f41c000800c501540e0713500b05284558030f501d00070711400d2204101d40b0300c0c1400031100810000b0300110380b82d05018190398072055840c010a1614062001d81820f0982700068424003001c81050317540c0c090b4600f404c1c0000400c7c08680c81c1345001d03290502c54201e04402c807424031400d846582c8401540c000f50a00c08014085c488080e845110011501150380e0f450030546a0000c804a600082d84d450360b1001030340c0312071194026000c0d44168500080d00c0d040100f84040403c1c018035050000d0342e80c00d49080a140320ba1240e40b07600050f02c4000c0b401481c4900402d80038988050031240c43c0c03030061b40303428280700c42c11501140c81d55141030002451030014044030350010700c682002d0000f810b0411029440b4020040320060042d03507a92030070001d001c00003141c584140c48a42c40441e8542c0c40042070354080241c002100440d00307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 662892284 1250 662891034 662891041
    0x60317131a070201031d030a0f020606010c0c090506130c0504090f060e0f0408040f140103140103021005130308180306090f1903270812040f0e040512070c0e 69
    0x48055441456000448942c5010501d60041d40280b0b8015010f182d0380d5140c1c0c201c420300d49810001410b25007450b44032103504689184000b4506907001741201e0410a00340b0005001032080314010043d10007400000c03030a034ac2d038000455041c0944020b140c06050410400c03e00c1c1e00e40020003001a030704000018401881110301e880103943d41c0340303e0b0b846803049400004212400304002c054206200304c809526181e5190b2080010350f07040c1e0800c0300700d01882c0b030380c0b10a0341da0580f0134001c1d48405034800424035891a00094041c0350b4998484003804400114040f0034220242460091907016000039140d0840402c881c0030701d80c2150f9103074003a12035900481e880c25030008001c00d01080b81001000d540070480d069500c0b160240100301c0c2841030011101d14010f60402e1140034481d003040100e0042071500480da440d244031016400c180c0300042009018043c032845440080c1c9001d1002818140c4a515003249444054a5160242075000c02c0040400000b04494021912922550380e00d079107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 662893534 1250 662892284 662892299
    0x30313030c08100203190506060c01050f100806150105090a05040e0705010e090f06010f0c02100f0207151b03020a02130501050307051f080709081504050f07061403090106031713 78
    0x10040d22600c2c0b100c2846d0308140c040300c00a0304407a070b02c814050260350808282482040c01c1d642e0944a1004a0b0030880c10400d00c2c02410760040010b251400040600b414840780c080c0c1d0350012001c10904121001441d80e890382c4404401c4002000301400c2007040103450000241c43e600320b4051b10340007030841105030201e494058443c0e409084500c00c0c00c0c42c245c480740c0042d602c907210a180c000a01c0101c1140b0307000361359140c01040711400c0c191543d0098002c2c1400007030a03d00f691f006150116440c0354000d05680d880195003241d80000d0800d40010302c0c107802d06900d0013506100095102e400c500d02896000d60b242c010f036040f5170301941224009500d450400008505240080802c00c0040780415001380c86803403007640192950800300d040c2519030b295241040c10b40030032a1100d0000c21b060008100c020041560508040406001101c1c10000c005048030340100302c41004010100c080381401c00294010700c01580d0005960306107c0e03000410760403a4201c5048080300e03022145000401a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 662894784 1250 662893534 662893537
    0xf010c0201090c090213150c0b06010f0c0201050706020c010e0a03090b0315061c0c0507030e1804150608011503050105130b0a0207060b060f090a0b1207030b030313030c081002 77
    0x65400f001c60b40d20103042050103402900400d0840c14400203651001481f1b54694604029211042d515034030003000341c3c00c00720004140500510f040000d05119207028580c03040c1d000e032009c0e509290040d030310003150801002034001d40024545651a00400010701c050004001001c28441d44640040d80e98401c142c4015000885050350744404501e07916004e45802c1000303042214090a1420312000060711a50448859000b4440498000540882459040041610b05241c01c4490213003c807044180c070030700c03c0c41c05000109503445405450761001d5050300401c0141c42010003c200c1610396041d40b21006d8000d110031385540d483c100c080790074011003036189402550840f80180d581d85032404110300950107000309031034203542c4060019003a0340c2c6400400405440506690310b507016001004a45403040d40100d00c41c0d04100005c828503042c3c03a0400e81e1068240c1400207030741034003901081c114400e030512044434000c4241d000c020010032101ca8003da504500c210794220381e90b2940328049 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 662896034 1250 662894784 662894801
    0x70f170a0b01211208150a080d051b1b120609120d0b090a0b0306011d07180b0a08011a13030b090c120606031203072c060c0f010c0201 59
    0x41c01e45000040c420240700d08074103010101842c01d81e500904607511000c0480d400b2000100004900d0703030078000201c2d02d80e1240002020101c0f042e22809203010002c42d5540072050428041c4a00070030205407104c2260050102c042410013692041c0071400c0d004030000207001f10f40361151100d511020400c0d540040c40e544606031107001402c844000d603000708000c0d0000740000407215198000c0d20401d40701c40100034050002c66078040be04618202c10103081610503003145210b40240d004060754031060030000ca41164650500d2101c00aa000840412a10070b40010400700f50004d100e4000d50391100300c4504071f51083d28400559190384c941c101d41403041010721800b01e20107850a00104204c02c64248c1c110294508a07100790f1200302c0440c1e49000840d2056030142c00440030003403035040600016070f10999144003e45035241c084000303000c441c4050100c0703025842030301c4051841548540c442c80001c0005041c15215040c803c030044d903607100401c140405508201c0303400c00440c014000d0901 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 662897284 1250 662896034 662896043
    0x20d031a010807141306021c05030402030d0509060702041a01030e070513020c0304121406070c020a0e190e03090301060503070e0412140a030506030c1f0507080c070f170a 75
    0x1c00c3e071140c910454401003034466810103500104100c1c2d0310074407054086401030000350060030b901c4101d6882c0c140256a4040c142c0c00b480410000c0000690b000f140c000c241d280c842c01c00949446111010800d14015004020f41080c40c0600380303000302e58a000707540c900751800d80c3c080c003c030b521400c01c090715503070a84209604048010760050386280325070050302c18901c521080b42d06199075101043c1c00101804803d0303507851021803800007109401c0c41025409441c0c0d09201c0d0300c05403281c0c04100d44040c584100c50300c1c21062000700d0070040d59903002403102c603c2d210f03040c8841035210940c01e031a6401004200d21035071070204006081c1c01d0104812046540102940c2d00c0d82c1e4881c0c4a001050840c20320907002c00103080c14402540790080c00ad0034070710102d0340c1d00082c02d00d880ca06040c40d00e4000000b607032141100c526034840384426400388601000d03035490199142c0001d8070308064039003c0d400d060501e9000c0c40b04081045104000300f072040310b0300184d040c0d40803c40b0300c0c42c46840300e08034031000c1e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 662898534 1250 662897284 662897297
    0xf042103240806010b07151a130605061b0a020d032705100810030c0e01030b010905091b270a180c030308070c0204090b150a0e040b13080307020d031a01 67
    0x1100d5448480a8030303c540c0214108150346109480c80408c071819080d0038544401f4141101445051a0201e28141501454104686420040003590f540924800c0c5402d002c1d00e02e40b400c840700390503c840d13040742d42d02400070507220003285400b410064030040c00040000030003008046110051680d88126400a031509400d100143d1048400c0302e00141110302103007529400000003040b24203441d00800d41400001150b50542c40c014a0b55a41a4000f001c160b0030402806120035000c20007818804040070490300d0b105000b0080f0301c184481403080548001540c0519540d81a64003216100300c18130102000810030018007140032a0702038a010304500030f1040e06100190051190507004066030515044007040c0e54005016600c0d1000116009040b603403d1040c240d5011601d140d201c481110021101420261079005098000b80081d00c1d40e0814800302e02040604900c030005917800c019070f641d492a051030080d603030f071801e064a000004d260880ca4000c000c10014440f00841c0143d4610 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 662899784 1250 662898534 662898539
    0x3020409080903060115080703050c091207050a141002121206041b03090b100b070809120727090c03060218271e0f04210324080601 58
    0x100804480c2000c5581c0e6000b04181c060760368040200a000703085401700c5540030340c140311006060490241c060b80c281820034082c0f00050720f03a40d099034505d03407040d100030405540e00c02c0c002d440c100541c0c3c007682d080030036a5008507000208a0300c40f42e0320304040e0f5010240c104440c008070b030f565189820000c00d20304144a11900c83c100c000403a600114014004101000c1f481c40a031500e9851a50340408070f9941e50001c4200105914040c0d03200c0204041e80c0c4030140740c814152514411190020b110080010301450a81d40b4003904c001c502108000701c440040c0c075100d030080011090b90000860307055030143c8912910082c0181d004483d4001542d00d44140b4503516000130b90020100320f0031a04000d0020105501d40e44845840c041e01500002644003024000c0c025590010300742074240d0704040b0b400d082c049050f00c0348503040034041c085101c0342d80d160704117150004031000d200682c9584044d4a501a17942c5a00320000c01d0031084050b003503a003039658402000da0068400e480c1e280c1c0244004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 662901034 1250 662899784 662899789
    0x210506011a0f0a0908010203100306050a0c2f0703050d080a0c02070b1c110a030c2c060408011130010504050a0f09081b06040f1104110c0c130c090302 66
    0x9040c01c610f0904000841035241d04480e03003640c10840720340d81c58820030107080090100c0383c05030b65000300348008100064800c820340105403086071031200004840d5805000810b11309c2c1c803010f03c144c294100035144041d81700d1030400d40b1090100f05a4001034811404525400300350301c2151403480441d0010b0904500d0b00700c48183c80d801482d0042e101911001d1861034060039070080e2101d200e121018181e40b0205075001034112000d500b28a000c02a200e080005150001c0e114104200c402c109148c1003201c01b00c0c0040e03040d210b1a0004420b550820011103041c51705c0760040d221711203851000440d5010318a80031034100c081100032940001c41c0f01d00410107400c081e402a900501030003408a01400c14a80e0b25042d602c681c902140e00041c002101b5211040000414095400000207005a4241071321a4258110080c2c4060f10006000c1da062120f5030700d075030000641279000c1215035201d416403007090783c45800c00244280180c02449104120600d1885814a15038864550140a90a6809 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 662902284 1250 662901034 662901037
    0x110303070f110a12030c0c030c0b040804080a030203040302030c271f06080105090609240103181101081609170a0206030c0d11090f0d0507210506011a0f 67
    0x18180038031280302d5000d02c0051080c403007446600d006041e134040c08219150004c1c04c4030039507244181040341c01105600041ea200700301c44102d6801c0b200015440c1c0380c07810100d1040c443d41d0b00c100441d03c0350210001c01c01d5000301c080d000710303402141a0303042c0201c01c00520072590a110714040421007840303440d101411803070500b190800070115040b480c003a00c45035204d50380b469580001c00401c010340300421070740c03411040c2d60794024825503801102e0300b08480c0440c90f201004d038a04161090a07812a05143d00c00d40c01341c1c4408403a2542c078292416a801c110420001c6407242c02d0011300c0020001d075150034419102400c80009a55540d9510b10300f40c1d43c0710761003105481490880c050340c0c00810144c1d40307800186020300070340e01c031107507803800da00d40d0f08000c482d160500407800c0b48082c017a034451a0340790031103220f907510180c4800149000d01d203061030070094940c11400c03072580c500880c0131100c80036010112416100700202c80d8541d885040b140307005003500121b0f00301c94604118002404c40500c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 662903534 1250 662902284 662902307
    0x32609061603140d020408010b0a03030c08210103060903080901050f070c020f06030f10061b170c0d2001090b040305090a0e190b1e01081008030c0102031611030307 72
    0x180c903401c2480f054450221607030050b1000620250049401c1c01910300a100d40c0704c40d90821100441c0e60b91455502500c40881440d024005034400300794125400c000c40c029030000801d0300d480f9200740d03841f850203600038440741409800098010001a01d86101403184c98000c0c82c40a5400b40303107583e010310072101800c1c0d5000407a046600d0710143c0f1540c0e100d50002d5409074151001520092900c20314548150403140d1200d8200450400101c864441d9103084282d9035403c011401c80c00d0138151455a803c0c4a12680e20010b403152141428801e9400444111035411626121100c1c607a80c0410509031411030030041e040c0340e4a400402c0019000f00010140d00802400b0226416580c08050161300411519000a20185001000c840e031042c4200302c140340084a003500c2200703c001140b41400c003007039030781418800e44101044c3d80305d40462040c801029401b0450755240c6544c210103020750400d64082c0c00780701000f61004c44032806424200751000c04c000045080d030340c0f0218119003e1303450f403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 662904784 1250 662903534 662903537
    0x20f0409050a1110020703170d060503100f0c030209130b040b090a0903020c01030c0e010e0604051e090c0a1d19031115090a090908090307032609061603 67
    0x41000c031000800c180026859140104800400840b803c420704c00b80340e00d02d030525421500254010300028203c402820a0301c40181300c2a5106d503020a411402490b0540011380c0c0362044124225081c0c500382c20100c175021443d0400d1040100d04a020b03800da005101289078003a001c06079002e102c1e240d035484012004002003000c10060000030200e1040b000603504504840d4560514500703050f01000092480c9000f0300e006c0100c4041310030010002d40150319128100580781290409a6a406042d6405441c0061000c0c50403907254154031401d22034154a5805000b170300001840f06075030340d003e503501c02c0d01c40e03100c503811401e60012820300000d66054250b0702070054000b4808090411070124080d40c0f103200c0315400c401d0700100b04000c6a00c4100e450a080d80304010b08540c540340c5045a0007150f01300040800c0c0e240c21407510048500440311003a03003510640e0300010600c0000c0180001c1c0011880190300304042e10241407131148a0742d8100740d04080b041280489028103945111740e054083e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 662906034 1250 662904784 662904791
    0x5010e1512010305030d05090610170c1f09050607021f0c17430510020a0207180e030f070501020c0114060a140a1521021b030a0c020f04 60
    0x80c81d29416403442038205130351550000c5054112154640304042e00400d6142c0104400c2ca4150280e18003c00c0a004c0e80143c0302074034405141c2828100000907112070002c1a46036800c2d40507a0a10200d0718242c6480e0000c0c940210004030b03420080b0440d00440d8000d8400c0b103c1003041100c60410201050640f41040310314100c0310f02040000300c1c041d081c4040d5961065480d009101c04009021010680c881c80c94008546414992001038540b0440040340044407a030b104a0708019040003103510014842c2400010b03040781c69a40481c0340002e031048120038810701121003179050210f41011100013416481003250b012a1807182000d42140d52040c0b00140c46e0007502e0303820301d0a4a090040c4c070501c620842c810b204c040d1820b01c0f81e80d40909001420031505906410000705804180d10a007822511200001c0604c3c0744030b203508186660005150185401980c1d80e068000d44c031004100c8002010b0380f80700f850188020085076500075199440c0c042240c016020895000404140594070603038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 662907284 1250 662906034 662906047
    0x130602031308040605041a030f011701020d09050f071514090a03021e040f0b0a05281203020d0f20100f020408070e09030d0c03140f090c06030105010e15 67
    0x102e0900410207403085a48894076240b402caa41001a61070303812408030780390f06008101514803291a0a0b04640c00d504920308129800e000c424020301c0780805c0008074500341000f0340e00748100095502050103107182102c8d0300c0c5642d6802c203600c2906241a81c00021103405e42c6034200c0042c80007600800c18010920420740c1d69960014410403040c0000d1240d51000140a0301c00d8a00761113804241c00e81e031071091089999400028074030242600940b80b1907840a03101540441903140c210208003800c40280440c00c2c1c640c0a814000f0019500841c010300c58070f41000851031040c00320b00010145925804640642040154410000210000540e108003684040c01384480c1c0a504c8450350241d03030059585041484450030400c09410500c0402d040c441404116000042222450a00b9a40000309020201c004034082e10101d103d140804030f40707009110724842c8484025000e06413100480d5034081e2840c00784051400244190707800300c0d90b0085d804426040c64201c0544600f903d5003803070b00e40350 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 662908534 1250 662907284 662907293
    0x1093807120c09121e05061e0a15030b130b10290a0c11100e090708090d03020f0f16020102060a1a041a0907030b01171306020313 57
    0x100e034100002407100c401199100c01600c901c0350b1080d21850720051442c1030840300d45400c015860020004100d080280030384440584808040700d0303002003036401e00d003040003034880d810b070000d2080f0310014a4800410182c24039442849003c0c107451540714081407664490804401c80248041080310420f21a03000151442000910460340da001d4084242c3c200a55240e1910311212814209603441c0100100e1003140d0091328030014143c541200b6019652038a850020203003c2e08903040401e1a142107011501300441d500c1d400c1003540d400500d65140c0e6422101c1e20030079183d1703151907002400c0f040007440c420380040c0321020300707a035083d440d204814801e0000d95010041c446501001300345402d0466a051000d2074003c1071180c0103100c2180804040c051702241034a9041c852030b43c5501d205803a1518072420300640c680180b101d00700346060000903000d01049000c00380010401e809201c1c000c822071a1442c091020144001052512580e407503000b9800a040305254500301100c500004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 662909784 1250 662908534 662908643
    0x20a1e0e060409020a081b0105030919050a050318150304030c03271d16090b1e130f0605070b06091003021207030302060f04050a030305190905031b0109 67
    0x10040c0b103008087c40303518a2000701880e40528082410481c080013030141b141e000180441e0072083e20001422010440c0c03070807902d000d0a00a000700b4502010032146449841005201d003001002d8885440b241c0c2c940403c2485031000b1500140820030020032200401d103d2010004031900d42440852101c00e19408064101180d03800003002014462540f404001000e24a9230850040805900d0b4000a03071400b4203d03c005028544460307c01085034056608081840000c1235030508001e543d4030309207010101c9101d81c50041f40310580115400240315807282003140c1180d40c00110020dc40c0c4c40341c000300401c0c0d61010749a5580d0314100c640200150382c40084c1d103480312000c0e8008210080c5076180103414190001d20802000303807004c0c1040042840810b410b49801d5051038005555940d9044080034109542010401c2501d003420160400500100404400d00b00e0400c0d03c82c14800202000e0a80c2c6617040700800c541c4000d004130078032980070b03110007418030700040c40881281130804030400b06 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 662911034 1250 662909784 662909789
    0x321060305010207050c010e0a0312140a02010506120303010f05090a0204050307060804030f020d0503040209040311010c03091703150603130215040e1b0a120e19020a1e0e060409020a 80
    0x280e943c005800b0040200400980ca000d4078207080114001d149080021299800f40c40058200100800201007262041c00d801454170f00015945407601c4074054006d000b0142203c59074020501d08010300074510b000403d80f81200e035004c0b49200c0c00e0f81800c0074031002c1d07017000e015201740e02d40903c0045420359007800036901814042e0f4601d4124602421700030305100210811000799040840d06000d816802021039a001d60142d44001c4561600e00d01200c40242c10f41080c1038030f503c0d2010108040b90f068200485503401a074150300c2c1101c120490400e10321050b1051020318207002200009820201c2c0038541c0001e502a81008180050300411804540000000b4261000150038481c4075101429a6001146082200c480341080c0c00580c0a51040c5e424810500c45400e181d08406a182e40101516107000000d507075180c2c10051080d50b034001c4902c0e003240f081000e0700d004182c01e00d90f20081d03520040320b48400185035181465100070010050314036604241c90b84040340c096240c11104400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 662912284 1250 662911034 662911043
    0x4240f060801150b03010311040e1606020f07090605090114011b0804170a02150313080c07080f160b0f09061810020a210c1709190602030703210603 65
    0xa0750760050100002010603500b0400c4d8126043c001480440c45000c0c454129880548000a000000281013460502c070070f00d008002650000300480c1055000c81c1200540c2a500c086076070854580e44041c00347c50300e5002ea5900304a00d140100a03461310110501900c010605081d84001520100e800307d01c2d04140c41659614130000e0700700325803603898000d807402c40c14000250400210340d5001444104d40c802d9100001800800405e40445000c000001240e82c03001040d56100311541c10303c1c1d2100401d01c602c0c01d03c3d00502c250001e80000c040f40e401c0031440b02081100406041021218260b0041d080d0500746840501c149041500c0b544001c1c41142006441c0010107412081001074504048407450115000201d8180001d160744000c1e100e14281e031210043c9001d0030b40b4040300d00c00880c03030300a800140040070034030582e40c0c080c1c020107201c8002e0781c0c1c20380c604115080c8440101018400c080042c0e00030001003000c24403900740c095901c00360000403504a04000d143c842612080e40041d01c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 662913534 1250 662912284 662912291
    0x80f04030309090501150305090f0106090b0306460507170a1a1c061e0612021503070908010e0c130b0f010c08070506010608160804240f060801 63
    0x2041c1904400041c00400d0300e02000e2025604118052184070910f600b0a024541c441000c0703149017100740504240080320300020440d0f40c2c2e88040860190280e040d1480c06406518080b402c85c0300381c9100d0501360300c00e03010aa12480100320f01c80c0e010300c02d0314680c500300141032516000e401c0940e0007914090380084d942c0c400c0043c89060804404071000d044400c04902c0c141c2c2c0404202d040000ca03088041c011159605680e14000c086140b0071040800100060b1610388a5485601e4400740e4035540000040c0030041a0348441030310b109403c0f4841c02075440000c2d9454400c1d11103120f0021075018940341341108007d070790703a01c3c0b4be401d403404503d490010b5000656801201d091040c04030072140d0111b01d050000d0258000400d9406918184240c108102c400c0c503407041c0200d040032181c525500c5011a9110761795140700504000041d1840c21509107040d210b14032062080e0380c0103004030703049800500c001145240d120740e50301c4d094611084c0c0756201c01c240c0705a0201841900014113a820011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 662914784 1250 662913534 662913539
    0xd020d090b0f090c0a060f0e1306031202031e07030e09040606090f0b060d0b01021905010501050109061701060f200706020607020a05070b09150c010f1a030c06090d080f04 75
    0x30602c2d24000c2606140e6801045804060360399102110100c403018280003008448050341110107800c0d602c604da8008040030319070500c01072075a1280003100e00030900320b0418145d00404907124890300c1d02c41f000c0d10443d80c0c1001e806c0b001400041920500ca82043c00416103101c0200e1b001e960211000d840140c1d58420811900c3e5142c0514081200010030811036203007080300041080c00b4644190070115070301e112201041c1d0080201c030701141401c20b0100660401450264040c1509004050000d03202d50000103200d17010385e21340a007200504521960907030901c0012100440000070030010001c0100b0881c0a002c0c61741038014015507940050700080c3c1c1000c00c003a251800181403101107501181000d030124231b01049050a0383e412502e100d6407150150001002c2c04021541c80702111400201d00d12015415480300c4c65a89880c00d0501404607a103a407000000c072000031007905908044040380c680e01c0c0000c000e012128000704402204403103600e03006906e401071840401491030000d000e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 662916034 1250 662914784 662914801
    0xa020403140a0308100e04060507020c030708010c0e010c02061e1905030412051201060e010e1008240d02091b0a020f0c092503060305060723090303040302060d020d090b 74
    0x24552203180a42c0d1300c0740b001d1030455600441c02e40104080e00c801e50301e274080307428a44207100c40019100000c044601c501d8864070441d0007845d0702441e82c008270300c13801460025540122a1011219001403415040c80c601c400c0c4485540741a81c4c40202001d81044038000030070f40541141d080011035a40c0381e8032498a8540308406041c12002c1909001c414043c01c2c1084d0220b580d03982c15100a481c142541116140050f1800d91419801580c8150094203c3c1d4070306902c0300b18a48503e45540e9001854211180c0d807201c00f0040703c0c0440e8128800417150000350400804035030700140901406500246e80424403412a0451f20780c25005070406040624415810080c00b25044402c81d01c070b05c118107045030b6610745049031022440708045440501f11210307001340e11400040d0340101c142c81c01450001401400c0c0500b40d03c207882c0404141c0a500c03d4050008260b95182030098015446d207400c40d001c2001d6908042c40d01144140c080208a0320107045c0d005071340c1380611030a0f0311012401c10148 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 662917284 1250 662916034 662916047
    0x9052a09010f12080c1203040609120c0201050d0c050d02030c0403050d080c04090b13060e0108100209030d1b06110702120c090c0924070311030708030f0a020403140a03 74
    0x8482e07101d00741003206009441808109800c0f50350301011450740c8042e0401007900f00038040b80d003041034100120400081c8401ba4012414240c4901c1c81c3c0014260f182d5015222403010307001c0a80051024403c80c44407aa00341e011030071452007801c04c18281344940109006a03030007290042d000442c007003805c20802104204c0b1055600550414001602d400d40c45159640038030700c10440e086481e8001c0c2410360b100d2000e50407860561100c00d000443e02d4060042d10007400b803045202c03510070030361800c0ba014654425190030540040c00f910100300303095002c41d40310085408440240c0420f0109070009070701c51140110111106080340e80702c800500400104040300740340d4400b1030300410790001e026a644c42015a004032401c80041d00c807000717800480d0b0f00e1417a080c4000048443c40d10718007150b0064102400b2503d100e550303220064294080c0040d02c03402181c0005040030b0040c00881c2010410071074540c3d12a104030401420140d40c1c4d111520034247d04200140260408480c2c4401d0550164 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 662918534 1250 662917284 662917289
    0x8071103030a06090e120304021507120816261023150306091603021303050f060c1312050120030703051f1e0801060e09060708060108070309052a0901 66
    0x1000c1d2840c0d0081c095031603007c1c44010402440b45902c00b00c0350188a46000645071541d4004407444801005410060299801551012400d296031598550030500c01c119510b5840e0007421151790408001d04030180f0030001a04503941c1d20070742800480c603003541007180f202c814030074101e02c441c51000350203100c60032441c0e1440c02d00c03461003081000f04548031045100c0d041701007032041302c1061114500480c001e010355610019511035010002091000000b181c03082c1c984800d06407038041e2520501c41d805446150340d024141d110b10042000600c48541d19100c4842c01800080f44914010030351042001202c3d0803a02d02d0b55020080c00700041c2d05105071544a00030310340d880680b0240b658a41d03611001c40c42650b0411100400082500300d0442032f0000402c8000000e01841da1940203520041e10708803006a581c1c4100000101a00d1107480c03036901030401a164840c950310343c202d084000c1d200c181401e03507842c803c20002c0801450400d44808088103000c4010540c02800c03400c2080c09030069 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 662919784 1250 662918534 662918561
    0x609090510060503090106031704050a09050f0f0405070306050c0d0b010c0b1603020f03270d0c030e0d170408010c030209030d03380103050703140708071103030a0609 73
    0x981003060340400380c107445066503920b09000c3e40f6a540e00d40441d01620043d00024105202415241c411841da040039000fa47c0c4212068400240c1b91204c0c00100c03042141c010403054203030804580030801042e03103160414060320940d84801e40303944401050320b0003610420001c420028500007900014030403449402024a402c2a100e441c54440c0300c2d2100010340f003030917456900391030502c0d824001c1e070403180c2d5201d015485070703128503060701550b01022070146a8000d09901c0c48120603400706c00301c1c136140f51541e1a114544005000d0b14112626103548810a4002c0d035042e24040100350718804444c955040051100d654a0400d05210b00b524403056601044c5401408410410307540400c0f03162400005281c0003403c00c440c90407103081c801c80c105294214402d41407200701c03e400748090400b404182070301c041c01543c5a00800b03c2c111541200c800c8195800c250200307880d14170844805400c41183c6c0f618143c0e4003403204181e8211384c02541c604d1a15603540750200300040040c0901a5600c08a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 662921034 1250 662919784 662919791
    0xf0603030703080424060315150b0d1e090f03020c0a23061207030b0901120b15040e0f0c0a060305060d0813091d01140601171e10060909 60
    0x2035550203802407101801c01001140c2d10165070301c20801d000809008170070404814400e05a031b030304044820f8100c00004500c158180103120300b424030090540812038820700c410903d400200b8000c500149104000c0207070f21035a02d00714054004203401a804814007905850045000c1854040d1034004e485c11000e0007a42ca4040410207071485203129554500383d0000c20325604440ca001510600c0348a007100d4044030410140804298140e104503000c5c20252541d11860340ca50f5441c48408019200c0206070b11118130010f2100c01c13904003a2503e4844c090408210315420012f420b0405200154024042d03010302100006031400d0710000c001852503080800840c10000302183c0d03a103042c540f000e800803500068038030384044010400f8000700a401010050400760202e401d610040c0200b030b120702c0e5801c3c8281403083d01810b4200f1405001d05864110060000c1c4082940c0303003000030308040b00840c00c6403560304a100714100c02d034070483c0d580d01e20710009400c102c1c000d810301c19550000c42c001c0c0e26 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 662922284 1250 662921034 662921047
    0x31f0f060e0903040e040c05031507032d0b1f120b0f01020a0b0c0408030f04080f0f0c040b03100603030c03020f060601050733021b011808130905040302060f060303 72
    0x2d01000702d406442403c2e803540c1840da81c6051089a605540c1c3c0640d8041c442c504a000c1c80c1d070079088516000d02c3e1166410300c0150040740c1026610041e128820b0b09460849041400c2c507c590f5010081e41040036004054104019410003800c501502c102ea000c20a503e94080070220240701d6000d0b01307041141c60305c3d008144000000d50700c0e00d21540c0240080c3c688070120300000000810b48d00100240d00c11aa6100d1680443c500719403c1481482014821204000221480410501c902c0d00e1410020a403801d6030400300405130a80d446e00c560140a00c12914000403e140910310156000362600c4500d50440d2030000e180c484290000b403403d4101d042484840d03a80a0100c0b4400e64100040d090044005405403003060b901c405803804c14080c03074200720790f0110550050079a0111001d00381c024003403656542404d8901076401c15007028101f4030800000342138440600102030390051400281501ca01541080311016601500940e2114003003014601650840c19030040041d0091400c044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 662923534 1250 662922284 662922301
    0xb01030f02180906120316110d12080717040f03110a0b0c0d0b040915051807090e0f10060315060b0703030b01110a15150305070b09031f0f060e 63
    0x10b00200c6104400781c901290310b541c1c034071071140900d8040805890351010b00c10b0040b400340001c004116450030707642d81607510b80c2c41e00c070507007191542d04442c0d03800c4003801c6c010707085985440003032440c401d0201c0d14424409000300c140c0044d101c1e501c26034842484c42803c1c00c0207000071401e44005006a806074510400085203074610340e80121a461400c0c2e20b80b1990311003003001e030002d41c0a25400502c2c0c00fa05906101d00e10060740301198a1080c10481c40c0c88402540400c1e00f0b6095080c001e55100070020043e02801c1d604c40c040294452042d541a051108034540c1000700c1e0b0f90f40d04900c0c03901da54060041c8001c9040f00ba4055002d260104811b503e0840b158642d4003410002030103045d5030b0600f0b0314499018510400480426a042d6044441240303001c0c3e009150100544c2c180034030303285014040c181401102015a0b4206000f0302d902d44c42d205100340f407036124004003a01405482658001d22004103c2119000395206000c07404002104041045410a030700c1401c980820034140901308 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 662924784 1250 662923534 662923567
    0x909020715063305070b133008061306080f0c01030615030b0a090507050c07050405010b030f0c0c011a0f100813020607080f0a14040e18010b0a03060b01030f02 70
    0x21403c6986440444425509880602070510040e02502198040246055241291408440c483d040216200100c11054011041b9007400c201345a030100b0071800445010b001c0b1907a001c04d005010f04c0e5114240701d143e10669410358410070260380603a00010140e0300502980112071420b29003003282925001c60000201840d4180000f81580e58020035056154030903141f000d0002c0b08010f2140d070900e140020b0150703103d070b041856180291300b070200d6107261134021b2074125200c81001781c0c10358803074500c070064603840604411340480040014208105003801902108550144944070b90031151081c421805c0710a4007042c0321b80341a0790a004901d401003107054110b40400312074088418680301050480c400c19101030128180814040c90800b41c0d88001d001d040c8181c0d4a4140d030407144d00e0000712500941c021256080750400026240041440d0410076400d42e080000c81c1409006010514a40351034006541d03440c0ca80058590b2560140200e5800b0b003040401107141040c58512110072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 662926034 1250 662924784 662924849
    0x50c04060c060207170d1401050325080a0c09050f131410020d0504020a0501091a03041a0405060411120a120e061801080f060112050601090902071506 66
    0x500000354000002e010080d070540d0a42c40e4404134442c1744c4000761408440c140c0088403d244140c1c2054914610744928000300c5040314400790041c00b054114031800240c0d22600382070f0043c00b5105000018503040100301c2c081d901402410002007450802101c0030a8038801054811003c0000003404858450010300030003198102c1c01c1c002141c45102031550400f007060071500c0c041030001c10900303200a0b003a807010703000303605c00c80300401c0b010750f01e50043d130f4508a140b1441c000ca603000711550790340404071030040d51b205106185000d1030003810840c019092400790b90079102c651003c001c00c8100010500322114440080f03034206403d008000c80f4035600c0034039074401408400340b1000c1540d43c9000d060501c10560004000c2a11203a07002c4e101d21151101c82e0300035001449000102d08481e03520800c030b50080d40e069403003c01c00d60610390145c02420b0b001e00340a040010640000070748920502c09030180c2407140303039500c0302c040ca90300960040d5000c5820038482000582e400d85d40000441122840 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 662927284 1250 662926034 662926037
    0x9011b020d020d0302101a0f0301060e040f08091203090f19170c060c0d0216050d110a0305191118041e05120403050120030105011b1e0213050c0406 65
    0x60384401ca280c00c07400c000c5030b032440071040b6050403242c00085014001c491002c4074143d03008c000d848103020800d82038400900c80d400c1d24070b002d0300114010802d2a02a001e0050103881002d14003e88007001c0b440980c4c802070122181c0e0404103030202c544c900031001c450310120031203054071051003092030175010300628490325040c0400030509612a11090040355490340c002009c4684031850a6902ca46501c1d104144a0060044162012240c4e01d0b2a50240a950300640002d40c90740f101d94170300001341800b512980d07100900c40d02c00400514100030300344034400d0120b01c00c0e4140c0610f203442040b64100e021030a2007168503000601e14400003202c07031540960403814000e9160b031a120780450f25561040d001e0100e0041030340c1c2e9248546c01d4001002200d21680080180f8410403070031144150802d8200d105915040004000c1c944c40b403494051402c0d605010081405034940d80e41c20000400212021000c07080803c40003549041120700341d403108401000d000c0f034501070142000f030703108901441b0b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 662928534 1250 662927284 662927299
    0x1180b0a0e190b0c0d0912121205240a0b220e07030231051512040506040317090c040504080403021002060f060d050a0b1b0d0209011b020d02 62
    0x41982e40c941d440c0000b40c94400d503000704034a40710002d1800c141e00103001100756106481505002c0c0b4822002d400071903000300c0300418501429076500792099200c40b820002c200080044090b03803602403081d14061402010328005095400d094205101c0350f1651080c413658220b5010008030007803030202c901d03040700c4071049611940240c0c4408035120301500400a0548040c00700a0b01c1c9816138000c0c90302c0102e02e654025880c414002c543c0e1800da89030900982507134207a904000c1c0d4101000c19901c45c04607000e02d0f5050800b507148512050380300300c5060f0f03801d0b40040c00f0b01007031503005003080d40141320300d01359900a4908403210542e26000c1f031501078000c0c0d540310009014820741c04103503405103600410840e5030744807d510007903403000155000d020f81031803000462074904d40b175242c40104580c42000781130040b500c1d0b100c480c2d040d8401000140f100303e240600c2400c072180e42c0000c0103840d0f00809c0050325566180c00051100c2c010f0074802414803040c020b188050b80e01da0199081281c1c3c11640310 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 662929784 1250 662928534 662928557
    0xc06011701090c1232060a0504050c040c02030d0f06030c08060105010519021f05073b0604150503150d2f040e0f24180102090901030f0201180b0a 64
    0x2001c0200a042090313030403041003000b17600304250686400d08504040700c1110010f49800c1c00100445100381c400404541c88003c0602141c1490340010070303206498010743c0e06080e0000c1506042d610000100080f10b6901d078814070070001901000000380800310000c00842d814180041d01c1d91240d000b4541000348132080101c040741c400c1040034203c00407800b108412008188069001d090f003a01c80a01160303090b08031420520481c81d001001415001100d0341c950952404880b1605070142d8281e0020305c03c10000c261122307400c1554162000704d94909541c0d150285603928052120428030340b29851901d130365030201c1d001c007080d14040e4505807a012003018015054010700b0042060203a0464100060210031000120b40b14a98074000025902e621022492131400c2c0d0b42500c0e01002188801c401052940c3cbd6032000ea00140002400010304d0000c08000141c030a140990003281c481d03560911580455a11181c06510742c00c0050900d06064141182264107000d00c41b000420020a00c10b036 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 662931034 1250 662929784 662929793
    0x80706090c0303050c0615100509040b060723060405030f0a180e070320191b0b0105040606020d0e040b0f060c0303011401090e0c1309020c06011701090c12 68
    0xd8081264840503110100c1d07a80d240c09880c2d900110103c40d0f55024031070008608181c3c01e900301d00d28090003001e031255268509401d484980100fa591a040313070b40e885a16980d92a41001030000c140980e0120284400725004104c0e41c00144844580e240c0200c0e0901001079000020380340052a0362100315219465a036084400407001c0d406030942e10640c0e100042c00d0380031100310300c0c09440540c4d800d1007640039807c40a03401c041010012214402d08100981d10070489100300540b04006141c0141d101225211400000140402c10341d45002c880004010741e240500c0340f03500030601ca0001d00981e00c5c0314600070b003092036402000c0380180d48a80941c44281d0728802200301118000700b40680300c0300640b10346c0c0d503250002d0190000010110a00d00000d6002c1d80d2920101d6043d4852240301e0f54034100c1c1e004e02034100b070403500c4007650000c0021480b096170b030014002c402e10220040c441036140501802c02e0000207940e59a850340340602ca000440c81e15076510090780c0000399a034180704181d141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 662932284 1250 662931034 662931041
    0x6090e010603020a032a180b0d0b0607020d06020a0305070c1208061908010b0f090f0c0c0307020603040308040210140f0f070605070815030c1315050405070e0301050a020412080706 79
    0x34042c50103c034080001500c41c06c0022030900031010340d0387c0000e4a144031104070300b00d0b0240c020760420101c24880c041480c90103402102c0010700190a0030708241c8181d000c00c406c1c0d480514102c0d00300741c0220320004041c1d030500c11142e200c9942d1500c01d910000035190301c400084134161250801400c0c00010722240c440304400070340c492180300d0f9000050b41c2d03035000e1802072070403510003445180048644085071502c0e6080e103006555280c0401143c1e15001740d07114203030b8099800000c00780000d204034409a0b441d4405548036502030303210154589041d2040084110301c3c1c501d102c00384114501120719181415040d98030781d4041582c8103a850b181c08440c0c891500030440018200d90405d000c001010b644500b0349400703084909032401ba03042d4201f04064a8482c0c42c0e0506802180c000060340382100c8941041101400310410001225107400109041c0d0b4011a500d40201d54140902c09550609105031030703021a940c0011401d01e42040e03010340800e281580c0140041c100441d0740c8045c00b81950 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 662933534 1250 662932284 662932301
    0x1608150102010b1011150c041205070e0a0c0e1519050408010507050a090812030406090212070801061a090a0b0a02070905010909120e0121060e010b070c06090e010603020a03 76
    0x521020749004c050f803004203040c84c4a0003600381401030244075002840604030590081d203442e46401d0402c4e0401e00003010002401000b62828490140001041d24074284281d01450074840d020850f000d201c580984103007900001395004039508042d07070840490560070344241d407540000c07100d41c1e1041d144045a20b801b564200400c80e5182209100d11250080c0003001060305680790a5a01c5d0303603442009840e409000501c1c80401800c000040c0064440d501c500e04191000b41458901c00d0440301440c5085202d0300484020781d901c200c00d1140c8408506c200d50241c0041d048645480d030514041689019a0b101d035180181000c6038066996000340310020140071200c4040010b0f40e540c40441000d4070240e00182d42c100706821280741e40038031941002c03c6503001a1600584550340c86840c21700e81c05854240503a480e60740390046040640d440d4403e008000100025031120010b05060045c008035920803010f201104008100c403400780454941100c0351420010307284d0068070815400b504005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 662934784 1250 662933534 662933539
    0x3120b0d02040f06140a03080a080c07140d031505060f09120d020a020a0e071d04060506131404051b0304050106120302030a020d02010204060203090f06040b120f1608150102010b 78
    0xc0d4501100c26401d1380b101d411184012005142000c000040c040741c140b41e400050004202084185601402030480c039410000d040c110034503100860300c07010014440c4425400650f0068602c881c034846d0305008481c02407104070451440d1910f0301001a0040c03240301e080c00ca1002011443c9840c0f55103043c1b100120b540800c00380c0310010b242c03440003900e03005141b00032441800c022001041000d070308400c41d881401d045d00e801901421005c2940c0b54000d0381403403075511907101c880108407529442e010f01708401803900680344e402c0c1805020220300081c0c00c1d03074500441c50a8200b29103020b043c0076010212a20303034540c9a5949640c2012805844143c208100429010005408141d400402818401220740c01c3c0c51010201000403030a1f44154466500181d00a220910352490688a03450b440c0c00c0003400d903894071380ea0780d4030303e00e10f5003000300500d441e44068410006260310b10035080b5071040d1070500980b4190b80458024080c0f42024201b070518140300524805036034003d601449210400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 662936034 1250 662934784 662934791
    0x10141305011d0903190804050f01060b0901030605040213050d030c020d0f02030d02070f050f0d1a0106021504020306040308060301020904061410020a0804060f0909052d0403120b0d0204 81
    0x442c6041810814010320b00210748620a0001d102c1c01e202000359070340010000d5181001c40001e0808a66406e00070780181e8a90007402540c403e4444248640c0e00280352010040340c4401c010000581140c07442e90000c2e01580c0108448071520b000d241c09441580c008850148904803e4241140d1181b404a0007d420541c074400e2072007480440c0e40300b89180ca200701c0032110414030280d01242c07141c405215248951021040034001403030252807920707500c20043c1040f40b00300d107140c0319030503600e944403440041001e10000620081d03605120180b41003c0501c0b858800f4245940802d6440f18001c0015040007400000728145035001e40485155100042c001c3c4865030311202140d103800b40705040c0910a02e00c800040c60418000f00c0d0106969400c8074034182054685201030300c030308925035150810088203110108004ca824031540c1d008080140b00300d2200d0388529510280d00c60308008991400c2c00b000c042000185e8841039001340452840d001181ca4015000800c000101e50b01d07000b51300c90705 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 662937284 1250 662936034 662936039
    0x2e11030d02070521120402040e01021317060c03040b07080c070203030d270f140703050601030804080706030b100c030302040f0611150609161701061e0302031014130501 74
    0x140010000c0c1604414003491100c4c01481c2500a0036114040410101d0311002d00010058502680484a841c0940c8000f51034410413000e5a102100039402407030048400303406000d109401004030b540c0c03000003014490b24504050b20b031100d0b20b1034010182820007075104001041410030806a6514950180c1165215440300780f02c403000c3c0c503503031480312917103615101c400c0c10450005115601442c1c02458020280e0b641e03403100c0858103d007800400c5248528100000003560800c4014000c5008004041c3c68900708100103082c1415948000e08060506201c402c80740d0320280c40004a2607030713080181d4074021070320341900a801168482030300780407000400240203802c40c21a0301440e07504400e0341d12251f585c0e6051b50580030140d68464001e02d2400001c1c50001451540c01407161140c00d0520300b001d001070121300b44401c240c12460028400d59054040b0044282d2131030304400c141d0600b54294070741041808051081442a21f403882a1171807e020b550300c8154011040c00500c403400e220542c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 662938534 1250 662937284 662937293
    0xb13051c170106030c08070f0f050706090b240108012301110f250605040b13030c18200d020d15090c1101090c09020304050c040c08062e11030d0207 65
    0xe646100e00841d1b10407000510203441007409034043c8403642c480d079441d10f140c100101c1c1c882d0800780b0304443d85a0786001c1031000c2804590200c1c4a204c06041302907032031f1940d0340502c0b648139082e1101c3d4140020800148401b851a440820210543c4045210f041e0940c0c001200c401c680b00342c9040e1940107421095240850105a9112400451040c031540108401d03243c02c41402034403c610005805000a200c0850580e0052280d242c541164828880d1240c403503e00c280c1c2142c0c01010075102103002560001c866002d0300325a44c1c80d100d0090b11000c01004c1d8100c85200d0b10346912821a4000f58000d05401251321540e00000c000400309141c5031901013800060051680348400314400c4981c95999500c140120f2030031a611056281c5001e00d0413120501a4201a00880e01802181d04100b080e0310749110307021241119548100f50b90402c40284020b200f4040c1140c9024643c80b144680d1010350729142c00000422460b29103090a8601d50a60842c000c1815901d046400083d0704001d11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 662939784 1250 662938534 662938541
    0x230c04170c13230411090408120106020a0618050703020108070522050103051612090206040902120f060a060507020f0a0f030309030605060109082e15030b13051c17010603 75
    0x650340b100c0b08500640c102000003003c1074040307034000c099000001d01c950803801c040c04e289030442c1c4a0401203040100134208080614003d0b042440164403a4602d0300501105009441d92220040030b402c0070317891036031203607903c0d4040c0f4000641803040000215501c24440c0c42214241c40516118503220a9500d481c4804842240302d900e00080c100008554000c038505103406c000429030310b07440080c0c0b01407164000604504c10041c2c1e403110080c00000341c081c038140024181d503031840c1e40107100c0d40b500e10700d4a40c404201170a4a8080c203420700040c00f145402c58111689a60111210300904404200080c40000150048101d10244a03000010150400d02001c02c0d82d20030001401250380d500c0046804101074800e8102c6540301001c92600410f070203903a0300341030005c40c000d040003924100c00181518070703138400300300d0301c465815081061100074a00c072074110555500b407104420198403003655480510b80030030020340551481c5c1014500641005050400715914a07203950303524180079008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 662941034 1250 662939784 662939801
    0x604091b12021806011b0f060608011d010b03030403020402090d0c08030c060114010f1d03060c0901020609030304170d060e10140111060c090f0d0501230c04170c13 72
    0x514400b0f003246490802980954400c450603981c40362a0381c030040c0076014403000e003a829902d40c004040800041805030103590064801c11002003403a491462403944180d0382e8035140001d0380d140c28225281513502000b12001c490b01118050b0b04c603000400040c544813500724004015450418000802000101c040c11000e0703c04c3c400d440d031503aa00d50604002c1d400710881c07140003501c1030080c0c1c9406030050450140264002d50480204041180880e282c220203031114081910081100360480da81005030580c80b0500c40c01442c2542403e503215505140b10031a00f0900e0368004c40d00796040d000540c0018020905a095510a8100108521290202030003240405422440d860320300703500403040f4285207040a00144100e40d103140a1503074036003001510f0ba9201d06050310b00545603492902380080980500000100f0f0042001103512201c030119031841e034071565804001039911184140d408544144040c0180040002907071401c3c003031180b100e654400d460300270010340d2025641c0503850 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 662942284 1250 662941034 662941039
    0x50f04031404060f030e010f050c27061615050c0301090606030e060a1a46030206031518060906011b0609020f030703050303061c05060604091b1202 65
    0x3107000c1d14460500207100e00d02840c004a4111604800214403a501a05425141c0c400001b9040c05020081094a41c165900764940101041d00e02070512650f400d00060070301c401c8845202001400440e0541c000d01c1030840e407040e00038100509210307070310b61034280781c1d034205004120300d1402490700703815038100303000e0720100501d028800310701640030388103032411000750b4001445c5036640c1c240104054800c04264852100400818150030740b0703280030000310f0700e82c15480c00308c042d0f50016240321000d06a00c00c03454405084031009940300c9818900ca03045d80e0301998441c2d501d54070400040143e220110045402c850707a011a210b001081c1101c403400b48c1c200721401c40f05030300e580c5c0044941c140c142110082241f21501d403200007074a15402040c2892024102c140e0b140c141200080c2824006e61081e00ca0b60070020400c8094a45260030152100c0131900800403c0e50356116540e82e04401010140241d9a035000301c01404803250120701c0b04281d80d0404292262902c01d40004201c0d80c01c0c00320f0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 662943534 1250 662942284 662942297
    0xc080f040c0314011b030209210705060a110f0d0f08040507050a0308122d09011805160803030115051e040f03051005010b07020603070507120906020d080424060504050f0403 76
    0x2c07043d100c3d008541910700010550008040b081e8035092700f54001030940700305880350510018040e15184060072101a15454100c18058840031403070402900410148003a0050900f803c1e14542040e002d8061041d03915160500341d840e072038240c0c80d291454010035880b80c40c00f5000020010b5101c0103000d11101440c4e2215141c03036100001c0101150582c45030144420701d0f802180c01000e005840e0741c08650b05001003500941107110b132242075181d03003050742ca44e000f4000c0e450882d0703041209500104403010045166624140750300e84400300c0004600c0030000d0001f54103602c04038540242c4000403000500da590f031079a80200350120082031100315024007440041c9403030700700d80d44125812107400324281c40c42c00030303103034201310381071344005c2c11002402014021340c0040b62402e68130300301c2c001940d2160300c6094244240a07242465585140040001002c104000168604000714041403002c070703244e40c9410701c80d0001c000f07040ca036040260820b1403d002c020034500100703600d5029501075103880 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 662944784 1250 662943534 662943581
    0x70f1a16020708030318100923030414130e0625030506100c05030d1506090915060311040302030a05250f0303210e150a0c080f040c031401 61
    0x40c0d031900903511460f8056001031000400c1c01c03089891001050040c10140c0751440144041e00c4116183c2c0340d42a03880070405842c0510182c84c510500c1e0303140040350000d608117803424601c0c030000803900360502c1c040c14600f414124a40400e4002080e40c41c0e06505648452400d82004581440d403042d08041c02a80c40c00312441243c000e2007424054900501300c00310717800c6035500580714280400000c4030035200402005100c0c3c0c43c2c500c03d107003c02820510f900140c1d40f4091004141c0e0b1041d4002c04102c40c0303030081000c1461603240b5820100c0d1000e050201c0c03000c4042c0783c003101501559002035014000c4d040f01c0c20400c84042400c01c1d4000100e00b013012805002c00f802410740d20940669100f268112074140007081c081c2d404608030044081080e0080c3c1c90581859080d20004124603039541c3c82008002640c40100080e20f5005028030000c000c2003181c1c0b8401001d000d009082d4150512214005c030b801d004100c001d0401030758000b0002d81100d0741a0a510340280b4a28952003007074007411920 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 662946034 1250 662944784 662944787
    0x120a05100b0a050d140319020705100509061c0204090e010b090117100e03040f030303140c0c0a06050415060303081008010204060e0f0a051002010b010908060417070f1a16 75
    0x1c9050f2500902511041c0c000c940e42c07100854200c50124801c2c2c0300130f11075646151442040910388290540c050304441d89800e082c840c4603e5054071301010f00100740004201030b1110b009030380002c503403c0341c140d06242480003081c5c001d2060340c001c20b40a034109a040d40c60f00c0015006245008003d60790300441e0fa98903001c1401081c500520405150490449800d061202d40c02802c1c0c107038a0003003524906a03075040380b401400655881100404d48403955801c40e800b48118141c0c0c0308091350f03a807600d017050484283d6160321602e9001041140d4402c0070070244005003030b0031036119502c04420030140d031712400e02a040a034112071000d01c11640781d402150704c41060080d501150565140c0260444504081121420702080c901d908550004e6000540355540703400141208a5500002103144106d13000410601441c4c00c001c407194081c805103c0010305035103100481900b541941c0b61a5827082c0340040050944540280c00341003080310201c042d40d140d03208140035884c50601c248110080000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 662947284 1250 662946034 662946049
    0x24030e19110a0e0f091f05150d0321110d021903020f0d0e0f012a02070f062a080301091404120503060301020409020d0506010e011b11120a05100b 64
    0x58a108103d065011411041039502c1c41d0b40c200c21010240c446500f0030201c100c8954107442c0b6046005500c460a0010600100e10150052801902c0c0b0380c03034841081c0c5010b0604401704451155016801207180c10401d401d81c0300141c0c005d900b0503c03954608150b980d0001139004400d00f000c1940c03000200140c0a0300034401c845c0c100e040d142041d401d151840303072120014000703080c4414050107030fa00c6000c0300680c20b200d0400842c170450070741481000200c5501016030310020060003990f1091805000015a10307158004564661401e04140318100360740e11540181040c051a4501403040b03034804208040c000381d4103907091031604010003902e44100350b1601206550181110412080c401402445800250350080c40070b0005031506503904034890403a4020304e4030002e015600c2c3c080c46a41d6a0202c41480111403d00c3c000070b0145140940c0c10b030450f0217041c001d21a403036079950107400d5194800100e0400e010b100c00c0d550261a41d042030340c2c54000c06550061306902d0804510301c2443e2200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 662948534 1250 662947284 662947289
    0x40605030a0b0f0a0608010e010e071e090c020c0a030b091b0d06200d0b09010801090b0a0c02010906021219020c030703080a06080a030c030f0924030e19110a 69
    0x660342c428580340d01010390642003014241c0c000d11030b01c03110003003204c05c001d0141c40c0c91400b446d000064017800d0f201d035407414040760b074000c1160201c02c1c0c0725034507101041600309002c0d43c400b045d000903a5001c9260036458094400b02c0c85811403001c800000074013401b20f414900c520104010b503811040d8100c507903800400f1415185601031002481e403004030300154044421142c580038610f900941a2401c03803405d0308841883c0007038541710400780e4513606107030058a004020b450024020342c4a6aa240c0781a9000100b080c141381c0da0f1044441a1a1f100350800200e00303030090021503071444412046800540308503034140800c0c05074107044840b110b0b184200d07000300781e000c40078500b070848070348e8212170012000e40310706003c0d9259080403c07035100510813016582d00c0381d02c80c0aa030304140c0c60042c10304451a0880c0081c801081b204010445800050b0f010b14032509401c5021800b040d039080d00102100141e513542c0b4411901c0f40c0103900380074800d00f41100c1c040e5000803c0c030034021041104880090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 662949640 1106 662948534 662948543
    0xd020102251b0f2d2102040501060801060305060d020a150c050d02033001030f03032309071a0a030519050f160206091e010b03010f0b040605030a 64
    0xd04600b4098008130740c818044080000c050302c0e405051740301d2038261684102a910a00610a1042c18000e0f40140104460350b101c5000811000f400d0003031901003441c000100d11b441c41c00e0094004072581c000e00070100b0358107000044009000d0400c001d028010380d840c64400140341489041d4031407840d0f500450f21000016007202a001848007080c101003d0010203044500030840305505507030704203041c402c03070201d1803408800400454041c8100d401a00f004056090446640d80d40900c0700c0d84111800c031a280c0007400b408810b1744201a204400412500c1030450180c0c200c60f1740308203010000e8a41000d4494028140c0b0400c8400b07144182d00b81c020083d420500f28070000305018640300600c03003481c040643c01d9440325034010000c10381c120001100d110240c2500149407509020b0001d0001c50189107094024012040d2251708c02d03802c0c00c20200d500d040000310058000c0c0c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 662769784 662949640 := by
  have h0 := BRFrame.cov_init 662769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 662769784 ≤ n) (h2 : n < 662949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
