-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1328
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:24:02.038038+00:00
-- url     : https://prove2.me/submissions/d1bc7b29-8be6-4463-b484-f5bacf321551

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 238669064 ≤ n < 238848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 238670314 1250 238669064 238669097
    0x31e0316020105130f0f08030703210b04090f0209180d2a03080406050609040210050310080708010e100c200a0219030302010b0f132406050c0601060903030206010308030601 76
    0x2c203030081c81ca80617001410fa2078000d190340c03078203031540104a1a800c10803122002c04c3d00024801c45003280508009000581d1000c480024812401001d50186c140f594610600040d001d41c955a1402214241900d4940262078000d155449184194070780105994441890180845040c0842c510303005100e44411400910034425032844c084001c980c1603400e00041c84914420203074490001e070345d82000c0e400d086e00001e010890812040c000c008001001400016000e5116001400740d01708650b1415196204d00c1d02804c010f15423020240310f403c1c088413240c07500b40560814188161101c0420b50f04a0303620121001300340082d801e442c4100541c0000685881a00c0341c8210245011001900c2c198a0000e081d180e07841903092081020b40010003a9550b20042c0e26140180082d002a5904543c1c0d50001d08403603409070845000245040003543d15000320040048003105000d4a0882e0380310103041c1d0b180040c500010380164400c900600c0020308100003150032600504043e4000d4012421 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 238671564 1250 238670314 238670347
    0xa02100e03040609120b04020402090415091a010305010e1317041e05040b01120509010605060d0203090d0c08030406020306150d0603030f0908060a11220302031e0316020105 76
    0x52060380d0300000d410018183d105541d8405080d4001c28040700401d20340342c064000c600900013070b1040c0da00151141140c0d559500c482f02c4c80c0009504010301d16503c901c1c6500621000301002203203603c182c526403c1358482d00c00d80e03044e1101c500d410f05090311902201d085051881000311890400301a0410300251050080d10003000c05503454011000da1006201c0080007941c021400345044c8412038007140c1e00b05400600075078030150006040d540da4420701d0b0140100d90302035138100500081c5420501c1054000310703ca8844c0e140cc803040301c180d00e041110031003142a005000c0d080180046000545290011070300b00a0040010305000c0c008194a0340c6a40186000e10078540e40d5001001016081880010340b5605820070481051401c4d071095215440140b10802c4a0384d40d41d104500228644151000c400c42821007000c09050451170f20080c5042d804203078820310507941c1803282050100d441d049011280e8002d141803402d04803842000b00c00107101241800801c1c4000440041c0034203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 238672814 1250 238671564 238671581
    0x20705030403170403120e0303030a0b060418060509090c0102030304030c05150a0207060c0e0a090b0a0b1c051b0406180305370c0506030c070c06030903020c0a1a0a0210 74
    0x148102d946030702d14a000322407040030851b00c0c0144448080e07204019500842980d40c0314282c2e200115500c42c503400021100d1140f034004101801d042400d101d04810154081c03800d48400340c81c00c0c42c02340c032084003e03035450303055608141c01a40f0810018000038866491720070824440c0088500c1e00f0035090300107540c0d503400c890003c10700c0d5010600d1400e0007602d010742606403441b03084c11002010b0140c0403400480ca507004401c0e0f072035181c80c3c1e81c1031917403180c90040c00106200c0b019252210070503d5400300f01d20007144086815400d06021408101c03c0c0f601344903402e102d4880d038516040c60036105840e00d041d002800281044103030030000c04910f0500c0030846d6042084540003c1ca24041c1d42015403403c1a650550004843e44801c0002089002c41c1029160f00700d43c043c0d200c0d5141e00707200f034507803080c07203001407501c2c00040000a4a60b01500811302c0d0f04d02c41d400782d40d981d42141d81880741000701403041500094804018020042100c002030401500d1403050343c42c20380c0600c0c0c020042d5280b51 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 238674064 1250 238672814 238672853
    0x3b0f0d030b01030b0f03030a050a051c090c0b0a0c0213021b0708070e010807031419080a090b1606050901150806072006010902030601053006060705060a020705030403 73
    0x441d103a545540c0e061043c403510103011110500c5071501071022039520b0040d10050001c0c403200048502c00741d80100f05a90000320060811180110b01c844080c0192520300c004071400c1d404004041003180030f08054403174401503603846410b070300116001c204030090074400b8104501d508000c0992600b083c4e0b40003860845d80b07600289a80c80c03801c1042894501a5840044580c000342c006000041011402c1c400300da4000c10381103165141d0b504158280030390300e40c00344020f0f0103d20f049002c12844c0000b4103180c0d801e54807014006a62600804d0940c032820740e0401000d441c40181000142c119804590408450b1000044050b1156040c0e00c01d07a201d900b001c0400e50202d410840d07801e901481d0201c40700d41c5511884007203241241c42c1a1303079038010f02a0344100c50b0044000b403020b0741305109603070380c00039404068602151a25a049000c1d1910515500108501800140b20742400c03811a41145c0e80f1000600c00307076460007100ca009400110040b01e9500041000001003040304030700c04c06c00e9508 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 238675314 1250 238674064 238674071
    0x604020409020f090403030e070503030703020c090915130c0603050402060a14130306020910020a2102030d0609050a0b040605010221040e101d1b0307020a060c02103b0f0d03 76
    0x50a0581c2d289c111160711280c407941c400c01000002a60105c4c2103184000188c90340503083e00c920a071182400c0b030b210b00e03a02141581c1070030000030700fa1005190041e0b9001d05200603400303440e044201c0545c3c0c0101c60180d0012020007a1020b441e101d881420343c1c4049d0740b0380244c1080049200e01284240c6a0b1042e14a1f0b82c004c50100342d18034280000d1040c4410a00040041c40d025a6a44500301d480049050440c841089081a118002c2c0201d403040c001d0907404124503911442000000c210546010301d230b0703900d0100d20b10b030942080e12400003070750416001000d13160b102c1003014100c0c4c040b039000343ca0044003d0100007148003021700c04501409d0032396094100340f07041c0954400315050324070641504070350010910002a407894180e407980e51240000310303a42e03501c8220582c80c0141c0048001c0c0014900350540040950108060745404500e00f0107100ca8023454548401e03106160504802e480b4210289021900941c540031546900e03c0056600601d80b0007106030800c0500c80030040442e44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 238676564 1250 238675314 238675331
    0x5010201110a270b091804030818070506070b040b0601020d09090b0d0804030809010f0c020a09090303150f05130204080606062208010f050903030f0c090112050108030702031c020604020409020f09040303 89
    0x41208100d08801c05034020a0821f103041c0d20004c24904015103d9070703405143c0750300801d2803d024001c9201034000a4a60380e40c800d202d00c2c0490390303c6001c45007510904003000c04690036610124140c0801d940c41d5444038a5142042c03403d00041108a03006a4405c404640c41000075610102070f000841c01480c0c425184c4013800300242103901015260f904001e040341c400f00c0140c0d900000c44003911890030340001d504115250940c010181164503e260300a1030100089880c4da084c5040142c483c251580603164000382c0e58803040c1e009502840c1403070781040300007440e1801c02201801c16520644200c640c03c0c0d001540c042c05500e003a81211500342d46a4160140b281c00a0003038513040600d0400452a6150140f003010f01e5440c0500040d084403400211404560b1280d10400215845010104510b594800c0c0d42d80c3e5030307440304204074081c1c02200e00002c8140303d050720110100115802a144540d41d42c1d013000700414603408200d900070003035514a4034030f85030103c405226038425100021843d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 238677814 1250 238676564 238676569
    0x1406030c06130f081b03070614160812040507170606121c09080c0d110904061116050c100921080c0d02071401090e06030c0402070f0c05010201110a270b09 68
    0x3e545c2e079030343ea010740c0c03058604000c0c8590000410006070310704c1031120380f10940c1055030b28082c902100082e14040010400f000000c010320105c6004521800c01c55030350310380e9900620501d6901c90440c1015410410005440341000a1a4422600c040065590b0101e00110304c1c9240c0c0400480e940c0012a0b4140c24003001c1d0081001c00040c440403141c00c0c1d145c0441c0da481c0010400c0b2803e12600a441c00004281004565009204e10845403822030391160651941110700c58003201e8103940714460301505400c5400c0581d4081c02c010b070b0b01c0e41c42400940c1018160001e0600b114010206248218a910045210300e4040c00e846044c0ca806440da0314181308000f440c002c900d800c958140d58071013507499161f07038000e00814100c030001e14120150780e9031400000e041c11450000e03107410a0000078641c00304076817200c03651980b42c400c0205025443d1910012402c81e02c1c082a840900c003410401113a00364042c461884103203913034192107000403141d40100c2410001c03e500c9855811000f042d41c6010b031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 238679064 1250 238677814 238677853
    0x10b040903180608060901031b0305100903020705040b03070e040f060501060c0209060301050f130c0512060f0c0403032f07061107060e0d2913061406030c06130f08 72
    0x5003030134139000f01213041c09400169040418403005000c2032310407891241d48080240b03560010341e0480180c4040000700100d40c0c001e01041101140107016418000c00d1604d007612500204410240051204d41d00f41a00009401030280040e40c828550a5081e000651140501c0d40070b049a90f0b540310f840e28003803051121346500901414400e906000401c05080c0014066950052614240e8090b040c0309042601d50b00c4520782245410003030124205080d4940007890ba809041e00b1503483c45d090380c4220315a10603000d580001000a28559641d28141a010450030b001084808403802c5a031030418000e454210f00b603001c0e10224170500412556041e0a100000041c40d190804d8000d040e0a140000c7e0000c80b12800180a0100b020301c0a42c0985403015089844032801400c0d02035050040404501c504600404c41e0402e00b411034010b07481032405103290080e0809001480980c40310410405180c0201454000c104103480b4006400384030071450100070801c141c00750200d4243e148101042 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 238680314 1250 238679064 238679069
    0x512040b18030d0e01180e040503030610020d0e06030a11070c060806240d06170c1306052d0a061d0a0302060301030b0a1503080a02011b091205010b04090318 69
    0x20340288019020f40e5400a428008440003440c0904858881042e414000f03000780c3c1211200e80c034002c042004000c000001540240c01c204c555462a800c8000c00f203981e64001038480000400707141c94020135082c10310285401916000d40030410404251750150903400041c010750b0996681e920030410a500850034581084050b6510004012070081c2d00d00c10075151038260071804000504800b104100e81c0c03042015040c1c2080d01021032901d20384845c0e4503c5103004280c0b14100d030041c0042900700310300c80c2078101c480103030510702c009000c480d00e500302c040000c1c042c03c01a0002c07150040140d40b40d40715a0081d105903191450112640c903a1001303400c46251080e40601450441480903a98400039641103035803080c040a4943d0710007540e5406010f500480f00100111010084200040e01c000350450b60600d50081140c072114a0000500e0000709510740d005c1b0321101e00900c440600084108081400b580010034600140c0d808102260400d04080e00014101046864500c5020842400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 238681564 1250 238680314 238680319
    0x1504020a020303150f030d05030618070207080601092706060e01060f0905031501031203020c0123100521070f0b03011e05031c0c020904050f010b0901030c120512040b18 74
    0x8038000300c5006c207544181034140391040c043d010001801603500c401c240030340d58944003001601404c01d02c1003e0b559524070301030500180901000460803803801d2040318141d264a03800d141d0b01005507981c21000c02029032059580c4c44d103581c00418100700800405000b0201a43c4c0d800a0701102070703004040c1100c5420140c8250440c2e071a0070102e025210f06541500d070004080486149004002c0e8000d2080d11943d4410f03500b03010700c50746903689a004d02080344400c115600e14aa941c0d000d0b84201d02000d0007455400b00910400c5a881140640d4440d1401c8021301100d40403a1507009099030301c401540294120100000103110b24031402c18042e0208a9440b00c9401880c01e000004e82ca454007001140b0700c03541c0c500d11600b401481060340d541c1c1c0c1b41d0060304690090038641001c07525680318a00d103c0807982084004140f0342000b41e2020704803600004158203031030401c80e10328800202c951095550303100c2e400a4000700c0d044400203000401c40001e0302d40c0c0e14102c0b81c4800088040002c0c7c07191 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 238682814 1250 238681564 238681579
    0x80706020f060408090a0f060309110306090604150906050c040f0506030106050a2604050606190810020f12090714090103081e0409020d06030b0112080409051504020a02030315 77
    0x641001c0015a243c00503400419603440e140050040b82000e2100d030300c07604400740c007550001003054051344060407060103032082c18401c5100206066030345805a40c081c41980c0701e200040c1c04114005100e5900900e1181c02081c5c400360340d01c40310b050314001e803498080520000f07001c001800041816000409055070600d0071985001000b0300f081c0214100d2505011100e01c440c20340f03d0150b480c07001e001d00400440c0c9854102824403030785e90340c030403140103003c2d51040302e000754041480c400140031203c41c00003e0986e02c0d840e100000103900013103048450902c040c0480b11104481c0102c5a210380d20300c100901c8441e1400e1000c600702d1441d200da0501402c45a001440402c0c0d0b079500b116131024640b0b00c1e8040380540c0e0305103103031180700b00e0f801440514404161000010642e0f0401c04c1140c2c026240c140c00759881c3e0207940c030300c0d0b41c00c0e1300010b2002904101c1040015a640c102c02c0d0f1112a21090342c66088a440c0403c0590740814495001600000104441c0c0c50030100c003c40c00140545941 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 238684064 1250 238682814 238682833
    0x1704260105010f1413060e1008030c07050105090a080109210e0603010302010507020d0b0c090a0b04050f0909070f0308041805071b15060905011517010608070c0203120408070602 78
    0x4003c00303811401168244c44203081c13004565158102d50801e5180c0c644170400c06666161283c4103040c0c0e09896402105503150742c00a4140400001c0e00e42449191000d0311025250600544e0b07a070340140a0940c0037160154001403510082c8151050140038040f0b00c00c1c3d040960148031409400724200c2d80501c9803025161000b601c4070000d890650342d081c200199111501e0001504c0c0c030b080c0860082c0f1a581c45020015012000d202501c0b58800039140791182903143d0184003244c1c0180d00a094000410192070003651030250703081da401c802c400d4140c0c0d0405443c0e003c2c04c520000590005c2d641c0502c00034080012401400409550a1101c1d40c02c00290230700306030003441d0301c1c0c141c141000f2400c5480715030070601002d03207041601826031417001c00901d69681144006000c0034410500c401a8882d8540100c41c01044002c14032406208001e200f41e090085c01c0d11042e801a08040400146889241c0142c408008910180f080d141907161504c1c030341002d0301c0c0381c845141c21000c1150400c0d542c0c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 238685314 1250 238684064 238684079
    0x1315090c14030f0f0717010207150203040f1713060e330301090606080708070c06050c0d020a03090204150803190315090b10080f040f170426010501 65
    0x4000035606808022a001d40c001030019141012103d503003060760040040451300c03400300141101c00c440c101d28044c0d441c00621004c2a080307006450700a00210107541e44021045107035402580d10501c11100c00d110110284c0b600c170031b811050285203156400000319010702c228807156550040c011807400401d840160400b09440c0442c01c248000a0920145040810602c10900c0c0359219440480c031502c0350703500c00e01c06014103c02c0c80b5034004101242d000c500c50310711820300036219103200d0301d600100f1582e40e520000100b00c000c002a0341c010091054208038117040c001010450915580818001341a004000c2212803881c0c06d5030108403d000b0401140c0000300c141c0d1080e2224a103400c5800a89400c1070b0090318800c0c0c501e50301060b007481c0120b45010385900184c0c81190075038014403290500c1c001074070917180985140180302e48140000300003401c107120000607244104000e07001601001000b606641168000d015103096004100070242c0700403400880300c0c8500f00c028032095141540c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 238686564 1250 238685314 238685333
    0x80f0a06150e0303091513081222030f08130e060f0402130b120115031a0d050a0c1214030304020603180f070e1501021605040b0d020306131509 63
    0x141601842111084180760f56000d00c00c0c1c6480c1030003d4800b285040700800110150b50192201c10300440b600c0b80013049400e400140c01e058010070810041c9000300c2c441010f4034001142d410364141c19916000400041e400020310302442d0b10580800b512110322030110f10105050750409000c0c1101441005155505c4070b003c80c105001c1901c00507642c403c004401c0e42c40603841e41000c240981e0008884110f8000684e41d241201c10300202c850310400c480d40200c05640304265005080c200c4502500c0981c0781240725402800d2240c411140c20040950b10b210402c8040e6000c10405244002c80c40184880f41d80302d043c0500b4454051499450b0a600052490001802c5001004180942600288010001f001c5003a5282e0116210b0715a95011000368070f40450b151200c1c5c640341d19603500c90b54000101c0d0441c101c80d03038001c0c0008605000500c40204402c03000103910403014491040035071800e100c0e05000c0e021030700c50385000384441d003085140b20544280202c1d09500d4408004045040a0b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 238687814 1250 238686564 238686599
    0x90504020705011803050909010e01030201090303081f06020c13050c1e040321030e030a08040308130212030d06051203040306021b24090f060a0507030e0706080f0a06 73
    0x1580140c403040c4030b0038594010402d44020f41820741080341054185074104019125410341155124126078aa400c07030a80000d0030b200c024042689400148002070060310155840341e449482214a500c0400c4503179003900c0e403540502c000d0780028038051414200107629440504000c01300b409181000d0440345001d00c0f602c8416141c10b4103003060421100380e5501200c00641d000045980d4521240841c074180f402400f440c5000b003450125030b0100c0701000700558000844a0302e03200886e540d252420b03180d4901c0240394014031072a07689c1150042c2d846000148041d88603400941d204c0301c81003c03100464510780c00240c401e610320b003400d003c4040004103c5081d00e50003c80540c44801c5440c40e40c20008405801c52500d019802e418105040300c271350540c0c4a01c02c3c0e046100c100d900d81102d801d44500350190106465004000003880a5071250400e80d00049180360014501c92007014117403d003030f1980c10000001e17405c501401031510303001d4040e40e041405040704000c12841c0444129001c040031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 238689064 1250 238687814 238687819
    0x2a0f0203030c1b100f060f08060703151a1201080f0307061107021e0102070e10060c051e0609010e010b0a14040b190302040e1902090c0d1401060f0e010905 68
    0x2c2e0481e0803003c6101600e041d442c4900032690b0910074002e0b8074020300850b610800b90185061320001e0285d0401c03101e001100c4029001d4202a190070000324064010f0000300c20080c0c6070104001488040b2025040c0000c0c0d41100f130344c0d151496502007041005040c1d01103640ca90100d4141210321001204031070107190f0084000803d890b890704a42494001c64201a500100b403040c41d074855800c0e00c5542102c0c0c0401d078242c2d640113480b03198084003040143c0c0c00d6500120a220103100c001c4c001c000c01c002541c007400455464040021030340c5142d240f410014540d07500305070b0070700c90312200c24003920011401c1400284440042c1034085410a14288141c80c800d45d800a00c0080302d4480e0742c4003900c1e50f1006003400703145010700105100300350340511040b4042d6140040342101040c2c003042c4020102c0900307c401d1310394400c540030003444038030141c507140e0700601c2001410300c1e03189688034504020401254510340396150039000707800b000f6613209460074010f00211120720b0380c3e800000242512001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 238690314 1250 238689064 238689067
    0x12110105070c050a0b1206010305100515070501052706090607050d0e0109080a200703020f060c0303010305160504150512010605090f010302041503050307080d0e012a0f0203030c 78
    0x298104a918080300f070b0300850700f00c6484200070420301000e030001c0c848070585046e9030b141c1da21090011421901e0031500042c00c4900000c0520441c50300c1c04412080100026105040c00b559444450031a08151000403914a10001d030700291000c4a01c3c040d00c8010500181c00d1500e028403000d615004001c10520400c41c0000300c044030f9403030a50140c000c40740504020071611b140c5240c941c990343d00c03800c0700c10041142510050221080c3c0e04481c1d40584100001d048003e2455003446801c0c514060038682c081024070008150301d02c100081c500941c0948010314004000d444980901540d50704140d0003241006001c0c41110158a1008200e030826550014031f01403204150380141941e07000075a08c04c25030b40901200312901204107060742d0089030100400c1940500400202d21329100040079034005116240216180c0800303424444000d071404241c070302d0710700421402c44e1050114a04c2840010340034540310101c812850f031003a02c01d800e01a119440a1101a54901008180841c00c000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 238691564 1250 238690314 238690327
    0x8071b08030703110c030309010c02151c0c081608041113060e060f01030e190309120302010212240909030708190e0d12030e0a0803010603021312110105 67
    0x10188001001052050141c03502d078101450002c05003046220300b21680c2c1306014441000d0f24010045070035200058407100c820381d40355401c1c0008007880c05000b20401500340845070040b180d0142010307030f10b1180100000c200d0005900a000e010000e02042f0b801190840c039140c0007a00440701540143c2c0260b12a500010b80030000703505006103402102400d800c02c0f200190900107c3c040c54043c52044525051008100004508a483c2108400043c3e800788140b40740c802e0301040240701050081c580705a0054450b1020040003107840001c4006070743c00191550401c1e12154540e800030108800e56900c860741d0381e0b584c1c480b0782d501500603100f4031405000c1000003000300201d411090b4403840854542525200b440c41142e040b889075070114003403910011103450000d03d52040d541c0e211101102881ca0598205e00800c0310600e1a400361041c5408200030481d082c01450082c405642c01607039480081e10f070030b9248007141d40b2054a60004e158850001503082c941d25000c00c60230300e00aa180d05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 238692814 1250 238691564 238691603
    0x10603110d0f2108090604080f220f0e0a1506110f060f040218040c120206070203010e0d11060105030607080c13080606090702030c0c130f060b07020f0105070807 71
    0x2584080000c04000d4156644101c542c81076683c140c200b04551102e1616548840c9419107680040350014403850003008a9201040424040c020301c6d003c40c2d0b1307250481d14120800800c905030035000400d009061140030071000c0455085164400c3c01104c05000e120121081403001003190300541042c460030007075001e8891010080c1034130314171020084510604040390030101c0c0c50029101640100c12074522100300d1f801c40c4036038901072a44000d0304181513151003d161004800e0141c1207034448001c124107000342e6000d008014540403d44042c0c0804030215401804404c6510700c2160300380c01120040186941c08510240e2001d0b250801d55659600c601d22034000e441582107112000c4060140407030f0500c400102544110000c1e51280500d850301c0b00c0990356405501d208104a03030061070006d03103e013020f050044019040840c00303c0d06000880c00d802c1a02d0381500000107050000c82c0c5602985030a4003203c80d07002d4207092413460040d2035107409415225814001e49041000a1203040f2032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 238694064 1250 238692814 238692833
    0x209060706060f0311031902010c020f0607060e190302030d0207020a0e010e090d08010e04140f101b080c040e0618041113060617090709060b040603060602010603110d 73
    0x40d0762020082081c40d45440303c640b44902c29010a0329131440e884c001d401d803400c0001e2180240d040d11000d61409046541c01100c0d0b003000c0d42022078001002c0c1c1210405030321a0b80140070090b12031480419186061040c061900c05110000700d040384101080c0000300f50082700b16001c40701740040141e0385a61070b00100d40741050540c41030000c0c0038084000540c406800d00c42e2805202e88600380c515690b0a04811034200400b8001e0645003941840807400082d07401844132901c005860541c0c080c200e080320ba05051656101c42c034090b20f600c4410304880008464075492001c0301c141460703407103424541c00c04c80090241d8020f11505210541c04541580d030386000d030341c0c000344880e00440c1c55454640340c4500e15503c0d01040314050a0400c00c40c0c00e41c00301c54000c1c6826501c865440040703842c601d1010742c8001c070000e0240c902a000e17068000c2041180c034040d6002404a4045aa076101e01e0018003c045403000d074421811645040418800554501580100100c040360502080801c0c2e04205000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 238695314 1250 238694064 238694077
    0x301060305030a050c0705060712030c030f0204080a0209060d050d0f02010b030d030207020108150609010c02130c0903210804030e18040b160320070c12050303040c0501030209030709020906 83
    0x4a01c4040f41892030142d01000034a00f50340d020003515502a51102404490b000d0100000c0c84000030795a1042ca1a0ac01d61058420403401d1030302240c0e05800001c5101264029082601c950300004c6103101903081803140c032608240260780e1407000c1d00729516800c0c1c84100c11082035040142620281d40104c2c400d4008c000d124100800f5103611051550f406002940041c600301c0c0410040d400140307010106020040344c94502510503440d00c513400004403801070006204a07480007650300b007111580024800d101216107103496004d42c550441c00c000701c05505140b0441040c0f41029640340c441e50b80079041e15003242d4103003032003440302524100003200ca01484425907410a0340c10108800c2c400c100c02c1c054058034040c13568401810a2000807070030340d104407580345001c0648040d584507203a10180109440c0d80201c4a00c0e500ca41c0f03941515808040c503600544507036001006010a10521040b1038000302024242180381c40f001d030000c07035202d80b40740c030840400d00e078041407100c641e4480c00100c800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 238696564 1250 238695314 238695323
    0x7090e070e1501030f0b09150a0b030c12161d060f032809020a1e05060c06090606010e090703090309050a180e030a080a0509010b210c190603050603010603 68
    0x2407a0030302c05207840d4140291114002802c0442d00c16511080d44200303511440040d005c10415550071180b418040c0c118085540c000000410000c0d400c1d950001841c00b80c1d981d0a030503076440000b6244084124405082c1000d2038814149400146801840e1040e02e01c06810030b1111083d21400080c4407030054940700260900c0020030400c402e0001d4050b015400103010582c14040d001100c444221011001c4c02500b1082d102400d016680c0d040380f04098501d8003200d51542c0c0c41e102c0010906a80190300c00300d02e580d00c0f06003845017030f0105000f850b42c0f0120a280420051000303c0015040460180c079050a0503500c1c1001c070b0925205101c03200141a014019104071550303025100c0c00744261645c01c0541c0d5180000311441000b011041780d451000503664a966038507000d170000d0081201500b000f08a660ba25099011501c60340000b8003c1d2600034240303069911411055030a01800c0301c1d619103d005a100040100d24000e400c070010794029103400601d40e500c140200340185001c2c0c00140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 238697814 1250 238696564 238696589
    0x607140c0904030201140709180f0e0a030804210509210105090c03070905060109031403120414161a0705120408061006030507020c22050a0b0f010203070507090e07 72
    0x418913405412500c11050ba071a11041e071680d07055030803203198016015850280c812010465078600c900e4000f0060300529510004d9900c1c0d10301d142030b103010341c602c0003100400c80301c0007040184591030440741044844030304001c03841c3d042c2d5540100188500d03d04240f00e60034a000c040c0080c00c0b60600803c0e20123480008000c142070007050b13141e030381d031141c10424800d01c540071000c2401130440c0180c1e402501e06860303c860083c00c41da03d007101700200400001d4144000d121602c07001c07a034403c207640070303a00502d000103400c3d0102a02c54202022a50060110b18000c003081100038010010180a601a46809511400d4910b480c80c2080700d00c030f09840340c4060102c0d000c9200c15000c2156402517680341810386805a80e21001da040d940110384041c0580c0001d68410090304203280c00c0301c280c400307980300c1c291000300888000040300d8040d541100055984c01c1d054249040544000308489401d000550510885589440e5546118018200c483d500c62100545003c010414000588203402e40030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 238699064 1250 238697814 238697821
    0xe04080c0607092111090c1905030103020a210b0a0f0509010507020712030f050703050f070f030210090c05120f0d0e0301060506190f020c04060e15040b0607140c09 72
    0xf00056042d000342645840e80c00401500c1403039034910b00070301640c0584510745001c1e8403010850304002c000d100d400302000c100012034602c2400c0c0021011105503031039a64407541180103009900030503400c80142c400d0401c0c2071700300259041a00191295100e1001d04841d510f440414000c0d28107609414001c038209002d01c0742404045d0041c3d03106244c1e941c205c3d10f60580c3d07083d85e080000c21011000c3c012490144030b480c502841080105003050081c1427441c0b030245422841c00095200540641303448427928000020035a06003c3c042e01540401c00a000000741e81d00d6034088101c035403042d10b201e106030540d0060004014003071101d0100e015410358100040c5c0c000b01900034003040d1003140c8a54600304020584c0c1c50948140e40c0101160441428440e29400007620f007602c42044140170361241642030190342c1d841b8050b49002d003a501c0800071140c1000e44007166034131240500c0d135105506003111580301e52114000d88152540000070340341d01d10081003009080c10982030313015400001e2030040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 238700314 1250 238699064 238699067
    0x40c0513030605041a04020907080c130605090109060f0f0c14010203190501061d010c0f0209010b1b07060c0f0303020708030a05070219050d0c02060c01020307021e030408070e04080c0607 82
    0x42c611590080e8540d42c0000740c024681e51117010200c800075404141840461006880303812070319404140900c2c3da628100c0d5049040710903940b00e6000000041c0005400032065900072903110007444d403820403110040c4a004060442c4003002c0f241010044401c11410500c1000c2102080e11040c4400071940d03400c1c00700e100d50516100340d4104c590f0310704000c000030b54184100300004018041550700c0c1941c1265000441e4071001c1114250742307040044142c00056a11548203d0081124054040da0f541000e0720b0b00741c0095241d244010180c018807010414150001c085455450748205d4000640300d091800b0742c028041c4800141c5076910110401040d051254081c1d40515065003c0301e0b00b20f0803a0400410020f4070100060040d00800c482009a40c01044001c404600c010800c90800c864040b480e422a00f08a41440050b40141d80f810580d03210071104484508848000c0c5107483d04000c8040d0792001c451041044444551001500f4000200300762026003407a1010340d00a403c0c80c0c4030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 238701564 1250 238700314 238700321
    0x6130f0f03170c0a0b1312030f06140d0210050c010203040f0308010806130803060105160b010e010e0405070e0c0c01020706050610032702030a020306130b100311040c05130306 77
    0x41214803039800d8801c0c02d00c60012000342e842500444009095440c0b4a90b6007109100015002e10b0f04030010300c000c000040c80c050401c105d4040c4e00c0d0740004030301e15042c52400503a0210381c0079401811a6100d000b00644510881c0d07403040d03070180e911340c040a41c401c0f011240c1e031107060040200e03948084180001c0040b800041c00185010341d80e00c190698071501101c1e00c0e0320301038511041302c03546249403000080400c4040c40d880740381418514102681c1c46681d600b80184001d04440303811460005105400c81e2052583c09002d0142c400c01d4a07240558445a40f80301a010740074178001c158000441c0c03203100004603800041c0c030034029034643d5154a040c40c05400103403400c0d880741106a42003c44540701e07224104009013150f0b003880403000410018019a03410803c10f03030309400f6480c84000542c800f0404180130340040d56400301c0d80350f00ca042038102c5035005080790548040c07001d41040400c05a201314000104d0491380026910b002c8042542c0c588036184860b203103980481c10000601080383d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 238702814 1250 238701564 238701569
    0x907050d0819050f0d09170406080a050a0506100e0d08070303050a0507021207020d06020904060f03061a1305090f06010603061a071e060603050304030609060c02061506130f0f 77
    0x350221092031840740d00f6110303801220326602c0c1000c014031441500c0409500b02211690241407000c01c03900e19480c03880364944c0f00390482008103564500348503000c0403610600b607010350440020025800c1050005007203013000b003504010450b011255056039950944403800b01507000308640c1c0d44102518014001d042c048410060aa2038800000c079000d00108a00c1c2e090401e58003860300c0c0010a60030894a031569203030598045600340140704040d241c0d8400c2c40007910134003032646851441c0d803800a06a80071402c2e00b8000b45c4159050003041e442e611881d8007518410b041c0400e0740d070345002c1400d14111340d40300205818420040002080e680507407201064584030810022100c5050540d1103641c4a01c4078000c001d0801c00030301c80b078440c0e04002d201005600c85c40002c80e4095484d00d90314070b03540054200343d85041d0b42e070303824004000c205d1181d058281c03035070b001a010520781004010504005900c4240c000d0400081030001811b0030840c0304003a20942d554815103030b8440071128291100b50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 238704064 1250 238702814 238702837
    0xb030115030e0606030606060a050c0109080903100b0a050d0f050604080a020f0319080c1b0105070e0d050601050f0d0506010906082514010c0b16080114090606030907050d08 76
    0x2c0c1c04180c480102044152191201400500c041d442d00001d000c103607841402c070201042020b101e207958110081c010080c26078054421540c4940c1500e04150600c03002ca000d0f004044c0c5000209841522854041d4040781c00849501d0040c0b510750a1103034465048400003800e0707004002c07c20040007010000791081da04654201ca414400e00d04174503980b44100800482e0703040c00911a14041e41c4a58501c036032050003100b040e4281f8105920700c4801043d0703460300c040c45035116801c01a6203035110348442007503032044070050101c814640b0b0380f41d103070841801040c0c0201d05881c002d130541c0d140c2000380071500e07600c1004c4070b01543e511802c140c01424a40212205030284205d9040390203201c818043d1082880c0a0101c4c0e2a40340400d59042802c0d0130001d141801010004000800c0c0b440407854400e41d12840305415901c10060300a000d079005812681025000c402c44200941b074418070654440c40a95400f1360b2625400522480c00711144d0100354010202007825080140041c054801580d50 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 238705314 1250 238704064 238704071
    0xf030d0c05011107050a0b040309030506340c1b0506040e06120a02011719020f03060a060f020316020a03020d081c0603170a17100609080d050f03100b03011503 70
    0x1c214200c940d6100d03000b40a00175a001c200c000021441a44e46503170010310a00b00303c0115075495a80d641402411035031401c1c21f00841203802d601c40b6105090030b1580020a40052000841c01c0020f8503503148668050440301d04000e10110040008000c50080c00c00103010b19140c50791052000e5012001311250b03801114002509000410b000449901d42941611400450315460040050702a00200040341c100140802c1003240035a038401030a640c648485c3d01e40c0d4a00c0c001080c04400b0b48035078082e00800c205400e50561040e404000e846000d00c0003200c2e0144e5034070f80e00000700071040d02c1e000a5441100c002c8120f0402030f402c001091800c1c02030f181002c84c100d12030200c0c8119030b014800504a00440c0419503400307240d17040140748203481400e15040d4051202c5017228444011500140700e00b84590050140d640c0062228000740950401041800490b040c014240d00a4140c0360464540c084042440e094101c0e00020103050054038007a2a9a0744200c160504035004a000001c00c2c40d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 238706564 1250 238705314 238705331
    0x20c0316080115030209061e040216050105100b0415020a0c0608040507060516020103050a152303160e040206040e040317010519210b10030501060b04140402090f030d0c0501 76
    0x54030f0610308122034004051214556401c8184101082c1c1c5911000420b14090003585d89551644068401d01c00295000394000015290039400c40700040d01c0020011240070080000d480c2ca801207606889120556040e40b101961041e407038051034240c0141040d21200000c507400307a21204451040d801142142e50355503550700c0a8a443c030401048485402800005102550107900041d81084450034001081182c4110224401d100d607013082c503000101030710205c6035481c0381c80801c00559044000d00300320b020315102c04010308200d00c10091802441d40c00034055503542e4040c0c0d070041025000500c6e003072405160003008070b81070a41c1c403411003004200218a07814040000241070030b40c5d09403407540c3e0703040542510349200300302c25403510f81000444120004081220960141280c00015480e450031803030300c0d909480054105031040107003170100300014000c01b030b06c19a1401e4180d0300180d9844101000ca204550081b0455400d880b5811255031400d92040d483e29003140180c00070403640c1c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 238707814 1250 238706564 238706591
    0x11030409050a060f3002180702120a0c020f0a030b04050d1d01020c240f090907020303061c030309240c140a111c021c03140a050403020c03160801 64
    0x510703801010484c5c001d003042e00d843c2e41d40d16081c4810703840c1014004041240603030b0014281d100f410280c1407030003400c101070041503501040b02400a030030300d00c055030620b4241000100b03107440c00b0601911400000501080d2501d900c41004051500300e9540c100034a820300705107070b0350030b4903a000c0800125140303481d0308580030291030200b103038205034068000030344108200081c03c0c0000b500c0c800c03420941b07140c103c28014060003c2c90b0003054084c40ca91900c60240400190050040c80941590020410005166251401070545102005d68043c070095907081c00c400418061340c0090448901100554080c2014034203010700e4460035009100043c104e00b4111940311030003014032125403080c09980d841c0da0041400140d10403110741202d42d00e040d9100e0a003020107140c1c401c1805a04521210404000182d4174082a5212070906002e0b80705042110301088000070400c102841d5100e02007001c01d80b003441407440808005080712400000500300e00a0341e00940b003114450343c6050703240344090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 238709064 1250 238707814 238707839
    0x140708010305060f06061b010f1b020606040501030c03080f0d05070c02030c151b0c06040f050118060504030303020f16031808010b1c17030705030103060507030e06070e0111030409050a06 82
    0x301c1015228600700000c8047c101100200300f8110303001d5540b03a646814003c2145e2180172103040035600c1e40300c5030006480e8046d0400e000588081d000300e052000500101d8001d401d101c044940c40b144859480400030050703403e0b4020111118025400c000602441c19803100a100c0c5080c02141540e4820179594100003001e00c0210100c1c00c0000c1c280700d80d03810210528001c03544203083c0400d840203007441e0fa00203401b40d40716030840117845081510901495078080020a074107644040301409447c28070102a005002d148001801c054000032000340d080440419944007c110703800400e00c0003070078940500451401d821454001111007800160210140580405000080c0c5403001202108280f80072000e111902960380f0112030f140480411103900c01148200d070690b560342e841e9419480e01c10f0554101514003410142021500b00500d60085441030308048541000340e411100e040040c2d45010540b1003010a902020400084683d001d0b0440c5108a0303044034200314483d121030040701d0b031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 238710314 1250 238709064 238709071
    0x1a15040c0c17160602030a0501050a0803071502040e0907030201020f031e09030708060f1b0a021b04060515090a060f0f03020703020c0d110406150c080d140708010305060f 75
    0x10403409400c4007244141000c4960320034902d03003142c0b6080c4a00708480c0030044804040b25529400070804c481c940c22445210b001d00300c200ea1070704e0003e2400c044140e40740030341780d006090040c5010411194480303950455004007504c1102c0b01d10351402035041d64440c0840c0c0f01c142e0141c007e891101c3c2c2d40202c01f00807134803040e0802940394900c82240c941c803a81034200141c5035405202d0314601151441080100b20301c40c0f07959004402142c589a1001007101405040115560500b804440301c12600031070b0003410b85003c0420003100011220001d80030b80f40350390015820152138101c146c0c950209a00602e071144003aa5004032582e5181c0048404000c020066000100f1020091001600ca500140550781c001c2c412a1018444a0002510349644031011205070520424072181d60502c0c0c000c2e44d0080c44145074450310804100400f0341642090180100710250000b541c2501c4030311503120311050b904104080a9920304100c002e42400b10a000070784051141c0e41c00940307100e02c0c0c080401c0c40b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 238711564 1250 238710314 238710317
    0x607050f0d0b030a06061509061d010c0f02120d030509060c040312031b050306040e0105102603040b04080712120804020409151b0207030206070215071a15040c 70
    0x3414103800c028600070055142c0203a81402201200400300341140554005007031104050034121002040c0500306080035409107060140c21804c4a00603061104880e003040420708000a40c0002444c01e00b081e8102000000d50010301000d0100b0300e02030010300701510b003070b01b52420441e5850b0601202d640350303001c854600b034107101000180001841ca04011039a1415400d0101c1c6045000d100c42e814142080c07125000580040700708009890140078580c0303808250300013003100e41010441d002e9800d0b80f0380111002c140301c90050030b00002806045604a03c041020b4984994603001d0108540d8441c0c1f01d104035611441c1e80c0810004007a4041c2c0382a25444440809540c184c20015206136074001d00503030740940c0c1c507443c890100b602d4070082896501c6000d8001481100328003034000c0c0203045442c0500b150720640d81400180ca40608484600c1d0701250b0305003111182000d000706a108840c2e000b0407241c080303009442c2c0c59003440311040c02403201d01825400c0148034420f2000f201d8403032000d40b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 238712814 1250 238711564 238711567
    0xc0601170c09091e011b051c0b010525030311070b0106140c0f030d1b022508011404022d13150602070905010b070b19020f071a011a0301090b030109170702030607050f 73
    0x208c138090316034010780c040b4406040c51802e2285009002c046110b109428a00c40c3c4030446641e01010782c540300d07407400c101d00301c0086402c0c85882d440e01045100d0501a0109021000c0c102c103000c00081800c1e02d0090034210220303480e004417100030b40c0d00d07a0001c0c10481c035100e05100034005500e6049408082c1144264000d00089960344170b80c40f656000e080c0000c036040b45411010440c20808e0107204043c0042c05d01c2c1c0745050a05105000c5040f002441d0390820140040086541902884402d0340d00a01250031520a490a0078000d0060041c07101a01826803921400140b0540129044048911804041055a90b18079213003016209140000701501d044c1c40c0000e8811030070800700c440302c000421005003403241c00c9481e28140e501000060344c410f00e1180c84205401c102c0071405015180b10030524040300064850743c0510f00042c050901c0c019114104480075031000d601c0144078035040309000103c21185000380b6290707404018268003a001d00400500d640f80904221089030641c4803199 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 238714064 1250 238712814 238712857
    0x9120c051c0306090c032a120b0a0e090d081b07030f1101060f03111008040b070c0f120305070804080a030b06070c03080c0601170c09091e011b05 64
    0xa5102120a0480310601d030f612400072490400512900140c0304103130700c0001d03000a44019415032180034040030180310f002c00c0c0000c8611944400180c000850180d004619081440d000541101e10360b0001d40c071858a01301040400d00c000101b891071841141c03542e441a44521028103100740c3d214a014500207410412403000038030680c0d0741c24600c01540380c5501c48626002c4805d0958140345d000842c4011440d20074000c3c0006507090030714400701107500950741545d804020780880d40041010300344c4404803000503450317400b440600454581c42100c1e102007600f54038000c2c10030741c0c0c0006d411700003a10741030005940303d0064004174043e80d00048482d00f801e01403003084010f0500b010805030003110900055000840124060015500c245580c030b440b8a0700501c940c0c03510074143d20500702c8104143d0001c001403400300c0c5d01c07251142c0c103680782030844d0384508050349000b15281c3c0d15084882c5e003185001030764406601400c2d020100000c40f0f2204480b03260101c48500504043c000359100c8007144 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 238715314 1250 238714064 238714093
    0x6030a11040e160f0b090901060305130b010b120f042a18091a040b0610050c0607120c0908030d0f060302150702040b010309321009120c05 61
    0x900e044040c01440850060400c40000381012444600000c914101d09402c0c040c0050b060b5581000d01000c480c0c441c1410103078400030301c84043c10302c01d40c820b0680e204040340059110700768100c1c2c0c980d045120b40c1c2c11542d550a044000354000c54040241200e1000030034029400c50866500a43e040400130300720400f2084400c40184c01c0c02c103a4125100114000541c451041a00c264008d18000e8005044506403c1c0143d1260701007130100c0904218108210014850711741042d00040700b9901031514655241081c1d0350791007091484402e80c4241c4042000c40d03540801140d20340c0d43c0304141070006c82620781c01034507030f1442030182e0b540ba50000c0c4000150b880d12a0b225440e203204071900441e01070b17946d40205500c03501011400c0290f00b0300040050942c10305010302c2050306400c0c40c082007000340c2900c803001c16076042d9190406202a80860701541c010180c085e2600340c0c5500240c2f0102ca41d040402c03001025950b5085031920714200c0011009805082d010000c6a04000640b402602d110309 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 238716564 1250 238715314 238715333
    0x7090f171510050a0f0f1401090b18130209030f061504020d110a02211306031e05130b0c31030c030b060102060a060506042601020d0203190506030a 65
    0x103040d01c90b003a0b0306400100c80c0c0d40d034070b4058014004882c146002c14207124582e000044990031100924400014105041e68030031407903401c41d0596a1203a4465200310300d4031069400c03103802d20768803982000d1011420310080d8018084440220219103138040304800054442000712442081d240d0b40c80c501c800d59040c0340e0020000c403200410300007071415540200d44401e400c8514001c005070300c07004801d040322002c20f0f080e0300803800aa8040342860301454034805d40c40c0d900e01500701010f8480003501801c5082d208100d41804169a080c8814601400e070310f100f61545107016514185000d002c80c005400c400c0071648180d18041c4500051428100f41c02c1d02a0301140381c20009619441001000c5000e0115030006184174524003440c1c0d00341400028949003015200c80492850004100001c0e50b0701c1040314212001e400758203c04c2544c4030310b50100307020200460069540006608600310001d54025481150000c0e80e24900307080d001038010880e801100c0c090b8056004030070910129011a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 238717814 1250 238716564 238716571
    0x2070e060f0609040f1d060f0403030c020c040c020102130b0f0304020d0510090501020a031d1b06070611070501110c0a060209040209030313060816080610030207020907090f1715 78
    0x40002d46000c0400b0b0205040b600a04001c049080e6a114038035032418444040e1200b07180040c00500c810305140350101c2a82c0c402500c01411706070740d0102c800b0038500a00c2884410300004104008986101c600a07021350700c07450800c560f980301090045004076031003080e10610700c08901043c0c1507507182d0f0b0034001e0703100c58448259607521801010504c4511180903080d01c00c1d00c113100240e00c5030804400034050780d000382640c40b2410301c04c0b10060310f8803100051000d650310102039138820013081440840d07254800c225016001c0d905108030244078107040c10040070036600c100020481034400c8440401e003405020785005140d0000c0f0384240114240fa000303408130711002000146440808800603181d64080004010040264441040aa50860481980020b50882181030240b110703600800c003040c000c00c90307880ba4800c245c41a001510130740c160303001c46034050608500e03030610b5000a0201e4681e4452000604003145010840507440000d07280541905401404900c0800b5600c5c4590803004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 238719064 1250 238717814 238717819
    0x1e0d0e1c05060406060312031109130b1810060306030c12020303040504020d0c020f0c06090118030602040b030a05161409042903190201020d0809070305010212150102070e060f 77
    0x48080e5012031800c0c025a03000e2481084002410b070728518040b0010500e11090105141c50004124100c0c0c05031b004079010004200d950380c0c041064072403907000130403003112990b0b000b62120191141104c00031110394001c1507800c1428518507030b9514100d042d038000c1d000040804145200c1005856084c10046150034802410349080c251200081800c0303801c10200d45100d00d80711010001280d8050100341040081c0b4000352400882e2900132580d80d01ca800c0e20241000008022001141402d00c0d0000195900400c20340d5299921155401223400640b1f000216a150a01040662034601c6012404c1c41060315400313a048601c9a03004107640114500c43d0708503880c0c00c104200c1254000050481240314002c6102442c3c1070740c1403510700200440e000415144800304000940e0700015030700280342d42482d0007181c03640c410012906151041c0d1004000d0340c00491174551751041190854420703d96008410181d5460340012a504c3c00240b08080020306008045582c80c10400066a07170714202 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 238720314 1250 238719064 238719109
    0x91507030c080a0b030c12010b0301050a060306050702010903050415050c0a050106050a0b0306030a03050d38060f04050d2102011b03050f010501030507110a050606180c0d1505121e0d0e 81
    0x1009c0c042800e655046038140202c5036100001e004000052141c641c0100701480208184401590301801510442c000c10003035034109450300710311174800c8048400000008c010784c1c0070b0030a00d01c2d04038060640b500030140705031516440410130341c507007000381e034441e000040c0140f4010249440c15560b59021070f101d045065280c1162501001202600c0c2070784480c3e00d07015149004410489100e0005545009403060200300f00c0d00b416450040240c41c20342c0c0c0f0480d440d107011800d903d0640f13485103c4040010f40300c0301694a0402540d01940301006040140030300342e11156420b80c00b24112003040340d540860303841c608018040d952082d8041c0360300074110b0509103030030441103418a15051200d10111401d600400c200001030602e41004450b900d03516520b5071607424240c130505031034090250116840b07a911400070808862b217064210051802601042c00d0300f01d91000d190b100c001c414401d0814628500282c840e1000c00075071051100d8075543d402c14074071014001c2041218017000301c5e2400c1d903007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 238721564 1250 238720314 238720331
    0x1503050604230102090609091e10030b060f01020604030c02060f040b0c0c0d02060d050403030b060708090907020f0c0f030109050303010b1c020a05030a05091507030c080a0b030c1201 80
    0x1000302074012401155a0729400800504800807003440c8002248280d0051015101585032034003550545034040761100050717a10b501d0590804140701d40d0f5459480105004d02400c0780600100805690140302040c1041c3e40d040280114802d15030140740c016803001c000030307000c6031082002c00ca086100034095458a803500800c83c000c0d4000b030b081b4800c2c0d50000101c025100608000012541006031040c018483c00c0c0d40000c2d40500805001103a030781d80300c60014040600c82d03804a60740f500c0090451f9120709007824980076542281e00c0c640c1c0500401008141940c5c000030b194280300720003600410079004180148040e034080600d10305d81541d2a211240e0001d18184007941c068400c000c446525030070034200d03081031006068261f81000d40304003c1c0072a130325880401c407540301c1c80c0701a0105458641c006410300d4002040a030350007101d540d4081c000400ea041c0c0020250782f500399100005030321403200072070444058910403541350f032051b41040941c0c20a4180712200e9480301700001009003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 238722814 1250 238721564 238721573
    0x3040f0803070e19050a26030a03050105031605091302040f020403051609060308030f04050a0212010203190b0604140307080105071e0509030606040f09061e0b01080f07031503 77
    0x1002542c034400442c1c4640e1000c05103040c46032070030320305001420031200554506008168544900d010b80201100070701c0c1c01a07540c0701c0490562044144117070880e40d90744580e410040041500380501032207409070000d4603400d10010400c800039224018606001d079100e031901c00350f41504412003280c016494404c0503581a41d248098402940038002521400f80841d01c0c00000c8411508030300c036200c0c500385040c80450b10b0402036941c0501d00440001164540d4140f50b443d10a080e90000d511040c01e541c001c02c8a030b010f40185000f48800090215500700080740041510341c0d000b003031074000405202c104410b401d051140101d000c005803e5403003c5440320f0070385003540d00444011000c182040c00c407640148030089150105416444c0a41c2030078100d000103622445c015180d18403941d1a008149150106580304151a9a2016003003180c6500d9030f07c140c0411540194454546140005009895002c0c030102441010204c0801c9001d03138510f4002d50040001c84441010450554400300009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 238724064 1250 238722814 238722817
    0x806010c0c030506040b07050a0f0f050702091006021e0c060306010315060201020c0d09030b132405040c05101719020a1d040c0c06051e040c18020403080301050603040f08 75
    0x460103480136010a107003a06003890f82d0312025041e00d0030401c0400c00b41002607444460440700303c15a281c220b0000f44c0c00748088074907002d5603002a6000b84101c3c05d00007480800800e440803150b030390b000c1da41e01e44142e09005440a00b00c8861002a4202d003800d0f003078502e45140116440350b030505000909a0040c40d5080004496400010140c3c0d80010342d19030401c1c081140c4540740100e0701d81400c0441c25a502e210f02c020010304000704561040c0801c00030801c209222007285d5008904a480100c12207010001800080c0c0b41134a03c001c0c940b001040c181031400212003850700c180c54500300345140503140003140100070002404624103803200d80040c0c000d80002d14048200d40d4417070440005902d0699448003250360128419447c2140c000040c2c0d03003104c000d40d401c42d081a40080e25580780191020044520722210a44202c414200410089000200016500300302c4241c1000d9030100e52003001c80c0714a000c06400d441e400d000410036460110000d550043c8100403080481c101982c54841a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 238725314 1250 238724064 238724069
    0x501021306020c0904021f02011b0906140403082703070b09120f0c04090203010219050a0801090b0d0f020d0f03030f0e010b060307231c05010803190806010c0c 70
    0x80004100c0812031140c0c10840d1500b1040c0c101c503803111500b0168001265101c03400030039404407103104030000c0c200d4000c4d48811001401c3e204003050b0420442d0008000300002c0c000d01e000300305c0e403600c0c2030200080d00307041c2c500f500d5110001d00d1030040c0c1000306140e081c160340e500311007441ca0820380f402d003501e05019540c000d0006800785030b141c01e4403c041110000c1c8000c022800750b4000d001c524031040000400b802c903020151000110034041e4008203029104100c0030309001078003400340e01e500740d40c40401014401d0380f039601c07141c1c43d9880e200b4000584d8605203040b94002c6001013044003040c0b1001901840c180b00400c6040113480ca030b0b5820030003aa00303010640101c0d81d1801d602564484074014040c40d916100002c2190b400144001a200d02000d80380b10108400c110701407280e0121108808070324034007007034215110b17001e48219a40c009140b0000030ba41d0b5040400008980000000b914004107580208000114010340e04480186005220a0401c02d60030418804500c150711021701 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 238726564 1250 238725314 238725337
    0x30d180606080d03050601020a050d14070c0f060f02030703080106051c1406120a05120c03070c030510151d10050a090f05100e01140d0b1906060908031c09050102 71
    0x9545640c9107002d01185c00007407005040d90401c009140c00244081140c00d003103002d03400c01d94410070740e0055000c2903002d0750000520304280c03403501146120711401d21804943d210b5449141e400090355003203849019407500200804c0030480140b0040e8002c402600c0050206120101d480e60042e039008181e5402404c000b0248012406102181c209401005130810213400104a407102540c0c4483c2d0320030302c0906c001c0c0b5030507011500c0001e508061085808041c0c1180718180200c0d16070030070316202c0503281e40040010345800d0b441861a500b5a0602c401c0790300e8131070415040c0e21030924440c4040c01c01000c2d400e50300302e905008640780c1d03200e1070301d00c014125848002070520354081006040300d002400c4840081120401000703100701e2141c401d4150f51001c2c449201101c0c005001c500c00b170803801c0008058a050780c08000320400c03505001d0b400c0f402901d00600c05d01d699101c05503500d403200d004030b04054004021501d41080e03200459030740010318010000d420b908585441e400c98024105090 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 238727814 1250 238726564 238726573
    0x4090c030f0501120b07030e07121109011d090105070c0b042604050310150b0705120a0c112d010c050307050303010f140f040e1f060f06030e030d18060608 68
    0x20f02800829099002209040030459a12885001c8d5038804480c82500990031041c924001000074200d264556104094040388855845441d13201000c440032465a0380c2200301000a848007005001d11400b0711101d4860451000071a2180800d1a0300100103680342c41c50418510050004490051142c00c030700200c05486500740000c05042031003400041a025003800c82c0100d0710391400d0910811108a0040b0030ba0310b120300d2905900300203185054100341e14002c140c80010580140b40980c0c4c2600c64602020144c1c1d01d6820868403401c8010450100b00748051b01c004050005205c18251407014101111100c00700d0703494514560060904a034160808801042030560141407040074050444000c07107130103408804186140204640d071441540c8076103150760308401c03d02c04200c0013124003400350004156000703004040c2c0000e124143d000c0103007400000b070303013407080c07250741d440c1c4680c04041e40c40c110700d840f1140d02921294505060b13061030300e01a00c002848510800f0020000360b400791 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 238729064 1250 238727814 238727849
    0x10c120f020c12070b090121051603020304030e1306050301021602030106060804080f0f04050603040f150b06190207051c030206010b07050d1404050d0303020c06070504030804090c030f0501 83
    0x1e0070000c0d09001d0a003d24642051401c181c1e50108110094540030001750b074680910b100100d0b9500781c500220720b0340f6415064a08040d1641c0e070030881c07080b61010070050550440190440803403004590280002c0e12080e45400340d0700c0d01d1981c0f540040507120002c50703d40e403294000b0782242e0007030700c146901404503005c9804500b42030040a00411060908010b14034041d01c40e40c526218042102d10020703000a1000c86088100c0185c0d4041d08001d08180e840b480c017498150744e801e585581c207948100c032030303542d040e0885e402e401410070081e4058131407401c041ca00002d4840a007501c145941c01e5004804020410381c480c0081c034224245080d5085e20601300d281406400d011040e001403641d10404c00244003c07a00004d40860000e040b4502a904118040c401342110f0280e070704800d600203103441200b01410381c56000342141e54061029121151580f03102503c07240b1991000811700c10050104000c18100c40d03000d41c1c3d00701c1c2e00d401c01142604081800d0011030350b00740c0010100b000035603d032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 238730314 1250 238729064 238729067
    0xa06030212060a03030206041e0c0303020a02190602031b072c06010e0607030516080301080304080c09090c0d05030d060e010305150702060a09020a030b07030b0306100320010c120f 79
    0xc00e0b0448025258442400d0561303d0081d2241d20040000c0e0031b502a402c203c803443d802d1044444112900b180c07480c0f4010342c0340c1c5002900d411003040280d1040c00e40545024400b4000b8140d01c0c1207550039002986004a01802d40c0d029070114070325803400f40522100003440d1500c07068039181c01000c45103030003080c1e542d03106a15940c4002410035410400615001240341d01e0380300840d048990036052880d00c4110748040500342c01c01514000301413100c04400000d000c00000080c00549040c8000d540c0d00380e0200080c046000e0080b03e40b4001031340801c4c01c3c2c2616090040001421a001c1c0382030700d203081c0840e01c05105492699104408072411139004000340101408502c0d20140c10203c08540d9080c425070080d51170301c2c060400f0950568401c02c00f0215030340c40c5000c42c0155400030003024146001513014000b4401300c40e0107402401400001070481f0951140541540d900c1500a0040c0058442c4c0f511680d880548050622040c078201601250002040c0100d04d0300c2503035001c0505d4a405070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 238731564 1250 238730314 238730347
    0x123120718090218060c0309040f151a03040f14060103050d1704030e040b03010e100209210307060c200607020706181404020f0a03050708010509070e04050709050a060302 75
    0x102294040c818000c1c089104440c0c0b0300390311280001c031510b50711000c040c6c3d50f0340d003984036074065140d2051616100c102090125000f110004008170841d138042951001c0d800c025401d0b4605100c03500508000260000d10007120b21038a003402500d10003541d1494401d6203142000070780050765198003610301c0d03c0342140c0c0035040141c0901c0d9400c0042c041c0c18140d0b00500647d00d581c003540c2c40b5075120080641d80d074400f580060000540c00b4122041181c0700c080c07800c000d610041c02076020301c2080a94924580e1080c56014590255200451400c0d0494070303800020082500c842c800c002c00c0e28807102400602c14031424070196520050980b50a21040191610f41140d0041040c00224400c8000c2260a0001c039822100300d42d680703284084080e00018001c0c0315100082c43c01038030102e2a4144290b044c0e020611403001500c030000e41e0798a41003001100d400c01c82e4190000750a00f0100d1030320307042c544c000d5038106000d42080800a41c0380ca00107440c035449504220300127980482e00e009414031144 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 238732814 1250 238731564 238731569
    0x6050a0b1e0c0a020d060f0903050c010b060903030f031e0a021b0c01050a050f04050d05101425170c0a08010f0605070807030c051207150b0123120718 66
    0x1091460701035200d01d40ca40303d03400141c010b0f2151200c0e0b2503403818449140c01454201031551070402003160a444c01803c04d4000c000c6052030381d840c02d960540517051034002c0300c1020307a0050095062090b2071030f00c107220303500052544440c5119907100d50030501006e082d0b540140200c180150702d070b03107200c0c8607040402940c0f510904d4030384c010301803510140d81001c2102c0d800112440c1040c0d64030f00d4029000414441d9a2115801c90204041c032002c4c007c01060601300d2030400c500070700048000e261307041d0307145000b030314207519a18003002401012405001c10070504d0b01c450410092450503a01c1e0183c4140301200c00c001c101c04005000350784594811440c85c00b401a8903c51200d80d410034600822500914030001e200440010340b107024103014801e81040d071503000d03088074100b210030400841d0039000746008807030002941c555001055000e0041d078140b41c50603522001e5401080028418046484080c0005140200025040511450b04d004c0c131525403a21103072400112442054580401795 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 238734064 1250 238732814 238732867
    0x8070f0804031119060e12030421021305010303090e09100c08011e0b04031103160303090603110c30070f03180b04120c080307050a06061d0a02030a06050a0b 69
    0x180313090040385d41250010b1000d58054a40c0c2942480c0c0d0144d9a10310b00c00d9401481100c1c00100d1144c0c49802403100040c076140c400c1c0c40301001107520125000a6540038000140803e0700e007442032080c000c102c401d40750f10000420842c0e04003000060561300b241c0c0701c10b00041c000b40007000144015000364083c4c410088051414001d42891701c40542030341d00031070100030240c008200c2c03113480c81e41e000c010b28080b8800b80543e008520796280b4014003490700512984010a052950307943c0c2d24840d18041d615484120b00207001100304510100c1d0301001c000c10044800d0552403030600f1000c0e4100058410648246591080136940b400c0180640480c2c81581000e210b640100340100c0c1d403940251000c80e02038003944030002c9043d151044040340d284e000013410f80b201081140a100b400910400403074041c0e2002c000c0d15860394119003818850595003201c4481d01c001159171624554001d592118450f40c00140c4a612a80000e0040c0003075071120030040008260b407800600c1c0b114003100c403503103072 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 238735314 1250 238734064 238734109
    0x50a051506041d090703120518010e030c011101020d021c06080c030d0c0809060705150106020102091c0c030b10090b1c0206030405120309031b0a030c08070f08040311 73
    0x1d0100d854020400c103d80481858002d00100341510f20810010018591001d00500100080e000080154102d118864105ca4042d07008a0065004107081c403400c0c40701030090080300d4155001580c41003482d41c0403400070b644c04c00041d0540b401c2840079290f500c2100317820000e84402e85081e0310075aa40d5030400d4070183c0060459000540c0c00141c8801203190701d00307042c00303280110b0510744081c0c01031000070703500448002418010400f002c03640c25200410151b20511a0762100c00403802c0f80a000300d02d40c0c224000340c1c130403c80040252084407030140315040e1502d0198699980e0290b030b00c3c041c0c0d080d00c0e040d10400d00a00c040900b03400750480c0107806586040902500042c504075110814501900403140007010505004040c040c0c8500850440c1e03445540b400c150741100c0d0381380d018021130041c03c01961084c502842001c00c10410068156071120320800702a250056285d0081100711614101e001015000070301d803002070001140944c40035008201440107101140c60101d0307454111015 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 238736564 1250 238735314 238735319
    0x3050106051005030f0403170c030105041527060801020a03090b2809210806030d0309050705120f0a0507031103033a0509100e070e01060e01050d050a05150604 70
    0xb40700c3d00f507a5218600140548068a9a04040e2a00c0210300c600130903e03190442080440085240254100c80d01a03c08001c601a403050600c182c40083c0100d500c05000c2d82504643c65810350000c800006003014002072141e603406041c0e08981c0902c080c0c0003c01d4a071060300c802d200040591540c0200020140700e04e91601d44454400d4103980003c4105480d5140043d0702400349a580503a82c4102003d0018000020010003400204049030f201d0f11912549105508080c4240103031540e459005000740f8850f414881040b0540052000b07001803449042041840060304100456070039000c3c101030112103040d810700405450703074002d0240c02680b040060b400e13003400803124130b140d0700384c3d6445102c400800310a100022048040071050654100030a0121048001c030b40c01c101c080e600481002074049080c0d10a444465034401c4089a01341c4e4401001a603000b01560712009005140075880d1031104840d40088600c10380d1440b0301c2666610070407510340c003000c03102030350303a28125001c50600f407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 238737814 1250 238736564 238736567
    0x1050705070918021201051b0909130201020c03150907051e010c140111030f07030b010804110a0306020301080307020102071a0405191203021c0f0c03180506040f030501060510 77
    0x41d07988242180030b40e4450100c0c80c55060140076400603070f4003c24004102c109028410f0281c801507a0720000401211911011000c070001151034804024054401d81d41da010070750380800741982c805a05500404210264581d0b00b07010349200701003004408402802c0c89030f412481c1103034030380025024820321070b0054402d40511802d031202100034a00312880c0145464480c02a101c42890ba200395802d080f100d81600c00001e000c1c61143c01281d400e80b000c0e0b0f9640c0c0b0120240c0e5104d012440c0030608203404100400c1c2c0c040b0500000c52800741005850f41e41e03a076504000c90b0b10903406681541c101080e0f0004540e07051000100420396002a150060748004070714005101307501c9201e02c690380311060b003400f078280d00101c200181091000ea0703902a11a04001e0b454401c3c020491201032005901d0800060042100d030107600340990b90550601e980e03603400d80700b10f825580580310450040d04000350075503910b00240041c0140705000040302c2e05d0341c6059800d5601c542c024510902000021680d000e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 238739064 1250 238737814 238737823
    0x10e010303082403030408010f051b0703080405030c060708070e0a0806060f0d02030d0e0909150415090210120e30040803030c04141e010806010201180b040302060601050705 76
    0x3007540000708581d060f083d10301842c042d0860520341502021900088490040d4001601692090300a0085945d840c0602c2020301000480c6510504240a01408644101c00990307025200e0400c903031a001c131003460585801da08454000c006412002049041680701b2105040090180c407001c0b521800c10702056142d00000b090030380101e80f103109100841d0390b00360711854450b80103070944a5050201200130800c0c001862018011590800810300c02540001c10000d40034000c015000e2903141c030b6503130841c5580d118110b0720280d82c0750950301001d6900c10114140c2c40c03400da261041c4170188480002c0560f512081e91020342d402070440d0b100d065640c6030381c421078410004800e58084036110720650382070240d5009120948404030411030566240d00040c8290341c0c044c42d61484110f800c100304140d0600c1003c0500400050b2026240554000c00000d600450140000310b000c0d03a450300c0701000d030340325100c0035581d04007248148400e154040c0441c0d50041028030b0150f18041c85601c41035601c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 238740314 1250 238739064 238739071
    0x403021c02010914031002030901020d290f04020c010e010507020105070903030206040b091501092c03090904150f1d01050c0f0a03320622020d020405030303100608010e01030308 78
    0x1c4c1d100041c1081c2143e0b0700b80030805e00c0520b041011074403818003c045074004c2d00510080d11035035107080007094030254681000303070715901d100303050542e04000725080c805540c4000c0e00142e000341d02030000c090107100c04e005e0180c20f45001e038000180c1e45004903000b800d403240a841c60090040380e0000b480807070340c0820440d40c4035400a130001600e8a428503500d00d0300c0c03690500e01040c0411140003040715443c680041c03240051840c0c0721480f0400c50007070480c0c041d489028101e0f0341d41c030400042d6040e0400255156005010b01c2da00031031540150540401d4401d61704911546582d0341c031441d0320000d032000c0c00300000400b88000700701e00d150081041c5010f00c200c803801c070b019440100b00d14201358030a07001b5010700c42c2d2aa582c0120301c86000090500d1586403408881c0a401c1c5d400010641d0510190b2507500001d104803180e0b140d403800310400001d40c4544001c42d400740e020403001c2401e803002c00085004000c2a020780b89003a2414800400f4440103130002860564a00d0040000c1307940000710b60f41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 238741564 1250 238740314 238740329
    0x10803070305090f03010204060f090f0f0603050612100b0405010e0c0a05070507081501030212011406040c050705071d0901020a0e010e0f09011806140d060e0712080403021c020109 79
    0x60719192600002d8910411300102c59256000240100d10290300c80c1d81c40c10105400d450f088903560b250512243d4450183c002c90340d5001004608001c1c02c0c0c0b20b0b402154000c0f8000d40010740042808003241d00f090600e90143c0b4145845d640c071402282840e21845006084840d419001e03420000100b032918810780035030004002020030310809002003403149038010300c040d20456800d51140c0c100050038143c24401648076084a0140c0c052805c01800b800155034203000d08140940d865204000c0140340c2203211008000060050303400145080024401074010094003142c0350041038400b82d1602c100900846869005209181419402c40142d1655030341c02d08101d81504032000100c0d0250b0080400290b005110f080000b40500d40c102c5001400f40c1e001c03d05000f060b4481c4220741d10350004261440d04440341c1c0507080007140107540710b450440c0d41c41042e54615591003200324011400c1c4d02043e1407a0702c00150400451500b100c0594a031800741c04022403128032600040c10001044c0f0a100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 238742814 1250 238741564 238741567
    0x60702090705041706061c020d0222020d1d0a03020a020112092003010b011d060703090e07030b04140c0d0506040e19020f010212030c090301150b0d050609010803070305 74
    0x290250b01401c142d0700544404441d410451141345003141c1e8580d01540d105001d00000900380c00d0503803c641c000035035140c0182150310240103035401c0c03100c5110141810306092040406643d00082140020082c0a2244002141e541840d10400ca4168400b0340d4481c0d1b0b03580701c1080c41c00040c0c1c02259042c600b903024200341e5070b154251208075010b4103403180001c146030103028400b00b50381d04d80c42c1048500d04058000300218807081005403200c3c144d180c041c11a1b5050180020940d20344003000380043c91191803c2c1c010940c0d20b10f900d4444ca541a00c00b01e010a480d4207244a0b030781400d00ca40c1d10b17a0845040450901d050207022180a0304c2410201080540c42c0d5000070303041d440750b41004946070b51510440304503600b0400701e8940d08114400c103e2141c0504122901c1c1507200240076940c5d5204405240e26545514402030070075840342e03800e035806540303600d42d101c00600100c20718002024a0050590364075040e0000c00708941004159030720a15103c001031013074640010980d0070b000d0341414010b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 238744064 1250 238742814 238742821
    0x120c0d1401060201020a121107020f040b030105011d0a020a1413030210030f0501091109010c030c0503040303030e0606031b0d0c120807050706030207110904080c0a230c06070209 78
    0x15409030580814461100405200014046605500a101501542c2d0300c4500349050000d015060310420319100c190b1103c14800c000c09480c1070121075800b01c0300140001060f40b00103001c2801e64509911500f144d40b10625134003a1400e400d0004e0380d01080c040000c51508954035400341881a1107020b007403050101042049403000d10041c00030146800901105030b00c0c2086100130064001805581000c03070820000240392000341c0601d034000801000c086041c00c0c42c0000454904800c60400e404010b800644107001c202c040c001000514026580400e04c101c41d005900d20746000502054042d500c4005012065080c8840340441007030304482c900d09240381801c242030200c119401c106801c41d403800c0740c04204481503000b0b000203032140066034002075540b2800d401301d00485502801004a14000d400c40d4500b1122444c0d10901c00d20301d090428403820401440c04168490803602d00c0700b0006500c85000c0f90907003a00c3c41804500091668100c1500420104d002e0050020b000d440c100001c07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 238745314 1250 238744064 238744087
    0x180403020a051c171605130b040b0a030e1605092802040603111c020d0204082505120a140a0f030504030314030f060f0319030810060302120c 62
    0x4102030340b40c224044400262030b1078600c9590303103000543c480c04908507400e102850000d4005480c4141c000895680c52401e540d0302c01d44003580100d1500e540f28038402c1011844402076009840540700c0315048589800f80e1340e8003d0101c510b040c4801c0324a90102c1c5c10240c0c0c4120328649102aa01d098070005003985860a4041c0b01c0e580c081c0c1001301c07140d407024201c0d06040e15640500100c2e019a9014480c02481c5440482684101200b0a40b11341e03030300d80481550015500108641c1c10034000042c6402d41d1030008500b000e512140001241c890b4031850040304110f0018203000d006c04544c40814110001c0c8070b10758030940000001d1030315030002c00103092f00c02d090004143d5207400074181c1c0504540d915000304164410b000032804104025075900030000341500350fa1003141c140900c0d1596849540400041084e104841945031050340d05001409074544250005684640c640e100d285c03c01000c641004095174015104261050041075080c1c0c0c05140c42e00e400c0800c14444641d9409100e01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 238746564 1250 238745314 238745323
    0x50d060b1207210e0c041406012c04020f030f07110307150902030601081e070b0a030b03120d091713051908010203010b040e06100203030a0c050403020a08061b030618040302 76
    0x480c5003c03985054060340303540c1004990b140c40a002110100900c001141e005103402400355003075800940c1e100c070912030300b05078203502d190845613030220300e00e0070b100610020342a80d105000d1031203494004828017142c1a00ca400304c58104209040140754809d81901d09540d90103030b18400707480030400e60310341c0308083d40da60300c02441f40d41c014040d02d0966131101850f80e92520581244007118580024500d00000701065181c01c2e10112a00d4030702d00741c00003c084018202074004030390b160080a06030009001440010480807003010382c049030706040d030f090404c3c81c52028001c0b658403010401000c005028011800ea0076a40221a03402c00740c0b0182100301043c24158000203125071000001098081405020308110307190001440c0700355a4039828440805211a2804096441400414000b03115a0002054079200b03103081030030140e07a40c00298400085038044207450700305e0300030300141c000000d0800020404032525240346092400218061b49080c0303c100440742186004030b02014424003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 238747814 1250 238746564 238746617
    0x313060b0904050a050d030e030d020f360a03021c1a091c0c12050f07050111090103060e0408070f0213020703031409070623070f03050d060b1207 64
    0x100121141d2034a8a040750741c03200b04d541d0940f42442000246510144a4001e0b4a00d09034860040c40c2000d43c1040e2a0740607401458107a42d8242060011070a14000441031160300069085803403a0751544000e19150340d0a9610101d0240e01307003090600240c0c854244c0d5640b1840c000b40e14443e10031150501c140c03c46006081038508403c004203101d54800300040d40d64003030003210480207c2e0000030000b031740c020046400081c4512040e955490f0b1880c010005061000d9000549038a041c0d695500c040c01c45121505119580c1008540e26110b1350341845203c0182c815002c0480c624100398a401d41140038440d0018002c442c0d0410000c11501da03002d024100c0700a0304800d54460b0340b180740c0640034180c500c080c17841070307441c03000050720881c0e00095441c1200c40503228902403800e84411a80d0000050b214000070850802190000850b490500d0300030600070342c3c804e5283d15500c0382020a4503126400240c0003141445001051200911203c0d0031101605001e07023040c16101c4021124201380 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 238749064 1250 238747814 238747819
    0x3010b0708040e1302030c0906011205040203070f170d110a0809010e040f050403030c051317031608030a0608070b030c0d060b0d0207030e0d05070b0a11070f0501020f07030203030313060b 82
    0x208184804a0042084d000c4881d10840646162000300d10178414000002c070740c010b0020b448a01c0044818030365502650700701e4009030541c1c1046440d12003100707491410742d21215075140514203d1400d5141400000302d500411b1910401031700c800700d1070503500c481c1ba88000d08204000946042568000e0900c040300300c0000d40709120010038114400c008040499069020038103001d4510b564510500444a1600820009150450904801c4075000480d101c2c042c8980c402017080b00b100740c1c3d02c100e002505500c200940c075602c0c6420032803201a074007158400820f40c0d101c00001d00101a136030041ea5880044009a244c8441c000e4840350090031681d401800d50000c0002c040d444404079400802d600d50098689001c28009001440b4249041010290007a04110001d0050848040060404071080d141101010301141201401c120050344400e68079110303140c0c10040f0f5601841010010003d80025048491860700841e440384802410048150500c640384070411400e5841018201c001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 238750314 1250 238749064 238749089
    0x1003060e0c07110907091e080105040f14030a05180f040906050a14090a0602090102120309061006050a1e0c060509010b0f0a0f0b1b160905010b0f03010b070804 70
    0x84800200d1941c442101951010303102c0b0481061800e05513010f500a180e203a48028155207030002400090305031500d0036984210840000482100074001c190249010b03105c2d0002d200e005207406014a10300305484501900240301d2a011107400c142620313500e0403190050f450300a00040002c10310000e03c000380e540246020100400d0160542c0218410a0340c40b00130040c0c82c103400b00812620904a944020660101e251100003441e103402078441100180112103210703020320340406164204483d0417009620540c03c00c404855480201002030070f8600b0090316101314408018015409842d4400341100d0403150504110310404540224682140d0b0070406400c0c12042c1c1400b800d00248582d110301c85540d400701c1c40f440c059541c0fa04072340084540070801850700c5c21000254000d0a603078140350400400000b20042c1c18400d0070703100007500003012003103401c00e20603004031041030304a0144108113010446603407113001d08880c1554071944c89035854803042d2801c03540750311a50b000220951003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 238751564 1250 238750314 238750321
    0x70c0f0b190509011a120a020904110109060f080a0b0a17011a1f0309060f0504080d05250c050a05070e0a180c03030c0c0506180108010e0601020c1003060e 68
    0x500282007061803000310418002512480009803e030b41740310f111100f10031a0a480e6611a1920300741c03030b40c1c402d4802070175101881c44c9900091281076045500791400441014900d180750b038405400750140c1068288008003402803c00106501001040712000e02c1e0b0b1102449031582c1c84400e034100a144900c0b132880282030005000303000c4c1c40005180b080300002e41d2200c00052034210046440b128000300c81c803107800c00d0500e048016044942c4d041d00e90310f80c0c2c1d050f884c824000da0b02500303101c1e40c0600c1e0310690f0346001102410444c0c174014010143da814180e0324850036400c400c09664170410504c1d111100000754100b0750300f0f1001c0e55400400c0c0c1d10602c800007903117040032140b40e841111100e070100541b21203049100944504003500a152645000c130030320009020319901c20205001d00d078002001c4e43c40d6800300d0003d13800b0440c05003000c2a040040d080c10342c0d01034829805850701100700707145410b200e00080c0d0394000480c6443d100702da8098140340150300c250b00040040403c150145050704 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 238752814 1250 238751564 238751581
    0x61103040f1b0b0a051201050f0306220203030d0b031b0901090c2619020403050d0c0326100b070506010506071511030717100b0f0f070812011d070c0f0b 67
    0x344841b0151107001e103020b0001515191000780003144080150140080ba0f40f54072150004850f00d00d4400040c031030803c040e60158800308046c010385500b402001030380000d150b0806280c20341c2c40f005c0d11071046e100d8400381c0356612410300f95811a000300c1000f15044841c24020b48255110540d100d8070413540000d42c4010140b50107009016041c030313a40c6260864060780c0e101b0f041e88074034000070348103600990041e0b1040740314107181b000581c0240b6010348001c210103400e500d1900b07204885000680c2d01800d01030407414040ba07080050400c400388034078100340c42c2e070b519841e01d1051040c00d200e184c0100c3d10406100c115103e45116440f500e004100c541c00b107030011041600252071100009204654405031107032014a014001c2c507080d8600c080c254078251b00603803564440480380d050180c0901442d00e510503280007508066102e80426510b6900750700b202c49501e14140c0c0a544509c880d1b1207101c00c910b224200d0203400807410b14002080400c81d0070300c107000007550400101404100000c109558 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 238754064 1250 238752814 238752817
    0x90d021203090418030207030b13120e040b030c0a09020315120601142709030c010e10140601050d020c150c0307020d14121801090f061103040f1b0b0a05 67
    0x14804030380c00c000801e04007140f1303e020070131904000c0159022410900c0410f00c00302ca200e910000780341c0c1010f49404650b5511010003000f4030304d034010503100030400800b4a064020071680b04420780090081e005203c0006210714624450907100075130000c00f1501e250b00c43d85040e42c00102c0a4450f80c5010048914540e54002c2441170021043d241c0030543d45925103150f081c82d000b400584a0350b55540d070781e14070f10003024010b000c1c00d40900c002c01c1062207019007802564546142c11000d00700036101410014140d961140000d46440815810411141c1e0400709840e090f258441c00181c9805201000a00d88541d81030740310040301d620001c001070501068011351058500b070f13082e40c0c118503203035034196003c510f142c80c0c03d10a90020b00024020500c5805002d80c481e401c4420003007e0003e2403102400c4a02c204000c0d90f40e107a40300300c0c4030103001c030b14020150503c0300c224a03e1f280d032801e900c402d2140a4a2070004205101c0e02c2181c801f0b1840600206000e000f000550301e545186240c00580103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 238755314 1250 238754064 238754077
    0x3030403090b030103171b0115031104090b010e041502070b0103060e010c020d030e1510060f140a050904090c0b030105032e15240809061b090d021203 66
    0x1030003507038011400241035410b6030304803580103240b242903d5201581d031b2032980111640c00d0080c0b40018810038644424000c4020354544045141a95811802c043d440350307405903102e5024500300032007100050b00307101e805811540b0540101d00152242d15203031814030340c040c4220042c5130010407004144800c40740c00904a0303110351010010390009060450a03550180381c540f0147e001b1101d2000254003a401001c451842d41090741d403405000341740b4560450042c0d45500001000c0315007071010075000035031000b1994144c14840f180b2202001c0d00d8003140b1a42610804000c40801c21101580326600075802c850343c005041d500c0d598992034102401d8000b407190b103200e0303c00c01030100380c003044509580500c00410b6004040c0c014042e55105c01801d8000e14006d10003264680c001201b1814032100c0821881c21070404108010f07100c8000c102100141c0200e1440c0c00050901124032015100312404001707030101c003601c0d5500c49d400105820070483c400303034000c1c2c1200041d5403001c4000c002010f4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 238756564 1250 238755314 238755317
    0x110a091a090a1509180b010b0703080f011a0d0608030c0d030c0f020c15130306090303060f08030702040f200903011107020a09050a09020d0303050403080916030602130b070503030403 80
    0x8190b500c4107000c80c151000410000450303018514280180542c607000404200126009400350b008640d813851041542680712078203818000c5200f41c03c043e80501000c0d045801c01c103481d200e80d414444402c1c9000b9100c41d03054100785000030000380a01c0340b500018024202c0d83d050729202c0002d0329049031075002c80210000040e1404994985040c042d2084035840f143d11b07801408030030742400a002c0f9200145030740c0022083e0520400c0091048500c1100155100c2c0c0804150381c0b03598500a01610700b690002a02d201c0c0fa050b080c0b28203500002546c0c0e000e07804880100781d0030300c1840d2400050040a40e059820b0740200c44801d0580d0b0ba03480140003a500a5008000f0383c600821050110300139039400035400b800144c0c0411402e80c3d81e0b08456000201580c0014101d81c0580c00030344054040542100070940760802c120070b16400101c0154800407940141805100f0684810b00b94403007800021305203980428040c0314091511135a101800c8041d071469510501401c00507601d800c05c880860 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 238757814 1250 238756564 238756579
    0x225020a0b0a0c1202210a0f0804060902040e030a0314010506190e100509031b030d050a020c0d0f120314070c05070b0c031c06031709030109020415080c041503110a091a 74
    0xd1940c5141003107c02e440701c155200302c5030b0381c494207040321240300c0a00280c0ea446c0e1202034141c0581d035140300c0d0740c51140440c002107590f10030320103000d400e035542401441080c90040b401040b80c0c9e21200f085036000c1500701c0d040e0030a204100003d440140c464000d090300881100841080360f40c1100c024030003090110304403035142d1030b400000c49004800340c6185415030001c6090710100c5000d400540f0750079101c0e0050301c00c04000308012500c044100c00003568010304d040c00480602201c0f43e184070166039503241c02c0c014055040030841440300c0203840c0d4010040000c08010921600f0b10400c070140c0031000b000c9582e02c0100170079aa4940020b05001e9600245000900600405e8410081204c1e80102d8214030510308903d0703d0400c1e00860358250b00755403034107403440043c0c0e0f90b0312403454980c0120002d0b500079070514072454039200316840c0322401036140400d5021460b14203007924084035800040900c94503000ba001c5101003545a0100c1c401038149003c804404200384d0840c8844074007038501c031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 238759064 1250 238757814 238757863
    0x2203030e0114070c0e0903190509042403031103090307090c02160e01030605151f0f021b12070e0a0203040b070f081602030412060225020a0b0a0c1202 66
    0x2956510650f18010070500f100075042002c132040c0f8460b9a031010145043e2030506d5001c09400240611290480c80028400502d0000c02c0c1303014420706085400e10002d0301c1c01707030b10400d4019001074114000031b0305200310740268441003a01041203d5802102501344c4048503512410103018203202203d00c2d0140c01080b41c4903000b400307445002e504482d00031308824032a03440d54880f80c4c01010060800c25040030306001d021f2181c0c4404620446203810400199205261030100074003003001d03000300710704540042401c0701119642c2c0e2010b03640706d042200c0200301c4851402842c3d10340381155000411000c000001c025100c1d074107a002c2c5210383d000d81c90600f01e5596080b02202c516052840070f401040440c404103c5100244041040b0407090b8012246029151800d032442c1b001520310441e100b80d000211300c240c210398444407840720700c01f12403405120071140d0300150200c0e080c0e000348030443e000461512301240c411081c0c2001250084a0001000081c540080d1502d0301d40d0500d00300d07044060b245c2d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 238760314 1250 238759064 238759097
    0xc03070b010b0c0a11040212130308010602010509070501030f02070609030909140714030402010e032a040c02070612150e07030c0c08190207080607020c1504060905062203030e01 78
    0x84800f1030108002070409202c007990b5615101c000034803070a030410b6082c001c0c01e202482400120303001da04820013074140d081076854010f01d1500160171010469041030300380715400a001451a003621024200403c61102d1511000b00038001c3c404040c10b020b0500381c801003855004181c0c0c4041c1c0c0c5420034180001124502c2040318905d00b50354070030004c0c403c20035180d80845074202564005205240603c0055010360000e45400120321100c0119544504441d48050840e0034003202c201090710280a10410380d20040e446240d81c0c4502c1d814040d0500d003c448400301680900003680550300301628a40c3ca03954000300b41041200d80d500800d2a01c1102c0e00c42c18019401c400140e540085618a00103a81c0041005440c540308600d00754881c0000210f5609418001c107407081c4001d500600000300d855041118088210040c0e40011400300800d000d61980203400b502030360fa05070354655445024030b10741241090050140100c0c01c126076030200030180d2190345c52401c841e090341c5804141070308406 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 238761564 1250 238760314 238760317
    0x50c030a180b030402090106080c0912300a051b0102070303021201050108060d120c062406050406080a0c090b0c07050109050612040609050a0206070f1a09030307230c03070b010b 78
    0x1400396104a411004000542c452780d070b05940511502c02c1141132808003804602c10240690710507030190000c802d42c0b00700140405428002c10898000f94041180030440001c052250200303d40402600081c44001400f02c0c503040d90b4a048900000c5548100c3c60400038001c0d044000107900a105003c000620f661048403510300440c001040210344c1c000660b544c80450800c1c020101c24000104840b001003a0b05100e61040382e03211140c1c5011010044070407804d02000c031381121052000a01003400b800d540588401c0e8810700e8900000350150081401f51034610565104441144000400a02c507640c007081420031030f5421303201d0030880d80e10340e01009258000c8480001c564042080044c010608a4000001071801001501e440b003120381c0200300541d0000c00255201e4035018805000c07c40c039070034004055090001200220308000c80125141e00c00a0010710801c135a0aa2143c603a440913003502290480d03101040e5520004000815100d4000c6103007502c0b1000f5100001031700ca80e0440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 238762814 1250 238761564 238761571
    0xf09411606050a03060e071b03030b060d0b1302041a070c171c140d0510030605100812030c0304031107090e010b0f04023405031308060601030b090115050c030a180b03 73
    0x100e88004400001c1316031032340504100c0e400c2d01016211602c290180d00c815006090311031803410007241c04011501880030041e407440401c2d1002d841048204400c3c10700c194004c00d4620314114081d07a0b06440d040c0940614015042003800000c2c000340714020010002d210050f44d40d844000082c0d500c6e801c041a1450f104c1c00014403640030080182d445d2907841540080d40c428440b10700c00041c0341e144d403a02c1c402c441e4222844405800c00740c00c180107c0e03004000052625a0701e0954034518074250501c13001c1c13800090301c010180448010451011182404190007800c0da180d010000100c204550b113018080301041607000c0c02480c8020b04480c2814001c03110f980601014085882100c4080b02040010019aa4a203501020901c100103031090000b4000c1080c8201c0200d43c940c202004e0605141c4043c150606240c40c000d884801501c0f0300e03e2560450700e540700d0814948580071000d540b07d01c00c1403420f4840780400a42c200165421009004049003803030701007076a958a8840042c031921065 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 238764064 1250 238762814 238762817
    0x3040b061e06070c0b0406170108120702040b0d050a0b010603110702150307051606090b0a230a0e030c011d150f13060f09411606050a03060e07 63
    0x820007035007418007100a0003064400d4650f0100c2035503620340703207180d03410540101c000075a50014201045100340d01a901615035040517000c04018042c2d50103d40c490f20900a01444c0c480c0484c003200c0d6182540c051000e03030880c0c20f82d004070090b03141607c0440000d002c1c0d000170900d003682c0c100201855206507880b0700d601803c804481451200300c0c41c41508010880f2003008001c2040b00094030800155030074540c4078000c0810360020f0b500c1c14441002000f041d0961480c50805c0d0800d49124000c0ac0d5034000c076000c006144180c0700d4800000c042d02c101055048203201c002a0002000c0055000300c01c01040102e625480c4040d02031281d48035080c18034600128901c500102e03100000c5c0801e02a0085c808401c4541a041207640d80000d0b10110400f10710b080c5c0e9562540c1c0b091001d5042c002c0c80051410960f5100006c204810003500a10003154001041446000c5071803100c040101401100446401d01d80c03090350b800005000794015849100042e0800b03c0000e441044000d1450095055 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 238765314 1250 238764064 238764109
    0x11505030d0306080c061602030a0501150605030705070b0a1d03030604050a11072d080c01060801020405030a060b04150b03070e060901090b130308041707050909060c2101090203040b06 81
    0x81c001c0111b96009078044100303100e01e0064401c0169400c00035203400521880c004a90318601ca98004401c480c0340d4040f00600c0010010001040d5100b8116171380542c1c440303120700d06901c7d0b0204079402401454110800408002d040d2400264000007441c454601168107111950b40c1c0421223080da0041450000480c00c140011000a400d25241d58030b1101950388801b2655a41e025100c503407228020240d8003060001802c06100000f8000c1c4009080c404000358506803800300403070341c1c4a91040014001c2039a44001801c1c959036500501d0782c5252480a1201103a11149603c43c07a920549030f40c00440d210140b40710a5061020580302d21060507103c0c20800f03450011844030a03800003640c040c865410180c044002418800904040c0414172104000703030001c2ca10441c80c0c0b2100f90050352244480d01c0400070341d240b00040c040c1d070140d120110a0344440440342c481610b004150140c6208218090012030019120350185102d140a098520441c0d2903000502c07030154090f100e941000d004c3c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 238766564 1250 238765314 238765333
    0x313110a0326090301050a020405030d0e010f03020d0207020604030c0e0a1404030e01120e0705100c1106090a0314010b011b050601030b100504060e010801060609080604110a0305011505030d030608 86
    0x42245503180c2d0300c2c4100180038039081000001901312801200c15801c2c841d801b080c248514182001240452201814880c01a414600000e44102c4814201c50b0806800103240c20310030410350161183d956000c1c00540d01ea507101c0c648042800e0440c06158955000c20f0b00060400417540504641d03001c850301c94803071035111a202240c0d80408403400300d061020a901c0c0e2212038155114210700c01031980d0160032090309001c100142c5004210884041001c076503000c00104031001c0c48003d003d1000c42c1e00f5661000f4950106d55040010360003d44543c0c404440c400e00c21006401c420800c6809a941c4080c0d01e40000d6100c548804502015242d644050b00500c00503840d2500e40b50000065080800c2e00da179920009019210395401005002c0644070041010b56424054100600940e00b41460b905081003000c568680c0c1c010f00251480c15081324a28980d12000084000fa541210007400414060740d00100300c0100e5106983c040e209240450314803a101c0d01c031313107130541d0340035005450320a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 238767814 1250 238766564 238766603
    0x1a0c04060e0f06091207050a09111602120f010c12020f03070f050f0a0509031009051b2116050102030a120b03151306050105011b0201030906110313110a03 68
    0x4807451407054001500300004070703055071072075a451480b851045c0100513090400052240c10485a0305c61340101741440941507098004205950002e041420f005401c07440c1800068401d16001c41c507428039014000d130030400300c0360640140c004c0e102591a40039256950a41680403403007107400d40305c2d02145c20300104190a108542c0c014003120b0a203861801c040c040300a0761050307806201101d0100d0000144201141403c0c4400f903001e001c0c0790800c015040254907440e403180410003ca02c8443d0801900354802d907681c001100ca07014401c08045041c00941450640d03a034040076070419076081c102800502980f0000072500e10203c40d41e03c8260703000452441d20060410400340b10790502810520818018030410b00600c24034185e041170084050b0760408908030b40b010f0700712604105281134100c5404110745480b60003283d080c60300281499480c1000c10042078480070400c16a080042030041c0280e1260700c59a80c14000c1c1e510f80c524180090070414107124a01c80103003543d0540d41b484000c007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 238769064 1250 238767814 238767829
    0x7110609061804090c0602030408060a05091e01020c0d0306050306160f12090206120105010914010206010308030711010c05030a0e06090c04200d15080309130218030a1a0c04060e 78
    0x203001c2d0000c51080707105d0352840d0081d02541c1000c3d0041e8030200741000a48810030809401200d48003040216060038000c15456201c501115910340a2414920b01312920075811150489540c60070340d0481c000e03005009000d001607204ea148240b240a010818501c0801c44d003504401d026250800750070a48001601e00c4a040d0b85080780300c0341e940c95041c0250f12590000c0c2031004180014441641c1042d00151400903950044031441522246078140351b42c0015074141500e402101943c2c4a0307980140441d41154802605941c81d402d00d108102c80e40e4000340a5070142d00c4aa05c140700b08250000c0f0160380310b404556043d03040c1e01401c0c812440d810190b000d092054909074807000c9212410f107404009030301414805a4981c0d58400d450710400e0140344002c0903040c0c0740040c514140c00c840000d00e9030156040d02403103142d07001409070000e0401244200c0c000e00b014013610f034152914281808116500c1e1070302009451164005844080b030701080f101a90b0f03298413070102180299040c00483c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 238770314 1250 238769064 238769107
    0x51008240109050a0306143916030804120f02210f0417010f020327012007060605010c0f0f1a04050a1101030c09030f0507030f03050711060906 63
    0x10700c81100d0b00030070251a8000400c002d03600400000c0782c0440c4800d4040200074000f081c0000800400c1d01e6103450041c1c440300d8219025400340c81000848c0c0c000c008244034410003101841003a1099100b10404d034014000c14172840c06009403600100780d2000c01c0e00c6016215420740f0040c3c100c0c1c00c5c00d080450b00d07164600d02c103405a13210541029410301340c900e4150b2050300320720b40c03154448040b008480e800340a21111911901825804d60521001000d0b040d20002d00074003110207081860341060344254440700e415814424034009c14030851a9840300d0354404441940d0b41070034103502080c80c0d400380c082c2c100d406a10240b6800141519295428105c1c085070040f00d000c4000710781c0c1d1100600c03e08419011f03d009101030100d0984a1502c2103015022019443c141802c0003191703400382d034020007120200c1b03030040803c6d51356402a00d807907414601c080d00020b059000150b043c80c141503003c40548000c92050a058211404080400802e400745003040780e408802001213660644412a00c10030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 238771564 1250 238770314 238770317
    0xb0a080a02070f050f0c030d080c09030a0203071d09030313021309020406060504360c050c0105040303020405100206190c110d1805011809020c0a1a010510082401 71
    0x5000b45503407070301008010140103481943c010404408044000e110481c880e0b038044000700032402c0d11035406407007104001e03d804002880400d1201d00c81d02c05205d0340103d96401070a440126882c0d001c8640c08004625500ca5840744500003e0904e40340002140d0003060580e44040301d10750150708014000084a441114283e00e4007440f00c01610769000b005c000c1c02886c1c540300d4469007000810780020212002d0010290880c1807811030080d600b903201e0f050140d0533403020502903451303041130702d080c8150b12294042e5843d10381040249a49603010b001034860469038007001e40c9125400301c2c0d989409a9070b908203070801400312a05062103620071015000a42480041d0b01d0002c00d1007802e255044407a0400f0505640060209132007060005001e08001d003040c40d401010341c45802c281d07040074060030240f80d9000a034003c400b0f100300044c6c1103d82c0c0c0035182c002210205085450102c0003842007070b0040c48840707048041e69001d01c0c3c055100e4010400c201c2c00c1049410036201401c00c000021a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 238772814 1250 238771564 238771567
    0x50f0f031c1806020c030306040b01020a0f020f0301020403170703090f0b1206130507020a02040605040603081b15040c0801060614090d1112010e150915060a0b12060f0105040b0a080a02 81
    0x10000329a4006010745c00c0410001c0c580b240f80000c1440f040d582c5148101741150000045000001c50f20a400c003521a01600c591481113880740200340203128541014100b1403141140089000780719004005141c805e5803282c4070306582c0e251510b44c0501c3c038091241e5400302030002c02d85255150215551104c3d000300b02042180b0018504001c40d50196800f400580000300c000c030541c1481d006100040600355800c00915145454925890241d1a01508143d40455a108056504014020402421040c82e0710142003514000071038144074814100b4550801c100018124081c50761305203240c803240300f1750f441d184211040104440500008550355007024030405c0480e161803001862110f66080005441e0340907910581c079001c28030b012010303141181c104000b608940800c4a1140e2148804a003405454a8001890001040d00400e161150204040100b801e5440245010b5072094a41c0c04d480980680111002d110701d010308100c07510708000e2052224801c100b52a44040000c0006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 238774064 1250 238772814 238772861
    0x702150c0f03040f020a0b030c04090b040204080d0c050f0303161809052d090c09181203180d0e0d060603060912080a05070807081e04050f0f031c 64
    0x1005030b0420380741501c1080b10707000100210b0501000420141c1100000700341186090764400c030b424481c0740038200303c40d506c03515800540d032226019200074003030b2901950007080004400820490341c80a06581510030b84600c07003007008001c411a40604c0e200f90561a82104082054510988030000e4201cbd00045801c0041c0605261003654080d49011101c007000181c91030907003500d565008600e4640d654001c0510002050004100040c2142510501400e070f54181207215080e69801001340349000b88000ca141000c00480107510401e6030070008003c041000382c5840e6030301051815540444d4401c1100040307850100034000d151403040d41c020913020340720350769034080d1140d02404889050340c129800c01003d410010242d07005912040411081c40e140b80c00a00c0030b48040d113048240082207000ca2040c001002584000d13840410340d250a6003000d1801c03541d50a4611000c004900a100e00420f00340d602000719540413521042400034114401c0c100c02c020302e02c809a001c0c0920001604 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 238775314 1250 238774064 238774087
    0x80105060f130b040f050303030c0306190b04031b060c02010f11010e010905010f2f07171c110708040e0a021b100c091d0901020904020403050a020307050103050702150c 74
    0x15140070700a180110f9072a20b2130007115500d01c0301550030142c800d8000b80b0400c982c3c040404140d943c008012280860001291102201c100c1e869400066407a40006004018040c54002061806040d42d000760402955000c0403541940f220074000d00050460484a8030719215800040b004c1c1920800012800b001c0d080d00c0c1d0844200040840d81a51203030b0003c070690840b4401c5052980e0480781001c0d882080701520382c00c20381200620524201c0104a51003800101c0462a42d0030850b005e00e42d039204248100d02031030040c501580c20640781800c044644400c19031065441b1190310090440c20907041020400310340500034880c8406580c05d0184030241041080207042000030380300500410071400741400309507000481d580303041c00050401003210200002440004001c1c40494441030388aa81d031481c003900c21101c100707900c6400030a010060040200f400c400c2c851007181112000c07540c2c0c42c015400e8480860340100540c000340b46031b00c100030005c03808691000c182808d0030300e0001ca0044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 238776564 1250 238775314 238775347
    0x4091e1103071404050c09060a050708040506030f24030307080d1b0c0b0a11040306050402010e15042108040608040807020603040b16140906070c03020907020d080c0a080105060f 78
    0x2283d51110f1034012520309040c00d00c5440d80103800c2148a901d40002000030882621644400030304110002914a050006490581c5c01502d1300030002030b80d070b0a012151241d500302c140c0b490100c58802c14201042041004080c1185150180295042030b11a4a41d840d003600890210074a20b03072204c10101d401104513000c441d08200c0303910b84024146081c03e0594980c200286000c2016245c4034000e40f910360302e0001d403011a98400000300e0242d80d140300487d4000b64120045400024469842c00c1510080024005580c284000240c94070301100e40704406c83c5a62901a20706001003005101d140c1c4294109c9910a005880e800e103482c1c0d955001c50165401101c003903070141e00c5902400381c2d030b500e0b01d00210703601a4240742c01030451b4a01d0704a80342c06e105070340b800b0344203000014500082040c850360050007190000c1581003d8900390314060740710781c0c00105200006100c1d10000340c3d80f0580c01c060303814043c069641c18405a080c20180700c42684400405200c1c403100384070340000c5440500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 238777814 1250 238776564 238776569
    0x60815010825180c08180a230f0714010c02060711030f19020f03030903150712020705060708060a030b042405070914030706050904090c03050a060203100504091e110307 74
    0x1500091050071041c4010629031024068203008000918414003a0100041041c0f805230020403200400384212000f03000382400e1541c42d0060300580034004040f80d0041040350440c0c0c80807054034503801d0700c8001102c0c40501210004c3d4850401d01a00001c51102100215241d030090215000070401145851070581c002c0303241145016101c400e20112b003041d415031030400506030021800c240307903c40029240c42c8001c1142829020500006010620600c1c507901d00c001c0b4100115541c01c064102039444240c11221100891540000314a850601505001c1101d0b0090405880bc5d212551416140c0b50100d02c52075815045158060317500e000c900c5080c1c0110215100c60b204640792008036001c1d40901d10303803035110303800c4540c00f0071050380c01004a4100b42d004850000341c5413240e1030b0500b00c01301c0130f820141c5140304582098003001940d07401107002e2002d080c08800303155942c0007004103403505510300030f18944202c80701080b007040c0381d20720381d4606205001c10040d80078280c0200b880c040c2035a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 238779064 1250 238777814 238777859
    0x703020904210504030803040f02040b0d060221100b0c0c062701020303090316141c1d010c120c062c010e07060807090b0d060815010825 60
    0x10002c401c1d01d040c2202c0c254a0303a041c1040c604107481c0d91141403190000074005484030b000c515204086648660101610080042110b48154402e00300f00c402504400b0312600d5007138842d07620300c0002201c100014031a03010303d04a0349025040c49a40e080c9a08200d41555080c80340b0400040150766a50282c6640001e080c10b4449403140c0c3d402100b1000041e0b40c6242c1550420400c3c05078018001c01140c1ca0001c1004407942180d0b0715151280320801500115501c0d4040c0a100340480c1809a1019212030040d559100180c19408040c0d480310340d01001a0340858144405c0c40001030b0410503840203220749042140060341d9a40340d0400750354421a20201c0b050200a54010310b81d5044c03a0203c1c01d0719618000c01070840c2448000e542e4460307500074a400d00018200040398503105101c1d01c0080c5c0020300045445880c05e45079480070b01a14010403080340160200d89640252a900c024100d901520040c0715070300f03102046070780c2000c22020030010300302200e074041415a400000e82c800003451 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 238780314 1250 238779064 238779083
    0x304080d050a2c0f0f0409080703081501020a15021303032102090906010e0613031109090a110111070e1e22022e11070603060501050414030703020904 66
    0x7002c400400c0f0400004021640340041c0074840b03280003460300c1040602d2820b40e142c44000f02075100144a4000b6100b8040d402420300302c0e5802080f851034081c00401d4031a459182d520f46860041c5141c0f500c80c503006500583c841032450000c1845001c0700403000c0c86400c401171400441d58280785407891240c2041c3c0200c0e40b180001910080302201480c2d029500b0641107040c0106440003414119018022a0402c20700c1302e80c40c0c0003507548404488040c8800043c0640305a581c1c9400d4101d0035540c00340c140b00b0700c0044009140740d000402d21081140d40644040301034650200150340d540603c0d1002e060398400d00c2808a100d50301d0541c400c0c00703004181d01842243c41030000d0204091002028130024110140e0b502c1081c40441c2201c0200b00d0741240c0c10b050350005c0304a05003801d80c144e402010444100a0482c00c05038000713000d030038481004001e0712195034417401c5c207805035511480b501c1c1c0000c1c003c1100304520101101d6201201100500f40d95803103a0303a8000030720380c4070705907800d481c110030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 238781564 1250 238780314 238780327
    0x3060b03040302070f0f050307291305030705100210090309080a0b0105040f11070303023a0507020607020a14030d020c161d070804050a0204050106030c0e0a0f170304080d05 76
    0x1081a01d400040c0b0401c0c00d0003291604140c007090300c54803d4031400f40ca0744210070540c809100450b0ac1240c1480c0c0401c10940c0710b0507020102c0001d40c200c0d100da0350007402181004181d41c00c000398440e1030440c2540040c52079000102181c001418105c1d0182d04000b502c080208030410140007107070005004041c982e01950422003000100c4e0000d803860f1070443d240c419501c00d801404010303034032440e0705401d00507207554122000000000003034504c13180b5400d00402c24000590301e02c13180020380610f21400c004560342c05200b6030362000c040d40c401c00913911400900340010540402c0c00a140c42050642e0300304040011480141c4e08600c42404c00d079003103606220004106030500100511340740300c65110027100040c50480e521b90203081e99007000018400a01480001c0103082007569010b8020800756035918401001000c4160070480014030180d4140383c0c624010074101e090f00c070070100040742c0900c0d0429101c91a03041e45156009400b0a00001034140c2d0280494082030f1314079110580c2c1e41c0d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 238782814 1250 238781564 238781579
    0x50609012318070e1c020102151b0d02070b130c0b16051e0f0a030516031b030503061504150503040c0e040f021518100306050316030516080606040c03060b0304030207 73
    0x60a45d40d00e400c0c2a0f00c1c0f182400050b0b80d00003181d22541d0300490700c1c80700c65140c0c140c07082121010030441c50301c10240007600e10000440c41e80100505805061710380000d40310000030700d889000312240940400d403c030206011102c81e1500500c03455100c000364190744802542c5213418110b00c46200420300c00d10000b0480340b20300030302240141440d401c010f030150145581e0054402c2c020307081401d007800740d140703803800806000740b0300ca00c40c00186c03450190302400903250040403540119802c9000c2c040d003a205152855400f800c2d141918441001c0c0d040810b012001160140c000520643d041614070b0b00c0000c40d072801300c04507400713680034400140f01c600c00ca0041c03040901b496600f01c03021210400c5214070b04510544401590102210007844181c560282180502102d40044d0740c1070280d6071021421828914601003168810003d0b2894640614150864000340f03200d85941034001d000099001c0c43d056220805421860500107501034960811500c4d41d00111000c801583c8080401e02511 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 238784064 1250 238782814 238782829
    0x50c0a020c03160905070507020301020d05091009030206060603041a0405010e0d0e2103210a060b0909190207060c0206041412090607050309040203070210050609012318070e 76
    0x1000354001c000b003a080f0001c0d1003900302c443c45100c0d24641d0320404036008500c907000315020650010004c1d92030351540101034005100581e84042c40d41b04800e40700d03100708041c0c001c4000341601500a41250f07a00c007000e01c001688002c1c403c407900440b60411124508565409034001ca01800c0002102c5461a480e1071608698901c0c58041c42140d0181c501a07a85003205645440094a000200c6481410a0b945980228010410820040380024080c0c9101114080c440d2044d52014002c0c01d995403886502032242d070100d1600705500c003001030401d4580a030490310781e95200070014900344d050f0726940c00301e5020030311f00381c01604118280402c3c03012084c1c0d601c185205e020050140000150b110b004244140b02a0383d016800100344202480700c00d0050394500c10001c1c0003556a85401d200094840004221501c802840c2ca00490300ca810140260307810384107a503004086034030360901541090300042034000d61090102c0189450400b852500764043c90880c1c0300c184551203950300b0000d44 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 238785314 1250 238784064 238784083
    0x418060b03060a060c0302012a02060f04080301060c030c0f1536021908150109050601020613080c07030c050a06020307172802070e130c030201050d0f050c0a02 70
    0x3500c028030901001c1d076200302e00081243c1c02400c10b90380750f1180c3e10302a1b003d400a000b0700820043c11110203000c201c1d4807401000c0140c155405d0b1103450ba10038000411001040e9005030600d00180010300042e8002c074a55a000703806410010b060b08400e6480808203400e01c2d000325001d83c03100000080c0c1d89100d0086000e150816139150100303003070484001440361110600380040200311003403441592140002d1444c00c0700c00550300014103458500755a961030700711000c1c00200300540000034404002d482140d004a505a000d400e458696248403080301c0481842591b0010041244010640040050f0002140f081c03e010346c0d210b240a0411030568582d034000002c1d500100b044d100061030708070040342421180d00d07009071258030a095481d4003801d410b06d200700e0000c1440350b000c00b1680000710f03841112101c1d2240c025582d118007160301200c0c10014000d0403441c1c01c58040c001980103030040c1140d10915440000c2c001d20302c0f1210401e80e842a40c0880b0b1800e0001280c41e1004d5051099410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 238786564 1250 238785314 238785329
    0x7080a0303151d06010e01090902030a050f0f04050a0308061f08070207050409080429070302010902190b2a031317070308030406020306010311070602030708090d200111041806 77
    0x10f240d4801d40c01c604140700010661030422464109a03030b030581c003440c1f0070005864004011501c034a446c402c0040185400d447d4a144c80503070380700140c1480b000000292103241d02030080c00385c1c0200365500b074404050160042e80e010740f07258a19040c2080840300444a0340141d074170064203042c943d501030b003804244d421050007281000d08410105079403801b00c80c1145c1d9030341e003641c0b110111588000000c00c1107031110640c000c07001071014281a4150000031000740220b0301400b00c241a0243d00c41110650303c40c2403078061040c0001e1031080050010302e803005034000c00d944030391010700d22010304540c402081303440b20742c0020205120380351005031450400e2400700d00400302541503444000d054000100000e085d00d0300080058500c2c1d10a410900001e039480e40d8040d21003200c0d150010180d0070440d58040000c200c0d1000442c211000505292802140d4a03404070071001c0c080e602e090409042d50660480d1348941c2503002502c45100100010a88000f0b80307803602e03920350f00c21010313141e584c0d01444 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 238787814 1250 238786564 238786589
    0x304050a020117010614090301090206070b0103030305010902120a0515030d050d20030c07080705070308041809020f12150106020a1b030507050f2d0a09090c0504050907080a030315 79
    0x30700740c1c02498550b1034548150303031b01d91203021400000f0702501030054000c0d0488408075140d82040303104048581600d1203038030103001c242e0302c509040b0104e014802001c0800008140890002c400640c0595000003290500c1e0305101d200700c1c003027454100c5a004541c000345001035211078003510740c485c0c0000202c40302e06403000707005620300c07099441c003010300041041d04c030020305403040140880c11140480e034020280c520349940c81c10148500e03002842094038242d1410226540e482607445002c00040d4002e210b400382212840500c5003c0c244620b95050324495144c0781e07036a119030641064000c200035801070501500e00c2c41c01c1d00301c50344104d29202080590040620000c0c901203011003e0742c006a620a6038000c0c0d14000405039480021080b101c80c01200c00c40910f06e402c0d0001e940b07040000e8400040c41ca40d2007080e54201c4070054030281c00c12402c0e4a0510643c40c05401c12904641c000085a041540f0b901059081141d0b02d0340031000b00e542c07500c035000382c1c0f2144001034008105d144c0424 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 238789064 1250 238787814 238787819
    0x307030c080f01060f020a05010e0a11010e0109090b0a0503030c06070306080601030b060105030c04051905100207061d0109031401050403020616050d0b01120903091d060d0f02150304050a02011701 86
    0x900b07205010f01500080c803458010440300c0d58400c0080e00c54140d00b040080c04542d0b03045060b05d40b0340350300d10400c2e144000c0d0b2001130140b03940121b4100111501c1039503000074481c6000020350003811140a240d9101d1841000050384e46e41c1000645003c100020140c105ca08010709c014044a60b02d601091454001c00700400c04140c90440700c6501150030700f410790340c0344e071903040b5581c007071081c1c3d009540d000400140300e4242e040300d4154041075810660310805142c90b4150142d1b91501c00b44034250020340700480803026905107884800c15000c041c181046000d4580c0c0d070b00c015015251602e40040c0c0e5540040105040c0d0401400f40c10441f0f01040e4621400d94060040c030612441d8031403040b4580321402c2c00b22992044040a1340461aa1000c04c00640c0501c0d000340300034954855452150030207a49240c1000b04103050900900004041020b0b80c161599003208540d124101079038010418041301d4412014030000710300c603074425006007100e208140300252100c0f21030140c0600e07013070000006 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 238790314 1250 238789064 238789081
    0x60609150907120b1c06050a0608030711030304090204030b0f0121030e18090a1103030325030207080721020607020327191703090603040f031b05030307030c08 70
    0x540d40c12990601e0240f00203041e6000707040252860092490b00075071001c1a00d203074510700d050809215449a10148016240c3c183da21080e54168040e406843c0c0040000c1000540540d00c600c1c01c10310007405880c24241d076034031034404903013103a401aa002d0380204104680c1050140005000d40004c50248181504041d41882d20036235040e401028054503200002e280e07034030600d100316407000003181801c061501c0f41c845071700c0b122843c0080b02e200d100344c21021600c0c9404000c0d42d00c00c031a180d0050a00c41c9104100354441c14a82c82d03030009060303080229101048031580100b04030703406420f00303d03402214240e88a1003046941d00a0085403c003505004002d0f902104695a00e400d012040c00e0614240c4034a0070007c2041d042e256119508a2200383d103026180e4400044031200241c554800c0300612480d0b890384200039000394052000c10014000038010300901c1c80e054024a03102e00c2c0c01c80c016203515035600303030b10030281c4442d4008010803441903030500400310400c4003480e00d515117003000d160 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 238791564 1250 238790314 238790329
    0x30d02030c0d110115090c030b011e080415150e060321030c09040f060e0f09070603110919030b0c120105060d09020a0306140a0204080303070f2006060915 68
    0x69040030807180e12903d44180109410038250b440d0b000304480300e295501d20084d00100b03011a00706002c603007000e203203003801d6019500681c400e40a480f0050344c60340e8890380132510300d20000c0040300c2106610742c4036141942c8500c98101d511b003001d2156450b140c20005410640134000b00098403e91240c0e1200380c032181c45205200f0100980d030f840703c1e12900c80e500a15a1030080c10f00d0682c100d464040381120481640d00554202c900843c42c00000352240104d0031701001e0204d0310880d20380d10602041260ba8403941c460070150841d44400c50801c00080c00088601d15003000180041d403507041b092050003500d600150300310801002062030090000e4040840d0741c01407003581c0c4610f0001c00c0400140c43c2c240c002c4400554014075000d806512440e050000b00110102c10322582d00b5480000c0c0307441840c1c8211380590b11030a004506590742c068080754120038810703101c01017001c03d0004400e4102c82e16040c9905034580d50280803940307441400c6c007a1301d00d0300400b08410000c0c0c0c03050f1200c80c1d455890 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 238792814 1250 238791564 238791583
    0x1a03010501050d09083c0720030a0206160501060905070c171e07030801140d060c0e040501090b090a0b0d0b1f030c090c17070c02010909021602030d02030c 68
    0x31404a100649400d0029160240c0c20000014110050810a020304001030b005400404480d004072200001c40c000c14090243e028000d060302035402454505030915023403c0c0000f400142200d1102c5000e40c042442504558050f01401c0c909800e5581009428001c5002400100f10204450700d0441c4e0010800d2000341c00192001c0040071114132910030550448154199068108000001100c400e030810b50000c0c00c1540007034420000440d4580c1103201501304c60000400e8511007000e10f4807020024012048120140300090406c03608a0325603009180c000c06800e4400a48107108405008801c0d03c01426645c0180c40c100d4071340c5980c3e80d030b07215020105801681d980d0b600e039180c4401b40c00000301e01d1800080b5401c5140000304000c00c00e00c0b0744003030303800040090128619142050b2020074100360091224081540058582480340c17854000c001d005240149507140d881c409101241c1c011034510180501c11071050b0306500b410010214812130600c000c600e0310080043c00c079114003441 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 238794064 1250 238792814 238792837
    0x10f0e1005040806010602070509131106090d0b04030201050a180503040e0c0f040e0109180c0611010906050a09170a08060d060e061f090c020c100201090f0506011a0301050105 77
    0x11050440a01c914282c1c0c000d840742d24100c40c1203503140d44000c2d580d042c140c41058031414002c0d0000345003500724600018120b5000f00442d10200c0d604040102e985c000300162a0818010407030700010480c0310201074003441c040d400005141c144035400d81c00b5034a500b4044180a102c6540c2e00c1c0000c2c0c0300100700c400325461803906504c02d40745c0105502051044100b03030a0390000c045004107400e29409002412122090400c1040e2605401005109421840302800d40600901e080010502071404000c100150600018524616583e810200c8209840215026a41e92601020000400303041206a51050703660f600301010b00341d00802404005120307071300071030309c0842c00d100b0410340d1380090f2140008002524030514003096003c0300090548400d090a10008a00007090101031048000554040d80a0010708100b00184264000d0b40c0401200b1503503100d0303159021510024245000c14400d01c0900020351600d10b1400d015003a003d0040c641000401c010420b40e0f070400708070382620601 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 238795314 1250 238794064 238794079
    0x30b27040204020a09030b010308030108070905090a0615050607061422120c0204090501020310050609060702090c040506040608010303020f03041d040c2114011404140109080f0a030b010f0e 83
    0x2138110448103500542d100410410902001004110505015505031030000044440c010b50b180010340654030143c2d088102c0c2e0b040b41c0880c80210324a90800703045200420002c4561b41e0791040491520383c00b80209890030756460141c9071440121200b0160412030721250555200c201079138a690f0440107000090104110100c1815014001d8180c0180300750014010030803a041418601e000c2c2d481214107041d04040408081401d103400025594040c101030306440c103241c0c1030303130038002601c001030600522240140800145e0741d49400050000c1c10169507100b100d94950321b40039103006040403c1e4801500103000a019600e082c039401907119040c442c0f025a2500c0703500f03201b41c0800c5039030441d40585098070f0b410700304010540681000c1522481180d0114914420901e089030001440d0821540b0030720b02140104801840501040071000c0001510214075511804180d20038100e1060021010500b100065010701c69044449001c0c201a08841012000245086058604a44150310 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 238796564 1250 238795314 238795327
    0xf06111b090709030605040b060126070f05040909060b090c090d06090305090a170d0804050c010c022b0c0b030f01090e010e01051306150b03010b091c03030b2704020402 74
    0x80f60300001c0041d50050300030407907410325050103155408112a00c1d030100b45000e0000c42c081c26515825981c8941041400b059a05c030b02000302c407910070181c0ca1404101c8180030103d461090752062007a042e21614000400f0400101402411a8000d1001c040301c00c0600012403940c0b5103030341da00b1710a80e104400003401c206c0c40c502a1054055540c085030013111041c00451a0041c48850819111310b2000710752515100d010f007240d210303100301c60041040c4c00c1000407000c1d079405040c90720081440145580018880055000308064103880340d124000000f42c106014004c00b5030310a00580140424180785240c90300948060321410720034071118550b6801900190036081d803000010800d584001e00c4241008101903100c2402020251621803508006820900550365070300119480d24401c681180e01cac058204142d6081042c0c13039a0001e111f000e84242e184080c008400047d8440c3d01d000810666000900000a40f410303d415005402c2031b8081001c0700309021501d07441581190056034501 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 238797814 1250 238796564 238796567
    0xc030709060503061809060a0b030a020109051002071206050f1501080708060a0503120304060c0905010903030e0102150f1b0a020304030f061424010807050306090a0e03040f06111b0907 81
    0x144c5850381100c5d103046060034407501d0100410128040d0041100910441c004a070405172039840445c8000d0206621a0081200381081c0004102843c0507005840c041583c4114017100043c1d004011103806640c3e50400811541070082250408420b003050110240f020001a00030380700074040f08140001000003d0f0659990180071010b000c02905071003080c4c640041c02030083d0000d881c102d40c040e0408840224917403044c8140c004690050b50b405001518546041e1501404906000e04600030480364040c0f1241036450a40610140301d006403162810502d6901d41c022242031009002008108840d000ca0307000040d20160303500b044544001c0c0c21186480401001c0d09080e400002100004200c1d2480c1003180001e6452000000c0360318407007a44004440b00041190b020000c02c0c011310202e840c83c00d00105030791b8000b0388102c00041001500c4800380c07443d00241d000512480e203541061082c243c9c40703080038421101140c010484040d0b03008841031121800100e440c0200c2941001403042c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 238799064 1250 238797814 238797829
    0x50f07171207050403050622033614040e03071509020901121101020601031104020a0203040e0103050106030b0f011d040501020d14010501091d0a0b06040b13050f1c02010806030c19030b0c03070906050306 89
    0x51490890102b1400c07000c0c8090204107501c80c2c4030382c0d40a120311035841d909141c042c60454890f000040c6141c5445030750341903c000d4854003520300c2141e0f2540014016210054180d028011030855000c40c810b00e032030f016008510b1082d203141150031000c01000051200344004101d00780844002da10750612004c124a103000b82c0e40000c01e8032820310000001c0c817806600c0316003501e01601c114503ca80c0c0c0d01c41412402d4400380f0824010211611500d80c5840840071043e070040e1190001518068980e080c08050340c902c1001a82c913030f03406a004004940c1c000709071600412861941d008000906210404ca409004203070680c8136481c0c00c0d6032501c40c1e03036000849000d4079221030083e0315003c1200c0050320001c1540070300c2d03024900c01c2940d130b100b030318010f00054024115a6041c14506181d90b00454549030094696509807160907107031401a900c2084e8280000711800d4400101480c60030101c00e04003001e022139420b40c0c410800d114800c1d40c071001040c2070305d9407410b00c00d40d29140c020210318503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 238800314 1250 238799064 238799117
    0x11060904021b0c0d080901050a090801020a020601080c030c010806060d0e0712020109060503061c05100f090b060a030203060f190c03021801050f0717120705040305062203 75
    0x300703100046020404882412288000301100115600e40144105000a100200c0c2010302401414441c810007980710b04020010480d8034502200d0031640c9005050998002410010250308480010301040d2003c02071070507131078800c0780102400a14400080c00c810b1019010a0090f100056408891681c0e41c002c0f001580d0074004072254580d4401e02c80100e064240c00490016140b0900004c00030f01c1001a01e003e660002c0c18100780000490b00b020003a01d250070222894018070340c40703a030072900302d00c25078880300b901040100360601546010085090001c0201d1703c554021441440035071400a56a6803054403850a072049864640417001035500e62410b005d0b183e814010454101903050300500110260788904072070801c5500015511030040c00d03680b13402c0800a020000105200c5000481040172801410780b40480707454030555030752800c0b545180802c20024003001040020070409034031224000c00d2813140360b90491120811500544c1c06820401c131440e00e501503030070410030002d8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 238801564 1250 238800314 238800319
    0x1c0b061809060417130603021c050703020a140a020703080309010917120a0e190f0c0e2202010c0f050f0d09060210090c0b13090603060b10050c0a110609 67
    0x20903107410041c059072254203c07030484440018255a004948025041d220290545525601503a0903c2c1c001c5009400151100000360b540036206441d8200d14450b41d40245801c4ea0056651012240013404074407443c03640079054001000440c3c0c02c15800705014090700d6101300a951b4130b45070440d100b809002c0c004c00150402240764141d1400d10064002064269500600715034030350b032048008e90494030035086c941c82c41d411001e868241640da4158001c201c512420004825075013607207030a2005405074000248113180b623000d110f15007903106501c1c034440001c022646014020790380000c240442c40d00c402801c0c0c00003041c0100c02c00c0024840100420352920454080c10b240503030007881d01006204a0004d0b018190310071103043d80b070f030280105c216004003602620380d01d0014a50040d80c868981003008244800020410042c0343c09140001c41c000c40300862038505010030030a0040c000c40f40310060000030041103124100105a154141d90440c0003030302e94040301c20101e8082d1054035020750713 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 238802814 1250 238801564 238801609
    0x30f0f0510020a11010c0f1b141608030f070b1509070c020108010f0302010c080705010b06030405030d180f02101e032301050a1e030204061502010b1c0b06 68
    0x103440581e41e001e40742c9105103075100d110004150401a00703c4600e0704103e000030b541c3c28552102180562401003600541c421115201c0c000f0340c403088603510003080f440c03032650821640c15080440d2565070601901042019529100748910409924894600000c2c800185640000c01d170a030b4a144c0741091400103171184502d40340402e8020030081510000300e002c210002d00101309138020f1480704065940c1a11030b0851014181c0319901d49400c1100700f00c0e104e40d21821007480da80ca401e8003850040f4030a80c0207545440710b507810034054819105034520225200100c1030040340b03600f03206046450301580c4134442100058411102d81000700085032101950200c00c030b1030244d040e0301c07102c551410f00040c450307404607101141614050031302c00c0d04d601c82c4e890403040c0540c400c6480445003120301c010b000c40d8403035070380d40c08203059480b25406610788424000c00c5411117902801031a0302c7c0707134003294920724648080d6217182c800a2101e8010300b2100002001515a03201c4800100c580001c801210 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 238804064 1250 238802814 238802833
    0x609090b0709090e0a020603060a050a0b04060210200705010608031602030c030102120c160506040605070e01020703031b0501112b050f0f0402061e09040b0105070507030f0f05 77
    0x140310114095541c200060711001000408031020f11a21583c0c078001800f510700d03100a42c0800480e60000750206522640058001555a450140041c014010503443d244c4481c5440400380c00d110803640d0b126002400d01480c41108104071943c0b03024030400700700098661032103050280c01804260032288052100180200740003088500d86020140300701c0c02c60f005c0304403060030b1600383c4c0a0018241d140340520f40200d040e040103813024081d0303031000d20070103100350260351202d031b240c49000e8400390b84a680c2d503014007c1050f441000c40080305420300040600d41d01d15640109940740300c0407030a9104428002a100b041020341080c244a6116541c0740d4a5520102c103a07002c10301c1101811801d9071031100a81d2001c812400b030940308895500c1d02e14070075600c3d814260000640200700301ea11100800030040c800c0c1e4074107903049034042100f10f89512000c00d0b90910003100c020f98102410b0000522411000070000542801a65400001201401d0340d503d03040c0890120080c00415a02403030001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 238805314 1250 238804064 238804073
    0xa260d0c020c040c020304152d121a0d080309030409110d0b0a18021e27010903020d080c0c1804060c030204030b040f0203190b4303060909 61
    0x1072040910b02100c08005008015800ba6070700c1c400c51051041045420f10300c0d000d898019040100010480c030003124404060100e1801801c01d00010b0801094100001c200c055644c0e2189502c240c000101200c00b5003008070004001741d1005038020030002000000842880040c41643e0040980510902500031285400c1c10241c11110405200c6490440342500c64a002c4010034201c07901c0c681d040c20000c03061283d000207944107850110340c1c1c10851022031040c15000c0000d00d45544002141d00c41010780c503004268004014a419041019040e4140050307a94103101c1c20049502144060b03450341440040c034205500140320640c42164481c1c0400122a8040c156105622861080221640381d00341035040f80074a010140070200e0700000540018500c000111040f8001821074001110380c400029141c488210200c032200c5c00c0c50184052030720320242070310070803441e240f06050003181c0d01500698580c02d4002a030240c1e04e2000020726041c06540503030064000c07040e0500404503e07050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 238806564 1250 238805314 238805323
    0x5010e090a0e161502210d06031203090605070305061008040c0308070c06080105090408040308130308130f0b160221160509090a051c030e160303020f0a260d0c02 71
    0x404143c80c2195613120f85072480864039100d8500c800d5480344010240b843c00070702c0d54001050b1022032603552030001c40450704207501d0b040d226901ea6408101c503282480e242c0151400038101c10107141c00d000c18418141d480e40c1c110072078240d081c5001c540136541c0d402c0c5690a111958000f0300962400543e210902210440c82001e480090319074201503640e0360107221803400219005015003105210910001c1d184000801d040c4603822a0500e006490341c4400c0c031580d100c001100524a40c003602000320b14052003101c0000d01108000c10705080a040036010152803010300288942d07000c040403c000002100345d0451104404222602c0d40ba0300c4400d104400031a01506114440c203400080060000140041610781c1c08405040c00d40080880181003140301c580240c14540c4982c0450b508904c10458685036968182c00000003030f14504000c5d0400602130741c3c02c4441d81010091030080b40b0008403100c2c2c9408000344404104100b070804401c10b008490340044d00a040c1010380074140d60000307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 238807814 1250 238806564 238806569
    0x4060c17181207080c06070302010b09011707090b130c0903060c120b0d020a1502010b0312072d150b0316030201090603020c101d10021c0605010e090a0e16 68
    0x60782c0c0c4a54807001c6070360381d640e18074503c039401003680442d6480d001400c4c004040d0894a01ca80000710301d1141100010784c49203026080151402400d030252503800c0020020310b4010710381c8139410400c4083c1c41c00030440360100e0340d8810754456110070030998042e200310461401150802c0c802c00c00c1c071540d80c900800d02c3c0c3d80c6503440c20095007009001140751030b0502c44405290f600801785150b5910703103180d840d60b20400c0d40d05001995a240442c0515450070701c40c90015109030540035980701101c0c03a142c1c1d0b1903102c211200b5105482005d03c0c0d8202c46408646801c01504050407031021051100400003502c1950000c5402d400b03111100031211f00d03500e1514003580d01c00d0701d40360350705516000c4c218224003c0518204c15684115091070132035080d90b00c9015603285450071842c450400c25140b44c0743c145490a200650796000685d030101121900c9801c141100c0e440d8140f000b1481c140000b01500c0034229014031030a01d01000c21013104080d401001185020000e40d00c0180c035040c003014842d2800e1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 238809064 1250 238807814 238807819
    0x207021807111005010b0304060b0103110c070905011a041202210d02011103070c1709040504080a020105090114160903060e031c050105031e1f0b0315060604060c1718 73
    0x41c0c0f041c81007010303000382410b0310004615541142c0d150f88800c40a4039034400c500341031566611100c0c0c00c81660740e004242500540c8024519140b61880120403244164031140a8545440c088401015003c01f2207044a031240881c101c114192b000083e90401c840b925845288000c0300e481e02c2c04007010904046070303e0550002c01c00344521006c4401c50784002c0f80c0e03110016000d50300c010f0000d480c2442c80300c0303526034072148a070900c944034020500f251011365090324044804a18407011581c24080e207131340403800400910607034200752205103001502a00424041e060581000c8003984180d1911008541018050000000000400c0d48a9104010008000c0c00c415083d038903258160244c181280c50241c01016800a0350002401c1110755018410050103a60314441c14241c40058500b20852200c0300013552092480406240005040c5482c406800f20700421031036a0361a0280c50894034207051070005184907160000d140040c0711001c0f0a0310070041081c0c0260383d000f02c86c046080409 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 238810314 1250 238809064 238809073
    0xa031e06030213111606020301080706020a050327130e0d1806030b060c0d170f0f010504020a020c0603040b07080c03040f030f03140f06210a0204020702180711 70
    0x58208910694150707010180d008034080e15000550310080e8000c4030310b04000000e00b41014400d00585070208880c1c40c0543e0b00980220051215950909c2000700401c0c85000610030601e50307903501502c900400c10b030740354015940f600181944069291108203000000c211810101c18084108000c5c4400c0640070050311420601351910350085064604040e21034401c0c0350410b02c1e100301140900b03000c0000c20b40110081c014407612181c2085003610308800c64559400c0ca0031001c0c0e0000f03001000818004111200310140a502084514802e0543e00280c4003d6134a2100503070a0789060300414020343c00030800810401440706000320240602c58554510010782c4822a0f8940b9500041d14049c0c1800f02142d000c0002070302642c146d94000d400c1d0b040c01f00c1d038104038410905050300c040350308458618003c0100400c0344bc19020118000840100c451444410942825520482d20740300a002d10b6000401000b0740d074400022071130110800c01f1842e85840d1020703000b400880d91255a10840c402e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 238811564 1250 238810314 238810361
    0x80309060103120e010207170703170a120b010c0b091207050c130e120304060b061902010b10020706081e10090b010503010e0a0513080c032205030a03110f030a03 71
    0x4608000000604c0590060011310b04011b040716101411040f030300001d2103108400000600140c0311040540e0203c00e095840e40070700700d400303065040c0e07002034035101c90315006a04003643c0c3c01105944240f6080203100340d00f55503440100d0300d042c40d800e10308030380c0d0740001c25114200300c000201003000103010344420321100c0401c5900b400342e8007010b4011503507400030290000082c0403a00610380c818010b10000c02c0744000c45010510030303800000c0e07240385000700e40900120b241d02400745024196041c1c038441c020044006000f91101d406000d49000c02000402040104202c5800d002d48001c05006004040c2010200da803d0954948154000783c0d0403e003c035051580100140d904071a080c188481d41e40c0d43c1c040491004000050140b200494540c1c9004041210100034203402100c04009650700c0000484100c4c1c80b82c02d400740921040d40c003a00501990300c2c01301744500e405034142071450204e00401030080c00c3c1641072040761b07058800031840540c41a81604803107a400c0116500855040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 238812814 1250 238811564 238811567
    0x11403040201141c11071a09030d090b0a050f15010c020102010f06260307150c05120106050307030f0605030703111f02030915090f0f040f02040f0305160e1f0308030906010312 77
    0x65110180c01048044618821444060000c6034090308071000c5d0b2b864030018a003800c040f190102020360703204600302d003046841601131060b0394203c1d682c000b0003403032440c0804040304452903043d41d060400141c03e0030141103900175000540411009101400f000d03484020803c044692880c0a00c50300380d2402a2010041c00403003250419074120010451074155044100b0181680107031180c20048208280008610a080f01c14041d021540c0c41d0745e501d0400140003010b580811740d040400c00e00d4150100500d942c009508011640c0c010403194081d030b8a40000707507181400c02030903c0a0420312121103040ea07408401000d141e4812928826401c61300f424400c1079004890241e078104810254052840c85c0400d107611107c0002000491880100c2421005a80050380105506045220140100003007400100241da0f44240d1008800c0d281c0302c001c0100b5030b00500340d62032180c00c1610300c0440042e4001c028000c0c54000300f0440e03503420b12188003a40d030340f001d10080c0c0307141060308070307590f4444d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 238814064 1250 238812814 238812817
    0x20a0e1005090f010c080a0201050a1a0132030702060f0709050d0318081006090606020d080414010603020d0b0601020c010f09260109030504030309050103020306011403040201141c11 80
    0x8405a440034107100b800d03018452102042c8400038103206907035403414001120f100052604040c954004a041d080441a00050741c0d0001c00310001207142003802001030b607015040303003a208024821000340e0100049021040c0b00b840803140e010305e00000c1080591b580001d8503d00030b4031180000d8495649034201224901d25602032254860110b10200d80481d100d4803407090700c05604c412254103c0c0d5220300761490400d04084480719562030300400c0054880718481c0d00010445c80c0054504900d402c0c00040c0b00c280001c10003040d00201c02c00380441c1034401d6000c00c01959010344a43d1000320701c1d040003140d24a08866041c010f12407076949020355440f5031032880034104c6644500c82080d0410b101240a140c0041e894800f04010790b0f81418100720902440c20010300a880d2a0380d03450460a0050210605030401d605044c01001404442d90f0300450101e84401805189a101e41b200d03c012100300d603003107502c214907070004908162a00745c508842c1c40d07140c07844e50b001c0003104140180e01e00c0a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 238815314 1250 238814064 238814089
    0xc06010e0c030103150b030115030b060607080412050c030102041409090109020303030105120c0406120c060504050f04091406010f23060a110f030a02060f090604021e03070b0d020a0e 80
    0x550500b8001000002d404c07081000800c40e02400200307241c0900d9005c87d003140c0170404481030003500700404005000c44c20b50745a8018105440380e40c9081d1150315020070510581c0705030040110100007940900c042071000c00304408000b03000390f589076a141914803c0c482c2c11401648182840d201149210704144200054a0f602a01844c116840e04042101d0010700710a4202e00f0301030842c8503a00b41d0f50f28492030000d0302a001c3c04141c540c00909000c6101c2141d50030141c14001308200600c1981c0e502a1004d02c00141160080340700001e034a4049624541c8034070103011881914008201083c8100d044410743e02400c001110b40500d040da003691410004880e1504140704001c03920219200d404582582c03010407088503403601998941a1450b440140d020005820910611070a40c20054134160000e46d81401090b550505400240e05441407000c0c100360700301c4c82c81d00c140c00f030b8030240400c400508190b4a447d4032900c070500840040e6000f0041000040d0340c141d9440f0345440c00079040402c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 238816564 1250 238815314 238815331
    0x5030a110703090513140109050f06010c1e03050d150305010f02120408220311031509150709081f05070504030804270e0c010201050921030604020c01060b0c06010e 72
    0xc0040c1380c50180081c981c05070140300a4182c9648501c0b0000010041940c002c1041e22030001e050f140a492014032144d0142a0a040181600e44007000c82c20321b440f0b0309010381e004800b0140b103418615085e60305200b84609111303614180030305104c62001a482110459000d038000740402428244000c04038480d20000b107240d80000e5001c01c020030701c0400540009c1d8401d00341d100400ba07012800c0c44100141e6401200d00344107504502c001c908060007204c0300b403c8d40f56160740e80340c103245c2c40341034544804c4054000c080302c0c00303000121590712820320000109036410607140000f00e01440d4185400200300a500f80c1801d010101e103456100300100e070116500101d0440c18181000c41e9002a0059400100d4a50f49111000c2c0501217041c0b040480420720500206060403d40001900703646000317009689a40051180c4030120110340e00c2e04444985994269540f541c0d60340015000340144900c1c0d00b095840c203500170031640d1042c1e0003821500083d41c101c034030340ea9070740400320003406c0122030062 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 238817814 1250 238816564 238816577
    0x607050f03060a03080c061801090305030705090a05120a060e03090906100509040c0509040b0f0f010c051905030406021216060203070c1b0f05090f0f090307050d05030a110703 77
    0x1110305480050740d0400c200400140c1c0340c42c1d5a4441480300d0704443d4012016801c01401c1c0b100d42218000903034000c6a11000a000848413a02d0240c41404001c01e11824000c0000700c0c280d803130350b594000c6000351070001c1c483c3c1241181701c0c841b60713510702058104607100391812050310004078001017500c007160030003030460078599038500c203000c1180003036a40380702840800e100844a039502c50050a110700701d42d40d10941c4030001c000420040e00e48414100c0d02035803296200300b40e15103901e11281b410032400e0a08a007909040d01c0c1c414500668294182000fa503103170100740c20401d01100038002c503586a42101e0005000c440d0b480c40c01c0c401e1107071506000e00500400310001e0025005980c2c0002281404080e0300c519440e0710f020b4032a8030301c2500484c103a00d0818040152082b1780c9001900058404403210315003200c02e01c00111019180003450b403030708000201001d1040040f140c0096000e810349a091411400260450304251340f01c0c013100d410855045603540f00e0505031040503801d6034804 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 238819064 1250 238817814 238817827
    0x8100902091b0408030f07020a050d0b06091801181a0c0306090403030b0603070906020d180b09040e030a0503100501081e0703061203120c14033c0414060705 69
    0x80300701c65410800b030041c5840c02e001c0010301000c00e101610411000841d0190341c0c0c2424810041d0020680e00306522800002c280a004207014074411a8000002e0351002040d0300c4079230051960790a00d49003050103600301401c00318030541f541c01c0c40340701c10b106050600c0e1b01450540d03500c140140850300c1031414441400011041d103030856106030058000c0c100014624643d6002c10801da1086a4a50201d981d81200308155503040000500104841c03800d0f12014076452007403449480c00c0d1003508910300300840c030307180195201c1d40030600c04410f04003225a030348103030a005007a5030400c44402076040c2000000140e0381d40981001c511a01004042d440c40902640b0340310000c000203481d00702003640c0d038000031440981c283d00c9076051500039202c0c10480c07003400c40403c080c1c4071a0350240e4100500c0401221100400d00181c9400404e0050b10044583c0030300501111444031180e0a9041e1003250311006060454215050189004401c440c5001140306011944c40d40255848800103d080144 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 238820314 1250 238819064 238819081
    0x30304080a170f1b0405010504051e061303060b180c0315060c01060e0c090a03081804060f0302120a050303011505130305010b090714340305040810090209 68
    0x78284101541411005806040c04003440b6020840320862641203040034061002a410400e01c01120f50300c0c0c1d602d00c1d20742440c0c0002d2090280b81704031400b6500c0f654050201d008064840403120001a02051311016076082d0000360110300d2005036480fa00c0c00804100e2410140203034001511000c00d05c1c0416100c01c01400c4031540010f000038624094001e1002c00c1c4d07034503500100a00c02d07449002007a2a4100581c00c0741707051001d000e42c20f518030f041140307030070640702d20f0f90781e808480c0c0003c3c00c00d4944144540c8200301401c004612507109140000c0420205140314040302940d0080c3d803400881d941c0b05176296551010441c0190080c2e200340b004018840301048200184481803800d80e0520603824407401e080110707500222816516140b00528034240410388590040c418646100d250100144007030b140e00c50100ca840d00d20341081071500c40b09110500c00382050404084142040c200c5043c02492600140500c81c814000c441e548212090640100300303003540c00408030f0000d5100e0440c1f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 238821564 1250 238820314 238820317
    0xb0906030405030717190c050d140c01020d0f060902031506090d050f100c0807120f180b0a1d030f09040b10032a021921030b040501051203030408 64
    0x101ca0b00e110402c004400100000c1c48090400c022203142600e4042c10304000c20042c00d0615000100588103640302c022800005d0141111519030920110f04001134180030003034400c20041348200d6000040c002d80002e01075000070048034108200704502c0d41c80c1c4040c00103a100541e52062000442403442c41503240200c0100b000a00082280710324164699031a420034038191000c1545070171000c128483e12000e80226000d0b80034501c0c0c26a05031030303e01c2d8003624006c1300c80c0e00d1622035a0b0f60f80b4046421101c50380500300360002d1500e81c5400140354640300d6609201160441049414882840f1072107140510240c0c0d6000941d010310300704861030540e201d0680050b4807030396005e5100d00c220201c6440d50041d0003888a4507507404650203d24080c1d000b400e40c0081c144c2c10b1010b0300342070602d5186501040807440300100c1c640c2d801c9000681d040c940302d48200c14203841000030000c0c0b001c41c001c58142e40714160b8498182c0c0c0510107a0b03640c0f41040300071611100c8250942e0001c10014000411490 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 238822814 1250 238821564 238821571
    0x3020118051e040f0606030603060605010203090d030810030807060903020c030c10030f140c04032108060d05070906170111040605161506060806040b0301060305070b131e031205040b090603 83
    0xf040002d415007215650350070345510307900c07050103c0da0391401401030101501502c0041c107420300086203400302420125000c04070090010301041480c030045070a031115480008000c54000c0d21980d100e44984c00c18000401071001c003100540308600f004002400e0100c7d0b00107a803000144804562580128150054550712407600d10301c983c2c400958400010308822240140d41d0807030900d0700d881c05d5281c0445c0300903055041c00b84940401024800310350b80149226440134090b141407548088619196151402d07076040540c0007030412002180c0c050385c5100f0008202c00d1a0000d000c1a03106440402091046001e000700081040003140c0c03441550480100740140300303242c10b05002080b00050400c90702c0780d40124000070b80b11814012241313082c0c05404c0c2040000c400070002640382d03a5507540e8032081482041c43d18100072501c10107075001c0c1000403009005a098200141c001200341d91000801c2e030104540a10100000c00c02039032152042e103003541c0c1d520000b0b034070b40345414003000030541005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 238824064 1250 238822814 238822819
    0xf06010b0c010e1603030f050306090a0216020409060e0d050c0307140709060b0304060b010e030d030b0d0f050606090c120114040e0d0918021204021c0203070b0403020118051e 77
    0x35194100d003403200700031324000070028060103000e2078214038004005500742e0020504104d403d000b445025030310410701e140c1042030810f0040c1d40d0403a00303504502d0441300c600003a500500d00040d0009019003a0882001845200b060f00c420710105403054030207005100614031280d00902036580000d00c07540c0b00a0000c8498030071103c4441c2c1c2e4040312070070360343e0540102d040c4103404070611082210a015610803014242401e603071002c043d102080d52940703d05000000c05856952038001e0752102a10203c44580112411110304800e090841d45c1d032101751405409032000900050301c60110606482c0401c0c000441d071a216480c1c000310101c0e0445819030554400d5454030040014101040321000802580d11500225854400400301e08543c1f540540b580c80c0c0100445c140a0340007170705540c0e011b681160040420f41c00600e41000e14103d00e04025010b00c03c900d400302d01540c400010b441228401d0360b0340c1000da0400c100c2501d044d200341c41899000745c80e003c800382801106c10703406584003501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 238825314 1250 238824064 238824071
    0x602030a09120906020106091a0904030e04020f09030601050616062c060f0702010e2a0301020f0d050702010903170703110d0c1106040803130f0507260f06010b0c01 72
    0x281c46449502c40800d8000010a85096040040781c0d0203005620003440d00c81030401086100581d03024000d000550702c14800e03d90f1200080400d40100c000c002100000740c0308545810710103050140c0c030b40c44031094510070b02c114800002c00780307840401c5801381481005102c1500c40c09070340d103030060425948000c20607a1030100600f00c001803006100400390803200100f00600b4640d24241c0341c080301410307000840e41440c3c002c900b6094002504000042d440740e580300805e05202c007001c510764039400c41591550002070000d0f04404000081d003a0720a13030074030410250712801c505900301d980001d07004000c40c01401c3e00d4007640501e8108194409010700303010031100301c80d03681c409441c0e01c141c0c0c9003510f00d036450701c0c02d54020364460103805500000d40010714481c109600c6d003600c113000003450251846e0349001d40760104030141c10b0030a6815403042c100e481e070580b14941d0503038a01072144820304918004007031059164000850b20500c0c2c000d0400303054a84d08040e0310040316070012003000225900c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 238826564 1250 238825314 238825331
    0x108060106140a020c0904060c200d0e150c0601060207060e090705031e0a1a010212030c131503091104091a0a0603020307150206090609030301060e04060801020a1706010207080a0602030a 82
    0x680703e8100f485030307215032800600e0040309e038409000a880b03183c1900e07540e1020212103d0705100010070560003201810012480302801c000074140010781c45000346142c2c0c0208414000010005200341a1603036a02910130711034403890115a030042da42221a40901c2840119106038015401180c05c50418030783c1c070342c490540e031600c2038505c0800c0d45c2800005c0d40c0c504007041b02c51701041d003441020b072007480501041d50240c045d10406010141c07294480381c400040050782c09022400e41001086001424031640c800139201400030540880d0641d194225a0303c2d5001ca850300b44200080254096905100400842c00400c0d1481000307041c64040c0d0342d20380c404805a5000c01c406001440781600702002c010010700c2c02400c10320302800005865103c01e041c09007141011041d24103507800c62915500403d54100010050551039200d0046540b00146014600c0d52000c00e044807400801c00111040d20360600490f503882080c82008259000325554800160040d0011604110041d03008528000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 238827814 1250 238826564 238826569
    0x9020a0903080c0a03031a030a060b0a0503060f01090c050c19060f0609020304050c0a0f0b03071e030c020c010905030d050d090203010e0307110f0f040c03110f040504050108060106140a020c 83
    0x1403089406100f60340c402560310b010940c1c07500440c00746d142c6e44004d025545040002003640c034030051100410b01c94842910803103d40f5604000d000418005044804500b007401c003600b0400000e00981c00154184004694010300803001c84034030909403030084c00114500b48400e45440007200040b01e0303954a403483c0d00d58512003030060700302501d8420001a582d086c01c0c64410b03e8a01903101e5903020b4021010300b00417a00e00d4083d2541103031103800d0794a64940e1516012a00492000e0540c01fa070b0403100d803610700040d41544151800c5400d0b4081320055082000150780c0e04d00c2078840c4581c140c0c800341c0f90701d20017403203240640242c1d003c0031b10220703201c18030b640040d00703460500c02240c500f0307840880e40c101400700d000700030090000c007907401901e00100390011a9035513600e0f007042405523888000d6440308502c25444840c90414009002d03032141d1070044e210440fa881482402d105a00786000401c1068000c40c01e00c1c100c614036107030f29410340d1810217030010a800c152030b10f2055014442e200c44654 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 238829064 1250 238827814 238827817
    0x70f03030813061b1701031110051201030c0302010f09141912050c090f010e071b0c0b04060306090203060d030e0112051e01140907030b121002030103060c0c080409020a090308 77
    0x4180c1010300d07541c81d013074084000c0100300f415510310b014031a6280100003007030b04d400b002481c0800580b04660f14884541d003e46161048040c00c030008010000008280002e42c07003040c0550340700340d8652540032a9040e048a00708001d025241e80b102c6c4aa281c0c0d6080c2c0b401044182d03800070304000082c0440d6a034a81e03401003108060041c0c0320ba8002c081c0b4140c0c84d141182107030750b004008041184255041211900d94014018600400d002010b802c0009100800c070071420340c00e0b0b1080461981c0703912613205407429040707440b83e82c1c0424107000e8046000a01802a41e2180701e0103400860701c02840d840498401000d484d80a0511030380b4011024100c455002d10f900c076405c40a0b031603441101040c0a503882c2c100591191392440c2c03054882111a81d601c16100f50032418614000c2060415000004ca030280c0300c0c0e02500f801c0c0314580003900190382d5900518104c90045d8020000070840c003806440500400308000c14200c02004184074018a50b809843d44942504e440d810060702e0760303a5032102c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 238830314 1250 238829064 238829081
    0x60906190b0a030e071208070c0905130b16170604020f0d150501030e1b060f07050a050c03010c14070303021201170610140405040501022107020708070f0303081306 72
    0x100040024020b00070b40e01401a0032800504000078244c062428100001e40001600000c003008800034104d018054192009000f81031044410040d90034070300d030344901500f15000304845030440b90b07000802041110641c82174050751511408002c059096212501d0b034401441c075603000d6421300891a44a000030041c140c0b44060140000d682031000e960440da400540e442141014108001520741500100700e00881591041c0c0d030440d441c41500c002410750041c2075160140b030401150704811b028000512050760340c018816526080504000d2500382c4280145e41004500c1d8a1206008002c0c0d200c01030103d40e0207440c0050a184201c5550b1720310107800e03844040301c24181d8480c007162082c10300c107031394101c242a039006621505c0d000704841c810004c06651417080381e40c0e000144c2070005c01e4044400f203411012a038030102e801c0382121201c100b019541c4c230b80180300f420303c04154500c001038500255098109400b818910b1507404840c00300c00101441c0045c224500081e0000d8106d001d55410b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 238831564 1250 238830314 238830329
    0x91406090d090801060b0d0507020a060f14010b1315020a0f03091716090f0e0111130602121603030b090103150e06060a17160e060103050906040b06090619 68
    0x2084994250041142d2410341001c0210b07403400384200301ca1505803049a08021030000c0128040e5180541a404c0100b8844090f00705810320341c1c2a0030940055200280484451483d10b03030070703601c89807800a140106e0000c01f01e032000c080c40502800720b02c0000349400d080244120b032000c0000b9a144c184400c0482c13421400f0404545040c03100544a40409080c0704400c0d00402e01050b001c121320107a01940e12480d400650781e12100e5804040c81c4d0406d4000f4040400240f01440411003080e00d02c0e40f040c2c401810043d410300d00844d64a02c0495043d1460032061001c6090071002c441901031540381c003104500303040ea15000300d400e5440ba10341040c000c40c000d14440d030603490b60030484819102000303420405034010404000c01036032806907901c00e40707503041c40826511114403801449c00703920303810780003500ca480080003c46202c070303d81d5103204010aaa0074000c40d01c0b0480d0060791401c0654004003544803640c006038190810300700850348803030000c0104611520094596480c400c01d50000308 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 238832814 1250 238831564 238831573
    0xc09060c01020c0303061f080103140a06021b011103040f0602030c0c060411040608010b06040e18031803070b0f0318120f030a11130306020d06050604060c0b0a060f0302010309140609 80
    0x901407501f4030b459681401c119500300180c65031460000d080c5e040c1400001e02044406a1590f4030030410030501c00b949a025104666908040e101ca101c666207048041d111503090000559445d8040803da90280b030340304105c0c00c030074501036441d60041d410041080683c0402840400c0c10f0000030800c6c18092800b54222541900c1c448040c8800d07100e0540103840035a0609000c5030864444400706e07000c89600f01d200810300e450b031038980c5031001514400c0940030310000c2007100198121210b414800c4400314203d23190541c1e21100a11680070345284c424150f08280005408001000c0c2c1100070001080d00340d40c5221907d250f07819040e044241a2072404001000b00014580c0c1480382c0c1c189000c5c689240d6083c00c03070b4120406c030364000758000100615008101a031090b060b075002503024040041515413225169070380200307816201c40007610340025020100342074030241d00c103110984490a0010a8a9083d500103401400c088981110500030313034608136940b01c0d024040f243c01a00c0100180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 238834064 1250 238832814 238832821
    0x10228020a150f050c0c0a0608010905160c0222060f180e031c06051f0f110d0509061204050c0a061409102106090c0306030b0c09060c01020c0303 64
    0x480c440c806604003007038900395903144890035070308000b180c14050783c02d140c0300c0c1e51116a80700c064240280458040c3e044a074080d000304840e03400c00d202038183c0341902001c0119640d088245000d0515110340000403807003004940d00903042807072191100c8540030f86100d010481d042000c03070844489034818800036060700700921840d58080c41c040042c1c41c0c000310038456404136015150708c80c46008824081c131001d00009000501098100d04010b290052482014000402d4000302200015200c4000200b03428410000d581c001c0ea90780300e504494000512010711221030070303031325684105000caa1058003800a030150f003044100140c480d610540103011100003034400d000c2a171069410020034002c8540c1911844d403000c2080ea80940000c903491803114060141c00e99500890712588003041d500c2902c0120100d04a400000403544105810051600080c40c1103044520320300000b400b0168901c0860725000d0208041d00c108080104043d1a18050300615400c9a100500d80c844541010041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 238835314 1250 238834064 238834069
    0x1501170703240510030e0703060e030304150e060f091002300112150e03070303050f010b090108010902030705041d0103061404050a02040e0309062701090612020901022802 75
    0x21201184440490740c2980da00f001c00145800040140c86030416581e00b8124094100c1000000300440e00034004014244445104c25125803007114141c800d40b0000206103640400d41c0b007001402c0806034040e01070b0707889120b10701c2c5601c02e015003010040d12500600a24103841c0e44001c0490440142180464a60020180071881911580c0001081d03002004000700300114a1047c07065a104256902010344200006c004048485581c0c0182c80085080d004040d0503600c058016041841c00705a10b03030ba20400646107100324000f06000450700e900400103d00c0301c2d0080d5030428203038241541002c0d210364284024038002200c105454010400410501503541b0640507445848004027440346040d0301d4450f9280d0000c00003c2c09956160f004900e19202801030f901848001040b044c0d407010490400800d0000041d803c2d10030300c1011146450b5980a841c26108448207521103c2010280d28030003002500300c4041103055010311026401c1410342ca0343c8004100328003220340c02414030036005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 238836564 1250 238835314 238835351
    0xe0f06010603050105090c0c160311040e030412140c09040b0a0e160b072409030905101e050906030f07020105090106050906061b012a090303081501170703 68
    0xc01000d241c0f60000521460b20f0f00c03c1c040d540401041151070380c4900f03600e44145400905044080b5089042101004100c421054001d11302030489090001c5900194180d4992149104003035400d4204e00d40c40b00003c8c6420440015484043c0558060205007804220640070417501110b4600108080042038462441031003040769120008100b49800c0c041480c040f02501c0c080c4886140740421100c0420503114110300c8188040301440894401c0000044041c2802d08401c07400314508440108090505507580f041d0900c40d0382d1800c040300300258807401028180c0d8009001c10404014081a5455600080d130140390028000002c902c0d0002e0000c4c00c45801402e04c0e0388507410202c0411095840750780d0241c2004080380e55590381d50f001c0071546038100c00b1100100341d950a1801c079841c2034101004014281c11a440c480a01a2840004945580c4140801008150020007040601800110101c0c1c2500181424400034000d45900d03200904106c0341000081d442c0e55000b80d00044900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 238837814 1250 238836564 238836569
    0x907080c030a08030a0b0a06030c020f010b13020901091703120906070f080c04050415090b01170c160807060e1608030904050a090804030308010e060d030c14100e0f0601 74
    0x2000360100c0c0e114800025250390450b940030380b8005001c0045903500e0f8243c1e00401c83d039103004060700140ca58429018001c0d1040b5055440540999006400703480f2040c00b540009040041c02c0340c03054444003125800a4000710380d2681040034103500891003035080e0b0543c24000f0310200041d0345521000d07010b108c08601c014500300842c0c01c25000d0281c40340d08210709011801e01420b204d98542c1c0d40d202403182c00d004a511640e070290610415090700c0e140d02091005880540800340305104945c0d0040d0359501e124296130140180d0007000a001c0181403018184403195019210b102d142c0035110b2240542203c002a12000d958815039005000c04201c0391030200d91100860944038648a01540c59000b05408240501d84560014039001c0050344084c1100350300c400040c1d03c941d143d007801402500240554000360b080e2034040f0b999443c0059128031a0399140d03849170600300302692246940312040008041911400b042e0a512102d24014400c2c0143c0a600401c480010034107200d01d0910180e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 238839064 1250 238837814 238837829
    0x10c02010503060103090222061404020702060d0c03091a070306090b2b14030c0c0f0a0618030b011203020c09090606010f0203070c090e0d110d110c03010203040501050907 75
    0x414140005036003107000d990b4404424203001910a902c2d00200380400d18918980440500701503409506a9141d032160042d2079000501c21191078420050004030311803d100079500000c1408204040102600b100400409a01e40440d410b501903a819003a114035280100e40010303810104607100340c0c94070840d4010400c009090003281d000307e011421455401402a0844585a03c950014030400754043d10855000100e4140d000b82e0008107501d0350806210f82a40d8004d00c8540700c2e86292111044c502204002c0078050040d00d0040290764005100c466004941d05000000011401d405d807498020110325040c0c200c080100d1900070309100142e603e03c1c3c42a80c1d45018003010440c0007a40c95070043c02800e01140310100c1d4003041c0c2c43c1d4013509000400e000e00d08000840c081e41c040d000008181f80c42c004844031691601c0c800d440b016400800d809440d40901d8502900a100d01390710025004c070142540c043c110f90340b022a003680e10498040c0c82c1c1c1e039111024400700c018100080c03401041032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 238840314 1250 238839064 238839077
    0xe180703110f03010c0909020901020a1502030124050d0209120d0504092009240a1e030203040b0a110d14100f0f05010c14010c020a0204060603020909062701030c0e0601 74
    0xc01ca17001e00000802d0080014666010508214590081003005141600702d4074201c0c0b1648401e0b00c0102a500901589241401c0d40040c104050503007a4803041800c05621524104400b540380e410080d0044414942d10a4281440400800043c000c0a41c61101651283c1c1e9490408030038900b07a9102590a00381ca540c0280041c0d03c2010b102c09441c01c0a0089440c1c070240380c4070126031034010010b000b404140410000d0300d01007864000c007408440644009404143e0164040198100e0004540203001c89403802c0000e0500c2000d548a01c0c01511144020380c14041010914005c41d03d00c80925582d03c4080f0301800114005c00b0b918000511481100c1800d050500612003000341542c4201814494003d02510402555003000803404103000300030800c400c22207a00a64440c061003050f0300a600c3c0103800305209200380202e0782185806000f8004944031003040c00900b81d04403120780c03081308801440516981d04184224021802038901101c0e060401005108506000d4511810b1181 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 238841564 1250 238840314 238840331
    0xb16090315020304030203130803071101050c0a12120606090513060605070b040c1802030411010305160e131b020c03060103170921010c030e0c0108010e180703110f0301 74
    0x44454104840384001d00000d80c0f0390320340d0b00d000d0f455801407a00c0603101807201900401c80480c0080a040481d0044600705904a6910019580c81c4140310a481440d0000c3d1032600210318a0b088806000c44285450741105017003003c06011120709802c550002a00da040821185c0707000d100d5003251034540c50341000001d18109000d0039a1099000051940903003400082c20301100081e01001407044a18000e1414202a0468020340c011034044422108154101074135520038401d403446401020010b1300840b42458041c2c030403824002c0191382c000d4120a0600c1001524029901411540024051403035a5010041e003041c21030729072075020380e002d400100042410940301000d08503c64075000d90f50000c48003c1384d011a100c009030300b8041c40101c011503030100154444091501d075a82c0402c99881103441298132001c00400c2c081c0040c03071900050010103040300b400f940021690a4800304030701000b05683c10000c1a074419581700c80d505900d00710324101902030350f1a880089008004400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 238842814 1250 238841564 238841573
    0x212030705150105180901021309020415090f06030e03071202070315020c030d090f02040509030d0e0c06030a0c05040321171003080a05090d06090c080d021b0d0803040b160903 77
    0x4241c0c001700d01c174020100c1c000c2101c1c02820340c101e41c1011162007080c03503860b45400101c0003030b50040c03241c614020201c1c103502071024810034005058420324800c165456103403076403c4003d81020340706054140000c001c18030005000f0000c0004c0c10b000c03600600b0a01c3c3c61070411104503004010342c01d0320b0b00d0040014446546c0007004aa0003441c603000b000810b01c5160034900340f28500410002d400500c0c01e818401c2c000b1001028003000380d0164800c3c00281041c100f51501c0c1c40c07501c0c03d21380d00801c003403021611022107600b00700842640d03850601e080a1396922035290b81c0e030301d0000d80049481010740d1104200d60010700580300740300c5d401003a0901d04000980c080c645002d031001401204c5d020803c0c6410700d1080044071020b002c01403241100d8111818000d00410401c00204c400c04c2c3c803004005404607010a03408030402954014118000491400d11a06100404015489529140680b000806034030203180524082d0030748011918218901910030001c0c01903034004d04c402e1240410004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 238844064 1250 238842814 238842829
    0x2030105090339030c060f070f080a02030c0c1009050d0302071214221e0b03130515150307050a0f1e0f03051c030b0127030212030705150105 62
    0x2000d2046410240c0141a15142102d560300810f101c8034040051800011180051020b0043c01221840e132660b8603200b0040d40c1c4c1c0b45008415070301103206507000410100b09640a13652044140800d9031802e00c1c100d00d06401c250920045800c590360365050382c0c040c00300401030a9802009070070218036009054441c542c401400c1c1401e00c00b00110700342982e002c1c2c01c0a9084d0744c1e2684440c001081800110103e0f0724034080e040c024629031481444603d07281e6081d41496504450307029904030b207151200303001c15107000c0c0c001105844611451902800e10580941c10300d00c07404d8000203190509070721000b05800c080e40c3d13070703c00c0e48280c10b5401d00340131545500c10410211541100c10307403000102c10b0031142c07505015a015201c0790b500b100000051000100b41c041440000d550044446001d054054048580395100b503070014002c0305400ea0351301021400b03c1e482a500b201e1a141a40d034a0f030026218010f40034900d0350f40c1e04040f510004104080150700e0010008120840070703503042c1800704000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 238845314 1250 238844064 238844107
    0x30215060d1a0601020c0405180c031204060f03140c030109141018091a07021c0c02040e0c04090813090504050a0308041b060c140a020d03260103050703020301050903 73
    0x2820301c0b21010424582c000c2109040f9104042d000f44564940b81000004002a0070302981d900e00401c03111121038034001c254944108070202400307090034180401201e401d40b140140d070b0185561050302c11010944003000500c40e4509408043d960346c1000101000e44061880c00e03141521810180700c02d801c004480c42c1d040e101c5144020703e01e80c2640b034140c0050440d0030005010050b13941c181130702074898002c28030b00c200f03447e40803280480d956000380070070640c50110060008000c00d819100501d005d802040748519804200e5200c0c4040c5400201101c074080350807100c142001480f81010b2000f51046070042980180c10041850b05485a41e2144a589001030070049110300040800602c00c03142d0580c61096440d034909580c80d202e016214006282040d603d039043e80000040800c000991454142d5000d4607a8040c020203030f40a03140c0035885900628000d0f150440503d0469810300910700940c0260700900e552860750060500b1900c0c044c01d5410103400410103000c5000d18000200d50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 238846564 1250 238845314 238845353
    0x1a101715060907090f0803030403020c06030103240204180609060f03030e06090a0b0307080406050f0c0a180503030a0c0b0f3304020a031a0609010c031d060403030215060d 75
    0x251a07880f00350480e01003101e500b100c181c80c000c2c881d020941c0c03403002002e984507522070b40032150340050302800c001c1a030109102c020402402c801c180403050000482c104600c21040710054203203500d82c6140c910703101740140d1040c1110396840040140d0296802480000c0c0303078400540f80d015003181c4004000d8440c100295000f401c0000b0303c0e8a0715260a88000001d042c100c542075245d0810203002003407070100b43c4003503ca550802c4041080301100d20800c5005007099602d4910302036400b00300b90350f01031010110b180000c0200000154a4034184010620000c50356907a180c034600038901880c0e98038010b0404000709801100304901540c150100c0c40302340b40d003000341500d5401041240c40510040d100c040d50043c4c008500b81440e15015040307032004c81003141d0001c14034080a011b03c00c013030056060720303800600046003030004640184007043d00619403d9200d00e0580860780840d82d15409644220016400b03400b8240403654a11040c68001500f21803c400c080d45984680c1c14039080320104170b1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 238847814 1250 238846564 238846579
    0x60402130b0304080f0c031c060e01030b06031626210c0102040305070e04060f050411010302070c030b07020619051e0603010902040603060b03280f1a10171506 70
    0xd00744000d200a0310394243e490617502d030307903400c0780b0310070701c0d141e400c1440c410680083c0035055514a44050103032005a83e2212141c1c4980da00c1d54031456510000600f500d0740500903102120303e000042d0a40902034005045010342d1700300404d851603041e2595a10ba180650411810001d07000e00c1c030700b51222100400c1405a032a03040c0c10b20b925009208130381c0020b05034030411900280503030540450a100e280141002c00c00848450318030401e4540445000b000045400c0403940950b00943c098000103016440000f507a903100d03a50007121410603104000564030000800c500410010b1240784034145c130034020b21117801c2c0340c1c510f0030804d119040641c1003c840400040d415840944c000190a40c00510070321115035030f424500010000b00344c145d03009001d1511007814410005d003003042204144141d0281d6131680d61120040c001c0044412100c00da110b01a215080070508030250140c0644004170360b91134a0424a680110300399039100041d900200844140d18601041c0c0b40c1d40040141c9084 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 238848920 1106 238847814 238847821
    0x1504050715093204230c030a0507260a0222050108060102070f0512030909070e2e1d0d0506060922080702060d050106020d0206060402130b03 62
    0x641807000341c528081c61070130541c1c0318a140007801044050304a410300e108501200080d90a10499900402840b0000100d441401d03002084d9042c60318013005052441030b50b26404004080340e00101c0e40005001d51142c0e0111040c1000000c003040518007a00e1399103c4d0041b25002d010f00141d83e1200196240d400001c1d80416103050b24844c007200e501d08010001c2c0620408106074407408281300e2103400d82c1f01e01d4401401101c0d25140d10f4140c007803040074801b01c10440185800d8683e01035160031249044003411b60802d41e824034020030204034a03040e00310000312501e61542c10610521aa805200700401c0c0b50380a00070071203124006440340128600c0205452041c0c001d0b0103031580ea5980019040300c028518184051302c0a814010b00640d00b5084a009a02110242e0440d864109150b61b05100b41544100112011400e0107100c80011002c490342d805100b80d106c0000010 = true := by decide +kernel

theorem cover : BRFrame.Cov 238669064 238848920 := by
  have h0 := BRFrame.cov_init 238669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 238669064 ≤ n) (h2 : n < 238848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
