-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4464
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:42:07.379529+00:00
-- url     : https://prove2.me/submissions/eb883f25-9695-42b9-a3a0-37013c361657

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 802697841 ≤ n < 802877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 802699091 1250 802697841 802697851
    0x15110717090d0204150801150b0405010f050408010504031106010501030e0c04050a0e0303161e020a17040b0d0509061b16080904050f18160302211608150f 68
    0x24903840312480000074080c4450042c0c0690003614281c980d00c0c4003c408180c040075106100001d01034204600304e8089102c2403072050481c580d405100170310403984181203010500d00c451074128201a00c5525850071542c042e103040740401e64419499004a03c103009040c018102400c003082080c10b810700706074071482e0341d0403081d110356520301c00a50107041c10350040c0c2c2c2c40161001265100d1400401e4401640c080a8142020640103404802c0c01420940c14141122080d400b41002203890b0307680ca058000f11180721030802c10240804122802490090200b01002c0107001c2103905040c4401810038a014141103c885a40303030161a00450780d00c101c8459101d10350f40800b410045040101c080e014400d481640182000140001090350502c80ea0090001c0281030400380d140c503241d41e60740c07040441c0e81401050016130400c0076107170145c180307020004401100000c095852100c0c42c1070a40350840349081160400c0d0a015521040000404000e04903003803c0e894144100c802080c4100108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 802700341 1250 802699091 802699133
    0x17130804060329032e060b070501060e070e01050a020106080f010c11010204060801180b1e030c1909020a03090f03050c070b0414060d0e011d0c010831050a151107 71
    0x10b061782900d111152044264040508010440e1604e980700300d5a8001d1000340d910358200107003c44c03030b004072440079400344015803201c01e50580a60019140c58104001d08825075582d540c000074407200034044401010540c8000180e40011400d0140c1490b9070b291010300e8580c411300051181c1d90b0003101c02419180b9295200d56901a009224070290013101e5545801100c80d2002103903000441e581c0004d1004101c0550700b0000746007040c80400100c118115101d00300c0704004204510040d401000710080601c3d01040440140c0c0364600006400c2c8411000283c0001e6141081441409454042d1111050030391620b89001d1303655500001244145104603c0010807815a80e00c0d40d001c0b00040408000a120314000c0d1700d521005802c3e106e060b10120f01510031200c10641c4034101c940e00c02c40d20015012001800700c030685151102d0f0f03605511340034212180940124408101c26900703280300d100700c4001c25000801c51401c0c1c0c2c00000000d59100418080e440c00101d130807100310200d52142e6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 802701591 1250 802700341 802700383
    0xa0603050c0901140c010207080904060e04050c01110f070308031b031023120105190c05030f04030c02120d0318030c0f0c09060602030315030307031713080406032903 73
    0x5160740d079036482101c170076006a600c000b81001c100460140548150041142c0811040d036940d0205402642d088030700902980040c00310091645c0101e40508001c0c030520102d4060004d02143c0300d142001d55041911541d50100c10864038050120121000382403161035581903040c04000b00903c612640100d000c034210f41200c8040e107105400b105095107400070803040d90703062180041c034000c04094800c081880c0c032a004420000310b550040c02d070307108595612903196a507234102d96001c2d042e0181085040103e0803010f9000740e030b1000c4840e883e8070344c40000b5105040b60f406d0301800315a4140e09082c6880758025100010030303002001e1480c100d4100300c4881d02c0b100a49003200c07491b1019040300d04a9454401d004c41d4140d4004055072048071901c015039200081981013603a00e0003010001800980600100c41e100e800c03504200c2d4001000c805590f092001d5550382c0c00322908650405c80000381d498444007401941204c16014030f24851070210440c000b28000300303071503050200c150f170040c2c2c0c501 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 802702841 1250 802701591 802701617
    0x3061c080f0d110d02070309060203090f0618030f0304060323040b060102010902041d060c0403051c0c300807050d0c17090a0309080f0303070c150603110a0603050c0901 74
    0x10b400080315031401c01038680e1358640301e641d060000d400540301a80004d0282d080410098000400c45000c090000c0c0585001d00b404801c010681d0f10031644101000106200480292410040441000250009583c0385e6040030710013411558101f90000028000404200d10104005020342e0440c2c0c21140c001c007250750b280c0050b8058481000300030740052800b10a8168050b0141c05009200c0d03a40050342c0903922102c940740c60718012400098441d400c12049001e50303440140e140d903203210203814144c0360300b0840d0701e8840d2041001200188030091640100351540030078100d0303080980080c03d00641da4140003130014040c0c01000113807004e46030340d007450101c16401103014407110258001140e80600d89100020307241c008295007180440c04880d000b1400c100089240c03a1505600f00045040d581d4a2204840e03480d00d00d082030342d1b501a000e40c080d0103012107009890196008400c0007190540100502841c560715030701000815142409000e034140509080f40d041304000d180c100b80b14019 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 802704091 1250 802702841 802702867
    0x60603070201150905150301060f0b0c070b030a02030415151707080703050705030712050309131811011107060806060318061008011d061b040b04060503061c080f 71
    0x40083c2450480310500000120707042642c004620843c40714800c0f11100d580b2400380740c00e8030290300400038142e08070801070110b4003030f6102914540180e03070112004035588216007161540f0903200381e03041a03000404c000900c98950800c0e28406034500e420403188032039803000780038910a40070f403540d01c0054089207511a43c08001e2800903020400c2a240c00554900d0120b40d140410300c03d00d0f02900070280005030384180d1014281c005034000000c0c0d490564144100322050915405955400e1341d00d09221540c0c1028020713000070b440c1b04000071009040c0c01d0001520703c1048042d04016a4000c0900344080380d40440c0700740c1c1045c025207080d0f07140d032550040c04001c2070615010510074843d03802086424040100e2080c11281944000c1000901c1040c440ba1103040311000844aa4015004100d20700d00c981441d40c4285103403859181030640707803590b014003036101c1e500c500c0c000362020007884071501d04200e130008a500034000d9010306071380c40d80d543d1034180144d5060025056000c0703140400c0d484 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 802705341 1250 802704091 802704101
    0xb0306090406110f0a03150501080402031b0105040b04060806010207170a0b0c0702040c020a0308060a06080705070f022706030703210c0b0414100b090c160b270d08060603070201 78
    0x9204d80b44ca58803840100030080007401000c1c030344074000b0740303c03100054194010422103003c0c1d40c0140c0540044a01e0000e4145601443c00d007d5041010810001070000420b402500150950381d881e00442c1c07c240700020301d820919040700302c021840d96291036454400159402d1002d0344200041c84940e100321681360103000c0c0c0340001c0d4002e82401c0170314100c2d50b40401d159071018465200c0320304a844002c18041410070a000361360100e0b4100d004241994062005440034910601540100c0c500c0b950218850400d503800c03200001182200f0b54190b10204001c0a038030500c1540280320070b62540c2c03507000a10042d045a0440300c81010403084140b481071022509040e00030383e5199880c1041d1419480410b460000c1c6a6113006102104080e0602e501030442c010000034103c00706038458011030050789c0c0c0074040e521090f190248681001403240c400441c42134401c0001c41118840301c00e0749501c5000c01c845c0c0b206140d0002d5501070f84440e0002512508044165170154890750b42d2001640100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 802706591 1250 802705341 802705357
    0x16030e19030c0c0f0305070b07031b020607141e1203070507020d051f0c03090228030501050a05010f08030c0318060903010219020f16030f05031207090f0b030609040611 74
    0x3018545000c558541802c0f84e15040f00d200b90203d40c0c546980e002041c1041c02046d01c000c0010305100d003d05840410007a01c1800d60740018070040c0361074101d9407465407807170030028581e805c0e03001903203680184030360300c10702c1203500301480040e01c864140a040c2240a200003400d0500340000416480c0540d00c5a01440c40d455a01c8005c6880ea4100015100a03000604280301e2820f070034002c844040c0c034480d0050406d404d5000e401302d42504100a808551007003031070b01301c0c18420410300002011800034081c4d00c0c09072403450000501c03035040c2141003070600d50b2a0052120342d07100700100314056000000321030a800124030603640c541001400161039125480301c180e810f41c0049080301d025002868000940321407a000c07114881440b40ca039070313216242c1c683d0008074002203000410100e000842e007144914800c6041c3c0340380412154080300c04000a441c002e000030301400052050141d0890281c000d44203d1450b0350540c98900d0016605250040000305500c2d100c88500d10f02c1548202510050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 802707841 1250 802706591 802706603
    0xe0406180f030908120f071103010f0603110a0608011d07022a2b0f0c0801150e0901050c16030c05030d0b03070b16081803120316030e19030c 62
    0x1505007400c00070101c2c0014044c0110701c4c0102d481c2c0d84014121740e0121214104070401c0315041c4201d644843c5d2403034900c200c4482e0155200c0b21a000b44010502c1054040d610400d104402d044c0402c080c04078210781504458281300148005025003400e44a9449100c58941d100081503680d9103403ca043c003180200d0701d6000820003840d903a0681040012821682065034681e4010b1409110b64200c50302c986524000303180b1140b5a800440e0141c03115140c160b008062503042c1a43c1c84208500b1030f0390750664540900352840e01404120080002c0940122070070b4024046400d007003480541c82d01c5160b48445500310003048a40030140a0a00c1d42c21a40c0c100302580d40b00c881e034410940c05007020b41e100c00d20078061040701041900d010701c299501070340c01020404e046c0c2551303130701d4905031740c401100188180c00c240400d4486980400c820500c040000c1c00042c0c49007840b0502c41203030f60441c4040014103040040e01340b2a0709000403800b2020092018980c00d800c1d0604094414803000e00024060f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 802709091 1250 802707841 802707863
    0x16080712030605040e0a0305030c0a1407030509010809030a09050d021206240a08070306051806071706091302130b13020c0f1f020304030e18040203010b0a0e040618 72
    0x1029016032104040f18810f84041c055240b40f030310f03065255020b0080042c0890700c14000b00c0c81090201000d400500d480741013900300d403480020815119007112504500041340000c480b400341d640402c869812403424070045080900144006e130800742940101c81c0169007415082d01550754410003007000381c900005a40b00303801c1101e40c0d08010000c0b060342640c0b41c65440ca00000c1400e007070b410702c006c0303440710009070843c2811552060090000a4000314245210045040c41100c0070700201e4015025038071010889003141d8a000180b8dd0000c1002d0f00c5040350074104240236407100229180d03607a040351045c04032040c0528500040144150542d048009032040c064580096401041c20b807a4480840c0c80707821540c036140da9100241072007030b01d560209a0a8078020b2000c0e801a43c2c1051181c18511244a0b2003004501c22101500c62a9042d941c2d4805010540c2005e219100e1030030415103c0d44249410290700002c0ca040150004003101c3d582c5181c000f004141d4402003890300d80c00914415 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 802710341 1250 802709091 802709123
    0x1d0c06031902030f04171e0d060e0112020a0e01060507060e0708011103040b1501021e070e0a14060405010602031b0a080c0601030b010b090d0b04111903050f01020c03160807 76
    0xa85510484041383c05418080940103c946401d05485047e04002100c10840d10040c00941e19a000182600b415986400c804103609420200150181403107030441e5401d0b00041c0100403141400344e1102543d03141d01030043c0100c540c40b10403500c1c1d040e0811400300c0c0040c50880300518004040e4001083c951038444540c20041e0038400a5008a0054040800540710744051ba981e2114415600b409a071207400e0240703820104071003500c00b501c528000e55074600e6680c0219000c251044030301408040da0303444031045401450301c510382c01217006e8408108940c1000c1020b9039038030418821007030343c1a03951808410941c003000945182580910144d4031580c910914550324602030104a6079804000008502040042c06461903100020b00c54040b03160b86031600c40007128040c02c1a40c0100c0000f0003106651903880c0c41c000e0130341d400c450906205265040c80350130400c0705002d004150340100003440b107640000069030032800e1020380c41e00441480d071a21741154401c0c184c0003000207003a000c22030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 802711591 1250 802710341 802710361
    0x3060506011232010f1815060906030f09110f130603030c0308090c061e0c0a030e18270717030a0816020d050a0315090903031d0c0603190203 62
    0xa005810f2850385046030704031041100c603986024000c1514409211004010104400280001c4024600c2c4005076208a5041c0c070119951542c0008000c100d040c4410044103525102d020781c0400080410130001426a888500500000a00c1403192555003100c446e5555051180c2030701d02c0c0203903030800c00150b4a1401074145202144280d000c00c1c81c4000243d808803020400401a0f180280424903202004101e13189070f4030a00100918800107100281c41c2950800490107801c0c000d440e491000400d50040220344003901d0f512505040d900c406000f07482c0c04125204005010303000784285d00b105c40a00003480d01010360300c4541d00d40c440840800c9510400f00003481096440da49003502a60b80700e40005a40c01d002c0217500040e8008a075031008148140090030b0034505030300d0041103002042d04444407d40e00d68021038030169032402d10f4800c15405124410f90840c19803021017041403003030034070380d00e40310b070005558010180000003c50540488001c00100c1c00803900464072410240e80d04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 802712841 1250 802711591 802711631
    0xf140901170604150204170708010536010b1c0512070f02040e190b01081c020d0f031404051e1207060b0f3106030309030605060112 58
    0x180550092000850080c04a00c0c00c86030303200d03a16009159a03280e5540314016200e42402103a0013603801d201c04203180d04d040190303031050301c91800140b0304241030061882c01c4540c040c00400c1611922000c1d10000d1a90a05940200441c80d0200e5107503511501447c1c00343c000d00801680c0000c010601d055000c81046031000494010002c0301d61030180c5140040713051203088009070000000342a42c0c4018501900107031200b81000d0300307450b00c002400300c1c6140700044047e0101c410015603c010301c81070200300a01031a070401800020136494010001079141c01906925404104920b44c81c0070109000b0303000841000145016a040b40c9858103209071220280d01401c0003c254868081020080008400098130700e901d00c1149441517a40d04c0c0700c020b0105030b9516402003003144100005503a88404c1107403402e18444050076810801000500f804180707009640c0301e6290550074000301381d0100d4500140d9074001c1000509480d41001604d04510324801280b040e0704001e0740c5e00e00c0740341103840 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 802714091 1250 802712841 802712879
    0x905010e041e0803060f040e030d0c120b06030f0c1e04060305070c03050d0911030a08030f010b030403050a03020d020705100c0e040603020d030806011110060e071e08060301060f 78
    0x320401800b510440c00800b40c2c2c92100601901d4083c0042541494a14034804994200800010381072428445450a41e0010702240380d0265685001c0d40f41203802458001d00d0100301e0b0020000e20300d40d18002000d5002c058007840302c1ca481074000030040c004007000c41707446042c8075142c141060381e1384445100d075a201303000b1140000e0822011a07086030040d0f0f0003600542d0b04d0b0301c5250514151006100061030412401d40b507a55140d0104000b944090201c80c42c40f50240802701d9580c41d0900d282300b81404181d03c482c8036407a0030400c01010039400b0041c1c84806919190141e9104000d07141c10020b4014090082c040f4040c0e0004810842180c0d484041c480e01c8175110503040055402c01c1008842881c44041d400103502c00d08480000d1052103440d500010504003210082d8190b0a6a45402c150002c0741d80300c940c1e01c10051011001841002d540010146000d18568554003082000c4812010081d01402080d4001c99111364082d008040034100010001381e801d0764135903089c41840e83c6012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 802715341 1250 802714091 802714103
    0x3040c090e100f021e09030a06090606080d0206070203070807020d02100f090915053309032a0906010e12010203100614040b0a0909111c020901270905010e04 69
    0x882e2503400d07041c84c000e0fa40740040d8a91400071004400f020303022164804034145a050040d6001500020194410303c15071034020761002038845d042c01801464201520550015944180d0800030001d03400021912071380c0d480f54045e6101c242920108005803020070009501002d4100305500441d40410241202001580e89101c01a40c461a08080703a08196840d030074203c00c800144014181010b5201d20684002c000701803214100030342501c1c80004a020312884280001c03200aa454100000041034140e90b82c511050300c45032890711004042007000303c1c01071015000280b90341c2c0c0100880e4405620251540661480884400c0e002f035004440d0311003600700310742e8041500c6108180100c0c03000f0b548a1074130310b810305181418034140c104100380f00800c5583e10005c190307441c075400f07824003014a0610149e101d9001003546107074602c801603603104c1130b8414481003a540e80c0c02a94081440002c0000130205000b01848000000090b0840e88010b81401c00008011029100107072046011310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 802716591 1250 802715341 802715351
    0x10b060319061403030403170c06070c03030510180b0102010e060702070620030a1404050a03080d141014030c030a0b060a0f060e040c03140108100605030a150203040c090e10 76
    0x425103c2c18421400000381c26900902c402d10000d0740b6003207060340721508c651100741820354694a031b514062048450600084030041c4071810140c150040c103400c000310203110034000e0709015611103e60a4011070309031440d184c810200017039000794083c859483c80c41d016501c42e4a0704801c061b59a48241c4070f034000091096403d08940d0911138109038508103040c01862031f100e19070f41e0854585030b1102d03a65884003400c101c001110360350040b0f508010741c4919641ca441f010b543c0e9180048a41d21448108107501a804020007000c1034040d034801c1e220145001048580580c0200386000300b162a55034042c410807030f14500703000904140c0c610800c42200e10103d429100d24094040b00c8080c8142d0020803940c4e4480c000c03d160681000c4d04040503480c3c00100000c0f003084078648032100380c0c002e94443d08282c05e4120245146d014050281c1010f500421100110343d8460008035007910300e40444642c044041400c00071110910001041e80d00014001c444840c1090740c0c64458611341c241d040b614123 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 802717841 1250 802716591 802716599
    0x6050d0b04020702030706090f080a020d2904030f0f2105070302070f06050402040605030a0b07081b190305060a14100e1e1f021b064323010b06031906 66
    0xd42c2f002c5a40c0c003030700c4040101116a01d0311910820058181c0e2030150460241280010300c0044a100300d00076a0343d044120520380b80648126610041740c010402011005030380302c1000d403880c0b40440c0b0b0034900000c040e52070180440c001d0154201c014a42c117030128155050000580185001d80d000316000c0051503030b540c003090380d01c030300c00381d00200940c11130400210418002d00d51070b5800091510a07441a1800c3e5030407880c10740c4030030305000e2204008440628425031610030710707511903019211441042e04198103000101d07038803115a4852505c011220746428441c4c080c0549807400a000d00841b24040300d84407540c0c40d20403c406000f0400b15000008031030509400354882102d40e00a0520388035045034501e90304182c002e4154100c4004c0141250210f0103c001703035403200b07007072080c40c10600c0030028000c540382e2209100c3c080349000b0200040800e42451a90318105020003048802503c641409230140418249196006201008020007285d00132510940b41001a20400030b25840d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 802719091 1250 802717841 802717843
    0x60b030d090f080d12020901121d060c130b180301150303021212010501080604090b070c03020f160611010905060412110706021b040906111e0406050d0b04020702030706090f08 77
    0x20304c41c403420000700c1c85200c0101015643d8000e0003c00818036144403010b18947c07190082d604140141c48070300b0880031540743d1340704e0144000c0760012900c400e030b140340444800c1070064994003406206160000040c3d00d404c120060200e5082c0ea00d000b030028850865101d1780300d1140740c141d11081e8054046d007240c51180d111400200d5200d11600008100c5a07401c0c4001101c4420001b445607411a035580f022201040280742410310825499032241040c06545c60001d05000340798040030301e00d50181c020089072000c055440c000fa0703401031801c2c600520013030171910302400c0c500713a001d44540120800d00080c0200c81d0588200d010454541000f007140c0c2072007241e03a4114a100317060068008a40181401942d2819a040320b03000500119070004240c645004803040700036251094a00001c022815510884840b43e01100e2f440e04103003000d14102011b805840b0780038405480c4c5a490220075001d58496064494030354018046400650300c411014050789198080c2c038085080c01c01c07000a080030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 802720341 1250 802719091 802719103
    0x103060314010e060c250602160501020301060e06070507090e070f1e060f0f1209080c0106090c110a030c031106070e151813021605010b0f010e01020a030804060b030d090f08 76
    0xb80f480200e21b060b42e041d42c001c036000e08040003213a00355020003007403418004103040c5031881030040000607580e500d0080c016084d90941005140180d50074407407403011a00106e40c40c2c0840c0d0551001040342c40c000300f0340354142400d41e0007880354160400b4010400c0701c1c010b03404002e10030060308400411034a0345d4043e00d881d103104000d1400a040c4011300014036104121b0400c17078107000704c8003091184c0c6a5860002d142c22a113007011726a0340d105420401c01696001e900c082885a003012240b07030000b0000d5135140d20798940b001e402d0000703505020003014840c4100362203222103582075500c182005070004100c010321031000c0b0320034190303480054014000c8a040741c2030200c0e030003c03103180c058528040c8403082140346e0031448025401d0240d501424040350b201c040075407240b40005030400e0003d081041d0724041403c440d04105ca100541c2d04c4d5030360009141118035405061141003503840b46052009000e10381c10054050113480d400502c4650411440016030309ca40e5030303141c2034585461610303075628 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 802721591 1250 802720341 802720357
    0x90f010503092e0903020313120b0106110c060a02061b03090705040f0f0e061e010e0606130510020703020310050702190302210304060b01020a02031b0103060314010e060c 75
    0x50011050303011a5030480342d4410345003443c83c401c0034416a0020300101258000c0d9003d4002d07801c0001c3c40a03421204c1c1c580400980203100c69a050000b098540c02c011031814090182444450046212240000c20080315002c1c40145103544d80c4010250094031000159604020800b03540010310402000d0f1050300c3c4200c444900904070b8030300d0801040054075646064154040d503c8007848600801070107522680110a8024406400c0c140701204c0c03000441e003100800080c42000501c55000710840287d08401704940da240c549014240c07900c00340c0310a6215583c4240080c046811036070300030444a044900840c107803034090540a03a03200603190221566001608000f15445003444400c0322181e010703004e0b1044861050340704000d11802c0840d260824580d8102008103c00c0000a000d0440441020701c084d11800709240e000c6642d60130402c0b150448031041c100c074860325074400d0f8401c100464100d5201065040d215841768000d2030700c0000140c1502032040091280e551090807640d4403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 802722841 1250 802721591 802721593
    0x50f0f091f020d0c14030304030302030708131a1f03210c0f0b180106090207140c030601060809010f09060b1c0c05040507090b03070e010216051e03150903090f01050309 74
    0x84040d403d0456802c2901001111180340b860544000064100003851046221380c0303005a5a08003050090400e020040080400650404400f0005186040c80301e90740561000090829160300740c441030248042c4503520f1032610794403000424040102d89100401511142003500c4011511040b00d850400070b1000d002001d81004c030000240710030001030b51140e600c90041066406180049007592029880b5a05003600419450240f0041d0310000c1d4418280b00001c01d0b1844040780402e84030541445070500b440400340008880c554290499030f08500306c40e904000c0c90101d4900040201006041c0700d005015194079030600c4c6010001c01e802c640d420082016400c0c0c588000c04c00a454014525420403400c4e6900140314800c00016500525443c3c940e03d00c5a01101c0009141c603900c0c0340b007521021200f42040000f52250802484200c020242c001d02c40c0460b1404207280c241e840046000d040c44842c1080300c041ca02101034002c0b1301080710980c4400c80d24100465003401305680368030003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 802724091 1250 802722841 802722853
    0x5010515031504020903030406021c090602060601180801020c0102130504140f0a0f0c121401060c11040222080f06060f0d061407030c09050a030807030c03050f0f091f02 74
    0x30b0541500750382030b0501c03001003003d45005994000710703045400641c440700259101c4048503200da20740d942c00c200019018030380308070200d2030f00c00e0003580c03000081d09680c144520942c40d214042c5040084030082c1025034001d40da108034129405000f540032081501003180b4403039012030540b07000e0040b0f00d9000940e140d2210f02d03032114a414050340300090014000c103581d440040005500718003c1c10340c0ca6900392035485080d0000310301b050554025a44040786404002c0050016580010300350407015007000b41c03541c0480d0400041400de104250f5025299175102070a407002c1c1e07846407040015500c280c0103581c6e40320b5a051100c1d907206400d589450703201074058603e4030a400c0c04610416101c4c0100c030f022401d0408030540c040b0500c030643d240d40000752110751824010b500312107024018a0142ea03050803491460300c0d0303a003480c010130000500300032420f40340c041814482c10544400c0c01d9230100a80d0398610200c1c0b400c02031350110071104d01a501022070741c0010701d030060b00c00f00c81060075000f07096 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 802725341 1250 802724091 802724101
    0x901090f080a03060509010303030e0d090e07050a0215100807080607051b240a0c0c0503090d031403070302070c080307150507111603060e03030c07110105071a07030501051503 77
    0x1c95800c8000084101651214002000d54170711b41640d008500a48000880c028218a45410b0005120b9410144454080204101c480b0841c9843d403007900c0f03107842a29450300318008c0b810000d000789503081c00e548580c14010221030700300004080f203207000c0c112000340c3c2da1440314030b483d480102d5911000c120280f200241000d030040c0f8032509242440e0650782d442511990030ba07120310f0403e40303802c1c5451810042180e2622284240c0c107100c4110f04062406904941e50542d8078030411790458000c13030062016904141c080d00300b03107030704040d1010550340320300d0319440090083d000001d042d940e06001101c0001e8510010049400098200380000441c20141e40e6190103400d019042c0c00400800d014150b03407c210a2008a18200c9541c800c9400585142800c038151842134000c03509a820410900040c10030b280b0489205651000f1032a44824488005035628000c88401602032154010f0b008c4070342042c074000b144148420b8800b000350303980791014020380e482c841c140d1000f01e0808001080c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 802726591 1250 802725341 802725353
    0x1e2a081006031e091523041217010e0f010f05010813030504150c0c1d0a24032105250c0b07080706050915010e1f080d080901090f 57
    0x600500c180912a400b024403402915003102c03459102941d400700382a26905c2d125456000f00c1280031420002c01c0030143d44040c0c0824034400242c0010500e60050100020341402031404088070311002e2503130f416940e99118004401c00d07045035035443c0f400c40320002040b62718400c001c4d20155141039456040319500c0f102c0c09240c0401c0f80300c060702401018803000605601030300309801c0c4165941c0d50255410342c9440e14404040a54001d495620303078182e44d0b0704d1404d4089032120740c840424000414224021074034070540e0049080580100116003002009002442048421501c20000e18602a0096020440c0d00b4040c140c00c99605000154004c6201c216140ba8043c0440c0034010b00075a40e903413029400220303072220a04585d042c6011a0101c1070004a00ca202d078440c8510380903010009002840f0030080005008650f42c2000a1000c903800803e00000e042e01c10b0150b0b80342d4492a0389030811a03a0380e2407004c000c0f00001c1c451f2000504802d1060180310300b4903502030409441411281d03506 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 802727841 1250 802726591 802726601
    0xf071a0f070f0306030816020a0b09030a032625031103010512010204050622060201021e07080904420e1b04180609050603101e2a08100603 61
    0x1c01d0400d502c8050110105401100518500c6680807c5400184403441800100281907001c8480328034107006a00c0c4039100810310b140000d500d032400d00b08058020051006c094912603c252180080204121800072100003402d082903485c03040d001e044030f40060490a40b5400b41c3c41c0603141505000400c1076090951140710102c0039000094185615000032807880c2d001005147c0d6812807a01c013103c075081f03120000310b01818062000390701e0031309109071510b1252610303160021400c1d0002202020702060380705803040c0d0440200103205009500e000285c071045180d007802c11580c0200b0b00107082150411404415811410b008a030b5585003006000c0702c1480200340180c2c88000001c8108a00e40c0f24004201a040c0c240c0d5001c0d15101c80c04a0300219840f98101240c06440c00701845190769001803640d4003d0220800441c004086420b2081c03c6078908400c0407400341884845880084501c107101003190080414188107500b1210490f00304030150360035501c1c0141054280a9a8800e42003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 802729091 1250 802727841 802727867
    0x50a05120c091008060f040209011d040201050702011704030804020306010b0a0206040b0403020c0303070c0911090d15180506061806010c0f0206040315020c0d021b0103020d060302060f071a0f07 85
    0x2040c0990f540c0c98a6071818800c044038504460400001004214584203c810340584144101c5c0301070862525424281088050400790500801041e032400f16803140c20500d204081c40707032451318203040616001d40b0a81080e5002c134031901880d00003141118800040d03e00c40111035004204585940d00c901001580c0a0010380460161062042d51920108000d1900038495000c1d0210b040c94000c2020458003128584140c80008010301c003190303561a102100503a0704070b86c00800300807081ca044402071451001000d403140c4403452200502001044076841035000303640071061401c88105e49446400100c0300540410380c20000c01010500a49580405600c05880240350030380303a45440d440840c4000c53b0356602a0005101c212960b001c1c447c030304000300f04d40000c0401d0b0f0242065403070030b01c019244840c1095800318900030b4040207134100310011900075006541da50341500b041c060a40c0801815600c010752a40015039400c0601030541c401c030400407011566840d100300c2190828081c03c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 802730341 1250 802729091 802729111
    0x100f02090901031505100b0a0f210f05060306040c0e0702010b130204080f060403210906090620162004050a1a0603010803030a0504050319030204050a05120c09 70
    0x4100308541d1924000640614050a905030801038078007551000c1d94001803e41600c1b150211080107412080c2c0c0c2510b60030211401d00c11000e103400c146c1106c441c0122006030388540606020300d1081d0b00701d940f1480d40c440003c4d405120503580c0c10f041c143d4030b50080d0340003822048800000c100c5a8405c0c0f0758140c0000e82480041403400b01c0754001112415a0340b02003081030380c005004c100e4510200040209000810040e00035450503403405801c00c0441c108420718401d000202c503414405a03403040599950010707003040f8421072420a680148403110640c0c0e4100d01d0401480e101c281c41109480d45001e07501d03040e5034211038950f00d02002c4c0d2012540d00340040680a0904031a0f5901e0044611480380d049001840010603001441c417840f00c5040b82c0c0c0203c1040005004090b004030450340d0183c0340c9500420070340c503580307000c5240d072003902c1d16031055014501400e940c070390345600100115031045607801001074031441000143c07110304a11a61580c403440c03101c90141005550903503c044060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 802731591 1250 802730341 802730347
    0x90c08060609060a09090c081009090f06051005030709021201051c0807080715050405010c03110301150c150608011a1003110c030708070501050f06010f0e0a030c0e040221100f02 78
    0xc070907407051f20034051a10b00400c10000800101103210b40d0b03450018200c214040c403001005854000c4005002c080190042d82c60b00001582450000d03001c01c018240034007140c0141d90307280030a00080d0040781d10617902d1200d40c00006494903000807409003c1c8080400301c8002c510340c0c0d0355110907a00400045030f82c00d006200b41c5c0c01081c0300d02455089204071110202c1d50b0310301482e00d10f0840d00403001c0c00b01418a4840391403000442802903a054680701c00c050f49407688800000d42e003250344034070300400c280c49070070012a000440e034000e981201d04450082c00310150b150300c4000110040303403106400005a00c5803845141c82034102c40709050701000705500d00303645140101e0641e0300181d02500d08020000d120800c01c1002d01c24142d0014212142c2d140908003400002c1200900c041c0100811002c0c02201c0000d03034a0498200007160b2007003502c0c8540b1742d1102084105202201c090f440789100403068070690004079400e40a80c000d1038080d00039440000c1162000300700391000c00300f149a0074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 802732841 1250 802731591 802731599
    0x8061311130f0f061a091f09080c0904030f051b0d0c151506110c18011e0b090d05010e03030f191a09060111060709090c08060609060a09 60
    0x40001c4040c0740030380403408501064024010015107088442d0760f2405031400c002004207840e903406041e20301030403a140303e80ea541510001880c0b0843d500c02407000c020aa41b004101a81202c0c28500300d4400d4820394044903006800c00c0640c4008507000b4010a54170313418017414a02c108002c01f4008164000d1009048108a60506e0020882901d03800b1450300b88990b0700384a00d4466a5401002c004418401c0c41102000d81c00090030074400c44080c000d078241221800c220a10003020302103000b501c2c01c150002d100390f040300711060078031401440599050661030035019400d81c400554940e0007205140900d00400c0c00b00202e10354030103868079540c5602440d040481030009501600450f40d44070b030341e803c021060501d001c500c03000c1e020f00700c1d240c04084110300c1c0e4070011001c0c0d0440708586200543c1d580d0b1005840644141c000403400d4011002000481600b081c1d0340c038180c0d0340c01780b41001107500102d019030303000b0000d880c8140e206d02c00744100e82452900070001e212b6000e00380341804142d551 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 802734091 1250 802732841 802732849
    0x90516180902032b0201060909020607080307090b0d05010611030304021806030c04050a240315050604020d020a0309061109090606070503070c080a02012604021e030d05090f01030608061311 83
    0x41e1160b80d44601c4c0c40b4540c59214654240038160190100c2d040400c25060325a00050707403803043d9140101004004000241800e0103500340724010202d50340d4040c0d0340e03844101c050000702002d0280b103000c14132442c41c0e01039130000082564820b590251034580c2c0f88070072107555841544003c0c013090345881409045041c68403180a00d42c00340b64210000300d03900c41c2c810411045141562140c8250581200040012400c00c6582144281c14a000090355488001c0070802900c2044030341c507805070000031001c0050381c0c1b65001c0c0320600d01501e4104111400342618120ba481060f03103441d4840c00c81004a0040d10f07005c801080c55512650859203000c00b240e030344550030705455204500d26002001c1c1d0000b9540c200c580c00c1c2c40c41c40034010600f08120750910600003468043c0020f0b001d00c10101101203403c0358650041c04100c402411940e94496040000340281c2c01301070168000c03070386100c500c2040d5020b0701a20013035590200180400341c1c2d43c6104c80520f541c0e51001640d04074520032885146480b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 802735341 1250 802734091 802734133
    0x1090b072a090212090f0307170309070f03030f020d1e03230f011a0f030c0715020d06030c0b121b1908091b0306070e0103140a09051618090203 63
    0x301d280b400c0c60007854104c1d0558102401c040c5401c1d80d1f40c00c1000480c00241d440404804000e010380700c22900c0f9240d4400c903034030703005140d0041c503044280114003105158003c60f100ba11005030764219000b0170749800e01120f14800600c40f0b032000d1000d900214904900a0b00f050a00081c01c00f24150041c64001e100311020500b92403818210b002100144032480d04500e864400c0e04500510626044801c1c2d9040c0c02d0f44401441c0c00c000d12800700b010001c01c1008407240409020b0340f5800d41d100c4a9040c01403004122521049590301441000090304550440079a0300c2d51024850001480d6541c1c0d05600300502d00203608101c089007007000300001c1c214581c1c22241d81125680d6003049203081140e203031800708801000b5003202007a050070071465400154641c0e0100c0d86191500d802038548005074050b00041030004e0700c0c55614400c01c0340302402544021204c1c2c0c007800c2222200100403000c05040c10304e500808070355103991080542d881c481e0b6003064000920140484038010102c00d4200c00c030340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 802736591 1250 802735341 802735357
    0xf1716030609051b03100b130c210605060d020a0903080408060708071707120207080f07020a06050309070308070c1d060a06110718200901090b072a0902 67
    0x182d031030201809204080161300d280b0182d2500b440c4201e4040000659640141ca41040b00c1541301d6542c013106845042c0c2005003803484070b10a03c404200302801614402d45880380800c3d0100b809a14001c40c00d05006035001c440c8081c0449140003d00401c41c0701a43c03106a065040c004410b2001000071494002440101101009461941499480204180b00c00f8100d201040f042207110706c00400d84441464124229007400b260b0070b0203458415011f0300544101403c800008148614000c1c0260020100d0500c2114441c0c0500c0d00c1c0d00b801c1c0e445000c1524450f1560744405824000a04014001c01c01613010b103c207039001c0755a46003404044403505102c1411541940c0500200d81887c80b0200080c0c4014140340704500e44081049070b07100c6ca90b1007183e0244442003142101042c0590268043d924004880c407042501041220025800000840d0000342080d0000504001c1d4106071818940d1000700c01a282c000c0d00c4000314504242d5a8101aa0625800000e9590304a1004007240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 802737841 1250 802736591 802736603
    0xf0304080a0312050108030313110a121101020a03170402011b081210120305070809030a0305030103121704020103020702010e03032b0606360308180a0f171603 70
    0x10140700d24005203002c3c0c0c20300464490300c0c101401400411130120590794080382800b0b58480c1190142401000031403110390082e0005400500860000a50030840c0c62060242c2043e104a8054400490740c0c2c03e01510054000340000c0991486070030981803154203d401490181000040d004088610039003009040b0360208000075101c10b02c034001c0d40301e0303a403020002d4010600b9031301d48443c507040950841c4d002020000e000035a4820412010107603900e41002404036032219000f8038010704150300a020944001c03070310f00800c010280c4545031620301c049103ca906c3e40e09490303641c0158065008410200e05008410051000e40d4800700050800c00c02c410404800e1280280c1d1070066a4140d5035011150380c1c2041002c0c01940e0304069521a00404038403540c04691694408a0440e607401e0200003c00110341400424401402d000d41516248044641c00c420450010041c19000700c0c400c075031142c2c501d24020000a141d035401c96000e17030703d00c1c4180d80b07a02c2070807a824400e86ca032540003110b00d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 802739091 1250 802737841 802737853
    0x3030f06040516020712031404060923010e1002031e0901140903031e070807060504061a0a2309180606030d09091107050a050f0d090f170f030408 64
    0x540750034080c298216403802c400b800341c0c02d0300850094403490b1a00482c0003804409003c4c404244c801c4010595598035180300d83d450315251030000b0281e000512444c03040080b595081c4c0001030080c81600070500050311a405c0d50380e04035043c0700746041e601c0d602005500081c0701c082e24014180800d119001801040242d403200d0007000035048506c0a440c1c107803605014003010304a41c13400011910030403607840841548410101c008001445010030080205401040441c200312180d00860b0140c0e114070020300070780c0c40381074111801d114404644d990103002c2c12000c00c0600d08641901102c801e590720340c841035101010100b02d01d81c400f501c40b1403403840e02c40d81000044909108080d04070b041180603000e8519003003c020100d600c075009007070710301d03a480c6075220780e03600c0220403102000d602200b9640075500e2410500d07240c2c6892030703030714070726024020190700c44030700ca00200c41c1a65070210194244c18102200d198040301c8250042c4031900c9804410a07403400200090030040c03030b41710f0091207 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 802740341 1250 802739091 802739101
    0x11418010f020f070b0702190602150f070215040206130f03060f0608030d151d06130c02100509070e190c030b011202071b080f010e060609070c050a0503030f 69
    0xc0074030100c04140464010350004002d46030003064030310440d84803503079450b2201c0440c00011701e441240c030b102c01c03014a000a000146150045940210040000c000310420f40c4d90040d0960702e0f4a040f9100070041e0016849089120b8a4002c060f0700315002078000ea0524103400301d0041d0510780d03074100010a451007241001000903d001ea01c2e081500c4540a0054900d800400342d0359000350800200002c0c3c40741051030b00d10b080350400d4401800c5061001e00b5084640d882082030311030a5a40c14080c00403155543d002e54228041c4200b004050360040c4456480c0d0b402483c000c1c0000b901000850141c003500040392050301c00b00c64081c03548112603414070b0711503038105411500c15484100600d418041c1d000c109a07005203108500200041d8050303a1030f48103207094103260b01100212081c4c030400c420701103141c01c400103401306640001c0008100e0b115200840c2a5a040100e502e41c2d400001d8800142440340b0603030500300c80c588148100da0342c012041e50358074110340040303440600c8050348a04000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 802741591 1250 802740341 802740347
    0xc18020d0f091e140304060507020f011103030c070807080c0c0a14060a081807060914010219020f03121c240b0327010905160f031101141801 62
    0x400d003000901c0100034012a50380e41031a02c8000c0c0b81d0340251940c1d581c14520a2000002401110200c001c058136552504c0d40e4029005402100301a0701074074208000c2105135004d0008507540030b84c540000c60559840d40c080030034a0f0322400080f5a5490117100840000340344002400601140d040900480680101071213042c040300d90041018489d0803040b400c20ba10769004407004190640703000040b50b502e00811b1804520068556410f5100395440080c1c0300b40d101c064401511680242c42c840b0b001400012a03a030104242030090503240b2002c080014a03110324a041c1200c0c0107000e4546e02d92282c98503040301c0d0001068500c01c1d9002c100c0c55070142445204800760001c1800d00100420303070154011420b80c0160040c00c0c2500000804504a2403014211380f240c00d16038075000181c8481440070602030848a0021101e9100b4074001b440a08802d13540714003500c1d20105a25280303407964450800d000004040c4ea414040104c250201c01d007079110040410412070441c494003150001c1c001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 802742841 1250 802741591 802741601
    0x1315180312270b070303060509090c040507051c02130b070602040302040f0903120504170f0c010e01020c1515130b0a090b06090d020307080601060215090d0e0d0c18020d 74
    0x92540b5115400c5600118002802c01d10160340480001c81c0d2503031403a2800390300070141a007001d5070001c156001c02c680070000040462500c07809442c00c0c0401d031102c5805070340e2400341c4107824480e9001c091402400d1136095001d000311040840d1150000b56942c0c40191099000c14800d48411f03400003400d00641c20030340102202c0382e006180c10066604292030080c10001500c00c0a12480d0315000841c0501070b840d188854084004403119a45503181825001c143d40f140000744071950900d0380c0511000d034180300340e40d02d0342c00000c00f40400500392602d00718900c030010716080c41a6001d202d082001e48403480c5107501885819000240c15145c035040081344410382d13004041d480e0808201c42401d45615050303d50b03110b03090720f40300b2111a1602c0000c1c20a60140c2040015100f18400000e400d90300040081c4900000f03580c4500f651a035042c0710740c884201c000700303401044031003200303000d14245410048015402080d6400b84a0344401c82d0443c0b000c0e8030251509115004951111252001d100d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 802744091 1250 802742841 802742867
    0x32040e010603060812030f06210c130c0504060818010f06081902010905040207050a20150705030f0c0f0f06342d090e0c1315180312 58
    0x818034071140070501c400700d06c4000e1010008001080c040ba0baa9110740c0015603410800130a42902d039250003d145039100a1865282d220f012100f080344440785240c8140700000c41a541c500d032410b41803800c251a42e1070301801d1a0030081c0011328511a0700b0083c42110840302040d14082112450080300e6031030200c003c100100103403d15026040180c1e0480031350300071908207030350150712034040f420485d0801704000d0002e1300b860814032216071706884410a2a00d4440110b0f071002510300700615481c00ca02904000518903070041016000202c292030240920541c44030480701d2070104451464100b60790781c070403105030f03902400c14407011014071554403242c0b441240b0421100000b00d0106200e0741003281648090040000041d2000301c4d40c1b000d10144403900003c2104250b003a0701c801010800c2d548110242804603002241094109404640045002e03400c030507141800c02102c0341c2c225030b00c180800c0602c84500c040c16148103c221200000754000e45103130000b40d82c1210040c05486030303880 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 802745341 1250 802744091 802744093
    0x406030e0f06011502150c070b10150507020411130806060f0d060c090f0e0a2003061203090307030c210c0e0a021204141c32040e0106030608 62
    0x16403880030050018402d41100e4030150003488003003034210103a040c0250912122240e5003241d00304090140c80307000804007540701d416601078035500c28a078200c418081d070103030b2002c0392a0000e1a00e0700038841c10103810340500080000034400044a80760030310380e0002c0c4042442030303030046042080c0b24060045640c000b50236a20069090554000629220b004510080290b0754400e80807007400d10441c00c040c041c14481003944c10f1941c640c1d01180b290503040b41d0040340f040c100291018802d50719100754180780382909400d410340d00c400080040004800001e203546100a00c12031001d03a504016550086001d505581c00260800300c144492000445010b8203402c00d18488000041c0507a15082c1240d1501d032440d030044d00da50f40c00c600607114003d600c00510765050140b000b417003c000080c210000301c0a0465540782c040c0046110f11004070040f003004612802c101c807031400c00047c9080c04885584643c000070842e82a6038002d5a00540c0014140c01240070040c042180c01d40309031070142880350 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 802746591 1250 802745341 802745353
    0x6130b0307321203040501180509010609081b0f12010902041803110d081f0330030b1309060908031006020f010504050303070518030a080a030f0e0607140c010c02030406030e 76
    0x243d142c5950f1300c02c0c0c0c880e444c1085035044a0101c40180d6094a20281070300510f07004140d40d40e144006c14242d400d000b506054002e940750808118002d040f6064035070400341860607103201c240100700c07603d20700b82c004a086540750841080140d035107110f0340f030300c48c0c0c000d401075441c1b45141e00700180302e902c250035144500d900090900c0d070016080b24049500c1411003105a540c03480c5440c01c004e6000c030640c0000e0007000e45984051140c0e115441c0071014000d800110100c1c0c404004c0c0c210280c42035440c034240c0040d40c0740f9038083e0030005900480b94081c040c01001c1030001d16aa2940542c0d8000c44a80741e07003160041e010300215038103020340d5032400d1441e4000d1080c0d0500352034003034480c880a0520f40030700000180c11010180080d0301412000e0303006041d111103525034200601154803030440700000a1620301c049007140024459140d5410b0b50030001c182c40c2d41c03000d100b5104043c00c3c3e210200d10190038041440d510b0001d00540241d00700d01d0340079544892600c49c025040e20b5001e181642aa0001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 802747841 1250 802746591 802746619
    0x20d1e062909030a080a031a1918020708040e0f0f070503150d06090312050601021b15070803011202010806010509030a0b10090f0501030507090506130b030732 70
    0x1a07045100e20001e60071003036503449078034006803824454100007030a1910110744030b81c0041d05035104030b0312801603e261400c103140c1d80302000300c1000110141a4035441840081c44a0304045108011106071401b006140c030360b250b00c40083c0c0350401d510a11050a01504000b41030750000c41282d041701c8070324070307010903400c0400e405880c070b00008080c2d83c4141c0101c2040da1135035607000015800e03250044d03c1040602c00c282001050040c880014022031818031021405551001039440c0340100d00f400740400ea24980410442100c48a03d01e00c42200300c24010b40700880c0071a00294000c00080e2000c10441800384005400c40c10000c4c400b82c103011040c44041129100483c9442819600c412202056610360303580e00c4840000f42c1100e01e8a03481d1400d0003441d2103071903100c40e0503a0700500440304d801e03956421400070742e1811242c090700204140c407084420307416034110300c151a00081c06e8403107040d168820301c5545030f01c01079118103000d900c83d10300b140f80c03000340f024500307402c01034030089540c880b9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 802749091 1250 802747841 802747889
    0x9260403020a083009092d1314030910020d030609181524030203060604060602120a0516122d0f03020903010903050a09081c0e0103020d1e06 62
    0xd6030b221880c1c0600c0130302c24040b0182c030041c21590b80c0a0010040121418107030507146080f0a405609a0030704040c0308040f4048250f800d00d14480d031500241c498020499a40300c01c200c0442d2624a003a5100a0040c4015607072404500c4c07514181d41d900414400b0000302008082d125981d01a40c14a460040e91461103001450040c0400e500069106d900b00c032440c1501c0010840b8250404a024070b000c0745a01c04070380d813085802141d000714210741c00c1c3d455071030421003155190300c28080581c0c04607085041007507814010b029003480604000c0d05041108c00c03184100f04190108a84003041031010000fa2900104850b82594880003014407a04a00265000c104502e105100c10b0001c5080f45a0300940700e030301212044140507009010b415114603000e4116000841e00f8000306038000c8004c60380d60713070001e58501440303106960007030718001c042421346072940007aa9580c1016000c202c0c03500003e21b540034508110300002041d64400c040041e0f9401120419000445004808169134040c011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 802750341 1250 802749091 802749133
    0x1080a032a0201030b011b0615091b0e01110a2103090f2409060c0807020d020c0f0a09021314060f03180a0b0c12250309260403020a08 59
    0x190a0800240c02080d0100599010414442074021f0034078062500081050540040d55050314400705080c15503200d95481054880100003200c02518200006400c40d102d42025107640300c042c142160301103082a0001e040c90b44451058894040b41425801496011181e1616168084c5801c214080c8180e071340c10003200c00090f001e03000c00b012100c3c1092014040b510030104100c020310400a110041c80d0600141031444055800b2850b060001003009001294460441d1a654050040d130310022040000045161006a400c02c1302030320301141d0030209200401e55940d070a4000074006140c0b424407504d94440d00da5450142e00288241004000f092003a25000b08010003050b500319408041e45140c02c2d280e0b600607020428440c2030015450144004101d80301c412b1081081a95582090808000c1c80c100040254041d0420312804607100e54003142d0418401d01420404104407045021554030102d20329884480008040046107032030140c0d2001484648003030003007170304601950f00c201c407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 802751591 1250 802750341 802750343
    0x603030a030b011b050a1205040e0c0d151d061909020f0d0603030f12050103080f0c100615111203040f050c060310080c0d05031c090b01080a032a 64
    0x152511101882d681c0511880501500c000c0388140c0d80c011941080c0780c1c0d032601c4c01400c0d9460211860012041d900c102d0884003528000c0c6d90303103030454a0b401200c00c2141d00240030b038400b00366182c401020300007414a000d40103016402022a42d034441c101a46030404010f42810701c100c01d00b904041c00b00c40d40c2d1403080b0443d66040c4005071a0310010750308100e144907040c0315002c00e51a000d004020190030010440c5001429070702e05140b1007000154800b101c2007808084c24042c3e05000c1611800900001030440301e0741403041c1c4900e011041c9201081e640542c1026859140003880084070310391020302d01c0c86c100d01e10402441411f4042032031090901c80944040c11078010000c0b14405e0103005c01000d81c9108025040d070343d0302e00e0030101c000b400850314042c0308540d00444941d40894030709003c40d89100c0e5040030107140340c00d070f05047c00c10700c0015100714880f8641c4c4407410340c00491282040c0c640244241c00140c40e41c001320703140c0203107545c0b040200780c00001880900d0a5200e4030941c2014041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 802752841 1250 802751591 802751597
    0xe0702010509190203160e073207060b03101d0102070c0e0c040b120613090c06110f03190810080601090f060b0a090602010c2105040c03050d0507020907080603030a 72
    0x207041c0d00101707051800801059803c1b5800c2680010104030410312184100008c1c0d40d141060400c03107001d030350314070001160000701001ca552001200c0044400a0521b03500c03504001848080190200742422403030001c00c61030039031f244610b041010140711a00d129827003950007185810704560794459480410301590200704451400240880c0e41403040f100905441c090403070b2298401b20047c1d03030014040340c0b428020064280040002c080600848413542d41c00180c1008840c2012001c84400c440460a00718921a002c1d112415250910091081c00940d0074100b21094a01e040030380f25140160402e0340d55103082100b0003104001091680c151001c3d1358000c00c9140000d034000014040c41d4000200c0c203d4001071001300303950800c4d01407003111161b40080c41149040388060f513159049804103418883c0c2919800c0c60b90300c03036a00266000344558601c0019a403252030b40392070104204004800701d800020400107501d403140074141d00c081240350101040c40e140020035103d018044405080c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 802754091 1250 802752841 802752883
    0x5100506042321060412140909070e10030207020a05061c020f09041b02070e280f141f1802071a1f05030f0d0f270e0702010509 56
    0x1181c0d444a42c0b2030200b090403caa03007074611079029116101c14054404881c0120f616502442d013a0050b4a5115000358410f4502d00305220307003050103000e40004050340c08000c43c5070810300302030f943e080c03a5104e901855940161075800d0740c4140008001c198002a104610602010b5030704291071072580c5036190182400358543c0074028800040780640191607911030f052540001c0aa94030804420b10b9035840d600704e07075045070f84401c010a114030070340d01c0b164501d99100a0407944001d2a004042500340001c0010701d091900c0721082c1212030109040c01c1c0f0f941c4900c18815801803c04000c0070184400c0e500040d018a0a080f50a00c3e19a0b9041c00c00300a4010958200f4440c0409000c0504900c1c9080184e032407621215030450004090b041c8072031030840035004903050030002207a40b07500300b25a00800c1c5410481401f030310b0030250030b00900d0070804c10b0342003400440709c102104001290303c03429861909040084040120340000c106400310782c90001003140403031002800b51400759510701f110403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 802755341 1250 802754091 802754159
    0x31509240d0809030106090b0f0405010305070b07080d020a050a09060f0215061306080c0a0e010e0402064e0f011a040e0c041502070e0a0f0207150510050604 69
    0x161401145142c0c4e605519100340001c406680d6000500710b442c045034050103100850003000203c5400f0b000192155022400502c800d29151000f860a140243c003401d0402d050840c1407016603000780c0c11480080c0000c41e0f0503030100d82055860000d020710b410a1000046d8aa030025035420b40654030110400140c40400c8850b00c582580d580000014003061240c55220a80c40e99290710450280c1d00403c4121b400040d0174040c0115103040e1803101c00d1898954480307408120054101103108000000540085004100c4c0c580c00656030713990300454000c070402a203840040d014102d0624040400c000d03000c1284e090700c0428008d0645000a060341c07040317208013030882c0150245400c03444550032a01c007800110210318001d4001c84401303d00e00a00000070200403a11074109100d44038180449801084200400c2c0c2c100034115001814018100f11094403284881090b06140c0d14406645030103024411203641c0e140b40c00ba100a4841925041c504040038000102d40315807400f80ea550001a40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 802756591 1250 802755341 802755353
    0x10f140313081210050a090c050f0307050c160e0a060806061e0406180509070303170703090f03050a020705030f0c010507060b061b0105010608071d0d08031509240d 72
    0x2e415605001c50840884c9010800b9402d44102c0e0f0040705d1060940369000200d104080c015900c140c04103907255030a040c0d4142c14001942c0002d401401405028062005c2d00d242c06c01810341e140e020b9100050319103103000c101c2a04482c01406030540c490500310309001c07540002680c00d8002405980c0d041717040100c1c203502280314101313040540e0300c5800c2042c0014010380d0306190454081c1c1c4480100040d480d488403d030340d41c03000c5100040c08a001d08540c189883d081003491580013003241030110345003d00fa074800c21022136022045007c240081000e1100550402202020301401e50051850b8000c01c2e0070140d5444d50b4085403810000006142010040c0a8002c0140c454014003e00c0e00c03403001129510188102031555405903280100001e000c9101e44103980c0150394603111100041e03c031140b410003c00310100e0305a00710014105000014542c80300a501c60010040a00d140d102110200152080301621411151002e007006400c08101c00d07543c02c0d0040300413240720285201c00d141503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 802757841 1250 802756591 802756597
    0x82122050a150c0207050f0901030201050f0c0717060603010c0e04231509100303050304081602030f03030a0e06010302060a08091e030a03180f11010e0d11010f14031308 74
    0xc102e024088803607a1003140c01d0300980c0040c8120713001d85545d162540c05109040c802d6211a039486000c00c4010030155000303400424a09480c0a021071901c80c2d00c1d00c0f542e00c2c00c4a580d1000c42c41900140c1107044180b01404400e4001c08124024405038001c19402020a801c14012900c116a036060007206424906803c1d4000c1c50401e20612092600509444600d070301480800d02400e550800174041c21045c10380c4038140c0c1e5140d10703480c1c11525140c8808003d41c101b6800c00200311850038480340581d50800c003030790b0142044d0000b140c0e00d2070080d40c00c0b4150762441810002e90750094006000582c1e410003501c1c000032451400781003a0380c0c4d88031020310301240b035010686c4a09201070034100d240c90210003803500c019251024030040001c1c0c4103000b00c4900d0104068880e0218811040006400001002c9000da0504d026070304840030f080000d9504908203c21500552441502c8030b4650300140001d080c103110f814410048030003444480000c5c0b10080c101d28040d4403a50660007003024240903 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 802759091 1250 802757841 802757843
    0x10020604120527090903031b0703090e0a1505031b1009050a0609080d05030405100911060c070509160f2f1f020a05040e060a030609082122050a 63
    0x4a00d038004000d61451101000883d06140500036040c0040c10100c000001c99002e046104022200341941100310520f40d0444101102000342415000403440403402200d030107180754440c00200e074858281900091070742c42d400355000350096034480001028860a000c204541940da04076504a01c0c1002c5075200c0480c0c02ca84c0d840986e0300004200c0d5a84101c1c00402e5400c03910841d4102802d4000c1a525404207c4006195a1140301c8810060180307410480e0071600c600050f90320000d40400141c142e421641e450f00a9038080748041000d4a0101042e0390003146c0c9100101000044200c002c026500c4001480b09100b0703e5501e07404a81c198000c0d030f0080b0307400380070510345000b40c411003551100b609501803031800003001d0303a001094803540b0071640075a5107901c07050300c0d0074a4003405c00c04c011801001c5990051000c04c2c000003088a031702608440910810041c1d980e10300c10781c500d031030140074440d030640c0541911b002c01003080d0100301c0c4002c5143c4a14407a0300d0b401341e9850040d1400c01d00d408 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 802760341 1250 802759091 802759117
    0x90627060302040c3605130e0f0d170c07081c02030406050403180f3503121506180d0515190e0601120213020f040501030b100206041205 60
    0x180b01310140c1c1c1c03002e44206a40c44210360715201c00d443d440c06001c01c03600c4144405800c01c0b101410499442c1070750000150341c41d1648040303450352000496034102100e05029030b0454010000322034119a100741d41c110840f07050f20030189141010601c125a50044440003030500c60002030800c1415840700c42c00001449203401950380f4a85071030a000074080030781c0c00314049600c0c0485200c3c203030000e08084040e80d0800c689507000d189008095410204200d40c00000c0c0f0201c1c859a00c000b08001d80d8031a0021200300045555109009500d64484401000516a2070394040d0b01c0d851652101c04441d06e4804040420340b001008500150415150700d070010118891401c0781c40c103100542da00c443c0718074a081260b4086005a0b032056040d10178031007443d0246c1d04010010320140f15840f40b0511094000740c03480c284448402001012640030000303d8907651000f150400c450341e031500480c01009015910b01c0e1080c0c40401000e940c0b26005030000317003503004202e0000466441035040d1480104404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 802761591 1250 802760341 802760351
    0x2071407030c050f0627190f0f0803040803390f100b0904021c02030607050c010b040603030512040204022b110703020601180f110d0609062706030204 66
    0xb20304616102a60311801e4000d0f11902810402480c0c84000e807084054069040e44e400d4600310106a0001c207400103803035018100040001e070101e00a041e03000500081c94000c0b42c8541010308055107001c10390b00400c03003035204010501400001009031244045140e130400502e2840b80c04101d0b9580300701884501582c40a02150700480000a5a001e04401d810940e940e441d100b128070f1082d1908601100e03000021100803a006003000b5040394406c507945512a01013440300e60000b41000c0042c0d50050009001160740600100203100f4101c80341c0c03045070308102d000d25594001d8418003400c40d070350316650300c2d002c002800d54a13a901140c0c6945500d17400c1e030010540201949090b200b100c014416010f2400a02c1104514140c040b694800d400d9002040340d80c0c42c00108100700c1e5024209020aa6100e00070380c12000c40c035001b00000c00409903030850301d80301405014411620b05501403056503003010301c1000319019124106694050361508074000b20b18070075a6a02400702c5900c000d40061502c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 802762841 1250 802761591 802761593
    0x213050d0515010b03010b160204140405060403020c060910030b040605060f1c0501050315090f03030a09021f0e01030f0e0f06040308090105011a03040303230106020f03030907030201030207140703 86
    0x2140402c606005040c1c42c40c920390301c98500c2d0045010900601c40c400340108480a244884c4103c94940c491004002280500030105841c2c2c2c015000d6a045466510030000d0100300341e01840020481201901c80310b0412110100040c0b003540304840c803809065030303240300f8101a02da0b600800301425001d00b04641c0c4242e0b410805909a120304460405140240010203a41c102070042c5030403154010001d0040071016030203030000900c00b901c5d02c400791054005117281a44140302440c812501001c0000302c1030003500500ad43d113150200000311907010582012040d81c0c100d002d07400031044c00c3c60001030442e94803040c00c1c02081c0d5000c21070200d00c0f03401c62680c02504002445481184a50f48620075605d03191901801c0c0c50003170160b000e00e4100081900d4001d8070220256620a0207841c000c80c101c0c0c015000c00511058140400284028800052041d00d8041200307d441203a808011032039880d040300d41c1502d6481c80e0000904040d000581e0301c06001d2410a4071408183c804140c5840581d2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 802764091 1250 802762841 802762843
    0x3080c0c1504050d02010b01090f090b130504051e011b210219021c17041509050601050103150509012105070b1801030516030b120d111912030213050d05 67
    0x10340d44c0d00401582800755860b42d84d489516201c0c11500000300342144075041000c01e00107407a02c2c105541c0c10101281410b44180340034000c80b4000c5014001a05800075011401c41c8142014601203d02d40c1c100001540c2952500c01c8c80000d01c401403801d840740d50b07201e00078a4400c207440000e0000e01400804c8000c2e01c860100b807400014805c6400316401407250084250011025803140b9011407084101921041408910070b80d1052040d0b04403040380503900303c0341b801c81d00f007210300359020b51085005004558142c814401ba401c149940c50100f44c0c40c0030002405800140941c240c030340501c1e0400b12049030f40346041c2143c150b212007074403002c588821141005da0480d0400003111450030000034406d50082c441d8a000c1c0c01c00c0e2104100c182a20310059003d4a0301209054000c5001e0650a1713959500b4031940d51078103000da039500820440c040c08181b81c01740d0880c040c100d10401c104031400040d0004290071581c2c049003005611800c01d000d90303504941181e0f102680191898250104001c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 802765341 1250 802764091 802764103
    0x2a071a0318010b270618010608130f08120a02041a0c030706020a0f080703110d020309100627050702210712050316080c040501110309130b120a03080c0c150405 70
    0x4403001d01c1c0700c005d40e12001001040d840954114251b0701178500107028003407144141d0380d4050b85e20740c0f03c1e51007240d4560b42c41c1c007030f000782200998411601243d40400d0000140760990481009403066081c0ba043c18006e10041d01d0340c00c940302140c9030004414410f1141403007501c0c04290400011916200c10140c0036210520400303544c0005203880340000c107494013a2181c5c1660204c40350541c3d04020407060018000d51000d040055030f03200c0c0940e022070400030340c0180009082c0c01d804555408036043c003400e2034030b0902d00540f40040e0410f0b040204103580000d0070320700e0008a0700f0610442c3c44208403074129218180001d08007403007540d0301c03180041e0003400441c0649100240c60a10078010041240c0c0c034a0700781c410018100c02003108006541c4141862001c181d10b01081da440e140083c000540080c104807400b4503d140c83d90340c40c00852074050062051124030320068101c091490760002d0104000030303e10300d103a02d00418944001c18003001006009810b50f4401c0d0f00b14206410a00e03510f507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 802766591 1250 802765341 802765399
    0x4060309231e0312071b0f0503090a06021f020a0c0507090614010518060c0102132c0411090c0c0316140d0e090406022a071a0318010b 59
    0x145507003404040d030202c00400c07180c104100602e21145a1902d6500300c0f040112440c1c4142903a81c0340c050880450b4054040500c0030788160f0046690750015014407081d10034a07401001550000c052020320101d407040c00c5425003544040050703036200090025030362200741040282c214420070b40d000c00c1d62841940041d003a10007000542e090040e060004640a1080d9000d22001a003008114111420b04801401c881241c1c90000f42c20316280d10f00801070070700641e0280030450068081901d030840749001c801c2148081407040000307480c0584a1601e00408102c0da0ba0091180c2c10005408540c044c054032071003507081c0140c80c1d5441051060224041a40300191101002c1ca218074400002c00100400e00c1000d0b40c4441c100050814104024220028800c1d1181a000c0240001040c8141b0103640120b41d41850104045400b0b01000d1a016280e0015501041034803003110844000b0400d0b66840500001240303070b44904600340d10301415903106103d40110301103412903100100c01c94052003003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 802767841 1250 802766591 802766623
    0x11011803050f0d06120b0a151202010818031602090a051e0c13060c03090506040810020f0712110706020c312306030601050d031d150706140103080406030923 69
    0x145c40d002d280c0703032881c10381c1c1c07091454149d00d8080400055011307110075070344a2140c001d1a90400d196600d081d045500c105440d020514082c3c9106085280c50b10070160400312001003086545885c1c9500850702e403003480d2400c6c0c2065140001440080d0082c201c40031120100c8004004564030707100a0b00b00c280c000400c9011819100e80815281090001c1c0c8049900e1b40b8010700d5002d2203a034000c1d000354048400f041c4c030f50100700a064003242d000940f2038000c44d520b82c3c0344002190712590040c00e21115400041c1190000e403039035200c03580e0307406c150b144030a04007040102054200c0102801a410040c0415045043c500140d0101c10800740c0c0e0000c010560900740c8450b95402e00305502c420090051035405076a031507150001c68418807407846003901103518000801c02400c002022a18490400b0080070400074030102004500c2c0101441c02541c4115800d05506507070310344000740103600541081641e910103400601803415444003c000ba003400c1a001d5101350a0b8441d00c49040424503914 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 802769091 1250 802767841 802767851
    0x70f0606061115070e0a03060e06091005011202101806030e120f03010b070215070b0a0c030903020c0907021002160308130b040b0c07060c11011803050f0d06120b0a 72
    0x8003403404281ea043d03a118000a1a480c1e5440107001c1e00c16403070032002079420014030700c004030029881e4460000000090700007002d543c6003c1183e1894442024840301d0150b041070010014880490b44e150f03151a03046a18010720a02c1d030400700c40041560b0648490313845450030004203690150302503000c00d403130b20301a10070a00e401a40b0540740c2c400c910300322900070010001040000c00500c06044490b1000749a8020700342d0b01440e103001ca400078030b002c0e01c1c6000d0320024022418454820b07082c2c562110f007010700030311119440c007a41b80c00700b1b00780703950044100c02c0001d0640b038402d200e00720710382c3c400c80c00c11511401901094883c6010541c001c802191715240482d403091100c0d414049159401000d0344581c8c2d84075521400700c0380d001b60040c910050203204040c00500580111500030a981c0c0d240310091180d00300d00c90a49a00048842c05000119510004031f81d0190407100c03054503a0142598400020f502c81c0f00420090b4052004503140030250f0b401c100450b102280a102c1032101401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 802770341 1250 802769091 802769117
    0x305160504030305090f030106050303030a050f36010e0d110106060816030b06040518060f09060d02012a080403110604060512061933020a0b0903070f060606 69
    0x3040d00c11070001801203102841807459918003180750700000d11000d00007090321a545c0b0082480e50304140ca103c0b00040d03e800411405080e100085940401c5c03d41d5021802d0151000b002c14860004c2c4510390140d068010844e030802c03003500b20a03035045a1608031062030342da0714002811511007a00340344142d401d000c07002400d5403298076081d000c0c42c1640ca5609200641840c242c0040c40303500d44030b035009441408001855600d8170302070f55142140d04070002c002d2030420100901e100f400000548075035031000034024181c60f42000c0320700040e0b082c00c00d03c01400c010708000d540c0c1100710070a5803103020301000440c200414100604100c0b03208080c5c041c0701800d07010410800d401a4000c1030001030003800303014141c0184071138064102d14007030858940d4a001d40c040c0d00782c80e0101c1d04100d0000e028603440c00f81c070090034504c0c013800078090a01494900c0d00c0f014020f44915122601030140d0180f9400705060b42014011251000d501c0460204446141d1400001030800ca110326004500c0e1020f60030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 802771591 1250 802770341 802770347
    0x9121a0c0c1b09010e070c080307110d0207081b030a05010606110607030b24130312090905010e1602072c0c0703210209031203040b060d0c05010507080c030307030516 73
    0x1403916078001c3c09490b580c0c1c00c1800504842000418040c2001314034040c10001c100c1c254002d5008100c2662901c11300404611003034546800b103080181103500c50201003120400214494900407040141c4410411204000030315044140700c02801e154600b1000241c069000464400003451002c01c0d61511f60b224401034049030b04105404c0d0b0481030a16076180c036014201544210340c1d1a0400c100d0a0151a41141d00c1c20805a001110302d000020100c00815800c610300e44001c28a0420074000c940c18908000400c00014184400e042c11100a00f07400600a02101014000b1600740001c1e40d01203104925080d11507090b90b1402100780b5012070154032000041341d1140c0c0d01600d80d940f0449108007401e0760021005400c0c0c84099007848140100d030760a2180c4600d1900c880e20144d228181070030494500391002c2c22082c8280c9821a010000481051110040701e01c242002500c4881c1414081010301c2a2602100d540c0070000805c031300d480e0103074012401440c15032481c001c9860383e01025 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 802772841 1250 802771591 802771633
    0x50a08070303140901050706090b060a0f0b0f070215070b0118090317091c020a050d0e180402030a060e1c020c03030d2004151d0109121a0c0c 62
    0x280010310703c400c1d48045101c05400a01100b0010315140c0c0c90a0020b0b00c40808542a00508441d06516481880b205243c020400f2000d800e428895541c0d40d440d1500902061089010729440c2c6800400c11074199541d4113042c01c00806500f510541d161600c4c40d01c8101d400742405200c0480800c4400c0d2500d101c0c10380308640a550303164842d8405055102c079107203001074000f048502d45106240302c02d080180a2100c40c0100d8001e80c005203032400251802c00d0900c40380038550820840324036110b4400756614484900845480078201030f940c2c4a6001203401d081d0f440d90302800c150b0820b4401030203510002030600b281c42c0b0074600ea010301030f004034080380c403a0020205540c3c190310920001400140540c00400f1400c0c000508840401504150329460b80044c1d01c006101e20742c200e00b405004da002000391110034540800c03083d0380c00c18003001900040c260301a03e14020b000103459410082c409107041d80701d26500c0d50401e950328000d48400501e60194a4408650043c2482202c00000e00002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 802774091 1250 802772841 802772843
    0x5011b0f240608150a020d06031509030207080d050a0f03020d0c0504050906030601030804180f110406181508180a0c14010e0a0b0a020a0f1208010501081e0a0b120304050a080703 78
    0x440c01152501505c5d400030350081403102d006159241d00c0000024881c100514025213559004244c10020b030038042d080c165183d225115a411400710f4503c1c80d9407001c21100036808030b0911980101061008038000d01500c514044c1e13042c40c0241c01c545d4950000043c00460b08216000f80140e41c0d91800e058596800b0b10005108910070b01090014840084031149681307900e04000075002110203c0e4410b0345c84540340040c410b00c0000e000d12030141d000ea06000754000410340c5c01c44980c41c0c280142103040180006004004541c40407c64003c0c100c06c0410800281a040301c0e07040085080000300102c680c850303501e41c00350590380918a5401005c845265503801007509030720918041c7c10342040c4e40118008000c501851062100044600c0300180c04a800350f214035401151b009009400e136501a0407580c1403045d00360801c2035a0b030070607941084803286014840e11a03120140020090407105c05055400fa41d0b602c01c51501c02e4000000e04200c0c0d5003118440700312a91400c10686074a01808 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 802775341 1250 802774091 802774123
    0x30b090109020a030b1504051801060e01031d0d17090d1e02071a0a090911161403071b090b03070b07170a200705011b0f240608 56
    0x10481c90301654050700c1d9815007400c000c5424803684000454100426110740c1c03111102003418031a42c100710703041000b8565000c0342e6a082c0d504086000e0490541d444005040544920031101d4092215040202050180048801190080d20050885201c15404000110035074001403d0114000303004100020039071110403125025138440c45400029000700029442025000074068035032049506141e100f80360000c2c0c80d500380103401001c1d45041d91103100701c00c0c11300f03c864035084554411200d2181008083d03010311f03005c031700e40301034080d0610301901d05c40c2c000410024144050b1101560b404154402c0d2855059111b00040b8101e400100080343c0640c030080d0140061880c00c2c0042445078002c080e036400ea035010b040c8410190344091091400240d441d920002001c1e503227189941401410030103054511b01b0305000810034500d1038500c0c2d41c2d48116441500501c540480b10000ba941c014a0b2036103800d40740d0008060340030a60613800c440d585001c42c00180c840010460a0403c50349003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 802776591 1250 802775341 802775359
    0x3020c031c18080303130605070c031d130218010e03060126010603150207031b0b070e0f120706020f1507030e010b100807030b1207171606021606030b 66
    0x1d04581401d0469030301c03040b2402401021400c00350400c05184614112040b4844103200f038500801603e201405510920001350018400079400030894038600d00c4d46a400c000c102240c1000400d290200b400200f00b00d480002c1c00d42005505a07030051a50b1002e0320703512841d842c41c1061603039686091142c108180d00f00b0043c40c1e00c43d03141200c6c10841c40201030000c40d5041d16034403201100e290140603030240c80e0f40000c24500700f60300703e419020b0300c10361254080030900c1c242d12503c6122100030590010041c83c100c2d00042555040d0826000e400c0c040d0141442900740d800c1e0695a00c00c1e405131102603c607010540000a50000c0da0940c8490707503116181e03076902c460600354003a107140c00101c60b8554a400c8410800d4030350b00c1c8124241525603840d0f50807403c0c40308001e0110b0345150800c03405000c11000394a0700c01c034002120811200c0200032826140c11442d4070364203108860000d1510884c030282e00003011940010032202240000741d4110f54107a94041c1502150f594500d0541c111500e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 802777841 1250 802776591 802776643
    0x181503110d2d0b0901150603023414060408041a090603070306062c0603040602040f0f03020102060c03130b04020103062105010c0e1e030309041803020c03 68
    0x901c00e2025403500c40c541e0350b004200200000000d001d254880e2010301107641030460148042c2119058114001c00002c101d07102400e0283c0518420038040c2c1c0c81807540004040c0b07a41e02c00d000c1ca0402004404e80803040c407481206503d188100c0c241410703900303c02011300c1c03000d0301000810540d0080d688010072605c2c00340307801c1c4807030000c100078041c00f244076006110841c4503840c4c0b44001c602c60f400c01c1d6400a40d070340c24003c2c050400c8000442d891050400c3c084a031440000341000f030102d403182201d2183d00c9a90b5807410101a02c242c1e00b03c816945d07034098000a0910100c840002071304e200b6003e880c1c0ca81d4422201103401d0104032004641381c2207008440000c540403003011900140180f401003046511550900c0340401070030003007249582e106c0e1824060103400c2c0700315014041c85142404010302105c000682d950180902001000524034100d54a07036010401c4170b450344800344c401d011425420b802608440c00050040c1d0141c090880d25210501d0041403040c01c4e420140c1e4118100310003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 802779091 1250 802777841 802777849
    0x605190504180507050d0c030507180f030b1b0f040e0a050402131d0d180801020f0307080711070e0601170705030c07060612050309030708030405090c07030201021318150311 76
    0xa4041014850104929000680306001352903403a04103407000b00783c608084400402072072556503203c2c3c01c4a142d0201f070cc690850008a40101c2c1d40001c00c882168881112a40081e080d90101403095000010803907080d0641a010340112500c5030080c1600e039655010170000d0322812640294000c2d0f03000300031003900390198050300c40c56900141e01040b41543c1c0149a140c81d04054842c80455030051050724017000c0c46100d40c2c09015068025400c01e8001490b04582d400084d003503030709200f0450006107070039201d03032050b907610900141150f80e00eaa54800121140e00e06032138071800640b038055070301c5820143c0d41c8c1e001d016804a6665a1859903031074610506600080030459903603803102c4000806078041000720305450b0082001e155240d086804040c42d0510b140d2100c016900300784400c111a170f84d00402d03507a0103000c2d070031400e03540e40703907072034200e009106000307081c00c1c1c00b02100e4002c500c1071008a80300741080c001d02d130104449a2008950ae080038040d11000784500c0031002c1080303c600b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 802780341 1250 802779091 802779101
    0xc07081903021303060e0d031e0c1202040308190c03020a0611070b090102040503010e0d0c02130f0c02010603020f122112091513030813110a060519050418 68
    0x801480c00500780080c80303884081c4800c10b50b100352455511170076185c0e10b159040c44044000c07100341c00c0800408001e01020a103c40841d85c0507070609d07a9810210b150540503003010044082e07401811560f6607228070701840990061766040c400009070984142410380140070b40e41540d80c060f0000e10304181d00b07681e610042c020354002695010420700810001991881046001d210580d00140c1c076241000d05050071280b035040303c2d04465100c04a101200750b0001902d41007035405546240780354038444d01410141001805000d0b08919151940c060194190300c030f4411b9038030840c2c040f4041d40002080001a20420a032040140c22140e092550381d00401c0400d0511800904258103003041100c580104000c1207841c4042c0303400c002c2654642c14501c040789613110303041c50b10007210100b6588000f807151900803d00c3d1b241d0a4603014140c28400b150013400000380c001413107a0542622240001c001e900501500002061741c8800460454020410788054603103441c01011205084452000600 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 802781591 1250 802780341 802780387
    0x405220209101e0c0f11011b060b0f060406120f0b030601060804030e0406030f0b04060f2d1b052b020702090f0906070c02030f0d0207030b0c0708 64
    0x1503820440100d450300c400020030480301d820b444030040603161204010707103210040c94810030002d161500d0303800114650800700419030042000100600444010b0303842d8101c8074141a500a20a82c1c80010010303190424481072030103403880f180741251842400fa15004500407200400c6200721800031240141d802242c46240c2101e001c212001e9801c0400c0c1068400c4c1c02c1000000c42e85c004000a140d04a81d2200c0c4400083e44c04000903071868440c811040c2007440d004101504070400b00e024019542c0001c05010054401000010400c41c110700c0492501d003480144e619000010b02d190315094400d06c5409840c4803001110405488002c40d00c0e0340c040d0400b48003003801c41007021241c0d00c0e010303410301101500d54001a650402c0d40100544108001d10424102d80c1060400103520f00c04600305070003034030138101000314640610003c0e00b030000070703124001d052195a018034100313540000c0ca482280d00038102c5460035202c3e0741c0b06061502c505100944040b1007041000b1071140040a422458 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 802782841 1250 802781591 802781659
    0xd09050a12030608060115020714060c162102090402060708070c2c090d031109061c1803080619090507020c03250b0304060e0d050a0906050405 63
    0x4100c1996410400000101100002a0760340c001400842c008004403809030003003241076a1400a00c0000940d02c007440c0c0156042420b031903008109030b8680394161082c0300403203001e64622000a01401c2c140b508103120314a400450600001e4598034420310107842e5640103090042290340b80e809001d82503001d4002140c8003441000303400d0114100c3d00d2924080c0c24101d01c818542c10b031940100c14000410001140e00d020305005114251000051120818a10f8100031403e48a00e088607051742c040c0031900c90700180001440440900c46060f41c683f0030742042000c102d42d01d007159001c0c1d4002480240200440c07a00d1011a035a4a040300040c1984280a10120a21070b01d030303141441662801d450b030402580c401c0f04d0b15071040c035081c805125503900c03600700c9206c3c5040b50890810300110922540d1080f40000020406014040d040740c40c007000d00380d044a281c100c4500d80109181d1041104c1d01c002080110041855482402140c2c01c403900180900c0110708064520801d044560701d501d115 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 802784091 1250 802782841 802782853
    0x608060f0c0c0a0506010e06060316080603010209030307060b0415060c08090a12080304050d0e0d03030e031603050c01050c072004063204050106170415050a0c020d03110d0905 77
    0xc4030004100b110f07001841100a41403d5151158030f40c45460040c0046100710030a000b00041c00c00a80700c80341901c0c166140058594039100c0119009128510201d40c2500000030164144016900300e01c0d0540740545041084904a440f040701d00358241c00f40754002a0000c05c00408608001c0c080d21050354000e2800c0e1815580d882d01c0780e5120039285080b02c202c14080201b200f40441802400052429070400d9231680074018001900510070380390090905580c2c8000c5401c080e0100180c1e0390703452481e9214215007040b42005070a03034001c001003401c25801e01002440c0846010191031419500240780581c2c44c0c41d02e42825100701c040850650081d070354080010f6001d5620341060510a10201d20076007a14003400841c040d000e0007003015000c1d42c28000100403099108c9504401030300c40107411140d90b00d81d4500101d50307105030420400c5035400c21061244620309540014803a13002902100d40803000101d040d002d9a0507407051180042041c00241c400d203040b90080b211880c416005c0c0d0380 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 802785341 1250 802784091 802784107
    0xc09031005070f083903010e061903050a06020304060b042c010b0d0201030207030917010614031603120504270c2d0c0f0510050601030608060f0c 64
    0x840d00c40d10120504500340c49400b4001c0964110032003007802601e83c07400301d90b076140680c45551a0802d9900c000ca80c50030220f100280c052003890b45445801d0b0104409a0f00c0d6500e00a4091300350042c1c605602c2135001d0b240404082d0b1104001c0c0046a034800c02814110a05803103090007904010002e4039616101d000e2460700380d5591086041d40e036403d51071641818850818221401e5551501c070803a68500b1a8085095881d00c00e46512903a09184c003580d9808180741c100c4600040387d02c442c0191050805002902c1c9040d0041d00076100c60b181c0215003040740408065071413002c44900300c1c0c00c10b0540024404201c03240800c00c4468000d042207450503644905802c00340072480c903850000c13025119588041c0c00705000c1c54411410138980019001a0400103500b4a984c04403000716451802c03895524440c0281c1161150780d801044e4109080d1050034100d4a41010b0750440f0451480e020000b10550300920494042c0c448000082005550303950605252100c00f40503000c0410082c0000c4d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 802786591 1250 802785341 802785343
    0x1303230417070b0c1c0e09040c03140102090d020405100515070201080a1a04270c03021009053601090f0f060b07020f0a031416120812040f051e0606040614090c0903 72
    0xd8008c41c441c04000030381c0b919500306a01c1040c08074001c0c503800c0e4010040e070101075640840541080740c04503800105a150002424040f4469074803c903000402c100c1000e0611115002501c0903600030380311000142c1d24600e40204a51032a0102c403020156612000960304159101c00c4541d400c0720251b50310107004012803444032001581c11a02000c001302c1c04d008604000784610108040c0d418800541c9003024009900a0b1034091059000c0c441219403031824a407810900c144040c11211507080d0796166a0701d1805006078650642c00181040001c91b0011100e1045004641c641c141c0d45050084076130810100d5507101c01c17540c1e400320280d04048085046c2c0c80e198680210220020300c00d407003a108004400090607400390042d11940d039201d1001c1001132040700c864000300601e40e4900c0ea9180340c07107407118002c1e041c05015445842d0f118840140032400d4402c104170f1007800c0340d84a940c0c1074100810354145000d45054036800001c500c403181401c0c800b00b50040e10400030035040a51500102e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 802787841 1250 802786591 802786609
    0xf0115050405150a0908061305010f050c030712060308031e1b1b01020c01020a0c170306180921040503010605060721021f02040302181303230417070b0c1c0e 69
    0x3208e94018400b98004010092041c003c0303a840c551824400e9103014298400d03d80801040082030184c000c007403c100550540c0f110014603405020349031030b81016008086081400814220080040004039900c0c3c00c807124682c0d050741502c2c0c042c0f4a0f22502c450040c0c100a001e40b89403549640038407007241c121000307001810000e15541c3e503801c074542440c204038480d18441d0718000c0c51030b40200b00780441602c80e40403d01c000030803258075645580380c0301c01440c40d10544d00c0520030065914401a1310b030081450090045035400c50081c480d80d80c45004002c1184030790b000040400b400d0030741050074050f9440403040c128010380199201c544a20400030361035417113480c80100083d4001024811445e1100d407111603501d00c4046100e20707107031103002d070b001d502040302020b418400e55a80d0041500b00341204002a8030134060b5480d100d55a0700041d0104402410908240340114000451039143c1030302074810744d00001008090810030002030556900c2c1c07034010403003045012a070020684d00c455a80c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 802789091 1250 802787841 802787851
    0x33902070503120306012a080702010903020301021c0608010b01120c0e0603070210140c07170d0906090c060305040309171e1515060a21050f0115050405150a090806 72
    0x540d0b6494802d0004041c600c50340100b88450314a4401c22031a80c0c082501f800280c1e901051141d41c1d11510300050320b40003010350002f54590300014110304040300e40c00340d50f0b070740d10412074041c0202602c61401030300b40d801c14001d05001031814108660303000c0180e007140c401c2c61020b040600400b022180030911075401107d080f40944e014510010441105209280b41e09250f4001c02841c0e0424004005007441040310117400d071460001c80b84907090802c4126a00d80010a500308001c030654a4a2005881c5413071050322404070035440001e0060190184c6845280c0c95552905290300f09080c5500c0314030b04401c109640d200b0348042c00c0c410020003160301c00010f00d400003807404010300b044200041c9802401a0001c00349040f507a900c640311002602d44075000c1e4102207018051481c12070620402c807003c0840664100f0060290250451b46041e06a90b550204c0d540c8003104030005490601c00c13481403075000804100c00010400405000d488001040e180c0b1420040d52040308500d01202928 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 802790341 1250 802789091 802789123
    0x1e080a0f0906020604080301030303094b020906060304060b0d0308090f0a0201120209030f25060c02090708040203030c2b0804080d0b15040801050601033902070503 72
    0x10610100300d82020000e0700a140300c0c4014001c1c0c1ca0260790b0b074003217804184001410303d40c4607601c1c1c3e0108444109100c41804098a41c01c60301681180e46840e1280289540c0c00005000510300701a44801200400d1098010301100d00d65100c05c801d0000703036400200140c07030083e40d8030901800d5a50306028619014002d950700355050410301e03803007810010041008071040e40000c00505c0181d8000c0000c0428110013000140c891307212070003190809140514030f0050380900c080d0601001c64100440751545030340b40c4403900346500c0707000c01c1c3c0d00070320344c0300340030394031000b12400149240d106000d0507510601c00f4050305d0501729003480e1b55103000301032504000842840391402c1c8010380c050205c0584041c0b40d02c0c0c0444c2e141020703116610781340315a82503400e5180d2103d4445005884101c0f41001d00f4000404180d96155645003d47c007c01081d034034180040e06103084808400e41c1401c56241c1c1807840f503c5030420441541060749000314100440d01907005400001889580c140003161400107600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 802791591 1250 802790341 802790357
    0x609060d2f0906010e0d02130e0616110d050d180f060e1023090c13050f0c0405031b010e0301020c060405010e03190c172b0b06071e080a 60
    0x1d0200304542000800b40c0781000348048203150590744488a6031001034066960030400c607950410708010302181d05500c1c03031078807a41080c00461484001c41946522245c0e840a003813440e000303e000e858607101d0b80800000790050050310740f4040e8503409034180100111111442202907330b1040c541d6142c00d041510419a41d1030741d400b000c2000e004500c0e1907611020704010b2424100d40800301ca0107424502c3e80e55086601c0002c0000d60200405142003030b00034142000c55034506050001340408071803e200c41d4000c5000b01b0140751242040c0da0640e40024084d001800c0c41c0d4220b0080c60102a403414100000c03c0f103074081c1c5403002c0c0300034004089401d0181c015031806003000750170f4800d03090649a01d54003c1080034007460b841031004925072034501e00030300c055859043c2502e0a4843c00c0c080c0445000c00a054558a4a2000301c400b2035000700581e0700500010810150845408146454202904120301700005003656a0740103c3d19050b0341d21000e0f2449070721801c02035002201134002264881c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 802792841 1250 802791591 802791683
    0x20c0a15030507080106172d100e040b010e1f0602070302150306310510030b1312050c01020c010f05100e15060c013b0102030609060d 59
    0x9806042c3e440481414603d107a07500d0304038000c00340b036159109007990b00c0110f8003145401e10158141e40c40c1028469121144034919154040110010b0301d0007014941281b00000e580000812054030454100c08804407980c43d00041404610009000366621103101c11034030080ca0407044044007501e420b5005200f95401d51040c0b150342c1b0310803130142c0400c1605004102c51a42c440e109814618184d840007850b41600c140449510303040c0c0d61b42e1032402ca05040800c19841141c10000d41104e000344044a00c42c1c032907101031031240700a800054050001c0d40c3c0c150002c40d010310001c006078114003000603c0d00c0c044141d06421a220041c4025009448809101940d442c909640004e400441404151810f00d2942000c01c035410400540c02650007246078181d0349800c0d4040a00001249000c2001000c030321540001078542c01c240c1c20f4150f90410620603032403030500c00d89108240251022034540c03945010403081d03200c1e00d40212450303e4000c40c001141d02c05060300045807103440c84540200409 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 802794091 1250 802792841 802792847
    0xf03010915050109181e030c1707030306060527010e030604060e06070f09030b060609120c0306070207030b220c08010b0f0f011211091e0a050d081207020c0a15 70
    0x5c600e00c0c1e500301c801c0c000140c00480d203484128100e00600c0e0850105809803440c007617030b10200c042406010120240718500b0182a0b0f04028500640301307550812542e80c442006a409010b90340205844101d0842d040204050484113010350711014180b0700300d01d07203640b00000c2c540401145e0031070b1003548130b6040c1c100781c40303080004581005140c2010003070802140bc0c0103017412094803002d4801c16030f20001c00d07690345528088460341d0f0b501400700c3c806000d502c4403050392182c01811071360013445290000307100e40c1e101240001c10b07682d10250600054652514000641c2c11510f00c4107103105d19034124100050b4a1003450000701486030020910560710340410000d044040d080368015200c1a01c0c924090780d0000c18850351040e66203000481905204040c00107014074010741d6000181070200c1c4441119503103409102c0c080445000316810744440922007024401d0030000e10034030040c8281d414041c001a0380c140c0c84501031040b103105c203550500064121a0303581c000c03100b0381c01a00d0603901c96070f8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 802795341 1250 802794091 802794101
    0xa09080f16060e1f150315020306090a05060d0204020304020303090d12230a051e0307171501020703030c060f140603010e0d320d0213230f03010915050109 68
    0x681e14003c0d0400031036420550043c0d030b4030f4222454110f580c030000c0601001d5010172810140d904800000c00c2440341010400080d48140c80d054861014030300080c0c040c04190058511404000d40f4001400c079083e828440070f500050801c0340d042c0400c0c44081440e4071745040c0350f06039038041c40007030110190f2114081c10240e02150300fa0700b0040642180c81441c2500c030101d5040c581c4078681240c0d10302c1e2200c1007120074445e401d29254251800820b200c465603101420941036031605854144030384075240c00303002000340180346a0258000b4802000800e005810041c0780300d0245a000c80c05c6002c880c449400c448440070700b1030122070f946092200030705003440740300c2d5040d68003c004e003260412403030040d00048102c041a1311070302c20380e80710b02e26255031034250000c004490b0001700c0d1207550850b4210007030b4101840b82e00c1201000c9800113141c82001c0074100700c0706001c00d403460a098041c428800305190790000940c041d07480d40001c00000d0112000c0fa5003510361401c00040550504c03011400703940b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 802796591 1250 802795341 802795361
    0x25091404121b0f0201120e0c03010606020102390105090a030e040203060109140111030c0102030a0e0d0f030515120d0306060f140c070b0708041505030408030a09080f1606 75
    0x4403400c08142c29008440b0744842d440d0750000940341a03003640d440125203c15000d2891160182404030020240c02d00203450b40010748114001d10440341c54500407404c0380204102e59000000001c0c00f980394216449940b000c0480ca00c85d154001400d5031509400d5481c01d03030700d0150550002a18000389a070046014880c4803048030190f1650800000007011000c0301d0161602c460700c000c0102805a0240701c0034400c4d6002c0348260382d180c5207206240f50003900122110300c5002e040c40a40c4034a100040340151810010b41c6520307088a40714601103008110041440300303d161440a0310026540b000d02003d240411003000f0b0609800fa04c00050945445a1180040c454140c0ca0702c09610b801000f4400381ca140d060079103803101414a419860800c0542c0101d5820600280c0b40c003c0c444007400400030780e032846e0102d04203115a401c0450f11403004540140285106001080c0d00003126002420000d008041050034080090400c0340c05501550900c005c04800c07584490811203036002d13031f40100d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 802797841 1250 802796591 802796597
    0x110a0909020f0912061006081312051611090906070f0507020f040e0d0909020a021b0d02040501062303070807030239010e030f09010503100b161109092509140412 71
    0x81c140f041c40005960000309004045040101a41018510410035217540c1e51038002e5000d050043350411710402040c94940d1409110203900080d6900b42c0090181d0003000c842d606d00614280685045807180c02c0f241d0100c0e4405c016983c15400355a6034010703507618601c030802400b03441180b19005802480300b40d109000480c010301200c1b640d00e8001c180d9203c8038022131564080382020f8400030312aa484070078001e501620b018000b050442d40030f8805124a02010f4541000c1180407420020b9400100c0b021b000148041c000194854420b8002d00100c2240c1001505038042a0070350044841400c013280c10441c0c00c41c0b55488414509000b801e110b1032807200a5864001c008610307540c5d038401c1c1035429040c07020002c04a414142460400d00040080d4600d00e41c80398810002c028501c0b0701900c007038682034902c0860b010145007041c00c3da4001c05034a4010300f9034200c00d494210a404540c071a1f2603101c080f01100041110b11400350640d0411420101c81c01403400e8600154004551f0f0300020030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 802799091 1250 802797841 802797857
    0xf0f0f020d2406270605090f180f211c05060406050604030f06021c020a030c03050106111c210c02121201050d060b040f0f110a0909020f0912061006 65
    0x40d132030380b0300003041c260350b80c1004440300c0c0900a03407100b002d40701541c005c58100c041c1a04104802d00c141c41c020f0b002d144400c450a14405032038070055030300c2010403500c0c2426040802c03010541e41d045502c80117540481c10350f082c00c2404250025203034036840e80e81c501c1e0303984c0c48400b040414074051042501520040382c910f804e090541e280c90b22940011030000744030a42c0001e41d00e0f0307140c06000c004103444d09925010b6551700744001c0f005000c1e01000b0040c001180c101070002c507074a8000d02002c001390765440004c05154000044081125404642c0541441001c03110203680348940740c00c907111240c95020214507a555507200a10b040c80d1a6000d4900764821f004421986050352415811542e0440d04601351050a040510080c412610002d80c01803502d0270707030130b1450801d070049956240010010030000003560300415a074070a4151800c002034084d5014000304a45074003501d10002c1c05481e0904058607180400c42c418840003160308143d000c0010002d14640702282080948558944884 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 802800341 1250 802799091 802799099
    0x1b060a090312020a0507020339090402041515090806010b130b130b1209010c02010204051302030a0b0d03020622020f010c05160b0405010201050606070f0f0f020d2406 73
    0x10b0a115544070040d5607030002004c8054511510903110341c650000c051703d0130907408400310b103080d8010a5104100b01d512440700b41039107414007180f47c24101d000d41031202581d215400c0000074040c034203005070030104000010690b1a80e2204403008503019031100c481c4941010b03401c41c81c003001640013000e40b41080203001741d8082c03180040c030101c5402403603094641d0300c0401801a42e85241d000312500b00c1c4045914010341281d0f0707208901601040c0000c00501001da281242130344a00d0207403e420101803003000003e428140e004661008030910000b513600d01d144002441082ca01000780c00580c070000a01044850788501c42000e03e5919940003a03001942d408600e200d04403610290501551001031400c2c0002808030814200700034020762003164481e00f41480540050061034010361030600050b0356410241d0807100c03034580000545070600e80315595007442c0e40c0380c840116807144a42940c480143c441240406d41548a1841481042c0e4140e070308103130343c4164120861603075050040c104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 802801591 1250 802800341 802800347
    0x1214060c090906240f0d0230090c220603030c02120a030e01050703031e021903060f03060e0304081002090906180406020d020906210c0f0f1606021b060a0903 69
    0xe4000001e4907451034850a0590140005000d00c0456100560000074516051258609000c13115100c00da980480780c8013010f00484036401c115409d031007981c481c9190341824a480c0351000b00100701da40d851380c21b0b000c118810000340c0d0056403044003c122130b03001150444ca400018a011203034200d008110f100c0c00398030000c080341c208100c400d0601c03134005002c0060510076000000402880c1c01000600d07005141401c00940c003600c060860f0031800c1c1c6c0d0042c2031318400c2c00f03400b08071028011741c1642c45003036446060041800100c0304045200802001070354100c14005070038104600507006031600f0040d01404408100105414821800c034003031410302c01042040160440d401680058685020404400091251b008103540c80440850380250080300d06100402641c01c14100c40074617141d030240341e01e8602034100c1102c007016003846000c0008030014003810b140e0303042c40042e0001e40c20070307280c0c3c0040368002008080d80100c000d0704001c485004100264000001c20700070032500407961401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 802802841 1250 802801591 802801639
    0x605031b011403091005040c050316050a080c01140901021507050414040b0627030a080c070906050a06030c0e130f0606050c0d03051302091f0b09010503011214060c090906 75
    0x910605e82c2e40ea00400c080c412034980c080c0203000d010301110a581142c4110031810183c0303110322440303400075140104000c00003040c1001c0318003040e100c050380490442c0c803007005608000c050a0441c0310b01e140c01d40e801031841349980d00130340c155201c4030b9446083c49961045880003d54603405641011a5085251102c0d01202c0358076902e101c0142220300f01d052405613032815644041d51620420459200b405203500084c100e15190340e003121181c580e140b1103081915083d1244a900c081d0110b020401c890185c1c0245401d480300d0300d403201c1e2400321750000070002c1c04104011681644d898014540003400d602c2503101400e1681011820414042c0c2c160356035042c442c01810805444101255015000d034142d0070f102940200000c0c401e2400007d440012320548400b4520340c00600d1000500d010401d01b00d6040031410707900c4078a5607081000a9440c0d5602c00802c90314421000c00d01c3d03110060500ca2140208a003034082c2d070f030760b8a02004100f100310b400350a0b14411100200508041c000b20011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 802804091 1250 802802841 802802863
    0x2f03070e06060904060b04260a020603010506070809030303010f230927060903130b03060603010b09010c06060b0d140915190921020f0601090f0605031b01140309 71
    0x4169643d000080214020700810b0b07024000102002c1b80120700000d0400001202e00341070310820302e0070480c40c21881da4a00200e180a500984100010300290900c03500404c402401011031610303100c082000b181c5582c6c4244e12400040c0e091600900032000c5030445c0300b400328941c8400c88140817a4400144107500701030125070b018800307090b01910501120842c07050400e40d0a00f039031000e1811a14482d1294030061420700c0c10400500c01140f01c18140c8141ca0294101804040c1180c0c2042e80300000b42d1700095140c1d0601580e104420300140c0076004120203055110002034032801a0b0b00100259119804200c4e0364400420400c4140b04000038078081c03200e080c20380d111407521b84109100c1006c3c45824102055401c4c2482102802814002c0301094140a40886e129001c0c0e06401ca0702c0e41942d9130b01034071540010004000060f030300d40060607a581284070000b901070f07840c00003d1400c8003241000b049108000d41d08600c0d9a005440040c1c0e048004a08a00e54a4824a010344400c9090b003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 802805341 1250 802804091 802804099
    0x2010213150c0506041b050105190f20070303300902150d0b130b010c060908090a0305010f0e030a0f080403121d010e070518090a2f03070e06 62
    0x91010421803103a200409490b0300003091312424100f034244010251348030511000103060740c0ea0000f0f81940b00d84100e4101c503c01c40c01c4404138140d030800c201c0e02c40c161686260304002c00c04078200e00500c030807000c849003101c9507401420074a25515001d000c9070350001e080141203020040583d100300d50300302484c0c0441014103000030745c03030a203100084c5543d1029400d2400390342e0110750914001160390110b142d031201100c1010303010702240c4a09040e62505104c050000340c4142190f400207141d500210006481400001d0410641402113100c8940eaa403050340c03107139124104520003a80b2845540341000b140400386103400e00f0306038094920803081c403000c0104a14200081d00341489800c0c0301c8015000300c0303014031064805500001e0302e51040c1e10100c0680d4a040f840301d00e810000188001254406072102a550424002c00c04440d40c2c01801c0d0b8400b405600c41c5070700003d01c082040380c0c040760b412100000000c5800c109801c0e501600810034003940c01a6424015450001c1090380c0c0308600700c0d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 802806591 1250 802805341 802805369
    0xb10051b010e060103050703060e0c0f040f060b0d02280c03050a030603021801090537020c06070f02060901020711130f050405071404050f0a0510080f07060305010602010213 76
    0x480941c010821284550001c2c0602030001c003c20502040010807a8001d50082c03104141042d1001e8403046030250840d03001e903051150454505042e00b040440e000f6404000413481c0e503511840000d940103541e0700c0213007a8002001100c003211440c4280014940800800c251840703c1005001c030745141c2005014440081140c1907014402d0304200c014581c0036046e00321262481a410710101028080c1c407804604202c0082c0000c003658240800524828000081c200c80c505009000015500c645410741d41c0c00300f2141010b41c00c2007118501413840c82d030350108022543e10000341015006441d004159004100e0070021942225511080350340480341d4400d05040d00c413000380100030040c00c80b0b2030141810100b20a0040102c2c5103000c8941c140000c0103011502000c2108031a0200d130380012194100c00031400e244010360140f64850740509480c01216110081c15107040341c1c41801c01c0840c1d22050003030041c5580342c002d16005000d540025403c01c0b00e4560446584055806403103084005c03a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 802807841 1250 802806591 802806637
    0x60324080a062f1b191407030f050604051c081b04080f060114040204030503121b070804093602041e0f0c1701090506130204080109020102010b1005 65
    0x40c40c0744484043d400494504400c0810605492034000341c20b0701e8a010741c4010107160400c00403a904107038400d403988500a00c4295a0391b02882d0140c03001140170303882047c8002c000034105481c40b4000c2c42c0684000c14251400c1d01d4054034044142e040003240d001c00010b103108a0b9086078441e9004107041d00e00b94000390000001240600595104482c2d034851900c0c110b001c0f900126556060300c0d50f511507544084403010078081a48500d2000a01e180d0041180e41c111040541c1010f804c2802e8451001c200000113213403881c00d411111b400d8401d6280054200010411440741c00042143e1400d040c00a100044201d110f62004c0c00903c82240041410f07001155125445084443c0c0d00000d10071410b40340141d403100802800c0400d0800b545400380328201d0074002c241d50210f0f1042d1040f5040c241e824005804081d14015054942000c00910425003411310b43c00a040902401000000c010940740002420b5a16548007240214904100d01c0401d50b4030800701c0e9100103c40703105140901e00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 802809091 1250 802807841 802807871
    0xa0e090c13090f1820090c1803160e01080d08012610061203200c0607081c05060405160504210c120311010c020304030314090a060324080a06 62
    0x251320003201c182d4248083d030324100a980c031650b088418031440c0c6801004d007250f052080b0b00009490700e50b0038080900c4805204500d074070480c40c41d00c00182c01c4d04e40c1a102607101c030854180030381203003031208802001880f0004042120f60000105403900921b254500b12811040c1031000d9885008044952000301d0705078020801d17600c8402413241d08010f090f80c2c80b4640d008078031102008500246080c08042d40d5001405580144610171001030003181c8100010041c4a81c40803500f191604d10510a20030500325215805440c848404004281498013000704000c41b000100000780000c145940302c02a16888016a0700b91800790041452840c0d19413482e00a50207243e078020041c4440020110b880d0000d1020f481c44648a0340340c8c020285188605982030f82c014141e0040164024402000401c0c843c03a002c500c0c1c040c114100b030b440c1080c10400b054001800750402c0f404680c0b640400c000701c01812403a01c080080e500005407045040242c1c441e211300c603601c0c1c09040d142e21045c4003482855 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 802810341 1250 802809091 802809101
    0x20c010504150c0c0e01091404150e07080609070f0501110d14090a09020a0e030d0e010e041d010c0f1403010302090414030c0c0103180803070f140a0e090c13090f 71
    0x14100c4c0610b07982c4ca9454110428040b0240a00f0302c03014100146603003c86240c240c600d02660380580008942c0641142c410010524a030245415100740030001035003120a0100c5c60103941c1d0b80000d0013449040c081c6888254003a90700080c10040c81c1010312104440204180f081521035240040b400c0281921540300c6001d61811541c2c058846800055034188a500400c041c84c0103031956280840c00104064072035080741003420209003e1780d002205913204040d01c1c0c045410040c00040d00c031241e8240c0c0e058411462080e0903103690340302c2150f40416002900e0800d035140c0e529158800c0d60340c41c4480c0c0d08600040c030009021390042d201203001c1101c01a048100c0219500c1201e0f126003d0809840d80e410b9450769890109103001c90401134146000451450300b50072040305440c60300c5a01088a00c40c9501030702804010802e4a400300310b54201c07000b01200519503607914459000001013005040c405481894062400c106515010180400314012102c10f5080000c24401e46520200504 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 802811591 1250 802810341 802810343
    0x3070f0606031106031303181509180203090303041e062d200f0f12180105040c06050a020c1c020901090e060412021207080c1603030e210a0b04030807020c010504150c 73
    0x66841d10302c8501c460b80300034610702f00c0b410341402c0500160fa02e0001d000f00c0c4029500070900da0810000540410003a554024203407600f65006645411251911002c5403072140541039014000c1d1894171505509152816031004075040c104044d180d0508546020300c0d0607681458041c1004c80c0b501064080307841a101c810300400905681c401c04403d082c3d40121044603041e040044c0c41c000040c4500051040d03a1007103500491062080d820b1030801d480790780007095600118400c0d45482d564079140d500800c040c00c1680b04801182c214507104015007840141c000303214040ca4911243e41c0041d00098035900190030540407142d411100b0350807414114136034a450505d110020b00a4100000507000300504e0000d01c0c01d69804a2040a14031107400e038500c009000134890280b400700c64a484210382ca04004d60201002900310301012480c20075045200540c0c1e0903015004000925410403902c0d90700512a2016001c41c0864500103400350046001d1380b035034034100104400c41c0c6070090610304202 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 802812841 1250 802811591 802811609
    0x160809010b062b2406020f100207230f0f06040b0103120c051603060e0f0a02040b040f140f060d0b040303020f0c010231050105091203070f060603110603130318 70
    0x10030110024407500c40300e400b852813203020032600196842c03020076500e0342d0501000c082d050004a081c0800003a4000120a0300d4020084110070394942c2100c03c0070030924180000b90014030318506001d401e1200350b01086545801c10700820001031800780d03101c0d0650742c0c408485000a480802d040390f00cad0032016401066071243da0402014a000b620000b400c485c401c400c00c0c802140340e0344140b038803255544800c45241c1e0090fa440d00c014900350b001008000006080028100c4088000009035104906070f0000703405a201070003020070003110b02980c80141503a480060710794544c2d506124410080000d000c15034042040d0301e031a02c500044881300280d10000b95203502c07103460781400c980590840031400d0b140e0444e42c1100000326424203030172902e05031192418420b11100303118040b00034950500c800d000801030400000c000900d0403841a000302c0000610310309602c2c050342c9101070310301d844d449000140104103030f40403488002c840055052602403240d400100320180000301c682c00240013 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 802814091 1250 802812841 802812851
    0x1003140405010905060109020c3708030411030a0c17070e04053016020307030206040308120907050d1e0203100c120506030309190509160809010b062b 66
    0x14000c0540080f440c660040090f0340d40c6036030710300c1e03800220310070058280d0054005000c00004400103440450141821903007001c21071031403046040e0004004201101d51507800710a01c01803000010380311452040540081880708501c1e203894013012064424007801c0401121100704e0801d05010315001041c0c4500034000c58106441c14603200c440d641c085004a19011030b03242e4220f00400c984600790203101c9581813401d070307002c00003040d00410714006a0300740c0700c1e00e8030010052b25220000c0000314010f1041c0b0b86c0b5074901d80d008444030000030700400c10a03031001c0401d02c9155103c0394120001b42d448000c1c0c0e203059540d01032414000c5182ea0b00654180194007201c00280003a070402c540144050f56030310703102886c101c00030040b5003090710305c55015030052089001505180080d000b4540021250303194544c3d540d40001c060f910115000d071140512018811101034001203c5504000000000d12000d141c3c0400300303805004c2c101036441c3c07031505800c4010409121601c0400f60700ca400d102480 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 802815341 1250 802814091 802814093
    0x30519120c0f1205072f1606110309031b0301230601021e0703031809020301122906060f0d02030c18060c0322081b040501140f10031404 60
    0xa4602041c055601050050b583c03c0040c80c954459a0710914103a120305185130304c0113481480009032a60004d0800c82195154002043d040100c49041802c1044608089003070100c01403460a51104040c9141c2c410702c0001035556010032240304c0c00780a03161a220301c41c2d100303000a0241c80744e40d10421010030350f24101c85940c0c8955036000e00c110381c00e07021035074000030130202c603c447c3c213008035030075000e410241e414000039208280d0f40c5241d200e1065980704a80d1204081c00c1207034400e920803016800403a87c0394080001400e020460f2511840c07900101329443c81c81c0780c44285000700030610607a00000c40d030007101d00d0281030b1418036480c11002c640b07903d00920092480c5e480110748004020080c01541e407a4130700802150341c1c00500001440c02c0c00348044020180916682600a00103c8160080340030041001120b51506103212180300181d41d00050108803034040c7c0045011102c0c031141030b901074950102c5aa41d151013550a0115403c19050450080c0140040110717882c0c0e0801c03c0c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 802816591 1250 802815341 802815347
    0x41a070206010f170309060307020a050d0e09010f060f030c0504080d0804050606030604030c060e12160308070810030b090309041503031103090901260d111207030519120c 75
    0x181620040c030314a003c2070703031511040d0040c0348010703001110640c0100321208079410400e010b1900039840d4012940d1007220f5994403400c040d03080c2001e200159400040d00c00515003031450364014004209160095410080c00a000d021042e80f1001816269220a4211031203402228002d1600f01c0c1034401021442400502d944025603040d1454401d420101b2118034003c02d805000720380c551a814120703940f0b9950701000d4000c540c0b100641d8043e6048920301a000300c0000c0100005545c08502c2c024004d103000340808034090309100800c400d0700c0420600c020042d5502007070301d030003902801e515503900d034615240d813041240741034009041c1000c900c01d181c07501c1030f0700301603a10a032031b00740c004a980111665a03001d600009a800042c003401000340a46440c650071048040405440944030302c8003a144c40c1ca80211140400180d03a540c0706d4651030001e001240140e02103016040c9041c0c0c607034600402c14016100524101d49509000801c140e0061110719609081a8801e0000f60018000a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 802817841 1250 802816591 802816603
    0x6120d020f011104060c030c11041407170601080613020c0f010905100b0619051b25051005030705041a0703030c0c0b1602160f0305070e041109041a0702 67
    0x440703190308201c1c1801c00c076402441621305546056a9030701c02450789440c1100e05110621060390801246001004292100d000c0c1405134070448c11038404a0609100041043c0d00c082800805c0c0b008880500c103051b03a0254035203401250880d101c10301e801ca4079030300380c00034410442d640640d0310036103450505107030041d0405442c050049050303035a841032110b842c4041e684071a081c4c0b80d0010003001010b454404103032102040c00c1452a04e0b500781500364601c1070074500c0c80040e0100c0c9601c000203440030741880f0a82c07070b610120810741c00c1003260700c4c240109d410382406400d04000d0203000301c0011441c520070000c1e070740140029070002d0203110111200f44006d03404201d0a070000780c185207080e015503014125442219600045003060b030f070f803807400c030040440081e80c80c24110700410403c0765104a10617000c201401920340c1602d5a1403851400d00c2c6003c4903039200d45070000ca0f040401c03010914010402c99052401c1d51001001d81e201d14110030f00320300c8906421500404d0005100c21982e000440b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 802819091 1250 802817841 802817863
    0x306120f0c011116090f0b060703120513080f0702031507030c02010513200319061415030a0b06011e050a080a1a042c060f24010806120d02 61
    0x905144410070410a603c0d03510804c0800d40c3c0e096241010044640e80740e010314000d038140320740018024203010005041d80c1c0a9101640014100c10102e031800c48076101d45034001d41088188590440e0700d5030741256a0049140e42c0c018010046480070540d10706010014a10309803000e01c12451910b1000034004008051306070b80198681000504117410618080c82c0c1542c002c07007c01417500314bc0c00070718400c0e000700004030b40501074a07407403a503640f212070142e16800f44107203004035031170003110303900052040c001707101d00c940e9200060481450784011404807035140d00010703032200540c0d540005130b81c101043c110307849400110154082206a01a029011070041a030b00e200301074891114420548292828075a04c00f642c250344060241b0b4a6404006000c071070b1710800d40d10b1016141c02c8000180f070802d030300700650081c40400280e910110030540e03204005044043c0658100060032000d601121a8141031203c800c020407201d50b550b4000071618003840080b2087c00140603170094032444079180c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 802820341 1250 802819091 802819097
    0x309010e010c120e071707080111030103020603061203070209040305071a0601050f0a1806020a050d1706011b0501051503390105040b040b030f010510140306120f0c01 73
    0x8010410020306029640203040c1e1595402001c8000402510041140c20810030040c4144c100c001031440000b0344941e054800003000c0c0c40d0442c9094681420348030540380d803000c86c01c8108014001aa942000d9030b03008407003640c0c03020030500e554401c20725620400300043d5100d2903543c01c000c01c040d800401003001a01c9165040041c0c04030002e242c000e5030083c4c60881c08144280541080b803481e05c03015160f028030901d400103074003ca1860b00200d29249412440058114905100a0100400400c80d1010413441c0c088070b0b101e80310010300e200761805032642d410407070805030555045426031884c5002541080080005003041013214510340003040d082c80c06401001c2941d1a001c07000741078140d45074240680d0071440500c04681e65502c0448840d5141844000e00011400c0141070000e400540080e40c1c2a41eaa070801a03450380c50784030164006481a2401161407000961101c84a080598a0758840380c880d260200090380d440000304074081c06108001d4110320071000051000c00d0060b00380c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 802821591 1250 802820341 802820351
    0x30c07033605060307020d0509030109020d0c0608160219060b1e010e0301090c05190e07020f120f121b0a090e090604020d1707140303150307080a0215040b040b030901 73
    0x3d00015000c2245d01c0360240c1c10650340d150141e4003650040ca01d0f14002800080c4145083d4001a241c01c0d8141058642180f140030510050f9008800c40381c10914903210351107a00c500000003550341c0101040710840f030b19520900c0c400c01200c1e0308032665480c401480050f420705010481102c0414546003140000c0c2c80705114403540c01c0c184100e190031600000315540c03090505040c01910500b038241e0100f030204c03043c00000c2e07101c0c201134680d018003e540e020b80b601410400d9407a2409001c504d10f40b88070351041003500b040880d14021509410000804441503075030b41c009040480902509041164030006840d040a940c440004000c1c0d50a00034600801c0d110b003d50141e803644115030003900460900f1001010400704809481c0644060709903e1800480303035109007034090780390303901440c0d0780c404010f211903151948083e60310008154020504649400030b0142d44000340c14020b800344d0280907401e0501c0210b0303422038020741754509030665243e030f88034540e2120307034812220000306511708 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 802822841 1250 802821591 802821599
    0xc020901050108070c1e05061305150f0403030c092c0a0e0706081302041a120105070206070e2407020a090b01091710050702030a02071406030c070336 66
    0x7030f601e414002e14059540000d010210b42d03400345550320f901e8001c0100f9540c824039000160302006010710509503c20070000480c2240390080c50000c6103480304201c50845000c10900303090700c607440e40e4419054070340400c444110600a84081803640c002402a50143c140d1042042088115065825140a94042e00c1d90307503140b02c204440f00700071000d2007900b1200c82000310f544294800b50b049407070010203894000107540028202c1c0d0302580141041c4d03e9104205289240151000082c0450840203011a140006000703480d203100401c000240541c40030000006d4584442800c0c1003840300c05000090548030300b441615400c8207500702d10528808030041041140c50040700e420700c40685880c88124184268100001d00084c803400b950b200b40491a2104a4940202030140d54281c025596580c542c20009003410f40741d41203c14019803802c20014107841c0c40f41101e41c02680101c50b241c441e18035160031125840f41c0e082642032110b420b4003448800d48110802e4040e1a044e000360600e00355a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 802824091 1250 802822841 802822847
    0x5073b090603120f040e13110105160605130f0b011403030c0606040911030d092d03080f04080f101802090609040213090b0a05090f0d03090501060f03030c0209010501 73
    0x112541501034000a007040b07110f80108019246000b81c0c00c149a050a4440a0101e01484c00300c5610b0305021508500034203021101e88035000c81c210030b103006031401064400c2509603018920000780600e554800090301d01c10903490001d002940140580e003405605d04000d038030f4000a008031100c80504561f80282803500104440ba0b10104201070700e1980d9030f060401c0002c4c911000306440030040e90381c0c02040d0355818080000305480580324802e2a50600303a51a0021303101b80302c12515440d240d0f05000e100c0c031015205900f140d900040c019a110000010601c940c0101e5200e4145845100b070f68040c46640420341c2160a003254500304aa082e207064400101c0d091030002075000101000070601c1e81c14004440c5074000d0001e081c201174280c1052200084508620060301c185020f02c09224040307415000b425000b50b490f000508034441810059610340d00c102141400b4903564010600402000390002402800141d9031004656074a08002d0000e42c01d03103c00324480c1f10110000300741580 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 802825341 1250 802824091 802824109
    0x21905030a170f0a03090b0105061309110708131d010e01051c0203060a0218030a0302060c0d140f040203010e060708010612090602070309031506030f0605073b 70
    0x1001412845100d494035511007001050091010504100ea4184552001c0013003038000c5840c2e45c0011180781d941000c0b443c401046c0c1103030f03100c1c130801c01022038000d040c09400303c15110412000540d1544c2d44400300340a01c5409401804250040b0380304c0e482280c0a0411001c90303541d480da160510030416104190f10800340118030b41121600e00510947c1442c0c1c03a00c46220140d107507004103a204d5500080d25003c021185810140c0c0c000800d9000055240c0924003042c1d0180c0041a880403141e4010752140e200504044c00a4030100d10811103405541000e8401054102d2030401410400c00c01000010200c034241d01075828040917421905001405512504981c1c0e5408041c0c0d003000e4040716078410014440084640701c01032030001c1203203132008141c8280300740c861141c0c80d807952401d4406500074442d21980ca5241034010008200c1c1041d8188040d544040c0c00620356854400a64400701c000b40000048100700300c0d6014115001200f81c0143c101c6002d01100c12140c40d010022900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 802826591 1250 802825341 802825349
    0x2040513020102100e2d060a0b040b031902010509010c24050c09090105060306010203040803040b0d0b010207030305181c05010e163b0408180d0206180301020d090c030219 75
    0x54010801b440c01040d0070090140110441e5034641c0c0680038007407060307245c41816544008055078034140d41003a460035208281020000341c0180000d40051090034003510f550443c041e040c03010002e484015030b846900e260307200795031040c00c0c159141c44043d0400c5111030b5034840d048040346408049155281c0390003d4800c3c0920003040142c40381e090100380b000a80001d004141035100030700c00441c0500e0184060030161182c078040395101c0f00700011800030b80f119040442d041d074215042c28408644c0c8441196940440b0240c4080c0c00c030040350100310301c0003c420000300d00304c81081140c2c0c1080410741100d460420700b48200d410420341040032402440c4944a20741c01e503a0041040c03403455052a929401060a100904012084031a007110a0460844003140c440ca000030308020f911186201c0030503100c0054501c103076601402c1d03020601a20840950342c8020f54002c508040e6640d094040741c0f090b00d50340d5014040d0b024640b82c4840110b1035800308034401c40084016800303100580390302c1000c80d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 802827841 1250 802826591 802826593
    0xd030f14030609070c0201030b03101a040203010b030a0207050a060e010c0909050606040e090a0611070c0f1208070c03020402130f0803090102060f0405011413060e2d03040302040513020102100e 85
    0x75456020342030350768446104d006c038103143c0c072040c0d001d540c4d503000d0014079550348400d00007040a4a007960489111460343c59000c0c441d61060005002d00000f203400d41c0e81c064860070005a0741c5180d814950b241003061032000303140a0414842e0182c0000c113420a00c840c1405444044515407951180c1c1c00f52042103401c20742044083c0010800801060703c3c081e080049081994001506900c513501a10745900f51040c45004c00a80c420030040940e1443d0020005084000e5105003415800d1486d0403c000b40605015800318840d010300440101c1c882c0190341c020030465855020fa4007080f100d100340c1c440c0311001d920350340002801403000f008650503904141c0c040c18031075071072100000341e02c10094003d81d0300e503582d0f80402c42000c0c090050680a402411010080b03a030710381c40d10b00d040d210280d842407130580103070090980f0200440811040100074500c0e0703640540a9030b6109245014592029501500740414800c0c0b05200181a402c1c1074000e071b003501d8541100c2c040074010b0b21110402e08582d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 802829091 1250 802827841 802827859
    0x28061403070e071b0c03050303040b070207051c03180f050a0e0c03040f1a040602090913030e10020f07170c0d242c010c0c0203030d0f0207020d030f140306 68
    0x1500d0300c01e13888000910800781d01c0b80c002403a55101c41d070206000ba0812581d55000200b44000e02c402c00d262954440743c548010190300c0c0c1800042500703607829184040d5900100441001014040c440300d150813070441d50b141d094580e03a0405079050010764418940108084240401e05c4141041130030f10031001e4070803003442c540b11079940d001e02151841042d901804504140c80b02d41c41c2c0d000d103007805070780034500c00350b102c6042a0801c1030103000030b090340b20300104a07609900003c0e048200c00182150448101c03190041c03140c000d81c00c064450805007054012600042007040d400700005100f03041100440d5000007000083c041852200c0d81c020700310b40c1e6064204060181d034508044007410840c48042410203265050741d000d4039190b0448420009003541f80ca001140c24450004010f80c145400313102c031850790700440d480b0701c00c1210a6422544a021030a900c203265011200c1c9540c3c0505100701d01002c6041c0105103d0b01010f00700c0000c0c078284030451034440080160307405614020308900b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 802830341 1250 802829091 802829101
    0x1012141b010f0c110609120a0b0403202e11030a0606050c060c0702032109090c0415110f07030807050d051c05090c130e0111030c1228061403070e 64
    0x1e140e4228201c01e1f0b62199104d84195040c020501500c07031141d1003a001100d403402c161401410214039241e03180c070365800c004ca406400f001c002038452149803a0038100c2e200400c01d24895540741051900340040340d401e00903034031200f8146000071417140b009001c04010f00d03a11010300305d030548540c0384a1728160f404680850440351241c4010f0580b41c0c8020700300c80350410207a48e15910384140c19204000300d50041080501030801c130f0300007584403103a0003803540f4281c10100c0e0720288200c1c070070b034a0081208070800990050401c104200b6100800e00c00c448440e50359180c0111107600c800e00032107803802071100c41e502550040040d650701010000e41c0e82400c200c20700c901002044001c00b400e15911441c0e02d008680d4039003103000d0400d09030341c04001c1401c00000d8040b6080d0381d000b0b01e094400f04030030070410020001450558428083c000c085031036070384448034903580c00188500c0c550255030390a81810360840095019104550303003c006400d1f20618081019140c02031031141c0c114061080000070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 802831591 1250 802830341 802830349
    0xf030c06030a061a030405010f051b0906250210020106050603041709120706020f06040b06150c0d0801090c050309120f0c070f080606091012141b010f0c11 68
    0x50303480405a00000343d01640c544654044484a04210341d418070b000081c881817013030a000390110f40e0007140302031099042484226205220248905090041c00300b04000241e0396002103501111141d18520b41c071000e0482640b46404000c2c00c124440d00d551200d0002050042c00344901700c4800030301031410344e600c2c1c0c2c444078100d40c00c1c5011840f81e0801042144841d60719111b05a0030003141c1d42c001c20800d814124081e02e0b000c2c0074103103000359034080810040010044100b0990101c0c0542e4041d500c0a00c20503100781c140503804010300036004049a20029035807210701e0904071000300c4010f005441d0500c2064803544010b03200e4001c50341261015047c5c4030740d50002008514419044a454003401640301c0f814100c03a6000104a25a0a9020480040e00700502a042002121000040e007072102040345001401d100b420184860154802c1c140502030059068840d0424140c0b030840d242008424200c40a00000501080e504190880600c0c443e0043c14007161380f1008605600c0803d400700 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 802832841 1250 802831591 802831597
    0x307260402040f020d1d0607141c1413151416090f0b040e0703060f1e0906170d0305090312091606120b03030a090302040914030301150e0f030c06 64
    0x701101980801003131403580c1c028407a075403c856181024006d0210305c00541400c05001901e110104440409401c0c440c90742601168050303160044203118000c01804450050000c0401e13803481e011992040100030707042d4000f0512414810120000040780c0303124444110790344081560006a2200001401c9404a6401c0150841070b428407540c0e8a03542c94203106468034940090328011800b0a00304989500e0701e90302c0ea000700e400e0030b0600180b818000890505400c43c4601c042c80880400290450038105100102510004078140201c0781c07260508840412215600c0c0060700c40c2d12a02d606213031003031086074051103044000d11b2900f654049081c0500001400c0c22071140034a400003030002a50b007050000034400d0785c13030751690380c0c40948031481103901881807180290410400c0040d1203610155840640e50304441c002951541d5041c410360078018044002040c0c4800000411461118050054001c0550703542d0240b0482e0355051002c02580b00e14141c0d00f581c02001c09000030301e01103001e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 802834091 1250 802832841 802832861
    0xc21050f09030109020901080a020f0301110a05130806010b070201231603120c03050105030d0e030a03031d0a0c1a070b041e0602040e06090a151a091203030726040204 73
    0x85101300c3c1d9a00051b400c42e05c2a03108500a52000252000318204903500020401089000f0001114861941d86051150843c0c20b400c1280003d01010034003840b03464840600754002c00c8504641e129162511903610152040c0e005c00c421101c01004c00e80d02c0141548802d03103080f202130501d803580000404401007203504400780841c4058070100c0164503c00d050000081d0b580119907545410141803c0203007031490801048211421407440343c80028400c10020351620b03000034910101c04407402e12030320264407410103002c0e002400c024404449070300c03800c0d00c1003213068045817040c20306000c0c0c075407141010040c905c01d4000009804244240c2e801c2d0004418080d42a0004040d9540d4504a82c8160880c000000104042c0511030811540840e0b00403040841040307903140c2401118403401d410b00c6070440d000900c1d1032071100101440e00740d9406000290241e43d0511031b06001c10703100d400031122040009c1110400d0400204ca51900c004030701441510311030580c8858080c04050112121 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 802835341 1250 802834091 802834093
    0x1e05041d160312140319090203030a1e020703030c0813120803041e020112090503040b0c01020301140411031b0f0307030e010f021e07210c21050f0903 66
    0x30588003030201441040507184160580103000340c10340c6003540e003400c6820707422030411880c0e140310f48800071102d003107a4100f40000310703502040c4108400305000c1c001c00c1c407009415000100b2154400c03a04247d15030200310540e406003500c000400c0c02241c1c0c4249503c006000600030340e003804040b0710490000d00d40c0c0400380c01081c14550310361019196000f01c2d04812100c2100000c1044203200030305800c1d044030803074007070200241034464000030400d003600070078030251640e03ca0195007000303410401c8400030700540004a441da0002c10085000350424810030380b1412035603501150514042c4111207581d42c09096a605588900c2000209a0a2000c05412224003001246e01c038404100c05148a2500365070f000c107042c1e401c030726554203403140c1c50103501b1464014001c5124086003e1203681c11150b051140070f0301ca04407070802d0381c1c00c01800f0800d0b058401c0040c603481c103000c0c0e0242c4c18005032805800c103205001c541081c1c40c002d14511860f2000011014412800800c102d80300070071101600070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 802836591 1250 802835341 802835381
    0x1b030315050406120b06040c1d03010902040e0f0c030c01020706110f1009030f1103030a09030c08030106030501080607080f0105010f05071407061101060b040e060307030f05030703091e0504 83
    0x700800d04072440c42e0403c03121541100500c108200314104e845a02850039941800181e8682c8801342c0704845a000000c1d01e9403107400c50850b162401d50041a07055002002802603940402c840c68690a555040078203034041d14804031440e003000101c944031b102040e4020311030703549080360441e550500c00840c2c1340d1038000c1e17810f440415038040001420b018510b1500084018844c40c2c0606a5000e0082c0081403100420382004103420120070f4982c04030f0840030200d405859407030308580801d403400c4000c01d2510048000b1481c0c1c0c0d4150f1110b4183c0701604210b403c0c9403605030701070301c100c40704841140b21400c09400520940d442038800780c01d009000d04203141807604035036840d036102c1c1181500e81081e9100d10410800694040000341c001c21801000304035080c01d041d0001c2403803003940030302000001141c1c085035541d11708101c02c0c00103540104165203486880c5c901207071a50701c50441540040c9100c03001084c03400c242900c2d4035042c0c900b5403408a0041c80d0009210103403110b03086040c0310314112 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 802837841 1250 802836591 802836599
    0x150a05040c030c06030f0e0613031101020702090117070518011a04080a150506040c090504110f0f0d140601020c21030d0603060609150b0d1d010c02010506011b030315 73
    0x1000f04074018240a88000ca0204a807038038000c11030b42c012105425990100e0203004a4240e0b04000f00c06464051030020b240d2840c00480b00c1c0684100d680094218502800004005180702054204401180300703403035561380d440b41001004002c070441a0044855100104200100da031074020900d030015603014141540c0e280c40c3d60900e407007040256030110884144900c90581c1e48119917110808442c20031001842003401010780d41b05000d418000c0340e03210342c0240c0c5040c4580a81d036107145803d0303030b00daa240c02c90f1360318200c1b90f00016614a500b40c10b18010490151070b0503080761080406034001d20500d5204c2c0100082425254a030305d40004105142042950341400240211100030b1000f00da11461464082c080f54110740c404c510301c510b0b00c40341c451440040402c07a0115455000320700e8542626810040080c010001d003545155418922420b035800c06410908002040760000c11903a521580196190710704044011666920940003900190081d44400303029203983e00ca00c40c0207a21 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 802839091 1250 802837841 802837853
    0xc030c0f03060d1403192102030a06080706050418051608070c050d020d020c0301020a08061207050402070b0f06040c0906054006030b0307033302090a08150a05040c03 73
    0x203021607000c81c03900000b4081003104c030b01e0b100302d1824012510b421040b2414072070b0a9081190400c80c001f02e55600000400e0b10740c00c80b40c00080241c00100c0c203031455030b0340d94507018015a0040c03182000c103040d032450302c0b08048114455039104140d03402ca4084604511503084803481c10040000c1d0900140b00031890202d94100200f07060140c0301e40007001010107081b006032410300c90050151080c0c0c010894402c29541c0044200d81181058800a048500c032018a0f401e2400c0c03600010380040c8045500014089005c200f03900405640c0d0a10945842d04000e1000307640903c923250340412a40482005584d20450040c460584804480305000345590882550020000410134540001c1110078041510446d40c220003050f0354201085900032090200c0c2e01e40c001031001034503104003d240703002c10480b20000001510440003040c1c5a44000c000100e00a4200700311140c061004001d002c2480f110010301e1b0030000c042b4280c14245942c1d102c40400c0501001001151a068070000000000700 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 802840341 1250 802839091 802839113
    0x41203030f0e030c07090203090c040c120504150b0f0f090c130b0a020c1f050f1c0c0e0a08190f0f030e03011811120129090c030c0f03060d 61
    0x1d0042c0650340d40c00b0000d00d00f0303142890903000011018410000e100750307158000f90107009030100750b40c0890510001841542c042081c242e003d0f03000c500b004108010070407880c1100000b1180d1000801074048143e040c040d40142c8040031a80012884000006c585400c48003a0360080405008615148c070b10b0f0324841303d29206034040c9130f41e0b00000c140c1000e0140c0610107850032200540780740071200170010034002144030303603d400c00c2401800200203103010140c004641e810514002c0411b03008100440d2180100305008c5140c0014850240004261400750003002c100c0e01e40d9402000d200300900d089009410160504440080303c1198400028442c0005110554001d459145400c00640241400c1d2071032001c406103125003840030400002c000720302c00c543e0380c641501c452800503201c03a035403401001419820101090007000002080145201c400d00d240310542e203816254407024840e00c0302d07000070f03244404800310910180c06a440010f024582c0501e0007000e001c104c441a0712070052000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 802841591 1250 802840341 802840361
    0x11091305010305060a150308030405100501060c0210140a0806190303020d0909090b040818031c17010f0315060902040b030906130b0a09170408030c070e0c041203030f 73
    0x140c9a90040040c41001d00c00c0707985c07004140c1800d02003220340d070003250301c400b80c18000144461000303c085801d20404000c480c0107550f1200d0304011558550a001d09003410105c42284941002000200c98501c035645130745000b04011001424140c00752811380321405c00074840d07074000481c0d0b01c0c030703800d00041d50342c42500944c0a034000e003114219a030703001022003a40303410100300c1c18104080d800c0059026003441d0761081d0071200c0030303448040342180f01d04119900c1c60001d906206203124660350001000100a504c0e020340c41303800d40415010305404560342c1c02d204240300398003109801c101040ca16255040c5000d034082c13000650503112441c2c0c43c22070b00b050308110a0408007004021005108101d1903800c02c00d8207824280300301d419074542062010051455210f142c643c42140100a50458101e00c0c0031004820035803219100d0814681e260000b0f403222100303104854001a9050300751504a024900c0c03840107925190800350707050504003590f141201003640d07800c5004501c8030144200608a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 802842841 1250 802841591 802841629
    0xf0e0303030705120c07020a21020406081f1a060a170a060303031a030723030601080c0301061a07120909020c0c010f140d0c11121201060503010501121109 68
    0xc1c1c0384d000045048254010b1441c402c07007504010f1040941d495182c41070440707840c1d8840490a07005420350800103120300384000c0d085420600d003c6505100030500010301c0601140c040d4001200c1e030601d0b01a1070104501601c45101075000c0c0321503013013010042000049505041303524400c0b20b4201103142600700c0f190b184c070b00da84120600030941c0c18001c07040911400343d204030404080c0303000281c41e50468400e024412000900703d0164246400080f81c4101e00142519550340e9a051000e0300c4601c000a420711030b503c0c188001c42c42801340500e0940311880190420b060440d90f60300c0da00300d01c00018990f030601120501c000350385a03060004018030202c900c042d20b00007004000250404115070803500910030010090400b007134001e425980c6000a4460109056101b444191529492045409114000d2000803043c000c0c0d680005c0c2104946c07084480c1d0580e070703611412242400203010b91f43c0010301d0810b04501d02178503078110708084460200b2092410084900094042c12058090a05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 802844091 1250 802842841 802842847
    0x60d0b091b0a0e0f2e031407030c0b070219080d02010e0f03161e0f0b0a06060c020103020c070e07020703030801050a03020307051323090d030b100f0e0303030705 71
    0x101501451004000800a880b45820725003401c5032211841d40040000101c0c50302200040c03100007a007002e80102e00c0320036081c2c6a00d41110702c0a2409000b0501050302c8050040070390326101500010101c045a4103c0c203143c0d01c1c1420900101ea15500000040ea0300001d0240082c81e5181018002d100501d1074a0040583d071107012006402c3d141650b400710300c107800955a0240e800310202c122012100083d00b142c0c0c040290346042c00d81c1000a03200221400c1072048134200b0482c402011402c81c034000c0c0611091070b510803083c0820381d451400390702c0015900042e030200550103a0003424044040f201622480340e100c0c04170510a060031501d810061384141c03410070515400400e02409003600740e03483e500050454000c26500d0300c0920a850191074600700c0b0844070109a480390350302d91582e18140740d10b150b0f443c0d0b0007114047c0c00d8640740d502d40104003808441c5402445000d1050002804104a032094254192200b44002043c00300380702441a80300b8056030248002d6100310215141d0300d132 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 802845341 1250 802844091 802844113
    0x50316051911010c170f0a09080304080c090901090212100605044a0a030327020402130b031003030215130818041a0906011d040203060d0b09 62
    0x49030080c1d8041d031441c4501c502407a080401d641012601060700c007030a05540494580c500710602d181d0305203480c5c1401002043e550b014030030382002400c0340340880d92124882500c410303140e5100d104034420800b0380c0d404400800a9800d250312500e40c40202100005940d42d5603801180e1900e001000c4800c282d00040c8003003085502c944a02005408156803c02042258003681441c0740d80d0100700d04c031240301d142e50b24200351240805410300d038081540222000d60299a0082d920080b003042100843d042ca4a0000368071380b521681913100540394100342280149800307000007544091020906807581c1600131032800e6612004601503a2440e0002d0302062440c207009040400c0e6241d03115103105440c0501c45086104082c204400c0d0300029666650700308851102c101280c60000f440c1c0103810446d40340380013a4113141c0c18500f00d20a076044012036540d5001101c0b0742c6924095103481c500d25003000e038242c0c181640915809840500050400c1c1340c1c54880140807401110741306055481307881407503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 802846591 1250 802845341 802845343
    0x6030c0c122c010503012312030d0f0c020c010c0c09060e0a15120b150901090c120c050d05090309040608030d0b100503061909020d02130b1e130305031605 68
    0x1c0820080b9040c04644400400002449484107200320300c20721008640e01200000e05401d14503100c24002c00350940302e4080301030241c894010f0070900c41c0c0249000e8029041038814021180b800c10300368050a10b5140c1c0c0001035401058420056400071a4030b2400b0820200500c80c040c0a007845d501c50074040c1c682100d44005854a02d00c4842c5101200002006140c85c511040b600c01035201d24048030a41d00c400c0081030003642640711a0740030011200000c0d22220a42c8a6928041160b642030381207031100e40d00300180c0719120000390009908103c83c2ca4101180d600c0305800510340420b9a242907804d00c0003400703880c095040704c0601c0d003001810b8811030000c0d200c2c40c1841d28040e03c10b00410380d014580035146010080089019511540d64808030000600f50140903241180045480b1b080060848009400035190001d606010380302c040303a158540c806942040404600a440c5110385c41c4074244103810001c0480300b40c40b403400b03010000500078009010300b500340040022a20380e65003405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 802847841 1250 802846591 802846637
    0x11010c030218030c0108040b041406010b07061a010f18151106072c060c0a030f1107080a0624061d120601050402030717010f0806090f03030106030c0c12 67
    0x1083c03080c0c4c0050616012640c014a941da0b0050308090100015511402c00300d80c00300c1903000388082c070300499002260f018040740c003810125000d80020041d00e4140c14891020814043e1604d0200d00d12071540c9103042e01c102001c24200c00f8a41100e00b001d0390740c014500e000c0180700700050204450302c1121030b4007501008110b51100091515501c0f440014082c0410703039000150810290001c1c8513441035580320517040302d104000220440b104d42495050040c80010310034090000100103442200c2c0450340000c4250907160680d002e84940041551544000c0125001600e0442c2c1601111002c0540c08800d0070020125034941e89100c000700b0030400900c820b0000f119102e441140400342c0718010014003a0f042d550705850050703480d21240c1c420303900196110b80e1306401c4c00c1424008a4410400302002084a02e03140c01c41c1e00980303d40001e26115168403440c2c500e554418801005800d00c240c005032080380c0c142c1040d805103074207a00c44003008111462180003003400000c00300c07641c613440024 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 802849091 1250 802847841 802847887
    0xb0408120702060c0a05070c260d020f150907051008070206060d2001020705040f0207060e062a19080f06010201020f0a080a02040801061d090d09030f0311010c0302 72
    0x78180f03d00d45548150f219010310040601044000318080d400c105001b4140310141120000020300d041e00d01c4800480b10619290580d00360141c10403885c0004e000182080c5c5c00701e400409455176181c560b0440120b00801420490288140c00c40010291079580081d400c00c0503556510290b40352055003c1d02e44000a403017980603114248028010031790301208082e480015004540104900600403031603d2016040079a0003441c0641e0400b03802e2903030b4010243d040c81000103005c0c1986104007541ca4490441ea020394001c180e82c0112428214be00c0d0302ea400403030214181d418401091506070307007880c44070104008900b5007024820b80300d44600201d54000402d04c001d43c40e0004c010601c80c500d014084540040c0b1a00c000403400720402e81e0140d801a000350380003040300340d6442010144044079900198400410a40820004030002c80c003544c500c041c9031901034140c0d2550b5110743c0c0740554180e0940801958560341031800c1c80c01e020740d410310490344c1d03005070321452268020000b50840041c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 802850341 1250 802849091 802849093
    0x30a1b1505250305160c170708010f1107020909030c010203150118030c14010e0315060a0608040b0105060f130f0f0902040305060a021c06030c0f15080a0e0a0b0408120702 75
    0x6002d002070f07444001c98401c0f88180c6414211142c1c50316201c5074040c500d8001299a8088028405030710300e0004103103084407072030002030060460802210302151526140aa9010010040d00c0d016007880714950f904941310208072403400452a900c6401ca0f04203030344542c500300e20040158202c0d83c0c0714038009003100d0403a81075000c06240d50f039900311902d81803080144c1e2421000302148140c3c0150b585c0183d07901c002e02036401080840d040c0c03c0f40800200d41303082c8600040300e00404c2080c4078031851032050384d103e203800d103a69080604011094000c40844040d040c001c2090700d810a1b0160b0005008140307052000c0ca1507410450301003c0c041090704010040d41c81400b0403c04100c00291701908620180303801680c1701c0e80120310034941d4103426080018181402c900108010341c0b908040110791000300c1c02100d407078542c94a2151005100450800105540049203184610307922955416800008507410b010140d030380d13001520001c40c2c040d10701c6c003c08140407240501b180916540040148 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 802851591 1250 802850341 802850407
    0x5070815060901020c0f0312030a0507030c0504120213180b04020307090b06040302041107020a08030c10020715110c10050406150f031106040905090a020109080c030a1b1505 76
    0xb80002d41c2c5989803220244510181d40f030b41e050585052010414140707020903030640d00c0c40d15070302a0015040c20707039521001916120300c1111003489502550140c80c40061902460300c4c1e240c0800030503001441c50300080e0ba94900d100c8108001142810440c1445110b00864600d0036004040c280182a4007600a26060492004d410380d01c4034101e030290f03035048900240c180000c0d050100f041c042c070706009400280c01880801e0f811000000f0780520320400301100c210030f102d1100b000c00c0c0e001c4d44400034001c140241c05a815039100c3d41190300d011040c20910340c10224041360041c81e20000d5108500c0c1c0d255120180014450715020b104613428504008440d21850508500e2400b402172001034112a4541120b110b503507240d5003290700400d0143c00c144264200844415150b2804000c1207010507401c00b000268020085000c14000100401030320402c80c075911102d8114041d03078802c05103540e05440219408a6003242e06c0c514562507134030300717464a80c00c40c250f066000b000f0420b1b03c0600d00301 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 802852841 1250 802851591 802851607
    0x20a0c081f09050a05150114180c16170c010b120319020a151a12030a14271e0a03080d15030308090d080906071808010507081506 57
    0x41c081c0d10010001d0040004070020316080541c00c10f030f40800001e015014124200103100520368034281a00c0d2210519540ca0204001704544848150008480496850002583c901d440c9025122036044010b00c400c110946560f110171400400e0020100c00802040401d0640303000d03c11080540401d403131180241c009102e8150b540d0042c0081e660784c40b409910010030a903c2800b8491035558440e00005d2120154a00e4801030b0a00c14069009120080c1411420303141c02c1000440e4070b9040c2000d5071900d41d40b180c0458031540002d152950290302045500311041d00728010328500481c0391094242e40300f481080000a2400d01d140c9550001481c414004907aa003040200850b54003c244955540144444202909254001400101d01200300000b4150041101e82c8152004426039403100529403080e526540c0a940846003a031164000901e440d000d503200515000d0035140003080155100c2d02036007502c1c1d00311200d82c0052501024030030401d1074800710f01c04407041101d5580c1800c0d08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 802854091 1250 802852841 802852873
    0x1703040506090f031204080102040303080a0b1f180b1e07110105070c090504030806090717060d02030703080f09010201060b0c06040204270803060f03060708010e07051306020a0c08 79
    0x40410070391107000c2c10f200b102e820b40d03010032a5458207101d2004a03034840782d460003214003d400c075100030303808951580005610307804c59100d00c02c001400240304003820300c00402400d044501260080e0244041c2081303049030300303411984040003000700811003031b550030300500500501800300a0307610b602c2d0b1040c42104006a5072010b1203c00c0e88017881d000d0703210645030920352804203142c1c0c4442d8038240b030141407000f85648608560312403901030f41d600507140c48004080f14520420401401011070b8040801c01510303003001180c0e4200d00007811035071a00d841380c84801250b4020781080b500d00900040801165030207004001c02400c2c00e10041d428000d00c81003013a02c5820003031000784100d942d20092444011058000c110440c0403445d840c60300e48179840e012429500995a051148261841c120030070725002459910817001542c90000d9a468169203902d40100036100b40c0912400748121a02c1485124250009105e5580200080d035000d040a01514403d44c00001c031a80210100020b2040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 802855341 1250 802854091 802854097
    0x111120907060807090b0904090c0b030402010842032d0328020a08040f061d01170408090d1a090115050f03100c09030b0702010902030a030c0219080303011703040506 73
    0x445841c0c1c83d554822940041d0089c0070000008003003481c7c604000c40c140c0c45d004c019500c00c9200b82c0307401c042d944410011076070b2400d20410280004810511182c4c168400b40c0d0014a03664400c103502801d0400d01001074103000300300c050103044c80540a2000c41c4160000d115054a2441c4000b03140340068142000c03550003440d000201c00300120110b00c920440c42040400a083c0d049001262242d03110041034030011124810f880002d110b00c042c040031004200c201e0701010074143c440304483c80c201c4e621208001c80080c804d483d100c00901c4120800c0d103410407035542c0710744a810020b0a0319048500d800d07401c00c0262100303400c0e81c034050001e901300c19806960300584d481200e820305851500d1001a00e000c034110968082c3d9070074004151003458010031030b4015a40318900c1c048490f40c03041d0040703080f14120369002c0d47c1941f0044580700481d0045020b501e81c00d00207070180c0174040d81e103403109450300120f5005944e03c0d84004010400c0003120b0010b0740e6180e44410145182614000024107580 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 802856591 1250 802855341 802855349
    0x5090d0311070615050f01050c03031501090305070b1c02031b1b01020c070311100219020a03050a031e020a0c05040e010b10030f0f110d0e011112090706080709 70
    0x1550703036951011940304203400c0c2da4440e41c0c00401400801c03041a056040806140300300303406072540070b000600302e40c00790007518481081c240c0210f09640d5003203d20280c079000e0130000e60500c01c2045000c400f2400a02c800c401030320181c0c2d0f5980c0e070f031803903c1c901603c03100040350010322684c4140140001c10500298040921a0304c41d5041e8403600c0a031094000000800c46502040d07100080da10b040d1100400e107102101c1c086c2d00e0314401151b40206008491402c8140d4500503000740c15a103440300380c0e551700b07520713203a0000d41144445501d0f550b8035803070140c100c40194049518010780b07000041608003125407044081c80a011007c1c030036601d002c6481c04034002c141c8240d0f1528540b42d00304d0801d61000c2c0805038010202c4103090030b80003000d4020410214100301c0c4900380f6126145102d0303140210b50220907100407482ca840c010049500041c041354000c801103549a06400c2014400000500b00c902034071008040c00303080129206260101c0d90b4449000d2001681c10041e246410552032000c403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 802857841 1250 802856591 802856597
    0x316140d02180c0910020105160c08190306090606020a02120106050f220c1806030203060d020420181c0b0601110109080d020705010b03010e071208070b091f05090d 72
    0x1607110000b1050710f0703005040c3c9044e081043e00849804003a0305400c4a0300401e000300403492090145c05045550700c5d9001c90141096604100c980901420341c0b1182000c8150341c6400606e058640c9180401c0d10070b40e60242c801640100b0441c2c080d8a04078824005494440002b008602d2604d008070320901c0c00808a80c2c40b0300c0101030107004142c0360a10001c3d03140900748040100c0070706000080d00141d19030507228030345203042c4004610f550283c400c03607001d00d2000300b0741c0130b034456140d0030400a0101703e9404e80d040401c05401e0381491008801421004c1120315045949000704414009540201d0364500703000f80d1103148900c042004015440e400001c00e19002e4055010403c5180c0902079106000b0440500060750b1034440500e0b0f4080c0500500c0b44000b400320303c4040c020075090b03070b150907648075954202d40b00410416004007544d002103441001c0e0f582c10003107a52910181030208494141e9560407005000c000d42c41c48545401c10035a502d1000c00060a00c171445546e9085141d8020040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 802859091 1250 802857841 802857889
    0xf2a14012307170d0e060c0307080c07030302071209090c0206040804060309021c0609061b08010b0d0e0109060f060b030c220519060809070e04200316140d02 69
    0x1d00408060180300c1140550f0500d030344180240c00600103141d05201c3c03200d940201c001241668110108481c02a20b00c0c0c1c0d01d800c201e8860120541c10ba501100d8101c0500d036003001440c001619007045800001440e8556843c045d14011482060f5a84658048110b403c1141040700003100345007510151201c500c0c0000743e60f20240f02185409440d0346040c8599082c02c1815001c204454002d00c4007244500d00038000d81c8101c4071441386413540c500409012406441c010b0102c2c40c3c0ca4070262110449031080071503100300d02102c280c2150b14001054410903110700030601107100b00c1c0a0217008261546800d461440c0040202c1403078082d18440c11a562210030301100e00300d8070f01c2c10703030170140c071000780085c042803052006007103002110301c600300c00300305201c002440303407240490210115031503401094900e42d507603603c81042c002040a100b540d0f000080001495440c2000f1801040c0440740e42841c01508180c01850b61504d003201c00d03840340782d960303c1200041c3c03541061804000d25803590307207213 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 802860341 1250 802859091 802859093
    0xa0c17070c051002130504060303020c040e012918011a070312060e1f050d020609120303090708120a09030b090709150f050402070b040f2a14012307 65
    0x140c8541c1d1440003401c1031140800c140c200190b50750040c401031804029010289036030b10305010540e4410b200c01340158210712000704190503d50810b2000c0f2a03040000604560b01418041c00d50408240305402e60b0444c0c14440c0d89030600c000075444201040e4000400d9601d441c4e248a03000001224003003100350302040801c01c0602070041407180301801a0b003030240c02c1d00c0e600400064901221100360b40d940011a010322404030282c0340055450280004050000076002d12903507900058045400515030f1800444500c0d050001c1d5000d020900050160759182034141c1d071501030180003800c0d4880003000f84000903600001c3c00300c102d9a00c031406000030f94032000080d003050003640c40f81c1e5200381030200c2401c0c4030300d1000001065038844003111b6200c50310f440600040740100280240550404808540802c00041c11580d44500c104201700b984400f0310165020a021011a151400d5406c001407015440241b5487e07040c1c002840c24000b1130704009502d050104c1d2412100d142c0000008800c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 802861591 1250 802860341 802860347
    0xd0b0615070618030e01030b060306010e060906040b0a080106021903030e0327330313050d1706091e06030304081c0201060e040812061c060b03060a0c1707 68
    0x603003040d0b0041000c10080200c0d95142843e03640510341200044c1c0c2c0707101001c280c0c0d0b0203407051030340303622001c0c00a030300395a1420b006440302014840c2d480e52003801445000b01a54400005002038151a600c498441450040c041c068401c180c02c0705080d90054800003008903280c1703107407454868052401042c100d00510100341544500580c009140c03110b2707000100ba04684101841c80c085003981c01030300103441030314130101032021040c0c1c088150b1f5607440070f0340c0405e000e1009160404030941c0700d403906583c156a0341c4e20b402148002e0b02c0100d40900b1588407400c503421581d580c030000980740c41b040c0b0300e06600c12140d000d10b45885809410100b102280058404009441c0500000400c445100a0100f421040f02628003074000056085c07007130101d0460007204030680039951007016107090000002c40300e184400c008080541005141c0c415101c10103a10100010040c028100090314220701c070141400c0c241c008060300b40311030070186180700c2503500c02c40c1810b480b850301e4509142030719090000c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 802862841 1250 802861591 802861597
    0x60409020f1f090f050a031101051c05040606120209041203061206090b070e03100506130908071a270f0123100f2607090c08060d0b0615 60
    0x195400200c02d0160114054202030b8400d0111000e80b600207045940302c6a5584440d814040c20380c110300659030030000601020215444c40005050160806071201420b0401c0c207050750108854544403014070041c0300c0c0360f210b580040d004418004131942c0350b54000c81e0b441140500020301184207030b9a54410039110303500410280042d5500c6440e800403a0800310041e020b0624160342c460080c1c00403522050142822000c160400740140130031070b99400501004220040001d81c0203d440e903610000742010744240180307903114200046e103e88050800401d0f40e4660500f8084100082040c032400030082003001869444414000441590400380103060041c00303004c1d04055070a0040f03041c5030560309442c41c1c108090b4400b0b0803002d40da90380169042000c2078440e103a070340c4840110601c003e03501c2100d40317203d4403860500d00d0301404103640c00b07602c0d240c429030003844035030783d9a04401c460641c4201055000003044805128000c4140c8402545480107004a845428188004402d1a442c0030075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 802864091 1250 802862841 802862869
    0x1e030a09060e2d0103050906010f0506072a060f23160f050a26120702240a0c0e060307050a020a05030a020d080604090308181e1e1506040902 62
    0x1448036400312031010040500c2084001c035000c2400c290004d20720b9400003411034101e80cae41401c041480ea24010034009580d0201c1801d942c205140d0303c1a10200d61603280341290344006081e803100304d600c0d2850041026024000c11000c1021041030580d11458141a84407401c24082c2d00725902d60100041d540d000c904030320000d020101a0860106219010400310420340c0a000c4401c022111907042c2c400f404e074882030140c5240c07028003400540402d65450b0b16804043c0d0b0048490180c0c0000d01651070b54041a030700005510700c0c0e020040011180c2c001d15241c4a0a800d012003001e0000c0006a00c0740401040d810811501144c0c25901c548200f0006031071030303088825242c1d80c1c0007500009484c0c0c119561444049504070002c10f0302418240b0800480603015034400d641a02c450707034804400d09903180da5442c5482140d402043e40c026884420038454001030081c60320b981070400c095580891001c0044458116850600c2c8801c14207a52079800002101c0c0003c0c03140603440040c2d20700c3d08000e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 802865341 1250 802864091 802864129
    0xa090513091b0807080a031d220f1506090b0c0a080d061505070f0204200a170106020706020d18030c080606130507020a0b0a0e06091e030a09060e 64
    0x7604419400d2001902d07010b451091007aa541d40d5211680d0301d542da4044140240081d4150340c004452071040401260054001040400700c1c1d85e00340c0d800102c20032007441c1096000d584954407001074080d40705001e44050044200d4030107520f02000544002c495200d400e040c4040051021152070091240421840c2d10102d01c07a01e484e00e117482d0400400d110302656041a0841d109440958016410b5590850f03004600040000d000d5081c08050240a0a09829241da800082d40c00b0400c00010340110304442c2c0d035400072052486070b0b40c0d6000e18107034070030000d41d00600400d21425030f0202c2d64800040060502c024000c0c400304188003002c038180d0019245c0700c4501c0d40070821072000301e04140241411500d43d80d0400701d107a034010454070180e82020142e844580810009801400c8142c0d00200310400060f45510080b1ba031030410390300300d03002d00c1180c0208001100c90034a0900030021881d5801c0154100400014041c0c82141503010300e900740300c0d800c0d13020f03c895070303e4403e0401c0c5011501 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 802866591 1250 802865341 802865363
    0x20609060603030d05150d080a0e0906150c28020102060c03060a150905031b01081e0612030d060906050a06020718050a0b1002010209010318171605010606090512030a09051309 77
    0x418182d80d527801450007200014181d1213010064600201c0c42d07406034200420310000109100c1e404000b69010240181c00b174012203010900c85e591610141800300303140c102c1900b20320210b100084c2403d0000701411040381e01070080c089603846000d10881a1240c1078107080c1104134030001034486807010b9000c076615128460740c256140f10340f03000c7d8003410042a00ea0014688882068001c006502810110010b214200080042c03501c55400d60303c3c007600300c0940b4a0406110001401d844041e00514013080d10b4100c10456814011125801446a40301030a00e050401d4410b80310b940b642c05482815586440201b001c80001d90f10a000f800c070300030041001c0e0308d450880a8080d41000b0b017464046890980c0c2c804c101c5c404201101d507104d92000000b03003003003100756420b11640c2240145030700070198245843c00254091007881c014080701d454020125103020f081101d002030720a142d0909400c14071075000c2d0182c0140f07166080e1038048425441d0750f5810a40c14004000300300c80039000140e10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 802867841 1250 802866591 802866593
    0x2a0625050f010c0e041d011a1815100c050730171c020d02030402010e06030f0a15090c0e010306050d05031903091b0302190302010e0d08220510030c0f03110424020609060603030d05150d 81
    0x10000032281a002601c1101c00c1c03041c2c070b10b03900e41060020038043a2072006500c4d402542ca0028500800d101804809424003541054a00300c2c102c1c0c01c00d04501400d9580002840195130300002c1040c4001c6040320140d296141c1210858810400a0704001a20b5140e41c1071640700100d01c0fa40c400540b0000c502005140520940240341c260806041404280307170001c003044034113015480da144150010003d43ca0020f100b042c0e82d0840c0c0803040c101d41015541c100310340004405080c03081505c80440c941045490460040012041c0f0601143e80d507458070240400041c3d030402041d00c0c0c100c0041300c418042130302c1170400c50070b40d200300c4038071400301031001c440b100500180400300c0060b502c00b510145041030f5000010350442e51414944000700f182c107000784803990304c00c1d00000908281400c455040a94541c09144502810245810880007907aa04041560704008495008841d1001011705080020105e6102d110301c0384543d6a0544450004200041411180d0710062014200648901072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 802869091 1250 802867841 802867859
    0xf09050a0308010b0a0f050f0f0f032e06110a051006081e12070614010308040e092a0625050f010c0e041d011a1815100c0507 55
    0x8804012408682c2520000c180c00c4140c10581c2c03460049505c813007546d00300001082d280358100801b803248880f010800c85010649960113000781d070080d202819140e08251000c0d00c0000703161141c80b0041c40201107040e46208200e41c2c00c0e0100d64031414014040310348402494100070201074060b00522800d690501c014010703500103c100d130705140590351807128002031507007000c200c2415501160701c03503424040c03858103c2e00200045482400700141503000d40c031030300480c1c100036071059131500300104081241540300e28074203501419090140c110006d003141007031a030b40707680100f440032f944840c800404640c44801c221001c20610b15500c01c082c82c8803500d5005d00402d00c0100315200c2c084c0c40c1203000840f505000701e506824a60322039848410b00281404001c0000810805901040f01807015203048284580421003080d001d03400c80b985c0488007480b4140701e01200905038120440200b010403102c01d40440b6400d0401ca0b500c00840e100e01d007048540b00c2141d0005481801003010000b00040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 802870341 1250 802869091 802869103
    0x703060b01033308010e0d08071101090c0e070507050d0e1315031103030c0d0f0306150e0a15050906030c070c14010f030501030f021306080a06020c0606060423040f0905 74
    0x100b83e1040810540703990410382a1b85402000282d50340c080882c41c40540d0080d09460307442150340c07804d81e1005c444071502d0f500352603501d00103480304505a4400d022848900403215482142410070500d828981d0b5940c50350380601c3d4406804001002038910007a68602411800780521010240804030740c40101500036201403004450b0024040d069400078140401a80d40858281021348803070b015200c025900016400d1b510010141d91726408143c4182c03460041080481c1503031b40341c5001510300c083c0201210190841c05003280c01b0004845003941c840c044602c01c100039038105403240c0302c0340c4c20f115090007211001488031810600110f2091075040110650410985c1d80c10b02a850003c41541110828080507101000400e480c0d030240c141101540f101d0181d0f00000500c03541d45001c0c190074006181e404560780c0c0d8000842100e0100d0400c640c940100d8216403680ca82803070b0100611800034584503416032041d21140240f2a540c540d80816000d03080002c00b44000d1340640350094440b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 802871591 1250 802870341 802870421
    0x1140406020c0a061b0b04030c0b0702010e160803091c080703050d050a05010b04030b04020d061e150522090c03031205070905010212090a1a03010f1202030703060b0103 74
    0x10401d8080064554803440301134141c40e140c900e091750007095544480038485c0780240b041c0c09210342c140b03180000408001e4403620455540d07000040116800c511142020250400d1401203040510709028086000c02100c42d08030382200c140034020540c2d2200400e41075500300c082c01c5201c01241d024203140c4c00c83d008011070038004004000f295100060300088034000c3c094018104414001400081e62085826402c14001010042da05495598100a035660380203840000c1e0912140981b1092160017401221450007981071190760400c0081127107401d03040410f00e00191400c00c6e41010200682c801020346405c0903180b0407098403070401610000854601003000d81c601000103040a114003e80c505a4030140e002e010001e200100e4000c05800407500a43e00503094000080e40d51000b503140c403203920307400d090280c403985800d0304044454155840311245188060500005030340c00b00301001625070113100040d100e400e4400482c000c0011a541035104c00c154454524000040d40e035001620f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 802872841 1250 802871591 802871599
    0x20c0601170a0221100f1503171c140103020112051003021909060e061c0305040614090405090f1209011718031b070e190b01140406020c 60
    0x2a640d854034030340350000303461080c000d40d000700b1201801031505007001c10b0030402e8105240c3c1d0b81100c0c540c0d4181428402111010311075a5401d40d29020059402100c0d074402c0242100e810035865500d43c4501c803c20011051074030100000d030226122280103080020089001c0100849140b108509032540c0081c0010780c04585035040b18182102180501486020840e00501e941403840d824030103140c8039014400810302c5d440b000461515250320444006000b0905403030100c1c200b800620020602806007584041024602480070a81013401c40c2e0132603229244c01990b0000e1203510300028003c401465038020b041000b03010b03007004002130b0a40c031078256500356103076003841004070f0400d4401c401103240443e91002030400c580c03070100380e40c0e940180031a800d1240e454880200c903045a0040f40c02c0c00d589461903602c2000e502041290340043c010701c0c001c0701101c1c28401c0115030700d0003018845031509501c90303410761ba0320f92042c0380380410020345410180c0c49a848050182d182c4031400700c46401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 802874091 1250 802872841 802872853
    0x30301120b0109111914160c050a27020702091531090203010b0405071d0603070c0609020d050304060c0512030721020f0f04030209061e1918020c 64
    0xa00d000c284101e92038440c481c01c2203443d1102200c4907480500400417850300f03014500800c0d5400e070040e400201111050b114003440c1e5820140b400c40c5803012180c21a5006111140c01031001034902c0451002d07078050300545a84052000c4401d0001c0c2c0b0413001c0080d004580070007407010341d0600d14800c4109050032140c0300c00e03440c4410b0305903803039410300d1075140c045019189100850001c558019401c2500280000c11403040706004682600c40548640c00020725000c0e44071b203982003880095180d50740803507810b071031828850700081083c40c41e0bc03c060185d80d80d415a41045565010807145242d034030005176500c0325a1107801421280e6024810740ba54003406d4400260040e0400131a03104154903141d40740d004540b01120294280f800980303100c6035500700000181242118042d10b0515405141156100d082d44103201180038003806003405601c00340c401806074509040b20f10744040303080d208031005804007401448400388650094040d00e170340e011070991302c0000d6001854004466411111 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 802875341 1250 802874091 802874099
    0x914090c012a050a050f030c071e14030a060603140d0207030b1f2102010e010c0b0c030c041205032a0d140d0c020c01020606010302070f060b01050c030301120b01 71
    0x1040320102c00c0c900910030b4802c5a000060000303040029556005004544e121000c55403018502070584030022103d40c008a0301680c0d83c0d0040061708044c002841ca22200481e0744c10071b60312040c020740540b04030303141c10458550507071718100300d0111169003000b424440e0303598900b040135005401d00b900040b140214071002210340d000141035000c4030b500505400c502c2c3c0d25039580034a510341c0450b117a00030748500580081c46190900e10700508000c0c140d011920030701d5a20015000e00e00d50711006040c0070400403424040342c02041d036a580301c440c00000942d242d5803481c01c5149441030b074000e0005217050a0080c028440000060160385080c0107400d1034101400010100c0940c0201c001030907548031201c042d420b18402c0e0b081110302e40ca01d5803124180381841d8014020b5a03030f80c3c0d224100692144540341e0f03d943c5c0c10000c2c1608442d003800d045140c01d0180c0c950700401c0c50490800b0300055118140303012264071800841e543d03541c1504c1900c0e1256121a9100501d0309812419285240384c500041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 802876591 1250 802875341 802875347
    0x4051905060a030f0602250b01050102011b02061306020903030406181a0703030c0e180403030b040e031623070801050f071d0a17010c110c22060914090c01 68
    0x2030ba50810b10300e004c101110b6a44201075481808480b08944003d00f0b2403002c2c4102003449030605114407903078261581010002421218081c02c10b102004060203402e25058010030b105420841004800740c1e1406039082c1200a0320607c5040c0c0c3c0c00d0b01c00000d00242c243c0c0e211038018100030007080c0154109a4880c0a00c03c0e04101c28801e81e0401e100f009000d0010b4000d51000d13080c0d9030941080c1d100001030000191070324103400700030748a40300b10904000425601d8825196122001c88003088070703003519600140d5070b005001c4210210180c8041e69010b02c550003512080203400035031a4908a0601000c10f921801d4a100d582c04540c24500072482d03c86510108610400302c0390341d120030083e070320009800c2c1c400300c01c0c0005402104c0c2c3c50b070200e55500c0e420200c0095000c00000400d100030506d80007403014107280040c502e550441d0808020507a2250b03042c0810f040c8190840c3d40094001d508040201000d5102c0003400389000d4000e00140c65800d9094442d0452005403111181504015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 802877697 1106 802876591 802876609
    0x727090507180507021501060309030314070201020408160303170a090615050312030112170d020c0a0309060e0a0b0c010b030f070f080a0503030a0f0b0405190506 71
    0xc0c0060b2540b8002c00d070700310784180f0041c450000440001010f00c5d6060240d2010543c45801620901d44a80c001c8525072010307128075402d03070030042c4010303000750320510801c20103020b1401c54001092898480a08894160321140d218514284007121480e10091620826560328150000450500c0c0b00b260522166540f40c50340003803c04082500d040d6402c00b00401d910020401400f0488207203441c040d032140d104444860344005081c0100a5000300941441c40e14030102c0d04003152180003900581c164025161000d0668940b038040b1416846140440e42024009030b04004045082d00140b80388000c180000501558403130029080c601d440e005d85840368004101440140c0743c940c07803003004296200c02400c41c00c10b5555140d40340d0100503e0050200d81d0350b01c10310800c10954100040001c4001c1c030402ca145811000520742c02c0c030b0030810071005440c00000071214184000b007 = true := by decide +kernel

theorem cover : BRFrame.Cov 802697841 802877697 := by
  have h0 := BRFrame.cov_init 802697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 802697841 ≤ n) (h2 : n < 802877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
