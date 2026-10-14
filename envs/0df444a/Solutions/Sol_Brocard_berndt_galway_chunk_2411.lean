-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2411
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:38:11.52521+00:00
-- url     : https://prove2.me/submissions/0b369c69-6443-4e24-8003-f1af29503e2a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 433453237 ≤ n < 433633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 433454487 1250 433453237 433453247
    0x504082b09052101020f1209010605013002160f02040c0f053a0f0b040605012102090d0309090c05030402060307050a0207090f021c020c06012102030d090501 69
    0x9180d00040241881092165440b103c154038801000d112200b80300c2035078440329a00902071561204442c4030002580c21640c2c1e04014507e0007410414003c0100300d90700d08c015031380442100251408030418a80c01446120300004504040011001c01f43c5015412800b074001001d01406c01c4540301c81c0b07000303180c0560900d8462103030368009074144100c282d00c0d01d04014109010320b0703402c021712400f201d00b00302c4420284001071400d500f1100e2251281140f01c03000101030302d441d0307050810716894a144100a890103000e442d0440304180c6503140440201d00c0d03291410004101041d54561b003c02c501e245c151152040d10241c1802076650800da0313400d00040505842d80c0e030713400320100306080c03090001595680703089941140781410141e546d041d44ca1070030781c03c002c5968030064403a80f624094020309044e41d0000c1092260158000d151003104041d902c04a0069001c40441940800014010400c030702070710408070409040200000c0e000d46e40002d2500b40344c0144072001862015080000756000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 433455737 1250 433454487 433454563
    0x3040510060b07110a0b0909090c0a060e030d0306050618030307170702090108010903021002090418030306090c030510030308190203090717010504022b050304080309030706090e010509040201050408 87
    0x844019040c2032802401c0d0f0428060011000d08c00d520000102d4600764040001520041c0080d00900710b00f50349a030080d1200d00445061806401000c440500c09486031080405880000384014180100c01400c0d400010707410880a0b0944010071141c000314200780a1150810130303e2200d280d80d0744c41841882800b02041e03200e00c2e070a078141010344000940105403a41c4c941e100040060b11407040c2c40c0020301401c203080d456002a0445e155050a06d5410f030404000d40300000b1040c480d404190030100c0484030111082c0340741ca400e141c4180b000a116481c030981049080d04d08000074a0441e252900700da00540c4c0c110001d80c03121201300408004001004040409140200454070f0150046800300284007098440209102c20401d19115040d00200b100381c0c1040480b6221912501e0007641d95000031982d900c83d02c80c0300d00002d0602c0c452200c540503500880414007441c3d1a20301400b18081000d0070480c1441418000403524a100700008000c0100ca4004800c0e9146510300c80c0038188a5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 433456987 1250 433455737 433455739
    0x905030303010b030c0904110d0f2d0509032a07050406061b03111501030203010509030304050d0e0f100f0e0445030801031205030f07030203040510060b0711 69
    0x1800108076a01c981d030141c9605c2040c0703080d1281e82e50441400280140f0015808601c101404114444120070039445103044114000c4101300e401d6043c610061404031400c0c01014500341440600d4085000d5001550070144450403a81086c80c04c524131031a5085124016083da44145202c1422010820a18000b0302003640c082281a051580c000c000790100601c001c3d134076203065104030030580328500c03160908100e40152201040d2080c1420315001082c80181e10030760a140c0402d00b908804001c82e170143c1e0344903009004034101d1000130381d00c0368202402c05070b101101007511070305500c400105e22441c0769140e4030755100702800c0d0400b6040c0d008440080c0c0c00b491500510865050380f00d0110034800c07064070602c0d036a5074000261141c100c601c81c8004c100e00543d030548402010780000300c0c03030305880c0315006d0541e9014504104590b2400304440e00c210280400d0086050540264000c60700603000e04140c8070b0018a9407040740a0782c3d00340d4050035820000107480024480e82c980707420302c0c00c84c3c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 433458237 1250 433456987 433456993
    0x1608060901061a0403021915030b0a0509010b09120111130306140106021e010609020c060106260106030903111c030f1104210b0405071a03090d180305010e0d090503 72
    0x1207000c64804030707800f139400000d0140c020155107000021510031403c00406404c1c1d800c10f4406224100100544150341009010307658ac440003080a00d00300c3d10f450305860343e981e403c9040800700c40810414409070040c0d01e40307555980c0c8103102d03c0c018060043c04a0100c4403080c0411515600e0300b80100d915285611b040d034010103005220450f1302194041002420781445d0703644a41b500142030040103d5030100701d805100140b4000320f500085080c80c1260056195401800c0d01e140e1800c110f00c05680902280d100400c0041c060f0500079401401c080b0302a107842440c0c0c2c40001042031034251031450a8108120301140518181d50501800c1300086800314107201d9240d195042d1a801e01942c0681f06c510240882c5424201c1c1241040303a60707150b04180c001e0110306107410042d84580f03450082c0341c40f81000c4c01e05585090b04010443c0d01620488000342600301841800302c58000e29458006418001c5400c0000446d400f4000c5c0c00615a40c50064410740740556405040003032280e0110b80607030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 433459487 1250 433458237 433458269
    0x80a0807030c080106050c070f0305070e06031513170a030609050601050c031b120a03090213050f060d1b0e010e01091b0f02100c1710210203160806090106 68
    0x140d00543c002d04552035410805d031180c208492850800c90207400030119003010f904000140701c070028141c0c00b12030451116141e1510740c2018903403504090300d0380c4030742582c8500c04662880481840c040b0110b0281e2a13205003200c0c2255078202c1603110807081c0d800030b0789414040c0216040d901c60603821801c2401c22600d80b1407401100c80c1c80c1c0c001c40f010300701c4800c4040d1951611220502c401c100750000c40318034a035244e6140d070001e401450091801d034010b008086070303810900d24504c9a1401140c8000e1200310941e19541080205000100c00311401101d004100d94032507001c6010001500800e000f41100e5030414045c03004d0450142c3c80404901d00f01071310f0100e40c0c40e5102c01d4031810781c0e05182040000b02188801e030302d0040d00e00000f41860740307040e05810003a5803202d0491007404202e80c1c0303140c50342c807644d8544080c040f4a0080c020b0105041d103880709200e410341c82e00a189440507059480c4484181e048002d070707038030581c081452600408100040300a0a1081901a040240700f000c644 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 433460737 1250 433459487 433459511
    0x80c01060e060d0305031803041220011202033c0c07020a06140906070c080606040b0a0519050d030806120f150406022205033016050a080a080703 64
    0x1440f980034041c0a024000000c150440b03800d1001075410324004040340e40e1940e0b6103c00c412407046d411819500900c00300100c04003480b10010208040005941e980511494020950020b50000d800d422a02008090346c01d17844000c4030109030000c04200c1e280072084005c003d60026039500a2080c481008104002070042c2d032840b8000d01594440d18203203000700709141855800c0e110b2007299a6201c1e0010403180b04110300c81d06114152913100c2c00781e5007586c40d00d00510096500b03d114641c2e2045000001380710900b017011044000c009440849010036944000cc01c00c0001c081005400048007072080195a003040003040c000f42d822440289460f129990315036440382e441411102c1b18103441d0020406003c401e40594480e00c645140040c1c9181d1146150a007004203441064024042d40140950304840780b40d028070129030881150009022100075101c0075030000d241052016600c20010003c10303c00c0244590007486044060365902807420301620080001305504100b6003051455080c2d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 433461987 1250 433460737 433460749
    0x4170a08070b070207030f050d030b0303070c0b0306060702040e0a03030b010c0b0106031e050708040507050102120d050406090503030412080a0c0e13020c160905070201060819020f0409080c01060e06 87
    0x768030b401c0028244280c6415070101d003062480e50000e015080044c6540e0103012020903103020011036070300c0030410340f03c8000074142c0764010440050850030402c1820000950b00200465004e580104070b00d160401036030018003100d43c81c6104000b1680442c800904040c1c251090307174808002400c2284403070000f85d0b5030351a00e9205018000c100342c1c80e208400050140d01403951103444484905000e00c0c90320100040845204450596683c41040e50000d801e50021405101d100d081136002c61401c110118032102401e800350003101c025030307503490a8011a10a00156005078840c1c040c2d4102d41b07601c084018a05e240c0603060a07401490300c942201e03015000308003006001000d07600224100c48460000b8001c4c014090404001c2c06500c1d0f4810301c42d01e031540c2c26030582d01d03019010802911401e001300e080b218113002e041250351007803000c00702d040c02030b0504585041c07008120500d90880b100109058844280c1c04550284020074004400c1c0f10a0240c2d1019003030286c00c107e003e2a01c0000182 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 433463237 1250 433461987 433461997
    0x2123070e090102040317070f0204110a120507051b15040b1918022e090918050607080901061e080c030a03080c1c06171009080304170d0903030204170a08 67
    0x102040340050b2902c1023020700811101c01c55002803040040554101200d40c95a0120aa580002d540400c542807100458494280141056a030f07150501c80f080404035900404280000d0040c8242880c000075130520b000e20a01c207078424240d00d5440c0c106070512104d0000b110342e801040303131f04040078070203418030001d03030400b0441e01102c40504080c10311403401542540c580502c89400803c040701d403002600151140c0c00c540c481e0b403082009004c3c441c90703030050851b40d441c0100190044004a42d04a21690026400208042c000a0b032140d076030405c0710501c5074074188600e02e840740010400c581601841210603808013500906000000b9135402041404024001060746a01103900300d0420b543d400d01d682820f034080b404101094850728a50602c0c0c19180da058818030900c080002540218003880070f00940c00352409046446560b500d40c040c0bc3d240f80c07131200c500c0d41400210070b100114081c0d103a41034020b4400680c0c03941440c0702c3c2d0030340c00e511802810740c9622102d0303400002070020b0700303c803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 433464487 1250 433463237 433463273
    0x305030a11091e030c0d0203030f0a110303040f2a0e070e06030406090b1308030408030703090209100f06030b060d0905031306110106050108012123070e0901020403 72
    0x340303148403058101c0380d40210401107800c41d940c807920040305110010481c80ba14400c0b001c403a03160702d50a04201203011781c16002901500284404140e1242c0b800107020b41c0070342800c002d0300941e00d02080782c2c61034100300c80c1544d00070090b80c40842404040000c11010100a505c0050140001f00c1030700c0450b2028415410100c4106002030000c0c0e2180242c0c15204800403d00d580d00d0800e810700601074010010140c1d0031086041c04940d140c117501c0b070304036038103644501107038216585c44d2100300c40798200400b49010301d40c965240800596071505220720030a4800b1100d0700d05070501c1c1e1445a8074000342c01040c241460207100001c50354425040d203071440740d8203101084a1015180460660080c840c01004c0740141031000700721560422101d40c0c0802000c030080282507524401150188028850740314201c5180c04109844000807000c85201c034029888040c0da6011403c1440319000c0b0f06031024034035081340100307100e9030940c0710035103401000020007542054210307299a41d040b10340301c0e40b031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 433465737 1250 433464487 433464491
    0x12927040209061309050102030f10060804030806010c0602040e04030314090c0f040912050309010f0203040c05011b080a0f02160b090909010f110d05090703031d03010e03160b0709030305030a 84
    0x140641d41d406046a48502c03564201740070680f400d251160103504140d4940d040702c02d229001948613159100910201c401560302c480072622562015100f5210140c00d680c1000040c0c103191b07000c2405400203000604420051040ca0700e0719080040480e40b000a10f01036000424040c48103040000425141662086803180d01f11074484000070f0051180b14001072480d01400b404904144d040310141d4800e030b041384001d00418582c1c101001c01c03480112001489804c0c48001445107510400505a40310320500d0040fa5000d410303100c08071203411041e030b1003001a9140d02c8041d940c645c1480051103010180003404020f80c05e040341d0a1a9014002080d4043c201c80d50019003036a901f5000786540e4820380380c0411211204500b0004207074412014080072a051601040201400203150b008581e01680c41c07003401c20362546840200d0300c0351401d041e49076488000c015940c0d8003d00040c0301000400200401800035460b010446000c000e0505091000740c8008002103034014086a61040c000100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 433466987 1250 433465737 433465741
    0x15080105220902030a0b040c08010908040b0d0e0a11040b040203010e010501141b3d0f060b030f01080705010c0b071b14060907090b0310020c012927040209 68
    0x100d038008001c2c02c4006540b502c00d020420091001741b00c8683d02681c0101d5100b01508e48440d0b43c030b03080c0d6894480080c880c0c030f800c000400082820030050030002d01c2c035803400b00d000340080c580b5501e0041e0152090703031081d268601500240c6850702c122511480162015415585410701114042c80148503e90600403112040d80d02c020010084550034843c085a2401540102049580e103a005c0d00b0600c09080c0c81603031020400d05a4940d103c0180402c015003c003151015000c500900b607201c000c842d0f100d0300c4160108442d074204014620500f4101d035203060b50361400400d14035140c0650320940c1884030040110002c100c4002c0c07080d03808901c0782001440103036401d17201d280006214a010b04a603496510032004100d010640c140164920b508840c0e69613240c1a018040341c619502140d0306a1081d007412245040703e40140805404103400012280031b0101685150490281034000c20040b07170009034401e182c00007034680c01030b8036000071040c04800600c0b4580d00b2407003c0c2003c3d10495103080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 433468237 1250 433466987 433467049
    0xf0509010b061e090303030c03150609031908190810320d06020304050c030106090b131515200d09181b0e010206010509091e030c07060915080105 64
    0x869241d041c000d000c580e40c0c0c0c5000e801200e1503800950340f103c6007420020814405282000607141001d4cc000c1c007401900300c104402c0c9111720039105084600c45024407001c9210381e1101e060f94500f40190720340d20205d140c0350305d0342c03499020560044007034003d042690211908401041c14811103011201420290042c1d00050b00b51020b40d070024005030001040200300680408c501d02c046c04c096000b07124054070fa0f228131b81984c29005240343c0000f010401310810782d00036000b0b410207520010040e070001c1d40340c81804070703d000d6203134815020400c684540c84080d85002503000c80e4450540c082c0c104500f41c00802002e0b46d100303226040d210111a1107844070442c20354001150f240000d00070f0426003102d25030190120102c10409400b50140744000200e608018400600c42d10410300501991030442b40003e1030000d02002c0360340244400d1008030f003a002e0800003a006403c941c0c45001005141c00d208500040c030100c1c0340c0c010403c0340c1b00100410303181c07030030010f204440c0c01d0b42808160345106 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 433469487 1250 433468237 433468297
    0x10e090a0f150f0c08060d020a0e0f0619081905011b0e040605010804350720041505011b1b0f060f0f0c0f0609060f0509010b06 56
    0x904090900d014031540c0d1001c1050500c4010000c0c11640d0b0305101e084007046281c41116000100803010840d4040062418505040c0c405001031000713241880c07042e1507506980c9515012030350620440d1a90080c0001e030316202c07100f40c113400c05100081030314a08010726035840e88000c1c121417142e4080034081404101c800e420980e5203541c60300c1e288410100044005082e030b41040800b601841c501800800d440d4820780714144030f10340000b0103074140b88a5000301c00f03907880c10a50503040c040684085501118406004181c56405052801150240c0c110364088464850000c03600c103a10785082001c0c140018427808088500909000c8456914010309001c4069403100c01846004560500e60001c440b141e440007e0380d2404041c0b1050355168132007038800000260303250300400e01d0104c076000040d2203030032985000b07441603402071074401d031b50b941d01c8059070307013021007101c440e9100c0c0d003401558200e41c49926400608036000748030084500011600074420311036003102c810384801d0142d110007142 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 433470737 1250 433469487 433469503
    0x30302040e0a090201113702030f0c010305010f1202040f18030207081c050f030c041a1206011422030206120114060910080601031e0603141203010e09 66
    0x1c0d8a404000e40741c10000c0d04000d11070984124041003c0c91100c0814080020303140c1c41c40b5920216440000510712500d4400c0300328214480c544011000704800180c40078448544480d0690f00241042e8231060b0024003500d2050b040342014400031031040103900104200c1a4015405850004904215501c14805043c40c0800c00d001d4000f0064070000301b42e80020a80c08031108581624010f9082044112401d0310b88000c0304002001484211100b030b0391440210b4003e031403910307081d203415a140250f900f100449608042d10500c0030400104644281d5031442e4010742c00d10302083c42c0c2c10340410010740f6024186040d82e151911102040c041c0820a210344081d58004101d6501c4d440ca085060390040000d029519075808188800101e130f08028054a40b5030f0301c0140800070086001e1030842d4440303001400030b410180c9402040b9802005c40082521520321000b000c65028158100200180d03071680050615038000d56140c0c3c500100319055a040d154901100707007944d1202c2c12000d1820543d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 433471987 1250 433470737 433470749
    0xd02130504060906050c090108100e0601050c01090b0a0204170c031b040b130912050415030203040206070b01030501021b1f051e010914010605071505060114030a06050111030307020d0c03030204 85
    0x2d46406e0200d00c4100c0c00203001d142100341d072400c0840d5940142c460703c2c181103101d8810541c0c050004a6042d6000348064581500c150000040d810b12541301c201c601041034500c11943c1ba4002810702010041c20f1034101c200081e0b4000f42007443e42c51001c00d5030b0780301d4a00000312611120107032002c16034803a00320003100305004050100380040360b20103e0003019010700855115110901204503907015001b91750072a810080180200c911010068010750300062049074800001c0000d400014030b00000e0501840c010b000040c0c0b2000c3c2000e84010261281d010a0350980c40119281400905506000b040c3e110101c808121500d0f024003140da04492800c541c3c140c090f003400045500e43ca1684240c0b441d16030f041503060141d0303a96009803141c0c840c181016200c3da800d510000344480c1d00360401d9800c5213061410b161561074504401d10181c0050b1440076100d61121410445507030302c0f0b80502201d4968030085d51440c00d10980103981d4000881e40503061084510f80724003858002d6044c1ca0007818 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 433473237 1250 433471987 433471991
    0x509040e0d0e090621010506030c0a0b0a0f1101020a0c02030c010c020607020d03020f0a0302061e09151504090f0606050a050a09111603080414030a0f03090c0f0303021b0d02130504060906 82
    0x20001740640c0604001c07168540a440f481e00248910718041c032110341102c4001d81e5107450300710100400c4800701c848403054000e02403104001c0c00b02403001d03c000c20000d1010740d02c0140c00d060603c1054109520303866803504001c0d01c40c000c14096541d100c00c4592045d030441d503001130b10145103800c0c1d040050441c2c241d8543d004890503141456004100d00f8412580b8602041074007184210302c80341e644d42500e5030304155012180d5114141015075916420410f464400144483c0c84000281030300e483c440121603041c41e03440c030182000f10780d0203a14042d06003261456401820000071411013640c6102d450344a54994100c00f1000c0e50b04c1c8222002040009402c0c41c1491300750030702410394202560100c43c0341010301303206480c2d0745000c029a110800720340e540c00c00c14900c5c0441200039080300d02003900c60b0301d01040001040342c5800c0803900154441d40140031000e4043c40100c03454003003004418094a5280c48060060381d502c24007010040051200203016111070a00e0710081000c00d0008044074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 433474487 1250 433473237 433473289
    0xa0507170a0c05010e12220b030c0c06010b0315010c170331151e0c0e01080a090b04060216020901090e0d090f030b06150a0509040e0d0e0906 62
    0x594040c100b10301c441d02900080c0f10906038411032035540c2c10341320b040e11820703081440308141c000310a410b84454100340090405400c1e44541c00600540c0c42a80c4010b0344e980b00043d400c030300782c109020050041c00c01524181c1180360480610700600c0300510340c0784c10020104504020400940b10030f45201c03015140035038591406413200202e0810b00076802400601c11000000c520041c1e0a007101625400720903103a0202c0f4806d94100502040c40c1c42201049070350190581c0007040c0d10401d10301d60500ea46910f04d1a0844001400044020741007983c40c81c204200c80300414040c0002e50b400a0784800e0050b40c42c003130844038101d10300c4203202c000c1d800035250700001118400c51304400d4211200c48169101c002524800f40c170314805500c256102c0c0c05c81004100089860007017280c1e0f011202400c98041040c4c2e440400c4810703400803007002d000c00c0c4041103030229410244142d40d0b02c22100d200428072001601c0018040c80c0e8024031240c80f841d90070f0002400c545403000d095100c8013503080c032542c1031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 433475737 1250 433474487 433474507
    0xa120203090309090c0913020a020708250f0605030403180302060d060e013206070203030a030606080c0408100905030c0d050409240308031f03050606040e0c03030a050717 75
    0x951014482610484104c0d0104020f00b554a040700e45007580100007858510501d0b41c0c04020303400103142c6200f58003521800150440e42031050014031200c00c00118414080d08004100c280d0b6a508160400d00d11200107206040c3c20800300ca4000c1e416042c8000e80d0700514040c0242c0fa00030340c0000b5001307403010032410038080d140d400600a0720101d554411a60ba04c444001c00041800400f240403120201e41480451300c052000c0460800c0c0034040d1480c001054010038a10f60000f911580003e81e40c05040006590098103903400220704161a40b51524014400b0b590b1500b901501004540d128a41c0b801c2100810445002141c400c054074015610048040d16035041803007040c80f8141030000040b05014042c40495140c444150851656811038903440429040140a51140350100c012949220103100c0380800840c82040101840d2908070248010703251002101c00f2168802000304080b40d034040b041c0d4002160902d40a0b0320713401c09081c006000d0180500c03149440c90009690300706 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 433476987 1250 433475737 433475743
    0x4030c1b08030d1d030403060b0319080406020c01030506010c0b0711120d060f05151b010510091401050918070e0c03060307080f0601090f0f1b09120809060a12020309 73
    0x14401c40003000c011820308411400e400b130703444011002503074000f0031041c0000388090f4080d5910800140c00ca4005103100f14105d1404030301e8030401d64a040011070100312096040002c44c00042080c03a090086040c410006040c0c40f203602c100510303c1d004080080d10f02c5110b54102e1581f0b49090302162039440700072200a15582c000c01d640d001071400c0c00c0740071070480a0f0b600781000302e50001e00b9060140f24034000314811504090424640c1c210610a40059207009002d028003030022090310821052600c0004002c64419180d4031002c0084000100615518407171099406480394001c2465110042c8050b81010b03419000b201921030501d061010306100792000e54840c440550840e559252180042541d8070410481d0600326800340005101602c11030308a500b071790010b18404520302000700c0003d0151000d0080c4001070806440d61100e407594400304403401440110901c01c0720f10215102c40b500c1380b08900000d4061000003800003000791181584410500c454035045460741400a84151 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 433478237 1250 433476987 433476997
    0x30a0b030a1b08010e061b0c030f040b0d0c0804050a0b070315090903141206040b010309240b100e0d0309031208040201140c2a0301141e060904030c1b0803 68
    0x189640c43c0040e02c82c581c03580050410700800c08a41c12a5031071680078007c600c02c2c0c1c081150103505000600055401012107006000602000740769991a1002c405c040011030300c1c0004980100442c060a01010802c04140c7e200701079000619001c6954940b401900601a40b480300e1402904140f4002100318442d03221543da40d01c00d650301c0e140c42d105208000150b0003201e85c449103c0100e40041216072070568009042c2d55418100819180d00d9500c41d071414000c080c0d012407032a02229401c2034440301a205480340c00b0030450b0702e14007144a440c0010505141008003074050f2040584c600c06041c00703840030748011940019002003e2108440007442c403203007940d04074041040c0e406101c1002ca0080309448000d0b84100c010310385031f01640da1001c9940784001c0c162415014080c840b000741d03203003030141201145103030303c951186052100d01c880c000c040021103616842e4000c4140004d0b035403451301d210303040b90300361030000c807688594282200b86010802002e02c1404a81c0400104900088050a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 433479487 1250 433478237 433478249
    0x28170a020f03010506010906110c100f02060703020c0c0103051f0f15020a11010c03030e03030c0403200109030215040803120f09151816080c10030b06030a0b030a1b 72
    0x1c0d440d9078180003894260340c8251209404986114014449584030b00320490014030b03105c0440b41e400c841c4a021500d400303201d900c0f102c0040d00500300e129410303404014a036001003e07454114130303101c02c4c80003094490a03141105810035446102040032903600d0071043c1408090f1034840004907946250b4004040ca0724401c070342615030314a0340c950909001044082550343c0040c4150303c8005544011101c103060103c046051690358284032000840c1007000d144038045603252543c0d11800c50408489183c03840007154504204d540440c40c0e9668042030341411640d043d2004080703151210504100360040342c100313034814400031420f00c40c1071660101c00c3d8010282070480d45600e891784101640c441d0b40c1181000301c41044400410000319800d01d521000b0300f1040e013030755031014105d40c0c0d80c140001a82e0243c01180c7c0302c001070080d48d240191500b0003803126820100056203542c1c01081071408000c20412511b907459040b2846510248a071050300c40d0301a102810050949400f003400c11414003840d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 433480737 1250 433479487 433479499
    0x315060d0c080601171e060310060306060f080102040f09020f0c0d170603010b011e03020d0501120c06171603020409020304060510060c030c08090f030a0f120e28170a02 74
    0x1708005284019a40070700341200c0715030540c024108400d25008000361559401d0303c140180501c0d80c2040d0301c02c00e00075510841c4003060461611882c154040b03215000301d92a03074030400040206121450148080314042040541c440170528004211030090015205d9640100b1401e9010700703510080c1d85001200d610003000f0551151010b26081350300141c030b40c6000c1801110a1540080100700c2c643d8500d03614500035150090f034400032816200c0a07404203a0441600c5440740400c5070501081000d8607640c40c000b4a8940190301c19544a10054540708050350104524082540309804560141180300303020341d40c030300342450014001c0404842a103c125110301c0f002c95803d1040c03031044c0503140c150765240b40008a0b5280c4803425403121b031540c0e901a0f041e000160250300c06100d40c0c02260f00605610001d00b0380341c140002400702060400e42044810304103080540d8034100c4a0031b08403d0f517850755403000b456540001401c440303a0003d0241e6201d080701d10746c2040d400588074071a1407080d100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 433481987 1250 433480737 433480757
    0x10507110a2a0f1a0c2d07030f0210030b09040803060a1a0c15060102120d060806090307111906122903010b0904080304080c0109081204050c09040302030315060d0c080601 75
    0xf1321480e00030042912025000040c82c56000f241600d500e0300d010101e0110b0b0607400d44e2110b0300924000b1180e00440d00c1c0d50101a0031415803411420007407902081d800d003444410300d01000500000c03001000201503900100200d000741c0c0710701d060344014142c45509181744403c0555403241c203400052401082d8807402c3d0070340324410241300889002d030b6010b070010000701e04400c43c00250303604220781c800b950716a10f920005004008003c8180600700b0900919900d40d801d090544601702003140a034010b400001d000c20210001015030012200e0a2038086540504d03004054003810b10f62450540d02030b40048003070000344400f084c8154450080307000b081555090b03410f108c40d030402150b020b00201428800500031403205001400740b03505032000080c0e509510303658111380b608400464840040c6100c101710070000104200381402104965000880c03500d07650003075030391000418140041e0403142c124401174a503201681c188100000c13050259691030580140035007000c65519002900071301c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 433483237 1250 433481987 433482029
    0x1030b0610030c0e061c05130c0b0f040e040312050103030f030e0105090606010c08041a030f0a0b10120608100c0915050a0f050702040f0509010507110a2a0f 69
    0x120b010180600c91321806070540e0786804001c4282c00011100300f0111540100c01442a8144241c0e4410f80200c0004140710081f03040070407400905400529a81c24104805a0b0b007517144002e03142111480143c0101c40e1342e481c501150481d0b000e404408d00b8900303040010082640040f1050412086680c08000400040600c2802d0710000e840c0f02e003141e00b00c403010030101c1d4480c0c01042c5820b4000c8061500e015a50044a40864014584007051040100c1448200003041080d241c20070400c980c00e00c212802034000900e03180c00c10007500180660301035050510744d1650084c0b40109101000d0360340a50380b0300e4201e00a02148440b0300005400c20388042810710803019200301403d02a0390b000c3c208625840e05465100305090441d0601400b13128510042c0d40e01c1c0180f0110310012500400e140c00c1004015094540c083d042e4000c1c0700713a201810000080c002503503c00c003500a03040f403003c2c1080743c0d0340d40c0400009055410940d081124042401da2000d51240221103104901030b194440c120 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 433484487 1250 433483237 433483241
    0xa0905030d05161b08100b010e040504200f060c030705060601030e03030712020f030109022106060d050a110708030f060a0b0a0f0e1f02070905040c0521030301030b061003 75
    0x5110412650111a010204461864600c00c218055841310b03600d6440b20061032034840c844000700751140c0c0b9a4141e83e0a96400381c19000507180540742444681020341d507400c40360b0741d0300e206407001308640000050255074800c1c0300144030782c000e00407540e140c10b104503994070b079840a5000e46c3c4620170301e00820810752091080b54403138503092000d1400c40d1170b40f0382c0c201c40004010705441009902441036000d545881401180209051800180d45030040054070810900028044064017080f404000481e19080212080c03001030340c0700001c15644646144e402009d040d010910b1461002c2400010800780c00003c0d4001c00f02909a1841c903900c0d902040f28500590080051540c8180a4541058003a0420031080291810010212003208001c203456007914000160005449840510301c50740620150020381441c10003440245429102c040200c2000e10a450188040903841c0e15090581d0754040301413500001600c0d560350b903a0070000f2031b0480c29107032503100350508517122504900074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 433485737 1250 433484487 433484497
    0xa0f17010b070f1b120515060a150507050a0f0203100b030a030c03110604030f18080312070504120c050103060b1c0b030a020d05030a09050a180209040b060a0905030d05 74
    0x100c545480e000140d615480c0000010304110381c10710700143d42180304c056800260010b0305500b5540e84170b510007424401e00d010290440c0c1d688001101062017215210840c1c8603040d00d500140760346c8800752000080b5010300c41c07040082c3c0b0500860700c0b20400c01c40c400c004900380034000c8040701c00c0c1c00e908550200443e101c1e1024150b240d40304000c91f800181c080e0f50400403041c06400d10680880b1601d40c2d0b40c1c02c04034112000c50000c0e4106040215903500821440035586806060800050900361029680d2260442f400303141240032000a501e00e11613001c41c0c0140c803a2031080c0c1c201818500d4101c06020b00c80c00307241d01080c14414013048100c403020a0340c151201101014001388082c42c102c2d001401482400f60f054012000c1e0070000d600c1e1140017440b0140b05400440c0c1d10070450300b00501c8420310f074101f24801c00034040c00304400300301703c3c0248114880c04040140d890480f0310000c1c0050925064407a003041300880e0f4000d17403913003280d001000c990055095403203022031160116014030070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 433486987 1250 433485737 433485749
    0x708010f060614040b1204021203120f0714091e12010608010c0503190c1e05120f0606070b0606070f06050610300e0106171501030c0e1306020a0f1701 66
    0x70a000706c4010800e044040c68020340090204003003080381d500b206003154403c00001c1d5052081d0340604c4103410300080b4280c0e006541d031801c200c0e4500c1000d022803a9100d906c40541c0710381501d49581e0341a00101240300c05841c00280942c1e11408054002c9000c0c01c21485002065484c01c401016003500030000c0328480d003041008200501d01b4000341c00002d1203403900c82401c100e6540d1900c080d040c4540207102080d1b8480d258152100361002d880c0812100041103140712040800038800d0f951140010343d0103007580403011003642e90310540441d110307001e0058007030705640d44110003109000d0184d202500580094901102410000d001515680800c0c821031041c2501a0904000104000c2e1010510940301a01180051440300001c1c20340d00d280d00604c081300a18101003110a5080001c410300c008802c1d036140c4d56614646034053324421300d1044203040410280000c42c03200414400c581ca0940c010001c5464090340b0700f00a2000008243d92008201000038981c1c219000e0840e050485203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 433488237 1250 433486987 433487009
    0x914010e010b0a0210060b0904110a05070330090b09120d0b0a0302150c0f0f0304141c0602032a070609030c0c03050c100806030a0b06030708010f06061404 68
    0x4609400e50b0081e90001014100710300607a011084401014041c03000100b107414038154940d00510200000c03500c548940491441007003060005840d00007040d148500c0d01401e040740e00c000a46402e5900458841000203051810410004100c8803079124401302406404014a00d640d08621103540705058004114101404e01180c96a03a00c0c0d600501d82c0e1103c007402810105d40c2c0d03513010030928280c0c8109284550404911260017080800519003003900c01401859840c407003481c416180d1055000b0a083c40c1c28103101604141c603412903e9840203d001c043c0d40c070f8000e060412100a4006444092050490911040607030a14901c0b941e0003480070034030240390a64940d034440080c0814241202800400246d100103e032107804c4c02001540110003410300d0045401c20800c82070502c259001c24403c0314000d00a8a48000030900486680545031002544580b0002450710200b54015900c035820501390300040e032b03900c0d0401ca045400d69151041c40c21840c0940140d503002c1c600401d00151 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 433489487 1250 433488237 433488239
    0x8150a05070e030601051002010b120c0f061204080304020a030b090c0114041a090a120c03030806010503040f170910110f0102030118090611160215190e030f0106030b010914010e01 79
    0x22500c47c0f200240c80e1321a000008041103908003242c0341c0103403042c1102e685c0c0c2188103500042d00700f5803801c1656031002c5581920b04508000ea10405142c040c02c0a0706581000c000582151030b0312100d403018503002480c0c01e45529140003000e555010303491100c0c0c0044c0103040c5500352041c141e0282c0701602c040c2c501106000c80044030200c02a0000261143d110b40c84c1d03500000d5680704403d0b6201e03d02d000e4806060128290700707010740b0900e4090101d0381001130800400c0b01280b9410a0f4052040c0d20038555044407603840c10b27212103401144a0540d000c50700c078880480d500d803c04170256640359080181e48011071210000c03800c0307000900c00d2035511008001c004032410255400329100a01c01c900c0040e8051000030a0380040d04a001400b000380900310b1544158030b000c500c4091000078041c09e03546000c2c4402c80c0041d02031808643c80302030052211240103c0c0d0f50910825201c030615100800c903807980d03802c00039000ca40c01c1c03040c08c0282d864001080b220320442d500c058169204059070902a03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 433490737 1250 433489487 433489489
    0x501090815040f0803090f0d020a12050c01060b0d02090306090a210c0b0709081c14070305040b0a05030f1005010e010f1815181a1308150a05070e03060105 68
    0x541c001407046502d0381200d00c501000a01d100301950103406034000412134510042140d40c030307140307040000700107541c4129110000560b142040c84015107082c0340c91512196048022809018981c00201da40d902c04580702900c0e203029409460b07194012411100f580c0c4030004586d480c0c114041c0003400211038903810640c00340581010380c903101c289240c208041601903c42c844109000c3e1911030000300c20781410480b42408100c550a9207011074007420092446000c098549110310181014455020486400703242c084c40540e0700405d90340d411980d69a00340f540007456a44220792440417150a640842c000001c58801c2d90103507107040c0c580322980c0141800544481c0088502c4a041015924000200c5011013072404002d1200c040000320000030b060000d841d00134042040c408401a451040000c3c0d40816403000c0d5a02481d009540d80d00c814054406004030785400065540c46918210581d140c2e804603c2da01c201ca00b4601085a502d406008031004041e0142e9664140c2c0308000610203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 433491987 1250 433490737 433490773
    0xf020d03050f0a030c1d1e0d06060f0305070b04080c01031109030109030c1103011109090901021b0d0801050d0b04150608070b1207020706020303012102040f1505010908 74
    0x801400380c1041d904100000392061074903400311401000107034030f86029400960b00000303500c0000b102468401d81c0b0b180300300042409102407511050405100012144103611450b5640403015000001800a81d131215002c4411201600c07003182c081c03148290016042c4405030540d002c1d500c0c0d40020b01360540d180320046029164100801c022031a040200d00c685075024419040d602d40719441d0104251510306090f11500e000c211014001d9051465135a50024840300310f031420307841180c00c007115407103240745240203014036100300d0f40e903051a550100010070001250b10f00e015a50f6113400c0580c1e00c7e04240300c1d200e1060070b00180b1407619040402d00043c25140140c10800203140d0006050366550715131403800d0403543c01712110401c00101403e000d8001702c04070b94480c445000a00d2041e141800081d07880c401485100301c20356a461201c03c0e20030130100c41e02160b6400900501801000c1248280103080710a485c0385603041c036000004455008108043c11101c0c401c000e003030303501549007440f11 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 433493237 1250 433491987 433492009
    0x2030106121a06120421020703060921180b1e0307030b040606030b0301050606030105150c011e0b011e050313020607050106060e1201091101111e0d090e040f02 70
    0x248803802c0c400d15003154644101130b0610000301a0b0f408058100344c00c2041e0111308094410761605000d502c08812a80c0000e41d0100700d0340e21110005121919040107002c03c0c229030201e05c01038124200381191a54061880100d405892420202465aa00c1c01c8003a602c41e08040038801410410050f03042c0400002442d40050b55050100f0495901c0c80003404980c02e0303030000340201c1c0e500c1862044904092041a80c8204159500703455541040d001901c01600a5114054802d0008090305501c0e401e41003000040482d02e0318009441c0034000f4100500300c45042d560005031018040f8600c49907040101d89600c985403181881c5868816403442c140040450580e08000d04000303410008109100325070040c00c080c0e40d9810400050020094049030020740c583c9241c2c109003001000c0b41020001300140207090808851300502d00f000c0d41e003060720480d1043d10024008580b48040311010030b14031a089010358448400507180d0703900d80248401914040d024030401800a0010704007844811 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 433494487 1250 433493237 433493261
    0x1b0901030b060112060609090609290102031326160b0a0201110d02071a040809040b0127090e01060807151403041511030601020a032f0318040203010612 67
    0x100c04c04011039901e905607880b030b034072800000e0603000f01080010800e21510014000d0454240201844000030140d19a551250426022105e485080240e8000c20031100d04841d18070a0f07000c03881d60764002c0c1da0100410300880030000880352652040400100d5880d40030031035007088031311007070400c4100750707054104030703050130070342d03607102124040720b048000600301e01d00c00c6820250ba90b0f0190f02e820a0a405000f040d5201c040700001408009103255042d03c10107001641c0005040018600488180a50391a1981c401030024044d403905a100c0c0100c0c2c0030703505c1140e000e1180b12039107004d0f00d00b281d081d44071b010300c1904400814030a12054000c041078006551400b040e810b9142e000d648100d074400d9038222034000f803582031454170000c02d00a0f1500c0210180ba864154030f41035002070b486010802004040045200b401c820540c180140a604110303080007400a021601c581c00355646d118814662640d04109058209458030b0b00071613050340c15590310f955066010340c50f141c0c05407950122030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 433495737 1250 433494487 433494497
    0x515061605160305030405120a052a04060b3438010f0603020304030f08041b06030902090a09030c0308091c0527012f060c0405031b0901030b0601 64
    0x120555507400700c0c2c080040d40c0103c000c0c1d599903190000b009100e80345500303000c060750801c0c490382010641c04074540403124050040390107503010441d01003c04500601039250701c64940300020072400081409086400c00c1404139040100138010907010303070141e07010704100e0182c1047d50000043d11080015511340e01c00b1780f00840e840d580346101012096401d0f14050300d40f0500c001001881c10588001d00207054a0a04500d1030506840003400b02e030075004180d062010301d4010808020001d5951594220ec000c0080c11458584900501401e0340c500140e10480c15803001c1101e81d0000e00c40c52100c8c03a0705071600da68000301c95400b95070400b402007035035180b40038000d582c400c142c09500c402088101181d0340c01d5a5803034242c61082c20120060428450800848042440317a60842c00100310444c5940c0f180500030680304140b14646540b08035a241401680b062000900007480988141d41045041d100340d08000c203281440c0390109400c4650004050004201140f40c032020f003a0020018509 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 433496987 1250 433495737 433495753
    0xa03092019150e04090b1f060305040305181908030d140f130c03050d08060a1706073603061d06130309050d05060415020a02030904022212060515061605 67
    0x80345940f042c100c41c0d1580d10580315240c1c1007040300880c213147c00740c1041c1c01c04112500741500e00074040e0091005043d5405009c0440c5401a0380b0340700400c1e40c54442c814610740543c0c031900201d4898100f210544400d40c02c01040882c41c040d00c06205215146582c2c500120355503a812104050960344029245172104801c00f10201e0420302c203440c0d04200c9903c8607210b604100c010320803443c0d803552141c4a40602420410350003400490038a40100d0245451952020001c10103144424207000010304824003d00910b03281e00f40381650400c0300e024407400c00000401621003403550991031807400c201d4010f1000075001100c0e4034058030150340a454260324041c1c072040811000700d26164181c52551049082008001c040410340c0301c03c840302401541401c00e110800b9640b4042c501049215a8001c02c001c4a4556800b041c00c2549003ca440415499580c19414030000445a0f05032a0300303080c00d000404a0391600080039403600081c00092403d0340110510300c0448202c0d100301c40314024030003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 433498237 1250 433496987 433496993
    0xa02040b0301080d0f1715031609091106070201020717100504050f010c0e0604031401180f030809060105060f071109180106080708060106050a03092019150e0409 71
    0x3010314060720f1104018910740d04001400340c4000084c00c404800c11404040c551080c0078500951a0840c0c55403180c5017510f81e0350030020b0705120610440100840c0400c07000188030800740c00c00003200303004582c00001000618107000941c45080c402a0140e40420403c004c10b01e0220780a185d108880340554104a4105109005035001500d01340e40700c0c0d01c1108021503449080c420042d17005c1c40c50034540310154140c0041241c60059220150019200d441080304e104020b4001a044207114801c026040109141810040c13540d40c1050b0b0004002d44001000c9400c0040e0311810b139040248142d040811019601c051944404012604d080c201c1241d107140e9216a8001c7d405044410030a403120310505000da0700319041a40302c8961940700310001c2201c2daa01059240c19200103140840e90b414252000750050b101c00c000040019603e441c41200000185180302d594550486241000e034403000840c2100705401e00a0301c038124948100d9000c0c1c07501a040c0c00c08129005080407681c940349403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 433499487 1250 433498237 433498259
    0x920030a090c1203090e07111506040b090415020901050d0507021c050a20030702040c11010b06120403111c09090c1107060503150a0801021b030304080d0b061b010e0d1112030a0204 79
    0x6004030b041c0c0c13118038081c8092441c00e4020300ca01d0b0400dd41d10401c45140ca919000d030401d06003101c400e041c17a4000380540d134691148040f030f120803c0c1001d040c440703414000d000a40d100c100c3d88005a00c1d007603010300020721510400498265242c596110b038205d071246c0880e032100300d50840130106944400c000c8940142c8030760250000c4152152201e10345012000409400d40d40354502c0e492160004101e4065000c0080c1809038100e40c1502e8056641500030124624181007030300001c1c040c001b0380e10581543c5901110b08000d0321800441400500300c0340c0340980e8405800d0300040d070b40303802c50041801510721650245520043c1d10703440304c170a1500c04011441c21070083c2c0140e090741c1d40004d18661940c040e4000444003031000001180356203099103441045000c1ca175003ca02064580303440c20b996550ba031043e1036481010b110707403101881044420900900e034401c510703180f50042c0c48a058080d1f000d401c205441c12020340107410091041c00c4003507641e0784000c2520058541c03e20010903030300d80c10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 433500737 1250 433499487 433499503
    0x210b0c0a0915020f010b0a08123a060609150f050d1d010b0603040c181b0c0302070509090709050604021306021011040f0920030a090c1203090e0711 65
    0xb98000e800c8602800800a003901c10110446004000755801040740c100d0024030140d0880c015500903440314800311460756452070f541c41108007804e600800e0b204c10f100b000c0c0c50340842c42401608200f41070b52820b00340c41c0c01c0c80d580304d84060007044100083d4000d0145595015044892074401d15003d6844031260844040c41541001c01a507442c100c0207142c42407056104009084640605515041d90744145906043c003503e00d0203050212040340c03600301d94100b18510119040200c80c40321080f00001d0035962030b21800e070018480c2040020b810b0818096103405845a80042e040c944e09000070031000d0b0030043c200315086035080002920b0400d00001340e5014224540c09055545400da20000644146821008020800b0001002034420002da194204c0d0040000880d100000c490200030a407030b0b00c4081d84242d800081002a9150395030700000c02184070700700c080e8042ea1a030727140107485254240d008000c01d0f20ba000c24800ea40e500c1202551040151905000d1050515110b50804d00c003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 433501987 1250 433500737 433500779
    0x7030b0c070b103b041410050103051b1f03090507210f0203010f3803030703180b0c0d0e120c040209060706060f210b0c0a09 55
    0x4618601001a00c11482e600b00c00b80c1d000d448a458140707255452558101070b107004001400c3c2c00068403c411242c0c82e00780c10b007400f4504085038609801c007224660101c2d08900654000c026580c500c0868500c501d50503030b03030000010128030729064403043c03403280740c281520341c01004250300352000c04e0010950300941009a40c041044840751628a2520803590040e221100c042d6100302a04601015580d101e0760f001945103109001e50700100b8010101340e104402c0c1c85080910b404403110101520264000b4520342001e5440d6080c0c0143c00384107040d03103003542d0541040080d500807074400c0b484801018500310860500507a18031084400350f00041e85104260415001020301541100c04840100700039100701000001081d803941d00d410341c64000d02d00c01d590100316104e103903c0e10300568028540c401c008111250310b440c846d001d41881882407044140324035030900415181440041c4a00794802c281d040d842d10348101000f5250040d040c880c2c2080724100c000283c100c01d5a11038605459 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 433503237 1250 433501987 433502011
    0x506070609021804080d05180d320d0e03120403020105040c05010c0201020a120e06040605032d010e07020a1a0f010e01140607080d090b0f0a090309031407030b 70
    0x1d0076205003c083c09000c011078400b080c01008000200303c1c40411035100200c0743c00001416900ca03260a850a0350510185495118200001e03114a8000c92a210910045200514241c0c1c1c1c0d0216542100c240850300306810340140a000e20010850f046010110080c000351307030038100c85024003280c1f000d040380c0c2900141e440e50203100c140201c1a4208010b840c080c0303884200c102407500041e60300d100c2c8140080c0701e0f8020f5020303000f03814450002c0c0c08840400900590b43c80d503440300020134a030015544560152542c4030196844030b0001a500d140d201d141c4801a003a82c60440d841d20000703c000c00700010350041090500001d640d40c1c01c200b20044844840042c107043c0303283c403102e502c00c050701b010a00d00c090100500204113450580c40d850501110342d185e5038142071a0025841c01815100c2508500b4aa140d008024500045901c00d2840304498507265480c08170400c203035034000c2005400b06651040501c0031408118460f91100303400c50440309540e650b696541400b41d400c8400c102c0c010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 433504487 1250 433503237 433503251
    0x2120d06051005180f011704030e06040b0406080603010902150708090a09050403110d1b0f0605010e090d09060c0605070e090a020901020d1805062109030a0f0201140c09030705060706 80
    0x8010b0440000c64544c1030741e9514801600342d00180c2240c1283c8550009505158009030415100c4c454403400ea400143c0099211035031614148200e0b08940109004620000002951407d05107d80c008441e0024400320a2a59104c3c070660142c1c071962098841c940100542d034100d48036100c000006011a550019441c43c00703040080c202c21107280c42f0146508031600e40035013140e014007190745ca0892100c820044407107920b032001000340d00000003012642054000107103000c8440a0a105d40344c80800d44100c0001c5490407106001170380a00030200b0360784011074002c522a503210b282d002e04a800c184900c1a0200c0000d01d03138034011940c011071243c0025003840556414059940c003054a414135441807140f001d040610100c49008003402040d0100d0440302d50180c4802c0b0381400c0030000300202d0b46c0d082c15081d641e200c2d40400c0a04010070091414445210710511582e02d1007900c1d80408811038445402c2d034891648041100b03039040c85240c1e808196035a41c1c03802895180c2c82100300150303072 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 433505737 1250 433504487 433504507
    0x3180e240306040b040b0c0d0908040905091908090402040b0c0c030d0905030c0603070314090703110d031b03021c12050c12130c1a03060102060a02090102120d06051005 74
    0x2030120391045000c1d40020041c00700044200f119550443d81c005c4005038940d0f220078044400c0c1c0071b40305600100c01e00348002042440003a000410554102c0074081c4015a0303200d9640f07035182004005054041141052280840c0110000e400c01d44002000903182c19500e402100040d000700070240070321307000400c1d0419540b800308600d0030b01c60b02500b0a1810b03030745407a0020ba00c4d400000ba12070b00810f000000a031145100380e00400f100b0594070008021070a00b00d40352681d42000e400101ea0900d0030508410040c940802c20701000e55050b0b5403800440d4118100300a0391840710030460175441805903454000c200300540682d003040a40e60703c0307155130001c8000700940f04050200e140c0100100f00d0340469103100710303400ba844000384203100910307002460410000c0e00c8562100312108040112900d8041e1204000d6020740c81c243d08403011620340c01d412008a20440e03d5076030159008645290070009000b0180162103014840020500d0b5a480407403052540c2e041c654000850005200d262 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 433506987 1250 433505737 433505791
    0x20a03080d1a010905060a120902090103051005070804020603010306201804060506041d0411130504050609070806160201090b010b0403020102070905010f0e190e031b0604050a03180e 80
    0x40c008091a1102e0040d18045c04034040c0c0c4a40c81c100802c00c078005d2404040300c8025003040d04100c0d4050400b13149582d40781021a2182c0c04210600c0849040402107114503101351301050050750001d1543c1d01d180d1844d603a800050446011071403d140740d180c0ca401d01405040060440340d0034401c192490f1a14803410001184d80c0358101621a0030280f0060200000004400551402507681600300e9221070070011441e0b02040040390b404000d585081e0840002c1f03810031030159129904484903621480000d9450304094082c0d0a0154003140020710700203051038400740403540600000540070002d80758601c03444803d03000403070b442c1400a420400c55904000788001040003040800095040100103000b401451061001060000300400da035036031604002101045068810014119003080c1030303450350020007554168032103500c2142c9100d0307000308006220b65400303409403461744840c5d6400d071042540c420001c00701c00f010078404160300030266100f601482601035190300000782e181d02410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 433508237 1250 433506987 433507031
    0x315030d03021e25080c0f030c030301030611130306020712082a0705060f010614120f040809040f091709060f0a111f110f0306042d0203090d030209031504020a03080d 73
    0x52940200270042d01480d000c01071764150307680b00001003901e02c19660080c0380390044480c1c080800100a40003c108602039005240403807007415020710101c980e11003503e2004048400511580701020b801140d115000301d80102c0003e10000c150400c0c1e21034980301d16100040f59030174104804400184070850300496644013101c150740d00d05184c40c3c0c21201c0100807040142401801340b0b407100104041110034815507802d140c0141040090320382e4004250050050b1a0045c1c0780043c0c01a102030b141611001100d41402016040501d080d0780c80c0d0550900307a0022801c070040051909000310100014008080c48450780d1084086a040400e400411500d440c14601082d90040010f00724804200c0f0540e40c0c00b40c42140d0000d03490710308000030b9040d810001c000000351100d02401440c00c003032aa000d103000700d0b000c40448001884002c010750492013200e204a40c1a4400000ba66031202d1003ca00303640030f80b0140c51100c0041e580e60300e507011070308400c555400a40d110b1300701000d075000b1070003800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 433509487 1250 433508237 433508263
    0x1106130e1017071401050415020606010e03010c020d120f090c06080c0a0f0513090c020d0e0f01090b0c01020403060903031a0d1101031d030315030d03021e25080c 71
    0x942c1d100210a03416900c00042c891081c00c2001070540245a80c042c00c195030090445205440d0262405c1400a4449004407a454081400c0b507030304451a080511403203640482d035800501d8a480b0500059030750f10700c2c108803440d002c1d844541000c0c07244040d0252190b407510444400903014245400907010001c0140440c5075100f00f44103040b0000c0d4018400015044181811559042010b01ca6052004240c000d00b91050410301046002c541c00a00d10360395404c0383e500d06080041e96010404401d100d030450318001020b1040610100751503200070308100c0b034a040018601552550341134256021600c054010a55a240c840e040202d8400b1651a9081c01c80d2403444410642d0740701c800c0c2121710510300b41010340d0340d95030440801c4482068401020311000f16500c030b240c24485014444021a42680640074500040c5a120302a00a0f0703240d20007111400081218011a000c2d5180c2200c034010506a8007988084003a108443d510280d85001d0703149180d444107400d231040d140c8900d0b01300c11 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 433510737 1250 433509487 433509509
    0xa050105012102060307050703020109020306271c030509160e010e130308071103160b060301063204141014010e1e03011506020729071106130e10 64
    0x2d540142d50b99001c480d88590b00c2c1c01c10545602007030504900400c95004029018491002805000000f10940b44000d00158000040b03494100d4209521807040030340103103680c500340703a540460a0207600700e541c0c00301c0b03000c0071911241001042c4030741b011030b66803001068201000061000045e003100341544a0070018500d00401d00a42d00203001500c000c0001d0100446c0c100f201c2d801e841d040c0f0807a481022580340142402c040e03030520f56641c501c00e1710b05030f10a62800c1c00000d49031030106611040c082000c0c41c03601e00c41c43c0010704071032442076007464282e1041cdd64900d50300300c2215500d0103e02034006155040c010710704108180c0340003400e00601c1070503c8a45e50000c030280e65440b9455003d00384144964601c1620000464090040c038682c0c002002245803011904075070014102c3d040b034070340c03481002d10484640038010807004181e0188484e880108a80d60100340c80d018206605940075006d07070f1501582c4240d0890182107a00100c00300c1c1c01e1803040c0928205d0608414020301411410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 433511987 1250 433510737 433510799
    0xe01080c0a080f06040e0a0605180a0f12051c0c030f0e031c02090d151a090f180f01091502040506090d050309060d0219080103081b0a050a05010501 65
    0x4050042c8500615140c038112180b00020050f46450f00142000c00c1100c08540c0c1c00ea690f0b19200e802380000302c40c1a268416010401c00c9034440020b5101040c50300303d140c58010403003544818030109605410707442400300c20819004414489445600300ea40940000544802c081074000d082e0340d200720700d001d203050620440b1142d03200040111880708106001c41c5540704c800c0d1000202a0203103494070355210030080001414458100003040801c840714404001c690900c4140344d213004030020b8050b4000b02050001001c0d4010b42c2d0110750482c0c6020100c11000c40b148075210f213820006070f401602a5180e0000400304280903000d05c02c542900b02c415400d150400300070681c640558040b42e4411408a5540b80921109000711010003101030195940d405c0d45503003180c003a40c8030023a00441441403c0c6140c1e0a14840c40305281602da219142d1403500440b4000044080c2501250101d00d01401594400040341003114042c91440340001046541c5459495508180ca590a400c0c8080d11200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 433513237 1250 433511987 433512007
    0x110f150306010e010201061205030306090f0c04030b0915180f0606130b0a03080f12010b070b150a0b2101060c0f0b130818030618030316021603030e01080c 68
    0x40d01d600090030b181c004156000480100d02601d0303194841c41d51100c0c41c010b882c040c8a0080000c1d031103490180e480c441d2684a10240580546045400c00c841c45130078030092001032846006541c1001d08001180d0040c484c040b004842417400360b8106607030319083c1c004038144150620036090001030141c042e02080c174001c4041078007010191540561030f07036508103002c079079034540143c8000f03107400c52100c1761134016040000700d495102983c07101410240800001d44d100038001151100ea0740140c40da0751a885078400b522000c10015405540a454090007080103d4520003a081c8540044000c40486c0f110190311401840182c1040c401c0051180c0600c02180140c4508850258040744070318007907840040502004c44046402801c2c01030018020402102041c1e010703107440c400310300756549500c800c00c601380700280c41e1445120940007071000603400300104003902e0100d81c00c0d00650b540790603200c1900440031440e4004802045101c1c0504205503408080350b50311420780b000c61480c12071408 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 433514487 1250 433513237 433513279
    0x20a17070b04110d050f010203090c1509131e02190206071e0302040b0304030c11010e130f020405030105070c0b0705071709191d101406030a1404110f 66
    0xb00090103004908800903029110700e000303518807980000664070350080c42c180c014040c0d401559641440d01c0b86480300c421601c0c28003030b505400d010014016151001c400c00380080181c00711040b04171300360743d2450300c0714403e0040c500341c034000c07210080165190502002c240d00c4041d540304402c11580144108221140c202000c00021065090f01c0a90703104805011400b03407142c0d0300311300150750010091000b015044804010769900c40d01000c03151038480c80c01103c580d0b03405a000303030740b00d80424074000300308549a1200760001e00411001d8645a10350021038295401500c6c80e00c0081c0c91004480d090050203442d46400c011700703191103464000903032629074075408600d9031046000d100180b490496a90f4101d480000304818250341c0d011350340c402d1842c41250842855842c0084100c0014160304521801102911188401c1c49516800e000c05d1000701d810040401ca10303141e840c410500703c0c070310007541c0c45e10940c03050001d2441c20200d0024407210b464401ea00b42c1c0a8102a440c00e08040030b10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 433515737 1250 433514487 433514491
    0xc061a03030a080406060906030c0501031a031b0406050307060e1306180221010f060909150b071e050703030e01031e20030c04050901051813030e10020a17070b 70
    0xd00c1d2003c002c0c0c4543c10034500034001d079881040411b00c1c18800004110a2040030411608241c900704440300350480304a1410034407411251b4180c1013400f85004407000c2c212032120300d500c0607100181c020b403100007003031402545030403040202e0b40019a0307082d94549594100e02c0100d01c4e02c8180301d0b0500e00111107490001c42c413040e00009401181e070b08442e00c03240d240507440300d03a16450000c2c5947c1d030f00045042c000c0d082c040c103000181075a90205000000e8011540c3c40e00d9401d400d142903500c0c14003c186d990f002302e03604135021030000c05075200ba00310210031440c8040c05403011b003030800d1441c42e001e09400499040b0038181400c260107400360102020204400310326882c0041540d5404580e104030a4118191400c5500c80220074441c20000d407401501c25910143c03800001640c0710303c00c01507403034580c01d0180d0400840381c00161006d5080b11104c1c154622a00b003241e040d403c1140050140504810b40c1c0c0b005a0001c40c81d4420f2004480c2495400e8801001c2e017441c01c01c440d11414000000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 433516987 1250 433515737 433515757
    0xf0203220b0c0d020705010c0807110a02010905040207140f0d0306060306061d12010f0b0312040503060103030e1f030b030c04021602060f210709150806210d0c061a0303 74
    0x1085801d20408aa0105d89840380e010000300004100000050410f81041c0c44000000d085c1c040e101c407000c040060301c2c071101c40d0142c45811b2003030b18000400010394400c00045424451295000c40344080401003070580c145854082c280500d00540002d04450090f0300600406050000c2040901d41008400307201c158003090025401000c1c80100f0070485120906860303030b41c6481c0b6074100000c2254030010910400710b0030740c0e20270841118401d420b401140940e5505070880e20040001902603151030400c08800751122940c03107032001c2d10714a40b8071071150b42c002003502d40c0c075a040d8610f828417401e84400d108640442c105841d4080c0109070360600780b0000d02030840050141d1703403014060240c94042403d130b0245484141508881c0418180640c2e440c0007003010554081134150714807880700c9180c002540e5080241c0d444000308603140e0408882c0307200c801404002c2c1c8001000620082c4101e80c1142c9803031140740414070b0100100c840c0c02c44521344445100c980246240c2e0040300300c0d803036820 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 433518237 1250 433516987 433517011
    0xc0201050a0306030b0c120901050c03130c080a08030406150f0b09060d0f06060210020f070f0807140f0c0d0b010b030402011803150f02090d12030f0f0203220b 70
    0xd107100940040410b40c10180c00d00c0941c2041000d505441c000800321070b110300d40e20f0205916603c0e489400c2e40e50070399000000110900000340510304108110341031a004040788500c0c2c0e03940d564405d003010864241a00c3c08440001080107200081c0142941e601022030100581454500141001221402160001400080c1c0a01550382d42001e5601881d4204010132850000300e50003002001a407107480d01601a40400720100070480c0300340c500c500354686d1601e04c0d143d10f5a5600f642000c5404c0c0840d5096028019440401e0000490302030f1900b110f00200300e03e810701148145400b9600381010701c1122443c1d1210001307030440b03501c00c0c111402a008147c0700c0e220303840107a514003e03040401c4149030a000d000800e10081c3c800800c0f022629110070000442006502000e83c4100303480d407904544165011f0002811040c0c54649841340740c50002520040c48040409580c501050341404580100134041044080c0d4160400b803040c012244d1900051503640d040c1e0110018441700d1942 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 433519487 1250 433518237 433518247
    0x40b040b0112150e03090a180c090b03010506031008032d04050d08030a06081207030e060f1801110102040e04150e120f1e032406090d020d3e010c020105 67
    0x90108140c0ea40d860008001f10901900c901191074005207000d203082c0a5400c1544107007805005840f030718140c480d41c03101542755a00740014810142d10252a40480c1c2d28400000124003c0070f1010f8103141d0072800d02c0042c2005280310324020880080c04801a102d01004100b01e903980e0034070301c051815440044a0788039910b200c807580041c0101d600c42d80312401a50030010ba80c40500c0d0040088501c652140c1402c5420f1205100d00f134060074007808a00c003400c101c00c07070005441c004003040308074051519281d202c2d140c070035050998000da4000030120007500305000404c40500720a0210411100081000400e540d126a55800c10820521410f08000400103260b040410854540c0d9a0111014010018a40710340b9100c0e03008480e03000d00c1d02030301d04001d05068075061809507944001055181000d50040c01c10020181c1400100d034881e81c1410705000284080c03541603c0291090500c4000d03880c440340042c248001407500481d54103800200364041c2c1c3e089501d0346a10368081c81c10340d88403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 433520737 1250 433519487 433519511
    0x5040317211b04060c1407051002060703060b030103020a030204020315060f0a0e04051611030c01091103060a0e06070f1206080303061002010524040f06080606030708010204030c0501030b0d0b040b040b011215 91
    0x11100c1f5400894126940380c0d1941040e40d000203009003e00072036030301001600d035510050003581c042800001d5100c40d01910800252400d600611307046401e6402d0780307401142c4000000c00a030300803101c040c11024013003119180182c05c4081d0217104030b01554140400d2a110a403107604000308034851060103041010b4440d0750700100240d0720807500c00c400821008600703091140b00050f01c48000d0b44284a94800501062190300840200d55400c000400b0644c036030f8501923901d0b602c070780248010402c441c00c1514071048240100002890b1711000f440d41d07404c04109001d2000a80c075070308000d42e8101000c0c0040d680710b01d82098030004210007104a00051800000d0280c1940c803440c9040c00d04011011400d02130100300d540c09000304508903550b159452840f6400d0b03000d944000341c02c21140c0a41080694025000f10103092401003204503040e180381d0b21314681034029101a40c0480c56001007100b00807490f03d00c540075064000e0860046405540e403a800b00030400c0d852401d03991285214485 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 433521987 1250 433520737 433520743
    0x611071d0606070c08010f0917070302070612091505072006010e070e1f080916050f1f0f030b040203010b03191b020f060a0c05040317211b04060c14 65
    0x5006004000c1c405d0307e68546402000d0800620706440103200c1880d82311902040200321000ca03507040d0043c0101074500301d801d035500b05c8030f0315160104a0310340c0d1301c0600007919800501ca5030300015900044038204102c0040100108480c6510414a4a80d0ba8a6440e00000728181100c005e22a648016034403003600311854903003034584d69080030360303203961440c04a0480612880c0160560f00d005055031103102c840d564460348031b814403040d131142c5804c4c070445c00c00914136070300c0400c05442c1c2c04204a40020000c3e00d03a180d03c01000000c1c01c91450030481070340c14001d41e000c501040f02c0c00d40c1154108520f0120601c005400b420440b50003070010540c0e14090b400c20070301d01012030b2413440c07020a442406500c0340c00301060300805001e400002151100030f40b0400d00c0c04800c954038507050604598405c604106440d1107030511030020b01600d41403882c43d88900030203800d4a000b4050b5400c10032081c468010128020348441d040520042c0201907004078800400390b0810b101d01c08481d00c0c040d410382 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 433523237 1250 433521987 433521989
    0x150b03100b030a0b03060a050c0a03050c0405030f0709050a06050924040f0b0910030b0708070216060e040f0b1509060403080f070c09050108060a0509160611071d0606070c 75
    0x107007060080300700f05a24a82c0d900115860340d00380e00707850f01d5a980130624000c9034401c80341c1110446060060310380e01c43c420b9016650103102166120b14040c0c40e40700180c94480c54500c22490303584441401c0c0422001800b40c203030070100000d82402040e0501000500d0501e0040030804410b002c2030111f040c0042d14141d40c2c4a4070700140080024201182e5040081d04200003003501a0704148086204140041c010b14100c0b07030007019001080e100c00c042118a03050142480003144201c18614682200702c1340540001c0107a506c0d510a0001c600003840143c400f00489400034601c0e0643c2d0300b020b501c1c0d0401c60b50900a0700104980d40c0c04128000900c640195040a410800d0100d0a94003041d81c4900818041d4000d00f0480b9409940c0c90881d400d40b142400342c050340b0b402000100b0724a016a420603504018210141c9907641d548a03c607410b50384c5c0940c4100c0002d46401343c03080401e01c0074440d040c0070302300340d5912503a0b08018024030000003401528240c000c1400054039020701500d205080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 433524487 1250 433523237 433523249
    0x601200a0822060f0f0c1211100e0703020a050d030207050f151305090903030412030f0204080a05060a230c07030903020d060b030c0607050d080619031410150b0310 72
    0x2c1468039808000d11640a030250320001c0361701140c3d00c418881c064055660541d1388034032000c1004070324034003c882c0f0405180d9043c5040c45811345030341d21001d5900950701ea8079503050007800c50703d20303500402a840c1c410340e101c18021903400b02c1040102c1d602040d43c40035184266561a002c0c620600851a91702943c403149024074404100044500d000000400842c0c4088540c11100e1f00c0d9269096120712054600501c0c0190ba811600802806134008000004000c0300040c00c00b0f03500d0034100e003000d20703062048640350424401c02600414910501407100622a640544200d09020030011114050b0810552420125015040500c56000c0c00051a8041c05a074078940c0300703203401d501400a8241c601e20078041c400c1a01400c1c01d0203c01c1c0c03011507030440020051711002140683e02803101078100340c1c1203201002c24001c04c180c0180c0310300c002c0d4842c8003442010011094180d003025034102c551241c040c01c1480e0410078912014166060f00d10844640d42c1d07946400d403040f207601190364405 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 433525737 1250 433524487 433524547
    0x8150103110f1c0c051c110f040308070b070504050a05061c020c070801110a0c061e020c030a081803071202071a040e060405010e0a1d150601200a08 65
    0x2600301d0490f00302d15091810380c48081880303108010b04041e01d0500030100c1e00c2d0445080050208064001500104000b11540c60f4032464a0540c0c1c4a424085d403003078000342ca04100000725441013244440381d8540c001140e18000e4207007810000041e00da4034071407145502c10302d40415810051000200d10311007007540309804550300c00b0b4925045848040f188100505940303407500d451403180c000b00c100c4070504000d0b41e0707a02e040b6056130b480c100101581d030b885880300c44107404031012a07602813008201241c02c1d94000c54441c07080300b400510410008201000c1c0c0803401c40d800184030b00000541d040c4d2039100da10070140780007104c03040b0310344803003a8004524034041c40104110120b118000b0019500c0300c0310090003699604050000f621802c3c422100e0814001e40004d03082c1810358404507840c0c41c01040b00b000300444195103464405600d086071200501c00741032110960708011180d402401644410340c00020300100592180d01a9001074000340d400203241040c0c0d03108051810b038280b00c0c041c0c0e07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 433526987 1250 433525737 433525747
    0x41a0607020f0d0c0521100f02070c060918111902030c0d0801090f14010b090a03021909060806070c03120b0d0308070905040e0714010302160506040c0608150103110f 73
    0x1388680d42480c4556809940c610317080003002400c141c2c1c103401c03184402c1b000300080c100c1201d0040c024100c00e010b0421b072a50031f1000780009140068110001c122542e9074400c20b034200001c0c3c01c220303a4000c0c083d52040340fa2a1030800700020580590300f59003990034100c065203c012006905607c40c891284001d03021300200d1504241d084561141600c0c803090003000070301043c0902c5012a50303004007136509880c0d04001041905a00070041203000700240070303405c44540d42d501003000024040354803004101c820209020b864210310403900103015080003020f803800c0104001d005058094009070822404160f003a40b50a1990461a00070030050800303028542d490800600f044019248080050108540021180750070f0048a03052070a030310192441e6840c05a030020583e82421005040c180c00303015905455180b0f50000c0b281a0054025122500e000e2400f40d100c0390403074100c4800d1206500074001e5a0f8903e0b200880081004e080004101c2c801035144100390081c42c031614440400014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 433528237 1250 433526987 433526993
    0x3100f27150e0a05090c060a0e1909060909021003020f070807082502041401060e090405120c21070314070f050f0109020301150b03160c0c03030906020606041a0607020f0d 75
    0x2c442c505c82d41d03c0b0000c0d521810343c070b07070304201c514841c0210000000d90900c0b0115154034180d2140c90160b0b00e04102c1085482e500c0c4503030800e940315540803030035480e59066800150b0074240206120700d4640e150852030031403a80600c1c1b02c140210b85020700310a402041c0c0d60200024603049400d5085000c5000d05020450b480701036a100600008902403820402a00405c10b140441036042c1c0f421611034150084040c4180032410100a0003690a48500e0348007525645500b4020800164043c0c064010810080c12150040b411001c10009404042258401096100244000c00401170007115a541c11034144208000c008a0001d0054000d40c2014094400154048c400580c402c3c0c00030b1002c0250034405031204522403050540380c2c03008000160b10f001e50005010074640040c1001d4600c4540c4c1d896210b040d4a4940080707021a210781000d002150b0100b1000307074801c1080303400b4440d01c401c1e4001a5241c01446185c64010000800d14800710360328080400c2101c0809000c000414100307003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 433529487 1250 433528237 433528241
    0x190e070e011d07090b2208030703090608250c021915030b0d0f0203120a050d0b040c021b030102070215030f010501181a0903010203100f27150e0a 64
    0x8820402802e070710180c4080309440441846200301240c1d03d90720042441d050840940c1e41c0181e00406280c80341a44a01a07103c60742d4950001c0d0005000071138442d0071070b2074042c000c9180c64120741c052145807020080c0e1070390205000114002c150114400c00e00c01da142c280c40e40e81c105c0100035030016942005415045450244404490710700079000382c070105c80c1178260210395112412a802040320540382003c00c1070f40414a00507031000d42180c1c03041d005103100700c42da13811071254540001c4c0005803869003546d13180111030301c4c900c00b25420400c5648614000c3e556040c600e03800b04204415201c044240d0394294103070344245401038100d0041d0b044050b001110f60348103c82c100700c030740030000c0042000d511604202000c101c0404d02c0340c00c030741e0a00c420030307403080d450584018040c14100040301003502e0a0001d9801b030203141d044615203509160031740c00c8500f42904400200c650819140821502e08090445100307050340000800c0c4035850106150140d440c2c01c024022a03040f02444910203003a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 433530737 1250 433529487 433529489
    0x3120e0a030e01050a02030706020c0309100201020c210d051801110408070905061c0c03060f0b04050612071802041d09060a23060d12030902031203010608190e070e01 73
    0x941e9000040002d820040d0b80e9030091642120050344103100e80702c00105a60f001700076401c80542102e0078003071a0350028016a40098004005035004607443c8901042040000740025202040d01d010300c0c5c4030b84170311a00340101c00e40c07822183e840c4c0004c41d404c6103c0c1200d0020020001c0d0080c800d10b07500e03200c0c2000a5100748900c00182c8a00c01c0c002800320141c1c8102d5000c0e090080a05000a210152481c0e10b044070b054290b0701241003101c000000f40007442800c0102e40d00300404216516414100412140000c06480c01100c0754950101c890f4008200711050303621910920502e10840c4913144004d000d140c0203034000709204100401d8203220381021900c81c0a0040854015035503c480b224290b401411540c0010000400c04c001542e0a60060f189d0100000e0321a404128040d01c80301c2101d4441c08100010075a5005c149080d41003d02c4581e04d1007082c1040c140ca15454900000d101140c010a8409603107603001c004115451140c000040e090b084008503070105440702c0c0c03d50072000c02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 433531987 1250 433530737 433530743
    0x60c0909180b15091605040b0301090501050405090a02031009032604150603030e0d03230a110604020d0b180102040902040e01050d0308040204020318070b070b0601080f011203120e0a 80
    0xa11000100000c15603031418008060141921404c0e0f00c80c129103c1c01c1c98200c104c86000d0190520002c00c8464441002d14001c05a031003000ca015407601041c0303c11108040d0107210650000e0b013650002d620b00050301c140300e2045400010f01d120050604440c0715034034641c05240d08002446c0800340603031890a4030701450043c5018810140301d505040300302c80c80d1b0f11004001c04d43c00c450818051a007001c00d4102c45c1c0c000d0921702038200010400c0c01200502ca042d112104002040304081194024000d00e401c1d1060300040600342002d07000111100c079564001480c4c0400d40002a07281c03a02c103040d00000c10138010080d920746403101c03508000f07034006008140c911140400006010320b88a036241e1700c47c68060b2141065074441e40c0a1201030b610051440189030780b4180ba070710f003000302005030400900400a045403120100d02e84401c040788083d040700d0401410300e0a210583c14420b6010b411526103a04004c001d13079151505440403501c1507684019a840e1031800d0607035200100c0c480414506c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 433533237 1250 433531987 433532003
    0x60b01020d11121c0203090703060b0105070b011503060e0f0108120301030308041103010605031005100504020702030715023a090605120c0408190b010e010b07060c090918 75
    0x49601c0045410500001c00b0403003a601c580300c09030000e42c0c1c3c000240141c0581c0f4040c2004a00702d0411303d001c1e03034010380c3e4140c100d03403010707004106024052042208500003468058035052440d01c0d0283c1c09881800f60141014062201900060183d8403401c010002c0b07148494040c500803000c440111024803640b21a4010302c10781d007151101c25001c4a06803907054561417143d44030b42d2a540035220180c03c219816640c0c2d81c10200384ca66080040110325903d44601240901c2e00314801e0380d600d4680c0e80400e00490050040780c006940c0031841c031054440202100100043c4140300700c1c94901c40381801401c2d000c4030410181e000d8101e041200400d0808505001c00b0a107011007110b41941501c180000108184001c0f078040395550b10300c54101012010850038103484100c01403e2111000d151090508040d14980070000c031300418900600a0b40303c580b010391300d000710440841c0304002c001480a5940c01e00400268090101d070405494051001c004454014081259141103144144e8583c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 433534487 1250 433533237 433533253
    0x501050708030c090307030506180f0c0102030f1809011202011b050c150f04300507150c0b070305061504050a0b031801020a0201021b06040201090b0d09080304060b0102 74
    0x54011411034812550010080e480d42d52584a4103205030400b04045502d4000e22000102140080100a01403629160035218058032070072013074680044071940307154680000a183c20141e802000791070b13030101c28220055450740038562005d5100c441240c4258000b011100208100041450680301c80340700b070700c801510f1a6170b5020308603055050300004010b680710541e00c500908002c0480b5a00640700c551445c02c000408284440c3c0c1d80254000c0f0102500100172008001e10f41c07000d1a001d8031100c4483c1245000c00c0e00ca1a4850000d402010030b200d90716000c1c036040a00c1003500e482415000940c2c00b07050b00784280e0082c041d00c0103484451041c0c0c00c805414074400341d0300040724211040203200c04241031130200040300641008003ea1004111000d20f2100000d080c00105852483d0f94001a9550075103048840110041070300c4040c1079000c0c004200050340c0051215007550322550020f500c41c840d82042201400c0c540750010f00c1c0908c00700174031080104030342140d400850f09030260b80d402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 433535737 1250 433534487 433534489
    0xc140d051309020310031b03080309010e0607091a0f071202060a230a0507020a05150402010f1e030902041b020c12030a1205060d0b0412180f091a0a0612050105 70
    0x44e000c00e036500c1003654010001080011860109180d88180481d20071800c181e4a48960311560003c440310080b03651940b211444801c828040c007540041513040844c1164284801e2002c09010b491640340090000540b1207400100e5000303850203e40e014101c54800c0045050080d01d40e9019039100c01018201031500e603a0030101503c400c5401905241450b03199203034011880904406003d0105500031006c440c4040740090080d92000142c0c19900c0c0c0311420b0600c0010640c0080c184450100480d0302122111091804100341c4d8a220720300c0d012468010360b000003001032403019000120500d060f03170f0080f4181c0d000729181000d02c0d01281c010450070303400d01c04503440c0d1084c840b01400003503111a031907040c900130f41e22403500010301801a0f80031180300e5503003c01075007050b00c0c03c0e0b800c101c0382c40540c0002035100b0400780800c04824801b842d5146030905090080015005034a0120303240c0d401c005042d0500c00c0b41d075250243c01001e85a40658481016141c584101c41d10128141484004125 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 433536987 1250 433535737 433535741
    0x1512010f0507030e0c0108060a030803010e190902091333060f05010906320c010b01030c08130f0506150109091503060b0f040c051c0506060301060c140d051309 70
    0x713900ca404c000c0c086002d8a02c00440711010010190b80e480080d010020010a1602014601070b0400321006016420200900e1344401140300030000250f04122813080140c030f696244c550402c0c403405103185000802c6c64002402010074600307060b81400311444031140c02d5040c81840c049070129804200c016103d81d42400070300b03114040d20340840c01008080001d02d2140802c2a051034070070b04804a440d070070080b10030110f0b80c100000002e5410104514046800c20311842980c1c42c402d00303040220240200014081310801060081c91900c08a070407028004180c00304481c182e804810b80b841460181580032104c4240203c460004000200c0814144007e03c5110b50307205415000c00301c400e16541d50000604001503c15411007900c2c00d140c1e10035102c2d80141000d9184580300e860300e5000140520700d0780b0228a018120250810080c0002074991b0b0b0700f03d0703054841034076000f010340c0058200402828200a400c204501c00c449180c1d4a003580305024003560300c0080b03040000c107545d941510742 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 433538237 1250 433536987 433537001
    0x121218021807210203010501141620040906060e070f120f0212090a0308060d03050301141c1406071707030c020712030c060b011110051512010f050703 66
    0x1400078841e080c15089a2215441564002d2a61404528040001c011031208030103640025450b00e80220041c00301c2d603041050002440c2d40c2c9405141046040c0d900c000940c900100064400c0c403210865071415507511503030003030b080c6026109100c01a030f58038001e4001c0101e0701c038022a030120f0b440495074040c89210a9a1034045956a55000c905100340343d000400020300006140340c2d00b041300240007522980c28a1045203d40003500441c4c095050240c940040208524400c00d803401452000a4100042d00d05503580036803880050081c40d8040b030100c0840c45e03003100d481d0b44416011020000b24030074a5651405010039144c81b07440d0b0070021344800140c4c0e6250f10343c05082600007200a440390340094075154413803048580d20396864200d5111207803005401d82c000f400030014241880190f004c3c0c203055001c2864811a007240e8681c41c40d0315101460800440e141d00c820101c0c1090481d50244101c00000520815140c4108000f01d03000302208000f04071f4450402c0c00041c3c505000340300b561 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 433539487 1250 433538237 433538239
    0xb0d050106050712080c09150a0201050919060b190f1a090d030c052505040605120c010809010902100f120b060f0f0417010c090b1c0e010912121802 65
    0x44c41c0301d600800d0648004800612005000b14140022030156a03071104501e414252803542c0d65803101e58aa000742500c0b0014184e512640c025000c0382d016035450400140d82c15000300e000100031400c90b00003010b02c4803180714017460860b60345011800403541d840e008100e4000320390015054900c0b80e000819801800340581d030000c0c55014000209004200150704c0c54408c07400d07940d260440290400000300c84850303c80c07894001c46024081c03402c040c41004003400d800c030b60303924068880700c40321a07403016002891410002c03250080b03581a5400d401840304580d00400c000719151074400000d01884500c42e400b03000038281c0d210070402c110248a580b68440c405800640380a45011300c00c0902c1e0b0101c0c1c0c8481104c03404200004010104000304215003020f0f000100b500c0c00c1c001c2c8002c003014036a810005100404000c00d5401980440503800051180705001c02d03d005050081401411260b2018224000130a01107411503407120b43d10511101205081092002030000305a141011020003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 433540737 1250 433539487 433539503
    0xc06011d0a05090c1e0109080601030c170f03030c03061807020a1e0b090a23030a031a3001090b04060b0d33020f09010e04150b0d0501060507 62
    0x10415407425034012640c004500000c0b9684030041c90089001d079190a2004a8600307080e40105d0703c10760b4410f81d002d0007410400c0003030142c1d50450300c40e0711000d100c61041040f800c00036151400e0f80c00080c4190400d000ea04429030380c49160a81070803200f5030045641d44c2c4641101d200c9403c40b0184421110f01441c11580285021000b41c0e542e21400c440f0b0038101074002c031004c0440030000c0c0d0743c40f000d6880f80d0102e4010b450b0485c05403500700f41084040c50340c0311424040d0203210701d41c0d00b00041602e039040d034140780c0460002010110f040610070041003460300030b4042c0a52000380d108000113000e4a148000d400010601804401800c0301c4030404020080b1400c1c4000c00e010459581041040001c000c0ca00301911081d40c2e6182c5c4081044800240fa10620044506442400c2841d188a007521721805600d880405a10b1502910a142405040c0682140d0203085a10f940d80440c0c0c000d000380d400a0341070360f00c2d40300341956030b08041103003a0541d0401001050745403040c4150b881c00c1c0e03809880 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 433541987 1250 433540737 433540741
    0xe0c010f02060420040e0c0312070f03080a0225050c121e100c080a0b03070308030402010503040c05040f0b1207380a030207020f100f110307080c030c06011d 69
    0x1401da480c641c50805840d03c0c4c80d0610203042ca0b56070ba0f00c640400141600d00510415a0240506003440c038100e22200c8001d2080c08178201007950880711142260741854850059901c3c40454802401004401c00b0301030503c4412a0580c4221020107201e18068011a03c0c5551030300c003044502c00c030902050070305400800d03000104058a80301440d425489006481c100390138000300c40f044401c20001c003800280f484061002c60803841c072459110b070000b0360141c2145811502c075507225100282000781000380000008050119189000d400b40400401c2840710704158070044024060f50068980315088903854980400000640d0780116000510746940361030005d81201c034007081c00012003002c0000c600c90141c42415900044c0607411168a00580303d00d490300620441c001c1c1c540c8014068070015a9008850b5084030300119408001e2501070900b44400008604500901100900e901004161041e03901004000303080040c0107441114642e82e0b85540714844401b8803603034002e0901d0b034200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 433543237 1250 433541987 433541993
    0xf0b220c06031805190c08070b0306010e040e010e030406030e062a1903090b0c0306090406020a0314010f0e0c3c12040605091212060307050a090e0c010f020604 70
    0x340c0c8200740f5034802d840002450380c032410b040600c240c8a240d80d42c41d043e03c0c42d03420031204441030000380c1440300c0100740c0582403500c401000e1001522150600c04607407144002d039940c64016005102104d40203001c600ba449040781e07903a4005010304070202e818507124180704140083c0581c407401d094040c80780c4a0003032003c18000c0e01076406005d10307510010805509101d2400c0381c0006607110710341d00021680d016003003200021001506022868404005024060b9582e980750781d0401d030800300040c0d8400103030030103038000c1100381400300c0c08144541c000a210b003008480c1d038003111025207881d403c542e52540c104806100c0e1a408894217205049408815141b0210ba1880e03d0080385610f00803021a41d0b0b24055a08054400c9091442c41d8041104000890065a4010300741400038019080062031000c01c5000d940d00010000c0200030000d0160364040181400501c070192801c011107481c0d401e102c02500700f14011459900c50310040c5452540b08805520b0800682e034090409616155 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 433544487 1250 433543237 433543241
    0xc0906090403020715121a03030307180f170601120b070c050c0904050a021005031302040207060b04020a0206010906060c0201051b07090e031c020915070f0f0b220c0603 74
    0x74106070110720074a01c010402003008090441d0480c140d864031000501100d82410903a03044032000c200c503010345a07840519403000026290040c50780e06000031101e454a21001407408683e201080c0130021041c009021071101c50b80386005c0c0c0d80b500942d0480d80c1ca0386000000b45601d10801440003440100090030248901c040000ba14843d4003503450102da00c7c070005014a5013910203036803a41000b10300c90114a4070b400000c40141480c280700741940b4080e282c00952003406000030b4010750b000201c1d08100070703076076001c15070b2000020030454035401c030504029640c0100f4010000914074146000c01c0d40c44c01806480b1407140c1c140d40e418980b0054954440e40600c0f0048003d400d803007810000700f40706400d4002c136030800c2412001140c4800d07800620041c016811582005c000d07104100d03d500a0300d41811042020700380c260f040b40e07a079090b031601142100d01807030040d00d40d040e032444000401c030086030080c0c01101e61000c44102040442e07100c0707100d100a24001050f8241b003900812440b8069 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 433545737 1250 433544487 433544491
    0x40c05072a0e06042409021608030f0f091f020c0a14010e07170703020904020d060e030703030b1c32060a0617070311060712110f0c090609 61
    0x800300e642a0020035034654030345402a400d202d8446040107a5401c091250840889030441178a103004180c60100700408224010291070b10740009444603060b240ca46070b804800d0344260405c2c1c1d01d00c4c2001c002e6144150581e00180c0303030141d00d808104040000110078404002d603102840b09100c5165009000358040d007801e030301c4d6029124030440840c20708100d50100416920002caa440c2d44901d460341002d1068104403049c18030b4010305682c81c0000203900082d0303a815100100240c44900010300303514441340000300031900308400f43e0505200400078100091007a00c040c0440032324041004642275150100c10706101c80c521110380416004528004c0300c403c1100e54810341d4890354444c0d01c440441c642c40750040ea00003414017a800c4000c0c07103044000c1c120081c200000043d04561507450304090b10002e00015000031000e84c45c1d036542400c50b461140e03c49038202c09884448000313001303088400d01071502401a00702e5010b9025010400c901d804000410794500b1340d84801c10072200304c0300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 433546987 1250 433545737 433545773
    0x81302040b0301020c0c0907170115020c060301091b050708030a0c11030703020708150c07030e0103020d020418150b0703030504050102190c050706031a0f12070b0d050105040c0507 79
    0x503441d4400c240d890a200600c5011801d0b8058007010408406020380800050010700400141e42c202c410701c07134180d41000f03048d1082c40c03c414118074007026040749080b214164081d4450000000090407100d81d6100003849083d0041441900e05c030b03210f041e0340c580a140c0019018604c00c200213845051190301480004103542082608041c295040c0380c91500718a0003200568000a4240b0649904000900f0a907006050708401d61074102904010380c0504400201408001078108811744c2c02901aa21580c05103032045407580c0d6141c4100c0c3e01c00001c402c2d05c804940c6020b8895681d21034a1812800f0781da6071210341840c001c0e0b82e903000c40003400700800c1034415542c2884040001348520308c42c1051a103040d0340c0d01030000d81c0380c2059402d010407540001309043c60040140c2c003594603400c40b5401214200c0e40300071b0080307110012503401041498002032030f0192140105011021402900024140c101c0421181e0380301c1007403000f242c00d81568800031a0080c0030070780009440c940b28803400c2d11 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 433548237 1250 433546987 433546991
    0x509041415010f1403070b070201120e06070507060f1505010509040b0d051c0203090a0510020a060f1a010309020a0b2a0105040201030c0f090509090717030a110d08130204 75
    0x44030601c0c248016000c1c0c021400e0008214010080501643e1820442150031005000f00c10f01e815100d00311882003040c000d041c4010901096200c440507404944c000700c280e820346070300d480e00c05001840741d07000b40c404940031450125000c40e0515284207000441c100381164240103400c001c01907540d03800c030b0101558001d40f5200c140c01d25468401c5200c0d100d5100d54010000d1890b1522000b0015030520707081c0302158002e100c2041150350301e410700740450758203854440c100d410f200c07070803400c0240140018042d03d05100101034840895803204110b000900d8003031444c2112900118251340f46444042e40c400c01c03d180a0103800d191030000c0c011016039041c40040d44d20501c094001219914000305600e940d52002c0005658050080c1800c0512620700345440f0140e0400280c44104503019a600401181000400d4a00f040140c100a04000041c031140d00a001203000e50340e5000341d1039480001c13002c4000c082407002c0041d01402c00d4265481e040d1442c1d0360514114041c0711100380590f4056 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 433549487 1250 433548237 433548253
    0x71d010c02040203090127050c010f1d0109050405040f02030c1215060d021306030605131a0a0e1603050d0c1a07050d090503030f15030d0e06040302090c0705120405090414 75
    0xc4101c1c155030301d0141e407d0516103000f9495042c91402c1c04112440c250600c140103071000b8909500083c0c048040e00c1846103504105580070049440e59400c0d00029041803030442408140172050425001c07083c8200c088a01c0020750fa0705101d050844040200e00c203070701642c0f20b01c000c034030b13401c2c1490b6014602411a43c1c40d4001e540001e48100c80a00c04039004a6079a4814030503c0700c03c0c010142d2200c840b50f4039004140c406d94846101650405840707034050000c2003c40d80140c6190081520901c2c0401105e004030f50406960204042512080725280310706562084514001c2c45032180107600890000030b1002c5481c0005c090700402486072040110400c044406c5c10303400d10451078001d0041004603100e10300000001701010001c0e019290800740182c1a90040e6000078429a2044c420301d0058589003811010444901840d00000d40c41007810702080f400d400b069000c1c020150085040300c081c00002c04c0b64403070611481c0503e80e004480b010020f000b08044101c403144000800c0c00321030202c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 433550737 1250 433549487 433549511
    0x80d120e03030c181005120417130603050105180105150403080406030507020d1d010c02040612210309122006101503050108030d0e1f05071d010c020402030901 70
    0x594021500540f4050010501a98000c13500c201d8100c44c04040d2413010020801280160260140d040c044d56500941f0700090108080310400d00040400252565110265888400e1780b800c401d005000020b454100009440d1030111846079034174560f2a0140c50a03400c0c84103000b4031034502e80c1000c24052040000000203000301c0000c000a000c07a80e4001610304001d2030003814524200740c41c5003000710700c11105202d044014264610302d0403d0800e01801c807883d00c003142c00340c0350907401103090f03c640e030408905000c44084c1e0348a0385020011000e04007808807805034100e44813000050220451500041d0495000360583d401201c00070314020040583d1400b103615208040311000c8000b031000004000c5000c89510001da03400c03190400f40050340c10580b900f5600d0007003200c0c4940380d6807906142c4817100c40a0200d00d06642d8080c0068211065091084018100980380c110000308140d210388040703221407441c04500c50059440032802c081d1502000043e400c081c2c03500155550710300d03040301d203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 433551987 1250 433550737 433550743
    0x90206090d080f070501050406050915010612090c09060f120b060d02040f09061515140a030204030213050601080f011401080603011b081905010e1902040302150c010e07080d120e 78
    0x141380e100d0000401e651070180f5000003500c0025222401c103074410014a03e0101403981610b040d11154604036808000c022011000703424090070161121001c8100030400000640050056031020b80c803040303941e556120340c641d084182e600c01170b081882850106d44203240c802d201c030180038002440802c15100c01c450000032600c1600c400c0303030701507983c584461f105540c41c0814401405041c1841049580d421006000842d0382c010211f070b00000021012412402641031711301850b001b9024202203441100004020f00c2c094074000e000ca0a038400003502007403040c8102d8184ea0401c80402e20844c01c40006489121300a4249a0325548400c50310219046e10400034442c0d241d550b5403c0e03603d042c0700e44008035030740b050085011243d0519005100001580c001182c1001c4604007038068588940551402030085400003075210115092980d140810440648038000810f0001c000c60400c1444d4a55500a54451201300350808002040e00342e00402091640907040303140070a036804900b0034142 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 433553237 1250 433551987 433551997
    0xb0a020a02060c01050403020c060c0304033f034d0a050703030513170c010f020f041424090a0308070305070b09010603030c06050403170a02040513090206090d080f 72
    0x121380d5a0410407051550421075050400da081d81d0703041c585124020329985903c07e502001d0b040182c0201d0710300840c1c1401c824608440c001701801c154580c0d00343e454070304851401c0042e2000170300304000b1040d0030481c0d4100324044600220300b031300c4545c0302c240703515600d0425001000d81654103c0b4012144907088004182411083e40d070f003680e03454a40340240031100c0142c0400c00e0104400b03400f00020300310b9100220088003108129482d0707549640050f02409110403045146400800c0c1011510250006041560700c81c07002c1c612248078500c00c0c0480308a80c201e07001401d030204550603600700383c1d02006190412000e803803d45030640301e031600152940050404c400185001401c00103010841c500c07250040720300c20003400350a2658500400103240d810000c0c08480d40d40021604142c003036405901e00c00c01c200b0405030750740380c0b94446030029000f43c422a8002d10b9214914260840d8510070405c0e0198003d00d1a03044c401190140040203190704811106448208600800d4601c1100904 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 433554487 1250 433553237 433553257
    0x11116090c11100c121418120406020c090105030f0c04021602060f0a03140f01030221060702101b09142b110103062111060a03020d0506010504050303040b0a020a0206 73
    0x4c2000340c41064014142d1150950090403146802102d183e550404100103811050b0024030b08074050001b6050703400c021501c000300d03502c440c0000d40000c1d030076004240415000000c440e540d1441e80c0e80c5044c5a11001407100c0c9180e903400c00a50305095181c21340c0503240520305080d10b01140d0b10540d010038003a03841600a90020300c400310703560303810359898015090001800685c814160a00d008021410038060000a100320b1400240c4006910380c1303502c2802c2c1007941c804403550303030402400c044d407203401c0600200d41c0e05040c1403400c0f040045031014401c90030501d5446081c00f41c604091300c016680108020b40c1c0c4590002c900075401c24042d070314286119500700210094032000c1c070f802405103103000d01860606041800800498a074805a40c169840801130307a0000500ca242112003101046034896001002203000303049507500d98003822040300141c00400240d110b440054855020354418580d05038030400080c0000d40c2c0d850060210b040c028012900e42c03c8450707001550a0b04505441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 433555737 1250 433554487 433554491
    0x504110307170d0207061205041703130308180d12060e07180e0103110108060a0803030c131211060c0f01110a0f080705090f030c040e030702011116090c1110 69
    0x1803a0407030b0a000d0300d454601140014000207140100180c84904003a4004d11601e55171000070b000d02c40410035082c2c9141241089550742d03d0904040e0394078101c021019000a61030740700042031101c103036407030501882804004007585110b030041110300144000c44414115100c0340000340000c11050080d01a02c3c0603190016060104413221035005880d600a4141552403001000492514030134402c60010038a041042d80c1d440101062215409178031419a61000004100275281043d01421800640c50102640d0300d0b83c8106e44030500250f21009404d8001c4035030020b8240c41e016005100302c40e8490b06480c10070404800850840d100506c8144250000254581f592680240003c00180303990400c03000c81e0030440c0e4010424050340101e41d008001851141e2003554003005001081040240140320303108441d102c00380c49401102080340482d400324209140c801d004219480c42e030031440c1c0030681141c942a280d0b80540f004200c01c40502502c4180249074800500043c64407030106100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 433556987 1250 433555737 433555769
    0xc02030a06090b25050c0a0f030f03110909060607050a062f031006031d0102041e060912080306010c08030a051b070201200c120706080106210504110307 67
    0x4500c42c5444024403080481046142d4004808185588071850710740c51710f072042d114a00e05000d1881c0009a910107404250f0034100f14007090351001e80002082000d64090140307030080043c0201f580686061580e200440d04000b8485007000c0c0702070b10b0040e010340c00300c40d00d095085e00e03220112403108000394130420195883d41c1f194901141c40d1040000d000a21524615105154030810f052a000d284201a03d820751340c0c01104101d10230806d10220f0100856907035a8800c1791030380c4a00c02d20b0f00905200b58400000a5607030054200d901243ca52100b0315240004a503694a02588001e000c28180075401c03001c40042066500590711440340d9920005030ba0420941390702d0104000380f04440c180e281006002c1c0140d0f44030200007813183e143c20000190b04640307010b041c01d041000c03107806c1c0c002c6801942d00014140028080342120381d180c840820503600e60504440b080d041039524200c1c1c003a44e18080010000c00d034811070384280561a840e07856125000064100081070380421600b0005001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 433558237 1250 433556987 433556993
    0x2001030605180915011d0402061b0a0213090302070b0304051c020604350d0e0109050703060e28020111030d020d1425052206031a0609100c02030a0609 66
    0x403241303181400000079610340c074141d600075082c42035490601902440c800440e086403103110a6030460401e508050b00302d003c0410076a075480605280686c8103107001d403582d180c040b1440c070900c0c040035010340c09891200d08100180b8955440640200c820340318000c903100d840c181c0907003441000003141c1c1c042d00303940c24241480d11441910207805422110703d200b40b42d0110004000050f1030a01c00c051068030784000d0401d104c01060001c1241149500f03058460040090228080b81903c1c4107440804c8020303100d40d0642e80d912420400880b5405c08402d01028400d601c81848601038414540014402c00400803a4116001040710103660350300407a00840c251494043d43c0341c0a021801102c503c0e1138107141c003100c11544800c041801c0400460205100e510502c11101402c1a00780655105800c113158a110701107540700d541c00182c50030542c0d103603207100361042d100d854000a10650800d8251000c001010b1782405000041c48501400c180041e107042c0070300a03900b03004142c000742c0314034141 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 433559487 1250 433558237 433558243
    0x240c050f0715080a1104120c03050d020f060703061a0702040f060e100b18061e0f1b010b030a0b13060905070905010b16061a061801031820010306051809 67
    0x604030f44d510f1420701c2d00c0b0341c1082d1032801c29103044640600801c1c4003414142082d600700c243c3c40c0c00291007401034000c4664404c1c1c0001d00101840c00c0b5404585041d40d60103000c40440e540cd0054001400604c0910851920000083c000c60340c001803000031203452401c01c00d01101d00f40d0740003114451401c41000010041e1100300740052600c003074280e1030f12030040d860400308481020000d1040002281c2120001d40c80044119020110305907142c1d540488000c0981e43e03040308240d007420312010100140c128006000e21100074101070300412080000d60b6854020700f00081001d1144002c0c8003459010801c02d02443c100316000b0320203869081c0c100108002a150144c10101115030204103070b80090a1042000c69856082800051a40000c09441d6009201590510f80c01140400c0003801e2404a186010b071170002603c3c00c00007241011060b00403c15441400741107400d001841d0f490107007840e4400d0454150514001a0740c1c3d84450003d803010988207080040d4000500400000c01010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 433560737 1250 433559487 433559491
    0xc090e07060e24131203030e1006050d03120b13150503061b07020105040b03150a080607020d18050303070b01030b010506070f030e0409020a08011401240c050f071508 73
    0x41d18018180d03c2030704040150000543c0c4485004100059815404950041200e000d04140c02c0341040d100c9460070b004024100c200314005240c040d8020b0120a8021842143c085500c050709203400701d040741e14140c44104103085024034254888100480c0b658800000c044212405407001514a2003910301001d1122a60070450096005005008121521011400050606d0000c1d0790352024a440101d0f142d015903032051000e030301b000c41031000c90792454550455121040c1c0344030484503919500240c0d40d100a80d0070754050f800c00c032030340051a4410060321840d60802c000d9251059507510120f465607201030070582c2c85c0386014006004200b0f869000c00c0c0100821a030040c1080c0c0c11307469107140005080700003404e10100d8100181c007a16641c0108000d107400402c0b60071115a540b5500e400382105016207000d0001c00ca0011a400c070b5440442600c0d803480392200081c0c041d51400c00e4514920400041c0c5492103088803080c45180b0800c50f07800580f26900b6281d055007807c0e48050700c07007800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 433561987 1250 433560737 433560739
    0x905010f0803040b0d090503040303120f050402060d1a0303040312020d020a03020309010807031d0f07050105030c030f0601020304170705040b120a15090204360f020d0c090e07060e 79
    0x3065010440003400006440988440710400340c3c1da02d008800780c000500890300c0c010458040402c0c000b0916030059504200721424841c04c5c441c00c0d20440c0c142c403c1714002c07100250b100c007092005149451f040c9d03018015014161008006403090b200c0000e2440d00181c0c0102c0b00c07907062f55040d9890366814443c08444c986c03607000412825109540c065124056030310040d0400580302c0c0003034550351003500302c04003221083c191241d019420b00100d941b12840392042c11024031032840c000440c0d510503401c6a10600000040e0781c02d5032a2010862000c40018005d24110320051001007080c2100c0e0440016000c3ea010003061524038210900050713030118605288034600c00049504440d802084038815254003503550302c4a4084515404007c00c03e00c1d601a401615040c444520110388075109004260b1100000156620100c40d5505020341c40d40002c1818614445000c0141843d003405400a071045807a40c0303103192101005012580300c16110310055200f42c41c02c1108030303000000c88a003144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 433563237 1250 433561987 433562009
    0x304020102071a0a03021315110d020d05030114032d0d09030203030703082a041a070804031502160609020a0e0c1c02070602160605160f030c02150907090501 69
    0x30101d41443c80c0d90007000d4a980a1603000580c04160740e0400012101901d6100c0968031040c06185008042e40b074022040e080504c1400956541c503030000070f03424900310309656168a180e0900818035000c04911000581500c50340d500300009141e0051901410b511250102c01844943ca0300545842100b000010911800e01002c1c0f0150710040100c0b00400c0e094200200e25450f50760350310010300107003460014054108a028440e00256000500c00c0321342c0f101721a0303489580d00403034034518491408002c080c86c1041000300002000b8800000300390560503001420040c42901c0a46a180035041c2140e01e01d640c1c42c1c0e40d000b1441d0260015000e003411241124003440c260b07008249902c5661101c82d59045016050b5580302e80c00e8049405480d4494401d644a50402070f86000d0a010103100310f500b00c2c10b001c001100b440d00a500c80044040e01c4e07485a140942806094000341321410080c4214000d183c81640f074007104019040c00740303024100410840e032030004403c04032403040e00001c0f1041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 433564487 1250 433563237 433563269
    0x2105070f030506010228050c1c1e1b030b090c09180f0307030f09090b0a18090605010e09100216030f050c060f150102030901080121060908030402010207 67
    0x1903002449044503405070900090307684461005074074280002d003040b64010203640c0f0075000d400741c0c0003100301c3c018803c00464143d82030403000c001038080c451041310a44104100804003044402074103417070b001965000e0915070001511801429a100c03941c44520189002e401c0040021701c11072541e000003041d0241014104100008649900c0500801c07041041c20003c002100700074040c03401c000c0070716001c582c1e0b40c4001d03140180286c81c4082071100071960401000482041174001c01c5518400145030a0900b401e1400c1c0c1c155183c6080d02a0f0101540c13001c00500044152180c6c6018090761a2401410b151440e9014544908240781c0c03415140180b00c00d0325000d070040124131304a0750509142888820205c4116103901440b4000740031440b0b00d00500c007203c0b5419440c00c0c000c00035442c540d822907503860016603803449003140c4c0f140000c440000420070f4030031000c01c0242200341d032901020f0024651701ea0000751205100e003610640d40002c00d00c000c560301040f448005004a14001b5558 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 433565737 1250 433564487 433564501
    0x40503070b01120f2d05011409030c06041211010903080406110708030103020d02040b09070905100302182e0e040b040c020307060b0d21110102030c090d11060a2105 72
    0x139511005004102e1095150b104080d89100030078040d0310101540c89049200700c13801c2040c0604603d4880b25044a40305002c81d00304100070048907140808a40104404d403100c0d0380f840e10103d8071101040801c060380901003c0c98800b80200725219020b5a0340c201c003800c15003065002c54600c500c00d4011200200500c074005401d040682c1d04503074044802e814081094008a4050000c1d2503860b68030190900800c2805904800594156070080c0c1385e941e035201c0c20351815000c0784a210502c42e640c09115940c0390b22440e114030304250100100d1014101d402c440c205451241c0446103028022038522a001c01c02400d00d8407a0901000013200c052203204076081c4065101d118500d005080d1641f1445402001e0b2219a1540e070b90340d912101555420b0280c0744501002002c000da140b000842c0c81040580c62041402541c2c010580005860b2805c1002c00c1009140b0072944012910190300480f403029682d1120b019000503a050f0301c0c0e072062761070703040480724148204090100300305140905111030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 433566987 1250 433565737 433565753
    0x10e12090a14040b120f0c030109020901050d1506090f0f06030b0c13050d11030c040501080601120213180c08010e030706051f061107060314041b0e040503070b0112 72
    0x1c940d10082c0d001050785804010402400c40b110b203190b00720340707480380070109000d0000f00d02000203c41015210003580000801d407d0f03c0c1a504003950100c0d014006000d14603000d41410207140c410242500407032290600c4906644007580201a540d507110542c0300c05002c64054283d0030401c3d03150801c4114115581e81d010170401810780152982c001c500e83d0a048078100c401c0010740401440080311410314601160400c1c02203035528064003a41c0020241401d00d405003a040c0d543d003e01070a2203078200140c84448000d005001e0740d210111014200b04154270707100d012210240810010200301060801001c60380082e4842541a071512454421444002c4140c98007207a1001021038a6200c00101a90709010140703404d140307484220b000a102c070340000070030440403226070035942280e40c0e8407000d800300c5580031104407080c0007040c001400284c00070450200da054107035003480980d458031040c00c600b040c03c940484803a840000c038181405a180b0b0381d14010041000078081c59a030030781c2c40d100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 433568237 1250 433566987 433566989
    0x10918120f020313120606051e040b0303091905100c0b07080a0605091005011409030709020c0708070f030203100e032b0c0509091b0a111c02010e12090a 67
    0xc010907801c103403101c01e209104071101e03c2d080c0318903c44201c0e11091003010307000d1034003811034031549015030001d0f41303081011000009840ca245c013641d40500400900c00540b90502070305a050000f00450092980c519110314091880900c401080909202c148a02e59101c01145001c1c8805c400c00d01002030355130072510798840e1003403070000401d0315201500809040190011075200d842d5204200da1680d13070b815044103c2c2c1090b40c9500440c10035600c424514460802c08a03015000000244848000f6800400d041ca01c1c0c4400c80700151f998484c042c2c105410343c0c0103d101c2d140c5078101001541780030080844950007003e010030204181e0004240e8030b20400c2c40c420b0b00003452254440d002a500802c46541c54192039051140c4054007200510035449040b040d0701c580f042c14049240020540450219510700b000e18528084440505a507825007200300318400d0700c240400d000f0252282c02412520210640010645400500b541800c142c020490240a0708040c0050601aa079031030f0440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 433569487 1250 433568237 433568273
    0x120011d152206060305030d060b0f0409021606060b0301090e0c102001050a0209180606070206030a0e0703031d0f130e03090303040b04150201061a0307020a1703010918 74
    0x15186030444100310b03004040000300601a10701e080c02c000284007021008080c01c00d00070b1001c0014585900d44001d03903020304401071110440c00d100c14411900540d004200303051030395404442d08001603403090305459547c2c001d90f10341c1401000400409001d1300441610000c000c0152034411081000301e100c1c40c0540f4030040c1000101c0110b42c078502d1007904c0e14102200c05800a01481c6081c20340c40e406540014480c6004003000b01072201038548040880d4094003000f03102903c2c08102e60200210b0790400340c0f00e07001039a0750704070000040c80c0070048100111f00c6601c9100140c1000714142c1d0600c0e412203180380c0582000c4c40e030700041c0d1745d41403410b90121040590004140c802005681d14600038003001075017511001601045030005407001e8811900d0004100d6528201c01604030300341c4004c2d108540e0002104d204c6240d44a146202842c0e00090174812504000d070551590003210f02011007542c11040004014001b00909000784020700c0c40101012640301e40580e1550514002e821a030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 433570737 1250 433569487 433569511
    0xa21020c0c04091401090b071404150507050f0d0906030e2d0102070203120301090c1b2d0303050103050105060d03021f11030403020127200120011d15 66
    0x482000b600c2032613406134801070402000034400514001c1c17034404090340c0c2040407404509164114914040454040c3c0b04000c80000c102400c540081d55190070a650869007405a88214034000000304400140840f4998130b4121041c07900d64003804441d4007014084140d0080081200e02804200d01c0c080d042c2403003200119494900d2500c0d40c02409801c1c0025454020608845200c1c41190061416100f10101c1081481240740d02542c0c0038039842005400c0400201030760000c01c440311035100130381c04007100c41000322400e035001e003c103030382c04010403004030f0303903a03401403040c41000d04c55190700100a031944800c03182903450103035513901c40102102110a100c5d2503070104040703035008846400b0301e64240320746905003441c010703001c0c0400186171441026640c0703060898990039100d00c00115081505419240070b071401d5030303d2405e0f0400101b818003400d40c0048106052201356440380190300ca000107100310701c501e50400c4100328a002c04e159944402e5845050000381501241c02598031046 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 433571987 1250 433570737 433570751
    0x10050d0201180909050703020f01050c061b071e060c0302090a0e0a0212090303180a0803010b13050916030501080d0921020306070e0907080705040b0c010906020a21020c0c04 76
    0x1048030b0030410740011400e541070402c1d41041040c005080740c01e43c0e00c216410b6a6011554004440c14040d8266940583d8014000701c1d404480c601410000250500100d500c3c00400307844541030380c205041a9103000094504120a2148501c00c0400d10301c0545000c3d0318200d002000900100243e005800c8400a02c0c000b050040c100b075030440b822244a403401503030a242070300f0f00c84d07202c2d0012200c40f102c15105042c1a2420200072456541056007c564242942d00381096021103400c288143c81c56130754441d4000c143e50743e82a07004ca2040f802c03001d100c0940d000840b4010150b850607403203400c060303118426100969821a102070140c841a6052030640955894075080e4500b84501c0650076000715402d000314151702000c00d0300411b60503a500b4441c0d4803010303c125000b80302114440c0006509101c03d00c040d800250040070031207011000800c2030038064482900f2a0b000380880c0f00812004115228401c914101c58106141804d604504000390b11254949503e241c5103014401c43d034680c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 433573237 1250 433571987 433572017
    0x281e050a0302220330050315040b030a050601050a0603060b030403260709050405090d020a1b03150c03050f040302150403091211030f280f0803041a10050d0201 70
    0x1070100040f501d1800c014810719940d0402c140141c61130402c461600e88034140000100440c581c088000c0c02d0a9a2101c1c40c40d0f54406601000d00c00002909601c151a28074442d00d90350304100c2104141c1c000c0c070142035154580f4040210004d482d41c8041d0a2508041c010008034009805403644150941003100a26010800d10328500365a5030484c80f01d4900103040c024150b512903a030405560090300c0410254070b0705030042c0c2e55075202c20b41841c0142e2041404a000800c80075666080c2c0c65084c0c0c201c00040d4032035541004018107201d026058a48d145a0300c03814540c54043c0c4c0c1c1d00119200b0b41810207047c2510001d4030f4042da4141e080c8172002a83c08101054400c9803030000030701002d940e544d600001072900c04090f91990f5034092107882120146811044041101034501d400516180107107204c4101444000140f9901651402c21006038440401c80d42d0340110b00c00e0f071090504d0500d412201d1116861298054494030080000a105100548403a2213204080d502401c19240c4509498 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 433574487 1250 433573237 433573267
    0xc1b1c021f0320040602011a060a0e0a080106080a1a0f0a0911060a0e040f020f18030a02042a080c070308150316260a17281e050a0302 59
    0x40c03d00c1500e5942007001c4010f140081000e04207460703c82d03000b030042141502c5400b0b003001c3c800300803903404030003045804c0c003082c0100c8082001e804090322820007140e0707402100307085910540c002482500150030710003c01114524003003c8d100b1a00e09034019040c940100c0c2d03807880d40103040010a41d554407101d002d121007810003140420008060907514180d4120052580d00050203840c00b4134201200441c18440900075145000321100c0345600b4043c2c0082018050300c61051030079051300401d001030703000d81c94a001b00074000201c40c1d0308401d140d14524140707080340207a0604108100d151414042c500c030780801124032880d054500880903440d07900e0909519844458410791601c11820052402486651000126040700341112420300790b1120702016144501c52140b034032342140c800380000400910206400c42001d000c111304055441207009240c840142c005105803258401052050b68840c52003c0288886a07622210001c0b06502601c0780c0134190f42c25003072540100780821040340391 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 433575737 1250 433574487 433574501
    0x1203031303110a030c030206151f0e03011404021306080c040c020f060a150501050f0901030c0903140714030f060f060d02060301090b0316150807050c1b1c021f03 71
    0x42043d24140002898041e280d00c2c02d5130001c80c09400360320009083c50a01c02c1c0d103110b90000c068000d68001c02e10300310002d02600c0d010f14030000c0c84204130032140162403d01c0742040341c034840b018203c0740c3e0a140c010009002c81108a0074501810b00101707000307103000031401a00410703050750007140081c0715040984c10100281c010340034a106260420040100c3c0d0b03004042610403080c1d0722202d071901c1d440119140d10840301100b103201020010b140c01944a9888002186030a18080900c503480742d54080403036506a1400d5000e50081b02e080c01003174003400301c40c004044214018680140340002458035000024031070407900118000140994680c51003110b0000d6000700655669a16114200c00522040c0e4445000f4400c801d03400890300004003840c2c0685541180000e85090741039000c40d048031006046208004080c41014482c140c200f00104022244602c4440040780031310901c0742a610342034902100c1c0010384201d0002d621820954404000c0303540c00003120b59281e203402d8000c0c2c054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 433576987 1250 433575737 433575767
    0x4090b130e060a06150804021005040e010803180a05010c15020f070b09010501270b030109150c031515050304050c1c110d0b0c0d061815051203031303 66
    0x800301164418407010815034440c2c1e00c904010000d0688510f03940c40000861400030010900031400301c1e01600e04820048030b0000c442c50720341d14080e1500110a2807480a80c01038011354408a800300b0304150b4100b0392080c0781c9040c3d0b420b08050b032518000800b2000400400740001004489440e052103458040703511079024009a20707900c41062400d001c07030f90701c2124030f1035081d46001c2c0040340c0107143c4946010f60034144000c0d0170b15800040341d100024000444030396031640d038454001001418105d807030340010740400c00004850340c482001a0a8544120865103968401c400600400d6198103400d41c1c511014903045d81c81f9030760380c900343e8603142c102c40b04e20754000241ca18030312b00303904444240c0850034811090041940c056006110b85034101c0382e80204003903000c1d000100b09482c403601515561200034000304000365038a174400d0500070302000d1005681d80b26a1200d0b07000d002018140c4c01403c040c0d48a6a8070400c3c2540649c481c04003400340d84050a0004102040c50310030142000440c403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 433578237 1250 433576987 433576991
    0x9061413182903060f070e060a180f14030601080d120212010909230c0906030309040507020d0e0a03020f010c0807080c0706141911031c0c11030f04090b13 68
    0x9149a900c400c0325042c0184640b081c450200004d81d05c02c03003103134500e00801c026150042c034200100c04020143d040800003208010118804207032250008800d00010483c40f50381901d403504116000900c18443c1c030941d402580b20303100400c03d8010019203614406914544407000b0b039003c2030100060b10034a102581c05150f24400440d85e8400e583c0000301091280414015481407840300c0c0d0b4400c220801149907540043d0705070047ca04060b11942d81c403100081c01d4a1511080034001402c0340d00c161b03041c000503408000ca4225458100300c0011094104654042c906481c0d81d0014502c03034103040301c10303041294882480c0100002c00c0d041c0c82100b680882031540314100103050a070344440c24404c940004810000381d404800c8124103c07210002184444041291135041c10b039001000c5810b00c8100f0f01c402c00004a0f1503072030401c80803040002e0840411011080d8000621000c111030606103950001c02204250004070030072182202c043d640c0120744004454002944820004218404a4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 433579487 1250 433578237 433578281
    0x915060f0903150b060408010b03191a070c21020105091f0209040209030f03120601050903100b120304090e06060307060503160314091501091109060d02190906141318 73
    0x98107404c49c1290220a07811030304c1e4100c0e481c944030805112504c014204609541c1c80c50403947c260003c803030340601c2c18200403420900c00d80c0c40380c200280070307290340008140d101e2880c240c00e035080c000d05410140c4a401006d81d03150b860031095541001204402006a0024101100c0d4032030b038064609041000f01a600c41c00300c003148854480e0b209540003a10380c1e8a1600182d119800b800c1a120010070290041181031007400d80702c80100388100384154031103600d100c401c5084400b00000e0014050003c808250700924610035803030f201000c0c0115219410105042c003a07581e001080d01d600150a20380e454410807024429170003040d046000820031038003a01003040c1d688000442c03034054600c41c20101c0440c0c0c3e84601040480b00901119508440c04101315031007454000041c10660307843d414014a003803103c001c3e41d813542840d06c001e0004101492010441960090407031070340d007800312540a103001e0103103500800484a5008051004100a520710706080c440e81c000b411080f45100048155 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 433580737 1250 433579487 433579499
    0x3120507140111040e1302120c030f0d081b0f18030c0d050601090207021f020601050306160c29072f1902190915060f0903150b0604 58
    0x958001241600d0740040c040600e80d10007814880d055140ca24541c405040508105010301c0c0408064045a21941d4031500071015941d94184243c80c03000700c800400900812034103140c00c104024829100e96009407091440050300940b20391303403144c4110030188514100a038440b050f8040c03044030080c0301401103500c51001e40594502c0c1c00b07822007142264080c80a400403c40007c40c003040040071a00454010040540c16401424080e48014021045801c02801414807403840b004260010f81c0040c1c01000359060502c40c0c5600600b601003142ca119182d10400f801900010a0013000000344036201402d40090091144c1440508124401a402c24140091002003165418a10051002c0d0b0200d038141007001814030824661019040700b8030003c007040380c8408020301c16604141036080301e035800ba003028000d0010f80b01c602400604003013040c0d411000d1803425007049090040061520002c0c1c0c1d0007a44800c00c6991080440280c3c000201e0301c50094a81201c01c241c1100c0041408124 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 433581987 1250 433580737 433580747
    0x109030f03050406031b0c030e0d0203190b01170c010e060c1902010f030204180e0705062115090414030c07080a062003070c03140a0c020a0e1504090c0312 68
    0x4554131a9000d0044406a5164400c3c178002c00c680e8101103450100b14100007030252034a9820281d004002c02100041034020a0510b000722140d1243e81d04549d0310031041040c000541d83c05041c1100d8070040d440140c10840d0341e5002258200c6061001581032038010366600400c440e25041503000303480441c0381c046038124150030780140c00c0380422036144030007070f6041c464420f41e401c80c1c00400d2007401128014880c7e10050019180124550244080116150321000b00070714400c08805c0811291350090618020322101c00b07041e80110700180c0302e04200300c2d0707602e4003520341154001d52280780c802903180140303155105030200c4100344d000c1c40c1d80c0001c0c2d120010412000301405144144006290780c60352207960b40d80560804c49003c01030000c0b400c024890508022414880e08200d150034041034150411a008107001200244060070103c08508085030400c0060107103a05441040c1001c2100340c00c014107511b25a401a5603d40c4060140b040007a10000203541090601103000440d03070700148 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 433583237 1250 433581987 433581989
    0x1302070204060e0c0d09080c06090601060207080d093c030b0603030a0c0b040f210f0c080405060c0a0803160f020f060f091c030204050102010b0306040b0c03060109030f030504 77
    0x440740b0302d44900080c403042c441c2d14143c49200e90441ca58030740144a002c01006060301c1c90181c400700001d00030450604003c0002034024003a20004110729850004000d00c0c180407908400d0f501c3c0c03c00100031000a8102500500342d80840751820b42001c00da01c0304001aa010212814980c9042004452840d4000380020107070781c01a001000b03141c0c1c6542c18940e60784901c10100340000d00c0c8081c542d0100d108540c0d510340051044480200c040d2558613507041d02d900c46240d0030b6010304c8070440c9030b00a98016074054175400090070000c0300000c1c1d41d01d586200d03006500c5010f004034000180c4c6080e8032000d010252050343d00c0b000454490070060700301d036403403500c0c3c4500c0004200005800c80400b030000030304201c02801030000701159580e0581300b19102c12b0180014025105203044541c42c41c04100c146141200700313540040e26107203030000090a41e168400c929010790403078400e001c080350707010071181e41c4201c0c0c2c80582030b074070303200c1d100101c850041690001c0c0076071038100c801307400f019407000040c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 433584487 1250 433583237 433583239
    0x15040f05013003050307020313030309050111160e190e0601051c05070306150e091617100c11030a030209100306060f0e01020708070305010e0601060f0207061d13020702 74
    0x590344014000010b07200140010604a40d48031141201c00002d100b5001140e100c102441035030300740050b802454104500d030390030490101e115107800f80001d5a001d40c4114500b03000c00c00410985000c040040d0f820b12160007406044602000013030b442c4d0681460402c046d5041c060b08101c400c1c600300481b601c2d20400e010b0240324444d031045802c0c1040c84040c904030b581d0342000103401540d03e543d4544006000140d40c403049200070100004000d40140c1c8414403583c940c0c03002c1c00c010312803203a5501406d8510f8000070101885500d42d0103810070006943d400c0b5081d800300008664040c2c0206a80782c0410500c090030038407001a021021542c5500030300b01118044d19181c452020000050781a074000b80900ea0005d5511042491140e2064201c0700a10700180180e42c0c0e03c5403540c0c8032904095864100380c03016911452440c4000108008140c0100b41910342400c0c0111900303802500d032800b91080e002008410480c04440c49848058400141001002072048607101040400a900804070503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 433585737 1250 433584487 433584509
    0x21e10031a0307030812060d06020a0c0201020d230702030a050f0a050f0c09040b180706200105070903300909050f01030b0a200304050f0708030403020105040b0315040f0501 76
    0x10341c00d4200001c0c15001e50b0307440120135040c250311a000d81d11117000100001c0d40f04900d840914085001c51006015411585d541c0008807400c90001a1400703052450307040c00c00c40181001d08d4495641010070200000d5095a6541e9040354000240b070309049100107030480c040e0b80c0750450ba004000a128a41d03d100d0300a69040380c6040340c1c01611590362500701030304040e407140002c0003d26246801a440320020b00c02140700c11107001c11918001840d04000b0100391007106100d0810301032080c2c1e40340402032100900040c94a0400180f00c3c0d032241c440280468500504211404a8640f03400028002888540400c660100c40207000041c030f8070401060901d840e010903401c1d10f0020b00641640d0308035580103e15200c404071000280300c1e000700340800e0b81000f0020304085040c0300085010700d0080d002020083c512511250400036150301c0b00300d0b568010002040140d03048800d8500700c981004001d5101d136034100c845860031410349001a4400d10341400c50440719010350106059034819054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 433586987 1250 433585737 433585781
    0x10806010e100f060c150c02030a110a080d0b0d0605040b0a060603020c0d050a02030405061201030b0f090a020103021e0c060106090602010e0c060702030a14060403020c060a0c021e1003 81
    0x2c000c0e114015030180e524003810300003061000702c0c095030450403000d01c210032039030f59404840498821a981d1865010060b00000383d0810425401010002031a402101420040049980350022132103080070714225030392201443c0c0040c0e03035002c102c554405d40055003441076181c5480c1c2640717154001ca859554091402c0b00205005100344251650155044000c100014403003070182d41c550004460f250840c88100008580c1e074441c2c0001c0e0a1200300c29070b244105505505d06610503500051121f0003038a8850100714000d200015590032030340e020300380140d071440d0b440f4130712000c40100110030702e000c40001103003200d01c0030028005048541a0b51764140c210349511049090b10b010740000311480c5d1086030810491f203021001000114401030072203410210a5480d00b0001c035081c0c00c014030541201e02000285501403101d28440c1c0411a0060b15000ca40400980705c51041c81010740036140f541203001ca440b000801c40c10202500030a26820070285d1070000340648903010b1101c41010a0b024 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 433588237 1250 433586987 433587001
    0x212030417011401050108070806060f0a031a04020703020d03020c030409060806041101030b150f0d09031e1b140f0f0318030a051507050d0f020306190b191205010806010e 75
    0x462076061750416521344600e500c52450031540e0150151820703500442c03c014004694425000070941180a030302c02007022160700c1003101d00782410390190740c012401001800b00095006c1088403802c071540c100140c5680c1103042007890750040740c100100e1640303400ba0201d107000e0300141d11481140301308018080c540f541801102901d400080e49504080d0940070f0315102800c0c04094070041b2041080a13084c5010907002400f901d12021098012481160b200b5103240c00c4070341030401500d01400e0580000d003032100c1c0f2900c4400a081d02410b07900b804a07150240c00c10074480740714040d00642c21242044040300c2c2c0c4544030b0740480c0b074010300c0c040f000d503500040d400c0c081614094a50880302420117008030065100403071400500c010204201005003085140f018442c07088103e010130300041c0c5134a00b940c28402c2a101c0c20548818000f804002000b525580c2000c071019040b5500900000c031908080c140c40e082210380b0302180c03075401c210010410050000300b0904850049800c1c0c00c1c19281c10f0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 433589487 1250 433588237 433588271
    0x50a0b0d02010807030c1e080414070e04021c050a061a01020c09070309030908060403080403080a0504110f010203040902070f0c05010f0914120a0302010f05011d13021203041701 78
    0x803100030b0104078031400040ca030500a9001030070460b0103040401c0d40060012400014808418400001c00c10b00c00030f00090100c00d144803000d14100c0e200a1a4180c00c042d401d0803500300090009100c1c0c1c91042500125180800c2c03001d55a60380b200458050064502e0140050040903244941e1502020460049580f00160280800c600a407e070145600d50410071405006258000e5050050700c29000409200070003945100398000e40d6000e84a040501d0005c007005000350010440c641482d00b84008280d141d41250b40c03808040320908055048800140c0c00d40c052507000d8000c040c4040760103014814400c415004191040d80b040071038a807038000555080d1403240c0a031000a2042a0502085206450500c16042d0041000845044030380c0b0ba81e00d068022007080b00142d4603a11070340c5540080b40241ca01415901400b03034a00c45000c260003d00c40030062954804104442400c0190749450680e02d03c00079212007038940d01d40c1c943c001140500e5013003040d01e01070341c81c1400f210703c05010a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 433590737 1250 433589487 433589509
    0x51f0f1e0c0e010e12031b2404121d0d031805180c0d060b0f07030f0806030d1817031c05010e0705070302010e0f0a300f0201060b0a03050a0b 62
    0x50715132240d034a0b8030b1010b0044002c070b01490fa040c1e5200c01c0001d1282118035000a461a000300030003490100403c90742003414140b080104100c16070380805010014004000c40c5842100c1403a14103111894007541c40d134610403041100760400004d0303110300e090592240700d00c8010010031900c030310fa0f66139440c180a80c0c1d6039911402d42501d1549800f02c1d50701200200109001e120103080414044c0d159075000c00c065204111092070441d002030a80205a08a8000c80c0d000c801420904280d2401c40c000c84d0f00d50a07100c0d4420304000c0001c4240152280c40041100a0001c81c403d2a81d41658454038a40d280d00245200320f05e00b1159620107070800c580d020f1035060703410043c0341c0d4a41e07454041c4255050f400c014130403401d55480e20fa105250780030401c42000211940e074010014501c580c2841c004103e140485181c440074074000720780b01e803000812820720199091801003041c40c3c06580490040280ea000007969500000d125580d0700d40c190440d03402103004840410070a01c40400300000d444c0701c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 433591987 1250 433590737 433590739
    0x28080d080103081b01020a03020405090a05040803060d0201090305070803070b0c2d0d050c090f011e0c0c0f1401030606032d090b090607020c0904051f0f1e0c0e 70
    0x208034014400142ca500180c21403818500000c1000e40c4d01500d00c82c00c0ea04034810150000c2d42c003040411003490160012500300e081c1c90400c20550500e42c0300e020003440b0042900703000da811807200600b10b903c2111040011034100d400e0f2002103444004041d03d076806950107842e1308000e01c000c200f444401401303e82c2c0320525807100c003821080e42d52072000744000340d086011001ea001e014280c2e203004540102d503c106880380c140741c0c0e05d50318803013008109089500041e040021180405140c00344180200340303009120300344928071100711f141518a0a400760403400d21610070200025a5031403002d50303002c9000098906020a41d200e54003101118586074580c0c040002d41b40c0c00c125294980300039030007174458020b0302043c4540c03140c88600c0940c00956030305180303900550400101c0356051119400900084810b4407883c01d043c0c440741d980d4032101c2c010117110880502d0442241100350b00280340141210000c1c0403e01d00151847c259901d4242103004079400d02290240692007104c0071007004030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 433593237 1250 433591987 433591997
    0x60912080f160e040f0e100b09060f030721050c01080f0a0509030408011a1003050c0f0d021c05070906031b050c070902072d030c120e28080d 62
    0x14951030024081026102101c1c140300d03d03040b10040304d0312240075807514200003030000306110750b0b00100700c4c0c03401e9480440d4107260b0303140010040c455a15503c1c1544c0050040707540d11040111503001070304000d81503000c4510022441c000b107212400c2d0f910f000340c0325406034094401d01c02d421001510306280c1100c4040c0214000c400160814441d98081c3d600101c40008582c202916610750301c0c04c442201e07550402c0c050310308489600c1880c242031501d0850117286802d015904002c0040980b80c05142d06402c4900e4010648240c4912181d0680f080303113280902d0032044036103100d407100041c8010340305000041e81c180d00110b0018082c0c0592074039000042585419071010700011602c0e0307044030340600c10a00030b100c2c000614000d140040c1c0020f0f8060503050301c100b41000c65860400540329000016001a2095035011913005100050703416004099204c000888803001c440000000f00c481d584140390000d12081000207030100444031205044a40700a0f843e0b8041a43c2c0303e09195088002503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 433594487 1250 433593237 433593241
    0x41209150c0f08040b120604110a0c03120203010f05090a0e030318070308030a020309190b13020d0212060603010f0506210a0605010e070e060711011b0b0103060912080f 74
    0x5108012404400340506050040c0610b180c2d1000910390080d8400382a2000c081845950500c00309240d83c0c04c007504036010083c1003403241104440d8040d00c05218140f0000f40742c12000e01d4060a880000c2e2040640211360301c0d80c507801808000d00c00b9005c0d4600810800c40003410710b0205201d860000072090000350301f984e6a03003510090500c7e010042c4105030048640c00000a0b1510340a940603222240025890385025030241d49800003072901c49036042000d8035002d010666104280c3c2d081444180e0a091040e0b0324004501c040320150002500541d041645503c074541c04295140600b03006c0b0000d00200d0b940f20012000e550f0705650295000010b441040c001d102455540180d02804a0a0b84c80c102c50684034a0203c1d50260301600783c0714420810064102e900c90028034503076104031101820480291540006420a444c0e5a41449034000e01c08014050100306599015407101022205685038030b003501c0540940b60049804503030820108000c680280011381c070580d50101d2642d40e1b9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 433595737 1250 433594487 433594529
    0xc060f09110402091302030c03180303040c21020612010306181709010318060b090c03070f0e3f070303050d09020a1703090a091802040e0f03030708041209 68
    0xa500981c0c443d80e103c0c000c03002507401d2003464005940718000c8e10b02e4064076403404602034580c5030140c04641c83c054004204010016045071045000d1710390021074402c850704140841c1c24801e044c250040d6010303d000c5045c1243c0c01c400c08100341620701c20101840080c050100320702c1841c0c06260010325a00d40c0051010a0354500c0d4007821281d44145400320710141da41c103a180002d4480a01034070a5a202c28102c1c54500300301200c5900143d01c00c5000b481c0d880c0c800c00061051038803120703000c10050035510159183da2841c0450202c0d81c03860802d851030300c981e1014041d034042140d0346144505071444024040c1040411404101da0305511a180b0701515999068000c14a4442c100d9006a6501d40031074240b201e144682900c141184c025a42c50645804100e481c030282d40c01040c4150400c20110306021405125542ca2927054034045260807a4200040c00c0004214510700e0510020040051075a804800107000b503024641020524950500889602c08903004039004203032546005124 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 433596987 1250 433595737 433595741
    0x901120504060f0e1c05090609010c141c030f09030e19091b122703050706021306090902040503060f041a0123041404081309020301060c060f091104 65
    0x44188148800680f203c041c18680e4100c80c41c420646005520007000d02e0850071002869050061443c100785092131012400116240b18011016040140456040042100405a2410a0781000c003940c4001010002c41503410803c030b031581d0000707400c00c103001160024038451402c4071030300b55440c0200b1501c1c44050100d640354111a5280c107146249001a8109440c82407000440940c0c0981c510b080e07010000800040300e200c2104001860052204c40000039400f04802e442001c6056011880b811b0900355028041c0c0b5501414041c0000340e680103254020300c0780b40c1a0740140d00e4241c03195440358050710890040b8016582c065001001050f0b080007030564056000c0e101c0d03000c41c207208500014000e00701c0020703846451098600c3c3c441c090006200c04452443e45000d42d0304004020044c1007003000d00c00040c00140c0711000016800c0c41c40c2500700a0031001e0b003480c10301955a565036510007040d10382c05800c29140c5510300741c0b080c2814031050003031088035600300c2e1800200b07001860400c40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 433598237 1250 433596987 433596991
    0x5070b011509030507141e2d040203010806160c0503030708060d02060a030b2412060f0a06020d030f05070507120e151b062e0b0c0a030e040209011205 66
    0x7040c81001d00e000000682c3c100080d4010345000700010708403040c21010321403920304806000b9078180d13094440c1d81c01921200e4010800c0c0b51500c2c0d502100403403c92401542c11005021180c0050001001250491000a0190155624202608110642c43c5045820b03000c81c000041194004001091050784a800e4954000c003000f059507480f240186c1c00590a1740c4100b100b0750110740c9410209a40d85801d04403a4810698150131080d208a60540c0e01d510303100c0c03000c5d900c0d8a8503007580400d8407612111050101c00310041c00c6010b40503115680695654100c410780b00001b403e2152020041d140d5004d540c0c05244682c56080c00c0c0004c5039110b00c0034a15408003d4100f00440d00c0c5021941c0d58490707040c007400d81c481000c030b03562801c50860641c48401c1403000309c0c0030b9020f4401d00524650f10203414160031180c8601410b43c0d020500541007003092944800c6042c400800d480854603401f203070741000d01d8407946607588000c80c500140004c1e4001c41c0d04090200e071203000c24109a01213900199 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 433599487 1250 433598237 433598279
    0xe010e04051e07020106060f030f0605180f06060a0c0b1806011203090b04030309180207150b0405092d2b080906100302040e0a0f0302061605070b01 65
    0x240041155011404985044810310005041c481000c1c001900b4940c010307400c14100d20085c464142844800741140400550500816644540300790f0809029030003480646002810a00d60214003d100223500c1d038260b039001c103c0c00d0050041011490000102c65821304203844000b40090389032100d000f0444003c00a1007100c10341e2804e91043c0c0f03000e008981c00303002c80c4911007803030fa500c0e42801051088150024201360400b0442440441d8118410104481c1400200131003001c1d402c000401034012070100030141d50511000e50740d0361070203402921000c071b000e0b40c0402c519584c80c0741c6503548107904081c069400170403908101420070410032150003090103000302d07082c01411000c000460418150b82e05403816a5071710250800790302801c00340d04260080018001c1d400c12481d0308a0b07584503031200038801d036500c45a0380271750350050103c616030329000384901145450600b0301075107800c400c9901d01182e0b9103040003c0740480c01841910350494200f0300c503d180362300300180c804405441c40c5401e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 433600737 1250 433599487 433599497
    0x130507110607081017190804180c11010915020d0204030c0b04060809030a050a1b0203030703030f050604021c020726120c0c15040606121b060203030c0301060e01 71
    0xd1420800104016070245a403580d03030980c2850302140720440e04440340c001100041c0304070f00302c44202c0c00009801e0b1010400308866142d651a0b03242034015031042e03500c10101c4805480d0f584e841011513a000c0e80070b1860710b03202d141005120f03411050132581d20500042c1556a2034408210140490340504001c6240c18030051a281c0c59494800815046074850b0001020000b801c7c0b040c035900c2000e01c3c1d00600301c0d8000f0f6042225174a40038141c4d0040901030020444201622000300345000e0065603003640140030740703550320722604006005c1c1c0743c22886440c14a0424000c510a82494030031250000e00b0001c0303200c078490441100e080694800c0809071115202203401c68420f043c171400c4c0842c007000329800c00d0354501061407010700f1504010204a8070302024803d80904002c0800c6e50b1482840c4210600303030301d65070391520100500c0d494006245121090008600b000fa02039140c00c84400b42018150f519981e0703c204a0703503440201c0b560142a44144010028940141c4540e40e41c007005040c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 433601987 1250 433600737 433600757
    0x3021f06120501050405010e03161401060308030a15140d020114040510080411040b09010905190516031103010f0e0712050c0a11060606042304020c1c0c02130507 71
    0x21507081c0850382a01a100ea075514014402041024481c0340c108142c030b44051070503c0101d01d942540b0744032409000d0000c42c1040c40e564506c0340291701500c05558000001a2a400c1c078124980040c0892091885400d4034044042920050300401c0c9086520081400c881305849a00454000c2d01c4804106140c03c0c0a100208850340c40680a20341d64001c0d584800e0b603842d00b4180142c3c10307401d481c80140110b143c40356806283e160300074400c0c103403149a000451151150080c5c501c2e5504c07080d2500404c40d08e4031052001006c6410107a191000840e641030200001100d51804644070a12984072101c154160400100d20b40b28041c590250079810720000e151050070410058074070440e0703891881180061007454140c4c0004080c10100100d40007860039160030808120b00e03110f91b0140c51201d603510011690794114070514004800c03806042035403110081e0b40280e58801e149409117440d480494000c0c28558810000c00d00751540040c000b01d4071140e615500c07401040d001c5c11a00c100500d00704 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 433603237 1250 433601987 433601999
    0x30b01050c0a030309171903050402030f010510080708010b030d03091713030212030306030d231606060b13030209070306051e04060603110d051e0a14100303021f06 72
    0x1020101150003601e02040240ba2031400c00b8190000c0b4051100424047c0000404203401c90700b5080300303245600f0001016103031400000d24058070200c0d14406982020104091901c07540d92000c1115000c008441112b61104446800c1e200380c46096030b0142d1007107101c0f805507032194000c07462980c060102032030740f522500c040036003030360103480c16278101d1034034a10400443c00c1c045455600070410303002039411400c1060001c1d40b98050813907003004100d0140306200c1c60500007a4810341040e4905081035079030310364901c0c1d402c07440018182501c980e40750080005815090004a400f80040c505804000c203046070700300036104401034900c10406030356001c0821141c5603403000c0d000001c0100c40ca0100242054104026129190480c1c070030103081941c0040403048a10641d800400035140100742e0703984030070030111600c4c0303821742580c19110403d050186400c0141d03c6408030401da054002099542c1e401030004070003d901c00100140d124a410402101c3c0f0402c0034200d081340c7c020702007045c0d55a14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 433604487 1250 433603237 433603243
    0x60e060f150a0207060e0a080c010804050106080129030606130e330a060f09020d0b18011706040c180b060a050406080a05060f011b0203010615080702070e07030b01050c 74
    0x20b80b0100141e44035070018001c1c1c81d00854140030200c022a06158002d00b0000c016850300011000f8a05011451010038204007003134110b10083c0200c00000c100d0185a007240314202094000c114141c0040c0c400c248026040100c2d24500c03401d40901071a4030318141a00800003840c900039220707840e00540d0a00400849104d51030501c0700c44526242c0070001c11241440d80c1904041d2040352014901042000070041a0020004684ca11180140ca61146034421409806140c0d5820740c041680d4400304403044900710000e058035100046009013214500303080b41d42e10000e440250403482030710301c200200d2101a5100a00415101010030b030307d410000881e100360842c1707174030b2004500b010a061007401e501402d66988088041c80a02460030a00041600418142806810040e555000b00b14900701c0410031541c217913001d0001c002c6240d943e081c40b11440403686200c80080d1394030001c180110310004480060b0740c180d0203078507104e0310743c0d030401e030020802102c20354140001400139030b585010034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 433605737 1250 433604487 433604497
    0x7050c0d080309100627020708040609080d0c05120a0c050715020f07030f060b0607141609360501020309101112040f02040609181401060e060f15 64
    0x1601c15549030b040c14100c0904002504000105840c40c00c40e00b00845801e00d10500031040345496503409100700500001d020748503280d0081d0420380005000201541c0c0324008804039003081c2e06441041c02d40c5082240c46102e140d1015005c0e9002c46030040b035400f42c0300e004058180441c03d05000101c1e00790748150403c18594454000780c106031010341d0004d501401050021038001024103a0541540e840d031311f4180c0c5160029012641c1c40006032402d80b2400100d8011b0f1b032300103610314240c030302291400d541c4222000351b80418030b61500c0c00094480841c00365541c40d00210502010560507035824007034164070782d034810540030140d60016003c0381c0e080c4019401880c0c0c0e40301600c0d004000000447c00c0d190740180b05520002c04200101411251a880c603030031a0340400c4500204500e800007801400c6150028004149000c22540c001d984180068058034890554501c481040082150882d40b0622a103c4d90710704a03400240285005a843e440c060030003402c61299082c0300042441941107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 433606987 1250 433605737 433605743
    0x4020d0b0d050f07090e030f03041704080a030e04020a0e040911040f060306050f0610030c031d030306012a0206071406010608041b30080a170c0403030903020607050c0d 74
    0x100e085140c1010050040c00040d1041d040e09020b11481b64044560300d1180c2d0a94855149000c0b0120b000c000b0600070030015405c1c40360b40191600d4960000944032141460b04402168000111b6406400c0c82d000380d4a080b03c068903244400c3d1000c0040c40050300c450102142d40200c0000c0c10502c5985500c1186880d201329200041d07030324258036002048400241c840903c100100e420803000b50f0b201e00110080a655140102e001c0d4940f44007640980101074180102c079180380c02c1083c1c1c0040000245100e003400740d80e06503600344004408801c02d1236004244000381d400e80340384800350824600501c6c40c030707110721080b004209950311400d00300745c420b030480c8001600c400103100500000c031640e04202c1100318601e649243c80c1000d0800e8544000c40c2c00d0781d90400e404203400110400600c005401504151101d44d955480352000f00420303090f4284000e403440c0100440c0340c0340e04034401d542c20b9940c1a29102413040c00c42d020026107801c032603000c681c030744100000601729403540c000301c03210644 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 433608237 1250 433606987 433606993
    0x503031801060803040828050706050304051605030c10050d020408030a020615010c0605060f0a1410020a0503040b0730030c0f0e09090a20030f06011404020d0b0d05 72
    0x41480081429103240b5444024151300030f00080c011202c020880520007050001c14a207201454081c2c090014480c200280150085a2000404940110040d88528402e00070354001281c00b800e2010f501049009250700b66100b200b80920311308040741417400c415800e080150400b840381e6400c100380c0e4400e402803105904003052226803240c0412806801200d4081c402448407500030000308000c040c10700c040c1038a502e860204401d9128080c0000750001c0240c002c004503070712074806c0902c028019003854040d804000c0782904039807010454010003640040510714143c5000c05540864002c0c0740d041e107440700c0e140d600d04200074107141e00c91542c60045000d226828480800a001c40781051410400d0014540500086503030069080c00c42e0001241e0404881d1141d00c2214030b41400e007d001000c011030411070010458514510250703c00303040f81103d2210740d4040b00385485210a100d141d424050440841c801d528107a0094403240007041e0001410095000028000c002021001c1d038245d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 433609487 1250 433608237 433608271
    0x60f030c05090603030f07081602030a061d0c0102060f0604020912071a161523010302030705010c0305040e0601020a12170a06050a1e050406061709150c0d09050303 72
    0x802c2c1126000d602c40d1003180510b00308000c8000c20122846640d0380100060400240156480501101c0c132100ca60050708840e880036161500701c00420596000f510740c2e580440011800b00c0300010002c59418040c0d000d40401d8035007040700030080c14041c28656000341c003841a0015a10f585542800442da0300000301341d40c1e4900303103805011004071403140694080400c5100795440c0480320b9004641d6001300040e800030386003440b4400400391790301d0481e94002c15580d0b1300e400410842c3c126050300e000310203039881c80b582d41c00195032441c40520010b01055050000b003040b0110710038515804601030060b5144501c8030b58402514143e07031013440022648060741440c1c1c1482202c00f240e8405250f000c1000f40070f01303000020b5644e19451142190341045141c40000042509050300300800c0e0181003889815181c000244c0428020218401c450f40d442c00090b891001c00516030030300980780680142291903a200d5800b0b183c0c08500ca4034891501e50403882c000840810065104070343c26200151a8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 433610737 1250 433609487 433609489
    0x7051c0b1f030c05030103021f020a02060c03040e0906060a0e1e0109050a0515030601050609010c05010213151b02062a010f0b03060f150d050f15090a0c0504020d060f030c05 76
    0x83d00c0d01d98084042142c00e200510040c0c03248a041c036806003034441024150301c0401c8040b4a001c0c20704000a401c0180800e128074860800005001a5100c9020109441d80d815006641d180030450b1a03d50140311420b040005004070341006030080c0d51700500e806420200602079102400030707884004940c0e81c800420101c00f10510449402610400c03042440c4000400080d640784e00600415101d080c0c0058041984e0380900040303055154400c0c000d42d214110040380b40350b500440d2165515200f00c8101080c3c5151280400300d162402d0803c10490003041602400f88a420402031401c1072101d00e203040c0d04084001c0c81c101e070318600340e0340082600501c03400d0284c103450503141d40b18002c0c1e01c02410b11031401080300026502c030031a500b001c900103201c0000076121090300306010f042c0340592100c02d03062030f02c00302e48500007840b03541030614162201d540c59542c40300c0620001d4081d020203101032215240c2600289461030451101049441e1180c2c00554541d9555100720b40c2072034020410082 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 433611987 1250 433610737 433610741
    0x20604030b0f061c0c170718050702010c171b2502010f0c0b0a0e1213060305060d030f0c020307081b0a060302090a09240e0907080607051c0b1f03 64
    0x4020120f100c40703001d0f0b240d5614241d042203203001b0980344104034001c1d51041e280c03c000080052800c0042c4940c7e0800d1032a142c40280001c1c2c801c9030040d4200a00904400d00a8511300501b244c01ca02c1c1910650f140c2100c140044207083d28059200ba04001034021006094800c044000e0107035001050f11049200243c1840030100c3d0340010720038107458446c0461001102250b010194510105240320303540d1075a82009004421351200f8a80400d48000d496007200781c00051351a0f54070204030540320b15007004501c51580e940100001c6440701e410600703500c40d076041e1007514400f400310b40000d52504070050624500181c0f943c0c80d2011800701008510b80781420000501140c2402c520b00501c0801085001155004044500d9261070f035055885480944c40003c0381055101c21511b561200102140040c056903d0070282c400c20501091411003c11814040d000b542c0717a0500c0d01c40d1143c22240315400d410581925582c1e00c06080d4642d4860f2660a031841e0641041c0b5054410740c00c0d0040c1c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 433613237 1250 433611987 433612009
    0x60306020a170709061404090207080c010609110901030c1707030c1704020f010c17120627270d050307021009030f0c11030a4407020604030b0f06 64
    0xe02100700c00305000401e03402c0300444c0c066603540c0ca40020000600e80c03900c0c81511440c2e000244d003901c00038240003131010601c09031888050302d40c028400345a480303081000341c8070040c002e1480d40c0c008200000803580654000d250082c03890030b1152030b0500d0b00805445200d01213903224042500c0d07401c0b50300e00c2ca9112500902d040b520089518090400d600820010264010b4035418400e80041d91401e00820104400b1103421103103501e035a90000f462002042c00064480071f0203400301e00004001945031030f94a9141501c540d440d0203280e601c0750f4101c160040d1125451059941e100180c51200c2006d20a24010107442c1d00e40581e40d00b80040c0080c64001c0322507801c0c9070b8900c0c1031646000250b1241580b1802e00c00c5150800c0c026025082c8034070b441a11b0b1002c540c0c98880c0305400b8040100d10304503101140d9103504507400c200305a0750390b150f0003000ba0039a8508000a000864030300e0703002030090140507001400d220f05194803555800080c0100381d0380d11500c001c81204100c00c9140015809d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 433614487 1250 433613237 433613267
    0x9033c041404020f07020108090a08030405012711040209150d02070b010f08060408030a0216110a150e0d050703080d050609010f03200114070303050115021c08040510060306020a 78
    0x181350960418582d40e5a001c0c1e200d00038100704522000c80c0d8620420000c104949030020105980da00713043c40d169009011020400880c110044286004030f03c0040d0043d182c02d030018001c80e581030144003003100a41c02043d10304d510400700090b00c0c2541d214503010703120100c0512001a55807215081121074807805920004d0450110702040c07141020104d04180c00c00d6110300d8554907a00e03408a440003138040d002d050001606450352042c01d12034180d0103500350748070544081a2003900c880780041c4007418580010007049205400c0281818020b4414540f5030040c802c3e034100d10b80341e65448900d81c2c800280410b0007601d40307041c0103551808018843c018585900c15460b1286566510281c16008485410204490142001f042e90052150001c201304100d41c032640c4158600d07024008100038015900300d070741821a2000c0701e034000555100904050300390064185181e090071a00301000410445c1c40c0d0240b80ba0000d0501883d005200c0a5031051201503103c00903010000c0c90304031441601 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 433615737 1250 433614487 433614491
    0x20408010623030304180216030302091908070e0402040608011d12040609230a301a0408041203090305101e0b120a0f0201140309033c041404 62
    0x51402d5035400403c650480f0200c1d42c184402d030501454002c020f00505c9540c004110318448030808042d03059005101c2d0500c21901000d000f521401c1d4000000058050b450035603006032030500103d0020a5825809480144085002611403484609607405500002404003010b000800046c0c01440341c5190b4007441e90130a0b040600e0030600420110042c271644035210840100848480a82c2d0700317685500c40c010f03004482c20f65549413240780c8412580d0030700c1c8581007400607a00d422641d50300c86035030268115010351960420b60a200481e40d1004d041210241c108100000316a9800c0d0f58818034980280c031921245459410140e041544030f00c00500014a0588140301000000e0414650f03078190318070004640c1084d00c0440d103c8115410a00070a1090444060400201c03c4038030040714400e82c1c500c407101c403d0829002460009550740800c3d504140300c01040070707200300c550300183d20103000b56141d544804000003150315410450012105000034061003502c3c1d4428644028901c241d0b41 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 433616987 1250 433615737 433615799
    0x906080f0d0e06030702010b0411040501090e010e0105060a05190503070305090d090b090a0f0320010c0b04030309020409240506220c020a0c0b0406020613050c0103110d0204080106 79
    0x8000d100b0101001d489200c0d00f008800704500520035444500a0034000d0000c0241d08038212244859802900c00e0303600040d01d001012510b0107910003250704954070414005c100d80d0a02003040341c0c43e00101090401c010051220359050101d05041441000854603400e50700d040040b00201900c81c001c02214142d0310038a4510600c0d940f201407481114a030a80b03440e22880a0400160000708652184060341596000802480135000022001c1c1c45400442452092107600540342001d040801600c07104056000502090080e080b00a20b144018000141440f280e07071107200788107440c4078412414602a100248005491103000d0f04108200ea02c00390703c040e28000180d05415000000403007585030342600071803500820402c1c07005079110140c40c040d280c0300c2e0001c1889800602c1903000501c02c1201041c07240507192811401e1f01d03004800341c4030b8003800000550240c0b01d011003690341c1c1d003c100000030402d030680c070240c000f40c1020300002c80c09d14604019504000c1d0103490810b00c2c0200380701 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 433618237 1250 433616987 433617013
    0x30412030b0a0b092b02011809060b19080402060307031104031403030a060905100515040806041415060d0602181e240301030b1003050d0302041d01050f04020d0b0301060906080f 78
    0x117000018942c246404240b09011905948070f10700310303034400021141017100c041208031805010700000203c2c400200018180000121010041a540a50003040406c0481c2c80c952090304061842002601001c0c03410f40e59940d030380d4800b0105101124113800200030b029031206680110401440324001c2030205d400c004240000304190fa2203558401d03054424600184050213080d20000c005400642c0d815150600706203841217031000c21100c450040501044902d1600795903140511005810180103d0240d45c0c1c80001f980800318500710150152114801d90341c4030035802180802e035002402008558806000b80900404080244175861080c5003890f0012503003902c1c1129002411040251249128654203040302c1e0070191680c0034051140c4200b42d0541c00410403625140440500036041b91041c101039182801010740c0107503060b000f244945001c3d0080c103211074040c06e0004842c0b540e100007900b1185540d00c2905450749509003000003440c00d05c081400c54100102400f440c40280c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 433619487 1250 433618237 433618309
    0x402180114010c020a050409050601240e10020a050106030809100903112b030201090c0b090109030215160f03020114070e0108191401090f0e03030412030b0a0b09 71
    0x80c111410000703c2460340c415951413001040041502030020020b0945074141070b81c50b082d0902890500c5580715100801c00501404446581c00482d907038913450600310410448401d031541c0d24241148a00302100c2c000c00c01c2031140304001c620440c0100c0e90307401e80720309119016204003014010b0004804041010454094803400c20b03c404480d000182417143c10240c64050101e03074450340304c1251500c04000c26405500110480d030080580020b000c1c0d40c0d02c041e04091080d03100d0a800070791034105c10001030a21400d1141c11180b049000d03410403a140c1c5900f1003d0501c0e10303003030b50055101580c000a064080c411403a80c0d44c241300380c04016244c125405003640680140301810040c3c1c40780052182030341001800141081c0321001e10504140c900c0501e103a450a0003150052803034403585100700725051164041d072640800c0030b1404c0da5510f856450210351100c41c1c4405254980000c1c0303c1310342d11200080060710031040d24035101c40180050200d0000c1c0c0fa040041e80f019500341c05800d682030300c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 433620737 1250 433619487 433619519
    0x261b0403030c020f0301140f1e040f0f06020c032710080c0a02031c0c030e0708070303050f070c060203071104020301050603060d1104050a0e0c04020a0915210504021801 74
    0x155024580c4e01d1101c808a8010040c51103206030b499040c40600c4480e080ba502064080c1c0c00c0130700454040c584080350200c540c0b0003076800805001020440d0b10006120f10800149203004940042c1054280ca0b040c90a540c001401e0144040f80300c40f00c150010180243c18000040c1514100d0041c074074810302901e50440a050b0300d204000229102086520070000c440008008104042d002c4070b081d0000005880301141700c0c070120341443c0102030103040002c3d68070110340418008082841c51134406903055440000074810001081001d83c01045022091070700801984d4000e590340d49540c01c3c510090502c00078428419801000104115600d44003502d804c135000711fa05084010b039510b012040ba10382480c41c1a003040c18002000400800c0b0713880010911001d005075440303d9020000c11007244603012070403004c5501004148401c003001070781a404204e483c00c01400075208815500c00500f410300c14940710343d071598100b100f141406c030004402d01c0c98030040400c41d0350400d2103151982c610 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 433621987 1250 433620737 433620739
    0x1e0a05060928060b070b06240c16080f0f0a02030c0f27070e030a1505040201020307150623030604110105210928030f261b0403030c02 59
    0xa003422042400300d0a02c200c29025408801c104034080d81c655611141d5000709500384c4039441c11000140039030030150140a84c54003ca0400344400403c0010401c4982105c4000903642c46909405c20003480002c6075903028011020040100c42c00c2c03155254640458603c0001c0755401074400c0000507280004d000600c00030444080c4028089040882c61150030198052505016072141181c80302c80340104a00480b200d035501d403050310010042c165a18990b030001402e117803101b2107504000c0c4882d0311a40d001441441581c0c90705005403542031080d008100264802962048204000303d01d000c0e40c0c03018004003483c8031168800450009865000040018040c6081100c608410382e1094040312009002e60380d404030341054a281c80b950401c0c08440703403440d510030000b0b03000042c92300c02e95403c403441d03040c260b604040c02160b8080703401540711040c00381031140c103805804856040340840d041070b4000c0e1a40c1081c514054440d14541000500c5401c0820000c02c0103001080d80400c43c00411a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 433623237 1250 433621987 433622011
    0x6161202031e041b0801090803010e0405030c06040b010e070804120e030709020409020d110301080601030f02040f06080c09180c09151c0c050619030c0207030b1e0a050609 75
    0x70762203050301040782c400480c4400d4400ba01c03040004010801c00e520024100c208540324680b501d602d40d80c2d00300e603600100504412014001001410f5004081d958407910410645e4140142405043d00d480026501101d8120702d082c010b10170240c10412040d0702008600d025503e0f428240c48484020110112a00c104140041d4416050f00c041103903c00508440004651741da0b51350407a8402904070f205441405030500c5400d0104142d485c0a4a059030faa150140680c0d0f443c55a4484081c1d804083c12a042512400944190381d01ca2041034014280c1e0400f401c84c9200c03180401c0846c1c40020000300300250906c0e03c1200003100054a4886100b0940c0d440741c0079202c500c0c80406002c00303c440300d544018240601c038164003100860080c464400c1000101d17494580040088600a5020741410782c401900061140e170710035040445418810300682c1c411310f80360744a2101200085030f1191a080400601c840ca0700d03083d03014280e011815079410856400e0940000300201009030980c0d44e014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 433624487 1250 433623237 433623241
    0x60c0906070501110d0608010b030a020a0509070201060b03010f050405180d0e191d01090b0904022206060503090f030304050c0906120f0c010f0e0a0519050a0801020c0616120203 78
    0xb150135408440030141040b521915012100b1102c0302500c0c0078010310440b9401d003c40c2070001d0070009000862580d001300b058034510700700320034080240d02c000d200030119034076000c000420042d4200118042c0c42d42140210040e0700300f40c01e010503200c0140c901065024000869541c94001141e045454031807850f100360301c041c21500041c200f2802c0b40c1600d0442c10500310015184003540c40d0126403083c0c070b05ca83e800b540e076a051080201c0d80c042c1055078000c028040020014606851452000245841104400c07840c01c2800360841e4215002000480c000009102d8500b10030002100d84580c62401186189444d0340c038070b034503421040c2480b030041441ca0007003020b07655101c100c03a01d0140381d20112580b5400d0556042e907940031104602d07012580860400400c58880d0001081a9001800785003181345080c091001d8902188500e4407035110350000490950b60b4602004000c1c4a82800507803101c1007044140c0c144400900500505421901e017414003640100319000e80c00040d0b0ba0050b225 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 433625737 1250 433624487 433624493
    0xe0102030721260f060109060c03030b010c050f060403030f1e0207060b10020106291206040e1213090509070b031017030d0606111e01020f2802060c090607 68
    0xc00b244544050400c180300700c20f0400e601005141d24403d05081000c44c0d5541c41d500010340b036140c41e90040000143c504051000460700075003011002a0061400e5407104070192181d80c1011481c4031040220380003801848141503042c0102d224001c3c2d02181041000103502d0405800c020202ca400021a0003203210f0060010542c41468040c1d0040e0808081c03d5001c080280288118000c6030f800d1110040b110510071344002c0ba03400c0402241c003c035440e00780c0c0420a22808507000744041c1d44a501c4140900c640c0c10306000d0030b0031030303060540300c1600c1e6902e9030510002d5900b1500003445851805003000400000050311130f0031604281002c43d900e407110034962400131b030103030004440503a5405001100d1318002000f4240500000800c00000791908800c840802c0e21111b00e0b19943e00480100f0401100003202d81c0800e40c900000528040d00304660342038541209800444c0c00300d81080035070701081c401da44400410110310141c0070614091104809034061851001d0007101c0102e4a2010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 433626987 1250 433625737 433625747
    0xd060e011104030f03020d020307021008091f0b030c0418030c060e03181306060e28061e03110703050702030a020a09050603010f1e0c120203160e0102030721 69
    0x10405449080c1542c0c0c1d600c0703040110580c400c580045005210344c560741c01e5040e1011050303800156004106400c03550541c18100d07210b00001d40b0a107103900441d00c4200300c45d0a005418015000804030126400d103d4100305070400b00b01c210031030701071400e0011410390b081c4400d0750081d41a505090038841c0d080d04e41401401052183d01340c0700c040c4000180014190f0083c92003c041640031070340b0b460305200c0581440196041c501c100300200b0000c051905240c1380050206100318031480301182000c2048454001110040e413012002c142c40100d00d01006d00e9210000380d06202a05090013522840622800346200d075140c040c042110114082085507070901240071031540050100304056140e04840c4000c00c025580281b00c0d61a02040d002408524001c200741d80300c0300c1016102e10b801e04088600070348501f0b03520008000c0c0050785108442c90510196028803a0545010260717107050002920b03001010000c14190b500c14408900080c0342521900d4508988030488480055410800d031a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 433628237 1250 433626987 433627001
    0x308031f061205060105090306010905070e030109060903110f25081f0501080a02090a0c05071a01090f0b0603041101090b2d04060203030f100e13060c030b0d060e01 72
    0x901100a18005605944009615600c0e02842d00030409602c40000559540c41005002c5400d600210010001222107600040d4084502d003401200b040d40000064211080d0110441d0404d588200c031800340360b404410500203100880092000c141001c84032a03540707840d20301016946d41c1084c2e000503960092a542c0d0018862441124414400c501c030700440310170400303141d940d45490000002040200050b4410410b80c000c0c1c0210700e162200c0c0d0300c0ba8050034010294100b0f01104002000009078859040404540b0440110344954142102901910124090441c401d401c0508680d40c550b41d0708222034005a00c440c179008031511050040c0c580300034552240c00041b0010420642c91402c040e5403000181021506c181601c0301130040f56118000c3c1e015810042e4418000640b0340c44a0860607500142d0300c8601c0f045030b6503503043c2e85c1c8042d0801c0322502201610a2003c0c4200100350150b040c0d84102800c081c0840c800450202c1c0b1000189000980f042da110780c59040d44000a6029103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 433629487 1250 433628237 433628281
    0x106030504152307022118060304140304080601080d02070e060105090a0b030108010c090503030c03090d1104020d020d0c0f0e04270812010f030f080c0c041a0a0618030803 75
    0x1140e86403849000e0340311560f02000b114584042c241c00740351840e5050440e81c1c50f00e080d1321410480400721090008c50380000380101c42c01c00907100d9a00700c0d40410006000108003a01c000e15407503041203402d5080c41510324002c8150340c01001c040c010015400c0c100d51b88040300313203404c90300d590b82e080c00510071007926031104044c140000300100e82e042c0d064000080500094454040345695001815941d116003c00e110f825042400102c02c075240c6100d20b8905c4501590003880c000c2c0600c0002802c99010440303009030795038006050b99101e2401d014410160b4050304004052080d030000203410500080003003445180c0d5062100c0031107104090a500c10780300c40d86401c850448521300710380c03150310101e441c43d4400c1704080009002c0ca901d41d43c01064a51011494a1790074581d6110400d582181c481d010b014080c1d5422000c0d9070700c0300c2c071840300d407540103154401d40103203003206114440400d90041d0041100715565001c200680007090ba04a0f1341c0724440325500e5980407460b50280c56000d03078030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 433630737 1250 433629487 433629551
    0x3020c150403020c180f151306120c050d030801061808060f06280303030207020d1506030b1e0609070c1b0801140103051c02071814010603050415 64
    0x4403061560006856281890644100707102c1a030841d1a00341e908806c90b00310000207220701c0065003e41045c2a00544908087c054a400b415164221000d6030003a03040303501c2c0c103199180c1060030f010089451030000c01741500c90903000c1d0f1090700e0041070f0b0701c2c4c14001e14050043d06003050007000700f02c00744000105240400c0d03603000c0c14103800901d441d980584000703103d802e09850748400c40d400c86124165040e102800080d0103032031664103070003a400000040e40d00100c0700411001003490914003003804015003500081c55801e502d06107141c007101800503018044e140c42901a8032551004040e0040c3c41212081c0701c40c1c1d22110308403a10380710850007c00e801c80c0340340841f80008000803010181c1c0c0842d4002d02544180345000c48403e80d0910010b0590360281c0549000c0400c0388a6030405822144190380b0020707222455001c014a0b040b903e005002d507188485441d80d056181072901510491034240300504040e15007005011040c4446a0099074600e0b0300114001c18100d51428080c1184131 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 433631987 1250 433630737 433630741
    0x50d030504090f0e1f02040e010639020108060d020a0b030403120c090e0a0b0a0b070c050f090615070b070e0103051e07030b0409021908101b03020c15 66
    0x50141d042031040c1e41d4441e00700b05003505003844074091501001e00d104001c040000204501340c0c04a48082d503030045841d402c00000c0b6144840c01d45c07840c041c0c141611080410f166800ca0b0000120100c620080d04e880102c004072000b803568090300c0c0d4800d40928001489844002c00209441c410b6000294401c0000c40d00050190b601c00c042c601c940d010780c03154200494858840c3c010303500c1890b5040001101040c041c0301d50612210b00c0e6030090040000014040f010002251140a07550440080000c4c0480e120041005541520700685000e442c800002030806001c2603118402070301651068101444001d103540300700d0140c03809107421241ea0400c0341824040a441d030131007200e80c50700003800c080004080c0c0d03143c1c1924801c450b0031010402c00c00e41d1485403c400404159845070fa01c00d80301c084100160f55280e001080b201409400084c03100e00d05640c0515182e0749403004800c0d1030a02a043c0440d44101d142d01301c8100d0340c0e06015030748040c4283d5a90400c0d0788106101402000201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 433633093 1106 433631987 433631993
    0x402060f0d0902180108010e0304080303070c0f12091503050906060111012d0615050702060a09030206360307151b0803060406060e1c0804050d 63
    0x440001c51240583c0014440c0000034503540400c0a210010b1200f18828440c804006500754003d501e031624080c4100d8580c0401031554043c00f1180440710148954120010800c942c0441c040490010088000d480701420340155070444403959524024103000348244c90082c41080c005007210b503684401100c0050890442d00c4c459501d4614155001d4646880701100303030031081c1e000502c0241425088111440c2c0d038882000c5039541c0c10001000c641203421134403000e80548545503103229041082c2c404840c0c65100941001d00041d05000c0d050242500749900c9081500300c44002c4070f0011641a080403244102c3d505400c1031a04115844005400b0900c08800d400c14044108403c0000000e100705c8080503a400d00001042009924240c030540029082c5800c000200c8101c0d0800700c1c04407107507030460000682d80542c542c0140292082038078001d101c010100400c0c2c5503030f45 = true := by decide +kernel

theorem cover : BRFrame.Cov 433453237 433633093 := by
  have h0 := BRFrame.cov_init 433453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 433453237 ≤ n) (h2 : n < 433633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
