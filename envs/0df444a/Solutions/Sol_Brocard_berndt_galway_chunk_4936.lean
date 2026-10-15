-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4936
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:12:43.52858+00:00
-- url     : https://prove2.me/submissions/2584a609-18ad-46b9-9820-45c62a8aa08c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 887589928 ≤ n < 887769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 887591178 1250 887589928 887589953
    0x5012402120a0e180604050c0a1d0312041e0906080a06021602120f07150e04020f1317010c0206071e020708031317030a1b060212010f0312020a 63
    0x11014241d8440c42060710450365403c0440701141c1103000101941c01e13032604000003501c58001603a0601943d194281466000d00c540c4610f80001090b4080ca5100d5610030040600d004d000142250a2440c144030003551617400750742f1a155202c040107040204080110303421005100d2050200b10b8503290039919600e4000d0ba5000505690740015059180000b0702e41080846402401004860b0710107944a80e07207d03090b2080c20381030f106142c400919200c40480610460510360740d003111281c51101440301a42090607031003c001d00034001c1840b84051f1912a4004100f04c0415250440c800e007103175401c54180c0761042d000c44d04102c003004451500310b002d03d01c01d1428000d1030b55195400900c120b040120070380101002d07002c0060404000c01c151408a000e13a070400001900d0321040e000165036a1148629036004a012541c04065a4000c5046050300368001c0001619042c01460661100c0000740c2100700038080d0000c062050001e2000142005ca00c140018090b040003900c0e8001c06400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 887592428 1250 887591178 887591203
    0x218060306071b1e03080a05071211090402070809120a0807120219060203150d0c0b0c19030215131703090a05010e060115140301060c0303020f070605012402 69
    0x306600c1810b075409010480941c3c560300039545902640107505184485040158150b0018404c140030800d03901203441814001e00e141c1d00c68071840c900c03034100e0b000541480b0000b00221902881740c14100c1d01c4500085c426540b05002e525580c0c05480100300c01000c5c50344a004940e4082804080002c2c480e5085802d107940140030041c0010a82c0b404a04d85a006c030405141c426030309600c40c04101d01900518010201e218800b401040c0e18000e1010b201c0c0c50403800703400c150482c14200b1035000c0b10001030401011706000d4132220300b00c440c000383c0c40c00d81c0c8210880041c0e114a00420440605071582d9800c03418400800c0c00244150326201c00346109601c0d100180600000450002c91041051070f414680c0580240000e245014106446400901c107028502128401014040703209940c0b0a90f4038000c0740e00113003140d00b000c80031103003032010603000c600b4541e00300b0040fc0c501140f0710252442a110780c0b03022850f5030510b02c0c01360040b016070040c0c141102644c91080d14164000c6514000440d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 887593678 1250 887592428 887592437
    0x20303070e04022203060506180619050312070312020301032102013b0309010203160519140705010212120402182509030c03020d051f0207021806030607 67
    0xa4400094001c2c842c4100044c041d11001940721030400a0303182c150116401188100516074624060003411013115480d0894200750307000142003440c201d1104203aa00d031000580041c5603c41c00428a04034000c41445001c0002017000c0d803c040d4807400d8031102000c9450154150b514594940c02102c500134034003240100449a54091107200b580690034a4411480e021003500b001c603000304010090314820746010300c26020342d04625000104658009006074000c43c80e1500511000313003002440c0404441c2c9000c0c021341c1154200030b61090060703085c01105200740c006540040680341000c194000c42c150f401c407800001d800c544000590749840740c4040070300015540c0f88001103a100d88114504043c0307591200340807000e02c06030071440007081c40c0740309405070741da01910a2380d0005152000510a109501c0284010b041c65859a11041e1154085542d000c03030340c046255203070901c451000b40b41d07a404036251040d880c250b5600442d42c600340d100c03480c9500f07120002ca51a004014445410b10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 887594928 1250 887593678 887593697
    0xf1c050304060e0f010c0c05070b0301140904060b03100b120607020d0e011b06150b0c0a17120a0b01020c06040e010522090b150f010c02100c0218101502030307 70
    0x203083c00e104401100e00120020400034068420203010381c001700e54103aa0300d200ba000082500001042241c1c10f03039a0602c406581150004100403000303100370022540180c40e4034a180103078030100000c208003131501c44040340f10301c0487d0601c00c1185091113141403d51081c82444038407600442c031070741c000c04149048800140c403800140c41c00d414814051110318a0381840c2018081c440d0b0000c100c1440400000721025074070345190003a8082d44602e58547d801c50800c00b03001641c01c89108540b1151080707810704002115481e04c884601c11917001c49a80e480c4c2c40400030a42e418000c14600500884620303007050704209809034040014010f444c00b58100103510700c000a0207140114503030070120f00612155944c0d1800ca00302030421b44040c4105122120f0385461850051681807000d041a55000b04860941d001c00161411120841041c049251080e00158881e002012040c5886c80d800e50001d0400150aa14800d0071303902600035018007202d000501980801160b800450300e14101d80070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 887596178 1250 887594928 887594951
    0xf060b0307050a0906061403040c0501080406141008070503010216060c110a15050703090803161e031a0907020601031104020d05070c020a050a0f030201030203090a0506090f1c05030406 81
    0xc0c12842d0308003a40c0100000e500154a40300380e000441554416079030b034550b10040710310041346400b040d00c000303240060322074013130103107512074240c040c0c2c0316000e28000b1610344c0300c5098518100b02d00b80e13020035422203020002c0c05640ca040040c840180b1003039008601e88018048d048411007460400200806d80769014420454072401c11034811805d0041648d0001c0054034207405c00800e00c10740000f03540d00f4800050b140798020300c1541c0605401c50603407483c50340e0f40b02d144102161070020703480900c0000c0c0401009810b0800d88000b0380300850303c0020391f40182850701d00300800c0c1b101500c1d01c1030000e00100400141c0c04158941100d80c40907032000f120740440c0028020740102d900c920340852401c4100300c00b5550000300201c95030b000303a40790740c25545c9900c244091501640104400c0710f400d42d030304000652281e4000e40d84191440103480c54548190341d081c0c00c00a00741d0b48048a0b9100c4a45454480303024040d5460b0352042c01e0300c40400404000000e0418003000f04040d10b080d913143e481519 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 887597428 1250 887596178 887596183
    0x30a052704050f0a24030615030503041d0a0e21250b0708010e15030a020d030201020a090b1e070302010209190f06110c120307120804120c0f060b03 65
    0x15145008000703102c180b038410906900f01c2801c46140084a040c112901310340305000c039240340101c41c2188149006400d544035a4003a01c2e050204001020413039400101107a001d10103040507042050200150a80001c4c12401031100038000144c0b0754a8500c0c9800c0a400c0042c03521907040103110410280062190916418010301d055172200c0450000c00d69030901c0712008895684c1c0c420a041c440c291501581103034410001d004254608400c080490001400002c0c91400301c05c000b0116090380c1030f15404240e4100e45e00740200d025070b4010030180c03012500041e210018100e5010803604144000e801885401070b191103106114100003a4502458400e4048132622440980000b40000701b00103207180380e01083c400d84210f9103040001151440c0300d03000e980401e0305104010000c0003044410042c807500d01403404811440108011000a01c642506100c10a100d456180d000e1600f400c1203010508403c2c0c500e0100141040c02c000010480d000d44440b8030f801c1080000e0001d044004a072 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 887598678 1250 887597428 887597497
    0x80423061209030f0c0102040e01090506030d080912040311091609090b0d0803090606040f14010b09180108010507030f0c020a1113020c1006080109150504030905041a010f02030a05 79
    0x50002034001071005461703805400500881b550034400501c0c60b0b0b61003080001300c40c800d44030b40e0303816004141c10740d440603c642d2401c0d070443d10354415108030000c100358a00083c1e0050b0700444500c54800d00202c80e0f03140180d0010b42c00525007180509410305044020300247c1b5074011881c0310750340c0341d030b420b103180c0c49560501c00b40f00d906c078028547d2407e20320402076442d1021180c41d84510304050740580c0d882c90328024115100218450300c1c20343d03401d0610703100032900401022034004642c21542040b8042000e00607000300a00300000400f0300704441d00809a6520940310103070b060400c0c10a5a485074009003034070545400c15030400403c4183d41c001100c0c1c3c10300da140c081c0e05074008642c8004204010612113031b00c0d22a4a0300f000500d907250000381c240d80d00f448000c0c0180d101100c8505a40c3c01d01e811041e80184646809501c294032a00002d04036000c02e0080c4140b450141c5080341c155030040701e0140302c1c034040d000950400300c28500c02022751041d07c008004041c03403169071603003c04006000d00c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 887599928 1250 887598678 887598697
    0x70803013003030b042702012109120f1e0c05100c02070f0806060603070503070306050301060b0a0f140301062105040b06030d0f0203070206071a0408042306120903 72
    0x51404a4030b03090040103005000728031486130b490324402039298803c1d0f0558581d81300466503402501545900155a21804c5541c030f03002d01801015000c128880070f00c100b0300120310402c1d18181c90350310382c10f0040121104c500050107120001000c0d041803032488822061400c0f040c50000c0300101d00b440d14a040c5005100365684050419100d48940e039004070702201510340c00d00800c2c0f070041c1e558840c0c941d01c220507204145c009500b0004112014440c50066901c034100e4140810345694400200c1d0071194a5032040f090800d010401440640d40964011320000c8076192100c4054415041046184018880c032018003010540c00c41500c02e120000d1040b07001d611004001d540351070301b4448824881203611500c24000c2213400b29013940030b0507070030070b04030b525a0055041040f82c2e402e002d100d0707004c0321090b0703107a0b1441c40c21801c40094800001c0d03c16072042c4a950344440c60001075000c40000640c0900c000801c5003580710064490505450304160015400f01054641a654904500c40c0382a103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 887601178 1250 887599928 887600009
    0x1c05071517190c09061404050f0f0d05030c0a031407030806010e03150903070311060c070f06090803090c0406050a05130903090803130f050406060507140102040b0a0206091207080301 80
    0x107041068200280404071070483e103503041d8291b1511171810181c41280912070b8480345803030000c40c0e2410120b0400c3e43d540405030241040c1c0c88162101480c5030031409041c1121b41c0020940d0041590000c007102804000d41003141c240002a60054002c04001b06454100080c8010100759035408103c1030740812040c1c0640300c00340c140400d10a4481d80420010341c0810308810351510130b82c80010700c2d540710701d07125181503007420550303902c1c0881400c02c4130f000e0300e4043c0c0b10903d681c0442c51501c0210b0003580f1a02c02031180300760020510064070791070340c0601c4c4200c50800382003255449818510040c0e41400790b0025600805285c25107d0707000c99000031409100105280d890308002c24024010b030b80c41042c0c100c0c0844d9481041200b904c1c2c05024400004109000641c00280140202c4004202d100000360070103440782420801c0c0d03000b0b29160001a80300c9000e00902c41f40501102040103c0b803110b882ca0a011601e4921440c4410b1182c0b120000e80700c0495615400c4099010080f504400308 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 887602428 1250 887601178 887601191
    0x110a020409021314011e0e070305060d0804090b1813060b1917060a0b1e120d051c09020f010f09050a15030c0903020a050d0f021c0507151719 62
    0xc401340300300310034052082c405417060f040700c440180c081000d800316603284100501c15541c4801c11009004040d001d10f40140c10b000192000446650180029042140001541403207480070004501c04150401d4004903c0702e00348001d41030550705603803010342c0001d0003040c1030390a074010400f0382c05610201200114151008605000303010302048041045004a80c0b180d152554202c045030f1040a40c154002010380612a1840c596400f03c010706800416204c0340c4034650800c0d80c240b1403083c883c40d001030740c00290705000d1020080b54a2800d120140204800402c942c0400c0020281d142c985044c040009101500541b20348035101c0035090281006469076a01c1e2680100c1c0b52056101c0310210b405e200c9000140342c42200050205c1e5002462808402d10304420700c100a15000c1c4140d61100c10701c0c0d41c00c8013503128034a00710001482242d088030007200a04000b0f04110042d00240301c001c2e41c04000314200360b40406030b4040740c0c0650500c0241a12602103801c0c40341101460020035904010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 887603678 1250 887602428 887602451
    0x3031e120a05040203100212071407120503090d0801030f0605060a0f14011d01080402100e040504050321010e01090203070306170d02010b030f0a0b07091a030a0b01110a0204090213 79
    0x802c0140650701c00c2d0304464015a40007101760a90003000365000703403440240d00092080d84954104c540902804030407514109080c0c5a20807100040468840403031000824800351150811500c40a04100c3c6000041541107039100009058410409454241c450010a5460b520310b42c055009000300c481d02d40040750b50318042c00b00c02c5051b99a09000c15081c0400c0c003118040340c120194031010595138034030b4668440e0308200303c00390025074520400c04070712a40c1080340ca80317100d4107000358001c50086d622110307645002c02940170907000e032200003c54500108060b440603198070b81950200c15006d83c80755100201180180100d0380008a40810b022401e140c3d1800403d44105000083d0f0007408a08008018160303202004903c491190340f01c12030040100d011091219002595072500b240c040f941e070700c03044009000074981c50700005000424001d004a003880f403140000070071700b0414141010110f980f500c4890100c4007a000d0f50300d69090354115a280c15003104114034140c002c004070011740 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 887604928 1250 887603678 887603681
    0x171009110a030c051c05060a0c021015030204050a061a0a05090a0e150f1c02030f0d201b0904020102070b0d1406030102070507061805060307031407090503031e120a 72
    0x1c0c440d641c041c80344e00305c0f00c2e144c50301c1400100b038403150044020201074558685040c014144e40d01d919045000344405000076070890300480302108a00a000e1b4405815401000308464001d80300c401680e1070150208071142a0100700c0500c641105107154031542c00008c2551540700312f216a0341c0c807090b000380c0807603d1006011081c1c05000c08001544058410805000e0324481c840fa50a41c084281c6100c800c8580404400420b0b044c40901518144000d01917058039108515030a40c001c42c8184040c0103940364091482a100c0710144006c002051203c0d130b260080c0121587e003107000303024007000102564001c00580d0300901140d0300c0550b603000004030060050212030003003001c4c0203403800418001e1030140295000c99800002521140d458a1410b40340920b000e1340407081051642c100094541d0b409010b58466140f030384001c00c41040b40003030302e54801c7c00103207000203210200c00d00f84010b4400000362a15545010030044c0c034138080c44003a905c0c81c003581c89040c280222000c01c01840c1d4416 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 887606178 1250 887604928 887604953
    0x41e050a1e140a0302060c0c070f080129090138040f0801200a17090c0a0501110d03150521071d06101707020c010801171009110a03 58
    0xc82c0307000d948100c1811500e8035110b9140000e00168041c1020541d0550315a008108455882c4211780c40695a07509680f03486c42c5aa0010080e03035900c101a0980036000c1e045140310030307a084202450710101800007210311806000d89800250784003510042030044c0804005e0207403200182c0ca1400e003054200070515402401810f107450030b00c440018010700c05008006040c142000000010905003549500641055515804000420030059101c1e4411005a40104041001b600482d4280828420310740195446541007210240041c4480340c0045100000642d003450086515803041814000c1c0303400c00d0f005035074040300c180d14500c60208401d0000814401c82d009680f00c66a660131070b000c0d581e0348803096110105000b000a01c0c54540100e0517208020302d0300380001d98030115024121207000c00c803005d10160740060340303404a5603009900e80c1c3c01010700340d1070030003040304801245d0340320310050f00369a404644543d024810001e0003e42ca041000b0007500f100030380c0799a400d208494100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 887607428 1250 887606178 887606183
    0x40609030e121e03042105010902100305150108061e150d06090f06060c14280c08031c200a050d0e0a0f08031302060d0e01050609041e050a1e 62
    0xc100f0100d21030303014003106503000c07510240e440d440b803042d580101c0b511441d06148211025541c81c100e400c0180d0380c800207601c5040caa41c0d80040c203850440c110041083c00301142038140002142045140e40e19000315200c6d090052410316545620417000c180c481060141c00d941484010130784e5480c0302e160750321034422511540810302c02c8041107107103032048580c68003440e0f001513084d55000c4c0214000304d100001240008003142c404000305000c080d00030f0701a6034030b8480c907a405203c0070148441e0a0001020b050988003443c035000304078408104150000e81103080c0c49403507c10700d4103030007050f40724100d0700780100304800d540c0c0160f030000030020791150301603140351442c11076007150103940001d0400245a10803c0070b0030000d00e6444007019504010705400000c140d25402000580701c46010f4586056480004103035030902800312401d507040184607a0085009004200124000700c103201905003001091401e00314941c2055420070a0703c400161182e034a14001c5080010300b5440c8862250 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 887608678 1250 887607428 887607463
    0x50c070b060f0105092e030903020f060f13080906030f0403020d02070e0a020309031308010203192f0c0d0207031103030a121d010504050106031103070806040609030e12 74
    0x341d4580802c04004590408607000841c18025070640e42041c102945825405180a42922001206a4a40c5c04003e680e50002a0f2140090010107030100304d00c0ca2003000307140251800d4030b031440c140d94503408000c00c150103c1013042115420f2044d80000c44002c020040e216607601d00d0320303035001d2601e0041500d04400502ca5001c1a00700640b02103000804d440d010034645005444400e9804043d400141000800d800204070f881100100380d11500c1c020310700c100002d6102d00e00b40c98180303600c3c000c203261002d082c0e08009c080c0c250b00741410070914144060322140041d10160101d140c45500030180d25441c0b42c803c0c070b09400e540e00c1c1c0019600c070481b44030301d0241c0000c1544006068a070700500c0c2101c000b0600d02900d1545180340c0da007100c8400c03400405072044c200003c501d8076003526800c2e507040d5031a9540308414000e11201c1c1169103000d11007600200071f641d240c920010307510380000b000070303059540d03c0b044031041610614001c0d510400040400c540c5181d0103103040d868079450694194443c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 887609928 1250 887608678 887608681
    0xa0810021201060f08060f1c060905190510020c1603080d050123010305181510050103140c070c0306060b12150f060c01060305341211040b04050c070b 66
    0xe4440d41490ba244c14696803062400e0303c0320001d000305001d0100130f035540502c40150030046442001c9107280362a0080e840810608014144607050020320103404200300b10b042c94400100c0e400250409900b0802040180d4807010030084608040e41d1f4204607403401c810402c00014420508094091b040c0c11040400c0b442e40d07038580076a58100c8602040103100510303240c5801c0c9600a46c01940e0120360040c003404200c04014541d4148944404c0c001440c0000070240800e02c00301c4515807001d4803007820b0800005801c80d001549940d40104400c03400840022038008010460722014011540003405201c2e2070344030007c0d0211a00540f0080c4400041c00b030000d490030b4a103080d0001c0d1184040d1220040e11a0481481f90a80c030040da180955920b070000040040d00400c1144418481c1900440c1030182003207a4828800c1c2650b06c200c4008071610041c030500d80080301ca401c02c181e21854440c100c0f0109404070300942041c280441d0711070300c2c101c00c000340341030358a00615980c0e1054404800c80e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 887611178 1250 887609928 887609939
    0x6060902030f040b07171e010b04050108010e070c050d0c060f1109060a02010e0a23061b030403170403030209010905120a14161427060402090a0810021201 68
    0x120302089a460710340c02c1440010502054980364420b4000368203241c0b15050a40306401c0404407841612039004080c0e1070044240941051501103003d041030101b03141c07034140b60800080040c0811700464104a07040d6003c20103090140308107888a0383d002d002d885075103603002c40c043c3c984040003400395a80317400e228100c040b140a03481440030022480f0310050800384000305004007070704800406415596078501c2080d84c0c510802110111a00c9841c5882c9030350380c88001101c0c00d04d100c0c02c0241d0700368080c01c14030082001e00180b0203241c51280911989030f94139810300325107100b00401c8910303a02c1e00c18414003080c5a8150010080b944003070b00c0e8ad1800e40e50b64001c0c071600e1180b003c010655130700144801300000e12040c111003500800c45049070500000e54240001c0c480260f030001e52090030b1136207050031f1401c105c000e00c4802001d80d00c0b1000d00e548512044203c0400017002c1d41d120365400594008640d4520084102402e498402c6034001c1c20307600180d4000f90b0040045051001080d0000160f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 887612428 1250 887611178 887611181
    0xf1b120c060f111c0c1707050f0a080d09080d0507030506040c09030c0b0f130e0105030c060c150c040f0905060f10020304030f020d0605070c060507020c0d1403190c060609 75
    0x200e0201400180350a491482031134543c1da00c440300c46010849058070f4000410600c480451904141700c0400d0ba1b190038518150386086146400c1901581246c0700c410041141d00080d1a2000a005000b06181013a490500120710a018000307000d80e1810b0144008a40c1c5075001031703c100c805581c02c002d440b03962941642c402c1d4142c40000d1a214041005000100038100507045c003581c1885c140b0300384030420303111100b00d001d15040316140c1540180104813603d000c0088413080f680c1602e14501d807000c902d000507140c1c3d18000803c980588004e021403c0200c42c5000c4400510081031609c00f0b4948481c456005088103985c014450b04c00301c8060741051401c140901414805038004510303045c42c1d80d49d411041d1190500c140d900c580e440524101058890003000d12400c680d5541c61525030b1103140810456038050f1140e0b0456101d04540c1e00c240d02e07030340e0401c121160070600c41c003003044940c14081d00d14030a03000940390505000344081c1e0400e40040726808201d01c158014000d06803203074203400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 887613678 1250 887612428 887612447
    0x302060f150d030509030c0307031a010f0b03071b0506090a03121a0112140c0a1b150f060f061107091416030e07030b01090b04090f1b120c060f 63
    0xa90020b8410007810009000b240242111003018040e9000b00403010000b9051584039407042e10f0141c11035649400ca00d1030b04401034003500400030031001c0c041c20602a01d100c2e000042a607824003007024502c0b038600466010001c0c0d0241e020f01103030001d1070500103a50b02d443d10f610046002c14038011a801441289009203416480030950103020740541100445403908980c01000c6015034403400480c41403e500000c030301c1400300746404c950341c078228a401055105400c12610410f01062001000102400e00c030540280c012440030450702c03030038482480105050f902c0082861009003000551940041440d088050380b541a01c295964a018050a44020314600141d401c84400000c010311038020b40d00c1c05540d218600020b00f07107020f5108501c0c041d1a904113071410440d900c0100035900045c02054055034040d5002d01c05a11191f1b110005c414040c1c1004012031140c80e40808101004401c850007809103420801110000b400d000305032001030302823800000d40000012120600a04502 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 887614928 1250 887613678 887613721
    0x90a02130905040525150206150301022106120a05250f15050403230d0c02060706050c09100804061a030d0f020106080f07080c03150f04030c020d0302060f 68
    0x340120414161500d00c02c241030010003185d51003034840420b6442c0c4480e10888003038825001012581031092a80c0e03000e511507003c0303500c00d0703004000b00400806d806068020480d05102503410a40301c03480080d40c5e4200d0030300c031000c4904c034120030300c414070100041c0d18000e0384080540c650300843c0c5061055030849217010720341c0810701d055000c10042000305402180486903160040c1003a40301e94807180242e109040e061445e059038004c0d060f9440090003e0b001c114640c0c00c009022454035808940c284c002c07004050f00e210b0303580000900c51315042040344c842600040081d04104190000680781e000c066038165001ca152110140d5810901302000004400050042c404000d001c102210112407400e029030440d5200c0f600020851810000000d43c0700c2c03920041d0a00038148400f0380d107005da540c0d40c290303c6540040305080102d10394074031542d00b04009100201c0340e69039070b0500f5669114550700003500990030000450034140c0c0840c00d41d01440d1600071810058a030501002d42c18400440c04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 887616178 1250 887614928 887614933
    0x1e05091026010209040203010303020c210c060c0f0102030112111504050f0a05103507050d0e0607110c01110643120c050f0c010902090a021309050405 66
    0x11096210407201411009040300303400540750032203400c0481c040c0c0e0000e9000f280983d00200c100031091030030484650500609100c0990081080016180e0702c00c10154240c1c0622000250f041c8203100c01e000e84050b14650000039596569035480050f100007146400fa035042d1217140c0b000c0d125140c1039080100c1604441e2540c1d0405090108100e41141245d1040c0c2d486a280030b0009802c1e101d00301c0c1e000c4080d441c0d0701c0307120251040c0014950b6061480418456000c2140c03089248910601c0034036030032498074a0304944682200000d03030020280350000d114103100d036a04000725950300c440e03041c04d0216800c003512100c140c404015540c0c600c6c01404003030b17140c01240000f02c220140a00d5803001107051030300d8580320182c0c0c503140304030004003112600c100c484034041035200f65040100d403810030701c50702c17020003507540030b1000142640201a40c040304204006100882480c09410240640d86c0052a11003142080aa804020352146000250704617503081c00103500040c9105062089820202 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 887617428 1250 887616178 887616209
    0x80c030c040b0105090a03051f0203062107090f0b100f1409190320030601080a0201080411091003020f010302280507080a05030f060a050d14071e050910 67
    0x100006059040c81c02d40c100b00c1d090084403201d544403a01c2c00c004601444c00350903003020351305a407820054902ca0005070a80104140315250306e4450800d00301d20380e41002c0b01403003031003240c0c01401c1001942c003c040c1c060400500d54201e0f242a44014a045c8080b902c1168604072000f055a01040000000b0045420003540c101e202001d180245080c501c0149034103901034902500c0c1d900040c1d01c1d0010380300c8038810307c03c03083c0d80d034011202801603aa04a000b40441d42c50518456510300c61058001c3c10010260045020040705818035481404002c00019140c1b0306001740c10b121150b641300036440b40c0d001c4981145507502030310807038500d88201725030a071400a0800c0311002d4440281c0c89001040002c000c52000705a00c100030704071000b103e42c0e0b516600c0c140940007191001d03002d010180701d0306c1761240801c8141c0d591511303901c140d41d11504c0c40400320044180141480041d5000015415424601030070044002c080c2800340c070340c01c6176074039015180d000011800000f24050380c26052003006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 887618678 1250 887617428 887617453
    0x90b0a09020105040b0f030a0e0106050a061b1a04150506100311250c0f12030c30113d0204151b02011211040503010e0c0109080c03 58
    0xc008000060040c10701d0b03850143d07501e90303141040d40800009808039030040b00380800410700340181d4058000c550002d02c0007506000008070303042c031144208414040f5048141d403c0c5503402040414003074100c00c02c0071420201c103110a5420204440469240c50a00e910300c4a240b818400d5600596014003005500e42c5811002d8004110b191110081e03000c041c8100110441d0200d51101007024550303017110702c0c4c0710501e41768518075115045500000060708040c409440c4216005600c10780602d0040170980c00390030265079a20001d1106a812400c0c826000401e45c50020342d08400340066485448004184001ca43c47d04912005101049580c012003800346610750400728007004008002c40529032000050012a4083c1e8003400b03009001c0603014100c5c50f080041c1c03062201141e0644070075510300e1707400208041e40c0c16542c014082d940f0746140c800b0800070802d5034080d00000e030007000403988031004c155413059540c0e0a035002540d40c45011600310b401060340c21483c0030240003461403c5210 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 887619928 1250 887618678 887618681
    0x30607090f180f020a0302040302031207050309010825031b1803030804170a020a0b06010503100315020f16050706110601060503220c061b08031303140705160504090b0a 74
    0x36002d500030742c4580c5030400c101440d01c0107244168050310010ba6442ca140b041c542810030844000d40f881e501030007103030046440801211100202440c000825503900300051100c09440800f00c600c05040d0001410319541591003521505100b003284481070403000c00c22107104029504402c840c0c45582010000240550190b42d0018410001c0c01850441c01d544801c140c2c00038036584006074495201841401103518503250403610a04e00b061a40c9030000740030080d60a103220040c0382d43d22948060b0010842a03040e19a0712409884440d500c1315203080f802110420080180d81c51300510700e0004400d40a96001d050504080001d420b4683c40d11b00c0940305908020302201e41c205d40160f4402007000350380780040b821031194172005200c5082c80001091208204c0d007515408080308070520204000005699105841e50203004a80c0241d207811111004a40303070b0f4004001c40416454104807002c541c40100080d48041802a0b941c1c5208000079103180e4440640303a40c1c6810b01240d00d85006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 887621178 1250 887619928 887619959
    0x1050d030e1e09100608010e0112030c02030f07170106080309090a0f1d010207030906030606050d022d0406020f0a0809091b0301060f1d0306070819150302030607090f 73
    0x40e001c0b000944810008221560b0b004c03550165011002d403018080c0b43c3d007000900c0d01400384008507644d0f6605000704524136403030750800038091140f80088201150b5003088200c0c0091a904181c6466a17921010000d903094420280c002d05e5091900c00305070400300109070f640350080140140072035110b18088200914112040026580c3c55090035920501880384004191803584001a17482644d0704008002c204203401c40b82c06c25041150401100f984082540c0b00008100b00c010b0b610040310104c06c4114102d541d400c2c4992001c1c40f2004040103c540290044038a1f0740c09880c10360801030007090f1034251489008001900030301c130a07109130500502c0c00d0b51001030039682d0210b00d110760080f50007036003090340081c0000f54050111480f02e40d10a69150820701840302e4041040038140001e130f00c8160003403a400c100080b40c00041c80b0880c607401c0c0d4840f502c0d040d80b0200104c000c0707000b201d254240b80307010031782c0648501400308003141e1040c900b0100712008500d03030685560a0921209a0104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 887622428 1250 887621178 887621209
    0x5030c040321110106030c09240f08160303091203050d110406090b03090303010b2d2709070f0c2009070f1704241401050d030e 56
    0x424840400052201c000c800c010762012260b180350740c501120000d2101e21282542209641001c604100041c8100d6060341699003101010484294111400a10126030a008500b8a00c03500d40007030440009081030007685ca040058444617400440b04502070703a402c0c440200000c02c918000c100c6003012900c24901a4401d15100c0e24011800950307206031418201d41c0f91500e90001010844640c1005000d001011a042d43c1400c42c504036110a0b2280030502c43d00140c40b10004055a400c0803201003005e840c14156100b00c4820000007075425150401e00d80e0581c488607005a8081d07404203c61907115441000b4064581c81d540c902045400c1c44802404030180030b007a54199001035201221001c50008207010000d9a04031801041b8046202034825420300c4020300c1001c3c1040d0740800400a5100c001d628001c840d01d862420815240100800780060030001b49444000405070308000000d42e80500b0061560740c9681c10001803150701280100460b01e000d14404041c240551003443c0c010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 887623678 1250 887622428 887622451
    0xd021606030b2d030607020c030a080a02010e07080115051c03230d1e0b01020304140109230102010f020405031f0e120309010c030603031710030501021b0106080d08070503 75
    0x5091072221504902003c5815105000060400c1a400c003040350540c0407825200070013951080b8004a0740312510010040d01002e4005a0380d08594001d405c01c1c003000d81280122640c40e41e550110900802010944003207403410214009040d1a000c0803000c00c90340d241c000640c0c1e04241d030383c0c1615942420585254070843c1c005d034612010b02c00c035018140c1c02019050105550707041c40c00002c041c0c8180d2181c110041d2501002a01c10b0b6070000c1500c0c1610034001d00001200e100100591340c0c03451540c40350b08400104043c44001d841800d207002c3c08442c003a0024482c0107000c281890a0b0700890040d1034040d0320058145004e90384170600441612991740d00090000c1c0310303180e0141008900c88107401d1908001081c400080001d00c50000c102000703140400c0740600703681d0000c02800c160340d0810078130240038000c504004582002c07040150b510200840d92482030005101d00e1031401001070b8510752810200103110480868808107200055a030989181d41d0b0a03000e80346600040e01000921 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 887624928 1250 887623678 887623699
    0xc0b0c0d150f0503010e032511040c170601080106140a03021b0102041a090603010b18121f201c06090917160308090c0a0e04050d021606030b 62
    0x40c0c0074001d100c0d020b0000c0c42031a07035400d4101070034582520800c0441c400107601c00c204420f820004100c910780101010308001c14001e81c40d041c04801c08038140c1100c0d60080c80c000440c80c0c80c68001d5000030b4500c1c0202448265a0b65050040d90514801d22484010504070707414000a209480700400c51107074242001803c0c00c080382c10380b480e0308007010f1039070000360350015091100d1940c0d0719101c1d801181e080042881c008010b400702ea5a40018440c10125100104a02e034000b91040b4500c1c0c3c1441c0060480040002400b924075502c0111404c8502e44502d103503048138180c1000c0c0a11092240c900d80000b6101c0e0ae001c400505a500003088104400002c080f245550501030017800010220340f200418804481e0800c20800400c484405407103210820160765001d008003c1900c000da0907041c20851070391940622404e04944e4079510343e10501040001c15810010002d80b8041c41c0911b08031000b00d00151000e03a602c0420350900000c6000d034240c10841144a500421404d0901401c10300c3c04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 887626178 1250 887624928 887624951
    0xa030f05031b12070305180307020d0c05220c0e0303031f0830041202040506011110020c06070c02030616020a06051302040e010b0a090209030f190c060c0b0c0d 70
    0x3508800f1a41c002c3d071501a090000a90341400b859411000200c54204004540800c0030340e00d11401c3d20081c09116030000c1d0304103106448100d02c0041201070709500c03100c44203d403403a403212035040c104101d1070310b003048950305580706100f00700e88104050025032071500d8802ba5000200c1003e042c5400d4034841000100740100c00703000c00100e40c400300901c40301499070b03a041c51500400780d00007110741c60824801000107c1002c400030100365015076002505403105801210104040000c50341d20b031041d00070100002030140c1c001c0a4440d1003a043d200203445420040341c1030700107448065419405000400c1080c140401680c1248a40f40103e86005009594110541c5c004071042419403030490688020740c2000e00403d0405a460070013006200c0b12000000d440c0c100901640c0007040d808507507081c02e524204044020b030101c440854243c2002c00d0038003025450600d104496418541303900140c400e0080d001d08000980c0000e0f4401d241e514061040980e8001c4079840040a4503042208078 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 887627428 1250 887626178 887626231
    0x3030405060f04171f0506010306031403070c2309070c0b0a06050f04141501050f030f06130507142a0c10020606030a11010915030219020a030f0503 65
    0x1c00b403840026650b1100d01d801101d01d804204084103411a40000300d4160444400b2100484001c080075030010351500e50380c0040300140000d40004020205060200c40c181c00000081e181c10ac0c442c103a180c0d407007916049500c0c2d011032440741d9110050007113072001d2441d103080980307251f028034240b1742600b204a05072514400e01d01c06543d01c13540c850f61000c0a21003414001c00e071102d029800c0d20103018006010380400090b01004000a98042c41c3d080803090580c85107044070100c0720f03040c0c4030302c1d204d06020348100070011064504038807944103145858500300301800752500c10a1147c40e120040c16503414041c0301c0f41c1c801d1b50341242c2c007024550342c010890003414004115144170801041c0c98a082820b01215030480c103041c0e411755022604200d9681e4000512512490f0b22003002e03000c07001003200603241e00c642038220b41d10440d100510807608070b62560203016001c0f2502d05030040703880c0c07100301681c803825003c0016001400c200e12140034103004030001c64228020414002214520800004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 887628678 1250 887627428 887627437
    0x30a0b01090c03180515090c03060109141326090402030f0906090c22110c0d03060b0a1b110303040306020315010201051e1e070e0907090515090303040506 68
    0xc0e01c554a800001d80d5079410320400d15900004130303048019007450b8a50075540c222240300d10141b540010002035a00c1c2c018070013205103690281c1280e4031561503005000141c00a4590030084a01e42d83c001a0300358006101110300540003510710306840d1062814203450350503030905500e03d0508200c050350300d03181d0b4030045109903400850403170b2505002038450309000014011540f01d600c007109905d6156211000c0c5c02c0032000c0c2e00050030184044101d683c01900e45c02500c00040c00700030900320035502020411038102d15030307590704014440d2159030700f90060140c0754629000034281c07041d480d407203074200c0b00300d030802401200034540e06207510f00060700d958401d800c2190f20b02d40100511900111810940e44040000d0000b0b00c00b62030501d45001415050171801e1a2825490002c078919508000c140f02c10a43c0000a280541c60100c00182991014140301402494281c0004181c64415203a0300c00382c55006220743d03400031501300c0c4001160008084294503000801c0001000d42c0e5100081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 887629928 1250 887628678 887628689
    0xf0f061c06050d110f060309101d030408060712090803060d020d08040b07020a141c0f1e3c02041b091502030301081f090b042f1e030a0b01 61
    0x882684041c3c2400300d0341403c009128000c0c00c082c4284001c101020602409e1034140560002d50368003040d6803915159040320960038140000503010600000c0455070510501e4a501c0d500040c0200c10310501c1103175010603026140d03010a20105841d460300302040c41c0c00500003425640002881c1d101d005c5668010380c40030040401c0042c40307d0441c02c0960f841e00080c21500001a441c5401c400030443e501d802c082510160110300649034100b094086040100ba03810105648000300f4101013001207028907242982e01a0b1172003e0070f170030804100e2503a03030200c000440f0700c1a807a401c05c0c500c4014000b9800101d0340561102d02501c130b0780072118040c2a082e88540e6074402900e103804220b1011b11040000d140c03c54004000511483d600000c8005840c4559031040790600da14a24000060004000c014020381920f0107000c00c3c404000b174940d0394180749440d500a042e040304840a070040c045100203410001156901440c0c0a0b47c003000d4050420140c00d40301503a10703070b55600d102640d090308003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 887631178 1250 887629928 887629943
    0xa0519020c0909030a1211040501030522060b040b040227010302041e0f080d050403080f0903030a210902011202030a0b030a03030f05010e0705070b041e110f0f061c06050d 75
    0x60410715405034803210301000780a801c00c25045070100704c1f04548214002c3e24181501c900100300384e05440007034403c018032800f070b00c8805040d80d85407160140010340281c610540c144004e400203444c1520071200346488076084d41c00ea0b0000596211040d503400e42e4420305140d420f100016003e40c08d03101c56a800104003282d0300c1c0d028246492410111140e402c0307240306601401090f50115006002c442c140c1e50011420754461619445010241c803800c41c0c110740502000c1080c00c48180c010a054124064005a040700c1c025170b0320004049940e0b208020b40011081204942c5059181d0b0003140c100610789800708100740c0c0741001c0b0340380c007588c0f902c201c0000303a40790110a4020058498103002d4403110001030400e081016000b8000e008940c0003130800360b04030002c1400c02c0710210423014200f9010709030703518895081c24802031801c142480749025141d900c1c100101807804600c0c100d4820001041241060300013091144400a102e040042090340c070000072610b6520100244d1446100b60b41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 887632428 1250 887631178 887631187
    0x13051f09020a17120906091804060b090915090705300d051b010e07060909060f03030c2316140d030f0e01120e030c06010b0a0519020c090903 62
    0x1448142c59440d40480300c2c0004007071580d8070100700865460074211040310b9060f15a5481d0300003503184d2150000840c1c0c407100002004a9084041c29050700c154041e0743c1c2004050300303880c20300110410031a02c00080340c00640500b0100005a0080f40c0c000360000d017141d03800b03a1602c0102d0300300e840d035176400300012488420760b4218408100805080c41c21141c003a0000c0522001d0141940c0907813803010106910a075142c1082000135030001c0c1007200300e001140c01a940d00d0380043e007065818000d00301380307034203041c40490100003003201642229415590a4803e840d02e0700c0d01070040307410411360380d18000d200c1842c2590002c01c1110892011040940051a91174102d010038000e081240301401814207000400109800818100001e085410004403444009004980003280e0102e24503d10b4a4804001d10148000014008211260084550f542d0300e4443d2a070440c0103e141030000200208181c0c01800288200c5009268560044801141003034000804050040300c24410681c800718 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 887633678 1250 887632428 887632433
    0xc030e030d0203190e010912060e0105010f090b030f0c061309050f060901141305310201080c070803150a030b0702010e0c06122a0c01060e0a0204080613051f09 70
    0xb1643c0102d00d41c50825504403141100047c040301c10368801c54040c0c3d4040000c29084c0003560b044001d41c88406030082107250f844a00030200100c0a004040904d80b901d502c00381c2c51300340002e0320100100c08030010b0403003120750740400c007440d804091100c103a003c4102c400100e07154113010f46402900c0c0d1000d0910507140890034808403030703030582c860348400c500546551056100c0101d801d8a1521368075021a03190790340284041e80c5141c0c4011040c1c103100c0c211503220600b0141c01000c5480d8401da070f4038511a103c2c040d010006006459000c1c0c1009800c001058800191102c9080c15500203080541300513540c4d02c1b6032000541c22540d840240c5d44401d00c0090204040c8528101044110f62060416190705d50707400c44e0303000081502c9480b129220202c80d80740f00d80d140c00021500801d00483d6103618650070280a48090b2140312401740200000c92949040c0b40250b4080e07501040c010305075661241d0b516800c80008007400c2d0340e10702865240f0809400d4181d11495241c1d107a00c4041904801031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 887634928 1250 887633678 887633707
    0x3090c3102041202010c14073b010b0d110a05180102070602280b040326040312051504061d0a0b0105091011030403060605100c02100c030e030d0203 65
    0xe49061005610400051249900c036401401c0902d4082ca0318044089840c600401c1d960f5040c0503180c0544900b160018600701c0c103100a44880114204520035012000a05610900e02c0c0e604404510521070042c4515080d8001411008421180105903503100100040950f804042244000303034000805619045a84001c501c5080d000e20052210300d2070f04000035140c41000c0720854200141b200ba88201203a070346001c031285600105048075a04140c5000350280d01c411034004408480d03580010226400004024842c036003549664141110300f0080c1d10003004018903408040203140100f01c2c0303a0311580301e035034003401c0348525260360703d4a411004904081c006204101143c24440b8500085c0d03445015104203800507a103040108280c41780503181e02005604460301e9100100e00082400303a1b0790009800c4030f00035600c0c44030072880002c0803510355100910185d0084803c925a80055104038170300c4031014042c2c501401c08042c10000a030400c0450070704500103900c00f1801c01c0902c10342 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 887636178 1250 887634928 887635009
    0x281e020a022e0905030f030720012d15090b0f06090d110a03050604060506011b0224210f0709030c090207031218030e0a0609090203090c 60
    0x184407200284944280503410001e00050302c0c039102c0c0d038403a161002080804c0060f1a460500094400c0d01c91904010040481f118400f2034000c5004010300b401c030010701845008072482d4803a8149030324058250b5240046c0c03041035085030280340e0b968030210780c0c041e852a81402408a2103004180817202c2c1007080030600d400c3c0003003882030008204c00803581e81d03000319421106620444c0074000f80e41b4100010f8803c03c46500203820780c06118204401c0003656440240320307650980340c4084864041c0070600d020b5950810003500144030440c1c250364900c00c55469030315800924200b510740402c400c02c1070b161410781c080c2000a0031500e002d0111b00280780b185940c0c0030106150600701c0b180b80d0744a0b00b400e804144a40d2486603030015403401814415415030305521003103070050055224002003002c1d420341c504c0058001546506080196207825510380041750340d9541c405000380c1c00c09554000940c00501481384a2042500c800351030745400c0032180014a01c4a003011280780c613450684401d094 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 887637428 1250 887636178 887636203
    0x140c040609020c06060f0f0a0b03191e050414100504260a08041506080f07060e0d0b0612150115172d0108011a09281e020a02 55
    0x14003803d0451100018401d91028040310010720204a0303101003018242042411600030303040000c00704814403ca002035000f28141032140d0f0076420f10703030000c000312030352405000c0300e5a80690703c980e0550000d0708200c1c0c0007800313451810007072117900c40810701d880014021004000d4a075410001071213140c011f4651030307084010502050307115440b40045544201d0780e112041c000140042410f1042c4000c0394041d0001d582d00400c40c6503292600c042d9100c0c2950700e0701c0e060b8804d0841c0443c00a11a1810f010b041101402404220103a40c0c0c98406198001707180e80c3e0040e1042e0404c41415204024450042c540088549000e504010b00003500d60717505042a0b050212042d00c50f284020280c03401c0794414661801517103002c0c9407101e070004d041c0180041c4d0002841746800412801c0047d03102102e440f500000484020410f90180112a072040300d88600d200d0b410f03078520500b15030200301e0004070101c5620001d003072034924140d0300300b20011061600100b580880ea04c180c5c15010010f1070f03030410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 887638678 1250 887637428 887637431
    0x305010e040b010b0f041a040806070f08010506160203010c0801150908060114030a0c08060108160503030415050c06040f0218040c15050403080d02070b0c0309150402010c140c040609 80
    0x1034075031a1190011010b214540b00f2160005501182800020aa5000d4480603003210480219007007520111342203030043c031409020f241d01283c41c00e03004411600d81d41030a51a542d0050f0b2a00341001402d4000007030100009190105400050341d0a102d4484a80810340325a002c070750401d16000045050007041000b0300203403440034400920b0009405045030003564140b50741c040c0302004a803c100714804000c0402051a03008613042c0c0001c11207505031074602003103072002c0c150342c54a501001d015204039070709904100402d22491100f805a4000c92484e401c00714689103900d04d4035071801100b10703030980b800c8001304035400443c80c20724162032103615031171200242e90400341c40b40a0090070600c0b582e258080b45404000c20103000d4420b40e0015900603210717948076041c082514010394044401140c0c1c102d1828005250460440b00f62405918804000d000f80c210b10742040c0713041c20b0040c0050f81845003031070030880012803404c8403001c88031b03901000d40011010342040c44280c0e031700d64012041c41d9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 887639928 1250 887638678 887638681
    0x1090e160e15041103072102070f0b370b1002060a0c020c030a033504080a120609020d0b01030e0a1b0b0a0804052413021516030305010e 60
    0x5181c2214090300040905680c0d00a520340390006401051403900d0440342c85008005c00451a4108000000740440707083c90b0102052860501800c030310038458001c0440518000400c0070034044c2c01c011354003020201d1004007140006046d03803c8560555040d00100072490040b036100b000600415910010940c0e0144c11142d000c0c8000c0e464800003401ca17004690b983c4c0100031500d100b0802020100340207020b4074804c0340c2c00e0070020600c3c0030340020241c504049840d4200725070800c4010b00d41211044d1201d2200f80c8460b56411545da10108200c010401509118982024613214600040050100040e0b07240c0c0a52503420984d08424510b81c181894140604010b5a002c1820b40100c0d41c850880344d00c60360054040c3c51a106250404030440034049016035003140c0008440c0d0045005070215400380c00b050070110036600e151032101e08060195400705075002140388840103ea44020000020a200c00310044850b030040c1021b022a030352034109000500d0f4051140a01501d000100505c05 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 887641178 1250 887639928 887639939
    0x70b0405010507020402071106030703020912030a0c150e240717012d080604150c0f08090a0b070f0e0315060f0a080105100608010905070206070f031401090e16 70
    0x80c1c3c0600c00c000b03030090380c001401400b00700c041e0754002d0104800600300b50b102c0c240400d0042c000d400208000c0e020f04101640e07000600f03000020798608100c0780d40c0e81403001f60380b80d880b0b14144072482200111503807104810b07100d261084c0480ca4588941c0002c1071490440d000c1c000649500c0900103500b8400040402d006010b4084805815078006190480316251820481d200d10390100005c160100c4440001103098540440c819010305e006400d060240c00c00c800d180802c803003480011034085010325150100c403901407406035902101c5034083d2040780c01c40b51202d10440c1400c50307540c00017a500d25401c524940d0003d1038036900940a4008200c03e05010a10100b003a42c06464a48501c002803049040e5a03078078455540a804240700910090400386540c500011f00381c001d68010905007400801d4069261140c10321407006a07000f0071903901c58000c1900c4242c1a24050010180c4070420900c0d902c5104240d1802013280490028104800745a80f5007003c449840300e030f040c2101031004010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 887642428 1250 887641178 887641187
    0xc01050a060e0615031302041a0103110f030708070507080d0e0709090b131e050a0618050c153907033306030f0506100501090b070516080f070b040501 66
    0x44c410440301515074030340707620a22001c883c036001c5000758400e00300250300c003442042c48400d0b0320009007a20140400840e400f48000180640e407550005041c0500c00603c06034801c544407508207a02d802c0003403030850786858484a41d488140046c1d030450301d941c012814042e0403c030031802011445400c1104806e15a01c258064002401c11485590040d0507042482124501d40d07a42c90710b1310028580304000e615249440d00900c12081d54903070706d4601c0361410312184071120ba07149a0f1241c060031801000f44204020f8240e440c910012a440c14080c1030f21590b6003600900c1010b008942d202d0000b800e40c40320131603142d40d0b00d0025900d074000a41c2000001c0008103503807030416550054940a090b2078a07a0b2140b940201c030100071460410700000203200f03a0000740da813154007540c151005691452440c0740403050768490b5a00040c3e5018040049016800c00762450900c10b0055070020402300e0045141103505420201e0160804501201084800c2000000a041c0b101a03030b420640b82000180 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 887643678 1250 887642428 887642449
    0x20c0d0809030c0406061e030b0a05010f021e1b1813060e030706021b010c020706050a0908060403020606010f0e030d03090312110405030c03010207051c140c01050a060e06 75
    0x10101100850791581940d400d10403002c2c1044040c01c10050075503a0440102007d07020b841826501c0407550700c07180c00718820f0242d0311000401500d88605076150200440b0341c410503000704011400340c0b0702e440b5540a035100250f0010b03074a4a0080c060b02c10000c4052071809152247e40f8444d0701040600c0ba8107010016072954413100f160f6a122003032040c1d0900038064824502c180005000000f54103081061a601a001742c0b20305040b0700c40b0040302000c03200c1c202c030409074071701015a0040204100f07240c41080100f41c441070b645030200c1d0003a62801c0d01850180c09172011400760300800c0c02c0080c1540d105501100101c00d0f4901618400418000700c1d444002c0c1006c03007800c050301c50b0036000915004a00700740c81c19036600010070400c3c404e6000c0125036003007800340c140320340a12506000d0074030781402650030050b0086d010701002e0341e001040080040707207802482c085c007440c0c00960052000000c0176100300c201e82c9001007458030b0030f61000001c9800c1a003228000e03e000c0c100f405070340c0e1540305101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 887644928 1250 887643678 887643683
    0x901030209100e040501140106030e0705042408071502031204030f03060b0a1d03010204051c020d0b130c1208092407080d0f020708070b07091802070210020c0d 70
    0x40d07507888007525001d001ca59a0003000038035003c0d00510003048815842020350a50280e03112071380340d0701c6400450559501c2021203640e58080301050001d4503159021101c1c01002c2e03c0045500044402003640098041c0e00c1559990800501001001c1280d0702c9608054014405540f0b072903444075820481140c090b0002d001c00040300120a05076000b03a2044001e05880d071100e075250010304000410040344101d03440301100901507140e0450405000b40c4081c0c820040110401c5080d0190140d91034031726800507a400101c0c2400344010840401005004a80503155036407a070582e0308291007890741551212608465905021001c11352180942c0c00f0124200d400c198551181564a000500184d0710441080400030b40b903030400a00000030405405c140009004142400300544128040c440d00034050200400c0307a50300260700b040c5055403114070303030801143c0790f600c861710300344a59601114690031075400a925410752500e032401c4030b1700a40314402003204d0f49044010072100030001000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 887646178 1250 887644928 887644939
    0x304180605101b12021504230601080d0c021f02061e0408031f050a1d01170a0813030c03080c0c150f0903011e021e070c0e0601032c07080c09010302 65
    0x2012074400d0010940e0150304481051070350030123050072914840f1400301d15641c41c110109001c2c51402c0442c80a048030085005000482c00c1e0007410385841e0000c91007240c4c003604010070007280b20801080e41c801055154000d00c51480d1082e010364440c1c1192600800c40000341c410000001d840d201260f5029004240b80e0a41e00e03140c0003508100801900019813050144401180200e00840103151204961144c000240d0f85c0d808942018102c8401c1403c0d55008a14401c0200e20302d100108030020807202080b2401d9507984034511760541d981c200321103c4034000f5090b0342841c01005a440c0b40c2c0802c45810304007071100301035440c41344100041c01e13460766004581070109940a500980c28070351007116034042e144a5441c0b1000070361000b02d403004485070148412110001345016604030340d5000e0311890000342804200c030490040240141d040540380c004c442c0c2d0022407080020287d803030700000e01c4500440c0a01181c142480c40d00080c1c8682e200c03c006c0411540d800244904483c0c06882 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 887647428 1250 887646178 887646203
    0x2191e020409050609061b270a150507151503020415080f0c03160b120c16050d0906020d050d050402040e03070533180304180605101b 59
    0x301d4003801c58004050007600400307003004003c4034003041143c0704241045020310904c0c1d01c090100d0560207404010400d6a044951005164071300d0060024940c034010700020916941d07174403010b2844c400c2d00002001440100c1c2c520100601050350044000741500d0074440004042d101d641004118071000c1e101d242c450701855426004d40304100c01510540b0140c4070b80c5078280300349954403000e102c5945d01070f110711001c403034a01910800d088151035131a20800d1030b009820b4912541c520004d4104010300008010116442c072140040c090420b01c40e00140680c00108000a0301200c1603a2103281903400c41c00e0710501686e4041d003103416001000c8000100b170f45490020500604a24991009610002a00174240100080c18a04900b10b0009400510ba07445c903200c200c001e540002401c0320f4404901080245000c1500d178a0000c02e08030407242003990307034500000803141003061006519070b215001e0016091400700400034010030300703185c0d0018103074813240f2400141035440a040c00c1072044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 887648678 1250 887647428 887647433
    0xb120604110c010911090f061807020115180606030e030702060c0309030706080108010c0e06030601120924050615091003020706050c03061309050c100c060203010e0702191e 76
    0x242c07030351803440100030801e4506525211080d002403480c80e07481100160300044049030307101c50f003c0c0b040901412130241c01d5050f2085110125010f07040790250f540b540d40075054490008504001000c507415000d00b2181d06440070300484101d0b412407001c16003440402142003c0000440c0d02440e8151040d542d40e26a103401c40b800c41c0100b09885926005058000035086e41c040f2001d4140c0308000020040100c9142007503800f038002c8125a40c2054091001954960240c5407607030030550300c0c110100318001f0030394a01800240034640c110403444542818140b800291142607401107094480081c80c81c020083c04525000d42501a885404000425003025200303030150f400c0c0c103074084000d0026040140c1041001d8200315100d50260800f104154008905402102042d581103005002c1d185070303860034004102c0b25881d00405000c1e0030250b51000802c240b00a500030691008120110300300804024200074a8070f1303000d000e0402044080000c60142c01c44140c044621010648512106d031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 887649928 1250 887648678 887648711
    0x41404120509010311120603070801050601020a080f1303080d27120203120108010b01030b031b040c201b030303010b03150d020d12081e010e06180a09020a0b120604 72
    0x8003141e04034105c004c0780380244d50505101301401174800310159200e19440303a030317002d08072101201c1050041c0e000f0054440496840c400a018042c403c0c045140741080d1168420200142c40c0d001300c1d41840001401003912000d84100c015800c50750980250811000c40f80070340c004002000a0021908000b91550250080040b580301c854240c60702040380d80e441a9843c002c160701e03946a030100303040400e00346961601044401175075070020480c1429070002d000303004c002c00006904c40144210700003014101d0010b51144004440100010866240d07000e5243c0d0744901c0d0854800c0c01b99200f071006108018a103c15258481070401142034448070300c0000030104916840302a410060400c04041804072808205489600c00d8440450646520010b000c0c1029030044003400c4583e1000144028680d1007103407508200700411207035112011481c0301401d140709490003002036a0705d0b84c01a0840c280556620000e1a41101540c2064889c24200030700c4000104614482c99a50007520001c001c003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 887651178 1250 887649928 887649941
    0x7020a05060702060402030d0e010c03230f090a06050412030f18080a06050c042102030a1b0905010506030f1f03080316080117120f22050414041205090103 68
    0x101168400c2c01d01e4040a901c681003510141e010340030710704080400034013501c0000c8180c003040e9141c1a000c001500c04481c64403240410b900f280880450008a044181c00504600800d240c451969080b6900401c48003039610b50000003404814071080040001503411450f1035600350030111204030340303a80221401d4a10598102e1004648900842d400800040b440d0101c0e12510040240e40c0301c0365030880b41806144107012941411824405c180c0e01e0382414400b070300d071010301240c008030001c1e60f407050710b0080d08800035901018900104102001806554010300301650141d1440c01e100300c3c0100d8402c80101045a24900a01c0c0c80d41c000f850807000900854001103080d072641440d440248140256041c0780700061807400000c1004544c59603200c2c002a08180100700840b00c02c0303818115504440082c4c1c021030b0003400104010312012500c2000c44140001019110741004100421990b50303034510003058051004100001d00382900086501c4507600300a902c0f1a50030004030b000d0000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 887652428 1250 887651178 887651183
    0x171b010c0c051804030e011403060105130801050a0c080a05070e0913020d051b090108072601020c06010911090a05060d18060912020d080c03070504050405070804140f06060907020a 79
    0x700002e8520403010029083e4001c0e0311943d83c0808004042004540081401040140211041020420a6010b04c004262204101c41c20725280d07a611564182101c02c202d46003030303040d521150b0900d40c19603c49000b59100159100400c00c0d8103107048010000c6140019050154040d4404120b480c0804000062090b41c01480e414842925181c020784440020b01c1c02d1281200c5400080310625000e02c0b154123803401000100155403420350030100d81c1820652071a03103d80300c501c601c002181d080c001000c4920b1903400070100c41d49000703011000c42d10100700c140c4e0030181c184003048641e52440b116104031070702154100d884400419403400146480700460754000c0c4041d02ea20200b0885030804120030b4040d031594080012100c000740d840364111541d40c0000f0345008000b650b1b5140741d002460b0020803914110381450740307a50218088580a40d48030010038143d000b00001c01c480028444080c0c0b8004018001000c883c48600741d4429024151038407504281000600452081085102a07034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 887653678 1250 887652428 887652439
    0x30903011b05181818010c0f0c060518030d0504050c0a080c0409060213031109310314040806150f0105070f0204390804030f0804210207171b010c0c05 66
    0x21700342840c40701ca000c03040641041d135081c0242c815409001d050840e5290700a515051030011103907660740000d01c0d00030000080c9020044a04c0201d500400c080d004a07029400005442e040600b0700d81c4c42c01030710198a500c81d070b002e020140b1542c40042080c2c00328050950380030800360140c0c546540039009403894642d04a007d50000000e20400315038000c01c010055400d07140a807103030035103212503543c02c1040121181d0000044c80040c1c0d200204210400e02900d030554180244403015400c941c082c0e800b40c104ea41c4101d0902850048901001c1078120381110090102c50310000060000d0040c0d18020300b1030f1044194200541d100ca81042d605021220740e140c510202035040c040000d041000171151821a0b000401300300d900520340c0a000d1034054a402c01a012040e00031514610014022649014001070744203606010058008450b281500600207042c20014000803c40400301c211006070b1058a5400c3c45a000c00f4450451400a01e400d42c0d001c40181849d0702c000a40760300c07480c1c105 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 887654928 1250 887653678 887653681
    0x1008160b0310170a150b0a0e04030519080405010c0e091801150e0115170a09080921160f090b030f0609030304060b040905060a0e070503010e030903011b051818 70
    0x8501c04a100f81013284284207402d5580c07044141e1108450140004c0e907009903900b20140615070007009541e520611034588585031a08001d8100300309020449054003058495052100700320081c05810b03908000b601d4070303400740d4580d01e0005804220142c800d21481039001500302866000b034110303040710a0400ceca0008425603402c2c4541402d0802d20030080e148034012a6403100794416956800d1030310301c2c2041c040580e141d860182000740b410240c2101c900300d00300024100e980701d400344144250000310782180c455940051050909601403020346204414501c2405105400102c0c1003e44510407000142701030148003092826044002c220803a00c0b8810420182039000002940b1a80c81b4070802e0085040480c1400160b13000184020141e030040000215628855803080c52607080080c200c5962a0b51781c0c0105c2c0c02c4640a030226000340d0000102c9141c9400c0902550102800000f10486551001312004080b4002d02c4005108800c10003054469950b0b283d101404101a6024071480c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 887656178 1250 887654928 887654969
    0x314060102030720010e180f1303020a02040513060515030c0102010c05030f0c0f07050102090f0d020d03121d01050405060c0307090e0604090c0b0d06080705010906120908121008160b0310 82
    0x2c0c8900304d42401c002306e00b1400189584c3c0d642604030b1132041c1d25030000c1000784101d03802c00000c1c04005091000d1010844c511401042e1540245800360a00000a402c006c95503001d042c1800c0b40ea51600b03065a04090b9038001c20780d03005c0200d0364424051210104151107121a810084c0f10b03401c0081400c10000c40d20b407003800343c103600810300c2103401c5400000b51000710082c0640401206000396200c42418181c0c00031900030001c0d4541c08444010008100c00c0003504902804402420b04c5180e0303650303204001c1000410869690061720200b0300504625250740020841c1c0c1140c09907032320340360f480d80200d5895255600300c0c400c43d40c0e000300701e01409e80c0c441c0c0149055402030024a1034590800c000083d1207000824020182c40040c1d41d1024400e00300f031800c3e6000c144d6205d88450669894100802090190340070340300710381e00b03c0c0e240381260901020080401c0c200d070300304c0c040980010201a40c9190b40201d010b0459081d0001c1648035650005000303010200381e071204100070340c0001074070f10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 887657428 1250 887656178 887656219
    0x418091106070818030c10030510030c06030c09090504080406050c03070507091b091401030e0309060a0e120601050102072709120306081603060207170a0314060102030720010e 77
    0x625130b01c031a90b80d800c0c241c1e40d01c00f007658951030031740c200707400042d4240341002d000d120b900030356440030040701d51914030380d6a5510344046554540c4640b0003e96529000380345154005a19001801609400c2c0554100360312914524401c0703120b1001031100c0041e0f02881d0f180306000343c0c0d9031580c10100f40c87c80b40d603460200802510300c003420030078000340a000d0084043d000d18140d2050b07524100b40900e19004003001900100b4424251b44411720003800803e9840e50750b0310040a5a503400e9a4070a020a0031400384181c0350556244c0e15504c0e04503800610190b40e0025000c4100e51101c0b080041611000e0701d0200d0f4194100001d500e01270900c0c0d9080d00340082c2100c08580c2e50802d07038007041415500d0040f5900c030b45e07403440411038540e0034010810200d0040d03000fa02440e03000d5075036803070310385001c85942c0b0507540900f4008010a48881170500e00106041555902801c00e00244d8034000715641e94410084801440c103507103180c58410500d060344140c050b40700c0c511001d01220080d469040480c030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 887658678 1250 887657428 887657437
    0x9020a0527090a0b0705270d0212100c051e0a1e2a21090816090605150304060e01020f0a080f09012325050705060c04180911060708 58
    0xe400d104d034031001c15040703441541102c0b206044d01ca42c100b4041360081d142c03460310192641c1e0030361001952504402583d10b20707800c2c040007021000108991080c01d501c5c001500d0f2010145001d009050003440a824060954405031940c03c803003007a500c00c00b409080c3e8180042004420181015202c0c1c0c0042070b41002c43d0701011101040e4002c114120300041c6540c0141d000340042c90540b281d03003001980016100c2c01c201c00459030804500558580591074941241d0b06030355002c508042c00100461a0b282c0314060103404c05488a00c219130a82002c9030390761201a00080510340e550861448410702941940c2c00c2e2440d01d40c0b125a20b012101c0020501a0142c400e05000704c5d80d01c001c00d20008052040745819020741034081c03401d0940001001d01e9090042c05550020740200d07450002c1b056100a5050183e401d485281d154807031350034102d20300580208112076581d001c0100340485401c60300c3c0301d034400201c803001084140d4145080440e101c142da039540e40014000c1036143c100000c010180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 887659928 1250 887658678 887658683
    0x903060207060b19081207020f0306070c1a07140d060f150810150809010204090c05071b080309060d1404030504031208070e041a13020a09060309020a0527090a 70
    0xa20841c1e495411040000125116500440d401032080c06c22030f00c55400a000e0046c0028412000c0e51460302c0480c0c20010200e80e1100014181060b110400c4007480e030394030544075103c800b65038600c0d06031005480c90600200000c4101c60104038034444241a4001001404c0c2009202000e00e030750b01101702c0500400c2807024085000c500006101c1c034140c003c40c900311019001d60340c1d903c490440d01565141005071504040e950200f0002c16040340c68001c0440d051030715500c099882c00e090900e034040b20000c50341314101001c1d18804100021000058a4000c1011518203996641c000f03400c2c4000c00e0302c10600c0c40b10f2a8070508210038181c00001400869000d070f021194221000d1800703d5140e102142c002c0b001c00c961030b9034211942015031100001c503191018442c810304030032001515105a405020b00640c0e0002040b24050f54450010345c0241042e040500140806e84c0c001101004640600ca00501c05103010100210000c80c050b0701440204004d9202c0342403881c0c00310340322107481d00107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 887661178 1250 887659928 887659939
    0x190221101a1002151b04090c050702130c020a03080a090507140109050603310812060a0f030521131e0b0313060b0324060405010f03020d11010903060207060b 69
    0x40000c058008514007940d46108400c1400700d40c1c0784018080d0000052217101c121910502000c2421410380c410000d8001d520b40b41c05450b04604e20420005d0903440418000725420300c5141c0004a4001900743c1803140e16080c07156240da41c152004008119207603018145100d4010001414410501c003907000400030f07a2499505074545c410320159200c1034821500d000106072030036140410703418485124044425148407019415115401c0d42d070021545450b08034a4041403007000e1800e540d0310720040c01d80402c440041840c44d1a0662240104501003880c801d101e030710000091491400c03201090b0408581c2040c103030f180c2d0000410111200d0300b0700c0c03070340b90366050104072440000c0a82c1e100300c41e814109070480c142c5598090107400c00d030380d4483d09031240c40c00001c3e107400e24001c843c90b2186012004001483c000c404c00c402c1e16010ba00140b111407003100d0134400f585820008641c0e0f0398002c0c9619002c040a10b0048500c0b8056a0000d803000f48085451000c010980c1c00040444804840 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 887662428 1250 887661178 887661199
    0x41a251505071101060e010f0b0310060f0219061406030f070b030402061b060a0e03030105131a06040b0d050a0905030703081302090c0d0c020115140409020402040f08190221101a 78
    0x848270643d200503540380a1003014108200403241c070803c48400c10440300c2c81034604010245074080455207210f50100c130740039207030100140c451040030541c40d0310030b00c110010130f17040d524161810f480b0501c60280728401c000010000702507442d80000c0300d080900b800a48481001840f03001a00e40405552104551342800c074041546080002520b060712401060f59901ca6940c44104004004100ca06d0445003a804403810159440001420040000060003070780c60311010211f400301c03100240001c05461401c9880004124004144c800450303050030051415210403541d2071000408100c000d43c84103035582004540012140544100d0a001c0003d00100d284884143c0c02c1e00c001d081c04803070a0040040030040300c40001e07103540803d1070213800062090b00d40c2d0003040590303209810040c01c007071141030104407201c0208406170100c3d080d844459800111a8000307118100001e00b503a140450401415204000c244645c44d0380032800501080781003007488042d071112080300e0241c7d201710301654 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 887663678 1250 887662428 887662439
    0x3020306120c010e0906120d02010c181508060303070c080a290402190512010204030210050f032a0a02010b01081e1803041a251505071101060e010f 65
    0x42c8015000016101c1c034001c107000c14280300d216080103003120385c400740505194030a0301052220345030045181e8000320f0a00c3c0c0e1004042c010203000c5140801e000d1000d0340c104100341000140c50080e520920301001c2c103440700130000386035000d10f801c041e00010481000107a0f0364400256405601d22900b0901d4207076950140f107811864203604144030000c2c1880000340103290032030303991107074803101d0312043c144a0b07e075408102c502040f0401140039a50000d404d2040d890501e0304400b85400a1070030a07d0310611403924483c1d8040a0b006800000c1040002004502080e001030040110840c002da00c450722001c00034060305411481e43d0100345c2210119180c80b01041540f40100030002045141d52608072031911005060301c035000050006000114412450707001d110601010f001e80035840300c000400c2c440510f40320b84403407000d2048000c4403800056029607410326404540710001815507070240161851445c078040300a480d40b07083c0021401018440d00b0034103a8080076111282607440d103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 887664928 1250 887663678 887663683
    0x42d0905060102060f0c04080d020c242506050406090b01051203160f08040e0403020c030a0c06030213030b10080c0f06121015050a080907030c060f0309080a0302030612 74
    0x1d864003801030b00084005018051803400c2c854001c035403804031038079040eaaa07400e1410010080000340c0140c02c8459500d026245c00d490180d0b030440c00c0200e5001d0b620031560000090f200d01c0158800d1802d40044803032401001c51140342d003e1303400132401c2c4020314081c904a00100740c480d0007291140e401c540003003410304124140040300600300004601c0c2c460001041042c2c1c021401d400c440d1030201c2105000051080800360005103003120102d0180c1c242498041d0600f107032546228025031080c810000821200034044040701e00604005985030844000c0442003909500080d02058101d0103005010320032503500d80c104c86047c401c0d0380140440008111506000782c1308103520030ba0a01030f1324581c66200d4003050b0803c81e8102100c0c10540e48550044c42805004803d6001c41c001250901d0025004000ca69101000d040545505801c580d074442210340540210701c2009440b900c1440218021b81c1300c405500e40143d06280c0350000c11000602a52080383d00d0b40c050002c880c901030120900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 887666178 1250 887664928 887664931
    0x1171b09071809020c0c0102070e040b06010f0e100e18060604150c0b070e21060106050a12020c030901020115140f011b050a0c06180504090206042d0905 67
    0x800000180e1241e03034003112064801e1081008940c90003200081d414240e100401100e4401d0003d030607802000e00c006402c040c0254441070345014842e0030000050440c2c602281e2040c02400e1084107609103140c03c45643c04154040c41d0096411004010381940040301820782400489424501c180c101c00c00d860035020a0b510550801810302044c010441c0a9031240021340091410300582142c54452406500c0143d80c21408601079803036440b480e062040d107034000d03ca032050ba421804403204182c2c07982e41e44144250300800c440414210031261142c030818102c080032903401d546514506940c0c944990000721050b0140d0f182030b131683d0380074440b040c10f901100e0076803003a00c0001540b070341404030680181040c141001072800d05005480114020840e015008000801031010989020328840305180c01880030b2180358079040407010301e103e60310302c10f40c0d40907900810900e805e0b2002c103841d07028540020581e004190030340c010400da92144400d1403a038183c031400f0085d5841d2947c0048440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 887667428 1250 887666178 887666233
    0x801050423011406070c092906092e030501080c040e07090b031921050f16020a090203010e0907050d150c0c140106060215060d140f060117 61
    0x1c10400403c0512410704060f0050708014240b40c2ca040c84136680e2482c000d060b078008504140d500c000c804010900040c0c05880200c1100c9a800c81d810008001440c5d805000d6000e0301c03545520303080c81c1901800c0110300100d90030b05d854243c03941c046824003070007604c42401083c00d103100c3e40c003c400481c42d060040d22290001030020b40600303800c04960754050b003011401503816200b0103407824071404150003104442d9001e8000e401c0072107170102c4400400601e901500e410007109010710b03800002c03001c003102c1131030f0f040d40d401000c803524a00c04100c000d1a183e000b501018404000000d18241c0c1c410010f20403480344003991505500c0b00208a240420074038041c10321448459000000030440d030203249a07510f035042c1424444110303520b04044006840e402903003651a90400c101083d01003116452107081a101580107103010808114a08505071000d0805c070b104c1e40103400106801c2c0b0a00300b41414000070b40b030440d80c40e80160300c0c0c030708821308004a00344a100d030310312041e003c200030a514840 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 887668678 1250 887667428 887667491
    0x6030405280b0f160f02120d060303030b030601061e1b060203040c0b0f030a05070e0a080c0102010f140f07140c01090c080f15090312040b01031403280908060708010504 74
    0x591202c0100c403917a6081d032030001580704400041c0d0b040050320010749141038004401040360350442c41c00400360741c807058055010747d20800043c0b08083e042078542803184001d0355a0013200c5030a00d07080303406070320400d41442001082c04982040c02165002903100b02d010f0701e041e60070f80382d40e64040c8010344244920b108129800b07101207940b104003500140d41040c0c1c0341c58800c20302c1c05001d00003000070005502c101c80f141e00000850026580a0007619251407180b10300300b00c4c00101840f5000b6580700140345914140e40700780021151400307401804050443c1811042d00e0348a04980c140c000c003403100c1c0a842a890004000480c01000500040d0174503201d0080d1101081d034007403d030340311100a0b000356001c0c04103221008542601140b10307845140204140141945035041107400e90b8840902102e19800820801d41c52142440d400603a00800441c1c5030001c590960302240d030040b560b0007030402da015000074002e900d0350000d2594140e5000719805c102d03d0880e00c26040070f20280004500012 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 887669928 1250 887668678 887668711
    0x307080310082823060a051b091c030504030b040b0109051308090d05100f15090b01090b070c031406091213050904081b030a0908030a0e06030405280b0f 67
    0x2540800d02c0110710384e1486400c11003508441807107420318104840200e18036507030b03d0030054031507030000f122900c81c840160030b01c1c81c080e07a44c0003080526410000907240724509801c490200f52141081301c004580040d420241814949440c44030b03c0820b103d140000b130b003000007180340c0148400e0030752100d6500c2013010345030216420620100602d105010780745805001e10641018105005511048120500000c3d16658015521a250f9000c1c0c00011807646444540c0c06940d0304061004182c5094500b41a151030940c43c003801d49250031740008014401c1920412200c140000b82c4502444d40b10301030700c46608403652122101e02502508550741c00e5612000c2084d410311b1040680c201c2d00910083c1c0c42c1544180102d18182e628080054107a4400103c3c4020107522500ba9806800702c00040e42c40d200c05990024070500103001d40c1c62061000002007030402070100450703107000020182191005c40040b003494900761001a00782c5042103030f18002507480c189101214071400d10103803c19010b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 887671178 1250 887669928 887669933
    0x5070c0606080c181b0d060303200604080318010207080a020c22110c0d3209041e0603030801090b03010207021c0c0f0e040309060e101103070803100828 67
    0x40b1a02800313000c04072001803170301ca909a030010014030990500081c0800c090b440c52030010406081c20f12200c1c145e2740354a5140c5441e50021039a150002e811082d00c54032a16074801c2d02c0400040400d184419600c00541c0001704101003015190604054094407105081c042c103000300501003200f1a9044007a00c0249080000300d0b6002c01c0000a046040e40d044c84100c0f0181850a0030b210038580c08500d00041c20440c0588a0740f4500040c007207202407018440c0304107121102e070300403602014462034036504100c031512813001c2c1941400e4012442404034540d40c1c10058800c000c28010241c5417828030b242c050143c2014000c442e00264080c00350f81c0160145400c590798110a540129814445200c0001d200c84c040c03141c8001034558104d0006007405d041c1f0380030f06144071036130080c824880c2c040503085140d955510b6240ec08401400c240e1481088043d136141103207c1c0d518010b20b860f1003c818060f500d07906501744401e440400c400c403000248482051890b00e545103014010041002c0e030308400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 887672428 1250 887671178 887671219
    0x210703020a1403070b01030609120c081912050a0c030c0e03030919240210050123012003041d1902160206120a14070203090909030405030105070c0606080c 68
    0x164084214250382c286080c541c5c070320f0315214080e40706032142a1564182410301007a02c180c41c1710020300707050400d00e80b00c4035500c036400c0c1d005102ca81c0901e402c0343e051484219004202c030b450100b25050003003000780340000303042004040803900c0320000b900d0b0201e03149141c0d00817111000d0707484004004500304401d550800090207120840d4158801e05010001504481510843d8050480a040841310302400704000c0c80c1002240c00d107900c80b4240703001000007580600c069192b10180e001100264020707400144c60034013000f080400d42c0030701a0400c400c0300340088058010f9030713410000d0b603605528031381c0002201c11003034402140c0980700464060104101741e00411110b5580461039000c19181d400191558210030b510680f181150400c00031032a1540c0b0901d20311b10084c404a038010f0a2084000b9500e0050b00e900501403200304021a200d081d00308243c5009000c010f000380b25520303004e20000d0a25030011011a0340a0a1150101c4c40d10400b09642c180400302801066407503100c04820407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 887673678 1250 887672428 887672453
    0x507210f020c010c0c290a0209040b1e0306010b0f040b03041103010c050a1701060e0f01030605040606020c0a09060602060c0702061201061805030106182705210703020a 74
    0x248507420460390784050710a0141c3c0000d05042c4d01c4241802840b0300f000309032900f9040c0610300003100f0703000b082c040006848a20350440310042c1c005858181c0350b40800c3c01425410390711a0b12448050444912425141034102500c50a800b940c3d0f0999840486004a000ea0000001d407460240030a1018445c1440a15401806041d00c03412104442002c242180d8801440400040c80011600e550542042c1e1880f10f503220103840c0045580742c041d00034010502d07203d40e903100d68071641440005d40e100343c001d000507081c0100f003042241d9a07602e01a50b02c00049a1050040f084140000313548030030361180d80112501500900000d40c1d0301c4507140d502e54094041264080805d00040382c0252611801038080d1803aa180c1001001c00a1040d2019104583c403a9102e6070504805024020340710454400441c1131441c0072400c4425802c0001e035800a94403130383c2d40341504103214000d001c00040c40c8107410080d03100c40f003090090411640400c1c410400b01a0140c1d11421004001903603400c81433 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 887674928 1250 887673678 887673701
    0x90b030d080402031f0b0109050f010c060c030e0f0604030305090307170307052209060801180204110f1c060f0b12190609020408060907050a092304120201050721 71
    0x161008022407205d040d40700c8150f400180519981c503084041941c101d4000000342c58111100c050401207440001e01d49880f40600410f803603224110352401c00d0203500100502e11208085d2002100c0c0101203954a14045400b0f4000038101004104151408001c0f03554254201e0036198a01350032261400d0942e002130422401c04c0b0007013044510300d000d6807040a5641c0c0100d400c45842c985041da2000c103440042d04000d9280e450140d60300101c800204c1400a800e5041c1c1d0041030703118010a0210766400f0702100a8011007000038880d00d40c150524131140f41811034503080000700d4540061001030708850240b0000006c00b004850804031b9041c11642c0c2c4010714050405800c2e0800c00d425041e500d50b64400401d03e43c000c1b900707014802c010300040e980800404002c0502d0303440c1c88005150079065200e49104142e6a00c0b00c080104103100203401100440480032800f41464908203002035035040c10040194030b4280070a01092240b852071b00c41c03031081100390074246022241080105101d4020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 887676178 1250 887674928 887674933
    0x9131b081227061e190c03080702060c0a030506030312091e0613140a02040606020f1c021f0204080a0c050f01020a02060d020a031401090213140102070308070302031c050709090b030d08040203 84
    0x40200081d00c45035040c075000907a031b140b0212450b203240290480d00058901019900040300b0008010600820b44031300c84030711b107404113854a640c0040790652059a40301e0907141808003c0040311000010f0005050341d01c820411241c0c00c8524402c4d07268141070b9801d507001c2240410200c046007103a800e000440c1c00c1c850030307036004603031035400a0116400f561000f000f60700301c404480600401070050107050107800080071081c11181a0003034071181117081960300443c20ba23980041011695050350301414075241101d0034030300c0a0810b5801000700b403003000d10505400d080807002d5403000c03441000055010348801c0c10110115400d0380a500300c03040010404d50386000c00d001d18038030715001c20700802152000581c0c0702031800740300907441c4403030700b00d109103410b13094111180b6680002c024040725004100151174800c240f03800c9007144200042c001c050b400721080480070bd940c40e0b003d640155004c0d107641c405541e44030b6402c410b490700303050180c0e49034110b900d8459200d400b44581640c054402001e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 887677428 1250 887676178 887676187
    0x9050a06021c05090f0c030708060c03130c060309020a05010309030c02040222030803150a140103330509151c02180a02030a0b09131b081227061e 64
    0x4001e0880d00b049882842c20351220600d410b421106004180d1070741419070141006a0034a270080d55641000740403598604800030002d80084d10000305001010350200b40c644002c0e98a40c001030240c0341203c0140e215101c115000a091360003442812042503154407040042c5206070200002500f14441d03002900001043c1804140f40d0b42c1d1501014521400030342e41c0300c2c103013941501c2403107420200380b9015604054052162000f60320342200c03440400d00e4049801d00f10149646450120419010f031101c50601c80009101500415101628030075141501541d0f82c40d024141d41d0900040e10f50b4120800b011281140c1c0c3d01c00241801950000c0d0076150041a4241d400f81040c1088680c19051703580841801180360103401420f14211007207406681d203013066481c0d030481c464846c8c2d0040c014000202c002c0105c4551151500090100209440d508003034501d5a0510754000d42c051680c40781d801c00384848222410404d81c2c10804041c2c00c50341000001118071b044100e8040c000382600c5814030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 887678678 1250 887677428 887677477
    0x408061f08030c061b0a02100902040b0d0803070f02010c09060c05030903120310080a03080c03090f0d03020c0c04152d0320040c0e01030c0c0605070906110109050a0602 74
    0x4180e0041000c0044c0b5051602c1c1004003002040414003a255110400c01103044641c00940542307400c107881000254201c9600c0054014030f10410403070f4010100d01c5a078020b0202c00300142d0300c00c01140d212b0040d00c02e02d20604074200c40358103400f8004688288014032203284546084100781d4400e0701201d03d40f903441400a46880d10204d80740380c20000000c10002d11a0502031514001e08940c0020010501965405450b0540c001c140c03211500002c0001000706c0000c0150301039042549081d1101c48510f0031005010358008010410107124182284800d030400d4403070070b000c0300b01200002c482d250511503102810107480050068100300314910105078900c85800310011071003039036040080c200c00c40c108100705401d00007442c8600e18050707192111139000341038a50141003d04c1d0010314a042c14000380c50000405501030b10191034201000310359034002001c070b82552a540c4813011a030001d001002d00f600c180f840003c2590300a042041c0c0000c010b90080d140c2c01600f8009054580c0040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 887679928 1250 887678678 887678683
    0x2150913140103030f050a050a14090d03020c031516050f1b0d120506010e04110417030406030e030408071e08030a0e0411040b07080c1c110c060408061f08 68
    0x1164151044020707900402c10190040d00903606204241001414005503480c042d1442c01440225824001400c1880300c2a4a02000322016200c0041004544c42c540c0e0400a688040511105009200348480e00c407111031800c0500d032040c5240040044403078049a0300b254180c0142d140020502000d0061041d040880a40d000c1034800030740040c444030b0040e44004001c206034000f07030303001180390806126260364041030703d40b03032814207031008500f03108207a0fa018028825588003001d45500143c44045461000c00103100302c03111642c1c1800504911000d107503c030310882c03048032401e0380f100d581040f2440007000300140c204d04065410146650b12038083c0d0071a0300814404002a110003c940e02e01e01e49840340c44102d18402e801542403030b040c02e10b0601d451141c044040d000400201322500b40c840100825041c1e040c41319003c03000d1886c1284080d00d4006026018021030207003510701041410440243c8080701c0400c0d00501d0f203a1542c400d40d4007081c0000c0c4450302506c000400109448604 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 887681178 1250 887679928 887679941
    0x1092004090903020f0703080a0f050a08150f06072303191218081909080703020d02030a1415010911030115180b09010201060f1212030b0901090b04050609010302150913 74
    0x3040a160307184030154008200307039070360050354ac140a82407020000240e030141d6800d81c41000c0048060720304451100003000404110900703a0700400004080c0d04000d9051403000c0c144c141c0030f16011210304400d41203526400b0f9541d40c042100d141e02d00302070b1200e1003542c89451401d0f00003400284480180310318900525030300740a4030001c41c0001c88070500707294031640062003c420b160641050f800c001403280c8549d440d202c081c0c415850040301005655040c02050130399940185d5141c02a440c1c0b402564481c030b250290700541d282c64000026891496006000194140c5100f003883c40c0c1c01c10307000c82c1d0003105e182c90840c03c001d000403a01c10301000e000030441c09010041409612101110002820759126420800d413500400c4010005421080d0340700c114a9440520104c1c0110110022401480131507050f681c4130040c440006445503469000c40107111041d9401e100c00e0380ca5038184280007100303200003900000000801d03502d5502030009480c0b01600100003440c00590322a0a100340c0e80e5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 887682428 1250 887681178 887681183
    0x40f030311060703050108070902070c05060a09080607020a020d081804090602090a05060c0d300b04050105010e03060a05060621060a0f031e080403150501092004090903020f0703 78
    0x8800100c040303a0703410001a0303031103c4a49030910141d818180403d03100e59003441000000c0d600425007001304086010941d010340009482c0c3c035114800307400000c0030820701d44103100c054059500818036651010550394100307500035020580104084d5500740440d8071801e600d0480082000741e0481c580c0e29401030380c410350701405c0c3c00740c2c540302e043c01009070546855014030710441e001c0255510901000c5204402d0140c10b0410302c0080008500c105000c1d030603030650b09180c540d020560700070664154801a100d00781601c0400c29a82c8620040d00c0000d000800168154403990000b4590012608840c0e40880c000d007010303050405842e21095032956000c214031050302c072502080b20508015003c28018600e4000031010245940c848425525050001007403010302980d1003428883c0c5101140c0096611041c0c03244409a06515080101800c1c0904400c0d2410324241041a600203003c000a5203034001116141034541803490008092001045055024031034484a10000c1072040100850 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 887683678 1250 887682428 887682437
    0xb0319140f041506050d061d03040602061f0302130504060b15040e07020c060d090f0f080a0905030102090f040f1407121b1b020307080607120b0405130b0c040f0303 72
    0x51614200c44507011180c203140b00d003131911404104a43c0c0c1c03603403090460354001c0c10025070721007441c07092204107804103612401480001400a03106600181e414881d544000140881d4800c0c02c0440d440f02c8064032029600c2214441000c44c044025840700360840d00c07662002600003003135000305030a0441301e007070200001c8010604001d60381147c0c1c0d500d50702c803819201400640c01e07a000060964000c0303102080c40c6a955848907801c0003030540419041a03004081a0381e80305144c0f40010b10b960000c0d11140004070f4403080000d80b41414000d984140e100105000e0950b002c410501004040092200445985036803608625040c840b104501a0b07040c2c4d5598407a0801041401c420703200c2c1000300d01d803409a144050b1030300c07983c894082c80414045404425982100c0e000003464029243c11000c107500614044c00005a0482540040382d03c2d0118180b00c0d0200480070031003240c0085402c46014254440c03590300081c00d088401d0b50000100302614107042e01c6e5200c8200e04003c9420450208 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 887684928 1250 887683678 887683681
    0x120c030c0603010b040e091005180115180e1204060f1404080706080a2306010f020a050601050402030711010c0302091804030c022211030115090b0319140f 68
    0x90605224103031481105462161440d4500040542944a640b140790102481d80010480105040c0100740700b59003041d506000300d0809070241400b003c1d0a003c6404107600c0c24000003012102000400c00703c50306441115069043c00380c1c014094500c8801c03211190042d60110341205080402030809801aa0b499521429a01e14040c1041c00b10039442e511080091108012211000541d0416500d1074501307202580c8030009000080c081d8000d5100003944510041c1010a0742212103601c80c01090b40c2d0300c0c1c8c0040240d0816600d03801c917844040e059800490041c081030906400440e0001d23054541400c0c00c4910a1461f821582071509480020740c00107400d4a062070282c401c2d1140c440000742da043c2508240da00503110781c5ca500720007401410411074036000114140280d0500020303100003801007803101a541c5100340e009024103c0845030101300100780500c02c00c05502510300c42c1114a10316200c0d003815500340c1070060417400440fa00d90700401e01c1120404045030240a45840c2d46103503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 887686178 1250 887684928 887684953
    0x902010c0209151903050c0a0b0711010507150902031b01081518010e06040501090c05030a0c031b05120c2104060f020c030703021213050d05010906140a141501180512 73
    0x10b00c0d02d4016020712500001c1c5089c0080c80715401244c0c80300e544100b0b030200c1d00e010b5000503a0345004184025066406001d2417654005041e002411902e02c2281500c038407404c2940711150b0b06c00c90110141c0003580b14400038000b42d140422000002c40002c2c120010720664000104060f00e098204d0103100c0610310030722403a41020301504e40074202100c01800070a080d440010018040102035000c0c0715210b109a0306414003941c4080c4002c1c6507039011094045250201030003a82c4502c50084051540c0400030300d500c0c031020152541071005920000001c9100c0321313400d4041c180640262030050351140d07681ca51410714030003400856886c0000d1525000b003810302904003640340503c140c5580c42000b845030000c01c400041800d803401103a070b002464845042a60040c94101d80041c0b40300d1901d100c080050022800781841445d4158040c00344a10b5802c0504d2000c0c0d082d110040d1040c4417080d14220b640c040c0482e030300052486c07044100c040346c0d54000250301c01000c2003603101c290000d5258260 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 887687428 1250 887686178 887686183
    0x90f060412023a140412050c0609090103080307051c05010302010e03011b111504050303100f05090402010c02270604060e09030f0901091e0e09010902010c020915190305 74
    0x480d43c0d041c00c91505100e071000c0c0c0f01d543c2008441001d241c21a80c80d8180c1100d03405000681000c951011a050315951130f902401001d4000d01020303a65407054802500b5946041011181d0030000038140d031003540d10b1592003070302a0700050000d1007404420b11035410444262001d02e245401c40c51000b258039413550001500c5035102d600410700030790400e95200140000030800c0f41c200820b500d0300c1525840150141400e1a842890425100088100780001d1090001c09107000b03400707080000310200d548040d401100d48092040720340201c451000200998000d0001050b414009480e61b60340c0d401c040185518000e85d0307990024807a0005080c014141898842d840152440d041071142c0c0b401c00b003110940d68051081082ca4005000489100036481426410000c0c006007104825503c943d509420110380c180c021074040f1054100004c01080050141804c0241c040c0c40301c140309980c9801703201c07140c1c3c0003c04004440e4003102441d4041d88501c032404903000c0100c0803003003001e41580792660 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 887688678 1250 887687428 887687443
    0x8070602070503070303050915010e06030c03030408060f060604060f0302030c120406050a0507031802060c1501090227010f1404121a06100203030129040320061809090f06041202 78
    0x12001d81c00008050004009d514046040d50046451700b81c40340c2e071700d0000038030708406040180e0301404003180004030b44500142d01030042456a00b0044c250740d84e4000d0080c50302981c401c0500050000304440300d00c601a038010358019160701d4006140c0405988080c005c81d200382c0e800c8905907030310740c03c21151044911440d9042400f6140501c80c20700d506140288039441690003a1084a0000d4840102030f02041000b52180010010000541e5101c10b01c81c000d40103420030040d0003925102840d4501400802e40303482540503141c80304c414040d03040855000100456404d8008410400030030024828500b020341c1921035041079040c1c0581040003a000380340a8040360042c03410f0001200d9480e008020389055607903500385c2031140c10b014040100d0759400d012440c040f9080000d4040309010300300000c0c8200401c900d924a0402038a48244044d510908034641c0c1e032110146881d2242d41f81c401092508804031070102d540386100c0803045401d00c0010b8804072428009812010b000940610421 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 887689928 1250 887688678 887688691
    0x130c0804051015050f03012304030f051c0b011218060e011b05130f030c060807110c0f0d02040f0b0909030f121e10080f06040c120807060207050307030305 68
    0x14452203070b1180c4010461520340c001c072403054000485d050050b440c01d5000240b0991540008007044c0b0000001201000013a181a4009611920901072413400740085481e003500f0024501c0c103403d050103e0500426401001c1410040c02d907420a2a800030350103424004c0840360242d407410a150b2908404030384e9201d50701c00d1240d040c03d003205420342ca115103044500c0f01e6030a0441d42c8d2504500c1142e141c542d50340168400b40ca1201c004400d20455407100c0302a20001c0c0c0b201e58081e100c0c00d4082c0c2e10001d0042659042d40c0c49100c0c44032031400c104111500c8038401808005d8001039079400201551034002040001c69640c46c0084850f01d0f104210744d410194030000f4501d0b024507040c0e41c0415100d030880103a119890003011030460801d050b41d071400d562600c4103090150403c1400304424420f1446403c05034400d40d00d40c0c0908100109680780150351107082c02d8134141c54241c528805000c105c0b015035065000380a1000829860300091107024894400b860791503800349409401c0302c0b03014040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 887691178 1250 887689928 887689931
    0x150301050910150308040b0913020f0406200a0213090501050a02030a0b060c0709051012030c020406171c020c0a03031206060e09060405190f0b040b03030c0318130c08040510 76
    0x100041400c05c1c0071103050301c904003800303540c172940312011031841c403017a86aa181c0684000f410305501407881000d401500c041da920315880203400c02c440408414005445506034200c0c41c4850010700d499405014142c0a049002c14600f400341c44060031201c0480e1b09a40c410340000030004a08100e00c16100000411103450381000003020805030ba659150040c0c070340107680d50000c02d080340c84a056000007001c0392030b15000300801c1807600070242c10810704228029810900007103904003160003104020f407100130040a000c0d18801d0046041c00315082031400b540601d5040306156242d1030b00c050050f5020b522240c0d59820510511400c03540785501c600100421608040296510f203004560800801c460104040c0c8450441a0500a2084801c5c4840340780c40310886203040c1d250810400b40100310b1342000780300d00e444140341d203910a01e820041a43c00822512142a1112000c0340e540c0001034005800d040740300c030a280071101003031000c0300401c00c2403080008021040080034800c100040b130 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 887692428 1250 887691178 887691221
    0x21120e06060a0f180c0309080309031201140d0b04020406030606060507030206091507030b1f09080609060702060708040606050a03150f0603020604140d0b1024020601030209150301050910 82
    0x200b280c113000384402d101d49030f60b00d419180440c284a40c1020104c960003e035482d0f964244071969940d250300a02c035482a4170302c004000500142c0c1d0030980442c4003406414410001c2035a0741b589407051000f042243e0280e541c0f480840461024822403000e0803c503101c0c04e945562908003e4a4040e0040c030803961030740014441c105491503444e0b401e40016180c01d010a1801f80c807000a240c214024200041d03401642c051500419440307040901200da044042d07030001e40f03504402da83c40750b030200c40300070160b400750021810291080307800383d03480b50090a0024085272a4000610003004542c000d589403480ca41c11038020600902c90705142c0507503004108409031075680400c41902882c070501e03400d0f24000c21012581d0715440760882a4550110b03038031841d8603151150403c00c00503030040c29000382c03109031002a900c1050005100350300164000302050780c030b10750800c142c3c508020100a141e10031543c1804107505c090041074010084807024002000507540040c0c2251070000072480b528030601c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 887693678 1250 887692428 887692439
    0x6030f021507030e0f12120d0e0604020604060c2402030f2409070e040e030c01060608010b04031101030b0306150f01020d09172515030921120e06060a0f 67
    0x1903d41c0034444098a031030003c103103c131001071350006d00c044072096240283d84000c04290308000040a1a00c900300007003050300501d020a5030340720700488009402980c00c00c402d00078640180f1140181c0791047d04452500b8008582501d204619010b03201c0038a034000c014001071850010010317070300001c1c44000005080304110005410181c010743c05000b0407020011402c1e4512031428140e000c000544180903208a0740f40150340c80d480040022199407038244e0108039540315048ca903048039261540c090906045403030340054580c4855001d414169a01100f03100354030103110281c420341b04101d40350140d081d01c400380003d502e020f2f41114115009a0110610b664102d0803110a4805500d5008000fa0034070f407200d0700e080300f296000c2d81d0890301c4070f000200801056900c001541c0b03030700409034410b030040c050035415510b501e8001400c1c3c00605101c1c40c154103080799658800740552800c042d03103094441c001c500310741c010b02c3c0030706031900400c0402c5200c1c10041d82d1180200504c070060341d030062921 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 887694928 1250 887693678 887693687
    0x3141b0907081303091707081006051f0c1a0a050a0531080f1806090a0e060f09010b07030e060f12040f0203060c04090513110d140106030f02150703 65
    0x1800f548222038a2041c0b801494410689200600741d14114008020741400c40266582c440d4819541e091003204181c5a60314410301900701240c3c4090400003a4020384021000b00d0281500400c08001050004c8070200d440412440650340c00720014240506111a00000b51036000f004225003906100074407888140444022800301c007000ea0328aa00058904d0b2454036000c2050058010140465001000956600140711050300310110b0000090b190b014400c0303900071040c1b0268002e148940030082d4002d0500390617170055000f403a8210b0080380c680002d10018080c2c02001001c0f0021035007100b0150041c4201019a0046030b60504114035004140401d20543d112281c0907800c80d4045401c01603440c04c1190119401402e664981c0380c04030b10800c1030f800911a690b00d840c100400f02d8003655104402c410360a42200b40001824007074000e21407207444003c0102d484540710103100fa03a4a0081c840d84001c1c5102d0f000c1800c29002c20300400ca009180d5036058103500200b0801c00700080d800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 887696178 1250 887694928 887694931
    0x4090f0b01080907141302030705030906070915050c031608040501110105010b091023070c1e03110102070315051e100909021c232d010603141b090708 66
    0xb4240700c1003400c03c5c2c540811003645041d800c81e40075074008824070924a4001d03001e18401c1c0024000c0310810750f54000b0480c1c001c03280d88030350180e0b01d0b0b01c0a00a14114427840c0181080c95000e030440b4504801c0401c000c1c607010f106078017616110341c0801c003804035607480080900d000015030300030720280d4144900c0710038600ca41d29550380306032640d18010303000c1e500808129040c0110201000000045039042144652108008840a0070201d0010500d80c7c075441440922403d1051040c40d02400e60307603515140c034a03010406e415880703002000000150380c0d90a1441c03039590700c2c50210311400c16050000c2d000300d25941c0004800c4c841e10070410551840215081101c55600000c102002240040b50482c44a410b05a040301c03580f0350b00c5d1081c8586200003808814801d40d01300b41f460109040c503a1200707030b68054a40c0c001d00740c06917038651041402450f00139184580000038400e41d43d03540d003840b10310303030a00184040d0000d22641003460306c000c8210b0150401510081c0c030629040000403c2d60300b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 887697428 1250 887696178 887696189
    0x1e1b0723061b2802010b030a0c1a0712181a070506060108131209051503040c0605090f0d02060c0303010320010f081911042603090d030c03050f04090f0b01080907 71
    0x1298500b41a9584c070075007100d500c45101806864a24509082604d22104a401400380500d2010550410070040c1d0b4221424981c11101a04066030329000c00c0310001401e401e24070000280040205480c080401900d0014240619059413080c2924090b814000000c0c031841c10302c01c2c958104040301040c40c890014140d841400d15803810108501681c1e00e500c40d8200c19003040c5580c12200c1c1e06d080c950001c50049000d00742040301241d070b4034002c545600c0741034041d07500020706003000e41c264104450b41031038aa01c010035190074510b0440d1800e1440e00240d00a440100128000807540041c488450390086c2003031070310300f070b144840d0f81002d0006c0c40050899400c408582e81480da0148a50380440305e14000100c420340ea850b6650700210240240804000e24046c01c4c1490f00022035000044500c0100c0c060548001241c090b20b0546d074241520301d0a409000d010800000100700c144001d02c040c1070380c1280007a110300c999412104592850b80c4403814407081c1300034040080c40008044c1c04172003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 887698678 1250 887697428 887697487
    0x3705100b0a110114132001120903020a1b0f0f05011409041515020d031404030e0114070b070806060a230408010e03031e1b0723061b 58
    0x300c035140c880c0c010401408000100c402c0b13041880243c81e054105600014056031205500305000c061030742072039001d01804d41c0031906d080d0b801400e207070480c1c00010342240240195412845542c444002c420040010303440d10a920a200740082100000524080c0c074880e07548141145c10f140000c0d12081f450320a903801e800d00440c00e00d441c0d540300d4010b100e19024849480110650398018141d003800c1c400140409400385032130090345d0900c24400c1c0d861400d2020442111610340352002da48041e030f01c00d07040d81007180f401c1403501c00c0c4260303200030180c00380700d02c001150924100c68028407200c0d020b410342b0321510041019521441d400000071040828040b51048520701501007001c007403103154410111542055403092070b492010000d10f00c0b4507003100c6443c1001598084413009100c00710f800720409408004081c2d5504d01c00300c0904142480b5200c10b0401d82200d000c4c00107016050b00d5040080d0b8041000c214810402181c6a4919003140d0103070703810820100400020700712407066030000b05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 887699928 1250 887698678 887698697
    0x403110a020306132117220b070809010c0903020f0402040b0c160b07031e11100e1011070303020304080f04030f03020c01110a030503041a0115020d1d093705100b0a 72
    0x16800358020447c0342c92031801d0307050064068649545088400c40303918000c252408002148130406010ba0207501c00c0c59035400603c41d085500b0801a1019404101c0d00140e0a21020a4141d4514001e02410205200615200c02013407402d025030440d5401162860038148105c10019800000b4105c0c18030064618450709000c1150449010748112402d1410340320b00024003428440650010640c09806025111070049004008095640d030001d5860039000230480d500100b40300398083c2d40c00c2803184000d68a40380d8440b40460007a041a081070361240540d00845003016010064a079803034100382403c006a010801c552a102c040000c009014044000b0008041095a07078008103280b240b0904030b206541c42d0202e54000144610340c00002d44a0001d14010309401113a072005090001c400d0855100180000d020007400701030445402c00c00c1c00e26000c00c4e8022040d100d60070b22000303030310081070403d424102d003000e0311000b82240203402504042400381c100c40d40f0454101510500340310111 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 887701178 1250 887699928 887699941
    0x503010b1804063b030306010c1203020f0706060e0709030b010902070204020c06100312110624090a1e06080309090711061510020f060403110a020306132117 69
    0x94052580d8810505111070298881d01003450700500f441800c030008095000c4e901518a0b58074442929040e0101d101d8000a40000703018020b40c0d484050b1500e8050704100d1854a01151500180c00458030103855071000c0c000a0f904041c05684441145070581c0820b1550b20740000b500c80c1030246030781c1c6680014504007591502c1d0101d40b001c00350b04044840340c0c9040d5014000c03101c204d0108442e801414031b0000280340c07044100340c003a001d07410041d0000380c80b20f49a0406824503040310001e040344941c020151941d81d00211b520070440c400340400c01c455000254100b0300e0f8000c40c05030345d203480d000d0188030140c03000054441000d41a60b1412030703a180d41c9801d8a030b240221070343c100c4520581d070030084100f03940c0b03400404804041e074002c0c40407090800141d0f114211002180c64030b6010341c0004000c24411180f100c0034030100020745081c02d8064000c6030800c00101da905400710821120107003002100d00484098580c802907101c7d81085a801c001c0c60011614482e004081070103000c0380c207 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 887702428 1250 887701178 887701181
    0x30b0c0a12110405180121050c090613090614010f0b040b030c07120e090610022509060905061c050613021507030305060a060810120606050607050a06060503010b180406 74
    0x913000042020660800c6031152004050090007105207404645040c0d603210f5001008008189a201018081201250302400840500100305d03030f620a080c040340544c0242d01d842aa040c5900401c40403c2240139076460300030254060703200c0f10314401d04080c20021084888160340a8a040c26803013075403074580e441b28001d10b000d0f0980c080c00d0600444d000c4c10805821070b00340d00310350509498002080d661001048140141680030380096001a441c81915561060b92800030060f0360078510441c07611440c550044408a420000d0303c0399840d814001d030f914140c14003941c40c5a40102e401c0b80300a884c0c0d10551111005031034201490b030801c1500d0304550f0340e114050340304094041440d40b20b80d80c6040c024050002907914500803009100b000c140c5503c070f83c41040c07141040520071a2030702d1815404170b00e042841350040d202c803641e45902080300e07a561801408154003070801000c1c1c1d00e2290815204968065101501c43e03890442c0380451a00da101d00c03801c0308a510341c200c1b802c641c3c0d40d0900b60b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 887703678 1250 887702428 887702437
    0x306011a0708090d050f100f0203061005030604140a1d0601031113180b010905061e01121404030f14041809060e010c0809072102040902031e07030b0c0a1211 69
    0x2051780c028031511103500e840000f02c03c014107002200602c2400412060328049100a40c0d009130400c0d9040f1401800501510041da0000d202500c000b0f000221307507010080b420410b0300c1e08260552101e0b02c00ba41d80111010784003250001201504855145a0340c041e07032076203c0303101c4030300484030298041907558082c0d001c803080411400781803180011600e00440130b00310074010b06d1042442d00000c280315050002405004404003500c4050550383c134401504c0006095412240c0305448a107c0c0034048080130b0b008d4003a501c2a112044e9800e410382c0098103400110703a4682c82e246091000b00812481100040c61f00c4901400001355901070f814003e01a044103100c0072015070a080e03c0e0414075034451705a034800c0d217007103043d00c2190d6150800c020343e10382070080c0c800d585900e91441401525140d840002c0c0548009d040307800ca440b03404c510346800c110300e0100465540054404005000d007004000c0e0707202c24090307002480e040841001800c4403101c61281c20800b50784400c5d10b041f41c4030800894 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 887704928 1250 887703678 887703683
    0x262a0a09050103050105190e06071b020301020f0406030b01050a1b02280f05060913150e0108010c080a05010e0f0a02040503010e01090218130f030c0807050c0306011a0708090d 77
    0x780810768613402c201c0e001c0c141c141c5505660318124080350403024100d03c00c1200c3c8030b801101070201c54850315400c0350380c3c40d040c0c4046903d10700750035070910040c0e40c01d20007881c140c030001400b107444a141400c043c0c1200c40301441181808400c100000070f00c0e80c0700c9004054102e00c0e031050380c607103800750012959054001201c81013070b0114070540c0404058000700c075070888490b020710700d8003580c0f9070050014501a410605402c220b0500058141c081150001a03503504103008280c082c40c0d036081d1402c1e641e03200385d00011240e5590f549130031181d64400040340d48034206403414080d651400d00c41400040b8010252200e179124940415180d54a07501290b00414004000744442083c1c84149402400c186000300c0c400d0909829902a0f8024000641e00c030300021111401c0034441501c1d048060201400101c00b0044a03000c1500020061806450002d0041d0300500c0f42c2e43c000c1041c1031070a01d040e04000544502000c150100140301030840741166804003415841d4442540810404444480700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 887706178 1250 887704928 887704931
    0xc032a021c0e101809111608031503210a180f170c0904081e0a08091b0603070c1403040308131707060e0316262a0a09 52
    0x3080c008903844000e00c15048003c40d55008481d20700001990703802d0300000521071581144104000100480d440a400701c0580d200311440d103012034600c1403075644189011601c204000c1b084c4440c218a040d011162040700364000c1082031001068040130324004840085040c01c0000c1ca442d803d4464020301521040c0c1036143c00100351524038001104405001d683c02090307443c00e40301d50906001a00c1c600340d0802604c00c0f10651900e0b00c40c0c1085034810007546c6403001c100744001442c0d58003d00200403041c0c25503110501400e01c110b08609045130310901120601c42c0500e09243e81d91392800716504507809041c170100c4240280b40c52041c14003a0141c80c000c5000218000051040c007400620320f0f106403070110001e550301d411500c032080702c03907c25a01599104840c188840c60050784046d448a200070111054401000408000c505070b1350000c520542040b03404d140c01e62181d5074000007032100c40c4060201c2c0b8440c0c40d0f01c417000b59028980ca81003010b5020000403030b612603000300800740c14403000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 887707428 1250 887706178 887706223
    0x40203060609130c0e0a2d03050d02010501030c06050306010905040e010b03060f181b10140316030b06070b06061b060f0106080f010e15040605040e060a0c032a02 71
    0x400b074004001c03015007100800e0070000385e1002c925203810344006840148080100910301502002c0b0350040040a0881040c0301c0030001c130204a08100c00045c054065001007825070452074404440203803644204140f01c42402401826a003117076081d03080d103034180d50001d00c1c00c1c5481078042c0540b41c05582650180944000c3c00700700d01c0d48071122482980840051681c0010507440265030780c8400b10700c860b10801e280090041071624100803001c001a900e00346601c030034a02c002496942c1b0540b81c0c1c000c0412080b442040741078040c001c49035021000c0790005d041c11880e440d07940e1803090081100b886031400186454082d11a881e420400d001003404890203860f000fa0349070701c00780b001c1c01044042400c1200090b80d10703203483ca000e81621800c0c0030303513003058079940c425844400c1c0e00d4200540c0285c0f5242c01003186d86862203044c01d4a4540f13401829141040c00b03403501180e055085103030425041401c1000c0100e010000e1005900d00950344198540844504900340700c40c8030700200c2c10007a090f2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 887708678 1250 887707428 887707459
    0xc0e09090715030b12030301030305301501031a0a051908030f1b03041503090201112d0703080a0c0f0605010e1e0f06010c0302070b070b010e07030e0c040203060609 72
    0x61140c4c00149050f039442108524110361290b483c002440000c000400c208900c2c0002a203001100c03400301c0000b0314580160251a2583c6103889040310329401001c00200b10409540c0d00d8062018003040444003448980e6022001c40c0070031109014480c0284c103103005490000720815911402000e002c0306a944540e00d00114120641c0b001c0e0000d00d400013442003525803003501100f142c0446010700c0c010750414034490400c1c0c0c0980390011040e030502c50081084e00c00204180860000b82c1042d101d45110b80b4801c5030800301e480c2c00c030501c1d45c0300ca5102c8041803000940382401c40e1902c1c2694100302004021a00d082000c540c2c41034001082617007004000229442c0240c803490168084242a151104e2100700001001c0c0d030403a1441e04203155140810881e500540504604501a00c1039030302c1a074464105018a41c001320742103a01c0c4140c0d8004000c004100d42116811203c030303140c184180c0c403075000c0f2259540070282c0c0440c17080b42d00001245031599404110348080348090011000c4400c0c20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 887709928 1250 887708678 887708681
    0x11208040801060b1e0f0a0c051f1b0c050604020105280e09010602150f07020a08160201180812030a0b03010c0309050c0609090c09120609011b030c0e0909071503 71
    0x304207842d0003840b828030380c098600c8041d00c80da00480202c2d5801c004140e00210b45950b0f00408c2940c03540900c21210040600901078610204141d00d8046411b021510f019651140c035001e203d400c1204018501000440104186405c1b40d02440c08944070245c80b4400c0745845c41180c2e401600c00e90107050b0f104031542040448201d010200d4045200c0da98034402643c03540010307422042c0e01540d170000101c030242610821a0800345510460f500340143e50317100c03002548004105084a00080200c004540e07010005104032400408403001441c500071041f99508100d280301c41c0006000700c00a00d0340c039103942c410049200003c0083c40f20b000c2c4454080c0042c4242e50003520340380140130024080c6d0500100722809002c0140001c0c0e1955140200d604268200e011030a034048001408130032003410070013a2a01812a80c070001030000032005540b942520384800803814103007088040205aa01b000003644410825071340d4690070f99800120301c0c01c001d00c0e81c10007054241900e10035214140c0c503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 887711178 1250 887709928 887709937
    0x1020a060f0b031e061b0703030f0e030f09040f020a020a080a020c10030f060b0f07020d06140c040f060e06091e040c0905030106051228050304091a0d020108011208040801060b 77
    0x100c217903515602c0701c0c030700030006180f583e02c25000080d00b080b4100020748030354062048100c9580000034685038003d00e0300c0c25503014540c9001c030380320702060100a500c2c1031310640590420b510021454403803e41e0010317407104030f5000050440a4042000c54109009000c0d903004c94500034051480f202d042800600100907089075460a240741a2000c0380c1c00d001c40e02100c0303d04186021960800d030840d403c10505171320283c0304036903003500d4502e850044c00c0c0940a80340126041031a458071356060001d19035068030035901100030070034000c04202c8030b80c640344200c960460702a0b814601d04006840c101d0b000c18070801c80c0039081498103404160032640003101c00e0039154114024084969990b041000b0b41030020400350a80d00540c0215610361115030031000786074168124081c000c1001d8503403a0540d0000d41c00481e185880c0c6003006110819040340d151850004c07500021082010b40000380100f40501548404000004d0b0340410f200c90780c8292801441080020b00600f40c81c0e203104442a0007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 887712428 1250 887711178 887711233
    0x6040608071e050f07050708030415021b060306090402060702130507020d080f0a0c0c0804030c0f0b03131101050c0a110a050907021f38040b01020a060f0b03 69
    0x80d03445034045007105104505601c1842c6546150a003c880c000200e12644003103000ca03603500c1201000a88440140003602c01000da00313003509181c10300c41074003a00f404c0780710700303014003959840700d41808507640d400603250840300c01e03100b89089030b50b140302049040c8107201d0b01950180203058480f003081416001a0b116000c02c0e82551410f6514041c16034148000f62004070310402800006580480562701c00d69440c40c1a2034001c0d84c1d0315a907294102107501a0b002a588070b05e0b083d005102070f0058a880b08020b10b206150302c0e01e145040c030f02c081d9a40040c075100802d9043c1c0300708241040e81c810001e4820040408040e43c2102110345489d0505c0d641011405000f15103054002500e85080908103210340030340d802502070f4040198481503c100c1103010400701c50343d42d00c142400c3e0346044000581407081903400b448401002081c9441d0004006203440c41507050a80840080c1d03400315045602c258000000300340003803024503881c050034100403003e0305841110710303008110394911181c042d54403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 887713678 1250 887712428 887712437
    0x3040c03020f1e04020904060f03050a061503080d090206090a0f0509060d080313050307060f020a02011b092c04050312070806150705070e0916050a050d03120b0604060807 75
    0x20150020300107102c4100b4511100d9598004043c2c0d41424550024065100028800034180d52110b0401c00e070500700746c009460b141d00601100d0100314907842012740248100b0401d2020034950341d00d0600d02d02c90910303c9068207031038911240444d1281025191300b8440200805281c94940c0e0201509400764030519205042c404049010360501c04d0441c12982d411a2540b40f5580d02c0c1c00150b00d414004e50003c45552008018140100d056445454004a910a00136a464500e10340003400e46454410710001040100800320f50300b6008003040c0100c840c000303501c150304a0480084491080041100c0100d00201e500b0881045800700c002e01899811140094090b15001d5085405080171140d1940113940c0c60542d07540b0740c03c0e2101400c0d515203d64215900d4507160b20400c03800d0700040d1046182070380011880d03482c8201844c1550040c10081c0c0d1a0104c8a250400040001d40035800241c20b1248002492003880940c1d00302c0030f142500a006981d403280e444000030b0403000120341580006 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 887714928 1250 887713678 887713699
    0x602010f060f0e13210905100e06041703070c0f15050c03070624272f0403080301030f1104050709140a08010504050313150914011403040c0302 63
    0x101402c1c010082039803d1440e500d1110342d510b014040b110104004240c510a04440d00070703c01c2400003100c40729440b0b10740d8400b06894a0300c02400030a03003503020800e040c00055482c0444d961500010764080750350400403c050003820046035419071081c040050500c803100301c004541807180044100483c0e264104a00026035452411140342c0103030341410400c0e41003000b40d8404100c16400c64041032140408061000900c0300c884600807000d0380c40b90201c41e803040e603860308032140145401005041040107000d2004041001c51100085400040c0011440c1c0c2d0303450403416600c0c09441c01b956006001030791b607503103d0406a004416240703045070180381c0c1c080b00a02034103040c09428020b0500d6280d881905040c90960340c05172046001440d00f00700c2500001480369001d00455014600031009156039082038461840700d59816000b88243c009103038441401598020208021110b858146021320701651004035030b00c45900c10800703800d01d0044141700034400c0e050b1402c2c003100e100b00e6078070080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 887716178 1250 887714928 887714939
    0xe010b0c10020d02040b120603010f0e0a0b041707060b210a1104020c0a061b08040201141303060c261509090c03010207120e0307050d200306010602010f06 68
    0x118480d041500300d268001e21228040388040e03802808031039203854405070929440e0500b103a40c9401c40010041e640d00780f4028400f59040a20a65000110f0082c081c020f500d017400601d03030348450302c3c0b01c014002501800000d0a03c8841054552507a0701d030b200d50360341c44009042500c040c050f0804141c2c4030f2030340c4403079421103120b4964624a01c29055406041e60340c049032241e41441c0301c8454110341160b000c10400fa88080f06000c1211072600c54140000c4000b8072540607801003030b0101c00d10060122a50038000543e810107007201a510002c102039a4500c480100700000015503400201501c0c1000d070f07d548015000404184180307021480407051900b0f0480142d4006425120034281c2068015130b1189403d040b980703241d1182200040300c0448610002182c22a40700000542c0e00440104600d91003580c0312250b1186008110001d1401c00e08000024202401444000740a840d214082c0d12020a10102c8000c1405005003522260f40c1d4034034011340070705043d01c4401707512481c262010a8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 887717428 1250 887716178 887716199
    0x90b0403020a06050c010b060d06030b0c0403080f0c030c011d060a290f030708030406080f01031203050406090f080408010e151506070f08190e01142a0102040e01 71
    0x3140c0c0c0041c92016003601c0c02030140c841d0350020f011003000b5501c403d900501c41d281d0100410548a44071400543c0c00d2840c240a007500901a10300458680100401c0021960140a0303c0400c07aa00c111070303554001e802d00d490300e1882030b10080c9445500f0011080500ca00c201d445c450982c4d112000c3e20401c0d80e401c0916800c8680c41c9101c002411195081481281e1030039102d007110182c0076000c4c00200341e81d580000c1c50a01994000704840d84002020700460b94010441130300812003101000e003d50440c0c0d1144905104950040c080540d140700290600190350010070304140c002410325146003aa04219045900c10300449500d0341c2055414950504006810804c180130072a400b4000d0301c4051410b2203902c50311303100300e43c0540700784002c101240000107808200c0d0300c00d601190352440103482400702049100c072a0414410820702c0000240d03001107007180c40d4103181c580c041d40c8102c01a01030280d00880e188015510400e0300305584203010550007801594407017109852141e9a0300400b22 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 887718678 1250 887717428 887717437
    0x219060c030c08090706033b1908031302040605040207150b0105040f030209070c1b0501021c080f09120d0e06090610061805061917070c150b040e0d090b 67
    0x150320340d010170030811a5610a6015400e1020f030700380e64000b40c2070100d040a00c00b00e0110304c0d8044e9080d400b4031741d02845004124a0030340103401214218540ca190306c500c5901c0c00014807100400d8003501c41001156070f82d07484480030b414020310840d2141c07141d01b40341403415080345651048903e400c0c00303070b2079039801203050f201180d68030045014014190307030a101c1c2810b400b403c0c50080c8268031021200140c1552209024201408120903201f4a0500028604161600b909003085800c074400c0c0b00c1035038000162540074540502e60040b03038840b010001e00d0140c2305880707103c08540c04952510f41c90641c2e08424200319000b411035109481e00d030852902c4100c00d0b20024034900c9050020000b0794025803400d004200002501c010165548000c00c200d0340c031a0051840441c20181c3c65103419800682c012640180344060401c10300e0b191201410700004168007800d05000342e1810341d44018181c0029042a0b00640103003c02402e101881c4d65030302020040c00081360701c0c03040100703004202e2002d98 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 887719928 1250 887718678 887718691
    0x9160608040c1703160f08120f100303090506070f0b0106170903040b041502010603061d0114060604090f0222031403030403080c070f0209041401060506190e010219060c030c08 77
    0x841ca058030a00007007485c0629620125407444400200301d0104880c000508070344990000d00300550314000381840e0460100a240c191303003901340c031014000300b0f030712010150035160203686150b075070801420314441917007800000628003851140042140365001c07036001d10480f00c51f9005d1584e40c440f140203580340d00a0b40600c12281c42d0034401005411081c040c0d82002a0311400005403540d282d8031000103482c04030005c880c44500e04015070541e40d40c00d00c030302099641001c400308031078109200010030500c218403600c44442d81301c0004009050055044513880d00c082100001850b0300c4000321004940f10b44000d0341c01c071814210540450001104891055a16945d040103e5449001030540c9030400d5070b064401c40280007452005072110034010707026074061020384e040008040201e90a64060b9044a8090141400003100c0581d9091082e06603000e5410710318148010b07200100e14040e460301000c040b0740309000302c0328240142944982000301d030580e0180000d50b036030001565492000d907801f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 887721178 1250 887719928 887719933
    0x1c050942090402130e07020102250c0312020321090f0601030f030315081009020f0301090f06091a16080703020a0503040b09030910050d0c090b0f0309160608040c17 72
    0xa500072480c05500410000360b03407400680c440f80d240c035456855488200e0f142400340c1c3d0700080d01460b40e1170850490404548a40302c0c202d03800f481d07540b6400d04100602c0010051501500c00e03130150360003070017a192000038802c00140d40842d0f041085880490076210840b43d03000790f1340780b0800c103440450145c4c10399410039404c0c548000345980c200c004004042e265100180e10032070214611505008144407009a040b0104400d040f80c010042e041c4072446a09100780e240c8120000042c40b0624140c00c1c0581041001800e0342c424185000c41085a80e80c04200c1c1000504114410011551134038442c84181c0d107420090390b400d0001c0c0d080384036140200011880520000d0002400108016408000002502d08140d20480844c1c00c2405c100f49100104002145400d01c003200d601c104584029540303030903a201860130010804030f00c6595078040025000000145000004001c00c0030301c102c140381600c00043e0b96490003031458005603801c40d00d23008020f10000d000c1d14540c190f4116400410003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 887722428 1250 887721178 887721187
    0xa05060a080f06150d0515040507020d030f02070b0106080a0e070e1614030c0913050c031f050603160809012a14041d181c050942 57
    0x16414004401020103130300c00030540c000c01485401201402c65940b024001185505150349410200c100c0480583d020b145003102300721000b5400256207450302d800e410f002070740048ad089524007a11944002622000001c00005501980b0140d26440303004000001c000a0304411509a210f006520804400034050b401040706404030140390000051241801c041e00e1319644040545600201c4415441d940007140723000c4e10b428000c25541080d00455004c00852400d1003003c80c0c81d00015050102a2581800040c2e851140c0c0074490040e200041500c3c1c0c071b0749006208000015812006440002c1081020881400050280401001e81c104901c0d00e2141004084513a8040d07405101f400c0151561130140c0d4414403400510260040c40490040c01850f82082c1c029140c000d0a80301d4081f8140c905071000210100c0c44e070b4108440c05000e541e1240000a0071141c5008600320940c1c0404000e80344021907622444070148100311090300c582072060701c580003005c1d2a07100c4410360046d00401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 887723678 1250 887722428 887722441
    0x9280314010e0d210e0a030e15070b150906010804080c010204090906140c07030c080913020c0f070f0b07060c11100b03070e09030d0f1803020604020a05060a08 70
    0xa0803006105a40001495241c00a0101c1c90841845080c00104071460010301c106524100c0080081c0c01442042c800441c6507540e482e980c0b50070444c0901000450203003031a066807180c50580703282d0407281c0300d0f58031004c01c2d081852407000160742040500403c1c409280c51410806050b6103d82070584450500d82c1c0c032a00c840940d64005c003400359140d582000f01058132100c512500f10000d0140100148000900d0010142c01001820641522409018020000e60701c92103441c40e80d5444580a074680600ca0003180d01441340304111004a80046484080000001440c21005142c00100ca1041d640c5038182000407615003e942124001000420041142904174182110186c50024151341009a44504140301c034052031501325128101e01402e440d0410094000d4a80d8089602003810900c425a03942c1c803621402e452000e484041e440c140107003d901605805221102d0f007030b640011881d00035103410003182c049104040319076020401e400c101e8152003810070a03403941d855039128403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 887724928 1250 887723678 887723693
    0x804030e03010605030703080408060c09130f06150c20030a0b2e061e090608070c080f13080118140309041d0f0109020f040f0f05040305092803 63
    0xc00885405649a8000040c1914100305032802907010b2507905440f1418201200c0c10040b0103049840606014031180c2e8035036030340d005108035400480400046180c400c000d14800b40c07009a2140d0107502045003c2c80440740c200c0c103072288840c440e8180040f444035003a0454442480070348056013541c0005520800a103e89020790307044800001801100701502003070301807140d05920000c90036180d07107408200f2543c00210201103460803e40740300350445160740040280c003044c030030882001090000b280100f8000e580001800e50031481c1c2640c0d03012220640d41055102048803021440340c48400919041d0602c03411000341c543c0d02a10404024944a01c03007118078150300440d25010401c0902e000740e80d00d210308800503030201d02034401000941030150500d0041015404103904002000700165211080031b042c1500c00c40d0300180000f00004200010080c15001d9840280b07044203200606400c0806840382c100100c410000d50301c42112104540c0c1140041640000c032a4142800001c910 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 887726178 1250 887724928 887724947
    0xd05070503040807260d0203031b120a020901410408010e1605010806091f03050a05070e010b070b041211031b0c03070f0b0f12011e0e07080403 63
    0x2440c01c881c106512080303071a0402d103195020704803420714504540c1400c04030001d21202ea010690240029112041740070307459100080ca582c40a1b0141078885200d0000441030310060015854202c0c5c075032510307441d0b0100944c00881c580b400328400a80506902ca004c514204510100750a12072403044600c0d00d455058860641c01c5500703c00034440401c03103031400d201e120140a58640100b000000340e405820308984640c00090401000b4070401c000e40d103511000e9a00542a00000020980c00c80d00e80e100c800115003004045000d808804000e00c4000123a18058036021a00915103981c0c0700100c006611420768020b000903038000004002c41c0900300d0b4807a956076142829078aa00c2c107610030750704590103600c0f0701030096070148210030010420400f900307200c0d0042d801806810705101c14910075100c1071140c20105407002401203050314185003a11682030b00400000e14658448141e150711181c84924551080e0074808000b0300400511500c900814003500c0d441680e883d0f686045803013030350 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 887727428 1250 887726178 887726183
    0x1509020c030f03040c030b101d060102160801051005031912020703060905030316050c07120c030f03082202180a1401060f0e27040606030c06030e011d0d0507 69
    0xa20541070102c1201005600c640e2180061002450031132905c590400005040d0348104000c40782c05010402860000c43c0310340d810710701865019034880004070318000d10103d1840345000303041000248040c0542109000301410241000e0203622002403542d100002c05c1c0a030941c81450f0110130208180030440009441240305442905859480e510242c0706062001c03256644000200989070000a030000804c072000d113000b03850403806038500e070f540710b20b203004000711301c98400807030f1080000c20715411004540c071041101c0044002d08000c1e00c4c0c24002c5500022800c0180503441d9010804203500c04000d9008081071140c2844600740e038200721000341381140c400d0307684814007004c12003a40d55030b0081c4001c0c0c1d04c0c2c40c00340500034001041409510031040c02240711010011410600d08492200c02900b4001c000b050303502c5080c854050441540050031a480901c1c01188242e4075800c0000c0002c0c2c240300034403441110210441c2e480d40012101c0f000750700704050010030940710b01d004001260 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 887728678 1250 887727428 887727433
    0xc030c0812010f03033b010509180f09160e0a150305011505090112020d051c1805270702030d0213090b0618010c0f060e0c03060a1509020c 61
    0x10880d030341c031103005182a0802d00030100040d40030410540c1c00684100c0000c2240200340f220390803404a6500700c0c501c84103030781c500b5003001d501c06040d0348181c00341c40c8000e200820807043d1009481040800385010b40b50740010001000000e8804800096181d09088000d00070220700c3d07261061280420601400100502e40c0b01c109840481e084400100040d6005200000b0070145c100c0703030f105c21104640c2c00b040c080c80f4901e0042160b540301c001c54441140d0155030785d0348020170350f03d045401d0101600444030a003028241d00c0c44050b81c4641c3c06500c11544039040e0f6952038940b01004080c0120045140407040c0045002150503004c2d1982e41c1c1089040c0120f81c2072440c0790094100340c1e0004401c00464140d4142d080011080602034041d01003025180103103010455007019602a28094695050100c00110700c41005210000c403854503070054010005846a5108240c0300c0c0c1c814294580700388591300109503810380d1071040d00000f9605641c1ca1560a18041300c2d0300280d003003500020504e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 887729928 1250 887728678 887728687
    0xd1506020a0b0403110f1f0603230c0607080d11071110090b0d051012030f030b06041a030a050702011a09060a030b07180e0402060304110f040204140f100c030c08 71
    0x3c0001b044174407584502c200241980d522800101200090a0f000b8286454203001c410004540014a940003481b044003044403003001f00040f8510f05800ca42d0fa0942007031f00001e01078140071081c8042c0c0001ca4004005100d200605144440039020701c0d90080c0c0847c0d405580c10a00c1d00d800c0d10101821001400d01d00f607020390b01d91820020390420282c00c072046450380c08210500141540310400b1748150b12150072074001c180c400404008125002c18181991101c9900341c50ba22401a28000c109080b83c0100c2c00b0150022060b96820a4800d01005820440130459041c01070003502240004000b50407541a466030810200000c054801c82d08005003031400b001240b2400340c0c451044549403a940328051800e200d928040e0f900350300c48050070600703205002c01a5500d40c226078205030003e24035041c10b450000015150480c02c44015440303480058005252510a01c0700e1520b14012101c2c0c0600906440078003ca4140060500700003a8624102000103801a1203410301e50380110840c5040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 887731178 1250 887729928 887729957
    0x40e06040209130e0a032706080c130303050403030f0e10050a03110a08010602101e0906020d05091b090f010302091906060905100314010308090310110d1506020a0b0403 74
    0x1100c444e03030840103042e000311034107006143c0c2000c9441031002800c603116460f0f243e030600000000f013a60265801700300f410004590500308810548641b03000c40e850b400285a50ba2901400c1980603110880c04126104a4081c00074003440038403501c440060074290200101c0041110a540102c0c0360506059807040141000301d00080508460180f07929014440d504180e00130346007040006110804c00d003083d1524040e2525402030b81d01c5040821804140c040a500c0c1c0f05019014280345846070074902010084c0d4204001204484059503683d14180035801005012841000300e4501c0c0c2c100c0c50400041005040c03d50100b070340002625a480b070503d440c500e5070410794001e03078010f000150010000b4051407070440c00d18007a649540c1010004140c900760811842281440040c08590b00407402440d40c0e1001d01145440b26030403041004584605801c681480d0004984403160030b00c0c0c55500030307105408042901c1034580d503070010412501c8555802e107000000030401c400300101c54504040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 887732428 1250 887731178 887731181
    0x60b0306180a0f050423030a020a0b040c05090a0b09071403150a05031005041203060302011b150204080604120f201504050f010e010b06070201031a03160614040e0604020913 76
    0x103144501000c3e00615030090306c6006402e46003e0f2140c040d001001400c031150780002d6001c0c00580c3c0700c04034620540d11402c5c00c604001c4070f6400542c000100b4010801d13241c2e110f03400800d00000c11100c01201c0d0700c2d0600100e81a4031740c0500d407001e08200b003000c140000d00000c1d0b40581c3c1e00000700030f801c0c19911386020034100300c0030785045901c503900c80040c081008034416900446401c1894208680d51560700020408840c3c0c1c60944044038402e1002801d00c80c00c03003081420380b0003d40c0c0c15583e50b40d6a01c001503464000300d03401c2c0c901c141c2e1184140386041c070a101c100e0300303404150f49802c80148100c8481000e0303418124100124451300c80711000030781003a00b656201d07900540207000722050504486003540c12501c01540c43d030741342005440c403a85c0c6004c00e694440390203290005030f039543d40c5444800f945c40707851550f40c1845102c880980c2c4040c4a0060700030341e003940d44c80c9044210880000301041c00b0301d0007400480c0400200003040303070a05a000c0c01c12500c000b051100c4440f00c2802003030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 887733678 1250 887732428 887732431
    0x9230a0602150106030209150715020a0c0c08030c0d08100f0308030a0510061b0204090c0b0318010209090408180a0b13060203070506040b0414120706060b0306180a0f05 74
    0x100560016031040300ba501650000a005201908066290808610003d500c2c2140014255044140440c0300e0051152095150114252100003155560420100078000d841c5980c021100a0720f00c02021607620382c088191854410080c0007040b1070760f031010341501d100e140142403400342e40b590000050035401c80c01a8000541c081d0050540c0d03820540220815204001c107148034071018040c04009255000180c580c031460901040c5c0d00d075601500c0000c001d403016001c050f001807229000400c070401a0002180640100c00c214000c02d08054a502c1c02d0340151780e1200d500618000006000c42e09000c000c0c00210700c4a030380d1000040c41900001c1c52061240c0101a85203804503010540b0b40c0b030300e1640030240c00c19000440c140503082d0b0703513681d44540042c0001c0a08010801040070448503a03106144d1803281c000351201d110001014820039000705805480381400c10380001001c44402040fa80101c80140c2050140794407614042c542d0500500081b000329900c070080451001a440f806 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 887734928 1250 887733678 887733689
    0x7030b19090c030e030a0206060402030730051e0105060d02040321110c060322050a1101020c0103050403020c101413050312030c03180a0f060c08100609230a 69
    0x15907241d080d000102140c0d1314003c0b540155004110301c1910070303000620164042411200541c2e04c1d903648604075030382845964001e03030303694103014030001a030a0381c0c144c2c0c40541c3d00e0b13040400040d0303600c45403010405030788920101100c0844006002604062005022501059002516043da680e5480300700c1c1406400741d006c5040001c0340c804403260702405066000c02d44c1d9004041e80c1400000040540c800500105e0350301200c909034210109170028402580c0d6005000c0e07a044036a2400c0501e203c1680d01d42003801030045560002e03081d8000c2c0310b805d00944d0154006c19240d25014103001e49203000c01002424000031000040d8541c00c1e100051207480d142c1130b4580d040c245840e042c907281c444201c90250788041d081c000c0103402e0a8400c1a2544440c0c0c41c04c1c4103043c0121840c15031306000c0c42354406444050317540300100c24000e680d0000d0800214075a21100305507240700c00c41074401c849006000009203a20300421100381801a070103404075642e941d4001c0e0248020010b2240b48660740030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 887736178 1250 887734928 887734931
    0x904021c031b0f05061f091505030d0c03030608070b070b060103060f0810290d03031103010e010e060306010b090f0a080304032303160b19061e0503030f0307030b1909 73
    0x1e00c0404c1428028160006005d403c00c1c2552810b413409190b1006150103084801a6202c90007030000c80c48548201c01480080e043e181c845c0c144500050490503d0344007640441c0c208013000400d040001015411604601c5003a8140321782c4e6a10b900e484900a4102810035480394000304240f00301400580080c50312100a207580f00b0700100d104103407009403240015442c41d080480b11500e80350a03040c009000111100c0d6080003c81c50b00b41c00405080c500140a00700c00f0001103544040040840c1c140c92050b50180d40a03900e8404055544c8001d00680415220610020b185401c3c02030101403802d60042294080c15240c0010a145401580c01541c1c00c40940c8a07c680c1c1700000920540c0700040c3e68003461621311041e83c0c0113150604e640c401070001350310030300003080b4508000040000b1191110148a185d0713540c1d04209141103074004048a03001d00c02c00c001b03002d250010403a11030403000303030b0414116035a66070154010080042c015400c010400700d0350941204520344000503081e032120 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 887737428 1250 887736178 887736203
    0x60d03180b030601110c0d02090402032a0a090c140d09060f020d0b0102070b0a050f04092405010c1a060307030206072009061f030e010e0304140904021c031b 69
    0x14604100081c00504c41d4102404c1b0341101e448520500722903d8055070b201116841e54400f1a1030b140c0d40407803410303202c40c292a501444405060340314084c00800c58a20b440f40b41c03121003007800c5a400883d400f000c24001484d00c0b400020b0040500300b80141118002281c0030745854034001c0d1501c010b00802e50650005100b00c501c015031141e07a514031000c0c030041c0300300c0e4103062400040b803140450902c18494086800031001c0180812a0081c0038030080a01c0820b001c0c0d4100e049884400070003404501540802151a52013000c020703000a8005021034102410903a158844142c080c040710740500801d40302101503120000100151442404034483d80c0245512080c06d42c0700300c40e81503120305500414850f0300c1d62050300344507401d10b03da044800200c0c060070098000f803108030012461942403801001001c0008406017049407070410340442000c0b0280100241c41310700316002540f10a00352006c0483d00b03406184185103074860700304811650403105c2e00c03208000a00004865109410380d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 887738678 1250 887737428 887737441
    0x4110a02030d050c030106090e10170309091612090c03020301061d06010903111e0907090906050a0b07140703060207080406120b0a050d0503160503040e01150206060d03180b03 77
    0x40b0b00c13030307011341d03010545411541000b0005108043ca4414428000742460100340f815003010822002004c58408240e04ca0300b024154a40303d03003007080d07901c1c451101d600c0020995400c900800c0208402c0351343d28116050200c101300002d000e5940296085160b8100100068400344038500241801d945001815520740e507400300c5401c0010062810014801c0c400c20000c2c6843c07914100540040760ba00300c8802801400f0078114020031138990b40554440144002d06401071146000d55138003100038401c103501c42c03050202c150007600c194146d03002c0404c5038102094564140c40a841c14039000e450300f841e980c2c0c40300300a80c0c02c00001542c1c02c14000400300181600800b45960440602c0350a005c240c00307030703030009102829510a40303000c3c54208901c2070401c0740910403155213800f014000c064188803410a5a5a80c001c0d004246401515100100c0e0340f00c9090810102100f407680202040d40c0e81e81c0610142c050b06440403001c2c07220700d804000f079541402d84200088c0c0300c0f499856071a8544a03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 887739928 1250 887738678 887738681
    0x62b0506010e01080706090e0f040510110a0f020f120a050f0d0f06050102210d0209031506090601052b090f060e0d0e030a0206030705090a14031203150f04110a02030d 73
    0x3c0d1b005100384071001c8805c10007421003a1260380d0041d41142c0c88441075459042c0141000c0744030320365049451600010340d443d000c2e030401030328040c010741d582c50107007040002c0140c0c1e8594000d02c042040307500c000000d803401d0031403100401d0012010310f802c9081c5110540160b05a07000171510000c55034072500c2ea9400000c9030710803000200000d200800a40c003460200703150208040d0300d0400f00800004011551840c0340c5c04403120300b00040c0841e000c0501d01030003030303c0310702d016a01207111720701000200320f096100700280c1c0c240b425201450790540f16900361008450070f00081d40d00c48681c407a6a21004529151080c00000d0300a20300842da1184011100e8242000b1001400c10b01291102908680c2c40000b9000c441d030b941a1903841d620340f40c0329010b580703902503184403c0c0d00031401c10700481d1010500c1000c015941064007200c0c886414003140c04a180030807100a014954403049500c898a0701c651940e20010011f0300008002d41c1c29001c55031f03107901007076403c405030b072001403403800c04800d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 887741178 1250 887739928 887739943
    0x7090c0504060503070f0e030703210e060a0e04090f06020c0f1209040504060f1e230f04111e0108010503030a08060607030509031006150206062b0506010e0108 70
    0x85190403450503003800c8024160380005070804007003041361002c00281c140a16244581c0400082c100c1d07802c60340c1ca14120310300b02c540040030440c0d5451952001610742c080c0c05401000301c401032580741040ba0200e02100c08400720000e16502c545ca800020010071600c031001079546014050140c1d036403070000d190ba440e015100b4a01c0d80564012151008004440000d13107200c0c1008444c0851039480d203042000261040c181518041883c002110914103811014108424440c4c1c038240000505d49031441e210454610504500713480071400903200e01619407900c0c2d401803003021443c1d95030800202040d0003c2c24000c0416040c2d070080000300b001e40e0011085401040700b24019484d104200e40c00500e09640600880e000304400305010040501850a50b404d036031010b400c4074484043c550002c400740425101e801743c5603d10321000c2c0032043c40815944d2141c40054502c03000c200305401c070040c21503e00420504a501549a00d000041003880103a00900e4a4451075515504124a80d07042030750 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 887742428 1250 887741178 887741201
    0x2802010206070c0b0c0c10020d0b0312070c14130c0e030c030303190507050403140102070b0606031303050c011113030506010501110709020d020715090b011e170304030506090709 78
    0x500c40f00c00f07002030706012007950300840c20250141c03034448900c4080d140804540e601c641081c0082041c103a90b101035808031940813821001c5401e4030040d500d8884880c42035000140c00220301c1e81080c44604c08c4804500354250300a00300403003801005c22440d003110a13140d00000001d61810899946203010800341c0944002240074510718180340138010303203600b641040088802e031214001100c00c0d0042d01514000c1d03820000401800b0120340050303000354410782c0115140c2000f100030400d2401c2c04800d4a108201040510400721b00b10f80b001c0d04d81c2c2c0c1005c40c440410b507413140000c4144080d44400fa2039004042c900c4400014114a00242800c0d0160042030400050340c40310400a0b43c00140c0004449012000582d103564042c0000080d225140c8003030800c0c801c4a0400218511036480f80072902e02911242031a40d8841180034043d151503014546000d4141006101d112449072011842c000f41d841181d2805660340c1d6018201041148d00c039441c0c4d001600c003000b64001d40e0103111010407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 887743678 1250 887742428 887742437
    0xf020a020615010e03060c072f040f0222031203090b010303030b0609060301180b1009061206031a0108010c170711250f0504021317280201020607 64
    0x5505100035924900101842082c0349160b18400b043d90265484c50000d20014007a20b0781441e100c1000320b500c2d03000d11800c440001043c4025128200c01385400c04d41c0ca03900d0301c840c1d00003204420401c00a403152440009400768204500051054a4107240780e0540308a15041e01743e9103141090100c604070300f0402014182405592400030f0070390800281075950506000681020100101d070082c02200903150304010000008102440c9401c1d03a840304202501003032089111403018407a00c112403a50500c0800c1c048a0184402d9009402084100000050028500780e03280c8401c01c103034101d0407214801c8038609006000c992028090090100c0450804402800c181402c2c0500901b0003802d0b24104181c521069041000503c10400d1154003610440e00c0080401d03000d101880c264800c1c042d044135083d500003040c2c03c041c026541a50420210481240c0c50401010000d5540c0940b00802c1e0040000c0784107080307181c220200d00340082c0c5c4512400204603100191805402a00700300034070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 887744928 1250 887743678 887743687
    0xe13020306010807060504050603091c0518010e030714120a0c1a0702060a2601060f09091a06210f0703110306030d140d0e030327030d0902010c0f0c03060f02 69
    0x15008000c0f102103030809d984080c1e03650b848007061420f00c059030f0780000c9002000d0030040c00d001e51100252580a004c46d41ca4000303007d410f4011340d910007001c1002ca4040c0c1003403008006c02d00000c01401c0817450083c201141100344800954100072164400b10340d02e070700c401e4040c0030391034140c480201c00302540c2855600d451202d4002030418007841c4480404c0102540c0000d1801803a500d06170a11084141030f2142941c50700e50150400042d480b000d00002c14510700010000314a004e070310320780b54100707041100c400300c00f5041c4482030f4450303440361285a40071400c2c0d00351010b4032003202780b080c0e0007075080003081d05003484003c0a4610f010202030303881a090080c0181c659022a4069a0000906020389400b0301d82607480c0490142020540c0240d10b00103a4040148001c8004d40c800c504c0714261208414004212043c1030542803812041079009008005502400c1d51101e100036005041c10005031089507100072801c41d1114040311b51001c1d0302c90030010001c030790041407840d10ba45075041d07082 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 887746178 1250 887744928 887744939
    0x60b0d0510050603090712060f0504060e06090a0b0f040807080406030c03050c180d0606091109030d020102070507140604150c02040f0b01051210090608030c070614030a020309070e13020306010807 86
    0x310740300c0d4052840c0010300c7c0251101000003e0340300a0001d10f069006206507d068140040108121400980940a4480002e01c50000440c2e03403007026900107801070312619511500501c1e0783c0f004000b22001d0308200140d0011491f1000a80010061641d0200d09441c0c15080282591f8010b400040784507c180071044500d51142040c081c03003070703081c0d446010407807407410007101401c1590f0025207030501d0000019000e80c401e0004289414058048030311149180c07070224200d115203940607041d0380108a003807081041090796902d0084005019606058681410f01c1d0008401d1741c1e181c01040312040c00e1070850800b4040d80c070501081050404c1400c203118000fa04c0d40c421030403450303041d084110000c0e00302040040c921020f130980402c10440c0d103232100781e2165240d02c40402403a091248080016000c0e1150754241c1c440740c80e1354050790841d142c034103c140c041d4001815424041c000c001003c6903042814107842d00c110180154451444143c2c01071604042c4180c121640039000807105014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 887747428 1250 887746178 887746183
    0x90606091203050c070b1c05100b0405120a06290108070203031303020f0a060b0a0b0301050f04020a110d0207330c0309030b0403080a0c02010c0215060301060b0d051005060309 77
    0x120745415040969480b44c1d40e00c0c1960500d01180c20079402032074007040b00c480c081e826018001d12010110704c1002141c03104014002c41400910490303051000411040c4018101425501039140d60311040300c030b01115031307510385047d01c005110041c204034020b2030140011170804041c051084080c201000342d801e0020000b500c078840100b580303a0021843d840402014400c02142130102c050301c0503940b0200c042d241400103001181c05942c030815000300c001c2100c0b0f00f0441124100d0f02d000f403a06200b0460300c03003800081d420040f074030014080386042000507000c1c14004148000f04550140c020076084c20100c0d0720308051726826400303a10300504840c50324468040c801156085074240040703c0429494111401003847d04010419050390050000305608001c0f2280035880d403010a0040f54030030750781203080314031401800c001a03100d8603d1140c42c0410351401a00202c010f00007103409078903105041041d60010845003840c960311800c0002d1890b405c2d550f040038007000c4403110b1071400c1c00c2d0409035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 887748678 1250 887747428 887747459
    0x3030d020c011505040e2805070b0a0206010609060804030c060b091e070504290c03130518090c010e031c0210050f040b192007060c091a070602160c09060609 69
    0x107203000b45182d540c0907504003800001d92423584401220b01541c0c0700e8000c0d00e0305400c501d4102d0003622070100040b4440d802a640f507801c1e11200d5a9040e65680c541d18101e03174803c200c0f0000d50301c0300e0b65040601c5c03c586034030545910038401c031322241070300c0789100707250a00c8000300502803420004240018042440d1190042d03004118007146205a400d0410202c0c0b000d00c903510841c80c140c800050500c2000c41c6d00030104040314400c40384600a03054546d45142017007400c90700d0300c0d00707500408507a01c40c7c2e6001e01440240b45d0070107822140c00b018111048002c5401c1e0781c1601c001740e4041280c02a5040660244a03401441c07035014220b642042d07551050107000c0900242aa90745030402a6103000c0c407a07016010301e1307030b000c4441203500b00300c801c0908041e84898020b41d96203062505980038140120b60b1032003283c048055000d403103480c1c92580d11481c2c02c40c9108840c110340030032024402040c1c0d01201802d4601840384080311a00e4034603c1c07030413210940e0081c000d00508000422400704000741e1007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 887749928 1250 887748678 887748703
    0x90b090604060e15070b010e09030a09061206050405071d06070210081e0f2508060d060905030409060e090a0b0c18100f02010b03010b060f0903030d020c011505040e 72
    0x24402a892600083e5078a4201c0b48011007130360300031a0311000d1115030112581251101800d9007041e450301e108a50300c900c520075070b40c0d0100b80116000c12080c0d210ba445890351250303484000481544030300005090707a070309071990400a4180d541c40000c9007400d50b071031998140102c0303040e4600015907022681102c10080040180202c000005204000909140d408462400c610f500c081c0b42458602c0c103501401c1d28226074412000b9a0f20000ba03c0780840100d0502c400e0311101501e42d500303420420f01d490303246401ca030020f850f0b1101d8800210b04101a10251a42910105406d420945040040034004181904592040c004d680103e0031414440e500f01c100d00120943d580c004c51110441c141a104800307030404070f00c891101d40c059005445404207100c5034001d010f0800c4910405003079960500c00141d000e2000c200310803d2000382801024103800243c103590400d1000321101c0b0481c0c00500858145944480e410242401e4000004010380800ca804005284c031032500f407960344065001c070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 887751178 1250 887749928 887749937
    0x2010e0c04020a050c060c07060b100e0f0607080309100c020d050d02091f030524010504050409030212070507031104180f021f050d0c08071d061c050601090b09060406 73
    0x14003c06481030045840c0d01146070110750841c2000c010021550344070001c21740b18245014188811780c075065090120713803042640c0b490482407084007001000c41041c849503510800402c240d04c00282608040c7d880341d90703940041c103032440c1000e030144241c032220f140c08000c6420190360900b40a03000f00c20b0304c071030b0603440c60300603140c44d182c1c03010840c0720302400c081d81c02c281d006065400b600c039490b400c002e20407001203405200c07264000d6580701c0b500e45407007905804140c041c001070180b8101743c0c6c007512605000344101c64910a25200303c041303540c415481030390107030000711040c8203003e890080007604190944003001014101070110282e01c14062008040d01c040322a90000c0d07540e03450f0041c0d900c04202000e2080504c0401c0c02502603449500300c02103070707402d041000001c240180001403182400751980c0c44c1038101c400c070368043c010b40003124690189041c09918050403146090801d14022040001070700d0030a14009816a0040d50080c50812010020200980c88907800d550807100181007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 887752428 1250 887751178 887751187
    0x1140a0e0c04021c060b040f0504022208060103050d1407151e0e061302030a08030703110307170901060609150e0607050102031012030504030215070605010f090b0102010e0c0402 78
    0x500341d00708050000070540c0300c0c2c008036150444024083c100c011048040d0010040d0b0b40d42da01c1100400c1c004c522171100c410401c02c01c00c00072810250001c00403000400070803a600740203c503a049090055400404907a80840d00502c10000c0030420040c22a405041034072000c00040e04504092041d104020f1003100c0d20418882c01d43c40c2c603008000b403003501c2c16980c06159140d01a20b40148203800c1c0841c0d083c495030740840d00f4910b640d02d4030094541c02034081c0c00b140d130309610b44542903400a0a01020907946401450045540c0b4000d18001c1950743c0d1241c00c4803481e16200301002030017810002440e450050104506134014030764004452000300d919480d075460500a030350000802d125103800c4080081c520301080819402140b00b1019201d10385040d40d00d400b5501013030f041c1d080e001004070b5010042400540f40a0070b45d5201e154101701c0807440c0250581d5007606132242a80001c0d40940200ca00b0301981d90b8078003848150000c01c0c40200300342d021941800c1d03902c254030700315240140d80c0000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 887753678 1250 887752428 887752451
    0x90201120e25290c0f06100501170109050415050c0a0306062120030a0b010f050717090f030d03050a0b0f0d06051b040324020309031e0903070807150201140a 69
    0xc00f81c40d0f01d005041305851403900c0c21200151900700454a05400c0f40c0c41c000c0120b103540c00307035046080000807a010420366a080041d98001044007400c10342d554545252403484400803070142d18807500080001790b07240e410800010301950314580041c4188407401c00800601a942c40509418822106011a40000d102600801400e00030314070a0501000410030512032440d070040e10303801100703a80d089211580d80300201c1d454010524010040310382c0110301201000010b000e05480c0e0002031030103800c41100d0000074035000480c450100172a880702c0800800300d01c42d109680340b101c0259003207240d002d820000a42c00790500751008100340d80d0350000c50640c0e210602c0701c1d04030b8500e1030b60080e5a16240d041007641a0360060381c0380b00010050314540c1d0944482d00a80703000f4400e1030021400c201c0f041e440f001181c000107421601489061040300e4a560b800c10200b0000e08802001d0200181801c08080050407400c040d1419a814903280c6a00d000404946c15409004c0361000543e044610 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 887754928 1250 887753678 887753759
    0x18081b060c03031b0c12031b250611070b100e010b0a2015010e0c04180b0103111314030f1510080109061a03070513090201120e25 57
    0x5511000588142c00b0f82000748901c0f40019809083c80840b00d104036081d071234056400340706010004030110801c01503201c60390002e8441402c141c5c81400c0c00b24032100300d840b100c1d07030a0700007540565006050205000f98550080c0303818005d4540100107800b95810700310b0007151807080d04006820003c00d03400c01c407400c0110012540c90042a40151028030100000000c1082401c1c040c9981000305a0302050102e82c2c0f18007110200d8a00e401c2c0b602410b2542c00099000b0706080d4446410700d03848a034545080d0f031448006200c40b0030150284401d2504080e282d440400c40c03c40040c1c000e51200ca0b0103025074100103180603481040000c4038801c0c0e690200b030702e10300201e941e0101c1c06540c00c02000d1f804200c40d0b90800c4080c0055503610007500d0040804150381c401c040c0c400c1c141c10205949124200040c1a000306207594010704000704091403005c01c07402112540b89110a00d500301040c0103c0c0781d500c7d02915500a5008401451014100040404100c11080b240c07060050040703121000503d00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 887756178 1250 887754928 887754937
    0x4090308010b0f13080a03120509191a070203040f05010219020f1503040503090906010804030c030815180105030610080c1c0b040302071a2818081b060c03031b 70
    0x100313180050250b541c401c1e42d90383c86281a00310003252140403115510122445264420080e039002410040e2204005500f400403044059031001e42c10610040c101e14010710030f9008a03250350045595601d000e0121322604590b421190441d0840040034150303075551310501e05e040d03030112007400c0c0c000c880100107484100701d0724a2540024000c020081404000300180c82c4503101941c0c156015514800111221b0204540040100310030070714a10109114601c900d903c0340c60082094a08503003100012810103a00540035034008500d0014001800e00b80140381c3c2101034480410301e254181540c42e80c440c0943c5140c1d0b40500111210036444070765800510542940100e10b12085e0f0400d820001d4440001c0d00404075240207100f0140c000c4416941100e07848141c00d0100507001c0c102040d1102c0d40c41c4c0c071341a050f04004a00c002c01c441c011510000000030849280140300207950024040f00c3c0011080380315200d09001d0240c001100c0020041700c0d88040340e0440c2c402d881c14141040f4469005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 887757428 1250 887756178 887756197
    0x607050601060c050601090203090607030c09080a0b011410140a020712060c020c060310060324060206150a14240309030406080a05010510230f0301031104090308010b0f 74
    0x401000050710b03070f0042c01e5006000d0168099400582c0c8594400007644000d031800d195a601440c00118901c2c4070368840c024440145c13401031503140d502c0781414540941c000040d10710071855801048070b10281c7c80d04c00c10140007035800742264084106c001c3e1035004500c0001403d802c0c006100800144280102c070302030001c03400817400841c5941407040045c000140c8090240c032484040340d1091418a041c3c0b4481d4483c100ba9500a17420004210701800c07444040762940c003072134880105c070b04802207810f80103005c4c1940200000e203000e10481e031782c101d22000c017203001d004070401c1404180350840340c1c00039100090300c02c060102d02e120310001d201980310601c6065400c0c08018802b480c030020005104540082d550310400d516400b0707446048034404e100381580004060b1070f841000b400786560005c60094581142c0f07018000c00b02c44020707a4030005501222120001c01482008a1640300400103401581c0c1000188010795000d80307415418001c51841c0d140100304a94613910708012544001d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 887758678 1250 887757428 887757433
    0xd020f1020390d061e050c0306190b16020307330c1b08010b011106130203030d050a060501080a021306031503021f0e030a110409021318030306140f040b060705 70
    0x43e01e5080001c01842882d40180d41045002000304041c402c0b4090799000e44d0a20541c580345886e40010007002e0780d0440a480451032000c02c0001d0300b61325200181000f6044010300005076607407403041500700081c5800c101c4203070840c0c3c4000d540d600d400500c154400c0582c180d460166000001301540e440890300d034000c11110312005900d04808146030402d04491040c002070041250b00e40042d0b031030040c0c4090903601235000d100002d04421074400d445590340e0000d4142ea00e0075a1031540c00040d02c5045480c900519118401000103582c06040681d0104100008609204602040c1c80303203140d56103e03481c1010340304c1e24170201140b00120103500855004268210483d05807032603604007019042c000003c1959101c0500c114240031880343d54136540808031941c681e04910803c030003000000001d0740c1045080040751070207400c0b849900507102c1d00c030300c1140400c1e0503860024240d8406411141c00100c46061030001034aa8601c2c6007440e940448001c80c0d010014000310f5200d000f0840041c2c01072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 887759928 1250 887758678 887758699
    0x30a02071416030b070f051e090a03110906040c020d1409040c02100e0d050a0f0c0c060215071121360d02060403020d020f102039 57
    0x2500b24816980072030f8400c4c840d58045581c0ca0b00146d904070039203042a00403480412554140c000c110000f4031b04d00703800e80f0030302e030501c0380c4003002c141078201681084480c5103135001c1d603503540c0c5807a0700803d41c08441114148003005403184001e40b50201d9840c1b00041c409001c0d020507010303d9070000c2e14070364240907004119910403200d00943e609881a42801c079685001901000d454010400f00003504035601d84c80e20300072095000326020350100c1c001c072042090307100c3c0d100300040319980d04400034000340e4010040c0c1c0341c40780d2700d203044070300080c00f00e030107000d10540e202141b08404107400721485818890441001c1d0a04200303480340c8140b4030394294104446c4910701000c403402c21a0f4800380054800786011421003c01e110760b6880d01c070b902035840b01044c0020001490096001c02840d4800760400d001214031030081003180004e40004000b180008002071505d4448400b8000280403840c0100041c1d80d002d0840313810582c45400888224110150981500420034007414400801400640342c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 887761178 1250 887759928 887759953
    0x40c0e04050a0218060903031b070801110901032d0b120a05070303141213060e0604122703320304050414060a09020d110f03010509010b0f030a020714 66
    0x30b502080144900480881c031300b1059090020581c0d061b5400a00118540b45800d0140200102000c0d440d12035480343c1d40700881c002400380200d6503005441c41342141c0b614184400902503603211000c041000c0c15540584449203250240755070500c0b0000000550031800c00049a40301440c007041502a10443e110b21013080000500c180c00c50b4001d80d02d4626a9036410646002840341000da20440b04030400417030031880b0300c0b12007510040c0c030881000480c0102c490003a4140355040710251075a81c0003580700c100d0190000070500c1074102c041068010004120325458514429010142120005c0b0010f614a03072440345414034000e4003171a48000c50900409c031540c1d01d0b4083c0c0074650007a820403c4412005d00302d81c03c01802480001c00016059050104140094101880391011140c584c8140700b03602044100070900070001c044460b03903940c14078061001040d03040c1d1049088040400102c42499129825a9042406a4400f40ea05c4406041000c020500c04201d1031170b500400e11501d05 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 887762428 1250 887761178 887761181
    0x70503030a0509030c03040e27010b010908030705100504020402070b0a020a0e060a201204120c050f090a0b2e0f0f09050d061401080a0c0e01060e040c0e04050a 70
    0x20403020040c040c00b01e80d4803036008544038001c82003440b80941c0144001c0c440313500000c1c600b0750301c1000c0607000c0000c5042007050100281e40d142c00591300d42d6480301503115550303000c030380b0034007501d000c00086140080d10b58415a903004c0083d180081c4e10390b1540071400310b680c1c9404491103640c1200185016052545072840203621180512002ca04074441420791030402c0d405407260400306131542c086a00706a01481140d000542c0d210a40e8000c03040c1441e01089a180540050a04200210080c0c6080d240601400c842c5070041c503c10060300e2549013296690810890307210703207a00c0004c00c40107091030104140c10a00e440030101001407040141404400c641e06100354541c507a141e50542d0400751007039646c510109402e070000707000141d05224a0504c401440020382c03007a880040c040040aa02010301242030308056202e800ca803c08400f485a2010003102801540300c44a450303500d0000301808a4002548403806182c0b0f0310348800500d4051410841c20650141041c404c5185c005e00a20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 887763678 1250 887762428 887762431
    0x216050d0e0415030803070210020d0b03070b040305030405010f0903050607031a0409050c040b03030706090c080607050406020c010e010215103b09071503050412030506010c030e0a030807050303 85
    0x5001491103915015280b4260040364152603185a1011041d03040d5280c0c6945588001c08207000c0d4400c2d103402020f100454402483e0903070081c03800143d079040c8081014100002540300c8480c8880900007803001c00c2c008002c039411582d09003024050f008401c8804c2e18a1840e55001900601400d010000c0580d0035401c00c504280b1074aa200c81c2807181d44013000f007107500300c107400742c550380c04500303402058107199124001d40e00c2c009046034180404e41d580c1100f69205480300300c0c0c402c1c61a1408014900342002102c1d00041c007420000d0805050250003903446c1d01d08505030b0304104404900304c12690007440780d1800451194401600351800052804016100c3d1003000c003441000b118180c0f804140b07046075144081d00a5200c12a02c021440c4240390107005088100540540080001d295030ba0744604600b2000c20348012034189003d0804a8142c0d028541e001c081c50f082c841040400d23a40300c82540206036060808200b200d1041c4042004d00c419a000281080e00c005040b105000000001c0c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 887764928 1250 887763678 887763703
    0xf06030212130f0308070c0818010f090815040c0305010227030c091b120a0506100e03030702101803140c0301020906070f06020d020d09052b0302090301021605 70
    0xd2858a0742609285010010b0b0320140c142010b1100f2800000c0c807400d40300d9000100c81c42c055140d410152512106940210404c1d907644102c1d0f0150081560084020b002e034544604004a541e0302e00012140c4540c000710002c40361802080000e401c01005140210145401030001c40d16528042d04c1c231071440c0c2c3e88607045e000c28200c00d102c0c46440c2c9400562042c81080c007802d10b0031f080d00e035950326688042a5204142500c00203000000303000400c10b81807840b0b03500084020901b8104070f414016407003d20b050320000c1200c2e2203144071060b10000100d801040d41550028410b003000c0400b2648200540601002e0711420314001050103422185811900940e9064407001d06184007098200d20800b0a034942040d0f0500440000c21300c0761126000a900a540c0586000185442103040781d00014144001540d81d003042814071604125082000300e10054403011010b2040040d00c44a44400c04074040580001c0c40d0600c0d40c4003074042d9507803841d08080304c0d01a0007070741c42d025840b00c0e0344540a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 887766178 1250 887764928 887764957
    0x1c030206090610060f0c02120604030921020117092802030114010602070b13090c1d030606090a1d030406090305061b0f09010302070c08030d0e0f06060f0a0f060302 72
    0x1046004440510300c40441d805900c8245c1000005042941d0418148105990000034121039080811091181c3c40c840d038845d40d12030458508011418005095001e852501c1e612402c401d040146d810030482006001c030b10072014002c1d622005003a140c1000d0303503c542030380c031090b0701400c20000941000b5021103108600070f01007020031b00a070741d0784500244100801039101c00c1080050207800c0380240814001400314482150300c644030002038035000340c403040007d4110310414030928007100b00340200d094100c0c060081130900000103801007a0113045054141d66402c1041c101034010b0811055400758002620340762030303444101800d940d92502c010b0780d46010b8003000071040f0020342516000036418080301402e1040c4a580d950f80c90304200d03401030516508000c00300204d034503440900b0080031000000d42d81d03a205e1036040342c107445030350b0030558047d44181140c03c4111404251217900800582c2e00800215200c07002507422900e40d4400c40308200320301e0010072601e6064004214002e24045e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 887767428 1250 887766178 887766181
    0x90b01080f0f0a02210303010f051806010c0b06061b0a0308060d150c090918110604050a05090a0b12030a1d01020d0305070302041d10170303040609021c0302060906 72
    0x25403586403000042d030418550040300500005107085042c1e50140b60140c1c0c405400c0c503851007401d5103581d01c00c1c1c222080f0801a40402c124602e000789149140302c170001d00051603402c02c8000a400921007144c02000e014001c030010b4615280c100c151217010b14040224400c40c4d08885034262038088100c03050300001c115500250581c01d214406044403648400080405241c1002d02c000804c0c2c460111020000342501c002030440a5001d02c224201070380280680d540781e549004c0e04406191400d15000300814042042030b640c88600310411160152400d102c9503845094240040c40d00f030210070340c070030310000c03070019440b03400406006010020784803070584141c2c0400010f05004094a01401644000d0960350b146100b0380190380c01c031b000b03418090300b4251140380702c442401006040381d56a14000e402c00010789a4070804d034000301001e46111034110100d010642c1c030381c80014000f43c6041e4680c41c40b40e046450326414a00440c000701c07261038200c0c0085c030b8020b40720001030310ba8010300d03c43e400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 887768678 1250 887767428 887767453
    0x809031204051c0203030703120b09090d03060e0c0412020402160803040b01080604150c140a0210050105090606040611150a0b01031b020c010c02030c040c0f230406120f090b0108 78
    0x320281c6a0b80c0045c015800c0c00d4855500b240e01d81c3d50204070303000c1e83c0c2e00d0b980441a00c1d224a610300d8051030317030390010307058200c0c15200c01000c642c070950007100443c2c4007070700340400b40740c4070001c8800766a03044c03240c02040e0080340041070203446100e0350790307101d80b036498202e50074050400301450041e407107540d58640c0341e41d9070101c4a54a032800d0720068042e150008144500d000181d02020b402901420040b02ea05210000c0e400300390841180d000260b04480820304501c0202c0c4a401d000d80b9048036400d14030300f040c1011820354040e80c0503840c14002c4444690794903c5040040304440b0b000b054100c10b452500b100242c01400030b000d5010301103800c18120034928480c601d0540c0d041c10b5643d009001c070149103c01166003c280706030607a018054500c00c0445501c0d2401460b03500c0c0b0183d02c65086145802200a21408201803070704002400e080c18081c081000324200d500b11401441c000d465814a544290010400320b90340401e41450552040104003008503090f04842c080f134150303401c2201c241c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 887769784 1106 887768678 887768719
    0x9031501030605271c0212070c0504050903070b0c1305060d0902090c030106171009180309090204081c0c0b071e0f0509010309080903120405 62
    0x200304001e034400c03402d89071020300801828801c10b81d0034003200503a200c04455004a034004519080412245c2c1b00b04a4150900f00c05051540e42d000c49180c1041001e4591140c9409681440c0005041d07080c04070581d9122078000200e0003055640050b9004954080840000b000c07105020115540c1c550a000d450000c03a982400907400003e40100040c0c104004c112102c0c221040006000f00b0b40d026400130099014010543d031292200003071807042070682e4201c3c200c02881d01040844440003549081c0ca0b450094558030019901c844800c0305034070840c020079609a010320340301d07103600114052080900c041403500b54400c0b12103980b080c5001c0d4041e0749d190001110a2507c4404442c2030052000d400381c1c506115200c00480c0c1005001e600803c10321905040d620523146080c003110342e040b100036400042c242c85003001d21400e00340e51a001400782c1401010300c0983c041d00090b0b00e = true := by decide +kernel

theorem cover : BRFrame.Cov 887589928 887769784 := by
  have h0 := BRFrame.cov_init 887589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 887589928 ≤ n) (h2 : n < 887769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
