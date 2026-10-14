-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0345
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:20:04.588432+00:00
-- url     : https://prove2.me/submissions/7a0ce6c6-ba1f-4f5f-9695-ddf1a77c63ea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 61870506 ≤ n < 62050362 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 61871756 1250 61870506 61870519
    0x405070203162a080709020a09060e0a170d08160903031803051b100804020901050618030601031209060311042706080309030c0405010302130504031b230307050601090209 75
    0x2000010f0100502c1c51001c00c45041d4602040206220811440026080000b0f0950602602500003000e9280e07910070392040240c52104401c01d601d0b404050300203002d0100c40040a0780c65072031600c1d078030790301d9491100010300031900062001031481d50325032221400d90344000580d895900c080301c40311520400801c1a100149002000900801807608443c6503c3c68200400700010104107801c1440d0748141d007031090500c200401a0356565016055600440d8119103030f0380606800b80105d01c000e42a01d4062040b000084144020580b0032507403400a55510003416031102c1e0102c00b92003015006454028013400140009102d01140443c10f62811120040320504c4c0d04040c0240e4400d0340c0480d01c244c00c001036100c990705092103820311034a41a00d0511007945180d0114412007090000c0140d4641c2d50b40100d8201031103502114451034100300359045079806410030580030548070840c0100e00e0341c110b990804018012041d98a82ca800c100981020303860a08440b000e5800150031075407202 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 61873006 1250 61871756 61871783
    0x12705060c12190905030a0b0f070c0602040e060a3201030f14070206011502070302040c1b030e1903020f0f04150603061a0405030a110301020f030a09020a05040507020316 75
    0x20365000280c01c16107050803c801001c400380301d01a10f03c1c1a00d03080b40380282c00032030030007000c65101d034203664010091800c890155079414a0803600c59070304410040c215400010001100c1c0300201c215405040c0850b151105183d135030701803010f1028021004410049010410a8800c446000501c2c00325010306000c10002c0700240710504403000449601e0000c2404001e101d1507560421409003d041d5900d008000b82d42070b018081e548680c6840001e10480c1c840c1c19001c0c11a1140c0d1012411010013841d20716901c0040c6030190015140d440054060180c0780d09980482420000c1602142d40260030ba0500c001c80b0f4083c0708420303003400312445e00700f5114007081d100300030301108010007840d060760002009401c00c5100d6001203041c0015201680c4140400d2002d56004198040340903808482005100d510001007806405600c00c4490052808020015002d9051b000644c98500c2141c0000ccc2c440d440710104001c0780e6040c0d132520011b07842070041c2545000ea0840b62080180206201c0f003000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 61874256 1250 61873006 61873033
    0xb04030f05120f0a0e0706090314030c150406180b0f0a061503090606090b030309010c0501060506040b09040510240309140109020a0e060d060506010e0a060806012705060c 75
    0x105041e6083d0301c2c06180c00041054562042c402c0c04203010b804409845070768541702c0020a40c400314000a032441619400d90195103c0400460786600101c80a0303805020308041141c05003030301103a0980740300b0f05245194400e5000040b484501c80d0f406140000640c44841051180c0c100003410440c1c0c0d1961034502142c0400040c0340020080320990340440c10811a1400b8025500301d503100504045c2003810003941c0d6034000c010395072480c03400e2a2907004103215040250240c1603e5200c190805000180411014041802004007020540c0c06002946441c0180c10303107101d80d071041141401a42800d841844070009548010715407910f00030030454803d840e102e01d0041c0c45400501c0e9695100b8201e4114244041404000c0080114482091810001007601100c81640040c202d80d070b5400040c045a0040c241185081405400454070b6501c03944044d200d040140d0315140401e5800400300040f283c141c0c0491540d9a1214058450910304000d1015a41210101c20300b2070154480a1390318 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 61875506 1250 61874256 61874287
    0x4060207181409010501050f0d080a0f200307020411090108010302060c01111201080106060224072604050601050316090207080906030408040f06050c0d14040b0a11010b0d0b04030f05 80
    0x95903c0400000d140c2d49000b0810074510345032800c0c28045d0400f5400b64000c81c103401c0c2503500021950606000c1120300c0107040303849180c43d0151515200c890300320090404000030140815500c240e2f01045003008012801c031b468000c5840c1e4600040001d40140018203010024015812600e4004210403591084000c0d00360403078000c0401c074030050700041041100901070304008000b03a002800d4001c1c0001d1940c03000045030003072120280380300400300300706074400c40c1a2180c03441e044943c04241e45d0038800b83e0a01c6c1d0b0041d10180c40500c035100010031702d0711700030618110028001c41910b103c00e01e4010204081d40090109481e808010321040c40162140d40045102c0c40c81055229515810014103000a0792a40c001d2401c00a0910134492103400000360544201d0660400c01200e501750100311405228a03040440c2400d408030300700100c03641121500c0308812380304009020031b039518000e00c40c2c1e41d0300414001d000c0c00507400100700443d014452500400301d07280b9041d4034003042d840e8807011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 61876756 1250 61875506 61875511
    0xe12030a0c02030d090f0303083102040b090709030b1905010f0806010e01030b010302040207020f030d03060e01080307030c0305030903040302030d08040227010911070210030501051203040602071814 87
    0xc280c01c020200114602840750460106160600001103428940242021100e40c00000c0c00d000c25140441c13060121100032004080c510a84101d841c0c4c0f205504d9010704120180890003981011401511481c08008213031058aa660701c41540c5444c64840e07144418020b440000000d41504c1ca100485501d80105030203001200c6543d0b88075807426940500d0088140e00c4106062500001440054111200300d81102e80480707016840f0480c03030000032441a1080816075041c824081c440510540640100c4211207001134031030002c0e82c1e2540b00c6a1070703114121000700094459a60680024040c00203180c0129084080f40d04182c3c895020919043c1d0b01903204000c0341e01c0f00200800c5251843c80450300c11001d0849048040e40007050181030581805161002780d141c036a592149103ca806581c8504e400030080c0160b800440030181c01007000303000303460003505051602040030600004070b404990b6950700070144207140c0303c0d0300501c14000110364003115499075104510042000411030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 61878006 1250 61876756 61876777
    0x1507120206071205061e060903160f0501030e0c04091b0602030715090f14010b04051005240405010807090e0403030b040c0906090b090103091a070813050a030e1203 72
    0x80d90300b0503580c094841403c40c146003d02c2418942000540e460b070f54480c0e50488007030007101c00c0701c0c40311900207095030144110280d054031551b0040888000658064011252a4180c2e541c12a807030744011002d0318107010600ea4542d00200301441181890340c03000d940c16000340700d610b03510004140310b0164181d00340d001c00016400171804200340501c00048034480f002035001004030b00d00315034902001c1c03a001500580702d1601c2c20303104001c0b41320039000038114400c0100100b00c50725100d80c00b22884002d0f8001c3c0760156962440c1c46050f12a0018190b16031400300034200d0505150400445141d01d00400c52401c02c600f81100150b043d400c40310040c0524420b440104049207185e0912080b9042901000200020540b0401800c0d410174488025640c0c0d61141964504c02440140c004e80301f800300007000c6090101030b41d04004c080c180e685000d4006682e03060215264280e04c40c91901401c000505150020000c100c0000e005081c4700d485d102000d0b001300100d2103000c1f2402e056402c03040e006e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 61879256 1250 61878006 61878013
    0x305010c030501060f020d030f0608011503050705030c01050f13050904030203030402090f100b1b0708030a08010b0301030c05010507020d05031b1005040c150e0907030603060b03060106050915071202 87
    0x301240c0350107005481c054407141ca40f52a03c4810b03520000c1d44d03101d02181807000e00d580c604210350080c2160f04510080d01ca9078009110140301c1600d0b0307a80800c500e200a5449000705079002c242e9140100b00d5140301901651b0f498145500706518406552007486c074808840221000000c0d1754a034400c1c41ea01c00c1c1d0090300603548a203818011700000e10b100624481320200c09800700303c1030030301c03041c0a00e068071460180d0585603600d116000101c4086928400c4d16840b07140000200c400e00003000302029030050381c030b941c800c0e6600d03051103007d03010a000081610307040900078800e55101d400907002183c00200090f0813903225480d050309540c03020b08011807103a884081038400c0c0380d0401519800c4400c5136020001840c10f91501d00302c42030f01d030041700c404c3c0030320600f801400c1d4031a250144040c2002044100305090146001c2c0041c000751104803070003410802401c1041c5030104440c1d04942d04c585859140080c00c404202e48621200d01811050200b0f202000115605007a000000f80c42e0350020f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 61880506 1250 61879256 61879271
    0x3080d0e06070c05010c0c02011407020102010e19050d050f0702090702030904110a030c0c0b0411060705060a02090a3c1208090102010e1b19090e010506100311090f040b0a030501 78
    0x101e0b01b500c0d80100c0c108180507610705c1c20320050340c1c04003001482900444400e40c6526003480100d000d0032a00d490740b611881340880c021946550181d003035810901c00e900b1100a1080c514060f255401008002c0c8032509042c400940903080040c0b176994007070818415070b03103410140d50000342240c64200542450788004035402564a4051203103e41440f641c0c1440c00c900c02c4690b540703402003500140010803031501c3c0e04074080b1030f40783c1505a401c030350313441030130f0303030024503240e41e80700002c1d0021540c00384601058100004e500c1201c01030140050607481151109403202c0d001da12901380500101d08281070494000a6510110f5900ca010303d4843c040d041d550b44128400213080d6080d5070f00e105610740251100f0300119404010310040d8180568001030034141540c8001c10420955100c03861240c2081000d40c18000c0642c00217200310011214100c0015040318120304960300307903110710040c2000b00710b066580d141c0794031100000d0310020000f144940e007040101d445100c403135000311090381d19441c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 61881756 1250 61880506 61880513
    0x50109050d02060d090f0f050303070e0a08060f06010905030f030315040e07090c0203090a15081f062109030804061109180702010603060c0c0204060b090303030103080d0e06070c 78
    0x16220003480c046a10400082640c0c00098062080c04400c004083d0f4595460041100075242c00c607011b41c102010154111090500c1d41c0c40360b2041325060b000a0301186c00c1046c41c070b0314210307110640340210004c00181c0d94402c0100f201c1c1034050700d00c81c180510040c0010b1540d4041010344030804400c8040d6440b0300305036a48844144c0d003c82541d202d0f88c2007444003520581c00240304002c4690441000c90001005c20040e420751060b00c0c0000d4005071000f0005c12003695164920a12140c10b40d540903590780c800b00000409003080c01c008810341c00c03004d01005400d12a0040c0c0e0054058880c11485411761000c3c444200c41c01c203842100400c0101081109111140c4a4120044c601c03200152401211000055070200c04001803264101620003044000f0f101754050409964407510800812824078400b500000c480102240700d581801004034002c030b03411b010f6440b40304000e0011415039096540388401c07070708180b191141051b55800195000f035000c101d5140100c1d0140c1306e03101c4c24140c0d0306 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 61883006 1250 61881756 61881767
    0x3070807060305060f1008100e0a09141b1512270a050a061119030b13020403050a020f22020d0c0305060f0108090c0d050d0305060102060f1315150501 66
    0x605445c401c00505c0c6552406486a62080082082614104d0203aa44c0c080e4040f18144070340c1c000c8503c844200080040f05e071200e6100c0c000c001d001c1d1450121030002c601045503915101c0313003a80e081000d001c50421203070416400340030301c0c005007001e074509044000c420a511b41004941c40072010900402c0c1c0329407100414040e954a40381d0402811400e00552a8181e0ba842c29100c000d03c981d6403590340450386442041030340da01c1d102c3d42c41034004158591600070050724084a95a1041e8045611205004158402c581c00c880e8001c010700300a42e0941c080000b180612121203820201d00c02400d501808540e0703203801d80e01c0414000684400c0409010011074880c401c3d020140351810045c00159130703410103410300c1680240b0f001440c0382d640805080c2804225404150090540b0440404200c800f260400f6001c40c0b07950b080029556100049a40c0d07003060352121040c00500c804581c0010010f251080c0c070034002c410320081d541041028400301c0d01c80080c60024007501c041c06010640c2c0c000e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 61884256 1250 61883006 61883011
    0x11040608060603070225030f0c1a070b06060307020c060301030308040302060f090322120804140607030f030f230604140c04052101061206110403030f080402010c0203070807060305 79
    0x192140b9085151060303000e55200449080349510120341240c2120046841d007864024603805140f40c1d0f05042140303400307400362466005520307081000b0103100c04022070070400d50350400d420206480640e2a42c00034442030b44c0c00030f01414110f01a0034101180798031068000d500961003aa69504a0725150900a0514102410b840b468520030014030100b18000400d80f011104810803140c04075100b071507802d80100490b4414494450107032541d605214450000d401107401e1000c610021034070322803c1203010300c11064000c012a03402007903002e200780b10703074005805255600400510003020140c0002c440c0c03660582480d0005601c0100605401c15001d11248418880075948507070410400400321805940155400303000500c1500e10b071038652900c801a28a4440c2c020442c1c9500da0528084600c1c03a54416a0300904204105039501e0040d0100c40849405544d905502d00b80d1f180c0880b131000740039100b80d04001380e45845a001d0303074061280710014030b927000c01441064a012406400e8a100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 61885506 1250 61884256 61884259
    0x30703060608030d1404030e28140a090207020303121308040f05030d0809060601050a02010906240b0a090311040e0706020607030b0102060f010e090f0d0f030b190e060102030408011104060806 84
    0x10705c3c09200c00250014890600d0060440d0280f18000021246007198a0b0b1031002110703200c6d1707001001854440034010b030328a9060540b45904030343c1d200c82c0c807003060b0720030340c80000e4140d401000700da1400c43e641c00d1003a0300180310707102000c062009902c51848580207a0440984419007450400041c5810400c20f02d4200c054206100cbd14a41000d185441e66002002c09040c86400a000040c60f8801c0d80824505540300b90f00304910440610042c02e0700e2502e20ba10344a024459401240c2c03100c141c01500c4122440342d58041d151810b5070356040283c1d42d0804019049900c410216642410901c1030b8005001c0c1507004215a1501030001030948081400c100c4c10b40d0014424848803103810310003e4103460040c180301a080d111020030502d4044500a1101d141c00345104001201e5400622175030a00780f5aa024850705606404002403200034105002840d0b40c004010070901103198401030740100c05005907800d00d0751b1900480d013902c500c03981503890302d1000039040c40907d802c06c00d4660803200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 61886756 1250 61885506 61885541
    0x1a01081f0603020a020307021815060f030109020d09020d06090204180305070b180a0b010303180602100e12040f0305010c030506060a08040c15020d02010e06130b06030703060608030d 80
    0x39100c01480c03142003240900e004160300024041030542c020400c50316155800742c001d030504015020a1180004c00fa1802041110350036a03d403000d02d050402e0716503042e00980120301e941d1810700c04000a50040303159004643d1968a41c401503540c41e514107013454010013000c01c034441c8910401046030406141d440c2e406410325000e4020903800302c2910001e0b42e100301c3c0fa00b0261112184c11010144404448006108001144041003d580791070350480b48a0b481e414605a4041d4910700c111429001d2240181d1210301d680d14005225009020140c86030800c0c6c4e4082c50078811a009075a006030815001d05501d0780c0d00300200f200900c108114900c40d4502005141002000150030740700d081d00e0002007000c401c011074184407200a8a01c0285004903010009003c0450702945a40c40802c800c805540b0700216284800c6000c10114410705034100d444000a5440c1c1d100018a0070203418940c05100c0c11501200242d40b034800d06029040400055482c2c03110031003c5420b0f118890041c03501c9a030b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 61888006 1250 61886756 61886791
    0x9031202010f0f1a040b0f060a05040303140909040b04020a08070f260606060c01060503030a0c050f0a02130c1b0c0302031603020a030b07030917030a0b03070f0e09030c011a0108 78
    0xb0203165400783e80135001c8401180740396003140095144030044440365171000c000101000b1240d04400140300300c9100380c4880001102190000710140a071199090700b01c400c0d140020f0000700100d0f4010780c071510040c00a0341b11525042050b02d0440c054000c1204104000d40034007003800014014134244c03030050440e440380711030407902c913864400c0681268081c90010944080c052820b4120304003402d8083c00b142c1d10303400780f40c00092004403200d01c1500d450050031520001e115000c284026116000350041642d80c179005e16401c000e150141031241000488806018800e0902e011004030782d00600c6001c1c083c5040d4010141040e1a000a6030915074000b442040140c450401d06400c030390300400c541880c1d59130380340c059000d006003203402400c0e05440083c1c000b5040c101c00241d4041d80c0344010811002c2050701c1419541c0750640601000c09110910401002582c1184940e02c4030b4448162414001750010345400d40c0c1c0b14039012042920340910040786540d10601072944100140709608810 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 61889256 1250 61888006 61888031
    0x72d200604050309100915020c09151e0a03020301050405060115020708070b070609021804060b04020c0c040b03010b03030c1b0904111003110c070806060f0603130309031202010f0f 79
    0x28424408079a0113440c4450115117040c0c01815507500410001505446428404071300941b6a811304031428071404415002c0f6821411501c80d01181010141504d0344000d03010300c1940d442c500c16683c56500c105040008030041c2c5087c040d260117144143d004244079414807810320f40c1c00150001220841d071080d0010441072400094032011a804d05030f4a565a00907030170081c001c2e02107464080d4201d1540494070f402000039014062286014032400c1290449000411069200704810034640360b0112000c440286019881101c0d181c00003800000c1d170542c1c21021074296049411195120f401440c0040e82c24030000c080c0c1e1542410032501300009107000d43d0b94901c5440300012182c00f5040c2076800d008294003e50004000440380f8844079200ca00742e451240da681d10344d010300b11141c012640031800f181800c0c0c0d040b0143d035400821050455450f1078191446143d07949054040105014000010a1034846c9169880040e6400400d0141c1220390250030388560011100e0100e01e0f2009120302e4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 61890506 1250 61889256 61889263
    0x15040c06110102130602030a0f0201021606050c0c01060e18011803050706110301081e070e19020706020310050108060907050d11070602120405070b03040b072d20060405 74
    0xda490504200d1045070003036000600a008040c100460401d080300e01140803a00003003d0019040c1ca6503d401c40ba15000e0001c03401e0380035104200c03583c0c03103004005c0c0c00000c059401203039020401c00859030810f040398411909447d9103034003400d00614104203020054030241a908240c0b0103c900a000c00c040032440012001000340000e07081001c081864010407074603800c04142007101040080e00c07944c5507210a40c940e201c00d03840041d80200740b910b501c00a940481c0d00310859602c4c1c144041241e0703688038001e01c0c0d8400f003640c01c40d84560170400d500004000d0b101450085100c0480004541e091500141c080b40c400303407115118200b00b00c10071503c50340c0304040352000031050a001c100243c1c1500f04e00e045018048000341054004555040180d07500748085124030b02030804ca40703040d69140c418144034807003910040c0c00701088500141700b05014034030301c405402000004d01c5c40720b02c540e013040c010300107527400100020b000d51004901c14201c6070312584044944001a2540303051690381c03545d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 61891756 1250 61890506 61890509
    0x1101020c0a0b0711120c071d0103020118080a030509040f02030906070302090415030b09070608040c050d24060302010906050c1c020312011403070b191d030a030c0515040c 75
    0x9400700c408001001d4038070602c040b40c0e50042c890110303012170303c40c1c0c141c0210503000b0f20f006035541e01c1407520010b03195204000c400b0715004118041891039086400440d45485081d803140c00e2800f100d4070014001c5002c009100d0b195010303070351340390700c2d41c0072a01004155103003240d4089040b401071042c40310040000c9401c54115040342070040c0d0351045d81e8041405400c4207141f250500d81051000400d00500c9409280300e0140b61054404a540b44c00040e100c0311802e4074054505410102c043c051030400d4180500c4c01400b440c0c02c00c20400080a2020081000f000c041001a450303880804c11075030448401c8018005a0600030b00b81030a403924280d0302c100c1e02000e240b0418440358251070090003801140c0302412403030580d0b0b005603140c1440c0329801880c1110a4041d02c40d810303000440741c0c03c1009031840c1300d900034004040040d9400b0308550203040c142908125410108201459980c204860501c49101e6201c200200d105402e000341401100c407000c51011108400300400141c91481250 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 61893006 1250 61891756 61891763
    0x91f020c18061804050c04060603150807060f051c05150f1e0904020d050d18050108160522060c03080c0301050303070803040501090804232407030309020402040609061101020c0a 78
    0x4070955102d081541c80c0c401c074000599001464131001043c118ad058010710407200c080a07840203c6640c5002c2c4a0b03503413070301c0d214650000d100c901c010314465100784001c199103441307240c4206102c09000344190403141d09551964050405c81c202001c01d00b1700710f40044480780100c5052030743c04001d1000031503044800b2901407003038800d54002002c5585158961001c50340082c1210204c0301c0c3d5202c09002c402101400c4e03000f031550081d00191541c07181ba49503100300001c000c101440070300c0a000380d40d56041800304154400704010f4034110004150a00f0000b40410390718210360302054227015142501c050414801503408000501c80c0e51000000c0303440382c0d80e018801079070303c0c2d03100c1c1055801080b0100000b00000030024001601c20403c10240201910325140310b045001c03400200248030381d0620614040c0300c40d0170380070702041d1003501c09015242e00038140401d0480d1240e002404903030240d0068004030f00302a10600203a0344c0401c03c2e14500601200840c5000d40c802e95082d9039490420006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 61894256 1250 61893006 61893049
    0x180e0c011e03020d0f02120109020405010f031d0d0504060e06030915070203040f0905180a02030604020f0a090f0204080705060c030304112106060f040c0c0206091f020c1806 76
    0x2000a42c400d038100ca041858800c0101700c2e410724011503001a500148201c10b5040c01c500022504d10000e10840d403c50344161145520400d411205074080e200c5402c248801c00c6880d6400c018a0380c0c148010600356210360784031907079181070100103465180003a000d40d0080c1d100340208100980000703080312580030f00c001051569030710704800300e18503c20b580000201e0005648005010000e076003009004004441e524624030507800c00d02540d80d604501c002c3c2d415484040403c0260810540911600d800030341591541e6132905a00001d441c20800b10400095000078100184c44041c0b00d500e028140031242103241c290b420800750764034000540b02804103174010b0120061503903001281001c8254550302e0694480c80c1c0c60b102500c800d802c0710007a00850060044503840d2500c3e2282d081c407807000c0d07103410007000d43c6a000d000355130700008009078021240c0242c0000058608200c01c805c213510b5030042403182002c105110214030a00c82e1000b41d902090107201c0980d42d40340c0c07100c01400c081c1d42c28 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 61895506 1250 61894256 61894307
    0x1060806063001060303080105010e06070b0a06080d050415090305070b090409020d12020714060409050919290f061201060509070302040e060f0a0302061b010501180e0c01 75
    0xc0e201480c45060b1401c80c0110240c14000642e08190415022240251203404590380d030340c0e0041d00e02400000da040c0e802102003050b80c0c0003440f0107942c607030003203000d0800254981e26582c84615003004020064081071001c6010054494a501540030661252804108032480d69680c0c95a407141805051014000400c8000803922035501c0444155002440541c100709036003001903d802c5690b4001006001d801d201042036040b800b0906001140501072034985860f01d03101030020800039154861901070580d0940d0001c51400c4c2c1c80d00058050114441c5041c0c4002d0006007500e4000381ca03042c100461002c0200b004140003e20b50301603000e541451000302602003e60041030359810195002000305c05100501d94035074090300540711074501440c500d44800d810020082103003802d9a510161080050006060600140038403040c0403604124580c91000c1103402c0da00d00b60851849500d05919860342e640382070090070125000013003c0d03c00e1903602400244142010a10525640240281c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 61896756 1250 61895506 61895539
    0xe090c012f03030708090c0406080d03020a090302310c0c03110a050106060f020c030a02030a062a0503160807020c150708040f030c060215040b060d020402031509090106080606 77
    0x1000e0310081c00d0000703490303991501101c042c02d100426962401c5500c1504031624130307818184212001c1d218140000c200d0305055000c120060b41c010020741e410045413082c0080103840b81ea0842407000c0111681004012151714001c1004681c1c101d40300c0040d081c840783c01c24242d0410b42c02102c45070503241118624112007a80791070015450b40007422580707800800151541d10441104200c2882c0e0b00b594090fa46c5a82015658040c9460203503240d0450342c41e481c00106143d00030640d41d40c041101d0386e6031403c1c4003180021140c0b940c05810108400000b04102d00c0803014441443c1e1016003003500650a18a000941d07a220032490a4001d000c40c0c0880310500c03034a00d05446050764080c403465a11a12070403c0c56206046120840c0e445884c10004501a03002055200081e02948100340f4250b40d2520740840b100c0000c0e01603500a00d070003070355001580300e50000714480c003050b11510310090548000d2107900c240081241e03095901d403080500020078040703001c0750070403811034000410080c800c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 61898006 1250 61896756 61896827
    0x609011802071119060f0e03100b03010b060a030903020601051e090a11070c05090708010308160c030b040b061201020a02030f030a140118200306060c0f06010b040e090c01 75
    0x148944c3c1c0c0640c45181100c0c40544200fa00d0083d112682e81c1c24100d01000740007074031000c1d0840c400d02d82c0f681154004c0d0302d071000301e9030096160800007000442c412621101240f4968800c03c0f0010010340c0750400401410380421060b0300500c000e4503407174419109424244880c104203028544100c230100f01088403901c480e0041a16030f050384415a654010501e050704192203c0c3c0324144c090140800004c0100f8000c0c1401c80c101ca4100026901d4894038440c019204d4030b40d0102221203451150004c004a124088403a101d64810120100141860700030824141c1d00d15801d0b241680c01001002820365002c000d80d40d2030200180b2581c2c49807590403111014001c0101440e680d4180c2c1c0b0700000307903c2e160380035403035880707135108420401150654800c1c200d8200208245140c03000030008501c0d0360400c2001000a1b048000c103884042c00384003001e42c00e1030000e034010065600c021405120303290042d072042c1d1304403110b18020a41ba010000c0044e04040849246402601c04190303207030304c10a0fa25 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 61899256 1250 61898006 61898033
    0x50f0310050915090f040b180f03030a0c12060b090d031209050319030b0906130f0c1808010605030d050705120a0c151a09071704080d05060901180207 66
    0x41500c0c0e841d1600c0f61140082c40d0210000c03503c2084450041004982ca4a0314540104d8100e0703240c0710b0542d0b0b08040959201d5911020818900c1505240e4061510500c00f0b5401401030b03800100d2503900360a0014500e122300b0030784081c400c3c03811804200a2a2040454812030810b845210021005040603106e074615020380303a02c00f80c209080403040103004401000001e040e40500c2c02c101c030200504608507203020560716001008400411190302d00003d001f94075001c40000032440380d600d501c1701019600258140d401240c1d1380c0c107081d00208001002440030382070100003000b11a107131a0000c0c2c2e54040410810081c042c1c00100c3c10240300080c4200c007034071040014400d9640e10030000c0102607001281c4146d0711500d03104070840a082080c01400e649503071141504070082d003040304002c9205405003180e01444a8054011202425424140c2c802c50107507060f00c0d00c8800880d054415610000c00381841078550500501402c0429080022050028031005854248901e001020724001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 61900506 1250 61899256 61899259
    0x60506033c2e091401021317070303030209040221090706050a080a09060605030708160b0a0c12020c150310060203030c04231507050708060105100c1109040b070809030703050f031005 80
    0x2a52813902403290150010314403c80348500c51034480340e643c03a0101403e200c1d12198807480d00941002c01c08288250003030203080d03400810052401c9005042c1104010440b16405c42040400c410400301c0312050000d140280f481d03080c00c5161401070b28000b0300d0001c0c02400e41681540c2c0340031480500c40ea03540004090003000e42100c1d0440d031142000f956a207041043c08a0440e280800414407002c1c60040d5140456241c807038664102c400da9850240c0d60001c000c0000314805c100310101990303181d5401c0c0307094000e4030000c2550b03820b1000240041044a400403000e643c010014058912a20411a0120780c10380e51720f041c10000c6908000c1d102d01d044540380760f00510304240c07000c1e404184130003052654400d0085500c2c95a541c40c0181d110f48c003d00ca4140c0c003d858081d030340c841c02d002c2c800e9040c5d050f01c500030b10041c01d0700f002c0000e80d01c0c10042e50240d0385000c0003801c00040036007000c4c0c03480d001140c0c440103504005989e41c00a14034401d0011007102e46c2c5010002c10341084031b070f000020242070f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 61901756 1250 61900506 61900523
    0x1501030504110613080609010b18060f06030a020a020c09010303090501080702030706020409061403060c1b0c120a030f090305121c060b0d0b0a03080403060506033c2e09 74
    0x40d130840c038010118036000300203003070180c0310108900c03580510a0059618015100742c00075148400c0707101c03001800410403900440c403c54400c50556461005501c0740444e0300c80162128940f14000386004c200301034407805501e90000500209420004c6201142c2c2c0900c1c0c038a005070f4441808a04501440000514441c008540800e13400d0054100d030054403074641c45050300400d0740301016500c4d40203442c0104111001c10503028059001900002c60311000e000303d0b902c1c01030000100b030880c0d4640c241541c0c15044002d4130f104066011295041da1346040ca40801d020341513845581d15641d103421158506040040c01c111005261a00040a01c4080808019190707448042c66207550104854008141c5081403072029842c1615228050782d420018080c20a811581d0340002800003524141d45842002059440d440c102c0034440710400104500403541c0c10f500c504209200041c00094050b600710381c0302407003442900e540103d1450b0800701194211804010203000400300e000e40a032030703580c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 61903006 1250 61901756 61901767
    0xf190c080c1c0201020a0e1005040515070209010b0f0906070312180b090708030304061104050607080c0709020702061603140403030203071416030b091207050c090105030615010305041106 82
    0x140810b074a804541101c0d41601c1100080c80100e080340f00c4e500d505004034101c5005d41e042d6041040b508802d58105007407242c80c00751134600082107444c01c0201480310300780000da200114181f80703140710b00500d00052094140455028030800314001e9540407401007030040f601c0000c0c10b20030490f88a8a690a140401c0b040c100300c581c50a1145034101d003610f03025032400c04900100c10009242d01210344c0ca4016505588036a910000a4242209011f1000e0001c2c4030125503603603040014803407644542e210b150340e01503030701c0c005003041400d9100b42541403040c80008090388584080f03030341d0072080b4800c0034a4550340e440d09488200424550550700107020a01104040d000401401c1183c01500b0000c8018000c1038565030343e005480d0142c042314100c0c1030400000c0c0060941036040300c600e2090310007085040d980f116403900031800c04d65541d8000302c10422242405105d150152406601610040c945424241c0c90b8607050701d2030364105591940010140034901840e0718000900924165031344 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 61904256 1250 61903006 61903027
    0x30403020307060c0504060c02121c0807021501050f190f14041b021510080a030e1305060604050d150903020109030f08060a091806140115050f190c08 66
    0x20b4020300c20840e2035614140c07280c4540741c05241910112000d81d0340f02c001145081d0309101503a00e451403450080c0c81540c2446030b0200f000304050714001e81139698046c1603c0d000303030001d01d40036400045500b4007000c0401400b40e0b40350416416500e00c0203072a12004001c8600341c100041e22181c1c09072101032a1300c9000304401c034007521a1842e402c42254203205284064980d444c50040f4466480301590040500740303c0351044844a603131180d140441d0b10840b43c0d035102c0d01c6082101082c2c0c100c00007041443c4200c26854604000c801d81c10054008000900c3c0450100d56184951f004580c481e1201c920b00c8070400c10054042e04000e0300e4035905000d00d02c20303868040e01078000c1c4901203020802041042c405603203d803c3c00c602c601c80007080343c400306107004540d400038440c503600c43c08202c0c3d09048000110312240901c1401c0310049102950640c9041202a5015003504c200020860b04001d60028130030340006031014170304440300050650a15400c152068080305500420300b21000c035100020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 61905506 1250 61904256 61904263
    0xf0c030c021206100e090c010e0307030b0403050403022e030213091409061e060103091a07020a030905030c0d060b0f0d06050901060905070f0c02030705031203190209010c08090a090203040302 84
    0x40c41c4d91409072000c05449000c0c102202808413603007510b59000440d092100d41c46403c903103c4440000e4241c0304e0300c40d00d90710b070501071040844094000c607400240070011424610707400303c65261001e05e0910750100d14529a032102d0900801030381010303000316440804d810010501001080d00701001c2081200b010604103aa0a04a8541d08103000c1c641c0024156800e05003030300d03240d6804144419031551904e005500030100d51400780d80341c80c0c2094040d442600c0c042c100c1d85c040c5446800520092400e49001803e201c69a00503600941008040030300944442c0103a0140552141000c107420302070743c0c042145540303e1106180d00280c195200e07401d00c10258001402440d4107070090014940303c05180044c2c543c03c0c0c0710340000491019421144070b1192926102c0c15200038160341c451559140020300d0000c030380310349200d00d510010030300039610245900c8a00507000d2400c15400d040c50b50380003803d08171000902038600d81c00090820055a509000800640b903407801c115101e04050900965 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 61906756 1250 61905506 61905511
    0x7051f020c150a0e030a2019050f070504060503030d0e0120070b0603150411040b0301051006030b030610030308070903050a030f02100618020703120203090a0309090501060f0c030c021206 82
    0x705113890281d154506000c800c03211140c0380ca0703c9070301c142d040c4403045000f000b516102203403050080d03c0c1410700c0c5d070900901101807a80110000c020701b10180d0f5182d41444c081d42e0045128a16041c01003141352004800d8500003c101500082c0c0341d03c210031044d01500381d46030200160502c074481c00540c0e040741e0010f0440d03140074944e44005a51084203056036440001d4800070b040c440500040c0000d0250543c990744103601910106540b0b10f244086802c0d518203a4a10307681d01e400c481c0601c1481c2c0d03d84110070010b40308500a11050a04c6814450450524080030701002884800504200d020324161801107500c001182d1f2a0310040c02c1c0101030801c9212210018024601d0500342d800341030244c14192031154107184243c84c611442c41000b03602c401d40807402d10885034140d00c2003445502c0514840c1180c1c102034440402a07160041c1900141d07004000082e10f00310041c4122640450001c43d03d00c06414441101030142c1010390301d61400b0351000391b0002c8528090301c800c0f00041180d90 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 61908006 1250 61906756 61906771
    0x90b030309270702011512050102070b0f0612030415030506180403050403031d030705040b0121020c0601050607110103090213020c15070c03021209040b09040614060607051f020c15 79
    0x541c551100f0728224240d910004ea0440e44100708502444202400901c403e5610700c81c000041c5440c40c66525040780000842d0b4100000085804001590030054540000f1404e05401b031440c042c2807407402c508480f05540d40c0d8040580d00c00c000f50130f41d00e80c2c3c40500481d2260381e090341350620701707131800900d0f40d4024001200010007002c20280c00c0c401c184081c142d20303180103000e0140d150070481404028186030500c3c50400c10b4000001e118070f21403600350a104440d0950142c0c0d20480e41d41340d1403038801c0c181c0c1b00c50700a00081003201d000c661b1310f0506417050a824a00814003250078000540708181e0102034415131440014100744840000503446211450700d0044080c1c2d9464240c2515a9119042d020303025030854002041030a406e0740003409241c000500004061400801043c40e40604403022521540d4a201803100081c00300840d560201003100da02d45000001d58401e40c8506006400c1d18503540b110900c480c0c0540e142d010b6030302070fa07607800c05c87c1c000074204151054496400d54103075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 61909256 1250 61908006 61908079
    0xb13140402070b150f040c1e02011104080f0609030702010c080f07021f0201052208090604080706020604110f2d04020c01061e030305030c070302070801021201030308060a030507090b030309 83
    0x110f81824030b405187c044900940700c0b0403a0f0480c005900a120000400850465588864070303544000002d020303002030b107603141c01005910507140065241880c040d101581642c014001140180c0c0d0100312011401c0d40000720039194a5810500c3e4518081c1010081d8480300090000140c1c4848081041600720703503600a01040d12340b802d00c10850301c1d400000382c0200310308268a5001c079403d0002080c0d4171f031000c2d203450f1805544101003828032186070000c800581140d000d11060100302c134034000200c1001c44001414180f52000114801600d600781c00244003074014070140c0c0304545240030a070083c098015561014001041c42c005c000601915901d200320340f81c01810360141c4000c03207050b039500d40c44152035511043d088030200c1d0001070044085105446020031400c50030f0010341001c0ca00030140d29802d50441c83e001d00725420091603039010300308001c2c08002013500010300d2000c4945079040000e441d003454000c41e0441c41480314084c0c11018a80348026091038000300f21210710a40050b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 61910506 1250 61909256 61909279
    0xa03021c0e03090d0c030506040302070f090606020330010f0501031d0d080c0705030d060e0901090c0302060a030e060c04090509060411090c070b09070f0b13140402070b15 75
    0xc250407103203a092a01e4696000744014522420085050b08105010b8409010f98030351b02d90b5540e10b850403c503002c03030041c0c21102080060102e11890341d0040c1041d45400c0c4500e40c200b00c002596400340e1050081000413407510b89518183d1280c0c60328a406040354007060568461140350030128071032282e00d000038a81204610403402c004942c00b034050701c16010f02034850301460201c92518016244400c03040f410082e840c000f44c030030401810b030079060705400320340385103444418512004003d100c8002e40c0d0505201c800041d201a5541040d40d904880c50307525030340c6000084004000b820b02d46c409512030501030111411154024000325080d074601405199920804681c41e520207481c01890003070a179810b2180f41c5001c0094950114500d45007a085c608a07440710342848405071155481b54010034030a000726803c1c40c101401804800c694a45040c44242aa40114a5a02c92118400844500c10070141e489404491142c0c0d044504580c1d941040300000b0b40c5000341c0d11805216040c1041c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 61911756 1250 61910506 61910557
    0x4120c0821030c0306010e10080f06092701060b040602061504140403120f0501090b0909120d0207080708210115050a0503060301060510181d061210020a0302 69
    0xd0102021040711101e003541c40780c0152040c16000030700018140850107000945a846001c60120700d55116564107005040c90420040c05900250165000e1984441000b04602254450405007006841c000c0b080454a040c0c032801050301c1e07001407954003000140010055070000700c5034013900112030f10404200b004810032048840c88150344c9090398000f00010042030140c079001054030b0300c540000ca40c0303c90300c0301042c080f68802d801050b911507503080381c5241c3e8140680d8459220b0351004c002c1806c80d03820070014103c0e000e02d4000c009095000103021040081c00000d4819a607840006151079413803501842004072240c100d411221183c03c0000107010089641c4000d030000d8a8036400d280c010710707080031a210f40c002007d058040d9200c240006032902c40160360707410b45070140e0750031405440201d140f840d00403007035104680f000010200d049140e0343c0e506250f60048000c030f800540109048a01034104040d00a80482c070620203d103041c1c1c1c681d0150020900301100869804440b03441c0c41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 61913006 1250 61911756 61911793
    0xa030510061a070f030c170f0a020607080705041a1909060210022104030318060b03010b0108060a1517090304050a0806040506010902091c06020d0b030d0e010507060204120c08 77
    0xc09001202254001310110f400380444588050040c0039507036513940ca1b41800513540d03005003026141100005511000d032036047c8001500720f615858514460304010100031300500031030090503a134021002103013029901180c101c2c1e40709807440e4000722003100b0218029006841da4402c15026018815031100722036582d00c2201e0804036031072a070010f20039030034580c00e2507844d004104400b417580d241601110b50020316200d0250f00d200740d0000c1440c42d2407000340350a42c0c80410800d4140400030091000035900c5840302d8007030341c030304001e0722010240d000001c0303c1144e030105c034400356447e860040c4007058101000400c280e800c15240f408540b661000c460340d039400201e802810680160006100002643d00101006000104542417206000e441c508004031207080c116041c07580050841a02040c6004a0380740840843c042c010182c0b4115001e811548070844940c100b0500084200400003075906442c050320180081d0442c140280c90041a00152070007a5a0a0b1245e003440103000314465 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 61914256 1250 61913006 61913017
    0x50301060801030b180f0604030e1806240d0e0706260711010e0604020910290d09050a06050912040b13050315011a0304020f09060a030510061a 63
    0x1070703440004583c80c0d5251060020380c058600320354031030003032070490600a041007110285400b80c2c0141100e070505107400303800d40408056050060050340d09440040c0030303c254a5034052403d407144219509150080c0c2c0c03038016000c2901c030b1980e20204800680c0461031b44080032b1040700340308462340c490b00c481d8190f80351249009880610104401c01800b0000e81c041c00e00d400c4581170a0146030b0b81080c40d1038a0079513200c1c1c03000340c040381e12036000c00080d89009540f054011400d58040c0e0301160401c05d100648018000c514412585001600d4419000d01c0c01140c0d281000340004014000503490b000d6265900404291000d600f4200070075040782c00410030003407410074407000030310b8030345001032240c102d0700b00342403849240b00d54010000706a10140003440c80080c0d210302d450215810501c180c0c00c4c84c90100010908205c05204000c01030702c400d0032054511108aa4400195032003500103103902c55650401029406900403c200c1c000c0709400040540b98200e01c0811b150102851203219070081 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 61915506 1250 61914256 61914269
    0xc0619090b090a0915050307170601091a1509130207060e0708061504060902042d0608010509090a0501060b0a12050402060901050a020f0604050c09010902030403140c030d0f0b010807050301 83
    0x83c1c001009003071200e600c200c00c2c0c048242c10181e50140d8440001c4e08000681c2d00c074545001c054000703403004803824840c1501401461104001080100ea43e60141180e0300251a0040001202500b104201d110998002e0b8400528002540d46161102d0000e07401c911000c8403442d06040344155450004103a40c1d003940c03401c130000c206a83e11500c02d001e580301d15500f41a013181c1e40c0e110208000805000900c041c3c10300405d140c0a4840c0d03660410b10a484110060503042c42240707040c0301855001d80304504440044440c44000d48420501c903083c8048490002c100c3d43c81c020300090705a2240d00582000e82c0c0903100c03110314460505aa40030b0310300c00c0b18001c3d402802000902420f600660150454056a104940c80541c8038031225107003410540d0290340a9000b0a00c481e01894003500786405800354510541c254103199130007401050f03400d040503070401d10100c0d0a01c1640070400030340b2400380c0356010030b00540c0c1603640c5010041800c54000e5001440380000100c446009800f100d040300c40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 61916756 1250 61915506 61915519
    0xd020d030b180f0705220609060203030f010e0709090509100f02040501020303010b07061b090302040c0e010e040b060c1204091505130c090e0403030516091805090c0619090b09 77
    0x32243d200400e038400090249080c013000340071020000d140c1280012078103103c00c1c4220b01d042c0c00c01c3c03000381002c00c0310f48c80801150f004000300000c1c64444060f00d8110303000c0208141aa854a4800740d8140741c26400507102d551903c4200052200c1c0000e07418011601210f0411400d848e400c00320301a0700c118050030b80941e02c200010024980d6180080282d18019240002d05070b8640b0114801c465006122100184c3c10304e07400d0080d840d00f8418111000790904003440302d2444180007034114030990b42e0f454851541c03102e040340c4603103d01084901030f0780d003c0107444480b0075500c60151560443c3c000d46041e14500f07111b01d29000202c035040030076510024804449080541410b101070041c1c00da440c0d0400040890010b062406428043e020710300c42c1d10301181c18581600c1c80e0981603003803407030301041203141c407403c1003207031960901c0d401c1803003043c0c9e4041050ba0342c074000350b40741c8283d9100c030340c3d0000c3c0300040040c807444481c0813401041090b5540d1a82059842d01250414020a00059840b40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 61918006 1250 61916756 61916761
    0x906050105070813030b0c03090d030501050d0206070201121803020f0106050105030613020d020f09040b01032013050a0f030b09071805060409050a0501050601140c06041202030c0d020d030b18 84
    0x203e440d0003900350302c429400d0301c00080d034495031a02d00791034040d03820442040d008003e0011052041c001c00d50000300f146004c0000e0340c0b411000408108015001034062000001c0750002d69101c0d549402190748080c0c403d1080e1001722030300f403400140060041c2e005001e42408171080a04c18001c1c02c049400507943c05082d500c60004200002c1c124000745508a0ba0800460040400c3d90001c1c01091800d40b558540b9024504244003d03103010b12030b907604161401056a1415244040380504991032009040c0c46550310100300080a119400040d401405100d002621003001e01049054a00ca902038070841c0d11440e40170f582d1680117000b1601503002a620051100015600080e40704000803c0071400f04025100d050500c603840d076003502d041c1d450b10100059560070040e0611b02d444c1004019203011552450349031a084068002010500340c8880964854400c00640b4124102c2d082a1282590085000b03951080103a0390305011900f4824015250f1502d03480d10701384080000424101d55 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 61919256 1250 61918006 61918013
    0x6180e06010c0605130b090616110106031a0403020f0706090603020f120a0b0907091202060304060b1801080705040b0f040b04020d0603060b0307080f070608090a080d0f06090605010507 81
    0x8550080c0101d0421840c1c000600100e402401042d000c1c1c0395182c0c0700c41e02050981051603032610000c0582c156548990288a41c00c90348000840200e1241e2a000d1900b240c020707117082c00742401c0e6101408190038240911070700000d007464140a00d10940131142c500d014660300d592039000500c00c180205854103030412450f8040e400600b003003031012003a035103001c40a4010034016170060311400803a80d035030304000b030803420040b114039000a0079050906c0c0c42460306a02c00801103020400a000e0346003c4046020006aa00640c511980c000c0c80c40d102c00501100d0b00820000900c5024250320540000180c54241441010342a4201410b000c6001c0c07015800c0c0009400134008060304a81d080240c004400810b10400d00a0340c410780c404141c05032010100361074031b1442d0704102c501d5000b90b850102c400318005203c900711003450500c1c1c403540d55540e50060620a0340c080290440000242c0c64941c42c90b56404005403102c01e140030030400780c40f281c14004891890003002c0c08100e0401211010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 61920506 1250 61919256 61919279
    0xc0206070c05100f05040501060b09030c040b030a0501140907050409020a09051b040b1e0412170f070303050601020d080603030d020c0c0301060b03010302031e0d05091c0b0603070618 80
    0x40600800403a20000c2c2c500f10010300310303006082e4a200305a601c41c00c2c00b0405c0020b001e1003004144042c0000d041c100c1042c0002e8560b94141d441034030441d6200e1403001e55440c1440428070351034114000b007150074140b01c0c2503103804c00112103124483c05081004156840c107403107086110390300600440102030411081400900b400740c500c01e0004600210000e410740c1c6013005002910301d10680644501e01005400048100c1983c551f02002c8107010030701418076003005820400350020a5088200701d0383d408114948101024118000c0000940f40c0505805401c01e0340520320030381c00c9a40864010700101d5490301c0595806525410402921403100e450740c018020261298043d65142c1a00400003821507905510145150ba0044010001e529081c4200c0707813002442c1c200003200a40764180d003074407007000408030010300c900841c911006031104542c0510071002d41d0541c10520140c2d00f03081c02c00c04800c4070803901c00d110701c2d00f0100d01207100719207103c0d0b21542102c5000000d82007078041e500303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 61921756 1250 61920506 61920527
    0x112d04020904020c0106081c090b0a03020703090306050103030306051002340b040e0414030a020709020d02090603090619020a050409090f0203061e06060403050307030e06040f270c020607 82
    0x41c819001e110740d590003134080c840d0b0001040400000d06800031440d08481c9004015a404403d1250705c5908000c0d4803065002ca40d440c0b50706103001030341c8141628090390769182a40002d000107203008004020940c259208a00b030702d6080751241d000d090000c0040b0382d10440c0c62400d00e03441d40c1d4640d5011000c000503581c01801c148011584000a484641849054009511210884640c50240810311000041030b45002c41140301851500c62043e0003c3d51b00c09151041207002c2d0750000d4a500c141010f541a103001c050020030450392400c080c4201595841d05440e0740d03038418500200703415222014400c942c40100161207850810385802c010714010801e090040e42c20b925012080d800595050015070f00c42c28184510f003251914001c0540000c40c0020040c5000d07040400c01400455400001e0f0740a9a40c18a0083d16443c012404102d0a0103164010040d4905002c80400c0c1d02c0d003a104000e0490050f4007000c8140d00d10003a00302d05482a078003030200540c001a000c601070b544280d0041c00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 61923006 1250 61921756 61921759
    0x50901080603011107050c0901081507051c0f0e0606190308030a11070f030f0206190509070810020703020c060301030206090d0503090d060501060813030e130612112d040209 76
    0x20b5514080030f130344c038556400310038100d8051f08400c06038880d80c5045121306002d408224020700205402d44a002030700c00016150f4403c5c01000315180d9000c1d031240f652080700e10380250041c0501000c81d030108c0c2c050241d03000008184e010300e400041c01da05004110320710018000108007006031640e1112802a40050900b5180d00c0d240d10255070340e00c445030020156640300f105090181035250500900c42c2034502c49140031500070005120703c280c5e5031194102035070310f02c035000906502c594506c14034040c0380d40e204640c1030252820703d50340f2525075800703400101d01a80031365010700d0030780c010000c4500c42404020740c00076060040520300e090158040203074a01c50002c4903e001d01a400040b008030490760100d46e403130b07141d100505c40950b00005440d0030152680d580216004503a4016000001c5643c6442c000d469400d44404452001d8201c1d500802e0004081220710000d410a0001e401e294400240602d01000d01c0e60001c991402c40941c0c4014000c403010b0b0380c10380c203100f0000a940641e603041d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 61924256 1250 61923006 61923011
    0x50925051c050c190309050604060f0b1003020301080d0206041a0c041805040c0e04200a1a09150c0604030c030e1306030201030b01020a0b0606030a0e0303072a0305090108060301 78
    0x8141440c201d210301c40c0030f001200300c015140e1300003e10300c2c00340b005a018104105400d064001c000520001354403a0043d034080c0d0f0100b40d000100c0040401400072502c0203501c10390b14250380b45615010350046050300e6040c010b0b145000704029040e84d450b10305460003892080c100100758601941038104e1604925060a11442c21359a40052040d041462140f0401e003540d82d405d110030040c5420403500102070860440b045890300d80c40e02d841c0c0650040315100440c60704101d0030541d6440200c00400303442c81d00000e54a551044a104401c0e42004040c107005840031202420b106400e40c0544000c05280d0006000d0741ea41c6940803581818494811000c0c04403421001c40d240d50b803481010103003040104000342d100c0c07031030000500399101145081d05642085070030030081003101f1003581c3d00c032509031441c587d85d407281c1440300000c1c10f5038480010280004418030030455401044988942e41c829111203081111011014011295400043c00f0410800c8441c56a501889906500c1070005000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 61925506 1250 61924256 61924297
    0x3030c1b0b0301030348020622090b120a080d020904020a0e010315150509030f030c160506030f0a150302090108010204031a010e0105060304060b1905092505 69
    0x481c030154100b03800440118103100d411405201e0015101015543d4951244403445403240e4442103003000c030382d0300d0f90f10803c840306130b1419515070f1400c440c8040310f0502103002d8110340d1240c01d440c18259000301c013141402c02407595503601c0c04001c90f400c0c052014001d4600e54410b60b80e0004150f0002201e105d119400340405101680c507403000c3d041d00310361a2546d10201c1c20880006085846400b914080e1129215091100c4891030300301c0445d4000034200140d40e004c0c103c0c006071a044248100500074400090780c6440c00b2004035080c40076401000d0301c070b031003541c0f035804212850000700c40b41c6070340e4489180042c4071554650002c400040180a180d41680e45a4011414582090f00004250382d0002800c00030460b40d079040b0128007101884120195061000d00340d10f0541c10702c00c8501c52000030000c101400780586c043e400018005100b200c1d4070030038440f07100c0c03801c002e84203180c45522140000b03941122003020034460200c0b48c0708450168003070007105540e9038000c9560b542ca07202d4002034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 61926756 1250 61925506 61925519
    0x3030c030a1509020307030c030603111207120602041a070b0f130209070f0e0303040f0504050711011404021002030a0206010521060903030901180b010b0306060f0a08040201020d0903030c1b 83
    0x1030680c041c00380b8103801340e6249020000030b0b0940b4070f016410310800d45811b8040012624810720407200c4401100d081c5548071000c481c40b447c2940c503400141942481900c440704010f907583c028011200304241100f0403c0580300401e078a80035500b00681501d240e01c0000e1402c0d0820b40340355a22681c440b81340250b000d8a0307004078a5100c0c0483c4e826004c80c854035032a40c3e10b81e4010090307005c52002100203628003400e16081300f405a41a2182c0c5000315150310103c1d50950280c40c4140c0903000400c000c101a04032114035480003082618180d0142421000d00e501c420303c00b00848004040e150000c210316460075091190300c40c000a00182541a0800c20459042d001e11215000d050410011a00c074205804030382c0c21a035404007039000e144443c41030354000900d134901041c1102c81e4051030365140da0b6600003050403446010303006011030100054821120f5044002980071324002e078221f494480190400340c52039401d601010780880c0020b54400c00092000000300b40388445c15559400b070564496 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 61928006 1250 61926756 61926791
    0xb0a090f14060a0318030f18260106080a0b040209070309052a100201050108060f040302100e030405041407090801050603190602070507060c03080f0105010c030507030207030219080106080c010203030c030a 90
    0x4021000908003161040307405500030440c0401088c450114000240352aa48062415200d0f008203070f11540c8004c40c00700e40b042036020900829100c810303182034280130b20300b482e25402d04590483c030500c2d1030008200018071900c103075840c0d241e00200030b05001c1501e1100d00000200c64255031500c0c40740c00c00341401501c0350b072051b02840c0070f903800110311541802c05090400d080204841c0c8003c003803104100110f40e001940d07041081140c8000108801030070400e5083d40b0464004580213410070010703540c003903426005248150314980d1220300080c1c036000007d090f11010f850480c1d255000e062107142c1101e41156024800f885114010300d050340f01c0d035406041c445941d1054003c10009685802410340000c045540600b06441009403036041c500040c10021560740043c0070801c0100b210800c00d8020031801d4051500180340051030981c0301d041c0e0401407030324000c0e00301039401c040c40016883c40008a200c000300f0140c0166003950b41d40c0c1401c00858200400e4000a6038440c041c00c1004490b14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 61929256 1250 61928006 61928051
    0x2030703080d02070b010503030c070326030f01080606100e01030c0504080709051b0301210201020a060e030301050301062102012303130317040f120302040f0b0a090f14060a03 77
    0x2d000075860700201d042500c00020140e0040380690030810040e401c01d44017091714000d40e41c0c00540c000c5002408031000c00140851038007929071803000000d000c1558203c00b2814126000d01040303e80b55a9664203200c0c420101e0720030840030072405100c001041d070098100411200d01c038074020b42020380d41c0c8484c4d4074040c01030b13011000c1c0640e00c0c030500044250340d40440700b4245143c3d210078039551500014040321440c3c050440e101f0b403000c1c0080c0003160301c280001c070a95600071909100841500700d450780c9070360084c40740e5840780d0301c2d11340c000460801c440c41703040e04101c0042c0e408000c56040d40041d00c86101030186040002d42d00c1c1640703000d2240c410051402800d62608070307190b13000d003894050826521149a0140005041d04000005001202c000d00c1c481e1300a0300820224075011042c0e01a015681090f4100c0040c608042070499004000c3c020301c1e0140e50b0740944c210360b6603001c1e0380000003600980100324414000c01c2d41608210009040303109080c07400017603240c0388002043c0100c424 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 61930506 1250 61929256 61929277
    0x6020a050c100c02071d01030809060f070311070f0303120504060e0604030201022709060d03022a03010501140607080f0405060f070b01080111091219030809060a060605090d0203070308 81
    0x19041c044400c1c690420040d0007414124106c0c1a1601d0144401848410144801000c02600060715400c03600c4043c103076440d0005810006807900418500034040d04164000030150f032003030381800928440159150812240c245e100c0140e130400120f0800080c0c0401030041d14041d403540c01d1030074070880c20407240d48240d00a600050300c40c240044060444158110840516400c1c3c0c2c0300010207980c0e000b84542c01410803a2400c008003076504e005da0400104640c18144154401012501080c840a0b000845c400880007001180e895445066030456243d00090b007081044c80840c00280c030b0040102003203aa02c002a50a065a403000109598050010f034225000046029400c000c01001e5403805810a4402880600c05006a103001406608405481150b500001484051080c0841c075006407401d00f60880b016403034200901010300a03150540c0300e100b0b03040010105500c9108070010782e1499980c4601d00380d40c4500304032504400490682c1c0c18000c0850000010301d50400070b000c808807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 61931756 1250 61930506 61930511
    0x40f060809010c02070e0c030712020301120201170f0414030409050114041b020309010c150c02060915010e060108040302010b04150501021b06030a05090a050604030201090b010b130306020a050c10 86
    0x1404a9140c1c296181501580300b5540001c001b40142c0040c15101c07980301c0c0c203c0700f4a0751240e81e481c400b00d40c070200e4240d10540e414400800410031004c0b0041c0744031014000c1c0c85a003032440304c0c1c1316010001402180c1c56000301a6040c003080000c2c0c106491000c018041d03800301c0b4105521282c440044440070b82c01184400c0c0c211080c1e040c181083c0c0038030b029450440b02d080c5011050f02002075103d108044080b410480701c0b03d80c00040100e03901901e00f80140e0314100f0804140c4580c03010f540e400c8240d86515031407003203040d20b50316001c01030250380c16980942070003032a0b81c80b180700560300317101d0241c406c4045d5500e4901401e600d4440f4414142c0d15003c01c1015500186003400181c10841000e04582c10307140050300060203a100c0c1402c803500310303d1002c40020035540e00204075040c112000d9004205000d210107000034075038150881c16040b03004601d804c009990301c0c072b040301003841180e000c140782d00300c149810004a90b481d0302511891095080c624a04060601c0c1d0500302800320015844865 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 61933006 1250 61931756 61931761
    0x9090f01060e04171306080903040b2a030705031c02070f03021c02010c020316020111240c09010c0605060307080313170105060117061c05011b02160302090606040f0608 74
    0x42404601c1001d6000035207903c1c85d040c017210000c1c00c007070740e5402034005100c01c24010401849080088a00078884030101a0b00c80d800d1204152203407525561511060307404685c074609864012085650341544140150b26010b40c6005d0b810000c211085000700c0d85500780411404165000350f000d0015100e85d0213400226041c25102c030a4110103009081160314144003050743d90380010440312018103031154540d2030101032004850a0720604066102c5000d20050340000b88131281c002e0459400400010441d5030b5141c0d00a06180030b000700e010b0014800c8203039000480d01d150302041d0407800190954404d2034491000070700c0c640c0620f80303d04002c074400d04104008008100c038a8154035600340284454104940002e144200c4812504162274108001c9030a59488007500c41d01e4a1207e019030400710001c0c1001070007028800c072600e8540d40035030049a0704500c0401d100c0e14080c2c0006051030030900350f8080c01081d000090110350801d01c2000701080d07049428031038030002c0c46943d9a04803980f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 61934256 1250 61933006 61933013
    0x60408030d0c0f0f080c0705030a020615010201020a08010306020309010603081c0f060311060c010b0a1d060f01080c090411030c0a0224010303050307050d1e060b03041109090f01060e04 81
    0x1035034440802c80c20001e0001001c440755500001c001002c21003403400101540711451041100e2080d28001441444005803140b44c00d500800d00500c150038000c2d040200e4640314005909038841c41f048580024511401840020300d294051500000c03500c0001402a40320b9a0b1036006501801c1d4010600305c002803e942148054000c914403103a1604051000b0b91856a0318020342078007103022031159101103107411440d00250701c2402e11010050000c03080f03e45d1000f22500c11004c0c02100480912003400090740e508041d8107500c85104181e50f000780f943c0da60002031303065402104140d9440782c0c841e200243c0c1d6800f01c8020f580150204542e459950514240c064902003003c2c690b4269005880d43c511240010000c08604403034240c00e00f25a0780e510f640b001c0701c0500c268100859101d280480101c55051010f50b61040c09021070000c0044a8031454180707203e000c01c49000308101451115a080d6007007143c41a034102c484841101e500580003a0503030300390380e220381002000c1c0c100e4030104800e1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 61935506 1250 61934256 61934261
    0x4050303061c0f02102309130c0f030c0c0503040b0309070f030f120e031507030e0c0a1203031401080105040b0a0c120b060d1a0f01050c031204020d02060408030d 71
    0x40304401c03050440300d28240e56140d60800a83e04080e104130311003c0800b50950240210107500302501803c3c1c545480c00015008841e003111203124042d19038903100484841d818070403888822210b443c1c0441500e1000f07070450141c030400301c0090030480300001000015000700050f00c054403050136415102c0c942a5409403503d00a5070008000d0564644c0401c0490703070342903206030100d42081020340b0310385070710005851455006007815054400c100000000c2c9500c90140c5015440d1ba603410300c0070103041510035590703010324800241d100e01c01398405c214801500403000c0c01c0500c01e04010800b07041000040010035026070104030103035150f4080000308100112003961045000c04104040111518000d0030400e0905041000913504c40c0c1c0e41d4401d540300d5040c1d406c001c03205807003409204400100802d00c08002c04059020740000d03042554550f0241054076082c0f40139000450408940c4094030f0a44680580300381c2c0c01489004004c00542c1b1154020f1001d040480020741d81c4404038020a801c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 61936756 1250 61935506 61935529
    0x812040b040308070c030209010b09031605010203040608090c060c03120709030b06060d1d070503070e040203120d0905030d0b03060a0b33040608010807080303090706050a0c05060405030306 83
    0x200014414444940c003a40c0039290801c2d1019124619498900030390300e603580010358001e640384c000040c0c2503821001004500000c0c0c0540e40e4030f40a942409002c002d4900640e4091780060000b0301155121710138081d0300140030811a03490281d0311001c43c050303510110345400203400020321400d0300e810f00c0081c5070b000481031900800c5180756894003110a0303000b60005100f100000740c0b102031291150029400c0042201c0c03a0110100c0b404601551030100380300300c90090203500c400140d1180d01e150141e100300c0d009005410481a40700003800340360b000d08800744200366201c4030480400c00400c05080900b103d61000100b404840f410146000320040c4004100360034001070a8403a1220301184840e01030003240d4680f40c0d60041c543c8051507c2580d04e5190101c004100010750a42c041d6003203040360a0602170300c925540340d403c101e86a00c4101c820100940c000002000914416001400034070924a8614131a80040ea00c0c2800c104c0d00f502c05848680c008410710040d846c1c0b600c40d511 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 61938006 1250 61936756 61936783
    0x10908060606030a0e0a051002180301020306150313080d0507031a100516060f0203060f030f0a0b0411030f07050a1e03080a030b030303040c091401051c05240108 71
    0x52440d0070400a4498400100780c2c089468031500c644448103010000c40c5e00c0c0e42e070b10209130350740b445481c5031182c02900080d00403407400c2c810100000c1d182c00e061003120b0148201401c605a03400b120b440e00310455102400b081c030700c40b01c05282d5801140030074002d403011b81401c4101155a003031505006040d128081c070400c2c26803100e40c116403100e5803070090000d0242c2003810250340700c0105c8180c05907000c034001006400d440c188500e122144480e9402184503210455600100c440d500e801d042c1c0d0394a64440c9880380d54407031314106001c0f074880384001e03501c03911840303a402d1071201050220303041030404601c0c19019404103205111a15003680c5072806841914112004201402c4424400b03109611001c1c24510002030070054452280e0040540003801804413581c90500b4070702401011030034443e4003032051410384404042107020205c2812150020040900d18044000e80716803840c500e0012142e910034419140082c0001c600c0f440340c2c01d0391130541e03c2c0e010340c549424603050080c40001e82 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 61939256 1250 61938006 61938013
    0x50d05070e010203070b0a1b0302070507060201022704060306020c03030405010c0e01170a0209030706050309060601031812120614011202121305030904111c0c0203030a0903030b040e0606010908 85
    0x20341d2990340001514500c0d504000d03000383c6a00d41e9030205004044914004144622024064601d280c0540083c107025101305c0071903000c10361700c8108a080b8002e04c83d51010303003a42c1d24150611116004500360b0f00c1b4030000c000283c050381d030b0f507034090880e0310034802c00c149500b01100b088144442031040300100742c0e031814198259484003000806991011800102a10051b4049400e00780554190740c1000c0c00901280c05182d11600e010380310f504101d0382801d0030300c24040091025440b83c01459a441440c0f0603003225201140d443c100440d032680001010000d44410102c01503e0b036000340c0c0c0041001402c0d01c8604104040010510f00f000e0b1801400716004001043c00290b6414290740d2111100140b445541a0f51410718110f100d850b03000c03580542040c2c08151208400c400a00a0b161042130440d6540031150010301691090120346000d03030420300c0010444042c641001840038401c0ca8006081060100003904550b418210007100b680b010041021650300050300170050003002009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 61940506 1250 61939256 61939277
    0xe010c050a0c11150705100606050706050601020a0c2909030a060504080403060603151b020601050405180304030b0402092a070201050c1005041b0302030c0607170406050d0507 77
    0x50036500c50110301c4020004422070640500c07208076000300002c41e00030090340100e5001a0100e2640e0805d120030781700350185044210780ca021510503002115026101c02d4101509034444200030440108428150f005141003007000030ba4681c0201c001e0701440a090a81c41008202295a1140600404100401000a00c29560f000030300280c00540c0b040c00440e00e5595454410721a00459000030325860400002100b0020000c0d5091512840000d0170400300c10002c1d01c0c8582201551084805a0020742c01801142403513041140c0c494440301c5050002c0680104461942d0300990013a961003150b01c0074882145441140d15030001c4064400e0352000d01606c1c02180c80c0c89000d1800b007001e000002d8031008690191040d981420301c118182d52164000313034102d4000d84000c940440d80c803202420345030b041c0800b00c8401407e80b83c011f030092100c000703601e0511040754088801519018240194403a92002e000000e10181c91030b6902c003038459041c030b84034000f52500501501e0522404000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 61941756 1250 61940506 61940531
    0xd090b090d060507020c060316080708010b070611190509040c091a0307180305060415050702100e1c0c031202070807060203071e05040602151b0a03020d02040e010503010e01 76
    0x1e2020034035401050000746a150300006a20302a0000f9032580c00041c080100501685580903418000d1a0b5072143c9089030303240701c01203d41c05400d0085050245040c40024049006644001c5845804078016403401c0e49024120300041003002000c000a20002b8000019041501030250ba6032550f05000c0746a600740444403800704600f80400a40c2d80c00070000420b500d00c642a0344882c1014000150760a41d12800d00e290bc400701102d080da020520b001c0094070070080c911134680300f620f00e40c0c040c04004001100c0800508107141c0303846010311405644801c100f9803c030b070050f115100d544811408010514001d0258001483c1e81945607206100c0340d00810445130895001661000d801a0789544a02c030954007129150340c0340310300440c0c2c4200a64195000070051060703652a400f101e007109450101c07542041e001301d440070000c14820185072034a070741d0800070380b01e2040725040140c1082e042200384801c80e00300c2d07409005200d040200400003420280b25806c80c1190721402407000c5c0c1080b40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 61943006 1250 61941756 61941769
    0x803090106091d1c0c06090605061e03060105190305010c0302090a150504030803040303090b0103050d02120c0c0d05030f0307020a02100807020c13110301140a050102072d05060c0d090b09 82
    0x14425a041c2c804c00400e60340061040010342072040c1e11010030081d420032800d1450041c1000c55116000710a8100340e0850b184031013036075002d1a14010000c00300750b170a10b803c0c080341d40c1041e011002c1b40d0306800b90102c005503007070041414514442e5001600c1e48070741700420400b904181e1000311031a60004044034556070000c2101c05503a044601265203884515040b030041645100251a0300d90000000c400c024011030402038014141c4d0868244100361900b0310301d82e10030b9281040e49507001c41140308150400d1841080104e00032020b503420000f0045003540c6580c000c490820050b0840501c000451808101d0345030003c0d001d20b0030504526006c00e02950f5010081c2c13042d8401c860724280c80da0783d04240c1e0050091600416503075612565a582940c2d810002c884e030840c8212030510020800c2c0d4400205401101c5207088400582d801d0401204241060614203120710b481a0801040030346440c3c1c02002900da412000f0100184061001803a0500981100c0c1c1d055508018290f0280c0c0c40c60f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 61944256 1250 61943006 61943023
    0x8010e07020706030b13140103061a060306100c0c0e070f050705060604150906030c0e06030c01020d0509131d070b0a0905060903102301090c080f040204090803090106091d 75
    0xb800c00080f17030711882c40083e00c0c0103030f0080e4044c0743e5424600f22800095030760007024102ca104840600004144c1020120408100408035800102c1480050028613003850384aa86030024101120b07410015180c03800a03241d40c1d048804031f04a04802c0c4a0013a500081d1807100f10200d00c0c0032400c04101e070fa142d913201c070f9002e41800d114640b260500c040c00d50071810800c0040c0075118081001d69503038601a4074174051031151006c0100301400250003070602050307030207030317044140c1c094682803480007002d94040d08142d1749a900413155256041781c000240c0b01e10b41c076180407031091030704886000b01b89618004803500100d4000100340441903030590003030b08000944000700e401d191103902e5500401d00c0c1009042d9440b00190824030450203400040b40f594403801100c1c80c1400003a81ca4504010035100396840d02800280f402002030404051200503a8015200420114035200152a001d4071904241c808440b81d1350355960030840d10700b2a2181581441c121000c100100f18003015040c1c41c0d050702c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 61945506 1250 61944256 61944269
    0x80304230913170a020d08061804020d170f04170c030717010e0d0f0f031103040308061c031d0d02030703060c090e01030303020406141606020d0605030303040b040308010e070207 78
    0x21a5070510030041c11655075440242c50f20400c54580050400c02540c0d140b04103407810224890a000c12034506182860b8081e10b07136242c82000d070031f8880da03082c444228030194060320b03000044030140c1c1c0b078500c2c0b440090032a40e1104900719295802c0101c0c6255560204141c0075440c1c1c0060f00042603901e01103010001c0721016a5503980310724111003810301404a607441c045460180035444030030b06030805068000741c0d24695402e01780006c2d08905400302c03055603c03c100000014130001e00028800c04801d0350141010b440d121840100d26031083c0d00204980048011034101c6514040a82910038440003900307040f1240c5c000c1c00250b80100c2d45500660002500690f100d5070b00280c10350180454200926854401d2505076075241001802508240a4040055080c00d000d040c0c22482d0016501400020b080d80003040c0d0803135580400a6004c0040d410245072038680c0000c60303070780900103184280c2c01400c3e900d100d460301d4503001b007c01c0d0058005000d03c008c60342c107101c486a400144031090320607 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 61946756 1250 61945506 61945531
    0x90b0f0f0301021201091407090f120f05030304060c120b0603011e05120a0b07050405061813140a0b0103020301180c020a02090403050c060105060306060a0c020a0306060803042309 79
    0x1060310101e40684140001309003a84c000b4000000c0314442a03111460b1039103207681901c5103440f4101c048070303160201e2040b03506103081600180401da0806c03100f00c0f040ea100e0418081c001400c0d0307a40b0360640d00225029103050b65a082e200e15a144c1010030f0301c942114200f030401c000c01a03900096107a02042c01800310403500b0308803527140340100009100c00b030f1400420035800f485030300c5030703481d40c50300000343c101c82c8041c00c1c4001c02d80090041d001d03641543c400800503401e245654420180ea005400c010303d80c440307050400300100103580e10034980c1101c0d0800d0708420b90716008103440b09a4032001c851504145c4100010480d0b03180303074009115a485421408102d58070b20880403450900009000b9500440c54010703c000c240c1c000008108035444201590000d83c0d8034010000d807070004841540c0c1001c020843c0340d0744240700784100160303644001d150603142c6c2d03201d4941d5002c564a5070040001e5031b00c0042c00313001800d00d01d0803004400c401c0101c803103600000c0c200441d5407040e026118848446 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 61948006 1250 61946756 61946779
    0x1103180f06040e07030e03070b0609041b1401090f03080708030411060a0c02040b040c0e060a02030c0a0302011d0307020a0905040218040803100f0e011511010f0b0a090b0f 75
    0x280c03058180341034018000c000380d44450700d40495010b84582035960001091400d0005405400c02100341c1d551141c10803100d598a039249400d10010040c001c008444200c848401d000c4a8880561010064000200c080c01601040c80000d412000c4a4111400001c40b0080410028074814206c0710100c4e4400c03215038a94845103070100303203000300e602c21640c0100003107000d04415a01520001e400c0d0300841d014440e05034a482444201e81e88284000e00042000040c00300c2424071300003c0034410302510489241ca480d002c1c1407030400800701000c0300141d44581c03155055066003c40e6156094180c40514507000140c3c1c0024544040d034442c3c40c0310740f6140c5002505550710b41d03201e0720800505500d40c080924183c58400b2103135000311130048402040490202c1c004645001c1102500ca1141c6205510390806207124210001c0904c0c4804002088186200c4102d00380110500b01b0f59151020a900100004010141c610358101040c1740d032030300c90009060317611000b0b000507508041e50700681c00c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 61949256 1250 61948006 61948009
    0x3060f03030d060306090605160e04020c03070b01170f070b04150c05010507080108060108071226070309090f0c051602011b05070f06030516080c070606150e01110318 73
    0x14000d8200d21008580f408000105110700c640049600b20b2045008124a5941c00540312a1065001d100000640890460096030038241d001700030316242a4102c90030b140c41955541074440d8260088180407050005256a085003041003403909103445002c1d10a090601e03100b0100b6004034404e002c42162118055643c490240f1a00000700341c002000b8003c5151036600500b0320042849080030900c1a1000012143c402080100545880380c0124040c180c0ca42c603a800306000d542d01001d00355010b40c0640349c04072048401464130034401e84507400036500d403908440440758031148a40007603081c0049420031542c810100c81076051611083c1c0c407a0159800102c807010001c400c103840b60300e1004002c206000c000904101198000c1111807851510760030120143c4600b1f43c0c50302c071180c4032301d13880110490060034034980c486580007a06051503090b0300c1d44425141160304c440036400700c2ca150345001710b40c4800c3e0090400028241080c040c40541840c0d40d59100300c181c030820141140030441400e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 61950506 1250 61949256 61949263
    0x210703020418090302070e060f120f0105041a060906060d09060b030d090504050c04060504030b0406230a0507080408030c090a0f090501050a060c170307030209041d0d050c0303060f03 80
    0x160064210784002c000000e0351040003400e030500241c015100e4903800244000301c00503031501c0b80e04090001c9500902d402d00b41300301c0c6902c01e00641440d00507580040e01303045003449014400e42c060600004d80310714107508101119000740070300d80030b0005082003110b5a111403085800d03a508001c800201c9e040c9d2803c01100400c08141610307414092026010440c0364400201d00035540c04440c10000382c1c66103d6966624881c91103030101203002400100041448207030700f40d0f80310307001d00004521030b00f24140c9800d90000301c035500c0a801880b001480903120040c8a900c6e4000e125013007500113814182c540e1030550000500304082d40c1d07400210b10401c1e88842082c480108412220015160303154003080c0c02908090094038041d80345420005070341e070b10a001c01102680c0060305915010030311110080e4a07400100f21005040e000c10142ca41a00c4500c50240c0c2c140da40c3e04100d00542c0e01c0b0f91170906090420300144100a410f0041c40d24124022040302d8100000b00c40d00c15102d40078030042801c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 61951756 1250 61950506 61950509
    0x80d0e0a08031905310512030309100207030908070e040c0b0313121106010306050108010b0312040302010503060a050d05010e0f12032d0907060f091404050406061503020c10022107030204 82
    0xc1d10080030310f1800c1048005c580d40c4d0582c1d00460b03156100c1d02800d000c2c030742d4901084943d1001c42d840700d4600b20707210100354020408140245440b1304a00d484500b200d03d00092580f003000c100024034100030a0000300840c580180000241103855410305a00c1180003040b4410054800f401e4050b070307682e10030300640c04041020409400d9420541e03403800c104000749001d03c01e40c0100d50070181c03149011f141c0070610b40c801420200103d4103003403c6030011141904010b12003500441301050100c0c155607034540d020151403142c0c0000c107403104444410b505100401c20050941e50280c41506008220720313080d45d5218030340310f25440030707136688090100698180d071511322802c66000e428092280340120f211403ea62641c0c4441e000c48101c0301d400c880701422032282100342c1140d40702000c1c0d035182581045070060b00401c0d01091480d22102e680a240b21b0702104480441c1d80090814400d41050001d45400c00061008600b002580c2c02110000403104480c2343e007645810002a5000f40642e060302e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 61953006 1250 61951756 61951807
    0x3050c04050c2505061b07030c0c0b0304060903030b090114060903010609050903040f06020c090106030e0f1b0108010e1611030c1c0806120304090e0106080d0e0a08031905 75
    0x440d00c0b10031200100304041c0c0d8003031300c050190f00e00050b401c0100c030b000140c0140c0480030580c0740c4078082d01d0481d08204c80c480d00726290301448500142e805030709400385005901550002400c800705203005804c854444040b9030040c4042c10040014807c003c0e00c0f030814500984106030743e0b40300702000074010103032a0010030030070b8600402d00070b103034000001030b005076400400d643e150180c1340d0350142d076030b0300703e4400841e07212400400502840788a5040220445151400c558410043c5078560341014103201c501d071440150314050180640e8885000c60040011040c80501400c10310707415030311201d980741c80c4001d0054a034002902050b04008842569820b83d05441c425841700080f10b5240d00000e01850000c3d20f40004900b40385002000c400c208180c00008502c0c11781ba102c4a0000791100541019455688080c001800882800180d0b82e01c40165103c4002d02d41d070008006d41181c064002c0084c80e4000d00108514000703c000c0c080508106080558952000c9009204045081c84040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 61954256 1250 61953006 61953037
    0x7051204032111060601270305160f050d02010f050f0705030409050c0c060f0c0c010f0b090709060e1c0f0f05010506100c0b04031403010609050a05010903050c04050c 73
    0x1d000c0340200034592030808404075116019075080846504511428683d0380d80c0100b000305000c0c0d07001e030170414060750342481c009440840c0096004640c07020f030740c0151800d4110900c510021402c040c4880041c2004054440d41c0c41c2c10240402d026528010000b414802d2030704803280c52a0041040d42c104000c166207440d130b01c80342880c2c015100d41151203151404c41c2000c01141502d42010180c0f41c40c0451031000300113076651000071010125000c1d1074405418420020641c0404007030003031005900b50114013045504211060045800000304494100096101c003406100e9026024845842084901e0781e000c13180d4103803841e1111410600104150003144000341008a501000d0300c1060203640200b03d540d95a205000f03000c0d0280148500107514140582d0016182c6000700340c00c14003c1ca09100251001c000b100310551007030300104041010124108241c1c40c000d115100a0b21080c40d03c86085491642d03560b80e07605448040c0b502c100c0e1a0000114500030481c02e07645030030300410341d5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 61955506 1250 61954256 61954259
    0x6090302161401020709020a050304170c250602030c10020a050d090f0501112113050601120b0c041508060d05010c050a0e180115020c040c0818060108100207051204 72
    0x4100d450a0022140075000302c01e8000b607420f80074030a80e143c11125272140340c91035941d07035901071158800c0302003180003074400c0c8203d4842550820410b10303410707404041c07440740450f05100a031800e00300d80d1000c021903000304400f001d000d001290070501c118240c00e025032910074030300e003e44140c042e000c0d04911003468003480c6801e00c000494032006050080340200040b040c41d50040f9102e00c207007948088402d0751415a410380c0120b801c3c030b160384a00b000d0040c1c544140a55103050501e903080e8045c40e1056001c14030001804040c8213103c0c2c001c402d540d120f41c5410300c0c00914040c5c15240e50b84010620501c7e40c00500d5075101e50150702202c0360300c03400800034000c2c80000070b00250411102c85001468581500340c0750b041100b0003c205001d40d10f00301071140e20b0000e4001240020004500850181c1455800076031594020440800407a4031000740c0c610708800380039561815220398901c00c0c1e0141e40108903c4a0100d41500c1c00c402d08200507070784600b6810014a000701440540983c031800050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 61956756 1250 61955506 61955519
    0x3060b07030f18030323040b131715070e01020c03060405160605040b1e0d021603030f021218010603051509010b03030c0613021f030e01060603180609030216 69
    0x4200c4100307051502c4007150340582c0500007034010560b00009020811060000c2d0403501440202d280e0f9a0622100c6ca152585a0800e44000d42201e03000c0680d030501d81000340041501428002038480440c00200314140c000c040c459403c04020380a9024400803004040041c3d1080c0049510904007030200c0c3c0441c01c01d41390031540c0d1040130010803100c7c0c0c00c0d40001b14200d482070b4110703012134040c5545a1f00f020b900b000680e916060144840c411108100b03d0b01c0c1004046001400701e688058821a0703104955007409429550000107843d450380c4100201446040030700c1e603064000c03480010710942d940640d440d05004002c2900054503a01c90a00b0b10300703c002d080d20a01d84243e0002c002488245111014190b8a028250801510740c100030005035446c0d60110010829500051240b801c9409c98500c5041120f40d800800380001d48800312049419024000d010041050385800c00030042e140810511340051400000c142a48500b8010141407081020064a500b04038084644564450 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 61958006 1250 61956756 61956767
    0x4090f06051b03010b0c07050d05010603020a050406080d08070201020d0e07050a0501091d060103020906070501150e011202060d020405040606020303010e220206090a030602030109090b090c1f03060b0703 89
    0x8880380303400c10303000401401c440d550840c00c603038868003182c1c196428002140865040074044402034032601ca0b00080a40d035a0800c80c2e58180514000580c44d819401481100c00035900501c0c0240d01700941040054400151403481c1035080ca06035680c4e03150301900b02d01910403821310b4a00c40f800d11680b60b001c0f2802041c2101103910840f108100d8558843c0103483c00c54040c4500a0607004010041010425440c1c5055019605250040c075102c0c4000001c1e207283c001160580c0c80d40e55401d07150000702484054407000d4010201d400400d0762405407200c03041490704400078060980400d202c00c02c8011070301600c0203440010410f204c0705488401c0256a0341013441107440d50301c400f80200d42c000240d042c90040d211248408000342001c250240702690303018a000a80161a560000003c00d103288043c5019018a01c004542c4507094104065809806800d00c0f4240e04035102d0300d00389070f4403040c0c0d001c44d844801020540019205d80b054008203940d43c007d000711a00021003004069000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 61959256 1250 61958006 61958033
    0x513020c0f010b03060115090b03011d0901141306091a0609070c030906080c210601020f06061c020607050d0f110c0904030315090e010902030607080f01090513020409 73
    0xc0084900304640c1800740c500b0703200e480310015019002040103102081500204980c000c04908054031103582d20030a42c0c2595100760312203035245c042803068000c011400d408181c2c1103d0204004c3c049030302624940c040c000c2d07000d40001980328100d07d04c8010000150010625940c000c4100011188a0607440c4024030007218801c2c8243d900d000050b102c5401b0750a801c4510707030145c6d00d40100c6800c00e6802c0d0b40d0309030044e0803250550010f01c42000c0301d9101c454215010381c2c030a12800c1880c01c082d03002a141c103a0302c079201100f40d0091010003081e91501b0301030882024400300d4081d451515800454010301c50380c0350290682c05207c0349040b40c0e6030422002108054181e4840901c080c0c1c2e2690983c80300b150b0240e403648605035101180c04644203820041c0605424104c00b00216a510240000c48004401c8000c10765142c10844066103424469030740c0c4803503641898061490401041d00003000c0501800f001a6501c40210709a403e503030105c5181c0603400342041210201d5418189401c0303000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 61960506 1250 61959256 61959277
    0x1b030106031a0603120c0304120314131503060e1915030b06011d06070609080c0f061608090d0507030311030c0304050106050307080d03091109040c060306050303090f060c07051302 79
    0x317480e421401039510904031011040040065030900d821310414451151808a042c0e0420034200c1c800262050101c0003418403d038482e41c04180140307448880100103540300440010f06103070100c00c0003005078801901d580141d26a103010440401ca05600f40200050f0801142910721070740b021017040050714206000d0042600d452014101c3c0050195050880540494001c1400c2c09410b0000c3e01036000040740a1040d80301d141002e511000b100d1500721418806200e5620031030600a2000f8030303030020344907201180303090340507442d01c0b201ca0740d5225100d104150070814006400424503200394042c1840d01e00900d0b240e41d8034200b64030355120a802c191001c1d0b559518080c00040c0c0f80c5030000380700084405a0014150074040e21506074000c0140c1c0304e0541d2810500c1c5554105581c610a10601c00c070300c9400003080301800c00c44000d0031140f03107400c03030b41c0280c2c42040107200c3e50391804248196040c0844400307550301640107076142061410340c045074202c000c158003000b598003150082c4ca0100c18 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 61961756 1250 61960506 61960513
    0xf04080613080a0806010903061b030f05011508090102070816061812050d18050a050706180302060d021c0f1406090c07050a0b070201051006050702031b030106031a0603 74
    0x1541c40307116000c010284402084408108150400701c0c0c01158490340c03081c01414070008507560380d11100c041d2214101060314082904d00b018980c2030301031154500d02e0008020800c100c0d0704140c18000320840806d401001d0140e803000054480c0425012200d00551028101d07460b00c0f0111900340d0100401c0f01c04641c00c90500c000038901105101110908542041c0d19038000080c501c81075855034890403014042640f9481d00f54100d4a00f408203140312481200242241451b034101142010000c3c1c100c1c3c0c080120900d5502d004c24105c210600c19660103c424582e10180104c040000b44221103c00028007092805031003440c83e180d0114048480c102c0007480140e01591400891510440e4019031083d6034a0121300801d456034050a41d161280d001c81d0440402d548404490388412259540180c5d140c40c200032650440819040c020846420f051781001000c0d4006a114142e0b22500034000750030040c40341865509400000066420004900c00500190340c89070f03900c182166498003912 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 61963006 1250 61961756 61961761
    0x30f080117070501030e070902070c0e1e22051c090b090603011206060503060c03040215030601020c0405040204180303060906060206070c060b0112020f07020405160f0c05030f0f040806 81
    0x150408441490030201c0e6025000c018203103001900103203106148140d561140b0070740031a00d400c0e08d20040c100240a1000700020318036104d8140581c2e48000d1100d0b1205031040f2411000f0000c45001301d40140c48010200700c040d01c500380b064500c07004620090054850b10b410100036041c00c2d4050000b5070785c072740c2e9031076010f948406100540344501c40c00d080d002401040101310001d05c0c0d41070380420521884000c40d80581e41c40009250800c140d860403c00c04000050104619003e003000c1c022890700d00440d400c62034081d002075151403c80c6501c502503515500001d045544560000142c80824500c0d0501c0400710b060090042809001c0da035001d92800748046042400081d62a205010590b10001200c0303050340c0c1d941c0a040401d259906110f550411050603606a0001c0d040004a944000d0386030300c0a401044151000500a001043c949003086100207038403101c11400c3e04d1560802180c1246a8034195280d4441c0c28544151480041120450251a0360061049400030400c079603054 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 61964256 1250 61963006 61963019
    0x2205060405070e220e070602030d0b03010504030507020d020a051f0e03010605090c0717030408120f01060516020604030b0901090b010b0307120f1d03030a1a131107050a030f0801 78
    0x105210340d40c01401d4031000c2c44007400d403000c1303e900f80c01c1e00003001c11907051a04a10f846d10016030003880258101044a208010482c421071005880c114024066410140c8000c0c1031072141d07000103809003500c034800b403003507440d80100d40b80188000741c88804090901c03800704044080b0004030500081104101300035030300d014000c3c4410f461000b80418080d84941e03d5038440f0394800b2608903500c403c81440e01c0700328030345000a548034034082c0300035030303a02c00c0b40360f10390180013100034070040c10740c41018014800c0035485000d803a020005070461590390321090000034024001c650000f0b20307e40c2250100315a5006c10341105800910402e0510785503600d0303804100e510702080351058001511052001c54000c00303030700261074403040500300003584100300201c006500450003c074501c540c4004240b248d0b001c814460042c0c190400b200e540b03100540c0c500003483c1350a9442001070229100c42681c109400c00e1421208143c2c0c0c004100c4464120030314004c1d01c0707501c0500c010408141c3d031100000c1c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 61965506 1250 61964256 61964267
    0xa0b03070302060d0b03160b0702041d2e051515040b09090a0605270901020403020612090102040e01090504050601060f0c030f05090d0302060604110f030f06220506040507 75
    0x80e40d074001e2980d410011404c01c042c004100444c2465410f1281003002d040000540c140480070340391000c4140d58401d5107005110035111100201d8000c04101040c80901c3c40020812120048800d280503903050090501e844248140d40c0e032210165180809208102c03900010f4008e0404040d207007071390881e01c07064210040380510320640d4642e0008100c91200c9240c031051699105289590001c1c1894950020400140c0e48001840d0500401c1040aa440c141050200e070b03c0020000258542421580401c40c640130702004c50020801c0000400c440700f0080d0140d4000c0e0800410a120360340e0b4481d418409080c090f1416241030298900205020344514070400d03d20019884000c030b07561003594120b80d02e810200d084d100304042803240f04802d0340c81c08000a6228001e80c001c0c020b506000d0108004c54049400719591018100040e120040144007501c2c2d2004008250036400d50300d0801180c07202c0d50151645030741d8500d41d00003220a1100783d201501070031040e182042283e80b00202641da = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 61966756 1250 61965506 61965509
    0xb0316020102070515090a0b0c0c161805040602040504090f110406060c11030705100908060609040c030b070c0218150a050a0b0a020c09010806042a060503040302010b090703050a0b0307 81
    0x315004050b01e114170314441407940740c0209240003214a581e5258481010f0b1001c25500340516200014046006040402403115421540003001004901d00700ea010f003601194020401c20a40740e00c001820f01c034103031781503c000b010003420900501c0d01602e0503401c8815800c00441d43c0402500000c40d40c3e04241c031800c025103249440c1d010028040c0e0f1a40140d600e00310b040d02c0d03418401c80d400842c00b51908215042e02c9011504c0301c00200341040e60650030130174001e207241d01900b040b030708000c0031425401203c0c0480740c10000c0c01d0345545851104554200030340e034019412010031080342c0c00000c5050b618078490006440d81941c8100f4000c208800004a4030441e81d11290902c42032240014000c01080820703c41d004070390941d9180004a0b10b44103090b40300f64002d400500800044c0403154810728941542d40710b10014191180800c0c01500209000d900c0c01c0000200c00a001c142c000d5100c01080c0400800e0a1202e15003414014054a400c6840c0000281031081480241c2000200c0070b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 61968006 1250 61966756 61966763
    0x6010b04060206130203190b0105031207050a03051e0f03040606080604020a090b0d0204090c0303021c050301090c170420040b010c1203020708030f0109050f06100e0102010f060b031602010207 84
    0xb00e621003030030889040c00d04e040241d0381409103d000d0701c00c2e41180300140719058894040041e46624000030075003045104025608144020442100091400304040b034065a2500341345440784010a003031803800259080c12030032107000040300003440c500345001d1880766200d20700a100c1e15403149019900c58400b501d00a42041d0a030b01c0030721a00921b0382000a030072802900240400140b030300020b00f0354020120960704441080820f0092650621089000c0300c2446190004140d4100005140d880140b02c0d41650550300c5c280700006904c51410078820b4404031246038a10b0400d807d102044920702c580855001c1c04010b1420003504180c056014107190584130900411640d8503040d1503541d01111000416a0800100000030401c60185006514588500302c10b9070420448d50700710b0302d000c3d107200760043c911001c10005503500c0b200c11030041d02e6840d18410030305810340180d0140c00c8030a40130454606000c00480c0340540310380918810001c48850b607164030640c103010781c00c034802c092014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 61969256 1250 61968006 61968013
    0x703020c011b0c0b090f011107050601050a0501170a0609020d0506100207120b0c04080f0d0f05030f0112050c040501090b03070b1207050c101104031a010806010603090f050f0c0306010b040602 84
    0x400b06144c00340b04d07903001200d031080d034028000b034407001c0303085681d8410441200d0f0400304155041c0301c010020306001d05801d0710000552070620700042c0108120442c0784100c0000320340000c5c600989a0801d40040000000030354503203002244450250004540383d41c00307600c2040c50344800910000306401140d81401050f41c003162184c541015041000f400c0c110b880310204030005800b03108100b9841400c03285009004101d00d902c50003002d0507041440b1004000c81441486200e494984a5904489144002d045c0170360b820700c1c080381400714001a1035446840c0000001d00412142c0080c2c8201d1403ca0a0b10304440e11059081c20f1802a01e10b1203e40c16024800144030f40d002c1d400900c0044400b1007240d4904815100f0981030300c00c01c0914400c14000071030200100b0181d048618080c000b044083e003000d6050500c04c03684e031901403003806e00b050340704c042120a100301060420001e0b500041503490801503038041c16a20880904030714044d10030342c40001240450035041d1307819559a540038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 61970506 1250 61969256 61969277
    0x903080703020904060b0406050307080a060f060c02040b0d060b031203040b06010309030c060908090a050f030d081803031003031b1e06061e03060b04110d020c0c06030703020c011b 79
    0x101c000703402c0618095001551201d0110b207000882010f0402007406d40c2d109592840c048000038045000605045030b69424a60f041c0210518240680e00303584040c41c143c9091070b120300018000c1c0c00009031854000805541003410307c1100d802c000d01c5007200b41c003240c010700303a0031402c0c100500c8112005442021060080f9105611a802201c1e2581c000c0c6041e812444660b1501822507960183c210f03007181c400912000707141800c2035185c00611044030b1545694440402191315404a907448204104400000500d8007400307000c4108040314a004503a1245041195007071310008d64002a00400c5107040c01041609220008100301039204004060f500440c3d901005601c9410300200c98554558001041c007100c0026561180810f181040008910b5814375200322008620f030680594105501d441c2140c0560044407100c103214080141d40f0070720190840d081003501809641d008200009101011780d26030007410455a0380d100800c80c11000440e89980c132444090306a000c115840386 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 61971756 1250 61970506 61970521
    0xf1a030d1e020304080607120b01050403030818030c01020d0b0306010b03010f03120323060909010e03041a040504020309070303030e03031504090c0e19201902030702090c071203090308 81
    0xa01d0a001450303401244d0415072103208003818610100c40080008041c0540d06e428010207014411300b601082c20014501411034a00820400d8003c00b10b030213503004e035034070090a00b0040003181c0190559900854481085c80c002401401d040c040c81c5129200b56000401c058a50710102e80c101c0d200f0707004064125145545000e400ba1202202d01c05260303036001c071054a5a0213402145c460310021034040b0082c42e000e004c020780004040e05200c1c15a1401d1444a1002c40000449094444040300c5040003070f00b40c0e121448500c03071a005150454000720902ca400d40001503c08240c9111340c03400d0101d403031030030005503a03800211265010030a0303100180b0390a0400754440c1c1c520b64091000100c5a640b500c7c03040e207000c10161080c03c290b41402000342080c0301680700c6c0540c01020301d00c0900c1c24070041120b9840324090845080e001c0c00c050b40300d40441c1402001123402455004e002c8007510310b402c041180c500d4000420940f42c8606e080701e0700c1600d512030701c00d4a04455240c0c07205c5035903440d00c10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 61973006 1250 61971756 61971797
    0x60a120e030c0319030f060f15020c0a050d080c0d050310080307020d02091312020607030b0a44030301090b060702090a050c1b0d1803080409020307120f1a030d 70
    0x104d00b455134840d07030140703286014002e00380580350a441e482e030090715051150480480d0181e00340304641000000c008a680c070210f40b881140c008031050345045403d82040c000c0c034400c4846000c103d00c1343d0400d0092094001c8081d521030a5401900c1040c40c0c0d803404066120310901c40d0096200c036000d89400014a412801150081048000b01e01d02105c1c0360b55200b00110703c8000795016034010000c00c401d0b0343e0305010744c00c0003060940700344000c5881c265400f41d10b450698a0303901440000b0a14200701c20880d600281102c0610b200280007101e45080c207170b1264004e0244002c15810702d80b81050900b04881210b28043d40036042507007035038481641400410025201c200740120030004404c0c204ca00d444503c00c0b030744400c0c01420114010f28009010b41106034a2107001a120003820808503040000740c408481102002594030780d00c40c1401c47d020702d11071032030203082440d2110780013808030141e0001e1412031550810b028041300f10303020560741343e008080c014001941c440d501c4101c8603807807 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 61974256 1250 61973006 61973047
    0x30b010621021606150e060d0803011401021f050124020c09040c0b0d02040512010b06030c03040201020a02091302010305010807080a03030b04020403020a0608090606100804020603070e060a120e030c03 88
    0x441e0401c4103d25030750311031043da00e050f031918108215801c01480002031030212580c00c1482205c040101950a5840150354041441181400883c40510100c0360b4020b006170140180300300d52441c0c0345044c81c102240105020300801d80380207400c48000b24201500060544107502540081c20100100001c006030110b00601c00c8030078003107021300020714904520140103003200d40c0101603183c604102c140322101c20400c45906075a0f0403d00200e0301516810103c980200d8421041a80c035562400141d20317005803564001e4005031408100440300b82d80e103e540482501c00d030703414003050f61f0750034841c1d0741c414043c060110160410a030b002e000900a80c002a22039602410240c24580d90350006086001f545e80040c02003840441001260782c0c0502100e0b40c481c0b400c0360024581094080020300b4076000801c024010040000031542c500d00030522060600c40080945aa40700491001001d00504140f4241c0d414140011964682400b0081e10f16800c5e40000650a11803c26014402003c1c070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 61975506 1250 61974256 61974277
    0x5180d030908301e060a03020108040206130b07081c05090705101709010b01020f06040c050105031305121b01060305030f030403182c04150c02010b03011401030b01062102 75
    0x2659510400c207255050884c0c4104900210001201c054542d0116130038001884648a44e83c0c15078180011b0380c00c40042c980060301074a0301c2d519002034040482102c41ca90f00003e0045e90003281510810140000602100034804042d0044468000740242641d070140c0d56410550810001403041c0d04007003403031120301075013131a25144030204440d111321691025544101180d44501482ea80c65804001804891040000800162501340c48a000c2008103011381c5041000010110342c066684c940c1d9004450740007400c0d1802c1d10880050713903e4942c0b2429146e40546001c00d85445084018806d500c12250040d002c3e6241c600e010380c040e402c551004008809018412010000f002540070301203018042c46210117894003400c7c2c0308406004044400707041038140c0d620408c0b0000c0c400388101c502c08014148046140e200001e0140d015090001281d50150300e090020184040c0181600303040700d000b4903c80e81c10741d032908004c85034030244800d10720440f0814110058068504e82c01009117880 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 61976756 1250 61975506 61975567
    0x2090303090d0f14070602030f0304022d01200c090a0e0a0c06020111190c062003040b0f010e04082217010f0c1403060f0405180d030908 60
    0x40100000b8420008010305941601c03805030481d003005030780000b00300a968810010f007001403801600035683d12402103407601025001c070100701151108040b207000801c100e10070055218082d00185410801d0031603190010301002a8084901c0c204070480d1811800b59005d03000d100103042c284150703401b020300110019035484880701c4034070400f80050031500f441141d152400314a070440c000c1c02c0d41e200c03038002d20385240f04008141f00365401c007040034514a080d05100144007280e081c44401404104c00d07104040c0541c041005201c20410000c52003544500c805080c40d0300c038420540e80c0107200f40540c014040800e00440c01140444000c0e0101e014414082106448501e2407010309421950211564200041000802c0c81013801040802d00c0071603010044400f030100000d2200d01800014030001c117001001c5070f02034403074001040111a0281050200f4100100b01ca085040005400e6601d40071710223842e0140c510074000c103c0003d800003416428442910f007400780007400b1041040704000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 61978006 1250 61976756 61976767
    0xe0c0c0105040305030a0f0c08070c050f10091704050a0b0708130603020c1504111017071e08100b210a02040915050310020903030f0d0c030c0e100302090303 69
    0x10800d004942c801c0380320f60f403940d0300c2c0d00f081c68424050300e10300f8215810321400c00c030a030014554440003142e0b10650600c0d05a9075070420b41401030400c103001e217460295014054043c05010740d680c0204d58003602c80d02c0101296010700005028602840c0181d03030344550120350400038842007402134003106005140b510320385001a0b8600d081030499a1080c0701198000c2000a00d0240a00482c4240341c1e44000801051a0a503207046100407068074a511502c420380000241c10b114414100041d0841581c00d1440d0600b02c3e4080c0003020307542c1002108181143c0c0203200107202d1100d69000e4230250301025051401c2c800e000c4042c0e089581d01000ea0184508240c8030702c0c2e64403031058018100300d02d0050781c403130901d100070b03007581c8000600a0180d0100c007420043c548001a640303400c400c880d900107844520040010781144650403070000340c1c1030049610855020a50f0090030580b034592020080705e000b01c00152001006a0309040d882598107035241c051500a4001f0481108014140c03441e20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 61979256 1250 61978006 61978027
    0x320060c0303010b07021810050406080c032104030615170f070303030906330b0901050f13031202010c09060813020904051006090e0708120d11040f09020a020705040b01090e0c 77
    0x247d00322030f03000e582038103c03c1c200100d041034400d2202402c0304801506904090f0390101c3e69460b045418101101c080102032501064100251406103502003c02d10020380682c00c82d842c0c1c50554040c0f00c0140307400c1003950a5aa070005880c4642c000d602c405803245a00e161404d4005120142c2e066500903240d20045080c0700e03112514400b400304004100d4503107019100c0044000b10701d41c20004918808000306801681c1000c15a02d051100b0307420a56985941182001e901c1e480da44014480380040c100c2d13420154043d00041903054003652101801592000119401c901c241c8081c40d803685060051000340c100788080503446402031080320701480c00c10042c40211902c80c1e100440d1190b50303e00740455142d081c00008018081c0b207006080584020407004100d125404920120075030f5404290400800300702514002c0000d4000044040e81d80c07002c1c20065401000e440c401805540400b0900c0d01d09440341030642407040c2c0d03036041501c0c100300c5420b22440c8007070b04145040030148040b1855 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 61980506 1250 61979256 61979299
    0x60b06091f0315060206040302011b0905040b0d050d080703050601081003140106081b030c1e0d0311100606030509060103030f0e01020a15060501120207050a080a0512010320060c0303010b0702 84
    0x411326035009140ca86003600313000342140c40b01103082031001c244440d4040d04e01d034440f40f50310560720100c0b0009001c5410100159000a03001001855805582481c66031240c0010704544510303250784040c0480e80c1c07080011502220115145266403070300ca5402c0c00811229413200c524a84c550000040301511500707594505110301c1880d00400d00c0540c81d001c42802c050003002103044047e201d00a03504480f4402542d0300c900c0303421250080c0f804019a10a2520501666030641540002c1e82e0322503080d44c980c040500034500a220201e414180440c405038130010f162412250180d680403820200518222008624121580e0443c8a501e0511001c10480342c1070041c405c00009000420368034100002d4242d2214140144540d441070100001181d4080f980d1403029600c004c00c159600c14a0b0b409491070300a84030410101182d00c4004420401c4008200c034189107085551404030101804100d064840d652005010b82c00c00c4c00100f0000041c000030303045241c070042401d0007031014518030410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 61981756 1250 61980506 61980509
    0x20304031b050d02010e01020309030405010f12050c0d051e07050306010207030c08060411010801061b23060f010504020f04091109030307121209050a0f2409060b06091f0315 76
    0x7043d0304024020549944c0911803000c600c01507200950841c030300860b105840f40614401c2c01d0501031023021441c10320b481000c81d184c035136180800401c00c3d41450800c00340c45412403924500560300d000701041044400d440e203544d4081042d001760708213a0700e45604503015080900f90340c5c15485101e2011000400161000c3d0203031a07140d0081c5218606400c05005030000902d020f03041c48500c1c1c3c010700000c2c0d0700074403032800f0820300c8200d034200a1151030201d01e02903002c52050800bc103024000f00030003402103a840d00440c3c01284044440c0d0302c035401c00049101d080102c8554110800c000c0200085a070850440c00c041904c9240c01c0a41c5003001c40e045500000084070065a03003000d480c04150850395804030091208410000031071141c0c0c0c1c9555072005218041c002c0c0110304c5103038003080410320340700701c04502c00300080003200c940c45050301c050300381c44804179841030511842e9000c0e13040800641d0290000101014443c842a02c0c03042c141c08210364140c7c1c03c05807644a405140710300083c5620 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 61983006 1250 61981756 61981763
    0x220c0302031905070210021e0301030f0b01270e0a050d0203031e040305120603010f060801060806010e09071206020702031b090703050f1815040305070314040b0409020304031b 77
    0x69a0703142c8281c0c180b000c80740390786002d4081407422003484000303980050403007a1000a160016540d60150108901c0448600e0b1500c2079200e00000110400c00d0180c0d440110030310a000314241070b600d422205011500700a0040200354942c1102c44840d1281d81000704503402c808190b401008454a8085c10108801c03050005a840042800320051542c2e0146c800c0c8004510110010308113964010211b01c5240da03400020110300002c1002582c0a50042d06000441c24082040da030755060340c14040c1590b881440d40c07034080c0e40000103080040041d03a078858590500544103082c2841c1199401d24108407094811075030905c110401131304c0030080605280f00d14451618454100c10421509040080c15101014107240501040080c0c0d00421900001100710014411382050400d514202c82d18440d620320318544404d03c4181130300440204a06c82c007907a0f625003008556007507600544030710301c150070040f00c0801c404c018000d40782e0301640e046840391400c0f40050800d1001500503c0360141c068 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 61984256 1250 61983006 61983011
    0x11103071d04021602090708090a03050d150806150f0a0b0309032b0b011b230102030a060501030b010f2f01020a02060106030b030d0c080a020319020d030f020304050c220c03 76
    0x540c5884004650300c811949230502c0030b4030b0847d0065803030303951f907020003014010007086e2082c00c0081030b00050040504100b21103c0030750390704c45690b0384080a8500b000b403e21440f50780c07000c13400d201c02c60140301c03080900700c2540d10f45850304070419588010010a400d00041c0840724540350418110840c94181c10031082510108100f50022100312001c034034180141d04c4c0600d80103100040c111410150072450740001c4030b41d440e4890204811122040c05c1e40e510000130021207440c3c07507004038151402a81c04001d10605140195602040f08044ca80400c8030a0184015000c1c011401c80c0050200088100d01801c940c1c1c4903403e90f0002d40701c200158025030010701400c0d505104040292404800410f4149200000a4401c03280c0b100302034450400001c408400398020411140704a40b080028049180c5000d030003516080c0f5141032000003824408a4000300111340280c030f002e80d8201000d00038003001d15040000d189141c007d60f04506d0b2740420f10109a1841d44500f503400460394501 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 61985506 1250 61984256 61984297
    0x11401061218030c06090201090b22080d0203040b0309120408030c2b0e0409020d0b1e0106050a110a02090106020d0806060309030301120305121314011103071d0402 72
    0x10340940b1400021032a000d1020802c60021992051100459641100002511650364001250b00d24150b402c801108003000445c103812030341100b901d9003083c0c0c02c0004c00316080d88509496868005800790b1000607401404117200c060061001941c201070300c842211080802821100620b4005a01108081d040444c0036900303c02c0c02d1001000c00050800554901d0b072071a1094418003040c529039908001040f49000e200391216800b00c08a10b400405060114ad214034005590304000c892509060b0980c4810314400c0080f40c0341c0a050755850340b1041d00b003001c0007200b100c5a40d0740035040041c0307100381c1c20500c1c05030b200d40c48158081c200c80d501030141d0502c00d8602420000016149602070141001089106440441500d0540f59078041c81c0180e4282403c0c00c49403400703001294100242d103802400812235100c481412010300c5811882ca642000c000540d00303c0d40c00034010703094000104001021648030b00c0c5000d60300301c001254108500b1660000c02d0484c2c0002c0c42900c2d03442c40100c007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 61986756 1250 61985506 61985537
    0x80f090c1c0b16020304090b0105090406030b180303040206070605040f02040c03020a110307020310050c0c010e010605100c1a1306060905100506030403050a03020d090b151e0d02090901140106 84
    0x1c40a6029020040074440400f948500039900d101d58481d0400b0f8654401030703410144c2c411822110700348030003002401782a0300d90a05040c83c62080d502d580c0b02c0304c0818074194100401006036407085400511081c21300c80c0a4440f031f006004018421520f050500e0dd0f0b60740180da46104a400b1480f00d540c0050b11002c1035000500b2040143e000c50b181940107000200040e23a00040b402039007c00000007150350384070041040c489024000644003503508040c0302110481c0150700c6a02100c4080344c07070040780400110103482c41d0901070380190000b0015030705000d490041001d17180d0402c0307545000301c040c8100754070b130741c8102c61468114501e0952240248540001100210707030240c44110344052460801d6a80600140708118900d0203042e0049403101401c00503900044100b0f4101d0080e22451501442c8000c40704403c0d07292a208009403a48000c01106200b03c42028200c0035000c807020782c0d00c503000c0121209006041035660364a0342e102030003540402011a0003092240c840745213080d003a00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 61988006 1250 61986756 61986773
    0x703020705010e1503010311040603050a050f060622050714040e0907050102031c0b0105120a050703060905010810090503090301090305040303090e160e010c0803010f050406080607080f090c1c 84
    0x82059100e26101312158010301d4080e800c803030440c1e90142c6284a00b86100020601520403075001400301c0c014189083c06102006c075201e50680c5980081d01c03415a140710411140c070009903c0e200c1c2140f034074075007688010352940c0111341000c3c843c00d086403920035540680500e544160044c11552400b0400c1c000601020000304000e084240060f505110310b8085442d020b09803500c112002a0300c4041541c060f9004000b01d03845003140c0410b8086030b02c2d00101610191000340d070a900020310705000000e04040c54032030350307041e100581c0c050507200c0090a002e0014000c110020340303907130004101c030500030340c3c0034820304252500c2621120b864504e1424040d05101c041d42c062940c81c0140420007603484908400480b0711030035418400d010090080c0102c900700500b20300204000e1340000040344440403500500101d540440d002e00845480b425010346a0300140d8480000c15041000b103040350141104850380400e444045500c1c90b5240e00010350b00d4400025400e03244210004101b0600c00e003c2c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 61989256 1250 61988006 61988027
    0xf06140312180d0c03120e030c0103060501140a090f03060c110601030507053709060b090603220501060306091109060f1e030303090304090516080f04020d08070302070501 75
    0x5407002d040c4851269042c062010750080d4070f2181c00007810714800c0000004c0764402858101c04418000044400c01074800340403610200e219100b6000700d0500740d072080c000c100550310181d4920751205007101d030f141426000626081c0a0003081c09020030714011089020740150300941000c94504003a0380c0240410040e5910300c039490300080018000303d900014407d08464080d96603000d90440391701c55040b20844000c40d0014181401c0c0070003681c0a0310300d65281039420513101081090b5455490000d00e100350212141c0190061000460490300b060440c01c110340e081c0e0000c2c580d4517442d81d0f5907003121001c0d00110b6025a031030701910240401455000301074603060b6860b44060038913100081c0b1390201d07605414441e000c200300c5880c2841c10405015a0a28050201c13512428103060b00340e21b03900075000b09032089140c00c0c0004d141c01000e1247c0000906280c440042c90380f034250300703200101c000500a0fa000300c4641c4007540010f01c1c0d0402064580e00940c0070308111800d00e0001000344804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 61990506 1250 61989256 61989283
    0xa0b060603010e040f080702031b030c0d030921050706030f0b06040b03040605060f0a03080301030215130306020a180603021804050603031213140604050c090118020306040f061403 79
    0x61005101801003005841e8006801078551001558545400b80f09031282c400000d4146c0280d03020324070480000f0380044801303801141910304c07460001d000e01005166403038002d40050104fc60800005240c48001d40c04145082040000d0020540358585865003c1c5c0c0480006603480e02c0c0344842030514494900790903803c03540b03d45810b1400700200424007000e00701a08160743c0380c010404554580c001c03008010f20140280644c1a917a092006d07050700244070503405101803040b0300242d1041c0341e040710301000e84115072030005400c58840800070342000e002c51007484a11941c1641c40384400540400829080d038000d43d4807100704840540c41d100d512000e5004a08080034002141e4000c403d89220f0385004210f080b4598880380041800442a02c001d449420a4001101e8807000401e6040c403840c000c4044506403107408080c041c01d81c1d400d1103007071080031840410801718102ea400458005034002c20100c0d42a02c0303c480001281c0055101d4040d00100313030003060f250700b02405030000100c1c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 61991756 1250 61990506 61990519
    0xf07050a031119030209130311010510030305030415050a060303020f06070219081306030b0102071401050423100f0306090504081e121302010815150a020307020d050a0b06 75
    0x6140d5500041c401c1105109101c0e51100f44403800c41e00c281c0d6420300080da001841c808442c103040c10700002c00110008183c00140b900d50090b03071000340501400e0700034580c07541224946491038404803800d4001401c1120064003640b442e2110307804034018240510142103002454a25614010745040003000301240950400303801c020900742c003c600980c26071040e07046000300c1b01c81487c14148504c103480890b00c2860b42510007180b03080d031581c01070b0b01c000000c0e003c64034181e403a0b41c055882001862101800201c0800044c4400c0c000c141480c070104881c00113241410840100045610f800400b0000000e82651315500703081c0d134507004001c002c01050700100032350700b040d440da21101d1085280c0080c03440350064240d4a0b02164034101c1e620066010141440d5042c007100455081105035016070008480c0d4010546400d030960300e040c0303000320042400140c84010b25040615800019a402c00c0d0300080c4100d60250300e42c03900031a0064490805403030144102d04d41aa02c641001d03181e10700800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 61993006 1250 61991756 61991759
    0x50105100305090705090703020c030c100e0604050307030507020406090c021005150102070b0a09030b1906060503070e010809010b0607080301080601090513030503090102210f072c060702040606020f07050a 90
    0x2c602180c984c003540c0040c0c5002040303540c0c000041e4082c0c459142040c000744000907500382d0070000400c008500d44a0410305110404040458640d507034020345014040390010040080085e001d540100700c841d00c05400440d04a83c1d6540304021910404000d00242c0c10a451504008400e88a01a4040003050110800e00803442c0001d590742d031903000c1c01058000028114101900454041e00215441784103a0107914101c9000e503100914880d10b043c409041c4500480c510380a80d064a01c1850300369916614600c800004554003d400717001e94071155a5941510b0246d102c4500610ba1075000d48515031340ca500d001415440c00030140d100b214000d1500040c84642400b58071405850b0b601450055141d0b114410002c2c02880380300011518111400c1030010001c48050040d03101e11207c2d089030f803c0707550b0103505030307680c1c00d0349100c070740040b1142640880c0a038176480c08081a6100545814100000c40d17000c2022990f0342c1d00a02c01690124217101d50400080010b039000d040155039020446 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 61994256 1250 61993006 61993021
    0x20d0903080d020d181a0105010c0201120905030a020a0c0909050703030807110601121101020106030b06061804050f0105190b0d050601020118081312120c0212010609050105100305 79
    0xa00d010003440000d00241c2048600c02c20b0b015a03003444800403041040224410b03085042e6051800d0484140d851081e00e04591514100e80c64101e42041e15000d019200075801110b4490050390552074507507807211880c011401c10006081b0b2101741d42c000309045541c60414100410b41c43d400740d241c0b2030412620310005000455240c2c02c41e681070600f4421525003100665030410b4400800030035106210000030609164600007445030700500c0891140010789004a00ba06e405c0d002c00b6040401ea0f5000c5171150401e000242000310302410a03a01c046464800601a036001b13136214070300e000c1c003034005021a03c0d1210341004914a41107180c0c401e0740ca05440303040640158190203110560395000078210f80d0003900890000006150b80c0003001e00c4500d8004119040181c4c00c0c002c60030003c0d0041049040e050400d408150811140c041410103401e086030301c2401c05034201d80111282d1042503014800340a032002514001102041da58101014041404000300000c81058107210601c0120b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 61995506 1250 61994256 61994267
    0xa06050f06160311031210030b0901290f0d060603050c1c020d02040902060c01060306060b0a05040311150d0603050c0f01051801231b0d0504120614090a12020d 70
    0xb90f6260811000d1410f81e40380d903d045004048034000b4450390ba10401004c0b03100821800140c3e4800c1941c1545901d9101000c0c2c00c031205008014480080d002c6000e8806080c001c0381940c040004180d8610018a1004203024031040c00d81203030940d171225402c2c800c0001c00c0c0b00c00015503170b0a8881d00c000c568510300c2d8000d01204401301030302440031030240e8400d6480725001100d1068019201039510411440350780d000300014030058840501d0700711b0200d6003074142411210a081296103450130036088d91074030414039120304003040d440b401100e0300c24591304540d4042e05034461800740009110b841c41c20490309007851083e0305481416140e605d52284d030781050654910900c0c403006000c0c1c00e500b2400580d03851184501d50080c40c0081c18441c12010320101c000d10030366030b03001c2d0420080418417480a03a5160320b181c000002c00e400784010b00942403400c402402c80742c0102e40105040309401402c064070001030381d0000c9a600800e9490b4103201d01ba210388040d14204c2d2004068800044500411 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 61996756 1250 61995506 61995547
    0xc0901060804051207081822020c010b0d03090f060e060304080901020c04020d0b040b06090105040e1308040308071b0302030613110a17070806010602060a0c050c060a06050f06 77
    0x240522100801c062010402103102c128144c40d403081e43c0c51100f0f003400d4a4070340004241f1242142c004280d2181820071100c000c550008428600c2d15440506040300f0194201d0f4100740401d660b40d02c0401032683d188104440024000c5d2550711301542080703000c192031071207504603e040c00917010409916480307031801c60313038016000190b054032101c1010040b41002c0c00203407030340c0e0b000d40003040c0d9510001c00d070703030041080c400101c404100499800040c04002e0195440070350104205100c20050036100b20007466010040d1044140045a0f543e103047d0385801c079400c252502c610200c1ea1030100304500107010b0b03c01640181c80c001c400c0c603541c000780c1e030b0300002085c01081c803000f48242000c003d0b0307821540341d0300b66008043c03a5201c1c1c0c13217000844245c0f0b0500284e081c00c0c41042000100c00d44007040b806c0c10b0701c0e00d03603000d4030490f03403a1081500038145100740082040300400a0b05061003083c401d441c007884201d01c1c0410402d1400c410001c088003030081761f0b03216400c1003100342c962b01c50001c030111 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 61998006 1250 61996756 61996769
    0x30b0609010c03020f0d050d0606170406022b020a17100302061c0e0c0102190b0a0911040c030506010e04060f0e04021809010608010c0507020d020918070e011401020c0901 75
    0x42102c00070302c0c040742080e2003c01d50000601c1074101a0a940f0b4011000c0d002d4086890420007843d80d803040c04882600c41c40c041813120807451004200400e580c1d40007480c14401d0070940010381014281100c1c0c01d920349540c3e0461003680402c0b030441c10799005110010798001e0000060b09414004007407002c1604520000380b00d20310000d0b251b00001d07032001c2140d41c7c4055103001042029030120710191a400b20b50111130060081034080b0303600d00c1d14004441c5d201074200d00382c07601940d2600c1030f02d401404058420368083e107078406c00e00202e994030701840744400d04070f98010810342000d40000d4448100c06004c00c3c0f090b410420140522021092504121080c501075004203440b14004180d0952000341c6c03c803440d40d42c0404016045005401c020100c447c407200070030078601c510104072441c0c081d4100095222072402e0407107000d803400d000e0f240d40240a22000d614034880031013250f07240148941c005214080350000411450060540030006c69600303001600161050000240740f1800500501 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 61999256 1250 61998006 61998017
    0x813080d0c02120705010b0406080d080112030302040504110a020610060203070308152701091401180b090a0905120f0318010212010f03020906121e031207050403050607030b060901 79
    0x9105144208944480350040c030030f00e03960320040790510f01d01070001090510301a5081203c002408400040c0c150404800799680031b01e540d0820034250000d0b10503070f50560826030207020114181e0f032180720b40a5018403030b0003096a244924540a030030528003c100350350145255804020868011044076802c981c145018005a52007003900030010b50443c09841d0040e1145100c03010340c0916a20401c0403081c0f0f0144401d507030307aa444411050795a000030846510090300010001c5014000800003031508042001c0b641011850108003603450440d00034180e00c0c3c980310a03a0500c68140101207001e00f02d16443c5181ca080c404601c1c1aa200141c40b041c00d5109082a10804010a50684290f160407c540b00141c2d6511b20f0948681c500c0e40c00705138441c00481000c183c4920308801140078210058010b0020221194002401c4c4203114898540c00e00080042440c0140000703c0c0138403852041d00e030300d41c0342c5003181041460008024115824107250400319200d680da004282c0301800740c2440e00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 62000506 1250 61999256 61999271
    0x30a0b16020a0c06020102041d01060c020607020102010f0e0601090c03050906060108090a0506040804060f2313030812071407031704060e01050f07020d05070c0909170403030804030813080d 83
    0x80b0314001c0c444102402d088416000420600e9041d001002103c8a40900310f0507001d20000282d0823000c20303ca0740001c9600c4d03a0354403005042c0310300582044c034014000052030401142401c1c0945070618001301160b0006401400411780a2282d03d1050282d440d04100700c2c41d040c00d0141d698070010308001e0500440d00e0028002850801042e81da541d40201554040c0c01c0a1a00c500350340c1160082601080144d40d51500c141d106101d08c01e40450120350a03e0009400c02e82d440f01c1c0d91107001c103020051300940010011903a2040103018034001100c03803958502e010a0020882c1001081c50a0700c030f8000c11082010a81c05486c45217900c0c001c2c0107101d80b0b40c640f440d07d080202030788000b6400f50b5080108004d600c41a180a50344038503d150261019490340c0d0740c0c11038951084500080042c4000d000c03d2103408031030791120083c80e11409815800c08050f10408a09070401e074400c400040303494040000301030b0b01441254020000b44d114032043d014581d04c50703078a402902c4454034410745d180300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 62001756 1250 62000506 62000551
    0xc050d09051213030605010b160312020408030406020303010302030c0a05130b0607060e0c030705040516081005060c07090e07060509010810030605070e030f06060102061b09060406110c030a0b 84
    0x301290000a010445039030b2601c081c96090074030790501c130560385140341000010f082006c0d2411030360f083c0600c4246015030f150766582907481841d101200d50410380d080c440400c1c0c400d400c00007400074104d541c0046840b0742c03540c07040500e00003018040c1342c02036409100821003074451580380841c0031044000840e503003083c10b011400c18000c0305005423006081c60410720000303002081d201d40d00c0c0016002c2c0e80b40c06481c0c0007408141e840c20b8800302d5080200f0525409860310500c0026006220460a580303d5079440c0300045540d0010149030000303411400c000c1000004c584210f207940702d6100301a0118900d00312000d0594000e41203010b0502545c8000207500564018020014540c002010040f50401d0503000341540d088102d0b95000b44182418041003103c00102c45200361016801810b0941d5407207a50984c0280403c05070032210400d1002641320f0707a90001800107440c00360383e01460b048100300754a01e00b000002c49a400303500251402c3c00400c6158000c143e101c095414003c041000c2000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 62003006 1250 62001756 62001763
    0xa0e15090a03140d0e030d0e031005040614010f0503070603090f06290108010509070e0102070b1611010c1203020f09030a150e06010807030b0c0f0307030b010801090c050d0905 77
    0x80c850391000e54820080100410310a4011a05558404568400c020303c80b054800010641140c1e0b8140e025034100351045100310a4808202405000d0b00d0382c840c0600d1201e0243d50080d01c0455409880d003900703021528081ca0558010000807101000151030000801d40316a002d01075041016140c1c85080c05000300760340881c000c07030707400801001200c09041d10140b2000390303440081c0c0440c0c100b0291561540c0325180d00780c141c410040c002035032910748100903602503550009071411750094580014079905040c01420280b00910003404103801c3c0d43c5440782025000650181c10301503070051000108951541902c062513060a0060392861a00c0c2d0420941c010740c0030560b85489051100d0302045403400c010440038030b10b401e06120886201c040b2640301c1c01d00340581d01095000b003804102050f0400307041c98000d05440210f0386000342540c001541c0b54400c41d181c5010a80301c0a51449650380f182c850360040001040401a000d0152070050141c4110254810400d803601800810700c1403d2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 62004256 1250 62003006 62003017
    0x302042a170a0f0912120605060403050c0f0d0803010303110c090103050312041103010f02120f010317030606040518180d09030318090501031b050d0201050d020a0e03060a0f0608030a0e15 82
    0x40005540300c5d110f10700092090020420707600145080100020392410034005031015650f001c1c0140c800c0092802c140089000e800c0b0780180d00ca1011013200001c503d000c8000e5001e14086d035198400400d8002080e80303042d032003c0009018851340001040800c1001c004d0740c06041d04101c65403110740b241c0c1041407082e20642000e07541546081104851a501075008104100341407403400b000e0358410001c0c400c0359209220141c490880300103900c02c401c0c0c2c4071009540c442030050029082949800103e590100e0402c0b0031100b2041107014002d29452011100305003038140e600a00312298450381c02042c000c0c0c01d20005080c0106800c00c080c1d01d100c6088000007a02000070301304502d40e520704003a1842e0070345e5020303009241d945032004111800e042110480c0a901a11214a00301d106250940298889180d4404201540509c0302203a0b0341801820300440e0f941074081429408424902e0480b403495003d0561907004001810005403c00315a98a1040407a4030058194050740c00c0003161044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 62005506 1250 62004256 62004263
    0x4081b190608072001060501020c1f05070611030109090b0a050709060f02120d0204031e050d08090109020a090c110a0c05010c0c0f0305070e0603161e0302042a170a0f09 74
    0x11000400a0300150b0003070f0107c84c7c00741c0c02c0f28050307002a424010a00e8800c04408405414030300920300c0d9a003d04010b141c040e10410000400910066002c881ca07002a04840e800355100d4061200380304003102e0035504115801c00030860781c100b01234082d000740420310130b4100b8051002c114000c558028404001409400b0310b4403661810746c03a040100940c41808200c0e034640c5031200d040d1a4841402c3d0040209a120000f40f035040c110520984403c1d20041c069040b66407a607031400c005071546815000100b241e10380109440c180e201020300f1601c21a081003c03580e000c00100f1010414020804084171420308104841d40b03a5420924210a0560040701c5082000200001004800512441181c004180c0100191240e90815456101d40000c102c2d070503822400c148051400044000301003000c0d1020881302c169070350701007400d40c5c054240303000000f05190f42c1940c103c581004c5041007203801d440c1c07511030009101118104541c0250004c020180d4880981c10300201950200340c0c1e082c1c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 62006756 1250 62005506 62005547
    0xb010e030a0f030f0c05060a020d060302030a03020a03080c1e0d06030f0b0601080a020301080606131e0e0c010905030307030f02010b18072a0618020604081b19060807 73
    0x5428007240b400c400728400c50014903400d00400d101441250741c5440d550341b2002400b09910349150f180301a4100c13041c2ca44500f41d40300310020050f5810809520341d0391181c1c026016003030035420081d1001c0340c000c00140d21044200901c8018840c08202000144030b0b08a100e0346604e004611000140b040b60002804100f000d01303540705101c40d411249215550036a5028101e68900360f03000c080c0e00003881240e00907070107500801c4281c50240504400343e81882c00018482100158401120002400b07069903281d45600d9504002c2c002e1003d6611348100b801c00c1888585414042680e0b0f22902d01d0180c00c0021401071041024400e4204005440c0001c000200ca590070845580f450107050700c100b00812807001c10b0460301c010a20180000005d0002103046200d030b030307841d4103010705407149600440940015800e0010f070307282c1e805807000e8a1441b005003598004494405060442e0f090503600c24902c901e0b0f1801c00414443c24082925103500c1c10000c141c841a00a440b4a030410040341002c45 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 62008006 1250 62006756 62006773
    0x60c140a0f0b0702010b1c051006090b130b0a05130f060905060f010806010203040603090312090303140109060b04090b04020c06040302060601090b0304050303150a0b07030302091315090b010e03 85
    0x103054040c929205004100140c0c031900c030380100f43c0c00c903850021147d400000c40d4100081c0903116030034107040785004005940110b50105214001c071021382d0041b1a0403a503d0358200d003103040c425400841d07910341c0841000a0a601390000b41702c00e4403441100d1007000000100302d40c0700015044001d10307038092003041c0659a100c41c1d0742d0b80a48002c41d18a401842c01c203040e880c0641c0b1520005005900c10780103181360030f0402c101100544800c1d481a000c1c85a0142e9210b220400d0740f2900d010103020703640000d5803c01800d06800800c1c0706074803919145042800c00c1c001d42c0001400c5070104c034502072001031b480d0480c0c00401c001e40511b00301461240240c00801003419000300301140702d140c090781c40e004000e858000084290100762009002903100b44009030300c1104a80d004800100c0003031a01d00001c1d076807082d040c4607034855682180000e4004c10200c00d0703400c01e40c0d195490b04081c80b20900014101e015622200d4509100c2d00740c0d80c41c0c5500c200c100c242d004140070000c440c0090300b6519a030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 62009256 1250 62008006 62008013
    0x240f0706050c091201140408030a0213030f02030717030f0a090902030406060503010507020f0a02040c020f1204060801050f030c090406020f04091d01110304030c0c0b07060e0c01090f060c140a 84
    0xf6000502a140144449114144001c00c18803803102038048428a590032501e403501c0c0d11580750002441c410600d5400c00c60740c01c800c2410804103000b14400c0003204000312091040c5801c2201640c0980707901c1c0401c00072041100c001006880c03084a1603c1c406856610001e41210103e5680e40000d40413880007040c030043c481c06e5003140007955010b034024811926091400c0780d4901c41e0b00c400c5210354002d020010014030b03003600b2507684543e03288126190365003180146800c090100305c0715134014100081c01c100305900300030b9150040000301c403402c00044596000c2501c40300342c00005031040c5c85000c0028204080c0364165541d00c0184580c0a84075a01c41510310000c2a41030a21140d041103002d50800b10601405003a05880d01d600c02241191070b2687c0658101017026012103110301c4030240030890380d8078500940f03900e6014050114240c111fa018142c10b164a0b802914104621042c051241c44083d070350145c102c1e103c9240c41e400304400c03401c012a0100b40001403203010b004882400301030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 62010506 1250 62009256 62009281
    0xe010203100503031606020304080904050705030702071208370203070507050f0f120a1b06030b010c05030301150915050c10060e070806120d020105090c240f070605 72
    0x507a18003184840d41503124001c040d6240298610000007a8140a4003030010703102da0003450300688240400f81c109081c00c00010155402150210001007000c020080c100f94104a424004c00c0c988081c400c0d000380d6034485541c540304441940402c0c7d144c58462035841c00380d11f2030500101440292044850384004402500c80d40310300407d8070316100b560400715035854000210a298800200340c40000700c014014020000c200c11107074a800d005a451810210b50054070021841c1c0c0c0d80c0d030a110000d81011009001c40300600007490400031040b0080340012030000c01c803410f44030785040381c50320580c500c44203d0310300c502030b04004001e100d0300c603040040c00e0b0014090000b02a8000035103401e0501d00307840d40110f9000d4403c240f15080104085204507000b03511440d0403050141000c0992404040c64510300381e16890001c3c0103030354030713020402c00c0380c0d05104101416404031601c00a80d001e8824091800d02d030f26800150343d060019203415442000c1d03080b255000d80c030400c10f100514044072540f10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 62011756 1250 62010506 62010511
    0x70c0b0918040821010f0f0e06040c1701060302040302090a0b010f0302090a0f0e04031e0e1302040902070b040b0618010e0c041d09010615051228022802070618090e010203 75
    0x3260040c21030202d8087c0000c190309050740e0f41000000c81c81d03508c1504000180600d042030806200d00c010b17101c0706001001b5005400b805180d103015907114034520600c00d000d40002e00464126180000f03402e0944e900c81c2c0260341081e441d00d005626868140c0002d5466003407603110301909184203a002481ca00c40c8030a051146000f901d601d650001585801c0c50210160000c00e00000c0d101d030341300c50191a0094401c4100e00d120b40b0010301341921081c00b0300c126031055500f654100c2c898800c020801000407001640b080c030644043c1000d0401460100c49040e060103010400c8038102c0015203001c4509040e0b8000700300f10303100000c00314a0146180094002940c801a4950070a000814800c4000c500e4600049045d5240e074504400300803100e05146c03015000400c0d149078045005610b04100e880c50180070008030300142d4801d088240c9640300400304513940c0812011a100f5400c1036000301d45201200c0280c1440615072008420202600c00980c00005246107070106081c01100305502452 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 62013006 1250 62011756 62011769
    0x16060b030607030923031b10050a020a0903080f121003122f0f03040f180501050a0303080429160c21020a060e03070c0b091804082101 59
    0x10303003a0302c0340801142521810b041c0541680d074101c90300c1d490100d44034003507aa020702c0101030b2803c060900c144800e40341c286450044036039029403c020604907080c440c464100d4010f07102107292585206015240c2005403001600b00760000c10003e1345021410125507003003020b55920641071030410421020007a1500007030301d21a11005030318481d140202e142400c410341c44844050080c41d0108418206007414000d910302c0e02855203204c907180c1003000908007500c4e00400001c0106d0800e07180c2d1941d0090640719000303a80c2040d004028a4441c1d0b0949d10a0b2501864110315954580c140005240b03504494005c0700e0705000001d203d0040d045800074062012402082d045480d00340045412a400c40809041700003a00c0f091051021035861145074442540155a4045001e86a120403900c60340000441c179000004c442c0c1c104401102c5141c00f41007004501400d21744a2004200305c56803840b5581036403a543c0001c1414007a40c90b060b00c155200c012a440e441e8203260000030581e000030320401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 62014256 1250 62013006 62013013
    0x90207260c0f0c0607020607050c130e0d02060c0904181e02040b030c010806041802030609030a020105070c08071211010203160305090f0c060702041508010213050a12030e03010216060b03 82
    0x748a02c10b0081000c2e100144001d010314107259680d0200031a55001351011a11881410480501501d031192448640c06501100140c0c00300005101c070300300100c48035200c086400110401440c40032680035a0003842c420f940010f03120a926010000705244004007425000c0e400c41c0281300c0300d5554034402c00c014400d40d401d2052801d0328083c141e441c0108010f0501190039180059014200b40c0d0050301d243c6004000000b58640d40e07004a428000d0039a8003003001d4000064010200303809016454025000d444c00f9854000c03140c44000c410300886100420001e200c05004c03000c54403910701c00d0890204040210758a0500d550720041c0300c0d02e50b401c5000800e0424002603003003080451191101c800f120081e0484043c04020080703540d1088130100d80c0150384109003094044040c0c100c0003e06045000103954900c101a5500c4044455008034810004024240070700411201020800c07070b07150a11a00b4683c00600180c0a80a1042100403081f4441c6101e42882940c0c1c00c840d075544019030a5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 62015506 1250 62014256 62014273
    0x80901020c0a05010c14070506070605040c0f03050303010b09010203041508060f0f030c061e07030f0212040f0506031801020d09020108011e050d060e01050f0613060f090207260c 78
    0x384908000c0e070b0320405000c00c140500450102d20461681e1b08003400e06030a0310142512035000800744c0d00082c1d0142d5040344c0d11010002000000c2e2800e002500200402c01400ca245a58481d540d1105014500c001c020200d215440c0740d0082090b140580342820107540c0c01d400a1000502003142103c00ca84241c044030828441414403030182d001340d00c0040c015202899001c018820141d0012041117000c01035903495042d028002d8000d040c007a032080d03846c2d882c003112080009250414840013440c1c01001000100060341c1d09641036011034000b0303203416841c2e9548001000d204952140004070a5000040124600f01c96910211460b41f00343c0352030a070769880b040050010307861080728964428000f034080c021458110a682e80b83c52040401151054071640b0716070070760f0000c1c0c400141c140030400c207204840c607011004400d106d100010401c0382c58070744200c070f04801400340f090307140d00d030f50000d034010501c002c0070780058050469a80c2c007000c0300c0000d45d082c06140d008440e5a201070280d00b88 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 62016756 1250 62015506 62015509
    0x20a060804030314040203190201051b0601030b070206130b090f01050c0a120b1309141b100302070506040b060a09060b0301060e1210111b0d03060f0305190302120304080901020c 78
    0x244d8003c40e00a0002c00c0714614a650035801e0301c6d8802e0082e41031200c107005180c14508500c203812080d922400c080c0c042545549020b011106000d0801d00035500003a04100b00005400810414586c200100002c01d4807090805800c240b00450502515400c0c6000c20140000b1200100ce038a540c80da030f8401142d000d0868a400c603070680c02c1c000e0380448101c4988101d1071040d040205010b004141010316401c04142c2c0510300740d40c240b448075000f117004080c22550714050b031500d100c0c413000f0b040c20b5203058070b00d0b03807149c1d01e81b00c00a000404c1005a42c004c1200d0791103400061015003030b080002c0100945500210b900354000b4450140010740001d126401c90403d1012107025103031000c01441000489824035010380689482c400004500b8044101c40805110001d14000140360140081101044001701610030941040318507840c000000c1001a4000a4414500610303082ea01c02003480c9140c00c9080c030b1003d0414208003503002c0280000e2040c910000d1004500c240c00720b80702c0344000d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 62018006 1250 62016756 62016791
    0x70c030c1a07141e07060306060309080a0804060b030d080405100204030b0f040f0209150103060e0903090108090705040e03030a0608010c05030606160602160615050f011803020a0608040303 83
    0x2680c4004900510000c00083c40242c0c8103145a00d5500c00e8514030340b0501d52410070705607025203101311544220010003400390103110307800140c42189000c0c840c0b2011605c038140244104990741080006100c001028031019601840509400806840070380b4114540104445000d903010b550324010100400d003510a94402c031400c9980c0160003010b07a1740d68454480780807030008c0058031039010114003800140c0d40c0a01c9030344180d1000010781e80b0005517400040403160781350400075490340c7c0340080c4031840100106498000e80b09285c4030006944141d259820a402a030201e500941071440b008030030b0304084081c2d841159404420007400303544126090903540d000406001081003007003c80c0c81070804000800d001244c00c181041c0f04a07466071207004a070302c0400a4404814582d519000b044507601951100c3d03042c8000e0504418108400946c050303054850007414455a5030642c1e1504400710400c4001350740051070890b41c00d035034030740c01707090408112800c41c00645403030746410b281071411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 62019256 1250 62018006 62018039
    0x8030a020d111207061406030d080c0f090a0303050304050f01090b0c0901050c0615041a15070f060e030d2912010e25080d08040816050102070c030c 65
    0xd500a022090080704180d401d42071480c40c90101d8094075500c200b00b20042c400410200d0311900e0001003101d10603118209070340d8082d0900c2d01c290020103034808070030f90100c085034011040b01611640e500d051001001030344511030b001078100000c00c10000505402c131010b50f2013540920159080e01c5881541c1900b00d841060f401488001d200c2c02040400c000c85000d01243c03203060601d02c1c03420102c407013101d1801c2400c0b5405080c001203c1c842c8200c5041c203014101490b0119214a03500741c081e10005990b90b100c4030b0b0300346083c44001c11a0014410100c40d140300d000d40105d82080f0034000c1c400c40644990018000380c45441c01d02142940215408070300154000d6603e158400a040a5081207000a41260092072640d04e840402030b4800c1c062001400002070810500010031b120fa40107401e2118681c030404040d0003003910781003001e4001c1c0103980d100d540008141d59920703030765201903162404000040d00c51361010500ca01000003024081050ba801030a8001c682580d8603000e0303825503003d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 62020506 1250 62019256 62019277
    0x20723030a05090d05010e01090c06021534080105010905060f03040b06040f0e03090301060803030702120f0f040603050f090105130602090f06120106030f050408040b1318020d060803 80
    0x30001d480d040380c4144050900f01c040148010380715041e503140c642c03d6810480c4030401c180d6640040c1010400c032858554010b00072030010309500101f03401d416046a0000f061544030702d140e1140000d20110f17042c851560401607000c004c1e4007c0801d40004d00c01c400034010075000c0b449031603010034075192100c191749880310007064075851355445603540ca885030805054290882c3d211440039480034202d0140500f0848404029515007020000f09420348a01d03605c01c80198000b04280101141c0c081401ea90081360820403c0c0d44202d5083d65070b41c2c40c0300b4144c40702410700001c2000306082da4190401401480c4030300c3e1a048a0b129000309500b200c0b001d2b1126a05031482584600c0002c031150007411440c04020106440d0340003841c0880e095601010701c0c4111510544018014140c243c426141d024105141c00c004a2409941d501543d102d0360144075003075130010542c01007140601200002410426120400c4680c3c0300050030042c1d0042c0c282c4050403814480c0119802c103001041d44c00d0380c1038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 62021756 1250 62020506 62020513
    0x1e1e130f08070f05060a140609010305070302060703090e1501020d03050108190609060204150206011a09061c0f0204050a0e040213020f0712020a03110316060203060103020c0a06020723 81
    0xe1a6544080c660000c4411034000d184180b104011070000c0c40400c1c42441140e9003ca1980030164007080b09050041c034441c40f46102c1401440070502c0000d02034140d80d0b0540e90a565a622400c065807814001c0e44000e1103180c40104111000240c5104550030301801e800311001d12580c0318050f03003965030034000c6807260360083c7c500e240740c401c0002e6501d00e505d0280e000001c1c45020780d21104141e03405500b0200283c9660045640020360402c43c003401801c4a00b50b42d5807521a070703400324200f84590000c603403180c0000300d20b100c0c0318035000402c00c4120311840c23401c0010261100000300690840c1c41401d03c1080c10b1000011090b03a10003240d44596030092283c078801d2000c185690003500480e082030812802886290000f4a481d00241d045503800e800403c004181443c2c01821803c5407640320001e03800c2071092552810541808160749988030002607200d5403030000480090240324101034161042c00f0b00881401002d9000f802140e0144903404485c500803011000203101c008802800c591 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 62023006 1250 62021756 62021783
    0x51804020307090506030408031f030506010e060609030105091e0d051902160e040605060103020a1718120c0609161202030307020d060e0c0301110a03051e1e13 70
    0x5810360041d60302403082d007803211600d500c07000402c0f01078100b154200c540c1c40700007082c019201c04442d420204201e040c0d01c460105400c41c0d407450340b107290610901030102004804030701c0540e0b480341038640c09940038008210911f442410f4556a500011a401e4075540c29913031100c00b208041036403840310010742c507103030700d002c0f4041da5402003040342d00d41d44004c40c0180e04035050419003800020340100a64041d00f0501c0c140f50501f081241c0e00603000d141418410442603824a41203003002c00e200070b520802200d180e548840c041282c1150110100c220702900c100812505a14000b81046440c004215402d1f551159050760391001280100ca42c5640ba0030b0040010300307004242104190f00c041c06690901c420b03940481c0c3e40450107601219030307607101c014000240b48104101c480c0e8107011002440902e100840141040c443c0705184400c041e04da800013410300c802640c0042107841e88060707290346450b1603110584810504e48001500c8403030800491400704100e00c034956090b4100d0103480120 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 62024256 1250 62023006 62023009
    0x1c050405010e120a080310091a0d0201030905070806010b1201050a030b0103020d0606050411040e0f1504020d0b06030c1b060601090b1b0708010b040b0405040b04030507021302041d0105010518 84
    0xc10103a50f03110601c2c8a4900041c0000301020040d41c002c40300c40340c200d00035a0410031140191b600080340661002000c0c86006459668513000407400c5c0d4080c200062030810380d04203141001825005280240709610000912500020090132408401c04030261140d03200c4042010b682e0040c4006003144a0707c20043c8003500d0054844004180b140d440082c0b00390b074410104080e00d13040d901c910f00051012904000d00200559520361010004242041600d0801c031081003440f20004407a001c3d580c082480b80048115074401c0d203240b8001040c070360301c910b45809506202c1c0c0c40001c003940c0c2401e5420704800c240c44002030032802468161141d0541f2400e1141038401c64000403002041243c81c4180101018000d00052002e80300102c0042840c0383c3c044140403d4402c4002028005d928142c10000810303000307021581c00c140d240c0382203681c80d102400010b40c40c054100b0b10340c00c0580b0010f0001200c150818100303030180c029444201841c3e9030b4800546260286220010440740c40940c07044d40b9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 62025506 1250 62024256 62024269
    0x14060304030e030a0c06050301051002010c0c060f11031812070302030316030908030405100c0203070f080a020a14010903020105060405090a0b04020111011509110901020d0503040c0b0c1c050405010e 87
    0x2410340280455160100315140d841480006500c0311b004100d0000041c031031410300320314900700ba403e01d000a0041c1e949501009001c4004510081c2025a694800c818101000e800c2110800f054000c05074407030810004c1d00d115444585d0600000c0c0c85240c00080410000a00380c07201203030150080e50070b5a55840d105621040900c0c890410035650740d08203000100b181c4081d41c0190302500060903840180c00c21002200c1d80c007421402554000e202c0b00d00082c480c822544510703030340100c281c0d44032a1003860036071401e40260340040030b41d0071903244200380c3d0005502900361540664000e000c1c44d203411041c80110f4100b42c075201e0040d08003000410100e0412080c50b43c1091042c5061240c80b58201680c50840303900d858011500c4601003810400e00c041800740b4030444803c2d071911450050710780300103580c1341d155820010031312001200003010b0245030a4090004d00914000fa03030b841400544040c3c9400b400420507803d015021040d141680c4254140c030181c902c103848040300701480c03000300300a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 62026756 1250 62025506 62025527
    0x8010c03050402280302150c06070207080c0103110903070b0c0c01090f0302060703021011040501020c090705070b13050304030f0302010f1e09150c090e0c0a020312090a140601050103061406030403 86
    0x10380081d8144c008010785541c649050494081c0c498541c4035a080c00b201e5040403800380030b15085611881c4c1c1809000c40114112209813000d00300042d00300d0740f0142c11141c03400b40c154400e41c14001c240c40010030f111450010000843c00009480d0000e0281c0015501801c2c54000c213000c5070380e000d40078001410094010014030b8084e00484a41851081c0720301c0c162120356880303804282c004a02080320b56010407640405000403034130b10101e032070000c200614a005c1e840300608129540c070003240121440540e0b90040030342000540f07a481d910fa082041c09100d40c20011801586007a0038002c50105500c91034108100009600340304180d45405c01000e0140e040050f11045a542182c005907000341c880c80d56022402d854181ca030030714000d002503100a0040c1500800c81080010f800d41503400300494954100003101210551107041800f440c02c00c011100810320811401840070314a000070300b09040350700980c2c052143c2c41e15000e203101c880e0b0880c0401c60f0009010b04c041000240600d00841 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 62028006 1250 62026756 62026819
    0x10b090d15050411030c04060e0a090f050307050102132111010e06030f070306122a0305010e07050a052e0e09010906031514070f03020c1608010c03050402 68
    0x208110031401ca4007100e0094604492080200103401c0d442d00f03082c4101014448100c40801206207000c0c015068103000500120080707589440f11802c00c950100c001d40480d0700310007129104d03900c0c1e00d400d80c000d50100d114241145010701000640f818440703000641d01941d0307190f001c082006540c441100001450205041c090b40d03405603441911080c2c0903501c105110100d034603890803e16005422694180c105c41e0a000e19101d441020a0750002c0006c1082014458207240c40d40204640741c1f581540d40008040e5400d000c0e627406072010001d04102903a000710303820a04c2c0c42c0c2d20030030400040300a250394602d07003d000310814044c1240c52143c1612203e14248004941c6a42300040d030500c200760031045a030740e59114284280042c55451a8100c1404003041048021070500b94021003401070000301000564104110300c2442901a601a003465004407a43c00000440c4244034800343e00440c400c07076103443c2d070402007984a4040c0030b0141e0740280c58a500000d0360b040041852402e404a43d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 62029256 1250 62028006 62028023
    0x40906020d09030306140102010c05070b0a0f05071d01020607090e090106051918020301030c03060f090209010807080f0307080306010f020a0f0f0311010b0901051905090702060717010b090d 83
    0x490401d141c5020740380070948030750ba0000b83c59007001d114103c01c0c4250030600b81117a24144408020507000070480c0e02c82070300481804025607900180b000500302100740301c801c0c1410101800340c4030f600018002c140300510000300b0041c854180c012a074450007180d01d200003071103001c403c0100702080b80380c1a41001580001040207502d40c404122402c078100c0d2415643c900000003086440d032840e01131412854070100c190b145515644a800252081c0d00001d061140d807400b6070131030402140c0c0017005c25030340a0540041503960f81103064940d81548181ca42901401c0c812044020010040341d1240da84508058115107a0313500444000140c05000010761207003402e00004200f0718145141e190b440b49070008241425441d00070303c0405c03080d00c0150940c0c1017616110180d91a1040107064a00564208003d60b001c143e25611600306c42e4043c0303804c1660982800400b50f40810142d03c100d0741501c07081c1d1146900c005a00400c0d209200d443c03001c03d0140107101c0540340840c900c003801d90003403d61 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 62030506 1250 62029256 62029267
    0x110a0e0409050607080403080c03250201021e0a020d0309020d0b0907090204080c0a0b09030703020f060909010b0702120d0f050304060207150e0706020106030807060209031e0109030320070204090602 87
    0x400c0e20303282056a1380e1000c0341c035990801c020168850f404540c00414008000d083d8102142200002005034415450000d04110010ba8542c0300358140c0350700000100080000038540c140d540c02a9205188600040c003441c2403500c0c11a00030b01449140540c094907605150f1035940b2003410340301e800381c101c40b038a001d41000020b80500c10300292000e44859005841b064411078104002150703a644003c0d10110240400b41044e5801704125088a4061741c140c021200242e0004a041c841e402d90030358001851070004c600300c2e40e2040541911442030f65800c18011040030700325520902c058048000401000726200031030b1007003014542151140e8030140c10007045507106071084004040e8219907550b2400c1020006208200d40310003031444c0e0000700081800e46d10b03a0040d512071010003401941c2c0005440345180c0341007018a00da1a900620390b03444007010090280605450b0505500007400e102d804030020760742883c040041230420028924103e40c59080c0000307800c601e403042d91060b80c203100c2d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 62031756 1250 62030506 62030513
    0x403050a030306081603151505030307080d140f070509030c060c01050601090b0a0e0402070c08061006080105030d080103110a03050f0a020406090b0319110301090c1404110a0e0409 79
    0x819484a01c03948002c240d00f030a100c800d41c9800e0800101c0359005800e55010000b15080e54021405170101c00c00206085048601d10164907200380e0099401d4400092200140300007000580440031801c0c8003449440c45481540b20400130a0307a03c01c4161b44030001241500d800b987c01040d960030301400b84c499001001c40045c5440e0042c000914083c2d44600c2003002c80e60f0711044400240c0541d094640c1414048500100702e050100c4049025640c0003820205000d0b000013150020a50304049920b03c2ca0100f500038095000c0d886404040750341d03400049400d240102d07906c0d46045803070740d03520450b81c60740d1a6082103810429066802503000480400804c02c240128810402c0510060640d8640303441804101c40c051f5102440d1a0303c1d0402842c220390380414400c840b451494020420700400f400d001054944440042d98150b03e81655001000300c164040c0080354442c1c01090b0002080340140800e6403003024502c2c906000411441103414046d01c51401d600101070030005a5030f21a07074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 62033006 1250 62031756 62031763
    0xc03120e15130c031a0f070914060f030103030e03100c1d01180303020106080f07050a03080f0408100501141c02060c191103010c170402060d0e01090f150915020f040305 74
    0x10411740740b00384641200b104240392005959000103c0c80c085007000e1412800003002c816031030003800742d030020002090707030242c1d505401c1d500a440d500111540e0ba59580c0383c041c0c500c00301c0900090090007800002c6148092a02c80c2400c03448480d00c801d03840400000050340b04010620000c0d0500c2150300303442030410326a0303080f000958030980001840c00d041c030440601c0c104d00b02c0340074406684801000c0c404c0d5240c0310b4005c000c03a41d0141103d910f03082801c0b80b0400f180a9900900340c503108909041801c460580c028604903000c02c06101c18007d40d280c00c0c01044d500c034070000702d01e140d8183c03101001030401070001c200000e101c0040d20302003040c103a01e0500c42d4494080548100c5500c90381052a440c007841000c201e100c4a00701146080c1403000b51407043d5400802c00391240d100442c07000300480e4960050710035141000c00820078200c080c40d182080000d0000301b1780b01c07500116402ea070020000d100c0e110908ea002104d400c241d52501c00b078507000e948080d07072240c81c40c141032000000058040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 62034256 1250 62033006 62033009
    0xb0f0c0d090f0309050a0f12020411071109060d050d08060402090303040603020405210706030908090d0b07030c0801050a26031b0105090a02010e0d0f080a0c03120e15130c 75
    0x50b00c0d168036000003410010851050382e000316201340075066081140103110010601200e0303000e104041c5406403400043e004040421143c00044400030342101080040301e83c80450031400c4601d00e00503200c540900c090341142d904010300f55884000e010102c0b0380a43d81c46540040b0040c00075142c00696000300341503420907032203440844d07004681840280f602400039400b140d1074406845407001809226542e03210240b140784141a6242015020701c500682118096400a010600c000380280f50200e4880710407180070000034a0407100c42c03616031040107428100c0b200240210155401d162840310f050100750807040741342d1402841c08901070024030141060f80b880800341c81c000c40340001c4050940364000c02c1021180c128589000041c0e8000420b2280090b003540d6060383e8003010f290213010f15a201300087d220900110303a04013001d90008203440001d110703a89640c0c0c64180e101009043d5074044d4003500c4540c02c038440c1c0c075250f0103081000507400102074100030410100b41d117400a018a90303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 62035506 1250 62034256 62034263
    0x30a05090102060603010c05041a04030609030801060e03070602120a031b020a03090611150a0914280f1b1e170a030815040e060903070204050f040b0f0c0d09 69
    0xc54050036668040c88820380c018815402845900303c64903000380244600d0080080c11001c41000d0b0341c00790540010389000d076074002020400d6106505001d0407503a0240300340c0300020803a2941030760502b0f0101c0c2c41b000b1280341d60014030200d0a40041c448294005a5103c0c0c10982d0392a44000c2c13012522288001c000300d90380180c1034112960800402100766a013005040c0700484150207040000020f40d28400c0e81d581d80d403040552980345501d0050103000c82e02420000c0d046003940301d008030100303814404026905070b002203850360003041a0383c1021900c005d00020358400c0460040303440800c6002030480d0500c9035403d9161100d802c07806200c40c5155a000f5818005018054001d600c0510600324800000411659070309030381c0200322400c01486181c4840c0004100c3c58030762101c5d002044400b5485c0182d80d114a040a4010341d81e404c250001c0e0711841c01c040100f001e00303c1c8000e45e07902032074101d00419210341c4c540341d10340480600075110700a004010049250307107800c20300c10300039118030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 62036756 1250 62035506 62035517
    0xe010e04090b011401080103030f0f210507180e0408030603070302091006020d090503030a181802070b130803040303151a070c050f010e090406090c030c06030c0e09070e0f03030a 78
    0x4000135001d084c0c01500c00141806064801840440c4d0482030b04c28480c400c6281001d400c10781d1a004aa91403640d5500319404012000000d611241e1508818400c0240e691402d4001da040d14400e868003c1500c1b4074414034030141e002ca800b00d25888000d580c09140541100d01043c2d40b9408560081400c441c000c01e030140c10f0005008203a414088001141a146480d0100a0411000940380e102d0200c06000748000c0c0b0718403003142c40352030b42c1c450020f096075448030016260300c0b000e1b580a54002081281d82070060400600106040c400344030416401c21042815907590356406c3d002040788255a034584001104006040c3d0209259194403103c001c82d100d4440700d40380f9043c802d60703050750002885120300c10a00740403a41e010340d0501c1d101d41c04441c1113001361a0b40c01c10300010300452034058200c14124201100b4002d01d080e2600441d0080c1ea000c1007519200882220000b0040c00d034190b100c02558081462188150f1a480044d00d004200c0d01e5047c0341880000d24503400081c0c001d000c9078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 62038006 1250 62036756 62036759
    0xb061303030807030204030c06080711060901020714011427060103030e040507020f1906061505071407061b0201020312040b01061716050c0321010e1f03030e010e04090b01 75
    0x16030140072643c001619040540c1407908580c3d4a0392441158080c40c0204034510000482c1180f081c0c840e1918180b4483c00d5481c20b050040b0614042d520920b0300303641c1003071058400c2c00079070014410850290302c080b9030240300791965881d40c2d81240001082a0700b001104030f100c860003500b880f030350740218426110032000200c3c0405103c10b50710003e040b0029504842ca400e4040407020803c0507002d840c02c0d4502d0302610f40c501d40103008000c543c001c6e4543c0b003032403010300c20003d40010050038480c1c05034003540340c10440e000c02107a80d040c0c01d0052a0010f0380300d1070031b4a601c400400006081c41d1050041d40d0500c0c20b11340141c0943c0700100c5094444212030070041060607001032070324000b03400c400306403a1145801541580c03500c1d040d20b15a0104a00050301096060050050701c54091300c0140c4241182542c0300395030322840d403c2c050030700010b202c00b01150360780c104400c2d0211550b000a0411140d103203161410b032409407035401010b0501c042c552580416a841e07104001019110b01149503555 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 62039256 1250 62038006 62038013
    0x1050f010801051501050c071205060702011d030409111c1506030c14160503030117010b041b03110931090201090314030715020a0807091401120b061303 67
    0x886040e4460221a4903000500194070124010804098420700780256558070b840111480c0412542c88010398801240382d0504204000c9002401030b03540ea4020b01c81c00c003e280c544001d2009220141410740c2c000c1008018440241d0007102c40d070072901c0c4d80541410400031942c1d150644140003582480c0d921008100c1c07400d950001030000c2d18051508203c1c1540640d006040d9210040700d05022080101349004009a000421108203900c041603075242e5940e0b020350fa0244035a844100403039420040d00c035400c0d0600e803151804030754211105090020340f88034280d008203c20100010251810490528644c41c1d40c501140c61504408031040c0290f042442071050380c1036489022042420003038010b0150781d0082180c802d07250480041b44007450801c004529511544400038145120514201d02e02a02a4041d01d028102a03c480c1003d50b40c0d8a42121024298010079003048140240c0d80304a502c9203c8840043c48404070001d04008201c001428a800032050300349030100307960040c03081 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 62040506 1250 62039256 62039281
    0x25020313080304210203030c010c120b030111030105040207031e0f080c040b0f030a02040911091f0203030a0b0402160b01180504020a0905070e10110706180b03041505090105 76
    0x1441ea1102450405080190780720070003450150408400300055258020b5503814411076014014180007001502d445500207001054030a030110170710b51511940e06040e04060054000c825460b80f15603240d0f80c00c001c01c00000390045103080d0208525038600010750074901124100b0903049464a82c4100c01c030740c4000b03041440c0100070000500c0144020444540c0e4601600c0c404a0f048d000340391a640e54805400c0240156400428103508008544c80c7c00a01a401006032600969203071220b000010352000ca00a0b01c00e04820050b44100000303201c076203007a8820060701c20010009441c2420140503408450041e4034291140c000b02c0c401002034540040c011541e42e01d0b403810510136480e1035000143c2c00c925901c159400d4503201e00001d0340403071140c41c2161103000000c03d1100b500071010b40050007004581140d10f0280b040c40d03408508a40100c4042498900c003d044103803c0c7c2c100320b01030045801c040c0c012541070042420510f402140f9019140c440d080c076100004e0706180c803e058100303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 62041756 1250 62040506 62040509
    0x302030903071e14032112040b1006020a02030a06050a0e0f03130602060112060c09170f0d110a0f0804050303120f0c0a0f030b13060602011b0503060901060825020313 73
    0xb1340d0b40b52010b016580c0700480d81c3c0180301c0f6060503003011480795a4800ca1244183c0024003400c100744030801c4100210711607220701600015a01b820304545442c030030799803010074010107941039000c1903148002420640020f544000741080105040004001984c5030518007a80d40341d4a800100d41c0500c80b0307002c00c84041c02401a07200401040d494581141d01e0114205070203030070251925050250140034a102e0380c000c01115001c0044c0341c68560841d901d440c1c203044410150700615801014040c425a0084504428040900450081c40c1c1d260306c030141c9048c9003110100320600000443d50307010b00c007502c0d109030703050440c452500d0071020190031640001c110652008c014072101c0481d075400240041e240400f0b080004501d10030600003484d004000800203c3c0320b041c0440441c0040d07046d00003843c1d03004401c0b05580302c4155000142d505000c00c4072100d400200c03d200401c159031180b045c86421403281220745003200c4034440000c1114400b0f4a984c40982c1c000101d50b10b00070b07106a00c810 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 62043006 1250 62041756 62041769
    0x20a0305161e0302031512030d060e0c040e0402030a05010212040605070906090905060d0212010b04150b0a0f030207120903030f020d0509010c0203070509010807061701140103090302030903071e 85
    0x141d07421a295080741c0340c0d40b00803040080550100c0025036034203001080000301c0e20010071202c400907100480c1c5640390300c03084a62808030700f00b07540000c400d4002c3c0002c0d80228100e4600a0520703081103a0182c03000b10090043c0d03414420750498001084084c402014891562151000c0918017030078140e040e528060f000304100030f0441c03020440d255002e0465410307601c0e25003020800340c40b044002035501440040196120352440310180300c001056100b040c0c000e00540c0c09001d5106481c0255080f8801032284281c0c100e010000034042c9482000101d01244060400500340f03010b58881016440011980c5800f01d00541c0081c000e0581010760010000c1042c8000c2000079210b00c8000c20a001d51640c1c14103005451030f08508556050001001410f400f500307451481d07030b454036410395030181c91060700f0208205070040250100301242c0c1d14140c0f603140b0411052088824011030003002c8901081d002c602050101c150240e41c20f100003001051341050145400c44204da040194200780d0344000e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 62044256 1250 62043006 62043017
    0x1d060f13030c1d07210b10020304080c0a1805060604031407050906040504051c050912030d050c0c0706050904021207031a0604081e070e07050703090914060d0c09020a030516 76
    0xa130707040c0d0084051090a051110f2042e00012119020003d003c0c4094550f9021502c01f10550049a002002e00103c452003400c482444c17403c2c10a00c05000c0850044456841256452400c40d0000e034000130b41110028102914142d5640c8544040d44054081c0c01c1d401d4210300700410080c5040d0f000c081e0000001c0f141000142069a100707541c800340040c0d17403070818400d10307407501c0158010000e50b050240b015001d2a290310007400d8841e1240d00605502a4082c5840040384a08404c003003659500201c000c006c000141c101601624aa0040c2d1440c9034880e03000c000313074807001203d41002c074083e1020351030220f9007440003c2350b80b1800a029184c00d004113014002040150800034190a041e080b0702141d070b120000040b15241007290030f41006a0012a400521001c158424000c0502c14020381d20364446e2070311010f5090030346800d0b2016034056841c01010585034900b68680780c249038451142040d02d56510070801042c1d8000321441e40109a448080140c1e00320410b029482000c2a4a0039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 62045506 1250 62044256 62044261
    0x70906090f141306060513021306020a050303180703061d06010b0c0304061202130314060604331707051201020306092202090c0301090c1d060f13030c1d 67
    0x41d0700e100c2000f000c043d0760360480682c04083c401c0d903900442c050100075001c951007070340c0c406404001e58440784d8000348a2401d1100025101d00c04201c1c8411154084c01640c9592200f14102c481c1c507403003003002c003442d0060440010000341d0030320410428450040840d07403400500340140e81009070590201c1c110000401040480260110803541600e1540c200010540481d00700034000780211884018880142400030051203682e40560800c1c4401104031380e0a541c4400c103202c15900e149040c0c03105450008048007004804445906140402d00b09840c0e1040d0350b0000030203550600c00000c155608422001c0c0454148260f15000040000e0000d500c0c0d414468040303483c50400500346081044100840e0304094000b6105000c440d400421070011410701450b900410b900c20311400f18150300d480b54000700703a4024070009140c0b040c0c201d0000611034210003444910b920500c0c00480c80d000c20041003100401c03403510900039600510002c0542418800720890009217609101150032441c400c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 62046756 1250 62045506 62045531
    0x31b110d03052203170108031903111602010c0f2406050d02010e12070617060d1a0a060305010203090309040c08040c050d0807060203040f060c090810050c0903070906090f 75
    0x100c66005140d0615050103d0080c1c03e0840b01817100950800c00b0000203400020720382070000143c422813450078982540b00c0744060041d0b04440310214214800001030041c08911380b43d400281c64218011b0404403650f41d00d40d80d03049400e5903100c40896081400032600081a0403404a03950042c9001200704012401e0000107681119958802410801321341030003092078403089a800c88101c9080c048540042d04d800002d8802c08444d422091543c02d4030f00000c4040c6803c4006201c000e8001c61115070701c440e40843c0801d50040107103110384658450400000249091004512591000001e19202c070b170500e08000607100e00050643c104000502440041841e07030b401d6000f220403c6501c9000481145803000342ca000c1d01c070300641103030310110800c02070013490071020f01030034454642081000c03070841050380d204050f030255905c540d00c480034440c00d03070486a02c400d81080e440c44c5c8070b5042c01d5421002928007012600110005501c0d0502040b881240c0d02550340300c10142a0180461841c41d074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 62048006 1250 62046756 62046781
    0x6042403121b0605061c11151c0f021b011401320109050409080a09080f1203060307030c06230405091306060506030a09050709020a050a0f031b110d0305 67
    0x703000f4009654441c0801c1c82d503a02c08065410441031070704001030045071810000c40307130408080d02500403c141c0d01150110080001201d0b40e14a0100c100c0c4101d00c0034811000c01019480d0003c10559420040710444081d0350f50080300c214200c00010640340389001c500051034206901880d007550312141c102820104440c0d041a000c090f070a5002200700300500125903c800580c01705811074681413001c0c00703101c0b1050040900040d9921508070942c2d65000050380c40200c1d50401041c0e4201442c59088000f242c001560440001012a0401c9441e5101c0c000103603103640c45400418042003480014000401c0b007030480711401010b40b0f08083c506000705200150050450164551060b1100c08000c0c56900440203000c004d40407686038a841d82c0d0000013010030240c00c1d01e0500c216040010f4540c80c500031030f00342d140182d507a86c0c104407a404064500d00401c007018014180c4641815010440540c0b4900801869903511070f1a241900c0c465400c0002c0e518483c410541040c081249141c10350 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 62049256 1250 62048006 62048057
    0x10e040e06071d04020706050106110a2604050a08070e1003020d0b090a0b071d060309030f030c070501020a0c0b01050906010c0b0c040f0f0504060b120604050604240312 74
    0x741480c0501240340080680704852043c0e1003544588040b0f05101401510741c8614180e03a000e07100e2040750f0700500c07560f6950750403000340206920301e1089200c00384107100b0956260003000907580d13400d00c2c0c0c403a000a1602261500010143d42c0300c024100326606002400701d42007404a001c0380344850031a000b0524040070454042e04940204010841c201002c10109c0c1e4159040070003c22039003425040104410300543e0410041d403001c1c4180b07140c91134280c0481f030140c0e590f44021481c140f03443c0d0010010f44c1005006007107044041c4a8000401e01c00c2c00205640342081e0350301c25150403d40ba18041031901a08514020700c1014100511a41c101030891803091f0001d4a0160541d01d600c1546018441ca400c02078000c1450000041d03407400c0e0000b800e0039203108407802e0081035250221903200f40a1245407a00302c80011011400e241403d0380103032740110f2301500214114400d6459101c80c1150304000d00c484400380303c1c0410a10800b8420141d00e285a49000e100c2030000010b14040d0003400d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 62050362 1106 62049256 62049271
    0x61602070b040504090302010b0306010b031e04110909010f091506060809030304120e0a060c060e07060c0b0a0902030607020a03030b0402030103080a0c060b0618010e040e06 76
    0x3040351400d840e0003001042c146480d00e01040040c0080c1c0a040d42555607a54140d40c242d00e040c8111030185c2145818079580e030600c0f038003220500b07000300b81020741581e003d014400028546070f40a00203650458071003000d43c0b1012603c4d07005100b0040841030b030030b1400c00c8000803c00300304e00036102c10891070300400c94a6610302003a106004201d40030100c40e041000020009043c030031380502e1022181c5400d00c80484404007040320070380c00d42c0112000c42d031400d50031001c10505000c0c2d00c03605104100070b48681440e20901a00080c5a20002400c035202c0c1070005860421680c0000a0140c005003151094140356002035122326140800b900001c0c02e1031070000f814113041c0201c0c0c0c122a4030454440c6480d4211a08030361042c4480d00485625444100d0003185560700d1004c0c05586524202c0400315100c1d28001600040b00134103041d008034184031040b25940004540241c0c080740 = true := by decide +kernel

theorem cover : BRFrame.Cov 61870506 62050362 := by
  have h0 := BRFrame.cov_init 61870506
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61870506 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 61870506 ≤ n) (h2 : n < 62050362) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
