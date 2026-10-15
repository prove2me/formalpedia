-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3997
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:17:13.601989+00:00
-- url     : https://prove2.me/submissions/32388b23-e897-4cce-818e-15376ce6f0b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 718705035 ≤ n < 718884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 718706285 1250 718705035 718705049
    0x31c0f0e04090b0718170a06180c12080405100f0315050918121204120318060507051207030c120614040e1005070203120a020c06060f0d020406150207 66
    0x7054140d5070b501200d01c84050300030780074072110203500300d2560485502c50300a07040f4406d1000d240e03c07a00440135650b46207080f040300c8280c1081880b0204143c2044800419500000314002c040d01d84602d58900c400b0300725050740c40610820000c10113480c0c0e210b14032404070342651500045090b101c401400c45100c11801000090405000c110036520502d426410a00580c010b40f16034a40141840c0740c041014598040d0fa4004201801d81001a002c154825070040c0d094482c0204040b004900b107860f044e0700c18a0142c80000c1c40d40c08102181c0c402c5030701c150701e820510303c0c00c06803101c0300b80c400134111410740020742c40e001043d02c0650301c00d040780c1c446000144140415414541c00101555140c0700b90b41c000c9940305c81501d803100c000c01400511540301102001603042c40000252aa03004049240c000c920350004200340070050301c00c03280e420205002426880d01c8000070010b03450141c0f451540d0141d00f00350000c025071788a125820052080f007015442071429514040e04002055201407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 718707535 1250 718706285 718706291
    0xb15090109080102030f0f0924060a030f0516050108010f030b101e03020a1e0905150d0309080d0c05031822051503160b0307050d0204060804050c0306100b0702031c0f0e04 75
    0x61451025130020109c1c3c141c021018040a5445201040944d03070250b0014060a031410030280a11401140321800e000c0c54840c1ca805854980c4015103a2400a200d846001c85001c4e4040021800380a1003641192701130071281061550340b2001d03e0580c40802c04000d5113101e000c020011440d2003c3c0c1c1c030740285900744206248030784000c6d412001180c54031032000d10603140c07400a2020406000c20b1140c00c20018090000c21946c6e05000740409100d0254120f240304006120703414070b003e14910900d0943c08002185040c2c1000085421340e0301d44143e150b000300551440c18011800014080208140302800251502e8042d65401500004448241c0a034010301c4001820070b1084410000f41c0d620305da40e403680c984039803a044071079125851003842450300c04280402c44940c0010100d000710b00035000c4a0004105c171041588030107051f00d07a0000c900d4112010840743c100f07100070748582c40c0000c003510001010110786110902c0540141000102503070056500303150010340742c0d84005000d440070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 718708785 1250 718707535 718707553
    0x10c0f050f07051c050307020d0512070e0109051002010c0e0406030b0423100e0d030507020d030c021204080c09160e0d06022b0608010b15090109080102030f0f09 71
    0x5040c80c40380d280303200034007000002d0300320038400104a800280300540d503181c210190060710061882e041900c2c6c180040c0261151440e4443c4614103a8002d00400c002c0034500d9111460259010b41d52411414144911608002010341e68052443c2502d652a000480d070f01e401118010442e1120164052103285001c3d005c0c0040b0ba040c2c040c495106078450340144411144001c4080e0b0101000d01000c1c0f24030802b102200151702603089405610410b01c00c9524103140118150140c4000300d4007100180d00c5a0b01507990180300b60403003075101c0d43c0ca005803460709207141f1000c58150306c16004a41a80d0009a542c41c041c00e0181c0ca80c0d5001d00c00345a884600300c1700450040c1410301410f60306102d50f000c60004800d0050650482c0c0e40d5605030120000581c5680a00582142c4242d40414500d072514500080028042c018000790510040042400c5580386402c906503405c078182c02810050f10800210314490b00744000c6010755a103501071100e6280c0003400c001e849078024030b030401e15009111a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 718710035 1250 718708785 718708787
    0x5060a0b030601121e0c08070f0801050403230706090b0f0603120d020708090d0b010306050a020c070513061a07170f030402090a0f0222080a02150f040b0403050f010c0f 74
    0x10340004964480503030085c2644200c10050200d5101c2c6001c0c1050410100000ba80c9400040038400c032034001803c1041e042d95184201d080b19001c607006004503224003a031290403000440400c001f010007449060030301016031501d00c03c035a91400c01321401c055500501c0320710600c4021540c2d008034220000e000c00e0f040100490340500400c0152071100da004504882008a840705070345040d01c000d0004144482107003004000804203100641e0f13050300e000d01003040c010356802142e1440d10450000e0000da490714060041c4102c46024a09800e135031000f012401d003850000104013100d00000707254552109007000c0004c4000d124008013114402c00c405103803605000292580309804031400940c0313648280064000d07000105c01303107190910002d108400c10380c450044542010b10038103521321aa0f12185190364658082c80080d6210381c41c818030103c0c1c4a00300000f0f040c0040c602c046541481c0e9074000000c5541c109030812901074120503540042c140c0d00b446191007441d201e1411618881000c90 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 718711285 1250 718710035 718710059
    0x503060f271519060f0e10020a0c0b0c07050f0d020303071a0717060909120307020a06050609070206011502010e0a211404050103020d0b060f09030618030a032705060a0b030601 77
    0xc1914113025403460300030b06250065182c4405951b0240004a002c1a0704000079102c1182c034408440c0c0c100100000305020420b403090b1800c55010000078072a80e13013001d08100c1c2c034403c0b0700c078480d61261448181c10b00684080c0050042503218071030b803440000b454582c40c1c103510401405082040000e082a00700e515001000a42141043e50144150b40702d558800b03050040030002020344890000038001e80990028030800100d02030310f001c00203a120001004040c400645014005901c20b50060000300202d00b411000004070f8000080c8941c00103d0307803410a41050420364840c07091041d084e1032103001c901c0e0611404071307515041c13090580d030304080075043c0124051941056404260754048003016401111340b95001400183c6400c000b200f003190941c0711100c00b034040e00424011030200844000d820f1400722009001e1420f00ca08545e00f10028400a000302c0042d16030340c03050114019481118030030141c000c1d8003130041403030083c0f00700b010b40d8081d071500c600a40c0100010015004419 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 718712535 1250 718711285 718711289
    0xb04020a12021e0310060f0807090b06030406050c04090c0306061e020604030e04090b0f04020117010b12220302010510050a0e0c0a0216060c11040506010503060f271519 74
    0x80000b16100f00d00042468070a9400c90b501c4010f2600001003074000c010060300d1b08640c0300d903048407101ea44ad0020481954507404645c0d40241c8180b020400080e91500308030b90181210421030b00301566864004c0c20b90722281c0311200444e550b0310341440703131a502c6050302e44220703c400b12514045040ba10025078032580208003808101c51032004071443d64445d049000c3d921b41000225841c0c2c02c0c052207051002c1c0c000d540803408a176003a400010320214041c4401d0484420207a0380e8200b01408050040c0807000030180141c3d8000250001d0519002a0b0511030080c000d5000003032900d07144282940d1901107801062060f203401e0810000b406840e041550b00604541a15480c2d030348041e000e900c2c0030052a1580023a1403000008984143d000304084078031030080c0002e07100441c916080c40b0485405030750440c001801000020402e041140c03125403030a901a049420b01a1080d100155401803c0b0103032110f803030f049080c01030002304180d41c1c2555900844203500c21502e003144019070400d0798 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 718713785 1250 718712535 718712569
    0x801080a0210020f0106030b0f011d070804080d061202090606190c0510060803070b07231606060620240a143301090504180606030b04020a1202 63
    0x182000b805428030a02a2140180481d8000e2020355200c0c541145220004c58500800070142c40000440b150051101420b01c00c0818181140e03031541c0504903081c8400410540d0502020402821814500d200f4400180f1032910003603103034142c92041020719000605200d00c1000280440244540341d5179a03101c03045481e090a428407038803072409601380386a8003941c8100300e2030220001480300b004001808054881c02d598200d540d640902580d03184091061035075410000440f61315240842030040c081029509000c0c840f0341c60a40e6068203031140e94000c8800942d0f2a0355105000c0d00207014500a0641d1201811401c1c440780070001880c1a1244805c0c1582111400b10b005e459055100c1e00c89003241c1d40d00c0005c07919004590b10107411100d10b011061441803001c0d005591074020100b00042416501c5d1760405203070904000240030f0601ca0001e11071183c5004a000401921401c8011446806803128a03e4240100a4110000d40c03090b00d0780c00c8170003001d00040e942d82d00005610402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 718715035 1250 718713785 718713799
    0xa090203030a0f0e1905090a05040302060402010516170c1911150c0d0503040231020d2712050f030a0507140c070311100207140d0507060518010801080a02 68
    0x700200c101c5113015800e2859802c80070107200e02c84c070300d5100d17a101000d6800a4405030561340b03900c110038048880803100540141c100f80c010500540c480c40c02001d0b01c042190f03500001da480d54840b54100c002041506211040004022405e04800d1000400901c44850307405080b82041d00c6191610094031030045c8507000c00d91245c0e0001c2a04c1e01a2560005031030101c9600300000d11001e015a4030507581a8030035441e84840401c40c4001100d240f6110030800103400840d1402c220303100180d04001c00c03000540340c50340c00d0302800022030f00c0c0042c440907200080d4640c0b0289400d03c1801c0c07600842c945802c1090400901d41d108007241f08581d0803d0301241d0001302980eaa800848010200c41e25503030540b203002075200f06c2e040000900c0e00030380740207030981c6220003200f000300090403680407152805a00003503c10041040380710819800d41c007016205420820465a41c681410941c5d0408004a0000b00ba8103100c03006481030561419030a0900110550403d40b81b1507441003004002486004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 718716285 1250 718715035 718715057
    0x30210110301090e0f1009030915020307030e040b030d091a040503030f0a0e060409020310090506150d0b090f0703060501030c1b020109170f1510061b081309050a090203030a 76
    0x10303007080b01c0348207184400c06940c06c81c81340c40c4440002d40040c0c40c040e800501c2c1600040340916540c4007100345582903800070f511b00041e9680564070043c82c2c40d1490703800b5a6891000c00540c50910841e9403c460a5903081c0d401030130150742020402d0705420300040950140030500c410f40b80001141c1c00301c0305d440c0d5421f884900c0010b003220240c08240f12650170200c042000107084405030081c50040c41e030020343c06441620b45140c4000c68904848103680418500e00c41d0b8503a0105000411100c09501004202d2310445408101192410356a0300310600c5100108841da950620500d00580401d18051011107102c00c0c00424260b0703812646c8521031a1007244c4011603000b0a0501d00401c843c2c44511000742d1a901050749810304035010100c0d41c0070b042e4452806c010000740e51803040901d81c1814419a0170810101c84010380c00f88a0540c880d207002e042c001150654002c1c000c40190030309c0c0d41c9401d5040c0803605040d05c070040d000d01c0b10075040000360001a44c01100703880041c2c45514041e60826 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 718717535 1250 718716285 718716311
    0x60302030f0a032319051c11090d0804080a030804030207060206091011090a030606050102010f090b0f0903040909050a02100203120c03062d040b0109120f0809190303021011030109 79
    0x1209620720340d20790140c2c0101a08151b81c00c4005492600c018050b0500224501c1507100151601c1c4029600d82d200104007900b02031030070440d580c1a07503004401d030505150311804000d14240c4100c105401250142c07003040100366041084402502051003c3c1071542040c0c80316541d2050042650000340d62100c404954000409003900d0708400b0083c04c01e03190b16907905042d401041d007030080f24015401c00080340705100c128010b502d101680103400b45050303070320703528100c551040c050242d00e1036010400000510040602a0210b81405070b00075050441e00742c4100543c040da075951400554205000032200d64405d0100b0380e9000442c1c842d882c0d40ea0769003400041c0a08400811040c00c010120b8003c1280b00152003d00d110010640f000c00c4106000300055820102910609194046100404c00054068580950803e104220740360405c04248001001071084c00202444d285062a0420078154100640c000c00913000c0b00c100310000310311071001e07000d1105001c0c040d2101d40341c00070440f01d9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 718718785 1250 718717535 718717537
    0xa020d12140f07140a050708070311250f140103090303060b0f03011802190f17040b0f060402032e05040213080c010314040b1810060302030f0a0323 65
    0x10681401000d60a880e160003140c22020b415070740000000c850320800c9404881d20012143c10240036140c0c2420041705035140c201990106a04504105110807038180c110020445046141805221656022040030b007201c031a85a0354000810f003083e00404100901c102084251032180078a40421011554102500902083e52010030342520000c0c0e103140d400c0f034510195060300d15501d82421201d000b400c07498241d00031607d2401c00940c0c150700180c0850b0081b0f1080000d210b150812104003003545106408981046030152254110607003081a03d6140c8400b10f03030300c510211f800714114200000c0307401c448495038441c0745460700300014134207c1c03e201307601d00d10082100030000d5503204008460500c00d84068401d15400340f1500026062940c02070080315000b03010b40400c4140760b604d40d210340380c6850018061005600b89084645002d1809101e0100b070316010800c04a8440c2c694414503241000741030036548240c02000b04907000aa100031a0480080300308081e02150342200124807139 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 718720035 1250 718718785 718718801
    0x20108070c0f0c080307020418081b15130515010e0105040c030b030f03040503060f011206050a0f0608060105031504080a08060102330108011a09070509040f050109110a020d12 77
    0xf0041080c00010721404004001e010740c1740700f51814490121080000c1d0048420404018841c45081c40340d940221007110b2030400e4100700780c08460011100c200345400742101a99281001d9284d9481ca03000d0001c20040e130a080c544540d0b00e03c125615240c110701c0100c1041c01000e11942e216048246c8541c0b0035002500342c041b00805035180090081c1c034403540c9600c6403045601901030200000e0007804007582140c1201d2205000011000c091790360800140b0004140d805c6080c0d480c04807010f0014548210303c064020307080103100650400c0c08052074005181100e071142c01740c840c10000001c243c4015203c80d1196400d04642d03c2d00e903500140d0804019140031381920700c03c4080c4c06840b0801c00340718080e5213a451200d1080c0d0342c03114882803e0700c0d4418202001c01030344500c0d0310154101000d01e44d5000d002881c2c52820102d2400c00501503d085e9011f01201c00d403144010311010106210b0181c454003601100b070b15103101c44901075121081c094000301406481c848a644202403500580a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 718721285 1250 718720035 718720043
    0xc0a0e0702060705180315010f080307050309010302030601110d0f02060a09170702040209060706020403060b0d0203060f060609040c031d0a020916030b150a0f050412080c030c070b0406031107020108070c0f 90
    0x100e400314483c7c040c2140b000905c1075800340c41c0e41c40c07800105040044200c806a0b90070501461800c0c4410380190040e610240042c0d041200c201c50b0b910300d60005022002e03074081ca03540c0740d84010410a00091030818050255104c281c0f904420310f00040000360802e404c0320060404c6a01e840e0381b4000640280201d00440d500311100140507000c10859500501c20382c0e200d0310042100c0301440080c88061001c0100081d0184d001c0000720b00800f80310310680e60310500042025161000490203c0c09032800c0b690b0b000e000c66243d450500c1c0316042010300c1e541201c0d911000341201c07007642e000550040402341a110100c1040900d28851070320a0300400d10074035014040c1465800c00c030146005075800341040c5400505006801d01090380320f80200c80031544c1d40668503810000b60303125424150310803800c5e0182440304000404803480103200500040140c06c030703440c0d10341e0700d0010080c05841c0000035008600004001010050707130040c035615004129403804492160040c9410360110700c101da0064 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 718722535 1250 718721285 718721293
    0x7111605210105131a0c040b031302031209041803052a1605040f0504080405060a02100c080f0c0304031d12100614030313060503091c020c0a0e07020607051803 70
    0x104d120403101800201030391107078000c40710080f030000c1a000c000d0825a094800810300f00020012056044091908121101d10140710f041d0583c2c0000d02d49406a0072501d4206004075940d2014a003a00c1a5600301040d1340c0308603400d11690350028043d201e82104142e40341e980210141c1c45030700346060207260410340022560302d0b06001d01c107070a4030b04c500e01c20781e4821401c1135840284242d090181d42d000d694048030b550305060400c800c10043e0382041a810003144244031001d490021280902e00f803a80080c0c03111641400c101d001641c810600402c5103507035003000c106110000e030748441c040541c1a400c840b0000001a81170001d142a10401d451004910601d5004c1440c40c926070b204004481d1400c11070303e049144e6606043d00c0f405040410701140c85010010401d25004400442c0d10165010030703980380200b04200826000d541c1880000103a103d5180101c913420031407882d9000c0e026000342da52a500e41600c5c025034039030000b01204104013010900d6940d942040b080b541c0144002400d41d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 718723785 1250 718722535 718722541
    0x6080a032a0c2d06080c070b1e160e090c1b0105010806220b0c0c070303030e1605031b01050f0c0f1507082e0e07111605210105 56
    0x2001d04070b080c0380159000c0d903554030001c0801c1c14914501169840304548900156484d1602c1540d0a11006212a401c48010018000001d1800c4111881038600402c24581c1b0000d0104190a0501c001d184044004418080c030121326088051107518010444040e20250b0340c1140340310450062207900481044ca0022411504a040d000581620260800c8801e29522130800d080880c103045c506454101610960002145c001c503a00c5601c4260309800c940b03040c0c3c614900303c3ca0a80f40b540140c1c000b80e5105440f01c80c04400303000103a0300300343c10130749500c2c2c9130b0030a40000d44904216400c60b801524812564200d640030b0815140d28804c0f0f200d50640340c02400f9400b54407000001394401d16030048140c0b0385952643c40c1d0b1910300032082c1d652400d4055503400304103501107001043c1c004003d03009600360f88042e0b0340007034810050711040150500e0f504041c0382c081d10905184841c2076454118801402048100d20452401c540e0110740e14800325421030310222038111309255441c595400e003010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 718725035 1250 718723785 718723793
    0x1303110d200108100b0a0e19120507050f060a05090103090b0a0b0108010f06270803030a02040518040b0a112709010e010b03010314011e15050406080a032a 68
    0x855540708001e0700e49110940c0c2d07010320400c50b00601e00954000800612450900740e20070403c070114088058204c5420301201c03030b400e03082c91880d80c2c40b440310001c038548080104107052040c200280400d4410900c4a41c02c80b00145450140000304400c1040104d00441e99038440c1c1c2150080380d0300b0000002c00d43c10307c411085c000c1c043c504046400300e01420000121281654040d804865041d51192800441c00a401940c0350100c0e03100d1600403481100410b0b488024002580550402900140c0d1603160100b4000030941003c138031064580352500f04404a148201c610f40d05c401c8407640040c15042c00e60151140d409125400391904a10000907001550390072082c5c403082d07208645100c0940c0c0c1e600410742c00348000b4068502c0040003440100002881010303071400b450f800100105501d80d10741e1030310072684000580407581c07079110300182d905412001c41d81009031400781c80901030241052280c03035032526400001000c10080d040b030040c01e07079412105190344407980015252250b0403424 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 718726285 1250 718725035 718725083
    0x106140a12092108090309190f08031e0a17130501020408030a020f210304170310140d0302030714072103090e070206160e10021509031303110d 63
    0x40d0101c1000c2c00300f41d6034115015040240c0301e41c040d840103500d02918a41407148013070350b00c00002d1020001500104042044500c018058036039000210785400400440c800203d0b0315001000c0004000c02c1000c4500754000e401104d01408a134071143c8503110314468003076000c01c001029109501c045000315003441c003c0f00414020300c5035800c582d000a2454482ca4a9040708c0c0c414500c081d2152642d96680409900510f45c802d010340c1c4044030801408010030055481242d10200060351481c06000440689044c0b540803a002e40b107106e0b1079107841d0b134081c1d580c5c0f1511401804590318107150b4445c0c070004110034000fa220b00007407201c044000e200404a1200d8255084000c034540c100d0102d115901c20811620506107607004000c41c2d11040c94052800381c0000d000b00405c12140c042400a4a0300745a0010f0402c16900410955a22a0010741d803074101801071109500b08000c07410701b46043e40c100806590f04045442c021390401d20000d54980c185840041010340c005e010801041d40141c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 718727535 1250 718726285 718726313
    0x1e03030c160f052224030f120504151d18041403070210030f090b130b0f010e0712020405131b080103120f020717060108070801050106140a1209 63
    0x40351a41407944400c204485410113145241344400c0341c0c02c42c20103402c0c054008903044901000400b00302c400c0e000b122403c0d01c072190026038040041449039410805c007511001182040c40c03811606141c20030511555054600401c04c040204040c88484044401c12810f20000402032a40720003a28a402050f115241100c055814807000d25a52900b6413010046030416030f4000c0460440320b411080540051180b4403415140380d90b10510711002400864401c0d0190500c45c042c100402d11a19020101c01c000130462041209034400406c00600b6100c1c80e1500300c40c80341000240e40c8007601c07100c4000c0c0a594842c40d840294031048103580d0b02d141c1d000140299039a46800c818a0a00c0c0d01614048000e1200824a612600080c41c4240c4a014141c10060051043e100d13166520361080c41d02040501c10298540c01000c01013017001010421131b0001c085450003400781c2d6141250152550760803600201c8030305000940b43c040740340f045100524055400702e0800488415041044c25500b81c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 718728785 1250 718727535 718727549
    0x3101a062b0b130207060e0f1c0207050a15140a0819020703020d03051008030d1b09030305090904080d0203040c06080705090f120c0d0b0702010b0f1e03030c16 70
    0x7420088009070310350203840340e0348501030030012603088400c81e4030780258403d01c0d0a0742d0866461081041c600d0060219080d4004004003d04d100030703c0004405110010640801c15584240d108020079240c050039001103c84001d0101c2210b003202c101507800341103880a818a6000001e0491240c9410003d42c030f004da80307010520a00031003020b50700700032485021800b901603440041800d0300c043c070942005511801100b101440c0b41d0743c074909139180d90421515000c400f44c03035990480d40c41c08010f1034a50022600d103401e40302103145403070140061154202848c000c80c42c4000160034000e4160454040104c2010215501e2409048c0f540801c403041c02040c0014801030042852039110308181c400c00d0310300400310504c1c0ca52907010070030b0041c8141d1065090b802518030044280c1da43c030101c1c0d44000d00481e00040b0521702000d00a08640800302d01d80c0c86000300741c181c0c211944a0000e01c488998055122801c12060400081d295000321000c41d83c2d284640c40c021843e21366400300e56400c6801d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 718730035 1250 718728785 718728847
    0x809061201030311191e060605031b09090a0201080a020702010915051c060501020304060c0f020901031a0c0a081311091f05060309033013030f0e03101a06 68
    0x40d04107050000d85d0342203010b000c00074005010191a941030307000c422460300c103000000d51310b0750f141c0c04607003041503110310120b4a10030460b4054140c100120402c0d804550b800c040c0c02d10305420343c00600040700186c126072505602161040440e4010650a40074090584040d20710714414440100554060200d02004060074101c02c40c20069501840042c0e030016000740d8245810480220359441c8a0030040d549180c0903258940582c0300c1c0341215000c1c50282182460b5944da0100d40b240c1c0c10b901034104007459030304112000e41c00380c2c001040c035040300302c500b400702400b509428800a0001d00a243d107502c00c100c1d0003440803032855202104140400751000d041d030030740d80e0820410680021100c06005030010400803c03040c503425040199025429442400504440040b0007440f00071904c2203104a0710003000c100f40758108240806040b420700d0101d0203045e00c0e00101e44c69911076402031410b2515001031001405d116040a551000094401074484d40c0d612042200c80f04118001039110403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 718731285 1250 718730035 718730053
    0xc030c061503021f0e0d15060902042409270e0d020c0d0b0109020304051603050d09052709030403080d090c15140a09050303070521090d0809061201030311 68
    0x1301001040e19a8469100c1040e90301c0c0f80400d12400b801c0a101c1110100d9980070314100324a8030344144005019100d20050f121810403901a40c106020545415164a0404070040b281c3c0d1113580d01090b1502c241600300c40300e101040c0000c044c90b114441185840c2044c0101149980001d2000d4200c0010307402c8460004001082c0400307440c0c8801c02521a5a5800050000120680086800074424011543c1e03e5401c4d90158561f2081c5030422952038011290134401d1507031111002025007030480d00644800f0b00c00f503429000c0b00a694418501000040019106444c140141c074001d542040899a031416040100e500610b01084100d03015100d241d40402d00c0406944d4204141c02c1c1d540b1000c18140c210031b100c20603038000a030000b0403c407445130045007a4509001900200d48140000c04044007003088150343d6114050381c07890010001d0014901aa8500745210002d0390040b1090303075141c80b0400414001d10a0140102401f200c03070700000101a4020543c8a1701c0304d000007900d607040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 718732535 1250 718731285 718731319
    0x70306090b0a0311061b061902030c0d110d02040f0305010608010c05180d080c1014090c1203070c030c0311041514030c040c03020406030515010f0c030c06150302 71
    0x5019070301582d030454510320303060002610b190070780000e8842c001c00d198146035a402081502d24175075011030590341c0003082804500417a010758101481585c0c2000c3d41586005142c41c400f9000301804420b800c0d450b180844000d0044400316001c040c03680724199915902d44c4141601078409100403540c40d0728010000450710f1040c800c0c0c1a518081e960303424a80405126002000650304011542c00403100001c44002680b241c020b1040d0b0b1000781c050400012295402e4040354240144551105010000c00082d5400031841400c03541c402c5919400c9021440111455801002c100030030078aa0140003009109a4000c40821284104801c8404840d8130003800141c51403020011a100c1d4950018002000585402c0002034005001c6481e42e4a05100003010340340410910008a540040d06109051745070203450ba00c035003046224414044e1041c0001e01004007100d2038400c0102d18071408041620500d03460150315007104040c001d1003030051000700c0c08481407000324422030845194070000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 718733785 1250 718732535 718732541
    0x2131806050901030201210504030e01080a0509070b0a09050409060e060c090f060a030209030a110a080f03030a050712090b0109060608090a020f042318070e060607081b0607030609 79
    0x145001030700e00d40070b69180d9030040d41c040540902403c2c5008901c9041600b06c065841901e2042d0f000c0e80e00e0b0b035204100b540000d0000e40700030700312540080c1400100032030414005655000c545a46107815610348107200c0854140d40281c0007658481d003481d48210511640b0340004400a080d0800d444040e140c0000c08007441c400c0060040e000100d86513082d0813481d2800c01380c0343c0e88c0010b06015207813100200c00a0300b40880d40b44100c03a58000380e0520402ca04182c80345a0181451100a06905041d103803040e9490000510701c1c8a401e031034a00041c2258452402d02e001e0281a6005220002451400081070070003401011403481c0391460005070b45101e40042400742c600350000d004503080b00c1c4c00340f00850783c004c41c00c41c0d00700b500c4035031913a0b4480c8040c4400c0942d0300404801c2200e81016000c040d08042102d58440d020380c4421010701c119981468626040b6070100c0f200c07559000681b03440c2002e4014241c0301d010001c030140905040c4140810444d1080c0c2e43c540d0100007081e01c4034032032800c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 718735035 1250 718733785 718733789
    0x150c030402092401141c0e1612060506041b02030d0b090103080702010804021c151a10030e1014090c0103020a3603080711011b0f0c0902131806 63
    0xc03030303e200003030740e0881d4001e2284004512100360031901d0910300039030300791250824504814020351b441e52040d03141034050100e034004541c140c540044075460001080d003002076112001d00815035400c082695990f40790700c82121085a03080c2d0f50907a14079404060345980003829024006814646050100c1c50178080590689510038515410322207580c0045a425000920413604504035000b11321884014245e1800f81c1481188070383d40c5030741303401c5403e01a607903419100c003401406d4401c0d0310043d43e01c0c40c13a220005c2c080c515000501071043e2031201d150104c83c60b074a50170f05251010078606c104175001c000d4855804c07041110280768011004604900c0384007924030004807116101d480a4210301c81e040180c65030b811001c2505042c07070942410304002a030046451001c0014807004000c141c251000000c41c007401c0c400000c1e1800b9860b2032010b0b0005e0b60003081da020070201c0030208030017011818041c1004000071506c440e40302c0420582d11200d1b000310480846240d4200e6185d054500500301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 718736285 1250 718735035 718735081
    0x41110050418060f0f03060605060306090105090c070b070807030e07050907120207020618130612030c031e0206101a0f160b100317130512150c03040209 67
    0x85481e107803a030b81c1400201c0c034010b4169850f840712800540e034010844000064552109100040d41c51441c12808650140e07204a010740000d0040000d5942d4036042141100c400382c0301c041707a0707076511600c0890500c10984000c00f51000315003031000f82d541c0904400d108103880d840410880c0d030901c410303d6031007410340304c0c190307100d854200044c00451003440504d000302d10304e400150400606034001441c64100d01103a5603200d40d928140b007054945614200710915500320308002c460301348080084007450306400502842801001c5600300761003580b5034806500c0743c0b01d002c03080d420101d00003500e6520503034800406040d82503010032409240d8600c001e120404420786894400e852900d910150000b02c8184040e55641a0f4003000c9200b0550503071003070f4004640800c040d401c5207042c1800f036050900780440c1c5c070b8003440b0071103007a0b440b50291000e640c0304540f01c01030b1002510441d45048030349442d100c4c142d0300080030b01c44041c455202450045100716081c8400780da415104403800c000d2b0000c149 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 718737535 1250 718736285 718736287
    0x31806051f051804112407060b12030a0e0a05130f060b0f030f060a03050303010b0d051b22080304090501080c010c030f110726100519151d04111005 65
    0x600103028908900303504203001e0402182c941086c480e01c036560305c012940060f0024009196410000103225044000e14208d45950401d9501c5406070741e00c1c002d1076210030920043c1141540e40381d07645c0c082e400c010180104405c0100341800c003410054542c8103129440c0605212003c1082c403004006e4421a11058407824203550700e00c01c51202440014011541110515001201140041c00218041d20708032000603a25168040380200715100200401010224100c0e0150030f0001d5504684e4545c560b5403031208100c03a00030840e5000115644000340612001034005004d00c030301c3d002030f4102c1e0107160580303203070407001c00041d074a510000794000c0c0018030f80140d00741450302512001414070100c0003120040c540b120528070650b140c481254201928000c0c0d044205081000740e400c115882c4030701880a0b0400c00012080c6000804c0c0c00ea074460346070020500d60b0502005984018045008203e00d002001002030700f041605407429501091700840e4000305003000b10310751003001c00650b034007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 718738785 1250 718737535 718737541
    0x50904090206040911071202070303080f280e070f0b120403020a0219082e090f05060103080a080c0c031e090a0303020610080f0c01031806051f0518 65
    0x100401030218201d912410a01010032600c0d100c0c4604044c0a0205548503540c0c6010300304494014007098080046520241052002a602c55443d68102020010461864036042019005418582c84580101c614540c20660400c00394005441e610110800d8803440c9440307004500000c04030380600342c440c0004115081001c090302004c217500c14041d1040e183c801117541e0014040000701607a10707491714020b42e0141f00c034490038880752400681c1800e40c0b0700e019010b0840d1040b0441c000e0210300501d580c820b0b045081c800592003031700c14a0781c09002d9441544e101e141c07200380c541090901d0000168610001500f84046d24211218001c50400560402c20543c1c1d40300389048130801c80d8402c8113401c0c0040074840d1600300c10302c0c014500c42e401400161820305120107a0040645c07142441c1e07031000c0525420b2500c0400e510021500038640400d001c03030b16916035494402d40c040010314183c03501c800c20a0786919254130b101400f80d82400d942c861a03a40d420032000d0703041240c0d110000c40400c008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 718740035 1250 718738785 718738789
    0x304061b12210212010918020901090c090e0c19090305030304170d1b020d0e0f1203130603020904060603020f0a0809120c010b09010e0c0a120b130c080f01060509 71
    0x10401c07040740000b65081e848404403801200760303048080300f581c04403c61070050085491034010f003c64034183d05403560b41c0c04107540020350f82000c10300c1410a215075072511060020710401814018269000240758141480181140d0310340c00015245003022003000d00200607481512036100b166000401141152100e489940e860300d140c80294020a10400500c2c02030300e540d000d0344200d0700e00010800244a40c405003c0c0c00e00201c401c40c0c401304403504c20750500d03941d02c0c14803e800444003510003c5001e4000c05034a8a10b01c1880502c107901020100300064142e13241d002420b00c80d105031400e0141541c1e81e4400c0d02079014851003002150014400100280c0c410410f441d44450700000315025020b00200145156200c03c5104990384d44424004c00941048440702d8010024900b801c0000e00d00310f00300a4441c000e5840ca142040044100803001859a0f0018404510018000b910840c40301c00003000034107140c81c0d03030f1740031640600001d020100300c52401c604850181e00e4551030001e0b6041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 718741285 1250 718740035 718740047
    0x60117120a031506030209010206060103110a030b060c01060f18050412080405012a0305090a120c050703120c06050f150d0609080a18150e0913050a050304061b12 71
    0x3000108043d034824400180e6140d4904030002041c0c1d98600680e150041c1000a08003200241528107160910799a2814114008201c0b0200c41842c1f500044121235000010054441d07440d031042d03a0340c00c1070008205185208070300e4080750084499001d0700d002e02503580f07040d07071802c480c00351451040f05109200d203401040460b6205115070000176914030f5405200b02e9400c640c140f010b4544d0271140c60300e070015400d0711807243c022807040020320860b003a99035103c90794082000b003442000100070204041100401000014541c0b0030400e150440c0c41c101c00400b400880d04050f925681880040348440240c1801e1900890b546224400d000c0215401c0c4112100100011920317195a0740340c3d18085100c940c080c001c4c103401542e0718030042c00100450403402d00540c02150004030300c004c5800c0301d690401c4100321107103c00e981007031060b91038202c0040c204010103070150540c041d20b0003c504000000c4000c00c00d681040d120000100a58000c06c1340b58803400c00d009050280002d00100182e010340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 718742535 1250 718741285 718741297
    0x60b01050c06070807030b040204080a26070602030402040506010804022407170306040e060f2809030305061011060112050c030d030606031103070c060908090d0b01050306011712 78
    0x81480c0745440455070000d8030b880d0040303800c00000360b1060140030f400c1e64140511611103608440640c201410900703071545404202c9001402211200c42d881c0900c0c80000d44403004681c4010240d88686543c05e003000a1350048800301e20441c40c1c40002040396000704038441c01181c000d021511401c0c560842c00b800b1085902c0540c12000060103210001105000e87c0307140300d84444603042d140d05103030042c0f0040d14000018460280c200b07000b001a880e010381069940203a503d005510240c4d407070b1507824000840d21440ea4086814031403c0018036130181c10a0340520410f60749003080c10032400e02180c50388040f0f401210f00e9040701c401040405200d02440040c607001e1404d60742001c0181c40005d2422480d040740c1404642c56100410505401d845100d01600c0501d442901e10b08e48140e0040000036545002442e00d81c0c0c03084030034140002017058440101000d408150302c8a91810500c50000e4240b02d00c42c46407160340c001142851040b41d884615206410040c42402207035106030032150044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 718743785 1250 718742535 718742537
    0x70219081e16140a06031407050702061b0c0901050a120f020a05040e071a0a0c02010c0c05060a0504030b0901090f0b090c030703060c020d08160e061c05100819060b01 73
    0xb400000d02951800c0e054500030300540300b000860144103424400240361030751120090500d013800380200180840306480e8400c96500e000c60741e6401034400280b1a0040404000001541c50380d01d540070316001490b408010350488000c12541e988100b0041115207600404482c48004e01c06100001c40c500c108800c2544001c001880d00d07a2100f0215049032900c8501070301584c0310303080401c417412980c441302407800e5040480601e04025040d000c0c040c6206d00600078108041d41019400340316400c20910013400e0010081950f4000d45203000304181c01138003064410008100100b07039007a105104c1c04407450341c000040c052218164503600000d08000704414140e0140c1551a40103550030710204000d50b214040004980400d240001d24000c508507142052043d06400d000900d0010003041010f44514642060000c0070003012592501038110500d58840303001d1042c0c1d0056150342c01c404d102e040010300c40c5520942c0d443d02d440c1c1da200700d5180e404e044480226600041b034955000b102e440001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 718745035 1250 718743785 718743793
    0x90a030905010c0218070c02100c170903010e0f0c12070e010909080c1207060f0c080402120102090d050331031e022205090307031e030e0d05070219081e 67
    0x500404511082811104480007c0c0d055244d04118039042510950003002031402d2141d0031103583c0d450a04c07100083c500d00300e0719004030703000103d60740035006856815900d00603100209900032110f50b941c007046034050310900e81444540c04002000440c0ba0807600004488415a442c0121400c0240300d0441c0603102c2641c04c018003410a50f04104000b450008a483c41c0c0c0d82d50564100501105d480901d41d5110b141454002c004859100001640050701144c103441e0104505085a00902c0780405030782e00070400c000080248040400134140040c0c240400d002240220285502e020309015100c14031080140d01c144042826170024070800613803504040c80f400c00e5500016907a000489450310800c3c5050f034000055041801020340001d42400254100303051650054881048030035241b00c5080718500300305d02e440c4290003002d5010320040550392141940300009005600a0300164096541c1c6c00001d007007010082d01ca8021103407030002604a0340741c0d180c0c0e0504d130750642c40c603004180d01c2307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 718746285 1250 718745035 718745059
    0x9060e06040c09060e040201021c050c0d050702030607111c021011031f05030d0e0f090c070311160603021c1d0c040212060d03180608070305090a030905010c02 70
    0x80104502402140500b00010140d468603c0c0ca10607581c060b0402c119000001040c000180d03000250b000260200c4013403132400310400c0d07904a0359805880d412100c1445004054610f8581010051000364000d90594080e43e44000b0b00b42c50117403100c0510059070740305101030713101510030000c14117411200d4815692011078030820201603e80740601c00e0020040001401640069000d21080380100340451014240ca4040000e440780502d0f0803070400c1c008a9103442d581691400b007055200c2078010031083c0c0c80e083c4984450040e0b081044210085801c1481440071100d00003030440c804951141511485410024210060b401c0f001d68004901407290702c00e00c4048060103006402024034103c80640c01000044a14018144035482e000354410801e03501e0210482062170b0344200c040d500c02c1c059007201d1408030340c0f42411002490300c618403030b0404100594840c09850145502c5e940034000e9840c2c0e4082d40346c845c0c0000100401080c0744c220b04200550103000c02802c04d0740004c0c000f10001c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 718747535 1250 718746285 718746311
    0x181008071404140103033002030903070302070905091c20030d0b010306140613030602030703060e160c03030506040b060d090c0f030c0509061302070609050d02120d0906 74
    0x108030760414040d0400c80c681079552410b00d88100b030010416a0a10000e6525588000c0e00031f0801c4240e0400303204041005825400d01d1030100005c00c3d255507000c41d80c0c1c1c0b8010355101d444e50820304d421001030040700000a0348071b2550080c54013903890303000940801341110903031062414110340000180810138800029a00c2e10880c2c1c041102c42010146a03138160250400c0b04540d0385842c0c0c030b41030600d804018081c40411030b01c080500c0320709a402950300c510003a10862601c10075030000304a940000104000f640d0305401800499080e0a062440303034960326400300da009000300035000002c034083d4040d00400d10940003a0303001038001d0030002d0102c881d107000c2002907000020341408180c41e180301e101040442c03590705c802001d40c51048824a4119a20205c80c0010707442020b01c00d0940b24080f5803540e640c1d0582b640d001e0320701d58003155a030b401c81c5003103400341050803016900c1c3c0c0100c2c040d14040a00120780481007105442d40c962511a004004400a0981032400d44e800c070354400e1001815 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 718748785 1250 718747535 718747543
    0x9010c020f0d050717010e03090409060b0a17010b0a05011706041e05090708070b0409020304080405063606040501030e0312042114030601080a09020604090f0b0a05181008 75
    0x2e40c0c00ba0001e880300605064481c0303216000d03030300340e035a1980c50900741075a00380e8048240c0c0c3d01e01c6c00444022400103400d00b08000a004104072182c1c1c04090303d200060006040c2c507800300f81110030380090044403405020018102c04a209150206c1c203001d20441c5104c100901081d07011000500004085c4903440080e035041103140303010301c0d120f81e0b02c005010600008019101c018003040c40101101c1d0b0400201c04500d0246103c2c44581c2078000c030210b001c1280103411b0f02c02904002e0001601c0b008040c001c03081c0c0403248120381103d5001101188180790303501401402c1c155000c1c05c2e0760315207464a001100142001501000c10740004c2c0034180115041c10903083c004c901490700c03118032a41180b00003c8a03140e0401039020b20010720b0800c0c1203c00e601c0c0549038040d0007420a0f00031961190f90303d90290143c0c20f8003d500107400640400e041400d68481403c0f44121030040280440e82000d02400100d180510760f4081d4480e250710701c80b40d036203c03074aaa100c3c00c1000c040d9242e0ba80d0b0700b0f01c00e143c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 718750035 1250 718748785 718748809
    0x609050708011d0114010f1503020c03130504360f05060c040e0114010c0303020306011b030206010f050f1c1a010305070311040c080a05060609270c0a020309010c020f 73
    0x1100b0900f80d201ca03c80d00003401400f280340d42c040210a195454095a0003601031140b00301300c40c004c2900c00e5141e003980282d042e50321040d0700c103050b00d0350b8082525240c0d28980706800385a1160745007146508040c540e040c003440050100c07102e000e01e0fa400d0085002d0f05001405403c0720419101d00303040c400940306004842c0103200c00010715480f0382c140840c064069a050f040350020110f00c2c00b0005041c0e03400544910701c25054200140c0da52a01401214425a2072000040c2c0080155400d41055800528a8100d9180014844145884204224042d00b07985481079002d050b14001d8000c49502d65410207001e403007201c8410032300301c0f80b010451000009070300c291002d0700040320070400d0040e2071460f0107003010221801c0205100035a030103011060003074070140c48207540717030300040c603075100c0e0411034141e1840141590291034004400905e130b2084100c045290352010000706018541d05c03c02d80b82d0154003030b0081c508081a120046519044050381a44d0000d80c6445070f106c4c13902c0392100242 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 718751285 1250 718750035 718750061
    0x60d0b040b01111507170906180a03090b0c191202061b0d09020f2d03030405012705060d090302010e0721052104060f05040e0103060905070801 63
    0x8045901104000841c0c1c00301c650641442003440403d00100d001207075046282c0c0203120140361a0700c81d20703405c554200c107500710000c452610303500b80285d50000145ca1ba1245000d070000080a1101400c0301d600c4418200000b03010590083e0140000072309503001d052000048022501c030f21048502012402500b44000d0315198040150201c8440c0c0c184400d03640101c00440e05070501e165101c2400e2144103005409507026a10001c85045558209862003496401060030000780e2807038840e8142c07146032480341c24082804954205280c01c01200741c40c11240141c4500140e4001550801c1031010b0000d907406548862680125081c0c1d1054058091a900740f040041c04015501e40642152400c001d212410717400820200310110401070310650710600f40c6001040c3c40d200f460054580214070884c0d2650740501c007a5110404012000360080f501c55654104580841043c280c4480c4258014583d2100020005002140161701710724643c0c0c3c480c80485254580c1c0c1d2089a00b16202c0c035810079 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 718752535 1250 718751285 718751291
    0x406080718360b06010206010b04120309080d0f020c0907020d050c0718091101030b031b0d05010c1e08040b130f051002041412030306090c12150a090524030a02060d 72
    0x306010b82c0050f10f0303078000b100f800201203950520440c105540103d01c503150000d400303019040c08051080e20f201e03001307000318004c40760b803e1602500034201042e94030089005100d01c0c00c0384000e074070f0603000d41030090b0441c3c0c0192440c5600c940f8112a9584800f000c403070684244e040005030138111240c64821030b05101000144440e5600d00b501e030305d111804105d4100740c100b100c2d204103a640071072028142c00c04011b1500028486070007050311030f1841d01c00940654604024140301c6500400110350340e60260301c0359090030b002c80105413a0f540c0240c402614105d00c0c1000110411450b101d604080c074022905030380140d640d603580354507003c202c40c2400113030fa401140030001007402d0308400f0100c24007200c1c88000100030110040e646d00000b88142d100b0082100405c501005040c00c8541d1250ba14401c00c0c0c2c240380c0461281400d0103008411801032070005400a145d0135584107190184c40700c4110601844030121449552681c254a0346500d8040c540011005030707500d900408212828607804 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 718753785 1250 718752535 718752641
    0x90f120d060608041205370e191202010c080a020d0801080102160809061e03150d030e0d080c030a0908011d0604080706150b090406080718 61
    0x108090301d15560000d41800700354000e0100045029003540a41c0c4c4151a025844441144110104904116074111409070f40f100c00e10380d05c00b4202c00d00b5010304a60700d401c004ea01a0b0000d00c500c138006000460b041c003c40c030005010700318400f81024031041c0149000c503444810b548030703d080ca41c032020002c0096405800085001d60f00030070f0060050002c20001c6041150681007a01c0030072080c1c0d00100403c40c0028001403581e60b04007903c200310507000e85000c1d5420130130b43c08030f4158410380b101100410f2144145005140c902094045640d0660b00e1a5000c0030040520145108050080355002c50610503030403044c404101425103003149903600b001c014130b06581c407821980140d54507400010790480c40d0b003920600054403904203502290441e13507200135040100040480403405103100701010390025554142c0000780040c22401c85003088003c1c0d5520065681e400303548500c020344e04800031004072066490b4400c016048000700038082200c00e404c071410050b000c2c004400c0c0400c02e03800203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 718755035 1250 718753785 718753807
    0x10e010509060106020a030831031701140603070e090703060f08030703050307050d0b0a0608060f1e01050a020f161a0f070f060f0606050c0c01020111030f090f12 71
    0x240c41c0c000c0301c40d030040c1007a5418400000c0d165011060080c080c800c8040118000010b450302e404c00183d007110b10400c8850b000c0e1090007100d103040c2d0b4150001418840701204401e040c04040781210441c80c51060002c800c0c206011060300f00a214606100011000303c1003515000ba01a2160f403d90b900001c5031401e000e4904a24403954100c10082da000b4006100082d4210080329080501e604185480b10b00c3d813a62030014111009507580c02000211001030802d4000300e10305e01445080320b900031054206002d001000301071321019070301d042c40840c0903000c40d4081c500600c9030aa15105403a8a0b441414086280594082181002100300c43c0300b0003500c2803d10000c51550700c0c1180c01854064540c40140c0c0a00078004080d10500da03544d40e11041100503805147c42500e040028000c040d59400d003c5c00d40c0d00117482c040a2402143d03008400e9601c1886644280003604120301c1c219103e040c1c564462010081c00c0074101e00c200e010720b01c075144c001c02183c43c2408c01110415614100703101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 718756285 1250 718755035 718755041
    0x2030916051f022104290d0b0604030f0302010605040f3c1107060b030d0c0314071e060e03070b152e020c090603150a1d012004030c03080a140c010e01 66
    0x141d5004c00814503440d400070341c03818211104211080307c04511414001c000407640c0c41194002081c10481f44044020075806403c028100c44046604100c0241c0c0d11510409a5090701505550014252082020800c0d242001c1418140c4540e05010030002c580022040351207045007098141c42c08661482048418012a491100244d01500c1309442000d40508950150000241804008941c000200313a90201341c40070320b0303007010380d0b011000031861403070105d5104010151642c42c14150784034960f10001045a8200d0391107811030540d80c1d81c4080c1c028005000400c181c1e0f10102034085501040101c420703241810003101081d0300e030100c01200181c0342c220803c28680c0150384030b030104210783e40d02051242c0002400c07106643c481d59074079041002401040c400c0d510943c560300040c055900b0550142c10340244080a06013144141c2d01c180364180514800103215081c89001440003940e0382c070181400e2956400d000d801c4c180300c1d02c0303a0b0486409c681006080784e9519200943e428030240 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 718757535 1250 718756285 718756319
    0x106121502160314070803041b1a04050d05010f050106050417010c0815040e061305061503030306060f040504110306040c1409040e07170102030916051f022104 70
    0x3110462900000051041009001120180900910030140c144402c400021580d00f42e90000b40142e032860245094040001d00d12441e4001c40c4100030081030303c000c03600480c00c3d01c814203440203062510303000401540414020084a0fa5504c80c0107004001e60720f80100c0e0b000e40308986a030f0b038a40e410a255403410b60224051210941c2c10303e80c13000d58903a0003500f1039401808260241e040f411401c0d001c01c0141940b40c604801034030400c010070441903807001e0107805040c419410703a8000d07168030040402c102da03060f050903810342003000800c41500e400c0d4001c080141c0803024003418180c0d104001412940d400c7c01c00d04520341c00100304120b41c6014401c140c69030b007441c18450500c0680400305034081c05030b000020b018660f21011902814001c0101c58020083d50250044c0100142560781c041d41040d540412188580b000d02c0e090925030a00e02d10603910003030804514014800070030007520300103e9500082d03020b2040c2d00d056020480d0404000703140d40036040b0382d44034602003102034190061 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 718758785 1250 718757535 718757573
    0x1b0a14060403050a111f050703080a0902120f010c020a0b070f1101060902090a090203240f03010207060209030115030506060103051806090c010f0903020d020d03030e100606080f06010f0f020f010612 87
    0x5510707010b00c081c0c100c419980d08603012b10301003043d69030310081d0310010100d60401035404115401c01662051001900440f046035881c002e005a01020000343d07a540814000140400300c103d00146505200d004000000c0d5150310b01050f5135020b4800507401c640c4139800812880ea00001c40c80340e24204603980e48010880582c0c110324626100f130340105290303e10091030014140302c0714407441c9a940c201c000310700060010021542c0300785600e880d01c000d50007c0c100718082d50030300046030340c642e02034a00394089a8004016100540d150070044004010062000140b000141030b0402c01810401885204000510042c900407000000150013010140305000030020700301414001600d516141c4e4000d036034103036120144400c01d45400d4024101860b444441440741c000c8100d0000e42a400c804103c03816500c88000f2500d40e122800314641c4116a5140802e03101103a0b1111288151b0fa0300b03c00403400d205490ba400c43c1c1c00d1005003568641e91203c00b610501119400c28403801908021440d026 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 718760035 1250 718758785 718758829
    0xb090103110a0b0a0e040e0c0a120219030c031b0f030308070809030408210c060f01031109220f02090711061326070b04141b0a14060403050a11 63
    0xb40d404002c0580b61503500240c000c6e44c40780303040c1031220003c0041182d01e00e0014540c19882d611402108440005080c00360301c00d100c8246099900920083ca54080d02c0c1c000c40100c61403400c40c4c40d07026003000300b50754450044803826000280c40a08402d81c0003d14401c4e038501c281418180001010100c02038a2110b954000b00020085408006503019581c02c43e403403d1400920161040540350141140444a0307000721070070440d140542000050581e4828a00d144400c4842c4044c480e45420460790505e25505071194142011041400c2606982c46007140c43e00744103e541c0480d11040040e1401c0d00490b154030b101410009052001c550700540d0305800c0c04000c0096118079200404002c0d060b040d40562888200b90000510225060f01d030700201c943d005400c091500d00381c102a0418850030301d004081c80d00c0c5a207601403005000003900140054006070800b00702c2030518502c000c00075845401013000100181050158030016405100074015615075241440070b000c0d034101300c18000d030701 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 718761285 1250 718760035 718760047
    0x2030f0f09010501061b0303060e0106050a0f110309040504142b02010b030304031209090213150201150b030c1204060b03060c13031209030503190e0114120a0b090103110a0b 76
    0x10340406c00b04083c00c810078150380c0f690550709041c1c00606e4950010700e10285601c0012811603001402400503c6036139603510103401c0c411008440342c06941008034555001000008001c0c0381513040660803901a0fa0503240c0901c614107241d18082c80304804018403d600704110240e2000e01e855958407002c54002444103214400010307499101d5400018100e034582416841d0312071140c4c0200700030340010b0b0403c43da22075040510050803c018491205040d00704581c4074207803807041c041c842c08403407400303d00c00070b41d03080c02d01e4090b45070401440030384d4815041c030008030b05880c3d102409000700d0080d01c00243c0090768400341820a40000c05141001c0c10412044100e00c440e001c0c510100c94000240b00810a10b840d03003219a0b00790740d0302c06085e500c00422402600741d0403217021a81ca0045403100c00400d0641c0d0b0042da001981c24044c2c1440c1001440708107206521442c40d00d9200e0032402d00000c000600c28006081807100ba0000e03144011078100066450816003000c0020300184a80b05003000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 718762535 1250 718761285 718761287
    0x80307030314180a023007091a06180324011e0305190204060b0406020d030e010c0c060b0d0819020705010305221b14130e1c1202030f0f0901050106 65
    0x90402d4001e000e000340c0200c03440e2002160151059184a001d06d101d2413003140c1541a55602c41401100105441d00d0030050280443d19100c5801c450081e2075141054810421407401c400c0300e828164150180805001082d19500440301001d2202e102280140d418038085600c3c00b08042000424001d1000090020800000d0107940000741c0341c050801d40003213071021070064509030713000204840000c0390100f81c0a4010a040201041c2c5680401c00d40e10600e5441e4281c41c40c0f40c05140208588042e504040b683d42d40041481c4180a00180000b281c155265505503002d00e00e14001e50903440d8103084095414044400142001d1a00703211508001c00c006405110340e4241410780742d5145c0c2140c00700124902080c10b1110001a802c48640e9514908c00314800c41407038081c480c2c840d80344403c0740c0300c016100701401003612600a11641d400c3c0c10b14122508803c110100500209000442d8819014001144541d800d4501c621071410036440c0e203550b00101401007910703039051000602000f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 718763785 1250 718762535 718762543
    0x40507090e1005030601090905010c020c0f130b10170a060302090a0e010f110a020c18010b2508090907030524060906072102150c0a0908030703031418 66
    0x518402501d001440d1035144181404500719440306805001d40302c00000c4400013640303c008107174055802889030099882080361a0607910308815404015801907d265060000b0ba04c40d6880c1040300000c1c2c444842d030005101e52400500b403070001010075604a00f209101000c0c5608802c4010083c08400c1c155400100060350040c080074042c0e643e641d00b2406048250040c0c0c004282041c410090150b01e45203041c07150f80f0228401780544a004c048040314100f54440549007840340e43d48500f16400d01440a02d81d0703121844036610109651800d0721803002120760019441c0c4940308850340d440240d018040640c500800e41e038180342c9080304000700d82040d4840c0305000000d42c1c0451014403410310000f01c150090380c0c0459000080454080d0030440082050b00048184803111501c6586158080340d862004083d01c00740c0c0070444010408500b00d400142c1420b4143d4108240354548507040c0ad032568008100540020fa101c001a10002e2114010f46400040240e51000e003800034031440d6070b071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 718765035 1250 718763785 718763789
    0x40201091502060c0d110711190e06040b0d081b0c220c02030d0f020315030109081603121a0906040e070b0304060204030f03020f15160f02120d061404050709 69
    0xb10070000039125160901c0c55000032106d01904800946070103142c14107158500400002c207005040402d401802219805540700489181200580710740e40e9440602025103501061a50008561150200020051800340c0441413441d180d0441c440c51140c05d0b9458100b500130658091040b02c9403d809414054110010300c036400d441c003048410210320100d01d58481d07001400711140c503159041500841b80c1c1c000f13500a60003040c11610050301002014201e640c3c507103000300301601c108103a43c41c601860800252260003030030aa0700c05010303180d4520135200501ca00b80a0072040200702c00c082d20317003201003a030051030649080001a0000704031581c0c500b90390040c1c040995000c00094200034198044070080d581c002a40e00040c00ca604e000b958400d00c0c00c140034134900a92410703c8440304000704d82d40c4658140d41c40e541e00810340d20380503112245003504003c110300808545031107160b1000000c000840c04e10000185aa103448401c00c00e011404198520035800c00051080466001c1c0061003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 718766285 1250 718765035 718765051
    0x6060503070809280201021b180a140705030a051008061b0723070605070c050d2108060a0f0b031f030515040320071505090a080604020109150206 64
    0xb41c42d45a00c81514a04102211100030504e42d41c5022002c0d0607080b400345500c28400c0c0c003202e0440c00d0340071111100101075002240c03c64040520301c4080c00800d0040381d00032240d03510010b58104044a40d0b1902042100c0c4403000c102c0c0001445074405c0a881025031180e0007007044a41941840009900c1700c2c1e020744138094240721424020a6001e8801c00c58492652201450aa00317a814070414403010088000c408140281c01d00050024080d40c1100c00c0b0950003200050101e0a000810211220961040c2c3c2e58150380e00e242c038885600d41000901a01140c0ca0741c40d01450035904104600489820803480f0411824041140f407161a05403500b0020416107402c40d4008025000040710043e80301815510408076003481e00000e0601c2c640c0114020743d20a07c0c40e0400c20360461003032085d110b04a180740d104010402615018403880c405010080c0703405454030401400143c2170f100c076500040030307a41001f400d000841da0801c02000c001d04000600c51071103000701e032002e9214440141020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 718767535 1250 718766285 718766297
    0x30d0302031e0a0c08011a070303020d0b041401141e0d050a0506040b011a070206091306050a27090b0f060604031a0403030e031c151203021006090606050307 69
    0x20784200301688a603542c441c103045207441c603142c941c18100141001c605503501141d40348002042c109903903810302c00c1000742154540d151020550302200254003440d02c0e0514190760381c040413040d03540c5004544100b81c0044580c190b550400c3c204540300100c192a0303a200322522202005401c00e0007080401c1c0c503000301d8100c0402400780c18100c1c1482d040040090260042904000270042c2110300303141a100d0454a106031300c1e8001e01c0c08070389403041c08401f0354040e100784158417030740c03504010344e45103180750faa0041201c594510208080481e00d4005148201d9070740c2100d035169000c0c088041800c2050281071107100304940700c1480031b00c40a05041b481c1c10302c80c00018069284c0d8030440d00215442100134951904440c403a100c030b50b006640480020b0f042c0101002441e030000180c902d04000d0b50b120700789195a03800500010034200491a058503481d03d400640d04903000098283c1ca80a6000b50212040c506030041c115840364000c541c0052416106024266200b0240d1350303c14000d09100c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 718768785 1250 718767535 718767541
    0xa0c3c0c08030c0709050106090303050d0b0a030512250b1b09031009051005221104050705070317040f0201030c0507061505180906040f031124010602060402030d030203 74
    0x111206440c550080c0e5042d120004008514000c00610f038021074000d108100210390706d44c10304071b45280c1d01e8403001d00015024468243d9108159024112a6000038030383c05041b942e9907552801d2200f040b10b841e071080d50100e44c0c0c4091000e4a0901540c0035110600100000000e5550905206000e0400d83c10b041410300003041e15400350045440400000301141e82244040c441c640280407200c0e01103a040c080e180d00e00703021460718000c40340181d41d0b62031124200306000700c412824003d01d920075981c03002c00c0400d0750940e0315944110f600170011355407002d541e4203c07030070090207007507910307030740d0300d0340c92a040100000304a285e120202c11641c24600820700c651107070411283c90041d040d0160001f8500a4030380c20500c40608118202c900036142820b20144110000407040411184000d4a80000d07001400040041031036154046c42070906c180c911903220000351401e0f425840395180460010f00078140c038180886030b03500500703071440240350034a00b541c0400d8841c03002d1010002495004004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 718770035 1250 718768785 718768793
    0x1303030b13020f030a0c02031809061519020c01020706120b0609060a0801140604080a110619020619060308070f051009150c0c050303040b1b0a0c3c 65
    0x4554040c640e00c065450304045079000e84194070540d01700750190304c0c18118405403800441035420486824111800103202c841c240701061000400d8160307c000c410344000242a903210107000b20841300003440c840340f081240c000e0301d080c00010366641598000750080200d00e03444640c41342500c074035000100302d200c500d10210703403140154181c059100101080580c03046031b00c0046913040359403602070818002290801d000c00b17403041d80a20a503613085100c042d40400d528500c01200300703102612882c031f8440c101800c8032400e2140011480160880000d11440c0460400245c0c14030241d4441004030902d16500c0c55564402c07140010301120340c040303c40b4140402807094400c01c03c0314020506c400f0407145451850858100e03c00d01c102441d1801d910043c502c07404422031700c0346e03101c40191302d507071115194000440300080800010012a4080e1051400490050710301201c440d12114203a15503494042d81e2540760390a5503000424650140501c40207400c0140101615229000e03114641820 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 718771285 1250 718770035 718770049
    0x313111509121f0e03160f1a130206070f0206040f0f08030a05120603011d07060305090d0207051c0f120816050d0b0d20031612060c0c0b0c1c051303030b 67
    0xd21140240103404034500303110b87c1c5500b11007000d20032950210381c03095045d00b98a00b5070060340c11450030020742640c1d10041c1810300040c048140030701000700120000d42c0c0000e0032071380185c018541a1504000801c04200f0342c0031800f01a18051028504000202000806a00480700b040000b40e001d000421041c0d11300390700c042900000c6035203c00c1e18030041408240d0318010740c4252000a0b15200005000074000710780130740c13140490b60141c604245002c0800c480d01031aa400c2581604c082c0840300e00045400700d03000b10306031040c22030030606000d9081c081c10034080100340d441c18504a00c0c05102c60f9501804a410480741c607880082d080f19800f002c503440d091080d00040135211070750300000442007407203092900e2035030490844080141e2140e540b1a842083e1040c2d110159656000e800020070903040081d1300d51041c6404044d00400b0b480d12a1010ba0694800d020208002074500902c160320080075074004980d90240000c0c204000421002050b14070080d08156403010602c0301952180 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 718772535 1250 718771285 718771297
    0xf030f0705070b04080319020f0301061416030f080601021914100e0a1103030c0c0f060910031505010201090308061003060b0d0e0601050a0b0313111509121f0e03 71
    0x6100c1d00d014031303180c40d282c21994000e60f071107040b400000418180c0c0c1781a0f8001c483c03014801c1c100041c00c5174030380501660fa50040d0500006440000d1186418100c810b0040c200d4032406a0798601c00c1ca00c801e0700140400002410090454001d00c094961400500d0750340411a54082e100c400011440120181029001c00c2c0440400b42410032650b10000c1c00558150007a004401c00044a0205010150380b48500c3d0120070b078542000101c85e80e47d18018199941e42200600030f81d00c5c0002a0740000e1045035140d03802d8000c656a0418214000394080340f00024140030300080207020b0a40c2c4003e04109001001d5510600804a00e05880352080d08a8001418403d01641e201e074041123910020f084080c0006019125100000525240030400700c02200e07001c02c0303000d142d40c81d401d200c1c1c901101000c0e415180c03900340101000d856221409030400d070061200c400e6807181c2030b5404003c0701255501e50346c03ca59000600074402c1c284041d91121940f02c048000203070300041f8000503800d50242e1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 718773785 1250 718772535 718772543
    0x50c100e030106090605100929070c06051b0321180604140f01060e0105131122090515091302060706050703050a06240306090f0c080c0f030f070507 65
    0x4078000254058080d0021030030354804445081e14041608021035481c04103202d12700c002915082c441e0700302c0c18980ca420214130b2510048603c0c1109540301d0b900c0d20122580b26500041001800c800710003608030741a003031488000c0c051407429110b031600d00311508891121101c1300102c4c2011035029201c071040100e450394050151065440d050030b150f034034030301070701c00840c407500800030040c0d6040010b10404050f5545018507107016400c000a10009124104441c0149550ba103071286da1004240003401c05800b014014407001c00c003030441c4509000c0c090703108006160900050001500500d0401583d4a1055031400358603500d16089454120021750f01a40240c000640c4000380100ca13045a4480c103180e813414030140e1242e000000c110385443c4205c01030640748054000c0b100521800f56059040246000314006807aa102101103406078040000d00b03640d01d50b141c852180d042070780141e01c4407a46620360308164088400448a10000307000d10080c41000e4006801c89002d442900e01060300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 718775035 1250 718773785 718773791
    0x3080306063f070e030d0f022a1e0a03080715090305071109070e010305181914030a0914120102031005091b0409050901020f1602150304050c100e0301 66
    0x180c0300c0800100e01e010781c4142c01120030070006218140a91a00c80301c07410094002d00c11172500860840e110640c04611904501640d01880f000040107055071102240b00101800001c1c03002d004c100a210b0320403180360b100c034190409038106540b004c0c0326104894010340d80b96075030621454440d5500300000d5423425001e140004400c141580310003c1c001d8548115a001030b0010200104155110225003001c0001d10808914030254480d400440d00300105a0080e600041001460350a020f820a0b1410107a580380c0d95031000d1200300107200d1a1780b074005019625001400c10001c081040a0041d5182e0790803050b01800da41c2c41d01e60207040800f058400854072070910400e800e0b92000544141d070305c50300404000c01c00311495600031121880741c061103145020300e03150700d110150800500c004c40c60755080c840da2172881d0010008050410424101c0c2104900070310400c01e04400c02c44441503110024420040016000162000e40030f40880e54210150221441142c10403183c403515070f051f5003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 718776285 1250 718775035 718775107
    0x31a060312070305030f0f010b090d060f0c02250b0a0f020a080304030e0906030c01021e0703020a1d011a0403140a020402041707120f0b09210301090509070308030606 73
    0x4d4008091805008454041035060b11400c4040b07807941002c3c0244513540740d007044680c7d01860520042c40300e00b4030900002c540f4003109a000000c0310208124140540c000700700018404c18007600d850925008801c180052a080c00c0c198060350040c4201401807050003048003c01c607000700029141f0a81c040300380d540d05d20b81071074020301c500c952003145402481c4c0280894060315003c210303120b942c0c1041c0d006183c00715030350a803821407200308280c80d1f4031070141c1342d408000b50300c40c0c00c8520041c1422161189030052506c80680300d460050b802041645501c0009030141c880c07a4088a0450382c04c0f013003135818410080d07441d5003000040d040095001e440081c0000344050715444401c1c03e07141c80000c0d520002d546d440c0d003216010310840000c125044a400541c009086100310a41142c6000d045500c0342c880100d05460b007051050040c8296540803004101c030070214081c091b0b00c0040f800c081e103415451a507c020340f034007019141e20f1041601080c90035841c0030038407042401501c03155001074880 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 718777535 1250 718776285 718776287
    0x90a060c0507050c030a150209060712020c031006060c030309051e0c0f06160b10090507020604020a0617070318060908070204110705060105010507020d02210610031a0603120703 78
    0x10b40007110407600340c000c01500b4100c03840d0114406109680207404141480c02d40064100290311025180b607001e407051054802043c120380380300500308103070380003840e50f284140b00b010b1030046900321544030710781818424010b0701c2d4890003510740543d15080100d140c0300b8510b0180e0800d041c44c01c18150f50590040024818440090068803035581501c413820740e181c200c8207102c854070503c0d8122445080800c90180000d8892030f450380d0042e6900d1102d075069466104c55810f8071000d840290050340103000b40001e41c0340c17200010000304001d05114805c0720b56800200703800703807004007003005050340c4025510407444402140c0515580c0040c3c1013240594500d441609600712071360903402149040030f0385d2051290715040307a46054204000305207907882c00004541e250302040c030490b00000d210034143c006880700b10020750350408074103e440381c0c034888a880790320740346008210784c09001c0c2d071810030000704d011745150902500b0b14000303040c110394034000820701c4c0800042c510522084002980d078189 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 718778785 1250 718777535 718777537
    0x1407090302041a0616030908070303050d0c1e080a060b0d09051e03071b1d060102010c0513060c05070803040f170304050901090c0c08040b09120105100e090a060c05 72
    0xaa4070840d0100b003440c03052500c142608040750755240c2c21480401907072941072030b001a0400720b18401d183c2824902d44070005130703050110f15442200411030119031721400c0c11050207180550000c074a00400d0826030b0400780a2008000428881070100007404281d4001642d0000c0c4081d2003084886039aa400c1c1501180017041d103072000b0b8850b0301683d41000880c070318410500f1548040313880110700301a07094407200c0d85981010300190091100403000145582c0207580003a07040e222210104481c07a14600290965402342400300c1000303001c014042c00c0c000e4003003940c006e40c2c4941c42e25007001074540c43d0461801c06d1982100c6d0052202040004040c803000e525041503800c1d4405808124002201c010740da03019601070294007480741c50060061284540c80401045d41d04d10385042a4401d44e190420ba540c440e03000042e6009001407503141a0801c8021130782031540d0f03a8020002c61405c07000242011b9510b0054440c000300400108644d032200f0000700051030b801c00e0040010203141a005802 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 718780035 1250 718778785 718778789
    0xa0b01080c03010e01090803071d130b12010c091a0c0609011d06061003020d090c06120b0f030d03090215121005090f0601110106210c120f030f03140709 67
    0x40b80d820400700340001e0206020383d45005601898060030341d101c500090b14051210030040190b00300d0101400725650740c403d0300300c4201c0030046001030080c502c2000e01c13002005500c0314480daa814000f03c050a41c0e4441c0c491822075142c841520001110001500000d200c0c080d01c140041c0b04040c24001e00c1350065100c0c082040c0003400701040b41d200d200005846207812580940c1c0712102c00240702c5a40d000c4d4004000a07030070a140000d001d90a5519180b8405640d080b080001e0001040c0002c45141841000080b0384204c40d182c204008000000307580300c6c244203000c0f04041d01d030b500c80c0c400c544034107141803840f580c0301102039202c0304583c130101644c038001c5403ca895410100c10000f9941010300c1301034080c60100020f00c0650703070381100644603058800316454656581e007900141000b10075601d4100350165500741c800310501e505040b44082800d400070352030f206000000800181046014a82503641804d02503c00b00031044160000c00c2e004c140c01d00084484403c10007103991064000e42 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 718781285 1250 718780035 718780039
    0x60d140309150301211709150c0115080102130b0f04051c1a070c0f15060801050105040501081515010c06091a1012020906030313060c050c0f0f0d02030a0b01080c 71
    0x82d081c50115500c140500307817490142074600b122404010040d8400000c0c00080c001901d02030056640d0044012140d001a1200580340d645a01e18140c1c4070007901544001d0001c50001d40c10101b11501d560b1001045105809040b030000904032041e9140c04241c80051500030007070082614030008580d11941480c0b0221400320030221185001c050801041e4000c3d9140c1c1d4a40fa2031516980d03441403c0d014604090380c411f400c5e0780c1030f141c80d86031b04d010303942c06807820704008581035151009001c00c1c1d420680010384184c04c56101c078070445104c49440e940c04800e0004803590454003000580e1407020039140038107400c3c00c0425000500100804006445106400404e0181d5650801400102e481d0059000c01e40e00030302020090b103042c280580c2c00c0040141070713034074001444020f20451240e5a02040224840703000c2c00c800c0c840280b1404044020075910312503150340060001d00802d1504010501c81d0103507a8507601951001c102e0a0510f542c880001089540c450075102d50314940764024034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 718782535 1250 718781285 718781309
    0x40605041a040e0112030210020a091d0615131802040e1f090b0303300a020304170a0201150306051b07020d020d140615100206060d140309150301 64
    0x101c2a40292003101c040b80e15880780c19034142d0130009075200541054509508510400b0303216100c400651009103106045611401d07034035403410503102c0101952006581d2400041c1703040101581700c6100010100388201c200c2940daa94801021098050a4000d0f007180c03900076000303c04000859004009680303050841d1109580d0740ba06150080803440c0b41c0300380440c100002080207a210b50800064010f006050380c0c00c0c1180c025031441c0b60070801c0b24040035080300314800218022202c0d1541c0e0404501c031025803031454152981e0103808081190f11011500020310000d03003520030b40c8040d10061342c0140d00a0302c959030303003403420244c001607130001401e2003000341c244079880500d03044400701a4041d1405000c0c101036001c01a996082d00b1082e01c0343c00c0b04c1a640e07400780d10240980c61180d03a2058045400305040c801340034581c0550740c07021080d07500480600c45036603079841510828a502035420701301c81014043d0380c0d09500940c440c0681041040910b05c004407240300c040e42c10703a66810b104c0703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 718783785 1250 718782535 718782569
    0xd0b01180614010e0913150605040509030f090913060f0509390f090108010603060c031a12070b1b011104061205060f0603040501090b07140406050d0e0304060504 71
    0x40c0758503040c1040c960204c3c2c26103a070b1030f0700c1d418102c500540c02a0041c101d08400c28198a50f4815940c0002c2c40201081d9110001d103c18030707291141d1500102c0e210019030070a21002d940d04030701d205011b0254842ca60900c001a076000d1125540101c955010805114081031800c0303800181909460103400b42c010610344825256421151100030321072006207014101040344001c031101510017405800c90846101504aa04c5103a55903009007d0300340000b5006141d800c100c0c044408e10780c40e05040608182006a03400c0c56080b86070300e080002c03030b1042c52250310790416a140030480c1e0321800c0600804152080c0c23002101a44984160b41d24009104c440105103280c07950303200b00d0040030040f445841e01c0304d041002d81e5004660014019060700d0b14207001400107006504103c0f004c4071140c1d115102c481c100081103020326080403d03810300149103999030400b0242030080f409440f0801c10003050802d85012250408205000800f09a995441c3c03502c0d40140f40e94043d00860b00c003681d2009030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 718785035 1250 718783785 718783799
    0x7120302010e1c2c04020c15150a03080a02010902030712260f07150f050601030e0a02010e040209060409050408040509220602160c170f060105030303040b060d0b011806 74
    0x1070700c03d20090b01d940d900080e81c01c00c004144003500c6025042c00202040d4650841e540b150702c01000850784940083c80f4100078141d01c5c4510b070030020b02e0281c07030141c880b4198245849100303040c0140d07a03010100700d81b1a41d140d0000c81c01824503801c042d61602c242131002030310705401003c500d8145c0c06031100040341c3c01517201700c3d400d032103900c0311084002004000010b602007204018040c4184544110000620244010425281e40c02c0034168a143c1e991f0a010040da054420055202605406000d210a45400182c028545161042c4c01035400042c960342c00d603501e4049038060302d80b03558104014141070a04803116002805176502400c65403000c40d02031007507101000341c0901c0300300b0840d142c8281940d07807a010b034202c83c075286d601d20a01001c400004003038a2001000c3d2091401c8039000351050700f40ba40c60008200c1260b146034004034010b2003951000302c21664042d800c940c11140365120100414040c03002e000d0042d00107004c1c070b4000301e0703020000c4407544018851048207110f03081d20789003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 718786285 1250 718785035 718785073
    0x90115030f02090306010302010e12030f180d020306010e100801090507030203010b1c020607030504150216050a1d0408090307030317070e060d090c080a1416210507120302010e 77
    0xf04164180d0101c001000158400c40600390540b002400c03441d14a410724035000e1841d0032001c610f240a51020406281084000c8200d1503415405c440c0150b6005c0c06401280d01c3c1c0c08103015034001c4442c06400501340028a001c490000c0410100030407d000050038900d4461090340800c80c4294240f00c4000c0c0300b03140c445804443d80c11907440c030383e805e01c0071582042242c1d0711a070703011401c0c058107110010314000e80e404070710303c148280d80207030000d50084181280084030315000305119400f00f040038040c0c0c0304003c040c034880161020040741c0a88540c241040213000715103000303038103101c3c5100100805070f01445042c0050b084030305001c01c988a0400540c2c000c000141c1143e00010180040e074a60307040d9070230010005010300014120240c60341c081e242460b0340c40e80181c4045412000420600301c04002d01c1c40740d2215154030000c0343c0e05004030a081d0320882800328200d098132450344402c0c400144213150041c040c00c0e501d552602e4103450f005e40a0000a00324280c1402510351103040d44890070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 718787535 1250 718786285 718786297
    0x1306170609010e0708060103150806040b010e27030904092301020414011b142104050607200303040f030204140708060409060b1020030a120207080702090115030f02 72
    0x712082c542e0754070f9a20445c0c02c91401000c0c90f042644580c00c00d640144030b030030000094500c1c10f002d0301701d92520341004844010107074010b1208450303000400180381801c500407001d01002d450041442c40340002c40c24a54002c2d1181c503940103250031600020018034062032260604002600c0d481c444124850324201d0140c1e1140c05c2203010016031080503036100d00c070300344c50114500720350600a981d50f80710341c41083c03085890010715a05c040c00055100020029503014903815200d901c3c80c141c140f01c0440c4560240c0c650041010504060400301c1015404184042102c003408594035244d940141920b40070301d511040c0d00461800740c44000054203940d0175032241d0300715100d4551030b898007006d00004018202065070039958404074855a580c5a4005140742d80e01a44c850b200c040102805203114901c54450000d1540104150311419810040d40c800c503c801140041e1201a20306200e0958031503014000d501c601d5a00000c5080080020b881c0d2406070241d60030400d0300b42e0001028200d110319 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 718788785 1250 718787535 718787549
    0x706021207020105071a090708121306201b1e0d14070f03050102030f0708130b180d0906080601030218040908160b01050114041203080c130617060901 66
    0x4000641c0994020002404a188250340014410303042845c0c101c1e0004099a04d5611900800000c0008000c20071405242580380110310389004648040003045141c14824401400030707400c0c2c0441c60a5004024003400c202c0e142c10395800c09020311142080d40500710301d5605c90014030b410705c0260031003044440c4d9005000740000841c12000d031508040ca0003002d09103c3e040c0305411000c80c1e1204800610002944204000341e101e013040b4090010702ca030700620071030800600200300482d0201510142c88229044aa080c007551038018903000c08c414000140c00d030314413818901303020b4641d000103000308440f40e643c1c41d036005803206401101a4486e10145041c4801130748200d0034949050740c86000e002d4842d0005510b0070544c15545410711201110940f611503071000100015604100340c0c0400c40030039090711385040c1c10040c810a15540200016040029100001c2c0c013000014007210b00f007445a404d0120341540d0f500340240600004140e10a003c10344201149881c105000150705a446c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 718790035 1250 718788785 718788787
    0x40b010e01030515090111070c0302210703080d0609110a0809070807060e041814070609050d030809070f1e08030412080d1107060f2009010c020111160807060212 71
    0x134000483c1d010080217000092039540e0b401c0303040b5450107808000c000c1103128002a0541e80d18500410506c010485c5007028006d4660f10304410744540401c1c040107503075202d014180c440b003d81450301c0050105401142d440382c600822110800c803000c0140101c1c0d0181d545800c6169a10b00080b921a0b0342c5200300103084c3e01000c01481024064070005000d0f5002034000542c8203032020203039904091020301511920078080c400c0c10465820f02c06003000c0c0090341007500b4064503100225000110621002e400c002c3c2d820b02181800a0130300c6200e0061840f0f641c41000c0d240c41d0745040d840306890200d03c0009114040c00040d10000c04000e40d002c460041c0c0803003410004940380c1000640c2b0030440140140d03039590010036400034500150900901451001034101e0352040780c802241d03034039001d594035500b16080c0300b104036030103008030740d50b20b0001c0c0b810380c1c1c40c640503100580e0720000550001009000d41c541803c00c541801200303c084444010403685038a64491090b42c5034119400c640300000c034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 718791285 1250 718790035 718790053
    0xe0c0d020919020d32151f0801031202120301030816021210060f05060a2a050d082a090406080f0a060b0607150c050c01020a0e030c04020c0303131403070b040b010e010305 75
    0x44001004410201e014124581f080308520f12040c08292496214011a1a0000510500c886059881104d009600040100082200600e42d50340014400144008400990b0210580060030301034401c41c0d01800b0022000c020710350380da80b100300c241403001700b00c1d18000c00001d40d120794414080848030082c01e064070340a0f92100c102d403103200941c03000b0001a002c6c41c08183c40903108203048691805031001c0c00c0c08120b0364400403c1072802030700b100101d03020b8809503000400c0140030014000c0039040c8580d0340340c071441f011601404895011511600900c5070407142c0a1010420f08103842c49000104480c20100741080f616019254000c1c080c4000700034552080f150b541d01c50391030307542c03141425070401d2451000d4600303903405150004001030b5030340f010303403480d0034100a00420040216403d60814210918469590100510001011038050103403010700c008129003440001c018030a4980d124410305081888403c190b40031149807403c2030001601c03030040e440040c10780b40d0040203000030728 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 718792535 1250 718791285 718791301
    0x17120c03070203120112050d0504053106060c0c0506040e240907030e1005061c17070803010f080604030c06092a05040e0c0d020919020d32 61
    0xa08014011002e6110801c020388a00024860842c02800d1440080030801958038100c0d0502c4200001ca0040c404240010310141c1e0743c0d81400b00c0d902c0350080441004000c01500c00d00c21620660a0404640c60034070041201940030b1907002320507014100341c1100076a98407d02040388540d10641c2e540d07a103844e0100c0c00880205212606411103140080e01510480c00000d800d484251101c03008295103070825800084140134a001c90501544100018a0120301003030344480e81c4007030908450400c083c05020007030342e401c0034002c00101891594481d0000c2c500302e1a00e074800c3c021950301c240d0f000c00c0000c00305400991030f84104da16540e10091442160380e20f00c050320100000f200c010300032144070303465020600c024004407030128082c6442d891038101401f0441d102079403100303225008002180407035107420035581803059041d2012440c50382c441001d201e82045454500c1c0d034250000034403824104650700301c038541e01d000b140c41d84003e46030660400000c0e00c3c0340c0240c0e08070301001e9000404103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 718793785 1250 718792535 718792537
    0xa080708210c07060e0f090114010c0c08010510061101110d0c0509040c02032710180b0d0c03050106030e0a080d0905060a0e15010b12040303060e1317120c 68
    0x1c4503822a403506141e150690942415920f801039400100ca060f4021141d10f407030103220184003400d4492071815414200052007a01c1011003c5041c8000c000c035a030104205050390400800542d0001c21007410603d08000801907240315003400145040030480d00c0d60703810300c16a40400c0d180340c24036181405001003c0702618076035a42d0001d01c07405001e441e6564130341e07000f440c0598401e9409556106401d404011171510785808010886036681d004189689031245d00840426860826411111200052146000a9401003221030b140400c402ca82001e0940040074042019281840640c1c0c0325141201103a00d00156194658009000c4e1004195004000c09981b0080c400c04100400b49480da64078000d000c4e9194444180c0c0c0300c1e6010081d180c14810098441c10380d03030050031554900810703440180546908107000440100100302058042e602c200014510003451418038a4070100c20400684040740599904600c0700780044002240c07170480e698642e014040c41d040e622441100056 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 718795035 1250 718793785 718793833
    0x910060b0712050a0e190b030a1b050f0f1303050d210e0a1101030612150c17040605150909030307020708070f0b0319050c0703120933060b090a080708 66
    0x581d200031b4902040700407078003000f10b208044002010400001c0004800da604030072180c140700304030b01031003002160f1071041c08540030a0b031403541e0f0301d4a41510b81103110030305015620052407882500003403c1440d412100da030b8851060440340c01142181c1c1c17078405094a041101c2a282c80d04030700b00500010b02001102d007007508041c50b00007451620381c05100a20407152a081c0c074565803100c0c1c840300d0700d42c26000d250303041e154520348407605542d00b00d911034070100c0140c00100b010b5201c0000941c5001c143e0318190403440c0c010480e081504008c45410b860b03a10580c4d80740700600820302e0208102c50001464411a100c0c00300b408403543c40c114280c1d0791030704054102401060054940b0940a255000e102d000b05205001a50f42d8249450702410300041084510a6070f4107100694020421040301a09002145880001c0180c489842059044609858013031502d00d49040480c0c05024900a042d14100035100f40300c025403201b402d65580c0f8500d1013a440e0b0750313002440c1002c1442d844079003112 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 718796285 1250 718795035 718795069
    0x1401060503040c0803180901090b06030c0d09051605031b0109061101020c01061d100f0e090312010828080301170a201305130b0910060b0712050a0e 65
    0x408144c41c0c2005a046074091480f4002c800302c000300704105854905080381c010040940200483c00da1f140105040d400024003101224101044a00c880c00441d0449425a98400c0907240c80d0340509080d064070490303d0007094024402c0840c4012890201c1180b00300c0040161500002da601c4c4c000102c1e400280042d0f007407115502880303100c2504600340500000f80c8a100c04000002c201c4801002c3c41c007400030403112110810800030448cc2e00150b40250030f540843c2c81407405965002c2d0072525622550616030441400a00006420781000c5039926404000b040204202c2002c5600324558108148010700b199400304010440c5045c1d10541120f6103c5200a03030710200596111402e045140c1401e4401052105091402528104000e05c0d800003d90320104006c1c2481c01c5044181080f07060b0041a000e0140c01061155004004034007110706080c0f81808229190ac040c2480c0b604100012540038011501c1c814500380944291071000b0900c0e600e201008aa810800105801010b0300740 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 718797535 1250 718796285 718796303
    0x4060203181009030e2710030f1419110d110612061302070f0201030c030209030f010905010c0503060108130312020d09151a0105071b030f0308060103140106050304 72
    0x8050910140b10111002129040000700d880e541c0c01e0183c00581a4255184501c6851400c442c40301102c480440010000600298881d61a07059080e1061300f150030150400041e407180c80b0410213800c5c00000c03589010130503a80b10072510000c0d4864480d24200007006250517070401052424403044452655014001c181c11500e8080e021810f203620046c0d40f04601c46a040801030b25082c2890284580b104200045141c1500c07034982048903809103000074101a101e80c100c00d032040c400d0301070340c1d418240181900c00d1070b041a02c90f00d00074480b001040f9519424460080b007080d00860a0700e22131350045c0c584201302d0780c500944401c441c1c14000120b09110041010208200300380c0302902d6250300c2c10703000003540f0609080c0603801601c40d1410900c80c6042c102c924012a80301d401103c407000c1d00382003103a00e80d55103280c4006000f241c034490410a07007011100100744618070460b5480c880c02612040390507100c06004505070f034813115240c110075508000401031203100700000d40d0701901078042d007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 718798785 1250 718797535 718797571
    0x30a1706130513050c09040b01060e04241a070503070b0c0d05070309022e050702040b040e06011806050907080402130615030f05060a14150f13120201020604060203 72
    0x52400c0710003d40300b04a60003c5030300720a0802c2000c000c09000c41c10101c0e0303011307040d01d455607400d15030403c1401031604000e203044180d18140c80d1070700310f543d9401510075409071404006000d13001c0d130b203620700c1000d07000900c40c24000542a110ba0440e560280c0110196144c04044d446103500c805020b061013035403400c01c001c0d510310950765114450007410540d0303000c14104094010403440c07003a208140c11440300340b88801d900780681518014008034035410060344840c0a0f000050042440c1041917411500f0321545c080350400100d20507051b40d210441c0701c084030764466114001c561031030080c5030300160f040000c551000d009202c040e0b405440204480c12452545881505480071640800c414020080c014044a60140145d03000c0161860080046141803400030760220000d11a075031313082c0c1245d650242da41c0c441103044940c0c0c0c2c11121a2660b15003142e8444182a40000c15a0700c900c08441030120300b0b01d440142c00d1a08540590040c01c69445988030a40207610143c44d02d0585004100300d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 718800035 1250 718798785 718798819
    0x2032e090f06051e011220011d060f120f310c0b1305120f0a020d08041d1509090604030e040b0a1d06030a0308040f110d0f0c08030a1706 60
    0x13a001e031001c50807542d1048990b02e4280f12100306070001482e15401c0750045011a6401031400079104c0980c0b192041c3d144103803010820300e110b14006040d13070b40c00010300e403400d03050b0f0030469500441000e24941c1c1c480c2d41d5824441d000b400c4011144940d144017010000011100190114070a0700030000c8017030955441d220245a44e10034800300b651000000d03c10041460220100b1000a4807140607001c442415070101b03880c0c0e250340030020b10540c142d07010a018000e03444281d402034000e480e804d0200d5011005100c00d01c2000325114100d28120684000c040d0130952002c4d4001c01034000200304680303c0340e03401d5076806000c031038080d0130543da5030010703c032034ad502c4041c503004050240307119486450344046040480002020310b400783d4000c43d0a40700080d80822000c0e0b001c1e80240c042d804070f040d1480e00744803001c06205041ea10011403502e07001404000f8410b040d00c0d600c561224000301380d941035095100d000341c041131004942003100178402810b0b002c5200c0d5020340001d00d2030200c82ca4170701d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 718801285 1250 718800035 718800091
    0x90618090f0509010b060f04090f1401030507030c060f050405100311041e15020d05070609050a0c06030c0f0503150621100602030f0304110d02032e090f0605 69
    0x307940c40c0c8951200140000b41d402803042d0f109100f41921803920741500d9902c007025031711592113008901ca595460010100d00584d0169080508910a80040b035a40b410040c1e5641e519000130b903000742c8015000160741707005203442060240d0302c0d11084d080c94600810401c00049150281e0141074440140c0711108405000030405402045079088010080207041400d2541a401800340b0302020211000140e800050b0b4011800041c40e14030307513404107441e0180180c2600100103106105040d820030401a24001c1e002c00c2d142980d0302040308480d4200708031102545c1001050126038100042080706215040c21888500060b010520b0008060300411f194a0b640c842402d1140f415010b00240106000d2582d00418980c401035051031841d0500d2040742c48040d00c020054600445d010030f4644854580101d5160024107445400c840104010f1441030031282d8451004884140104096050310850002d00d41040e5034100702521960340c54028040a80341102107184d000c503c0104001c240d03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 718802535 1250 718801285 718801301
    0x9101a1005071416050102070f09230a1a03010c0c0212070b0c01062607140a080d0206191112090c0d03020c0f100e090a0e0a08130e060109061809 64
    0x1c0018051066000c03c204e40a64031a04810f0464110101c2081040d4039500c0010a0301e42101001540722000507401030100403a0750030001c244980000c0007080c40e025030000d8051004640000142448882010300701c0302000204000308000842510160038084c0701403400200300b170100c40b0307116156082990700d074020a00b4103225a44504c400d0120142c8041c1c00781c4e15144031100414101d540d1030107a600c604550240d2000e0419141c144a90f50b40d80d69207600040109100f0b071180ca800e503200080d21104229808000180a01402c0d00400e0709841009003480540c42c8050400120121380e2207403810161920341140f14051800f5100d5850719246142184a5001000301c0a185400c4c80070480d80c801e07509109140f010300b52004140c008502c256080400ca503a218640da44502280c0100905605c80500b03200302c0002e60101715101d0b00400d0800a4282e400e0320856581c60300b805500c0040703400a00080591000700b000d50b0040c070807125000500c80d0241e4055440304204d1046070481 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 718803785 1250 718802535 718802573
    0xc0c21061a0316141504180603080307020102180f0d290702070603140c0a0c050109150905151303080403090506030406140609040210050a0c060e0609101a100507 71
    0x2143c04120b0384008120448004100b501c3ca024944142420040c090280303205104490010840741d40c030b12410f0307500030000346034010f4445443e0f08105000034002c4d0098002c8000c1d181c183c0c561445c251512071201c8821f148000d1401503090820381d0340485803170441d200c15a44102002d0102e0f80c4038603d910b070901c05d000c2c590040100c6032610500809481d075512490308501e05500501460400c40400c0f203400700b8060809440990503031034094018800880301606480f0160078006030154203420804815001d00119002680540560a525601a0741c00c00c029107014076a0720000380102c41140d4054040c3c10f104074156a19008100d140c0e000b2181101d04640d1030401000503154089042e81086064440360802c4c90030f80d02040c080f503c1000c0071001e00002003080d101c590700c06e0820007138031076000e4410702081400c40680c84e0340c0e170010382d541103003401703044184412460340f80320310384161149a140e89074070105141448540e000c08004041040300400c4800d01041c1c1e890101202c000e0ac0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 718805035 1250 718803785 718803823
    0x14190b0a0e040c03020c0d05120c1b0106090209100203030c03040b10180c091205060c0c28030807020604030804022715090c07080304060f060f060c0c21061a03 70
    0x841c0481c5407c2020b1030510303400f40030061181141c00195000807980c403038a40c2c500503549100162018803016030b4004101403d6003402d00100b482022034000d0a504a4141e401d5820b1110000c030030390f1030b0b0108452041c94100248000380120f01d0b01c031062a0040102e084003074919480d4a00710942021440103d02516143c951191001ea80701034000e0040040b00002e1052001aa40b106d8a6001c0030b882c0c40300041022408080e10901800134140c008a09002041c507050b0750720b103000100360380001c2500417401c100000b402860000c41c0d5184601c0d0b00d69142c403a0342d5180d9081001010310381c2e1020b41d1100d20300d10100b0310442040c41143c010055100c1c0c41d1300e00d1440b0380402800c0c820051804079040818802240020303041c01c1079a800c190300c010003041c6401c03480201c000501c0268494408221030440001e54160030000380110707d4058600e080c102d07525504051111203a2040c008603035503140c10300c40081840c651018810044841c448105403180000180c030300580c040d02c8102c0801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 718806285 1250 718805035 718805047
    0x718020919080a15050105090a0e010b1e0907111c051e030f06011b08090d020d0b0906070903030e0f04060b18130e0601030b09070305011514190b0a0e040c0302 70
    0x31a038100e03050300c4c3c40d650006102960520003c1550780718050305103052903480703202d140780c2101c00b0740251011100240c01110100f00840c610100c80f540300310618003c41c83c00003ca09041e00c500803042520111100034891203685100a5032141c005182d61010000300b8003528140b0449507000c0000752600b0b000c5562241000506100685006010b103418001e00400325214500103511144d0610740140b4019101c44150010a5601490750402548040c420304030308100311401c0022030040c00d10404035280c507641c10304192184c55544c000a03000c034a100300d60080500e0710020400c0c240101900100d910342d40d41c15000c0c0142c06c1083c4064034101081c549000c5402c0c0b640d007040d601c083c1440d01380201c1d1102c00041e1303180d4106000240541c40c003500020a00301003005003800071603008000300a100e9030070b1419000003882e80903000d40b0080440c0111101d02e80703034911b040040540c1420760b8000746040d4480c00d07a54426104c410500116080c1c0d181103503100d104a40320000140c40141c5c3d126 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 718807535 1250 718806285 718806293
    0xc0f0615180e010501140103090c18022d09100e09010303091d0f04141e2b090e10030602040e0610051c0207060e2406030718020919080a 60
    0x50059000c40503d03890580100010040409200304010702801c0000e200649070400036148480c6400401c402440b84c0d4182c21200455801003400c46107a1280030460f0031200c5c549443d81007070045514454005200b05480781c03403c10002e80052a603401d1280c405007001021034a075440907031040e00880c00d00c0300d00308203000308a055480e5018075401d14500500e02149005031001015202130f1441501e50014230741094200850030310501035100b880c41c02c4072a4900290b680d000340343c07031980300c4c07a0300d0f004144110001d40c440301840e0306546510082608050b44018000001005003ea00711403d4002000c910180f0013000542542209142d49240038020b204020900007034036030411104100400180d400008070300b04480b142c540140e43e514850800700003800c420381400595010725140d43c450441095107100d04901d04c0756080ca010798a005c07c05444140d60303c20382501041b880307449418088140c1c018010164020300d048143d0f1815240d2450744107070761b000480c05600a140d11010b03c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 718808785 1250 718807535 718807541
    0x90717010609081908040806010f0f0b0702030303070e19030305030901050601081009150e090f0705030d02031b12040f06080603070b090907300f06060c0f061518 71
    0x14208508040d0702c0589003201d00780c0c0e1203102948000c48800c2d000704003010001e10a08445c02401a00708a40465840c1c0800c10100c00b1184281d45459000c107034000b030100e4000d81070b0b6580c2a001006142540c2d10380c18180d46002c030420556a00078400c071300070510401480c0e1440c024600a5840c1500ca16016103100d085032000b6208905201c00340c410044050030031a00300044d20400d00f001b20b81401260038501d503c5140c3c1d0405100e04400400300a0b0700180011450311604500c4120f602e242e680d4014903031034000081410005130401c21643e40301c9120462000c024818400446100070300030071490406800c642c0002005c0050b02ca01040407070b600014043c1c00076400c030050402540750820090b807030b12496101601512075600000ca10764010070201585041c52107180003c005206c6000303c555890794000001c0c1303403401d400665483c20621a100994056480364502c4560a4a03807980d20010003104841e01501c40140c030540000e4155281c1c014194002e210f1405080d100141003a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 718810035 1250 718808785 718808789
    0x302310b1816112e14151e13020301050117250210090605071b08030c0c100c0801170115050103020a0215040c060908063309071701 58
    0x5050a003014002c07078850051003000c0840752410102640e000c085242820020100111038001c0c8940502c404044040c400460f040d521016007003181365903552406070354180950f01c00298048010054030182008201000b14903040403000d4591035440002860401d45a600310b42100e80200042041e5601701083c2c0481b07410301c0040d840c040c9000101c0c45100c0308984801101c5015100d04418031f14000d03c40c915041d140c000c4240190a4641020300207042d0982d5101c0014101000503200c0b4031401001241866109070410300e140c40780030340f41096800c0404e031550640204040ea12050000f80b10321050345c011a190402550316100d01d40300c501001070b085600b564149540d07005150440640f080030380c0c03402d08006840380c584440c100c1c0742400c1e0035421101203a0032006e00c014420050064000c9603843da036040c64807602c0b06002d03622801d00351400f0942d009154000840902551030074401401e20340e9231a4540c0c4001000200c4020b002d440041c08101075500e075200c1d00c140c00c400c80780 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 718811285 1250 718810035 718810069
    0x10e100b091b1c090b1311010c081806160501230411010f0203090a170607020304120305070819120b190b0c0f062401020c01090302310b 60
    0x5902c144a8000000c0e61082141885400e21600d11525648000703600c600303140341e042000040c2c0c0d032030506162103040c84002800c1e18a0409144800307080e600c101c001400380c5500c100a281490a4050300c0c40910381d019240560180c002e00c241100007048001400c44217010740300108003808403010a1900c0c029125031380c0c628400c090200000b00c4c00d51032421080c0b100a02e061040c40c0410203080741180682050700b90300c440003031000112000d540c4101241e01e6002030542e02d2036200d092003640e0f244298440c103120f02d0001e203c8080880d00a4000c0c0180b00d0042e00300d146086808001e40c03030340b43d10000295010800005110f07101086600c250f602502c810341d005000c070300107900c0311000c030714092282c0a00501c0014150415440c28054071100c0c089840071203007a410700c14440c00c584283c41c0b10200c1a00070030450050300750301c00a407042c3c6030b030380607160006500d046400384618205100780d491000d0300c81c000c1450323100b0160041007071543d22450700060307420301e003030100301944031000500c80d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 718812535 1250 718811285 718811311
    0x30c1501060e010806122a041505090f0a110d021207030605030601140f03100c08090a0c1503200d060b030603070504240803030a06080316021002010e100b09 69
    0x40c20698201c2e00d00c40d00700c00304642c5030400c3d40b1b204843c00d1a181c401590300c4580820b0000703e82c50241165050204a0405c5606000d070109415003030b5001d40040c802c0c00d5000c0540c4003c12640030008156507089101000049410321107404030002e0b075441810340c042c107180c1c0050b00d1034000f1100765079950080d001780780074070404e07241c0000266a0071040c0120070748ec00d02c5c80103800207a40c2e5200149000c81000e02511580f4132001f411f4401054408172140220328040d00003000c502010034803040090f072003c02210940d00306412200c1c141000d80007841450713600c1e0114411454501c05a1000c0040b8080b0340740d40e40101f01403a002c1d10780c0d40d48141c201c40d03014014000700d5078001c917000064130025100003c406201c0325031703c1900c048299202e41c020050101c04200c000000c0004e510800f525402442401c4d503500d0b1042e5680304c0d01308080f0440b8400c2c0310300ca0062616031141318041035140300224200f810b800045051040000760344203200c2d524400422079080040030f055202285040314 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 718813785 1250 718812535 718812557
    0x30b0106031d070e0621010516170f18100606020709060302090109050705041703030103021c030818070f120515040317060432150f040f020c030c150106 67
    0x302c0e0b54003607a001301044010b2140014001d84c4030711a401101080d202481b0039080d0b8070b194014001c0500b40d40030b03520f03581500c40c0c001c1824040c00089000d5020300d45070501982d50341440714520031001d4200c45106055041c40c1006481c2000902264a160500010740c0c0e0720700b00010b0310740003a03540100d10b518102a420070169540084413411500081d60201d119580d20400300c80c03611481e000381451041305c415080c3e02c45000400745060760310942d03002d240744680d040c40e00c03444a1038410081c00910038500240d1009441a0700c0860110348204a07420b0545075046541144034a030403452801451f02540024000c04108200341030107150850035480c00d00781c50040440c0f03105101c05003031104400100d201a1030b186d01c1406088074402c400032082400c3d005000203410314030240000c10b9055000305030300380a0261800700005c1d009041d000440058410700002d443e100f51b00c90342e110780c2031011068010b0309100415804030503001614519030b10803c000c65115068001e03404005041c189 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 718815035 1250 718813785 718813841
    0x120506150703050c010204030609150b0619030e0a0503160512250f0803070504290313050f060103030e15040b0703030b040b2d040e030703080709030c030b010603 71
    0x1240c181030b425150042d03844003030803001c5019125582c0014407544c5040040b80038005500e016005a041d10783c801c0c8040400030040158a01801c640c9090000c000c09503881d201e17000e07a000e0346418410030241c0e000c00f171554036040c2c2950410b0507120f2034141c01020240800000744800d15199640c0d00e25141404000c7d000458850078203020f4084440c012214401030040b00c560180c407550388034814650f0381c500340307100900c650410b01c20403007090070005242088044000048008cc071101c0c09042c110340d90304481d807421100d890004c1d141030141640c00c0070030020501036070303001e14003d0700c940221085000034403104610362415003400790400e110502c0000c1c03e0200701c48440c1d40519001c00e448103d00005401400800e0300580d00c4030010002c2c680080040c0e20000003a00d4042120382d03108150018801541c0b01c16945400b01e4004102c0000041e005105144e007000c1e6500e4140a02902c96580e440f6a403100e8005941d00d43c060070040041356814099100e0045c03c03904459200354024030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 718816285 1250 718815035 718815037
    0xa0305060702010f1b0e060408060106021605030c1e0604030c080102040509060144100513060602031c0b030f0604020306060109050607170f0406050726030a0519090312050615 77
    0x8174004101e052170401c50280e031648156000f9244810913202a541d449501035902d003241d014001c0643c00c0801c00013040c0c5008a981c00c000c4601400d903c0c411500c50614401ca200c1520400e507000c08103110100114007034107609009003e40200050ba92420f0000304007041c1001400103040160501403001c4407007086e5000e880d141032210042c50020031012030090507070004103148040d6402d440c1004410140d012a140844030243c03800d00d00c1511031209035040d516540034400160f0b1027007040d41081c0161445500c024100c0e0000080c4d91140c0703d0010381441c02d0503603100b801d503001c0c10a1100350b00d07040c04480d030001e80c2400c004140515020102d610703070050340d030042e2003001640c81d01e41ca124140f1003224103a19184c0d65090350b60f0f842d038030043d05076004541c00f91002c24809040c00300d152448000d0100003a00c2c2c0300c03d1030075aa513030704140300540310080c4014421810109224003010240c000c03440120700c01d45440342c0f10354010041008450005081910a0744015810040500084 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 718817535 1250 718816285 718816331
    0xb061f0224100312050913050403080702011118120610170705011d030f01050108030d05010e1302060a050d060e061c0b0610170a09150c020c010e0f0a0305060702010f 73
    0x1c0d40000d010381d150708291118060030700190f0300244144480011fa522550150b88624407940751500c543d107402000328200c2e02003100749007460394100200640c07042e140d1028121254010701c15118180940182810504140c91107080c1d000d900741c5c2842003149502c0351088044591001700300007481c00300020481c1c507004201400d1441100c0b814240b54900340308048c0ca41062500078422540d4840320b00341d07241e00031908502c10f18038120001c1803018540d003120b4002c40040c070b42220f5800443d020000c1641c007444001081c0001001441c4010382d082c0904030042c03031421000d0095141020034091150540795607400c440f03a400618070001583d944005801a0b01a50602c9a50741611002c3c0da2489025150700c40e224045410800c8140040e00101201032045041140e544c1c07040c100102592805803c507000358004000c030750510f510541500558140040c50392800d0b03040800402c4001407150402c0e11a600100700f0003841c1234090040d14019101042c003040340e01500c0c081044140f00c01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 718818785 1250 718817535 718817543
    0xc100e12030c07051e15060d080f0c070f03061b080c0f070b090d0915020c1021090506010b070f140a05060c040f060f020a0b061f02241003 61
    0x2001080300100302c1c00070345038480e512900300c44644031400460f4819850485484146208004030303c12512101e44c48a170196401070950f10949805546024468012a50000c0c45010a00c030320a00300c4030802000005003100d185040700581075050040030b854940c0c11140ea00070040c0303100d02005900403207081c1c2c000c5c0e0302000c3c1600e0707000d0800044114405c0080282000034001c05200705c0d04c07804200304444a0080d254850459590981c49240141740c520540150300140b254600c1030828500a08450105191540460580200d282c41c0c4540f214001d40d00f0990700c1040320300b00300040100c4d40c09001403950a41c28824140d035441c80c40c1150100040490040300b80d400d1240343d08204107031486921000783d61403031510341d800c003156070030a108507085103504020003d181c901601400b5080e412035070240c10840420f4890120f00c0002038602908400c03000309025142003854000c10005240d54090205048095010319101d0710581180604d08a0710090121700808081a070041ba80d00c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 718820035 1250 718818785 718818787
    0x2041d06030c040e1501080d080a2301080303060907020613020402221701050604200306311a0f100903020607290727030f080c100e12 59
    0x34400440d04000200265540050510901081c803860120300d0003000716059480c1d241c02c0e80e0b80c0134955035611511000c8070129820402080700103016070401e02e4039628039003c1c4070011401e03095605100c4d4099000c44084e0b000442440024030304050001e4000d031241c40200401c1c2400c0b0340301c41d44102c81100080c42640e00180000390200350000704502d5413a0190075000c1242c1d04c650740501c2d00481240c0b2101940780c040002c14500e080c0c424040425280c0e00c2907040c40300101c5103100543d0010b44040e6002c4030810f000194001d06501c40c03400c022020b850f42d895485d01d40c0e014010b0b41c40061449000c070f12090703030202481d1560182c0950303002003140c07548000d151280e015603001d05203400180d0800800240c0c6014004034800020b02c0720101513114190043c1032095059006041c0d440600040d051041c0148503d1041c034411440ca26884420806a9807599080364040c0d404070103e60450380070641001e14082808211109000701000b0b0140d4040e1007603480d00c42010a2048144541c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 718821285 1250 718820035 718820041
    0x711030c1c0c0314010b01140f030402010507050f0604031d03010e03070204020f0c0a030c0c080d090b031b070b0403111f05100801091430030c07050601090e0c0402041d 74
    0x185000450b0019904848a441c2460030802240d01074410100503a001c50040c504a1030802500700494840d2603981640d03a08503111a401110a640500c2c000c0d1076606c240002ea0031408410710005004500c40d48030918841e0b80c440303000c0f02c045029585184603900d440e042206900c0f000c404c54641507411540180c3e0380c080015042d00300d0140103d4681c032031041d00d01100403d0380000d0b8080003203008600c044803890780c1e00e10013662258140f6281d030026601c03500c100710107461a40071310b42000013050510002c9006001c2034030980c000e50740a40f03105c640d40051100741908008040e500d068004040c0501a2021000d050303c100d6102031000e0099680002808503004149010301070030007a4024440c01220741462600d0303a40401c550120b03401004441400800ca0a1880b0810718581a000079a030b07000444c0f00390303950002018203403640302c10400d0200141061100902800305a00b000883c9689088084c0c40c100340403144034002d034410401481004605980e90030006c604a0050500395 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 718822535 1250 718821285 718821293
    0x90c0306022206020f120901020c13060503190606090203060603070e041d030d1a0d030c17031305120307050d0b13020a02010606180e010e040602040f03080711030c1c 73
    0x10b8000e5805810080000c0700124070036038041007419000b000581180c80e00d40c01c5c0c02c00c419007071080d0720070340c2d026900c034940a1b01c0a050080c1c40c118124103101d80020115074903404203040030002c0c04413083c90b610f804528020012640705940190070741f41c01c04c600b186040004504284000351803241888081d40307030510143c2e035a0704410522600c0c696111400c9a081454951713035048610a00c03600fa0030510910400440000620720035600141101c1013240c2c02e0320700b541e0000510105460b000c10081450841002c1200214001d11440030240401b209504259052030304001d04980004030400503c12495808015a60000c000000000c0c0e00d030f8004c400901800da4086810b20407500106074044c903030790103511800031204030341c8a03251f060350003801007405000c00380a403034800740d085801488a031207040001a80700744220801440d0a8a440c0d690480b160341d50700c01c0b03c0c01071300010440304002206203075440b5082d00354024840580d00500080482c4219030340480c000b01e551031610240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 718823785 1250 718822535 718822567
    0x10602060615190507110d0201210605060a180b070809101205070f180b03041403132408090a0206030619141503090c1c05100f0e01090c030602 63
    0x80301e40340703580018043ca0490142007508200c20607210101101c3e14143c0d6420418010721200368140e4895494980107040700280f20948100030f840107948140100307294580c4002440300c041e55440710520b410107410003010f07000264101c05441c0e07070180040400a4019002e41380707200d000300c44600940441040841d2900380441a002816040038140041150043c4d4150890190f995a070484005600100385020358030b8400d210002d203080000a020402c0070380c040342e02107400b8090741c4c90010801c40c01c809113501508804d04040403803d251007807001c50403c150305800141050300003468282d40c42e0341c032031400c440060f00822001000030916543c40255000b150050030350054940d4440c910505684448901c081c02246aa5152003401c4000020740e03100d600103100401c40d405400c0d091141c45203090310800c1a18641040d11000143c0600140c84210019040040c040c481030f0890001e45220828403070300c40c1d14115501000c107100506031419682c00110141e0758540c4400c043e200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 718825035 1250 718823785 718823797
    0xe18060907080c0409171308060114030a060c090f0611010f0e030a180b2a01022a0c090114192907120801030b06040204050a0303080406090611090a0806010602060615 73
    0x12000000030412500002d103003081c400c0d21014022070f87e880c0e032911000541640044106533141c0d112408800014005800c0800d05642034506818000d550b2003150303040301c580b50401004039031114007411a01e9400d104034100f45400d4482405048580400f143c0c4078444e10564000b0091705103050070b60442900c08010090800e80300480c1d482c00500c01c1100035040d800c42080c8011701d1994502100c010500a88001a40e52540605a0400d041c803400003288144204a168000e00641008030b81e100007043d4020004504500210340c4a0f60402c0034110405591000a00c1001360600611a12402d80200c1c14120b00441c03030b46030b0804500040c5c0c0d00480303600810407400c94074200c800607404614541204c0c4035280c00e000d1601c03003604010980c0114060301c0d8000400101c20000300307104180c06a0024000c050008050401e0703109c4030700f91410b42c90703403280c81d0200054041c490705000b0028002840c8102c080c06095041c414001d480e0303203001c3c086c240300d22041c4181442d0386a0142c100c0c3d070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 718826285 1250 718825035 718825073
    0x10e070e060a03090314040515161505060f22020c01110403050304030b0f0f0c0702120703050c0117090d0c17031014060304050a060c090e18060907080c0409 69
    0x14442c5641c081c001c015051300390040380003858010485400c4050001a02e041d40d600410b40c0707081011003041e100064000032100c0080101003100c0001080841541c200280b0760340001060328a403c505100070000342110312405125041040c004c449030a2000101346000e049015139100e4a4405044c09882d0f08100300541c003000050000402c0700020042045912464010203d035030384030058506c003082110320380c00c078000300b000003404c140e1624000c01800d440201542d11907004980c100346080c0d80b58104940590105801041940c0c11102055408141003840740d150701c1c01c080070035140d481341341d821070034004500900b20400800328000c03242d10b414441c21a4485c5000010803d0704d03001e81c0309d0944070070340d101d84070300319410140c013124440c0d60130000405c90001150b40300002404c89174401c0c02046400c04c3d000c80e00342c40605015000e03d54401140000c02204000f40e0708103140036060000980c80084104603040001c00c0300c01400030121000a42183c450134040d40f070351400b44000c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 718827535 1250 718826285 718826287
    0x140111120f0106020f030406030c050d1e0509010e0c24180f0402040308191202040f1e034209050c040e03040b0904020705120c24010e070e06 62
    0x904902818800c0600c601c100e0154101d059988410030780e22018030080c2810030303030420081845132a018ac0c0055140702d5484c94980d280c00c0303480200f141150703000d403108184505480c148401c07900090140321741080b20640200b14800700d41d0312107a61001c6068640b40030794100300c0e0400703118034071a4801c03c40300c03180007040e035071750303c81007010b2a0381c030480b02000d44510882503414081e33041500c2a134080d2a481208a490042540c86100000d401c0700c88401c1000b80c03030360034581e11180740e0010308020620700c080c2c01c0400342850814200206140741c04408046140f10400100c0c0b0644600a01e2000c1b5486c0f0304175003480401c69480b1401048000b08030449420f16403881c5041d10b90091060b40d00500503204e040c210700041100b6204411103038042c7d5441803000f400800c42507002007544000c01403005190441607030781c0a0038003030b136110b5000d100e440c00300c1d075426080030902c150200341320100c3d90400c500741500030035141c1541c1800f404040101080019003070794040c400c904842a0020b040c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 718828785 1250 718827535 718827547
    0x370609050a12080903090d061805120a090b0c0601060f030b0907080601020f01092012060c040501090e01031e050309120304051215070309170d0b040b0f010804140111 73
    0x51604070031102c400d40014100c01e000418044000c01510748809008105176641c140544441024121017100000b00075402000880002d00c1045140c40d04c1c6c1c1c0d40d484182e110441540060400c500c141c0c4036240350502044000c14a102c0460090b056408500301080f040e8a0b044048000b0400c03000c030241c01007104406c1c070030340a403c40c114501c01c04099007103ea10801c842c0b041070a8500400000386100352002c43d402404107010401070032044041c00c0201c1c0b1040c1704050300d1038004261141c050083e4002010f00c01c40d40d0060141d03000c0c000511280c5402d5140d0b0340c0f414444060428082c02c1241041c3c105010000180101d80201800900c1088040004102d0a440390311911880380b140709191007074044c1ca0b42c080340c2c9c40a1034031000c8215526660b6440e00f90041c05102c241150b8200170014024417028550014001e00011201e0001d0742d0180c0e80c05000407595030348842446a001ca0105ca059a030b8054070030b40e8040d521924946401d08241d85042c050443c1c3d03106440310810203d51 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 718830035 1250 718828785 718828793
    0x507090e041a0717060f01121b02061f0306020306060c035203092403060e060907030b0a1815050d030504060f120e0a0302370609050a 59
    0x811200c0380c0704405035002c80c0d1103100d0182d51110b5420501c0322100c400f10b000999629041c0014420400e040c100050808e40380f4891a08071107250420b0000c05605903c036100055042100640c4170074007003610380c10340020321042d240748012031000070f00d03d81e00000041c1c8540c40310001c3d1030017000700804803900d41c041c0d00b420f40408200d14428641c250204000240170080c09541c140780404001011041550280700d8001044034010055051081c6080d00003800460f4441060420306480403500039041e103000001c041d2603407544001000302c0c0b04409e0106503a500c2c43c1050f000711081c00e0000b000e441b04004909404540e80c0000d80c0b4803d4009150781c8110180c1150303000c00240070300e440c0015224002c000d42e910b0b050740081c1c00502c00380018803c15025a08000d20101507050400c51504d00c0160b0001b5110160340d802030716040705006508142c0c0402140e07190200d83c034082050406404200308086132812030041c1424020021071007407090907030081c00c05c0703500310b010782e078091482c0d0030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 718831285 1250 718830035 718830053
    0xb06041203030b1e01083414030f0c0306031606270303090b0c0114100303031a031f202101050d02010806010e090901060f0e0c0a030507090e04 63
    0x1010750100b0300300300c80c082d101e16010018001c2100310354940b4902207152001101c080b00d00602207905803403255092078950348015540c240201e801c903010a041c00d0744100041c9042680104005005424000e0002c0c1405400c8101e5000749840320840c0c696490f90006464140c10007c2d025415000c0b10b004100c60790b0099284502c040c450301c0f40c200000144d15000c4040213288000380000746408028403040e00c0d00d00042070f40b07014901c0003040742200d150001e001c2d502d0644590b010010030032010002c15426000c0c01d13216840004c3c44025696070440440d44812074015021484016613500951b2505140c2c069000c00d1100304083d00d448003000000e140300d41c481c920016512064194071114804541348082c1619800340228085004641c0155034012018007130505002d083c0400860031380703c2c00070891296034110300200d111450000591010207268001940660421040101c042c15a07402c0314000c00062400103041d0340c60180c00c4034800d1454011340c8007004060244014482161 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 718832535 1250 718831285 718831319
    0x150610170f07230901080c0c010f0f0b1c080c0307060f0c18120803150303070f02040e0a02182203050a080105040c170901020f0a0206010305060112020d110102010b0604 74
    0x5201d86858210b2a070b030f148100ca491060814061104010343c1c0d0280d4410425031b034101000807102c80c14486504115400d541c11038104079400c0d0381d50160603250b40c0c01406031040d250b00c20398200c0f000900d14000d20080425103100070703104010015a0502d6000d040044a03c983d8000700d04208260062450101414003040c1c0d00b40001d90b06000100e0500016801200700c2c0d0710a106010031100690720140d41e03800041100421807000307401c2d1980341e1003e20040070301c036110b0411a1100b008a20400c000c50300584481641c680c424801074006840780300c21506254a002e16201d003135511200c403851280086442a155001804111401c140d00030000e4582e0b0324403034840500580c0c90340b0038841100c606040100000c2c07203243c0505409102d1100103504049064000f42c80c29518605a850f030350f1081e005d60005034400801001481014071145001d030034100c41c207106441a940009200030030114014180031010310030001681c1c003d5208940c2103501601c400c1c0c8450395100b08800b403003a85 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 718833785 1250 718832535 718832537
    0x6120712150e06180f04030c06021c06090204140904061b050d060602030a120c0e04062303070321020f070b04170105041e1a0f041202150610170f07 65
    0x18000704502d80303400000462502001c0e6445801382c0d56400610442e004050415424810382c0e01030031010540a00007403410180100d1002103248800c8510011605030b076222654040c81800244030203e0300003240c15145c0d07003c5516600c2c0303840d01d08100b0000c05174505244048407001811640050300040503102440c4003400c200b054680d02d0f00240e841e4412105c05100040440c040c9482c011952b0303001c2c07501091689001d6110f401c2c14030100d42242d00e942c005040042030805002390b69010440d20349840c55068016001107807440d51a09120040a4010255088000c00113140d0503c04c00811240c80084011141c0040c1e840e0702c5600700b42d005001c1c801c25214020500180c0440501800b8061a8080003105507110280803c8005802c015012901110790869400c0030812000100e80a444896101c02c41403c2c01c0c078040320103032103103010241950001254500d4151130000034039841601502c9910180401c50021206a07842809108000e8540001d2051028880f90201d01c01c2540d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 718835035 1250 718833785 718833809
    0x506030f01051207060c0221100b0a21030e220911011707050a09050d08040816030c1a0910030f200714121b0c0a050612071215 56
    0x41d080034207448544c64080d140108690030705950050a00c0e034440e89070314012162601610300185440c9050603070402a04402684800d12881189003038094000101f40c04127040c080703a55030201d03013442141e4114000d02484070300070454500741c80301c540d40e40011902000302e59100c1c0a0703014440c010301f82044d0031365010641d80040d21195014920b00c0014111014003a001507584000c102c40a80c81640c04201308507e83d580025107455403e000300c032807441810201c2e00c403801c0c000410306d44904d10940b64048201c404c0f040003c503480c03081c030303a090302c0100815030018641341c050a00790344901c041ea190800b41507200c05c0d07855585030b800000c8000c1c0c900000d0002c0b071402c220400507070300548115424664104692000203c546401c601c4180c0004251000791a401c1c0c0010210b822442c0f8031080070b45001c2d101c580400f800e0180c2030f61240e0454040460b50f08080c08180d0b1070040c0300c02035210b040d041e030200309072600880a41c0101c200e00c00c01031000a00030380303810712030414502c911020b10380 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 718836285 1250 718835035 718835059
    0x8060a0e1f0f12031724010210150815220503120a1a09061c06090f030207170706050d231609170606010f11011a030c0a0303020319090506030f0105 65
    0x184169024000c100480c0b0284200340705801403050844c104048031f066105800c8001621030f00750143c04981c0031a202c100c0d41e144d03d071030030050610340300d600d176010048042400c001c1c4803031034111880911a640d119160380d0108901c0e0191a61142d4070034041c440c00c00400708146c1c004c82e5004a1940b140070f261070030300c488030341c001c1c490795030310681d256940220314108003088517503c842e80e40c581c03d002d0b21000c100d5144d02d1325500c1b080c400c004010ba00680001100b030004c1050003200321040b804e8400281086490040002c100c3d0151101c100941a100c10207130212050800507100000000600c1042a0800644030018040b0580004000c1001084005507009940341e101d506000944050072059035004011103000707a03821a44000d00070070740003000e2402c200b4400c68001c0e80305094600c075402e41c40c0080500d0315035400c441600c150340400c400d10000780c4c048182c625840c0720801401c42c0c010035078000c0c0e65494040c0c100b0f83e0015004001c0080300034050412504031101640ca40700106 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 718837535 1250 718836285 718836317
    0x180111181801140d020409030c051e070303050304050f011e14010b03011e0e13030801050d020a031502071509230d0c03050f0313020108060a0e1f0f1203 67
    0x5541060503090100c40300c80104180d82d6181c07900600c03c40d004203011141c0d450b80c2d0025089a002040580000748006d8071030080140c10800c1c9800b0307402c8507885013020303448010000e58488060000504000d00440030600b04401001585100b1100130001c0c88018036000502d043e00003055032103c102c5081010354801d000030504054140c0300e8604189117541c0c2442580e2031180b09103040c164550071303454000291404107240c44c40c041d0082d40c0d20b40820208604000f07060410603001a0301c80d0001a500c0340041c1d45070350810b41229800101110100d4018003508000d00400380050300401a1540140d0001703602d90050803024072426407050303142a000c0d0240120600c0090704081c65000040d01001c841c018444018118403a18065280114540300d100e1603420559080e0300141445415030115a0001586940030a0640d00340c28428034140300c006003920081d006130007140035008022117641c01d04002c00c010307200ea200303002401c5584c0c0086444901184000f500010000c081f485101c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 718838785 1250 718837535 718837549
    0x150613020f09060f0415120b01051204060c140729070c06090206071a09010b01021b04090f0f03020624090c09280e090a02010206010e18011118 63
    0x418040e0007030302d0401060209011a560004011443c3c4880c103100010b40c81c03582141e8181c0e1088250744496441c0390b030104101c15100f940769103c2c14020184400c4005000c2c0781381181e4000c0d0000c1d00031a00090482c010b49002000c007a8004000200254006c02d02c0002c24502c48004005904041240d2a0341d0007028580382c140c0c0c01900240b0191400b01c04151503411200031280010500f9240c100d10703944080c0d0300003600d10060f40d0305240c0020040c140740c0a200b2084c0700402800035001c0d400380781080c0c0c156040800383d40c520995440042c030090041d100c1c458020154002c14200c6100030714140030b907952500710b034041c1880101c0d03450701003072507a503411200c0c6252001d02304d84c01a4940d808a1089c540013a412250040b160101c04c103909400c1d40b052050354581c94841003103450804191141c001802803006442c0d511030b0302541c005036400581e00b4115003216a118900341c0b034440142d041c0c4c0419040e0300b900d9600f0007403c2c1c910304144500411801d4240f102d91251a14401c05002c05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 718840035 1250 718838785 718838797
    0x70203070c051c0f0615090b0f0108060109120312020a0816050906030a0e0a02100509030d050408070e0402031f1d1c1101090206120f010e040b01050f0d0515061302 72
    0x40c490f04806000006148480e501100c3c1d216120114030031250040e160348140d60356004613081c544419405589082c03503040060405070a1a00381e0b242d00e0203400203000001d2a10401c0c80f5949040c002c0414548900880d003030316179084406640c1d41c280400000c104010548200148204000b020040c29000b0030840d10b03038142c0a0001b508694407048620001e288660740d0810700c2c0100c914250040c0d503041130000c16505141ca03285d49490a6105151416410150003014810100401d1120010000f554002c8402c0e03074040c2001a61540701107400c000c002e411003006100d9405034900640c901d5001100e44005503100f0b9116440d00e100550307690200900e0035070901c07000c00c001c2c40855100f4107803258040c100702c001003408000c039808140c071b5501c0012590650880c2d4400d11003d4840d00414500401e1401c582c0380322810130303840704444e00134184540381c400c01241c02c080a5944415600d03802c0c036a08407064400c03080300000351140a020458803113224001c01c5650001c1c5894620903500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 718841285 1250 718840035 718840069
    0x10e01090c02150411150a08040b060f030c0607050c0d0507090f050705070b071e050909090312070804020f040501091406040c02150a060e010b0d060b030130050303070203070c05 78
    0xf015242ea890704103010075803078459504150003501c512003940d0048010080c21001d90794070b11442ca41801c2070031046030040c1420b40300340b1343c4031020002682c00040c81103081c94216a030558401841c80c10514103480d40109540080c1c16007071400c2403000115001040b500000f5080c02600d90545090040b2102140c5480c04a04140807010200e4a0f041803145c0c441c01604103c040503c2c09180390304c221031100c08034000284001143c60081c1020b0b40341c283c01c1079a2030300450518907c07103a01d50703a95030018103640c04c108050000800359035400c2e0390200c480d400503104010658482c500100238142c00e01d0340b02d0360a80d043c03001c06c10303d003444d02c18040c1d05091580545149900103100081d084405000d0402107900c840002c60a40304078079049000303144800701c4607030f82d611441c10001504e480b90f000c40e1001c0f40c20720040000315008a0300c2c002c10700b030740101c3c0e40386503500200045000d000c00e00084c1c43d620000c42004201d54000000700383e0113005500c12000701c0c0c5e4820411a212080300c0c0310320 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 718842535 1250 718841285 718841323
    0x3070305030a05040303091707051c05040303050a03292805040207111e1305010b040b0319060b04050a0915050f0109081605090f060d14011103010e01090c02 69
    0x40d0b1801400d6002a820074400d25002c075a6145035200c900c1d44100094110004902c0010a001080380410000c40d00c100703644110202003c030544060128001e5100140a100000900a800700d00c00d910162100400154403070300c5404040170b201d0302002101c2014020020344010700e0700000211840c1c0c001c200302180f490201814442440007a40000d40308645045125842c0102c1d503031000e0580715001002e09a40300c2020a41c0308104160a0714500c00c68014944001889404d41040840c2c0649101e07040c1d403a920740f5400850004001052450608245824070110390030f0714032002007044a000700ca81850003615407460700102d5071401ca0070202916188420032060a203030703c0501d50088141850030100341d0b5a11024141f0504c3d40510419986542d8140318a29000c04080d8010070b0003998240e2926040010481c245e40302c80d8080d08509481c8a18030048009402084480440c621003c2e101c0d691084202170440003030064076691401c103110380c81c2482c400078902040120240341c0c1c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 718843785 1250 718842535 718842541
    0xc030c05191701140c0a140f07030c1106030424060e041b03080a020715031413080417010608071e1a092101050f13031107080715030e0307030503 64
    0x91480405102c1840d919502d5002030400c840d44005000d100b4143c50701c40302d5441d442c41000404480114011402566003404003041507942c031400c0e2400c070f6526003031810601c041410060038046040b981d4640c050030000c2040200f210301d074140c4d115030790180b0160f062041d058003480b007a0369031801341400c400020000100071030f14200161454804c41502c048a481d12034a400043c1e5000040c2d0f0000b43c0e010260800801c481000b607208401142c0c5000c000043c110708a8020400d800f9000086803140a8518411b1040e030004480c010042c1d5004000c2055000380035601038187da10611440c1d01400b038000400b607a2046d05c0345181d02d00300d0140201d103401c21008005103280340d2202d030300c1c64005000c50141c5031034034000410140038101c0105000d003200d20071b05003501c0e030081c6810255080042071250f8254200c070803d005a5050070310741c9905504551790342c600400c90344005044d200d030080000f02c1c0e011358001d0706400e100b1507409003d0751068200c10369803131150380c00041c0011810400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 718845035 1250 718843785 718843799
    0x3031204080c0f0616350411060702090604022107090f0f150c030302040503010603111309030e01030e16030b06090a360c030308150103060308181c0c030c0519 70
    0x10005100e0b52015140c1c2d506c9441080815482040c07189030010320f00c1030510040c070520382800e02000100302c5405190040e40d034041180c80c00040c00081c0a07030340100710481e100c41c5103d5151080070002d00c42d03450a01e40604001c2200046204800c074003440c110300801c5889484040c02c080c0ca030030307880d03020b1141140307403007280d40d000d4815054003019420301c0f002c903860350300f030003000300440c0074101444002c503005c410082904071103501100c20515124001d0001f9400200d8000b180200342400140d0421514460b41802c03400c8008640130001c4044c04001c1101c81c80c0d03280d000368000d59032014656100b4041c13200721101c0100b010201d849085044600c031a0b89100c08402e1820341b0020202c040807075075030f201d000d101c0350000c0700401d4000381007000201c0b51421340301308031200340780500007a072858031444581e105240390300e42c06d150b24004407a01030312010045904441c4002c0700001845103401d000c901c1d00070902045541000c0314400156910302102d010320004214031086640070310f0202 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 718846285 1250 718845035 718845047
    0x50406062912090a05030307020d031b090504050a0f14071707023016060e150105040e0307020604061106061f0c060608030a0c06180803041103031204080c0f0616 71
    0x2c60305a191142190190001d501400031f14052801034005000030200d0940c041c041e1124108200c548840744480800e28076800b50030807084030340030b44e000289602d520140c00064500030000c64045400d0003086544810080b0b10907106409540d1075044141003400341c0d2040c80001d590702070060f030008404540b1703248000c0c1c09014100000155090310cc100300c4100c0041d030401590301c002100050140c10612111f07004458030580e4000140c003910030b04181c1d52280302010301600780595070f2aa40164103240800444000c40d80061062740c942d9a0f90380001c01410b13505046004174050344011495030b007007500240c1d22840320b2030380c60344020b507920780d0440d9020143c4805582464840c2c20005040f24140024403042515a448420703070307805414024141c40c02d4448d0a1058410040c0400115030002c1c2526089940314108200d0500520002407441c01041041d05490b500c00044c002046125002007a00007004019281b50302d081481c02600c5800499401d031b0340d89a500409502548540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 718847535 1250 718846285 718846291
    0x40b0712050c1f0b090a05150114040e13060e0a0312110d0905101107060e0f0a08130801050c04031202070b0d0b010c051e1002040b0d0b0f04050406062912 68
    0x7003c002031642e0040002108140150341d9003000594440038045641c1410554416030982807d0041110300088000d0403d44501d2041058100013540031443c000c40b003046141e220340e0806020300c5592000f403001911039180700d6040f40820440091642e182c840c5024000c0641c1500f8a40c0f410049101c8101c0040e01c42d4200c216054010051005a414150b2041500030f007a41c2c82d43d00e445001c5407030503a00726842104070102c2580406c00c40241a040014100ea015504c03060709074580b100014183c0c0307854040c0d003129020707500700020071900c400400040c2c0b0889005810180d10310018400581c0c84110600800803084010400d2030034110003a040f42c0014001031600501c1c5622075140c081c2403807204261000c0d46a14480711111220b41000403c5480030445011450300785444c031143c8840c420b40c1c15110980783c840ca00303540f0b143e4034000100e0815a024005001c94506458010010134071401010580881d002d0b4040c284446000401d240446140314103103002181c40041c2890b03a002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 718848785 1250 718847535 718847593
    0x2a0d0c1211010e0105190b0307141504080c01091202090711100e01150e190c0e040903030b1302040e01170319050d110313031112040b0712050c 63
    0x71081d5a246100900c1050a44421040009414205003001c901d4181c0600c00c0e200303080c1d044c181782800c103a8020070002d040390055481a0420401c080200e03c0300c0c10709900c0030422080105d00001c81c2c000c04903a1400e2400c00744d0701d0754070316a02d403105c3c0c00407000d4400020350003804840000d15814003410780d603c18003c0c10310890720803180b000302020a40e1841454400c4994480f00c1c0180118880c3c031005001d0708a40764980c2451030115130003941900c80d0441c8a10140d19004d80402c1ca030300403034030a10030b06070240086c45a11401e080181c040d00f1804541401040e04600c4d10400c0100d61098400f035840312400c1441e140d1800343c058150396681c40001b00c00340820480103030650307000010b91000038101e444850b2682c4100c1200411602000c0f803200450b0790030010881c4c14032681e11241c030007a600d400d182d81068291850b55281125140240302102c00001c0d001c03842d94040e4024103800c0b0322525014204c01d9181c4401c445500030012191150b0740004810008000013424508820310302c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 718850035 1250 718848785 718848797
    0x30a1206050d06090b060402090310111306020604031e0c110613030308160f0e190503060717060a06140f160b04060b0f0f0f03122a0d0c12 61
    0x1100000340b5203041801d0100e440e90fa0ba40c500b5010001c0700c0b1465a409601110110700300b000e00300101c4d85800d249050b41d2602a591a0445e1010000000752410405464407900030940c4404000c1e550704000d841c2a00400c500074000002200c0d04085450752002036580c003264007030b040d40d4540b46c1d51000341ca07003a0310080912800b00c1d80e40e203011805004501a5440800d5030804036000014030362040c0c40541000f410888407200d0030340001041d106614240c1d41c441c00d414044414000307402094000c142c1c18040c1c50300b800303c5164003200b5080c2c101001000c0300c0039070716402c0c100820955148a90381c040b482d40400050000c0300c1c040601101030303810451600d0071741c21002c0c8400107808030000300c03085008071050100307102d4984034421241400340c0c0c4860a03018090005401c000b448100c0c00d1081c03031314403a00800307a2000c2c011a0150042941c0941d00c1d201c1c0030440c0c8800301940c400140d8401c28284111782d40001c0059004400b00894403254841a041d803034000520090001c00d100b4001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 718851285 1250 718850035 718850039
    0x90507021b1516080d0912030b09040206070827010f021612050f0601030f0b0703200d0e0609070911031006180315050a150e1602010b18011d0108030a1206 68
    0x600300e401408188400c82000840c1b003da03140c000494030b110040101010302e094000d6448d40c07900002c498100d5012548640c4441444c58052594482c3e41e0720304403000749980844090003800c503a5000544030989800c030804c50743e5581241c0d60f0248035039031421542510070030044400044c240500d0540610155030059a0b8282d1140c90300d0f80a0344211084400500e40009110100e8585600100186401d001c0e240851100074080782c140400e02c2c0c40110700241105525120ba4009084c40c040d0200b6540985040c00510ba1502c00a10464100c18244801301d207102c4a1442140d00c10318408130318048a5003413030030403600e03406038840304c021f0325000403030110200768520180d6242c4100d00e6404940c0d4640f40a502e800e540100084912000c0d4070304060002d44002d000056203d42c010310f0280f4011040c14080740500740420b00142c00c01401044240760f103410410703440c10f807114010450304507984640b100a0000c0248a6249c2e590014841c100740c0030f05c12407244500707001c000c4021402c0c90b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 718852535 1250 718851285 718851293
    0x201216150207120b0a06150e0f0a080d030b27040303020c0c06030103050604050c04060f1406130f03030e01021f05070c08041d0c0702090403050d020c07090507021b1516 74
    0x3d600b5100079a4041100001c0249041080c02020017a0610b04086110308464400282c0711410105009115043c120003504054490700c1d01c0600070211441100d403500600c4c50040c00a102d401c10841c00b80d04134040507030030306142d403102d00d07415039000036510604d40e5103803801c40081d0404940d40006000c0c5403120701d55a41c1c2c5001960186004d040036000038141441c016280c40c0d502d01701c039400703903081281c200b01a03501003c05900716013500448203c074000d0640040c0e1140f14a5070100d164500b031810104941e940c69091000b5644030340c0381d00080368440c10040e41d89a0201c030074800082c03411801456400c01540189401c40343c80e05003190014841d40e20b01443d0b170442d4200344807110012241d14034407030000e80d0558001c00d44a0b0401c4c42c04080d500851240c41c001880601404000207291150074026412102980c4124003900c1009444103003180181c0410f5642c00014407811003207012030b180100d05a200510000d05401d0340c3d400005045509030800c40140f40c0d203e1013200104042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 718853785 1250 718852535 718852559
    0x3140a0807080406060e075c03070620031009020702010507151a192105070b12180705040e030c060405340b07020d201216150207 57
    0x611459211510129003940c01d00c0201c0500304080303040840e52072040d0101400c0b00c1c1110380059801d0101010520100b12301c01c414038864440706203d4031001500c801404001d5010000480c0d441e03440206003207107890015030502090310884c480d00d00d0501c0400200b070080c5d004280c0c1c02e2040c1041070034051580c60b00040c0c0720203001032101d51501c9640400e40d024008400e0351410308200c0d050881c180c0803c095540700c080700d00594003040c414840389110111215081814281d21004a4201e50b4469020601f01c0c1c1083d40e018169000c5100482c0b6910a0030f011385c0d00000300c110080015038509020003003d07002458a40070103000c2017008400000e028005035107d41d001e8001410710707011801e0604500040c030400400c041c8214880c00040c043c10448240890b12049040e60311004130340001405075009800c0205422880c0c00900c443d4001c1c80c0c55007c881c00102d03800c1c0c4000180c195096140c2c43c52000e0416000108030050049500c800915203207641e00d481240c24040d1242030304801c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 718855035 1250 718853785 718853791
    0x90902031008120412021215010602030706050c030103020f191d090d0305040b0703090317090d02010c020f030d0f06050301060b030a0b041a10120c050703140a0807080406060e 77
    0x8022a0724001c1c04004400c222403004541d040480c036140916144d820300c480b001d003040003485185c0b00d40c034186488504205202000031000342905655951b4000a0759030b0348039000c111070480c1007000042108100c8810b0780e0480f41c0280000140c000070030300f003210101c05d22490101c41d89004c4008507900c0321106880e840210301012107511418001410780c98103034400c1c640001c05040c0341c100300000303a02d60881d9130006290704000c100214646420b459141c03240c05a030303020740820010030441d017000141100c1e074144e0a80081000c4045040304903250140700e0340800c40380c0e0007000b07450840e014960100c0302601c910000005c8880d11400040e0039105154401c40c15407002105000716030042e4407a0f0110003500706ca00308441c1d0041080e0110311605000194070851084114465050291a11480100841d0b101f0030030064030160282441c1c01040c001c0d000111b98840404a0070310711012130700854050340300c01c103c40d074441e002150805402801204c08540f01c1c1000a04030320184240c0380 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 718856285 1250 718855035 718855051
    0x12050d092103021606030c08010b0306060403140102040b0f03040b060904080a0e030c100f0813020a1202031c031a01021b040e031b0706120b13050c041a281d0109090203 74
    0x4c0d41140d900004123000c4043e08007401c603020802c144842643e403807013143c00301d0307510240c0d42a002c4000e02044d4024081d503880b0724002c040005403240300c0c021100045209a00c244600c40040e2a88000d02c101540215002840e0200821240c1c00c850301801901717031607800007812150300c00c0c000c2d00451040d040303481d00b80f00454041d46004c4101074100c413000b6408000f5080c41c0201c030b603450300010b5030076410b4451501c1844841c03441a055444c02c1c03220f42c403050580c00004062010402d4000e0050415001a201d210107164808000e980701140c0390f000c844500150202a0280f50708000090281e00d0501300c1070f1008201030206480c1c0e0b000d200441e15050b60103890118a401800303048a190310300000c90452030b0040c550b003580c4c1c81030208450504641030003d00c603500c92404c00c002d88101d40010420032441d815007001c04407660300606541c10101c0c0c4880110384800b06400c00c0d50364800b400800700d5441020742c0e4400b40c0841103000c0c1110140f511031185552000004100d07070098070064 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 718857535 1250 718856285 718856291
    0xe0f0708061012030903030305060109031a070318051b01020c0a031b0b091e040e160302041103070206010b0a09231002031615140112050d09210302160603 68
    0x124002c508840303800028008141d002d00340d0340482d500242055103c1c00002c0905988002050159210310075242c0a160311800240c0250341c540018003485c081202c2c410b0029080202104160424603550f0405d80e5000c0001c1459450001810710401c5a84000354118401c90321010216583d40c00c48000840c052608440700010a03900f6102006698001d10300c0050204050002074640361310322102c412824140c160821a00c0740040c1c090b0200c482d20300310b02d214110784542c82c44c1e00a90030f03900b203d100303c9e0104402203135404613a40901003110740c000940c01000042044481580003400c4030019440c00c1d034601500d0740d900343d80610300100da0b20700ca0030482c04000c41d641400d24010341040c0750382c0011424101c200c4180c0f1a1007034003840003400e0351151038a55000d456070ba040200704a40079107550746d207907031134490f41100c507030b000c0e642551544240b1012040560065a5007000d031001003140b040d070600c1d5904208020301e8250700031421849404281a03d13644040101405019140d5000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 718858785 1250 718857535 718857541
    0x42130207080f1e040b0f090f03011a0310060302030303010e040f081215010c08030a0209040906090b06190605030106050c10090c050a0605030c03060409050a08030f06180f0a0e0f070806 81
    0x1545010402128407102000c00c402e004078003182c001c0d11b07024041500a40d98480c0f034600840c007440d5922038016095802c011942c036502952005203540000144c04894140311501d02e403800707440c500c2c070020b90150010401031205161904070241e200340240700001810410750394213619075002e080303280f80c00140c0605202044a285140002c842c50034a0308030001e8070251220b8001c5c0c48090070049406600040c46545911280c00030901941c2040c410081400d550030916149c9034110f580d0f03841401d10038078159521150410700030030b0301c0b880e90750103007180e003001c6094510382d10034400c810701845460560382503100d560281c4601e040c810041d00004610300b90901c50907561a80140007070081c1401045081c050400075a68484000c0740c0100c4c003c4075a0808909000660748013030044440042008130310003449500307a005180c150381111500c240e030344420b42140d40c01ea079242081c1d18404081002c4020542040c00e582d0405000e5805107580640c40e03601d49201d81d440700640b07400100030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 718860035 1250 718858785 718858807
    0x2a060106090e16110f0105180105090d0c0323070302070e100e340207060e010905030a020904110a12020307120b04060e1542130207080f 60
    0x260030014840c0032044100c41c1400348078007150400000c0c5030310401031000502c10400c84c04101c01d80314003d50354001c0105003007020b008080c60b003034590340e51034641c2040085a07074100e0000d80764804e27503150f6950440c0c0307881e40d960880b0461040b1040c21b0311012440c00064494000754010300003a4840d800070002c01c0d281c040904000c400042400e0520205244104003002c0629401940f00c0c00703444e400c001804c03481003d0340c10020030301c202001403e81018010200360300003880005403815078503004901c0d21105c0045885402e5409120b8054000e482e140c2c0050034144103981d0030503c0740000d4080c0c1200031020854a071126401012442c0c96415118103504050200601a00205503558185441d64540b510717280340c080d000800da240e8403101c0c0d01074541c0c02c3c40f12690510025011000c5401c000c0509000054510030f100380c0d0b00401c141805044401040449039078081c4000f00423222a400704005080010158559203035800700880000100814010038003117542e452803649425007440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 718861285 1250 718860035 718860047
    0x1803080f0d27170d0507080711011b0c02010e03160603060503010203091908190504150e011b050102070206031008060106020c01021002031503070303120e030f040501052a060106 78
    0x1c1010701d10403120300b0001403a0041e801d500e00054000303400b8010051101c0180d10b09110313412543d526585002c081c454400e41c81040e80f4055441540c9241d14400c0400285080b034980c83c0c40704104a402851040003503006000c1d84914900506051000d1003420001c81d0400c04400008208208408001d2001d40c2d090f00c90807018120a500860542c0740241d145554ad001c0442412140c0020201400801241c0c1e4202c0b2030058110001511019100c500500203030000d002e0500d111125841e0704400500c1004008144001652600032404486010901c00c00491006540c80c3d5000c00410016842e1b1030011400384101e40c00e00c0e00c40314039045c3c03403a0134032034103030000780854201012103902a03900040581e15215824030050392500d1b0150b254070081e4500d807105402d401400c100005050300400c0200714412003200a00c20030f94082540340d264411103000b52000b01e0305100c20700081d40300d800030300f11400341d01410440715000c15270429500c0020040c950800d5111a00512000e5849a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 718862535 1250 718861285 718861301
    0x9010501060f0216030b100b0a021506190e100b041806080601080d081509090a11010f35010807091406011e1b0b1b070f031803080f0d 59
    0x71018082948041355132100700c242da403001a20050542000c1071484081220a0303008000d4030403078550b5680c0031540691206034007005a540110b1000000c0d115080c040c4656602034801e00b006100da17400d050703c0d240c41e02d0015080c07091484d04140041f440802110041014012207500d0100c950541e040b540d0039540641c201311240e801c680c004000504000500640b18200e50030900502d83d1110705113540d40061903903695109814006210207940c001c2051035917140140c2481d900e401d226401900d25491640c140400030b00c91030b04801e10080702413031b0092443c2c5c00710075001c81c140c030601c1e2003c80d9031002c2e00110700075000a0410040e01c9801d124112102010040401d4680f600301c3c006800d910b89101c420342d00606a0206402c01407160700150200c51558070042d04801003030426409005040f1001001c0380c0c2d500c515841766560143c01d8070350f140d60004d40300700c44105940e004c40f000803030500d000340844d201a0303000c030009401c080900b442c1060160381e01d44414010305508141c407064 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 718863785 1250 718862535 718862537
    0xa0f06030c0e0a11120618040f0b180c010302071a070f090e0606030610020f01240504061202330d0b1027050604090b03061503030703030b01110609010501060f 70
    0x442404201d000d131010345000c107060071410105030760384c00301003502c0c00c0148420700045c1d80008100010000070f08451010180200c03245945640d9080586a59002e01088003001d41d000e10600d42d40382d8440e400030301e001d074458070199018501420492405280a49107000131845480b004440e00c0d42c028550b00040402c690030711414200000407900030f200181c615401a02600c1c030302c601c0700307008010720f501640e000c00080021304c66502c0030b420f1000d1743c4040c01080450701c030742c00030f22407078903001d00c2d41500c3d00883da09083e00d5080e03080003800304040c02c030020101c0c400800840000101d0000410454940220507039a902c1e00700728208075020414414402e10030321401402250784100c1c8410b0442542c1e040049184200c400d5652036041035008a5000303500182c081140015038101c900040d0b82502140d4403034175203088244c4080701d00000703150194014402c500101e8441c0d045a40c0000c4181441c0b580d440c200c0d440740382040022540c114103070391641e00400000d9400602c0070089151 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 718865035 1250 718863785 718863791
    0x308040308100320120f010b1e1003090c090606030c090e040309050907020129040c02030421030c02120109030212090904120509060d0603121103070b0a0f06030c0e0a 73
    0xc6590b818490003e00c440c0740300000c0c4500401001d52218030300d951045c02d81100300c03000b1420b002103490207000311041c1e9a01640201942d601c003c542078241512104005084100315501810118000d00000c075003620318040c082c0303000801c00c201d80304560240c4010368012445400d6004003901c8000b0703940c465810502d2007010400400e51040501c0c00f65002291240c08646031000201d000d07007075260101c6002551207a00c120b40003200380040182c050140c80500c403000c4462802e9071240514850b543c41309080c000b100c41ca26800c81d860010841c4070307003800b20610308a0f0f00490007500c0a0220504160340d201401c105041d0100003143c0c082004020701c40c507010340c0c04040352000308081c0005011050347c0c0b0803030100f54042c0d070a4614251001c0e10254a80e402600094050a1a40b0059601d140151500000f551195850018804c43d60f401145459101e42c6c0c1c5000f02c5000806c0000201d40d101d941c0710400e006070140e440218040c10b1600c1c80702e810700f80610512000540718180c1585 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 718866285 1250 718865035 718865039
    0x901060e011203080a050a060906080309120607020706030b010309200f0a0602030a12140403081801021303020f040b120d02010509010b09131e061e0e060a090f020d030804030810 78
    0x35102103015800740342ea500225654481f540c1342006003401d904840c9059040c000c0c00700d442030340000600411401100e40c200c01a80c103045d0951145000e5810000680190800740022406900a6044540c06142c0002e1201907034603004951101e10716241e00c0201b21103590643c0c2d180c6096039004c818001c9a46038004c91030418060351301d20603070302d5a8080c0032110142d91500400f950000080c1c00914000045c0713841c2c10b140084c1404001c40d0560481d8404110040103150144213440c0c1c00c01e08186900003035400d50b020081c410409100035035000e0340b590384004054842a0b0600800300030720b0002c0c103c00c5004c20019082d40c40091203094987c0c034201c103410345543c8058965403c1080c0a11442d00c03061709040004048901d02c0020000301d0320740c0c0f0030108100280d800280d20180b900c0004600f100810403140580d0400005a090360f030120000c2040c4187c0c43c1e1042891038818003200200300ca50768007285a8400d900c01c03c2e404200341c00104010b154218014a0f8001018219014143c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 718867535 1250 718866285 718866287
    0x111303030f2a15150614040b0304081b0a050703170c07080705040b090402090c032505090406050616150213030f0203061f0303030b060702090a1d0a05030409230901060e011203 77
    0x450303c1030340d0410441071b10003c51309a07180100d070b0140c1648001c055803480c260800c801c669003c44d9200081c84280c8924035001c140115001e0403055021000d01103c1e89151070356145810302030010f030310b404c808028031405080100500300003454101d010b8500603140408000482d40399034043d5005415540400c001650390160750f036800501d4008598498683c0c05102ca41c000c40c540500480030241140380c3c14003a0041302411a40904540134803600d500d03001030040c1f9000d658684c410184a4114040c00242d400e00154a49002c040c1d0050503d12582c410b54248100c0350300c00d8461100088400c0154101030200c40e41c032084650000d821000181d44010301120f4038400a020144e80f00303041c400550300c81003181d008a030003d00700d02d141c1c1000c82058009084078441c00d518030043c051507003c04400450114030545d00000a10300300f40c41d11b5002d00151545111400500c440110202355601c4401e103001c1c01100b41000004403107040440001c01c0c160103030842031010301c4c0415210002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 718868785 1250 718867535 718867571
    0xe070c02031b24090a0b0405030714030a140c060403061b0201060503030412020303090411030702060a110d05060d0204020309160503030708040513060e0a0b04111303030f2a15 77
    0x14500d00b15025401200c1120f400c0340d00d003d0381c14400d50109003101d00244141c000400ba2054450440540d030507a9902d81117900c803060000102034264102d41d1001000c14040403400010002e0102550401924070000070600e0740a60011600d8551700d54007440310323150500900000800e1070008100c01403e00c00007981e02c0c004d5205181881c140f01cac2401c03046480c1070064840c0c6400c00780c07080c0041020b4100002e182d401c200c0701d480041c401c900c005450000340c0c0c000c005200c110840c5203031408400b04109405403200400d43c0e038020304081c0c210390058446100851068010380058000f02e04c4207002402c3c00600c03035220b54800d80c021f2042703c0100e1030000440b0708981045a80d8403c4206403403050f4042c00709a485075040f04041810010520b40c503030801161a06c04a404022043c6244508c3d1054040e4504017001034003070140500000740141d500b011148214103001c500c11586851400c0d6140f06a1849001c072201e04030601d0403c8041815004808080c4105002c045a02d800144d83c1d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 718870035 1250 718868785 718868809
    0x170c030103020d1104050a0209100905060414040204151e0e060d020c0a05070603021905030108060a0207050f010606031b03022811010608010903110706081f0e070c02031b 75
    0x300e03021220190302045600e424258081c28041c00c1440315203481f690380d1000390032141c0e0443c000e82048401c490440e1141440100f6644002c1c620750800d0304103400d10701041c0900c22a207410030f500300400705051a410503896460f400300c0c1d80e064100318040100c4030110101250384000e010030306804d400c0caa583c84090f510001e88075100181c941c100602c0661500c2140840074210340150007010400355030540003001007044c00f82040c6128a01c84004541e03520091042000542084000c540802850b03001402014046e40480d1813074261000fa0700c0c00c40f0065840034010a03030f196000b015000030902082140e5010703050860a108941240b0b203507204d0181e03884031a4000007180c008001c0d01680c1c84440566905000300072840d11030901a0003031050780710540118a0140ca0400111000500c00060328a96640e60301545c5441c0c10744050200c100341100505d2003215004504604404071b1030f442058160b55418000a4500505080500c0e00c0b441da0040d180030320801c40c0c130352214100810 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 718871285 1250 718870035 718870039
    0x303190c020a0314010608060601020a030e092802040305010615050714030408030403110406050604030201090e0c07060f05180d0906140c15010f06020604030f050c0a02090108030a170c03010302 85
    0x39012140e072000a0039140560001016821400380040650205502000982d0f4080040b40d2a40d19600c00580c1c0d100001c48000740061b40310f0748840310f14101540c1c1190002020003035486490f01700480c200303065041d85000c1c3d5000e68042001c2044c81024000c000c000c04544c141c0081003c01c4640040551050a4001c0c002e145500500d440003001042110001d1402070241d03a00d484d140d203071060210741d912010300d01c514103003140071500f8a88181201c04881d416103d02da151441e01401036007010000740a890646018008540440c0a902944040d01a0f40e480003610345816407041d015403401c81141c49056001720000200305800501880a4503681d040030074420501c031045610500c43c03980701c081d40d8061000b8417103100c80e0144070907050b52100d4102e411400d4661204903915070007294060b0004100410084044e402a4010302c01c8501d010183c1d4882c10032a008240e030b0100a90140314036610004070100c40c143d001d41c4a025402403881c5c010300d40d0030a118410b08500042c00068 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 718872535 1250 718871285 718871297
    0x100506030604050709081c0320250c06080f15060901030f110c060417070b061e040c02031e1216020f011a0103060602011e0f0b131a030319 61
    0xb913109000361000ca00510340c200840e031814000e12600c00791040b186c01c0b039102203801c110800c85000710012810b10f21300e0803402140d080251110103049001850031315072208800c01002103001ca01d080400201800302d60700c0e41e4959040401c50161814801800700b034070718281c1d42c103140c4030f503a070b0b001203820051003442c0c0401c00650205480b0000d0442c5c4014404c851000520740c01750140201d001c0d4401c0f4058103000100301c502481c42042441510301c010302014013500090310501d8128104c0d401094040b50385a800240c90001c00c013150345511402016a02c00b0829200c00260038007603000000c0d050544600740b01e503110006141e03041c083c00120800b02c183d80a01c00b0ba41c803c1001d40c0a40440c1d40003407040500703d18400c0100f4620603441800203003404404100710780140240c005c64400040c04242801e072400e00d06008041e5001c3c145076460700d4410030380c120b99074810030900390041e04e940011b82e04142c400040c0780c40701000e5400d00079001171128403c0714000005202d20500e20381415 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 718873785 1250 718872535 718872541
    0x607051002030915094e0712020105090f010905103801020c010305041e03051308030309100506010504060c0c0e070201050f09060c070219080601080d0810050603060405 74
    0x159041a035107021240000c1400020000d00003400202c2884460301b003241c60f4113403082a07007070151a0900401c6050440a030320100e002e078406806821900c03040c0e5248903400c1c050b03580d5403050302c00c07200000100141e442d903052103144e2a0901c00043e240100e94002c110202c010380c1c5890719840b01010303100010360b64101c1e1200c5840000400410303092920540002009640481d00e403e50410034900c0c0148500d11080965500074841c0c18003803600f0264409540e00c0c40008038010b0301c0d803041c1c101c08001c018058124840d408200b14005425402c002d562030f46008001ca40c50b018044443c2c01601d0304140078010542d801c030044500742e0f00a442c00c040d4011031400c2021801641c0c1d440100078403d400200041d0a0781944114003502d00141c241c8003d80b0303003503640c0380c2e28001521b58400071101080383c90300525100481c41e003940f9900760030403002d80c0ea070f048550030310100343d01004440d042003000a0200354004c81d420307400300309140c152903102e0414010680c9800b0050256004075551404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 718875035 1250 718873785 718873801
    0x1120b0a02040f180c03150e04030e06030907031104051501050f070206040609030209150a1707091407080106051206060711090c09040b0f090c070c170a11060705100203 74
    0x1203a025005030041550340c3c5648030394003020071441c0c3c1c3d059200a864142ca1610a038801d010b1320340c0541007103011b05022420b16508148400020704128180025144007007126280c090286100d4403c1c04094103903540395080440c460001c00201c9807140703243c9000c20102c4100c14404000030741080c6001610341c1d0002c08062a40c0c49840400ba6201c6c40c00700d000902c0b103070b00c9038140056900c00e4582034082d44583c442a240d0b9804603c2103a40f050341044203108000c03111094420700e04111040769562a47c906401e02160782c00b009803100d1004d00410484040e4008420034010010f40c5003082c50320300400b408001c0c0020140c00c0354421000041e00d00244549025a01510341000b04840441c0c00c080050384015800b012000340030303909005c050b41891a11650112201e40f01a007400d0035503640c00801001e99010030000c9805607000c0d07001240003141c010b140c01c04040c003200180740380403503410a9984581d0844240d440342c48108010720001360041a94445450340380c0000da140c1d11a005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 718876285 1250 718875035 718875037
    0x507030f06050a061202090f100b16050d020a030f0804150203190b040b030a150905031903050105100c140718020d0b030106031a090a060216110901120b0a02 69
    0x12000c0c0110300c4814811080c0085980000c1c02403400c00301c204289503840708a9840c030125210042d500602990000b21031070400070000780d014089500707481006440d4144445940c0020071419581400e19500a0400004201e2040055424001010f08801707555009016065a000f07d50800c107249004c50100030284a10090700c00f084501991689020b240f0360503118488003e6181c6181807900007002418184551030020f00080c024214900164450200c240d501c10407845030b13227a4441002d00814014800703080b40500040030340d02c030407403011401029200306070802c6101e80c07220301c03169090300e0b04042c040d202150302c10018180743c1e10124440f0301b0051180d00c450301a42800000d1142c0c051242c0c0184001041c6042c2044201310220900d400c81e160790200030940070303811800e40242c840407000e580e8042c00480441d100801070b651800c080e42c0209203407034000c500c1403490004000c005c401c02c40151a09440e000d00940c904240e070703001494400700251044401c0c9022a2841c00690 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 718877535 1250 718876285 718876289
    0x150301150507080c0f06010902031603180c1805060306010e04030c0c030b0903041a120c0d060b0406110c010f0e010f030e06040c0f06030219030b03010f15080f0309060a0c0507 77
    0x75859118031320000101d403a2940256140d0580c01907400114032400c3d00d100707981c0542034a100281c02c2240710b541c241d0003007034070310444150020180c1600b0005800543c40802420100146a4180825000210550300301411032880f0303401407030050002e402280c40b201d9015405141424107004142800040740381d054101600c44500c060800c108844008020000ca41e0049801d902104100010003818000c1c591031440284850000c01c00c200b0501018000303100c0b450070000740a541e200a00c250f0b40d8041e90245000c5900c44100000e0301e603044c0240b5800c09428203155010f502c1d0060014401303c1e101c1d2000703051042142c0f050b540188250f10980086013590308132051803c0030300342000d041c0000e104e030b02d02c0d0030041007021070303103034030a000382d98501801448910855401e58000d4029042d40b201443d010765a40582e480c0c4083d190154004140301d10a546290500302566103080c41114032419105030f00401030042562907420440740340c43c0c003d107000003061500b071805030304143c266 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 718878785 1250 718877535 718877543
    0xf1203020c01050c21010515090612010602010902011707080a020f0f07060f0b01020f0304091e020d1a01090f090c140c0318010c051525020309030c150301150507 71
    0x10200102100c400005003402000040c0c20f040070722116805c58681082405160382107004401c81c2051380104802410605500030001d5060200d501c562240c400c5c4268840030040c0e4451000030f0543d60081074004420106041941c0c252802d50406882c041c0080c1820980d1a030006114455a03c1300d02620f000203900d502d078a41c1c4910a0420001810184094444403403810112104540c0001030b000c40440e04c6401070350804c4e10b4854010000d00b005a104400c9440b405280071442c1411f1000f80301410115100054501840401d9000c0a80860001d4140f25135100d09024075003101c1d900c0d8040303036014040030429a0030940b040355841004240c9580841011030464400d038808000f4008088441d200c01ea41c20080c1c90044a010650764005003507a00151011030b40340c00d01414040e800300003030038070320b4080b24000f0901e14200c00e08091140144c0010a078103032180f805010110503403030125010098641007040381002031006102d039598804410f04040d0074540124241c072002500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 718880035 1250 718878785 718878791
    0x304111306152307122703080d270f020d0204020708030103290a05071404060504090b0d05030a051e1606180506070c0201020309100216060c0f1203020c01 68
    0x2c10100644112209050140c2c404440b903100484001494161040703141c00c03210038241a205944240c685840607035040c810919584100d0030681e42040004008510843e40d50781d846001050700c0086800030004680d401c03440030400300d0a190441050319070142c000000020102e0207200203002003a0340c08000f900f050010a81c0e00c140800b07503010310b0480303010301c040d001c04001504401d40310080c1100204031002460000c50102e02055204030b60006090401c9010980844551321440d00641d000d1b800003500010f0520007100d460045064000c016075141c20340e80741645d14180c482c003030001d401d010400d001c50740c41340030700704100500d45070103240d0800d5a807200380080d4a840d529100106803140d034108a1840c0501100c0c06000e9801c41e000740180510391611031040794100f458007001c1e81144405d01164095076550000d44a0051007a001044858030540c0203840784180350307020809020f03d00114401203543c0e6008a41c400741d102044c08006030310f984040e8020f014400c2000f86a600e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 718881285 1250 718880035 718880069
    0xd0810052e0305180606130e03090d060b0102250302101b0f060b0d0f081305090f04120c1208061210090b01092306030118050c10050304111306 63
    0x24042c0e000900584c0140040354086891407122942d0f14010340390303142c00c0404446080040105a403104d109455034006507440c0c5800480025044811804c0994000d40d980540c0401583c0400c03080d20806280b941545c01c0c1d000c803855521070b0350004e03c4040e01803a01100b041d507441e4031505c5075000002009040b503d85c1c42a070b04040d014010f200c1c408450081c600946880319241c12007054820541c800481846110a55207030415a001030301c03425101391404d4001f107226601c07501c480d8410500080c40e02a180703054117240c10342c548508040d0b0240300d04400c0c1c840104090b400c05492901c03050418541d143c8680020681096944402903000e0003403443d441480001508100103250189030900c5503a600c84400c01c04942003d1030024500c001c00c460038246001041d041a030101c802000022a4030141c082e590703280281c090700700c501d80c01c08201c0c0c040914007008020141c040f2840c0107410346c039041c1d45841809801d09104d901c100e02c407200c40f4030010070580180b40900481881c140c80d0310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 718882535 1250 718881285 718881287
    0x1e0703050c06280c030f05040819020301020910050309070f08120703020a170a02011b0c11030a02060c0a0b15060702010c0f0507060905030c03030901170411040911030d0810052e 78
    0x644e8550032000250040249045280701d0700996042d1800070000d4140000c1580400d15601e002140498041d5004c2c0003018695071611742c040250045030300c40c1941d82c07070641d80300b41c2082c501e80c000c0b40e52440b8804040c00300900004029007a444e405070dc5a94801c65814181e00d041040c600041900252080101c51510001d02500c40403106800900008501103040c3d51500c010400f500002002e80b04c40001007001440c84c1401e0260250583c2c51442903500401c006030721404a04110785d0001d003140c03007082440368601d980002d0344020914900714182c0059800c5c8106440a410092020156028480c1c1101294003480c5c0c410101e40c62141d0320380300504254883e11070030b8841e02500d010640d0381d0030040210761a0403016903c010200d08200300341e00c04044090000e807041c003c180c404d0006a01c41348660207800d40142c3c5160f01043e410750815143c04400f60310070040041d803e007848121301e40b1900c0030087e90000c41f251420310851303410509a0085544000001154814402c050701e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 718883785 1250 718882535 718882547
    0x2090703020c0c0a0e070f030b03030301080c09011418090f0f060a0617071e090c051c0b1012020d091406010b03040506060d02120f1e0703050c0628 65
    0x30240e4401a0f03400c0a4030b0714104006050390303109011605c1c50f00301c00201081d10a4001a0380641c1c60b040000e82208000b001c68a160801d801c1070700c4651003920000824074044620a006080c007194244d811120030010900c003064103102c110041e40d40b0008144000c0c0144040010380302081300b00c454007201402460350751007043d5000765400380b40040c04904840400302e4031145001240003001d06615003050500c006090f0000803000d42d5005001081079580c9002b54440b031107090303480c1038942d0408101c4072808043c103818030b00014a415401c44007501c4007059442140705a040c000445484a4964006441000002c2c005185841100c008110054800c3c8190b00c08070000c40b00c650f070300c8001c510114441030303501030300d01c2e8050400a440307450000f026203c1688042c0812501c0c80700460740c0d9141040034901c4c844960444100c42c01303001403038012014102011002065954a5034070750036102c0c01040000c0e4002e040015043c07030303800c50540040c91408260b0410140c08559038500800c0c13 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 718884892 1107 718883785 718883797
    0x4020d0311060424051e040602090a0f0e0f0906040f081e090102210d0b0406050d1202060903180603070c0506011e15051b03070209070302 61
    0x405409105250007a8031540c40d03031502d4518a004e80c00040301d10704405950600c0c0c60308124111802c030450000e9456240f1241e03030039803a00d04202001c0d110b29400f05400c44a115000124030865811b582c048818007944168107882d03605504045602c10359843d01c0a60040021070701140c10b12080f00155441401e44900e001d5518460b143c0d10501c0701c07201e03502d844001c0313440c50a55070144210030b2642d01d6040d5248003258490b22489441c011000d44801103a500d03161098140c60f15072101d005070800400c1404105881e02d0f0010080f501c140341c03000140505400f096140000005070340e003001c00a8170800f01c80180c10240304803504005e001c1c1e002c004244c208900410030505c10a400707410780d0345e2015000c07034144c4540d0b000d110403030780700c0c3c81e11032628050480500e602c98155100003004c901804400c070b200b108901c0c81c40c0964500a0340c08941203044c001103135010380c01852 = true := by decide +kernel

theorem cover : BRFrame.Cov 718705035 718884892 := by
  have h0 := BRFrame.cov_init 718705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 718705035 ≤ n) (h2 : n < 718884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
