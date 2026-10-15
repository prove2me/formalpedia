-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4422
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:34:03.262149+00:00
-- url     : https://prove2.me/submissions/35e2d5af-7369-4a2b-9d59-974720ec2433

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 795143884 ≤ n < 795323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 795145134 1250 795143884 795143903
    0x608091b0607110915192d0317030907060c03080403080603070b0705031b030c0d12110d09023105100e16020c04090f030c1a150f0a060c0f 61
    0x42a6240b139400c500c200500c0b408806040345040512404803d0170184490103c2615020701c0240303682644840c00700103880ca040c030300c00745240200030406030542c40541400e5814000c1200f10082c18000c6200d01d1011040318009550749504889a410202d0f0290000328070078013040c001792052508ca03410500040031907464545400c80c00e01560321040c021103195000040070102551041035020445003000d010b90b0030710380d0300c0070b003c0e40f0b0301611a25078003005100b86440849100382c0e0300006282003030410072512000185d20b040c00820000b08240c0c410038001c1e01540a24070036003030360032507110518561400074001d50400d80c00b5040242104648091400d4003003005128000c00920494848103074200c103401d0361078045d090086c3ea140303449c040c3d420200480c001c6004000b201c6a95903140c64230800e0910203061400111030700d1007400e0001607610341030080d506089003024500c0172084440f1000b044445c402c2108542c0c1034400e0001160b07020360100040340e4804080c001d05401040f000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 795146384 1250 795145134 795145163
    0x90913080a020318033c030406090302031005270703060f022104080f0a18030813060c020a0302040b1c0c0312080907091a090c03010608091b0607 64
    0xc00303a9081401c41d040164400b103681c104100d581c0d2510204448160054180d0481482d610000c1480c00f221218440c500c503850300380310410046074603078521000d40660761034540b1140018103910302c512090b03202e48101889008407804600c1010b0286005072800c000381c0781f91b00310b400700181c00340321118514000c201c0000b0101e06240181c003800420305000507966803152212083d0031505014a18020308140204000510580100d41d402c503000703160542c69181c140e4084403201d100c818003910001c1b1030500041048000c0c000b600c2e500d034204400b4a0501e031030322001c031005c03a170b441000703548200c4842080000d400d003a84602d0400c3d00243c0007441ca045000851006450b01c14001c6941c04442401007090040315014084180b0243c50030117420306250f081c0d80d50340c9155022341c022241d83c4013034040c80c080000e407a040c0182c0010b000604c5078034014042c030318190024400d03500441d1004000075070848020500541c012005401600c1003a050014010030741c20126045032007800c42c0c81c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 795147634 1250 795146384 795146393
    0x31416090b04090e010507050c1f1e0e0c010e030a0f03020a02150d050112020117060105041a0d0e030a08070309030e0d110114030114010503131212061a090913 70
    0x30000761445501c0454861300c24204142160001880102082400d0140021200c0040703211000144070070210414003000d02d09240042010003c1c044010300000e01032035a100e216000400030002c8c0e02d080d184400c1d070040065030400e009101c200ea058000d00042400103400f00120782c2107038042d104881041d6140e6011070103a03154480e41a1450b2000301d1035441e403c05a025070381c054a004030b850b03182c941895001070401180c00d00c094001c0449039000071707150b07445041654010070b03000303440c42212050500d0030002079211080c10310b5814107007048035a40742000011521100095507491000b941c40c0c240881c02071031030010440410101070811509a0b4030700c111003c5442c000c0d5401d6152040b07650016040303054828030858040b80510042020204a04054501801c2030030465600c3da0380890300c840404401d140185000c103140c940b02c42191f40012001c030182c01c602c5003001002d0322202140100f40065405401000c010000309403981441c00301103820406071461881d00c41010f070750303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 795148884 1250 795147634 795147637
    0x2040b0424020102092b0501050a02040e010e040201021f090c230d12141b0a0c0807080303070c031101060810230a0e0733031416090b 59
    0x1aa940c10300400141005810150440600401c82c0003c5241c002c0f40c402051003c058160081c0c0c8100c0c3d40d4004909000490982d132503010b0b03009000700414038040904000a4116000d1400581d0107003002040501c01e00510b240201d4050300108500c1180202003c2175491a4182d002d501d5251401e080010390012792800c0642002e61412406040d6005214150100b46031380d43d200f011811000c030b000c1600584107554608651a00c0b6007290b1500368842c84903c03503200c80c407030b1410380d10703104002035a00031901425407413055400080541d80e0311036003a981c100d58060808290030810214403443e0080c4000800c00d4801c0c1000006e4900d013646941c01c60310b02e0b034001d450f40e4002641000d542003440c440c080300c10b8280d08800c2007180355041c4081e8074041c02030030414150b035260380d1100032241c200b000310010906070201100d940200310300d92841c1240504c0d40f101d0070101311182c0038014007a0060300d101c1244454000f61a655103000401d04400360b00f900300030b00c80c541c000800c0030683d150 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 795150134 1250 795148884 795148889
    0x3030815010e03100b2209031b020a0905130f0c0501090812030a0b130504112110020306012007050910030f030e15040e04050d0e0603010b0711181501020601062102040b04 75
    0x148001a003600740d0401030301e20810020032740e51440e0602082c00040c1d94000c00a420b80e07a40860000307459440007880b541e04041144050300703400030000c0140c10007041a4903101621000c3e40e40485166681c1113040d0b0754500c0d942008060301050001824410007507000c00e502c00401001031500c06003280280d0102e5a0584040d41d041c06030049801e507504004205500740130b440d40c1d1842219000c5220765458a02c0c22682c1920f103500000801c509a00c0358190b000381100044103500c407208400c240c1a070312074451050034000d01200c40000e0003254000e200f070007102e40100d4040d078040c005903000c494620500302141ea108034002044c00d810003250340904082c02d2450310807407007400c181c100b262408000228030390401100d08100c1c4042d4442e0001d40e411030304441d450a4039030041d40ba06a80340c5070b0b02c2c00c13100c1e0015003921040c05018021610603000b1a04801d104010107907003801261a29402d004400c0480e401881c2d0a404604a80c1035400101e1510001410162201320781856680a036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 795151384 1250 795150134 795150199
    0x27091e0c01020607180317090402040f0602071e030311010e060106020a052b0f020f0109120e090c040b0901120e0a051212040f02120703030815010e03100b 68
    0x100015056075070100520f035042250b50400c0020041402e851224482035804001c0c940000b90281c42c0c0454100010f90b0464031004009644494541501d1181c800c3c0c28850340d0010303c0f62210005520b030a03a0700c903001c0305440f00f00c03101d0340f43e00310349080c1d42c1d00c149203d82e8a215965055000d2080b1000d0044501a05030b42c9d0181200c2d0284e41000d5182240791008401040400700d04c02d60519040410b807030401f000c90624105020984800b40d0404005130302d515001d500302009030302000a01046c8844c20b400f140c0310805000d2081d820f100c0518004c0742c40380e00c2100200000c0c003410704460042c5c9841d0380b05143c980c15143c000207042050f100030004444c213542c485140c0904102c020705c2603061500c14211098100300003804134084d203020240c13015003c10240b00b0342e0029916a0303580001d0803200c040848501e6035492a0080c84198101d9030366070600c4000d5a16403003503200301642005a20700800810035007041c0c0800e000100814848650302c40019205003410140b2242ea0440c5c00d07282 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 795152634 1250 795151384 795151393
    0x7140102150c13030615140306010504092303041a1204080f0403080d02040302090f04240f1b1803080d0f06030f030201020307080f0f0f0a0b0402040f0503070527091e 73
    0x7032190421b000c44107421103100303000000301540136a14000340c8075044502c00c840220310008a4280803105489504c140c1003081c10101030b40042810000c01030003240c0b466030f080300050455035000c16a500425008601054030a03000c80d02003101e40002d01000c128004c5203d290694aa4600318a035006e54003010342c0640114007081176140a800b520b60099803610b10000c6450585e9034034070601060074014001e160501400101408103610108000c010706404012010006a10300404e0540d40c101074000362100080d5002100c41081c108100c952103507120303003410300c40d03190000503004858003409550780ea54000008212002a20000103000760001696401d0040004042079030040540385400603003000e20846000d412103a9070700c4680300041d9125610b40d105c0c444094078070f814045501038000b28000c0342031020088420111001182210f00c5280c0e1002070000d084000038408480a409054120801c5480c0e03484035030150300b01c0e050312064521310841c04060b104464a56186070310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 795153884 1250 795152634 795152651
    0x100e070f0e041d10051b0c010213080a0c092d230f0a11040324051e100b0405010c05032109010e0a022112041707140102150c130306 58
    0x203101000c9210f109013428442407800b590017401c0c20345c046d018884480000540201b00f15802c1d410707a140008200342055500365a02603803561580854004d8516036000310b070001c2d450b4400e110b1505031040e8a00800d8100f0000c81e0310050501c0c4070444040f00e59200d0385400c1c1d6000c20350446da041c88184079210700c000d0034104100c01c0500c01c0108020840307442c2440c001d003000007500036101180d41c84a944400c1078804641c2c0c2946400c6c0a60604065062034203100040705420442100407014071044201552144480c070b032841c003107124079010b0400c104001d0119510404110303415500030000c49144c51019a0f80d00202d644605104c140c5c2d00d035500034000b05c0203007070107655180c00045c0010001c0380c1003a000a0800c071203940d08000c00080c00d880100c0c0c619800c1c020300c00340a00900405032540e680da100b8045d0307513500d0130b120344d058080d181d0041545071010491078180e0506900501c40050506c000180d0034001030802c40c0320b0038040c81900e0034803103031a1444010311b20840000c0388045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 795155134 1250 795153884 795153941
    0xe03062a2a16061d0103020909070201050601020d2307170a030f24060509120703050a02090108071422020d0c020f030412120905030d0302030708100e070f0e04 70
    0x8035150790b00c0c08907440d00c07181040126486004111250200c20708415541e80360380050b0001d101d240d40d0f0325000303040c0e02d040141460b019030041d486258280c090b00e855510a205c2100c0361074804a90054040c0d2160722076106441c0140900486880740c170108081009441580615402103840b05000a0301c444c650002166140116240c1c10311800015160a10340c40c94194415000c0c0500001c215001c1242c00c0203944944100c11b00482260946600c0d60700c90a2041c2c07169429102680110702800c0000350003640045d811701210507030070000c00740741d251008000605400b034100e00201140e5118a060512a5100a0410901c3c0702e500065440440b00043d00b003140ea1648812217402c00d000400c02100d1174140a2255a4044040c0c0d0076109400b5065400307510300c0e0403541c1c040c07040100c0160f059030154002e50040d2420b03280d220b0181d0310480c91610048941c01034116058911004c10190b074080c01d01701d403070840c0504241d04c50702034140105084510200c810304054028190040703600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 795156384 1250 795155134 795155143
    0xd0906050403051f0e0709091a070816030209060a08010f080c2d09151801290d1410050306040f080702150a0203120603070303270308030a0b010e03062a2a 68
    0x109e110030046807586462940a428508001c2c200e59040756004102d60480d4440ea0456590180040029132629002200100402024003032242c4c01e03a20000041441000011650040c403801002503d00703540d0418002008030f4441214031407407014002d8022565501070030030748103101038913000164006600c1000a082c2c216070082404001480040c401e03a405103216107031195142c1201200c100700b07038403804180c3c0308894081c0c070280e10300b10490f50440801c801c0940220b02d100607a4031081d45400405031158016a402840c0d647c81145490000f9400001760407024001080c583e04000b8522140c0c0855100480d2070005030800100300c12400960f100340d542180b8154000c20a690940d0b502504090b21211141c0c501141181a420788804800c56500030b140d0148400313840741007102c3e0b10400b0341681803465010500010141d074881c10005900e9201d2000031160035034507001c0104045d00b04025001414008004110042246007900041d0740a10300380c1c012002400510840e69040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 795157634 1250 795156384 795156413
    0xf0b060702150405101e0815011b0b01090b0127030201031e0504060203090f0109021302030903040f060c0c05011715240301030c060c03051c06080d020d0906050403051f0e070909 78
    0x91010b200b0502c00d590410500702d0411503801e02b00b40c4240044148042417a03424613100a0441150200204050300580c00240c0840b000ba2034403801850701c0700c032007952000c08100450f200c25400e041000550711039003200e4895401c140c2002508040034455006403a4100e90a030b584540000910020400400528075200c664600130081040c080d80021082c12003540e410302c04d1038000c004161411000c2c03044a00400890f0180d81207036075a401c0107031030b46c807000710300f5200982c82c0798001032594011342d882d582140a401c1080850781c0e07112812400400030314806500326440c2e038440822520702c4001001c00c50210000b00b030300e0390300d980b03440c00d80c1081680040040146041e44000001d4006003070b01c0c14a008441e111035a1030072641c16000410701984000e1661148102c41074200340c0218192130941101e5460220b81c94136000d081e03802c0d02ca45d1000a0540d48503560001403207007851680c103481440c4260210307040c3c000c449010715190031900401e03840355550b200c060400074100d108690 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 795158884 1250 795157634 795157637
    0xe0a180f0501091115040e062d010801060504060203031f08160f06020c01050706020c010b10111506010e0103090812041a010828020f0306010f05040f0b060702150405101e 75
    0x1c3d944884113002450303015920803440070340302d07c0c00812410798804040789030007036a44110315904410140c42440010b01c01c0046030205011030000b0680d10f11443c00c480940c1c0e0a03400451540d103542c0304070b85a140c52022601240c5c11480c0005c03803040c1060100101642020500811082c14550b1107e030144482c1e0058040d940416500034050340c115055882454000b00c0060301c0c0c0031182d0095024002000c1480d90016030700403032110707150f000510080b100c807200c4100c5600352103128595400c07640a8892601240c2c417042c1c000f0300740d840703a0800d0300c0c0c0c0e504c16984c003070502d09050045400075a059508031805040c0c030a034130202903180300c3c2250043c0724110003020f0700a42c3c0c14034004040f0034210361a140b05441410f240c290b480f201d0f90b1000c0010003404440b030075a900d04000c03480210354001c3e148070301e0811103286140c1a07113018880000100401c094a05401c55082081141040002c030880c02e100703100008081d038804001d00c541040903110b00003a240c5000e8801d25081e0504007000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 795160134 1250 795158884 795158899
    0x40606030b16030e1c12060515070311072403020409020309012301031707210513050102120f03090a051501210b180a0206031608100e0a180f05010911 66
    0x54404a01034945003e150b141850385030203240140040107090b541d005140c01c80c141902c0741d1800c40c1038200500c06240681d40d0076004100b10033030039840e014240f28000e81c003000100244503102d00490b0403803121656040043ca8030b0f9550718100d003030380c00032260450565500c010b140f0600030a1602e450400b00c01c400e616210f5811540c1e9404d400303170b410143e0344c42100040b45001c200b00a8040b00d1002100b40c218960020b0021a8006c0199200d11900c07031481800d05000200c039400081c00780032104540b51010f0820132640c4035400b0742e4100038240903451117a01c207003002140301030040035019200500458010740c10000013140c482d090a018000350545100d62001145140003229000300982150b02c6000324110794141c0b80c80c40e0080c020390b002e40000107010b1552080240c0c0c00303502d80b260300c8012259a0700700d000da420304030b00c0c072941004106038000168070f044541d02098805900340c3c4000c0f05407481d515038112158034160200e40c140e40d43d10090040c017507100b11000d0b4410089840703c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 795161384 1250 795160134 795160153
    0xf070b0313081602060d06050307050103060617040c21051c0e010309080d020d020711010216033003020a111f0911090705030a0f02030601090b03040606030b16030e 72
    0x6820500c48110103012520b000c00d602c4620341c61000c8200724950010709a94851902c07468940c0200140e11a840c8a485145000035003075010380240c000311102c0c0e0302d400d501011005901014038000034411120074051490101380f8001d820300c07800a00b0621201c5900ba11640d1900503d00450840c00e41010003c164481d000c3d00e43c045001e0703120900a1030702080003181c91034009298010300000c414554000306036100804001d5026155041c00f40c103000ca05610700e0001641c55400a8001990704011203805001180c00f03c582d412103051603010400d000d00d8a040040310f0464001c0d16040000d4000640402d85540281c2a00d05c0800c0440609000c2c80301c0d544105190880061016005440d01003100a001025000015454024050f080715140c0200010501e0344100c032100c100d140380c0340c0c42640500c03441c800d9a01c5410103840e442d0302c1c24200302c0420329a40008108a400e241c0310203000c800a10a001610300803822490b6100d04105e818001505450102e107404440354001e0210 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 795162634 1250 795161384 795161401
    0x1e140405060708150409031719050109090b01150e031e0c012c010c05070e010e0a020c030a08060f0a0608010503302203110901050607020d02010806011b050f070b03 72
    0x201039040b44d00040906c1a49000e071031701c801015030f000040340301000b08403100760750300066504032080100400213680c0b903080313040488524910140c41d0710800c00040c040d210144424504680040c1001031092602d80b00103458440325800036800c82000c1c1c14104440c6204010482800b0000d00304403100d554140741e1815580c412006262020540c0c1d9105d140d80d0b4001c200703030302105800c04207858105468a001280c00302c0c0a100e043c56442d40280060440880380c42580c25614402014600d0561415011141c00c41c0150209500c440c2c0385041c06111355400200c4001000503480b801103a61400e0101814084095040d905c07001203921030f001c100b41c0102000401569410340307561103e0052551030b24240540c0104450f503140041c010060110841c808104420100c1d0b0040060b038807041448400c3c0242c0200a4101100c4004100158052546d495104606140441e0000045214084030011800e415200341c0c00c0907107074070302e034002c03c1c00300902400340d506030bc4d4a981003031003d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 795163884 1250 795162634 795162661
    0x30201180f060315050906030d231210060c05120706060b120a0c020f0c040c090b03240f10031d1203010e0c041508040302150a0203070306090c050d1e140405060708 72
    0x80040412007800012052201c1103c1c41e41022640488819194880c0266000b1103100c2540d80801c00300380c001001900901c00e68000e0070580e4007001030f01c00d144041e0b901c9246038200047011240310340c40e05408101c0e0070841d0060150140015468000d43c280107010340119045010050215001100e40e00c04825000a13089036042007980c1c002600c50480c5011227910549800400844e400001401701c9181c904010540d01160f1107645204e04a40c00100040301c55103494644e0030480c0300d6503048455010307070b10401c140c1c100480c11140000b021103183d8103094030400c0a0220000200c014403580f80080c001030b600020a00c185442c09080080e81c4440d00c420303841c0c1004100000c030026080510912110070004082400d107089030074171520410113504219105d00000785400000500b42e4294020b4164418940c2c032030310f14280343d030301454014004101900c0c0d50b03282120700c040380800c0e042c803581c0392030480d000341110141414600242020300150020041182e00001c1c001080300101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 795165134 1250 795163884 795163903
    0x90a0c3b04090209040b040605010b0306010c03031a03121206180433090210020105010f090b030a08030a0207152c1507050307021510030201180f06031505090603 71
    0x44080e140da240d00c0020300a025480c5009400c92820300620040000e5091003d000f43d00c6900d081c08240c0e2269401903441c00110303500350029601d04181000729000f94001882d00201c9076015400d03c10440101e0301c2c104400490800908000410045a10754082e041c0e0f08142c044428038544c601441102c90b4250029201614100c0c0381c4440480a04252401807650114001d49803122107031081c00e04000d041c7c400090380101002c40d60b00344514810720a141c160748250361510002800c11441e000113044100103142c0510440004001003085c1c000510710941c855a40507a036160140381130b005071209003903030841c282c0c102524985c444a00403094034807a44800080e00743c44024100e9540340240c60058540150960307014044001d43c0040158820411074003180e180440c4410410318400c41211222040c9644680a20043d03100b81d00c918041070b00001c18915076600c1d0300c0145106e8120b40d11000202e680c07400c03e00c8100c1c50404140c002880c08940407201840c0400200742c0316007050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 795166384 1250 795165134 795165227
    0x603020d080f0403061e0c0503101a120c030106201908040e0403121104050108040f0201140301140406050105160f170d0905070909020604061d090a0c 66
    0xb244000181100e03070160790080d034002c0750900210f40000d4000140d1200401c3c80f5648504192000680c203002e1421680510500340c4e111903030324602400804521016024003061820400c02650440d1a205055000d01703c0328001c0c0f1342e41c0d45040c00180c140e101c0c0300006003402c2200010aa40464041480e40d50741c00d00d01d009100e80f1001e032810504074480e94004540c000e402030f00348801d144c0c0c0315003004c021403541c9100b000600c1c2c0482e106040c0d8003451003502d0024190400103400600c140074a90304462060500340352401c1c3c0c9800110b01c54100360410040741c4452000201a441e207030050500501080c06e1840c07038103420825a490f03210070078001602c1c0e0b01c8415140c074104925413004984040c4500302c01c585420402c141e94001d041c081e02d054801d0301c20200d01048030841489034110b510741c01407080e840e01d45032a070191180c402c0010001520040030110211503150007031801d1040c4004440061001d85100b4003810700c000c400943e68011007081140000341e4003000c403110f0700c82c244 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 795167634 1250 795166384 795166387
    0x403030809011e0906200904020903100903230301030b06060304050c0a120311030306360424061401200a1a0c0f0a0305040303090b010b03010f05040603020d08 70
    0x81c0700070540500f004424070704110300494010180701c81030303910018203d0310031941403200d00d103249030a01121071505907101c410141000070600700d00d0254000d00a01d0000750548003084070140c030301012a07880c01029404a5220400b420302c4615800001c1e00030341007000041d0840d41140c80b402140f0a0080c140b80c0a40390010100e0140300d800c02001e800f983c001016010215200c034921803070500424412408901003001c2809201c070040107807441404041d0505488803150b40300954a070f4044915440c100d00c075807002101c5202c418103210305c26405800d5400401d030000b40c0c40c58403010395020f5811224030f003400600c100811203c045444203030910b4200c1d007070070f40105800c2044101c0d0078130708054486c02c10304c8001c000c0500982038000000d00181b07221907588100e03003a00c0b4800d650345c41d4800c0d082003000c500400d01942c00150050b010385000201e1101c81d58603001201005c1e00320383e144c010080010000010f0b46d40f90200607000580c1c041c00081d1540d404281980c199180040c00b1480 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 795168884 1250 795167634 795167641
    0x1b080702210105070e1516030e12010603030f080f040c03230f01060f06050711040216050a060518070305060a023619060e041512060e070f03050304030308 68
    0x780260990780300d6001c28002c0010f410140806800c4020240040740101d0580c21b04400607041c44041d14440c005998071f4201c0c0510950b0100e40e403031415001690312401140151300402000d10070701300914401d8032041c400007100b0801070a1000020076414035071030101c1c10080020602e0319802c0461b075000c1201f1403180c100e10b410350501c3c44585006c44203485048041940e5010540150046078240030030240541c1d200c2e541294140302e124000b502c01c030b958030604d90841c18564002c1140c0070000d07010382506035495860034200520200e05032002d41d00d034010300100c0749444c80e030a82e0205543c8010418681b07199602500c0b0030b00105480c4103035030302141c1f407805948000c48801051406101c1c0d401c1c1c014507407c0001206820070f052034040d50350045903c0d1440e400094000c1603e10741e40381c00305600c0c0c2041c2040f02030700c007a00c81124408080e540006408404080c600c0b01c0c00e100c0d1102080c03072881064030346d14020840d8031240c200c01400e0010004180d011007124240c07a01850802980e98 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 795170134 1250 795168884 795168919
    0x1206121a040203250509070206010806130f1406040611040609142e170c090f0409050709020702091006080705030912030103140d0f05040b0706091a071b080702 70
    0x101d510700c83d90381c551081d491032100840001c07040b0585504407140c10091f1242c03038040b0381e140024060407030340354800302c0401c420011503010849018480c60204070580081d030b803041140e2100307814028065000e8000c0c041040042d00409110404204e0300e0750405103003240003001c10015100326208800c07564480e16054480240d0301030706030010b031150741c038400346446600582469a100e0b24005418080e9103d44550030190302c40c01000400e1400303060000c4842005221840c0c00d0390079038030030340d6881210000794042c490000101022107005803070b0500c90051080c900d100800d00b0080105201e002d01840f0382280311a90000751603e013860301d9641d8861010310b0f090481d29a819000c02c080000803c11258640d1a100d00c21054142e58948140310000e584980c4400c41c100003040040c4401e2000040c4003001d44141805800049082c0c2465100d5000b462a01c000300f014440405040254550300003490a264a009032442c002c40740c2580c8510b00700303000780140240304251040e0054040b1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 795171384 1250 795170134 795170143
    0x40b04060806070e1003061406030712060806010906050603010b04060c0213140a0c0f0c0b0702010f090609110117060d03050c03031303140901140307020102040f061206121a040203 79
    0x20700c8840129591030030704800240840300124045840341700c284039a0026540f190003024211900c401113140e0000440080005541000301150204180c0c0031200001c4071076402224002c1c048035003e00800d504103008002550090b03004207001e85002c000412030702d0800c504850481c0c3d0301d840e100c0d820300c1451000600d8a241c1480304110030f03040020780707100b507804082c010340601e281000400203800212400e60303108c80310700b8075440404c00b07048041001c2540a8050f50b07000115100000703020104400e5801103540e000415181d15a6034160f140810400004030066041d09003404180c080201c201d440000c54014a218041d0210850000806000340162200c020043d001d481c0c882c60007012030302e0391100340c00c41074000a0404842225207034000302100c40892060796041d24134014500032400d01d030300143c941011590308120010342d419428007410007502281c1c0d220000324501042c00c8040c3c0c0c0707560700701101043c4c8014480c80014800c843e8400100c00f640300596450341d6600000c0d050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 795172634 1250 795171384 795171389
    0x3180a030504050112110d0507030e0a08130e061c1106120a1515031a10110601090c05090f01020c04060b1e0309070302091003060c08180d0e040b0406 66
    0x184a81600001019003140151040d20300c04e907181100081a07107011015a85003100c410b04d12001081100320a001d81d4100551201072341c2400f160341a000d01d84e043c03520000c618159040000400c94500400500700030600405048072104040d0400708002405620000701c180207171254902040200b21b1540c0f840c40ca0038800070159511441c03d24401c00c014a003c454554109203401407880068141c0300d41c1c201510154002800b410a603240140c0c014914851040114a10b200010140c1d0b5100c0b11424a604004d6607503015500702840368a00e131441c103811069040d810180314500d01035010094600240c001c8541ca80060b4880c0010b0f803e1903c824105038100381030480205514142d20000e02c0383c660360100b00031203001029206a95400152011001d58101040230005454a00b015030f40282e0340c02140c8440b10b589a80b254110303251761448001045003a0104005ea05460804881c42d101d00400b815102c410594001c15090981b0f0156103d15075801250485c0c0c2c5071540310703201 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 795173884 1250 795172634 795172681
    0xe0403020a1a0106022415030c090c0a08010e04020306060d030e0a091d06190b0111100b010809030c060a020f31052409180a05040209130c0b03 63
    0x250380c80308840882c044109000e0640076220710151840d00c000c3c0c1e54082d00b00340701060885070b1262901c60000c06480c2c1c880d240c0c19818070034043e074003505503079003007500b80554400b42c45a0b0b942c281e0600040d142c03200581c0301501412a0300100000760700c01203003031948000c0488054543e80b9892030250364010030300d00000d802c000fa03170380086060205980600304800c8446044408083c00e0403145996a004031500c40e21466036000740070070078103140c02507825520141003402c001c400c2074407150314120300c22041039403042d210314001040e03507009202140c0201020010314a8880500d0b21980d40d00e1029080d486210360010748614010908007e80b80d40d80e094805800028141c2211040c011081121b18182400000e42c001031a00d005103442070203050280c8181c2e04050a01c8598400d604500c04075500000c26030b8502070600010300c600d512640d14048005002e04050040c4000c80d04010284551070703290641c24404100c844a03804126040c504d1000c0c2d995072480646039100441e07202910 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 795175134 1250 795173884 795173903
    0x5130b15041d0607081b18181018060803070b07140c010204090b01050a0207031202070f0b031902180d1104020c0f10150302040507140313050f0105100e0403020a 71
    0xa01090011030128040c41d219a1024456211030742c5107003104600006e0010072060402050400d5810350040c0700c2170450040c0503113110346420030382c1c41041e0310441c2e8078111401c40c007800b402800c851044450502030703100410803010341000c0c4015a248110030000d1b108400610001e48514482d6615114201e401c0c20001d0701c8a0203800c0c481c2c00b0f5001800b86a110358108407a203802544502c06442d01c440d0164020301c54a49140c40d00c02910b0340000c501000c41c0107000000c01c0701041903c8030002030202c0e004959030780c03501c60400d003500c442c10042e0080312401000301d204060060f1441010000c01101e0100d008a51490001c800e144d001108540240c000b0485e40801c0801240f07a2203444041002e841800412640740d50884240b02e000d40380091001c64240007500346607000b03036030045150420140c000d43e2500341c203415030011616001c584082051800400030180603642100d07008400912550400d00f6071250215628012006442c490b0000142858400c105280b5915080080706 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 795176384 1250 795175134 795175181
    0x703080619080a060e0a0f0b0403030209030601060c0201110a020a090e010e150f13030206073e01060e220f0c140a06050a090506030c220905130b1504 66
    0x907500d070080190b051310b940740b80c07030300380f0404039004152280210b60001c402e100c10201959140b48407540907005a00301760342840103540da910100700503806030601d0340703a10440351000d10004103100311150145d0a90b1300319100341001620703007141d10f5040e00d0f0300043c0851482d8145802c0f07801841705070354000c014425801d48070000d690440010740101c60b00c420101056039500c2541c503042d06c0d4608002c0040c6d2019000481d55407207103070782c0f403c6ca070401c9510940b8072070030103e100380c0110704401044030001c04042c0b9810550007489050003d044411005190741384c6150508200c4090041d00340d40c1d080c0d100b408104210003003070074075116903020300380c0a140c41d10b07400c041e8118046001d01601a04200034042070060040d010707550101150307612501054142424080182c0020b03251400184080c040030a0030400c580300282c0d8a80c400310031140c04d900e084a40002c0d20005044111040c0603044001e0105e07502040b03140e032060410760240c1c040c010304004900280b044d200040c4810480b40d928 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 795177634 1250 795176384 795176399
    0x3010612060b06030702030307030f06080607120c1d0d020301020403140a123b1003020d0606030903082220030d030608071404021225050a050703080619 67
    0x4816125006040401608102c2824048144401d483c4100541e000348005440f09104c0e401001c0c040302010400b066440d03451205c1c43c50400d0645401c808605900203030000c0100f070340300d0042c2c1c2011505c0e2544107509201003410405004202c2c0d58090030300d406150040d500c094045500031507100d41c10304214a02c0c410110b44900001008440d11031940c1800c5039860312960f4162003c400080524002c04840640b01040d01041038220300d191051071158030040c1da404040406007000d68801681e1010224044401c03144560006802e00d4038005448001c2a0300c610307d43c0d0b10185c03408076168211545840d60541e910581c1001301148070210000d11085079600c41801c3c004021b8046032010702224205500352000c5000e441c240e0340c0300310ba080150305036689001b1b00304000903100526210380b080304e110709507108552504c150000308c5a2080c0344010315030300c01079521080c81d0080c00e003131005400811074802c41c0300160810011501090056841e0b54049001003900d2130f0700c81d00790b0303038480c035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 795178884 1250 795177634 795177659
    0x5070c0503061003150209092a16020108061c080a1817061506030a0c030209040f05010f0b0c07050f1801030b062b030f1704050c090108010e1f0209030106 68
    0x10880b1100c20a00c640b24001249000b5690f191030010480d010a9603104d02c1d02d0007200c1e1091031200000314540c202740000c203c550060a0340402c06841c0070031a0428000503280c1c041c0549042e02034039030500d849484501c007115400c02c095002c00100d81c0c0c0d2208a400311003c07440d07007802d0901c0d07030b60040300041c05092000082e1500c0350204140c035001d40d0380245001450300004519078204e0000c00014003440200ea100498491032402e005040c15448400301d011107602c113802d4002c0e0b035643c03070041c010b601c4884002001000603001140c50948120780207500c40e00c0c680304003405405241404010b030323522800e041046511142100c9030f04d607900d003800142200c0c02e8600c80d004003040301e11804118041c500400080011015040350004070742c1d022250281c2d03020121040040c0303040300d262410000d070506c0b8000d50007100106078403640070042001d00c03901a40042c402d42c1c075003039041050f44004680200074030341d00790a001c0b01040350514080a0f10a021010754194a440c1011a040d418400c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 795180134 1250 795178884 795178889
    0x1908040b060103020a2106170f461a041a071b030806010f020712020f0a050a080a02030c10170c0c1e0c06090d0609150920011e05070c05030610 63
    0x41e40000040c84060b100c0e41c1311040c0100c201d02d6500200e0000381d1050b12509903000e480c0312984181c00c10092400d402910030480280082441c0300d160800c0140702c4d0041c102c0400c000c000c0c0954020b403c14de99050f260759070141189a4032200000099000741c016042002040c881460031030110740c0343e150060000d0001c8600740c1c08510000b598140881c400640356041d94118008200003c2d02074080003450307c0b4810006034080700c0003034041201c0d1078603138580000344090b00041444946520415041c800d020b030300d06000c0c003548aa268200703030344145001103103c903a41911070140c4071b18503040340300e1141041c021120f00c500b4800d02185400c105190802100c41070603039042001020070410f5038424940c04540c88642015a10017059032503110b4410b4034400c1ca101000d0540383c4000d64107030750200c0820f030b40b5520b1a01c400c0403c003a0704903041440d0342091801c1d08a400310001842c005101e404a510104500030070984104085100c5090242c0002401c0b5a96807414941c00c5215000d1030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 795181384 1250 795180134 795180149
    0x5070e0a0e060d0609030e09070503010612110702030a05060103121409060a030e0d020d020f0601031a0a0e01110307120908180301060e010b071403030105090109090206070f081908040b060103020a2106 88
    0x5800276201e64455000e9034103842007951280031100d0704000c140040d082869200b40c0280d02009881e006070303400c02c400c01d0142e100f000580003961444c00c0c116101c507103062800c030500c44040989010801c1c2d100448810f07aa00325080c1e40c4406526004030000e05da0851030301610f2041d8111340018030b400003803a64241707510390300b00d800c00181741c100c0c9030302c5200a1100030500d8103400c042c0b400c00d010403001154003c000410020708001010445425200882c200001c8058004140800c0d280c5c0301588035110503a25009202a280c2507440500070f20451042c517014401c0da8000c9030465800303400c03400050901d8280d070a02540c452042c160b8075804120704803502800402c40821071038001c0292030403544024406000f03a803030301300324002401702c20004aa009400700030038000120313019946030405000715255502d82d0705500743d00000e02c9210032403006108001c010040003500949000d0b41c007000c2843c000d038503800404010340d89001c0308010180380440104030b001344501141e10000c1115503c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 795182634 1250 795181384 795181399
    0x1202011110111801110307030f0c0b010308030f06040b03060411060708040b1224090c070506070c030906020106030203061b0c030d0f0f0506060901030c0207080304170105070e0a0e060d0609030e 85
    0x890015540d801241c00c1700d8171150070070300180340400e0290460640700c002d5401c0c880c84200441d07803030841040090b0821118488044140000c6c2e010780090075601c40340590302003080107481c0001075070319900104020140240340041a9040c1c071040d0549481540c0011041d4035030340c48502108060b08249500645909c10500103050748900c85003401d0100283d003101071030401d114040c444900c100800a00c40804200030a030002401009440d03c1350105035141c118050591030b0092800f007859200d1002c6a0600c241400582d07808140700b500f04009040319601302990414090440c020115055000d0101180e0140c5841aa4101d40d00302501903004016010480d00c2c20341c01c40b10261081c54214005000f11517003940251b020700702036060b500445801d144c0e520001403035036006410451001c0006c143d81c44202c1d41c00d002d101c0e0840c24a0805005e070318203a4002c108807080910601181e06954000309a080d200d1f0400c1d03805154000e02c0c20300100c0700e81d0802900d811181c000c00e40c001c008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 795183884 1250 795182634 795182677
    0x605150d181e1b120b0105370b0a02150603012a17010f0302040e060105060724050703022206120b15121f120201111011 53
    0x1040c80c9400d481d81e1003000c07820000300341558500451582d04085810321500c00f00388400c0701d0148081c2009100f1113808080440d21441c0a000d1010306a000d44d000b042d0740b44002000da1551403681040440d0f40403200250000c1c05c003280c60350200340e0f02c21090800d0014144224690204000205500112814a4548032681818200c8d80c01403420b20100780c0300040f42c454002c05029010101c03107a49040b140d079240c0595107250141013070340900b050121082c410001c506250041404025145020748480d614140104080307102c1c0640041c980102c41d0784080da1010003014065140f1085101001103142450b00603000703500610324044480f480c03007540e0005064401e14081921015a250340721300e40c882d0300c00e8000d44101107049900c03a220302c154039001940d080140c861501d03c0302034018141400e4104280c12050442115041c106e40383c0d003402102c0300001c49a829070350a18062004000b541c0c105403d00707a02641f002c0c0454140706542604142d11030260000700d150515840314500d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 795185134 1250 795183884 795183911
    0x20d0c080d1d1309060c08061201020403020904260c0303010f090504020a090e101a09060a14151605160b07172b050a0b0603091509010605150d 63
    0x50400d6031155207408526602d6020f0405500020a2501680c4089028005552001c0a40d1120401080054106820069107150030215410703142c80c690300840c0f0741420741d004100b045030000c0019009500c0404550101c0ea0703c104207140b4101281c1d03940c0d0f100c07000742180d95220f50007849100181800d20a0210f12440300e4880e07640960750060207800d0040c40e10003000080e0122451040007802084c2d240701c441da940d030144002d039109090f5a6400e240304041003049440c80500414054180d500301404a4240c0310710034000d00100b190105109826041c01c44c603a41724509604e0304050840080c102042000508004006410070f0724204490312a4010106400f80c01001b6100e110003c5000210250803c010035204d943c2044809201100421a00010600e941c10190083c3e0f51020400c00890710302c180c56400070f04a814900d1828600803150b40e83c0c000d500c62220660f1500041694a41d0950168006050103050380380702001500c0c00b00040c3d004041c1c08461a030a00c00401d0300607 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 795186384 1250 795185134 795185147
    0x30c071e1505120c1c1e02070302060c0f2808090d0c0305251a090d140a170c04030b09010516080a0204031b03050d0c02090a0b030307020d0c080d 64
    0x101c140350748107070401940200603200500d010300b031146200c0c0300304640760200c202040518150128240b0201d429290720320040c800311144440c04540e64818000440001e501042c010380110b06a074019465076120205187c4500c03580301809180d442070042418603074248004101c0224107600c0303200303c5598808005441e02d030300081c0c20b4000f451081100002900400140c0745051203c580c000420917890304590300c41707040314001c0c1c40040d00c101404903c3c02040380c0d402d5100740820040d007070710200780c10064503074444e041104c0345886020680c250000d11074026031050811501184607e4280301c1c001e104550700500003a590381a5100001308100b0301405424020b201340d5150b00a0241c444034200c070700c00e00161003101d0b03c0c2e400304030020210ba414009159980a480f0369104001d2552510b5441c1030140f000c60000d00005128000159446100d4654030600a0201240d02001179002034118490154020f40c07292000c66103d00f440400350b2104140d84041c02120840707441d5040607182d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 795187634 1250 795186384 795186419
    0x3081008072105030f070213060513051324150e010e090f0303010303020d08150f06090406050306180f19060b120a0b161d0909030c071e 60
    0x59010080800862401c5501d8403020b00c1103442d0401c1e50050303aa103031070071a4040c0355070540410001c2100025423403d01111102803c40640c10001e0514120218800c1482c442040080305d581d200020b2400c0f05017045155010b60144c800c0c80d03603001071341284003010143e03a404004107107810b4003000d640810008400580f0b00c02c444107041c2da0718114030100024001400200d944c003440e444804120810009075010b14070a070003800b80384803900402411400e00030288030002042c44818080c54503035601000c612001561525650840c0c0404140540600d0340546d0b01440366108000441c001e46455800195004040d258a0351760645a6940e820208400324800483c1600840000d03403198402803500e100a0062660007500d0764915060030480038055074540107050800c810044581c080012402c4141400110100d00017640c0540111b000e60032070081032100007040c0d1500c0100162031610b4403050464401c60703214000034048440f103080781c00444500c2100450f110701e84000c0c1011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 795188884 1250 795187634 795187649
    0xa0f060e010302090c0c161e140d060b0604030f12020111031911071212020a0225051519020312060f010c020301050a06050a050301200a120501090603030810 69
    0xc580d003560200040390202070a0005490f02c00c01000301034410078008494075078280c0005e044180c1c40c00d10003c08440700760f0383d06240740d0f1104006000780c0b8265078100903c5801910750780c4080195103007240c020074034400d085601c41c3c0041000410001e045566000e0a03124980c2d29502e240746440c280c0c241c96461042e910071050a10000303041910020282c22a200c030079a020840241140c0585965030120303500751620402d200246410a810402c28401d00c000703100c04500c0c01c000f5420081d155650501040b402c02d980c8030341082c0340e030300c80c800c0c0401800b8010a580c48075128440910b4090340580b010f90500f500d03071055503000768000f10030b80d4804400300d50301c03000c20742d01c002c00c010241c001c0f44811b074103002c2100b0508002d62001d00c02c3d684100100381d00052030b182040108000310802da4010741c801d80c1805214584154050741c1c0ca1200c00018031096210050034005650005480f000000c845140038000034404000f5040720301280d00075101e24866445012800b110300303901d400f91a4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 795190134 1250 795188884 795188909
    0x170f1203070905060d020d1e0b1f03020a050910030c1205012103021e061512030d0513080a090501080a0b030a020f13020301030b06010809071d0703140f0a0f06 70
    0x6410118024807041c0d90480c0018074200d0042c480c0b50403a101d11030008e405140c41880d0f2160700344184078800c03c10b030045071403e80c24140c0c0b0410002c49640c96251004054010580341072481c0a0700948580d072030010403210102d062100300074010024a003036270000400c0c2c851040c4511246204003410783c0c0060024401000d50380d80205c4025240440440843c80b03072881b02c440c90031500c04410041c000344030181130507040030120001000e8401c015544280361003d0350303180030900002254001c125241011a95039036840226008a00c5c030100500046400030784440d10302d40c0003045000341d80090325809040e45030500c490701140da0100c0041c0e010340c810400c51303000d85400c07200c0d0360525000a082c081840070001c50581a60000c1c1e10485201d0440c005001e05580c11414450380301c49034131b008000161134800107104444036088480b41d4a0402c0340895013040c420b03040412171400410382e1703040d01e0a180940e003030040800c9907000d075924600816482100c203a4001e140031a0300020691 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 795191384 1250 795190134 795190139
    0xc0307120c0c02090a140603030a0519020106051210060f0803070f0804090207061d0c0a0306050618160206060613090b0a030f030906021b0a1e170f12030709 69
    0x990060081c41e0307807481880928401e0b40300683d180c2000d640b26000032440840c0d03488001160a1000c1c0020300032501c030f60001d0002c0e54980e0760000039680c052000921401000120540580c01072049401c05034104942003196031f01d0900000c0c507860300001040007004441c0d9603108420340840140103070b0078990002c004100c00300b503282c0d048511071402000e0a03890240d4a0840c1c600700d0b80801411a1101d49544031001d0000c0d100e401c58501d149944050103003005100c000070451081404018625555900841d06c4d644840a044c9800c41c0e0b00094000141001c0000c1c816481d00100181c005206190000e800c0e404d200c0f0546442c86071190680802c00d0600a0302c4018020346400150400180100000440c074001d14100d0402c3c002c3e01d07030300403442c10a24024145204d00b255000c8141c4007090144250b103451828078106c4550f080c45447d5070340076070300b42d0610888036440010b030030030107007003405030b060001c1140b08207000301c0340899403c03825880404a482c04102c034008080350010804 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 795192634 1250 795191384 795191417
    0xc0c060106020a120c0606050a081501140a1a09040f06151707050c2409060a053d081e0f190c0f0f09050609090c060a020f060c120c0307 60
    0xc017800d4610032000800d00ea0388038404100e01403801d501007442c542c80503d0080d035074824a949540500b003415444003042c04c41d4070100d41d0240351417040d4107000540303401050503606e40d02d0540b05079450003001031010310388500b50340003d0700307160290080340e0100c94481c804080c090702c6150380c51619040c55107074564800c01c041d00c90b6008010b640c1e10707a00400412022106007005031b8080b0b885072001c1c1c89128101109903906e0b0042c0186031100383c514200c02d202c02503104502042c46545898104044620580f0b02035407100a0100a050f40260908011842d500082148a0b100c0c0e0710b000b10030300c0701c40050f4095035122440c0755814003940000c80c80c80006115011150b8000b03000d560070750382840d81c60000c0703584803009612a0100300c890003014401c00f5044c3c010641c1118003180d41d5142c0c1e0400e18000f03500d420040429500c91100003d9852040f030003408000d4000014200b900c480d89405964507680d584824040500102c0441c0010007506101042e03a000d118251b58895100001049 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 795193884 1250 795192634 795192647
    0x105071e020f0303010803070b090304030c090b010e0d0b06010206130209060906060403140f0118120305060a050a030b04060b060a080c09030313060f03061a120c070501050c0c060106020a12 83
    0x1035800c2140242006140780d02c030100002c0d4000c11424000b190b0705c0b207460904c1ea01e218005020700605800401040011400f100101030a82d10390303d1001a00e0030003100180d0702d0f1084032445503006500144c540003800000d9112600c5880c007a000d42d0107075590301e802c003550b003501600c0080d804120900401d00b10b042040312258403480c0508058542900c03915207403103540b0214106400781c0c1c040b0004403d000c03020f0041ca510344688041c00c100c00400c40d55951480400e80402201301a9140c3c0083c4403556202006802420050080100e403070322814142e100c020125001da8005007051107020490070008202c2c0c0c200080d607680c3c10402d40b1340581030100341c1d003d014010340c140b01c00d001801803c0c0850f0b403100300800454464841260054401505440043e84000c05050300c0608407100d02c890101128514680380020150595074205102d5041c0a2200003500c5586051700b08000603542070018599078403040103e68060f039845604070f80d50f2070a944014001e44a009140320035034060700 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 795195134 1250 795193884 795193937
    0x7120f0212090a1b050604060e1f090303031a030d0c1106190806090c0a180e010b040e090304060c140307140d0f020f072105060f060a08010507 63
    0x410140c903045a0081c120041003003620403001a4000c412001c0812201c03603550030510071804c0102e1002d03132030403000402d14019480f81109000c20440d2280351070707403501c412001c2100e1000c1810050007016200506100b101d0004a0200f841c28003a40405503103084400f0000c40c1c0200100088000800e04950706044104c00f101d10010020094107950b88040141104a5005c100c12841d92031081300140b0186014051600a207140001d01201300c0700c1008a420102450505854880c4060303001213010165501580101103840004984540303550000d0040f41d486900c00308060300c4881e0303c40d881e489140302d80000b0a0380000002c0008880d01c41407181001020250b900300b03503072901c0317900c1c6058203000c17030404542007184c0c421040341d04540000092103072880104500400791170704035a209082d01a14015904003e040d03600214514425036a4613031060a86100e0308254070f10f4000c2103002d64445100c2c210904001c107146405103d024400d0318196581d1f480c040c400f41100c6090500c85 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 795196384 1250 795195134 795195161
    0x24090f03051306020f070504380f09060108012c0a0203010524040603110415020606040e0d1d04090c080604030201112b020d09081308060105030709240314010507080712 74
    0x2700c580590412000d0f004403502c4819a001003850f40c01403040020030181e81f00c0e0309120f62803560910849036885650141501c102145181640b2074069200408814600e07403514220000c1c1e00304110308240303801a5040741ea040e1140c1750341c2c400c80001011024005d0f805a4031094051004214080c800c1d00006012440c00c0405c51400e5111020400c0205000740b40f03038050303480241070010900b494400e1411461404014140e41c4c1c090002c02454180a030011440c094440000e4500c1d0365250361101d804d0b00c0d440b542500001d0354950000781c40c0c1408a0741603016519101041850030300c02340845111610034114115a95400551046901e2006640382d142d16400e102070300c1c1801c414400d40c5003040c002c1c519552030340307001d8011391054092500013011581007580100401c1e1400103442c01641d10510001c00c100f000c500d240c54050070031002c1000e00c42d26542002007031040e10840d00541d512030000074040f40e42c841001390398403d0709403a414001010b41141040101c060342c004195807021 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 795197634 1250 795196384 795196421
    0x1202090f13020702030c090c09010c02060c01090c15090f0501080411040609020702040509120f0f0d1404060516080c07020102070906060801080f010924090f03051306020f070504 78
    0x500c4046a962a0803054000c152903002404100750b10702003007101c10b804012070700c0341924944070f141c004035400b8898121b41406506814501190f495400ba5510052400001c11481c0114248503000d11081d1188000002100651400003445085094142e80614107203049583c5040e00440702c1410013007040c1e541070010741500107140c0d9607001e504001c059524000d41c44100500403c811a04068054015030784071075101d21400340c1130030030307120003950b00340303155844640c118021890f81c8103000c04603011034a407500506590016040481c06103004400c10000da665102d582081c4583d114164004603a0b00780c000785200081c40000c043ca20303c1071040d40e0050f81c0c0d070500102903a110fa04084c020032150307401488580b008005035542801010003d00506140340c84101d01d00824602d075659a500003558041d140590307401c6504055443b0030040c4555103141030040c12900200c4c40302c040095501000614180300064120120681c43d003d0500710380781c002000020101da00041200c0e588 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 795198884 1250 795197634 795197659
    0xb070221030c0708071a09090f07110102030f071e0804120212040e1609030b130f0212010506030c190e09011103150436030212180a15120209 62
    0x24040b0340d00070401e000080c80c9580c14111003540c0d01b0400200781c040d9a00030321000781c00742e6500c00b00c6a0898807102c071102c10351711001d204943c032800c803141da1043d640c00002406a400850203826201c0d6880d82c3d14800766800c0c094402d00060011100d0b00b0000b25808042408102c0942500c68088800e00403264100d2480d080c0190941140d40600d0f20302c9054020003400d10b074294900c24401e0000c1c0342a00c80141180d54030246408040c00c00c018081450380300008021803819207134103c6400030300340d0b880323907512545050107032504890040c06400380c041e50b41002c0c01c000554840c5121221614800c0c1418000c4499060340c0003801c000c041e64039400c1900d2030841d49401580581d0011030b260700c3c0000c0000510065900c036400c009014550728440480c2c00301000c5209500c0c00c1c10b11080f42c2910018242240f502100c01581c00e08200000b54094044141c0c5400c9400c00c401590403038a0181d80789980144038041c1079103135000c42c0d4001a020004407195000f040c024200410b803860264 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 795200134 1250 795198884 795198907
    0x210080f060105093a0303061a073305010b18120a0f08090d03111c1407020109050a090e1207021005030a06030c0e040b15060d0915150f0b07022103 65
    0x1c1160410b4000c680e84110500c0303024000402000500288105270b40b50907126500c4c4103008414a200f19451000302c0382d00d80403100c2c50814070403040c0c514007090000d540c41d050807541541c003010112110090059410000e4105424103060b41007444015089048454035000d20308444100c00b12401c86040111305646d61b142c04890040701d010f81e65400403240600e031400d11f0a440707071010071640107080c00c5103500d070381d4055450348078191440e00f00b90300e440540c070042e030f260030080d0080346c1c1c040701c000004a10202d55512401d0503050391003c580000d02004030400342489603001c065000035414000180c410700400c01582c018080300760020b1616500c1d203d0034004c21181e0041c0ea50385110000788000d2011615a280d080301a9171b0640e00b60074842d600280c5184511a10154500e4441600c00c003400900d0800c07040214145c00113204684d24029090000056405808944250000041005610181901d804550240000300d040c40511a15030040c1f84010010019100070804030701c502 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 795201384 1250 795200134 795200239
    0x1231605030c130503100504050d020606030604021201021c0b010210150905100801050405100e1903030e010b030f010b0910030305120c0c030a02010f060617010e060d0210080f06010509 81
    0x4041e034080082d0078105480c0544c1042130f402b50850031548070a00b4410241d8002c6001d5410560445c0e160300b52030ba60b04003450183c0a180c06081e54592001c00c03040c19100190845541910242d0907200c615144442030746c00c0715480c91070403114020b00b800070301400c0c01c540d00c00c0b908140b40c5c8040000703e95584002d2400d60f0340440c1c003140d80c0e403c981c20292410200f802a4002c030f4480e84060600d90540840c00d103000c91404101030704050300e40840c80c0d1505000e6010b034000c55005800c0c5ca8081d01d01d10450340c040c0984420240c0070340e01c402c0001d1a00a071021052050700d5155581c1032800441075003400071201d0240c104000d803241044501d132000000c03c024002551a90000f061003119403019a0031036009511100a2200c200030380c0700306030117180c109419601110901c0949490b02008038000b40d400b00f8000390080714600c0044109a000f21100303100e0040781c0c1000850750b4400004440a004401e01c2a411a0304c001e078143e90008000c0008490030070f42d081381210901c00f0003a80c041c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 795202634 1250 795201384 795201403
    0xb0a0903080726030405030d110c0f0a0b0108010501451b02010203130204090f05030406050409060503030702060703080613180506011d13050f01231605030c130503 72
    0x543d01e184000750b0703015800c44031600300c00741445109411858661a8103440748665900e80c6402c42c3d0300c0d0800400e10785103900340c13515841c00004443c042c00070180c59aa940c12000c00a440c000782c01000040c100105004088c1a1843d42c5285460520300701d4048000350042c03040d1000300841009a2030b054844445846503c400580001c01d4205143c000c01c185820301c4c68041046900400c10800410840268016580d50555001401e1240c0d420003980d502e1017540020010300002400007000e56020019005858800c50300304406a41c68040540c0d03482200c02c0250420300901c009804207004803021075120001914a04164504034110700407100c400fa0640c02511001d11400d00b13124003000054090413005030611148050740034036a000030310081201c0b00c0c0b50030105000c01007200a00c000400514104000d04c1500310f481407140d14070038402c4c210103e160b154000110005101c01e0740e085410099180c080c51600c901c3c403d144140d01c003040c1020368040080f0001025103080003052017 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 795203884 1250 795202634 795202643
    0x1021614360412110c0d0203031b030903060702070608010e09100f06140409020619120507080a0506060720040204180c03060b0708042601020a02010b01020f010c090b0a09030807 78
    0x605141c58a803003403041c3c240b02c1041c020040018039030078942c02d0025410002d0042159051030320001031000034a1031041071210580c40c80103118a2a11200020152210841c11016583d2907514108101e075260340c548195000140c813103004000100c002121680c0064043d404c0d40d01e0a51460706d01c1c41501e05607000141a56610381e0f04000d19100002d00786a01802150240150b2250b60009022030040d41070b41c60584c40019038510465015030440e400243e0070b00c03024462071816500c080c1c2a1001220007582c96410640080e00754500760040395459a80a105007080041c5c1340c40190381080e0100c2060b0b08a507080101107106080d882c8428140041104041507a070903e0f40000c0c1940c4895001d00103520040c40b51400181c40b1006032002ea50b11992510b04100400d80b41110315849000c00210551000030070b20f05042c1e064020f201d030b5450a80885421903d145809422142c145461030001403d030801404440a2000140302240341864140c1d41a03440f5101e0740c44652058034220b9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 795205134 1250 795203884 795203989
    0x31802040525030c0818190303290d030c05070503190c170a20040e010903021b1c05030d020a020d08100b19091e0501021614 55
    0x510310401100d000c1c2c2c52101900c0c06100c94076000d68042c02e0080d015203042000c00000c90001e44c111b108201c5280070310542850300720586400c0c00c020303000340f84840050000c502a11003071904400c01c64102d24200d0400740072000e1064064404035060701c80181c046600f4018940d00007583c0c0c1d400c0103021841904a00d4004100ba41440c10400d605016444150900e540350501202440003042842c030090b00403811503c00c001504107003500d0813296880c0341e0b01624140103000d0690701548003070300140c0b003034086030600344070350b80030000c80200c0c00c10701548040b001d1186d501d42c0340d0122658400d5032054080ba81807010105940060340c022000040040e40600c0309014042e9000745001e400c603400c2c02c0607405080c1007009040c21031080d04000002c82d10209a46001284100300910041180e055001d0100e88d02c2072440708542c1151103818018890910017120540d080304410084603c0d009021010280c03c20900031313843e00c021042002d001307000074120300400c141b1480b07105c075509104002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 795206384 1250 795205134 795205171
    0x9011506110642060403150b03150a0c020307050a08090109060c030c030305070c060911240d0c050f040806191506080c0f0f04030606081504030318020405 68
    0x20700c0c0880081000312440c1a464141d0841e0350304000211054800700e0f0005229004620121038422400a042d5004000010000203000744000c1c10200d66002c0f40c3e080c013241c485a000c03d42c4c0c3e45007021071490008401c001164603600d059012000d02850342c0140c03405e2850b140c603071a003032000411055403070301da000410004960340007207588060702803403c0002c8548007a880003804050a030344000c0525580758080350707100c0c0c0160080c051695100f001445602c0c2c5500e440501300101009460180001404210840c0404d014a6101e44846c0c03200c42d0500c03000000e460064078030700b1440d00c20703c0020041c46400000500041000e40615401814103050001c2100712041629001c01249844d0552a140c0401b056240c1800c4640034070f820340c0607480703c0e144102503200703032114104002000901c1c004140342c100085d000b00d900482c01001100e03034810400751503c0d45142d00086611191000400090003a441880c041c1d034841903e210240c0540e010504440b01074811302c06485a42070352 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 795207634 1250 795206384 795206417
    0xc210a060908040306050c0c0a0f0c0312170603010e0a02060f161212020901050304060c090f0834030308040c17032703190521041d0c09060309011506 66
    0x1b0a604909030003c1140b40c04140041a41c5a00620100403e91b6452044070030901004c203240c500a1600241e40d880010f0030704d134010300a800070790380701004419840300049c4185010710036121000c0440c1d025209040e1980d0800050f9031100d1160140424240440801d025000c007d401030a40700d81c1003114500120140038106c8000c00e0035134007100380100b210079600d99001c02569046944610082040b60003010103450405107500b03d1007482c01e445500003070029000512614483c140007000280d41d9099480e131035441c1c15425208180c92810100700300107885a080c055109020b42240e0703007451349603c403040c540300300000b004201d98400300f508144040c0d100c7d800090704a03c0c40d10b40e40c04030400001300352a00e24500325055410640c00355001407140901c0080c1038800014031144101000001c1c1c08040c1d0042d028a000d1154a0b4500c01400052400c0040c0030307a561104040c100000034041090f590b0000301741e02043d5481d55400b20396000c1101e01400070780741e56103c203c10404032403003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 795208884 1250 795207634 795207641
    0x50411121924051c060f0605060309010204140f0d03050c0f070306090302010c080402031c0525030906110c10030e07030b1b090906100507120206040c080c210a060908040306 76
    0x80f502c100c654155414815003080420410550300840c0440c1040032150001e004202a622864224100204000441c2c00650017402960001c0c202d08400d40c1040f002c0c0178409500100743d5402030502501c07580860300a034064902d41c51034208407031844900400301820b0014551048880b0368403a100300c0101a028001c0203507130601c6140000803441c0a80000c3d940e161100c515490881c92444c500008601c220200c1c0c0c022007401e11080c020010324807850710418403015066000620b003801c0455004c0c401e58118640384410801407520300c00542c200590030050720329480915588044010620f0010b020f220015402904510514074080030780b0b01e8815060f00a05e401400c0030442d12010f0769a0310306098101000761001100c0c2d5002941c1542c80340303e1250050504840c0e00c00032a00b09900203011445180700d20010003000f592a00e045070b80c0d1a0007480c441c0d002c3c426041070005030894103004046040d00c0c0b0120340a58009843e510b00300c0744440c074161100e090006050003405514003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 795210134 1250 795208884 795208889
    0xf0b0a0801080a1218030b040f05071a032d0910150503060a020703050c06190f0b0d030c0201050d0e010207021503070801211e0507050411121924 64
    0x103001c0080c0a55140e0050300704c0d440c40c007018003500c02103c98486100c00d030700e1406558007850700c07107841c1800c0c18049100c20030581c00704d901c1c0c4038101c4041100300d00d03042c42917081e0b003c1800c102c0c115280c0807800046c0a41c0c0504e40a0140d542c0b01c4442c140c2c0c4540001140100c2d0341101400e06240784610302801d0320350180404040b0844414100880c3c0c9000030003d500c940340050040e11103429280444a6104031498440d8030f01c03801c404e0020b07400c245200e603100064994010800381d05d80303420000a49000d000d40550040d80d5140d030901090160064280d81441450802d00c1c110070030040408480c42101e240003507030340c0400c0b10004c50920500c0341000442440e0401d05518182c1c0d80103200401c14029040c048248030041c010f069040c0700004104c2d940710440b100007200c42408000d000b148448140d485115545002480d03003801c0c0b00f109041f20301c41c4034603894004100d01c440782c044006402c00740941c2c0d00300200c00c4105081c1c070030b95403524004440300c0d801d00e080208490344807480781c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 795211384 1250 795210134 795210149
    0xa0c02100e041a010f081815010603050a1802010807020c09010602070e0c04032f0d0b04260a20150f1806010311120d0e0a0603061409100f0b0a0801 65
    0x12110b80b459030381050f445901c030034983c945120580d4030a0f85007100b5101c50707c60324040c2c2c0b0507150311501000400361141d05a4416036004c000c96900d250682c8180c800c0381c402201805104400d01c0c000d548600100d507882007050049880600c0742002180c0c20103400d901480040e0400304080c4180030000b000541c0000010948609080c1140c4600b41c0400400c0b401060880c003428a5000c8a5801000110b40c520300800d240300e40c030402e08148000c000100c6080b154405041030042c1401c6102c22001c07090411007281c5030410380c18000a40d600911802c25030142d47d000f072181d080a8000300514480c011141903d8015400d105860b00f418101c09001d92480403000c1c010b500080b6400554517046a41090862601340006000f1607030b50024490740e0880c500800360309030344480d080150f0182d2100c0503a45080003c0c0d0b140d0040f0100ca4142c0907000d220b040035141401e962420412242c2c0281210070500c1e070840d40c0e069680b40e90b0740da0fa07000402c0d40e180850803012480c0c00c01d00312801094803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 795212634 1250 795211384 795211421
    0x2040f0e06060313050a0506041a0604020c06061314160e0111060c0a050f030a1e020705150604020c2505010815010f0e040e03120601180b0a0c02100e04 67
    0x40380000d00901004000000482a80c0078400c05e02c0420810386003a036400c1425a01c207400e0074140080a12840d904091405152102140d001d0405100700c3e0030200c0c0c00006403070140c5448081102c0e0520b041010f60002c0d46904512410004c11500b1500401c8200842a586032504d040038090490354400c40e810711400c4605005080004950664043c41e101d05080d0755401154003901c00c0d00600081101c651808000c01807030b04202c1e0b0000354101084410b80e96000d84240b440d100380d1041280042c5103400420041d101040410384060300410000c20142c00d10b4078148100d40390682041d00204c0d80341003000c0022104c6a80c0d498000600700c00c1c82d000f000c40c50140c1c841d0883c03201500d03015040201944213134075020b20880b910a00800d005200f400640c003442600369803030f00b00248080e100c10061020075460b46c01805210320384c0c103a07555183c2521b031800e00024840c0e0040c20548052024404c0b1319401070b1384021a02d480c03012191200c0c0001400c807000d110449a984641c1410200c2d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 795213884 1250 795212634 795212641
    0x4060c110709020d0f0b09040b0c070c03060b03070b0c07060e0a05090403080708060d0b01030f14010e0f0f2e0204050d0c09050601030608031b01060f030b16021b010c0501150902040f0e 81
    0x40300c41307c0b950b000c1c1e0002d40b2440780ba15101000c4000e48074001001c1e0980841203804020441c0907003220140c0c5000f141115205911381e2000580780c4114185010717198090241000264051010342880f9600100b0000c101c69669010a10620003100c00f1000600035100b04065941c01082c5113420440030303600d803414101c0c0b550b104801000d045c0030203402140d11080440401c032442e800007203000907140084c000a2850b04803660341e12400107148040c1d005000d00c40c008917100150721158400c5803000da125980c81d02500f100402c448080c0c07202890b80801c80070a10b0f845031504100e800e8452181c03170401134544400d400031203401400c0d036810107052030300400c101c0e9000401d60b010703c0c001003081c898144020303080900401c0c0c00d5001040d414800381e400011b102c64840807030321502100780d0b901d016103c2400101c1e1108020404401c01260300c3e240b00300d50b5446170512041441c41403000042d00040482209601d108540c44940105d4001405012801e112030160006122000c0982c0d810308 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 795215134 1250 795213884 795213889
    0x90c0403020a18020d0e21030411010e030f030a020303010312030e0705060c15040f110907020a0f08121008070506040308040b0c190602090102150f04060c110709020d0f0b 75
    0x2c1d010320601c1e20a040369042280840c6180e4100d41403041001c0c81000600121401291108a1110040c1d4000394401025115000c507104503803040707902c00b0f041d15060402c1001500c02ca8000441e058052244450140c2d522904100412078442d168006544035071440ca0040c01030a80d038200c082c20035041000c1c9455140c000590a4213031001150a07940318900803421501c0c003546600002040039110040c00140004110500b003094092084188056604400d10103410820340710700c2c005920001130fa50120f44260b44e0303440e145104400243ca0720540c03455005c0084010340300401000b00c40081008081c100b04000740003003100b07454443c101407554a440c400d502842c0300d40180c0c030000090f101028041440700700c3c0e46840070107d5401655150504030000e4010b20701480c090b1240b540c144e00c4c0c600c40500d4680c4142c0c10501e2103403560703589a5a01c0098540c9403020824080841c807941d010460500c005009881d001c1c10040c2c643c2e10400180341a10040040b1a100d50f181480018054 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 795216384 1250 795215134 795215149
    0x1d1003030f210c0306030c0e01031a070e1512070212070312090c120b010501140708160b0a0f05060d080a050f071a0901050a051501200703030e090c040302 68
    0x101030034240222030550344506442c00c219403400c03690707406141c1110300210b035815034030050075a4004c6104182c0207850b020812030f0b2180030302010b045a03407146400901441c40820385a4410002e00e4022000075904000c2a14603a0300d070f40350302840102065010f0344400e0b0f807054070b42c4040288005d05203c0040c101c03030402c9114245000d0704101c00c01440200700807458011212065218642504141c5c1d10002054503081024045a10600312800040c05610a036444000303100038880251030112280e0b00d0fa0f545078400d402c039500500c00c480c290400320b00d28400e0b46114040c501030100d000780c4002c598004035030005100c00c3c407444056009130b002c01c9070744041d5100102c40d4148607544103035900254105000751040140050f2000765191114100b44480a000d814550300070301c902d81301d1644c0e072401c0d83c0c8204c17821031103200703040704040c0e0a6208084c00480544451100c49409402d15140c504118068000b83c010440514066603207042c0f02c000180e000c40c00c0004c240c14203041da0b0008111 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 795217634 1250 795216384 795216407
    0x6040c080c0a02030f032802070b24090411031e070302090907080f0d0e220209061e07021503041505100b0a0c0b010512060f090a0203071d100303 64
    0x1840482d219000900810846a0034403078282266201c0ca8040c92500700c8180301803109000034104040c403070340c010003802030707401c2c05600c50a40c80195a8104810b40030b41c2d541e98209840707000c0307041130b0002500c03590580c9001c2c5000b1400b02c0c4020350224245440c1c0540d026101c104080c020080062001c000700e50755003500c1d8111464111070325030301e841c2407070241690030140381070007120390501d50b00b80c0004091003112034a80340c40c0740d44642882000b810080c4c0c00030745c19058040d041781c071603040318550082a003110010141410f00003c90000c100c02d14103050b21120714080041d0100562030312400c003205041903c1c80162840c900341c0e4070384102c4000241e02007001078880012541145c50a064000544514460141c403819540e40003010740d45840015503041031400001714003800c002802016506091005004030317280c1218035110312600138442c451038080d1350b036508010f81d42440f03088001c02e100448280640740c100c420301b45240d405041601c500038081001c1000a4100502c54613 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 795218884 1250 795217634 795217651
    0x3030f03060109051005030a0c090602100e2404020a05151602030109140d030e060c0f0c16030507090c0206060907081003020604061112090904120516030302030f06040c08 75
    0x100e94940100603182c003950354100700d034000e2407a03c03010412a4040d01540c4610a402000d00058180042c01c0d640d0010b14007403130300140c05c134401d044420700484e00300203800030f0840201c8200d20b11100b03445d18114080003840c0f40e560010000d0000794a0032051580242500712141d4003040b01400726001d1030702c2a050800d4040001c0740300b00056650a50000326440c0e0004050000d009003805a1503c46480000c402c0c04a4038015041181c10300c000b400a21800070410810311700851206060b040b03401154240c03032144030701c000c018040700c1d6504c1280e00451244000b003d015050841642c2070303540f00300e01c1c0c04c115808081086600e0ba2074910b000c0e040989400c0c1741c00745448002c101c089160540d00041d400c48000030b0002140c59202c0c0304110100d204505492144184180d207092600c01d0810080d032218625002c100850040311131492840321a0070800d180040c0402101443d034103550b0107030302082d030100400808201441405501645c102c90800a0b03a081c1e0700b02606004010305600d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 795220134 1250 795218884 795218887
    0x80c150306030d110307170703030f0b0a1e0510090e0702120306040905030909070f0e0901030819050c0d0203120a2c030f0d0507020f0a080a030504032109110f03030f 73
    0x71300021306000320b0f950103421801c5401040304540030f00255500030f80341100003900e00b10080802d500140b2413401c40b144020059a40180b505020840b003004841403400c0701d0340c91240c0020550303541030106160508030b488030b80c00c0030300c1c002d0300c4000c82400030400c2095410000c00d501701c0340c01e048102c9521480840e0000b444a900e03051052450080e458444c0e004110702c024041c0c07480d000b0000b41c078840c0310307543c1d090382d01500c900c18044011000c0c800100741c0c100600c04014402e0b43c5c1c14084240c1034480c50420700380390308480d01c2c924040c0082a00e10141e00001120558103211554040d44140701700828001d0050180200420600c400e252081805030f002d0303020760480f02441100d080d0107000e25000d85600c0c80c0c81666000709429a4100058400e0501d03039056a00d011800c1c0c140290025200d43c100400380c04154044c00f0002c2007103041041c06646403442c1407079081160300039030020400050030744152501003081517030740e10218031441d056110005640e40010271956152511503189 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 795221384 1250 795220134 795220157
    0x50f011a0c120f041503060513060303021002180d2f010f0305071209110a0618030b09100e011e060b16080f04030302031c0203270a0c080c150306030d 66
    0x202c0500540d00850405c0035040d030291456a45900404103440046500705030160071310f025801118101c0c4401009a045024400d201d0040e03540a00f1404007412090400c40c01820000b4154154600003183d0b000c0c0d18010030450a201c1c0101d0502c0006028000c1810160180001c2c000b0044d05442c03000b015118030008001074841d9610030a8034a888030107105046982c5403c7c8981c10040b10740c40c0c00b907015107200142141c800c4c40e20450340d00311407004ca8461801c2d51511721440720000c01000561141070b140c4034203081c09128150583c66540f00001d101a5801c1c610074260540344002c4030b0180c201142070041e4500c841c100c44141066030f00c2c3c84010340c0c462500540b076002e54204443d1801006ca000001c0c50b1300413008107616820180740120007903560390b804049010540e00c00b6018081c43c00142e85000a11882e01c0e090304404003111f006031515900c0d11100d81e202d40100c6560340000c003645c3d00d2800c20501180e150b00c1000e10003401d514140003c03030f40d201c80c018454802c01503840c0e0003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 795222634 1250 795221384 795221407
    0x80c030a06180b040b0d02060f0c01181a090a03021002250506010503060c070f061d0129120319120609060e06060310090f0f050f011a0c12 61
    0x15000038451180100c1546201d450007074002d0480720a0f141c0260308101000f8030368070740505803043c0300d940209100c0c00d05420610300903141e0000610450385668032401c171f145000c0c0c40184043c1c828030507110030500e08aa00c07032440c25910040c21080066202c04940c0700026000b140781e10050a03001d01c0107880d142440080b81c40026420306440343c104c441c681103018803401041050503628243e048406984806644942138413518401600b400c03490310001000030300035002400600c08054108200696020b112030071070344010500f00041c00991101c0c0090817481003440500705040307a0207000c00b140400501d80307a1160f4511801c4c034208210429007014040c05e80b02d00c42c4800f525080102c1625011814020481e034001c0c402201e01c85400180c01e0b262542c00c90340300306034940201e034426103031541000140007030107495201151103e981b6250311a4610845209103810207000b04154981070280008822226190060303510400c0300255000b400500710700f0b411481040b80c0d90b0307040160b05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 795223884 1250 795222634 795222641
    0x130b100807031d0f0601061b031b0812190c0c11030a080d05090715021005060a12110f04020304121202040f2d081509030f0a120c030c080c030a 63
    0x32551861511043c2826082000107465440d850b4403108550490f6211502910b11207503a84108000113043e03481040041d104040c40b2030380d413983d56003202d4008043c0e524842e450300080803103103250000c035081001480c480c0d07111140c0d00c0c0c00341d83d0400100518000007460701d159040060003210300480c0d0201c5c940c80800403808195046500c150315031514500c6000985070036103003952240301e2031002040c400d400000258180041e5001419604122284030025140041c10603a0001c003114000a00c28503410b03078041c1052046003141174001c040810803401c03040c6030515078011441401008000340703c3e16409440030040c0e0501c2400800c1640c20040a8441d54005904030242c04000041036a0304048440d1400d4482d407130084046040c040c08904103007030b4820344096030321480b0000f1a469421103c01d80045051060301d1410b08000c40f000d9896010040802c001406144060342c2504503104540b540312243c541801030788500d460080000c0005006044a003100101084441001c0d07803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 795225134 1250 795223884 795223901
    0x9090e07031b090c020d0906110f0f0102071a0c16080904020a1110110f0c0703050105040309051804080304140f01050903030703111312030c081305130b10080703 71
    0x50038100c0e00081d0301030b0950760030b14801e40070103034144865600054008108090100403580d00c26610610705841101d80007050100680fa03401814881209481c0a021041126040400141e924034a62502044401050780018200036024042c400b006071520308440030001e0600c2d400c00070300c0341d50900c010b40c0d12408452560041c0700052000e072042e000340d00080c11030700e10001d48155920103080c0f41e06540a4a0900c10b000c5000c2061301000c030404000b814800461030f0483d004640c0b02c1c0d45550840c0c5003aa01030700801c0c01004d0406c03282c50119031414148054070000403103400c10f80c0d51403c480c0009040100480e200352082e82020304104548052209001c0c002d0100e41003101d1401d403241c0c000d1b1075450019042c4440001140000c0c411900b058610000640c4c1040c034103070790007a10040c1d1802c110101f00203010300c03d000c204001c01a09160b112003003032000e0300b40b03844100508403043c25150075219045c8240940507642d810f0f51004031030b100b4200032000d40c0e200310b1308600914028 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 795226384 1250 795225134 795225143
    0x702070b03100501030b040213030b070c0515090c030f0705040b01030209030312070206070504051f0519031521020d02061c05090606180a0c210e060a0c09090e0703 72
    0x10003000840400421842e04075202030301c1c1000704051190500050b072065014501d2251016403040000032085040264010814907003400000175565507141006861112520741d5142402803102c15481400440503d0b00c2c12401071004d03030a07441034103071208494800e43c0e10955039501500e025034000d0301156203a03480203041d81d644201012a04e212080c045d10302000500c030710400a855130b4014011101615401424036202803665101482600c0040c0018000c0007800d1001e00840c09190000706502003045d140816001442000701200044a910100703c58607880c606070200020b004041c1c0030340f501030351354a8040c840c03800400d40354840c072040c10304c1002e03124140766001c2c095036028034003d07055041601c40503265001009400d4001c081d200e5001c2c083c2001085581d146a40034a519240ca8100201040426444044100c281c083d00c000e200ea119000c010250740705100190780072920000801c01800114001081124180105032305150f03220007040801200308004030095600 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 795227634 1250 795226384 795226387
    0xa05010632131e060605030919150e0f0c100f23040f060e1005040b0703110d09090c0212030a0e010e0118121d06071a0901020a021605180702070b 64
    0x68a80c10380d20300d030980c1c06041c0390f2500c40041146881b90003140c2c002c2c1076601c020308810300503803a840d414003005e9030110345c4103e4819000b9801c0c496405401c00290300c401c00f43c215112490511030900c803000180b14450b200c0f40700410001500440c16104890b0b02d864042c04003c9030003150b2401700403200c881814448007080000700441620b0803582901c0140d603035a0300480103e81805010070100c0240f8010443c103000038800440140090910140a0700c0c0c0906802402c4080340d0901e00e05075440c00003d2880c0c1000e010070f44a80c0114050030714148028803080281c0d01515000d404041c0014551607115621352013010425080041c000141070000c00044080304802c081c4000c107410101c2e01e1080c036450305409140a5000000c5c1c1c000c100b00c040525035421420000d0940c0000000c0360100d00c1002004044540c1100b201d118814100005039199640e0401a181c9400310b1142000a0310b142c80511103038492000180c19062034586464403611001800d0f42840925003014a03107800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 795228884 1250 795227634 795227651
    0x601050d110d0f1a04150f0b041a0703020703110a03141b19090f0f0c18051903170f0a020706030c0302040b2a010e0a0501063213 57
    0x1c000080c00070400018081029001000d1064155000c42003612603c440b185a01c100d207051a801484c03007107143d010000107090711440c0008000f07695810200e031801c2c001c207040c091010009803410038a00191034480c02d04003284e9009503030b02e4840c00300a05041e40c0741d07c84102c545441c0300036030103160300680e1140707600c2e400d551807903580b4030b140c20610030b80080e900c48036501d0500300030050082c002d240520086509200448021b081882400300d001e0f23903242e080050240c214861461901007564641d4980c16444409007001c43c10303908403e1180006501d00508004071084c880c0031654802c8452102e0342140819075424050340303c0750f03204c1d6a80098002e8900360b011612001303460b80c50f2810041d0615100003181280600c1c0103641e0045800c020318045d03584200c0c19044100101e2070f0a00040d420202c4984c00d642040501c501a6484043c01504102c42806100b02a01300c4c0122500000a880807425064124545200f00315401d0700c03494080c1d45410040b030614080c800000e220816 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 795230134 1250 795228884 795228911
    0x2040e010e0d21020a02070b130e0f190b030703060e03040503060f010617070e0d020a0b041d160c0b0a11030c030421050a1d12010605030f0d0203120601050d 69
    0x20030b620342101c0303924142003d940c0704498401d403201445c0c1940140765180c140741a40c074003641305400b018030030401a40000341e941400f9201901c61014542ca900c1641400904108003034002d00c84403c01a081c0b19040846860019403102204d4100e0000f2034202c0740d40010703034110310440d0005500b6000d46000c100540b802c1500450403038903079a07580e141c3c40b039005207040c225140542c1c031480080c03220700c008009481c00c80c020310041c3d400101400003140e943c1d25aa021580f0950015940d00300c040300c0000c0e840303640d4486542c04442403c40b159840000c003c01040d4032488003004000396a18000b0613a4140c483d4002110f0522071000381d07a0300e050891503104550800c4404032064072250715581c42c0103100544041360140d240d1169418074030468002d488800f4458103511021807012003a0044d80e81d604000d00d0b5400e08400000744140c01d150905081481c03035440340c12640d001c40c4203c10001e9000040310f04c1034580442940160b00c4c0c240040341e46110707101040c481d0504101460640c803 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 795231384 1250 795230134 795230147
    0x20d15060f0e011e02031e0301291b060a0b01090806010501030203040821221203021e0301030c060f0807120c090e07090e18100e01060308070c03020102070501030905060402040e010e0d 81
    0x10100050071f83c45c00d803000c2c00d400140d10090040f442c100030600c0702e000c2003640b1806248240c02c203184003241010600b640090080080c444200d02d654801014001d040c445031103030f00400e600a28101601303d0a10140b0b41d65003d061003200d04040e80000010144042c900984501050075110009501d10880c2c48400b40b503c2500c02c40b01c01d8003285008002d40074121040003440b54801800824036100d400d0a030001e400051a00c0320381c1c1d1f64107104000800709a0300440c0a94410303944503c02e54208079009100c150030101d0395090045d11800c2c0004150424103000c01c2114218001c0386440490701c0850303a07180150b100942c1480340d00140079039180c20a04203020340d0303d00c030114940c0c3e0303031101d4101c03a00360f20042c140901604401c1c400038050b4002d0b006821401d020790000314074103540765075080a65203c40f40903181088201c006008569040c08050014030007441d007030180e90880c1c2c494507201e00014000911070343d501c2b4001c0444030350a4005600021003942940d1100c0c1c518000078105 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 795232634 1250 795231384 795231397
    0x3080c03040f1d0a051f030c08010c1418030a0b070509040509071203030216120903050c03060105060906160c0b1c050405060f0c0418020d15060f0e011e0203 69
    0x300d120110129141002d0541c8450030f00d02c8500100140d1590b40c0200002d0001038540702003041d0f148001c400308281d51b45205e0045219900d444841440c100e10305084030024500c20b130401014035411086d10000c0c4054400c00c500391000d40010322850700002c1d24102c03100d280104010a02c200300800140c000c005800c1c03020003a2030902950365208512a00d40045004803440101c05c00c10800104e8030a60180c41e9801c419680c4905418054450708400140d04075444002030300c1c18401d01c200b00c018441d003064208c0540060081d54140800191a40290901c41d8090240032540b01841d5140c6510320700e40340d80000501e646141c0302d01d0520401c0e4000840e400c5000140044c08520400c24410244520b4000c0048c0c03641d919620008100190090420505544140300c082a40c0ca100c810302660803004000040c0c2d079a00c2c2203046410350300c00240e0005418418601000180d4000d0000e00002403149003020300e808a01c0c1c0140d0700f5003548145007081900300406001d460b500040240300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 795233884 1250 795232634 795232649
    0x7030201110a052a030114011a13032a0e0a02070305190f02011419110c010f0506041407020a0305030901060b0d05010501201504020d151a1503010e060a03080c0304 72
    0x44c02503484050501784d070040c22103000183c066000401480039982d501c80b1364800c1541150349406888100444d0140d03080d002980c0b0907980150100c600c06902a080c6010b17a42640311208131460003282c0088054000e060b0380b1100e40011740481014070035411144450258040718120500030b0070001c04105d401c440c0c00d005507182896002c03064005980d02072050046851a00d02100c014042c100500060040070242080078401b08030381440030701500203600102c1000189900e03084e01004161b440c00c40203000703403000c00001e0008a036408140040d0380c0c5e0305403c1c038030313a681c480126107401451513500c412000c00c00460404d0f04901d01e9000903040381c0c4240e072041c141c1502e41c1204101603c514500105961103190f1041180b401001c078554000c1c0000c2442c82225890f0304e40f40303c020f00302155500c00315600d0551440200085002807603601040c2c072401c4100d89070103445c00c40340c07006001c2c0c02100040c0000042076950f8012805019681c4400c540784c403010408030562307480e01320340180310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 795235134 1250 795233884 795233953
    0x80a0510051e0114010905060f0c06012c0403110708010603060b10390807030305070503070e010e12030c031902030a0813060b03010204060f0806090907030201110a05 73
    0xb4101c18030112055502d50044010202d96440d0078850344407141648945810300031944800185643c03504044c0c400e0b000345000041ea9201e0a9001d181000b4058200a1055040e03d42c00b90020300d8440040700f101c028a0607107003183c3c860703080c08c0c1c51000107840940c540d84502d81c03011440100640000b003c580c07041c1800c1c07100e843c9200401c0038100360030708a1000510980030034103888503a0b24080400001840c4031543c4034820314580c0481c3e42c040039090f145a0130003d40207007015414440e50782d001400703281c8241141000380c0c00070861030b86120060304004440c031410304541e96140c1e088248500040c1102d0391070911450043e140e810415600c107455042c00281812503002108403101c080069840b44440d5407500b10720301d185241c0e4581a00c2103645c40311000442e40b402d20080020305525118184c8408026000418007140200040e00460b4410103100c8510400034580b02a01e5090810507500e10381507031400d01e0900c401d030002d00240304400d40541010008800c83c503010f5008090507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 795236384 1250 795235134 795235141
    0x60507050c030d1d0f090609070e19030312060b0405210a0b0412050f0f030c070c0e0a0b04060b070b06010c120f0f0c11090a06030b040c1e062106080a051005 69
    0x101c5d1010b170001a03650040310000c000780851500800603a448100c608281851499a00200326110060703060b2200034420020284241034105282c4c40400340c00d103000744161418280004140d0069100301ea00496500422a003400500d51256000d1549107007180e0340503082d81410704003003a058909a508aa0681b0010311142c031501c11a4400190081c0306440c080f040c0c21010314540c8020002040d68005008200c0012081c1400c3c00007031403814621201d40c01c0068102c0c0c02c80d47d00c44100c5204030300e010301c100041034405050b00c14482d0001500065681c0d03a80051b1031851000030010040034000600ea0700c103541084105550b41401d0b9100e2008607006407007030f038024a07645070250810280d00c0400c2e09514081e080e11703500040b031a1002c1419aa00e59480300d4000f0151000c0324039041e11041072000c0c03140c5090358000c1d07401203600700c01c038603140200140100d4081d81a08940888041c4094183c4c03030b40b5040240282503110448085c10414240152a8858448000c020383e04100c0071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 795237634 1250 795236384 795236389
    0x60501050a060503042d030c14031606230108030409050a0b01080f06060c03040305060f06030109120e0613030f03020609010510060c020a08011d07050904030801060507050c030d1d 79
    0x1000603202180c40f441d203151156210010707040b200002041c9201c0c02020240c081c0e401851070000f00500c01d4031110480d0b00d5a203050003a0070f410a000d0704030b540c801d00845401900c0944a8003403603822130400100305e02600c980460f5080c40940700012420040c0001880100c00001481280c030311101c01c0005403107100b03040d000e4981c5040d1040c0021100800b0800c0f0042d0012429081040248802d00d00454001c0440c2181c1143d40f0039a09900680c003000300500128012542c45801180200102c4041da40c7d80082c604e00302e580788040100c81d80040790a03440ea03d00325095020a10090680030b42d403498100311141200e0000c0303005020701c3e070105070034000c1405180d01900e401c600d412845e90500204448004102000717a07071080a810001440c0341c4284507045007540c0e004240034030998181e0304107203400f81c517911031030050b181d1000b0000440e40c08118035066407258a0400d54400c02800c2062902e20182600c82e850f014282d40f41100d141c0091020800c400000141c4080031084402c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 795238884 1250 795237634 795237649
    0x3150d2015180301060302210708060112080a030b040f0b040b04090c0b0904020d020301080d020d0f0509040504051e1b060c06071103071a04020a082a0a08061306050105 74
    0x1680d0081050000100700868052a00302c81c5901400016640d40e580d000503a001060418019045400d5165400201c0d0144070003005031101c01d0081c005545410101401d4003000400900f404101149801c800c501c00c1e007240070000070081c01800449066401480200381880303070700d0311480c501003075100c650400e4065027841c190000c87c5c0c12800d0345401c100c5001a0f01c1904100d9001d0f50070013884104801501c00345019001c0350b0b0091282c0415114041c0c80d0030488522501480b4080007041c0c031050388282103901402c0140c0d400308568880d843d01c40e1408120180c40441c6c2c104074514920400000141d070885076058441c200707114480302050081500c41c03d80c0b0020160807040c0040e0810b80502001e250b105010307400c47c1d242c88a140c48184000d0b52040210807050204000d02c4107510727103090050050084c40300a00302c00040140c46026110040380c203900718600c400866401c5594010080c0f004007003903815103148e441c041d14922038030000841c0480c0c800d85800000305560030140b2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 795240134 1250 795238884 795238909
    0x1090c110c130213030503180931150c031b050d02070f0b040302010501080c0406080d08040c092f0403050d080a020415021c08150603150d20 62
    0x40a0030702507a4603414410030710007103140d20410035003c200340083d0190750904000150700800c0036584521600d5103000349025075865070b0748200c0d241030a00108004415402e40104064100000740b03060a84542c0b0025210000107407041441640442a100c40ba070000c0711840b0140c0d60030400d82d9104442d0300b9480e410030300c6040000c0e5042c04001143d103803640c02090854003848001084100a40c0c91103240182260100c0050b515100100b00c0c0314020000b5a5103072030100c909019850410b958aa5510a15504041004400000b10301800340201884c5d001e0940c12605101002c101500b1210288000d134044070300501e0100f1541100d1000829501a40d0f030020140451505880040310036400c09482412250707400c100c002854262114803070200451034018080c40d141128000743c0c0780c3c0600880d44248800d49080209024000103000700c0702c8030848a840d1207803100d0b180154032000502005412540c041841014420101030080b0703100394511400380f02c0ca182c1010b0121044900 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 795241384 1250 795240134 795240167
    0x90313240e0a03210206070912060f0e3403170307030227040f0b011e021c0e0909030c1902041401090f0b09011503050601020f070b0301090c 62
    0x2000c84588a400051000207005000d240026240c2e181c00070400c020991103e02d150700c6501c040c4400c1e4044c407455600c00c406041c0700c0d00b000e00c1c080011507a550000d00080c80169210000c04803244a580b203226040359810880304058032044124009041500c102207a00100380300c40f994001411000b041900e034085100311340701d610304c0408040d0740c0015184809254007030048842e0340241158121080800546e44841c45c01c416061100711810144030014080c1032010000c4103980203c2500302c0c0c0d40401e041c1490404944800300c1c240301c0c0070040040c41c101740094000d0b00701d41c000084070090204456281c525200c0e030017000c1e80c0b84900320008001707800c03009455a03071103000031248030403a0000c0d001207507030ac40707001d007500b0016000d03040601c40b1135481c3c202071240b040b24450403140c804240e565a02c1c65041c0141d1340d48040c00740e101c45003010744610006a580c2d01c20301003076200e40c2c02c00045400c2143c0780c00020010390024040c9983e81498800030055043c4504407107a520702c0e12 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 795242634 1250 795241384 795241439
    0xc120309010c050a051005101202010801180f09081e070314130b0c0d09080a0b0a0b0a0509040b0402010e0d0308070c08190c05160b16020f0405090313 66
    0x1400640e6101001c1d101030703030f15014440c00b072408030300d00f0320080c206101d45103400142e0340781c161103661100505403c031120107010580da890050342c20244d00ea05450690a50051072400003420360040c00000040c000c00740d08100c1c8a170104540c0c14003905c095a4454260542903c4c5110000c080340102d050140000b400c1354140c4a83d0f81000004003142c0a003100c1000005403140404405079000c1c540d40110390307000940105600350301a5815000e031518502411005138591640d41c50560003610640005541da003c00c0021303a01c540340d61001740303000780008840d460107003800149000119000d80c08101d000406618a02d0041143d98901e42e00d501d8640c09612001c030304030f500c80c51203001203a05c020704004002c0249403205840406988176074400140e200300e0320b00641000b2040c89010001d2088010074450b10101206030b59002c041141c00c500070300c2080c0009400540c4001803243c106140100b07010500b040030008004413000700800360080b03540c964450b22a00c009000104080b0319 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 795243884 1250 795242634 795242647
    0xc1e0312210a1103090a0b07261306090305030403080a0c050f07020f0a080a020a1a19022806140103020112090203120c010c020f07080c090601120608010e0c1203 71
    0x214844801d0b00600710309000254a03800b000c220140b03500507101200d0316031004c1201e070300b00445203042580c40b16180c40d10003520382412400488452030601c4400510000304005070107450b008030000c00c040e402c80c400348000c40c610705000d40194001d980c10746c0001e0b890340010b40e0400c0c03e8091800052120f0b070321985404120f2644a1654001a800f03d80c40032400101005954900b400b0002030506040034042c01c0005104006240c3c4c030300c0d4015000300c42c21034420140400600203480010412040b040503400c1485422400c002c80d030703071076001558101a00d1561410b4a1620500c41510600c001c10540c0442c0654004d00142440002e00040c1500013081c0c900d074440d0809030002d0f201404440d144004201040900d0b00a40d000da41d050f903481034080070313469042200a241401d05000781c1889420f081045483e034040c221070701d01a074448000301c3c0c0f0a901c198903801011440c41c00c100f152a85410325540039114a012406507442880c0012095191074411000c20802c0030340107524210 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 795245134 1250 795243884 795243937
    0xc0307030305062205161d10120c05031509040b180109170c15131704150c02040e070509010e040807140606010306120302030307110c1e0312 62
    0x3001001c954215406030141681c4d101001c26004030380c0300b1900d01280c54036201d00b01c2e901135551200c558003000a002c030640881002c03c00070361030841c401d69051081c0301441100303407000d4002402d8000c2035450045000360039540603010354003c1080384401c05003195078030304010100742c0a0300c003d84000c41000210b1600301c0310070904049441d040f0000314825000d515000d08400742501c40d8024000c00099400840c0c6082c030207a1980100014807034030380e050240504031300c5020343c10004d0a0180880340b041202c500041524002c000700200000d0468109000030800640d26004901441c24800c042134000710200340203082d40c01c0680003022582c60000c8103020310f140034100340c41c1000b04010301408546400040302c03040190303000030013040c1805e0000508984450703000007140e008a4001d04000b96001c02142d400c05614600443d400384006c02e840d040030040b11b16243c0c0440b6010702c40c92444d030b0344e2010f50b101020840135500d90400c1000c003070310b09115140000c080e00a404c0c04881458 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 795246384 1250 795245134 795245141
    0xe0109020a020c090a0f02040e0414060919020f0a062309220e0a0311100606080c2109150105090403270509010f090b0d050303061c080307050306150c03070303 70
    0x10195405c042104504105a0303000c0b6485a00442050210841004244030320502c2142100401c5001001a468050b00c8075458116401c1ca8203140c00c950501c280665442d0b5544a0440300010701c2d001c1d0640e5030703040140280e41c3c07400c04001c0004500600038200021001038031090a405400001c000080c03841c5955040d41030510016090f03919082c000040000300072240c0701510035114220b05003500300403030b8540051030113800d480318201039080c00000da00442580d006880302070102d07115240c004c0c1010f808280503031004400c0c551941084080d140c0000e50010f4068003519072440342c4d0701c440034040070030b00c1140c02a0114007a01c43c0307903141600103614803210102070300c00c204ca03003078075400040c0b4503103401c0e8000301d4084032030382d801d100d5294284281c9002ca0b104968210600d40d15980d0f1341c2e00c80c003008224521928111b0501181030703692030f891010059000700c80070350f41e16141d0b9019000e5003050710300501a0301d070004840302c020b102108482d00602a0801141803400070307502100a03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 795247634 1250 795246384 795246391
    0x32703120f0603140a1a1801050405010b1e0f0625030c15151401030209041d060c0403050312071110240506030a0f0b060a0206010e0109020a020c09 65
    0x811040300c0d40c00505041a00c244410354448450118415255090441126558641030b585a4112113103040001c2e804922004e04034030901032182c0d0a03a9091a8040178911494945100c0e508040401003080010760140b802c0700000c03076101c41324100104130480e44002c210f403026040306181c02d5444161520001801c0050b60150044101c080f0924608140c023052207421004100011070110800010202034286007600c10b40c00c04c1491080640c5a4044d80c084c070071508804800749200c091350344a80c040b12080340c00074106101101d6980100c094202c2c1d80c0088210600480c00032960001d03c000c101c60844e600031008508000c003d2800c0c12808130301500c04000d12070a80c030711400e4030703c1c01d022905c12110622030014005e84507584000c00d100e80c2400109081048400030701c01a942e010541e50402110000015800901282d0f0b90043c00b5401d0450b900c040080703018030030b00b0340c000307400c1c0c0c140c800403129a4405c0c0d03030b144403031416405603000b40005a0048000317441c40f81454840d0766070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 795248884 1250 795247634 795247637
    0x10b011b08120a06080a24020a0c020d02060d090f020f030c010c150b100f03110c1b04020d090b04060e030708040603150b0a0f02060c0903030a0c1419050d032703 71
    0x8195580301c00171854034048010442c0d0074411804012211a01a001c1c040c060000e11303415450425404401080c1d0406c10300e000b8840d618240c02032055454802c00d640440710094400c100688040c100060100c500300c8040384115003802c5072503020300700030600250710001038442c8641000c0c00c0d510b0b050084408041310b04607170764400c1818030554980144003295050303912031440d1200c041c038000b000c0e94a080405000e8010800c02c3d520001c030001040032000e8140c1103104043e03064000024068410341b60710b00d04840c1031495000a002100c0c6020340680d124040400401080102e04c0c1d80fa405801d0000e000c0030310600041003086d000e5041030f448042a400b10f920020b4544252030315540000c1e1044001401e1b41191600013501001800c0d00700b000113a007181041024400a6900c0c03050015420070012180102400c00112801c0d041240a602c4240c8080780003039418101c9058004100391240e11581d080801c0641c0607100321051a8613660700000c07a10700703944061040c48240c3c0400c40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 795250134 1250 795248884 795248891
    0x11060f1e0f0d05070305060f0102210d020307030c08070318112706041406030d2d03151403060c1b03120708100617060a17010b011b08120a 61
    0x10720280075100100589500c0340320000d650f00b00300c41c0090403a42e0040c1042d025105644259295a80000b5a4950b509d94100000140710704030f0408503e6001d610b801203200d03400803080c00310b80c41d01604140d5840e4070f1955203240d141d0307865400724244e8201d44203011403108001f04510200c1c00f01c100981c8880809803000c1100d1301d09065002205004441c5d030828180348000f0302606240c107000300d88030301220305203203405814441c000079110303059214000d09029108090680c0c20912041c5040100c56114004031803000300a0003a0240295402000200f00265404031340c0d0a031000310003a8240003e0010b00340781ea9107808010341c0764403a546401c290b071080c40c83c411401d80c042006201040300d0060050071424a0000600541000307400f46000b80b01100b004c0c4016640082400f240f05240c01c9003103100d40b80c44001c102041070541000542c10458109101c030410b0541100100700402c1e60360110060f5041404110f0041c412801032007120100701e80d040c4032468103035541d0070524412000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 795251384 1250 795250134 795250147
    0x60207080304030e0406060518091302130507030c0c030219051207081201080a120f1403010311030f01110a053007020c01030212180a170711060f1e 65
    0x28010350002c45007100041d6400c10030a500f400c00d4040e03d030040c243c41c203180e030500c0020401d50001c0811301203000d000d0724440000548000481202c0404242c0191280d80c0c2400b80a040c4005490100e900b42c01013424000000c2c0d0309031241518903110380d01940134052042d01c520f07141d0303505604140c0665242c81620b041d030401c2c2f42d0100c0100603841c46407400c660b03107541d4002c0b50181444140d004145c15046098801c0210f07400d9520f0740e10400d681d1400621845008100765640f0001c0d00203089100c2c004030001c0100030704603040740381c0d071032044080f00e03003500c48151028240c80e103030261017683e51820f010260307220f0b0040b00a840e4440710b40d00d02c1441000750114002401603000c8a02020018010074004140d8040c0420f4084840a04c2c05520f003110032000c8054045014001c0b8840c0e0000b51144c1a81440502c1012219a800030136480300d0340305103c0f40c0420360464042580c104441c40c0c0040ea00303142803402c903000f90800e03035103507801d0108965108901c040521152944c00c10b040100c13 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 795252634 1250 795251384 795251393
    0x70b030c130512070314161a07080a050702041b02030a120905031809010927031106072109110d020105040312030c1d090a05130b09030a020d09120f060207 68
    0x2143e0300b8524400418005255042105203e003800c1c022a606411000040240d402c0c00d81308802a12a42c141d0301c1c04000f4440c15081d60b80c07040800260103284085504c1000341e43c828000c145141c004c69061100391010602c0740004050150345d1009640100720f031008960107a000c40c14401c042c217000003105941030b02c9003810b6a10a459070806c8001102002c007841ca80036904034094a0102800c0003224095468002c107042e8100084070541f20400a910401d0f04c01d500900105c0c07050015140e0786e040c09140608055607244840400c4540020305503903030001c2d4820005081c2d00324154060130422001440079103800e824050f07042100c02c01001c401300e401c820301c284101d18995000621141002c030002c143c0140c5035038024081ca014ad4a000c1c0300e0b07032200e80f55074020b4006100000d450f15005c0084000c1c0310007220040030000c0d050304001b4041c101201411017441d02d5001d840e0b0300f85103c1d804443d20308550081d6a40c41c21a40300d8000810050210005207a01c030b014010300d0510711341c46 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 795253884 1250 795252634 795252649
    0xb01021504060606080f010f030f0221010518150610140309160603090201020c01030c051303060e0d08011a07080d021c0f0e0c0607051509031209070b030c1305 70
    0x2410396180f070f02c41a00b0407100341d11a2039258481d620030491501941400b142c14210705007484040c00060030342e42c1d914150342e1100d0306805000404c8000503030b000e0102403041d002e48411984145000624802204240e40214030300d031b1010918a40e10030181c4e5210100b0a0081c0c44480103000c01c00800c201035500c0910314000c60107014807500829448003450250805050140c01c040c04142c20641340500507600000e2088101109080c0803825001000045520740511803580c00d9000c40040d00000740699544011144007500d019602080304041003aa8074010031f00c03610f07000c4203004000c0000d1250610241c6103451103443d600703144c011005151810b98106074084c01601c120a0301a1312510350b6440341d0640c01fa840b42003401850600030b01a6261000c0d903078018018000068240700704001030146000020007844c5074138403030900e801d220f0781d02d0304202101c1c800c00c2101c0c03010501510700001c034a400c81e2810b6104a2960b500c05240310310320f4000300e83c1e000c40070049110124203a43c40301b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 795255134 1250 795253884 795253891
    0xa09180503130e09030f0a030209041b0c0614060303030606160c0e011409010f0b0a0e1203040626060409021c0302240c07020f03030c1615021c030b010215 68
    0x1440c460310505010100c52114409021505145c0c020030403029514020029180103c845060050f1a0400d2070f000c074000c0c1100200301640c14510813a01c0031650307001810200000c2c02010f040000b81403440040303154040507203199134503902c14000242c440c50028028a4003440f40c1c0d0355031889002c580d84900309140107400c44822000840d00602050705100e80c4200c04d02e2049034803981a502d000810ba00283c2240140b8525903800075a00301d0942c0107004030006044058200310162940784801c6440360420702034000050782c4502d2180551002124504050b138641410121a803514010800180700180c006c90308600340b44143c414071941d040c40d400e46180642c001d010325400060001c0b01d070b0302c00000d0302c1d410050b40806101241030060b040d2038400d070381030315114440e00120f000a840c60003101c150788041c0c85417600c1e6840b0310038000001400c03119840607101c00101c40030800d0381c840804020116039454800121840130388640c202c0c062054040c01640c141c40103001e5405038044003103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 795256384 1250 795255134 795255157
    0x90405071a07140102030f06040b180a06060306050109060e100c0b070801032306060f0105040803030c071115070f061e0905100908043516050f0a09180503 68
    0x1240e600c051044501c3c4458821603904000c61551800180b501604080a80581e004503560608c1c070745503440c0c0b1100c00105214010f001800c0c0d290800c1000041c20a40c020500000c2c140200020746500440010043d20250b4236484140305284080c80414011700c1138900411004490a07030100320401c42d454028269a41d6003a0301d9811410300440c40d5018a021f40350b04c0002340684140000085606030300840115180400314480b03100403903050207650417101c0c441c0000011700030005400360040c44064410200b412000b044c0c00304100001d0303210055070650400c1004800005444960740c01c2c0214803960b0000b8000000500c050380304108a9000d01440769505548001d202c002c1001620107007007100240308660036a42c8014060140d441a041102010f07441c480072450035200c5a1052480c1ca81119000101c880e01e003903660242184a41d980d10040302c01181904240840e03490415026011188161801d038207000100b01c800d00c40340040020382c41580c0054003e100802012650 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 795257634 1250 795256384 795256387
    0x31e0306010216081902060c0d0903030f020d09050103180b100e15010507080a030f14010302241608040806010b0702090c12060405040303090c1e080a020a05090405071a 74
    0x19400a46050089403d5061100c0c41000070403410f00c00003928041909000c4134000007a9040c40030507080c0c081c10401c1401030041d0b0003c1341841e1703400050340d0110380c083c1d512140c42c1000c03040244d0701c0d201e03040100e81c002444543d061203294003a400c103074443c2911143c03100011006855540c6000d8042c1c85004035100081c2c410481c003a849480150070540c16065003800c40d0340a00080d010303114003040103021001c00300e003520445000e580040f00f1804140c2040c020281c03030785120207594109003c1244114640306a42030b15441e00c2c0901e01b8444818460729251400082069550000400088450f44400c00011401d0001482410b008080d441201034403800148100542d0079401003441040f03140074070460416410800781c254000c40d060742d000915072a541000c0f0054810804003034421210554000707080003212001014101c41da20051401e20386807003039151074840aa5000e540a9002034040c0220b00d000281142c001d445035040b18049c0399101110b803000c070170310305071580e01080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 795258884 1250 795257634 795257641
    0x609180a0b0a05091e060f18010501060201021b0d0917011d010606091a0301090b0409060504030f02071406070b0c041502030919030b1315020f0c010e0a02060d0e031e03 74
    0x41040b85c00410021a409180708542103c1410765600d8000e240401c801e065101260900b43e01c1c2c844080305101a900912941d130710b41001034080d5100e1108070b541480c0036070881c6c191420216400c113000805540b48000d03645010701c5100091402c01e14070089542e915880c03480f649010844501006c040800465041e1424001410014695110018000c0c0d5101c100e03040002c0fa0f01207a06444a058000418850b2000480c0007030005401c004c3c03a242c07405050105064100091010000c030a50072504003d07250442600140d03856000c280d0402c005014950018202000e00350f4424400380c02c4504050341c4545100302c05502c022184003680001501035074a040540c5ea860103102003088400065213156070340820702d000100314036040d1141d142d55904000f036044101011400c030500a549400c2a07084000c481e510002c011429507280c540e01d08068a40070030000303551900103041900385000d15100d1070140040c2101c15401f400108041a4560000003100600262168595844c0c0c603 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 795260134 1250 795258884 795258901
    0x110904020c062203021e0109021c020f0618040506040b100507051c0e061c0203101706130210020f0a29011a0c0a02060d0c080f0609180a0b0a05 63
    0x800c3d00e16614400d0048221290110f80c000078100c1401c1c0000c4d00c401000b1221030002d0f0300618031480000d601840c102082c0c90300507017003080049814000c444003200c00310078204000103407060500c202c0300940d009031711005c00d02c0c0a5004952204010b04007040310329280000076052034007804568049070380440c1031010320004000700082c008503000412140e40c0206006840764034415a41440342030001103e00442003203103007004c48070034184000e54680c101140c3c2e0b4030205005016540c01080140c021840d69000041c00d41c0c0240e0900c0f451007061801602070011885446240c1c03010b5100303031006013420b24002c00100702200d000351010359440002d00b2074a6400c0c46400d21044803d800d040050100784107520540c40050240c0f10400c1e03446a003005c0150601500d804003a50101003c00c00310b60001154200211030003072030356500c3c6569101d203140c19005405880840e0024803690001d15502071549000c00e000141d0070469805084540d148594030400701d44015840e501c40040c480c007038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 795261384 1250 795260134 795260161
    0xc0a061d010506010e210111031e010f0603090206070b040f12020c010f120f0f0c08070513140418030905090115170a0603020a0803041509030213110904020c06 70
    0x8030608000e2141d410200c00003002148408100c0b886140c00a400689490b00304111104440f0960000d1203684a03a0307800d4145500120b4908401d5144041c5001801c95010b81d024140c41030346400c0046c1a003045002c900520070030204070b810190400c00980072818a1001d203204a124a901c600400b1151504c42200920b8104080c25544145d251000b01c0ea04030071902c400300454509440a07041840071003020f441d0314402d082e407036403402c0c1c00381302030311560340210300c150b80c0710348420910b6195050116400d1054030a1a03c43c1100d8040034811803076505030041d4620002007000c0743c040c0008250290415681c1c2040707006c145101e10070444c0c0c2c200b01c11000c0c0100700c0384090f141c154008a00250104002200710781c0d040c2c400130b00003006003000e41c1c0804017940e0081c0482d100305807038500342541e90307002c1c0c0142c50101044c40b00100d0382a01c604100340c04d99501800c0440881d8465001c00080d224112030000361050510030400719031200c0c40501342c8200500000e01c52818403540c2c10940 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 795262634 1250 795261384 795261431
    0xe1005040e0c0d03030b10050409050c0903030d0e030d06060e03010c03020f1204020d08041e05100906050a020a02041802011407020a120c18060e060d02030c0d080c0a06 74
    0x24606040c9807440c850030100350031152100c00d44420703007100650320b0704600030420142d0103503100b825030b200c440c80729501001500640d45125400c10881e22004018840340c001c1020b55035040d441080200c01304166038011881e8020f08504403410110700030031400c2980c02a401c01ca000820086804005140034000c12103000c9450a08614086405181c04400e00c26022400c500240c1a40800c00319143c21111040c40750b0006100340c0ca89448140320340e00811801441902c0d0b00020b240070440c1d180c204080e00e44003c0c1a02d45204241c503180d0141c803036403c07405121080d8003403021a00d0141c1c40e14090201401031400c18001c003400c5920000d03000c82403d9000c17500d07911081c8008001a287e0f0020713a000d40c1c001104a0500300328924018440ca5007580002c0f081d0204142e40320b0a0130240d8108005130303510400b40d603080c5e554050a200146400340d4010350b0544c4400c0c40c40310a07091440000380501e0262840900e0021041c4119103070800a1a007103030556030720240980314420030308441d40c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 795263884 1250 795262634 795262639
    0xe1005041b05101803020907030203271f1e0c020d080c070f0c0825290a0516122303040326040f0c27090507030c0e1005 53
    0x10182c1c24600800c0d00807283d4107a9505011035600f0f80e0303110f880d86504071402141d004125290900c1d00d0000200613400986240c11999101207108406a1303401601c0044555800c004080400920800c1c0e80750b4030940d4441001c944e82d40c140e0b145403e10503401e124081c070400f0710200e403150301e407030009140072202c40c000401c01800d007040c06601d401c0c3c54200d8805139080100319604181c0d900308100c0f01002d9600201e1030344124541c004d80108600580c00e018031603071100c0c0707203c03603540c01c08141c010010300300c1181d80da4032003031110b80c14402c040050951400585410343c00c114020010b400b04101080c0c0c1520560f900d00074681ca5203a11450f50204641c0c201d92b1450109610780f92b10006000145c4000c1c00c1c010340005c443c030764407543e130380040355226526460780f0941882e04001140b011000010340b28400d80700c0000c25031706441d52888009002140c00000c0100d50440c81400807c00d08000b2a01402510400004116910402006025542c16400721410004a03c600021483e4021030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 795265134 1250 795263884 795263933
    0x13090b040311030a0915020c0303031008210306010305070201060515280c030302070f022e05090307060c080d060305030c010b0f0915120105010b0405091003240e100504 74
    0x480c2940c41089801103550308090280c07090001c0c86c3c05e80c01d0691401c849034140c440031080000300002401c146040b22829020340303a002d80310000300d44010316501c40e401e8120000301701084880d442640810390100f0b85100009040d5260400604616402040a0102c0001185511a205240f005412001d8520300910b151421203c3c000c0c2c600c5403000e8000d002c0c0365010035910103010b10a80390100e0180c1c000c0a640c401040c512001e88500350700041083d2070361186080c4606a40114111403150300000c004068681c034160040303900f90303095402150000f200780800e420360309480c01840c01640c07040300956103030f00300f04000c5400c4a0301d000c600d0707100b60012403c0e1800350320f0355450160401854891802000101310126811400ca461603003480d40c80c000001442c100c405000d00180c1f442180d00190b25200c403503071051082c01340e0002908130208400c08480410403100b40d48074131040c038100418040116140c0b181404085440b0b40d1030039842c3d40800003003046120307061225041d1502c810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 795266384 1250 795265134 795265147
    0x15120f0d12090f080a02010e0106170d020703030e0f010507050d090e090601031208070c2a061701060305040201110f01090209010b18040c12050103060b09130312020913090b04031103 80
    0xa4610f624511001c0c24803c00010402c015901c00e4000d82942c8569500034071115950390101c1168011071110001c180c010307403042501e014804170391242120341503a560001c1c91881010007175050181100181444400c1102c100010014403140d6070780000c0752200110180341c40d400044147d001041c41481e500003600500000c2c1603041c1101c911030440c501204590703111401034629074815078001d085407040c2420144c01040103900340103422520005000043c0d0380b01d80540752064021203034492262a50700512000344079600c0303d0b5009005140205142e1019002181012010103003207000d079450f5400340e81907040c185021401840c0101100c0e140c6400c0342801041410591507041c0b02d00e032500d04c0248214801c1c01030400e1740303006400030803403543c0d00c0c5001001410695180c0b40200760b40710000e20004c0d96004039843c5c19030552160744000740d550745484001c0d400342400b507600c101200c0103210840c00501c03030454894455485043c0b60300706802c0103003414a02840d4507105a0041001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 795267634 1250 795266384 795266393
    0x60609090b0f0417250c030c05010311040515090904060f0507140a0e13020c011b030915150306020705060a3e0f0a020a030e090f15120f0d1209 63
    0x11400e01304240d14020351074000c1140403000c0042c11948222402c0c440311a04814440c0110016048910624240100c141e0312001075040d05c480c01d0000030703446030a000c200306509125a0148407007856200311480c00c404c0c0000201c0203903068a043d41c855603103041d81140550a445410380200390b900340301441d40c8615012041c68490501d2090412084409903000354072047e810045034010003a0540d00d83c0c88800d1110300801c40d0382540103042c01b181240269441c00703886001d40e40390f00048a0640b000e04103a10074040c00e0001c071100301d900144500000840c0491002d80440d62280014007807908140e0140c20035a090340316150300b5034440b204500000e014511094030300d0303400d00300c407551180c2041080701000d0003003a030314201407040028010b40d51035003c0b41c86100144251a1000040c1c0f0040038080d0038802110749038141c0c402e000c04244845010005d102d0008002021011013a070b0903003600e0b051003000400343c072040e803019400e214000d801803480d5202d4040704404011901481d01c9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 795268884 1250 795267634 795267653
    0x408060903070c05060714100c0327140a0501090b01060e0a300203010204150206010602010501030b220507060e120f0303060d081204050a0308090102090f060c01020403060609090b0f04 81
    0x140764482c0780700080120800107038400c5c81808400f00b8041e05c03242e500f0030310f10401070300909003209c0000786040f01c8a03008d50b0b11340044142c06000c0324034091008400380e407a042e40d4000305178403a01c035109070581b040020f002409500101380c8140314484683d45000d1007d84203842000d1000e00c5800c01560601c90b02803c1301082c0c044140c0a0140e00b07002c040d40c0c1c2890504aa04c220294240d400018082030744140d4000c2110340c0d09155007260070580e40e4003012800c8600a02008194001c1d13040855414003809000d038500880131179024200b030210b0795815142140e194880d002003050403040035520b1809540d01b00200221072701410700802c90b20b40d1241c491100800103403107012603403074000138031a80c4801c1d01d031070103c80c10800c091400d00c2d08120740d03502003d082c120000340f00e540000341804818002d070384c034514000d00080e8201c4102e400300800354100380700440d00e81d9403e1100001003030746405044003e000208000403445e040707081403100c50300300511581e641165142031000003020b420 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 795270134 1250 795268884 795268889
    0xc020a0605060a120615080312041106040b030703060602010609020406080f10030506040503090319120c0819030b0a08010209090c07111f0809010b06092704080408060903070c 77
    0x20001081d0b0303607000c005008034803541c110103900c040300c25400e0100310082e480b00e0520004844009405a0396010b19640d0b0b00c42d062626110001f07010101d000550100c0d190000250014003481c1000d450369910b10241e0800c4410800290b21000c4c00c1003203c1d02031084001402c40d1140c10343c074050900c04040d0525070040d0166a050b9a400000b800c250080c12100001d19403100944400e82054101650750760400d0041600c01e01444403000300c00204104100f0116a1040707140740e6404440e0415900702e0810007055a0358003081003608100c803003140c0108903500c000d480008155666a092104014503074210039513a80c170402044020b590b401e1401d9030f1001c0400d02d0555514207610707106071b1a96481c0501e54101e104191441540c9000302c0c4180b40c018030990fa240255681c000105080e10407803404d00c0c1e0441400c028050403030070100c8521004800400c0303000340c6040b00b00c40e00780c0c0d00780301114192030b110008a02880007800a000658111295800842c07d089480d02e91103100e10861 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 795271384 1250 795270134 795270143
    0xf080706050c030f040e011d100b0d0905240f010305060c070303090b07081e0f0112060e0f0d11010228110d05041508160c1a07090312030c020a 63
    0xc642c50400440410032540c3c00e4500c1d81100e074595a844690070700c40c0c0001c3c082e4034a40000c80e0700640c00390781640d030002d114408148103407901501c1d241050070558403050001608644131084030001c21070400141042001c0703403d21880188511320795004001c005060b900e4440d40100041011510004596070071490100216507a212240350580003414403040003800c15000f1002c2100e4150081c002c6841030f102401c1c051807803223003c0c10001091074111a440324810700d2400500a4050144071040024810140058210068150710f843c0141d03c2d0514001d035445003045c1484941c1c0324003c4501c080035407000b54149285101034148401c20341d04c00b00308481642d000c1c509003910841d00c065511468a050710781d408407002c4020411341c0540541702107641301c2550748403001e1240000354070840d883d8110a025000c50301d0111450303810840250788103804402c8844401c1c4400076410700034005922800d040314551f14202001040c0074200a041c175117480341d5268895004a0b19815980d8070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 795272634 1250 795271384 795271387
    0x31050402090a0b0a0e0c19020115030303021305130209040b091e0c2101030c050307140d06020408070602060f01121203050c0c1f14041e08041505030f010f08070605 72
    0x20400840c2c0302140300e81c400700002240c4014003c0a04000b00140040028070301f82c03000c0d03480a00016401d03100286045854049480d00c01c00c0030900c0395000e4040741000b9045001000d6440002502914100c006400480d0303001034042d140d442e00e481207240042c02502e80c4c5205251045408500900d00e04200301c450300d502d400110b2060085046071f509420b401031b50114403070040f0460030502030901007118000800e010201d46450001564811600b40185107018154400280261886002012104c5c50f409001c007207503141041c03082c200a000315a0040240c2d161400e000d12903c0011f030700155064584030b40c4140428210021180346c20940d05021880741c81d408a03c10040c402c10b800c1c00450f020709034141038030400100c00c034003503254422010303c8031104145c01820701d45001d03500109444129101c0551181e03280690303040560103500b10300d040507500c010b80ba810f03065001c0301c240003070000004c00c01086880d8480a000d4803407034185c000f0a07030a00d0680341d80c1c0d81580c010002030000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 795273884 1250 795272634 795272651
    0x3020d06350723180f0f0108031e090d05060703050114060901030b0f04060b1c1a10090806040b0a0e340b04080a03020f1c0e0f31050402090a 62
    0x941c0f0300c214a100b801411565002607960004158007200f5501000c1e881100c5011400001c5c0800c03020303050752001c6000d180780c00c908441c0018280c480030740100781c80e41d00307010350035541c0d860290105102e40204c1c050720b814548941c0040844034141c0050b08015000351a20b0304075103c00050303401c0c03c0b10a00740040c0140f225000100c002119288480e40a401c03d0000700b1001181e00c080c4c404982c111040414940850181c1015184007040244100c11103100b540001e10307001149100001c1541840d9000c1074841d940d140c20482c0c00c1320700313641c580300d280d05024800300d05210310030706c03124400040c0103001c0321901e00c4c002121200e002000805034040f000c402e000003200001c00104143d28910341d56a99488140e500c0da030480c1015800740c06407a006024010000c240941980b00703c500704841004040c005440200c0d0f021092038000320842c4031232055448840075407c0c241911010700060401500076164844207440d2070b0840e031401c0000f404016150548082e4000001000c042020039 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 795275134 1250 795273884 795273929
    0x603142107080d02090a06020d0f030e0a02090606120f041e050d0806060d1811011b0201210504111c02010e09041a1f1406180103020d063507 62
    0x85c644007a5405800d641c400950030340c00003810356860415072074900c00f0002594056080303032030300c0c04041001e410280130f601c01403030300e000c41c0e5a02102c0104000d00780210f8403004075508004560f031407043c00301c3c081403009000d14010b00d41c4241218a826102d01449581c410752140070190714501800f0450b400b0030b007950740c1e00d019102c206006000c2000301c6515004000c0001e140040d003511300d4a441d6600d281c0c40d5101d0a114810710445402650310202d4580c0116190030b4458000ca6050410801111211602e80149401540202e00c1c25070150ba511003002150940c0c103240d4501103e00c41850301c0143d80000280802410884508003981d89038240145062550810b40e08080c64032020003070600801071903076400e601682902070105da1101d1a02c1070740944d00418540c000800d020101c80380c611030078042a80c10341850050b0070a0301404440040d606a604011501020701707030b91300b02c2a401c240b0207580d0000c040b5007030101c1c418a00d08054460b2840e001c1e6100c0c60f01c18454007100310 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 795276384 1250 795275134 795275137
    0x608030a030f1805010b040e030a0c030e010e041b140307020706030f02120408190c0f0b040203010908032e03021f140d0b011b050705100207090603142107080d02 71
    0x280c2126100f000074814a40503000380303842c4e12500c0c4503d143c2407081065581c000240c4513802025140c080e0344810a40303041d100f1041d4410300703d04000701c041c0d001589072240d00801d10640c0a105544014483d5201c01900c0200c400618910f01c10090042044c40b0354000740b00000c0b90b00d141000104c065010004c3e1000e0301c03800c0c0218013544012424030041007000c80080a1090028041c603940314042d070b804803110303141580080d01b20b807044010403001c079604800c2e2580252000300006009544c55a6005094000325650300c42034142d4600105040e484034507018840218021700003006080d9400581d038540348419098841e40b4034000301401e607014214804e00c1044007407001d034a88024101c0340000d0118089024002a05080401e103e0750584941003c803507405809084c101d824941031001c400c16400d01c00741144540e04000400583e540301e0a0017440c02480080c8c11a43c01441a5192400020585803505054000c0c442c01c0e2554400366045142e0021031071b582e4043c0014a000613 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 795277634 1250 795276384 795276401
    0x121e06024b0c01050c0c0708071a28050324090c0a091e06140702010c35030a0b03070f090515040c030b0307051914010c0c0906180608030a030f 63
    0x143d86030038140101118554044c040039040c100840c1d69054540a405403205c5551180011b01c170645003144140308112409842c01418482c1420f810449a201d4210380c42c441c00382c500003041c0000280607a840380360b0b500c9036400e414200c0210321020701d00c01241501c0f00092480c54000000f00301c451050348101c11607401485000c16080c048400710920140c241e40c54400c8101050302c105100590b80c4812040d50000f58050b15841d8448000751120741c05e29035454811842a444038202018950059a103d010740c901c1004580c3c4138074050740940c0c111414501424400c1c3c7c0540804c01c9164080011201603d06400d004100c1c0d481e4100b01a003c0401003604030b911606000031070000d2603140e40b001c0300c0300300308404440d60300e0790300c00c288003810716210b03040084481041018411b050f50039860001d44001890104500070760f41c0c8031609000500d410040d0300035292802044040e895826400c0460b100c22800c1018500d402d0303406030740740b01c0d040c1450249915485442408642c41d0700c105c90 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 795278884 1250 795277634 795277657
    0x5101107050a080d1505030c040902040b0a031b09060510030e01060312020307030807091508130602070506090c0108071b03020a05070902041a1201121e06024b 70
    0xd6040b0b614003200300b0b401205941c0c1c407051400c040d8060102000d144402112401b40c090004440118180300150040c64001c3c1c0c1c002d83c48502c1a10321780c8410b80c0e81c90065004d0440c440714140301400c03540300d00c0e007030341d1181c250034ac1029000c2c020303540ea1000340e40f603222080c10001050072591050b103000d000190310180030100e075120100000d94000c4014101e8500c6595180001d40c2c909030140c0f80725075903000d02030032160041200e130b0040b0b000c1c03600036402540000040906101c02d40d506426a07200b5542150280c0100003804500001002102d00194090030071704114900381c840241030200f00900c8200d1035042c0040c0c0400c0c54000d000440710715400c50700ba00d101c10303202c08a0700083e43c003a04c5042c5440030110000510700a1401c04d842d9406003443c4204c00036468148000d8409445940c152023482c00b26002e40400b18001d0300140d81d0034400d440240c0c948816804404007041c00302031810500e4480d5003004a00114021032001c5a0446003240300c901d403610702852000c1c00f0f03d6400f030b036 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 795280134 1250 795278884 795278893
    0x50328080a050910020616030e010b060705070e0a090b0609071e0806120708031e16050703170c0606130906060305060609060d1203020a1115060906030a0510110705 72
    0x522155001009010032201550303c100e601381803c80890b941c0c40100c540860001842c40000348651183c0c000040d000000d070008030b6075092030000640a544a03601c101c4095000a000704034250040d9081544002c06a000f00a0010039440e4401000f900800071031050136202c000a55050240c803c500b929801c910b511119801001c034007030002601643d0042c402d2140984291a00100180c46c4040d42e0080c4059800c02c804004901d1001c07c10508016052034144455254103110900c140325040c0642c00030206185103003072070510b14217240402d440d0a81e0800529142050009040d600802c00742c1e000200d210000c1407200040c0f001110041c149401d046001060000000e115030081104440115444d213507041000070a85420b04001c0442030910303050070342c180c081e60181401c1c403282e04085820015403802c490030100c00307880709140d81a4034000d22619003401080745034007000c03c3c1c0082c1002c11007a2101a5138041550138804070301e4864412100e280410b03019078030b01d964080101c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 795281384 1250 795280134 795280147
    0x151403070f0f1b140f0a020f093d0603111c11040e0402030c0301021c091e2a060e0436050d080423011d07081605032808 53
    0x8440105901044c1028130a020215080d000042103480910390f00401c00e01e031202500050001c01038000b040e840d204409107201c0320100c4901400d01c0252105000e810f078480602110340840803039103401484c1011310f001b50a0841d81c041004032840108110f450500c1a651034043c60f014085006424004003008600010314203980140180241d00c01c8007035a0341201d103a801e2500300d004000000d4001c011251f201c10004026500545055004d01c40703610343c072100c041c0823094014191008444d03041d41001c1100c0c204088280075260101e4084158000a280460003001186552407140c412944d920300400c00e41c1500a10203801010030492001704807680d0210fa000243c000d00580c0d00e40550b41e0880e03c0346120344446842150710009505501580d8a903140b602e070005410786049650300c695045949140061000c0340d0a8841c0040181606250100d414110108824140c0228902c41070201c5d035000304100e080040e001a80400040348460610090030b20302c0d0300640280000101c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 795282634 1250 795281384 795281393
    0x42a02010b03010b06031b072604051c021005130906030c06140405060f09030316061d0601080c090402130c08061c0b07051308010501151403070f0f1b 66
    0x3a00c0e21080450003007044c00c8071203003404030900c4126000ca0444144507d10300e08885000050f00c4842c0c0101c020681c0105215800030020382c03180084444c0000c04502040546032041e810101c100104015450500c00c95010403841c0049143e01c10a0210114415032182d51000d4000d00030080743c60140f03d00781d07490501d103074444000c4c01060000b07015801d0030b03081045032008a408450010b44041e180c036000d0300c0c6165850b0410b541e40380e40746c00708101200f0a221040b586198090280c1800503801b84505601141075803402e10622958011a0041200d2032020441c103640c1801540c802c009a59207100181c8141d1302880e000615a18140e4001c07e542d500031020340c45200140c0e194044821030424100412955180c01031041a4000005051500c00d1018100c40d1032707030150701b400e59510b60800391f003991000d8000e40c80424a00f01743c0301d01c4540c03144c1000038956091503139a01c0c40c10148030040c0039000c0c0e2141d60060129071104422068403a10901c01481100103103038202d032040c1d241 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 795283884 1250 795282634 795282641
    0x50702121b010e03160609061d0c0f030c01120b030304031b050102010b0402072a08191b0501020a0305090102120307030509120307020a0326090d03150506030105042a0201 75
    0x7207030115071070003e03580c032031007030000c01ca8450795507120300300900c00c11568509000d01103030002255200d8490650800f40300d032000d81070404115070400ba040c0c01031a030301070005002540403000c0c469400011040242d90b0400703404400e6182800010580c440d031000441d24600c60b070781c001030008103800041307859061929203080c15120240d00030f0100d8a82001084103a0142c0840070b0b01204128900240b031502c100c034446a8a4954490306841540c4c82c4407090038598151516296540d07030740f07254410030482d003030100340300c0c2403a008a5251a04040c0003c0d9110b0300c4080003010300c00001615280c03603000b00407020403080c0c403c030b0059591130030070320003000750409403180600c2c1e2050000c04900c0c90810303425684211429401044580020b44046070001408104062044a060141c45410017541e200e00e104a54a1000b080780c8200d07a40024200c415040c902c1c002104010810b2191740c5d500700440381183c004481c040f94120700101c598042c45480004507484481c500d0007070100725010341 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 795285134 1250 795283884 795283927
    0x1106070506100608040c0608060f0307120501060f1a0304060b0901090c02100c050a0f0e09090d080f0609070507060b0306101d01141002100f02120c091305070212 71
    0x100c148030b0295551100ba10041c0c020361740101000708010b0244203c138444e03040076900c464000e014030070002c12280401c1c1410801d0304021810340d03618500c681031080c240141c40061141260b6032907005c2c80c0c0002600c4402c20945030780086000000800c081c0491504503800c100c42c020220403003540d50714240720040c12409031800140c09120b13010f10a00c0f40034402d4400c222516200d2a00c0c3c0542460111007280000c40c104050000f22403091803680c50303414020f0f116005c3d90009001c1840642c0340075200e200000c0401205e1102c0f030003000b2a86d1107050350150032000b0f40c02e015466091914020f00a043d246640b1070705031080404010041610348464070860341440090034080d800e0a00d110711440090182c03460700360047c0085020b9003001d114011016a80e40b0554442e004003912480039103d002910160164011400400018180d1407246d081071060700814030306184640420360035058451000c0d201c990301e10005682e0f6009000380078120307890303240c1075a4501c28000302c0c6241c0c24032107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 795286384 1250 795285134 795285151
    0x204031703061e010203040902070804051c110d02010903050f1b010207030f0206070602070c0902070201031109010f0819060608090709060810021804020d0905010507050f090d1106070506 82
    0x2401030000540030001101e00503000540001d0f42d2001055080e0700001e01c001c5442e045100401c800034203800944003601005114040c0c00da0f440e45131004119540c00002903104038044074911010003d01c1710490188900002d076240400c00d1400c0c00180d426855507840500035000c0c0f41f0b01240d0b81d07040845c0810f0740b05405d40c0884248200400126515000d82c04000c0000e081e2045600261500c1e41c0604a15413003418050b26242c005d5403a0740003405141d000c0380b410380e0041581411503800d405030b0529001484203080c00d012010300002c0c10f0308082ca18000074009600f0103e502404801400d01c82242c0ca12801d03c04e0664880d8018070000f001c0b1144a2140140c031004a080c3c015400ac1034201c034a9440200b041c10703518080d000082d445510340051883c2440e07140000754403140041c140882040d400003880c4a000d01b0701d60300b9035100800f40d50401c0010810360188640340d40070f4403500c0409403058401d5044078902a005c104542120f40d5010034040340900401c680011320741c1c403a8021 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 795287634 1250 795286384 795286403
    0x1b010b101205011a0912120c06040506010b0f030c03071e0c02130507020d18050319030f0e0109060311090d060203092a0904021804200a1805190f020403 67
    0x2a51300d8580e203c4440c0b40001e0564008212407000b81c500000c228806c4019401610788600c00c00548441542c80450055095004101000300740f0400b441150300500504042a280139007450020034540700003448050821404070114005a214501006181c01082504085203406c5503020345890084107080380300703503d030500041d5041640d0007a10b0103140e45030020002c0b804041420344000c44208010b50f100d410b034100004003a90108a0524218000c03d84c440c2c0030700301410300802c488a20007052003804410019038421380d030310040c000e080310914580000e4a000394a0a20300900c6091082035000c906114010140007065000750302a0440350101c2d0710f10040201007456011041c1a190f0004440292030310b0181000301341641c2c410310040819a00307c56a003145090302d901600e003a0782c140168400100010515802c0c0071502000310348501e6090f10340904035080c082143c0c820040c0e40e80b0b6101040030750240b1046003400000303500c000d100f54504910312000a40180c0300544602c0030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 795288884 1250 795287634 795287639
    0x12030c051c0b1005070c270c0f26040305092106090c090709030f020a050301020309100f060b0301290c0d030f0c05340f02040e0705061b010b10120501 66
    0x1550403a00d800761b105046000c4070707103000710140024044000000d180310498168a00c407407964400c1507190700c7e13280c983c4450300c00c0858006090400d0020030310b0000d5a0a43c1820b441c000031441f07250320a078945080d554812107500400c5020380482e1500500c500703d032016598070f1001040301c40c4250380390f40880c0c0d040a0b00104200d540e180c26920000440ca002200740049070720b420700c610109001521081005030b131040403c0c2260b004403502d511507004441745554024584c09840c1e200c1c010107205100302e40c1005201c1c4443c2c80188224902d0a0300991703000c05000041001d0403020120080d030945540d0300c15034a50300c0310b030142103160000f86003401d2000e510545104102070241035942d0581040303559111b00004402c440c0f8402c00d48180c080c3c011981c401c0c58003407428414881c00b220510441c8500c144020345503420f80c290456003010700140204e849190a030780e114030b10420384000e075a5028184500504503900050b0300b1400c4206103081458000c0c0c8204c0440503000700801c82030f139 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 795290134 1250 795288884 795288887
    0x10302090d02150f2a0619050702031303081c05190e07120f1202010c080c0702240705011505010e06180603040b010e16020309100504171608010912030c051c0b10 71
    0x281142c103d041c44112040e0300007c06d09a0388420b90100f2240112403800c1d103004000040217840364801c0300c01ca07400040100c840c94400c6032003130031201c0e50704007886242003040d40c01c01e00010546041c0d000d180c0d0741d00c0d41d540e0000200304440051091000001180200b802c08407507181005800f074400e6503031a4515000c05105100d54565240607951304241c0d921b406458002c1d65020f92016a40100d0303950245440038825074280061000864840e03070b5601e40c40c0741550130b44620958105104004100800660741c021b00c40301056035085a0990f41c5494001183e2001c0100302d0342540c20810100030481044280c400090603603040c3c0707113011030790354444000e6148011080c500c600140c10500c6410040c2c24000ba10743c1403114075041042c2001d454501e64404040b14000505441e80101d440b003022500300c21612029000700002402680a40d07181d00c0c842a00c48400e00007010303981c8281e143d086108034159960304040c68221100100203880c060080c020007a902c9120304100040c14086a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 795291384 1250 795290134 795290143
    0x60b04090617032503030906060609140d02030d03110d0207051b0f1f05160f0b0f0106091e031209060906020c0102060f07020a05030703080f06010302090d02150f2a 72
    0xf0800001300c0c840318511605001c0c034620b42c00e1030072414142c4640c01c1c1d4000510354003800c00640b4641d500e140c91546400340044800c0e00400095018500380702012000d620b01007600c504859141c1404908540070340580e140d1440748907000010b084c4042031410401901040c1180c000c4161a0701d440101c1075441045610383e0f1104200354001174103001d2042c031030054104090030b68581e0900e9428420075480903450b090300b00500b102c000b4820303100001044001500c481c4c010f03581100c06c00056050080140601016001c1c9108800b5140186081114076908000141d980201c5504200f010b03100301900200765801a14045110a60b0129042c2d2000614001f143ca059000386100e03200c80718500c1141001030211030031401120200008654100000d00310b0070300c41e0342c4025a52134040380c400780d1090058000c034100360040200070450703924001c0e40101d00b50100d0b207000709400c007890000014441c1230b503c99410200403404001c046010a034202c400c0080011066141c6000640c198a4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 795292634 1250 795291384 795291397
    0x70902120109110d090204020412030e0a14101407150b040c030b10110a0c150306060206010f05040213051c0c080f0303072715020f0106080607030f060b0409061703 72
    0xf807903014807200382982440e4002c1241103002420052916840c4c03044400b01038407000080e00440c00d0350340b04c941c0905100c00c00b0f03001440791030400005070f460000060380c0e0382a004100d60800004403c01000c2c500382030103d4140307542c0228241c401d00003074480c0300040c040040500d0700c00c80c5418030864146000b0700a080c80c02200801c0c24034001060309040d641d51100b10040502c502c24107280710001800c801d51100a442d52480843d2207100901d0014143c8072560031030800c41d044007004000c8800300100070030945104035000360716000c0380303c8801040901903220541c42400102c103c411112500c210601c0c0034003400004810030f40312165a50b4601c1400621180c2e5271003080020303486403040025020107070b9900b0407500004500d454084001c2c5032a0440b1034482300e00ca031081201c40e0100980300c1000102d03c003e0000c145004851600d44e580141401d0078103031260113003ca65001588100003504074004c0e900d45840d202c480100041105006184d4052580440405041030000940b4207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 795293884 1250 795292634 795292661
    0xf140a0e0604020a0603020c0102210405061815220c1806050f0d080c0f03030105100f1416150b04240311060d020c0a0308010618050f01050408070902120109 69
    0x55807485c00504074004c5d03000030111005554240304001c148991341480104203018225903512900b0241420b609161001d86000e465a1802c050343e104e500d40411000c245600c00100100c1d2551100051190081001911a400305851500c4820454004c95050580340300210901ca41808460100d0450302c0d58014207501200000149585107000c00d0b240c296a0b1203280e006083c034134400441071030310505110704840ba800110050181e400c040c2d000c4500862503190031121078000d20401303032412a0b87c08080720303582000901c04450315a83c9213540501c030351280c4442000c802e14411240104044290707644200c1c10170b03450040d4101c208800000b0301021a481456403891540c03800085000ca41840c0d230440000d0001e01240b100702c1c07001c1c100c1c000394203020b0864880706150040034220140c02c83c00c2401700c0d400748064002280000c45040d214280c880380042d804200c01a42d184c002e0350300103182e51050120225003100c1c1500a27105054032076a41c10900d03600c0c2c20340c1d9801da8010500c90381 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 795295134 1250 795293884 795293899
    0x31b080c04020f0c1b09060402070803181e280c0e04110418030e01050309070509100302040903020304060201051b0a03020d0603050616020c030309030601030b0a0f140a0e060402 78
    0xc403500e09a4014034219081428940c90140303070345a180e00780060030031004c0c014050b0b61024505401e01c0c030700c450762100044070f04510300001ca42c1d514156005c040c15107034402e90280741580712000308000c0081c1d841000e01c02d12840d562003024156640d44280c0c3c1405410b003509180d030141c04002c4c0c0140c0f4180342c1c00021200f1441c1001150706441034002c2082c1e510602c0b050015040e500d40c1d110f07403a00d20300d4144e0001d0384d0140c1410094004a0071164480c100081001046440680030a40364103549080317884503010340b0b51498101040b10f02ea08041e60286c60202404201500000100704640c00b0f40c0007070216648076070640d08042000c1140d8141c60b5020840c220602d4070a074010404806502000640b00b600c1c0d03140c81c1d10300700d07013260301201080036803003020030a43e01003120100910085008624184003000840e440d400c0600c4024000c81803207000c0351076840950480050005070300e00400c5040050240036131071410075121166500d2511081000103030b80801c400d44980d80103000c20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 795296384 1250 795295134 795295153
    0x110a050909030a0e1f2a080408150106050306040b031e1c0e090a11130e010503120310030f03120c020a0c0e07140a09031502030402190f0509100806040c031b08 70
    0x7a10b607034550f0005540011201b0864401030f40150103010360690003010303400e46031414549030302d240a00740b416249030400780000401200c0d61000c100d030390050302560046031140c0c2c940d021900c0d040b00d08100309481031490394222a000d0300050a40648510785444500342d03451300e031090b03501101c403d1740242c10001e86030001c1c0b114101c0e0b4014164480043c0c08003803030800d81410502962050b6041001880510001003005140411821584100d188040d51035418003451224120314184401083d80c031211200e4401d040c003401c118002c9490b00b2000f0f02007290308040084d191808080c080300c0c900918034002c10302c45981c032070061140d507294076907582e600180bc403e00c007103401681d050380800038105d41c0800040c0d460b40600300d203490411000340c0c0b079080600c1080b0300110040009051410280300402c020070740d081181c0100c580c10307a42c40035180c981003503a81c03581380c0b2900b040b51b4602c00c0360144001c0003004000d032802c403401a4011501412009100952103060744128402035003c130310380 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 795297634 1250 795296384 795296387
    0x10c080d0b0f03030703090602060a02090f0d020103150b0702010201050708040f0303051801060303050c06130308070806060706021603080a06152105071d06090d110a050909030a0e1f 80
    0x8903111a00091068081050802c0080e2441d0b100c000b0031000621000410001140c04000340354000c544201d05505081c511700100e0f0703e85040c0c0003a140f081d0307044090b41041d6400303a801001e264079000c040310ba0103502e0f4a161403107940640c000702d0040d0301c1d1100050f0f0070383c800c000540c000c81c1d1100d40c44070141d405840031009004050407100607840c0c0980d0750805002e0134410200254425100c045c1c48144582003a818104001c0903200420040e00c1c000c0c0c00130781d200680613445003090400422544603140810018090031400802851000501c80140d600a81d00c00c00031a20a655400c12903669100b41e0b000d450551061b40a88005c4000a450640c0500c1c07c00118245004c00009811481d000341d40c141d9000b550400d0109401d512140d40c41000c02001044640055400c2450300200e4004180142c1c040ca401030b02036a50ba5000902c0c6984404e8440000e0400424150032814622481600c0f0760002c1080800728040c0c03c0c24494504020155100e83c111241402850a000080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 795298884 1250 795297634 795297641
    0x314070209013320030703140d02040b121f0e0105010c0f08031617190509030c0f070618030203190f0f0c0614090904080f16060504050705010c080d 65
    0x1c504108109401692052181441c0041c4410040d50b580042002d01d640384134005407114501c400d1a0010490140400d411040307208040110030609591000040c001070024061504141003c450001e00305524106410380c2c40e0080c021134030808a0228002000c1110021030311a5080c2601031200401c190360240020000027802100c10000c08001d6649030a404e50084962042e95050f400b030b802e074010f0344100c03589500310300302030209a182040c4a0281000452100c8001c00f6602c6000080b155542441590140840c40c030480b0481c18070b03444826180c009d1030040c0400940d01c01446a216511000702908072600540540001d600b501e1070902800b408030019200f491503041401e00040032140c0300780c0d01a0003540800320f589c0c20510024039040d1229507000e02032906002c00c40c0142d4861b88810f030440d1b4041901c5566080c80441c119041c024410b40d00003d11594000505220083e000305201e144030f4425075189544800040d203404180c010040c5c16200d0070b00c0283c00302c40e82c1e41d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 795300134 1250 795298884 795298919
    0xb0f01030f0f020c030406030606020d080a3b0d0207050612070302130801020304020405130530040e1602060108060c09030c090406021201062303100e040c03031407020901 75
    0x4001207030700640082c800e03050381c0c8504020001039000190030040d40380e143c45654041c0c11540301030100d48981350401011180050b06d4402c1203541ca03217445400c8000c2c05402d0848034041c1d000c5241401c000241c25011005039030700707415280901050100c1032403000c592402900e01c000d0040e4248180305c0d0000c146078400625200606070b00300054000c4540d03214400c07000340105400075a80786480c0c03040c002582c2d0003402d41d07211f4502000300e1000041011070b100240c05901e100080b80007440c1c820016240420b0603d0b5032008800240104840704d800c0e44080c881c1013221400c0c89000304515081344d6811007441012907036080300b00031030f00c4041b100d002404070318001002c40300001007c1001440241c0306540490311241d0004040c80150200b00400b030040400e0700346420511468090800903600c242000c3d040e40070b0000001c2e450045001031400a45a40c3c00031071960328042c41c051509649901003078001c14a040400809141554111340c42c80350302610740c0d401030b46444210030034008501d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 795301384 1250 795300134 795300161
    0x12010e06010819150b0307030b1005060f0702060706091b0509010b0406050405090a0b09010906061803030207050d03050706051e090303060a06030b0103021608041802030405060c0912101b02010b0f0103 88
    0x3034a82c2e021720b03941080600055801000b8030300391070030000395486003544164840342c02824140044640030308d008090f9148180c042d81c0030343d030750b180ca4507100b402030400003402046503480003200700a0b10f50cc0b036125826290700b501d044215980301d19450240340100e11407500060790412040c00b090501010081d080816800080745826041000400110090f00803450480e51104200711440e0b00150304044407248080ba0b04809065071070007900e5003914060030740030302e00e103d0a50701058804d20480c0c0c242e5401107800c001c03600344400154031012143d00e40c45025140840412052940441164000c01d00104603101030b0389400d100790082c110f050855414180c0c240035440e250321403012480f181c10b10036040c440c0d84a0510407800e40d20020000b4810030383c0e1040c0304000020307000040303158011104400b02354a4101642c00240440107003150076205024000c50b9010844140e003101d07601d00940403038207404140c0050103c1c00c0f25010481d9503440342020b00d003800746500a601c181c070020020f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 795302634 1250 795301384 795301391
    0x213110f03010e06040c0509011e0903020619081e04030e0409080c0c041d2515030c0807031b030c090918060e071802090a0512010e0601081915 63
    0x10032a889149400903400216088a25400c22140b0f1400e03200d05c000103051802c025081c03107444000207090b00381c40100e1892100840c44100c4145001e0414400116801030282c0d640b180082040000074440714198401302c0c8004000c2080299042d042d010000303448007031402580d842d500c0803507090180d441d02c2500159170700100e0000c654031100074038200100c500104041c04203441800212143d84065060441d082c813140c1010000200703110401900075030000c84810303405541c01384001815400300d0002d900303c40030345001a4268114405901d107640f40e26415070340d40003050b0b081d60794941d40c00d500d480c500102c4586282c021303400081418002d25210207030a03224110070085402c1d141034441c82003c40c8400100300076440c050004e242c40c0080141c211585809956503a005480344140d20036500810005a80d40b9862484001402c1c01020080a0345c21007003940c0c02060080740c2036695000341c800100342190000b541d40c000802d040f5490b142500581c886034610001c01c0d0704511851344 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 795303884 1250 795302634 795302647
    0xa06050411090a0c0e01080c04050603060303130e25080c0d090b0106020a0c0f080a080705030706060b0301150c0201051804060b0403060e1006261617010b01020a021311 74
    0x180c00c0c42031846040d1943c0009044031400c40050007811245aa8034104a042c400708041504950b0954007110303c00c3d1400d40c0c4a80b61100000e0660007400201544200c1c2c0e000000b6050b48280c24940c06000e0700c0c0615813066411100c0085400d0700402a0310104015601060030100c0707030802002d0080c8410070010343c2070f0840e41ca40c10100030a9201e0710050b8040100041070222405110000302001c80d080380c3c2851411540b5a1135145d1117001a00ea04800b14200d014004240212000d00c0d501c403104205070703074071030b001c00c0c94680080c000c410710750101c680301c011001e004501640d0441d805840b15030414440c2070356a075003252000c410b581c019840b8403000036450300b0b103800340000d54031a1001154002d82e440c80b5a00d41207509203c16216401c003176081240b82c3c0074036454030443d0410f055215452a805e00d159142a031080e045031640031001c0c4e00000e07454248555580c850701d414000b4000c14884400480e92028001c8001c0d5200201082c40203141b03d265209803584400c00b9112802d005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 795305134 1250 795303884 795303889
    0x50a0c060905030c0d111c141303060b242b05070e1f0c061103071e05041d090109121805090403051b0f0a1a070801080a06050411 57
    0x80700e2040880d216032000c11030ba050000e0522410200401c1458200340c0442c3c10307442181d444203a5400015504120b0b40c00e9202c0c58860000d440c0c00c5441d11030903e80d0381c0031554003100d0540c01d43c4415500e1a2811040040c1303441c0410282020007003e820883c0d01c40b030740459205099004e03861354048848601c81c0d00800550b01004038420308102d25001640745031901000d000b0150b00e1001d0391060f5020494180c20087c140d91000c8909210724088405580740e01c1c00034000c4c03130018414a1444400b0040044559001c45d0010307241c62800c80c0c00c011040c001105488501548c020781e62020310b00441a4213125241403125848030404002190ba054107450b12100b400c1541090400074803960400c40140d03c2600d085402400c0545d06880079241c03d490081c403174000c0074001d01104403a20409103442400304205c80881007444181e4104e0f4440c0d15000c071007800c15100085201c2e040100050f20302d801101094101c50002c030180503108034940d02d0500800e00200b085810032640d80400700310b42c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 795306384 1250 795305134 795305141
    0x8060102190b0a060b07080403060519090f140705131503061e0c051809060103091b060306090204080a1e0b100617271c0e09090f0607050a0c06 63
    0x6601584800c0c05500f0040b98410960b6074540126081803000c00041c00018069000c84007200d8001e0800921915041811250240c95194980c02c65061180c982c0500c0000151115824852041c08455403501040c4030340b1504030348210b0354401d00c00c203480d1035144402c3c1c120304101c81e41013403203c4104d91240c0d500001c5a0b00c18603c1d031205504030b41e02d01494603517403087c07003090285801c1c0f2604004800342c42d070110080d15a400d83c000e1150501040c901d034025041640c031107030b029078101258011885d070601d800450707116800029083c65000031b044082ca05c212400d48070808042d014403034041d1200c2c0995840c0120780c41d04641201d0300d91001c11110f444240c00740d00c2c10f010030304180f890120000c152000126a0f09020031600003480329845030000601c0c80a07011300c0388102d03d0420300030b0b00350601c0c1150041d8a05046d80d541e030b05043e42d51041d000c03074214000325012102a01c55100e1907a403190160802e00e9907512910125001502402c080d04401540b4604001d010800307035600c1095 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 795307634 1250 795306384 795306433
    0x1182105120d06050a120f030c050c04050a020d0b0a031101051e0d150510090302040c0210091112060c0f030a022101082103060d0201050c0d021f0509060708060102 72
    0x115030354039004c1c06a86024805031004008015081b801c070007990b11072001c2d01c040760308003c081c4102490500104081403025140541c00104100960700d04040c00038040d40c01511814095441c0021031662458400c0c1428262030b0440c0500700c108405000644032076000382c079081a890031042a807820803014000402e80c00c4420310011500c4c015074988182a1242034100c280314007512401c10990680c0410b00b0000c0701d8048a021903039074000d8800f0303410b007280801000155410030784910184000c48050900e049000d907800c0104264081c0c5070b40d1076003802e460781017514004200f4146000103c20103141c010f40390b41c3d40140342c60600103210140c01e80e01499101000145001000682c600703201d14420358212180c0303203404423080040d20344148401803d05129140400d404015a4801c3c41078541a072049012180702d5142c0000207035032220341410708401c0e02d10080f0800360700f42840c05101d002d42203100007000b0607100c00034280d0b140344000703000904501c106a001c0801070f200384c44d0107a4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 795308884 1250 795307634 795307657
    0x915091e050c0f121e011a0616060b040606050705071a1c11030a050907050316060804050c09011212021219170a1a03070303020705010807140a09050118210512 70
    0x390301c405d2041441c01d60f803440040150611150003000070703c0d01c2e160b00b00c0d4000054041c2032081c50314640341c10300041034030381441da81240c50454040340e107a8210000306181801030084450517951507071110507800503410300252620090001056105804848141402c0001404516000007041c558000d4108803a84020191607000b409106e11080c004480582404e90203000300e280d00400741103070120380e0b220b0034040200c81030004060003014001c0200c80d5038018815034031940d4400d001800d40c0c0190009a5040480c00c10f002e00103400060081e40080c0c001e80303214240901c010305141c900ba600b44082041c0b15003a40302034446003070b2000180c45101c82401c001010329400300c0041d01b42d000b40c0130160003940324580a1002c80c1c0c000031860100c650034a44010965078001085640d0310041d003103c1408040450208506ca410800c04002d0301e9080c1c3e80d00c0581001c1d2911424001c62034428400012021503079142c44182c0040e800915074001d604940311110041403800e001c0d400002d00d0340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 795310134 1250 795308884 795308923
    0xa080c07050d0e1c05060112050708010204030302030c19020a05060d02091020030f042904060903151407030b0613151b05030a050901030915091e050c0f12 68
    0x900b51401110745034544c10301d0303080d04c05144c3c6181d1340c0c143d45007030602510480c1c3c481114080e00f085000c00a22025040c110003c1d92156034900c0c0180d52a00801c0001841e405203031a4a070016085044213202250020169030403d49030205004540d841203000c0145240c081002c0d075019210000411614001940e41442d2520b2907403901800c01d1219103200030750782041222070b019940010544040d51412469020408800300d00e07100042c0001040011440e408140001d01c1900020207204403401980740e038402c450742101c0201200c000220a8400601c103c01041d0a980b1a0b8051070b44400d005d07211a28101c0810113110303002c51950300003040341d0740350040204025440400560310031700c802c4804022113602e6881c99240d0040b10000c00400001181180340ca80c807171382003401081e40042d048400c0c3e00300012010081c18100c0c4003580c1c2c2c8407083c0a956030000030148841909038002014002d182c3c40c520070480300000701d0f0500b60788980490340c5442d10318800e05c40030003203088246601 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 795311384 1250 795310134 795310157
    0x71a09060907030b16110703060e011404200a091409010c030207021806130606031d120a0503061206010b07120318030c030c05030a030f0b0a0b0a080c07050d 69
    0x140303000300090841010303030024182000003a216803040d5070861522000c1c003001d068038403800c40349402d4604500a661007045000410b02032258000000c090282000348447c3e054603403401c0040c00f040e90b000740428002d80000b0381e11400b81c081210311410050007203007859030364201d210903038103c90f6491915010f02424002d018609200701c568103a40d5082c103509010582e0001800000c02048071a075000301200050404e645100c00480d84110398042004500e44600b4018004c0c2400c001410700d0325010f0089603030100c0000344c03100d01a1b00d000840f514202542780100e84a4001030502600400d2401d000110500184010340c060710010003c6901c4442c1070908803050f507814620302e024540b41c0340c03d4220480c84c0c04000b581050705420801001c002d0f074078007180c0d820f8400402030000d01000c18000c030300d1949074100c4145400000030611000ca80f480800a41d68218442c122a00000b08600c00d08280a07000e129400362252514500748003260300c48500b0600007490f594005514030300b44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 795312634 1250 795311384 795311401
    0x423010b120604111e0408031801080718091107060e0307020a0b040b04030f08090d210503090715090f0905040b090604020a0e181608070e15040908071a 67
    0x1e0036401142203e09021000b81c82d001c0c951684111840203602004000902c000c070070281d02102c1c003d0100e8003c507035444552860700c499007a4410070484c00210311b840865009032040700400c182c16200d2090349138151a183e2804010000705100c2c1c80f00042c01e0003000040f65192092600551a0b00c0144d50f4941851040211021154000f078000f04420f1005102c01401d920a0318240c0380e00000e17515134000c1c3d07828195801d0140412459000010100d15000c02c4060039100c210003454000400e13200b0320008090b510b501084581d840d00d0760055000700003609214070382d4041024075042000c1000d403501e0011000c401560444c3c0415501e400922040182181030503a000b09681c000d01002d0506600003104042d00f0712880314503816200104010060641c006c0c20105048001c8030b203000c100300080c030201e070700b1442010074074041c990300001c4c610150700b0181e2042e4400d100c0e0f5101442144208401001000025076a1000c103011840010382c0d25000c0030409641c034180e031419807524440303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 795313884 1250 795312634 795312667
    0x6260a1503260309300304060f0608030a1707110f010203060a050d0b041719031b0e03060f3106150b0a0c0212120703090f0f050423010b 60
    0x5401c2009420004c0100c5890041035000c44d00380002e004011000c41c0880705d10161001240d0f100d88810b00100340010400e041d4401c0344608001c0350244074072903031080000d0316801000e8489010034807501103180400c007100302035988450f550a01c0303201c008007102518548030190b00c80c402160341c00001e102c2a441c01e0440d01c0b0003080100d0319500000b00658489055000242009040d0742c040c461501c540760815040d10070051080c0482d801440d041c0b88010041c0074100c01c15080642081c04480c00c075840303134000b0700d203c0e58064018400c03521034a1078443d21240040080308114a0071050019240104070382045100030700c0d0710303900c42c4019030510000b1500309000c0c1241d0060488810403580e10f903001560030201c12030524542c5445180041014550150703010400d85c0500c0c074840c001c120210001d0141c050227951409882521850840c010038094001c003d042c1380c20590810851030030360010b9550002d480c40c0b606e80d6031140a180d11684100783c11518210b0f101085078107900d0f10041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 795315134 1250 795313884 795313943
    0x70903050c0a050d0308090c12071d060f10020a0602130618030b0106030e071701020a140307122f091318140f061f06260a1503 56
    0xb945001c54520303102c00107092201943c1d00400303101029001802000c02801541c0c000b8202a00303540001c003172002d400d03031580d10300e000d0401e020a40007040708544c0c4e01ca56115220b0030700a420891102030300c03001c114181c07400b110300c08114072400500c44005000350014102034900407828100b6507050110160070742c0802c091004289a900d402000861b840d10203060441e496418005001040c0e030422500f02103482d04420111003200d40b103a03420240544c020b1480800c56071b00c1c884510002c2241c541d007448141e030200b0015111905654803401c240e4890b104080d64140786c01c820000c9002c81c100d5103060a054411154004a05000e1604007000380710a50715901c5000c000103040c07001071444115031901c0152001140003258407405004000e03407140c1e144500211002d80c0f80a051507010203d5032028640d504600810029085000740032682100c000101d000c005041c0d58080c5d0b00e01000020841110540c4036011034140e807004000090103907019a03e484685941c001c80742d0b18041c6081c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 795316384 1250 795315134 795315139
    0x303070f08070206150f0307080d08010b0a09090f021c0507030b0303250c0e150109090b03030d09111002061005031903030f0f180b0105010810120614070903050c 71
    0x70412403007507804154554001e050b41450a44980c5a42c0482c04d980c110584164040c4140d000218046034005202000e0035469544c01c100c43e0b03252045600b1038090701010002043c0d5101061211112580000c2da00891280d00103061020352200c3d659201100341045403c40e030b44405200b440796060145c1c06119505070002d6140c801029268203604105d440518100820a0307410000c01100001420003840b01303200e070482508104e644103607000b1a290a01c1d010a0646000040303c4200e4080c0c18807600000b0051800d1544c100b4058024015292040b1806013009680014540e030b07001c070001d80c89006a004254600d0300340e815468800c420380185200390b010354541c0240311031017a2140012685442c0208021201c24070714009000e500401405660406940c0701c10180b103012101300351800346550808990365880151000752056030701184259105206203e003031031480c0b5103030f0598414030001840c054442089403070000c05a4403240060040d41c1c041003480300030020280c298804 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 795317634 1250 795316384 795316397
    0x7050103060807091a060a112401050609010201060b040906060801080a21090e070c06050703060e0c07080708032a1801080a0902030618010c032c10020c0303070f 71
    0x200b401140c0e607050300744200341010351640300040d060080d4180070300000c01e020700380310303100c44c0d051602070006070075014a540c15101d49154100c200710389a411622502101d8a2814180d0906003030101c15030080d0891819592550400100c4040500040000f011209000079030340d824180f005100b280180d08c81c0f4859806045031074040380207060505800f02507414030340190030101038241c0300b40815a10594146400c0401c02045903041580e44400c0e500c00d11080065a03500d0409904407800d6000e4060319640781800120296502e100030071106010b50238460811324151380b043c0307180d40211240404100c000c00071802d0282c040804102c00c602c45210305041818100d005040d030500c3d005647d041210f0280440d410110344c0d0b000e0f1018030b80243c02da4050f803905448802c141000e0f02c0d80d02c1320035840d107100020624420f1080390313400104000465070000d602c01e000459491a1400c80c00e41d4020a2040008658144010103900000d00302950700c82c036059801400b41c80078800e05200f8881c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 795318884 1250 795317634 795317639
    0x30d081909020a050613090203070815030604050d050d0906150f080d1205040c031a060102100608030d0509030412050708160e0f0903041208030108121207050d09150209030705010306 80
    0x603483c0380079040c1c450a449090300e6000c050088411040190312440c0798a10000500c1081c65128654510a04404a1850120f8001424503a59000807035020b07213982c0101c003541039218840c40040070246d500403404941e1107584e4032214102d40d8544001e05400d000241c0404c10400d0f50f200090003010040060b00c0300b40d100440180404440340c0c1804509540d800028081140d1a0301c100c002c1c54219040c00e071103107400d084c1c0702c0394114159001805407003680403850602e0010301034101591860720140d410042441c1d1900003a0001030500084e6001c24800821042c0c0304040d80040107005800500000f817400408a06080320320b001c0c1000100c002070140300d040c80030b1611a81012018040005580d40c07500d41d541540181d410900d0070306013543d01d00d41170017a40c50182d4166021103065450107000b15094410510074060016074200c03025000991450040c00030b09034004043e20045918151942ca6a503d1012150403003109580820100301900b000c1210310b02418082c20100f010a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 795320134 1250 795318884 795318889
    0x2070e0f0c180d0606080114060306070e042a0203070b10050604031101111608060609040506070c0c0302061303060e0f1f180c031a0705090915030d08190902 69
    0x402c5400e401c0c07440114640080d02612500a50708003140c01c600c0812556807600c50071806000211140400c991700c0d44040f902605d0040380c880e02031040794880c42403500301002444003601e90810120500c10742840c98200101d0038071480700030101c403075000d19a19150752804034449000500086a80d0100001c01c1c030203a140c0900301c8041d40c0c2c00c034685c5c1e805801c4250040b02c1524400d42d540b0002d02818400300080410f203140b420540f4407000079601c03243d6805c8240603010b20b027141c0c0681290321000108bc000e50042100031841030140045a84a03034407900803a800d41d020000a00e03902190741410001d200c2d851041201d101d840201038400d0065004840d940c6091206440070502010901400148215404864400e144003030002000070b41c0c1c2815101d48910384425a114918002001c00030b400c442c000038403ca8982e20b800341030040c2d140500603100d078024020515050481c10391002d59904110303405d19101a0350328400c1d20702c1c1050104245d2524200060015418120703c0d50040c0e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 795321384 1250 795320134 795320137
    0x114070f03050c010e070603020301060e011103220b03040503070606150806060307020106050409060b030111130e06040e0f0d0e0d0c0b0f0405060c0102070c06090e0f1503070602070e0f0c 82
    0xa41c1526003142c6541d08100ca45006220000e80c11260748124040000c109400d40c000d54100c403015100c1d10201c0500310010368070360812051003000307600108108111b400308140413004046074408852130498036140c1801d803550055070284c40300e5101007411410480c15000b818041c1c0081c526118105c03080010140110802a141c21301c2220044006003049200354090002050000c0c020300c01c848203030070000c3c010401042441c0c005d50a042038100007031800300442d0b0341d86503120081041540f0f030002216010700e025106c140d11a45034400800d204008001d9039103c600824003818404031f49000103010302040b000aa401042100b4110001c42d0003014407608a072004e1004594803012003600c02d00750704c0355400041e841000400c540014400540c0500229403062941a03c1d89494003404d4654442c10f126180ca41c0c06100c0018aa52404059983c0c00103140c13017410801ca0321210019007050b0864020100690103090f080080014070295203400030315182403200103052501d1555007a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 795322634 1250 795321384 795321413
    0xf010920070f02030f01090b04140c0616050c1005031f05010210020304021212031503030906091e040e2112040215090d0606080f0705130908040f030305040302011407 73
    0x3108000b0820040d9181800440524010480200146200b42c81d10b904403400589044d07501400c00344101050b44c0340003032144007403000104402e04151658000f00b21442032000211114020007034480c1c0141c0324210641e036000701a8550541f00d181050b101101c900d102b5441c042c040305045010481030341c000c142d0002c12201e1b076a002d41d483e513460000c90410401d0040b001c00342d218144429407481a10f101a50050100c4405a4003910302c40c1c0c00c059480c042c103020706a000031f041001064514143c81881201c950070700c00c0042e601c4071000018120303021184a421250000c03c00c000c000500800b03000c1d000c00c2c005c10307160304107207625008400401c030061000b030068281040b2403103085140c40541d0f00100300186003c9603426a860b1820140025115010451143c1c12004c0b107100c2c0040307408001d40e01c003d0911014040d5603442031020341500384050b540d000d400c01c000310740c906001d03004c3c8000d540a512030755a180d2452000500010721003090325104481840803034005011400300303000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 795323741 1107 795322634 795322643
    0x603060709080d030f150b0d060929010c12030c030501080a0b150d0218160c0503040504020a03020d0207050c120f12130b030f01092007 60
    0x50925a5029856143c2c1200f9002c0030700c0c43c429400150200d05520001c00c203583c0083c04580c0412154110741c00300c060005241741da180c01c9000c1c440c001d041141d800c0215440d4408018034540170400710781c03281c00020016405a038402c0c00b800b07059981000c542d14602c500c4281c05001841c25000300d0011038109030001924100115100b140b19410902c001c4455072480b0700920340c2203214502541c0300c4181e400b2100581c5404036079110420200d90012814140800c40d5848009500035080c01c02090900c94000604048150f500725041070304c000d40c4840c9a40d100303801a0061050310501281302140c2c101c04e100d40011078452441d010303226048494041d81c100f649588010420035051f80c4140c81c2c56011403001001402c1440307094581c5540c05840d0305018583c0d50003036400d280c032001c0d40d600511001c0d03001c3c41016107448440741c003c0041c2074200110451405650000352 = true := by decide +kernel

theorem cover : BRFrame.Cov 795143884 795323741 := by
  have h0 := BRFrame.cov_init 795143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 795143884 ≤ n) (h2 : n < 795323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
