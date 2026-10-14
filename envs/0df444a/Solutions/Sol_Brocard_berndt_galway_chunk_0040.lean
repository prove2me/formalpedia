-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0040
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:30:59.26288+00:00
-- url     : https://prove2.me/submissions/1f52b285-badd-43d4-a528-d685e385e30b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 7014395 ≤ n < 7194252 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 7015645 1250 7014395 7014409
    0x6040f060b090607060603080304060203010608070e030309120a150e0717250e0106051305120601030210090f0902040504051003110105030618070309060b0102010e0312040606030b07050a0905 84
    0x200d400d000c1401000404950706184002d03044080c045e280000721700d50380c0e031280e02c0035a1048908681999002005000c440c0e004140540c2010441c40c141c01440e5064010980e40d124400c201072084005840303041c80044100710040c9615403141401c00391a06200c43e5202602040c00315446a002e0b880b40482c070040701a0252142e540741310014001442d0500100502052505031400001c68503400460082c07504104580206034039941d956407490b080003501454981d9800440c131415143c04440c088410006100d0b054980440701051011959030080d00d104075a9800740d01041c0d980280041c1408155020740704a840548040c401d070b03070350f11404032961465408000c04043c1d103000f0501c4d01d544560065a0302103006082c48002c03004030591400181c0046514200003622100b405081085600451200c51401c0c00240b10034808000070b10384074010208a140a0503c4a00280c2131145941081f0300540d0010841d0b0814100702c0c000a00a41c4103021501c0400c09002d800a80c07420619 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 7016895 1250 7015645 7015649
    0xb09010b06040312030b030d090501020105180a0b060a05130b030106060302070203030f0304050c04090b041704150c060b0d03080708010803030402060306060313020a0803122202010f05130306020306040f06 90
    0x40c41e16250500b96542c00c040c000d82c0288650405690b504014001c3e10200003a40003540140c482a0710b503403a240c002801d541004000300084500c2d040710095840b000560004096801001400c890751840d0200e13840c4080c03a401503500c05048400340200400507400408080400c0e4000d00001d6101c102c10740580c862030300c00030b425910030400040d020f80c410000c0c51f0031500c20703802d4a0076001003400050a40c1c0059009a070800c56034010700c02001407002001c00e0f000c0d0541801c508040c0f0300b0032942c002040d0324104d0340620000711032503010003015601009299600402e00186101b15040087c0114402c40c1d03444080740c0954004030711145d002003074900c600e500a028a181d0733a620800c0c07201580020f0003c52144034252031403c01070303603500102c901500d050002140c4815450078042c010042c068840e6541604058004e503082d581d510144506503020b01380340452030315003801180e1070b1240788152104400000c07004070401105800440c022841110305104191300704030014100e503068 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 7018145 1250 7016895 7016899
    0x7050603010f0510090504090b0114010c030509040c09090603050309030d02011e020d0207060e0102090f0603040b04020105070312060f150806010804061503020301050414060907030804030204150b0c01090b09010b 93
    0x202020411460070340130640207000e061a081a5040d59000810251001104102c8050441c03d0061100780c41495038400d03800707424a4076200c2902203071800752492280f02403141c0a152030703040b201038140c080e0600d140106210b950030001d503590b90070701c4e85c0c0b02e80007611202d100c0c0c041d03a880d00c0303e1240305011318402c55a10712000c0501c0801c10740d801d40290700240c00c5070f40142c0c09118100210350680f007101c60307038400e0000240c0e54041e240c04105903d404100b000c0c1c4a01d405100740008100b9114010740c0c420b0742800e1440d0384000c3c9050580d001265006122502e42c18200c000c912241409031080031581c64240783d1022000626003501d600d0021240f00340000d0340342002a011442d13942002102c03a0400c0c604907051903c03a004242543c00485050381c48031000305221800d410200046a4840a00c2002d041da860540d5202e29080c440c0c1c0c0f0010384686e07120110304019001070440c100007000a980c2103945c0380140c1c0f000e40c2c042d0101030300c00d540504400d40000c41802040c003a0b40301d04040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 7019395 1250 7018145 7018169
    0x30501151a18040c0306080c0406081902060702090a0606080604090308060906040f0207060213080105010b07060213090911030d0e01020a0201030e010609050106050309070b04060503040b09011104170705060301 92
    0x40c00000d41e54000855205000302252036440c202d403910311448850a001c0d603804108141000483c914051520319014003c51501804100002021409021001400c0c094034000000f90000480b20f00980901030f40c0404d44100f404030225180d44154202da442d629200285d607681750822048950303200700640450700340e034000351701868598426039114030010000910070442c031094804036003103231130700715030b10381d800030700100041d100c0d95000008000d110028085581082d01614460090400c0188903540110f80000b0340b40c040e03040c14000d00b40c011000c00c4007031a5810421110b556010501d8001c0c096400300c2010341d40714840300b20101c101030b0010301c00306505900440052400791940c03a1195640c04001c9442022401140d000b8a440d42d109070303d81c101991002d0414400d0713880401c03104020001003180d40d801c90141d0790b0280e0001040c1b05180d40d03e03498240902022069046014400a004121507124454034040340c01408121080c003070700c07801403002a100078041c900342c0c020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 7020645 1250 7019395 7019429
    0xf030506060901030902030a170909010506040803040b0708090907030504020103050601080709060e010507060f06030201020d0216030f140106080f0d0206010810090302030d05011418040b0c0a020106080f0703050115 94
    0x1004c1c1d04884005403000d0700725160301c2c0c410388420b001c40060300000c5003120000140c6144038504030042601420044030890b240a20b00382249a03603201d00d1090b1440110301144030b9040c440450f068400c0424050401030440c40d00910040c018081218104c4c042894600400e080e0351080c7c1c04188030303640b541c03600251681020300641d101410002c003641000403c10000b00022018011000d070005d0315200440d0550071840007906111140d4680d004540c030400003030145000ea0003880c000c0b40d8000103100d1a510740c0313082c040001c180c2920445481d6080240014204600103018507084089205481c84015004002ca03101d42c001c1c8645100c0f903010f481c0e5a0130780c0749940d0040301c9047c0b1a00450b85040442ca0b854020340e0000d0380402440b4000082c20602410010694840c05000d501c007801246040d0703032941c2403000060034480c0000c07000300740002c0f0107000358044400703050000210b03514000e203240c62556841c4a80012a800d500341707500101c440e0300c0c42c91240e00f500d003078242c040d80c051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 7021895 1250 7020645 7020647
    0x10e060d110d051b0a0512060a1107080a090603060503010b090610090305150702010f0501051c0206040906120c0b030f04080c150a090b0906060618040f050c0403030f030506060901 79
    0x256000207542d60119800d20103030000350b82002140081045400400d81503151141080341c052096031006008880240a41c403640401040c03070707540245940000902e00c100844042c0c0300b8010381d000204800300025503030301031726001910300b400c0b503516903070034808181c80e03409150996000f00c02054001d810325002c00c0003403074407402403420420940303041d150072996500c1d00340c40c00b61001c82c5090382e800004140036001b0350a02500480c1c14850000740403d515090203d6003c42030100c04000c1d01140384100811942d65000300da00030111443c0c14884181c6030288004c144032800c43c220344461604000045041e04607055030f120b206181e00301007480e40c80381c079058029031040c0640220b078043c0c64100c42890b445c2c0002240120f5a614002488824602d00307034462440141c5110000d5212208201d195a91039040b20366400d10380f2811222595442c0106024046000d0131002c81c0342070400304940c001e0940040c000f1a8041da43c3c1d80f00100320200d0650445000b41c03815034000c00c041000990765 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 7023145 1250 7021895 7021913
    0xb0702060306040b06040b040305100501030308010e18010c030209041401060c081e030406050601030c0309020901090c140c010c17060604030210020a0210020714010806030604030807020a0609110108010e060d 91
    0x2c03001070004600307049810f0001348580d0064002d00701c800700100301801170000801181228420442042140d035046440241c0030388814480c80040c04000030002d00b4030340b000140c4129040b0081c009004091000c070028019400262403240190f280c400034145520b580700c0014101c810136169420141c405032118499503104420240d48002001c80d405095000c0000a6102e2401814009414107210000405a455408103078040604114958001d42e0750b230125141121412000014060f50610098589255601c0a08501c600108040100b0a81034011084048969549601456640c0c0800c804442c098425940010381404240018100080d488540200b6401261400a250b500241001c1c000c4007901c0010381080100300907019030056a29200142424038031603070700c0c240c008207039546002007024080040032408124114000d0084000d01508100144124001410060381c01980b035030034140010120800000c07111a2240c50501805000302601c0c2c8240d4151920050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 7024395 1250 7023145 7023151
    0x4030b0a05090325020406080303040b070e030109140706080c030f130f050307150606050c0c100e0913120503010302010c020409060b061602040e030313060504030c0c0602060a0e01060b07020603 85
    0x2648001c001640c03100500d4000350100842180c0401d1000d01c4d54414001a50700e90361240c01560700030300501c400507445500680e4010320074a4500701e030034102c5000034058082e080d4098069044a0b11100800d50003052000503100962180c0005440b41a55030a003440b044420943c0041c0d0100800c05401503544c0110070540900072540368071040352240b5065038007102e400c540510910304c1000c0e03107506a00994000b0501410310034100110114515142c0b51550340d01c2e0311a204041e1200c0078240290050340f19010040c007012118640040311940c02c2d03491140990762074400a101c0190103200e001140d041ea5070603540c921000d40c1d0b0b542884003610603079804860342600d520242c4034640302e4001410346007034181801d071500c51060061001701c410103001c14100c0e4004004000c0b5060055180c29160355101c0300000d00ca95403400e003141d601c415140007c020148a07003000484660014915000d29100ea1040000c0c01000c540d40d400c81d0407903c107400119006004840151600b04040d5034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 7025645 1250 7024395 7024411
    0x10201060306020d020a020f010b0109030206130b0a1805090408160c05060a0203090406080102030403050405100e060a050901020d08070f0e0604030c03050601030312200a05091201050106021204030b0a05 89
    0xe42984035030b980401c2e60030101e0300ba1156507010642d00002c0f40d04200314002115050020040039403140300081090501d808082d00880d40040c1c4541e070346000b01540d0b0000c0c040314080589a200140d40100840300d11121071209110108000c900d914020038068015503202c510b041c900401d8100703040c4803030b00808040e68004e2080314000303819100c900003081c11510590245503241400000c020844004d90881e40150b0b00c14000c0000103a0407000301c8054a604980704005c49850800c01c9a01c1c41880ca61180c2000010400c0c5580e10b4018000d4844101c01749c00355003540f00f030881c04075085141126583d00103540c0042c801012380c0601c448040840000d0444c034a425101d4440e440810f20300d0b802201c03640c0c4500010405d05500000c81c002c1909a004180062002c907143c044050401014019a000340012a030314068013035800c8a038a0340018040c0510002c90300c400e6030080ca400d12601d0091b000d0102d81042c02d140400440302a070354021107090329a00c903030040e04010240100040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 7026895 1250 7025645 7025651
    0xb0c0c1b1201050702030c0106090b0a030303150b07030801030215120403030209030a050a0b0f06010f02120306060909040c03030905010e060315030703050f030a09061b060506040f0212041707051b010201 89
    0x40c01c000c081c021244240c8031500155943c040c4e10300c8407800c4079801c1e40800d0313510f0300c2c00781d00c000c3c1d81c3e480328a80811a07400d03290124a01400580046040016501040c100240000e02c3e00c201a00500f425040f40d000710307940c480c040c14502c5030700c0d1a44550010f2223401219000040c000900035406400c000c0409411500d412003a96207107440c20b0180caa043c1e850007928010025205c020b03c60090b8002c00c203180203900c8547c04d0360080e54800c940000751100c48000700000310a521410240c4152840003081ca40b0f1904140c242107100c3c400c01d00041d400580d40d4080800d0329402503420022010029103007a00e5035403000e440070204100003c40640c23500410f0703400030102d0010011440801004400385680300c0e448400504002519071000d1309200b511503440ca000d04424200d100340e640c201d90046160303a10031001400600d000c0d0080d44406201043c10107506540c0c020003480b50f4881c603001c078032180c0704040399101030180c00c0740203105a0264030a42280222501030a4420780180008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 7028145 1250 7026895 7026919
    0x40905030d020d0203040c05010c020105030a0504060b0402030403030b030c06090612060f03010203040c0f08060f010603020a210605010201180c0512030c19050c0405090c0607080405120102070b0c0c1b 88
    0x4000342d90120040030f5010350003005000600103444d4404000f000e0900b811460300075680d001901d980402858015070300d03079074030008040c4034071604820900e20000b0003c41d624a42841d0284c010590340050364002c7c8240d0008030704605228084900280000f4540c038209088040c2205d501c000c0141141d400607541c2d40c4d03080840d1001d001460299104424043d01c550a01d0f104901c1c03003c0a82c0651065842030040c0a0500305000c2c2060640c0c43c00c0c0340c05699000c050b9400d45045002407040200038903d0090101d842c20345500036419198264000d0142c0410410b0303800d0020b0000d000038040d040c254004000d0f62030100200700b07070100404142c900340415400282e08250581d595071049040501446081103001c0c0000ba0806000311010401800c00d03403500b0f03644040c1d111940e0f0007401d0020343d1209101e90714060f41c0042800800c01c00300d8900d1203120b80c0c042e4001304412580c00b445000490481d4258405496040c905040201540502d009049803000b440c89046030704a890000a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 7029395 1250 7028145 7028167
    0x170703151a0c160e070507030c030804030c0b04060c020f01060503190302120708030a0f0203040b01030204110d02030a0b04060602030403030f12060302030f07150203040501080c0306040212010806060109050109030f0204090503 99
    0x30601003074801c100988440340380045038130522600a00744810004100b10040000e604640c00c0000310b601446d20005c2035840e0302c3c09a5010f0005075020780649003070000c000070845a6003005030035101c240d0a0b00c03c0d4000d014440340c243c5401d40541c0d60306401c03010040c2109403400e900d02051500910403070318240e9400d211001141d10001090301c96060003c10000314486901824810f601d52400c1140f035842c141e101e0506604040c08000c2c4a541c65443c0300b00c00700150350990710305e16102c1404554a0030032414002c010510080b0aa000e1800c2542c000307002070020041c0c80c1182d4040c3c0300c0f43c001309440e1a00311105a0b0b14085840b40e190340300c0000c00940c40401ca005401e08000009041182c10008146030044600060004541c010030080c0402d0360f2050100360008210500c0546a0300c40c00700040103030241b03800400b00c05040c100009800d1a002a40701d018900a0321611081c0f5215801150b080465010107444418848410380040c2040e0703000e881610300a00aa03030408500c144 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 7030645 1250 7029395 7029403
    0x2090d030309050c01080609040b0601050c010c0201090c080303040c03260a0c110909030901030e0c030a1a07050406090b070f0602030106050406090906030209010e0a020d0606170703151a0c 83
    0x1000d40c0081c0e0303101841c0e401c00c102004510b40d4a00242068102844c0007800581c1804004000400498403030020441d0303070340901d082d980300385a044001e100d46072124000a000f4201c0700000d68801c01096000a80e501000c42164043c0b0b030000080c101803415500c9410310102036412181494001c6145040e12000007809840c44111560301d07503400506034180f0000e242c0c0c00700c0351203100740c98071000d0150345040002200c9200a080c01c02090212203070380e0701c07070510580c00001c6800d80115807074001001041500340740d00c0f01112001005c5520b403440c04131400d000f940210004503880450038006040544e002c0c22156124054040c032005a5950309416600700703900450102e440032406005a5410040686c050403c003042003040714a190002244008103102d100c028460079404111429400d404030f0705080c1c441a4244001303580c2d180007d00d091402103100240060002c0401d119070312a01a1010564100c40510034407820418280b0308042c81c44e11404805104000310001640140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 7031895 1250 7030645 7030669
    0x40204080c06130f15030b01090612090203031c050f01090902010c0308090309030a03020102030a0605010309050604020105070c08060c07110907021e0102120a0501080d02060c030403140c1009060c020d020c060a030209 95
    0x4170402c2c4440ea40d100207001e03114114800c1c1d040c072503401e00501c5855408803003640d20280c1c441021680d09081d0000c0b906512800340c14800d801c610019100140d48240c2026000d10010881038540b030780ea852003503040b94122000240020010500000402e10901165401680d6542071324500703480701c0300081c40c000590000304c1c0503035004410030040c820541f0130b10700101800e0900340002c10301039691640715640200002d040c0100400c08009010b9008207090150001904450550911012106036500100c100b214030342452088000641410902c2d2030041509800030042c08140d007405651004550000120b159402d22140c40c0c0700409c80003a0b8041c0da004940050503506140b0340c5400c08400c4c2c08880299440340050207031690070704017141c0c0e2160305403810040a640e18042c800182c030920400c0040d034400c113158103050325002c0d0700220706103203d54010814ec400303c1c482680c80e240c03540c40b0480542c10448038400503082480007810000000d18005203403914544c001030b0701e07000b81 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 7033145 1250 7031895 7031909
    0x2030c040b070614090c0109091d07060503010503010501050409110d0206131410030207030f0e030106091a0108090d0e060304080415020f100209060d0c120203070c020a05040204080c06130f 83
    0xd1201311041c03030f5030b40900942004040700a00088960240044c01c031401c14402d5011580d55050030802d20118010f2209200200c001a1004a0798480000702650070030301503548a9440c1800000b0245814810843c1541e131090810000003d5403081011901ca0b4880c05e90300034030104004000f088401d104d010181c08100c03a0015469250003e008401d00f4400303c070700c01d240c410801c08001c40c4d08210091562240e61801540c01c0710080046805821203074480d040030f60820042064543c054580114580002ea0350240c09a868030003040d0758521318296140410202201c030046420900d00031076100c0c1c0102c2c0c04900e81079541047c480c05002512480006030801400300403050410f000000740c0010b002f4003581490201c60009085206210001840350359440005c0740c001c1c000c2c400342c4403100156108540328506840d000d004000d038010103c0c403c5035166800300d00c031b20f0030f8400e4400350b030102402801c0c404000018848143c0c0720502d8505401c1e0290b030006000c4100d021710074042c000c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 7034395 1250 7033145 7033151
    0x6030c040204170105010e090304050907090806010e09010c020c0a060507110303030403050a02060c0909070c030c050706080a0b0301090b010b0309030408010911010f020604150f0f060b09030609070b070602030c040b0706 96
    0x2e803010f158211030060300300351030041c031010521480703070400003d503000d640c0210341081190700c41c0a416903101420754016850f9000303010000900e00d960100c0180b08000500091006070344015003245ca0b403a10004032a07111181480c00d0080c1c0d4400c07005082c45a105980c1c404141c42c100c00040c0c51500101d80440c00103000103400512036905004d030b82d0304544011412410040100b0026130082802041d0b07104100310442040b003454420071081400d02c0d04038082e00d10304e64803900d005040a008580f1440c0c864248140026a03003014070036012159000018131226900340745916905a10290600c0c6051005000205a0303410071311415030440c0c0318038600c2aa001d030041c00548102d00784000e000039504400c08110224807803004c134001010030b03100d002684020041003c40240000004822203900c1c2c03104c0070400080b120020312541d01c4c11021108142d9440d4141542d034034482c0074030402018184000c00000d819500950b070829240c000581c142902c0d44211a04d03500302c1c80302661182d031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 7035645 1250 7034395 7034429
    0x10207020d0c0501090b070807060203040305090d05060106080603070b0d0f0204030c06020106060305130b161b080d05010b032404020f03071d040203060d03080901060305030301060804050d02160b0306030c040204 93
    0xa0408001070090100101b640e0910590380c40d209441d00504401901c1160000009002c0612aa08582031548010446101c0722480e04000b640c3c0d000900131080841c004002184592800003144001c480c00c1c560054a0a0010f010300400b80022001c046015a0240400300c0090125580c1c0c0019044c1c99000007941450160001c0c15a00040c1108000c8240c22079500e0110325082d1000d540100202001100b44500c02400c83e04250b04203403081c0c1c40c500303059866081040510042c0546420320200b40466625042d80364400c0c802a910b05641c0040411214a50a0209a1080110001040142420007003681a03c00741d100321066400545000e5640c00070003100c1340c08029011064500b14114644100411801c03044900301905001c05440080c603004000d400003230245a01c0303000c1e01e0722942e492401508035901500c0c1100c0e13502401011400861001840740c103980c3c14000150300251610364019030550014100311b030540103074a214401c03502e80e400203100a01c1c1d802c41030f480c100303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 7036895 1250 7035645 7035647
    0x6090105010b0a090501030203100e0c04030b0a0c170702070f0e010323070b0705010902040c02011401061404030305180307030305130e1005041d010f06030606080c011709010207020d0c0501 83
    0x159050b08840d01d04101407021141460340502d00c40e00342c50742800d006a030b0303448840740d03190b20071900d0703008a41d103030149020080b0010f10740000c1c2088034030038501e00300c064540c1041402500c0c2c205803284000b40303820b0b0b005051704041c1d607040c5400030303204d0050f51001f640f6020305215001ca00d0b0040301101c0040381c010420800040052001c030705c801c0702040400c1ca503417030600740c54004a1096026481000c03840c5800c2c45400c1d403002000960003441088003000f81040070740a030104a8600c0e1005014100006a65014145007403103d00a103105520b0581140e0701903c00d138109104070203002034054080342c0c1a4804202d064042c5009442e890b454024000700d00d4622012908101440401d050502100d01c03201c0000c0f5080e04c508550128100d0758040e04080014002d00504995600b00f90400c0e29020982d800781090303a01441d0700b0f11006841d4003e495484256141c0340c1d00003100585055140d11420307108a400a845030009841c0c80c0b019000501c43c048400340c103842c60f066880f4100019 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 7038145 1250 7036895 7036901
    0x6120901050106110303070905010302030601020f06040c03030e06040303020706030906141f0b04050102060c091203070b0a051012120e030709020c100c090306050601020a060501120b06091003020d080409020c060901 94
    0xc0b07013008008610354035010900501c460240c0c4034441c1403680200224810368020700081c640441c124040710824901820320784110417042c40f056012072200780b003d9101e42003841c119810380340c01d0340040491030300c2d2080450081c04005000d0720816a02c0c03101c596108515103100d4040c4241c000e0b00c10f000c044940d0304181840380c5030300101d00400208010452a42c021480507882005011843c2c6c41e59000408200c0d07030100240c0009150000240312010008040c811901410b10038904010030f954421580c5001e402c940144400c146107602090001044500c2040c0b10050301d241c864444060100400d10306540b9800201c8007640201303890b110107404000006901140c96824403080e40c03000406002c404080c00003030f01c950344500004205074004c1013800a403603030102042002e0b41e503a03410007080034110802269500f9181000c903000d4548a48454095800d80e4000140c0c1c603c0c66080101100c2040021514a501808001800030291003e003072084414006040c1e180b0b04020003031700b1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 7039395 1250 7038145 7038167
    0x507020f090912031305060106020a060c020106050d02040207051f02070615060503012303061314061005040b04060e0403090806070207030c06030b030115060302040f0e061302070206120901050106 86
    0x8404207020005644000200e03407041502044030075039030307440d103041d4030340c0c1e0452400300130b49640708603000000d4030381c2c2c0010141140c60040108200b0054040000c80c26200c0c6d44c4252540070340081d00110140c07070507500400c2c810344550201c03606060f601200700501d00c0c1381d440721428294041060001d021490048191030f04403500d51000440c00c10718003810070300043c000c0c0070b074550154000314034141c4420014405e08100604850442c90200902c140c05210f146085a06284a0b25002c400e0303580081c4050194585150308004903042800384401040399008040e407164581500249040c0c00300c6211b03024601954030100c0e0242484c182524144014040f00c0441d840788008001080d90112040c064821504d000300743c80001034002405007240106041d5210307000840000e000d03400d58001c0c0300329840c1c00804c10341c05650b500c2440300c03004211485900091030103115580308843c0d034014071003507100a02013400d00312416500b2900c80e01c116188081e80e0343d520010b10103141c0108100b50 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 7040645 1250 7039395 7039399
    0xc1101060302030d0e030304030b040f03110f0c01030e10110306031504080702041508100905060a0204060c0602070c03080c03090102010614030307120e030109031e0212040b03070507080a0507020f 86
    0x203100d1440c1e0101c0d65035840c1070480410000e412070b080049944c00d0045078011a002110040d4604003030070140c4006551007000c9002c180c10008020b002200420200d0368802c0310009481e5588034040150003504440e006100e56005107085d449650000344628040620b0b0851043d07140e14201040c5807820300b405144d900420304050801000414220848203540d0341074030b0115054034840c264100c3e120160b00700f49a14001c00d501014405140d501561a02c3d000d07004482e001d03103600c0304000803403045028400006c2c1e580e03072044005c10099001860300718495040b01c0c2004c2e6594a0720002900010052402c1782c0000032291900d41e0709020b10006482c40500d00c030094841f0100107507582c402c00700c00408000705154480c0c2d1990044400404191015000780600c2e907036072a00800005014512554403034900b41500443c510000f0303901a204078072080780749060304040c450362280e04010120010044d040040c10000354071301c0003510521241da21010340356410343c410000c00d0248566214 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 7041895 1250 7040645 7040651
    0x10f02040806040809060f03190507030b0f0405041b0b0408100204050109050f01030e030d0209010314040203060403110f01020f090103050a0b13090302010e0102070b01030201020d030903050f031503060405010c1101 94
    0x20014071008201d05410a6200e41060360b1804180301281041c01055902c2d80c003500c003c4100021441d810010801030912038204218541d6021802d908482c0302282086c1c002580c5444529541403542c0040c1c0c01500a0640404801540c1c03050080650a038002400b4900e002c1401c0002c41c2e0100864081c0340c0d103000d010350504e802c20000a01405407803086511548603003403595120303406a8840c0d10b1200341003041d00e0307a400c2d0b01c01020000c2c0d84000180c81c002882c2018070041c00d00310789822401150b006010342102d4546807800c07980400068140300081c002c44550030b2081001344020f02c148822100160f0321042f0715400501280c00003041c0c0311344107040c2651030003203549460705003e0311003041e000041c0324125800d04900421114091922940c0300141100c01c3c444527168542c100d034403d90890388000b003841d0f021001e40c0d90307400e00200414024417007121040c0081000d50f41c0080c0c0e070701c002034004044500081c41e00c0c1d02030304c2c29203850359202403091110b503000000002010103030b4028 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 7043145 1250 7041895 7041899
    0x50106050717070b0c0c1006080d0c050f07030b0a0608030a02151003020406080106051c030804110111010f0606090605040e0a090c050607051b040e060402090405010f0c0302070203010f0204 83
    0x14206124541d40284108810340750050112260410b807854250050b101c80030914090325100400d500101e4500303001d01ca422140ba001440301c4c01101c080d1407a079000b80c6a0300c1e50744031f403d9580405c1c0c01001c44031400f80c2110210382ea0020062500107500620a00c2000d090016410044414035002101c440c1c004000c03401e025a00081d8a1140540c04568802c1d2551241038100f44c00c0c115800095205040000000760b00704150011419154102d407000c4014105d61703500015845541c4005001c12014030009022484260040302460818142035208440000a00d0308694044214000300c6e655500b0134419140d100c460440038217100e082562600b070800c0001090f0315002050040c030907882d450a0810003502401c4840127087c0074119980303032941468030644038040c00d44107644243c030044c81e860b183c4c5418000c20016a1105000d8152920307140c003880b110600c0144103450302d40d22198003245d030440c03070301c2010280a1143c2c3c00603154281b510401d42521411440c441e0221700511003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 7044395 1250 7043145 7043147
    0x9011208031b040f14030c04050103020108040809030c04050702061005010f090b03100b0c15070804080a0f021501060c1e03020309010503090a050706030f0509070f140409050607020a0506010801050106 88
    0xc481e005107a80c15402080800240310704824420794003c059055214100003d0b0b00d84901c407030305e43e005012003d80700c00b0108802880103c44007440302a002039041000b0501041c0782d24014005188090144ca0003110244081030507503270b05440176001a40210b04111101454826000241409207840f503111a441540100443c1c254010104080000004904800d210303080341c4005112a02c1c1a64440020540b002e48a603c90741c1c180c0700c51411000018100c0b0301c2000490312590340410014203010040c58212040800f03407c890341584280004100201c206007050b5008000359920100085014a01001c141c2d03026083c0640c100b50448440e00000c1c2c01005660750b2800a01c2e2070b58a0f0798078071651038a0031103c0400602940100440030885a905411016451804003002e020750b84451250790b03076850080c45060b4144c110310340c00380100c520000903503451020040c40401c41d0764044d02c40a081034015100400580d20604080041240030b0041c3c900410a1400800082d850144 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 7045645 1250 7044395 7044397
    0x201050402060904020a0306120303020a0f09080d080405010207150b040b120a0f0206130608010e1501020c010e01090503060f06040506010f0804030e04020d05090c12010204031112030405060705030909011208 91
    0x3c0c480e11458010070b03003650f0b8a220394850f070001d081c41d4202d41c40008080c100500290b005442070400290b40034181c501d0329000c0d6141c04111039a907001440c4a01640204841c2d000001c0d0084860355002c11081c1d01103102e5000d100c00c0300384540000a102e07a00c0703100300702c100c41d251184903000301440e00c190140c4401c045141c2145641000507400742d0140c520015811740700f403038244501140440310208865502004481c185c4400c41000d03100740d214800008013201030b150f0340300c2c01a4401d501c040d141d944070703a001000568040c188801990b0315040042d041c0031040700c1d40b140082c844401c0003a40d180030700516802c10f900307003800d2401c0c0181e204002e0000000400c05005d004012486000f81e80780e0f42e0480c0c01c0c602c4103440030445401d08265107074031100c0244245115804020300420b5642041c800c9404507680709099210304403160043c07005910720151070046d180400d10000420361540d900034445941b040024660303502040c800c00640352410782120941009403401c840005a02c20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 7046895 1250 7045645 7045657
    0x1031b050318010902030d02060a0b060301030203031c02040f060804061401080303010e07020a06020a0c0c0f18050c0705010905030307090b1201050f0f040c02070f090b010504050d05030c01020a091401020105040206 94
    0x228002c441c01c0c2c8484089805040c00c0e2500a4162003201341c03d1064607808214940600c8030901c05200320f00300c1e5010421940404c2c080a50715800c108a1001100e4007407046e403c0c800505030000d4107003507540003aa1030003c40c03540540042211313035040004009003803140b0301018141240281c1154180312040e0743e24003050241080c4119048045550607008100f106030203603021100b550f4407496010000c1c00c03005000740c2251041c04800b00843c128450400c800c094034080d1903241e1880c0c00410820001d88070280c02403420b100104240030105100f0f0154041d032601440c004c2d55030b420005001844044a5440701c24204000d02416074402c001201d45411610111840400d10b02c000b800501001c409070390155001c1d160031000d0b000c05e5004511a4125a000c8204401c00b40d569082c03007080e80c0a4284c43e90014008000078045403401e0715000b078207540180200c82c03d203658056441d08a9010581050120b26400350800c451098140c505941c00000e02c001c0c015420702d9030104281e40554 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 7048145 1250 7046895 7046911
    0x102160308040321090201080601020d02030a0e0607050a0303060812070b0105010309060f06030c05010e0105090306011a0708030901050114040e06070305060303070b010e0a0501050913030503040c0504050a060501031b0503 97
    0x4041001c0c544a0040103000c81e54000541d00840c1d0b0f8101e44c4c0004080d28801280441d481400003140b960010a04440e006560b03009549080620b000c00c40e4000680a9042d0307004c0028000e0340d012400400c1001d025a22a07280040c4180c145004d652500807100200e1400c074000f0400040020f009020590442e00c0a0034042641c400c00d20f04500682107091400c2910b41c0381c4003000040c005021005011100d0a8035446011a100070045505116144501d601603001800400648188031000401c24054021643c01c20000755104d060303a5109039510700320740c2c0d12a0014000c51411002240c1d0b00c0000301c2e42001000c0ca61480c8540300c00008118405242e0b4400c0083d0340703514144115120164003180c00d119960711010522841e410035550701034090310740310010400303092500d5024001c0c1494190100c50860b182c0e03040b1119480140f08840c562200200000c041e21380707010303440c000d014480c2c01158090400c1c0004089402c4c01204c1d0502d1071503c81c1c801e0036035030410110b80e0801c80b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 7049395 1250 7048145 7048157
    0x50306040c09050a090503070b04030e0f0a03080309030702090405012004210305160f06061d010902030408090406060c1401051003020402090f0a0308040905100302011b1103101d01021603 82
    0xd0b0130b040200500040001400038000011201c1c200090015664440c234441d40341e441300100301000740011505030b485000d4009800301070520108590a000d15071043c00031046a00c3d001c81d950204540400650b000c44030381c1c0d1103c8800180d4540401010850028205601d003060700d0320280d0040d031110030f40c0341d0744c8100c0b0b21660712013407501c9042122482c604a071024220601e80e4944828400c900010aa982c0c0e480c041001c0384100c1d00320a102c01490003242424851303400d00740c004009500140c0115046072007041941155290350180400400c030f80d499014034a500741c14101175002e040c40c00407000f649003e080180c03c030300c0d901c84202603030b806450050b107540e540c07000b144c0701e84819500e86c1e502446a010010400ca00440100140e5004e05c0042c4402d0b181d0f12080718580b55a400300034041840e82d0340b81c10001034620609484240241c80c440040d4644a01007410403540241c80102d0304d80310b10910183c0ca0768520b8141560020744003c500d081022414454103c0d0007150090070412 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 7050645 1250 7049395 7049401
    0x50705040519030203070602070602100b102006131a04030816050c01021b0d0905010503060603090a0b0c0d0b0a0b07020910080601150807030209010c060b01030608100203070306050306040c0905 85
    0x42002c01030018580c0502282c94440d01d448019644081600c1084010300c111140003208000e6800340401d080f00c094104410044910304c1540e00020040c1443c82070300c040f41e4008840001000b584d03004600b8070380c2d245d606076801c1c00c0201c4162610118100000e004078248400280d0250b24142e01c80003043c1c001040c4010590203c1d1346208005c1c200c042036001251148030f0000b140740010403031260310102ca514030b880d20401c1d50303000600d00c50503000c9402400000c2d02401c14500441e80002004250f6401a40d00c1e5070b04c0c9003a10050341c610005a04c0424141c0f40c94a05123b140c4104804841004c0014904100d4405c0c3d4401c0d2100203001c1c1e40e44c2004904880d480300c8030b42000e060940151105907031940e20100c010380d10001304500180600001c030300e0850080c403c6440307103031060f500c80d00403840d203407a000e01428408844038101580c400d4009980c100c00e00680580b000d2540300560b0347e0030044801001d440d06074105038420b4000b90240000210400ca6590484013810000300c2c1c4c0d03507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 7051895 1250 7050645 7050679
    0x1030e0307020a0306230106080604050705070f050d14161b0302030a0308060102010c030e03160c05130204051002010b030604060b04060f0602010504030906030507090506030402150c03030a0c030507050405 90
    0xc010507070300a4000c200700102108012140d001224080d084440400c11450001c50700303c2c84034828070800c00807550880c0804d1080c18036030400c0f54443c4150400c2d503e400c0c42c60b95120310b800300003031090b10350790020118a204580d01c032070012840d500c1c001e586410704104000f184480c3d006120020310144002242d110f1001132400500f0055800030141d4a02000d03608000d048a40226001401946400b00600459000784581441e44604000440c20a444003070088441520444160b80e0703078529010005180e40c1d2040d042510184810015840f10724040500c0500400c03100d080095904110b100421a200003a84562050b0060700c0800c40941c02c5000c41c0c014501c80c3c204030380b01e4220040202d001034054010601070b03807095580308102d0390ba4900460440d00c0c1903910000007210070070200701515084d0051904a80003c1c0b044040c0707096600b94428551160030050000d40001c41004182c00c228030800c0c5400341d090600b80034502d0140c0d40100f040c411809410311549031030b00301148117 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 7053145 1250 7051895 7051897
    0x503070503030a232709010e04030f02010609020c0109140307021c06020708042c0105090a02070c080304031a0106030b06030a05040302011404150c0519030e030c07060c02090c0310030201030e03 85
    0x85066800c0b0300c1d901c0310074043e4454000c2400300f920740010417022251680d8140110301c28101c850359000e88100ba11556811241c00203900c0c090000c40d9225400860341d0700052009240303010150000140c0290340c1d00d40703100c000000c1c151890103600248190303005a01c904910b50741d0850209580f0100d00100e1518a00a0103080d03400f6004003c041741c0400c0a400078040020031030509400008448008500d00307882c048240112a04108400042044902a50046c140700c0f88100200342540340c48107080d0345141c10550080da428801c0c510a220b0002d00c4401c0302e409000305d4501840344226001c0840e05611000e418080e95507a99400902854402c3d400b000d13903003803034600f000a6270400c0e0070600d82ca40718040448050030302c1c05403039110a50059084494411016108a070f8464180c01d05038002d108101440701d00d40400c1058407440001401204040c0c00151100300102c0041d0042c041d802e030300100700e0004580100b003840004003540403035000309c0307909290100d01d0340240c841c61411 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 7054395 1250 7053145 7053197
    0x5040b030a150b070507051203040905100501030c0207060504030210030e011e060b041a0a0c14030309070506071a040303020d091406090604030f030b060405090103080307090503070503030a 83
    0x144600802800503a800e41d82001c1c4102004a8024400c5034441c2c01140051103650310040c52680324840030065401c4c0410390000200d40c60007034070b0034541c8d04c40d00c41059403400c0314034500d0316003c00d009001e1580c151186210303608462005001c05070600030081c104e4407417400042e11400c000a65044040e100c0e40000320b0300c0055034024000700900300307a5030200880c01c900180c0c10908112001c80e9504218081e542100c0902070218411455001e424007180d01919107407041054101600c6c02184140c0c811020884000004583d00d00d03201c041141018210b801440c4182c80411010b4041800c140a1441d04620702000c0e0616032517910f025002841100d0403d075615007402e40d40c40c184503e0b880010b00c6c58882806880e11541e800c0032241c0c44020444000300071480311131419a5130f134401c2e404150b0202c80038020310f16054a4800158040070301f42c2c001c5a00f05000000c100e01d075503000202c000100410b8009101c0641880c0000e922401410301c11020001250400208800704183c0021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 7055645 1250 7054395 7054409
    0xa0b0c0d020a050306120d020a02090a090206040b12010807050604030602030916080703030908010c05070b0c0d0908030901150b030705090d02040606020105010509070e03030904020307020a0605180f0703170304030504 95
    0x5030707590b003014003d0f0581d0000c4038064800d0011a01c05c880c80030003c0740d510341a116540c0640417030f01d4640e08100507400094103156900d03544800940c0161101030080014115404210340c441d500102640340c2e10905801c140c0060f00000010482515400d094805903a070003480903849680d845600d629000311542c0c407982070400c0050000301c4000102e552026079000365915268a5100e0300d07a41c0c02e884075a911310000450400c016008034403890301003600940c03244c11980c6002c0704c3c40b1441003600d1610005555031075000040c0003034280c0920801942440c518626140d940c5081c220320b481e800300801030340600500240a02c0950b40d41c04031184030b298028003c000c00e80e19048000c1c000e04090040c0c0e03008690710804104914050000c00052800040044d4030b401295400c0c800030350000f030310044c1507201d440c21172800164a40149803080000c0d5008800c01a00804901e00d402507000c01d00146411114042c008242111000300c0340d03106102d4a680c0d61340f91417800301c0b071912035a44148 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 7056895 1250 7055645 7055647
    0x301020c0a12030c0302030603071a0403050102040b030f0703090b04031101060308030903030f0601020a11010c03030902041a0108070f171308030f0106020c120a111513080f010506030a0b0c0d02 85
    0xe401c0252501694602c6000ba5904000c0f42140400690480c031040c0d030265450ba101400401c5901c00c82444500c40344004603003103040c1079880d51940d080e1f0704035800810414070088100401681055080c540c40f000a18051110040310b4070781c403841c01c00182006e010804044658518034070f003500000020355001c03082654038501243d145440b90000d4640c00d240c407403030784c0120f4019031001501101a036040400b192518002030f00655940c030380440110203141d1102d8180c0b025a481d13101d080800b805d8480700c0300144540c4030004007440b500405440a000100540801e941d91003050754650350340007404074415031288681034943d04544c1c0c4e4000c00400e000030401c0841d00350314408078120f0b40a074085030108101e0004014046440c440c00d0400b6030300955105001ca10106040210b01b64003601100201101034610b0713100b540045401140c2e03c60b007003020484a403081081031212880003008002e9824404002629400711440140259400740d01048102c0000400c854000821000c11 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 7058145 1250 7056895 7056913
    0x606130305011a04060503030d0c120507030e010605041e090c0e09030406020d080106171005060f09010e09100e04060b03010204090504020f01090e16020703050a0b0609090307200301020c 82
    0x300e010b4a0190210743c9010403800901c500da00301400350000f900c02c002c2c095400c1c1000000d0102c01814482c8120303040100b0b02081041c1280b083c485d20380942d02e103070341c00b01b05903490b01e801c03500751080c5900c00e40c000c1d840c1105002400f0030a00f1808144203884902040041c810b050280506078950030224514070014207201c203800c0000020022078041d80c003614809003403a441030300c124409100e0840401c3da83e144031402a408003100307503803008190305080b2400c2c0c1c136207020911a07086154000c02510300007503880120f6802041620f0110b5046482c0781081c901402e82807180001d0b03100301940d820007003010804103c00e82e00200124100500210344032603841e5100c41c00b03080113941c2a8004d45140a41115551040082e001580c0c010800640c0c192540e5100c90083e04020482c54110f0007060030110009001380214180240904505c5081d400d0500030402c0b1a000a0700540c01c0398010408080018a095400c0c1034000400100300c1c6807000c0000400d01a1184003030040c654050101030f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 7059395 1250 7058145 7058153
    0xa0201090507060e03071205030d020304050114100801060806041208060102030f0705070303030609090c1a070f0b0108010b01021b060307090905070305040303050c0c06010509060d12081b0a050304020906061303 92
    0xf03113224603004a04a918940d0f44070642440080403040c05821900304000300c24001105400842e0072500c035000004c7d14008110003075401c403030705aa1689400c400d49208010212003401280d0180c170031480a40445c1c1007560b42c00c80c0359102d641200042c80820760005119030f00074030a9034112900611030664032010f615120792030343c100d03000c1107002c41d1600c01d01240c00411846420310f4a80e01c102d100d1309050030b06802c840c9905000ca88030f60340c401d04019000c001881c0c854240c2c2468450385440c4001c0d4101032405081d2100c055205045600010018001c034a141320b45007203004082d182d00741e1340d40301c400742112600e00c030703410a15480d410901030142050b0702d680414411400ba03941000709880c2c0c040030303600910420000710100d0340480014002e40c40d00150040d0000d400900302a91b0407543c2c1ea4503818400e03042012000f0884010401c250122043c600300b0340710040035110740c036110820300040c2003408050006401030312940e00240154031054129580b5404443c50760142030303901d1034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 7060645 1250 7059395 7059407
    0x509070509042702090405010b030a0b010509060d03050f181002030304030f180e09030702040504030c1e08030a09050a240f0506010203040608041a0103030c031d13020a020109050706 80
    0x45918029803070310300f40c3c1048001c288105035000c0c2601d8254203d0307010300c0c1c00b00026160050310595884d5610b1510b42a242c0c1c0030800103201600c00c5125680303a40c900000c0161010009100c1800f49980d1501c3e0b9000980c40011210324030a180a06502c648802e40044160103880d00480e40100201c07060000154001010f98422031295603100f95120503004100d44646008580c4101200b801c0e6040c810308c91150901540078000008880c140360007a000502a5902982d05070b0100c1d407411a00d02c00e100300030300c0c1c009078541903040001e804c90003a076036110140b20040503e505c2d6551001110100071041c000f42030415040405101507444160740c91310b0f41030713544100c41c2c000d0f854048250350100303842c025144102c105801643c20305141440036a07074118020402c0343c13102036011840d811213000c1c2440901860199540d04062803d92401404060718082620f41e041499408501e07103986040c5480c040600c880b90141e111000100c080c0e02410064000400034050003e0109801c0d80c000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 7061895 1250 7060645 7060657
    0x150c01060e0c1804060602030a0f03020f1204020907080402010c060b010219060605030c0a0509010306180b040b0105010f0809070b1c0509030d06050604121b051003050403030c020c01080604051005090705 89
    0xf12290b90341c05640c0704010071030760f01c0d20500703003d03030030500490031818028203840c4004003003400c0c0545410803281d0007403542da10202d20103590a20a009000a609010780200d502034064140006141050740010700300d41403428004201540352070000301d00ea4828001c0d84400e2145800b0b1810701103151404801800706401003a000b84121214001a0303d480b45124049a80141003096264211b8a6000241045000c48500d02c00541d030050000342d04e000c04184107602450903024294145000104036840b007090b02c504204041702070004581f4007042c10821030384081d80203035075080030401001100c601008403641051030042080781042010006056200103041c0c200310340c94640c000c00030b0320300541c02a410302c1e00e1030b81c0140e00003481008043c3c04002c03244151001003035840300002e00e00c9581d60107aa00198070b400500c4201034050140e0142540344e800070307140031a000e600081110344006c10452155440e500410050300342c800d600b201030040686210068900620090300e503074440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 7063145 1250 7061895 7061917
    0x60f0106110a02011d0d23010b04020f09100311040608060909060907180906050106030902010809071a070f0609080403050d2c1912060e010b150c01060e0c 68
    0x100741e01200c002408258204000d5050b125008031200380d40520440c01068052076800030000b504000101d1103000030380c0305041e03029244603000c120042d85035080d1070213070080c50300640c014041107040d841e618041e10101f030000d8411140d015078500045010348010303100410000d80003c0c1c04117078241d104001c9c500c1428107442090080d00c40300b542079a640000c49282c0c00b1a080303210f040c1f182c403001450005203d21926404610708440342c950300211070080e030000c03002ca66034103058800c558002c19040d03440203000015108039460010300d821100401e035601e07040f0030b01c0020000104003d0720030101a068006800f04060350240ca4460b0250380321b0b0200365903d01c11182044100f40c030984120a101d802070701164101007044003ca00600f48110780b40c0d9000c00204000c405508541c0c001c44010480c9801007100306465051038400c544110341d5843c0c859041c09590304d200d807588041c00c40984500c0803a039582e41c0c4110100c50040103543c00400c0c046d400d000901c40032982000c0078050149030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 7064395 1250 7063145 7063157
    0x40b0a090b0f0f0105090d03020f010c08070201050603010b130b191d0c130b0c0a1205040f060302030603030403240f020306040e0a05070303050a0302090d12030605030619020703030608060f0106 85
    0x421820414980e81c0e560f0314500048040014181c141003240c0000d81e250b02c41d004481a5100b203100c1c003030035203164880ea0300008074034000300030b02c05509024450b00540107800800c00318540070701050f546464110148039642e1549000c851540b50710540158000300c0180240c0c8054072008042110200d865130220181044000302d040d540e040c1044846c00c0c803000f02c010711700d18640031000c116a000181d4444050107000702c0240824084640070034181b03600c0c0c0e24144c0d5142041c5500d41c031010190055000c2510500400103142c90000485003640d40000140c41c05094240d0f4608408681040320342503281010f170281d07801c03803407a0059802140100d40070b00c0300c0e251401d29907030750740c0030104042c100b684010410030209020364020010403090f490050f1400180314013089001560890803036505540b20131034a003d5600d03101c1d0102820003107018202c40d041011910031512044900b0f294070690000b40d9004160080d448003004029600960756503182c040c0904003000c50911414010542c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 7065645 1250 7064395 7064419
    0x203010b06040b030a090206070f030e010906020703050709020c071208070309050405090a030c080d0618050c0f0307050a02150a050a060b03060303071e02060304050a0309090605010504050609040b0a090b 89
    0x2500c00709072025036a890340b4a90441c0d480480e00c1c1c003d01104502660801340410608000c94500414161528045d0720794400416001c0001031480e041c5078488421500301a0003030001070b02c0401d81c20211a1010009038680d410f81c48010b0410819611a40d4801c00c004c0b00d0004201d42c0c86c4c06440308500a403100440c803580d031014001071310070844a4000d11b4200032080c0000030f000e003900242e807030f0242a41c0c2c0c0c01c0606031004402112003541002445800d4201c00c162844600d01602e03a018491100c0c150901c50395040b61001400040d03b95414010b001c242004040d208200c1511345048000c2c00c60194200812948028901a00c003901d141d41030031000300e02510441c04403070189001400039031a024140e201c0011003144091940480d038a80300c4110007595660003e54002e070b0141002e441c8003151441e01074404261640b10719155820607508118170f87c0c105068908070395083d105c0540e15200c42001400901d140d520325031b8410300c1030f4004500308003254081c1c140313181c00313031101c1000302 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 7066895 1250 7065645 7065649
    0x40312030b190605130b031008010b1c02210102030a09120207030507050f03070e0708090d02060105150a02210a020106051912050a05010f0f050c03040b0106030b0109080f07030203010b 81
    0x803000342c0d03444001141c0502c204146403244005040090888061180050315010403c54503441a42c00d40c64840c0341c6001442144000e2180c1e4101d103404031114001c00c0348201b820304402e0810300d40684560203102101d155000b01000350410900500c001f10343c0c078030301601504018001e06c0e0b03099400091800d003e55034180009600c000380d0ba0003c1c02028514901010001890982884170742c241c0200798001490727030220740200740a8911511803000b10315062181a2800042062040455100310010026a1209060380f02030400ca026410741e10105088240d1808500c2c20103d16004601c4a4402018100700d014201c0501654024486140d035030080102c0092550495a190343c4081c0e8100501060302c612a41644d110b101a1901c1c54515143d680c21105002075405881d51200c3c9515165022481034a40c81046402c3c900c2c150708054907054480141400b49205266a0300b80024160780103c21400040011504456559842b070600c00c0e15200c40303100880c0a0340c20022004054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 7068145 1250 7066895 7066909
    0x10603020703120c03060512030a0e0a060503060904060b031605090705040803090409060e0303250504030b0403030e07180204030b0c0301031a06010e180402010206070e0607170f040312030b 83
    0x82d030980d40b0140c0c03405200c0d6040b40140701c281201001d1651340c0c0c000003510307151180e82c0301041039000c000e1602c0300c801c4000a0b02888061441a01c100600001405215004070940ba04040c007070795100b1244d5990b1405000074a0440201c030343c5807040285840f1119a881044003d461064031007402e00d8880740015500350045002d241c5064009000b0803841d401c00780d100a0301e543c0180804141e130f0148400311411a801902c203202891080c441160b80c004001060b901810707014908946010714545a40700e180001500050030580c48281d8221580030801c01240541800d1004940000d04050600d009500920080f5401d403001c00014061440c040242d078101c0703410194110290581c446080f0516030010615410301508031b0450400c1d440741000785070490a44020042103040600001e0300d0070800814900412a038280001c4258403010191104070b40d101c501040028100004900780d40182c0c44500891300d000300f000424448003580e1600039070202d07201040b00c004140b0622420b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 7069395 1250 7068145 7068157
    0xa0b0307120206160b0c18060a120515090106030c09050d0c0b0a031401060905030f010504030915050c03030408070b010b030103020a030b18151012020306010e071e020a0b01060302 79
    0x301100210260409900420805010780c601d4954800aa170302e05002e004181c68004000038040369000030f0720741c10044a83e0084040b5500340c1002c00f0704000806810380350325149001911070b4007140800c2c2d4425250003500f54002c1920b0303019078440000032300403e401032000000815042c0000740d6030a11810407203944d5000845050518244210b9020640c000440801010740e141c10409032032404512030303030180019980e0300000c5460581014a45075040000b0009a4074001c10b000c0042d40202c0d1000865000c1004010261580d050980301c50045081c42041c5002c00001c003c00c10401c41c0041800d103200b207005485a03620b811401502e40403d001c0290004480c2e9010b00101d808280450303440221700c1c99a500310450a6031150030910700c00c14035a06070400c1c00900c402210400e100e4005000c8441c0d04a00c068603e4000070b50780c0d4018426885081041c01c08038202c144507000404604c03030f0352504100c0c3e003054580d00a540e030b00da0241c25a400d50700b0000216811b8440c3c021a04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 7070645 1250 7069395 7069409
    0x702010515040e07060806061204030f0f051204030e040207050303040b0a0c0c0803040201050304020d02030d030603030e0102030a090308070c0e0c0403020907170a0519110309011802010c060b0a030c0902030a0b0307 94
    0x134241031141c00c2d46c5011010740203642c0110705000d494111940d00420600c29032003580c54990480000c2e40107450445842c0d0840d0a10105122660f0391102d8500c403258010f03054034101c0e15080c050340c04100288140403020b01203010001c2008140880112820300440740104100181e950000c002c44443c1842a0001c00f06041080840c0141d84a4005140c00c00c4c0001c1440141c041da07a80081d180c4000490600003180d20342c40200b023030682040d510540d400080c000b45207468141003000b400300b0b890780002002c0d0400869010180305502a0080107050781d406030143e1810400d881c15180e0b08a0300c403c130b11591844001070840d40c800c0c81362140c01e0041c0340000d00f254032100040000f03450700902c81000b10001228440c11114107000b070070b10074070032040019502d043c103100950a682680c00500d840d190416205c500507603001a920f410a9081000028144400c8000030403214080e80b01070301c3d01d0b450000202c0c0302079040c1e000f5402098103801c100455200e0303c0c103054407a002c0d4400d040c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 7071895 1250 7070645 7070653
    0x30103110a090204060e01020c0a08031c0209030102030106210605011202030405010902150403050115080a0308070509040212010e13020306070c03020a080307020109050d020703050712060b090702010515040e 91
    0x20014001011400c0480d100038149480c80c2e45030b8203400d049801130340c03000000680100f040a21560140601649100c0a4490780616410000301ca542e91040a0740c40141003016a40d0760b0600003140d05582c08000c00900035035aa5a4540c0c006000d58198400c89003c012204800007941009118000440e001a10341c140c102c42c0128a480081d08000c1c03040d40d02d5525020604016600d004800d410900c2c0d601c8455251401d6050040c211030042401e14026402100140044900055220704071076261a20351011364600b00c0c21070392805181a29a003041c008984440500607504869068a01d200403111082e40c41c82200401c07c0c1082034003a406402a40c040381c0d00070f1280c04589d4555019004132552403d080d96079560a5008840c4440140d640b5030002b030812605110141503203800c0c1c402441c08034196115176440c2c0c2154071680810300107016541d010045035811204881d14000e0030140c1c0d6107024040a4041c0004968041c17840c101d12100c44424134081c0302e403100201510000f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 7073145 1250 7071895 7071899
    0x3090801150605180a0e01080f0303090a080702120a06050406050c03240d02060409050405010501060203070302030307080714030a0506010e030703030816111905060a0902011b080c010c020303010f080a080301 91
    0x80d03c45038000c07581004c1101c1501081892501c03545880802060040d008113525850882d510307080851001010149030810000d00066a40020b801104981c210030900d1359050203100065010240d041c510301d203401404415000d000741c56010501c02da01583c401d0007280d031074003d0000d1780d02c4102d42c0e03045072003110495105413403e82e00440c56004800752090030342c0d001603000941d05030002c2d803003064017603119010002004828080c550042909000850070809181e50203503c90000801150401001c580000d154500c5902d08203d540e003040d030002d80c0d0303042184e80a0081c10040b5050f501250780c0e03601e81e540b20b0800140440441303800d40d4a55940d6110101c20740013101c801003141c0304100b04280740d0065041c0900540c0f02100020900040d16109031501600709500209901007080c6401e81c4080541d8002040071080300c0050b031b0802c8481c0031440c000d0321034080d419881449610705a291030403150000003c1d07041c0d51158040481950396291a00da950b258014000e10404040c001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 7074395 1250 7073145 7073147
    0x4050d030509030409020c1c020307080706020a0203120a020703030b010e03100b15130303020105060603040c0e04030311030115021c090b0c030c010906020409150602070b0903031204030903030908011506 89
    0x80960000100c0b000d0740d10b13043c4c0d2004d0000980e006201c1e00d4030a50000071810340782c0804140309094064032400610b091026985500800f40a01a00640010380004200301054402d004039003000d903184901d0400d5040840041000750400701003240402d01e0002c142041b580901900c3c2e10140d4024000c0010140310032565002e002c0281c4a680c010f0310303002c041203170200e0182c090b100e601c03108414003c03440d00e0340c01c0003425641d0180c181c41c0160070030400d010100d1349007401c050644503050080104d81d01c584c6400c5000b0120781100c003007030036008030010802001802d50f840f1021322a500b1a20382511a41740240d4600a60000101007110302004209140d040005006c11101810559091001c003c0980e030170b48500b640101c444582c0060140304e07249841c0300390b411001c21100140099420070700041d580e4902400b4017116500c01041044065504100300c49003840b1440c14400c0c542014070f80035042ca0f10600044002c1902d020010580150501c250f8805e5180324034990003030351074010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 7075645 1250 7074395 7074401
    0x7020915060d0903020a050322150207050d05190602030711010b0307090510080d050316020a030e06031906080604060507020f0c010e010908031602040b010f0207030813030c06021005060904050d03 86
    0x103c100c0960003130543e0342020500c2440034190f0003400b0020b03a05417007074441c0340000b4841290051606035503000c241140080d40010413030141c400c1501d8600403180e03141003142c03070584001c1e084160600011304542c01c000c400c0c4c028500546568440000c0c805001d1302c540d003a11550343c00550540c0c4915003c1056220a40cc8290410111801091080d440d051500e0406004500c0c090118000100344042d03003445004082505049202602d00e403181540c00070702c1250b421031030303500c0703402c02002140c0100400550b1401503802407030104607895688c0c5035191508c02c1103070141ca40501d0314000501840c00842c014820000e2007000d4500c2086400042d50400601800a41040b0881c80d0102d0441c1c810401402e03940b80c14a8a02c0c1c2d5000710744104000d898008044a04100624081d55196900000e2410503207601c0100a07442d00300e400103450507020380380e0021304003405421000130755940104098a5009540d017040c0025076a01040c012b01e0b80081e03c00820326401150315101d20740c480d80c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 7076895 1250 7075645 7075661
    0x4050a15050d0b0406091103030c0307020102060f0402060a0807050409020d05040b1305060a180b01080a2105120915070503071101020906040302060a03090c0f050a08060105010c020105070602040503030f07020915060d 95
    0x10f846200803847d04020038a503400c5861003411650000a4483c10f542e01081100d030b202d0f0403025529101d103415404505a4015200d595051182d8480400ca41d0b5018800b40c4001d080d80c0075003151941401c507114005010165030075104000c000707011903540000031842c94585604500104226101d02003920014610364140d001c2c40c140c1070003060006038904011500a0041e40000c051882140c18034031001d00c1c0019014560302d9804030241070907904203090342e505410640450740395036200e1500d01d003000521210b02c07080a1444003000499900030b4045c50041c0303c1d540c0c8424449901000007400c0b4443c4106043d4130006c103100400041c9001c03402807800032003500d00412946443e5840c03100f40340040e000180c0d41d2880d2502030029041c0500342c1d80050490f000103107020b524100018003014401400a410810001009410300080340c045400a24024040341c0d03503032903402444049900100c40c01c038401c9800d070700807030346d00030103003240316522407000306240d01c0d210002e02800010002a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 7078145 1250 7076895 7076903
    0x60d02090405100311030c13180602030405030a021006030503030a050402010302120705190201050124090b0a09060905090708010501110106050d060b030105060108070203040605071104050a15050d0b040609 90
    0x30030280060751a1401500c3c0a94030030306212003080c0c11440e12041d6241e200d40c00c94000d51202c100c5401d95510429001c003286025103000404d042e41444007000b0505c0c4980c094a082d00000600c0200700d0000000d080d074494035801d903201090412094405e4602d1072001134550350041c0041750400ca81c66014540041c0305040062504240c681e0b00015010215055000b042010070890307580c04420102840d002440c3c4000c106035810442d82c1074190003050041c001d00d441000000d04843d0091503000c0280c5010343c2e4240e15050b41c910000d100e02440d02600740001c7d01e0482c00103490410303c01c0d0138011566034413200401d07030803e00111024004c16880699035900d400c0002010340320922800c080d075005180100d41030351000280b40c2544e04c068240c40c10054a981007000d890b60100a44003552a0361404981d07584103400c3c81c141d020000086103901910700400e00514442a620000c400110851120866903580703080113281c2c05213607000380c2050320f403400160000b5401e5009460351881 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 7079395 1250 7078145 7078147
    0x8070608071b050c0306010504060b030103060506031614130501080613060605060408010506040501080708030403150207020a080606030d230f040b160605101401030207020d02030f010903031109030c060d02 90
    0x25007541441081c2040c20784954204c441e1408042c1000d210850140c40147c60500c501443c01000c400e45100510014103034903030701d102281c12640c062004121005c0c031021071a540070b41310f4461000500794500114469030301d111010f07c50707072454080d5604035144000502a1a0360f008402c0354000c080f40000c40d40c0d1a0764050100d200d03a2200040d1001c2c140349800082c00b0726200062008481060308090700341e82c800c0c00c08100030800041203600f43e0754022000240030b1080114a00a8018004003e62041c88500c0202c2c44040c00944a032003604100c045511002500200750383c041c2e020b03407001c00d0350740200d203900c030041c1c0080b402091004000030101c2e01d03259441180801c01d401c189007414000da149025581484080c0c01040d0300300c03561200c210801440d2030301e0910340d01c4a401d40d0303d041c103030081410015942c42201100c00700c0e03005401d640311f141174540b01500918a100003240402c0c038109034a90442e0703084043e2181c01001034020815036040c03c0401205810600c520b508103a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 7080645 1250 7079395 7079417
    0xb0f0d060923070503070b0c120d0902031005041b060e06090105071406040212010606050a030e10050a020c2506111905010218010201021201030b070c0609080405090708010807060807 80
    0x5010a14403000c200700c003070000076080c030b4205400e0070816071202641f000d00f40300800039818003003441505013086644950751610151204000380c072140700082c0d458040c455a040043c40990005445248940140070b10320740c80149010000148e0302a04000605284000780036090040082c1040541414880d0420000b0b50302d0b07901140c0d02d00d51004203600480c06020031420812684107054050703138001d2202508001008205000b9105002e08042d200d0483c1450381d1070170b111841c0f122094107410702280c5409000300000c3d41c81560801000e203c2c030005010b20010000d1000c0300c2c00c082c0072024918910f0100e040701d83d1703081204009218080d00040c0319058481d0320b1582103591042d8005a11074900552900170b03101041b51142c19640104450030400c05007070b0721f05054130351004c002c200b02d4a41000481300840300e943c0007041d0f149060712040130b00c000354000d08100c800071520310102c1c0e45c40d410200c072041428420201729900c0003009000d814010664039a1040540c03601d0b030282c1c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 7081895 1250 7080645 7080683
    0x10b0303030a060302010816020c0103020a091707060908070501020a1b15080106080c040e06011d060703030e0601050102010606140903160e0a05160507080702040605060403080408010b0f0d0609 85
    0x140c401c2e50350b05a025642d1008004550f04640c07420381c0510b040340108100840940701948801901c62098101580003c2c121042d03400b524044001e091100d0f00b003a410b0300100c603403d5682050380124801b00309035800c0003500f110001a240140c90043e40a880702991030740e140d068200a07172503e5900018041000301d101c8214458900c00d0b40c4a0b0368540500b94906040500f84043c064450450060200b00c288880d0381400d881d07a42003c800c0c42c218100704914441e0420841904d0031403a4084800640034050681c50b403c4000b480d0180001e4500d940d80e918016400c03200544034401c04500420141000305084001030400d05401600341d92101c0d1400101f030650b083c058012080d00f0f40d00c0707001e1021501107032280584c00144203c0380d400195091401420500902c6002800c9160001e0030104545480d08082c0042a024161649440c1c1b48c0c034044005030050f004100056180c04903c44243c0781015002d4032001010f00220030213245601c9440c09800c070b4020548209403260302e000c90321 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 7083145 1250 7081895 7081897
    0x20f0309060403120902100c030201090605070201060513020a020a02011b08070b0f070e0f10020115060e090f10050603130203061f060203040506032206020403030801031104020313060c02010b0303 86
    0x9189020041d00301c81c642450040c1820309110f01004c0903501d81028031006807030b08822416001ca990404120500c014a0202c0c0517000c4014000c003611b0500c010712502c0f0360150881025039100311801c0c01c241103050180c60032400b41d25290350041e8800340000016500a910300441c2013441100ca0207022201d4540c0b04055000308007c40da250010000c00070203550030300d0a113400250900e003a840f0800e0340d0000074000c1c04038074107180c4a6003548440011040c002d611a4984100710607501031071940d03820b07001c1c1035200708462250180c00c280001a408450032007625100796401c42c5880e610a01300010302805400052124942c20a541031100150f60100400740c843c2100c40c1c450100070644954a02c1020080c0e4011002d550081c00f0034421650b8030426a64440440da14a010700d1035015008080c255100d400900214070028000c024103600051282c1601d000f1000e5030401861001800102c1c802114a0100702c40c0c3d1180c01d0b40096603a40055800c0c1d03c8910020461075071000009081d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 7084395 1250 7083145 7083151
    0x2070809040e01021903050603190b040506090304060c030309240501080c0409080318071502030a0906050408030d1109040f020304060b01050c070915030803040501051506040b0a080a020f03 83
    0x45400890034640d00d180c94041c0e410980c0c000802542031100356540f0002c0482052549424592a100040d04030b8800b0001101c0b03500d00f191203030801102c10304240098840544060700c6900402d03000604549002088408036221903603400b0741707600c45171803c40041c100114207d5910100015160f03000d0300f00300b0717031000a101c5100c002450303500d84283d00e40303003030710550003540104e0810900b00d0201b41000b041e01c2c1e01030700388030f4941c465140f40c11240b800c00600713400071106081e40d5040c4d0b82c2801e600101804007428103440f51043d0503107075081510b040c0918801d0b51140d5204006a1030158001d80044049001d0000901d007052902e9001405807103001505482c060f03400310401c41400018040c9d041000c00c00e090a0345845540c035610303611041d02e0302034283c0d800d4454042d6009010700040500081d50070550842d00e900f06448c22901074001582d1040202520200c6540503150240882e0110b03001b101c0342c203250149120b003d03140c444c0000d26101d40c0d01d03401d00000120400031401184 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 7085645 1250 7084395 7084403
    0x150309100e0c1806030a06050604110408030a090e06090117070902040603290105070b090705030102030c070501140c0406030b060405030d02010219080c070305161202061006030203100b030402030a05010207 90
    0x1034502c49905001110700c021440c01d120502080511000342c6020075050300703158120300089025500c0ca030200300901885030b40070106040015000075000c90100182403161240d42d10445120380d100140018120140e039205e034000c40c40e07001042201c4c00c00020040301e5142a0654806c2907031008130b4000c0340c11660041020a071903c101414820000642c5c0380c25480c2000441c0d04143c0c0c602c002810f500070703500020035401c458408a0100301c9c0802609004005c014001d560781d1a08490001442d0070580c02180ca9601385800458540d840c50301d15845125012200c82c14545031250460241009090283e080881084003203426101400ba94040041c95000540c0d42c558070801c407a51003a10301140400c004c040c40c20300c2019492001203441841c1c052030495110015504440c0303158401d640c00600d49010041c4a0101c550045a100c0c4030300030b100404450655101c030194282c1c841111100305c54014890306028444401e4095034105001904540c20030007103644107400c903841803400385c0e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 7086895 1250 7085645 7085653
    0x308040504150e180709060f05090114010c03080703110309070e07050307050a03020307030b0607050d0305010b0c0a02120703020303040308030a060f08060406091e0c03020f04020702150309100e 85
    0x201003400c00380280c41004980b25403030601d440c82c16070740a00071000030b4492150303d00140484080385504020f01c902810b0703100d0b802c11041e540d032000e581c4000044c0c46101d0141245400009142003031100078800d03104d040e161500295140d560848084000400800c141aa1103c9500c0c01e04410005944900c0304040106140b604100c94009403a10080c215030411004000304100b0551003002d490348200c3c40c1c00d0160701e07603c5005090300549180384650b40c1210000c507021041c000002030103c4040c101c1c0d20200580d98039411109242d00c2000403075070441e40440c524030700500b000218040840000e400b81d03500180c0300d81c0040d0459103e80d0007555000c1000c000d000c080d00081c8613500c0100640c15a0419061a003e031007500c865000300090800b5a4800880040c80251083e50f940d13010128085c8000121a107002c1090030024041a800342c1c40311071a800e01030501d4800c440b0f8442c2c009007851750500c03205042c60310543c03000380400028050224080443c2c40f15000320500c007080e01000d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 7088145 1250 7086895 7086899
    0x30302010b130b01090b030a06050607120807030203010506071403040e090d020d080601120e0109080c0d03050a15050909010b0604090b010f02060c040b2a030403020108090a02060f07060b0a030804 86
    0x10340110b05000c08000a4500042900c080c0c2c0c10410b090119580074141589994480d44100010140d0b588402c5e003091000500100304250010000140c40302d0386c40f090815210350b4001ca040340800d0088a801505c10000700b004a8508514001800a548122454a0786490390034000340c0b8252100300041c1d10004202d01c040f0f40600c01001c01e0030580c50070710310901e071003c00203168001c032100c00b9081c556100c000743c0c400b803020b4102c0000359411060441c0d907004040d6610f65910103120140300000d1a0001040c4500b200b4080da4040300b01d075443d00040a41010200a4139440140c070b8080d456586260520080c0c40c0e042c003800051401d24800204640c01c200094040303c401001d90086401510410100b100510140c50603120f1124291740c580300c5201d01c42c1d1001e00c4007684495003801b0b00303805d2851408000010001e880c403e0380c030882261a001c01040d6140000c000095208405001c500780352660300c030241c200d1900070800070070b90740401008161158026082515500400502 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 7089395 1250 7088145 7088149
    0x109060605030d02010504050c06030717010b030108010b0103020705030a0809030409050a02030f090a020102060403031508030327030a09030308060609090f0a0507180506030714031503010609060501021e0115030302010b 96
    0x3c90f00c040340001c0c0040d04e45682c0b516181c0d0b04404045218400c0480403d400c10301c69003400f5031401c04403a1a00c800d507100c02115409400034441d0010540c01c0c240c0c10700c0c545d4071030b000b0350f40300c1c0358404000c6040c414025030560781c424005004803a14401404006243e41d080d0168a0150580c0d03000141d40f820010740e5800a01401001c0c10703060760007145900d0050341d001070b41d40c1d8003d405241c001564520800d8401c42c4468030390000301c5503c800310600c403281c0b14840404042c4011504554215070b0004626070300d90041b040c401c00400e50806040000c05d00850030380d0b90284006104900d4480444005002da42e401d590b50724846040c0c0c0100403001c101d0f441541e4110301c0c10f0178205110000109405028140c2c2e0141c14010b500210105001034015072654078560040d00300140c4a20340f00050000080008803131328400e41c00c2c6040010300c02d051388103030740c1030700c8041e40501403041d102040c0900c80220451942d4082d075075070300314015412048600101851103580089032100c40681 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 7090645 1250 7089395 7089403
    0x302070b060406030807110f040e0106090b010c03051b01021e03070801050909030403030302070204020c030406020a110405190203090a0204020a1211030105010903030f030905060c091002010506030c061b010906060503 95
    0x52070380254076115040c0007040742c2c84180d5420550100c090a14502e500340881c45000401e210141c00c24100304042284180642020003a140c041c641004071482150044601c00d149140203000300f1030800000d020050365001207192401500005032808485414810b9a4401807081c492076820110a01580035800112203004010488a0840d107081007039203280c9903c00c600c00241411b500003411021525139405490031004500d041c3c0e80c9403039443c60040e49561a003442224503901c00429048117180600c142c60040d0b00e6024074004080000c2c980e0700013507101078070b841028810303c0c00c6600103035075600003800d410b0380c8c6648078401c1800400a6406a5244010b1a01155410300c0184000e0b44d204429404483e0540780404140d01d413450294003d2044860290645c01000c00300718800c1070601c001c0c0401d04058808000010030010300301d0032030720240c2d140350345500300781c080d84401e1518002802102e0402204840c0d41c1c003032130004608585801a0450307809032100810410b42ca000c0c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 7091895 1250 7090645 7090651
    0x3080609010b0a030911120a02010206090105040f03030b06130303050405010908010b0f04110c070305030703110606030c060306040e0304080708070806010605070b0c0d0f0e0105011706040b0c190302070b 89
    0xaa140a40c40d410068240001d0040030894800c02da500c580c040d080c451250080f4640580161807981c6020140c038130f003512040421130980c0588120b00c0400c0d4446814800c00d0310aa420080712045030300156411409070030030440c000c0c0c5c800d80900c00c590f2501d0042c1070000080d442500c0b11540d4500d4000090f214525590080d4040d900d880c0100388030382c4071030303a01d01d512a40c100e800050050102081c802103000d06150b14415201c1c19101000b0044000003d2490602940f90f1150101104c12290f80e14001200d0154064000c401c0395481420400060364000034010000310b02540c071600846e00d1504142d1100e01c50758401d0500300610a41844400040c05510026100643c101400503000b4440d03010014122054200040c412524080c02e5500307130806000b05100c642043c4c62030002800c1d01501c070240702d500e0400001031038410b070746246002c440800040c045036074890303c4400329020002c0c000b840c4040f00b0043c0c03107100600c0d40315548100420341ca0040e00c94107030341410f41a0440c02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 7093145 1250 7091895 7091899
    0x80a0e030a050301090c05041203020106032003100f1d0601030b0109140c0306011704060203100e07090b0904201b010218120a05010c050d0b060313031815030603030806 74
    0x2000701240d2940d220044a0655000102c0400c10481186007110740f881182d01580390343c10314401c107000301075064000408030b9000e2070440c001400c3c00c5c1502d450040140602c203501d6402560f03240c2905403260014051001400f400203200c1c046d04007003481c1c0c04070000b216801a005071006108220100340e40d1030140074102020000007061481d455040311000d485c8411240e00440000c1e8642c3c82610780e9482540404058a01c80c01c0903d000d20107500190780c1d00505099004000c16140101c0301400c0c4161080d50300c204100d441c000d0280c040e98085e0b1911908251548801001c03200c6c80041c5040c0702c1000c04405a0381d0500c0108a20f0708040d051810741141d0041240081000d070300071105401c40c504a48404040c9910b440030703498298441c0c40202154240b29070703120040d800101a00701d51100810a00903110034404000c0c044c070049130201100340b0100020300c046481240d0b1650b59584a09500704d2240d1a000740303200e00f2940c00c0a142c00640c80381024420980c0c054410381c0c1001c81 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 7094395 1250 7093145 7093147
    0x90b12010e03030121051509010e0c010207050103020904110403030806031204051e01020a15020306030d0801030c060503040f0803040503030a060501080403080f100506040315180b0c0306010e10080a0e03 89
    0x1044421902e0384018070818440d88191413105904078845281050803e600008940380842c0c0c11a0300d00048004641c04000c41d481c1105042102d88046000c10388400140d0140c1181401c0c540150025080261001d400940e00d41042090002440050010350700940711044c0714a0600c0425103018038416081d1000e40041c4810041a20b80800200e1006212040c49001400c01e200407840c0c030342103145c0900b0f55000440076103403071300c41503000310700a4406a0a681c0c00c0e4000000c1510034402c02c0c4002016844d0030b1008104641c401d401440e046485144d2040da0000b644d142d00046070000c2c3c0e000c1d581c03a08000140705060340a84900002028282050038962815807009000241c0003000d144406082c100091a107402c4900384c040a060010701c00307900e45840b0308104484407803095481040903d481001039540000651101156502007603d01030f41d030310228180c7d00b035000644000e041c88507244d40040c4c42c0c0e4450300030380c03440030140d41d0f045828900400d0701c006850303203228001a542c00c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 7095645 1250 7094395 7094411
    0x24020c03070c05060c060105040b130f06030c06050a1e03061205070501080f0c070201080a0e0714090109050108030724060603020306030606060a0e09060f12060118050705040e060a0f090b1201 84
    0x6020070789070f0442300203c4d0009414440180410b84000300c007111155802e152100c4e00720b03049515408681506d01074110214115240c1805540502c5021800300101d0341121a244460341642103080d4411005d02c0c1c003003211503940c090016280d855400032280e03504030050904c410350344815003c1c1e10603000c20390003007507061041c1082001d2040d0311000c1c1c10000504002002c2c00c04076000040f03d103060000315404540c1c1ca030650808400c1e103503406880b42e04141c000051150b131501410b03040c0c0710380c20051032078044203a40703d0340c0c10841c82d0140c0235407460a40c6da28894128502c990310007009243c0340546d680c41c181c0209814410018040c5100d82002e11402400540c48813a00b440e504040c1c030301d0803040c0c44000004000b1001402010761105000503045212400851214100c1e1180445500caa00421510b0740940e01d00b2510040024000d120402070f01070031821207138101d500500000c1d01c040e00d414640b0704400c0e1941003810100d4443c03100d01014100358541850640a16000704000c0e5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 7096895 1250 7095645 7095667
    0x5030105010507210203090103050c0903060c0304150f09050d090b04050103020d06051203090109060c0b06130e010603050309010905040603080301260303160905030d020a24020c03070c0506 83
    0x4001802014104900814560200007510084090980c0a019001c020400c1040c0c001c0d0369910420702c550009092001141c0c0c00d0440c0c006450300b0300d4004000d00015559410001956003001300269485c0e4500050b540750940f06108002c1202039100001c074040265062880c03500b4440840c64082091300d6204100f6520383c24261005d880c000d10300545d0302c40800e12500d0142c607854000c20760024040717440c4025140000001c00c04882c003a01c615110583e501016500c3c502c540102074a6a52303400d00259907490083c04100c00c4100c140d80006600b980c0600d401d0858070a50011202e680c800079040380e5541c0c0200c0e00d80d00070f0000311000d008070b50566903140e20501043c42031111110001310744c0c400400c2c080361f0040302d00c81c071181200d03103903c0d024108134a502c0b110899035011a82000c070200c1c50b4280450200c00d20784603500100a020801c2d03691806904500d90a211003402450710090307003200c0b40c0004e0484140c403000964071140e03941404512241c10740e0045204400400104d8605 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 7098145 1250 7096895 7096897
    0x30a08010608060609130203060a05030d09050418061505010201110906070f020301111606150e0f09010608070e01080c0306090d030902010e0607080c06010501080601020a0f0f1202060a051605 84
    0x550307180e1404010030348908010510602030401c240e6808a01416600900e40c1680c1c080d503c1480200c0d44128803a0792403040c036483d04559681100010a127400c148039030f04243c1c200401d10800c641c100342d11442d058407400111924003000080c24001c40c10208159a0b09005081503940310380b20031498808007000168a80c800c10400030a80f08180140e50203568080d8841a0440400b002241c0c1e20340c4d603100310400c00c1d1980d0408075103442c41c2c01540d4405000e6800300d4403d584010403c0021511040400c054012000b04103a1240d0342705c0b0404150141c050005030000d2207241c000c20515410a15414100040014218007950054040000340c00c0d00182400200046040000710030703a0900040740c480d0342007810103400c2f050015080041001c80e80c018083c2159075010b844807640c80c0c100440e4600c02c160b40c803170300580c010340100d400301c0e02c070348001c41c0068030400302c014001116580e22a46814000c01031005030300b0000801c02c04021381d00815520100c2500030b00034101d8004030191803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 7099395 1250 7098145 7098149
    0x180102070f05150f0307080a1103040803010306091410020c0606100c03050703020102120103030e030606100e100306030b070302070c0803040506120a0b03010e0c041404020d0803040206070605040c0303090503030a0801 95
    0x12503a46841c3c1e2001d0040c0020881c1d0040c40b008030515a43d21b0300e00005403051405031282900700c0c0c940350340540d01d035000d1010b40c0c1c0515404030b480c03072a42e40f07140c4501c40504441c0750309890304289a554010080c408000c8107040020740740004d0303141d0012043d081c3c1010001004107001d00340582c100001c85510584401103e607240c01c2480d281c0704503090803030090040000d000080c2d004100080309042c0c2020324608150381c01c604440290b40c8060601502c1140c0d96103c01c04509c03030035050140e41ca000c0039030440c02140c070314002600b2962078860300d40000c0c042c0c60f40ea02191740015104103000a600c005c1028100e801c0c0258a01840c07e00800c0d894810101001c01510002000c907909034090f4001c00100240100244140c4030741c090350580310007440700d4242c031603454030981d20f121004448003103100e81d40003042441c3c120741076140e9552640c0300400490b40804104030b0300300019070b9482007a0107070f03018403040d2030703201d0640ca800b6102103a150440d0740b181d030090060240159000c105181 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 7100645 1250 7099395 7099399
    0x5010302030c130b0d050a0b010c11120102030411030105010807060e0402031302030609010509010b030109020f0607060b06040b07120309050a0303090c0f031511070503160f0204020d02180102070f05 87
    0x6540c0d520500c03802118050318070140720f4001076080004001c0c0044014081c0150b1340300040200d07031114182e20701110f0071416940e0100d10420000008070f02c040d40d144a001d0409007542542d01c108062072403c80e40116000c4403400d07440ba08148003400c0912030640501401e900030810b05040c148080c0004c1e00242240380300c1d940000001d80148001c42c044400c4540c003400f208d1450a002d46454082c0c4000c0310f0120041d0702c0c0c0005014a4038050142c02500794002e0045c40c00d200b40602808800d03440f844c1c0648605440703031003580d501e80b2040d005000901082001685035409480c0003d441700842d10304404243c20000c1d4030000c1500490000740d616070500300000c03020540d113402ca11508031948240040c680ca15400014480c1e0007091130700d050407030b010804c4081983c2c6c154204a025540000d04207600900802c0c2d002c0351503441e900200f41c040e02e9a400c14802c03a60004060f070b44542d0a10a2064020030398100c0701c10208440d1001000900103480c010703041c030062240511061203514 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 7101895 1250 7100645 7100647
    0xb0c010f0614150715020a08070e040b010905090405010e03070c03120c0c05090402030a02040f0c1404080d0809030403021005040503010c14030c0a05120106020105040201080a0606090605070201020c090906011809020303030105010302 102
    0x101081721210105111a036030740029500c4600c042c17005000c4501c2101e485000c16801914421149801d208048901c0360503110203546a0404050040000000300215001c0d9a00c4031600200c0204101030030700e040c0302c1c80d2000b103810304600d00179000c03401c00300c0356000b8800c1001282c4000b030744414113101600c03c286c1d08880a596240000b914007134041d840a500f042c87c01c0003119100c0c0807500000e140d04e12075250034800c81c0c0540041d051070721039441803071410381014400300b8035544507040300740d00000c2210480c0d05140e242d40000b04220b00001e40c4401140001030700b0415801d003806610101d0450f03081680e0301e140041000700580c400103101d6001c000d40020036841d05400f98040c0d5035112403424540800350303102c881c064000d08047e5016408143e5040006504000900809043d5130300d965542c00304600c0c1030401e48035600448001c03410742c02941c031501c80903100c881445104068010041200303514060400e8181100c850403031181e5800c1042107809a2000402c40e41110070a06c2c1c01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 7103145 1250 7101895 7101907
    0x30903020102120a02180a0b0a030b03070b0c0304060905010503130201080a090c08010603050c09070215060f0d0317070507020105040e04060209030a030305010305120307020d0c020301060b0c010f061415 89
    0x300d0082c85a5a01e40e00c02c9502d010600c90401110b0f40a841c0320041d012100c000c0c48600c40070030400c0c0d07031544900c0c0256002001820b40c510b21076000414030000c0a41124502030b00c0303005a1840d03401c1b0107000c1c600c0303520104e000c001d0242d20064a030014202803c185240d41002d6003400d07000d29109002a045c4018040401c0100300c6c00d0b8000340174503800550b1500d620323440702c03100ca01a0800d4441981c2d0380c0304050308007a0754500310791220300a0710640c00510715102c0c0711003500b42c1a8030040041e60720841503140444603440b4142040d01040c86682c50b6000d4110f1001d6207082801c002d41404104441880300f140140d0f000011102500d0902c1c04800256580d07240480291058010841d094003500c1d03510400c25030107400c501c2c16644100d05480910320003d01c0c540450204540c5400113902076929000594000e9030494202d0b40003a0004c03810b240c517204800f103650710443d5900182d80d074407103424080e80010b10420020701604d24034000e24040600c0000c0700341841940c503800c685000115 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 7104395 1250 7103145 7103147
    0x30c08040f0306060302040f020406080a0b0a120503090102070e01120b0a06050307030506040308010e040206030109050a14100302010210020f0306130b040903050406080a060608070c0c030f0b01050a0b1603030903 93
    0x5a40c020140800901da050740c40e460010083c111170b00c8201d0140d42446410882e4007014007d940a981c02e03036607a041240d54400c105005030200f001440d030840c001c60700224481824820104a1a0090004503519050f00c1c000902d00ba806600036032080800b440140100000882c0d00000c4540242c5e00046a4960003544002400c0c164412079242c46880000801c10030080340061085002c1d884030302d800c2c4c0c0d0303840f4201d00300c00303040b94006d500c0034082005100c00c00380381d4846901305144400001e40002ea50001007552a82540e50846901c0031400410466904010703002002040c40b0095050060081103030b9014080902114881c5180c129030b410041056440400500001407062241901e9420041d01e99405800748200140d5803500003170509840d4001c500441d40541d8450750b550340d4040c000c492510040c00c0895422003154000000300703042d840e41044450203100140f900317501d40401c0044c030507095442814440b10606c40c084102c1c441d8080e116040e07400d07060108d0617000c1032038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 7105645 1250 7104395 7104397
    0x30309010c17070c03051608070504021c15090f090c1203020a05031801030506060c060703050c0d050108030306040b0d030f0c02041d060103030905060f04031106040807030f0c15020604030c08 84
    0x495405100200b20042400740b640404c1c4102c900540c03d0f1404140580400301c5840c802e80150041940301c980104482d00342a801032054071110307500e6042000c0030080e07600503a180d0701e0080a8000c290740f0b00740305e412154403907004990398002d410031620540317a840020387d012030300c10780c194900c1d800390140038540240144040e1680c8602660b0f5901308007a100f941d25500040c40d180045d1900300052590b040407030845900200940c01804507994081c0c0c1200035180080c042c1e035840344144000303120f507035040c0611744c080c00b41c030313030203540c0301e151070414042110300003c0c17070b20b105869000b000340100750892848400d901c8039107020400000b00f80049009444d0701041e803002102c2c2224203001c3c000000c03811505903803080d03031803092190b502c40800c80705000d1040594100300307040004100091840240c0320515402070007032402c1c82c0e03803601c5150500c6295841a54521800c2103031804106400341c80201034031341e121a8803c81d802c031070002950f81d80300400c02401e10009107400014428504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 7106895 1250 7105645 7105673
    0x203040609140102030a060b0703020a170d020409020403060c030501030c090e01021b010504020f090121020d060501060504090b060a0f080603070e1305011d030a18030503030c1206090402030309010c 87
    0x3001e41681071040c2c14002d500840c2c50010407880e040021070150126400c50343c0041e0980e0080036022070540b17540044050403007030f203c2c0030300302040b0210400e40d460024100424840c1d6006888510f5810007100b6a088174038000c04052901005000081150000006681c2920000503000c00000c4a550080c400c000800000003500018002b016005401807072081e4400e980150b00c29068070280b00480c5000c0c000c10b46400080c205480d0310b400c1c69010302c80f80b00d000406044c0722041da525148215902a04004002030001409100400c0075000e0300d908103505489161038000c3c8840002d0000e03600d61440c504000e8241d011901c0c941d010400340e00039001560483c4101d0401110201e48500c102004a0b419402e148a0031120030407507404181649803e0091490b02403140c004503103038502c0c24240c40591000e00d40c0440860703030400c040d5104221040e806540c61410403810700c81c11320b004000a1140155004200060f01c0110559001e40001c0c01d20381480460791800d640807842007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 7108145 1250 7106895 7106903
    0x2031c050409050a1e1a040b030307020d0c051507030507030e061902010c0f020604020d0b06010c06050114040e0105060d06110418050402040605090408040b0a030605061b0610060e040203040609 85
    0x2070f092000350011a80f01c1c2444803450400410912000301400003030f946020f01c9030300d41c2101c141c068080790800743c03c8003040c0c2c2c50040a90340760a00c60750002d030000580d8100ce856000c06044d09110b907003000021110000300c8800d04078201081590014414032035640c0c02800c000407540b07a01e81d6500c0c0c440558140c100b40c2080c2403a818285c0100a00800c0003070740c0100000e8030310084800081c00411107902aa8002d807079815031218603195410301d0032028111504011120303e80c60045106445164040c0291071656140b00d113042003000280c40051008202d04d0745010107010040d0b071580003155503154068008180445001a8044c07035003e19441803c202c580144865034070815a8401c40c800d5200310307810800a40c4840c10301c070a803c1e0495004110f520100800e000740361041002d0507140100c0d20700420314a49030004140c007500080d084100c014030b0440c00c03d01d0304409109041e8085480c03204040c001e85048001800c80d4600c0030710314000c0e50300101040520815410003901c507500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 7109395 1250 7108145 7108151
    0xa03080a0305090106060504080a020618060304061a0603010806070305070e030706021011070b01030f020402161401050108030309070302010c0f050a080403060c0801031109061912050708070302031c050409 90
    0x2400103805080200c074000e4944d464034801044150040041c0c0d4280c0f18120020610f0b00312a600707003e0540d0150102d01a0003200507140b03001030340c4040c02140300d42d03c249030208030001d000a400c0c8007510354100481c400c4800340b0061024100000729590f115100380b41c082138a03164640c0c1a42e168161b19041d035054004c009000c00d52a03000686550140d281920420441d103408028500078000c2c804002e010424400041000c10074840c2d02c005614001800145884c0f48032221040c442e100407021034403480b008840242070741c000e1007050b00501a9001640c80d40c80c10781d12150f2218a1800000c0c14806d00e01c020b00141b11000340a40880d81d484801c940c81943d541c2461285a04540300440e002030521790840e0b0340c688582040790490307038008490032100700d0010400032603100040405401c0a1041c016041c5c0c028051110001400d107919908110440c5040060406c141c0c1e8014082c90340c816a01000180c4002414418402d181d41360341456841012044801e413149a100c030030500c1c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 7110645 1250 7109395 7109407
    0x50601060509090a020405180703020f030112110d0309050114070c0b04031205130905040f02180907080606030303040206130b03070201060510081905060307081b0103050c0c03070602090a0308 84
    0x10700100240319004084075480080d13a1010343c0700c001d81c40b0714081c0c181c220305001c6402d034a00250704800e903009045800d0150600420080714507a0b50826400241180c010784440403e0000407111700c0b000100a5030071549000b01c688004e8041019442080c0c1002040d249120785502c1580c00ea5074142d030700c80d036048110342c1e8669140c2d0395600a808259415401c07001d0b2410741a00800c11210100e0b00c034920382101d1860b00b08104010030000740706172040c084140845005070354850060101c3d24079076a4000d410700781140c40c10314181c182c0e000900716074000e0080c00350599001040d41d521640c1121125542d0341c11020b0150328006980c031044644101005014034990103401002c10782d40188e5103803501c1169150102c41d032220a03107102c5440c070022040391f90642e0a07a08104d62005000d001c444c861503850fa4858a402d11420108044840c240c6c40f83d50702e50b0b41402420381006040b4005803c2001481ca01ca40741e1094400c0200150343c001042045a01d44401e00030055400a1145032104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 7111895 1250 7110645 7110647
    0x90316050706080903130506030604020d09030f0801051002070e0606090a0b07120503061f030e0d030e0f030403120f020a02060f0c010501060801140d080906030903040f0603110a0f090305060106 85
    0x782680540000304100c00d0025075a800004243c4010319141c1c1441c0c9803407850b080c1482480d50019143c80d8000350200f0040850003a2401998212407182c5d07a0301c100b10003c83c9008041c880c060b04018400c1451040b4205040d500003030340b0f4151101301410624640b9401e00059007403054045d100d070040d0041c9400500740101c1d1018150060080e2651802c080c034000c02142d0920044420603030203e003014800c0da6841d0590660115074800c4c1c20000386495101d00d031145080d000c10b04840000780c46a003c170031b0004c8244001914038042500650420f82180c0d126845103881d5840d135000c10010041c0b4000c818030030080010001c4e0040c100d5a59408411008070195006003080304a542c01c1200024000d44161943c0d412100200c1c3c4243d0a00020f208101c5c4c40f000c82c120560f43d6171380c180901003c03561004021805200320200031580c4524020340b4502d112060340c400c505251800912603034500d10305040300d10140701441c00a50b5030940b40030640b0300c00d915801c050918030881d40042070103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 7113145 1250 7111895 7111903
    0x30b01030b07020c0402120408070c08100606090b13061d0904030305070201050601020a02011b1401050a090302120307050301090b060d1b110708030d050c07150b0f090f010303050309031605 83
    0x1240030f0350955002001c01c2c02440264401c1d0382130b904a08512800050220361064007901e0301c18803511303001c000e0070745e24141503280800c454042080c00743ea40b03d0802c04680c029203408001c3c8100e95000303040040310303544003145610300c1c40303000180140d00141e080c0728410b801d00d030440c1040c014a103040c1800e160800400400e011900031001d03606c0c00340403d070389600000311b0741c20a030f43c140d45045c09200d840318452088100c41c00d0480f40b6401c500c103a5122140207000315131040303403c40800150b10001d4203009190400005124103500e10400a211030b4036406000ca80c15641e4054010880b9828603000c1080352041c90b1001140300d24003940c3d10380c040700c02e00800380c40c00c1d0182c1d100304102444024151300ea490700d124105a940c003c001140d014141c0c1c1d00107560000403070052501700900c41d2594041d106074058002206640c0321042e8500346091528141741003015580e00030709180c611030079106460306000181c20712201000080e0804c00810071900070b00003008913252004c1d03a52910640d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 7114395 1250 7113145 7113151
    0x1090302070302040e03031009020a12050910050106050408030d020a050919031401020a0203070210030608030c0604030206010b03010b070201080a0f090c0302030d050c100c1b050f010b0301062706030b01030b 91
    0x10840c100351200e080c098002061364000c903003001c3c03403d06641c90300327510000a510000041c0107000100801440140c901d0ac0340c14451060f41024020404880e04050b04499058001c00c040c85010310080c806003400005480d5601e0f12081700582e11030301c034901941c050203956404c1d075000241da4010340300c4400341d08907001140e00c01d0f890803041c0014015100d00b44e0099440c003c0c01a8402c0c811400546030202c02140c070b9002078103000991940781e0700200d042d64080120301d019940490b044c0010554104605401008034080d010304550400256038100d20800501904000000003c1018010b4582c042c1c246100c07519410030040e9654604121405201d10013a03119004664403d01021b004500312550500c820000c0d2132090251a2a03030f00409006011504000c100410020420324882d03031055114018001031000110740d0325100c0c00d5a0300d1110150003641082010000b094001100f250752418514291016491070f0301400010502540007820f054540c0b40000144080f51040304c0c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 7115645 1250 7114395 7114399
    0x30319030c030c0503090d030b0d060903021c0e010c0303020a090e010f03050601050306040b0103120302071203050f06010c05030307140708040b0a1407050a02010804020d020a030b1501020a1a060105070501090302070302 96
    0x4100301c3e40310160b96501040740c4030300c03d0750032030003840510034480c2d80190820040204040c45004c11622007400300d4a80341c404901507405018404001401c81d1384060008a0303a11303011070f0316505040005c1c210030203040001c040c50f401041c1c03490b8040c05182440050011009241400d6035516100c0b030903000c803848261114000e10b00040781900700415603170700c00e5800c031200407126460340c0c1e00c000c3c0f14000e50812a003055824000200000c900011003044040f040da408103850800c5680000c000c000a001141840704915150300001c001005895101845041901d0307984114640b40342d040c410902d000303200800003e808244022854050200395020380d45500d1001c0220300c55411070300c50001c018040d54040d603940d80066200c0c440056029101038414074440c50564007084280085410440301d400d000340c1041b14402c461080168a15801d100504501c2603d4840700040c2d00b0340b540e4080d81ea0100000100b40d0f034011f004542003a54068000c111002650500075191111400128 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 7116895 1250 7115645 7115651
    0x71410060b03010b180a0e01060e0a0506090108061309020d0b0124020304050f06090405040605010501110c0a23030601140405011211010305040213090501020301031b0608070e030319030c03 83
    0xc51054050070542e81601c0d48403000900e4207002079208070740e08550050701c03076009003603c2000c142e60409003039880c000d098984a800f143c001c00b500b00000b100040d0400ba024074401d106c0051a03a03404034055410882c2500c10241001582c52100041c01c003168000c1e4100d0b00161040080001320b1a12504a03806041c806810716513003c1d1b804003045c004980c031401a4000d10040c0700d1450003002000001100514407460054104086826110210f4080d03c44a80d6100104a1560058851925481c07501c014040e10728030134000440c6075044d40110000c0406518901c80841c102d010707030341d1540c04020226078966960780118030703841d210450100d000e1030401c000000c2c0400d803d1015a9400c3c2d108450351035800002c8011002000020020f0fa401000052125024031481c4507132901e0500a41c00903a40f5070650170724040001c41048c074508806550342c0d041110700c0c0c1c48402c1030780000080c0381c05000f4840075000070349140500b8003000101841b0004548020780c06a100002045e0142c4040c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 7118145 1250 7116895 7116899
    0x40603030206040b01120201020303010306022d07030e0402030c040902030901091b080c0607030f0509010c0c0b1809090c060706020f1911060727030503030c0304020a0b030c0a0503070507141006 85
    0x4224a03081341d00023400b41e4010310040c40040c2d096005010046132440095481da011076080c0307502c40c2440740740c489800c140012140c0605600c144440b8003d0002d4906600c2d6080c00b0701081d00d588070703900c11076020a078044089000ea120070f4005a1905d600a1800308000403604118803086001c1c2c81074541a1040d40100304080c01e1040903180c00d41c0c0c05171030f4025a00054030058640741e100552840c1001031030700808000814041c0708d2005070400d901465142c203840f80188a45403000180f181c4950070b10b00411002e000001409843c41c50180c625503100c2800d840c042d406801484241d0401180c08941c150102803034544002d0540790554a02d4266030001d42402c1c0c031404295842b80024280720881c0360400d400c007040c44c40510850444098090b80e81d00c4460550b0001e9409041412000080c003042d032400300f0300304c00946100c2008a10714100b400d02104188039001a01c014000c0c080002043c40d8003c0060382d00301c5c4e820100b4040c00d44d50741e025003503c0e2240551607581c11340c42c02c800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 7119395 1250 7118145 7118159
    0x50102160c0510021b01030207030c02030609030a110a020a05040b031203190c0c150c020709021902061b0909070504031212240308030907080f010606031404081c0b040603030206040b01 81
    0xd042d502c0a92141c5140c40382c1c405c0d40110007a600080041e818042c2404446006840400c4881d2041403000040c60700e8194103a00108802441040103076154000204100075aa849220b402210b00c03c80b03000800d10190000700c0e04106e617400d0240790101c0d01108201d113900e65990410720707030154800304004152191100340d0b031440384524040e01c05050151040602080c50b03014081801113801100d01d03044d520b214903c203a900c0514041071481010180c5501c2c2c80d0100000f6030800c01511545051113840b500c00e000b0303402182c08480c85140138001082d207807800380041b200519000201c1100e80300b01240090125030240d031041120920f0205908100c5044c0c050452402920340442c40c0080e21359202d010040d0009025800907004880300041d8100f0108880e040c0a1401c60000c140c240c41c1c80310240494011210100d00001314804100000d5035200480342462440d248604c1c0340601d0044c0003000300346606480e5040303454800c02106054001440781d106511031070350070307000743c0e00c500c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 7120645 1250 7119395 7119403
    0xd090b12130204020c0102071104050c0c03030c0306010315080c011409030c010302070203030c010c110c010309030e011206050901091a060703090e040807021c140115060c050102160c051002 83
    0x88400d03000d0800d000854840c0315180618450a400280091305100368154413508990016400b01c511810420a080031400e040c0030b1960f0100d4100c032071fa800c000c81d940250b40c603440010b04240b001e0b031001001520f141c0c0250b10127440b62041c85050010151203040c510b40c0ca8420b20141400700340d800d41c0c04910703150308404541e610000038000c0c183e1a40b41c2c5006401a402c0890300b281c1c54081445241a8101c0c00d01c40c03502118403603070350b060316900ca080d421420704403060542410181440c4011011a40165100c40a61000c3c60710381c1140000070451402441c59400c1598480844000000c0120458110410602903010b4441e1024080f00400143d8400c2200080104131186000c000c0c00c1c00c0c080d0b01c50342c802e00a80f4601e02e4111150b0005500c4025041c3c561544250000d0980610640f58280b41080d540907000304080b881640075100d5881c1c40b48038030000c222445a4490803c0001c1d01642d0f680c3d1100004100070000c240ba092441071018091507008a880740180d1013000d01c001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 7121895 1250 7120645 7120657
    0x30103230115060e030705040e03030f0703020304030207140d050106031103070503070810020a05040b0a050301091b021b030f060a02180913060b0609030f0a0302060603010c050d0e01140403020d090b 87
    0x200b0781502440e0650a441251401051300c1d810702883c140011251101d00640c20107003200f402466507890402c847d94080880500a0810944144108070000e0b40004080c3c3c103444074100b103211003040b00030002e600120540c4d8014629400d03c500041048000e000b44200200124190b130003480d201c01c14140d0720b00d403034400c4030319030b602c010115100558030381d0040840d481c07103140061406480d20006c00f103a6020f504a03600141c030000040240808038801c01106042c184c00c00743d860059072f0170095449501c2907941c00003c0c030b552103005ca1071744c00b08000746000c41448241e0b409480e00405000003500701e0700c0341503650002c01da0001120301d1b085020f5032141110000034001e40342280c07605001816090407041c1c100c8410005030107943c6d020000003859036890401001131121501d4020306021014005500070780c14854039424442d04071054862044815100091456411000c140034003030352859116240243e50501c401e16601007503025941078240c0765200811b5888107840803520500c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 7123145 1250 7121895 7121921
    0x506010b091509030a05030a050309070e04210e1905030606030102040305060c0306060d020708071104110406030b0604030f030f02060f060607020d0302160b040f0e0105010206060904060608030301032301 89
    0x104400c0380350902000b0151912820140480e004066036660b000e1459004442c00404030b00c0100c1000001c80e01000042c018140c1091080c400f070610303954080d40741000828a90811595004c10f916691141240b01c3c1030b0030000b81003294204d54040440e811010703074000d41e0701074015100040c0f00ca04050003110200c07076002005140d03541d00d000410001d500050101584020100700280b282d60090002e4100035019901d49503844e0382c1c910b030007480500c20703d0140c2e00484c10100a010310310349890940701100e04500300440c80d20051000182c0c04e2183ea00f009202d00e0100c200ca030185680212960359118440d0211040354550006040c41c054040341d02c030f03500010400084006042078040403900e68403c1c0111445180352540036004036259800c000b40d08003020078100035008000c011900103242d803544d0100c40754103040c0000e4440000074280b034000c03407807140880c04104441d03001c500140f0714841643c1d2a0750710382c60200c003028003500c010851104100c074000c54095041c40b0f020416144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 7124395 1250 7123145 7123159
    0x120311030307020a120504030204020d02040501030e011a040c0c0c030302010c0809070e0c1b06070806011b0b0a0207020d0501060902130608060f0111010b040608030a0305010f12020402070602091801030506010b09 93
    0x383d40d149503a0045e940724500401c0740c20702002005840b240050410340310038520141e103440c00c01c0b00040c122102c00c80381d010b0503810003003008650b8840c0324001220340015580880c440c030118205603021040b203040201464665800081810381c1940205040013190307541c1c103483e4030340d280303003541d01c4000d40155000c10703e401c00400c0c00c0ca982c4d072000b008007050800344890340ca4462444941012f600711482004100524100708483da401101007260301400035420028103095190451042e000520000c94150300080c0c810a540d076656a1a244540c040e0090142541300c5a0384e4010350401d10881e98030703083d420001700380b6030700458245101e240302501010150f000a001100c810802ea10010821b540c0c84020742c0e076640725809090064204200119a00c0c0f0341018018102c3d44140e001c10903500d5400c00922410750003031103411850360121809a00c0310614200345000f03101d2501f600398483d02c507101c401441c00f814403005040742e000e00c0a440140c0c1e40d41070408400e1241c0018658001c0c2c3c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 7125645 1250 7124395 7124413
    0xc090305060610030e0f0d1b051504030e0a030813090204031e0201050918041205030601020316030521040606050906031009060608060c03100602010b0d03030b040908030112031103030702 82
    0x20003040f03c140c0d40d1910301e80410078448048545041c916100c0204d0810b030045480711203800e030059180c1104441b5401d144500100c2c41d00c41f151110840000740d190141c0400101b01494803803103621155000041c65032900c5d41e96441c004140c3da1005441007042d4008110004501e01c0303a10954017100e40001c1c07040c902989460440b1011400868100d06201e001c0c02407102c1358461590310703140404901400c80080c105420b1126801b401c4210004c200182003041001690f408070584d06d603d06a6010201c03406142d14040d0784600822079400c2401c89010311108880300d040c1d28107405580981010020303240c940d814480c03100412228181c15a101c0445400c0341c1c1d800d03600040203240140c0340000c02036190714070b06080800648003060842000f0052201c40e0740041c48000003825940020048050880b012072403e98952174054181545c40b50340112948035030700204111540a103049580c0d43e1904107448022003042801e5000410300c0c00f1a001c1a000001201c0c040d00d0980c004010f544 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 7126895 1250 7125645 7125649
    0x8011215020304060f0c03061e03030c02190801020d02030411030d051b07051206070210090b0105010c051509010c020d0207142b05010b011706010903080901030603080d0504060c0903050606 83
    0x142c00900115000365680d56020384504046c40340c0d01400d00c00b568081002483d01c0c0d00160940e54142c201e140d800c4400100704002600040510080743d41a42d08851040894017254400101a40321040d15400003404481c1459654000c5224034070a817280190200c9403000d1658421a01d0107001c04030350f00308880f466900c81212a0340c01003440e50b00f00c54519456801107034002c4d801c0600b40b801a4041c1003031080054040c0300c403c90680002204203c0c1e02000e4584040102d410700c030381030512a549404d10103005007886040400c00f0800200c01c0385080c44d482050007048206204401401035486130006548007040c4501190f825081d0052070000c08410805071900803825030207061a02c89140c040600290800000e582c001c9000064090249001400203100858031000c01c8022404016160f07070041036080035250841c407003540306d4910400580040c592900090010716010134060707050703156600a24410382c03107682d0500420394040c0c4241c4201034103000080a681240000807036034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 7128145 1250 7126895 7126897
    0xe06070e130f140c0703050304200325080309060711040b0d06060302031203071b1103030c01051806040302070303080c0f030a0e010c02060c041403030c070609060801121502 76
    0x464005001ca820340140c10705000445181407001c044003511000c64400125210702401e51002e44900094030b03260046e0340041c4940301c01070008020b602041011030402481c0c40b480d91043c000030302207030400d41c0d00d049461040782540a500b145901c2c58030780401d0400010007500d65a41c405003000d03081c850190b40d94807c0c1c0070300ad400b0341e41240d5504110703060740e5603402803003100c40d0180308005043c2e42140145801c004450304018600c1c88108180600320f41c0c0300d500402c20003030b24050300c403005940e49840204403103040180303503040c800031580031b41d03401e07041d400705028030444002650440402000c540d2181401c440c0500036801031882080420b00074085643e005403c04801450400c1055000c0c0040d0010307904482601d50b40d0380303400c080480074403a00511003203d0005064525010862103002c0c80755018480000349444d403c010030b52410000d9807030a004c0c000540b98444d48580000b0402061449a00000388804000280030161164642c940c0c43c1c001c0c12600138071722966006406 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 7129395 1250 7128145 7128167
    0x608070b0f07060c080a0c05030105010801050103020c0c10050c010501090c050f03090c03060c25080910030605060a02010203090d0e0108070318020a03050d020d05120f040314070606051002010e0607 87
    0x101c080041c0c034001202c3d403050501c800019101e1544500b0400c942c03d045a01c4034142c042800320810050015a0301f24610a044400910f00940d845440c00410340c280300d46a01030980001c40304018144054218001c0c1459000c80d0000300080c2c1c1c4ea81501009171000c0010070004070341c080042d0800404207000450b4440c1c1e044003113032a0800841c0201e444c3c02d500700d920b80c0c040d00d000f0451500341c07401c4034010f40c1010544642d0b00c09145064590714460b105580d00030b40b040e00c1c21b15a51644a009400000062100424003078503140e0a00020303010b0350044031401c0141c015444911080d5015060440204a040c0d40351341e001e0381da0050540051010080e905c440d814030b2658400160b030383c0c110410103548108081d10741114021030203442c0540e5100184107220062194507200301110300c42540c0041c3e05840d1026036140d5003001e5408803950809400110030000701d4209104ca00d07001a000c680382a200003000081c00707030341207080301c030900001c0c000c540005000c0b6035584d2140d502104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 7130645 1250 7129395 7129417
    0x140603010b0a36030b07020c0a05040b04090602070f020f1f080402010309080a02010903030b01020f0a060b0a033f08070806131a090c070b071206030b01080c12010608070b 75
    0x195100151419103c02201031041c10304034440c0940034010020010311460300f00300b050004107256000344001440d010484c0c05858020380d5124000c1466980d40c3d04a190400c0c0c00c82c0f801c655403820350801d4648440d04034030607801000c40d45081d05c0142840003480d046000ba03000085503512031028121001d5502070300c00d904040d00c4184402c042441e0707500503c42808a0740000070308000034034015040e100c0580030181503400c2009003c0586e05c005c02d1010149038000400100c6031003440004034840301e41c1d00701810b110032901c501b482c4140740032041c00c0000700e4000c1001c50354803a00c07286030454480c000c401d4001421540891055409201c4454000d10b0051101c1601030880300e8820854078149008104400360400641d0702d800d012510340e070010b14196a49260100c6030300e840c502d102000d0710403810031034840c0c00a0304034040d6502010203140e001608500550b03503420546d076180946640e0078400c4001d801c0f81001100d05100e4102100c8d418005810721500e000310302c0040d504031800140c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 7131895 1250 7130645 7130687
    0x50a0c0c0506040803031602071a0c01060e0709030506090304050d0b0411040c020d0e030703020604030b0a0b150903011a03072102060a0804120305040b0a05060102011803050301140603010b0a 84
    0x215156075048043c202500c0850001c0d500c80c644880400b0300070400303841600039500002da0501850000340c0340300c0300c040c54011000fa40c0d891b101d401c1c01e00411581c0d01042c90300304003c060005043d0701c24140c0d011680540100e5020ba11804620703a180d00c180e200b5680c0c0216480d03e200001103084007015031082c06100701c880080c0e04000890181c40b0010181d00040e000a651041d03940d030008640074900310182e000f0441c141c11a404102540f0460001522104075000059408901500808882400a000c5e40101c18242d8001910380e001942028842c0d420100e20340800c03081d0051064000340001e00400c0c1d05440d200c44100b4100c103100901c9149003640c0003070005a1502c10050401058550b40c482a80c540340c240802d1020203c030200003018142800d110105409822440d00552800f1002500352074000060f401051001c00141d541d03003d805280060541000156040700c40c08071004100640d9141001068442405a41130182e0144000009503125201200302100090540 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 7133145 1250 7131895 7131899
    0x30706030c0302130605251205070c0305070603050a0605040e100f150305060a05010b0c06040318030f030e100201020a02060412050909040803010503010f0b01080609070201020d0e0a06060f0303050a0c0c 89
    0x89030030307002c40e4001c800801c1d00013504071451f00040754110b1280c1c1282050840740c0d1620790780c800c00c28146196090401070040f5881040c8440001188002c55000c03044030000795035900040d02030002124200b2660f817402d40f0004442c02c00d400780d8407119201d480034010a079501004500100240c0040301d11441c2d96040c26041503070990325502c091401035006144500e00300d5400d0040c1e50058100d45045001440100707490300c00011421b0300254541481d00303011218100304d0000e50344a52010301003003603150305e0100381078204016400004055840240102c0440d4040e820307403207040712030001a8800400500841c05000c0c02902510651400c40e141c40308410010310358072400e550564500c40d0020040016250901ca2580084803440c003d00041c501c820001e000d018005240a014041007030004080318403e60454100004110042040746501d03504160b94504040c011200d81c3c1c40c01201181d40303401c518409081302c2d89582c58500c1c3c01000c00c000c50350180ca0b810100d415156103000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 7134395 1250 7133145 7133167
    0xf050906160605070302160609050c090c070303060501080618180703030906030b0405010506030103020103020306131505091308160302030d05070503060f0a060210090f0c1502060c09030706030c0302 87
    0x14000c1d1030711095803203030320314050030400111032004e00040e0a2503c1082804c8401c4149100c10380d80700c0e0083e0000492144508000b42405110388203290300125850803c480c000a4078017509546010790ba0404c61591a0340041d40c41740d00643e5440d80c8036200c03030350014048008020b01c96010b664901504844806140c00900c0e1466a4000300d0105001010600000c0d034940b107400d065180444007403005515010105441d4807040c08040d0400da000000074a59450b05035190803540d150000410100f0501c410242c4807500900525100b607003014041201c5850250000080c1c1e50812400742c0343c0f81c01121902c3c942090000101c0544c041404a0028001d1900c5072501c500c031a40c8406580385003e50030424004240344032644202110305042c042c2c87e90000c0c0d132400c0d400b2419000690703501e41d4280240a51500301d0020050340c40e545000c03d80c4030505007100101c5c2015002c0b940d654403001c080850174010140700d20780543c07189008005940c866003081c108030445080043c50030f440e80b40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 7135645 1250 7134395 7134397
    0x30c0d0b0d05070303080702070303120b030c090910060e04080301051009030804060504090501080a050a020f0411030a060501020c0d0f030509010309080c010902010e011b0b091504051c0804030f0f050906 89
    0x181c80b5900100b80130028103401482250344500c482c40902540d80c2150f030301600d001000d04501c2c0d44950340720302c6800d858800b0080110004401003000038140341480396143e4440248510709207c0e81010310000d03032910004a80c40c0610b40c010301070340c116030034002031022100c007154807902004058240000071034420130040000d44200d9440b5561a402c008802050710300603804490b5035481441c401003c12400b1800e400c510b5811503e0b0080740300350030b0000d006008070704100902404004180b100c04c00d01a441001110002e8003500c10703401d060001c01c0702c1d4040041c80901241c01c880503c0000a02c40c80040a441c54141400114440591251034160b0088403505280ea03556111503001c2d036801c0301348542038036401d282681809800804604e402984801c0007044c041031341c0085804010284201071250302e9203a1a0019840c090418583e141442c0275100a64510112189920f07071180c60024807883d0941c0340d105620058045c100c0c2c002c04d101c82c10504105080c020040c1e19540c5e18 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 7136895 1250 7135645 7135669
    0x10c02070e0f1b0a05040303021c05030a0e07090f0902100806030d0c020114030103030201050906010e0903041a041e0e09010b0105030f04060605030105010b070302011b09050d0303060306050403080910050705030c0d0b 95
    0xd0f88086c0c07903a055280c064509086083c0141c2070600c7c07886007204c0641c1c44000c0701e031321000b04100400c1200120100030b1620441d5004412040c0c20b0400c0c1c4e02492040e90701010b03415008945c8565242040c0b03030305851146040e0f0b412600b5401101d00d400c1058001e824081010744185070034407400384805007029054000781c00440060751504140088080f04018039809441d44d01d40c030400606010482550b00c0c4100d11031440740742a4100b41c0703c10f02d500718061320300a145104820015004035012a595110103000d8008000c8019000c00c3c0c14040500c950605454103031034191850b2180700e00d00c000074030010000c99480da1204808140b5442c03c0c0641802094000e031039580300c820f20b280c0a403d440c0b2920071242d01e21800315035621100e0380508004100c0f4410b0b18100c80c0b104003424100c01400343d54001418142c01c00083c00105a84500c890b8880d80011080e02c249000b940320240a490342511481c0004109101040c40c07005841c00806c400040040005000071900010408004500c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 7138145 1250 7136895 7136897
    0xa0507080417011a0a050f0a0e071112090303040302010518030a03020f0d0c0b040308040201020f120d0e0c01080c090406080f0105070e19030605070909050a090302010c02070e0f1b0a 80
    0x1040c202e03807903000034022244500454510a1905000d5502007980a056031003030f0381c420714501a145e0b0040d1aaa050364001c1c050102012859161404001d88090752403034601482d4800d001d0710010b042d50440070b44003030788401030195152504e1a00111030b503401c11905c64030720180d03929440704181da08220300c2104500c02d80150000c001aa0b440604000e8440c048605219600502c040020385c0d42c07403007560141d81820240695202c0d400100c2c0f40c5070303e641d030410f224402c5002d0b122948142c08040c14010403946014000c03840c61410150b01c400313120700041d001c1140507000c51682a07018003d8085400c014000064281e07032129094640041c0c41013a07030f8581d40d10b00a11014035800041c80200340c90903102c00080c0c01c1e10721030603e00000c0c0d512000d01440e90b10f4010603021446074032030741d00400c441c01051215013005101d107002011000d008602540c600910b940d0142d001150310021121400107001480e5101c1000820800004183c4000c01c8165200c4105281501c1e000d803010290b5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 7139395 1250 7138145 7138169
    0x10320061216030b03060606071b0f210b060918070b03040c090612080702040605040501060503090105090d020a0f02040603050d080a0e0c2805030d020a03030b060903120a05070804 79
    0x114410000c003410800d000b00080500b04401e444041d140081e4490300828141c8030345603076905034140003468403030381c0340c1040c3c03041e000c01d20020340740f66004101815101c008824102c5001c640800d0010181140d0000f04a8489600051218905803104981c02a81c02046e200b07081940352086042c4069900318010004002c42407100744400c0d0301d03c180203000f28a0082103218240030103c0185020760f40000e0001c400000d9660441d10f8942001c40206400740045c8101d584071800680703603810441d074041281d860f10340001d115042c0050f481040c90382c01e4028005020f070540b14281c20b008910b00913a082519030a0020002d10704020260f070a6040e40c1da04441410456000000d41e61008805460b503400501e045040c3d543da0200544810700c00c40000305d00703011030303800d1b01c1c11010a6448554103002c0d91511034400e580104000b001d40b4480d40d0100f00c4150800c00b0004c3c1402114241600341e44091440b41206211000070200c0d00d20034113015080a0050359401d90320390140d0000c11403810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 7140645 1250 7139395 7139401
    0x1110060602010c0210180818060403080702030f0109020901060f0302040803030901020a0912020102030f070609020406030303050a060e0c0403080703120c020c100c0b0f130213090b06010c08030103200612 89
    0x26060010408205c440c407401c0c01581049405000501c025013000740c0402c0000608038450816917402020f9490003034103807520759980341046e030941c1c0c2141c2c0c0280c0c0240074144040345035800600c620006c59034018540b00b0164245182101d88074182c4085c4d8082c5030382040080744411042003e076200d50f02050015a96004d2110010007164140e0b008038071450a00c0c0b40c00006070307000f0041e42c0d4008140001e0725140c401504003000a0402c0c0780300030307401c40d14001020081c075901d030b0011481804d1b044014880e0300d9a4128902c440141141e180d0203e800912052000607002c100070b0040c2c038024a0941d104808070000700c011a4400d8001c50007590001c10340d203401e42028500f207206401281002800500562269000581c0c01080300c451610b204002695a40d507c40441c04240e40241004010052182caa07400401000c2c10580d072114007e40040d15540c82029030184550384000c2403402c0d039107955200c45410320340500ba680c4c0203407505400415601e410028140340c110150000c04141 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 7141895 1250 7140645 7140647
    0x301030501060602070b0c070b0a0306050d050705040b06070201080a0c02031215090703050601050d0b0402040f06081e06100302090312071a010806060105070308040206070606080a030206090307030905011110060602010c 96
    0x7005c0e9104850880052094075041c05004c070f186401c543e400c9031250341c0c901d03400306d04400602c050380016074001ca000b2103507014081c000507183d00303840c41980d00f0020303080b2500c1086840d00490400038002001c584c0002c0146029400000e2502014011241002189214000360304022907a008401d120700c612200545050030100323401152905080016090a0340002c142e44102e044103584151150251905602d42c1ea04460042c0103482170508032a44411004020100603210b90401c000100c000c40e0001c90542c0b07807103002d60030040200c4c00b425490705050300a500300418069241c024122081710114503140200407a920802002086040c60060010300080680182c24568445000c000503070360444120780059070181003100319540c031440050780610920200400d424101500003445041c001500c1072490301c00c1c2c0035120b55580c1e44a10b90360743e00820701d0180001c2c202903402c002a5000e5140004c90082e0380c0c0581c5c0d02400c1c00648501a9089a841000140e654034000c004107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 7143145 1250 7141895 7141903
    0x7050c010503010f0302060702150307030b0103060503070503060609090705090411030f07140d050106080f03120106020109021509030f060f0a0b030c031b030708100606031d0706080a090203030301030501060602 92
    0x210009007400c0c2d0555040042c11000c0310303610301009001e40c100142d00402d541c0c0384e510441c0314200c02c80200784c1e0b0380380c8000001e000d030008169060100341003c80100d0246000315440060340d001a00502255851004220345008060100440743c09080000300703107a10341c000002d00c100e0040001283d0b034900300061510304480744200300b8407500207881c24880d89400f81c1100c08529002c8a4034101c40d80da0b8204280145600e078410841c0d4803910304d6804c25503e01001506560b506540110800d0b07982d5282079080c0c4800c0300f80254040840c81098210075071440c0600a003101c040c080300d01c045881842d0500e090380a0741d40c0030b018031540041040442250055800b0440c00360054039007025160301007641c0320850b08804203088440445d000c45601d0400283c030080c000081190840d0711903249401c0104154041c107400281400e42c0c0032811020848800c1c00c0e1100b0800806013240350001c12a40e540c00907240100c0280c9560040d40503a4007000510701950213400001101454038030b0207850 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 7144395 1250 7143145 7143163
    0x207020a0b0c060604020a091d04030305180c22050703050a060506040e0a0c02150a0c0f03060302010e09040203030f0c0c0406060e060d0b0105070209010306020306010f030b0312070f0503030c0705 86
    0x1180d801081050101030003c40d8080c3c00480940c0c01607181e0000c6041640c030166103411041c0c41e412610155400f501c80501d070240918000d0b1404c006980750600315030450402c0d03403010083c540c0504865a41c5051200c140d900780014204034500c10345210b06c0840a841e019505000083d480d402407005981c0244113410050408036201c1e49464030b4040010846200101058815941c52007417516983c0248407010500700078010300798035850305080b010000c061a42e4040c0011382d0a807200070145d4002d101c1c1c0d0065075016110901210480700c108081110018000ca070135010034040e0150440d50340000e001c140a940021304041040349092000700c509503405001080032010759170384035072109022183e0318400c4540c00305a009031040161600c1c030540d54000d40000c078520002060000540c0650b004142c26030b03c81000e00d03001030044003138500492171f071035058020f0f0041c0345201441c20010a12180706210810202c4075645540342182c1086034400d04d0000b00003500c3c010040148010381c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 7145645 1250 7144395 7144409
    0xc03040204060902030907050103020c030c030a020f0f0d0903082b140603010b09010302090408040e0708010306050f04020a06200f06010305190c0612020d1b14030f060108060604080d030207020a 85
    0xc158030b001410707145c2d00c1f011480f680d030506a000500d441007003000e0003215510300c0060b0440f03a070703140214070003540d450143e01d00c0c4083c0d0103401c02040c03200001107103000c401c00c0750780e582d50080303400c6482c3c9100780d038400021a907411710b80462406448051018001c0c10319648c1d040020b0521101c001c449a03441d0042500c1d1290349402c5656059995040a031415a0307015a10030b03406035100e03c0c2155440c400d45e0000f0329100b52800c01c006245610450030f50681e489044140910b443c1c030010504204001d580082d8001910742c01880150b1095100c4081070a40340013020114140300d02c030318144140c85c618a40c480d041a001401800800c20005040340039101c1c085004c1d07480b81d210010020b1003030050b00c00b00074181544c0c04082e11a0340548262046c48030042240c0061a5900702c4032624144501c000b0600c0c011061280031905c2c0d082e00e1150002000056050f581ca07401110b4209004000e0b55000c0418000818414000c110300d0075407603850b4800690f12420350040142c0c506183d40814 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 7146895 1250 7145645 7145647
    0x50103061409070e01120204090207020a060201020304030e0f0d0209090703060c110d12060521010e03070b130201020a080c151005010c0f0303060801020c0319020c0901031b0b030c03040204060902 86
    0x24031561590441c40c3e520258a19041d81034444400049601040451140d864140046404591754803030358000c0c00304038800c03a13001c81284c1c0c0d00c100036800c0c1e010842c1c018000c9080070b0039a03a0182090590304a00e40d00c002c1c52503d481c1c01590000c0c8806100356440010703075000000c1413080144a01c1100071205080c1426900059104080ca81d22011140722108001120308078441c41d980b00d400c41e1020780030090034810742215201c1c00320350b8078110b901401e65540c24910900f009070404000c035210740340c1105214400355070b0b0480754045a00c103280c0484c114400c00f4041008101c07028040c04200da001006410003188013110925500d5015102650b2200340c0d120401407a0b8112001e6a880d0340e02081c070384189865400d06600800c019841210954000581040e075080d0110050070a4040c0d250f0021041d148141e049954903660465140c101e4000401400821106514072814070750f2018615007668030350469031540c1d00183c403401c4100364040148805c41c5000c0c0914009051845811 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 7148145 1250 7146895 7146929
    0x14010f090209011806090e0d030605010311070f0203070509040506070e010513030605090a1202030705070902040308120a0e0a031706030609030406030c0507020a0305070f090204081b01020f010e0705010306 90
    0x4010081c10b2040d45954444044c4122003861181c00100050440e400200110710491403d04e442c0c07402c5429a00000f40742200209042d030091140d090382401209500341032060035501d410801c044c00c00700b039a0510880000040340e5642d940700e54030031445107014111070b05020320058101030300d48d20450305204040c804000c40c26071048440d0101e030741110020805440f581a19414401e4000e0301030310071149200c0b80181c5035000402002014031900495444641d036047c0306080380030350300000701022020098a0324040b2010103d42d044190400300240c000d2080300300c00e103000211441280807945030219014810308e14200c007039010b0001d602402803454408002d507140e1007140104024550380702103c2c540c452041083e01c0c0c0c95a03016007485c000c180c40342010740e0b03909180c0c46156544400f500010843d01e50340d00a4030304940c4124000e04150880c101c01c00c01403040325001c00d04501c901100d0f007100d0342c6c0034000c2220140660024064583c2894001403d40d0740fa0703005000e4081a8500b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 7149395 1250 7148145 7148149
    0xa0201020c09040201230307020706030608100917130302040b03030901120c0203090316050906190302060a110a030c02090726040602040e10050a060f080f0604020d0914010f0902 78
    0x1040c54030351070031189100c16070745610041e200b0074035862050012900b002e460144d901054401140a503125408446803256120740c12402d44120780642040f64100e1862040c008040350894140035200d104000c040801440408106401404201112038541c0f1805c0041d4145031280ca8038454041d0095840c1541640018200000041c030702223001c0d41d141840082a072080c810340d565480000e0513654171000403400200f62559a0092910480018010581d6403400140040c40d6404c0e51142c480d41d1807850b0204200c64121b19418824480c4001d4550310035102408455a401d02c00e40390118004800d00510084003001410310341480740307040d40089000010300155001180c507110014050b903d034540000a80503903440a02c07401044800d02c1130800c0c4118681c02601e006844003103001da990b900480340c0200900c030310004140184003049140203050685640400c02400141c0780c8001134011408072003142c0c0c01503514028065410141c40c6080c0500d030a4210280014010318180c5e0700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 7150645 1250 7149395 7149403
    0x305091305040b04020d0c0b0c07050a08030405150903070b07050109110a050d020607021507050a260405010c060608070b04180506010203030610030e01090b07030f0c020601050409020103090501050106090807080a020102 96
    0x4042d210309546c420b620f0800c0320b6551000040c10740305905586400380200d0781780d5250500d0180fa0310840d0a11004a40d40380c00100745c0e011950000c1100a242d1164018400c69900582c0150381501405c180800e024016a0017840380c2c900c144e000143c40f20880c10000d42403031800501d107200b5400705001304510350311058a41030283c1c04640781d907a201c4141c400600b9070300454002c00d042c0140031070302c5010f0000104501a519002e0440480c9160030184405c4c58200004940140d00c1d8060205000c0ca500c102d8240a80d5417080a001034850f071a10001450400c45600030080448000cc0a0041980b0b100103201600028642440141440c40020f034581c0001000103000b2207003110840d5005100c3d0304010150408100204100401820071020b001070032030350320011030b0a29940031003010301880340032504c20056000d081c2e16400d000400014080ea104107a04058030394036140c0114900b0321456000300308036100c104030907191250250030280942e00c078891540001d0145809130360041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 7151895 1250 7150645 7150651
    0x703030906030209060702040609020913090804060c02030f010614040608010e07120317010b04060806011701030314040f0b090102010e0a050a020103050a02041502012c030706020307030204050d0305091305040b 92
    0x20401607110180304d8041041c07400341e2440658894140200003544402035030043c0720201050b02c10032415455010854183e40740010018807840d410081008524400d040075034040d4402801e942c600365a800300c480c00d6607200c0d00700303080040f407281403039040380f40901c1000700510240e8001c0c8008501007072a1501c400c44c034468007100e201480c82c1710b000c05118a401d98448642040000444d517111081c007403590300540940d0010076400c001103092580101c8202c0726440080c1e8070440b03645e0841ea0b0031900d0320405090101c45000902010a80d0340c221881c1030041d002407848151202c0352a00024250345080504540c1038104460210120f040800c0010070582c080c01e01064075244c14041b44000e00c1143c0c8988030f103051002203800c0380d69043d003150358082d00794260ba075401c010203d4070035001440000040b44540c010440500050b0310794000d1035200503141001030810b543e440c0807400140c03144400f100010000285074420380750a1968880505020804006c0c42ca890342e60f0701e000101c0a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 7153145 1250 7151895 7151897
    0x303120b06040312091d090303070309050c0d060b0310060e18030d02070501090212060601050a0e0622060801080309010503010314070306020409090b06040902150705011404080c010e0703030906 85
    0x5481900e41986408080750000c60388199074114180031303014001e10a0110307000e20040341c00c5c50741d65660400c140700101c500801941e0041c620710340301e000341600100b100f80001c650034080e0619007030041e5611124508414011440072480341e114104150500000117030502d030281c0782c04c3c0140103030f04d000e51400d0f520a090381c1414030b810b00b4101415156014002c2c1c0740600c107000041410401c00c06410205005100740c9200705c0441e046481c07551104401c444550005005004170342e402403240760300c40382295016190070f14002020818a00c49150102c072040d040c00b00c84010003060342c0c84449240141048805181060b46181c0024440e01c0180300107000f00800651840350b581c410b200b210021507121108640d6a40d50f03018000c00f41041c1c0e44280c1c3c00c000c1000015806082070300482d076001354000d0151581807107020710340c3ca0b0750704019002d8481c1d43d640e0020700041d44000301094007950207082015200c218041c03401d030039108100d1310203481e500005810030000342c00032390400030341d451 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 7154395 1250 7153145 7153151
    0x1206040908121810061401030902010503070c03050f0708031b0a020c0f04140f0702010b0303040e0609040f0b07020604020a06030c0905061b0303160e01020604030503060f0a03020303121609030312 86
    0x5140d03044400c011001a0181c524080d04d01c60311340007001c50380036000315010030031280003c0d0300041c01542103415440e40640412001c100049030076105200c50a89a442402d00c08d00341509406151f581e60050708044441800c0002400101c820b108401c042ca0030081c0d05961070412040303402911080b00041d01401488800110041591a40c100708809104100303882000d00e400300c1a0700c103488080d10050003552804501d0122401d01104450984d10384031400c039525101c0206000300c4d200000d105544c00100b050340000054489034145000c2d00440d40100385e40d050034010441e5440469001170145450851b60f82103854000c100310f07084a404848058a900070084420101812800d1000c070310b0000004001c3c43c0c10910a444070745840646c2c9213a04500101d0042ea610300c030586025000c500203200285151410b80e41309c0f10310100c00741032010016035990202c1e14640249036050035054403c000c01a002c00b072144050411495490045212807071a20080c01024819503086400c0c0c0d2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 7155645 1250 7154395 7154401
    0x61409250309021305150a05010504030c140d020303030408040905130201081b040815010e0f090303010902090a0306051302030610140118030c0b0703020601060315060f030908040b120604090812 85
    0x41c498004c0f5403190f549003014031282c940b0341819011018555917441c0714180003100440c05512074010b071001c1e694402008003c660030b0244209070181111071455100a070610340c6001a1404d10156008920a07601143c8841c100507086050700e40c0206a0484124407040c80340160b0b81c0b08903140d810000207060542c9030502c20300080703001e02c25130700001040e1140d10000ca003600f410101582c1219641d1b41401d029031201800c280c0c40c0306040e61030f061540e10070b1005001c1d208159005103d02c500c001c00030780070349036a0354a04064a5080b51030340c1c980c00c201032076002507003400e001e495445158a4180003030305080c41040021811004101810820001d038031001c0468041c400c030700a0368220038030000b401c1d40c1d16401001603100c100c1c201d0040c082e07031000142c903d0182c081c00a0902c03100f2095445039003440021616901d030032071100704040c1c44045030b1021508460041029006011129075203010904020301d020402801c024055403909410342c0c0402c4840059402c1c0500790926a0396a813 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 7156895 1250 7155645 7155649
    0x7030c0b09070501030e010203010e07050a111002030702010e0105040c061b0b0f07020706080105030309010807031401080706022401090903020703051005040308090c010f030f0f06140925030902 85
    0x1150010010304518188090003904070000920304110350003680c00340400e250100481d42030340070a2103590540440030010030490741c0900c0c09443d00107082d141014002000c030448500e0034401007464811103a0001c1030007141039080c020400c0780d06d030310b43c0240002d092540c0d80d00746142c0c240c030454040002c00150701003c00007001c00800a00e41103503841a2605150260380003a1109a42080c050310a000303001890394040d01c40ea40c12200024051403c0c6489500155a020001003000040660300c00c0c040705812101c00c640e038041c10408004240041c2401c0010746014040024010505800e40300615800e52000d0300701e040d1140040f02140e000514601640b415040345c1001303145000e5030015000075000d40e4003c6116600030380d1410380c20380391040003640703412038251040e00152202e00094045402500425160800100001114030242c03021034101e44d00c43c0c1126030701003441003500d1330910703110081d550061403040c070200c032482c0034021031516030404124442c14142c84031204802e41d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 7158145 1250 7156895 7156907
    0xc01110f070b040e01120302070603090f120206010305070b0c03180103060503060a0b030d080103082a0a0311070605030601051213020d05010209010909230c04030215030106020601050402070201140703 88
    0x151048811201c105464142080030303600035015800c0460f52880002032101002d001c183c881c180c01d5000740c02c007a42024421000341c002c01d141500d00c000d47c0d40c0c40f0b10000b8125003e110550206501802e0954114940303030b820200720740d000607042d100c180328214040402000300c1e143c4941004216032114069001a001751a086e48030503414050a030400c402a00250420b9041640813016100e186236401400d8904000a00024244e42400c2c00340c020340d110070508000900140e1240481e40c85014680e1501c0c1c6041c1c22021000a42c1c6443c07076210075001089014040c205070b040140c190724090000900078020051302400704030501c8007203001d00c8003808010034a240c02070400310100710300b410304c00d0107540110066400202d91400c00100d1405505c02c0800302c0d00554111340d141fa108490200c400c500103400c039040d07100204000401642d03003c400c0752814094006003034607507140031300290070948140c0c4058081c034010401d460040c3e90100300c848400c016902c01c2034030380041c2d00f0b0071540c1c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 7159395 1250 7158145 7158163
    0x50f041407090303090501021c08040516060512060a03050c0d080c01020301060509130c050904020706020d0e060103020102060108070b03010b0a020f0706050408010b010306140906060f04061707050a020c0111 91
    0x10082100144482207034001c02e00420f8a01946803284580e6440f4012aa1221070072480b0780510400300034107a410784108085600540030b142100c0c001c0d22002d4004000c1c2c1015800300b40403d0001541140d18540c1d1303d44194060381c01c40f9440c100300d140d510b6903902c86031410141ca1003016400442c00810400c00c058403085107041000710f4403503840d0341c005071040d801100c5440c0f007400b10184031055024280505203d41d049039640504241c1140c2c00d04c0060340015804490040d000d01450128071881e00c60081d00d01c90400091120354558000613040c10b80c10382060030301340c010a00501021000030112811143c052f0465541c2c0c002c50031080342042c2190040701014020340c24002100f039440000b42c0300351f6072108000c10480c2c070060010340c2210344510412500341d05401c0740700004d00e403000d9902d900010140a40307113417003155072803000f95074459000b48010550708103803141c103118a031000b0303684034485e401d19501d094035a000c042d5542c0d0301164018100b114084401c06112001d01c642d501c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 7160645 1250 7159395 7159421
    0x3090507170a02090a020306030d140904020f030604060b3c13060e010c0507090c0201090b04080c0705010302030f18030c010606051215090406020f09060403150b0102010203060109050f04 82
    0x604100014619501c41c240048141d105413942408030ba081070380c5108403802004010000c0207011090791054560300c3c440e044c4540c90361014021076035540c03141d0000385200b280380c1c0c00071580e901c2c116041004444050300305001131303602400503180344030f40042410303080c9140c195510300320001078541d0407600c900303440d42da210a44042604002030940d40076810070384810b030b00c82414006041004441c1d44802400190455022030380820054402d58401d489a0516100206000307403642c41d48100c1d1202914103ca12010020301401025014005000944401d1806610f582000000c0050444011b4400d52007451442024141e0f010200200c41071608000c000f80201c0c0e69806018125400c20707190000c80d040004001071006410403202c910340380c030040c010002c9803103644450780290824020f016030008100403030501503580360301800056110b2400090300c00a05255030060302c04031500176040d6801030003881480d1780c008424005442051b0f580882030880300000a0252400d40c040c02c13 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 7161895 1250 7160645 7160669
    0x5030a1104150507020102010e0f0307020405180f03070c050a0b0405061303050d0504030506150a0b030709030804090b030d090e06010e0102100c0c050d020303040804090209060d11030a1d060703090507 88
    0xe0454000e406011100c5c000d8000f0031100e18400c9009842e00c0688140280c0360304108031400041c0740c03d500c141d41083c024a0501c44640c90300d203042e440c01140e4440c000c2c6035800460307a201000261551540640410b0b00c0c4a030005160204100c0709021740c0c02920711451010070746a00b44880b070680d0100442c1c22400b201c83d640354400c40079110340d020b40815603441c0a008005414410100e20804402c0781c0549007007611860b1980319034041d013010300510204035410b030000011031021000340000d480741c4903002032035441101c2054503100040100340d0a0140c0c48104202e0400f09a181c00e42c00b103800e00307001c0a0100003c004030b08055482c0720480c9241d00e07000400d101a0b87c4a0382458040e48140115110750032510700c103903a01d000c1100c3c0101455810001400a052150007a044030034001d05094140f096003c03171001510882c0c00225800790010041007a684c405001d034580c1c11540e0b00446e40d00c1c0000360f4004c0d450300c40c0100071206064a8400030000c00c4400c1090500504e1400c22038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 7163145 1250 7161895 7161929
    0xc070809030d111b03060408030601020f060a05010609080105040203120c010b0402070b0402010906110703020d110d05160f1220100207080d0302041d1f0803071406060105030a1104 79
    0xa0a045100e5801e02c102d44100455002964040d01001c40964030007401044560b6823960b400b02254001040241103005001d1204050402000301311b0090b1094040400e056042200003040312004d90f1003104668140401c0c40013513100400c0e007410b03c0e2411030040b582c0b1003c0150701402b40c040c1c48411a0001c0c4001641c0080c4424540424080c0e8403d99031980c1d8603588083c21901140b03180100501c607040140108010710b03042c2500400584038400c24008c1d601501d00181100d62200c2c03003512550003c551a0b031103e2381c0e1000100103003001c03200c400102402c20842c108840403101009000d24403029011224a0703052889014510000f4504075100f68411402911000a40704000380c6103c0c0c42d203020401406802960156268090360340102e14481600d0f40e00c1120203890821103044000c0f5080b441c4804c0d5141c4030207402c2e01001980d54540c24030740070070031082000e102051500036806221403a0780c4030301140c0d0014082900401d44040003010046135100301d9000002d60940c01c40c0c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 7164395 1250 7163145 7163147
    0x50402010e041d0a2901050616050106120f030806010504060f030e0304050409051005070503011202130b03030a020d08010503010e0304050d052a010e030114070c0807050a0305040f0605040501080c070809030d 91
    0x3003220102155070001410901c5d0f294071030b03131003030280140790780820140710f00300000d030b002c1d2202c4020a0194001061591b0fa5001409010305031190554451480044060a1680011416402200a01c1c24914291404500030400d012a8103002c3c00c25403503016501d0710f8201041500c024010007002007002840720318100350b6030100881000d061900b05800240518010001c0d00e040340e03c0d04a040500c5401582046076a291080a910010366100030b00f1407030303850402c0606031101080d0002d11240c0b8003c94040d0100d44164400ba210341e06101c0380341c011101c080151011100c1c21751300e80c96410894074105052900e40e0b4a4040c00b502c100c40054032200b4200b0001641007002e807107040082d001c00040c90b00344d694a0300d0308050202030901240413584030314000d090070b5028070320090a209031685e0b003a040160b500e0043d0700252001c10305100c0303040c0c0070041c00d00a0206090a81c03510b0710b4500041c2410f54000c041c960100b00114000040c001d540d0101e880342c0c00010290b030200120104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 7165645 1250 7164395 7164413
    0x10e060a0209010507060b0d0b041202010605060c0a0209100803071b050118150306050603010306020309190b0103030c02010c050319020f01020a02060103080c0c09010312020105060103050402010e041d0a 89
    0x14014505215650105100040520071682d8031081030b56518039101e01c50301c0d05405000ba002819812005140303c0b01c2c0407801c50340d1106e0141b0704c00c0340140340c210b07484d00000b07003980c1c9035402940c89803104004488502000080e0040c00940c1034940c2040c582e0340751204074919415501c0240a40070000d00c00c010040c4241c1190210340d075640510048030b4499004444207250b48110008092022205124024038140c2d000c144126a15020401c241c841001c034040f600280d2045a1061b00441403251101d01448101c01c00b008545a10400c000c40740c032190200401840060184100c4420100559201d484261210b5812408490740da20030340c44480e120101c080c50380401406103414114401006008541441840ba0f008045503425526551425404000d09060034031500381104160303110b0f11410b0b802180070f49180b0302118031381d9601074256080104444d04061800d8100001070b0b803c40341030341c10b4010564000565922641204080070a05e0131403440790310032407011604205183d6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 7166895 1250 7165645 7165661
    0x504030b100501030c08060303070b09010b0a0f03020f06070c03030806030109060c0806090106020d02030906030907090c09090e030306130207020102010e0712031e0801030f050a020a030c2402030a0c020f1201 91
    0x80c4e01006440d0b4100000c860a07681078401c00d905400800c10040401c0b64011142d4000c0200d00000458003102c2000803c00b000c1c66025108080303c100d010415464160010220280140c3c3c2692500341c00e5510980402d51340e0100800340140103010901585003503101c0d0382101d40c1310f042003006008900d0040e001800454000d8810290303000041803091000c10510052040b82e0011802c100d10303e030030070065800040041e82c1d6032045410014013031a481c003521105d40c5044d100c0c0c80d075403400c0100300008e8412504024443c2c1e84108140800e80e21074102030708066111140050300d410142c03004034054400d0301201c0802d88521040442c000d2021348440b1042da1003515210700c244c108802c5107440b0041c40301c3c031202081c40c250042000c07902040080760220311a0054031007001c0302c1d60006543d000150000d8440c800816824007404150144110001c008408070640c3c40064400c0259241b290104800400041403600c50464540d0161f0404d000d000800012164141003903ca00074480d20b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 7168145 1250 7166895 7166897
    0x201050c0c0409060207021f020c22050c19030c080f190c0509010f030e0d0c020303120a0c0909050603100b1203030906040b06011106010603050c0c0303100801150f05090402010504030b100501 84
    0x4803501040ca414011074288c0c1c0a02e1540180182203410020000800c075003013940030150203078130010103030303090b00780301e0140706400c40600c040d245e03178150001000140702c241080013818074001c49083c0313132500442d050380d02aa400001c0d60443d5a442c00d58034903c0707114040d018000d4100200c4901041e04003001c2d08042e4001e0340c464141401540c8100c06840d06403c80d41015000500d80c03120080c0f044c21121803041c009001c91349011402401c15040d04000c030b0b0200c2e0543d6586214220807548500f4020003403000080501240c242000000d48940036902045002d580d52440e203030182c0c4860794000e0f03450800380c0540c2e8070b901d000b085054584138102c800300d54800ca9000060969805408100f00b802030800c01040242e00b4040107400400020b840209540f40c14402402845003c0006611546c00c2c0e003001e049151500d4009400e40351000e40b00c12810307401c80750500c0f981c002800d01e54200e400c2110b0404c13442d25030b0300050b1250322650700b010705030390f0348082080111031001d40d41b202101e4003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 7169395 1250 7168145 7168159
    0x6090c090801151a03130c030506150603010e0f1b070602090405060307030803010603020a020703060c020c13050105030a060b04060906030c030b07030c0507020609180a06090501080106030804030201050c0c040906020702 96
    0x5000405150f20300b1401450043d03089203043d201c010000308051070340450040c404081c010f02544400201c40b416a1088640e903005104220500c6244801da6804141c00d460303160965040001c116a0756100500f41c108100c1c070b80f00014540ca02c44d00d140c1e42c1500c0700c0c1c06031941d540c4d203e0078658081d5012802043c080d50810f008200c81e804c0004086044980180c078082c00c41e400c104044000e54803050b002011441413450210120711a4452260341511a400a00e2a00c8041080c02141401d00002503074032850070004000e0380c3c4000c954001556446200002d5402c00030f00000e008001540110240916142010040090306100c00c0141c1380203500e030042680d19954102e095582000408000410600464005060090290443c200010400e0001c0c400800c00c104c69800d00311155607a840e2030702401c0001c0030070340c840e8038050601c0c90024080399042d6144c0b40424800d44c84001d0400000007065540042c3c14020404522002801030180210350f0409501941029505030b2003014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 7170645 1250 7169395 7169411
    0x10050301060812030c131a090906040501080d110f070e040201021b010c0611070510020d0b01020a05030f030702070b0d0603030306050f0d060e0c06030405030703080105090c031906090c090801 84
    0x1070003545409080f10b42ca441d59540c803410100da504040d100301000c0240c40000719206100c1074200d11600d0314050b5403611860080100060000c1c0900460301880c03604005120f0f01c0703804174065280550302d09016040070482000d40d4a05041a9021125406400c8011034940f01c0c21401600440c000d0f4210342102c8044110f150309490044140350110b882c200f00680010b089400c60180c543c0c05a01305802e01c44552101403c150140820712002503000596040c82c03c03072482030803603802080c4010605101c140e900c3d99602d11070100c64000100010000458003842002104042c0038214120342e11110701281e4100a003406000c02c0700441e0a00c10040fa15040018124001c0900101042a04146038440d84000d01a4546040326409009070f81001d0781c030380600a500643c880e00c0115a500e8050400804a14060300190310403025030003880b2644681c802030780c0e0400c1c0d2021744c0480041e03101210000401c020790040804034188032003040d8690300b180000003251a01c000a1085031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 7171895 1250 7170645 7170659
    0xe060102150f060112060302030f01050f0a0c0203030f150307030c08070e0906061002030f0a0512060604050607030809010b0a030b04030905030303010f1206020405150307020106090902090403030504020102070504051005030106 99
    0x80411100c00409442d0000042c2103580b02ea10224400c4400b000d001400b030362a80c010908058402c881603103280e450700288280c02da4001141e0b58040d038421400c10405002300e10007900ca2001900c80c8101550580c0458001c040700100c00040070001011030714010354030b150120250301944120440d80c00b5190001400e44900e4410602c5481608090222a50f580f4200070701c450f00039181c041148002d11441000d00170003001480035003440d888454a5905d80b660109050f0001405180275000c2408100419180c5400f5128210fa05040102041e92070f560400d004080c0c01c0c1149611038500c0320000705000c400b07070070b440c007540c001d650b0500019207900c207241c0e1724403003841400c00040e81034030b00700040d202c185d014443d01071003100094602070b0b03141d0019103180c82c45014070b1100500017042c04030721602480b03143e00030190f1034010300c5010f50607000558420801003003c5d040c107803500c000a04580c0309000400141c00300500802050401d456003420382c11a0b802101d0180d0320300036010030382e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 7173145 1250 7171895 7171933
    0x80111040302011403040615060c020a0f0602060708090a0215031e010302060d02130b07030302090109150509060a0c060c020715080c0a0f0909060b120c07200d0204060e060102 77
    0x750380c060711307007074240140038513801401d500c02030040c2c3d4501c0d681c0180c511004d482c4400c0c00f004105668400c4000d03002401041200102d507880020540c1c610301040041a030042403595005042e03046c440643c2e40d6021000c2e00301480100002d51080444003024280364400e801b56010340034007019120520309011124008131800c0c00040d5120f03605000260308200940c00812112110203034404016694034400c4405800284040b4040f903000300e035051555900812010040804403001803800c10980c00c0a80107100340e0054900603100021034071003a0740640c0c40064816800941040081c5d04060000e4461420b070043c1c000c00c800002c00c2c14082ca11403410340340604540718000d8504040013400341d84501c4100103020501c240d0750310001d2001024030682008100980942d5a00c040c0401220303407a8000a021501e02d5405000c1c1001260484030a0300a00c0d40f0f00c043e03d0b0300ca426002c005524150030303000081d4401e0408501081e2290404042c0f4003651084e003c8500c07031030742c520603183d113 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 7174395 1250 7173145 7173149
    0x50f010b07020d0213090618030305100b030705090604080a06090b06010e011205040201020705060703020f0106050603130201080907120c05030106050402030606070f0c170c0f010e011b080d06030c08011104 90
    0x1c0412124144405454560000255034040380e0000038070b84003943c0e400094031403003510b84001c230426031500e03c14560540070700c65006003860041007001d07040c040d107003983e4040078000b041040004202d0b51050b0301d49404580192a01c00200c5682040601c1c208014209844080350100d0345900850031a500500c200401c0100c143c480712000b25043c000000201001002039045204100d800034182d03c0741c000528490f80070b540901104003a00400700d00307490719640040d004220070800c00088002c0024580d10705d41d42481c2200c200d0321103a1000780340c00f1041e04003c881240612820007007128602d03883c011a08250001d000071581c1c2d5041004070b01088500c2900907004120500000343c1c41d00b01818003512803c0030380142070711a000002600e603ca50010b040f0b622202885a540c030b00740001192060003413270550150001400000c1011021740700043d0071050600c040c01c10009000290340da8180032200401000c0d40e6410403540805092182c0e41c115417819011542c9420b0010846003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 7175645 1250 7174395 7174399
    0xb1f06050a02030909090102090405011701140105060a1d040c0203070c090501050a0b0310031205180307031203020a0908030a08010315090206030403050c01020d0504050610050604030b011e030b0a050f010b0702 92
    0xc04c1c04484010310500d82401071551314170f550700f044000503e5903148103403030117132200540036034072070100409850031624005840b10300030f03002c540100036a03980e200c00c0b80c5003000c584c40e01405003440307000d0516503c0154007070035134401e0420a01070811603001018040c03a600460104c03011550300c0008808540c0300380909500240203040521141140b10b0003140c0055210b08085501c42d50b03074071016141c440c406540c000003480060030980d403003170740441c07c400040d0450282c06c000c0e15603aa100080003014010006064010904e01e040c68000d240080062810030142c039980c0131213290061460700d00340000c44803000301c24400c01e0010700c1c44c8100070800d0742c050400d40c6940c44a403030542d995041100c04240a41d001c10240e08890b002c0e004590080c1c0c0314900600305803d01e00300040c80c50806401281c01403505000400103e8500d02100e81100c078000c2400581425400413100920050780002e0440c209101c14000e10300c4507680640e20601a80402c0c00f0240d8888072812241d00c91704101035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 7176895 1250 7175645 7175647
    0x9080904150e0a0914150414060708041b270c08070903060213180b03060714040509130b01170610150e040e0d0206220f0b040f0b1f06050a0203 63
    0x41d1081003d03501003110140116003032800f820404003010300d0724503403011281280500c20709000030010403078140741030781803904040c0c0030f1450f01000007044108002d0000e0101100d5100502409806135022405844142510326983c9004807104d61140300d400d00c4880010b01d86510004400c2c800c071070460240003260b03550700110349142ca03907002a4002000442242c19103030400101e1041516a0ba65811505040414008000001c150a00b40c0007800141804080307448d006140308983d082f80c0c1500c0701261894910b84070107035101e00b94036103003e00903c0f44140c2c1c0f00214000c2d00c0008100d003241007039812650117580e8400e94015a09080c800da01030101d01040020100d40030b8100000038280107030000854141070141d052031f03c81c4940064001da000a01803041040044001c2e000d8038100301541d00c020106540c44144040c13940a0182260b82c00b040030500b0401c0c1c420003074074101e07040041c2c80302a0410581503130301c1d1240c1440e22640840056000a0120700650a941c541113040e0059 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 7178145 1250 7176895 7176901
    0x301060f09020c030f0301060f0201050705041d150d0807060e1603080307020109020301020a0504030204200319090b0708070206070804081b01020705030a08180304030c03110102010b030109080904150e 88
    0x801c06900425510001070009010a001404104002e180200f0090741c800f20000c42d03c080207030071660050115000c121082000307100d43c0203e4521880c04e03484010b00c428031a0f82d00e1880d00321301c20400c01031691104541000c0c0042c402080080c00d40325005410801c03c00c0c16940c0c0f1190741e2803031038801005c80e061420f410000700b06194050340d0b01100c1d60002041d8402c11f80d00007800c90348129680d8011274808203050095003094171400707c0c01b002d19202024903103c0c0c88100000c0e404010500b81c0009050075000d5545146900134444555112841040c0350800440103000100300b1900c0e0300051103060000740103644903030035841c01140c01009103842c0054410080c44040008170381c0281c159000c108810004030108000d000d59801070340c2e40b03405070800000c020307000d000c3e050309030403181d1084c002400070500c034001c2c603c1100c0d480400703a6952111040141e026003800d1071482d906500e03002a54061009c5c0c600184940b100448041000881c0d903034444080e0fa05502900b45500e51360400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 7179395 1250 7178145 7178159
    0x30a030e060106030b090412020f151b030103081e07080d02030601030c02010b0907080702070b04140f01020714040209040603020d030e01020d0201020424031506050405030d030504030c061a0303070605040b060301060f 95
    0x40d1505001030709c15a2540340c0807400c4c6911f4400c04c00d50f00d400c45204601000400030b9038000035a40009102041c51079540345448800305402801a00b94082c00c1c01c100d5100654503100171985404d90000d00980c0f1348030000740d080001c1d0411901240400e0a00030103e580034411302c242440703800024141200d036100d440d400c5607031540007401702c030552040c202c7c0410310709041d0010740024220b0307042336003881d240c100601c4204002101001c1c1503501c203038814001ca401000030328020150580f001030722410800006000f91403681e0001c1c0d00301d0130341c0314400c0515a01c00007880c9404420f0302155010b0300c0c4003c00f24200e1059100d54058500c0414000e180e00c0f18600038610700544901d40410b20074494042e01c4004207250303000390041140014100315600b428030140004501c40c0c101001a45440c2e107003c0c1c0b005290440080c01740d41e070307180100d0340d14904811a08200902400702d03501c420782840c01100505041d90161940b20f440340001e58035150500844050384c004402d5040010702e0045 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 7180645 1250 7179395 7179413
    0x50105040207030c0f051207050309030f0309031c030b040e0606010206010b03060a120f08042303010204060806040b0d060c02030702040b0f0d020108040c12030e010f030c020705061b030a030e060106030b0904 91
    0x1204803800d0140300b000307d5445d002a405401842e0007100950f1350b0382602c2c0101890301800d00ca4041660300f043c4501c00d0707140ea0118030038000758082c8000611200304a40308800426410308842d40c0149010b0b02d81c3d1b04681f00041d19403142e482070b0200d904c140d895074009082800100e51300f40d803240e0041c1050010000c142e0703400804a210f80302e2015075251036a14084180c000782c014003e90f00008d4241004500f0f850b001011908042c0e0003185000e08101c03008040f001e00426250055490300100615500e40e0001c1002a681007542006040c5078110300a40360b9001c01816071149080940031861450400444440c03204001d02c0100c0c40c8059030b00540344900010020b030b070711000110700058030005808400000394801d135116503200f00f0400014141205c9100c00e1400c16203800d103902203c2d40c001a881d401d403075086420580303800ba03052a100c01c2420001004810b0300000c03580b0030901d9055001003a0452081c800d80e105a0380340e4208074202c13441403040743e03800002c1c103011501142140e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 7181895 1250 7180645 7180673
    0x90604210302070204050103060221070905010c02011709010501060f09080307030e010c0506040c090518071a0409020c030408010b0108090703030309060603081602130b030304030b0907050a030c0504050105040207030c 95
    0x1c100503062109540009007160000d81c010380349a0340010354014030b071700000c4800040401488490190741898403005100c1c04150081728103215032804034006580c0039520500d0440040340308820300303203001034100d4040c0c6020320841d00428580c50030a40294050b400c56002d030b4036a900103506007401ca80f800c503514070110010f14140a12100c2e01404101c0a010341c51083d030003028007811042c5001006000c540005000901c3c2c605000803401d8024008100c1408859004c1c1d060840302404505820b03662059501c8040780c940f000441040c01c502c0400680111580d00c0c000300101012040103480c2c2040403900f108081d04414403c2c4000f9020b6840800024002c3c50009400703a1a82e940c2c115680c000180101c007500001c00400452414000d00c0b18a120080018400e1b4491036021981e68000d9010081413031780e480c000900540810018070004000c02045031270a503590341080485503866001d624061405c1000125071800c103030003128016980f43c1d555100d2808241c86a8141030598 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 7183145 1250 7181895 7181897
    0x70206031f0f08060702071a0d0e16080a02030c0109060f05030408090402070605060a170a0b061c0b091c0507120908010518010e12030601080406060b03071709060421 73
    0x100801194a401c00c0a040028040c1e1000030140d904100d07030047e141c218241e0000201c0c0c000583c080f21403240b00c06c107440c0f11510307084000c42c4d00c4143e40e410038101041900f0103180094111800030303455000040b01d214040c025016500b4000c000e0004441c00a01402a94089071803024000780f05440b6500866109029001541c10500c1500015041e83e1050800342c1e0744c0c94880090003100c0c982801404020000d14818134102d008541e10140c4030881054040d0400c0c1d00b1500103070044d00c408c107002140010138410034150ce402031818040c40c2e0780645400e40e007445450303844a0041481080880e141c22a03854550400d02c02d640e03a440310701d1640414504001c46004001900c02090003042d00a80210040c0545641080165030864681c07842d8408140d10a00c400940340c040c16040380d4000d00b007840d11040070340d1303103050001c00b6064030340c0031400d10b640c00010000025031044840001d04485098034005480345121643c0e02c23042a50080c00c07a40c0448501c039080c05410810511074482 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 7184395 1250 7183145 7183201
    0xc0804080102040306050a0f09020a120305130b04060212070201080f0c0705010e030a1803080d050903040f06030207020901060c03020c091009050a0e0606031501030f150207060c08090307020603 85
    0x320316000d420790308544c0c4201c90050f112400e111149a5a001f104044401041e042007800c0c1641c0014902c460a40b107030b04d180848040c0c4900c20300d4440e208840007240160118101d69130f4800410300c0355803280c8904401406110980541c00c0d0104c000c8500ba550141e6275186982c5500040383c10340c201c0038240d82402d200070000000005d0081c0034001410412101542d201c00000703d000d40b03402400c421955001201843c2032000442e040700313030780a05680e0307036001031541e840080480c510710035034100003040d41039080c00061466042c0c000703011039442a58a031003641d0340c034001030b10610b09402b030003000750b0007604800c1c00c00e086c8070452a034000c0d1a502d44181003561189030300100d400c00e80f840c512440d00c0c0e40445c1e041038001c01c8055041401a802010b6102d80440c0008281d00103000080120030002458002c3c4001390725079000004100c841150f98103142e241c800002e01241d0400d03400300d00d0309000942800b2000c4103803400307260058000c2d803a650381c004400552184501c5400c5041d28 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 7185645 1250 7184395 7184399
    0xf04151101091a1008030d090c0b0309061504020702061b030d0e0304080105070206010509040f030201020405130213080102160303020309120403050a1406010b0406030207020414130201030f0b03060103030c0804 92
    0x5400d000b0340114900400f000c0c9000c0401070301403c0e030310400800028003010020010071020b0b00000441d8032100c02d2800c009440046131400715564801c81d445a6641007020062200d100c03404100030707010301001c1020b10b2803008400144000da004907840030350712000600100b8900f240011110054043c840103503803512028840d19005c48080d1000450241d0000c10700340300c0c420003481015040217403400102140c2d0b15050004008900c010001880c5219401c0403200f058000d4041d200980320040149102d500c4403880c2000039000007280603a120f502a00000d08900180300325105488503181c2441c00303003481d03101170300a940058810750345c9104040000d00200420400b4101a5120758090600d01c039507824a02150403212440002c2a00000010040c49914008641c21240a41405621480ea81c00001c00601030b8550a1002800c081e041108501181c0341d03406106100342c030100001045040c401d0215040c521016416a001780014004680101c00300160184502d1507130f0301e019 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 7186895 1250 7185645 7185677
    0x40b100504020a0906030509070e061c0b0106050304021009030b010b070c0504020403030c050d030b010c03030c020102092e020703080702121c020d09050303030906010902090109030f1b06050f0415 86
    0x80d01c281c0f031100005189040a0064a0381070041c0d641019246000b440d05c02d05043c4181c00340074014188038400c48448010350310415010401c420507a8101d00510015a512100500940c0c0201d80491040f004c110440035411f00030701100054a4000c3c195010507800c0c203202e0749045d80700c0f42c0d0030b5510a414420001e841c0e9518001080650302ca40c2c0c90000700c070350a00e0803610344400110380800345801e1001c070030103599101c26080785440d018500483c1c400320b006800e03402489004501c54108802d490a038182130704520107103d1260303041c8007031081c40e20030780412a114052400010001d05041003001d0152a00d540101c0e0031011a074280d40d410040b41039000390b0030584146000250300310078460021150440b0600000700f030103401030b5140d1b00e081c000c0141c9038107050107038100b45a80800d81c402c40741d00c1080344602942c1d100c501c90040d10214104284480c46011803a42c65500c0c0040109001d0711400c15a404200c2d443e0089042078103006035047c118a60820850400c111140161400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 7188145 1250 7186895 7186897
    0x9050303010f03021f0503070302070201030906050412080a021c09020102010204081e1203070e0927030c0105011509030f080708120601080903030705040e040c05030a03050d0c0e0603040b10050402 86
    0x2042c0001c568041c0c645940f05001c05401102e01611104d0310072008010344035008000c5070b83c810018074005a03242700340d200580c001c10fa076100103440507180204200800000010100c12201d032038441c03a80d030340c1d126200201603106400360f0100048400e5a81c0340001e420b034010296031841400003605054981203030524252040702c0001800d2040342600c000190240007201c542480702108500e14603103050301405103008419654050b80050300056502141480c8554110b20a580202c4c250074020f8181a0790707030000d0b07100c11038652908000244482d080c1d50340c1a1615420303100c000501c2c0c0b65881e111030740d141d110401c0d10504410010301000a4501e0000e120540040300700146030700300384000404e004002401d0b118681d00c10414003943c0f40d040001d40d402c03500d40d031010100ca90394500e0400c000311440e074072864162090013002d404141d00030004d08001d5030381190802207040c2c601d208030b40b0748100e801260341060040012a021821a9103110b03801110b90350703040220340d502c00100e000c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 7189395 1250 7188145 7188149
    0x90319020a08012903060106090b07171801030e0a030816050c0613110102060402090c070c08030f07050f0601260f0a030206090c090c03010603091505070306150302120a02030702010905030301 84
    0x3c4c0000a13030040c0040e6421041310404030140c0007040c4940c1801006496240980902c414011000c2180741c204080c0c600d020380b080ea066440980c44002c102f0200ca1060b07001c82c40e103400710b0300340343d40040207500000c0c0d0f032440150981e840800340d80700d40c1400b101441d1096200001c1010402c4000303c1d8060404c0403074051410121410705503841e90808444c0c07401c00d501d102c4c2c110340110b000e20000d6914140c070b00c0d800130280d5240d2a903c4049250165041200f5800380156010200e681c140009181000d0980140510165091100032130900d503110002402588007450310001e113000f2854680302c5210604402200301d5046012524829184c100c03219001c50041c3d2100c1e0070050b500400f4016201c41d014140c0e0800260704050703010254602050080804165489103e2030510501c0100c40700e814030144400c100f14280380d80014060702440c0a1030880b01907060102c2c070701c18440d2003216142d29031850300c10440d4031403224030000fa50029001c8800c56480701400c20220758148000c1d40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 7190645 1250 7189395 7189421
    0x613030f0305070b070206070f051305040f02040305120403051203060a03050a0c0311011407021003090c0801090519020306070e0303040521010c0302040605180103060b0a020607020105060402090319020a0801 91
    0xa03c500b00b62400c800c00460040c064070841d080304c000d1081a64112141c007105007500e003492a00c40741d195403400384075540f9901c815803184c10709c80b1007421000960300810a481c000d80640b10398030300d550210f03803a0384102e100003031103580b14200086002d441d0102464020382c0050407240081d940b40c0b2041c5c5400761904045e80e1500c41c4140c10800c11241d8030008481e41c10a081000d4503844c0702117600c0c401c0c001d501010b4003421000780c500f0301061180e4450900c80707034031912506500340c8443d0800d00034080c4450442d094851001c00c484055102e8801911040c4d00a00402980c0d80c0d0243c211a103440701d11050750035100a2002040d40d9460030000003485d1a4241190040341070031003003900b5501d014520205242c41000700f44426a4068120380103058201c210381002c050260040700101150b902005085030003080e041c2da0158041006030044400da4001e000945035141000220f206410105500d503004210200c2c1c005041101d060045000501d103501d41907a030354000f401d50b89a514070b50307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 7191895 1250 7190645 7190647
    0xb0a0b04060501020606012001021b0714010314010302040f06030b0a0209040b09010303020a12020c0a03060f050f0906010501030f02190903020a0b03010e010605030604020c01110307110109050c0613030f0305 91
    0x41590034a07229000040400340b00070240d609203030300007900180035500d0074810118254500000c8131002d4046401070340244047c26034000e50011290380314180341c0100482c0c1c03a260381a8217820742c807078054418043c6070744c01c04058a900e0760303082100070502c0350458420151141000800301c1c001258540c840e040015000d0390798103500d8100300803151420b443c60f10400140c8010b0001c43d40c001075554269500c1245401c0c00b204505041e40b41c6642e07481c14507070103224a980401041203642020710858503903001407016450380d134281e1054581c00c0340c0815041e0700c4480108072b03d40c0b10b900850a0242046801417030410040310f051145600c4603041d00225020201c104114200741c49280005d201841281381503504100c04401b2071201846607504203c004001301e0602e659503070440e4030000312000204000340701d05185508981085407144041076110002d1070030f00506000b200c0b40c069100c8080c018000e40d0300c04210b91500000145a903401c500300e00440003030404200300f40b2644c002e1701c1d45 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 7193145 1250 7191895 7191911
    0x70501140d0e0d030b100206040b0406150e01180e01020703020d140708030f0708010e0c072003060405070e06030c0603010506160c0801050405011b02060f0702100f02070606060507020603010b03040804030b0a 91
    0x44103000700001441b404541c80030041002007609403000c9900103a2200010914008040d003801d00802d041c0c0011070390060040000030501d03094640d600c2d10180b01038080c880c001c20f0002140c01c1780110f20340503002d608200f9444c0040740c81503000c1006168100b81807410b03e20b854039140c5030740d0001ca030303c461244111414001055000400c07280102040e1564a401e4501800040c0081c02005401400e0403442004d10390380414186895410754005001c0f1841440c007401d01603030f100d01c240310b58059142c00002041c05400e0100e01c8800010000c2c04e0186540d183c5002e0043c03a90003900141445601d0302030b01c0d40011400d050f9907009000700400810f2600f0142001c07402c581078000c400a0000c941000c1c1c620141d00426415806107003603c2c9420142d0710780710280e081c25440050300c0300f42d900c3d04035140f00c4c070080756001e40b0b2a68010001002525140e44040c1c070b29128116001e0340c8a64140010004110940e00650b0321620614405040c5035480e80c4141d8001c00541d0380c01c0c507007900c030400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 7194252 1107 7193145 7193149
    0x304030c08090a090c031409061003030e0402070609050d03052202130e0d09031109010803040e19050a02041d06061804021204030203030711070501140d0e0d030b 71
    0x4c0520400710380c580002c000700849201604e01003100c00100d01610000290703584a18401007201803214250b4805a4a100401c000c0310390081c1c00301710000002c0d46500444d2030041c407540c020401550500005401c4e00e9000f0b00c8460541002403560f09507146891301c8403030341ca40580e02c000000104e00e103140701406c18076400d040a0300c0380304c1401c1021030340490208204c03401108c0b440900812101000741030107080c03040340e006500601c0140a18010203111581180500c0158446a114944640150355003210442845640400c0820501c50000e2050101280c0381044000900d0010009201d902810700d42241d00340c034a03505200703542c40e1a81110040a0703183c000c4142c9142c6850025581d50046072010001103801c8203501883c14005070b100d06582c8140c550000354200c0502e02c0c6540d0f0030294081c44656103039050520103603424040c1a080348880c2e075020520324070083c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 7014395 7194252 := by
  have h0 := BRFrame.cov_init 7014395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7014395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 7014395 ≤ n) (h2 : n < 7194252) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
