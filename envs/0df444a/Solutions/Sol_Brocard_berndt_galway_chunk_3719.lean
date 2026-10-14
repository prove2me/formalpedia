-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3719
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:28:32.010194+00:00
-- url     : https://prove2.me/submissions/3a94fd67-3e5a-4252-816b-89e74985ddbd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 668705035 ≤ n < 668884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 668706285 1250 668705035 668705041
    0xf0c0e162c10120f0f0605030c0916020f01050406050717060a1503020705031603080a050f1902070c0609061202031905181603150c02070e070e0312030a05070503010806 74
    0x2403034910120914220f00f4804144040c0f000b0140c01c0d2028503a0700d054a60351140b400c0b507002c16074803586028201c2a0010070040e0107040100f1005d150280c40d00c001418826100c0b20018420880d10355518100390090140c0d0400340741c104051b280c15240840410305440300c103552003c2100c02d49114601c000c0100070034a2030000d64101000b80c246aa8007055001c100910110700100000c1030300c1d145d0382d0351003450a403860130010803903107000e044840030740d003000203004ca40c4501d04480754214807241c0d0207100840159000500a11400c0300c0281082ca0400300001d0f02900f01c9407020884500d40c07074480030482c90354a100c00320700c8100c81d02c0c5400103804c20b41c040080890361190b0381c09440300526045800030725100c14a0107012140145070141c1c40d06041c01084550004241c840c0300060781808054442140a91034909a024011208810400003030245106400f105911034029042d50600800215010440da004541c0c961f00e0609040104688520820880341200d80d0741c000b41044d61 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 668707535 1250 668706285 668706289
    0x509040f08031803040e010e0115020705090c0403140d020d0e01020613030c0b010e1617160504091a12030403020a060507150204060815040c0203070f0c0e162c 70
    0x42c00240c105941c003032014200301e02a400800050011740310b800d0804844d0b40c5440521144000c05800c400365030181c2624200d0039580008140040d00c100300d80d4418140c3c2e41c80c903000040e028651014004803401441c00c4c0102c5004118010361031025400d42c2c81e004198001035880700c0c0440c0c24135005901200015200e085600400b840c164864a0210031804090710b0f0101d84c0e0310280c00100084042a080c0802c1010411007108003001c0b9050078000781c1e9003403201c03d501e02c10040c241ca00318899400030b6401a80f04208071000b61402031b504010003221300300a0030009217030f10300701401040848048170a690000040e030b0101e9600802d29011142003080444003900001c000301e651499a0001d400c14041074000340c40500502d035074009291a012408a09686411240d18000c80ca401c0c04904000e03400710071265802d8000505c3c0000700c00900e850440a04c8aa21501080b034041c1c0a0010800c9000364484204000e41d481d901c0c42c01810401e00e41c00c04886440050800c06064130350114 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 668708785 1250 668707535 668707537
    0x603021b01270606090e0303090106080a0b1915080c2404060f1806080712140a09050c03060702032d0a110102190503060420070201300203040c0509040f08 68
    0xb1445a0400708903541c0d2100c40000f540c10300f0300c1c039160a420200c2000928082407080e0002490881c1c000c0140c07540e142c171900c4100b00c018090348c3c0d09440c070072541c1050700c00603049080c0c11100c03480900b0440f41d0302d0051640300d2451240703080c0306050380c80c022400c1e100c55107040182d00004020b07003850306240c848145d5448980003100024050040f0040d503035a222034103444000c00f80c43d160303089036250085d0300502c40004000c00c4005146060f108416a5160340d0140c2d80c00440303280b0005400050381400c40c80e181800c230304a80d05100303100401401c03036030100140c01c0f08840f4250960400d034002c44085507200c142c0383c14000101050080385a013500c110003240b5042040300005141141d11008180d40030011203d032808103400005208103424284910341c084041400c0c420764003580601c1e032141604c10208060704100c2000722894a60f41d60480240c09291460000001d000c00740f903c0c031000c4c1d0401c80302600c075034000c4c6500142c5c60805100561085602c8000804100c8403541d640b001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 668710035 1250 668708785 668708861
    0x403021503130f0501020a030b0303030f040210050c0102040801020c0f030a020a15090f140d020102131205031201080106060f0806060307140f0403050a060606030b13091b0603021b01 80
    0x142c10b0220080e41c010030100c5000700012030099001682c0e9807070b0f500002c0c094590208806009520400c100481e254646d00c00940081e811134504288650a20040302c2901845000001035440046c00042c4840d0550091040740e158030207a4045020f00006075807280030388490031026030040b52200c40000c4401c07803014501c0f4024100064035803416100c0900407107904030210f0f200c0129101050083c1e0041140402041c0c0520080d8a04000703e04210072003402842032503c7da02c11020804100201071090b0f409404200a001c50f8540c0c1d55800b1078017034aa2442484042800700b00d08ad1650f911803c0b81d00c0c031402020300342d10302c0c645403240216000c01080f810310411110620440c0e00c0b410f40107004000030341c0600009c0c1501030003414120200c41c0150701c090189481c00084004548540c08014201c000c002000103034174080e03007004150900174240c100480c0311011000b04003160154050040380c00c240441d901240d0005c0c024600301d0b888940340c450014600501c42181c038040d14070003c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 668711285 1250 668710035 668710051
    0x3060e0d091503110f180906030c0f0303090301090c0e0604060e0708100906080c0405150a17070504060303170703290a03080307050423150d14010b0d110403021503 72
    0x180c0c000d8211613804072900168802450340500190100d802071009001c010b0800017121003019034101100060b503540714588140740a0004181c05074a56901407007a6212800058000d204110f500d20b04900b104031319015220804444002003500340c01c00b27110f00800d640c0014001d01c43d030740301d0010a80c0c0700007004180d007078405007030400450f40452a002d144001d004200080a02080400811042c1d9500414030101540038000b006041d503a4a1004000c44403408030703040e622202c0c0e441d00c0b400c110385034000c55000350400704008100355200100c0d401103a42180e035800a41c881c82000c81c142c1e01901c8407602100e07d44044015191840003c01c0400d210040034040c809a072a0b440c410303240c20403254070b008a000424100702c01b0080d80071401781c90480c0d9107030841443d001400a0051020088a8004e8600104d20030202e485594800c00c2c800940300e04294a66950382d050400503440307600000c014a041c0109204010540d100740d40c19254000c241d0801070009440d508070a80000300001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 668712535 1250 668711285 668711291
    0xb0c0706081302031e070b130905100905010e060909030702100e060706060e0a0b03030a05180616050d11150402091005090c0a170402010c06051b0c0703060e0d091503 73
    0x1074016941001180703005d4843c50b041c5a84c46400340c1c0ca060600d0120b901c04460702d94104032100d501a0310902d030b0700648588490000e03a6032159055120401440c0d0440d54080f45041d0012500c01000418a03118900032650038200d961400d1020751039009040000b034209110b00491003420340641e004e02e0324100c01412103401c10210f51108c80c25100d8a82c084408842c400341030146142290283d13a00142c004c0d001140713404071504000300648518041100203140d100d0343c800b12a80d441c0c1c00c940c482c1d40c84001603051020386051180d114403418500d100030580000c49180800c0c000f080074000d075824502080c00ba6035031a001c2c0000f1050007080c14100e841c06030310210703480c0d480c001040c1c090003401102e0b907190308042070f028005211404810443c2d0018004000c0142ea02070581010b40d07910041c00b040301e4031110b80700401d0205464205000e420007250020110000040150449000310b109000c11800400e00300e881c1c440c5c0c101d2450000344061010300c8030b41c4440444004d4510549400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 668713785 1250 668712535 668712571
    0x1502040e0f0a110a11120f030703050406151409060f0109091d0f0304030c0608010b0a0c0c08060711010f020322050a08030c0a02010c02070b0a0309030309020612010f0b0c070608 78
    0x3103201d43e8006404c1001050402d0491038141c8401c00c251850b4a14070f001c1540340c0012002d001d840d900005120500301340d101d00000e001c0000301e400c640c0b10082c0a00c00c0078021601e890a61241c1e02c4c403141058015a182d20001da003507c1c00d865440c844030300c10707100d032101181803581110113072900611640440300003010004166038100160003031010f280d0050f5860f1420351034905801d00ca5588641d04000c0410018850340701a202266581d41d214280124554207500d840c1c446900c013648101018003d071410400d017660051007072104501030340020401001d11420300c0c000c80c081030314400503207902c95407002201c240720044000d98a026100f2902101701a030ba422890340e1085030466140d050110740e1400c0c403a02402220031030103080c00a0124542003840c80b4205000c0c0300c600c541056114149030f020301d03001780c2c0414219900030b071015980342ca28003038109001e8001c0c400c0a404800b030100c006500101081505d104003407580280210314644075080390782c20000742540022410f14020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 668715035 1250 668713785 668713811
    0x20a12020d020a060e0319020306150d2f030f0c0d080408030f19110c010f090803031512190b041a0915060a05150f041208071502040e0f0a 61
    0x1c444002e000d5581c5d25400010140189030505041c010040c0304503603101107280041e41d010a130158040e80c0c2202d6002c004072501c0004180781500c0601030408214080080c4004003110f4981480c4007281c0c1c180c203440050b03c410b0503a2070f4035000303408100d50002034010f0000d1900c41400880c1500600259003040e840f000001d003994054030380b100340c1c030b0000500c0d41c2c176440780d03424802844103642c04c02910326500075102d036071140c9170010502d040241e414030341c40c41940903810603405094031000300c0ba180d00d040d8900310300300203c00c03541c00c0c801d240140302c0410403000007860500c00c503510032181c02e0320503003603541d8580813202800840c0c99024081c1c0c1d5000c0c2c501440909071045104000a2641076401e00e8450809840a403225005450403a018001912410b85c0401d108100100030740d52002402c16651660255400c814040100c501c900c20500c0a403001800000340910f540c466840c1816004078120f1141e48a001301001072040060411054400010b03031000705180701249522681c01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 668716285 1250 668715035 668715049
    0x60210020a021204090f05060906010804061139060c0a050a050906030f100609060c030c1106120103050c0d03120c1202132c040f0c09090c060e030703020a12020d02 72
    0x40b80403106d0f6903a052010704000c0c0c0c040c182e04198103441c05400c9003441d10000f003d407a0000c00160415440781038806d012202e00c02195150b2000328030f502151045c0000b03400400340081d800070204516246101a08500410151b000e1008100421300e004140541a5400d401070b071840760070700005104081d51a02e41a004500c0b41c00726210703001043c501000752036480c00454204d0303020040d0070102406443e400545400851703405003448400000ca070b01d0041c0b0071422072250701740c0003180895840c0080142c2c52805059170b100c2c03015a03503500010014014900c810704c034080c000600300b80300540c420300c17180d01c90080704900380703000007264a40c0c1030064141d0b40210900a0500380c203060030000c00c1f092416600d1411260013441c1d0b58800300342c41625182c3c801602c06070000c60814041010400c0340040c07940204050700003030081c00310030300707090031460203521500c0049864519415050f14001c500d41080d04d034000c0840c000c0a0411210710500c2d00324440498010140100301d01c0584e440e00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 668717535 1250 668716285 668716289
    0x408190f060c050d0e0a082a030711010f080601050307030509010b0306010803130e1005040b010203120a1d0c0904030e030a021c05070e1302100c12020a0506010f060210020a021204 79
    0x500c50940e2004e04500002c1101c240c00d050721000d0304030300d840030001740701c1e5000c032807151706040c50410100c01ca48250354005442c01c0b00c1c032140da100000310781381042940721040245c4030090b00c4103a02c18400c034109444030f01d4200c0d1181e0010f5001c000140d80d00740640c6c000c0790842180e40c00090a2002040820b00d022402c2e00110040c1d030021900c40328060300d1070080d00181ca10001030b845241010a0800c0c60541207002e5180300d591109200c5000b640b00300180c030306600e0303a10907014080c146030442c2e03402404c56602c01801d985142c1c1008007602400600e0506a1201800d5141c403603403980c404031341001000803010360500034080c4a90240c1e0b104500c080070491209240c0c508081720380782c00c070b14040c3e2a52110b030b00240611308120207450f807400211b00722a0195494080c0d0450184100d1712400940b03801801d08001440c6428035550000301c01d04c480340b160040b10000e17600d9400c0721019004510a8200603801a01840071310140e40c2c015003e41032003030048070828040205080e586030003c2e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 668718785 1250 668717535 668717537
    0xe0906011e09151a09030634030516030e0c0f0a0f0e091606020a0f02060706051503060a0b03071e0306050c0c060a0c08070c0c03020a06020a0311030408190f060c 71
    0x1d00f0041c80004a0703084150031510400e00100e2503c002c0901098486100401d1354034000000c5080d507045085000001243d003e194a058000582c20301d0042c00808007a0380c042d1506500603090f0107030602902c50501a05041e01c0100883d4499000300b080a00003510820781201c4003880c00034003030310500a15800752401118001c52450520300703240c90003c0c28404228a401e000307034100920760f00030522800341c9400c99801c44180140c1d0011600c6031113000030007481c291030402041099070014154000713448044054ae040360301c501048109850680d04515810341101c6030400500703942c5c008840005a07940c50001c0075036681e407541d00448108464150407064001a01201c801050204650280b81c11300c003004076001011000384042d00c01040c800500c4001000581480b1580041000440c0d00801e0650166100d0030b000f9158200d40104801040d41c550141500c0a004019607003901d00000c01400c000603204440d041040419405541145200d0030440102c1c2e0b080c003960210a9076 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 668720035 1250 668718785 668718821
    0x305060603010e091c0c0b090d0507081b0726060709090b040603051c17090d0806030f25050f240714070f230f1c0c0303090e0906011e09 60
    0xca401c10003040b04c001092300c161600421090341045400500340da520a03007001d00c4541711010f00b0104d202c0007904112801040c8074502d03000032003240c1051414400c00420003a46001c2e542ca8010301ea40b00c000b0388652001c40d440b40000e016000c2d07181d02580040700002e00206400c0c1d6640c84240c00c1c51441042a01f84c000c1b50100995080e400802c5030251403017000707509007036241a80c00039840c0c03800aa030043c10044030b040803440c07a035010050303064113003040703000d481c3c410464010500748803000034010056290b80300b1001170540b0700b40d50b49482010014105c001850b040ba012948010003e4607a9454001c0510131000801c1203444100c00705600c2800414141c1d060014401c5211031a601c28144165000e0b20505a84001c1d1907100c00f144056404400071b4100e1000a42c6400001800410301c0c040f44240000340016400420102c034040e4980204240c0c65403030305100c01908031141c0059502400c010001001e60341c2d2a20f003045009180c803000c6544402c20642035a040810844c00140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 668721285 1250 668720035 668720057
    0x703020f040f05040b1008060708040213060503030a020a050d02010b0a2c0f01060206062b020f060c1b0409080406140702130e1e0d1209080a020d0f0305060603010e091c 74
    0x50110446c000b8100100060029207800364008054120041000340103030002501c070107200409411281c05030400800380c80e20748031750500080d41e03969a0141501c091040c65075001e4198018400c900701464068100e4150f01e0614902a2112140300c03602c090711510360150580d401062074640f4000c202111710303104130b03514040009203003060107000135201e28103d85d00ca41020213020303000300700b40310000c0604900454500009401c1c0c01d514444c141c002030300240041c80c011010980b0140d145c51031012400100d180000c6c0000c4450401d40189100010070003809000d005280d6403c1840d00c4d83d0b144c600d0103240e42c1c0070032040309500400c0d541781074035801642140310b42480b01d00300d1035001036081c490040d5060304450b504c00b903c4101c4003e00130550b0b03038610115035580282203400d030005880c65a614a20030001d43c0c3c3c05000740c080c40064124813605c1c224511078059107009040c014407603400c5034204000c86001c07040c0900114150300c547d0504051514011040295078415a155624040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 668722535 1250 668721285 668721301
    0xc050a0207050618090601090302030d0521070819020d090606050f011e030b030f0106080a030f3902030703030206061801031505090346020703020f040f05040b 70
    0x22225812191090600384030001c2140c80e00b011040825004a030117507a1341e160040144c49541032500081d40500581c0703080035030242c010f4003e21009090b4240e0f050290694550f5040360001903421000143c0481d000c1140046802030120b40303121303480e200524254a5443c00c004a50300d101c0c04407011134580000304200e05e44588464400c01080c00d0259132001d07400b4212988504c1480240b06143e174410310742440361410000701c000d031100c43c17000300545a11100c19039680c0c040c4a10840c002068007202942c0c0a00c01e40322250100500004083d5415030052214541c441c591001400c1e00d0300e201c890310250f54100410001075000350090b0000c1d09001c001d0001400c1c00c000c4110880c200d480c0100002007c2048941c075144100740c1c0014030b502c8408100b0304600c61028605500070010220603490050688001809140594080301e9001d101d10442c2140c616a04480050f0700001010005414000700e000700660700180005030454908a80b03904885059606540c00c1801d0360400c9205 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 668723785 1250 668722535 668722543
    0xb03040b1021061410090c0219060e210a0f1106070e0f060702010903110a230102011d0d0c021504090209030c0603090604060b030309060a0c0b060901180e0f010c050a02 74
    0x1404003a90682d00500c0d01440c0104421054420061804d65520861000700d109011031503c9d142c01d1803c1407600411410260f000e85000d14101c3c200e0301074034184100d1014040c281400001c840100c075420302044400544102d00e002c0f12010030700c445910502110002800036500c00c0080351120000001180103224291010088403806801e0801a540141c1c2c1c11110700e40459a014200081c01c000c400d0116985005c6540103881c600040c1ca207101c640c441c3c0d4081e090f036404003a070082001800d03011b010720340c2d42c00120018026070800c81c0c15558141c4550284041e180c00584412001d04000d40c1c9000d8940c801c0d8480c040380755001c42e040c00c03145420300650010620031281e050440c1072880f852510788001510040070180d071000c04290301d4070300f80141c41000200828407a01c2d03078880f000181c100b25503d041122130801c40d0000036090b02e4201c01d5030381640e035540100101d10b46071041c1d5000034002415201c0d600d01c54144083c0341c5110034000d854200311140c2d00c0a031039010300074002e0b280c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 668725035 1250 668723785 668723801
    0x30606020304080703140f12030a0c0c0f0f170a030b130903020c010804050a0b10140301060303140c070e011d0901050106020a020f010c06141f0b03040b102106 70
    0x3190010001008020030004801c03003a280c100c0c00c05c0c81c6d04952160300601d003402602d0210440e0140d2140b6140c0300d03003074001641c815000d40606100207014000d00f160034225400c0000c120b904280010b4007c60000d15044840610840104000d604204012001e5070400035402002070f80300c0c042e43d040c506140208400001030007000303012801c80b85d03401a489100141081d410400d07440c000600303100040001304411038101102140c103007080180030042c05007900030501c40a5044286030183d007814410303441243e030180d451030010131004a958146034080d0041c04494407456101046003201c3e010001c1c000c100d003101c1c400c0760013909448010700917001400d07000e443e40751400402c541c603004207029101a5040720701a0b590454580143d90303103103240c1005000d071494040038143c10120b05a840c0d010350240c0c201100384051300d0034180707600034080c005d9a4441c082400850b0006142e540100e41001c2d1041242100355202e10000307a400c0d030070640841c04400c100007660103100d598803c180d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 668726285 1250 668725035 668725037
    0x18070507231023071808150106170a1109090a0b1c030f121e1a0604050f1c20130c05270a06090911090901030b070203040b03070f030606 60
    0x224500c2e001c20800c412080308443c111040381400000ca44511400d07000c000ca20403801600860341d00e400c1c03410340d40d040041c0d90f0096a00600c0012600501810304804500c41c064641803141d030340c2d18280c202410140070780310308204007132000200a94501d0440b502c19a520000007442d000800c0410129184c4907015642c00340f800200d50001c00c0c0e12440507018446603080910349500803020450017800c1501a010f943c1d0b406108503000340b00c6980150030100a140300c4060802191b20030040c1b14401c1c0e2040ea940310014411917000ba04200b622030a00070000415032041c40201e4a40c0c1e000d80044814000c00b001030814503010b1454501c00c40855840701a10802c10f108040c031001d40b1920031911b4124001d034200844002840128415101d0b140700a402201c0d016a00c403000741003c0705078000e45000f181003400c0c95801c3c885040560340c105a006010742c4003a441c40c1c403080b001e010064140300840c08100004038000c40004011409407a95580b161404086034100801302c8030300e038110034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 668727535 1250 668726285 668726291
    0x24040f0906060617181c0806180114040f021921050609072717210703110703081305181501030b010201060e01090606020f0c180705072310 61
    0x294003228841d59880310700845c0804000804a0070301340b5203480b51000c4003000c8206600c2e107100d60743c04000c09000726026204480a50071646205008241c24010311002d03039001007502c04a403921b42c1000004032580c001c0140f03006000102c039441e03407071a420140040b0341c4403d1140200c1b0424819000b00d08218401085076003408000101d6101024041d0010864401c44c0098120180340142c0c003000d00f50b21030483d40c10b07903400c83c1c00d2480e003039461140c020303002c0c6180c04040101a540300f44603041e0ba9a003894074203c51607400703454001030140c80302c01501c103030600400012600c0c0014400d00e043c080c7c4590707503d45888100076056683c5948400810038410600500040c182c0241e10407007006d00f07011a01c01d01d00c9004034010519540502c080143c0b10300000b03810000d9902000c1501d24650944002042d41e8481c29a2179000344105600030032008136080036007100c0354500343c2142c420b03c0c0c12403a01c9000e4480c01c5d068401d00382248491900c403403050b0b10419042020000d440c1a0312018 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 668728785 1250 668727535 668727557
    0xa0306050a0f031205030601030b0901030308073207050f06070818010c09090519181412090607170a020f0c1008060910052d060f0324040f09060606 65
    0x40b10b002c0c2c2d42001300c2424040e010010400f00d038044c0d0410782540c00003a080503207660b50390400510f0240162540ca0210b014a51548103200c2c19110100d9510ba00d104564840302170b0004001c03141d4000c5000b03031114025507941c2c03240c1c4001403081c3c60081401e030b0b50b0f0f001c181c200350b4680d140610041c403e105090b80742c1044072141c280c02c101081c0031100c501d80005000c1d500d503000c01c0d080115664488494524142d405807140701c511151501c00f5000703a4504501000c02c410955844403030150007020440103120402ca203152010040c08418031500c01d040500c07110344038091540c0c00c26001d000150304002d45044403120200400e04104a04683c00b840403050f1080103070181601800d00c50240c50703001e000038004080098000d00400020f0403c1103200740341149018007603044684040b0954420b0009800b0345865030070b640313078980605845407840d114a1560110440801c0000d40c0701034407990000d1b141e588a218101d00c5c2150050b01013a0140f951178024100d6440c3c1c2c10410500040800c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 668730035 1250 668728785 668728793
    0x1224070512061201231803070f060504150914250504021b06040f1401140f06150c0102180d0c06080c130909030f080402100e06040b0a0306050a0f03 65
    0x740d40001040e40d208000010700b0000f94050480076003c00c0003900f030103076240c401c0480c02d050284182a001c608a112a00a80d181901e91043c81c8015200ca1001c514400110f40e079640314941140c810750f0030040c4a071503102c0d030078140e400c0030006803004140c200542910318000d1048c000c26040c00015010806010154487c030100c040c0035143c09a60301003400c02c09558103028021310542c0c2081143c8592415203044010600c0305d80040b0b9101e04c50400703043e20300c1414001da4107030700c0c16000a240c0990b92201414166a00104455400820707000d0024030400c21070018a4451004070001d40d4030080316244042e0414160035603401402d81004100114401c51343c0c20054444a15240840b5240c0c04c041d0b40880c0500b061400040e0000740e00007462111960100340f09500c640c17510740103284e45910584140a045402a410804044010190380d200e407401041343e0b04010169820075469900116007034101d03031038120219030341e55814011494008015030050580d401d003208014210f5417 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 668731285 1250 668730035 668730067
    0x1020c01140a050f0f04080d03020403020f0d060902090c03071b0b0403030504031107060203180301020a08010317040b03090d080105030a0309061805190614040f05090612240705 78
    0x140c407001e2280100b60201c0c40c9208004880030300900300e507150344500825005c1a1183d005100ea0300b200d1290003076100c062400b90003078a040b250000e02e040a042c100801303101c21544d0840d01120900d650301d030840c00590344c0c2900380e8050b403810000c1e180c0300c0c03030b0071107010300f103220301d200c0e04064002201c3d032007c0040d0a5216072a0310560503d0081403a03210791800b5140300d18200b8038411503000300500481d07020390001c0a0a0740c034104100d8500b22100030010f0500700e1280a80300400203a14000500100703001c00116112890544c01c40c07803901e075490400f44066001610246607941014861107200380d07000e59102d004d46400c402508450318142c2d80500440c5440c070440c028403d10300a400400c0c05c0a040f07807001050302820542c0d40030307482c0180c014207904602072400030030004004108411000c60039281a80c64140858074464104000c000440000511260b0700011008001c1d00300142840b01541e6022503540841e00c19100034284808108010f150804003d8140700c02c41a80b08109 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 668732535 1250 668731285 668731307
    0x307020d050c030601080c0a0e010605070303110d0603060f1103092a0603040f05011a01140f0409140a0e0c010906030e0a0203061006090b0705061f1d0f0601020c01 72
    0x40c0c0300c42110405140c40c1e4104801d04032155407501130280001041d100114091001203c00c4440b50301c80c0f07444003214414003900b80907140002d00180001000240290b020b01c0100d82c0410450b418180b10003c034206903003050304101c6410391101051191060f081c05030b108400030a090603419440c210300d02c1e0707035920b08134041943c4101030006200001861001801b45182c00a01415034a1809081c00c206803a503000c011600c542c0790076071040180c08002001060ba00c0165113005a004c1078041104003a006680c00d44048901004002804007491181044c0340e11001806545468040211000c076000d0f248805c0c2103401c94a040c01043c2c0e404030f41c10040d00d4450070300040444600344084e1521421940c0250076100b1a411f11907602103549084048a4455944130121034448038607050310b00589100170001e42c03040c004121800d01101c811220140103c40e8102965a00c0039050b0490f03c1a0392509606040681800065544446c0203503000000307000600012689500007488081c0034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 668733785 1250 668732535 668732539
    0x241e060304060e03070803040519020f0d060f0203070c1e081213060c0201060f08120304080313120e0103111201060e030a0602180306060307061d01050d0c020d20030702 74
    0x1000504011090f84410689260901200e45581032445c18201592003036a040e0b03460f105010640146942d445a00c1902641c0a81034039500da805100b841442c03c1c0d10741044805c1c0f80c40304081d520161541c40910f1245403141d07107420552503070b0f0529400550705100c9201c012901c64071028049000e0904842c0c1034442c01010032070300d0391041507406e4010554000204200d007000005420184c0c150030400645043e807001c00012980c8080c0c5070b586800010700103800f42003d10006000c22828005103178407039000c2051902a81b101c1e6100c00b054010720f00054080340764110341da0b54a51307061143e20040b8911203c5540341c002902c2c8444505881446242b04118020a541200f91020701c080070000780d01c0141552945580c04a600e6100c440c082d14501078070681000a015245c0041d407a812503919488401070822461003544444440010b91414410200074101c50044140714071005070849602805509402c050b0050807007050458100841d80f01005e180740341500481111000c0e030341 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 668735035 1250 668733785 668733787
    0xe030a17091c030b03010f0b0a06112508030f12130510090501020f07050a0b090109020a150c0c03060b010305101a0d230708090a03080610090905241e06 67
    0x40b51002c034042d042c80c404031901542003505400c10b1403807e03004410301c0e20f800c695001040c1c0d00c41d0740032105003490f803140c202d40b41c0c00304407110316250039a203a4000f0304131064141c000ca80d45232107103986141c1c8844c42d111007103030001070031143c08001d46c0c18564000c154050030382912035940e2074803641d5401b802060001c29949881c80400c00030700754101c3e410030040e0742c41ca0703407130300850304200e40c8a0b00c0c0844251801c2e05400300040510806101e00b0804d680e00402480c206810803100c1c2501c80100075000e81401140321210700403c2d40507002800451041802140c19541134000409980e0003800c00e02c062142c030103041c072411450b80d4040d2802d5248050013501d41100f08400710141056029211450070388011495014584602c0700d8414406034071380721400e490301508190340d0f140944010380043e2802022854500d4001218440b031055442d186074010740707480183d02204c0d419603118481c0382880025070440c200456034030000c0903048815071079881002d40249003c21800001504c5500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 668736285 1250 668735035 668735083
    0x21302130806070306140420070c03060f09060b090c0f0a090b0c0102030603070f080d0f0309020907030b0a05010315120206070b0f0106172a0903010e030a1709 70
    0x80040c20080140076107021280b55051440018004201c140542c0c0280c03071580525040074240b9003d950460050500386906559103241d02480f640c01451084900044a000000108400d40249241c1c40c4000c3c0c0300181152051900e0421140c603404064040c101c200104101d40040c94140c440d40000340a40960321814013400321810700481d00700c070110b440082201042c0d140158080e502c1454150210f070141601d42060510340d454900c6100c50b41d80c451b501e0076101d02c0c411803a00400905505001c1202807144d40007850490044400b500000c1e916114403503a03261400310400103001c00c2c2000c2017001001422891861164083c0c0020b10700c0000c8414215182d20044511050300660110340c0e5081803240c4106022080c82201c0000d4078001c02c641905c0800c0d181c860203824400003600d40000076075140d1005100700600b405820905101c1c4080c02e450a01441540002c4e040242d80d47c2c80e00d1031000b03886250709490509030b218200c0108411541e0001c4d140481e040607807100154a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 668737535 1250 668736285 668736307
    0x7030812193e1b06100f15030b2701053c090406060501021b0f040506012102093a050a140a061d03120c04050d0807060506010c021302 59
    0x1e03482150b2a81804000a6000103600b45190010509185841610358588966500842002d550300500b030070760364451010001c403001c0b4440052205c200e418041000c43e56400000d0008a16680c120b0004032144000d40901c01403070000c0c0e0161504559443d5842481c42e070007000100c20644400001000f2102070702740c01515484945240001042c0800ca483c0c0f80c5000c601400d0288a01c40c00740c420b07490501c01c100c102000e1103041d82800340208003040e64000400000c0e11010304031070b05000500d503103c00720013074204585101000207800076035200010410320a6081150582c1040c0083c405502d40d004030014018604000724102040020a0581000390074800c0d80b140090071011101e1202c02944408105040164001c640070403150112900754441300b41221200c06591700100644410804101ca1481e00001c08011243c241178496001c600ea80b000100c0a5403019800301da920300300705c2c4601440303a014500b880e08800410559002c20000c002d1550741011440c0c0208201c0613003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 668738785 1250 668737535 668737631
    0x40e1305010e100605240901140d02042903010323010f1b020a080919081b19031709010e0d0305091207050a14030703081219 55
    0x140c000000b00b00c030b1000c003460141d80700408110f00554a040000c009440d240c81e040010180206080b88071020310304180c0c00342554000f02035a41407120703042c1000c40303150203200a0544a41414001642e0340d0429420b0750300340d01040c04c1020900882e0980761003034000c030816a81140c1c0d1045070840c0301c1c0e505c4136440c24118000143d2204640c6445590200c3c00c00a400c90111114440b80b0b12031200401c51007282c07103503000d00e8040c04800c0b080281e20600e007000c0245c141040794845010582d43e4071140464206071046c0f1944e40060901640c402162821800d4218014040880c01c44043c1c61a44c8220b54101a0b8030240d4440b8008604d08035a079000762007010201c0b900910144c0203000c2407a004d4500d4022404290044900318a54011800005070110669000501c0c80054515008104c0c501c0441500c2245d0540105940080000e4001001c0c0c03114100c80d0500340075611304090300701c215440d50011025103d0030a81c164841095160442660140b0018400c000f0800c06d980d440360 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 668740035 1250 668738785 668738821
    0xb0609030307022704060203160f09150c06050108070f06021b040c09082b030b0306040215130b0c0d0905090f3c060d3c060e0106050114040e 62
    0x40d124100c1c00c001c20040d0700d5005600c00c0608203003080349c1c3c4000d040f084502028850800000c102c0044090043d14241c100441030300200346800001220942c1e1580700ba078000307078002001a40110014044040c41d0f000d120064583c5100901c130310228100101e080d02d000c2d402c0180a1540e84034072454103841200320b64050714444c42281d08041140b0916986d1b403501404998020620140e000c40b00d40c400d0049400c0510014010b11036515140c08002c00d9181106840d62207201c1003005250803e0044841c00080080d511a940c560780302034086030412240c031100600300004000144050f41e00c4400c82904280d150342e011241d50f40d00072040b40c4211002c0c0d0082007292146e400a4007101c01c0100003090150001c40c2908980c4444040c0040403900c0340f03009007001640c540c2d099041c0f6000c07241400701207405010103542d4500b205103181081348a4020744842c0d84440c03d0400400c000d004880080c02c080c0f8100c03007404401103800070640940d00540140d191520041030074964440000d4030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 668741285 1250 668740035 668740099
    0x10203070c03030f140309030a11011812020c04091e0302070905090a060b0d05280f0c061806080c0903120d0b1813030302220e0a0b060903030702 64
    0x150710b030312400d01402084c64665070764002802066000d00c8100060142c90064060340029401c18001e07100c1590100302040b0f44000e80e40d42d030038110794000b50240001e400d4500500c008500101c00c010000c0c00d14005000b010702480c108410003001458034030050688030341e001d8a03059505090310301241070604591102207002d00740803c2c0910f0a03000305052a14904c500380410001c0e442c0003e01018031488000604030b504010013018500d00c40721690200c40e0382c461030400304055a65210400e60300500015600c00030a108244000c681040c0e0303020342c0100301120980214a410401050100c00620352410b80d000452480d2582d2410410b601c2060080030724183c852020400c5000140482114284640e0b404440002c1b411001c2d0710b185d000d02210400c0a114021986040c0c01a600001e10180c4952014035004520541c0c22186805802a10700082043c00c0407030401013034038104000d140c822601005103034000da400008881b456507050391041d24424841c00d05540e0b580c3c04018241c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 668742535 1250 668741285 668741303
    0x504050a0f020126070e010e0306010e0403140a020705100201050f040311030706050a0f0c090b042c19050108070509060d050708100209100302040506030a200705010207020f030c01020706030b01020307 88
    0x103e20041c424501c540319a40913942d882c1b0300e81d0780400454901075005145509030b0403000040c80b40e4100b03d80c0d22a4018001d0925144040265080000c0c55004185020060f001035100344451f142c803140705c2c0303044081d910003030055080507080059101800f800080910a1241c0b001d0141d0400f88140c4000e190408400c100d6803402d20308410180101c800780306400c500d0303d40c845483d1b9018030800b4003510503500c585411306043c0140c0d0701c20f1035407020420420a501103c0f07860024205489031b4480c00c180074480ca80da054100c111020b496040c1c102c040c0d01d03001001e09201d1a1295100310340d00200481e0b03a00508140e41c240a0300f4541c4542060309940a104444000c80500b078008250444040c0c0d5a008421a980c100b00c0803405075018499000c4810404a01035055580082c401682c2840002c95811003a40c05031851b684031260407030b5540d401007402010740c03070003d01e011117000c01039000c0c11f884000c1c000004c1d12003025005850078540d981c03030503035200c1e403080061340c1410354401d20b04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 668743785 1250 668742535 668742587
    0x906050a0803191e0e030f280203070e0a09030915170c040e040804032919061503060f0e16110f06010914070f0f0f0e1302070c090504050a0f0201 64
    0x3000c0c1c0124518086c0a0310030302c600e081500b4000107410b200d620f04001b01d02c80000400c0c489052010309000b0503a858070642401080100c40d42c0c900d40c2c028244214005110710a03840d0180c05030080b940b1082e980b07040c4c11015404c1c0c82e0403000011900c40030250040e0161b40d000c5240684d8091a0002d510b560341b1003080108020030240144140c03400342d07a115115041900080211100b6810000311141d148404920300c8106039182c5081c00312104000b0a1458441100c0340d14000d8080a4600180d00e403103040101504544890010b8820706400055a141204ea40c840c0d40c108004d0740d0f820003071484645d024204044c403146441c02240801d490540d42d40d40c0c0750002420030148101c52032107954001c1070007240102080840c0c06850f80f9411250041040b09980700e10941c14400c06118543d95803103110341d607510190106000aa0300140c955041c2d050000025081e0f4105d54550303440c203070138400466000a003003200d4070b0f84907402d40401101403004803000e445510b84004201c03500d001e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 668745035 1250 668743785 668743787
    0x9030512160c1d0901060f0b0304021f091401020a02030c0d0503071e060b01081006110c040f140601050412120e040f050106080c0a0504170c030a0803010906050a0803191e 75
    0x8107031031019481c030f0f41c194951507003030001d4204c4290744210b5102c55498103040101d415050041c1d40d0250000303214002489415242a54000108220000042d00781320306116007640f10350000202c000a100501c00c4090940c0803e594602a80c0118230031490b035103001d03042100130002c4545d4964000604171240000424509880c0c41c0c0600842c1c0e124107080e2a0083c9500c00c0021500c035480400301c60035014641a8155a1601d100c890544039001b0155844119181c2d4083e8080307c50708500e00058966500c0100300d1031710380c090700c42410020f0401c0b0402c01c8103ca150791150198010072031800d070030710300c400654505680d040425001800c10590241410031079110038101ca02d01d40320b0480c1c03aa6421040a054804c00f41601c01045041c407040c014030000401243d0100c80c01c808680100030888002494005446011113500300000018440c40f2540d0040100400d001d03035044606608083c2c480b500c1e40900d40e4014a843c2c0103c0508011034400d0104c0000780c000340c506000c21090680b4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 668746285 1250 668745035 668745059
    0x203070603140a020c0a0b0705090a080a020307060302120a0f14040803041b06050f13050a080a030e0901030c12050705040e030705010e06090319020a05120306090709030512160c 78
    0x1400402d01e100c031000100402d419000b01e903464502180139004d5100c43d9651100d0402d400b030008800c0050900c9502c002e916031600c1c003c003400c8898014541500c4a104040c81c20b950b030341155003050300501407170101c00c0c0500b4110f40c010300c14020200e6516010b60480000301600da071038244141c01c0030144820310041c00000c5000c4d41c021101840b400d14181d407c030300601c034039200308000103004000e180c664105000c00350a0641c210900c684506540b00c0001d41e1480d6070b5009142c40c0e0304844c1903081095001250040103080a072000859036146803107181c90200d00b440352860702e84295681004103c1c081c0302c180041e1000400410110300e0180c80282d8a40101c201100c69602c1e2000c40c0a070b40700300142c280d00c039517036090042d4600400303010306100b00d81c5680000b105506c1344080f8000028400e1004060208449a02039103c3c030b0b01d042003065a61001c0c003414140700c11400d0900100301c000c01d1002d91080300c01c0c1011f81d42c5070800c0c142e010900c880480a007410f050ba0501060300341080c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 668747535 1250 668746285 668746301
    0x190f0b030a24150306030506060d05070305070602030a020f010504030203030109020c1c020106060905060403022124040309150f0e0d06152d05011d040c02010c1220160203070603 78
    0xf1640a03081005034010f8088684500014003254007080000788940380200f519201c1d41c0c0720b04103445a007660b95a44c10b15080217500a400903800104104842c09d07030402c05800000c04402c001d11403424241c84c0a900c920060080724100c0344c0010b11864080020409220050120b113103d100d5040d10600c000c3c001e00389405800000380451000090a2500c54103072410b4940003009800d030300d54595141064108400c0410400740203e00364851946c00c0210040c2c0c0349445c50b000b47d00036203000d183c001c2203010f09411515144d1b0300e0070702080c250b0341e201511200c10000ca05080340080c90000c0000d468001418005001c2410304600d0003000c0050700d080c004890f104107404179007805180b910030304c55095102c5d4074007031031416104000540c410540300e001f540a14a1500c02c0c0780b255000705050302e19091482c2c002d80c0d15090b03801c0b507544d44480110138000310498100f100c2c0c19445c1d8064131075138032510005683d090104841d4518810340f10104403856008089030b06003542c5510290280c200c00c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 668748785 1250 668747535 668747549
    0x4031a0a290301060801200a0c0807030c0c050114030f0711070f141c03080618011211010201020a0215040206090901060207060306080d080a02031320190f0b030a24 72
    0x181c0c0000e00920140036404030202e07c811150b0000b09049030500240d00044844010400710071300107400300e50840020300c0b403076000c4d640d10440f81c101c904101044099640c00306040110304039402112030901400d981e00202e12410390701c802c0d00c88082c11078a039507810604d034102e801401c6000a50b40030038019402241d6107000d442c00c0c0b04038204104650400c1c0c00200801c0c2c0c4505c0500040081c0c410404a58880001031070038120981c29500b600088009802a250b0003103c0500c44040c0103681420510011092009601e002c0d0a003500030b4607400c0f203055140b040d2100720081402c55035010140d402c403c0d80600300b103400350303540c2c207000b5948c5003a03201c0d01000c245801004038440b080410080e208107015200c1464948480b1900802984010f2154041034030503460000050388408106915841d05404102d448000100700407171042d000043c10003040440f001003044419403040b803021200080b1960b91242c4d45d00c054a005010780e0609400b9114014009404109c25140d5000035141d075 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 668750035 1250 668748785 668748791
    0x60a0e01050a0b102a2009010f050409030309080a081b040806071b020d1101200c1012050901051006022e0204050603010e1b04031a0a290301 62
    0x141a01c054200c030f9001c111a60800d2151405843d114015281c14070024105106001e18100c500d030404c0400e640145c1c126441c1180000c0c1c10702001c80400112003201c41201e1110380c65150414a101c01034140c400d403405242c03503205800506002e0741c07000b400d850b08403400030764507215600c00510090341203c02500400020680d10b24a50f00e240a45007903902840003880d07980c0f01c855007542c0c00d0b5511400c440c2caa1640700d20810050700c030203000f505500d1103180b80010540c02000090000080b03000340313141c3c82003080d50003140680005000720800314291040460f589900204941c0c0841c0203940541541c100003d008070740070154880d51280b828603010024142c2c40e4035080361541c0584c03603014843d9040c04209074006019022101d104142c6a100518140d600c0b4042029034009038845d58168160008120599a6081c80400f14000045006292504584c1c0e4002c020b030811042e5443c9031901000103840c4104c41d03000b5460504910480c03000006850509201611458030710790007942 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 668751285 1250 668750035 668750041
    0xc0503241207120c0b04033210050108100c020a0204050408042402011d0d031e06031407080c010903170d09080a0f02061302010e150313061104180509010b03060a0e0105 74
    0x1002c0307050320152030723100d26100c0c641c40715440c49803240e69523040780140d641d0380000d2484a44504014928480c1c50091011a140d8503018260f420014803080c4107170001d0401401410781503021849a02195044030300144c070b0b440e24104600b05000da42c1058084150b10181c044406010800d0b24400189960080c00340707a03014800300400050b0340191400c158061082801024041d400c095007044081380010440034241608074251400d07075000303030781080e003c0d51001c030035050a03c2801e0140010300010803c224101e0002029050380d0f01c4003501500c0380b12031051407070b1010403c4500c00300c85d5240901048072941898443da600c241005d0300400c04c00a030850103940040b0b44907104214030b80c6681c82d04075241d0010b60301030111100155100d44400e049001c01d6103c0130155025121990340c0240d407010500c0c001046a594213100c08240d00d0901c0208801ca100c0f0310b82001407283c08074042155201c2d03001e0b603409480c0d4000b0403581030162104020703400f00540d0206041141010090005031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 668752535 1250 668751285 668751299
    0x60605010c0b040b0711011a0301061428030804061d011e12020c0703050d0f050f0409020d0b04090803060a050405011404021b0d020d030c0503241207120c 68
    0x1e0700030035008111040d2580041d011070f5055038015840600d03801c0207000c680e14840d40383c1c2181e109210b1f2804107071010f01442007a090902c15040a0187d9008048001e11100d00151552680310080041401c002081c40c1d06030f25419003074801554480c60710390f01d4649074a4080c0440d050366141c5c0c44510030b01200034045602c00c10f0181c084800b9141c81c28080d0310040c00485815a03940809024580c0030800034203803000420107100114025000380540d00b0504400070302051524a4120820000340005003940703000b00304443c01ca83e200d0303900507a0340350140e51060141054403549a440b07480c1c0861001801103440007588203c008540b4600c02079129010081182c60a00421115140b40c3c0010102800c00c0d600030200035200748044090360684240d1a8540424006e40d030f80160401d620040d00c0301e41602031065032403841d042076030a51601d900a110120380c0118001039000c10a29210b04507140c403031095074590041c1058500040d00ca00725130703101c003180c0300d400c403011162404001084 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 668753785 1250 668752535 668752547
    0x71109060d080c0102040302060c060f1312081005090424181709030d2a020f01080c270a050105041a07020a05131b030506060d11040f06090306060501 66
    0x1403180100301074148440c1d40c68010103074000a603149090b40d4200004005691950050402155044020400c1c1c3c40c064400400604015080c0d50780809407210b80800140408040504090035250020b9180d81e40c028001c1d00120300e82c000784d00041c21000b8081030001c0243d070622181240c406607080400354440d030f41c0807a40020030018501802007400000150400f9858640341c003001c0149080a003002c00082c1810041e000300c0000c600e0700c1c52120025260341a403481c0c0054141020ba4542e101600480c8803182042c2082c1e0400074850006030803030f492072007515007050b25607800800001c0082a1400d0040000694501c944440840014198412070480e804c0c2c52040e1190b0145420768044803225403c80c0c5c4081349d111b004c641c004280c2e44c4600000c0d40c0c03048882400420740d079250b60f000448001e01c02d10000e08050034a02044035548a29040310056000782100040c0b0001050840203640070b40c0d0008107840840c07846c001500750303000c0a44010b480c0990701c100401b503991001981e030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 668755035 1250 668753785 668753791
    0x10201061220010e0a031103030717040905060901031208180316140622081207080a0509060606040506070c1203020a0203160503071401170f0114030705030312101802071109 76
    0x417050038802c09000241d90b9400040c1c07961030140442c3d041c615543d8070381104061100c80c0c6c460b40c000c0454104454103960254a80201d8180e42603000355041d52035800e48421855500001c1c4403404001c1075100e0b0190a41000c82400303841501d46420b140f83c2111588510100300355040b05c40c14101c4401d140d004501a40901181e80c2110240c40c40e03a0044480082240c2c030589241109004c000712540900209911a010741e6481c01000e14240c1c400104551020b071040501c0da01030f200308080c2e622908200c505481d022103000d5180c1c1c52a25141502d0301d21034100030402e00511101004241d000942c808055100701d0640f2680b02010500d01000c40b02d038800c542c2d150740403400c1000305014603107a0340c05851041c5001d0782d0070203403a156048803d009650f5121701d43d032030744010804450321156042c04408103c1c00341030004d1070b100000e81d0301d0060000641160300602c001c18400c0c4034040b50300000300307000780c500341d40303800c80f0b07804400290000e40342510542031121405a5610380707104140c0c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 668756285 1250 668755035 668755039
    0x6020417121b030c0715030f02090901210204020f03160c0506040b06060705010c090f0602030406021f0b130506010e0d080d0507181e12150b010201061220010e 70
    0x420325200010b00040181848002038150000304030344c00c802e0f0001e01c455000341008110800224801c00401801c941d810003105074480d105121403070940c7d40b01140103044411004810a4688001070072900d6072280741002544248002000e401400700d600c0594800c41450000841144c06d011003a1400d805d800d10040441d0000c400103000600110328a13600608094002030400c4441d503200c03402c403007001c0343c11008103282c100d04100f50403003182d141025000500c040d50500b85041c01c0a540c40308800d058070342c161444008841350742c025601c140c94100004050111540003003550030001c090030395103280001e91a00c1c208002e030400002c015501c80e40920098540b4442500c4000109009441d42c420003034585950102c00d601b4500520107800d404440070350740c105250040340a01312603031102050300d80d4035400502040d46c0e010848050310f0a40400328070a8040d0004034018015900800000b80e800404035080c03080900b030305400d040d045450030464403000740040d5052142d8227403241e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 668757535 1250 668756285 668756287
    0xc0206040605030405010b0d0f1209080706080a09050102031e0f01060f050d06050a1710140103020d06150609090e06060906010f0903140303041b08030702010e0f0a030602041712 78
    0x60076200b80c0046a01078061000081e405405030001036400d44aa4010740d6040310f00c20140091090182500c2c01e034140c6810034445c0149005500c80e1185038510400c0d00b449002c8001031180701d440c0d00031910300c0740d000008540e0392500124002c4400288003007801040c0a030400604111107058041d8182d031741d1034503002401c2c071003814102e8082d80189806002c0703075100d05000a1039154440004041e00e515407c0e00c3e032404103926031610b0401c00032182907103681400340c06104842d0031421241520703015540c000b02c07001103003407503005420405849c0b006c45e46810300c0003035955030000d049400c0c2c41c00c1590034083d150700c80c44200e40c3c4060540b121948001204041801903000307152242c0071154500f090241140d0ba034590580b40c01c101e04078003020350800010007040025210400380d0050b445210300c41c0050a0110f07071581c900130508000c3c1844010185041c5603a42c1c2e22001003514002844250300c20703140e10b040740c065040b900c10040060380d02a83e9003003100010500c445884100780d011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 668758785 1250 668757535 668757539
    0x3010e0702010605030a32073f1703070905011403100501080a0b150901020d02060c0712091e05120a030503060d1e0501050402011806050d110f27010c020604 69
    0xa20040c1c1003010740703e54485036502d40c2e200681528000d07038800803c8000317004500d00d00540c0d11507040041c1480101e107001c1270080c1c1c07080c0719102c80402c0343e10342c0400b606203502c42c680b80000024155801390700b0450b07404030421010303e82c440d200c00103a8034280e0300e20024a8180404500b00c1c041965240705e4400d03545030a11895204010465000c1658900400c0c88031001000c1260b0a103988400b06a40d03c002135608032030350b010820f06400c3c44661000385650301c0c0030704104900340a9910020640e0f070642468000036841055440040d050b03003803501040612070b040800e110701992261a00070888000710034480400401c0c0e82820503016214a03103036a0307a05040090301061020f0413113041c0542261030952111001c3c10480b010300c94400060746082a00000d0140b074040c1d1440002825800d5060007443c2c2c1c44400e80b4600e003400ca0020030014a2400c0021072030180c4c400140501c0c0340031442c050341c411000c0c8201160413000f105807407ea0905801107880c41ca0000e40a5000f00d020170003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 668760035 1250 668758785 668758793
    0x120903020d030906060f0305070f0503030301030f06090203030d050f0405010c0306060f0c060e0109030504180b100c020117160314070c0f080922050a0903021b01050705011103010e0702010605030a 86
    0x40b00048a104e0840059039680f181700d19080c40e00d2503002a289a40a481d083c0000d4580c070007641c1c00307040110011415580f4565490164152011004041c00e44a4082204645040065960740c1403612414407045c40c0c08070800000d58002c5405a40a600b050001c07a051406071150760151034141d038400410300200c80064500041c6010105d135000c4d9200d442440c410030078451490200c1c400c2d940c10b030381c40d0b1030060002c00074208881c400d15074514142041046950b605110b0f102c07000c2c3d034100340b01e00c02e2007400141c800c51445071640f56012102010403115076211503070752445510a0b14100904e1130b81e100340e200c40d14802c60b155004242c8007540480071500724054200386a100c4c00c1070502c1c1031202400300b00d881480c080000383e140512040031201d02c4041c01880e50000304000200f0241c026034400079681c4441d000c0d0044a1a01c548042616910400448040a4102000f4422151401911030b51940309105e4030b102841504003091300c0074418001c0c40103d5000800a02d403090080c0ca03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 668761285 1250 668760035 668760041
    0x3050702030c0d020906271303120e060f0a020715020c210318030d020f0406110c010806060c150c030708011d040b060f0d03080405010c0c080d0e030702090412120903020d03 76
    0x514001d8480c07001c03c036087c0000d24100352171041c01d4042c800584c60609160141071200c00d04440016a800e0880500b03050100280041e405180c00c00100003a44400d05030b5002485410409056003200200600c05807585070010010f01081c00221600c41908111070307600c0518072962103142a40800200f031038510001500c1107000201019249411102c01c2e42d103017203074819000e03400d0183c1c01003400c000c03283d008403d1507030090401000c2c0c0503507142080000e0001c4401402280304d51004101d4500c6480108034021560080503041940d9090959150405400845078bc03000a020580003041c0c0e040c100100446200c0603882041c20380e00c582d59441e0460000408854228040c18400d0405a44900d0701408031402519640342e182860b081c001c0c203440c00320800c101489060000140020200d80890f030900036440c0e400614400162012415407103400c030007940c000070702002c1c0001c0c00901500c1c0100d00d400c80e02d40c0d521032100750401d08141e40700303401c015016030400d84102c0311a82c0207030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 668762535 1250 668761285 668761309
    0x90a2903031602061207080a11250305130b0301080106060c0f121b082701050f0904090c15030c17180a06050a0b01020f070e0c0f1603050702030c0d020906 68
    0x701800e0420300b64105107504c000c1c0460341b403000075640c8402e0020504403032007010455100c1401861502d1402440c03042c142c1d610303420030401485080080c4080c584540241e03400c90b405407141d1061281c0d6071040f190960000e026100055207828030009501e40a07600a00c400356111f80c0e0001003545680301d900c1105c2000110b0800c2c402000c150201c1a002c80d442201081e01c6031087d580c0f1390040d8042507242c49400b039024190000e024250401c66038000050f41c03030810118910540d102140c00210340030303287c159002000c048a400001c10161040e000300d80c40341160383c3c0c040090303100385e1904450660b2603e0301004221105400716060302c81c801070a80c00c4252040466600310482d60b21481141d074100c40810b501a40e814055495603814880c000f0702d40450f00040031420f052045007150401d0252002441502c0001d0003401d1102c083c0654019000140d403004030002c40741009010366028040c120301c6401440c07005103a0303103400300004e00c841d034000d00190956a034400c240070866a202c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 668763785 1250 668762535 668762539
    0x1507200309031f140f2403030c0a1e150e010e1f0c0c230a140c040501210602031801061203020c01090617060f090a2903031602 56
    0x304800203840c0c400308140044940d410b1403038004420180f1041007120108801502d407141e100c0280f01c0640900e82d5119088500e000f07078008800c40c0d402c1141c1072642c40b0305200d6090300002c107001071a1f440104000c0b95050080000c1118241501c5d46c1c100c00350b10200004003000b00c0f1a103903156940e00d640c403200004a15500000f409401c0100c200d20380000c0c410515414100902c1c401022041e1b801110b2140b02542001c2001100030f0b6190b20840e0303011354114224203040c0a52042641d010821043d00344d0304505d99105029a102c40b8039112062040b03854003460405c00009401c038031032107098419200402d022400d80d18595103040103513002915802041205020388116180300303109420041644402250f02a0000d02d0042e0a1450001015041c0f0100110403c0800d400c500c400d100c0300c030910090b5241d51380d403000041580c10507800b9182c22120780d10401401036601d03406240d081a1402001d01220008442056501c500341d417001d03012340051101c070384030f031041e00722442c2c81e5440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 668765035 1250 668763785 668763787
    0x606030c1d39131502070302031005250c030e0d02010507030e03010b151e0c1b0105040909081222031209061806050c091c15020a02070815072003 64
    0x2d81c02480c401d0b0800c000f40c074222079007501d0400c03000c041d2040e072000031802d80c00500243e81c0356030006074840142c0985d616041c0d46800c0003800d501210417118050300442d010315441e08243e15001080402285011004669038954106c00341c50b000d01840f00c1c05905a6445290111950301100c5540c0c0030705d0070b40c1e015900c0e00c0d900222596120001c00e03411010214503030325003d40c000d02440c0740031600c00d51030b0812002c01941d40080000318040d01c0c4d1005400b20580f0740f1001500485691146e40d00190060349415652010425800d00400e400b8880b80109401e80d1140920700e9141d005420f290101214503203c1c5c1c1e4002806040310205d10030168000160102e20741d21980b05842d41807404c0100400002e10880030400c082c46800d41041164643c41d0615048074041007640706140a940e40903500300d4004420000005078405d0300485100f800c0d512503080d5107000c0d55405060041894034000c041c11100c0810520342c0706841003140e50340e20741a440d80b4841946070720740000070207102400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 668766285 1250 668765035 668765131
    0xf0606080304171504022d1c0b0601020c0109140f0d03020d0828050c1b010b121614120111091309030f03180606030c1d 53
    0x220078009040140030550800840c1103994042505140361407400203d440ca075a02480056201d40740020543c25102c0c06908a43d0807103800c881118661070001d65008070310080e13882c2d922003401204070200d48113a0464526031580401a82c441c0300c0e1599490018411000030000c000806c950100d4098015016404441528011070584a61703064240c0c096070001c00402a03082d8800c08150344000045241074115127400700c0110b0104000c0c0c01c2c00c51258450340440c49040400e0102c804c0b01c005505648480da0710091001c1c044c200204880d40310310461004a41440c10100b00140030b00c05645072f29803d641441402c004004030102910b4110044a1070003285800920448d445607400101c02a2603445003010808903040d01c03103001c412181080f0f52140081c1d002400c3d4003006140d820046009541c8428000000c1e85000000c1c01c11403c09400000b40800300424000707070b40d030011000024044030f10580341d02e43c00554021003500c45d4594a6901e040c130061910311045904102100120 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 668767535 1250 668766285 668766299
    0xf1b1804241e0f200403030e01050a0f050a2604050709020702030c04090c0b12010510051206010c1113140c120114130c02010b011206290408011b081b070f0606 70
    0x701c628139081d015260001014002c5c150854011003c02100340f80107490f102400200505500c810340c454000e0044c0802c2d40c80c1041e02540c0006001280c40703002c0407410740c2d00c80303c01d404510292000c4c0c90038000d00d0004550510340b4001c5604550f0064001c01302c8184203000d22006144049040e5410f4281d0300c0081a1560750000405d54803004140f400c00c1c03035040804101401305900308000c10710504210410465544e0140c0075840002420140714040702c50500e40001c0d051074456079030080ca2540039a100329a03591003000340e020160f91044c459901c00c0da0b03806051240c1c145c0d080031031841c0c00c0100070701740c0c0d002c28020b0b0b034040c090f002e44011030040080e4001e0b146120a0b45015035129000c51081f542d00141c42d010a0b50041c0d400e101161400c03a004114203003049030000200144248100801c00603003c5074020302c440d5000b001200001ca034a0b109419284411100082d0010301240340c15524144080c2020222407121346441130aa0b2041e89003a2034030000c03a4429140c0000051603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 668768785 1250 668767535 668767571
    0x403060507050c1b0d08030a0609020a03020d0f060e040b1914190510060e0a1503061a040605030a0b01111f06080f1b1804241e0f 57
    0x510742501c4150b220680c6026280c1810100194083c400d46003000942207955200b0700a981c030f42e0400011540e03511140705aa0290580780c0003500d20600010390f941265600d0381c0200411980c0c0201004120600701d4a0003c1d140c4c280f00b951501443c071004200854170a00000d50400b120700c881c1d26072011450ba0003400d03218000c002540c504a000c04015401c90051075008044680da0b108010701d00c3c00c078510140c01c2c081760180904000d10100c030116039032181a180d038050308201008182c0d0740300b8100000e000c2c06060055249100045041900c80c9550806032026220613440740c07419681e610301083c0080465418081c1048a40200c10310701c080c00b0f0210554441c0381c1220340301840d600b00740240560383c0c50b5214100c0c035480f42d035408450010200d040071000c00443c06e2181d80c00c0c80309001a0700340c00741c2c51294424403800f80c01c0c4000c001c4c1e0308a4a42c0e004607100c00a0320404080c60039101260002c0050540c01c0b43c030007040032159131580d80480441c410850700001c00310082c3c84078920f1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 668770035 1250 668768785 668768791
    0x207020a360c0905030c13150503150703240b0304110607030305060f06130512010e070909060b060301030b0f0c0c030406120b040b0a1a0906160308090601230604030605 74
    0x580d92100661402540283d050300580020303402014a05804004070704a0120801c40c00100d5980d032000d07440891506a40130020240101110741100500350454044d0609541d84008a40741c60242c1c510304c06840d0108800311001d50706e28403424a800180115584014001c81e00301440b80480c00d50780d035558000d00000c0303000e55030005a9150640622580c0b900310948075100d50740512aa5605541000c40902074440075100b102444103954403a5024041080081041740165803000c40e5210741a404a1070b03190082e1410301120035a1402e0107640e120a0101420380629400011850481458035903000728180c5002864061a0100503065400c140c01030000940c02c0c621142148403540209024060100c0e8100b10010304800024082e40c01d504c42c0b10b506440950440c518503101c4800e0303a03e40c4102929480d9034031081105030b100a0f001020403000b06a8240c08180400c000117403d6041e0b40c3d0917080954800017000c3c954440221000406501071010840807000031620702803540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 668771285 1250 668770035 668770139
    0x10032d0c060810170a020f190303080714071520030c1c020906070b1807030c030b2503111306080103050d03021207030506011709030a02010f0207020a 66
    0x1550b0b040500b0710038510304030f40e4040007045042c0d0403403a44045000c610500400d504a8030b804c2115075039808520018203181a1a5101c000550008181500714502e948129a00c0e034480719101c80d40c06010a00d40546000907251110b001040c00740f044199000d422054508900c903206030070060300020031544129001c9103028408106040358414807a4100e0000e03a0480b410b50612a1380c601081d00d90080c0302e4040d01c54415000031946102c032001140450628090555000c1071b207a04114014041c20321040b036041c07406c03100041d2942d0065071500100410340b850100b10390694401100a800c0c68140584181d0042014078803840c4000302c96001000035855001c003941c91810310703500303124907541c2003414580100078809403504699200395100c280360074001103c0e21540d004951944550000d140095072100900c0b21560001002e0400b0588941c002e010184070402d0b10300a81c026120b000b9044000c0c070a00784000091400da0f200b1428030070002001c0c148110b4000e042116810f01c0203c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 668772535 1250 668771285 668771297
    0xc0d050304082b1b060e0a020f0306090a14031b0a0201030b060f0304020103050a0608101d150c0a1803030903061b0804060903140d020405040510032d0c06 68
    0x42d090007400b2101c65018000228003402d5092003445541e00024843c40c0304000c26011072100640840f220100a01e4010508016140340040817a40e665004134007684550542944812680750014103244a80c420002030402c5903110783e14401c030340c4141110780300203010501031614880010403048410502913001003c500030940005422540001c0001e40151020080000f0024400c41165000b640c2842e0000c0c0c43e5507640f81c0c5200808cc1c1e60805041409507507180301c110070a070340181c01c0403e174420700c81188400c09120a03999102184050f6000031100000032612800100501074040c1e1038184980e00c1c01040c0308242a00300243c2003100410218035003401440414031428000b840100b02140c4000240fa40107405d051008000030f02403615000340208161040110b03106820b0340401d42510b0707000d141802d901a40150003024001c520f070600003600842242c10207000c9039000041418191802c20a000b4002c0700903410180c3d00140380d040c3c00008038207070ba001c0010980c0740d03100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 668773785 1250 668772535 668772539
    0x15091c0215060306010b04061b021003020a1706010c0825050f0105010b1201050f03010e160e0a020721020f0303070c050606030a0507050d06150e060a0e0c09010c0201020c0d050304 79
    0x16900d074840241c2241d000e50700600050100f80c01c140111802c1d146917052441c201c00c0051440c4580c505059002134000641d8200d40c106190181c0107003004040325141c0540c410080115400d542c001140c8040c0011250400c82d00810680b030014042244807200c00c01d9a00c6007503401012924503040115800c3e400b400e49581104070038800c0c03d0240460144561829042c81c100c4c1001c40303410301415100e20a2120416031a076801d50004882d1700c1c4090550701c03810108006440030b81264800d17500080171403400541810a180308071401e00382e020ac000144a00c0440e404a0004a400100e070150b10500ca08003004840403c081c500c1500c0b03c4d40c885510220a1502da03092400291200e4040c3d4040201a800901c000c10001c042d610140c401071495000382c102070000c0e140005030802c12009003103010480b613044c9035200740305100030356035244095541c84442081c1c100407542c41c50450780500903100f40358403644202c21074600510489110b2030012001912211070100201d030a54000182 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 668775035 1250 668773785 668773813
    0x207030e1207060905010e01031401060503070e01020a020d1707080301030605060f0d170f090a080309100c17070602071b05040c020a0305070813080304080708010f0e15091c02 77
    0x1c90021101007001810b0181d01c1c29902500000880c0251410f000c106410500f00f81d103e5486004002c0d24800500722b20759442101400951003525002c1c0091004206a009540005907601030380760b01a011540c0340b42c1984942c6d9512003207144402100034100301d11004a0101000b850185004401c00920b900301142040722918403910b45174049c450102138000407030790720300200c0f407564107a40d08141e0312402c000009900f80700700e02255038041d0b90790001165110740000034084100090384c0ca0180050003c0702500c40700d01c000d40080c404200d03241c0c00754404800c0e8018180641c86421f025081ca03480d030361080c01d840769044860010207190f5074104180e250a004400110f41c1d540003401d507080d46070702c00030400e00c608900903004d5003000418003102d51900040c039008000031801d807511141ca41c9002601c8070290300c44d0302c5041d801c01da21116034000c00e00c2843c2000c640d400c02064482c1242e032142001c92402408245640600a07003104ae440300701410079004501e81d400b42030b028040c101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 668776285 1250 668775035 668775049
    0x5060906010f0f15080604060807060e030d02120a05070c03020a18050c03010b090d0203070509010608240609040f090b0c090306011a041208040906182004091a040207030e 75
    0x301c0443d030000c80d0b41040040080e8006040865101d916106905507101c40c0807901901199002064501c907000300082c5450344010703d112004030880a848a400c41d0540480c0d6030311940c009485400002c02c100c0181038010380060001c20300c980c2e81c9081287e680e400280202801358072080301e9114040410081c8034091080961042c0050803c034115418040b00304200c2c010021418080d1250150036802c3d5a000c01c5810014907005106d840ba568451000a0203030505903036818040214100090300700c0c1e0150032240640c0c8025101e00c0c00d0501d110701f00005094400c132840400755850805c00080b80e110b00107544078091138006d01340d44a600f10141854900148e0104c41030b601c484040380c0c3d0307040710b90089404a5076948002400b030040d5003001d201600c1039031b0024020078a4984002611428080000d000d00c3c2c10030b0040110401c0b040c030b04180b05000701d86080200360200014401142203501c0081e469a1208071200201c1c822400b1800f242c0c400c51054020405140c3e40080d203142c550 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 668777535 1250 668776285 668776289
    0x2100c09180501030309180e0f032104020d02092701411008030c0606040c08090d031d24010609030503090121090605061002160b07060905060906010f 66
    0x7810800041d0301d03540300201640c00500481d41608009140c0c1203030040b2a410428503034840c4005d903810b0200780a4070a42e642c0c40341d904129101030310600b11580c000800080ae10480d00a0034000508040354200401c480c1c000700000001c0003840c00d0704460b0148802d0b4514200035000000035040011001e0402c00801601500e00b11004030f0030320031140b89540300d4803132045190f090980140d00c44501c2c001103031b40c00350040c02440c80042040b6140349400203001d401768606aa00f0401e491203103404480400b02150000400e40c000d2800c112000e1184e4020f6075282440101050040c506500c080c4c10030054900110403450003403100a0070030212440180104064107080060354076645e100ba4490040c0c3d0f6505050004035400341c4111040000d440c2135140900701d08109032540c5241c80c800402003960254020905201e43c1c150b494000265038030000289001c19824074901001190250b000d51030448540c2d854003403000c0091810000580a5503022002e001550305103142c2040d0f90400e6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 668778785 1250 668777535 668777579
    0x18050715020a0f0809090f310f0302071a0304050105060102060613111308030318060c16150e07081b30071d0a0207030e060a02100c09 59
    0x8000305a0806070002816020180d10406540e8119040d08149600c4d004240d5402d402c480600e080100f8000c12031a11031003207540204400d070851104905001507041e0204800d00a03100300e21090200c1e1480d00d43c43c090511900c100c8241c00d8640350b0070084062107541e10301242801106010401c8400e00503d64001030078401440c1518083c40065a08602a0100c0030341c40e613212441d20701c18620700b00b110000d81901e4031071621199118003a0b560380c0c2c01100c0e10b003001d01c40c03034402068461010410a0180d00d1004115040c82481c3c001141c0c140d050250440300016004ca1a20030510140038180c0d000140300081c106c402c0ca0502c009040100c15003042000301c1d60030307000034980c0d5100b222f06012034079400d00703240c1d01810b40b0130f0024045088580c0740146100f030542c001b0b0354010058440d80903400e80d0031019070540f0f070307400601c05038051400006e0204080207091805420b1080c0a001100081d104840320340c250003880004598441c940e100000e00a11001c0c0401c4107000303494100c0004c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 668780035 1250 668778785 668778809
    0xe100f0b09220b090c0a03030f03050603060105130c0306030f030c0c08030a020307060b130e061501090e060609190305070f0611120307111b01170112060b060706180507 74
    0xb01c11919180301d00d0260010181032400000c101c5102c41003140900640703000d012a03000d6602c90401410108412568400181c2050000f40d9182400310f844c90480e000500746803080c48034000c040000e0141c0000751400c04d6a92103000002c90f0821011810050103503c1d6440800e5140c103080e240b21ba4182c102201070380c4104a402d0902d540041114141038204900040f080885400500101400c0301c139200b109092440000b140a4003150036401140034a002d80d00745e50000300152201e245501c50702d2540c41401b4000780e440e0902138010300c0c1c4c640c0014114070074150b04102090b04a445a082030320603922988041c4414200c1800d80c1010700400c0c03c2010b900c04141242075a100c0510700d4810041a01101040e12940500c444054111401301a62540401d8444428009030108000380c0024036407000601e41021803030041e8160340e58001404d4808c5056110100546003c15607940c00900030400d0402050760340c490303181f20100f407290380c118045890504902e000c032990800030210300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 668781285 1250 668780035 668780071
    0xf0501050304031b030e0603101403070513090804180b040507030e060601212d0c020a081621030c0201021603080603120a05071401090201050d0e100f0b09 68
    0x50484135101112075219100c3d1042c000500e012a11001014171007070b00603c1c0031091044082500507030f101526500d08060301460f1100741016030354060b0348681c941048480b91051010106a0440e07007000b401220114a444e686900c5580c024059082070007446944513554a20340c40c0c640682340d0006031a01e0b00348032104844040d15242c41d80508401e05010300c41942104c801001e84589901403030a80e0700b0000105009045400c280c0e60150141e02a210443c80403260031261003605c008003615802095202c42950307600d1340303a5009500e64641c001036002d031040002d5104987c6210007001907021080300c54054805420340700c0a8814805690050080111006280141c89089a09450704a040346c442e440880d04203404000c2c01030103214001240320916800c5030041407503601c529110341344120000e151600321a0002802800680100104000a503c03a0000e101200e4207070305407a0246621202803080310b9101082d2100142c880d62800301a1400107a156405101c607110841411 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 668782535 1250 668781285 668781287
    0x161506030305030606071401110c1c0203040b031015111e0606010c0f02030102041203020d02030f030105061809090d170f06040903020709050c0306090703020c1e01090209010b040f050105030403 85
    0x8000100700c5405620045501c50031f1200c111402000c01060300c1c000c101114201c1750203a2142e0010740800c0322440b48a212440407584141c80344181011607002d1030602e81003003d03003103090781301031300c8103170f06500f140008513090a00c070b0303006540c80d0099183c03800180803007010241000417821090141c1442c4e52980320803190040b800361390049092800006014980c0b5000d64103a002001c065050340c404100440c18001001c500180c0500940840d03e0002014a00b00d0b5030780b00c1e9050a41105c601800100510b05001d40500038524014a180903081c0b401c402117900801c048407c2d40c1d09a0018110f00180d42d0041710707001d10501708140d115201d140820001e9801000079018900455440c01207100b814401d000e100c02400c03003104140480d05002d08201d80039042510140d120322400408940114024400c4642d910980405090102c5001e080c5214007501c54060b41500e549548803a0f0042c1e4841300f4150203040350640d00b544039400c1400d0b40031074180740d401a40c184101003040c08003003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 668783785 1250 668782535 668782537
    0x12031512030207060302130b070516080313060804110402070b190c050405101b0c060e090f160504081006081204060c060b061608030601080907290f161506030305 71
    0xa44d04a0801590312086440141008282a0300400a0680210300c0208006021801c40d03400401220120003e40d22010619168402c21406445801c02440b080060074000d000c96a400b5000b191408290f4181a002c101130b81e1011f00226220b0107180200f001440c45010350b484900d50b06a8104100c00f5501d4020740140710744d0260074031611540d0910f600c6684601400600b5004174003402603254024038040710720020300d01501e004184030700c60074903a5080c50680e462280c0c28030039401c5d950307444000d840d2002042000a400c20060200320205400c0340401c0040b903120b096000c0018a24600803e543c00c2c070ba0041d81c0684803250400c000c0003440d610800c0c41d890250403d500042c024001c4002980c03074410743c0103d21203010700d00320300000d22003001c018600c0381c0002e0f2206183c0d0390f62401550788400040c042d58403840740c20100c1035604403110916420201c00091034514068807000401c100f504a180d40180740c045a04405041200c4441c14520310448001c080c800d040c20356030082c2807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 668785035 1250 668783785 668783789
    0x20a0c03090e1e130c0b1e0f09010e010309081902100608030a391a0c0f0a0203070f081e03010602070b28110f0a0203030306060c0a12031512030207 65
    0x4011411004503541483d01c084400c8241e40c41901400550380d5444102d40c2a0820722411412410001f8040c124800d4035049403100c00c0050a42450b2a400d9001541c0d48002440d603e410595a41107040004031601c00034641820002c1c0c5030b034000250000c2c02450308103006d80c011a041d003044000c010911000050340c0403094242040c080e021904203145940d290400d1548000101300b14105200c441d4114003034003280d0107450b689846142c403100c112554072082e2080845204100201064442081c01620602c0c80c1481074928001c9035440b247c224400f407940c00e59041c50001440e8507504050105288011401c2d02e1711030441d031400b40042e48460b054070500c80004400074910803100940c840715213140041d940b040194000b010001040d0003501041d00c4818454410710340e4070380500160381c03000c0e41d500030700452660741c81c282401550740080b800607002d8401c4080000000b1416892035410007517135074000076500340083c0b641004220310703400403655140394281400807d60200b48502 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 668786285 1250 668785035 668785081
    0x5011d100c110a110d060c032a08060907030f0212010503062409100e07033305060c0f030d0b01091512090c0909030c05070501033c020a0c03090e 64
    0x45031900c080130400965071444000c0c0307040d21f00a6560022034240d801800241c11000b141da44403a0344040f5140411080705412004c03405400004095142040d46c0d594001041e00c1c0118825100400b54030603600300d00500f46801900c6801880301781800c01100303074000c114030350b54000c1401c01d011540090300c2081c892802030082c500000c000341d4042005100511940380711804500e8a040024020030080070000e03100c070f61800c58560005071026074490544000b0750607541807072a0ae0100036030780c0e0104003070300354138041d6602004d60b03040180054030800d040c1000c04150031020400060581c110368202d01d0b0300d41d2407042c2c80540d03070703a10148402505022142c00104542c42d414400442d0f0159800711030308900b051004800c050b80600315101a9105108841c1080e44500054003aa08402d072917003603200212000c205a81390000602c0104176214403004079000001d640c0034280d0740040c8800001c00c0e900c103546d078201684003c5d42c9004200351150040141060350441c1251080c0c116100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 668787535 1250 668786285 668786303
    0x30506040f050f0a0513210923040b040f02030712060509070c060b04200c0114011212050c0d05030f1003050d0e031e0f1b0f040905011d100c110a 64
    0x1401070300d04a21040010b900060075800b008945900da003010325482c40c1400000302c0e08d10000075502e111020607000d03002908002c100d10317420001400018805240c0c2c4641c003507169441208119400c0c401140120103590b00d0a16040d4040d102d4002e0350101d500c800c1c02804403804000740a94020f0320740f00070030b9001c980802c0d40d044000000d8003400c3e8900984582c0d00d0041461030003e0340340002400c8520300d04001340f0032520322440440c01c2c1c403001d00c42c40405a18a20072800000c0741040d202c520b200880c28030904200510008614007070300e031003d61011400000501c2405403154a2903070340305c4c1600b24200c2840e0300315940c00380c44a41c81d080d144144001d0000000301c665060044e001240e141d400ca0101c100d60000c0d200e035503030f415074003d21341a02521140e16a002c0c0803500c90f1400801c00342079154001059802e21000700104041079425542c0d919100d04507404e4001100d00c4484100005e2448840e199031400445c4c040010074020300c0044051701c4c0050001040c110000c80d008040c00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 668788785 1250 668787535 668787541
    0x19170a0501084b0106260114040b100308040b030601090b1303020609220f0c0f0c02130e030705010c021006030c090902010903080f0414091e150d03030506040f050f0a05 74
    0x343c144031151035140c2c4415400c2140109071a441d1011285c02c0c1c2c144880b0400c81c81c0780d010100c034201d9015903001c8e00038a0242000402003802d40481903000514180100c415a030389440b496080d8125401c030300d081c003c0000602c03c481d80c0c00b03922000034009414025203812001c0c0c5100403003209600c00240030b6840400c0046d003e598a0800b50300d0881100604a0104642c2c928500100f90120040b0000c03843e040c540e0340c6084c480c042c3c030807010009440e16402d10f46a502048003180111420300700580d150310740540c02e000c0c1400580f802522030000403e003402d0014000c1c2c1403009a100b40341c845da01c2d041040000c81c000600c404d088030100c10b400a8844110300040751540320a410113804441c0009410403058001c100600440d401200d101601e040b03564100454850280d070030b0800042c0711000e0b44888107808658036000f42e40040550240703007035800403a40c1c8101c00e580c1070307010036950020444142400c1c080c090550003000303010401813030502c9241c5917101014106010880d41c403000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 668790035 1250 668788785 668788903
    0xf030102040b040e0406050901200c010615080f0123010302180301150807050402030712020d0e06090304080105090d0f0f2309120d0519170a050108 65
    0x4580240c92031102442d643c0383c0360001c401144000381c40881c0c0281c41d010014101e101c06100d0360304045141c5080c80c1054118062220b801d4100c540c0d166125580c0e00000100303154800c1d20005080c3c0d554175050303058908219820418a41640b0802d210652440845000200a003001c010100309081c0180c6035010b60b06031484105024a18035015880d051402c00e40344400b01c610b80860301110b040303520f030b9074030703602480240e0205032807500100c6d4080080c65002c02d903580240135271944403000098819512040c0c1c62510206640803d400c1d080018140720304a000e01810764054441c0c070042c1808041100020500341800840301c0402c5010182d14075114400c0c2e40201340c105c00c0c074410341120040a0b00302e442a6102c0148148280070030703a600704038000e0214185116201980300e0701d0a00080d11080d000901004085c0c004009041c0102d0244407210307080c441c0034252440b0f00082e95810b22100d5490020803080000c01c00c0800f0200d0f22646c2004448803425408035000c8410020b00418 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 668791285 1250 668790035 668790037
    0x6010206160c1e0210020d20030c01090303020c010605040e0a02060f1603170f042609130c03141b091507050a060b06070f080708090a030303090215030f060f030102 72
    0x180c0240f40c200c2c600e841c01d28441d81840007000460084400100c981034910007a40e94549a007191000329840507001c410001c98003600724410880201070f41e2038403014160030b500f100c200a5040700070a60104110101e00001d214000180100f600c04100555040340b445950b60341d103a0000744a0f0000003005481407180d01c003540c00b003c0c07a1000c030003100c05040c58007600c81061a04003041710f035540c4001179450318559040500964000001c80700018804e1900d03804d42d0240d0030b442403520810069044076031984400d4000d200b10740350002814540f01a40107060f240b2011030080e5010000d0305100c2201c0c040c08001d80700c41035424405544840b6030300420801d103002000030181e8078000c5140f400b0b224020904500d19480750700100103007060351040100c140a284d81c06414038108901402c00a0b0340280188401c1d401203e1007401d042101d0300261607d030458004500098880f543d070021400d0005075040c60120580d90941503240c440f1100b42905d80c0101224420000e004005140ba20294 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 668792535 1250 668791285 668791307
    0xb030604020603070302040e040311100204061b11030714190503030a08060307050a0e1807121415090a0506160f0c020a0302030105091e0708030403032d030906140601020616 76
    0x68110320462070241004bd000042d0164105690b0082c411622503c00d081d1080b136064417844e4459500000003502c0c409044441c04030211860306414516206a81d020409200104040030720409000090400d11481c000440c7e0004c183c0c01c0103103c140084d580100503101742032103d140061003070350f42c100000d141001d40e5100390b41111407818081205031006198510403500102d81c5c44909001d650015a0354110b40714070304c41c8101e42c0c003800c00052154032100e00c1c03071034000003114801c0390800c8030225404410764a140d95030b8042503000c410404207206050740051344c006000b01150081d400074140f03451100324001080300080314001150f803034111403c09150042d0003004a40340032501980d860141c160f0700c48018444202c0480c0b1440c00041103030a036071149001d141400d02e1942c0546e040c105d290901c040d1000c15000809130502c3c2d10100c2b561a2170150390101d040c1141d0f00b4058111880d4080c00b00f211030300c0700100081640c0000f40240c00c01000c0c00160100010b07400f007240c00600d01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 668793785 1250 668792535 668792549
    0x60c03090316060b1009060e040207051005091e031e28050408070503070807060813060f15091803050a110a051e03121f03080c0607030e010b03060402060307030204 72
    0x3006400c2c05000391584040b500b91019a00403100400080083c1d0340e410052161800003020350744d00b003040e0b050075005844650320850403185040000c0644205840007120168401d84c04994a525151480380c0c0c000e03d0000260095440c01c4d2012110b04442450a00710103000c040004121317000140c40b001609008001180c2216518402070008100d82e1261045407120300c03e40d4804201d52801151040481c2c0b0000010700b0b0f03c52400100380c500c918020301720b6207003990004200c00426900e0082d500000130190000a000c6002c0c2d0942036030702000d4202817100303444c21002e0868100e6545580f0700041e054180181c41d0702c415802101d07441c9000024694030700880c0002020410002843d48580001001e603540c0103605d0021166030380202c02000e4200c03d00ea2010407609421407044c500002080c100c40318901d40c8a441d9004a540810a0500254070600c100860541c4c948a10728400c00204001c0c4501c2140400003039403564081e1010b80301d1070b400004617440c1402941164010020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 668795035 1250 668793785 668793817
    0x10b030f15120d1701081f0902010c12080103031229030c060708030a05090c01020a0f02030309211c021b0d0203010c051e041d040c09110406090f08060c030903 70
    0x2a030801071402c0413074011040c02250800010618210101c0c1d05525100c151507150729013810440c0340d001612500406a06024010709000701262003140d1040c0b1901c00c54030381124079451403030002d001e40940024011a540380500d182c200c69224041c0310203016405416150081e00100000d042988842030140e0188002540004025a05014501c07852070760b0401c120540e90b200801c3d45844100074182c2c0141c00941c00324002507000104c1c0d0908034009002c503410705c103c60700452181021884098002c104101107000100000c00a10701ea05405811507004d9080d140000f0750b0310140740e405071000440c10480d0200c9900d540c4000c540703240c0c0080c000c5c0045840c0780b0014141f030b8480900d4440320302a60342000e454150341c808940854064490762030904440e80160070216001030f02c220340840306010f0009545080d406076044002d0158503030355440f868260041e00e070b03807810780c030209071004800c204100848020800d0756024074410600c594075504c01c8080e6080d4826981c41080d07000c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 668796285 1250 668795035 668795053
    0xc0c04020c010f060b04030309050910051e0f030a0b07030c03020c1e0d0804051207050a06050103120e01030e03040605070f0501020a020106030605060405090c011115040503070605010b030f1512 85
    0x7054004410035084440104581a02c0d682480700710310aa0102a001c00e41a0310100a18204204450341c002d00250080e003900b078880f4001407074981c02a00c40b280c0c03000c982610804900e440a8011540c080440c02450610032507501c02400e44002030400e803c0c59611007400910a009030100d40302107031010182c2d9000340c0e00701640c071524040901109030510503415500411801014801d000360340140c002d2903081d10360441c90701c051780120411a03c0340500e13031000e00002d800d8020707a4041c520500e0000302512140b0307401403d001190403a14101414482c00c41c21048012040724141d402c0341c60301319500d410609040340c1ca5000300324002c2c2190b100194051080f0f07419400042070703900c0f440b018003ca481d036070b04200585000343d4406142d07400c0034500d0000b942c01800b031305411075254000e0300c5440d0102c410355189182c0485069809410002d52141000300d0f5204490251510080c0d00d425810800060040c8400080040c04007580010b4910402e948d18070305800c50709442411181106 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 668797535 1250 668796285 668796307
    0xd1502040e010608040c031e0f1208060d03231306020105010e1008101d070803030103020918071401020717011b1b020d0c0f2402010504080405060c0c0402 68
    0x50300a1040101c0e00400d0000400e403d80b1074950076000700d4104140c4420345080d80ca902c108002e040c101c2d49005034620801c0300000d1012450500b4007030150070040c100310b401c0d40d8007400d88540100207503c294000144d440c00690080b400e00c4003504403065a0348240b52100c0c41c55024421803c805103a4050700c0320000d03049505400c91816900110722003055a100c1300d03c100a4440107000b40c0000b41c00180e075801034048290300c2240941c0b84026208201c00c2c90401160130441190090f64441d00b00100501c15810166201307501701c070075140850b6112040e0105a40c50341d00764015a0360700e0f1040a4011481e0388200044c8000c0c01c41c2c0d60004075004a032080040c005c2400c0e0042004003800603103103030700141c040c00562056401713419900d19201e21960030130204124000c801c4402840c07140b404a001c044c290b03c150701130000c1d042101420320280d013007000030b4540d0b12a20011a8140703420400019036080540e400c0f1882502c50341e44401c10000300b1070508a401c80080d070864408a2401185 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 668798785 1250 668797535 668797537
    0x201141e040212161d042001020a060c0201020c0c0616030f030b0a060c0506090105160e0402070f0606030b09010b0f01143709150c21080f0903090108150d1502 70
    0x1c07031741a0903040304e034154030582d0401c166081303c003d00075200c0482d000b0501481c0782c000c040c51040501c103039074070038449a40b55400c44042e01200001070b0740c0442e109500040400c000841c0d00412500582050350303c0072242c01103038a02400504108408c51010041c50281c1c0080410700001011075081c10b4a40300c1c0103103081c0c1d078110b00b9144c070300c52180811056501131243d035020302412482100f003169144070585901d1500c03138000e42c0140c2e08100040100d1880380c80d108415105402c0400e000c0d1460070300c0700020402400c03021050740343c0070894020781c0c0d50780e00780101e01e071003801c04c1c080110240d0300043c682d0041010508103c803100903480d101c0070700d0a0300412141445c1c10307a0424080c104000f1122a41640104141981384011142203640201000d09049100d518001c05090400d2451018a0400b009000c003240104041c00040741d14030054a90000d51003009502305000311000030000203001e48081585a80604049840c0e22041c0314108100d400c46c42e08081a0800c082032402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 668800035 1250 668798785 668798789
    0xb070305070e010801061b050609150c040b07060b0a17060115020706021237020d0e030d111e030706150b0334050a0201141e04021216 59
    0x24a8400028240340c0981042c0011440680d500b0031a82e09080d800c2e2540b094040820740382c800c0d210645000200c08000e00f910604801c006080b6105042e5500d20300c3d40030107014a0340c0244144410b01c012030201c070035940e0950b0824804140d10a040c0c01141d118013407a00841000d110100035080076000c0002d490381269503031140c41000a021040c12071320b03800300b4040c100050f041640f4001c21030754404080c2c148016403101040b40c4002d0170078501d000701503060030711800040944101e5500c40d018456502001810b04041200d4050900080d490b01480c20f03240061108009444030039140400410503041d645040c1501e080459040d01c40d907a0b007080750112001c84c01c00524058804501c4005000c0b41e07a0340380070341d00316181d40c41200201c03006550320580301d000e0507202c0304030003220004d01c6e80c070b121060b20783c41e60b10045504001d00b542d41341000031440d05021410f00ca0b89285403c103c006030b00e188640113250f0b888d240300140300d21100d101130f480c1a00c0f030246260b011014031080c24003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 668801285 1250 668800035 668800037
    0x2d060e1b06090405060f30120901110703050f0a021203040323010221010303021c081b0d1104080601080604050303070c0f050a0503031b0702130216060501030b07 71
    0x1103036481081248a0500340c10000d030401024003020416052079040241c001000410702841505444003040082c0c080f01d0f601e8101405000324140141c0390049046903010007600034080410b0300000d524524407405d81d016041041c0e101030410301c00010b21000c0007030740c1e0100c01d8624604200a00560b64001902c0c140e2080c12010000310000f1400000c58007100c1d40640c0031240c100c40301b44d083c19003150b034254800c0155001c010300305034210181c0240089608014506165504509009140801c827000c410305400d1030134a041d00558101c214164041c441e0a0011321861000104e01c003980030b00c07918407550314202591000520704903809001030b1200c00b001c03610b0b1030780e84035049aa01c580558018045810410118028610480c0030382d188038000d4a1101c00603002d907442c3c0349000c0e008041581d00d60030200c148a81074041c8400d4503054404000c90f1400c2840580002e0f80c02e144161004150b203034005808044803d611000b80115034001c50208450369590808800c64202110504 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 668802535 1250 668801285 668801293
    0x2030a0612050604060b060f03040317062e051b030403030212121906051e0102010f0c080a0507170c0711090411120709090f05060601020f0a2d060e 65
    0x304078010595001c0003040d402500a0242d40c6964440b040100410050103812140402044c10800c4e60140254091440780e0b4440d00b040301140c4692510027405008188920803c0446040d028010075001390f110440ca80c005402200c0c500c0e055425100ba11038030415500c0303540c5680c92001d404805041124082d40030b9840d4456103800d04912407040440c040c6010344404089440e948a1201ea03001c2c40394042c6000854544800000d80e2051815005400206022410800550b420700a8860a04040c0c43c00d110780e000307042c80a466a10001c084254460766440083c0840e841103150083d00c002000915580d170400085800090303000c2481920440503030b91028006052030490b8500c619000840045501050000c104101614a001035024800d80c3c1c1c001c1104041441050a818803480707010500308018584941007060041a07a03041d9040400418451000031615021880d440000030032445007032072282040e00e1145c2c80310fa6420360a05104010454558011001400018111 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 668803785 1250 668802535 668802539
    0x90705011e0e010302070c090203061914090603150c210f0a090c08010c0905030f06011d0406111218060106120c020102070204050f0709080115060c0f05070902030a06 73
    0x544280040c1070705081285480d25407400c07007610520b01182c50540c140740c0946410300503240c100303070144035030840d8001c550300009000d114a0101c4030100030b08210031900c1003013031902800002102600e03240038004c2441c0800964540c1d0184807425502e4005440240a8200b80c0c910014941010350541c001c503100210b441d40815062008038411200c10181500755030300c0c04400e0300501210702d02110701070281030001c1203084c400c0c09074941e1501a9643c1c024014039090416152000c4c1100869894100c000107000701070070460070414005c9030b95002074181d00c4620f01a001043c1e6080303403c84c410004944180030307414200da2140a2071005c00301100f0044901c12241c1c480c1c10a00c030b010302181c24980030340d840e2510758200d0074042540d8000142080c42d1038010600b681c0c0105c944140c940000300400440940007076004003e4031071003000300a000c0d0a06054042603145000300000d00c85440398030790412180c0107110103100d40c090140c0300a583d580305d602c40030750019513001041d0381c28a080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 668805035 1250 668803785 668803787
    0x909040b1e1003121e02030c010b0d0b010509060607052505010215061017041103150f060f131a1203090d1704030f0311060f040221010b0406060809070501 68
    0x4814001ca406900003103529145039182010b0302a03005a004c20300048003d00c03130b0480f045044060081e07140e03401540c2d580404d0714005007114292003ea5100e500340d610900081a036569100307055580988070788003d034461100180e5103004e0310f90020f01500c15101c01d91003500a042e141c1d0b080c0e500f40c481d080e90040c0c03284016a1101024856800f400641c44005480343ca0701040c0000c002c0c081d0f0410005207400598400c0b00364038119000c0e900c0594181d5140d50604003000b0301e403080c03002e00100c0003107402c2642c43d403070020768060101c43c418500c001d8006800ea8840c41684100e803502002003040791048007400481080509005224142a040c2034290030b202004503244c00200500c8201c078400207650355100854100c148503200f180601c0084005542500c0c0c1c05100f500030f440b441c00c00001c1c0b9050740d2a10b0300040134000360324200300038000180c451441c48250905250421405807075602c165600604c500c2a51540c0181001c03c001800303604918114051b401c1e81066681e0346c6e4881d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 668806285 1250 668805035 668805091
    0x30708041811220f061e020c0603070f090902120405060a0614011115190f02040b16050c1c0b01120519050a02030714010206060a03110f060909040b 65
    0x4910020094100905040090a6001820195615690743c00800d494130f002c1d0380700340441c0e0000e1011900b04070141221060021700c0300c00204a6200a001c0b0007044d4010510300d0002409090034400941510307545640901084d0b00a4490034108548036240301d01900300c403079025202503034180501d0001c0392643d070140c0144803d5070700b8800050501050000111113203078200c0003440c5203010311803a8411048030340003107901400108c85000320a00000c200c0300125070300388103602042481000100300d10302c0030784162810120f0202c00b401045680d4185607082c801c1c103d81c400c0d48045800364501560201303040b090722142c05401d808000d6a245d40030601c20703a05d0b900c5c002d0556130101880c118400032030046201c90710321500940e1041581540840d141001070740080e501190221a0060a542c0c10440d55600c00301c2110564200f03440e50301c800310a4070210081d24015285480c9000d00c4d511444115216003401802c441941e184c1805c0c010403080303050750b18003140d1606030210300403031072001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 668807535 1250 668806285 668806301
    0x30c22080601060e0301200304020a350115030507080d0302070c120f05030a03020a0e0910090b01050c03040315060b0304051203190e0c2d0f01030b030307080418 71
    0x200040c1a6079080c00740540361507070380a044940c11342d261981c42c01f100d40341420f50084503421050381602d0341032510420118000f607810090000c20510701c4a0000d0b140c512030304200c440300a007103042d0080e0b60f00c001409410076408603610603140110000400c0000189801100c0ca02401d542d00d500c860b03c0c4c02c03016889410005058180ea03008280419015141c2446960340b24079246450801305595213425074210950150110f50301103a0103100d5a006112452410745c2182c9410701407034040c2030401d4103241c41c05890b2000f03a4444001e05541d0084c4221440440500e0440703803215078030b180a0203a903038404580805141071070400600100800c080c1c070b0156601c003018182c01000030210110b6508001c0c0482c0c04010f5a00c600382a07842d01d88110301e6503c110b08060700f802d20586044c040d40401001c2c28040c001f400e0781c03812500000c20440180120070840d445007034400c0000048001e0171060542a903d40400500501005880001841110742054054071500d49120f40401200d00c21 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 668808785 1250 668807535 668807549
    0xf0403090807261c0504090c0e0913061805030315040908160516080f0c03121e09101d010c020d0201030b040f0c05250309030210020703050102030c22 66
    0x80344071034101040f192481c040750207100e4200c6282205001c1103003441c40c820500f6030701154000905100d210014012005c0c00f10032810300010342070b044400300d1500500144020112101d60b8032001c204100c0d40c00c403007180035030701a0342d07844041d50703091a85e2a64800d84441c0d030b46050344800010f0b00d09040c010b400010fa00a070321300d030801030210403680041c550380d5002c4415001e4445040340352a0140c480d40060090807000340f096035000a0164a0700305e005c03a4441c420790210307004074012080901140c40143c0b508601c1026143d035080d082c10b03140103803000198002003100d0f40000c4280e000b204118603140010301c200307a0200c4040151284a56150301030740000b00528100c015500a8115800c1c49001074000180035030300440400072100405010400038000152030300e0320041d2181e15075000c80004100c0210040d43e80d40c081d01000e480d12000740200d00711502c803400c860080c0706007001181c04c80c00940d900e1600480106041c0e01888442140d2a81800c3c480c2074200c90100e40c500352111 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 668810035 1250 668808785 668808809
    0x6010302010c17090310020702100e0a0911070b071812030804110607060c031a15030402040b030f0105010305070f0603020a020d140f0c0c0f030d05300f0403090807 72
    0x5880f504100002c546a0b05048481003100e202076440400400c0600e0041810060b154132061040040d0111070301c8c00300040000c0041001001d030341c1c512402c1c0c04c580101c0030000300d0000d450840035040c00350724009031062004004001035a508040341c403038041c02402c0146079158503104110743e001004580a00001e44007400500095010110003108074801007038642032004950340c6c0c0c1c00307881c115904c1c1400241c0701c0d5600b94151032244101000c4901c100d4440751002500700c08810540001800070748a142c0f00c440c84146620107218181d80541c20b10b00902c00e5603141c0c10070300d42d180c03040d200c0d0180d101d00083c400921141310344255002d60300c0b15030150081c040c00d07440031941c4802499442001100c1000b09041080d07c1c040100104005100900041100c0e4403c02c001c0560b1010250b01a4100502d03140b45290322004a80309100c044800101c145040d106c1d00c0c068001e04645032000da00904140140d803810ac40d4403e100b81d11a9444482454841d41001d8590140d03120f901d204480c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 668811285 1250 668810035 668810057
    0x5150906030a0921110a1505060103200301051305041a15030102180406080109021c03170108210a0e061c020a082d07030f060b0c0c09090601030201 65
    0x1425000035038105120003804603401045884819240e100300c0c8411383c05205010410038890381010002a0382c20030800600000542c079119401c0011200012007641e80e038400000e4810780c000c0e48082a61480f440d8885401c0808004403182d503842805001d1041d62145903104880110f4010b051103107501018481651a0080034404901006016841111343c03001d5074015586091014101c086907000400e40c200003510103000032203041d90007408031a410066801e02503254138540303810a40c1e20404030000351005007011a10040110310240010410000000362200c0004004c070821070040004114540c030702100300100e200d03c801a40115010003810700142c907001300500400c031002c0e182d95880c048000703441400c07640701d0190100495940ca040c0001c0303c503212080c075290003000143c0d00c1008621100c0d0404407100500307000405403200301c0310600320900c0d0001401010b070041040d46075500d4002d21502c40e409280181d000313400c541c0004888800000380350b4102d98040c1c54000840c2c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 668812535 1250 668811285 668811289
    0x230a0c14011d03010b060f07020118080a082b0203011d01050a0b0a0210090c0314070605030c0c012018090c07030807231e090102060105011818020c07051509 69
    0x10310034142c140e459543c8801141c03007603c41100611b02005c1030b0500f0b564801c2148005440c0c0641000000c1c035908a158080c866842c001500d058100e8203c0007240c2c4a00088185140301404204078100e0000e2941800b250704040c0d4000c1d50594820a82501c036140c50b0b83e141101c1964240700d0aa88560100d0f01000106114002400f240d20903105845042074419416000c0d90b0070001c003164003050451003003060110040202003032000c55806030441034607214004009000141203c460b605e800160928680703c250b021040321380d0070051410b60006400e0f0142d9040d001a200c103505c0ca00303440c1c2e04664910780b041c04103100b0001441300c10300341540da072012035003414010a40303030500c464088000c108444640c4482450006901125621030818440d28201c90029035203590081d001c1c048600b0f00d84e00401c0a80c1503503000c3c070b042056101083e44000d1844001d911248104551402000140e2907940040404000031030854442503034030b03010702034100d14080454880b501d0070f0060907924 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 668813785 1250 668812535 668812577
    0x702031e0705041b080105010203030f060918010504050d1803170f1b0f010f14070c051011041e0e0c070f021c03080a05130f230a0c1401 60
    0x19400469850075102c2021504480140c8003180407001c40032130008000b0341c00b42c15140581402e1003e075055090402c0789002c81c940c058100391040082c0d900280842c07080500e0006000c4070b020090040782090700301640c40e14507c80e021000641d00300b0303c41c2c55528000c03208404a075070004010140f003080250039081c0d41c002912100032410304000741c001d103071000a0010100d96081c0c02a0290b24500c1c000642150701001090404070b08110514401c00e000c0302d656680306040b4100b04090904a240003402d007039640086864661030200610705880100f00948242c0310300420000032030308080500b8202003101c0c42500c1500e61358600050070360049001a29801d4882d4138000e59400c0994005500c082d40740b00e04420340031400740080705050380180c00903044403031600d0411140c01c06842c0c00300d01d041e0f05040948032003007010300d8004100d0440c85d200c140421280e440611a03284044013511050b56034030640e000654100c0204008101c0071340407891000513140e40081e030141c00040e400c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 668815035 1250 668813785 668813833
    0x1e0c1005060a0f0b0309010515150a170109150e011a0f07050d05090906090603070512031201031217150d0f1a18010203090c0d1403161205070203 64
    0x25550700b0000590070003058201c005000c020309459141d142004403503085510040031101186800c80c072800b0039441c5d00d10210700340079216070a1917454500202c1a1003200720015125812036071032000080b031526581c0b102110721404503141ca81d041e500e14400c2e503100300030300440400c8020380039001011401100100b0f09100101485410582c0f552149420b113180d44041c00c0201c0e400184001c00c0b8070781410f100e40e105904560401036814440003003540c0380168001c0038040c0d9008184540e00010400664070050441200000c0540e140d01d8441d00000c072030325a800c017007600103100000107030380c13001c2d914440d10400c43c48800e0f426060341000400390b000358050307507160414550328001c2000030140080d514100c0000d8060f9041c503c050300181c0c03909034000204c503441402440f01241e40441c2900201c881182c02202007100d5080c51a043c1d9100d00804441d48030001d11002c903001c032040000d40d903601844100c0000c908504080d10107201d0414000d41c190814150200303060b1910b03c1b0381107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 668816285 1250 668815035 668815039
    0x31c0b10081012140313090b040e0a030e010e0616030201050702190b04020103061d070e10080a091403072405060112090c150e100f0903060207080706050c1e0c100506 73
    0x102c10b0911340780181c00c540c0680ca00c4628141d00000900c011111030140c88a00002910304001800c41d11940c02c4c0c6803818071030020f04019500210700b00c0382e8460008038031890360060010340e40e22100030400400c0818040d08401550a180000e05210b0012404602c1c4000c1255040d8980318143d40306040031700010401c9042c590b0310500807524851494030917403450141410b03461182001803001c0d000c01204401c02c2c1c401c1c4c002d5900b003c0510342c40340c101d540003520450041090390b120703d04100c2d20802400d480e10755200c045020400d0048600c101c50322100641110a0070354112000346040d10021100e45010880f0b00c464219201c038141d00c0328502d41c1c05014200b01064541005048164200903d113001950028403000c03e0324284003062001c02041c241501e01950a2a024103a2803603440054500c0343c0c00715195090040e10030850700100e40c086010400d82c90000c03520303003042d045501c2103030828445420000714009260100d5400079175504c001c1c1081010807540c98003410b80140155 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 668817535 1250 668816285 668816303
    0x50c061c020a0318060b151306030f09080703021f060b03040b060d020910050108010905090c0120060c03090c030604080315010e1009030515061e03031c0b10081012 72
    0x907014015101c0604149101e2600400c003521b901c8100322080d0740aa6009170760660402c01c100b909a500400301c802c403040c5090124027542c1d0910048020951294050201c403000134600d41010b80c04140d5000c415000e0030040480c58113001030340200c65040c001c9044000302000403c001c51042c41c11039620101c0148941c4058110358040f480b4010141c4504501e11010b400a100a40c3c01412540c09045160420030062070318004660381c4802c030303250b900d0500614002c8619001d8070110005841c0e00e440044a1890404d00c0440c0c8481c0d00807110100c542c0a02000e95140d0318000c15802c3c0030b1504564194103544881200118490041c0d40c8541071106050302d05402d40c82c3c074044180d40050300d44034021440c1c40d5040030760502c1014000c2600c00c1c403641082003150780d22060401c26941c00c03064a8025615031001080c07640c401c521001006041400c051540c40e0801c1d04112500d000560301c0f40042c002140c0180c80880381941c0052103034024610500544200a00f600161030080800d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 668818785 1250 668817535 668817551
    0x60909071a2506020301090b09040203191704080703111e0103020c010f0504060902090610090b07060609050a0e12040e010506030403050f0d06061b200118080109050c061c020a03 78
    0x80107102c8034181d04803106078000c801000b02d1801c80c0f00702a00d409082e1102080391502d0782c0013170b4903000700c40107000340248585004030602080ca0035944012004a406a0740d13151500b00455031002e13244411220049401041840c0742800910885180ca10500005444029200640103500300007000c00180d941c44d100d9903814050f6004041c080c50003450300094114050061022030f000081119028001c036a98036041e4550100e40b0600b00c404101500b81c03611141c1c64088060a42036004039111420002480003808c042da112035129403624080340c5201407060840e03c01030065106005840c41500f004002e541002c10040d03900902c0303032500e1450500f094203481d0054101d2000042010780c1e401040c040300d9004540940140d030b120700c3c1d14460900310303580e40d130450b4407442c00401001805e0700c8501c20ba034064000d5180300080c00701031812075500c0340c0d4154020402014141d500f4890060010440e0800001311005090180440074419005a02c05c41c00b0394010003426080507621820 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 668820035 1250 668818785 668818837
    0x6032015070c0e1608010605070201020312010312030c11031c02070206030f150108010b0a0302090414310c0512122b1e0b03070b070605060909071a 65
    0x1499050b100300207180d02c0034106040b6900589009001c0da2585100e11108204140c00c10a01c41c11140036140c040d58858007440100e0942c0140021910300b4078249001204010800d0103d001c03c213030344d075010426203441017412a107103070500360080141e41007042061480f44030720f070282c007480110900246c601309296010030465070003100e05020607030601e018465021906084000311000c2480d164520b941000540b40051081d4100801450340c00604032080d602c0b80e0300506040c42130001c1040503031420914010030f41305000084ac10750f040481441d03140c0100702d003020488030f4010001100b958146000d002c125500d00c42140003510459140d49a4003584d24002c0090001c142e10fa01441e1404a80e443c52400c0801c5115001d6800e005a0500100180c1000d90158100310004590a50761001281c1005465000981e400c14002400703030600219411040c0201000d59420b0120340e1019140340c1c943d5440d01801d010b82d014440010f45880e5058040c105049001904a5540c00b502203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 668821285 1250 668820035 668820037
    0x2160b090d1202010c1704241506030c1112030106110313140405060d0b0f0a02090306090109110109030506070e040209063405071a0c10051906032015 66
    0x80c0401130b9110640d000f00c2c01e5100d158594801c103000340845450519a032042080380415549100e0101c4a5600c1c0000c02c491b600200c107140d08040410a072640c80e40801000b409000100c0000301d804459080d918020014100140350045003d16081d6428060100e039070140c00d40d032a1100f032006000081980b4800c658400041818a1601c1202c1c9544401e200544200420551181d00501c00307480110300425803103035000136042441100c560360f20b14284000d016030813800350944a01001c120f1841415880703c4200790041e00000c4200400b00c1c01114910710350302004015070440342c085641c4c64098a42c550a20740c0c024009030a082d28803020904c80e8004210724000d0140f21480040c016086041405009982041100300c0d114a503c3d8035994402d0b52103047d80c464a00794102560300d0b038040641310190281002d1f900d00d41541e4024001402c400d82e400d1071000400c0628908100d5035110309030813207501040259904a401041400041c41c01c00100c2c3c110f0085114180c401600720 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 668822535 1250 668821285 668821313
    0x60304140304170f060c03011401142a010f11160c03020d2a0503070b1e040b13060e0a0509091f0f0b15040b1606110a0f02160b090d 58
    0x4000c240d10200415130a1030b00c5e8001c1c1684504290800c0140020a40080c13081c5503c042030801500d07005600c119400544201403d030407480350b1100c40a1803910070302c119141c01c00f081100038848448410315100c00c881c081c082007030041c401080001c0f01782020722003080885000350036101040d03540742c0100300040d49255080300ca819990026005c5102c19540060601d145091b04403901410701e07011039521300241c06600d05140001c22101984003907080c189071010341d0407510079203c0381e4500500e411504500c50111041d0140213010415610034844034240300e00052168540c50b10b0030040c804011400303043c40c00a40680040400d0b15201070641c1040071181f030400151050b078002081d4112000828010311440072039480204050000085d80e007900e04400b140c030b0795486c0e0aa424180c6c01040440102250b08124604440c1d02c000c10141c0f0340e44800b42c50b801011112070104a803901c50414900c0d0104548400034003003600110041c105003980a070154111582c16100d00000701040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 668823785 1250 668822535 668822579
    0x4020d170a0c030824040e030412140706030203070c0609031106090606010e0f0a0e0603030409060608190905100e19210203190503041e030c02011d060304140304 71
    0xc0b16a1000b05644001d040340c1c001410742d003600c510700b5404200d0b18003a81d03d400c998441c6031a0f10740c00f00404801d00c1110000d0108203042810300661340f605010102d440c1504500c07a00038444001042070081c000c0320f1041603142d4803c00c180380182e440034010083d00d502036040103850722420075130391002c03c882c500407807181000b004681b601d84001400c0ca40e88040e4103024003181d42c40710503142c1701c10034031209a524034220b1242998918000c00d14600a40d84404240c0e41828400110a030b0892500390050039800c03460544036800b24041c0090303521040c80102070ba44010700004104446500ca040045408400c2d1042c002d0380e080d10000340702001304140e03082600d10500c80d0503180a0100f8a1440c0c4082c00a142001c02446903031081103a00d80401d030030712900000081c100710381c80da010101204178900720325004040742002050301c0c52040c4101c7c00b08400034414149a1485010800201130040c0b01603d19900e6556080039041081e2550030300d07120500003c12451710429003020700d4091 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 668825035 1250 668823785 668823797
    0x6020c03031e072609010b1f030b0105042102131103060a06032a020c09040809030106080f0c010c110303040308030a0c0915050a09090c030e010e06070804020d170a 72
    0xc0d03001201c52800c0648120240612540d0200e813146442c05602c04804d200c440803103140d40d550701c50901402d009058140d0200f0154001d0b200d03200c3e02004040380d000d0aa1b01004541d00c4c0b17000544580c8154000c0d2001003e40c503880c0100058983d0303070554664030240c8440e41c5c180c17a4038900c0086e180c42c0c006000c2c00c3c1c500441040000d050942001d40180200d05e4248002400c40300010004000000d81b000782a40d41012104024000c05c07580e1044c4402a0021205140a0800000941006004034880c0d4204071001070f88100c001070049000303141d0301c090312a061151006507400a94514100c50501e034841d98216280d80504c051310040d401513144a989180040415049900f05180c0100b8400100c0c0d0a011426440d0b40b005008061424516911540342c40d0a4418119540c440c001e418140704212602c107905812072122210114001d00810720314480c425100e0008032507040c005003400c9c0014000d4500307140c0c080040c90094812206208411796490081d0384498100e1001c190 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 668826285 1250 668825035 668825071
    0x11e020403030e042708091c021f050d0c0216090222030b012d03120e01053a0f06060e120a02040b04240807060f091206020c0303 57
    0x90004040d05907102d08440030840f081c0e004c84a4480c04030b400f85d000704813200312003200c41000240012a2a01d4034007c01c00625171a94000404900e02445812801402a001100422004440c0c4038501d0301c40381d103882c2e04040840e075100c401001051044800c511411425102c0300c2c1c1e0002c501d02c064000346c5c1e1702582c1d6481040d4001c24070b00400c0820000502100d0301000492502d51426046d05c90044004201850b44082582c1101d40754501c000c0b0500c031420008100030007015804803648164039405480c000c0c1074010741e054080d10502200b184110550200c51200140c0c08a10350300550f03107900028003024601c1000c0b20600c1a5202e522641c40b0001e006054024032040801c120413502c40760100c1101d427041e51241c0000a00078051a241d80294044e6551a002001d540c031150081070082c1d80c10f00802c2880340c0b0701e031181c1156030007060408114188038000c40b00c0c9904451311100010b501d8544503680300c110016041e2021507080c401c5c1c4100c000288000c3d8002c04075040781d858403078 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 668827535 1250 668826285 668826287
    0x90e0a09050114100612060306290d020d0f031b150501050f0d1b15031a03010504030207030308060411520212010c110129040c02011e02040303 63
    0x6480036000b0b079076031982101080324019000e00054245d9040345071004088004d00c0084001d05180c1d00010480b0f414219080e175280351003e030303400ba80442e15006800907070030101032110641c00c40720042c1d00305440407150004905604c0b04c481c0700703a129141c500c04282d100490a03c03507040b484c40449280100421004103103006000e0356002d0304003241c400c810101101d000480207008058000c03d914154260101c400321240c00000042407a03807044040880001401002000f0460314503569502920000c0214281442414407460340758000700603450a5880076261201e0051509501c5911170080c801a001808090401c4156800e141c401014503298095580400e40c004240d0004040320103880d10300282c030144403c044000c9103c41000b008d4000310720f0032040d0000c441482e6080c0084002129840040b08444c903050300020018031194961003220258103800c9a01c03060b4003030443c00202d02d040c0c0e10030080c514290000082e00e81d00f01300301d840503451200104178050b40c0824104141 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 668828785 1250 668827535 668827541
    0x3020d050c0d0c0801060f0e28020c1f1a240403210f02120f09060301260c0f01050f090a06080108010c030209060d090203030706050f0103120c0209060f01090e0a090501 74
    0x83d045100303c4000848c28211000c0208000600e80d50345100900b05401c0d40e488150101184101701c0c55081d9502e652240a069655188200306007841999108089605550303100f045024032410b06030f0900e804121080000c00440d0f001c0460261800d400004030300300709400200300a6200c0c0c101c3c20860120785945c3c04010220903007080c140108000e00c02500703540130480060384070400c04a903850f03004007038031a00c0c9405034a8130240c00010000010032920882c00540c94010100c401244004041060702500c800200300a0b5401c0083c2c11442c0c0c60381d60080006d40186282d8100450500e92118001070450200360300c00008038280f40d0040c0040c4000b80540100146181829803420450720b021900512a0304c130448a0555035440c19411507806200702d4034480c0c1c00c04d0303080c085800c0840c2e454180e550284003c03503001c5990005a90918001d20a4a100e240c005100707091654a1710141b03d030f0b00c04039103517081c10401e50140100d1042d0241143d14000d03030240000284e0184145445421 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 668830035 1250 668828785 668828789
    0x6030501140a03030305090c120313050a150503130f061d03070c0b030705041a03011e0501080f061f0215060103060305032d0a020c240403020d050c0d0c080106 70
    0x2001d08407095550941ca44070750600849505250000d420f0340e580000c582401312803400c003940b0041880300c40c404144000082c00c031004507016200055560380b4104641c04006100e0318400660070a400d6200a0241b03019507803001581c044080c5105441c1d60303504040d0140c800443d813940d546c144240d40083d029503001c42c030000d00e038015494002c00d43c07580d00c500051882201040c04d40040003800461042c0c00351001880c01008484140c280300800b07a200790000d004884a5041c0780b580081c0c0e00b03041d070010004948041e180cbc0741850321010008a1040070081010390020300c03a1107008881c407810100f581e200569980504840b0f448058101c003050030182140e8101070504005001040001c0210f81c00703094011b941601400341002420040207080c4c6824408140110302d6088007900458071403261401101d040d50201c060f1a510401c1c0881a440c001058905110500043c2481d1100221060240003140c4200d40c0c140002941c8600804044801d040b95103020400311000f4020380c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 668831285 1250 668830035 668830049
    0xd030b150c1501050109050d0809040f021207080f04030504050910080d021e0a05060f100909080903100c120903020a0c030f0203070b07111e03070f080708030f040317040b030a050106030501 83
    0x10300343d187c18002540c010400314058408500012003c00540e1150702c0f68004c104a0300c0190340b500ca03511607500000d501110500042a18000092050300581212a104641c5078403400d04080c100000c0c0010080024513501342109010008214444100111400d00116031300801401d88640841b84051110b01ea040c04070360701c1102400006500072400ba507111500c82c07049134442da955959103500c19103903440145107915102528041c4901c2c0c1d0018000500290120740080f8130070300c0c0c281d04070744950b41040c0005200d62440d031440c00317060b005020308070b0003441211503811440d1208a80302c0c0484d8030858461200d500340f101141005d004140007020344400040c201280c644592078038480160305d03244100ca0004c203040c3d0302c44168080310080c0780d028003184c4000380c6592840740c0d808030342c0c022652140b140141c005181c103000070483d0a510306660400382001c0c0745560b620b0784043c01c02c2d021070b1000740610000c25aa00480061445401d00600100359945045c9002e011600180c008034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 668832535 1250 668831285 668831297
    0x13080606010905040b0d060b15070606091103070815190e091c020d08060d0807140105090109020a091508060405073212100e03041a0301080d030b150c15010501 70
    0x21140746d6884415821254100c213000c91202c0144000034003042d0f0b04894017604000100c1c0c1001440703250341c0180183c4203410010000140026480800703800110f5041001410817000540c91040940030400c84030006001d1a000e89180b003d02c0c0d00d4076509800c920b00214400d41040003914003000000c3d5405116000400910f0100c00002e484000001f03402c000d008024000c200c0c00e858140d490800184c21103e100d441d44128903000c0c0f240136040101030099800c0c134012802154040c82550141640101641005440c0a03400c001814052404401c5107058176000545040140304951080e0301ca0390243c100f45040c100d84048118880c40708041c14142c100881c412080d0740140300160316411600c9600680c5070560061600c9070500e202c0445504041e15002d0000300080900f040c1c5010100e2035142d81d94031140c0b208103000034403400810303074801b44814035814040e9002008005001d0500d58500b074601c5902d80d859800500c10f041c444d4801c82d00700f04036004500c800c5001d40801d10b001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 668833785 1250 668832535 668832551
    0x6140f1215060105120c03040c140f0405040f02092e060c0303090c09020409021315050304140a0f0b04120e06271201021c0b030318061308060601090504 67
    0x250748480003400726200d0400301000c240700b82e0144068600c0000d03091700d4112280761800c3c94000c0d9800a136030072202c1c908041008110110b5000c14030f03601d0100501903250440704001013002400003d4019500048058240800750721080c502512814080c2d0904618141c075a242001008501c0703200034614032850820f0050ac1d0340400d4400180f60946000304001d4101d003040806100b6560081710503034270002c0c0000d0800410340142040c20b801d1000c4211aa603900d2000c085c0c8003681d0142c0d400540c0030400280003401f424000350381168850219010025a50707608041100c1c100700c1651445140e001f008108404c00f2224280c0e0100b5140c13a0401146d5540445c845009007101110043d10494400301d201c40000c81407008c0500c028414803203881d200c609103000f54000da0008204040c10f4081c1c10781d0326068000c1c0745079023070081c00035450000c00340e0013042e0303080c074a59506601144c10040d54a064492070441006400d40d50701a00e0607041c007000142c40b20b90503a10542c004c2c1e083c6003032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 668835035 1250 668833785 668833819
    0x30304050c1018140436051203010b071e020306041227082e0f0204090c03140612100b04090c0303080103050105010e24031006140f 58
    0xc1000407150a9903810a1900a084140d41054407800440c00b03200c941c1d900020509a0510722202c4804261070800120708032416441e040684c3e03800124481c0f01505000030480c2c520b50f21043c10600800c00d031400001e442103030590952080e4418610150046008020701480307100000002640c12241c40403910141e01294403140024030140203d42d0241440130141d0080040e1800031800215442c0d41084000609080b8445401520a9031086440800000c3e08140c8440c09005488007101e031819010704c0f0030301c0502520001000344980070310001800c1111030249051101540e2801700c3e0104d85100c8d28022024018800b61146450343e03003010241c500400e101c264600490404925200414003160107411400d000508200c801c0c2000022325510038900ca069034804d00091007a642d0301d0100034440074080e41c0c0703407000c985041204280c0389560302c2d981c99031341030207001c2c0ca440046c0801c00340100c92256208007010030482c6e003c1809407800003c0c4802601040381c400000c8001c00403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 668836285 1250 668835035 668835043
    0x100e040b0d030e09060120030c07060306080a1515090906140106051209010605030a030906020708070302010f120605060c0a0201140f031f0308072f01021c0302040801020c0705030d0203030405 84
    0x10300f0728007482c030000100781940d20801220000a00c02c01e2005121240d50101564a51200d07241d50034600502c0801f06074144240030f00001c64041c20003c007082101034540c0810440b10f004442c2c0c84c5544c0d805143ca84800003001e6400400d541c82c800942c1c2c6400b4101202038402d04e4410341c40000401006009980c4c1041c140c0301948103104003100f0645c2c41c0558140145102d0300410f502d0300c130f41d10181382010761140124003956016401e440010303075640c84680d0b641525000003404540c03001500d10322203120390f500390301c41d4111000106040f80d68601048061b442040204001d4025401c294203550700034248035900002c0072080d41c0f9101c4001640c003490b00014000c07400d020203400c080c202143d502e00802c0044c6420500b1a96104031900e0240e40e9080c0d03a070b000070100e03007598034010360980303850501051445068015215075095840d14442c88a0081a00002e041e400d010200d00c0040920140151a90000c010030019080804041c41d000b2801c04501c2194001c00c20000003950100e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 668837535 1250 668836285 668836307
    0x10912110f0c220b03011b11010902010903030c230d140304020901170f12130b031006080a060f0b0702010305010b03090a030e0f100804020f10051215100e040b0d03 72
    0x807209510f00c50000c1d1640000c0c2482e02042c9a1560900c24065062244611008101a255102c1c84144d0b14042c609030309130b03088030748080e02040c00401d080020070700601265024520a200f180c40c1041d03450036a0b4005030608403070074900e62003100c9110b5200c2c0c000002c07000205950a4250441ca00b942c001100200140075803000d41c52406842c061a00040000f407403040880825200c84103540031210b40207402410181c00c44007440100056040c1d0b0282c04c803806040c0c0e6440009440b42000c0c07041c0c4200001802c00d100b040e5441d4000941484481d003640080e200500c02e807a920f03d01c1d800010140c07403041c1c0041c0a02d10b000c005100401400142600c0b800e03031f060500b10310b0b001180002419074085a00119084507000a20359002c603032040120344a184201c0345e1001541588060154144001c9442004200208462001201e031100c0007680210507141c1e0700610f425101c0414000f00c921a450030100d89111001201c0c1d1516000704808001c040d104450801401d480081400c4010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 668838785 1250 668837535 668837569
    0x9150703020102091e0901170a060b0102120403050601030b010b04051c0c0e0c03041214040504050c0f0f0a110a0c090203180102031014040e1e010912110f0c 69
    0x5804020903000790140d81c5805070060070505e40d01c4188135000c2c4800d038404d81c40b501c1892030300b0000c14044050402800105140c000410301c9a48966880008220260210341075201d0141c0011030308107440000d0020750321640280ca160b51552810004c1e000060700310400440040c0b206114a4070707412611805246010001151591a070401403045070070b54100e03013500c4802004002c030b44441307400114020741c42845550640031007844215612000c405000030942c10030041001645423541090790010050040c6601d403110140700c00d544c41d031000c2c01e100318403100031401d8461680c106400c000003003400d10280400407441d956480800d510b9006011100e03a011001c111404100d9411640e041c1303040000715903030700b8160004400d112240c4210042d007020489042110b042502508022161580052000700c00c40c0c0344402200388018130100300b540d651000c2e80b0108000841c00f0100702c1494032843c00910440b03480605044600601c010b0030340c40640d0b1101c80752031701d150303502950303000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 668840035 1250 668838785 668838787
    0x50a061d15090703060e0601020705130c270608250305070c020d05030c010c0e0a0303030903020a0b0a05071e270f0305031b1603111c05060901060b0915 67
    0x8012484401c01a01032a0300c0e000302442003000b8146401d544000c081d00d80744405034405549810049a41780014010aa0002040301c032040400c04180c014406452f074070306282190782445034008142f240d0070030081e03030254406541041495009402250016000ca85518440c0e0003903216081e04007602c0c2042c010160340b640001c1503540b2440290b070354294024040030303411034181007007940d82d0407042d80304802e946005600700340300b40030762000e40300d0001c0580320720b8240b89507403029001010032407000d0701940103860100001403c0b1b81401407160701d40000008250429010040045c8485101d41a00c901e0444003104030a8000c4a02101c649000c0d038800c03808190f9108411094031742e580500007800c04810040100003001c009401100500140c0e170329040940c03c8210740d5002d081c0c40741c0416040360345041c00800c50860030000c0c0c001c0301070000d014401c0008580a44418640000d8501b40c02c1a0240095400d01703000b503800030442109524100340006002412504014070b1140050744 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 668841285 1250 668840035 668840041
    0x50a1b06060302031609181e05120310031104020a021e03040b13080d0e0d060c210906050f070e28060c05010b030a0809011b0209130501050a061d 64
    0x390325005200a035a0203000c1d80c01110340715803d52651480c60143c0e104090a20b21070001200305e05481a500903044051010648803070b0403040c072100326144043e1242d02070600c200d110800b6200085020b0f6240d10f4142d0405071071400c02c038002c03e001d050050700c664010000042100e900265aa01007450f05a0000121103904295840c5200b01d034000041c170000800c4603603212200608e1340c42219039002c19141110300d860b50031181c0b00080c803082944404070b45401d40c0400d44950105c10740045034103003268462160310402c0c0d00700740030900c80503105032a84c0c003c20410046008568009450540b0403447e4140316801074485486101c0d003a015100f0f003e03201402418055400e0018032400341180780391605d03050001c1448104020540300c540c24100c0d4413460b4200010403445603038000520600300300302039004503284299490751448004655200c44056aa0140280d0040f11001d1000420b01c2907458110b0135980300800d400c4100d46001c8080000704120340d03c1112240d43c08401440301d80e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 668842535 1250 668841285 668841293
    0x100f03080a09080d031a0603010608180106050613050f180c09040225031704050c0f2206060e040b03060f0c07140a020108010801022b0b270601050a1b 66
    0x182d01640880c4441c42140007510f03005800d0b40c031a0003030340503807084e900110f034210044c8110781c8004e20442001500201c0099010351042d03c180c2c03588040d0000204000d560341002038103e820200720414000301041007000719140030808128440300c1621001065038031400340040d00100280303034003c441c100003141001940e407981240c0c0c0c4914400fa00e120303e00254100e00722080c5e4085000c4002c22000e402550301f8000e1055954030403640500140303c5007010200f441540000e008072a6000160742142034a0702407e1003011744d084203c04c0c400102a46895801002c3c2c96402e291035019500e03000200d0160b44001c101c85920600004800d2107a44400203451f1051140c008042c1c24881802043e040141011511801081c000d0f84e4a8243d0303602d0b440d03014201d1003658002c480550022803036940305120705054800010507404000340c2400000d020074801404920300080d491039481030b885a450700c0c4402d0a420500030f1900c141403d4030302002034074941c114002038a007041c2100c8803a00304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 668843785 1250 668842535 668842547
    0x3080702070e090607170405060a0908040e0a0e07051e0f010c0807080703081e041b08011a030106090b031908070f08030f0f071709010e061e100f03080a 67
    0x10403901d160700b1003d103401d20700d160b180c0d0004d0b142000040c400407042589490428429030003160848080c03c902d840d941581d41c02043c85060840d220350701408001407403980556510705c9101c072950082003140300c11541c24240b64881d0802ea2081c1d032440c00b14020641846900d1000c08400d8610024081c00302005030f5002150030350050444200040036400c000c409400343c203a41d446502c035001d2075203404031004400442004400307209030f85440000d01045841d041c003012021071104400c03005441c1c0b100319003035903840005200c080f0121407018100c4d060074403500c001004402802c001c1c00800d80002038440e4a030180e02200c8004107203e05042c09001d1044480303490b0f0020480d80c2503880d0b4584402c8a42084850007048176181d0001580000c280c0c011070b101c0c001c01e5803003054800d000201015505070280240029643e11194140c030694100b00f1580209007096400e468100740035102c43d1264002000701e41c0c2030710f0441c810060280b000303c640050380d44c08104c3c2a16890341043c100c4071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 668845035 1250 668843785 668843789
    0x6040b070b06040b0316030b070302190302071121060606030c04060f030e07060305070305130512220f08060c0a0206010b090303070c03140c04060315021b0709060e060405090a0308070207 82
    0xc9406511001034248206c581c0b46803c40b4410010341002d56560714060701207000d12007a070005c4408030006440b02a01c01c2d4010441c0d43c1c4241c20125404080c00c021540c11040b0b4000a68503900c0e9000895081e10100140d030f911a9045034003d15600d450144294035010700c0c402c1d641444641d84600208134001d4200c6001c1040440032a5584c03641c0c7d420040140c802910b078400841d10341030101c0d2603e000310111b00c0395540c000c070003854020100343c01c040032588002480c0c0da141c28581c1d075040d010040030a622009285c010800c8080c00e0420586e1420030b40003030541c1c2c600e84000c2103443c44858010824504403100040000d4540040c0c00100b402c1d446100ca00800c440c44008000c010041095040211089004101c401c418008410300c0103e840d1800702401300c0004401c60285540d4940007010311102c0d00800d10000c04030480340d51314003441900031508180d02c88206100ca1001540030b42d074850011202486241048a01d1035200c0f03025100c042c0801402c58001141c0900802207500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 668846285 1250 668845035 668845039
    0x16020a0905070305061005070c05190302041803020f060403021203130519030207060e0f09041b031110210e010204050a06030905070518150301320606040b070b06040b 73
    0xc40342c544602e00078020030084451a02c180341074201e110115100d4419100321940c40384820b600e0741d0402040100b5403c1000010050074103121021006032694011b60300381c50b100c1d500c410032054032403601900707100e2104a00035131071f8030120801002c03039400101a0141c02c02c2880c101d540c0c0c1c40780020846112005100580700c0c0c0f007060881903504141740c0c01c10141c603000303500343c07a00f05071205000ca81e10542c80e00c1e40d950040221140b0801894000ca0058110744181c01d0342c1101c1c0142990065040950340c015140e820100d0110409810100200c9a81c5071940c94061041201d0b40c0303031403003010601e031034810000d9611589282e28070b0f03095045801400e0005c0c400c422240d0b894130300401400f26203400b25031038001c10b200001d081c140105015868040704101403065035840320100021600c0131152075040d9200c0041c50314001c00c41118420501c03405455141d401c0c5131a002c400c48001c0500303450b002d030808000c10051417000070291018180d000c01c5244154681000050207041c0c04180c00c1d03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 668847535 1250 668846285 668846291
    0x311010311040e1603020c0706031a0d0305041e0e011202280501020f0d0c080c071d0f0f0402101b0b1e0c0306060d020f12090c042016020a09 62
    0x45554401c032802640b041d203007480c4c0e00e003c0c08040c071422000d84c0120b044141090344901c2d801d2007124001c0e000111005096000301812000400c0001c40b003001c448001d4020a10010f402d01c460034040603501c40000301c0d4500c544200745401840f0740280300502c101c25809034065940002c40d55401c000181c4c088806030702141803491420072007002c8509108113809440740e03510141c3c90b0f12000c510301170b03405c0d0152940c2c0b040304003603168100181d0002e40891042d024451010030410944c1c07824100603624042c2c0e041c55458224070100c00700c200505101c21f81e60f1003400300300040e500c15810b06c003145c2052804900d030a01d90b107000d1000100c6144002c04d896074860400c210102a0580900d2005c0382000c0881651174150400540b0311040c0e40c9150000c904210842e5070581c0c50b0000d2418401d0406c11625140340c40c006000c0000c02600c22705400d030481c440307101c1c2600e814000e440012611101e140310180785e407100401d50307108504c1307101d4845402c6030050066695a02861000b008189414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 668848785 1250 668847535 668847539
    0x60403020c030f0c0d0b07050d0f0902040c030509120921102403080a0e03190c050102030f072909060601080c1611121009200a031101031104 62
    0x203501c40d0407001c100c600a2003000b8220100c03800c001341c0914000400760120b82e0101c1d650b21072182600c801050340007402810821006243c00c180320700021000180c0300010304492610402041d2403825038204105414101440002c8602081401e400c0c036420305482d542d9031030000031a40550f0201803a519986a880140305a0140400c00c1242088908410881980600c0920b010030112150500607030640c56014000640c440c4000d0800480f1410810b121104140010340b5221030b100d1b032007a400c606201c0d81d80402401602c05401f4003401d0014504000c4000764401c10750089103005070101400d24031400c1070311100c1d02c2400e000d0740f40e0740c8607584528003260b800b580e500090320300b80c1c001108240012030824034001a92000100e03807900c00c04040d0251202c0c200381c426085070070746c0003080c040306804654080246002d4100e1802002c5814a01d038104845154408080040203003240340591129a0ba2099480c0a07030b0f500c417842c2400c50800000480042600c100c024441110001d00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 668850035 1250 668848785 668848787
    0x307050d0b01120c02101404030503160c0c150212040605090d061413110a0501140304111c1a1611030f1c0513030912150f061e06020604150b03060403 66
    0x16003a1116240c0714140a29152400480400c7c5030498000c3c00240050022448160440d000704601035124900070090440300d46421049400a83c00b0490b036002c82d620054140d901405410100300043d20090b0403d85040b9024186101e600089031140d10400c0c2c90000b000a598851007916007214030900d030600e4a015514003d284000e4181c8102c48000f01d04c100300e14101242d00107550741a92100fa001c075039891003c0c0150800340c4215100710300017070000b0300c503140d913a92030312003142e419140c070080b45413030800c2c0c6010709401000340c4030115040e003048980003807629207805200c00c9251994045030b051070254154012480721519000001070440100a901038041c0e56515410074100080c2d01d41ca40041c0c024051094001c0101c2c80c40e001c2081207d255629150005029008d40c104e207102a45c0104d0445020380c42401c000c0340d5a44081c400c2c41c102084800e800c5e219001031042c180d06004d0041d5071050028070042244d1800d0f081341885c1951a0420f03c040c560140441b0110305007890 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 668851285 1250 668850035 668850043
    0x1f1407051509010605150f07081b011a04060608010e01050607260901080f040309210209040f030201060605070c0b2a070513090c0504090204020c151009020307050d0b01120c02 77
    0x81000e00c00c000d8624000601c070301d240c00b11040054244041c5203040300964900043d50001040381d040741c00d0f0200d040c0ac840742d082c082d544034003a4010203503c0d540d28950411007280c0701d542100342045042401440010149001e19055440032a811502d451052410003a10351020340d103c187d02c01c0c0015001c04920600000d03042d0718409895035046956008101040302100301d401900144a00c45c003000440c401c00000c052340d04985030501035013011070300450000740782520100c2d03821f08010503500900d40d080c802c410140c5110320b012450403480c0d88800201c0c408a0240e4111340b50006145ca000c90842c41d0310300c40b481144009511942c092400b0f90f41c0320003191003075501503101e1040742601e912440c4a40020b036507210310f20b505003c0c102002e00001308080c4030201c1c1c2183d4200100c43d440d02d02004031000301d0b0b0b41159044c4080c40d02000982141c1040c0e030183c14854010700c140942643c0140076541c0600800d400040d460254100407154030b90181e005800841c500b40c100030f86594040303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 668852535 1250 668851285 668851289
    0xb04091a1c060516051602030129030d03020304080703110c09040602070b010602120f0c0114010f031428030e0402030109020c0606030d090501080a0b0a090b1f14070515090106 77
    0x20302c080000d59241141e413124a0020140340b000034404100302a10b09528900c558060f0b0300240000440c030f5000b07400d10003121030109190b1540452081d142070585410410443c035a406840c055085052642c1c410400e030081032002814031117014031780014007004100d1a0b038826030003405081d0381d003004e080c5a0700031342c8102c0040da4100601000410814000180101ca0124884400d481c0c2000000d880c1c44d55007003900d5040d0a1354031058410114200840c240d400b900d070250308448418a1840c2040d100e2507525440000e07900883c1c40b40039090914200040300b4a039400748400304030200e20302114500b003441c20782d035407183c03010001103405151903010702865824401180c100303484180415941f021107540550000d0842c550601c0030354400c0c02403070780043d00302c1d074007180603649000052606070312900030601c1c01d80d44441d00da14a14241d820300400884003480102d41442c0410010408900c00c080b4100300b0307030002060780400008100044126410250310380213410241d202c1c0d4040c0c540c0e8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 668853785 1250 668852535 668852543
    0x20060112051009032c090c1210030209190b0901300803060607060b10050306120c0303030c1c020a030b0f011d09070c02091609054218040e070b04091a1c 67
    0x44c0c0c00205040e04d09600001600d4004cc803028165840340800c0410100014a000c060b07500c841d140800c1d030b1107903014180070301544d403203000322040401c41c0002c031107922600c0d00c06102480c80c0b0006c007240c04a411603801040561307000e079468035541002000307885420700845e08400c4045403403540c03581c46801786010f000100c0e05c2450b10200d4042c455a210008480540d02d50802c101280f0300304001001000100c4000f50960000c54072001c084007260400d0301c4c1c0c60007194271591100c546250030300c5991680d135424240403040402c1d22200c050140030101e0306c40c1c0151142804550b105008041d004a040d50081c11907400340341c149070245c03005131283c200c1004107242040224407441c0440600d1002800c0259407804d00001030201000d001c000005032104004460680202d850218024040031303040240c0d04e40e40481c1e850a010849070041d0a81080ba00550801e100b00711481089500b12191a00041141248038040c0005001c07000002a440003143c88070988000c0e0440c0f000002e9402 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 668855035 1250 668853785 668853817
    0xb0a0c020910060e090402010c080406030f0510060f0c082b060905040807031d090a05090f012d0f0501030c080c06090f0120060112051009032c090c 65
    0x941112009400c00c6003d00d0020455604c041c0c00345003480d075103055009005141c4010745c01c0031074440c080103900c42e4011200281d1654542d180c0403156002e20754000c240503004d04031862400100500300c5d02a05403210400c403584611400380b01c2648140c45150842c0e0b0128006c0644404d440240c1d05022080203900700d04001c1c0009038850980304241c46140c0001c90145000016038040f1000383d9000f0b01043c04a000310000740f1191103801c03c091140790800c50010742402d2a240e5a440c1511403403c03809580e041c5403280740381d080504400303910032009440a2626182468180f0003411070701d62100095440e0400000900002d03600e44401c0301d001200762207140c0070f40024031400d44101c0390502d41100300307104103843c2365200e8a44072256544a42036812800c0a1091240c00c00c2c00aa000144034100f4010440038094140540081040c1070780c010865910103076405005a0b41004013003011110700251440c0c0c4c4000f0aa43d07800c001002002c0d13540038580745201c5e10081d00071129070312031480 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 668856285 1250 668855035 668855041
    0x102a030801080d081603020f0f071a01030302100f0207020d050106060807030b0619020f072402062715090717191212050f1608131104060b0a0c0209 65
    0x14022441c0c0e154020f444da01c25156036a403401c00105140c00250090402d41d081041c503540b101e0040140c82c840c000a40015a6807400341805850f030002540c22800c40069240104001303900081e070030400618400d40441c1036409813071620024081d480c0c001c0e40200e8900c00001c20440c0650080c415100306031900510303502c0d00d0104808840c48003003251f030031003401c104265240280351070b005144405132040b52452071b000c2c5400c030700b4101e1030343c8030042410b14170301c0251005080000c8401d8221076032000b0035a628051000e900b50504603010002c00100d1060062200380b002c4c0b00c5244800041c2c8035001003030070021505980c0c2c01c074900c103400c5001d1884034107015100f00030903e03161304060005060070303c0b03940b42c850804401000124405205a0030144030100305a4010f1a100da10b04025030030540c030b400051101d84481e02100b580c01c0295000801103413406101207124503030741201c20402e0135005280850002c01850700800740c803140115840c0f02c640c1d801103544040620980d14001651 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 668857535 1250 668856285 668856299
    0x10e01110a0503031e101a1c0501030c060e090f0c040e04030f030606030c0503060906010315180c05030603060112030521070905030319030908041d0411010f0806102a030801 76
    0x4150341c140c6e40e40078503d00400c140102926a403600c21802c000c102d01c0d2600191603501502418090300301001d8450b4010420b00400c1ea1488000300000d08040d608100002e00007002507030002c0909134000b00a0011402591003601503034042e00510900d003403e400e00c0d0401030403d0103e000b5070700c0000d0429801195051290241c1040e48401d40c1f90350341903489072000c000d81848010007182c1090b58840a011104005920280041c02e0303865040c00c004004c0480349050741c007a03151040034004c041083c00410b031400a009070450708c83d080010047e440c02e19080700c59208a203a6404004540c02154030240c0100c3c90081c060601a01d03030500c440d94a8062545a015031072180180f40e910701580c211286c001d401c90981144101142d514094482180658070b540384441405c1350ba03a0442003008004011504d50101d10b002d080c04140d400b6480c10040110b400149540e005d00d800710201e010450190004021030803040380c4106c0059621800004480540c441c141c0006010100008480e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 668858785 1250 668857535 668857591
    0x50d0e0a0f060f0b270612071703090a0311190b030612190804050a0801090f060903110604111503060607020d0c09050a0f0509010209010e010e01110a050303 69
    0x1281c0d01c822202215606901c81c44028000c0c44078488150391210801405540e9003004091104900c40c80d1003403801e070080841080741401800640a542d03044004c03c88007000240800448880302d10014000c4c00204405e41540075a801450704008450008010005e0810f09404003210561f00502c00b80c0e151300c00c2e0303590500e0600c2403684280c4c08001040395400c05002451002900c2c00c01c8031f071101e45035665071040c0440f00f80c058401d2a80801c05000510f0643e958500030071401c4002d0010441360740f522a000c03400e0250043c0302070340d10381038a010180500aa100300c2e08041c0701b07039481031034281045440c20a1701c400e0503219030b00241011103248000e4040e240a00c102170005801c082c19642803200071820301a06940801c0c41c8000010825828081c541c032504001c10003160382503042080d0410303070b1005000c4160a0740107000c0c1c015142d80c0202e0780800e2100c246030001c58840c444006030340c2d241e80c0c0a5100d105000d0034100100780a00000198000d0080801020348180313504502101e13 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 668860035 1250 668858785 668858803
    0xc04120c0e070f0f080c0405030f060a0b03121c0914210c0601050f010309080c030403021801050904061a121506040c0504060804050319020a0203012715020405040903050d0e 76
    0x1ca901113070b000c0642889004459801b8201c0c00034645030075142c0000a00e0541101301801c0154850400c020b0464501c3c050600c840c90160300410940c6130105090b001402085050180900000900030300442076030888030659400c0f10140c100c4201c900c08240c2c40b800c0d900c81c0d00030f1404209545c030440b004000d00301c980110030395010348402d034217100400200007008080c0c03604258071040c00d000841c622200400317240c04030100a40c0d13518514814842080f0324901000304400010004202039254481d6a13540940d010400041c5115408810601708181801e11038006c0052030440790784807000030b06038000c601036036010034065640d502000196010704030034000060003444204107241c042c5810980251044090300c2c144403402c00205610301030302000d900180c0c843c2c1e102c1e80a5040030b1082e10585200c612006600d200f20750344a0709054a920700080c10f0f200401d028500100361035040d900036140003001481070342120b0078014078a400c1550406412850060140611320000a103100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 668861285 1250 668860035 668860037
    0xf040b0a020618030a05160503130807050d1101080601140309010204050406140312031302180115180b0c070803180a060801051305150904050715020105010f0e0c04120c0e070f 77
    0x103c2c1003c00517080b41d20390086100e0f00a10746010f41030b031000500501c050143c6c00220740403160341c0d03850064154904400b80d4004c902031301154021387d010a21103c05840307018001e080404e80c0341c5400300101c92285e410111003018000c08424058002d2064004204440003143c0a2003c10f0311031081c100080401409203074940d008400302082d002d90040a19800081e405010001901ca0780200f00d80300e412650309100002c9400040c4003180c04100c007141040700a181109080d51040300170405400b290007040d00c061800304603103041040c10014013010380480e006984d00d400c203d14031600310390402c00040e403189521344400701c2c000784107482a074100d500003082801d801010078045402403001605000320a608400f250219440b411049401144100300400c40c00d03141ca4181c0034846000d00d01181164109401001450030003020101a5420001842da00d603c07400c2c80704800e48215400b103200010800c040301c0900000256503412506489500c00c045e5881030812140c4140c070383c1da048 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 668862535 1250 668861285 668861287
    0x8010f050f13051f06080a0e0102030907062001140601030c0c0f0b0a0902102d05030412050412060b01020727110408010e03091203070309060806060f040b0a02061803 73
    0x400c44000380d8110399080000c904c407620744c29000c0d200c1c1c40071500c00c0390040000b00307020005100341481e0074440c410740c018990000f1801c60030172480c0d00303850350014401e0034100724503400040070804800c2c648100c4141e0390002007085500d1001003000e003c80440d036990101f4075004040182a0007151010300a681c0a110008024120b81c0c94007070b4a04040c281c0300344c2aa80f0380c441c00058441d40080d01d61003940f03465415212020390b507070f08403806105544107440500aa0f03214092a04007055a030403c0c1e000c080c80300e10440108045583e40035940c0501c8c40c08600b4207244c02448008d52160b00040f00070b074281e03502c0c1d50300e520009200c603d401845040e15012404103441040c0c4540c8034450b201c4504d2030552806580c4e4124600f5623016080c501c40d650000a40003401d07241c00030101c03c2c0d0000010145090400b6030710060b040c0310440c810502840040c03400149103039922002c440b0002102c1c12040c1e200c94444e554103e9a410210700f01c0094850714000c40c5102c080c003002082d0002400c8021 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 668863785 1250 668862535 668862559
    0x62607061b0f031805030c030c0405060609030a2102030910030f1e0e01150302182505031911191407051c0e010909091406010608010f050f 61
    0x121421104415110500c081c04424540050100d855122546000750b07500b001c002e010600d50420011140e000c140300e80d000400d041b000740c401140350380c1030140403140001d140c1c0c2d507500401c4480c4280b085140e418054420171008210890240031101e0f5150b41e00a0541c04040d4416a42d07403003180310f05680f00228084038202d440c843d8014080e083c1030003802142e200100160b03042400114404014840d89441207111700c0d00c82440740c0e80301003100c0381246100301e14507000305421001006640113100e107030704002201103081000056241c054008854a0130180c0a0f0003405034100340e031035001004400b406e40d41001c00707a01816200c41017203d8024902262244200703003103019025500240145c161041d403c200d0300c40d01400c00540103001520821418105020340090600452418011346010380d04071640d00c140c03400241c0781000000100c8043c1c50800002c030040c0700c8516095442804004200a5405003c003812108141c000100e041c1e01d5104005840000d00059a0000031000354 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 668865035 1250 668863785 668863787
    0x20f10020c0c13021216031a090c031b040b030f070c0b07120605130603060c080408090f0d0206030703060911074101090203070906141509040903020106260706 70
    0xc4800a070f04610014a000c50100c3c12111450b0111255014100440d00f40014160540038003840c04c220501048040f0a01c5800544c0c5214060100201886e001c030000b80d1900c1844462044c01740c803040310f55140c9030b50b940754500ca0f91045468000040407070700424101401450211032144d0702903074403241a5200c10b41121400072048800c00c00944504c80064262203503918610007901021010a0304d600f14180391042e203016003242d00801c0000c3c410480130500311401c0e039400e4001118864200081c540c0040e000b0007094602940c400000424801031a8055110782d084030b0502c0e500f03100e20441102c40b02c2d114081d201000d0704010061100301d0102e0001c00b01403c3c50303540000d102c0140d00c101001001c1c48482002c48030700c683c4d5149412010342c642040301100810b13808100b40070440c280741402d1000301007012241d008212001e4204542d90181041d100c1e40c1034064010001c2d11000d090084c06441c0620410f050b19492802c071402c0044010080304041c0708000007808090702e4044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 668866285 1250 668865035 668865049
    0x9060b0307080a0e01320702060603060112020a0302060a11070807210507080604080424300f0c1b0803010e1906091d070303020c010c08090405010303020f10020c0c 72
    0x4c5496055690f2151803205140c00e144e240c00030038601c89a90148010210300448841011f81307610f0075903010504104090398000b401605640c0c00002252004410344046010136030b1941000f58070443c041034800740b8680c08030b0b07004040b59003041121042603803039a40c1d94607008180601d00d901400b5004060b4102c09a54000441e144a001107940051f5a9425a0704250081d14102c07520140010b08000e5801c00704c50361a040c40e100740d070280d06020352400c040c00c0c08400d14902c9104c1c5003e55050315101400008000701c0410000c1c00f032013041052034a00780188807e2054002088240002c40c02c9500c402d00c1402e10a680080e0f86840c690820340070100051000340a5002800001d04507644500e06000f540018840c1c154003007801a401d54554589400322159828a40c1c012501000400c0c1d002414000c22a420b0924800e04d00b85420a041c5c0742c031802c210030360020305000c000820180e00050f100007000a20080d1b849440e906211081030788210500403586901460400002c1c2c03601e00c1d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 668867535 1250 668866285 668866301
    0x1060b0c1606051e040503030f091201050f060405041112070614090f040e10090506060f01020c011d0d05030c15010b27040902130e070b1c090201020309030a0c09060b0307080a 77
    0x4e1401ca042c02e40c0c0d0b4000034030716401a032038034001e0807021a40d60401d0138030402408130251120020300162410848004100314000e000a00c52900c0d240803d0601c560304a0409500f0000303041301d01c40e1510020390356030f80d503414072500c000580c9410450b4181000541600c803c0301000b0700d202252910b001c1004043d081588802c070041c0100540c07845207050a2140126041c4100c000c1e1040386400030401803494102c42d150303419904600341d05402caa9021012520140d0120740d03914800d800c0740085108003100740c2c00103215100001c1c000107501c100040c500d05030139549100c076006a0700c5290b40b21036401144464800b0541c80c0064204032080081021150180504009440c0b174068002070b81c070700b09050a00c9251503a5050b42e100340c20302400031002074007003044001d00e030520b2008842d08000c2d45010301c4070080d41c0c40c0441c000b16842442182c0c00c01c40300a04483d50002036060003000520780380315006c0894030300b820000d0a542400e00348c92080030952181400c940e1040084000343c8000303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 668868785 1250 668867535 668867587
    0x3090312020118080f041e0509070306080c0405250305010905090109050d210911010806151b0708070609091b051213020901080c090f010311011b0501060b0c160605 72
    0x502c070115041f80200c803c070025a0000c0b504401051528060100d0150058001001c00d8101074051203451000103c01d4164a0281c40000355a500c00c4206880c2000c1c0d200320b080c075407040103034200c03540b42e15800a0b8181d8810f01e0081146882e50341070b150884144040040050300041800001c042c010084925407500b01c02600c0703440c82e0300704001401c031042072104440381c864485040000f946d101c2c1c03001f0341c0000c3c10b44d17482c070148100c4003880c0300602407030011080220400781449030092050086030300402031081140c40d00d0751902c10281c0050410b01898001500d4016030307440d011100700c0c1084652180da182c09280550265031230540364001810720300308008400600e00140c40306500b00d4001c186102c00b070110360a149003042640701e4003410003800706c2500401031012588200050155040c02d0804902001c00b90800e0342c40540f0052010700700b540780ca6000035583c420600140704682c2868242e07056403040c501c0400d203d42c5540101400035400340b05e6241c6069101c00c0c0b01e64198070b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 668870035 1250 668868785 668868787
    0x1a0901060f0e0a0605070b0a05062808190b090a0b0106050a0201021603080a0f060f050103052d011a07032001020f0c010b121c0e011b03090312020118080f 68
    0xc2d0b10200e4191a01c40d80079000242d0f0024442c4140203101281a0304071082d281c041c04107007070610000e046000f06078512002d044601c3c000401461840000e10000d0608209450000b0061140c00088040d1024190340d464002d5001510502011940d0494183c0c80008001c04c0d03400d000046401d80c1015a05000303641d801c2001d51400803100c541040c2652103955440b8282c900800c0071015550b41105801c2c84504010b400e000c0300301c40b194140145c0b00700703180005a69444600e415a02c0e6104a11308000958861807642c40000ca03000950603604140d4800070645a0000800c4881c45101006070002d0742d82080c000e44612481a03c0310483c0307445001500b0001001030100040e8001c138640540d60390340d208200d1490900c029010440d42c43d100c05401c0700840c000085000042c0c03054000c08200b810407000300070342c0c010706111022510f50103200510b00c01034a07000d04440d1003400103031900580c17030060220042c814040c40c40043e071440d49080000d031040d0344491254000918410040038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 668871285 1250 668870035 668870057
    0x80f0303160c080313031b020607021c0b090c0301180305220512060f070507050d050304061509050a0b1219020303040e0c04090b06160f05010608061305011a0901060f 73
    0x340c00c9010b14090005030400c0d40605c2543c1c076000e0025056060010b501d060505c500102698409003954000d64059481d181c3e0404d03002d0400030b9050461000500d40100f020134080310780d0300000c0302001502c0540003040062005100701c0380340c00c415440240058810042042e1085d402c140145000d07031004007001001c3d0701d070400107000c814a441201100d501180400a5130030201c1402a04030815051a40c580605034603180e486222100b41031050240c000045004c108180e031154400040340c00c404400c85440d82c44c1000545400d40b1050107a60520311344042d54074150303100c0c3d4072481d0800003c000c140c1611190828072400f00c02c0c01c9c2d9160206100004400c021130010a10950250940c03950f62800c01001000b29040500424080d07d414481d1200c29060207103400f001031b40100000c0b00a5610b0f1403d54054910b507080700b2414000e0f80c051001180355503061040c1305104100a010310100c01c12005800e040e144406948059072074010000300740180c60b507070f080280302e1401ca10030702 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 668872535 1250 668871285 668871293
    0x703120e010b0f0d030203070311032203110a0b3403440901020d0f06051e09040201030c1b030503100e0f010506160f0b10080f0303160c 60
    0x940340c204440450351107051010031880e09540e440c07200784044032031a00034501602d0095030ba0091080080c288060340901250001042003540c5069184010b0b140a50410f11880e880002040c40300b00c0d20340c2800b400c16162858502043d07010f4a2040c0c07910f5080c40100c1d00b11240c031040c0044035509003142e00c0c1c030902c07038000c00605000e080d41c042d4840f0391aa0b1540d581e40405000080108261080744200020350450304401c9014665a440041421512002c1003940244101e042c02c0130441d280c03040004c0025103e030448000c42c1e00481d0410300f09181c95012110f24240c0c0d007010343e4031840020000c0c00542c0617511076005c0f11400e15254955550a4103020042c40131100c00b0781c0440c002000b005141d1a01c1c920b0030019004414211102c1d0608203030b100001c107811f0150911801c40803400f140c40002c002d03155035070346801c00d07071025403280c0c54103000c0e00c042401d641801c2e030005000c0021032207000010f200504010b411005614654551302498001000d094080e030400c5070340f2103650b02107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 668873785 1250 668872535 668872541
    0x9010e040f0b0904080301050319051009020f091f3008091305091902030c010e04110f13050904050a061e050109152301050d020909011e1409040206070312 68
    0xd284117401c0103030b5950500003010714121b04407100740009070040e46101c000800110346910101d506c01c001003042016440000c0d40f912418030784603000b40c04030003007240200741c6400340928001d400794401355072500c0303a00072800c0780b1141806100c0801c0410760240d00c0072101c0c5000c06494024441541040c500714006520051034030804c402c2651610244500c08909118003d00b030701100e9a1241d0100480d40420348480031020300605201d880903d01a05443d140c10a016045603c0c3c1250383e1907072402103a208a8000c81e11410b520b00b0b1016001c509410300c400c0040c05650481d004044ca80d500c1d554400161000340284e8040a80c0c040600d006107905000c0d036400380c41c603040045800144038136002d0f03a00f62154042506015064002800c2644111705a02e20f1242031030001e0355a04ca00c80440702074032600103101d801504034400020041502c1058400d600180c0400d4070040e580c070518600c03d11000303078006070301036400b130082401844c0400080865601c2424075040080da465035074011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 668875035 1250 668873785 668873791
    0x252003040305031207080106030605094b1303021c050903070603021b0d081f05030a0302060601020601140906130b0409150c0c050a1218150f030209010e040f0b09 71
    0x1c07003000d0b4045c04080d9401024844c003511007450100250351620340000d4440101800048191981a91550b0303da0120034083e1001e03d1082c0d82000b041000301110340300b40c980c50030340c500784400800220342c004c0050703050b040025800d50b00624a004400f100342e5900103e40c1a00030501408010201207070310300744017903801411161030050b280c0c000f103c3d005010514581092900c3d0300704070980350f646600701c0300f2650000c40701000391403943d41e99510407607100300c685c21080e414840c100d4440201a130000780c080c03040800380d094819903641c82c2524aa03c0000410403984070f5168000076200f4240460001c240d1510640040749203085c1c0b002090031558070358003e540e00980c44a0380704400102e070040c0d4400e5a41031505200c2240700340c9486889884030000200b501101c20b501d01c0721039109007158401030502c107142d80c00c29540c44031641010f9019070819004203044003c00702d106400b81c400e0391205a010f07100e004041880300c081000900380120007012299403000b8004c0380740c07130301000d0b02c0c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 668876285 1250 668875035 668875057
    0xe04152c10050604150312030905011503050d050304030e10120518010e0706050301120224071e020102150910020a05070c05030106050a0b030a060e040b25200304030503 74
    0x451049901101c0503640010040c41c021410711200c5000380d0341c610050011030780c100000d520313070755411403040300644031902c0050304070340c245680340c50643d0044e0b2801c02145c3c4180c00300e0b85041c41c1060151210301003103e0140100325880c1d040041400c208500c0400d0340d20310b150141144000c05400ca0880318141c41c20902002149007101c1c0000c02403042d9801c08414000620032149801c1d802007640c48140a82300910f80c01d43c0c141d5046403214030f403090700840712130140921640ba0321458050703508020025503001c2042c0303030f11100c8407031603c03110780c0303065010707405030400788a141100c1a00c58070181c51001c0703c1c440d4901c001c910096a1024003203503809643d80039902c24a50411a003a07002940050307109926110007000503a0350283e4040031034082000894070ba5517140c0030800105240c0c2c1c4183d901c0c1381008100010011620784035489000c20b1003140f24180844010180b0310340d12000100d0108074032503149000e00d0440824205518400310481e4501916070790303600d064bd00b003001d41c50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 668877535 1250 668876285 668876293
    0xf062708010905060601020105010b160c0b0309030703090e130b1906080c0112020a020604200d030309120f0206130c0b071b1403033118060e04152c 65
    0x504001013840a9500f01409100030310865050450a4049219003a08002810030f145441c000b0403500d014001c000340102d00382d19840e854100c00e056101d0b4441c050440004400a5010800088171000540908006806140c80c00c01c035950f000d00001d8040d00361070700404031503000c515144507401854003030420b203c05040100c0a0703a0002d440705c04030540340c0440c180180800040107a000401c21307070180d00511480d241016001c010b00f0f40c00030750101641c2158500030801c0505405030000c02d0990720810700001c2d110600700301151080c400c00c11500050300508003281103e61114601c445982c001d80342c2101c40ca54420391030700c03507600001c41180c0c02142e80c0c0340b50540141e4949000001c200b5071070345100003031300c001c0002d032070f486224100503480048a0b9261040401441d103001c40b003007a6120341c500d4980300d5089101001c1c0e0350146500540c1081000b00c0c4040d0541c0c4e00d00c0c010380d0301c51804000c1d41d6042c0e0300c0301c001d805109110342406285100c00c810020074201c0318900c003086c3e04094 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 668878785 1250 668877535 668877551
    0x80903010c0e03010f061a070215040b0a0f0c02030a1b0f030b0604140403050723010f0e0c030d080c031b180103050f06030a060b150d0b0a06090f06270801 68
    0x490300392240710403541c0d1758501e0244108400b0a0b012400401200304801c0c0e02d070b40c0e10991000441c4070000d07001c80b0004400100d008070b00c0c202240d00410300005503840d203180001d50184200e0302ca5280800003174041d00a01040c0e4001150000a000058280440c2d09103440d2280c004044107440c44d44191441208a01440550b0904d8030610190480400a140e040e14141c2c40240443c07040400080a1442104e138401d03035502c0103000b00f2003010808000f4011a29001c80023009070985641c507003502c0c001c19107210941d160018900d00003140a40341c481403541e030721491460981008142500c4e2404940c1d603414101a420010041c0410004041800907000800103080ba04020500519020303440c05002e40356600003407003032a0a0348101d000c190240b084020414502103068007500540005c207034030040e41c032182c00850206500303503100d481c100c0da50b03d400c8994101512544040c42010001808114426000b60314464039184c14103110101c028201c241061182e80440c0c60f43c2d543c1d0140c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 668880035 1250 668878785 668878789
    0x109050109020a0e0103021e010c06060e0a111303060207020303090406120506070c0b0402040c0903050d02010606020c190b0c070506180f012c01020f010501170d0c03140304080903010c0e 82
    0x2e0f0001a02801c0605103c030740c103590105040351061070600c040d42010400342c62160703205a401e04607040d4012001e002007546c4521401e241c0b0019104a10500d080c847c405c3d62800c603090543d0300400510130384a45035441d68507200001e520001e8180d03018002000111020344a0303014071002040d00461342c00c0da0040c603050650410002814800c1041207111040e800300d0001ca0078a13800c0b58044034001019194584182c5031061964402060b50003034240d403c4401d0f8045d07010788100d070071507000ea4020002103010480c49070b41c100d40707180d54a040c4000610201c6041d402501c0d4010380c0e0070880b1030064440c2c0004e1015000aa078a1652024102c04d0700643d00f0241d80400c07511800b0b081c0701a034900902440c0c0c03c801c002400100341607007494440c0e0b030b4aa10030805110742c0d030103480080020b940c488500c1c4101d01a01001882c41b0300ca0100d007641d0080c40b6020004160303801d991070942c04850f0f01c1440d030b01d991010340196803102c1d00f800040348030b550038880c4400c0d1011070385500d4045094801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 668881285 1250 668880035 668880049
    0x10204081c0509010503150409120201020d0b0405010f091d01020f09011710150203070f0507090e030f0712090b0c06241807020321061c081605030c010905010902 71
    0x10440402400780f00c2e140342640c1210079070340c200b44400c42c103030100c0340b0700740100d030052100842c0503000c911240100e144454042d4020006a0309041c028801c24101d4420700090301c800303101c1c950410100c00800c1040c5031917035100141505604400900020488034007909a80140301880a0036100155010042da000201801c5405c4002443c95080c681150400a03411142c400d42c141c20a100101c08040b520074400c4a600e140d02a00640d5403000303505260382e0b0f0302614001c84051a14002a003c0343c018000107644410344845005460045255500c1c5a90000c550400050103610400450344504542c0179007000b1442c4001440540b801e5000c42119120b51b0f4070340da0074010055200c1d85a525801c008030b140007a140fa0300003642d162108100d1441c070030b0b2602009056110041020b0112004500c603006a000702c89600000184507040c01c101c90700032100400c50b000c00c025400707020b4070400f440294079004c0c02c152420001c1c1c00460340d0a4882c140d50071a1640d5584d5650011440c00c44 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 668882535 1250 668881285 668881333
    0x90807090e03031303110a0b0f0a0b030a12031e02030f0c1611151204050706031104051c1401061a091503180715031a010e060703090801020408 63
    0x40418415040007100c815100d10001d8820701c400c2501121400a05000b14110690203a0f21003c0380d106160500304041031841c02d41d10440300f100c6440c0807809204141c0924801401d0085c054203802c01255289907011002c6400a400d158440420054100c10340441402000f05e8100142c0d03a440c1c0100d00000303030320004091034140c40052001c2c08000350140141c0f126164044540080c01086500190f072105142d44015032044000640d41c031402030203403060f80254400c00c100c5017000c0c1c5a24055007503811031021a02602c1042c4000c001614207540b0051a03090b005060000301c11194541c2e4111300442e1840002c103a4540c1c00422070443c044c0c00101c00d1160180c14582003598100c0003a09040c400424040d4000700440415501030810840181c0800c60a00712525160740d01074450400800300c56400100c0c3ca01720a220950b0707941c07620480c103510140c0d98607491000440170008150040c1c4030079000c10640b0000840c03900000d2009201808002c0020400d004080c00701045420140c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 668883785 1250 668882535 668882549
    0x1c150f1401080d120f0c03060602060702060103110d0602090d032c090f071e020d0f1b030302031e011202030c03030c0606040b0f0409150e01060501021011040e07090807 74
    0x10004004220000c20100c00084203031034420f12400509803640003403e00c0f003100f4280c15242445040e891b98165101c48100c416513005d0f20615550001c051b600d461007444007914034480c0c2c1e00700c40c5c0d4a141240f103100351240f081e42c0060801c039040c030200354402c144a000310041013000c00809030001c0c1100ca2107140c0c09850500c00b16146962011a0100d20b001d00714000c00310f02080824401401401c0244102981e1200d080c050300607044020364510715021a180410344158840ca49076128202851074210f104a42c3d0900e0392665030118021340c0014070300c01c80c0070040604141d001c0e000c465604e000b04641544402c44140c1c0c0c1c0101803c1070424009031303109600c10005d42c84c00c10404216244d005000700c900244003c86a40841d411803000610035601501c0c02e07449004024003c5184d144102d06000100082a00705039201d088076268003550340907901c0407803100c030722a540303803c2489441c030515100da081950b80da10407224108103490240120f006100203120b1404100150030051a40c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 668884892 1107 668883785 668883821
    0xb120102040609051507020d170c0f010c050c0a0b10270e010b1309020a030c030f051002270a0b030106180909111c150f 53
    0x300340503140210b104110f0102d105e080c21403194004050781c0342d9451808000c6e808004800e0a01c0c541140d106194204c2c1245010520b4007809045001303000502080e075017030044a0039110710b514007604000003400070840c200c000094800c1400d41021103901c543d2246402d501d0240541c0d004200c1c4440001050440d110a5074200754103480b081301d00300411801d101109003612980c40c1043d50203159403080080c2482c4d55400190124070040c200f896403550703640d03018000c1400b94416520403105441c503100b0300c403043c81008540450404114607001803c111240481c03a511100d1381800006205030003292031b007520300e4002d44803c000132500c80d03950b511700402200469204800002241800145d81c8090b402141001caa000c1c0b01103840480c03003000c1c0f1028003400710040110091030301005010a022619200d00b1510072100440c200c0500380c607990135110004090102e4400c = true := by decide +kernel

theorem cover : BRFrame.Cov 668705035 668884892 := by
  have h0 := BRFrame.cov_init 668705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 668705035 ≤ n) (h2 : n < 668884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
