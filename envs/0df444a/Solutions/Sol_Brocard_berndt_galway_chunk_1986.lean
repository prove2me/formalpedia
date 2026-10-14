-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1986
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:23:31.188012+00:00
-- url     : https://prove2.me/submissions/d4e58e5b-f0c6-4192-a146-272b97bf01bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 357014388 ≤ n < 357194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 357015638 1250 357014388 357014401
    0x5180117010f0603060b030106320301180b0427020a03020a081f05130818040e011a09060306010306050c070c09140c070b04240504060203180a1a 64
    0x15040039001500e05080415941c582e408846103280e94058480032900b02100000c080e0045d400b10b0b4100d4801b652010108901c0b5984122074201e2240820281c04044c16a078100a0b4800c008600034400004002040214105080292040389010340c0c400c84c908620600280280020006501007112103a121190ba5200181c0380b80c5942d000650000c00400307000ca01e0790400900081d490401e840794054811a0003000800e465040f5408a011140710740200005551040604130601e00c0134501c080200440b00820100c0b2903514131544203a456007030342c8074203564040e403a201c0740101351130080c0c1c03515000c80840c0d520041844002c002c980d64100049041600109030f0304903540c0f11401e80c001c10342e92030200d405403003440e1404c0f040a100c100421480c0394650101c440c451b40c000054007980e0307619200c085442c0080607501c0b00040f81d829010380450345921030309100c0c0b0702c601401a120300340b6002000441c1071042143da0154002c44c4120081440c01e0240c1d2462a000b0b41c1850f425900d44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 357016888 1250 357015638 357015647
    0xc0809030f0102030c0702011701060c0f03120e070911090607020f0d0203030d020c1605030a11040605100302070b0f31020a090902030606031204170c151305030607051801 75
    0xc2905985548044117008514061304000c01456000340d881c165059611940d01c0300d915420301c640e8010032041c554030300c0040c000b1180c1c10b07429802824103a80b08100c909064065503508a60092503801000050002604a11503840f0704521410802d040074a0000030844a100e42840a88124442d40a900c8140c1c4d4880503c07a125901070107994640c02e0000611001c0e4000f0103100049002d103d01411540e151124107004842e00100280030403201ca0716015080c40e0480b101c1c503041621480045010348903c242d40c0280c03841c82d0380043c0c0d14403182c00c01500d41e41c4050310050032441700030203000304640d2a00501e03041e4000058401c94520301100c0c030309415003101c0e90003504480c0104001074000c6565000b115058001d400f0384600e0340c0c80e10101600c03260715900008d0b41d14000d201c24070905090700881c008001484089501c550444d00009260001203501035910010015006030a48030f003014000007440154024003003400c1c41c18000e001e80c01524100111070707981101c00b02660b03104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 357018138 1250 357016888 357016903
    0x902150a030c1b060f110f0c0705011403060105030601030605150d060f03050703020603090c0414090f0a230a0c14120c1c080d0905030406111b091306110a120c0c080903 74
    0x600e41b141e51400d032030781a60b040f600302c180f20080d10f009004002035503501030304ac06448060416802c901c3c6a81d100c0064450f40c00c050141410103030340e0301c000706898840300c11110007405600015a02c44003500c01c104180c0b14281c00044008408890030000200c00054400945e82d04440303003912a40d80700300c541d00c2d0101d40a0798641c414104005000c0340340c0c0003000240101668130376103d00d0480c5800e03813903455400000c01440c1050310501e0242100c601d00308414845001019103150510549460306a8840740d0401d0341808150956505103150124030980401c0c68070300a061415105400964030442c00700c0c100c83e0010281013804100042441106e00c4405402d0042007100c965090142d605c0c0c2003805070346d003c03920401100440340f00c001103043c0c200908041160382d100701a41800011000584a40e0300020950b40000c00500746018100841c84c20111050300e4042102c402404d2003401007030442c0162038454035202d45540500301107156600468030380d41d01c402003c0400e140096 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 357019388 1250 357018138 357018161
    0xc07061508010e210412031407061b0c020112021305180a060f0e0411040209060c161d0604020c0c060c0a150c020613081b01020403170307120f0902150a030c1b060f 72
    0x1000270301c1800c010141d032001d210400c1c1d410124411510640c0c0a651403021054040d01080140300e9450004d40c3c19001041c0440b0854040414160348801040c045000c409030028844101070401000d40080d00c40c0c000188144a10822014509142140001e20207000503091810320381c2d07207031200d440301e8040f41d0084501415071540d421010b0402500c810102d10804051408100d000851203410722060445c0c2084042508858440404103c0294032a0310b17605000d0054151000b015501d02000d010f46c1c02d4a50050410b801c200d250644807114000381c40a441031a01400c80c03c40c81e400070709140e1019076490b040f00c2c00c10040c100281c1c50300130920070b00c3c03003000380140341000d02c6c006402500480b40f2652140804400d900c510300488d0100b01e1385078001502d518041d856140e0340750488401d00502940000e040d14154000c11001096500f00c41642000040c0030380000ba0305200700200710443d0b1800050754904805003d819030300d6200c2c041d00c0c040c0c960300c180f101940aa84643c40301f06 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 357020638 1250 357019388 357019427
    0x10309081b120301060f02060f19050910060b040e0603030a0903061a03011e1a010203070b0c0c10062102030d0c0311010c1110050c030c07061508010e21041203 70
    0x1030303540c90300404e0480d0700203506c00140900d20114100d5080c11980c58012145404201110305460300c07040028000140801454490101c485001c024940300b5003002d414401146a41c079400e215080341d292070054502d5010345d00c10080c0d1810aa80001210241e0340e0240380400c400f0301d040b441100d01070300252200d40c154600388034241e80202a203901140146104407c0c054500d2600c03a4071103591928900c640980c20401001000516141c04541d204c580b00b0986820203803442900e500c0c2c03070300748104aa000380d0784003803c0c001c4c021a0b100110a07000b150100c41040c01d406e5005c00e8a4800d001d00003024000060040c02c2018040c13101840440040d00080059004c5050000c20300c0c055217821641d140540c170140c9404c0d00301401160710442250072024615110440392500d0796200030410b8030103a648080d09400c0d405004a14001020380100204210001c42c4d04241402000d540b125501c0c4000c007010801020220b058908442c01c43d0802081c3c01c03100c1c1025038045070036100c0c00c820f01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 357021888 1250 357020638 357020641
    0x7020a20061e0a0201060614041e030f0503031e150112020f0c1516050f160614100803090108010e040237170309130e2a010309081b1203 60
    0x1002c80002800280115600a000030382e9182e038291501050360b292018030310800c200501c0f03001c0c3c1301c201c1e0080c500450810309140729900d403a100044036411070121810781002003440000b2120030034500c03460342c902203251981c1c10000044a2859842c00c49035042c4807011980301148031041e41961221020220610341d01e40c201c43c140394440344200e031021200200800810341110301c4950a8540e0340c100c0d21100e00d00b6500d414504402d070442c62505410720f41e241c05000000fa254021810451300e5088413030082c2c1040c03088403039003a0071a044070855500030b0059115030382c8e00c002c03254116000b100c0c10b0103040c0c4503070000c10308418140701c0c901040a2707210075030020000c6049500c102d40d0604030101009540300e102c00211020f105a5616840e401440740c1c000c02d107000042e010110340600030008203003201c08912420183d091f004040c0c824155a1800c5070048200c102d000300300401d1070b0810030000984e40c0c040d00e6010b80c0200c5c072058031407202075040700c5408101c050b50090516041c0c2d9101d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 357023138 1250 357021888 357021937
    0x61d060405010c020c2805040f0b0108090c030304060305102103020d0e010e2106010f1e03030507030c1e1118010308091203090405011202010807020a2006 68
    0x15840169411681c641c0780c54008000c192010420030301d01100100b0741c001209900c0205c4207507014613a00e11200b0300f11104002920307039440c800e13527079600844c0744007040d800305003c009031221900404401700c40d00000c1d2a01c1c519a000720442e02502d01c00d040026494880010b105104102504400b40400030070391910f12000202e40a0503100d44607900300c4194a5080d4022150011001001808213a0143c000099481c0c030032500380c00d5a45074109182c2d02c00d0303a54656807600000381c0c4480110120482c041c0b001014241e4156103c01040b6440c56070f4610b1513030010681d10130444060108064aa4054104400d403602000d10915aa5105ca0014507609000b4207407046007440034405c03411040c020000510b5140320904a9402010712800c0c04180410300040d10140c4031441050700081145201c20b5a07030307104d01806001581100d603000d0002d84005041d44d50044c05540c2513500c0b405e00400021440e101e80d0344459a56914011112400070104071035010f5514080e112209900007002d6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 357024388 1250 357023138 357023143
    0xf0c02030306030d05090f010c030509040606080601090e0103170309070803030901020d06120209010306020a0504170601080d080c030403031107021314151807020c060d02070c0f0501050d09061d 85
    0x100b00443c02e03100d40c03030384000b4269500c0c42404507072600100748001981c840d600504040005501a0502034506070500c40058115080e68010002085050060000550b88100703200d010305126403000b01c0550554945000c20003e1805804001c2e4000000403180c90b0103106520040407940100c13501c0c0e0401949442c042e400c076111076922030740381980c0000c034101c41c01c0c201200d0a40141640d001070342541c5034800654040d107810824404204000500e5140d0a0b0441801210000140685506281c00b0750304118100580d0020028920140100d001e5200c0c126070b041549400c2c0040d00c0b002031400e104090103140f00c06903003e44502d148071000340194012210740352203031034180040e40d00c2d00d41c2c80781e8001101c400d00d900003c020031148080d09041302069041102c40c012660207a506000003440c6500040c82c030900542c012507650b00700440325540c00c01412622408d0780803542010300081c480c0c00354480146086440301d0b222170a0080a91111040004a003900c1e006002c0306018580e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 357025638 1250 357024388 357024391
    0x7030f0812011403061014040f111206030c0136090e06070f0207060f0315030506010303021b04050717190507090602061b03010e04061107121707021f0f0c020303 71
    0xa00038068000006c014244040c15401911010350f540c0300030031000801c1c040141014542044203d45e101a01000e2041c058042d00942404081c2c003129890020140350400c181a00c0c01b90600140034621070211030101c4440e551151500d0302c0ca40da285c0c00b02d0b0390100c1c1e008a130b44070140491614407403018034030002c2060740c41000e0503220001c844000050490780e80403584030b284005030005d11031a808501c203400040301460f800b0000560300f9229201e2500740103082c4c4c400c030b000d40d00c046128a601030640d00100c0c0c101030202c808000034902040f000d42125a0100c0d81148040d8190019288450702c4841680101c2000300403c174a18049a024041d010b442c069a0098824100040c5046850003c00104070000d1840740707040d41d10305012070b40007036000f8104a58058654900140101040d8050700b029800b803aa01c51030071409a0000d4950990b810a020490030b00f482007240054002030580e0404d80d2103002c070420b0b402608605401410040d0040c03400c0703814111070380c0d12143d0000145 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 357026888 1250 357025638 357025679
    0x3030903030e09010b180301020909100302010917070e180a0b060406090e07091d06040f0c080327030109051614030706170c0d09120f02010e07030f081201 68
    0x245110410402000202002445880119601040700d0602c0d032503000030904006d24040d0004d81003002010000f5803041084440003051114404100290343c0c0c0901d0b10001401c01000c800a01d101c03d295264a86a941c0100d40302059000302007403522030381e402201260380800c8140d80c07007a41189024440d05c00b007954610310460600c440460100341502c901c3c00d1000c51300740140521460b050040002d001e05440b0f100c0d015540c5500740d00c210300c06009941c41140300c0c0d0400000759030320340340c0724040c2c1c0010380003042542e00600160100c50b01e80b40380e2100301100c5951400c90b211104000038003400240200401600802c11000401041e00c24032006980d101c20300540704028250505d50f40704164824000080c0f550800a0303603070030610030306a030003681d010320365441d0080d840060f5003a1002000c08540c03003a4215511071010b503000880390f14210651000380400b90601101c00c1e40c0e04071a001c0940300842161080c0c080107800000c44441e182c1e4212100351035070f580c1c0140d075840c50804091 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 357028138 1250 357026888 357026897
    0xd05010513020102060c042423090406150806010c0503040f03080c010506120619060f080a1a0118020d0902030111030106030c02120316030e1002090103151401080903070204060303090303 82
    0x8a00311001e101c041d1026502070806141d036181200a000d0b10021281d1035032028060501344800500c2083c255105403270101200701951103220000b4032048500d03940c0501e601d031580c01e0108889641c0000020b030096000d18000c090310f02142405030a51150f039200619a03881c10034000108241c0c140a03180d0504580c00802599685905100e00000440c00310420344d0440c60000c0c000401c000e20b1041c2c44039800f0340c001442500c94007100c0344c0d0301e9550840b400039446281030b1402c00038402c8850080c0810316841110552408000350b400030700810f43e5880494003c00c80400d110101d500c8042400d40040090180c0909608001c51390360017802802c0001e8103007404014514000a0701200c4a41e100450903d15500c8074602070584402e5003c0804141e10751710103100804040050148000360351200594903c1000005011900c0d000d064880e42141c03528100320ba02c0d8031000704d0617a51000c0c2000c10507541e6030030300c25095201d2070200071b6100d850410040300b4164045c60b6081900d110340c84 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 357029388 1250 357028138 357028141
    0x30614060403030504030209040327030b250c15060308090307140f0f0d0f12020d140f0309070902032d1302040b06070c080105090106060c0c050904020d0501051302010206 75
    0x1884a03034819400080e0200310100000c10043c20411000ca40c000e0180c6020124910341e03030071041c0c02804104c01001030301c4141405009025a180c510380d0071000d00042d1814400c002d091080e41c00300740200360000d0024559004090000c01c00051001c904180c404100c190f80700c2c60100040d0708284680360180c4201400070030350107105200b04002a8006108028070710340101040203940707914640d10341101d410444000029580d1021840e014807804800c48143c070f107000000d18050500440c8020462840300d200d0303440d070541d02150f0110380d90320398281c0d5035924941c44602e44120b5a000e001903500c004104407550240c0403912009210960300071042103505080410042000e444041c000480d00c081c4000500c0c0c0f6034464254441e0140c00703c2d0400030719496642d5017004a5200300d21917510b4600b006040a003c0c450721014110908182005d05459213420f0030060311b030302655000c0c0740c010000c90155918140510101039129009101c01e14054603000c00480503204100d0161003841c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 357030638 1250 357029388 357029429
    0xd02030f03010302150d0507030f0b030c010c0b070201060e04030e132702010905060f040305060105150703210207030c02040c08090a030c110a080f151611011b0306 72
    0x2240c400c4034829400c01d0640e400c64081105e4550314600000340348004103e20345480e0302c07900079144901480d840c0000c001c40b07001821800c0d5002070349141d201c0c0e0400c1c0e2818100b60b07000341e1442280b035007002c102180e0740c2c0d40f40b0090380104029000710030300d40003000030041016807125041c140b80303500362920030110482e400558161040c62600840e280d4941b8000c42c04c1d4051022010074040c0140360001c029039564000c00e419901800c0140040d560008041c01807210401160b801000b050ba074448204a40d07a0070070f8440d00400700c0c01400c00040c03400040c4000c1060042e054040c000042c115514145454003030709180540382c04900860414600c6420540294207480c031030200350300a040980800d5a04403010a4200001c840c0c110950422070001d4484441c0d0001410410004050400b050741c0c1003451b0102600110180041e00402c00c40000e004146805500784181001c0f291640419103d030701400d40c40ea0140b40360718009181d0603070a035150b001101210485074281e00503a0009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 357031888 1250 357030638 357030643
    0x203070f0206310b12060f180c0711120604020603070306050a06080108010c030b01050a1404210519021e0f181515090d020a03332906041701020c0d02 66
    0x1251782503d0b01c200c00282c60b030400300003295500b8070080c03031240c0724540f29000010114040d00d40c501903010100c4d8400c100001c0041d00c007520502114240c22000650400c59501c0a0080000740210004400b0500b440d0190f0007070405004001c1907a80016110080108400424410204550300b0703c81400c00c00e50080c8213190714010107039030321890030403071000507510664000c4100c02180c0041000140d010f00c00007446880b1401c0b10158800c107a800e0a05c4c41c80c00548040c02010400100300d0744d401030360303000000c0005141c05110800e0700c5080300002024480d0b02e51a4581081542c02040005400304032270611869480030301035000480710040c04803507111040c4080504c201004007840b035180005e1601e000c0d0388000c01c4685201d44030303a03500003007c5c0050800030f00d0003100140f8038000c0f0204c038014500d41d88044010401e0020504601003c03020342150685101d241d002210000d4856000700c0340035054a034041c2035003c001c101c64174001d501c0f21a042603a4080d402c10b59000d144013 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 357033138 1250 357031888 357031897
    0x1802010801030210051315090503031303120c0609050601030b0c0c060415060b0f03091e0309040507030f021209070f0e0703050c091e0906040c0203070f0206310b 71
    0x1a500c00095a00b16401c1c0109911003000b001d0034010140303c94400d01034400043c1c4003505d40d90168101007149000003402c20002c03504004d03c2500103110380b041c40340e58480c108080b03a40110081d100001c90000603142041c1d940809403101d03052056003800d100c400500203040703034480d201c800610740e00c016118403e0b029502200040342c01100201d0003281c400c100d058010006882c000810655a1113141100c1c1d00000b02c0003130210012041101100303081c0400b00381d041c503140f40c40c810300c1844250280c503881606035481c030443d03588000c05d013060302c2035218001010701107104640d61741e25038225a03210481140c403610395101d0303004041200002940ea860444494080c49001621420025005808010803588880c1c0341441545059502c03040ca1402030382c100c2c00a01c240c1c0d5881c00900140810040c2498052424021018031081e4000125a038007504800000483c41083c400104588a42001d1819400500403c03e0301d000001d2201d5100159084108040301e03a5503540074442d004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 357034388 1250 357033138 357033143
    0x112150c120e0f0d2c060a110a1b050a080d08040b0408130e070e01031a010e04020c070605210105150f1c0f0c020715140c0105090a0618 60
    0x9407440000d2800c030140c205410101c40102580d40505400041a00c2d0414103403414000036529044e859020f0400d046411101c0241a40c0706102a100c0c80400d11521404d03121204100503024540e610302c8080c404806456840320362401e201409504000020a41d8000c0c83c1c0300305000c02d400141d100740000d584000d04250f445424440e91551a0746c2071140b402803065582c01410013907019140b4840360b410b0f01074480a14030b04181d04080c04010903240b0410440c0d030605252103407045450000740c034259480ca4092074005165526880070070b01078011001c0e8451107104074540819000c2d0013a01030901000c04810000030080c1c040c5400480400a01c10b1680051315055042041c884c201c00404044021100305c0f441c000c800c41110a07559060102240c3c0145d4400d030103ca41040c9019509e85182988000c0c0320340c1c1d007008010310440c04913103005030074041111000d18401e1103d40c00d48027801940f1000f0082d03803600c850710f40e458203000302c41201d855180140781c004142c00c2284800c1d1054 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 357035638 1250 357034388 357034397
    0x13031b0e0411040b0d080708031e06091920090102010c0c11091e0a1b020304030c090f09020604080a020114030702190c05190509010e0c030415140112150c 68
    0xb110500b4400200030301d5008540180d0110040c05c0411520b0004101080c030610981e96a4030303100b4124480305240e52690301545444506001080d80d0304050541c000c210070301c0003c05403200a02000040c074040000c65172820140800d0002004804041c004440084e0000d121080540008440000403260020007035840e50f20303039142078104080c4065001c4d459030402c0e040501503208803500b0000455001220b5a02c49040e034903160701403038101c2e0740a01a40021810f0604542d100321904c100c41c0202d051082d81d50000c003501d044503400c54586d00c3d4018100b1a6175584035400a51a04810302c41617006c0b45098507890768107549802202d210710382581c081c3c00d42c2c101d022403e054807400c2c880d060f41c40806221005c6166640c06c2c10380b004102a102081c03001614002c10300c006414140e1003030500440100401c50390440e21000c4a03401036021160407a400f62611180d0300402421901045240105001103820f682456000314494041c81120b0303901c1d411900180e06860000c80b1440004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 357036888 1250 357035638 357035663
    0x60702150601020a0602030f040309090b0f011b080a050a0306050a12021e03010614031002030f0403050f0f0406030f1a0307090e0a05060c07031101060302090c0a020313031b0e04 78
    0x3000100e511507088041481a01c40950154660a059030015144803551104160500c4100f51308410030100818569170705003c1c0b42c1186c0c0000c1c0c042e48003002c06c1410310034030348024a0144c00c01500498203540c0804071545032042075030024025005800c00780080b034540034004c5650b20f001840c450490741e4503c8a8001c6450a60a11200361506000c2100c030a098040e110302d00d603801e0007014081c20098030844d081444200c10540b40020302100103c2c014030400c1170004c6400c600c80f9590748150141092940d40540c8060b40009100d07a14010700c220201281c081110b5600d90071003500c803441c1403c01d0017100400d20310a4041c0b03000c001607035417651156804011544240c1c1111900101540584545040a84031a82081e0701140c0a41283c1000140e4504158001d241d00c081401c01100820541e404d540c00b094030144042c06c0e4007440e0001040068a1520800c211504c0300c074003c01032901d83d662440e054a02c2c005c0c2d200d1007104104c00d180302154402c100000315104680207103851544 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 357038138 1250 357036888 357036913
    0x50a0305090102030c01110a020d140d0b031002070506192c010e070f03061407090e0c04030218070206070e090408070302010207020a030318060905030c040e0c100201060305010b03060702 82
    0x2076100c040000d0640c04180081070860b603007842603584a01c008109656034a158000007410090f01c501168241b00d40c0b2403d00141c05a031400380c7e205a96080300c001442c0100c0c01c00039140031403240f0300602050000520f102004408610640140000e00c40b40302e401c401640042c0507143c1d107115910500d4100412844c00d100700d880311003a4801803200018686650000090400072282c2000458000015041042009504c00c0341c452090850952551b0700301400000d052403002d1203000d201615250206654060040844008682c02810b4800d24080203c402a881e4001ca5818000d8064400007901c524010740e08444003100040a40c020b40e6119070350603103640c2000005904665091020500507150b500103031024601a4a0300c1d89030707410b1600c825001c0d072482d4001000b0011241b008001c1501c0000703003e14810700c200e501103910152028190b05d00f42c10881e80700d80c000e0708581e1030300c201a0103520502c1542d001d10003c1c40b070341c00b00340285035840005854502c016841014400030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 357039388 1250 357038138 357038147
    0x80a0314151f0e01140f12010f0605040501080c2a06090f1c11100501082802220e01020d0b01020c0d081b0c090412080a06050f040c03020405090c1207020a050a03 71
    0x5151704001c03841e41401d4003d040c101c03007a04a6200c0740d401458440052252070078252840c40180f10030300c0c0c410303c0c1ca801c4c2070000b801c121024011000700301d030202d1105000119140310700030325a5510045000810442c0c1d410b96580029900060903004142100140f0343c800f00e121079001c40c907481035882c59003e080781140c000c082170486008500a403582510554030314060f043c002c000a10080400c0f01601003c543c4814840d054000f0545c050360303079000180c480c07c14510300302c0701c000c0f6155040e6134107a8922018040c81080d00c1d400d9403000850728201040d59005d001000401e0342260403084a95090080c0d0104415004d010b82d03400b4072a02d00e0b1700c040d002c0705030314a0b1080400e4824202080d0042a0001819541154000c414100c1c04c14196800821547d100c111403009101203441c0c18086040c04406095040c09161502c0c0c00c920310501070b804940c000c04001d0109440d030700e07003d81c0046443e00036082040030012058007042ca11407001070071007105034204020b00203520702c2e590241e8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 357040638 1250 357039388 357039407
    0xd200a053102040f0302100206150d020d02030d09090608030403020f040e0a0501090c0312030203070914220f0b0a0e06010518060c100f18080a0314151f0e01 69
    0x3200000e91048200260036180043c000511008040313011040c1944100700c10760070100c0f00001150300c00000c202941d0a4008241019801030b03a000c01c5d081080e0001c600052038030040650144030310503800d14169400081e0b4000c9a0024008012554451885913180c2c40b0368070000c0d502403030846070000c8600e000d40c00400041494000c0322540409596a5402d40303041c8002540e081c44506820401d20042c10a0180306018a00c1c08628500c0c0c00e90028140c0d010a00030608400c52000320321826440e2240158040d0a00d280e5003c02694113242c41c0300900084c141071443e40f818001d0300070140c10409e40c480243c40713a980344180d06564100046805070804855800f02c0c0a40b00c541a00d1602e60308002c0904c2550301001d08646079000c81110b040d10342c0a102d400119250a00b1003c0c01d5061140211805070702000581d5945280300045001c4c010044280013499811014409020101040d01544140c19136040141c0f142d07104101201b810b000362010040350780145070041d158070500461 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 357041888 1250 357040638 357040699
    0x1a01021f020405090c04050103051e150303130806041a040c090e12030f072c13020405030304081c050f0d020d1d0f0c030c0303041707050d200a05 64
    0x1800e00c3d80d01e00003e0b640303103c1600c40c80c4224500080a004a517818007030181d0100607496401140e01102c91842d07803500c001411094003e20460a104050f502801282c0b03101c019008500030040d00e441c4410307200c100c155012550f0310001e5809180c40b280030009541300fa80c01401103030341d4902c1c101070003001c0e000b180090038190082840d500c0c40104a440907600900c61002e03800c00720318208a010b441114035511980d1042c022803031311002d4011603059113424480a4801800600c0a200da0030003a0265400155242c040818045800d0b000040c030100c50520155840000340110f0300c054500e4030421040c20ba601004100144c008403a40d0018071801c1e045110000f00c1510982c811015031006e104107684541003940610751046081041da500d0704000c1307000e40110109200001e0746c0788100d110740c50706400982098110f020050100100420000c3c111400e0504649428001c0e91012000006254491403512078281401094002901c0780940024980b42c09060303243e4850040b01d040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 357043138 1250 357041888 357041891
    0x2205031b09130f11090622110909010b031e190207050a020409150f020c0c090405120316030612030e060f0f040902030114090c0301060305180d0f031a01021f 69
    0x200300c00102c3c9098800300c1980241c2d0300c462080690740400221000c0a401680300714002c08400c0c0007268101004146a62858400503c0c21481c1301600600d001c2e01c030b40250f010b9403100000036002901c80040d807045080b1158031140341404c005800e000d09055a0806580112070151040fa182980c02030803c58000d504a40e0322514a070700003015500ca4240c2280c55681030780c2108101c21003405485030000d48581c056085c080141d40355a503a1640107004c2c1e02c511420350101d000d000040c40221500c4000e103969680d83d107010311078844002155501500043e180c900d0010b01c00ba440d0000462881c0d0540d43c8018004c510800c100850304280402c140099040043c10300c803401c61002440100010303000940c032585010a0402c110400303d801d58040d00424007005071130340700d4208481c15207015080c0021580c036072022007034004003001c440c8a114424001003003042900070500c001011010756003803000d04210340004464200c124211400340c0d005a01c000118a2242520421591620070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 357044388 1250 357043138 357043171
    0x90b0f042f09250f020d030209030a0206031b0409020910080103050a0609140a03030b040501080c0112020d0617010e0105070f090303051b011d01050f061509040b062205031b09 77
    0x2651515950f40411000200384602c11260304980c0602c4000441e20b16030400b1801c0c200d1400c00311b500e402c0d1142c00240b04000010002d004400903159140e004010040d4040d01c440e128043c100082d03001314151032241051002282c207240c45002c1150580340d109025021006c1e05503144009410029002c44e040300c60001005240082000040788060084c0e40c00b0814400b040180f20442e00e06030040c0049801001140200307980044000d036400c62000401650781c0000a0800000c3c41c0541000002030314083c0c200d40c40720415009842c40850b020000c0059440e032080c00d581c141c00384207402c0e01107400700300b08102180c02580502030602c2ea405110142c40d6145c0040b9003166101d9801d5900203002d5500c403c01c054091080e1369021003100c0c1101d900f820808000740403441a840e2441310500b0003d2a084a909d9039000741912440107000140c58120051500c0c02c5407052807048502d14159100002d180e180c0020b82000e4001b001c80644c400340d00c00347c144000902c0c000d1882007111039222 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 357045638 1250 357044388 357044431
    0x6051906051b0d20010606050712020109051f151401030c02011509090c060905010207170307150209010e0105030609040f03020f0d12050a0e0d05030a090b0f042f09 72
    0x4007083c61000b8a50b2240342e01032041e10092004c01900e10240000e80c90150300b8815160028100c0321080d070800b8041001910300c90049014042c01c0c6001051800340120600340c01880405600104110321010302001442c007a1032141141725100303a40b84004000c041e0549540031b0380c40101c0c403900c01d02c000f00c0c62403040d58500b00d0024051b402044200d94035101202400b10001d0010003030000e514151040340e1030400000d507640028018200d444070b9504940d800e0030420412285c074250301440701c1f410303000c0400e4108004c1d0002111107000c902d0001540b1800d6110b002100d01c02c3c0c0005000d0300310b82e01c40343c64260490070030b5a4110154440c04031140a005010054000b0411183d51a03c081800401c0c0210130354601400040b180ca0405164080607000403c0b448058030aa2406a80f40d950b04040d00e006400b8451000d003411150304207100f08101240c0e1071034841c4d030041c0c8028400c5800f03030207601d00c036401c15030700c0c24000d0a003542d49108514158243c950001591000c5e070307010243c41c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 357046888 1250 357045638 357045643
    0x305090d080723070807091d0f07031101090b0d0c0c020612061504050108040b15101814031b03010902040f0911030f2e0c09060306051906051b 63
    0x15050307a0030022103d408002c1c03681e02c0e810040c141802c0300035104991424804551b144007a00880d0410b81d283c03c140c5072400c03950024408051030b4142100c80850140480e26140d4000b0301040c0d0341c0b010b125501d0b601d00c0d4060040704044a0150502920707040c0d00c0340c25030009160040340b42040103111002d01000d17a0301c001c06400903039829a00305e801c5080030020040c01c1846409801480c4030140310070040c076a000030b40d4950080c0c1001d0420081d6840710b40c0c2910050020f160641e0145004c1240303084c4aa02505403005d03800420141d41030262601c00308100d0b01d1041c6620359159005c09001d0407101c405131580500402d0160012501048603130000c1c0654060008680805030b8401c10b91051207808958a4521801903025041454080745615190300180c0e0790001d101c1d4000c40402d9011280f0032010300314100c00102000342c504c42e428010107802c40d920500340003030308000c808581450700166822031000e1001d40c45403203030719120045d40c29030000804907010005402c1150f0400a05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 357048138 1250 357046888 357046897
    0x10203060a1e050a180501090c0c0b090c063402030705010f090f031202150708013011091605120a02130308091504150e060c0f0a020f0108060108040305090d08 70
    0xc03c5544900c041c02c2d0410417080b40c905902450074242090840b92460740c0150b49030420517000904928070b80d0314a190f6500c1c0285080d100c640049000641c80e81c160900c10500c0e480c110340d800040c400c0f1550403560a41c0d0205600040d5054102c0035082040c0c4d03004000c2e000d007070880380c2409141190365810302155410a517000782e070400d2600100c01ca005a0505ca0521940c6214031500c406052044004020a805001d88202840000b0322034007505900455902d49442400c40c4440039103035446d00041d0154041492805080e20801051540d081c07684440540711496a0b8982003610010002207181c0025004015040d820001c01a10000300c4074890b0207180603000340d03640d81c45500d06000c0664403c1401a2000d0f5061009001500c3e0321b00f044d0302c543c0340301d2130003109400080001807032030304c80c442c08403840e88174020184607003c40100d1807120b923600031540034504e841000b0040d24904002c50b065800142b040001030000f81c05603001c1c04540c1c0024101c1000c01040b6560754441d5800b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 357049388 1250 357048138 357048149
    0xc050c041d061003031106041a0c0c01090c030309050604080d05030c04080a0c06120b0609043201030c170607120609110403020f12060103061a041b020f010203060a1e050a 75
    0x480103024014160006d16a04a1510340d030000e000c10320381500c4207006400d1010074698880760071001302d020f01105d402a99070032224400204032504030f51518911b043c02602c41203000c5000d001c0001460b15110040e501141c41103809031811030020b02c0102c0b4190300003054079190800c14031010442c1e2a0801c0030303124140c0703c0d0b41000f10707181c00c01d400540340c2000c807141e0080c50350510b96810240d0321154180c0d04d0800c0143c0c1c001c54405000031410248004d141c1018a801e00c10820701080004040701803812240201c640050280d150403000c2c0c565030b0780701d41c15400d0742d204c0f10214800b944502403010b021034203240001000c035218000c01054a032800d499641e5403101007020310a51400c5201048942012225036802c201c0b1300238003e4641c40144000b400480d942e87c1240c20f64070240081200100f4000c02c10406203940009081d240c40c1c10a03406001403056459400440c1345c14407c9078000c51004085a616a14280c103d20b54004220144c19100e00c60305c0d400901c0743c541280380000303000b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 357050638 1250 357049388 357049411
    0x2071a010603020c06061005090d05100e0a06051e0609100b0406030b1201090209011e08070e01150801060816050f0c0d0212070c030305030402030c0a03060b030c010c050c041d06 78
    0x40c0013800d62440c4c20406015903108400d1050f40503081904103080b911401000e0f6582c040d0b410450a10604000004861058050400003102c1140741c02040072444980325060402c00e50711000c503d64610141c0c1004000b04145800100306035152030209142c0c882c070b02d9408680b46588079043c0842d281c01a5028502103521404000413f282c119040c0c4003650118000300705550898001810580041c1725003036044813914840f261441c6104038880c007404400702110341d45036462518810b40402445000c419070109800c2880c0300748201c0c41c1d41c0c100c800b1540ca822a64940150f0304140c4580b2948420070304c9420086072060350000005001000c2c0b022019150380284c98038040d05100316804154050403040040c0400910314a8030350080e41d40514003207403a90344910202e80b0303201d0700e018010342c880d540785400400c21146411040281b103054003030b51801c40c0d4040040d96000c100320801012900f09400101d502e0900c2d0b802405d00a01d000c2d64104100c8403c01800c0c101002900d581207030340e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 357051888 1250 357050638 357050647
    0x609081b0309030f03030c310f05010e010810060e011b0f020a060504180902010e030f010902120304030302120901020c1e0306310309090c0315050901120602071a01060302 75
    0x525003407000c84500071204011718554640701c1c0141196205001410000d0410004841840f0308032000c4110850203018402c40103948414070042412820310500d8005000c121035245554442c0c444540a1089607200f0f40015091080070742c0c44442900c1500d0410400c01c0d04611290858522950030310300400c9084e00c6030b481d40c01809000c41850f08030000b400030401040080150303868008003c0303038944400180e10101440100da510f602c0c2a10706515206009001071090019442025054400c03070b03400c412000690301141e10380c040c0d440043e025030050403000100c81c1c1490010300301d00c0b5052056440c0240c0302400107620096888040e40d0041e001703228a1040c4c00c003041241e40000072004090b511401d4400c8881c030003041c041d5812090144158110201400b0f442c5039009008108030510080e00300d090028020108030340c030000d064503001000151410002a403e0680c3e00440c8020141541510b13014069070050710700701c031400740c0350744050107514900c2c4000d4003030302482d500503995 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 357053138 1250 357051888 357051907
    0x20403060f14070219020d0602031f051203040905180a030801090f090b1f03080c0d1209030912080f190206090c100c031211070b0a0203010b0301030609081b03 70
    0xc03075210707014a00c0b4014460b824032200030340008490b281c8546855032034840b02c41d2440400c1a44280301c500821450000c0188140c1c0d0300300700e00c4400b0076500351505468003980d0310100464001901c0303108403103030420881031000c042d40d600b049500c40d00c4001c038030358042e10800e426468224030290a40016140f0030040c070a012240c0140c0700c089400a40c28005000c0540b211001d8220107407020aa10a0079805142c8aa02610b0500d0041d40c203d42015112002d610010781c44040d02c01b00d00340050142d106070707005401d046c868080805d40540c0c9171a1201d040201d0201d014900984c1138a01c44414000306c2e50411aa500034480c1070384140d2130050340302c072440011b441c0c007074060060b21080d0050b0030180c02a86400c81e002c1501441843c20700003020482c01d090740d084880300c4400d0710050a2988001038203441d04000c2162501ca901906819501c1a250b001280000c0c080c02041341e1003040100041001a04010a03890040c5000c42c54a2003c805405a018000864800b50340010486440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 357054388 1250 357053138 357053141
    0x3040e01060503160807021905010606021005040b0606070c090f0228081506070c080c01020d02070e010b0d0e0a060603050712050c040c091203020708120f1813020403060f 75
    0x1445541022810750412840c041d10f08110791134800c041142c2800098205c0d071017084911400c1124400320700c003a400d1424494007078041401198090703c07804030300418220151084a10481d003206480c1c6490300c8007010400c05602001040d65a0300060354040350380300a51080e0341c9030141c4040c00581c0c0c1c541010240c1580420001c0300c1d41c903400302090314020541c00100741075010800284601c4a1202e20700000c0d40ca0250303210181c900018888041840240082c540700d048800760200d41c24000740c05422a40d8440e9409214550001030004104503850b1a000d003020140416000ca10300d480c24250317a00d0100b407210250380185d00c40d0010014480c092248901800000d101e2030150085c2d52101540d503081c004049000b265506800000c007842861640080d00c0f21000400b41085141002076540a01d80982103650280006082662012008450719800f0981c03030a410864005d0141c2100300c14038604542113280109110880003662004202840c416540096a14038101c000390 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 357055638 1250 357054388 357054391
    0x607080105121009080f0d021b06060d110a03150c091a12040203010e01090f031e120e100c090837050f0604080d0506180a0f02071403040e 61
    0x6018005902d208081d40a01140034540e40c503691001203645002454070106034420005209075000300460031911041c00d58005107000f4911300c001e40385400400c0f0182d070311440d042d6420f03640311030100d013407000180c0f00e03080240e440e8000519507101203640c2d450303002c0300120f8130103110405d550302e0310b070b5500e1b00703400c1010ba0700680944940405050710040180c80c03e07100746002d4045101000b4001011564250090200044030344001d1102d005540b804402d03d61000c04102c1c04070300f103501c507070b804203c00c507241e00c01d00501591100300c4200d000300d80030001d010f4105500c01c1d0b40150501c600100c071050150340c4000d04070341d60752100b291929003c0c40c100206620110050869013081080511205056a400400701c4c40300c262203103080c1c07800b0303440c0a41c144080380d0140941c40030007041c441038a020300561441c0150a108070381d1100104020300d40101143c070750400c0c40c1c5010841066490b4003a0540c81c0a15000500e400d00f1a1543c84c0c1d51011218802c02540c40007409000c26010741440d035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 357056888 1250 357055638 357055649
    0xc05010f140a120608030a0c03080a02070512030c0d110a02010608010b030627120d0506030c01200f03030c0307090602060c0409180813140d02030a20060c06070801 72
    0x108403411816103001c418072800900c9001c202c10744160140200160b400600104040030460b9560300410001030415101403c0030350202c1c50a13000140000c60a00849407916070082c060302d51703040d0400d4150180c1d000070342803c2c1101001c1c445081c1d00c0741e8a00c1881c0303a003011a02080c0c1c456180315402400c2d80c219801c400541c0c1d044c10f1900541ea00c0001d90141c0019021a500201c884a560803044a0b65180d06100d0244280500088e90000510040c83c2d0544114018801d42d0b580d41c1c10b16503510700c4800712030300040114001d900c0d102150f0304141e03150462840ad8403c2010300800c003910b941c00907140040156400014000110380210884008003498005000780c1d242000d0601c0031401244554205603850303860b00c0c4600c0080384c10039603115901c42c01c242e84850341410344080040e41c6010f0043c51806c0603000742e0b41071801240100c0e1035a070042c001c201c000f005642e03001c0516010502c1e00360100503410340080503501c220103096002517540c000c108902e030035440200407040680c800d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 357058138 1250 357056888 357056897
    0x1b060c0507050a0c09180c14150a0503040317070c030804110d0311190c120c050405040f021302092b060504030206040b06010c08070b07120204090e061f05010f02100501030c05010f 79
    0xe2034001901202140221409203441c08c1443c0a002e0200d62040c410500511010400007801d803504c682004c06903000350300a039101c48088007500240590740c40c043e1100b10206502882d5180002e01c10844298424410112400307110582d1010840e01302103d101100400e09202807a10084010420664501ca02c0380c00031300040c100b0f48400e480100540149011008010190030a0000c1094190000e08014008014601d02070030081c66080001408a00c200c0c0801303c540c1080c65240240c0d21100801030580f40454081350240c0b00e0400c1c1d14103403100b0407035910190800300d0581e1042602c51402038001e0052440c01d481c000500001c018402030520a13540c40c01d2010620741001e58500c01d501105245440e01c2c2d0010640d8540b10f82140d1600d201e000040100e0504065040003030a18603480c11140305071038000e52844250341000c5c1c0412221040c0ba020406036201e51082c0f9103052075401502c130b5840e0090b41107816181e09030019503500c88420410802568007825030203110906181 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 357059388 1250 357058138 357058181
    0x151104091d010e010207171305150c0a0c06081515071e0615080d05070b0628170307080901050304080f180111061003121107080115061b060c0507050a0c09 68
    0x3000f01c0030489e02034a40219220100110601e0300d45003252094a03003a8122010035a40f8541044124600c2c021200000c2d02000451f20310440c040145500244c010702c405110003600b00c242110b5003040c41e0540c0c501c0000e0502c0110b80c90140c0f4884100b90003810017085080c914a0941c1911442c1c0c0d00c035a4456120700343c00c400301036010064540b00d0394005d15284040e11844009603c0305c0c041c140900307203400c4040501108501001d0709101b00c034500f1400d03080c1e04540c0b100880c0c903401058409084154100000c1c03941d503201e40021a40103201d82c2c54a82802058440740c000d5410440f481140c1c800241410321a940c1c100c00240110352011006001c00d2401c92100c11032880705100c0100054009608420b0450150400e410344049020444035040d0303803162a94007038404d610070000328404106d00429054444c0c1c8240100d012088100500c010f0380c0e03621140140000480c41080060601490300022024803600308c990b40038050000b02e060800d9015411038504e4000600380b105500c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 357060638 1250 357059388 357059407
    0x618020315040b0c13031211060901090308190608030a02030a0e060a0c06050a020c0102070b1008073006060e15060301180e01021213151104091d010e01020717 70
    0x140f0050b403200020a140d520750700c107004214510b07101a0001412041c0b0f10f00c402a10301d50000840b450035610004899290704c2d002d082c54200d0785512005400104604002514081c043c1030042902042c010006612030f50b5004083c21a04104070590060704001040b24040c2e0740700c01e500c11404000c50302c09103000243c50002d00040c5d42c60030000c1c6030700c0d103400000304003801680c1500d140c1c000510080d07603901e4152600f8a10760b00300300c40128154050030400f00d1088400108402994201410108203075a18904110128400b00516034036000040303907603001038014001d900051880e22003c02c00c9062100f060302c28540c20982860003480180300400a48001c0e014140c001008858001f8031080e0600e809400382c85880c60004042c0d9240041c080c0c241001c1201c8113070039010300c0320745a0740ba01d03c001800c145c680c000c290109090082c4414480048941d1154854160340d10707140544a043c20b43c01402d6408003a400001da075070100d280c1c4184803d850000c80040107208000c2d107451002c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 357061888 1250 357060638 357060653
    0xd020409080409051032120a0605070c1a011401050c0a0c0b07060f0504050d0e03070509042607080306040515040e061518040809060705030d0501150e0a0509070c061802031504 77
    0x8100507c100c04200780912950000d00500c904181c00900601c0340d407800080141140c0d00501b001c40b070207a04008944c91585134842e8080c113841c00c56081c5140014060011605070304a00030503007041c001c55141c0310000700e007100103800601c1c4460140c2d032030b5803181c00c144040350301400540030007500340710401001034008502c040314404103040075125811181d000c030b460148903420268104000409004c140301d0101628188041e44015100710000303c10307000c0c41e09000701b02000704140410f0000c14410301d0185c00069220340080c8045250101110020b01950300707000000c803854000009103d200c526100c01d101d80001c003a10501d0900404803520707039810000400281c803032100815129050344e5034404a820083d00103040325101c0f955001c1c5d00d8010007080c456041d201001d40e002c0451940510f5007402642d030004c2c13030082428034000034000d0a1400405101c00c01a03000308000016501c0e1007210a50126180e05a20a49050ac1410319042103032114000250300c070404c010000d5002c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 357063138 1250 357061888 357061979
    0x7030b0a05041e0f02072108010306110d0c0c0b010f0e0f09190510060504050105100c050f0307030e0a0602010e1009051c080a050c090d0204090804090510 68
    0x2a180000e00e180e400c441483c05681c0481000c0d071084c10100c400301d1140304d070b0b0082c00916028401c4101d01d26032184611100400600e00c02001c1886c4c0401040070503002d6124070703c00313040040040d142448009000044550910920002c5403550f8101e0f01807100c072203101409041c1038030f000a42581014200014603c006140640806a1900140c102001031010000200520703c01e8903003816107260850303c4100303400702c0c1c2c1407851070414002081e103090f00484c0c3c100d8502814140030b210105030122840341d061517007074415101e207580c07003031011500300003c0807110f00a03511006c41c40800c3c0104914010035920441c01c5a0400101414184011a00181000f4100341c0026020340902d44039007454440c074203440000b440248030005aa4205a9003441000800010001c941c0d480b03908400f1400380b0981180c002121154000050400b5440110002e015904550429503180c00c00016074a0448106e04681074101c1c00300102c1115001e105c0c09100110030720010703c2110342580442548 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 357064388 1250 357063138 357063149
    0xb0f01120b06030106120b0114040b0a0303030207020a030b010f08010e0f0d0807020a0b040602030702010b18060f010905102c180c070506010609060f321303120807030b0a 75
    0x900404102d80c2d5400354800c40c020b0806d5607029000c0c0045051510001c40c0034459048200001a2502d0103840c0920404030710290041851440b1400d54078210000d400411040781c10000c10705020000c1085005120300900e00e00101d46085402d110055080d190b100c56800401d600002c81e08900c0200401c0191200b180e0b03280200040d642c588049180c102d41c0703a000b40043c00b0500a20051007101d40003940704460795002880701101d200207205401001c600d880e4070848010001c61610305d00302014141325503052402d022155252000504489040d044440201d18205c00441c00301c242000e40e5065104000442200c81002001284619054107581c0e61551003c2001819192410007500e0017180c02408035051580c6030b200c0909480524081c0034041a011040884010301c59215501105c010000c05030401200c01c4a074204220806001074852405000e009122401045218000c6014145180b091040c450029182410192151042505000c46030141e51110b5414804859 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 357065638 1250 357064388 357064403
    0x150a330308090a090906061a0304031403070c06020c0a032a060504021c0f03230d050c0c0d050d0b06120708040c1d1f0806010b0a0203250b0f0112 64
    0x342d000074000c1d0fa10b540150880502d084000307030500009500803c02d035200c5280d5400f80d540784421000c105c0c001201c0040000d64400340c000840c030500c40140d600302c101418480c0d013030103260b900c2c00140c0e0000c24805119910800d818802c0c141e2204058028002040710100c2c02c1000c036010595107148003401504450711a40400c0440d200c0c01408900316401090300e1030809114600460a07882d003c2d001e400003a6020b5600e290042c09c401070310704001d0b80202e0645840040f107461006802d00904485446009100440c8001000e22041680042ca40d507503075035400461a40000321010780040c607010f4a030a1001101c21102d03088903540105072400c00d032906a989241c044038050107030300007191441d480810222845400300055014140a103688000321004001141c09210680700b80380d465401180100f00d400802e00003407000011301e2040c2d030f103002d808421140003a0302c8000418481c540d903003040014001171450403500400041055041540b40502e2100d00b0000c1c10005070500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 357066888 1250 357065638 357065647
    0x402091305060a090e15060105030c0a0c021f0504150302070c18110c100b1c0f0311030a0c11012f0f0d02060f01060f080a0c02150a330308 61
    0x2030b0745014405008228078002800440d00030480170780c0301d03084440c2c184500070f10440031903030660041302580d20410907004a0350406e0790305030045a07601207100050780c106e6505613808104404600f90740001e800551280d0b5961442c0c080380b90f07031100001da0070204052040c03000000080e1403015020444e11120082500013010310a4135004103110f404c00c82c181000080d207690f80302c2c0081a0345403ca0740910040000d40041414003100c00280e100556051200c1c5c400300f000118041005a60342d4080d00e080c1071108000c160651466002002003804102408204000c100100d0319000404c0401e1a090700400e40700900c00d09003003003440c9082c00031541d41c1a140c201c00c0042240ca8460342d05031048a6156000b01c0b0042e482d14001c0c0d03200840c0450980010135803602030004c0c00642c0b00b0030303070381c60019503038014040e00201081c0b0481c20443c003c804481c011031061320200d5000f505250380000b43d0604014846c0c012040d003040b03282c10801900d80c0250403503d17810402040f0394000c81402d40e40c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 357068138 1250 357066888 357066901
    0x61505120406050712060f081603080a20031326060712020c0304090f2003010e040c05040515030d0f02120d0905070f0305011a0303091e0a12060b0402091305 69
    0x100c5040564500c3c5c00345000000980c80080c028210704481032101550390188100e0b00086000c06e840c00050400c40e001c1000d0b800d014030404038043c188100b40d05c5804510001c20718981503070702540b1040c0c602c3d0440c060602210034440d07118910785c0e01e5207803403200c0d800050540c151994001008807040c0301803601c2c010741ca00c0300b680440d284030740c8503400c0d00c2c0d0360707521241d0080003003c01116200080d0b1400d03070803800b0071164950007280801031050060441e03192030140b0104480041003129043c03481a0006810740f5940a814001d41e144c050802c0503030141e40c00e1514210080003180204903030702400d0105590081010803001c044070340725a64a408144911025144030440103000d40b1560b02c0010350100310a8001d426a40b0800c003d01c80003c0b4001f00c0803000821247c2254507070010896582f080c03525a801d019811840728a4008038004040010701b909a13940c40703040d600030f039404460204046031090010903441204e0842c14004510045598400507030803a840441e901c1c800f0031031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 357069388 1250 357068138 357068147
    0x301060b0702012304091d010b0307050d080315090a0e01050601020c011407020d140604050f0325050109240609050c040e180d121b12020706060b0d0615051204060507 73
    0x18100c00e82c020f015800190641f04151110b070904400f155181582001c0c4928011890508980340140300f40d100c1da10503103850070a5400501690240c032404440092992030301c00584d0306c1501d0a000000b04000c81c106464299480206840e0454008c07111880c41603802030020741205810500c81922200c0c14400304040e224060005081507a2038001081440000034407140301c0e900c50030a41c0d6400610a856075030368000d003445035920000822558485006042072841e929004e0000072071060419200c1c10b0b80800109160140d09224405050244642e40511001020040d800300441d140000036404a80a14000c03400802c580700042034505007280000400c14015100b51095410a0030002d04580c0001d1031002507141444031181e0490f544540c80301c254422a118507419401070440070f0000e43c000c0c01e0881c0e03400d035280400b1484400175030103071441c00114400001c4d41828001c0240e10003080c243c01c4403c01c581045510300790042d08203000d070859071201010030a500c64100540b03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 357070638 1250 357069388 357069397
    0x3090f0203010204030c0f0e0103050303160c02091006110c03030313031106010b0318060907090c020708060a0b09090f030906030a0b060304060f06090606050f030601030b1e0301060b07020123 84
    0x29070540c004a0080144083d0568141c110341820304000341c2e9aa0b1216a904440c3e4244401f0340560001d03c0081d60f07082d07940c80c440d10601d5042c640910f00c210103074002008008243c400c0e00045042d80c50034442503800c42e9450190001c460001d02002030560b0001c0e5481c40000c2c05080c05421800c101e00405008586c04403800d0585416100b4940e142d40041c2090740048a510814004202c0e4210718620f01248240c01920700a0150051034149011170303000c1c0c00c540c03004d0030852040103400a2884005d0050600a030000e24010540380c00c1241084654540a04010065003004c07820503281140041158004007007592096225035442c0d80100041004018141c0c100d50004104010424103610940e0303650080d641c2080029103a01600c0210b400c84c0c01840003184080015881c08001c0101443c0e2204051502245401040d80402c0181100030403940e4103009040101c0510319082c018034000d40a0044050704020300c80e00000e1079100c8014001000c0c0611144401d0803048140844 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 357071888 1250 357070638 357070643
    0xd06090206090d060e12040503060631050105120c03100b0d080c0313060809030702010503040c0801060f08060c070305030606030601020106320303030f1f0911070510060e0703090f 79
    0xf004048480c0c180f1002602e401007040110780034a4000341007100696007030b901610b070702400400d09955030700148010034400400350301580a1510304640b00200744010b400045070002c00c082400e515140501c01c0d00342e0b00c8441c50000c0e8020b449600003540340001d031102070800c01e0501240203a0380401003010801c6543c4081c10380680040c4034804844004001d00c8608048040100125030711002140e58403030070342d07819180d1340040080e180590303c00c070040d40c0c01a0081c501c03154150b6840e0790300d038212a102e070711104d6240380541080010070818001b030390b444130310411114a4411542c0c2e00034654880240598411400030002c100c059200f5400600600300c400c0720704400d444580b00c0c09121840c00030302420346264030a00b00c03003030341000b01c1541c3c0205003041841c2002d442d20b0300d01c04203140c11403445c00806c034801040014114100e0080c0882251341c102c2c8950b4401c07250810310b04092040e01c0c11000315081070400c005106680440d00d0b48042a445c2c001895141442c02880f03081072900d01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 357073138 1250 357071888 357071899
    0xc1603110709050123010207050402220611070e1512010b100503100611151b03010b030a0b0303090f040e0106052707110c0f0f030a0b0f090c0d0609020609 68
    0x101d030b00d0700150f10050580d51000b80b45540962111015000a000c0411060068010f000b08000320304054020784078030042e0881d84441d240a107034203000300400c41d521880c0020310b201ca0810400c0001d1000401406248020304001c3c648108108000604840f101d40515150020040c00c07820a61000c01c0320480100b91026514030308200400d103410a0701e18846d90790100303900081103070041e1140014029000060001034810700c80c032843c0311070001c01c0380c90002045003005201c0c5207030703c0c0118080c0499450150302c03810003822520485580030703409070103a030003044107212940e0380080c040500003040707601041e2031541c4030125024000d240c0c41280c002505400c80f41c80e2006000701000c1501400210018654480c1e00881d40010000013210144d0002244428581404d01c010f01d0f043c5c0010780003800050030407020a00d40300384044191100c0144000348034144109450007600300c00108014040403000400286000b50003100044c240e980c2c0301e03100030441d1120b20903031b0b8001000820 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 357074388 1250 357073138 357073153
    0x80c13020c0d0e040c3006080607021f06120b10050402040b0415031107080903010b090c0a090807230a08030a09080606191404090503131d0c160311 65
    0x1000e450510100c40140c4541d04141c5c1c2219001d05c00e242d540410360207600d9041403012500320351304004118942d04044030f6214000800c0c000e47c1001068007841a950050032100319085620607002500c3c0f1450b02c0c013a0500d802000105205820782615640000d0907401d40d458614040c9200215544059006030020900045217030b800d9020780212015061080c03046102404210110f644d910003100f51a40d0a02091012070102d1000c0d000744013002c1c00018405100c503000a01c40c0000304d40c00c081c00c920015500120aa000300d24000a01c074090052411030300744a4020244609440e80004807400b07a41e4541180d40d030031a40c68000d141800030faa9580d040d485c40105544520700034420039100c3c880219186080662070792840c1d6080c6142151454105007070b40c081038402c0801d180d0b015403100201008030720140007c1c22a88012555034845034940740c86c0540a14060014a82c40345a000403c412280041c0445110315a1381046003401c1c5601d10f42a03682c1c42005681c6c2c911481780c00ca = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 357075638 1250 357074388 357074413
    0x40c020a03120e071806030f21110309190b040305010203041202070b040e04150e0309031b0618012006010501080112050d08060a030b04060903030506030601080c13020c 74
    0x24a00d003840d80a540e8408144510342101400d54008a0401003140e0001c4002c0003441590004461001d20841001c140680e1f02e45990100c0c4003e95401d80e191082d12a180060700380c544080326500c00107051881800d8a40d0f030003141c4030f01170f80d000180202031034a144004640361402e014050215900480e80784c0c0d0700e0381003850017504110f13002c0741e66000941d44d00032914000a1848100d404d5020710f18501404d20613040e01e1004085d04c00c903016140490f00a0b07001c0441d0043e00c000d406000001c5848260200c201441c24402d400da2040c20182c0c0009102a501e0301c0c4122006004404100d00700d415840340104c2d100c1f298101c483c40d29820340100702806a9000c100c03681211400d903940c0b4260f0340c0f9201010354402121100411691100031640e00d4a4014144240c2c0080f00800e030142090341d0b600d030505400e00444048914a507620364140400da05842200e8004030290f00030315180d030500e0050395482c51902003291203a101c041101c101c1c3c0801360100c4010440540076990284084c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 357076888 1250 357075638 357075643
    0xc12210e0d030b03070b033111100c02010503150d1709010f05030903120c0d0603080d05011707060302070f081902060603030a0f030b061b161e06030c0e040c02 70
    0x1020140064200b9000e01010b240020f64042a6980414042c7c9180c07142842c00310b0480d00c00340104054120750303d0040344802c0b4141080c034280c0c050b10034001c21002404c00c2000c00c02d11405110140304a107550580541d90020650380d20400c8485180f05182440380080d5a21116810040411024031441d59031030441002426080d00c0070f0300c80d40d43e0310114a4064800c2e000448a10790383e0b81c03090000705900d403584c1e503038260001201c180d0680740003d00340303502040d40c410790000e0340c00369030010320749084a41510555005043d0f0100c0a518a80c54030110358544c1c100780300d10010181c000c02c1000c2403108440b020b82807141e024448903595103c070b100d0011a4004101c80c074026000300390002c4c2041c100402100e946c8605940c1c0c044900510302400d034002c002202e05c058102c4814401204411700355040b00c50001030f40402000c2d00290900d500b001c0b8540703070f00b159101081c40f450f940d80300310f03984520100b0b55001c1e090100d40070303800c04012580c495000001d194000c5c1425003503507810703030003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 357078138 1250 357076888 357076903
    0x7060c0f020303040303110c0108240a1701020a02071a0a0c0302070b13150311091002160b090a06020a050703021011060106111225020d060e0102030a06060c12210e 72
    0x740c0e0141c4209070f10702340065500b14001c58002d117509022103150740c01005a1000000448002030001c0b04e00c0c0d8481244d10b40c0141c4807109110b032030707600043c44120560108041d030003c21150b00d4101032002c8850040b1040d000b140c0d524001d00404c418071008050082c020300c03020b80416580c440d1984d110700c52000c00301d201c038880d103100134000c0a00031038218401e000740740d2030a140582c1c103440c0010420600503c910035038098011406034403080d035598131410500e00000c080e445100b98843c140c030002c020300415198001000c1d507100c5d031f02540000d000440c80c801102c1c2c045442c3c4c111950089000d882100019107041c00f94051480040b501c0c3e500401880f0207a410401200e0300c145011003500014441c207030503034141310355002c0701000b0f000c50200261805031001e0180c2ea45d013403280d07445005840c48410240441c0e5001705c00c004444450340f152000030501c514040011900079100c0922100c1c00c0550003080005614824149a000d5200e01c54022600c1d4810843d02c0440030030540c0390f924 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 357079388 1250 357078138 357078167
    0x40309080a0c1505070b0115020a02090a0b030d110d03050c0702120d08010506090915010c0807050f0d09032609030307030c020a0909080d05090114070e130c0207060c0f020303040303 80
    0xa030f8061203100103103d00c007940c035460382c0700c000c0390003030307420003041c074180110605c0038504500c40d103250000140c40e1000711900071860448013041d00c1100c00c08160500c004041480b04010328840741c204014800241c280b0000b410b4240083ca580b0360404804903446040c0020350005441002440741107000106268800c50035036609402d86d8031390082045910400389070a500c03a00d40d80100340c904500c802d22034480d10b01410301d603810070595560707803807aa04081001d03112034200d10213440a01400b07002011202e40c041c5030000503d8110354078509850708150250040800c00c4401c103003c03a621f813007180c010a200400f117036225449450002c04004008034200e0099400300340014a54140d4050903d84540c0001d82504025400c502c10004050040c40811b85640380c088585103031022400c81c50054555035543d0074013000034024010003004042c0040401c500d0000d074074071344640c0820340c40b0035034440b403520552405aa040c400784024145001a5242c0000980001010b0700140080b85051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 357080638 1250 357079388 357079409
    0xf070201060b27061209030c01060501030203060a030b0405070f08010608010f0b01091a040506070311010b0906210f030a0c20010c020402070501020c0a06151202130203040309080a0c 80
    0x41e02c40b02c0408490041c0c009038210401c05400d80c00b039000806540301210b0703102501a5040c55480341d40d1404a60060364659101d40000074010170f40403081c003e002c0075180030309055103503043c00408a141101749200240c080080800410200301d400d01400e0300030a50290380f03411680e12a540b4500038416403103850f0f1035601e84030302200c01d43d0450088419034001612554903c03807501c42080251101d070952102c01c40b10070440412140d45c3d080140c05954007a68440c41351551658580b421605407490072440760440100301300c1d80340d490440c40c1200000d000c001402000c01d8003035091030440030860321401c0340000b280080a15034450000503985e805031010603488007130901c1011403c0c01520200340001c40c182e181030302608013500201030a512400c0010700c2c0c6114150010f0400d4210041200c100d501c40d0060250310015804800c0501001200c0410380c80340ca03400520b0350260001c6905e10035401000280605000e0348000c801081c00f40c00740c03240d80500c0d1515907000140d038029203c144 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 357081888 1250 357080638 357080651
    0x2010b0102150610081003080408010504030e0402162604080c15040b0d0c05071406061504140d03030b030a080a18050904140f0d0c05011b1d180f070201 67
    0x3040300e40c40d01c1e80101c1001d803c11003aa131003840220303103400c0018081d41841151002c0040010004030007000181fa5200c000102400e00345801000e141e0989102413142d03005010003d0003250030b40d21340003110303445034501c048110300000110031854054000242d0751800b150020383c1c1d0901054500983d907085480d04104400405000001c1c0554028480c402000380008105590950b01c07a806040341e42c00c1041c1486103960381c20035480c1d008903045030035400120030300089050201c400c5101c07030400b00000781060b0519503031020a215070740b13440727204841d0800040d042c036000380e00c010280c0c18043c2c00d0750b1811400e070402503403135071044e80800001141d028204850000e2481d2a01c00d540004103c3e0801d500c607522405194040800e405000e4050f0070041413622204000120f150512621240d8000c030307040c2400c9003150083c03800b88001c103080c60600c8130005da1005100c0c1d01d8401c40d04582ca04400c0da080801c08610701041c41d8400004604180150f400101030007c0c031901e1a64003c1c45403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 357083138 1250 357081888 357081913
    0x605040501061509060f0c02040c02010e0105010602070b0a031821080604060302010801050603100905151906050a20010501060c0209130209010603091103030403030e090106030b060706050a0b090702010b0102 91
    0x2e07080494680400500304d02800e0140c6072080ea25003807000214540343c07120f030919800007403c80324103403089030143c2e40da1010020001400e0040900524441c000381422601d8a1800a154418a2102020181d0304d80310b42c0480081c250707035002c010360020341c20404480c081701c0007660301c1211651880400d00c1031000070001e19141c01150300b901d5060b5074558040e480c25091042d940c20141219841c1c03a52043c000c50700303542500c03e0f0761041400c0c0c010102403c40701000c3c84142010384064180101c2a5202070100c0c0d504501141e80308038840c500742040c000000007844554045400800c13042d400e0000010319140c0c072113178814006000f200c4103490ba840300f100444400c003c1000081d04103042100402903203007c0c0c0d001030030b00c3d8000d924940201c43c0e183d00183c00d503070198104901154208203007a034541403088180d8050410340c282044000d00b00c90001703815000316600180b0460b1100009000400d19801111100c003025000e40d03801d00705843d029010f052807107100d600511403001f03540c11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 357084388 1250 357083138 357083159
    0xd021b0601090b0d0b09031b010b1003090c0e040c0b041d0109140411010215010806010e1e0a09060b04020a090314010207031d040605090103050f16030203190618060504050106 77
    0x3000c0b801420807002d10035a84d601c0d00e403417000a00010003804240b0403490311085010480c2d080d685503000008502580d072080007600030300d5685c0c503820146086500c400041c001010142507805e00854090269100d1400100d9440a030f04aa0a018030200300012040c003444080700149100c82c181040580c1c844811100710760640c807801210071171600110f0040b03409c054901480013018810744044c24a00120341c0074200081c0e002d400294000c80040164061608070603401183c4504440720240102594503034110740902505c11140d510f1584104004041d071000c0543c400c054025501d8404515002d0f20301c0d900303844140c0e10b404940140400c0500e0602c200c810095043d21007102100b015090341584091803074034980c105549103408210b0340d9441020a00031441040280343c100f91840d09241061006004400c50444640c0c003400103030f801003020080341580d20f0254000c4107035414281c014010b140200c10300c0750301c0b038140c038000e0040e9034000f144600c4c09500244003c40c0e86852011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 357085638 1250 357084388 357084401
    0x80a140a0b06191101110a0f0c15110301090c1b030e0409061406040c020316110a03020a080a030f090f05090a061509080114060f10020a060f091101080403080a0b060d021b060109 78
    0x19021408c0713040d1035028025031942c6a004410007044924000308480c02c0f55048601001c0c0c03000040010082c45c6d03040e004081c1c3c031722414a007480780d00c00100780c00004403188601c02002d0040145c409429520355512009025411034010300901c4940740801c0c0d465801510750b1b500460400034080b000500010443d1100d801c0e9401c140c0c8150600c1e1961000c040004650541c01901138400002681e500e9514601800205028005000c01441d01412400b40d010100d4103110241c0010000c4151441c0010700b1180182c940f070880b07588603d00400140151381240249031940106001000c0d489140d8a0944480030002c2041c04d4029540d0440d50008031840c41c0d10211403c908019400d1080120741407540c0c038011108040700556411095948128410900760740d40d000500511483e4100350907050001e003050701040c242610018000d510081140c4030f11038031249014819200c02d0225542c4520015045480ba1000c0400c0c005440180d1070f0004540f08440000c00c1e4550fa612800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 357086888 1250 357085638 357085657
    0x3060f070801060c0201110604081c0b0604120624062a02220609090204050a0b030a33090b07110c040506040921080a140a0b0619110111 60
    0x1220160f1030018200c80800641c2c0c81203040150082e624010388804116a40c06113101301003598076080818166111480544880c020b00d034141000c0b5103070303034960108840a4503689451404400e0407414420050069a006681300c1c103800c04003c240a2205004070055034010b56036441001c1c0c0404926104100e4152000220400080d0941c0185042900310809032003050345c20300c051b039a445d4000100d4007154401c4088030340740d6100d41c04500c0d19120352030340300c440300504110740032007100801e13528201a48001c0160354109032905001290102000c00781ca070140c1c5120707401702e01400d400d006c0c3c40380c504220790500100b40415811800b0b80e03c01101590b07000000c01c02d1100c0d1108010103004040c0086400907030350303414080810340d80201c20420700f4450f090403d01b182c02c014014400a0300409000225103090040b40b070b903580d444e03c1150446299040864456004000030742e06100e8040303a641114103070000313002c034607401030204007040d51418000c000580c03110385090003501c141c1000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 357088138 1250 357086888 357086897
    0x810050102120702120303070f02070b0a05071b2303070503060c0313030e040f091a0c041e08031606061215020c010f06090b0f061305090a0e0d080603060f07 69
    0x200310ba5a0010010b00a6075000a0a4803080741eaa07842a07401c5034020b44404c0b0014146501c464841130301003000c18014101081030300d18100c18030030f005296005000d001452400f004c800c0185000402d4801c0c400f410350104480c454092400c03030360206603803510000c1e0203809a1040003c0e649800b00c1c4d03052281350090111843c550340d0040d80010324200800480900c070040001c0d008030340340c07407244070005142c044002805c4283d82c1030081d003c907101c9019090045c41d010400403044401010b4404944040c3d100020314005940040400e08468100f0a0366100218a000c080000701e50001102c60003401c007042030a48a201141030106948405083e140e00e0a042009442c0c13150b0007054070364842c100000d161120400d842090b56070503400b03514400d44034101681f00b450105125403003070384c084031500c2c5807820030401c9107500c400c036204091140d5008000074110040d10341240e5040d00d0310344192540c1d40a0b0b000085c1083d201030307400b90300a101d4200041c2801900c070200c140a100f1039200e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 357089388 1250 357088138 357088153
    0x305070509090109200415080d0302090103020408010c03021e0304020105030c1b0a12020705010e0f06090d06050f040c050409050606091909080c0111070f0b06040605120c010810050102 81
    0x61098002002d41a2545996500b0101020483e0360358802400b811149203110340c56503900c2000242c84078944142541d00c0c606034100100d100000e0300e5010074245040c0561180c8440740180d000b400b80344e000c038140303500701040c0450040e4035034000c2c40d1020180d000b01c031454240440e00c01581c0000c95000780441d104001160444018002528040e103124150416444420110a081070064142120300d03203140f50039a81300c1601401504041c02c400c0c80c000a8030205a40003507900c009800415001d00c038005400b000c0f81d01c41030048110150040800d01050808086a03840c1d00802c407002e0782c2c1c820329209d0104240c0382c580241c80501d40c00500030304054550404220841030082d01031000344403400110380800a4030f01480300e0050103480011b031107034028450f05081d902da01940700548207080207004001a1013071004800150030184802180d0351b0040498000e04c455000107a00c400e089040761018030001500d80c52010080c0d075140141e03110104400d0b0211720b980200c0303000d03811505 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 357090638 1250 357089388 357089399
    0x5070305070609061b030b0f01020c090610020f070f030b060f010806041d0f03070219080303010905060a051507060c031b031e0615180308031518010605071407030507 73
    0x104043c24042c028071001840041407100c94124003519110000866143c00100b07690f07203444414003241c07407070070300141a5901c1d01d040010011400144001d01c900a14201c1d050128800c1040707860080f02c41e41200c0200d500c0f41c56003103054400f480215010a195000071b103d43c05d0904000b800f03148181c41c4d21030152121000c110142c182d0918819100311080760001411a0400029905034a0300340999500d06440c01401600008003280e000c2c9608144020015081c0c00011241194044100003a25071100000180400b04903800b8035840034020302c2c940242c83d0740f400200a407034400c0c84201704a504505090302650b1243c0481d9001121100614074024029001400e1900c204001022a80d500c100380d034040350250380000302c0a0650702040541c5079005034014070f160b807d410040300d5884c6550781d110030f188401049480001c000c0b151030700964803501d80c2000007040c0d00d0403800e004d60711100020416040716900b80c2e4620f80080303025404220219805069a03005809416000d0400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 357091888 1250 357090638 357090641
    0x309030b10050d111801091d060603031902070f09020a110a030203250b0a140108010218040b010203090409110f0117010b0a0507050709141e010315061a0712050703050706 75
    0x204604c0c0c3c2c0003e0b500001c51601c10707a40503201e0103000c00c004001640300d400350b1001c400c007481e14440c0110b43e001d2814070806a81c0041915001000003215000309100920200c2c1008040e80c0045000c074009140031507000003940152140746426600c4852240c0e0311038109686031b81c00c0d113014015070020040002d11060b2030300307551006900388101d000700c28250361310301600840448481c0c00c3c6d1503a6024030f07103218001440450041650000035400d0813a8010700c1d02003078229000c41340c8141d0361590f07800da040e4000c0c015580640300040040002c0301c11406c0190b000382070030524a1203201d18650041417036014919040d55800020308582840c0c1c2042c0940c910303944618082000d02400b40840c1000074030401c400703406041201004609455400c1041291903c080c00c501801c0941d10300520070001030b01920781c1102d41045014502e56a02d14000000304103507001019000c024101013811004003500411126100d203040f002c12a2407004111581c0c05855001800a2002c10940011a505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 357093138 1250 357091888 357091913
    0xc060c0311040f080706140301230301050f010f0f06140a0c151509050603030a0806120106060206040210020a1e08040b0a020c04151514160309030b10050d 68
    0x5505000803000441c11551946400550000304001c12034002842610000c1c0011030050410381480c81100700c01e918441120f00050141a00300c0c030818103580405006580098460380002d0003c0026040c1085001c0c0314000034003401090000b04600000c0c052000c1d0000c0b81186e0540c2e4480544014107080700a55074044a1080d04000070464039002040c000c081004000340e11840000d00f6894449030700901d40103d40c8640e001c94030300720070420280c602000711042c0c0103042c5000031107030396020001982c0008030308602c206980303840c101040d1071340c00249030b0340201e00840300700000d4520600c0499885150302070050141e02a103444101c1c0c40c031304900044860f44502d44403400c040d104c61303400d0086d81080038400c00580c85860340700c0701070515200340b03130465104030190300302c00341040f503401e00d803200c41d5039490100070904640341c03043c2541c0019266845810070500e03071458070f030382401010b05109000a0b6805a00300000c604401c00f690b280d4400c8901c040e00301151003c02d030302d80c0c1c1c500000c13 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 357094388 1250 357093138 357093161
    0xf0c0b041707081f050603162702040515030403140c0d020129100c06020d0b0910030215090103020d020a09030201080c0c060103030804050f0f030d0f060b04050609061207020c0f01020d0c06 83
    0x200c0d160348200c1014202d41c01c8c040c01444400c6021075000e0449600b540c00a400001c001e00d1040000380701644503500c00044280c07464440a50340c0c0c8451804450003c0340030703040ca0b6400710114918104090205400d040b101859009110b0002e00042200d07030300d1f41c8020000600c203c03c000d00e0b905400c1554503842030401e1410301c1c2c107407441c1c01d4a643c030981e031040c2c1a040070742d5070359452004280781c0030000319000707520b000c00c1c61951070441d4081808005100c00003401980080344420321a0712a0b01102c0070215269410354417116125005404032209020890228105600044500c8101d2044d03c403000303441d40081c040d603440c0d604d09650f42c0101401c01c2d0703aa80a01810103035070502c1007040d0858085c10100555480d400340e000e1004a0304041300c00f11000341003050400440c555402a00c0507200c4c201d07106903481d42c0f0100055568400e103000c080c20744c1c4030071040060140d0041220485000195141842c500404004903261003060100801203801c080814021401c547d02ca51280701 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 357095638 1250 357094388 357094393
    0x1614130c09080f06010906210602090604050301020c03210c0d021c02120f090a05071a09090c07150203130609030207080132010e040f0c0b041707081f050603 69
    0xa85500302c00b0706100a0501e04081a030060300100110040f40c410071000342150a80280c1c5064480303040c1541c032410b018090140e5801180f403c04030b42d0b64104075802420020700866803818000d02994413a0081125084840c00c84100903c4507400386a0242c41a02c4641580f0314240104420b14025004404428461000001007510f2406c19100801d0119801b401c00324052903e000803a0340303003400401c00e0a568000702e011000042c03000504a0958858040c65180b41205203c903640b03d0044000d238950003000c200a100901c145400200201030090710b0964800b48583c00803000d81c4419035400c081225400044000300304598081c0003424400d03c103440f01a80e840c4903003400d6644c0e40d0714a11000c41d0554000704180c46458280d5030085001e809028a0341c03428041c04400d000081c00034200e04850450f0f0010460304071a000094040d02095603126900c860b07804582d40b0440201c89454407651501051404001604403214200090346c121500d032046203c10190201800068261 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 357096888 1250 357095638 357095657
    0xd0207020a03050c0301060501030e0a110310090804290412060e161e0f030f0c03050106090e0f21090f030604030302070c060e1c03110d021614130c 65
    0x107a0303880341c0e80e000640c05070000703000612100c010107003120039540c06241490315001e4002e04144020039140341040d08204031491036052000031a0628440d10241c606881c6025000c404001985010340191010840800e070384103410740c1e804000e2042c05059140b41c610a0104000b400e0002c140403039094881c1c400400c44d600100301484c41d00d22800001c2c5007120104100740110203d00d000095241d81254111003a04d141c12003080340341c001c42c0005008031030f100c4030003c2480105a800001580d0140c002c00681e80e54140100041940346403000300d0380121002201c910700000707161036000030032201c1d12032001a80307050030905038003155220741c001074030403080801e40e5014801c1a104900989001d0303940d003d103180c4a02090419048041030100c0d88000400342d07102d40310f2020300c004002e0036010800041381000d41d1042001c508807140d500c00d43d6407607076184c2d80c0030801404000003040303054440790b01e07141060500a071a00c1183e41110f40d0403400c00910500350000c0700221013600303000820 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 357098138 1250 357096888 357096893
    0x12a0816051902011a09060607021c0c060c02090f071205060312040b120618010302060d020d0e0f121e1303081b0d08040302030702010315050a030b010e0c09150d0207 73
    0x20b50054821080942d6495020141c1c1055440300c60383c0e1880120f441e032210b450a00005101030007903210182c00740b0440b81104400500030310420101c81d8121500d500b48946d202802060020070b03c1c0f0032801581503002182074070f1030101909004503403c4d25030900f600105074403000200401800c2a5161082c0c0349004040081d140052028080d82680c090341c0d04603401c008002070001806003800f40c00c415007404c11031111030034502d05403a8119410742d5a83c80019156004e4010306c0c1f2034600c00e515001c00f0b061107410004903503010502e41c032b0546000c05403525414049004010600c1183c075408000504901019002031030044481240010581c4e00ca80718081e1680242030460164524000f02440d150010020003071039a00c9440c3c0302d20700380707020354009445c3c1c021080d00030b0600d034840e13000040c96000320900c400a440098a100c860369901e0510301e07100e00c020312410072100e5401010503000310022080b6070a031540501b484148056034006c0d61f1103540051216214940d090240800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 357099388 1250 357098138 357098167
    0x90201090510030b1c02092206050c12180c090c072a090207030918090533010501020a0201080405010b030d0905090709260f010e012a081605 62
    0x10218150b6800051006802c401d110200004c205c00039400000c5084d80f9006a5030b4800040d4048241b07035110701a2440204030041c9140005d02c01001642010f080040310b6032401d01800c007a4544400b503400f540c41c0e004245c1120640c0c1090440b05403c04908200b440c01c040760502c2d000b5030311140e65071030400192102c0c001880410390410000654000d02005020044405000340a401d40114034001c0d542e03802420000360b038807072110700700004100b1109a0b101d65102c80d004541120036508040903c1d903c820703001c015404d1612101070906080700740b0420b004e0005040e20010780081246c40840e400551384400014411606592540501d0031651414083c070340c8200c0054a980280f0790502080009080d03005180e08108000a4010442103150ba0200521101180c81411004110040041c140001040802e0300783d0b00303003036038081002d10552200f51141c552550100b01307288818000c689041c25121500001040c66022a40e007610b9651f180f42c43d072959041c03062801c111a000000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 357100638 1250 357099388 357099409
    0xf0409050604030210020a050a0c1a1512120d050c0415020c0a0e090a0201050f040806010f03020306060901030b070e1804050708190512070606050a2301050304150902010905 76
    0x22026080903052208240c2c0400c40000030805c00d00c0150b040000503034004145c0c1c00b8005409042201007034000c024044851410344009980349100d41ca585025045504250191130141d80507116000d00c004030780401040140c0004070401c0a10714040e507450010300603050180c15200d00c91001c00c8001621440d00c49040d600100c15005031100202000401c417203039665510404881c50322100704604004d0218403001000e609007030050300c421007103d48003600d0290740c0080c03100344030b9040045401ca5030141c0c0c0100f02c9100b1021607510759501818003105000138400141131b460b0313100101d1900c60050462511145000d0182514030344c50300c1c1450180c1a0a90b8203071880c1e0811801070061640c00d2200d801c0b40804081d102030124070b02d0361025541e80364023030030203184000401c0200c200b11480c0c1060005120003013000c1c1149840e88403441c0c901e5680c10b4000515094540750310400d50040056038400d5800c0508007028034002013a14018000d403040c100d04102c1c01c088082010b0769a80e01c1207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 357101888 1250 357100638 357100643
    0x171c06030b10120318171612050a0b0c3901050903090405180303011706070905010e04090314160b01080a020907050a0e0a06110d091809020f0409 64
    0x45106803039420020300392040a010602c001c401000c00780041d10000410302451030745440c2041d000540d030b004a6800d1102c1e5000b078000d5100c0d058010841c2c3c0000120400e0741d00d4003c0103000d135203590300440c9400701c140c0c4d8001441500039451030030124000901481d4001c002880a91030f000c0107041040514031180300000d41040d02a13841000140b128500b002c100408400820403410004200703642c1e8042c0d4010588200e496100081c010302040c0c15000b0000384d50b02c1126242e5071a02c8108404162101c041070140c403a200004040600c16000c1c0801c4420607100c21040103185005e10002c1c0c2020030080d000e00484902000300c00203084010b00c1350b4030030422110184007152801c100100300c1a84800c0290340960f60800140e0344104041e600702040341080d85c1c1c2c030401c2e98426540040000c03151540075400040005040745c10011581c1c159804000b501c0310001410410b84d018650781c040e0032400380e1220200b2032058141c0d84075406071400104107490720795081c2c00050a403003000108 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 357103138 1250 357101888 357101891
    0x90620030d0525020601230904051c050909130f0c06050c0c01050f09010c1a010306140c031501111f2c0316080405060a030b010806010c020607171c 65
    0x800600c0101d52000c1c581d41c6681a00c0e400d510f10b04001d00969921040c00b4a6034240d4510000c045088842c80c1c03404052400604400500d240c6801c6c455220256408070003c0404480b00c8450f08600c04c40481d031160000400601c2e041c0c80780d2031001d0808848509c11074001018600060210784242002e000070101c0e540d449550b19486030940381011008140307a41032100502402c11949540c0c0140c0d0a900e4080c6050b92061040d42400f02900c0f410032071140500b0035181c008420b100c0f50f44c0040c1c1003c07074107000290341504c68144a001604c4100e82004110300d043c40f807501e1a40c811640072445109002c11503440c0c05000c440411017200443c004080d056540c80404406071207090101c0b514018000394070b240d4610f60010366100c2c0703d00001a00031003c0d000002c006c06c42c020701558081e1101406194807040c0c594800340061030f0b92500c16021400000006280d513200d2400c001c0c8265015220500301003440e61010103407008540244100300080c4800321541700210000543c580780603d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 357104388 1250 357103138 357103141
    0x8030c100b011103030408030c0418020306091501020d210c030f0e120d11161a0117100b042d060b12010b030601030e1618020406090620030d05 63
    0x484012200700d8188141800700400f4489041003011094175417003070300098865503d95a001c1020400c3c840d60304550100c1c82907070144418130015a010f12310454050340c4000807900d503408070403030342808034030141c0c0180c1c00001d0018483c4c1c85480030980c40d14141800b0322218510301540703025590403060fa0b01c006551440c680b40100b60b903004465001c941700d0050000304d598000101006e1044030160b002d9103480b54030290039000da079403c03139540c0800c108440c0d00c012101d25000840c1640d5a244000880340e440003c1508581842811203940c9040c0040119503000c1c0d1001e000380a0340e4000715445651800d140c085080c0c1b0f24014000c90a03520503180600a004412208445541e04251020003040c880c1c95403200710044528152001c000d00300f9101c0d80e48030b004a010f80360224008801d800380c07000c9148641400c03140d40702070711300656440c11061402e009040481c002d03845132a00140002d01c040041a000b4040d4171511010701c00c90340750407140500c1191442e40039032000c1c90120340c0e8a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 357105638 1250 357104388 357104413
    0x12050702090f0f010308071506181a130b0a030210020a03080a0506060a03110d090b2202030a02040c0909020406021614030c090a09020d0f0201270b030a0608030c 71
    0x1920070303402400100d0494803428801009101c42c1d80501008046d8140003d00505001c128030f0664180c1d490074070180205901c0b00041c48148031f500102d40d60481c1083c901000341c0026842c05520040040d200f0483d20000700200030180540b0b101ca140c00c080001408000340e111000c01d140840c0d9036030010441014646002030030a28010030500400e86000301313006041c3e4901c81143d800e295149004119000c982c008a480d43c460040d0803c092450500841d04010038020144e1017122030085820702030100c40e880703481c4098a406d0007585030700300e007411100600e840d600040c0c02c05030782d1030403085040e01ca0004030100da0140d009074000d80d0000a2801c0c45c0388007254108d014140c09526255134440d0500880ea5603034001c01114030400103030000a15440d200c0c1c1c4003a101307540041007070300800d109040c42c0113035a800c51400e81c0011510010350030700f40700d035102d1600f80c1a40d81d41904503c0f86010744940003a0070240c140b00019854403000288030305d00304080c1203801d8140024081c140c0608 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 357106888 1250 357105638 357105649
    0x18020a0801060906080708100b03090a020114040f0e0a0e0609010f060b0f030f07030b0312071104020c03070b0c0708030114010905041b05090f1002100e0106030b160c12050702 77
    0x581c0240b040042051040c07083c41d0b0b00909039600400f0703d040c00e9010351101c9088114881060b088031502c000d0210802501220015a11024034001c0c1c8030701000800010070103050740304074050381c04400c0224000300300c103d8403000e089600c0444568001009000a074050381007410942d0f0000960b03444466207441d28a03c0d118000091100d5a500e83c03400b0803000000610f40402021803d00c54007901c0003841081c040d0b0495019208002c0581d80300328085111040e441d00509030a440d003d15114070308140782024421103886050100040d401c02034260707031303584000310b000700340d00801c00c3c05000c8040001c801c0400ba6002e0b2070304843e0140d00f9440c50000401c1c079201580080c3c8228246a10000302c03010380070703990340310851602d403007681c41110070041020803411060b003a8003d00410700d00c1400d1540070580f614264414081804072282c03240040d400e85d142400090001592240410705c1000070a50204d48401c00e4100b10703c00c14100d444800007082c0e40c003001c20108000007542c00c11403414 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 357108138 1250 357106888 357106891
    0x313050609240d14130210030608120c12160807030c0204140106030b09100909021903080405030f0a030f0e0d20030d09030f0b091f0204090612240618020a08 69
    0x39003084d00e040c0c6030441d5102104111000301a00820b1010010805607200c4d800003c0a0034080084400c001c0c91680002c00307a50007900454100d010b6003450803d07401c23948044442002801d000c10400c4281c6460b02c070080d47c4620421418419800c10038001038841e03000c1e040140c5003400700c44c8002c0d131500314048c066605410b0355a121700010000c000d030300c04030801d220041e503910040000d0b0840c19840456005105000300c40c0410300c8181000003004600001002610007d500b03a400700382d260b0f10415a1503d43c4000103001c19417450b2888605e17803140082d003c1c00d00c4001c1c4180a40e9003561180403c0070940c2160210484200b040491b050400f080000303024125454441d88061440c0c13180300450210307010041c81c9914600208242000c104804040c51201e1900400041410f00c0501c3c001d620910900b45082d0030440b00050321242030304c00c0d1862940185e101680c018150340176248080300140065012a03a800000c6145000342c452980c0400c10b0b003100580e102ea8002000d09030850 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 357109388 1250 357108138 357108161
    0x12050c0304021807051210030516180b0a05040c09090507051e0d0213060c020109060f020c0904060f020a031e020a05160201032a0f020313050609240d 66
    0x10801e2000584a0300c040b44042c0d0a5050a5030705511000d8040302c541c441c1d0165004803c0662082c041480d0702c0d2420034048911460850304021409040c0b040074140707600c11004085007203071003442684a10b03041500741010040c0503c46081c0c40b5000141280c0390a00b000340007450809050000c060281f05140d00f010b000c2c10308170b040c03803240040402048100d880e10f500246001c126250141d0315601503941c51341c1403209000c91a0b454000040000c81c6000041c3d000803989180040c2c0c0c40e0003110111045000c03540544a03140303110040c8502d8200140c402c48109580342904004101c9503c0a00343c54421551b010401220f0f050b5002a440a680700d15a51a4410001c0342d01700d9801c0070880b40010a9000740800000241c00140d0040075580500e41e0380c1618a0004401400d00f9400054030138074a44600f1200407994804903a01d0040c41446181c8081c0603d0a004914004018004560008094081040c4502c00c41004980008020300e211100440c0c204141e60803030107a008401c030f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 357110638 1250 357109388 357109411
    0x10b0a0e390d021605030a031b0503040f030e0604090c080109060501022508030304060501061701031e080f040b03010305100b060306120118050303150306090717030c07061205 77
    0x61039018407000d503052540140c080301400140001c20380c09282c0594040380c000b0390114089010700d00f03100d6203d40c007204038540002d18041c00c2e04401820b611184030880110b90704c80d419961103640c1c00304002070042098043c80800f14513a51507070344400040003e010042c1c800303d0082600c1c0f801030820b007010b0700600980c90802e101800241d900080da00d00c0382c000d011510040301320115240c111200075800030030b1140400030801060280c1a0030a034101d0707040e50340722012003220032207503c10000d0a000040c030000f20b00740c00911000058001c1c807500380c041d03030605107040748125450003d544035a0001c0c2140708040010818418203120f00a504200b0070400e000b90300012001445600c00180042d10921021070030414843c400d5004901703130030a51224281000f0035040181d80da4004072140c0100c5901c0c05020800d5080105003940612102c0d40108000c2d4205907001c80000070700d12024140d848188a204980c5c43d040080100511458a502d1802580c401e03004043d69002420b104d0f564 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 357111888 1250 357110638 357110701
    0xf120c0405120a05151f090b010e06070f111306030f0209070203120f180607091701020a020712050c09040812070302091e0307081005060907021207060e010b0a0e 71
    0x24030101c0c450079614981e07081d078500303035484c020390440d0506c0c540c0303120058a04840012480c0911035104c400c2c240d900b620340041185800081061921408000804072240101c6400000d141c1800d0503480d440010642c02028055000c14401c4840d02c1e44260f4803445000b0240040d07080410301300f50003240c3c40c4055480d0130041c81c0845a0031710090308544038980c15800040407034000038100c4c4003034984402500c0607801c100e1001001414503002c1c44c201c5031040c40841d40410310500c00c03210300041940103040c40c0ca190141c1811048019141030300d0501450018080c0c55075051001485079200f0103807241c95000725411400601d10040c4044140351040040311035584d00c581e0700c2e412044200381c0060010f1400804642040000e503ca401ca030300c910355032006507a6003500840c0c4154402d41d01c0d0440340d945c0c00000c0380d65040c003078107154850700e003080400c0200305160002c030b40c0c0201001c00400c0605811010a140a446504c544d04255a141c140849103907002078201e00c8040c81050004e10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 357113138 1250 357111888 357111893
    0x7020303070e0d0b010603140c04081b150a0c15060e040807060603060f0b0103110a05120a180b0403110d0207120302010e0304090b090a0515060f120c0405120a 70
    0x4900c0060200014488550b00306641a0364040c40414903a034062580d4a09581d0342d1001343c0a0107080d0307583c132090001c0600182c1c00404201c1a202290344103801020320700b504049080c3c65054400150b500152080e01c600200d088250040c10000030329031392100307a01c0365420208608000c85a4604485041c01810410000070f2400d403500725400104031690f031007544c038000004104daa84010203c1e0306010403032103840b041303521420404000303072130500280b070501e40d50010502c1a860402c2c08070701c2c14019403c11086024149601056003200001d843d0354102e03140e00c058442c0d45e4100c4402501780b042000b0558481c0b4a01c1a0081d004000e0003c0c00d04900065112803140c015040005499209101418401d4100c94100da00303400a4030399881d1034a42007405007500c0c0515501031002c41c1c020851801551042038031030114640c198608403890300404c02c650380b004400e16000703042400050062190411101e0180e6031261141c1d64487c176000078007070000441506120380d90400c02a0f1f801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 357114388 1250 357113138 357113143
    0x11d0a120c0f061106071215030605060f01090b0d0207081c051b03090c01080916080d1112090d030905041d07080307170a03090b0702060103060b060405030a02010f05090d0c03020411030702 83
    0x42080300e40c02e00c01c17254400b0489580041c1140d07041e00c2d8031605001400412b2092079072005010b5542904d984004059480040d43c07050f100c0c0c42000d0f102c00d020884410311500c0c60b4060100c00f44514122840d0400744088100d0f10441340403c1038030243e84105104001914a5120b0340c40003180c1c88a60071441c1c000d14032074403200080300c804c0c14440c540c40013980558090214040030200b11807901540e54031172031103a56a52079024003902140c140684451408800213101400c2004800600c6c540860035003404445160003600702e003804444200401c4940d50780c0644031800c800440340c2040b010310303007038624a002c000d80c0c0403850680080060b131000c180f850740645030451140c441240d13244203c0d242240140106c400140442e0050024440802e030b000c01e031035040300e000325424003842c2641d0080048904c154800c0030740c56404a0901e40c01540152100000035002d810228123180c80344020031983c2803850422a0440b01004003803045241c0780c40380710000314040e403000c0d08502d481d09000e075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 357115638 1250 357114388 357114391
    0x302010f031a1009081902151e0f0307120203060a030308060a0324060503010c0503270609010902130b0105040e04051f020a0815011d0a120c0f061106 66
    0x80544510305107010102d8078090b02c1410a0191565080700c90407800202400e0103805210340502990000c035100c29880f6070011a450303001045141071200c10101000d25502c20000450a10015408440c01c0c0d0a100c02030001441002010307036a0f071a100400801e50350902c070707074403040500c140140480c548540f070826003500e9040c00c02440e0703510b43d60300168003c003c55000421448410401c0f0340e2007091880f0701060702e04400070a000e01c6844100301400d80301c40c0840d10001910500000303941c0203600c9001c8800e441c000e00c122000743e100101c2141440005c442d9030b07000c1e030b465250860031414081c890584100040404100256240000824a214512882602040030320106007809401e201502103109902441c8016a50749182078020f9000f20b000c80303000c90841000120148170312062a03140c460142d4403d02131702480c00103c0c0302104c00b81b49d495080000035002003104c46401610010b0316020b40c0b06a0324280c0342010344200340109402c040c0c108100d1100c0c1f51038040b40080c940303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 357116888 1250 357115638 357115667
    0x81501020708101a060301030c0302120601050609041a030f07180e0c04090203240a0612110603090c0d081b030408070e06150313050105071b060b06040503120a03060f030201 76
    0x1185003076290100000c00d80100c00c107076902110020001040001e0709c18000100d920a80d0445807079400e801c031040d1211001d1143c15081320341040024501c0c540396101c004140a101a885140d81c00403010038988a040c101c4480140d000350000c0c051405504449114007a4000c002d00610440d0011240c840c070340c4801460143d5200c0e42d01104665080c0004000c120124404035804030704984184001c507404c4e90b00c210620700d001c0700030034003806d01d8040340d1643c0d41055400c03824000d1308062105035800108900300c14001c02540074416981c1000040700c1c1c9004036030143d1200c09845000d03520300c0103901504040d07401003000308403441c0c01040a104541000c1c200351215556180425140f00c003231000c54850510000c20800c0e4183c084c0c151120032400707400200055030362920203507802c50b6818540358982c42c640c42c044001640030341162002090281c1b5003030409a868010900d0101100030715084103001040d801800c3d9494400d40e00200180b10341160291705e50b40000c2c0c8200c0c0c142900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 357118138 1250 357116888 357116891
    0x3080a0603170a140c010510060e1012110f0903060f061f0909050a020a12060b1209010f36020d081b0706030903030f02070b06060d180308150102070810 67
    0xf80c101050240d81448802c00c0c0062540e0381d1409100d0100340244022105c1c40611a054900803480c1407103003400304c5002c1c00140500c851140d03034800039101e07914000b062310380090715055290280030f8018007401c41c01c00c8400346c00d0b0b10345d00000101420104000c01c00f51480c17585804104181c0d81c3d5044c00d14803410410801802804810403c945810319034101056640c208018451000144e50003081c5c00840c0b503950000125a108498003510407502c02d003030380c0d00014003046404039011041d881d0050149000000d101c0804201b08055451100842d01c0144a980030180d03059011480c02043d040e503070824001d07145590f0300040c0d1100c1a03c034060810600030540381c00c100c0c40081c1034100c5e94610310460f0036243d80c0702e000802800759104120000713801c22008800c101c0a0740281c8050b2907012044001075910941406469003104012101c80d0391a242c103c000314891021a1070f803030b4026030380d80b000b41ca0301204000c601003c0351489070442d4440c05007084411801309814101100c1c1000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 357119388 1250 357118138 357118147
    0x51903030b0901120203060703060515180a140a060c020306160c050f0d020c030304180c0203160503041403030a080105011803020316080c0d050606011209060c02010903080a060317 79
    0x80480041203440a00d582003480c403000460b110a0400300075040a100b10201d440b01d90303441d40c048041e1045480b42c00d80152248071105603c44075203018040650b14281c0c24408001c0610000b4001010f0b0780c41502c240400000194240c2040c1c0a107202900d16030900d6a01d6610381c0e030109035600d074020003005401081d0b5042404c2644900360310340c48140c020702100d2450b000c020f880b42d100c04110341c0400242c0302d10310311540d070f6003408000d9070111170f681c3e100d0800000750081510090042034020400318002044a8036040c00c45a440c0c03054507010300c0085854504159090301c5141c001c44045100343c0c424040392403010ba000701202e044d1078082c0303020001d0207985074a140c0d10141ca508001d505004120200ba1160b40da000300100700c541c03030411104469044024003005196120000d45190482000a203155008031201000700308040000103080b402a1120070807941d6022001005035151100c84090641c0301c0c07009904020703c400c0400c90741e80380d90344a040d00002240302c05c01c00301d00402c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 357120638 1250 357119388 357119393
    0x9020102250501180e18011a0609060c0106120c030308060936030c06090d08010323120a050a0207410d0c0f080d0f03020702040b19030605060603040519 67
    0x204032800170902000e1802c800d0a1035070111110040b1200342070203a61821240c0103101c1440914801c2e802d030083c02c070f1480d000b608828040e2a903c4640b40050964031090001030b815401851298198081c0000882860452170010182d00700907055a2040b9a42410b01c003102d14540e014210300900c100c42954a44070805c4c20518882889994054038000410010080840818483e115106503010756000c01c008803002e8404032028000600210f400003000d03801525040301d050b4510143c0c0302202c203048004070780c403090b55004e2111080010b00c0400ea842207241c0402280c0054041c0800c400c80213594458080010038641651400c200000c42d06014032050b42c840320001400041e01802c1d80751a10308003110001550301c0781a154a40c5404d0010701c0c820003089e147d8052119039a50158051140340450294000d603209903800f5613100646801c607604d011000c0d4207102c040700d0030880580303103040076012180020985400780c1e030100100700c0000c40114109065404140450130900880e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 357121888 1250 357120638 357120677
    0x601120605041a0405010807060e0108100308041212090602030a18120b1e070c0201031d060103060501060f110a02010f1101020307082401170c070c0909020102250501 73
    0x181d01481c0c009203003003003020300b85203484407002e0100425503040c00207982c0e41e40655a200c11601c1400c00094201010351850362003224401d0f00180d501c1d0306041d41c0c41d26502c541801c0e80c031541c00804004090545601008034074020040780d0316050429540b410f00d843c4000e5224411403940208201c48400c07005c2c0610305055401015240d07410284503214818600f48a03031038400c1d990000c51007034201d41c00301c80d500041000d910490913640d0380e000866803580190041d00c141c0d40c00c95021001201c1051610004005060003507005400c042555490600003400580620007000108095240d94805140d00040c800795a540c1c2843d040d1003403064868200c901c003484146054880d4000000d02c0f03005030b8020780309030003680382460245d0300ea0240030f01303904600d2030350300b255012031141c0c0c10401c03140c0149205194092401d101031858001c044d5200092483d030b0350017140d40e4030707502d010000940d40d04210b2030b1010000035184508802d01c490122030320321000d20985040000000d02e252400c100c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 357123138 1250 357121888 357121901
    0x610090c020f1006080106080d140702060c010504060f1b14090102070b0c03090108061e040506040e10090b010902030f22020627060f04090216020a03051f020f03060112 74
    0x980152000100000f8100000c0c04c81803280002541c00d0a8000c65881800308008654000e20b0312088101400420301501e15003240c20107070703841134050103201c0c101c50080c000c1e640310303d20490000806810140b5035601b1210141004101501c000c42282d114542118160100c1210307008650346643c00d2500407842c00b0003640101e0901040400c4650010100201a05c1c07509803d881340c02c00e80d41d50a0900c10340100c01d8010003d01c40000f2107890240c1425403205801c41c20141c4003158070402070920b40e1501030f11841c3d05604a0380e410010080c00f90a00c442809032400c82e109525504210a00b00d0306d0b80009001c10290100f2002044444c910a48102005540c0901001c2d00e4410042107c17a000d041500006911100c8180e0811103180003c110b0308441d06a1100c142000e00703003182000250070001c12006103a0000000802683d075000100e80254481e400074614520403000d0072050380880c0200c81b10607401030104a401d0304004d0282c0e0340c00300003860a414044c9101403201d024060 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 357124388 1250 357123138 357123163
    0x30603121b032802010203060105190903061e0f0209090417070204050f070f030c0206070e0126092503030e040f1407030605090906010509100f1202010807020610090c02 74
    0x10004620b200000c4901060f9680c100b68580c0c0107891050040607400d030701c0100c400d18006041003240307451030030b0a111031442150452406003c2d4070b072642c4c0c51504483c60484406201c8a516220031102034450289405460300d1442c01d6060030243c801181c019140507000514a01d0022040801c0141038001c0c0d4415540003041480981402105080e061600361600340001d080751411080d0ba5001c4d00a8042d4214581e00404641d0380f0704d401151281c01c01441581007242500c07440c0d861211000300c000c1070320494042c40e0030034149840107500d04100c880d407070140c400580301002040b2410880440440e0b400d410100c0116800d6800100100b061200381c5502c2031404402008401651008a20404240e1410440c407500c1c1d4003000101901201c410213a90300080040c08241010580c0c182c0000d882d02001c0b01d5562240c00104140c1e1081d0460703c500c4183c590640251360f400910306400c11070b94009841582080d8026002010540c0122041281c42d0381da502140c0d0300c03c05c552540c462 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 357125638 1250 357124388 357124393
    0x402040b031c0c0b07050313111302070c050301050612070e271b0409080d0c030b030303010305030304060b09010b16050717060109060f26010f0207030302130605030603121b 76
    0x18040b00740a03000c801120800c0e11322201070000141194010003c9902698003898803c018010940d24040d0750030303100d00c0d402d4011101e0040050741e030480e40060041d641c85078100710441c904080030b041c00c4650040c4102c1c410f2600e0741d0111240040031800c0001d0380c2055499016030340d120014044105504110103c1d031025480c115503440c00b0101e03c02448007850400007000da50003400b00310070384205e00c50207020b94804008002200704940c2c010208592242000709010b56074000190441c4c100340d00c1900c080e08000100800c004e22441260031400040b203100b44a5414060714400354010b49007c6d14050020b440f58400744031080103072000502c0c440e610604000c200d0494240c4800b801e200300b80080b0f00780000414104403c00c41041a00d0100c42c03d141d2100c200c440103800030590b182c19003c00e5599410001d170000340307400181105030003600d01598460842c40e100720f10100030792112040000030320a02030240d501249482640000e0495262203400b581407070190304210307000801451 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 357126888 1250 357125638 357125683
    0x9021c050a030f0e060a08090735011103040303021308010f0204060206160f12290f030633030307030e0a0e0c030609070e030d0203130603060e0402040b03 68
    0x503001030310a55030307407007650307008a00650102c1c01d4034060b581c8407000717610010074030411410921596810f40d200c00600125030102e565401a20300c1d10201c116a031221300012889601e40c151616040c45030003110400030042e1000011645003640800b40c4020109030b00007965101c00842001020082c01452000b045822018600c0c01c000758814442c0c1701c050b01035100020651204002c450413000403907200c112840c11007140448114103c0d01010b040607070750352483d00491a8038004844080c01c10200c0503944110403003003000030b84140285074032070303400b0604004440300403813070030750f00850a1014030080640c0c00720740e00000d035402141a501071002040f1101070651140603505440000c0d41c0311001582c841320a4040548100c0d03c80c02505010008144941010b0f22495800400e07460811621002c410019042c6414451800010b91010611210700030b06011038000038056070404114031498440803102020000304003078400d540d17801c207020300da031420710000107162000850207010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 357128138 1250 357126888 357126893
    0x1060206100b0c0c130516050903060c1608030a0518030703140a02030702091303031404050c060f041e090608010218040b0604050a06050403060606050f09040c03110f030406050903070c0909021c 85
    0x620044910501f40b003074040c0100b0300c160090080b20780da610050003618140c0e440031281e40c510f0344104d40e442c600c8610704840102080113000694005c00d0042800704841c20108a9481c4a6100c1c021140e42900104a40130010780c20625410441d2001914991500101d4000f641103004d0140080d410841303c0b002c210307056200c4044000d1040c4613071010060305040d0070300c5030b1040d401110010b1032680204500d014616040001d450800002da0180785016110781d8840c00800c202c1e01c9401c0001540c11040c48004540e010301005804544001c5080c001c1c00303814107140142c0c200b02540629600c2c21800e40a44841c4200e8000d45805080300200c0ea5503410004e003640d02c1848150303130340c0c2d1034060b01041c294850800c80d0b591000034014103041200b039504002c014824520100c040c1a0b0794080c0380b41c1c2c01c144a02030b190751003805460903141d29140c1420400d03030700000c1c80c01c03c00e40c0080016900050031502d0f000281c5045a40000340302260307101045606292008104181038901101c004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 357129388 1250 357128138 357128141
    0x4170a0806030f0316060b06040f080c010806060a0e0d020d0803070504090e16030209091507030207110f060f07051f0603063b0106091103090601060206100b0c0c13 72
    0x200810b90442c0d071400380d41d0310055164040c41010100003403048508078041070040d01b007144513500003007410740b40551b224810001d141d0b96501130409a004103450024070360300000b0b050f038000b1003500c3c2c60340750200642004050038011800d441c440c2030821010019505d0f18620501800e0340040615624140010058099041071040307019860500d0f06500e04024040b95061111b104a81040062429582000f00b5a10001c02521980c480e00201c0450704100f40001c5024400c6910010f0744c0d0000790411024003171b03003100d181e4021015600c0580058440b9000c43c0ea80081120405031142640c1ca4464280140c424a54040c016184030b4142c00030f4165005208407442010100860041d1140b541c9041c030990801c5214100f00a408118008000514600c5201e500000040681d1680380520031940c0d210b1158a2040c0040200824103508015036409803445000800d95450185030241c50112680210710d2200f6003c03506401c1c8100070050014100e40040bc00300107000004907010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 357130638 1250 357129388 357129391
    0x20601030c06020f0d0e0303070209102916030203130e07080f090606130b0324010e010b090618121605010c020d06090203190506090601052704170a08 66
    0x2150041c0401e40024450300000d054082c0a400c400134020301100003034240c031408948406240c050108119203401680c60800541c410002c402c08680c8040c00c00d141e4108a040900b401c01100750034900100c00c0b00039481c1915403280351100748810f14051890124110700a0f0384c2c4010b040c031303890700b0081151210303803003954817406013560b4101543e503412030140c038006402d50b00f085031500813034007080d180d00f4490344610207203d009030042545030507100407e2802a07050260001c480340346107123070100c100300d090450040000e11280c8205506100e0000d010344140910a03214001c00a80f0202e60910b50a00240b6640010f052456115040c001d06482d5008908802c084800001004c0380c00c0d0b001d90207040f81a034001d40229080f03e013558031076000344a03402040ea03061040b1030005a2006109010180c001d102c0c4000e04294140712000340e01d444e0068110a214a100d8518080741d21050309003460300c00d0050200d00e2007510750341082c5203034800648800310100c0d030009281c4041600403002c2c9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 357131888 1250 357130638 357130643
    0x106030509011503031b140f060a061719061503080d2009090c13080307060507020105061f2102040e0903090603071101020d0c0f03050a111603120c02060103 69
    0x900402c8030784943c00a401950740001004904a8210f0940d0768100c2401d01c0b070740c0744c1301c0c2c0300e21042d81c034240010b1441c2040f08112403941e980701501704080740826006200080001d510784e00300c8104000c80044c0c6840610341e000001443e110610814050540c210b4000903046020300d50f803058403410805801c0d4448241c0e48840360401031080b02458003140701100003448490b51505100700d000801802c01400b90444035403c400b0f20640000c0794600b4410710040041c400150b681c1c0d0850f14000d801c3c7d07980141307401c0941e450202084416210008a046031081c03e0b48910240440300400741c0e00c154920410300210f441d240312036105501641e000308117030340c40c150707002d0607544d200350300e00e42d0380d02c2507a8500e90000f5050010940c2c49001e401134040480c02c20002505242a11102d1012640001c3d14207002032401070145000507011700c01e16411529141081c4105c480803a09100c0c9407195030030b6582200da406200c0c0080c90f101758484503044401240c18007001460360b40c0295101c90a0105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 357133138 1250 357131888 357131891
    0x11070c0e060307060516020406080d02030a0207080d081819060e15011206020306150c0604200109030201080a02040317071a070e09061c061401061d0607020604030209010603050901 79
    0x204110b4500010128111691552514503041e203006096a900c01a5282241c2040e25190007041e885001c0c0800811186540e000b140c56900d40c10000740b070f141071988120aa41c003c10301d0003484039440100c10307502c40b2944001407101198204a20b01d881012b003200310209803005801d40803c403181d081214203d03c24803c031406190000c83e91001c1260070720646846031180502d180000710250065035014030700078918000d8007012034400308503602031081c24040d9040707041084200a1b46640410707046138190713200c41c5250040300010f007001d2a103000c0039040c0114880000d81e01c044980444010703580c444499008030550444920158002000848250001c2c03840419035220422215200d845070380e440254aa50410500001020250400f40c024031840d8400c04000440f804500480e84a8500001da03d400700c040e0b01403403401a00003d04101d0820b1200e2041d6450b5020020040822202c040c0e0715503203440003520901c2a0b5000075044255107000041540d010343c01303d449403a06000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 357134388 1250 357133138 357133141
    0x18050102010209060405120f0a05030d051b0904090c0f120501060927050309060a110d1b0605060d061b080a0203040c060509011418150414060c0111070c0e 68
    0x1a4240e003e50100c1e0707500180140300400c01841d1011480360030a60380c105455580b121000b501c2d04200700b000096802d41c0c80024200e41d0b090040c4100c0c0d500420f10b00c2060300d602d03a0040100e069104042d2040d2041d5103640c000d80c280300802500c0c20003400392518640c1c009980c0c0c1000000081c16000907a0a546030000c00100000c06000719004000c80001e10901a500701c001c40c0f80c40300300140141d030070348070a21100c0070945843c001810b8409941e00d544158900f07903038415151510000100041261600101110f44060628441e206a104202242c983d03114030102d209002c00034000b0b010242440c5029141d50403045990b00400c8260b62000e0640d601d8800490603880f05540040014a040d001004030f1489000a4070240300149014441051403450300402c5401c0082540b5281c0007030040d8280c0391520b10301445039880810b2056081629205002007216800030844c0d00607180000e10344280f0500b1340c0f06406104403d0783c15500d0721164140340445411038003410000e6641c0702d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 357135638 1250 357134388 357134399
    0x91009060e01080717030d090311060a0e060c210c03100602031303080715142212111501030b07030e0a110411040806010b09010e0904030207030f02061918 68
    0x99114140d0710840f0060012a24240652102400604602025010605c131a6080c103100f07000d1950300c0ea0190780c540c42412444034150f4105880070300501003080c600380e0038014611010454039030004a11603138988600229a8034241c084200c421030030040194003c000140702d10a01543c001d072003944104005a0321607105a0340e80c42841442030001030f030b11300c0402c005a0202c006100303682c460f8680d801070320445c0a000b01038031110012035081c4007000d02000304070800e01028408207400e400149408560ba900c3e64034902c04550306100c2044011031050940307000c1080030811170340d2401004011580e403400e02c0e80d01c44900792034540029003410b03410030080038002003804516030454a07090f520403018042000030010540003907604901031100085090050005600822098400998032201c207400180b44607440d07420a407140000d4018032003c29070008113a01540d6002e070008903040303000e000040003401a03c0241e034110710700c21101c0c0d00e4a90302c551250030220600001d201d400c0c1d02d49 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 357136888 1250 357135638 357135659
    0x9040e010e06010e01060801090f0e0307060c020c060a080118060302060d050a0c0c080a2a11211f150320010f0e01030f060e04240603020a0b030403020c09100906 71
    0x6c0c40744400140100c00180701d401142e60100c0034107210b02d00c00165003001e50f40c4a50460300201e0f4180d07582c99407051014180e64040c040290f8680044850368980540c00b000549500c4040c0550300c2c4020000034824010041588110081c41c0c00804013500c96074211140d101514049454000c444e0411038411001e0b030080302200d0099a100c102c00d801c28000d8036040385e050510440100a61401080c00d080c050b400c44100c668450145134806800c06800003408844200d0301d481100c40035440e8601d0318440b0011900d070b982c1515258105401d80405c5018002a02450000740e10200410500000300320780d6801e64180302600341c0c540c050300c542c0b000054889441e0392404801144020f1041140307507200303a0040c0c0c030b072906050f40051559220304101c1c8a45100f200e048072240514403011440d00390400544080d4001040d00303010341402c40c0c1c00315400f0761071449108000200840410300300b600900c4118580c007000351002e0741525040c071580341e4903401c52160341c400d245400408189800780703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 357138138 1250 357136888 357136891
    0x40c0311060406210b0603091b030307050304050111010204091505130b0303090d1a04081209030c0307080a051b011d0109211205270a0f060e010209040e010e06010e 72
    0x240c031801c42c3d43c10310a280005104c0011240c1d41c001d0382c0c2d0010324803141d0f1158041d5000d011804014011030403905a903484014464000511a60061004400040c4000125400e0b900203280583e0040c0c403404005019004a40040303c8841c200b071810482e10300c1d51300c0e105044a604480f6044200d0035004c801007141c8241440c1c54143e04100101700300c034144190003140310341c414070040a4805101e17621050038002070f01d04413400d00000800c0002c421344810415008806500030314506003540e10390076541c1c031a0060083c411003010a14944050191081d52000001c64000c0d0039582070905245009142c0e5455228141c00400c1c00f50030341680500c104000c0035400030180150826181d80f5980109213243d0400800200b4030401102c5401406510f001e1841c4e2540f40e000304502d811105003030001110a00c00542c408940e50021501c48500d042582e40c10080024100c80c042e000140603100b002c40140d040b41c14480b01243e140c2055000c40c16100070103040d5a81030340c0362150340781c00020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 357139388 1250 357138138 357138149
    0x30504020f09060109050909060901150b071106070503070605011a0906090d050a020d11150307050d050a0b0312040f050301090210181a0c101e0e010e0303040c03110604 74
    0x40c10801d01c1040d0622202198000105040c00340d03909540304001424244201d602807a2904442c040c444441300901134181c803031145074100c40c80c1505084190400b4000c40c80b002c0c10010704600784002d036403078002c215981140c01009407a69030301c95091000142c0030030b00c5055460009100d00054540200040c3e4180450040009152142c0c038020403003224002803090300c01c0e0203694072910042e41c03a02480300030140b1a41c8030300c200810480400c06c0c1e21500700c40e01038510b81c042042140aa501004840d0f0f076800c00b041c0010a038855031060030007015402d84071605441804906045422444054000c0702e05030134840e80183d844400345400c0e0740713034000000d41204a012129080714001e800089000320741010358102180e40d8031143c0d01040d1a5014070700300e0700300011005071001c401d0010928001514506100800280401d41782207d148002400c0c0ca03a81c0b0420281d80c01400c0d04400b0413403980d0b1048a13160f0030305003000c00c104c400301e1100719101040009000300d1810f005085d1000c81e403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 357140638 1250 357139388 357139399
    0xf0a090f061d0f04021603090501050315090714041701050a0209060313060209060a0302040501080a0912050c0a120e010f26040203160303030e010e070b030117030f03130c0603050402 80
    0x2103074200756102e801020344010f5100410b0150115503032242d01c0a0241da042d500d2200c8100c10403424090081e05e9280c0113181003001c101304000d90910b0310a280400c0301d4003910014429602c030b071811a40300c074041441c4001e07920005400960920412031009080c8450b20003000380d0307143c200f410300c224811003811a402c083c003800004e8042000484d080140f40c01140d01520b004400800100c95a20100b05180032aa020505002c20b50780810600c0e40144041400c1100300107a89440300d115000b8480801003100000d40c8003039a680c03e0001c00e0f040799101c22001d0115200c044044d00c51086485030a0000b10400c020056503840341c9040700c22185414107104c0002c6ca11000d64000d42c4000304180c0c2c051184e0480041403040c84520b11005601964000420300e030b0302001c0d40d0a403a120304000d00940c1c032400d4280140b403d03510489044414503c1d083d106040000103c600394019441401441d00d130100030810040e501544040c9030071710843c50f901c111030300d92505804648007039034040d4100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 357141888 1250 357140638 357140657
    0xd080918181c140c1212070804020f060a0e0a090504050f0303040b060f121b04060506040f0e0a06080d0e010f0f0f0e010315091406010e0616170f0a090f06 68
    0x690080f4118640010711558251900f4496101c0d10f1400c260b0740b0f25800c14610000e0003041414000b641c06401c00c00d189484070460420390000749080343c090b60100d114a030b00081c2d0348040c1d0b028841c002001840035144502481c3d95a005030010b1008460030749540c01201e0750354178426002302c00c9921035540a24140390f21b40b9000d06000300c3d480095030040c0c10040c040000d1403d56020007000720380c2441e001d0018582078100050100f914010f038045c9020362000d01040c002411454491012340710600b820701e03203540e0f4007400346003e401c0715480001341e80184204041010744c440c04041130a88282c0341c00c2144403265401312096181201c3c0080000d8029034800d501038400c5801c08440c0b00305140109240c2480702d0000314001d0240d1040a10950f0307201403000340c2c840003800b581d100320242031142c045000d40e4080f1354a0301c40c40018840404003d500302042000016510101c1107004802a459881400da035a02e164401c804a00118400308030001712103d584040100b55502d558403000071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 357143138 1250 357141888 357141943
    0x1509050703030e030a0b0405010209030c0109210c12050604110117040201051b0d11070e01030c171006030305070b1302030309130e0a0609120311090d08091818 70
    0x15601000300c161341400340071103100110719840205401513000d00c2c001690b81180313a00305803510420203035060501c00c98010070042010741403030b0010342d5174810700d00d2810301d0030b03074909048190b07104e030846090003000755400c009010001078030300e00c02c41c0309000c3c654071500a000192141003550200100050064000500551086010340305503e83c026586d14a2008030141b04d04003401c000c550400540d640b2500c101f0450100448001084150401125035046407908070181d1b80e50301442c580c0b0070b000054291510b90412a001581c40402d4080021580b246801800c5a0141006a41805501c5e0100345003400b4040d800f003110b98001d00440c6000c0c01c80d400c1c04041c1203003d004410710b5a80d1b46d11000d140000303001e01200113216007800164400b052914403600f581c40ea2480c0c04141c545556001c005580300100c0b440c0700411034010190291626100c042482182c09a507049804e99162005140d00300c0e217403031f0003200c000000c0046a404002d04569a9648130450428000142000e500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 357144388 1250 357143138 357143147
    0x3170c0303180a2f090910020703140403060209090915010314030c12030108070b030c03041106090402070c050406050d110d03170103030f030c05090d150f0e01020403150905070303 79
    0x103204412415560504403d480e8081d400449401503513110001000110300c000400c42c21003a4074404850391440c40c200390148954840c074403407900d180580e00203061800e0500803083e03c540035111154107660b40c4c1c1c580c548100079400a03504180140b1034040450030110021441081c1da05020030381070020307841c5403140c40e03254540f4115040717240010010745000c88000c0c010303400d00d880941c2c0590b560f945000a8249401465445040f10310f10500500101800741d004a98000d074011b000c0510005c40b001c00a1440d1290813050390303215200081c680704104603560301c2c0c022248121020403942c1d40c1c07400ac0c00700c04018403000800c5002003c40d6510b503440e141200154040c02880c0c9180d00e40e00e50028910240e03004e070000d4012a11200c94240300a906014000080d1018981581403250312030105202882400e8002d0054081841c45168003200b82e00c00103440300f11041c18445912000e000c01d000350320030300080e40c0360100c00403c0d8400760024043e0b9607005a02c81c005004007403030350710100e4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 357145638 1250 357144388 357144421
    0x61401032d06120c030510050405151009051306060602030a05040302120106030204020c1c0e010806100311160605090a080306060307030f050403030b1206090d032007030903170c0303 80
    0x71005603036150100c2d18024101c510380381c040c03042400041013400e5041c140c0c40c10050420120206041034204000980c0100d0100394654600c484bc22840c6c6490724800c074480b296402044c04549040c0c01c0140041c40e01404d5001700b030040350200100b40d2503100407a00c2e40302d000700400204000f0041080141000c81d400c1c0c3c90b101d200400050115101d0b400901030381e2101c10505896842480600015001d4008510b100d480f0350810101d55058040040c04940c0002c0c00c3d070348540002028002428081d401645503413010200003503030b950544032007440344626841d00303540c0c2e249804002a0018000150f1225468020b0f408030300b183e480400b0030031303140e0000b80220101600e9003000820b40c03d490086034005c4d4484d40300812040100d005000e90040e4003400068584d020000b84407070341c800458000040f040b40d140110f081054009001c9841c2ca0a0a185101620009400d024185d004481c1d01c01d603407165185000c5a100c954010040380254000012503400800c04100c0040790303644801d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 357146888 1250 357145638 357145721
    0x121930020c011b0209070e130218010e0d050105012c19020c120315100804020d0201030e0a05030301030b0709061e0507060b060c06040312090b04110604050307080106140103 76
    0x40c00403190f0f44e408a0005034003640c0c0040130405181c1401110b02e8010707000f600c1d60384950821401d110308801040040e526200800d4140600081c8245c19a11858100f0800d581c02400a1255503550f80b44d51100300c425181014030142003250624042d847c0c409458040c980380120407024850b240d4650b0001e511a400c403220b90b203c0d44d8050b0040b201180042c44c420840d80c4c083c10b4000800c0b1003070241d114008401c0c8403c0085d60802c0100513078503102940c40440d020710740055551612006685007080503900981a03210200000041210700e07110644907a0b8944e48000c00e060b0b42d0722013034910000300705500008800100310110f240d0f00caa409003052034002c05003c81c01c04101c102260076070348090f80c0505143c200320200014550001100f14a032564103008104086071a1a03242c0314040181c0000c00003240c000e00d54074107507283c000361006424014140d070105c0390382d1079030140244180d10941c0c040c101201000747d000e6010740304030208419000c00f04242d002203030700c80000491865460 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 357148138 1250 357146888 357146927
    0x180301050603161a19021609230901020f0d0b030c0f01090b030403050f030a4505010f0c08010906081504061e1b0201150308040302121930020c01 64
    0x84015100c0600e0800c001d218298025010504800c00f03400102032094100307008d078a041c0324004402c04903ca03043d03c00603a00030403151454a51082081c0640302e0034100e4a003d001c0416245418201d55011401d10071040f02207809aa00d940c061050910041800601140314050200701c00c0300d2410007140e00c14460b00d041071522024000c4011541c20076141d0610040c0d50b41c001d07104482c00c1c9400d6034900042801c884003100038030080100081904c540540740c0340d50f50418101048425000038907401c007240c0050040322b201c041c0041c0f05401c01d03c100c4005d01e051060010b01404003054502c03000b0252030707a0003090b940e503849036406091801780c00b1601d09007a1180c82c1c4542424810000030000000300d03608a40c032100002070035180092481e2210b036420040410020b4030510403101102c4c0c0c103994414100c56510009411f040005000c8070b2140c3d040c400c000108407002c450340341400408800c164140c070250240364488082185007101503405945440c0702503001d2000e140b600e0075600f04c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 357149388 1250 357148138 357148147
    0x10b070f020d14150108280206070b1b03040308070813020d0606060f050c0703020f0a0b030a09033b0319080307090506070c050d06060b180301050603161a 68
    0x10490300e858001c2d05490f40c1081421102840700d0a02c0300c242101e40d0b80c455800d0650620829948403001080c0b4541c10412510102400c4640c45011039102c03a002001251155580d04100c0e80001d02102c10000c0c0c540020104103001c00e0b00410b5134003981d0166141e00c000d644295040d200d641001e07001d14a500091015000141d80303a9000c000136500c100b00c0800c0d00c2e03240510280c10110408129814024240014801c811000030a00200d9804440f407038851400c3e1000300f020140140c00c0810030301000070030864240700b40c0d00000c0105200350b807940820030702e100e890000021044220841204c2c2040c0c000081184d00302c407001d0207140102a107900c016441140c2125098a6400302c0e441c0c4000b00800c084c2c143c100007610001c02080e982c05150080729981d0b0481c0c0320050040e9841400d90100010501015503c140060071400c2c402a03901ca000003c8181c1018109500a100358200340c0011036030b0901060b8000483c0c008000200054200114051191140c55410030440030501 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 357150638 1250 357149388 357149393
    0x1b060f0a0c0f02040c0e030d0c0b06041505060406020c030601120201120b0120070e070801030515070e06120907060306050a05010e0409051615030c1b030306090f0b041407020303010b070f 82
    0x1250305c1098041d0703100c081c224040c050600d8100314603920700e1414041807000d0480410034401c4015408441200c0000b82d80191014801001e0125000a504090003050100f001c0d5000214000800011421111961790b96992140c003000344c42002800103050010107401d048160f000342041a205040371004043c0f001203a406030001034003640782c1a40160400c00403407000050058002c00d00c0d01c0c00c0511507055442d8580c3d41d4038021034804498001000140300c0c00e1003640d00506510005181640e81c80e600e50b48103219002c00d85142800703006401000644502034840c08040781c1000d000212861300d000019200181850000b0382c0054407082c450740000c0051100c481c80805030022204043e051103805440b9002011030a403e051806002c00511a041821380401d4a0840122070201e83d59186c210003514099100c807856070b080145026418140d0b03008480c400c0802c1d9800c1182022205444001080c107640c8500503030403c00051246442c0c030801006018003c60209180340c80da603 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 357151888 1250 357150638 357150641
    0xc0301050709090b060c031b07030b0403030f0f09150b040f02070f05060106110304120201050c010e031b03040e0609040201200705040f0b090f0a1d1b060f0a0c0f0204 73
    0x4441c04070028401c914180403d144038819116038800c2542e60905000a59050660781d105a00c070020116141040062640604100c0c0001071944502e4400060805140160160802c0300b12404142e08151a11010700390910078581c400d40c000400603510441c80740c80c0401440003000e81a040703500c40381500c0c0c00c560f02c0e00080491510400c0c0a14010003c0d042642c204071068201d1402c0050700f642403003904100200b035505841c6c010f404403105d076845100595280c41041d4001ba00e030350030800c01c240c40f224084043c145c00b500401c610305149206101e45a103074419802125030b9020f00102080b0755007004501140c0c090301c1030404010800500c3c0c7c0001c0851604958080ca5a0045c0800c0c4040d0403d4000c4418062004400744130014101d0001114410000c2c03040f82200462170009038a00360627007201d411500321005502e0325032040840207031502405925841130389201410f860351030900e0350850f0611807001e05414200350400108460040c0202c005a840d0000481d0f500c2c09a0b0b01ca = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 357153138 1250 357151888 357151891
    0x70e031c0e030a140c03070e0c0d0915092102060a0e01090c0b0307020d0e0603070f21050114010c050d0c1b1d06090108150402040e0d2316140c030105 66
    0x20b075404c81c0040140d80c3c2c40300d18000090340c529000c0d4124200c204480f071075098900f60000c9404408644405038100d40d9001003400381c1001d07040030070f100035551903a90507130300941d0224020b184009480640340350010407a0b000820b014016071204c00000c0000003aa03100d070054541080000c5076120030b58489841160b940d07004a03162400010511001035010040d40401b07085030304042c824078a10718001450760100500400c00d10032030601d00b55002c0d1043c80b0717400c5880245c1c00180140c100d0103003002300601090141c5000c0300700701c2001caa210742c000c0e14540c0386141e0103001407103010b24010707040703c80c40c6107154102d070301002401c00400340c4050050964040c011b401c484095410720740c400005d409502a1106000e8800d02c4014050110040383d10402104900c0b1508407545840c070220307000300190300d41c000182c010480308000c000c2d80005100380120881034a48c84580190200c0c3d00700e4495045c45210100c0514503035030004001c485080c1d1000c001500303881c0d00404001c0864250b910 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 357154388 1250 357153138 357153143
    0x50c060a020d032405010c0201020a1e0605060607121b0b01031103010b010e09160908010507110f061302090405031905030108010c050c0604030806060409021c05070e031c0e030a 78
    0x2e2442c03100140d152044070504c0d04901e40c41d00304c81164900c42903100c0300a0003154100030100e10800196402008840300c0246d01c00c0c0c1f1100b8613204402c6815260580300e500b190010300b0000400c08034540201511081c1e40c1112102c200740000303a06c1918800142d0201c603100341080391700580480d41e00340300c081c02140626078248c0b2b1070384500c040600312112156414140031070340f49915196210050416889007040218020fa0201140145d0300311a00d980b00315000c0d030901d420000515840341e0b0740e1a050600f181200d48844040d48401d4462074111240400501d0300800007016240c52184144c00078010410f0340d282040024080c44108a07400309907000c2400003004110060092090700c032014051310346070b0b0400c0900600c0c140c60300c50150016007000341c0032000c10481d9942c0c004070360040500c45003c541e0b46200081c00240e40d402c0d0488881010b1909002814840c0505910b03808450300802602401c1b08082e4040c2040e400041d0b05000c00804825508168804000c8056100d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 357155638 1250 357154388 357154393
    0x1305070207320306090d0302091207030501020403020103050622051803030703060810020f0d050c0408031603121e05040c050a17062203050a0302070f0b0612030313030309050c060a02 80
    0x1240d034100c160401c2c500000303540c0a640048108503e9480110f094083c1900c0c1d441c000d0703594040b07100040d812003a09032a80f04070b4042c0000000030014154000c100b201e02c01c3e00c0c1030205a80c0e2804222500f410b5900c0098001255140c0f10b110032403e500181c2e00c81240202100740f440d2121086146410403648100480d903142824800ac0000b0403a45000064205040d46004a4115004410f00031003403084040d513104c1010a0307180420405807000740c84000201c2c2e807211800c858a0030b003e6614182034020500384948405500b1403406090110005184805600b00c69200302c075009040040c016078800c120480085910b80d40d90010500401c440f0405030702e841c940860342d0341091000b400c0b070450001c10a8036908191505aa00c0d407a1a4150808a40f501c1c5405415406842203603402841b1a115504032003c10602c030300ad15002c1c1005442c165440c8601c414002c0e5a4401992201201075815460000003442504400c0b41d0710321038800d54000307060520102d0b039550040d000d80c00c00f42c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 357156888 1250 357155638 357155699
    0xa030f021902070803030603030403020d0f121d1507020904030e040c02240103030e0d0c08070b0301140904030806040207020a090e06070f02060103020d0807081c0c020f010501051305070207 83
    0xd80c2c10844403019003443d030007451840c1400c200182c2d4a200c2d501c4001c0c02501c420030000180f1440c1d29801c0d100f10303000290810071a4002000070444100051000d2401034115204251810181c84d41c030107400903031080f245800415001c125101000a10172010072808111042c0180c845020340d107804005a002040c134501a6160f1141c4603080c2411121050400d100410100e540054885403150080d608030307007200c0080c01c14032020b10550300100343c03902c1140303c0090b1440392080118100d564a254120703900300c4420800c0350410003501c0140000f145e82000c81c40500d000da0003400401d20050083c035805e03903241650001d480c505101c10905c0e401450030880215009920f1110301c1d080c0c0d03c05041035605543c009800c0180d96070f0041d0040c913001c20903004010300c03d03080b00c106102c0480310400084024040f0009840c03107200d600014040d840740c401880301305004060594a0050241803c10381d80200c24000f450001c01d2a0118402d1600029114000b1070f94542098103806105a40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 357158138 1250 357156888 357156937
    0x2030903040509130c09050645060f040c050c0f06010f06030504051c090f09050a1506021b0d0212060403030f181415010b04030b06310b030f0105040605070c0213020a030f02 76
    0x1d89c0015100c100d80720030341404020099441e000b012000d84011100003500302c0500c1c0003240c05000d0001c8000080c0f20b1003030355030a800000620756040b582d40807030700481191034000440568105a4008025600241d590360040384042901d6124411500c0e0980c0400d50f607034504152030107a540401c0b1269610018822000058010940350030507120510b4129840c061000799204d403040f0071040c0e841078100b4a002c0741c0d80e81c3c00751019125001045003900360400b070780c2c158a9400550381140864900329209034429802d0182c1030800420000e48040260281c80d0040d0340d0369440024000c030f016603111030303000100082d241030280002a1105840e40c2c210f107070a200201000e00454410301464400b455000100141807010440480e0714090034119102040b0141000140844c0d00d401401b50503411808154041c03441240585801d00154036540410742e05500b0091000e50005020f8182e00d1401030590000d05c40240c180c42d00061031300c2c4d0106884201c0e0882e02008080f81c80c250341c0c030341a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 357159388 1250 357158138 357158239
    0x1f09060515060d0c02100c2a050304120309030f050105060102011d192604090e01060f0b0d0b09090c1311040b0c0c03010c09051e01050912030d02030903040509130c090506 75
    0x2584901281c2c88c40010046407595541ca006038418903407010686101001058881d1781c1c580300550f0300500320940010300e4540f1a018001c12524680150b107403140345110488a4165600310b0307081d02010303104010203003024281984042e5801c2d0703801c06074036581c0282600d0074070303011030b41d607804080e05a1140e00300b103080c00c00d5510755200001d00b83c1c101141401040f500784ca00368104c88010580a1b91100300d61482c001030050b00f040c007030380108813000304940c00d01d0101c0c2c4034841d29800c480c01040301000242c0c41d800c4035040c8200128100c0f040c40140183d10b40399000385000750040046542000d021400179003900c034181911400502e1840c1c00300401d08213542100d004a0307160040220b0700561500003400b0b4019003003d81d215150002c0640c1d40d2690620441d003513035241700c1066581349021990795a42c0c1d4000d20800703000d03a28001c000381d694282640790785880c0b0380c007030a0401003a24051002024100c02750107658420b10503480c808400000ca2451513491114900c040540b400254a51a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 357160638 1250 357159388 357159437
    0x703060810060b12190c1809020f03060105130e07350c0a030608030720010504060f1805030d1706040b011b051f09060515060d0c02100c 60
    0xc510608150090060f800c03d20107a0b803080b84103c008800a0355803108202203d0036094548004518000c0c1103000b5940c461001542ca80701d001009001564907600c03401248500c3c82c00b6841884148080f80c0c0c02e45c4201c0042042c0c0c4080c41010200c20740314804148071000907174400c40400c440020440070f1204000f00724465144484901102103800b02561707941900c001d0901c40540000101000d106019601210150284108580c1c80d8442441c050200d00002c07050100d13003034503c00c100500796204100304e0b4250354050b41d69440500440a0913210000741c0c07091040b5242d8100b07004199030700d003004441402e000310340e551074111000900e01191510302408081c010b90512440c1c48440e6003190140c041402c500404002c2a4003c0c2060790910f5400d80c01032403c070003040c9040c10011066008134602d0b5004800c00c0101d5100d44482820303c0d5659001c03181c100c1400c0c08000b48a41d0941c1c8080c1c1014914010368081e50803284441003150003802030000403c821101d0451010840c40081c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 357161888 1250 357160638 357160663
    0x60901061401050c0a03080405012403141f02030c0f070b04060501090e0316050c03070b04080d0507031d030109060e0d020c0f0a030b0a0608010f140f010e0705070204090b07030608 79
    0x603441d00c002c0c40c0c451a05c5140d840b9010342406419000700c1e040240951220801e01140d5812251241c004445000314a8841c802607500b007801141c0c00054440103d010300c0d0480c0c026507007904050006c4401c04c082d400c003c0014410000502103c0c11100040004000103440350841113418a03161401c24101c40d010303004096503914040c0c0c1c50506460010480d84016690702e00500b0000151400601e4070500c40c52443d00360041d8500050200c2d000d10140095a01e1502500c41c0486040001c030344a0251060181c00141c0640f000d044844031003c1c10358a0f400040d00104076944240c07215002da4045001c07440ca02d600910100840c41e40c14081d0462100084a440d4100d4810800041055030280009041040310102040d81c44580d90321003402092400c000788103142a01c01907100409041c51031800d8500304e03d000805c900741d400708042c140d030f503566600c0304a500d501808070b89135000003008a130465600c4c0c10b10000714200c1e0001c18407803403031030307402088141c01c1608841c00d004841114 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 357163138 1250 357161888 357161897
    0x60e06040e0109050d0302090301020c07081c021203011802160803061005040e0708090a0c0618080607021203090102041e1d0c03011a0708030703060f0b07030c080714060901061401 79
    0x42c00011340c0118030900980243c1c6000358885080200081c024400c40001c00302c944541c0384d000441c101c0100d82014070300550801d502044841c2c1000381e0b103134901c072540c112003140304000600c070f10340c032219910000000c0300900508026880844400d03000c482c0c1c900b42c42411f804810481e0a11b02903261582c001c8061400078189403a08034010030402c00501b01400f0b00c074920b40054100c1104102c0c00044a4000440700c1c50b080d1742d490040e0000d00d80c0d0b0340d0151000e05130700d0041016080006e00c1800f8440030b0f4001c01e0612404050443c03950030113442c091080d5001c0200258840181301c0ca00000c4060785410380700c1c6031804c880b07010ac1c05c48007048a02807100400411401d124038201b524119031351502500b2044040e460b03d112644143c64005000305808810b0104aa6042d0300103415109481c220845064981c40f202d010b5010f040710013000940700d0315519000410f084c0c080c108080c8617500c00e64064032030314074041c200b8a0850750010035030f664030344c10131058400a00c45100c11b1001e090 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 357164388 1250 357163138 357163151
    0x70c050705010c0b01050f03161409130f0f0c17030409050f040c140a05040c0305040c080c06180d05070e240f040e0f01021b06010e28090204060e06040e01 68
    0x41d58403048134148981c80c4280b890806001c40764034240700041303401403941e881c0e0600c43d0300c40c041001e852400000c034500988890300050ad815480e80b40500c2050703040f520140003460360703942e40880b2224010044072080c811a000085140301044442d41600c100c0001c1c6032641e040102d003e013181c1000b00901c0c42503410106110200360f54104003c16100d0314415003107040180c20108488003035942c0800e0704140342c2000e01c0380f80c5030f040c0c1c020f0b80140c1c881c020707102c5201c5d520082a039480042c00c07062948040c08028005040544000e110140c1901038420a00ca0029803070f55030a00f64240d00018450400343c1c10000d4559416035a0a100c0c807189602c01417240300000416100004c02610300d001d1540c070900c10340111010044048075580c01002503540f1002401c80d07010300c00303c0c0340c841d1505210b0b03840049a086441503e040c03180c2c1c4c2009915401c080b00811030707801550700703241d02c00d40c0558400340140543c0b114001e14001d0032204080c0d40c4c2604040f400d0200701d58515240c1007a90f4500003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 357165638 1250 357164388 357164393
    0x70e0c090102062203140f13053c04110a030204030b090a080403060e0102090a03051b040e0a0b100e040302030301141002070e060406090f0c1e020616090806070c050705010c 76
    0x8004c416158244c038016074007248003208200103103c0c400781902142c001281c0c92000e12400160241904d200755001e150002020036403007900c0c00038800250b034006611204205907130020071224003020740144017103038160300310aa8026691040240c080045e80005081c8180110b121616801482e60740013000b02603400e4030340b0303242c0d0b0045020003485103072601c030b007154041400d40558a00540c020404412540c0e6442d00c15036551890001d601d800c8108003400b48145428410b11000d52248405090758106076610082102c0000700f829011030000c40000c504620f40c807800c5886035100f9001540c0d00d50411801030f0545800c1ca2620b4401c10ba034441b00e400300d82d40800c101080b2526501422555118000003a001d0480c5800884456103410512041c0098076001a00460851380380d80707030b000c008800c05004020402c1d217280b026130300901c0800d1180000c9055460b8442c1c0c14503000c000e8a8541c4500c41c105001511341c4000602c08041304010700074203000703200c0208000d00b001c0b0300d450000d5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 357166888 1250 357165638 357165691
    0xd0f030305090d0f0c08091c0c1406030417072f06030103050a0605060a080307030507061a0d032303070c17030702070e04050a0c060903030813170903070e0c09010206 73
    0x149400010060100c3e40304040001400540d907040c0030050000c1e40b803d83c81c800504854100344000d80d076041d2074600000300ac1c000111443c038098000f4000741c4c80e650347d5845502130504110710051002c0b400b0441c080c0469000c010500000c040c0c0c1103201c0400071000304207619461140c0041c0d100e00420001000001c20000f01c00004c944c3c0000003044940d542c80008034941015840104075010000e111750403d80c3c80b078000d020b0140703c0c0c00c0410a1241030100d030700f640900120f406810012030f208480100e40600070b030010401d280c80b041c03d2040e0896501c00702c00e0b0403e0724281c02040c0c080441004010b15071007210750090604800c1e90031440c005400940e2105240700e840c1000028030041802e2200130710051441941100e034035114151f1f9403000138505142c5100c103030005245c1e10081000710244540352011b1a40100520540004040110080c1c1d03203d07298040d414460380c9800181c3c03001c1c0192aa100d51444208070740c41d10301a100280c00e01000502c002082c8520140408200160 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 357168138 1250 357166888 357166907
    0xe01060f050d0506010c0507060504080f010605181302041109030c0d030525050a1214090d081b2d0313030807030c0510020318150106030f02090d0f030305090d 70
    0xb5410041040e0302c440005a5442000100140107800f80030b001140c815000802002280c0340001150100c9441c04045c0b4221140c40c09a42e0348010890b840600e030028002503d900302c4048003206020b41182e90011b8200c910300010039442a4011411311061b1a0a001606410380c099034a41441c1c3e4165030018090b01c600e4105030a00d4400030305100c003142c02004461a4168084100e0780b10281d076051518080100c00718031000a1f407000c91030003242014401f5035800c0f00001d804d101e070f00c4c0310507034901c00c0c541c0002100c042801715011f4024042c2900300a100807030500400f900b031140403504901d50151100946c1c5445541c4100448080000c0c1042420216500034041680714400c40c03408a886901e02f480142080c45014103244100c040f0398019070144400300e10900780074503c2214513454403816120700707a1015994004100c03060280d0072002410740e40c000300501d0600458001030b4003000020041d210800c5041030354003010b41511519420416080c0144403a070f05400d0014a24681c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 357169388 1250 357168138 357168157
    0x2307030c08240a020705100f200406030b04290427080706020903070e01060e0a0303050a0c020a1502030d060f180903020c0d03050c12040b07020f03250e01060f05 71
    0xb226000600c045460f98142d4440b16400410b48920f030440b01c3c0b40201802140c151407018616049040f60303415402070a4003852440344940c0c40c1001e140c400c09030700400001407101c2d041382d12075140302c501d41981d411000041360f0302c03c81e221001010100340011030301c4402c4546012480c01e8903c1e00c0d070000c07601138241e4142c0e10240c4641d869682e4035010020340a40050540c1501c00e049022640441c48898181695110b5035080445106407081140030385e80d44c0300c080d002c21420840c440710a88910f000350040d500250042d040707203030703549010701591081c12060300c0103130004900810007800074000ea600030459040354001850502c820606403880c0448482490341e550401e50040600034452902080b4004041c480950581d05002c4c0159000601c0e0040c64005c540c070720890007100a050b982034420b080c0c18103040ca113241e402e0017446426001035543c1441080300c0351004000f88520403091740400401401018908045120980310680005d400d01040e00501d4089a90000aa1711641c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 357170638 1250 357169388 357169453
    0x70c08010c09210b011203020d020c0d0b092109130603030f120b0603010b0d0c0c030f110f060901060302030d091a0d09060e0313080c0d0f2307030c08 66
    0x203c00114030540c0400040d00140341c201d800d800051601900c40d1407040c543e01135000d49513001d66140040340c41e031800300c0caa00d81c0007801050801c041048840c01e2940700c42030a00f281c0658404048100d020000004c0c984044400001c1c050034a04000341da0507407240607050305108160444d50b01034034140b0703005600b5003084003e030114507690041d07812140500401074551562940c60b0314000c0400e07070005a9880034a820085004807851103000301e10207460301540c4080686054101c112041c1c0e030703940140001e0340301d108907106030300c40b061003c140900300311f070000140c4a107507105050600c400201c1c110b0a00141c0d660412109401078103d000010b00640a0b0b070303403030840d501600700500f407144001d80418502000040340c40c1001000b03040c40303038000c401e45414580c0d650b6455500d042c42100740740c0140600745450300203803007182c241100a04c9403a40680b40c0c50b8022030f00c644280300e04007244860788503000410900100c1c14524010f0282c0c10050007030414041407400d500313600b00e0b80c10715110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 357171888 1250 357170638 357170669
    0x60516020a0203060c280e0a0b0c0615031015060e1203160c0801180b15010504090506010903020316062c0d060b13020702090108070e19061a070c08010c09 68
    0x4072041000010003100441b07190001d501d00c240028000414051100d0082e5040c03503001c1036070f01c1060300f07580b212001d0768010302c80c0d07a035100b83d00f0342e00c0003040030300d00c0c4c0501c186141880002054052041380c40789200c0ca4001203440c2c2030700117040310321100e03001d40142007e40c14500300440c08811542003106103208601481c020f0f190695180c0126448100c00d9441d10040e05800c03402d1181d21010709001d401001015100c0a202038024510507040324045441080100018a499003045a0250050400030403140e40c98006c81e0a110080210301c2240340601c0007408500d800c03c4188120340810312654100502c4d402c40c140188a000f9510352140200d03d520300100030480d0000c3c50304002c003034020001b88942c103220754060b420500e000c9110700151000816060000151482100c0c03074920f91700103e840d81c5940503110200225954201e6403100c01c003003010250b050b41d505c601020704001c142c1d158442d09240d98940c01c20b8200400c2a41803a6110203141d50041098094802071556072000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 357173138 1250 357171888 357171907
    0x3030f0212030a05070f02011802010c080904060e07080c04050a03030c171305040e060906010b1606050f071b03090b0a030e1c02070b031902160f060516020a0203060c 73
    0x80c641c80c40e60554502800000b080010240b60b040319001c0c0d0718685401071078521307242c0141d090300c003100c56424984600300c11441c059803180c4141e21a69000b80100f6241100348800315003a185290003220b203203105c03001800a0580e10010b10344c0d0000c0c0f0004041d0516040c4800500150210703c0094100134001c07060509101a503070070100c04494280302c00d0381d03840000c80c418103a0101807180c188218540180c00150941c08600540314003000005802c480e801c000c601840ca401c022008600c000044004100144040c8200ca02440d00d03205c8800641c41c10013802498070900d540d20070341680212000f50006134214055205032060040c0440d00c480c10302d04c084008022950b541441446204da1400310345800d800050400c2c1c2d5143d0070b6036103503a202c40946959210540b050301843c04c1c1a0f005520180080d80503284e003200740e60419920780c40c1e0741c40385407a202c440e89054031940d50303038811300407a6640400e01c1c16860880b800030340100141600000d49038100140070001c4441c001841500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 357174388 1250 357173138 357173143
    0x3110418020d0c0315050a0e06010c050307060c05091201020711060f133f060b04060506120a050924040309120506070801090501031e0c17013303030f02 67
    0x41a0341c25031003c00003214080b0700140600054001030200040072800486d040c10a0049074065070082c02c00d01d8540d407500001180c104000c40015525400305000b4440040e030a4007a003240301c0d100d40d81e4580c8803621b4004102da1210650701070900d9030320410103440000d007025a007400035003040390041d44698281c080c080c000c0c41780101810035034050610101e140c08100005401c0000501c410100c05091369004106000c84900140c01c50f5000341040d80014010760000e650803140584041041c1d0380d26400300d40b1030b820100400003800c06c0241004108940c0384246540b002c4144028141c1c00c980d4000c00d140011040c1807022404203800008080c14002c0100c0350081000c2a1f085242c40c1d42400d10b592074000c151003800c0082d00d2000009039010f81c601696043c0e941144008a240c1c09034400f800c0c004d0810b16084950940b001d0002400c90141484210713000c13040c80011982000d000000300424001c0c1a81e00940001c903801c2000e00007010110030143c0e6450b08083e81c0e814010341c010391 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 357175638 1250 357174388 357174397
    0x1111605040f1e15080f0601080c06030601300f0f0c02030a050901080c0c03040b0c0607030b1305150613030606050d03050f0703020708330622060b040b030f070311041802 75
    0x410920506c2100b030004180041d1660490b1041030a41784904903450030000d42c0d200030b85034940080c000d0880010480f01fa4010a109091421480d2100c41e00c2010302c1400d444034814040640395840b0300910800d131082c020b000a45c40c0303a1000d58948002502c01406900401c980c450411100b1000508480381200c1150b80c801c0340d0740100e82d10780b55036030310030300c100c0c0e05c030403841d1110b40030340c401040001d800390143c0d0380b000070004d0900810818087c036010041400a2130110030301c00c1046240c1d80c40d12901c0c004c00380c1401d0701601700318103410742c1030240559a903548081d0145c0c841032108008682d0207004d90305640540c001d155035481e410b0604918080c40e98000c14400e005440c0b00704200002481090340300b0078000040c40740740035024942d010355242190516003000c42c3c4044c1d81d1860322190104041102d03201e0000600545500443c1401c0d00f1a800495190720000b007440200320b0075504481d44068a440e092102151070700361900302d4026441845000740c80d0b101810743c180e10a80580f0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 357176888 1250 357175638 357175649
    0xb04020708040801021b030c030d0b0103090b09101103101424030402090c1813060e0108031b07030f11041e1d0c18040201111605040f1e15 61
    0x1c644aa07190300c0001c0c000d511800c5507441201c0290150421030f0004019181c06c4c0382004046c504195030012564040c3c228055658101540e44650750001031503200c50a010369045402001d041d0810800703402228007910306a16011000d00800c8510481c2c0076424064900c6042807040800d210320220344010105c8170544828900700203811150306101024511450088402141a46500c1480d1459104005252503088040c00c40e041301401e00c448021041501d43c2c07400075840e035032080c2a4000240030b07001007005405c0040c0100e94042101704048802071000c0c050262f00340303140c0e5a00c101d40081308000307280800702d109052a59845502086481c1c00c0c00c15850440701f0a2007504c0d006000850301c0f607541e8445001d81801d15200040c4c0f0038040c42000e0721380d0780121003034181190400e030b00070412410030a180d00f03050810a02841440103800500f0b5010512604001c10001501c1e00f444c00d1415140c5071010350720422410318445c0170040540c400000e03c20304000200c01d080c040c40e8002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 357178138 1250 357176888 357176903
    0xc1106150d1208061f05070b42041103010e07090b041403010c0212071e06090f060b01180311030708300c070e15031c020606030a05100b040207 63
    0x140c0b202e603802915151003680225140c0d51a4202c901c03010806540c6100c404002a2040c40356600190300101c241c1e4018466540c00020f8030840201ea05551641c511501c032010481d4104012900002d100e0802ca481c1c200d8051000c06030070f12000000c0c0c00144202e1400c4a854030204e01c0f19030213445110090030744140b030340381c2e02d6413600003041c2002c1e070480e03103a4004c1d8a45400d001004e0310106d500d0724800170132455a4a4155562602681042c01c00b06400c840c0a5a4290100096030351165401aa00c03031a156a00301c1c4150400504441f07841030704606004103410400e01c8135003001c2e400003e40703074440d41c10801441c03513902003450b101968100708054403a0a032601d00c484041049040c1040b402072030408a00d4065035502240d004d1352f505484142c3c071050061221000c00e00ca490340c00b0b40e031640d85501003610280000d03c1e200f040d244c9400d950102c3c00440e1a0360340c1c14041c656003c1d44c1500248040c5d085a55603607a074070480340036240c01545c1c0300c94500c2d0550340d40c1c040700d070b400d50021103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 357179388 1250 357178138 357178163
    0x50d0309030323030601050a0909050406060e180c3105090c0a14060a12050420010201051302011107080a05030315010c0305120a020904020d0c02010c1106150d 70
    0x100508100351900040d03010444210403041406041160461084481c3e11098110b0f2220710054869400548400302400f41e407038404281882a031040b50311841c010a00400c2c158074003020314420799000382121129403400f04070258294000030b110303d9080d40c1552583c8040512000220b22011210410800c05007200e6090140e500250001c502600740d03a401d591410001004111035680c1a110385422807654200010440c54880041c2003260355604040001c0340501c0c42810465008031000c4030800c120805c804c18a40004c1c01c0c10003001b4003800204441d052001c2d0450603400008c50003810042d40059120a0400c10f0080d10000c2c0980000c840302481e0300c1c5403240d201d800c1118111088d0320340c0700d1543d1107580f00b420003440c80d0703030181c40b05440d0107a030454482d600c2d60001c000b8001990200411200c13a255480200071244036958000791070031300703414024292940750010804200442130305203060350000c41d529821045203085254008000c1d030204031038031a140c1c40600503004122 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 357180638 1250 357179388 357179393
    0x304140f0f21070906081005090f101401090203060105030411120d0917030f07081602130b09070e131a0a1d0f0f160c080a09060e150f0d06050d 63
    0x100b42005440c207206464161341c407a6001030460b08680701c0c2215036803040c207611424141c130f50310880e00502a41c2c1661800c59403003141c180ba1405111146010642c0c1d00380444500b5441c2583c507014241040b0190301d981090b00009000d40800780c40501403054040018400d5901c90310460325008a800030385d041390f80040303c05054018107124179100d2050785071800c15800404021290442c03106002036040002503100c070140c54000e0081001d1a4031901a4040580d45440d641c10480c5070580703010810400d2201809003d80010b4842d5003441035520380700140d50f4074007510f01c0c0040c0c0c00480004000c5158500300c0055029001d001d50064120a800304041038560f802c104150390f051a02d06054480304120340c14200c08542c0507883c1060000843c0c0001c0041d110800f00e00316910307100134030381155120450540c0c002488400420a180d008100403a04110085400c0f402190542c6542e5031f5032030f1403070007413242c4091390000000000301c0191490f00703075211001070b15005d00003a05441403031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 357181888 1250 357180638 357180679
    0x1080c18092806030b041b03170a020c0102060415020a12020c28050c01080411032505060c0d0f0504081005071b02030c100c080d06060e01020304140f0f 67
    0x80d000d030b6400450520312005401d54010402182da00000c0c0c1541d039540c5459030402541c031072001740200241d42034000086400803603d00302d000c507401c2c5650382e18140504003914240602d00080d040d500703c1010040444c585188034030b400a4642405030b529040040300301c0300d410060900224207072000c16807444d0007a00040f4590001e46071b8901c0c01034484440300210300450035120080286d400036040c06900c1d40b040a500350040e01c038000e0f0070100040e89001078140151280211690358800c400c1010001111048000a05040d03861601d0500455021502c882d140702c1d4400501000f0b80407580348620030400c40d8001c02e04402070b11441c01103130203402e010b0310082d03070480002234603040360001c4c0c103410b02c260161141e402001882d60428103014801d038814490800010b0145407440200480d56100040c500c1140508001502d54102503020342010316801000341194030602c800d005800c0c10000c2640d202c182103410259104450001400b01500942c01c0d541000c9080229030740301854 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 357183138 1250 357181888 357181921
    0xa0f0303110906030a09023c040b040f0b010201230c160c0602060a0f0203010e06010e0f0a060e0a06030608030d200d0c11060709060e040e070f09050106030b01080c1809 74
    0x8c640300c4e241100d84850342c00314078400e5a50340d007660345900c0d0407103080d4152203090304844002a0003c211901d000e000603007120000600c41905c01d1302c42429a44540e42807041e9110948051840740d01b134051300c0d6441075218402032114114075030008610003d0700500c080d04501c20391241d05007046988840c00291507520a0f90200392513130810001001c0042c0600a4078143c2c1d8081d468131030705aa41000446240290844050704515022500f03052034584040b10f2019211036180d82c2e20021822003440151000e6900610400d440d008060248241c003200300da0018192000210f00d02d00c0c035582c1d404412a0300d844445142d900062402208070082d0171a07010300c00a6154070507030103204000d0584032001184d403c0c000880410080c03290f40e020b0b1844215580b8041e00001361454207030520307172404000307810207070805000d458200046070380c5019581c00b500003031400303001403089400044c0c04220081e000760004007000c1101c1d003114035000520009440018242891824410128803000c000e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 357184388 1250 357183138 357183143
    0xc0703031409010c03030504020a0308031315020c06060909030c100605041a030d0f0c05072411070e06011107060e0406050909070915120b0a06080a0f0303110906030a09 74
    0x1d50001c00840c00364a0402d8820204068403003492006580e0380c214001d0800a00c100ea00c819081b40101c045aa664007961092025540002c01880c50f0b090402c140400c2c03008400b8042c2c010001d0140082001c01c0ea29008501640c441040c0d44820001030b09600810126a05034400c82100c00a07403102600828201c4070160703000c100e0035120094070070710300503070300c0340a60503030b000c200340d003081610850350307100001074902d80718007003040554916060a1003940b1180c00d1000320080251505d1041008104801c160b00b48848640c04000711a921b6104602c106804107480d000040c4182e40181404000c0d414084280d03484940c40f4000030304480d40c41d070000c03401580380000110f55030506c005450f001d90360b00002020054903103001140501940061541d00383c85200000991620100c006124248036140c42c0080c4c1c6000c800c0b0804940c000d0744120001d5000c5d04040000c1890499100095600f44c075010840c0351031915030310350900c12070840542001c0000108104208183d1215500300c1c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 357185638 1250 357184388 357184397
    0x60a06090501050f0d0803091e030901021218060904090827040213140a0308070308040303140c1b070f0608040b1006210908311406070212030c070303 66
    0x90b00c44080c8064040d254100a0300040c09130105c40116480710061640000200120307103241d80d0714900c0c00801403088280024907800412561160740e0140801c0c0032811a10468034103152040145a40d680e10300d001031800384100081440550b100c41e00301d40d0310145c0101006e41c3d180400740446d41070b80c01d001a8901100040046810315192900844172442d6040709040d41440c104401c25140c03003585407035070342d2103a01600f00000080d881405080b1081c0a0386880c0201d01d05800d010302504d050303403282084e20120804000c078102101080d12952165a140c0c90310002c60705030310311300d44815900500046c113120b68000900d01d500c03c0c901489244544c02070100c9071a840a000c84481039405144046448403e0714104100702d001c1100c2141805000400d03c0852620b400c7c10366848524100413030890610058003a80c8422409880a52040c140510b0149440e10041e412515040307110300c10780c000a8941c0030756449229248511000030143d80d0b40b04180c60f41150b882206100490206 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 357186888 1250 357185638 357185641
    0x1805010506092b0501050906090c03010c0c110d1509022706090c1201090209011b1104110d060e160c0312020a030e0708070810180b0603030705060a060905 68
    0x80c1031820980e6a840400f50200a40d15881c0701409440074020481c804102484141400410001d0054602850700c2401500e080d00700402140c1c01c140800303007450f019038100030400d041103070b2142050152130303000b070500c00c8810f42103c005004e0f01480701c0c019281c00c0e001f560040341440180c2c41000c04c54800c4900f1242800c45542040441d490303d9035400e808160303800007450505003440215444050386600602c1c202d0f171016200c41601e801e0b004111116404580450300b960409032148880d400b0601211500c042e6581d0202c09511202815001d00d840baa8100810640321090700c0c1e0198850500f400f5041d21008841c103101e004a2340303034008680070010003004034020f005000c2c034681c16954080306907004000075000b9510030f8078980308050780c50443d154080c1c1d052198801505101c0d014045052a000c1858581184d980002688510348580c041c1003c5500c11118100e0783d218811110b80d40e43e0b0f0b030000e421030240f25005005801420308104602880703074000c0c0243e8140b0301e81004075 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 357188138 1250 357186888 357186899
    0x302010c14342907020d060606030501140d200103020708070614060a030b01120309211b08032d1602030114070f030b120a060608070801090503070303050703060504020301180501 78
    0x10304480f80d59a440b541456001e503503459000000038604140050003440e180c0c6a180e0340c550481c0c98507800800082d42e140f0050201c880c00c2c0300d0251181c40304803003c01d03c400854171000f084031b502c4072824480c140c00c1d44913a455a4040d4060b504141c1c1c002e00f035541c540e04581400d00c007401f665403d043d00c010240c0005102d5241045448050380d4128a107103500d60f0030141000ca14041060040d405c4c4500144c000414441310b0800c0764101e0503400d0503c04102851401110700c101002110780401c034900e030280003040c000815140380460104129898000072100c1111001c440e4501002c1c2840c00103d8629000c40d6044a0b441c0364820307002005501201c2071100084c0f001943c0070320000f014104105010340c40703600400f0401c500102030500c40d055400c03181d41340c29010041155110f40310401005130a409001d03103002000c5480003484001481d64a041d00c074400c4e00801000d05036120b000c00c05243c03181e88040090325001e001190340796152011f881d440c41a078051540050300b0034002250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 357189388 1250 357188138 357188159
    0x606180903020a08070609151a04020406020c0f060d0c0206090d022a0f0a0611012306060d060911091009050a05060c101112010b040302010c1434 64
    0x89054140d4050701d29030300d1a44d9080b4660f4003034082036170b0300d588814104001c81d100341986039a4111070200010b030a003a4001c6003406043d0018004d10486c07060008000c41c540124450300300075800c440820001d91504002240c0723002d00c4030750182e0645800d42c420030481d0001840c50184042c0d10454038415814502240c0e100d0b00c00b4200404902d89040c20056292982c0003c0c403005001080085800d100001140281034140d00c14000141d51a030a143c0581082c401c034408400404074064a403c990041e40c09001800f910b203a01610f030004081080d001540c0c04400a000f040c3c0c4180100340390517403159440e42015001d50701c60420b107041c6014403801503e058080301c02c09010f0f401c000e85040c040080380c0d04100c111036414001e45034546508183c0d0b05ca9950440a000b0756684c480c10715807908401001c05030400c100c12801080280003503a0072044200c8500d60000069952004003602c02e030500d4440e44030104072401900c0c9200c5440d041c0100301c00034030142914454040c0e40d034030352840d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 357190638 1250 357189388 357189401
    0x10c030917070c0506090102010b04050403020120091e0d06091a010e06011e0311040e0109050906090c1c0f1524050909030f0d0f06050409020f01230403060618 70
    0x1000e104450f00108400e00b4610050542c0e180140000501240d80c4008034054810448040300141d40d9480121490104440c4030000c5005096900341015003039400b19405003a81c011403460050441a1303101e207540c406046030812a403013042072114000a00d4201e0071203032500610a588007480001051078000c10a40d10f04c103c81c1652114162000d1a401041d49080036002c0700400d511540c920040500c42d20040c4000d100d8050007003455850542c40c40c00300c0d20b02500360b59007500054107102c210003002480b90415903048840508031883c0100c0e002c010394441c1001072140192a210500380078801e42c0201d500d40c140300e410720103034000c6455000f0140300100d1450300702050040500c543c1c100310910030b80c0004c120007182d18103054501404440e070400e548107059070392a00741c1031442d0701d43c9020348001008166401d220f09900395001540741e0f110218a2810890001100d0f2201ea5450030020000c48036040040c0e038564503401c0000c080c10840c0a01c60b401c2c0d55205000000c0f40c031520601 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 357191888 1250 357190638 357190643
    0xa2109050a0b070201060b0f090f10020604080906070b0f0907050301050106020703170c0f0703060b19030807020a17070801050c04050603010b0c0304030507150f0e0a06140c010c03091707 82
    0x2480c86026503075601009802c060280c5045641e190004554061044020030040d0781211020b03446840c2c540130003100322046600d0318010781d415141c00070516000940940c01c039521410840d210014400403031080c0c019100058090544101440100d8210019542c01001840f0603201d0141d00d8030b060600340e40d0203104180050740006801c0010400ca401c2a0b6841782d0342140c501d04e400e00e2030303441600c1c1000041d9a84680c0e00540780800400102c0d00c50860240020b480006001c214280050940b0040b44005054a24001402c10440d0360f8044490301038421190f0003503544400d0500c5668808030741c02000300c00c3d842d000c0440e04809001e4155000c840d00113127500d103140c0c01e00075035001542000b440c9880c6803106100105c0000c20074440e160140c0942c510b04541d0310746203140104901000032003c424064040407150b400c0c0c41c0c44071958150780b83c03402c08004851010030600a5440303a190200c0d807551a0643c0500a250b15810000c80715004182200c2510b0071903c40840c60711070344500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 357193138 1250 357191888 357191893
    0x50105040f0605130e10050709050108090d050403020d05030904050c0d0b0d2d0b0115090608160e010e130f0605060a0903170c0a0507080f010b0306010504110f0a210905 74
    0x5034100c4025030382080d07101170030a400752160b902c18040c003c0c040d603105940a81c0480c00d4014180801c0d40c2c0410455440102000200030034010000042c206100b54007000e40698520f0000c0400d11404000b2186034100c0604100031a150289805895401c0303081100700050403c64855042e1604a14a16210390810104494801400020610ba07140038980103021000c03c418803001c150100d0744603000300542041c81e01242030001c00140070340080d030020411300030410144107000b1b0503030311081c000c1021402d140702a86030720030050b504203001842c580c2d44a21001100e4144503040c1d046624100e090341b00602a407503e590030899140600d100820000c1d0031120704001003200311000c60801385035440860f2804000c072080a0411102901c10348655001510030000d00c1c80c00c022800480b2080300080160042c9900020745925043c41a548900d807114540c03080070109070304840081220250070780e51088014405403280d0101c200441680046000420400041c0e02131005000c0d4000c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 357194244 1106 357193138 357193159
    0x308120708040809011d040c03090c050d150f090227090c060d0203100f0f06020d0305011a03190507030e0618030406080424050105040f0605 62
    0xd10040003008010032003c034403000c09403151100c007440c001d0b0a4012420f42445002031126401e41d200380360003089110150145c1c400f25581d8810440d2a06080e965001c21903070101014000e409040c2c05003005000c20400d0380038960303110030700d1400036040d0709a4012038031200e040720301c0040702d4484241d280c04041408c0310040d0b00c188800001d200315800b03000400c2850251b10042e520302500400450081c0d207005240c8005484280f40c40a04c00e0b0342d13900080e0520451348240409402002c20b01150342c2d04c00d0050328107803500c026202d91100e000c800c2004183e44001c0500b8541414040108003c400c10300400b40a0303c40c1d95004217480f40f00c0f1112a08013a80036020a0041c0f03141c2415000c040c002106a0781161854240010079556074141041e1140c0603403200880384012110300d181c40120742d88210b040c4e4609440c10015400c684002804030785960060582c411310208 = true := by decide +kernel

theorem cover : BRFrame.Cov 357014388 357194244 := by
  have h0 := BRFrame.cov_init 357014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 357014388 ≤ n) (h2 : n < 357194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
