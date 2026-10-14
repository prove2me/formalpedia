-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0869
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:18:24.093988+00:00
-- url     : https://prove2.me/submissions/5c1c0af2-af7b-4d23-bdf6-641a4e68c89d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 156115107 ≤ n < 156294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 156116357 1250 156115107 156115109
    0x90c030316080a170a0b012c090a020d050903070c0e040b0105060a14070606050405090c01081f03050a1b0f0602060f060f130f201902011d06060a080607021002030a0207020604 77
    0x20802d50f44900301140342d60403400b082d11110308c0780065286801040142c40c0c00c1c2041140e0350744182c003500c00041c000f9103558142e803601e40c80ca0004001038609003144c15940c3d0301c2164195241803801e04001080e9180e02402c1f417040740c2c840d01d01600c0c0c2c0d280400707000e0300b03400c00003007141803080c08100c1c115580b24140c080c2451602035000811290700d050f09002c1151006002083c0c20740040500001c0c0fa608130390a650083d072000014080010381250b8030742180210781005120b4002c0391040e01c1485682c1c0c45205102c502912041d0100d81c1c0d0f01c120142000c0d40e40b01e14405604034000069400c0004004940d1100020305901c0c00311903048000703a0307010344100d204600d2550743c4400b185024258424500300419514246540c182c140d003640541d4040c8603845000041d2092482c5070307081c401c0d00048080034008104001034120003814a48428044075014041c03408490b0000309800c002650502400258000d04408611019540d0180d40018000c3c5e01180c1c08024941c01a00c90100902c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 156117607 1250 156116357 156116371
    0xc03030c030c061814010b0f01050d14010605130b190c2103141f030206030a020904090c140d030905040e0a020d14061305060105060d1404030503090c030316080a17 72
    0x810201c8940ca41038103420045240c0c51a280e1400b0380122036500c408204212303c0409082c1942c40d04142c0700f450000c1c0400c0e84280074651820b0300000740f070326009800f400c01c02c8079402200007015180c980000c19402034100004e0300310307918290f2074091405090400b8076103002d02d0943d0030790340c000d06822401680200040c1c0c0002d80d1011440c1c40b046898018503000001c07130380610088021030251006011860002a1007448000041403400050780d048805043c400382003800b03040018140440540b0707141c441c41d8407405500084442914041c141401e200c0d5250f11803200960a04040c04014500c00c1440d1013248117078080304015981e0441d80b03c06551044610700c01c10020f409450b0300f885405018001d00c4d02c03080128100180c0003040c914103440e0706403405510350b1903030108ac2003d4943e210700500101c11900a1105042d8080000c62081030034a044980d6107102005159407442034900c0000c220740030803200800201d401c0010130145c41e20f0301d0095800c0c0c4a1104000e08940d0a407040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 156118857 1250 156117607 156117641
    0xc02010203042607140406090b03060c03100f030503091512370510050d0f1106041203090501090f080309040b011403090a030e09010e0708070201020f0c06041a040c03030c030c06 78
    0x60601403031b10b0301403900070700303190034080c408081c0300d0001c80e03540c450180044400000110006508140364100034004021411052050030303078905005880e03034004034400303000394072042403500c0000030002141e66100484410300b00380d554644511002c51141150145403001d180000305001281d02c103800e00540903004001a18100460308000800860380f00701e0058040b8103c402c0400c91484901d120300e60030800c010511101c5400281c414811a0000d041c4902811b11020500d6403151001040e503c003a00c911403182c1e103402200d41c0301181d82c880e00f40240e000700a82c070641e00301600200e2440c107041c1012410030007140c050f0038030350f001141e43d01c045502047c000000d0650107524080c08113016a2400099418030605040c60748006158000307010311503020403d403d100b5411603d21301140081c0d543c03244400010a502da800a8070251803250500c00c10300c450300c4102001c0d60040b43c0c4052028200761039a54103503240c280684094090080c0ca84440b00402c603c0c0c050010f68a40940503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 156120107 1250 156118857 156118889
    0x1061d060301050a06030209040809010339030b100509030a020a18050a05060904060c1205010f0806010f060207030f030e030105040305190809190609151b0c02010203042607 76
    0x781400c6450081401c607010703040000c10800341e12420a216002034001c00c3d5541c0d2100325030010b8014007220710340c6903500000c007120000110040d045c0c2400321b0384840e10304501700a0711036003182980c0d451803a081c1c0c032450b034012200106000c1c90081503c80c030080c0980744030a86d036400140d1264070550019400c035281c03141d5800700b982e8520070190b00080e01c28040007030342808400328007428002800284015514a07803010a94002c034200d190b401d005020502083d83c40c1d41c0403040d032540300d00c03c0740ca90384698400420303104c00c40e203054000c1d5045580207100c442d00d540c55803550001103140c241c091000c46c40301325107281c60a000f4240f165000c1e86070303d07070386a02e5001409580d00840064108004040050227040440407441000c4801200000100c0522900f051002404d11100c014200100302030365056461841c0c110504455441c4003c072095070300c401055448031048031000340160000c11051120203035048000e0807004945030b5404141c0c044103560f6240400c1a00091a80203c202d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 156121357 1250 156120107 156120109
    0x2505120106030b010803030403080402120a05010525080112060209011202070c060806091b0f0d05010305010e0606030304030312090602040512060612070f12050c09070e01080c030f07030e01061d06 86
    0x503c25006060700c1004515602c3c0079100201400d0010f007000388501d2340700150348114141001034180c80f0340c001d0000c010600b010351805c010310b801108080348801004a00406180c0640c5600e81260512801d4040006c0c2c15600c1100a500400d800d506006070801e0b1a407030345003103102601c81e2602c20500240300c1402c048000e40141d400421191040101400300702500c60414458104e81440381c180f60b465400c040442d26160240365260b8001c2441c0500010038080d054110315030381e6203560291036090702c818050544034482c901029000c980c0607103000942c80b690394440c1030031074041c0400504103516640020a85142c02d1159a0a6030106003030000e11300e4095038402c49401e0395801007032007603e850b1403e214403001d407280b50000000c116804c81030000611000045c1540141400a140f501a00181040b801005d0b20350008032150700240c5028086070859004078400b240c1d045080c1e4800740110b01500c0c07204084a543d540f107003000a0701508000c0344141c00340c1100100405c034a4200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 156122607 1250 156121357 156121373
    0x708090c040506061606181a07030b012a08210702010e0a11040e0f030d0c020a0c031401110f071a0c0406231803010e010e250512010603 60
    0x103644203601e40014000c150340c45408a500ca025188208507581c2d4550500c43c006018450082d200c11261310714100410001201c0c11040c019120300c42c07121030722441c400710212100c0144407404103881c002c9112024000f01d038546000340e0844016400b0500ca40d80e464115000030405500044007608100501d900101850703500c40d01f0313403000f000741c003402c1e003a0b5981d68440c5520141c101400c4e081018441c0e103840d0403c1d000c0500540c100d9481c142d811068580d42c0c0c0c0075500400900e860600046810f074400304a01c0741198004071440c0c05c03d401c42d10348045003004144051360310740d48d83c114440e20b081c10754080c10f030340344c05000c0140e220381444c10405600e4003c2c01000e1100c808210401519101400545040e40c4c02d0340351004181e1007070003221040d104140c0f0364040d6030f0400301e0030000741c2c218030003a012482c009038002d04c86070240428290a0700c014502c40724090b00001c0e0201102040aa165001c001d104100e402c1450b80d41c01c0412a501020201b44038582d441da070081c03091003108 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 156123857 1250 156122607 156122623
    0xb040b031329070c0c1e1a03010e0a060510050c030c0106080601211e020a0e0405030d23060105030c04031a07021c0e100e1c02040e0a031706010c0b070809 68
    0xa4107013072034501442da0303031440c55030018060400d44003501d03404c6082d04c1005100c010090203d13070004201c40c3d50700c54007944954000b4403490301e03040011000502d10030301e24069a01110307009010740d100e030030804005581e03542010b943c01119120a008c200c003204001d001d6280101160f801070b209039414022400038400744d100014041001c100c0002000078500010317161060000c551a0003014410300c00104020702540c000c42c080c00c0d06906110520001000420340900120820020b08035005142242d60ba4402c02c041c000c22503c00000c2ca055000c0d0780215402103070000316515207516a940d8104610103d280002c40200140030031421070380400050f660401401c0c1603604403401200010100410064540c2c016140007441023607150040f41c00c2c20014500504846221a80d05940460619020340c140d1013507017040c40b0403444440102c0c11031200c07609607032008079107000085d8102581c440a484507041000307910811012820301025280655039590320009075082110240340742c038041d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 156125107 1250 156123857 156123871
    0x100305010f151a070503040305100c0e0f09071b0804090b031c0c03140a050304020f0a0f12020d050a0503030a05010e060109030201030f061a0c15010b040b031329 71
    0x281100000c0ea840100b01030700d0445860710364500b4510801184045107020b680740043c0140b10105000c020030001041c5036640d1581c18500708072400c8602c0d011110310701c20070800c0390042005601c8907000d0801803403050740060300b4149031480317004800480540c91414001039407080e002007814004010750f40100203806400720018014101a03114103070740c40306c9103005801072103051b80502d4201802036002d81d01c840c50501c105601c6150300030000d0b00d203602c2160704a1046c0080010540c180c41c29107580e20542d608a001c11207141d04003540e0309106030078034a06030b0f401010340c80c400002440400109041c6c2d44114040c58803410082040029250181c02000004076002e00300401641d2242c61102101d80900c1d01103200c0b851141d006005100680102ca0b00705080380400da14664130300010041845400212529240d1801e00c41c4540030084c082c1d41c8504500b00b004100400003803002e95000801070311134802a9031140d0b2921880001c10850038a0038410203c0301b20701e003042d400280c0d80011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 156126357 1250 156125107 156125111
    0x70314030103021813080301030c150c05060601030908120c070b090a12030504060207020d05031306090b0703050c1f15060c0201020a12170a02030f07091203050702130203100305010f 80
    0x41035600040c916020303c0703100b802c1d2120220011751500308801030315102a40120350555256124100728880c4599030140070400540300700c3e9070100e180300d8180542540d402c40043c1c186501c03030400460180420341d40684070b01800f8170000400c1461502003500130f8480075812030b600c803a14542034001c0c0c440113101c6811138101055a0300803d111000340b91000c0705a00c7c000a00b40d5641c6080360090084407800ba420803a0724501030100325000005001c0c4000f10416120040e5543c035003221581814003400410759020310840c0006401003002c0e060810440d016181402c84c035582001841c050382c58102c6a0359280d1419603010854500104080d10039072915450303059550700081d59803050007000400022400d014070078001c1c0300303071102c10800c0104c50081c822070030250412400b80d0002d403124549500c2c41400320b410342d80201d21038411501080d14000804016032001d58840d081071718287c0c0c10400b00c1c1c01c105448501c92000307500c00e01c80d1440d0000b04904509150342103c116101c002071080c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 156127607 1250 156126357 156126359
    0x12070f021204091d10060504150f050d0c17030405011b0305030f280504210804030f05040e0103080705012904020705010609090b07030e0d050403150b060d020703140301 74
    0x10700ca401150309907211560f02150007440140c0030103500741c1c807690400580c098150200305080f8942c100c4812610110f80078000400040c3c604901c411462040c0080030001c10410006810962021000305000320098052030365100d2100d285d070314113a18100206d80001806000c590f80103c5980c9a4079801d03481c5c0d8000044135507019109120190001c01410a1040051003182c1d0700c20350740307032400e9201c3c90016401c9121155036000d03000c240c608503206000320b51400d00516010900b0b404103040b0343d482c40d00c1c607121614103907501041d1600341340410004010100320010302d880f800340203610540384199a03803420f003411800c441c1c401c280b448002c0004108040221100e681b4102106000c0306c0051f075035a414504180101819400600420b042206850600031501c40c8140314030895101805141400c0e140b9075126035820001034081001800140040b035040f4811580d400e0380a2400995000d9290010300a900032420741d90380caa80001d004020140c0c031500c4849441c0407245518119 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 156128857 1250 156127607 156127633
    0x5060703020f0306092a1b120a08100f14100305060307060e030a0f0b090709050403020d030e011d0304090608030702240d020c060a05010b07110f0d05010212070f02 72
    0x24480541030a2150b005c02c0f011070507100c40d866174079020040301d000004044c0410308413619030380c00c000d6032248004400d81d100111480003042c12025107001c4014585030130401503041d13908071300180400030040318600020807109100c00c01c02000d044100901040c00f8078001c10401d1101d0300040781000c1506020a0218a440000320501a03644a041800b80301034201c022030b103000c000303000103850505401425401c2c071801c104440d010b6079807201075407001d5803100004021f4030070035280200141d011f030a200050a20a900c11600010202d0001c6503025801e18920320441541c0415100c0d81c200080400800d4064440c020003002240041d608050464000403140c0000104031074944034803d00c01070a8070118000c8402401c4060806c54990004d5201d15980d02411a000d00e01c0c40e1502001050300718034402943c1ca1f0941c001d8801c20540340b00c10a010071064071602d41a00079800d01404000a402800035101168a404c0c1000040c40c005034002e20115078034111000395000500400f40d8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 156130107 1250 156128857 156128887
    0x1704150306051e09012d090b0103060e0c030417040e190f2a02010e060705040e010f03150905030d020f0d0612080a0f050f0a0c0615151103070503070f0506070302 71
    0x455621000e50440726159904644004070703011211b03071401700c00c5c120110748220190f0043d02c3c040820303602044040c0e01c0310000d0f031b20801e056030002e010100500002c0c0004894411426000d01002007060a045e40c50218604030318050707660910320119001d09007602d045500c28000b007941c080006100000f502080c00100b14200c040d00711003d2150051404854000d401214540c2c14140132642c0515210600500d04d0300715000312904000f0301e10001a0252030a4501c4d800e0700d13080103c00d0f02030300c01000240014902814115640e000920410103a261548042e01c0440d4000761510794640c0165122002c0707985035001110003c1d00c05106d080070800d014255202c034034950505a13a1921001c005072441d01030024600c29040d4002001400a90300001c9204c1d010301c0741c0000e01c01d13525452513001c800d941600a41d04107185983c5211030142c851585120302014110540703142200940302e9a09540c800d4070107039003841c440e01080040000401080ea0f200020b0300d8118104900e64811400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 156131357 1250 156130107 156130109
    0xb04090209061902030415080c03060d020112050c070204050c0a02030a0c06090c18050907031106090604030c030b0601080a140403030b030f070609050a05040213031704150306051e0901 81
    0x10110360100351540700341c440304201e03a1900201021034260701d441041c000d40ea503116006142d100b601002050040e54002d03042103003e4816000c0075425075035520280101c44124402c00d80c108500c0c0e407414a084100e6200b0107000d14424101d0710b03a20030b0140140416200e010384902d8500000704507003400340f40d01100740c904c440024a00700304030a5240c10040c0c060461806c0241a001c4101000283d5000c10b4008000c21460103000b0301c40c90b030300d56a00c0c0d0f0325032003180300103005071601c500d8841e01e501d0140c004200300c2d00f005040d07a08103500ca0301c0c1d08004a4031034208661030010b41092040b9580c01030307600360388020407102c00d1012100880044010b150040c00003414591a0403140c000c0d0f58080c000e10f40048424412a04007039079404000b46044640d01c01e05000c1d541484010070131f800c16000300c030050f000001c60084198503641c0c600250700d06120101c0d2100c1d00900001c2040c80d41804003010615040d6404200c0754107100800c00e141c190040c80c0000c00121100b1801c4d1034032007843c158 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 156132607 1250 156131357 156131369
    0x1050a030f050708100203040311160302010809010e0a050304050102160b04092315041802030a11040b03030d0e010f0209030a150b04060909050c220b24090405060405010b04 76
    0x80107882502d04203191101d240c115203068081d420305da103110310b140d501643c0702e14000d60b00d5070b80301070f1038143c40c64030307040c0729010760546801110702813000d54000d000003500803081000008182c000200030078105060143d0851380c1e5000001c0801c03d0b50f070b04000da078640f584906c0074161801e250400106192045c0c0c442c1d41c812036200c0100e512002802c02c0b501e0346004841000540e11300d001e20081441c48030303007445544035910b4014a080e01031514000c001d15107501800805480649490f0000c0d00d515407649554084c1c0c4410140240f6141071014080e1040414404a06103031003032205ca007900d0f0120541405e15105004c00211694009059108142c10815419155915015580141001c01019600a03040c0103000a150b8560751091301064021816100c01005600c201f05c40304c511841e4494141e9107004410040c40c501c0c1c0d0040340740441c024040c07002280180f121240c0c6908281068001030804514880181003d004150380890115010001c542c100800010207001d140260 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 156133857 1250 156132607 156132623
    0x807030c02030403080708090405010602120a050706060f0b18101407030905090108030901140c06010e070207080106030311011a0342071101060806060607060f0507050a090b0301050a03 81
    0x40c40d03680e000384101c80c050350700000c110307507508220b0912001c0c0c2c2d846903241c24041c1d443c00c1c0000518038130100304011802020182c8501e003200d00d0400321084e0300080d02c181c238800d0751290700141c3e540c05462590300802020075466192050441030092081c0c0c031401040c0102d050000780c084440d0312075180d5444010a4000c10b40b00c01c0581400c98203185103070003081e00038040b00000704906500001803c0b008409994125040710a0100f400150040300c040b01d02541c0b00c6001400816041c410f4543e001205104854486588550760350135074046a10030b0303010403604586140d42503000e005407250070006401c0b0710449042e41c0046555907500301900512041c45803190380c000400c005c071018030400c04424182c6409405c4a0000c0700400c02e445c104040b40100340036011680041c0203003012a41c0303810240400b90303104001d01c46242d020003800c41e1540d664100308041f83c0c0d01c82c460f290256425980e455103d0741303842d2001e001e00d03600350401d84107010144010400c907a58080b4070803e483d802041c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 156135107 1250 156133857 156133871
    0x7150e010c080c010501031103070b041802091314010e181005150d080a0215010b09060d240302010e1909200301090b012c09180f1c030507080703 64
    0x5406a4020204110f40d95400c3c40700000c2880f0300d00c0c155180c4000100c0c1a6005d06945402aa803207114901c1126444882c3c14a1a10021061b80c0500f41407000501840008900c5824100440e040c2e0003c5140803a031200050200044d2520800e0b0710a62002e581c0740d400c2d910300c50155503060250380e1001d19640b070704001f503c0139443c0c1c0c100f032103504009008031180310000c0c07a01c1c54058100d40c41c1d440045c07003900d142d444801c50034944c69040ba521106614509041c000610000307034084c9012040144d1140d92071607003a00140b40000312100c00480d003014481c21407000410013290240070606c2400085130070b421500c18003410104603034000c540001d101c00000780075070914496041ca42c0190f00080300024581d815500841100f1409984000d80c0140c0d0042d22070480010b5a00908a1004401c0c9002c540c00d0100c80c041d044115903a100000c1400d0040107440c00d2500e08141c805600f000c0c03050000001704101c4034203110505d080074400c0f803519410042c50b1440080c00c2c0070406486101c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 156136357 1250 156135107 156135113
    0xa0803070f021210050115050304030504031214030f0403030606020c03070e090a020a0f0608011e09020a03060e010609080c0301050708040803190612023a060b03030c0c0307150e010c 80
    0x11500300c2c50003010058442452095900134018402407254018103d0805490b82d0101d100e04200c0f44120342c16100c56003400d05540301c3c0e0104201101442083c0070f1145002c042008003000614403510702e0740801d803118502864002c0a450541c2d1100c0c096500140103819140ea0100d4044162281d0f034016001c0b036a60788003110b1a2425100001c1e40183d540303c00811021407400f8840140c4803c2c0c0c0b130704031190366101c11402c03400002022914003442a02000c0c4182410b9400610050545203008204507484010701c1030085003c0c3c4c41100803907500c040810000b01306026410742103604400030000c8d0701d4407110180605900070300040401c2c90000010382d800c0c820809400e10a203680d0010131941d40c4405d400d4000c003549400907840f0f070440074203401005403440c2d0320346510105818038880c403a441a110700303c044443e48040301c00903220207100c10a03480c100090200c545c9a0002450402d500308145070500240750460f403102e0000e04241c4c01c6668200c200392081140c203203800b0304c0c80350281c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 156137607 1250 156136357 156136369
    0xf14090621120a0201050103020a0609060815240307090b0403050d0807021216140d0905060a0c1b05011107080606210d0801080f070e041217040b01140a0803070f02 72
    0x300a201d81d0b00300402c1111843e9415071120781070700d00c2541c0100304251610f4066034401c41d1840340d00001203988001076051040c040810401c024050255004591b5030b140c040b50345c4882003000407010b0350101c104105039602c041c107440100524080075162a06503183d0340d80300c10700c03841d0301014400c3d45404204007074800c000c0300041c00503d02202e40c5522761145d1149194540d4801552914080d0124107141d000216800105541a80300d03012550b20b0001071003059001180d00c4410310829008900110b00d149100d03c10700c1c0c1c0c981c100e2207200d90400c0005489100d400c0000c101551102d5014000c507900056860342080782100c2103110040c203104483c00d04041d80e49407403200d0007101d0b0011f22043d00f004149043ea450b15090f03c508803c021992550740105100f0150400c180300d01080110b4001b1b44c0100b80382d43c1c20b1a28149000425800c000824020f0300c0440c1ca029029004220f08680321441a00601048480000c8540b03890962582c1c2d0141400103400c0b0f445a030f402008556401d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 156138857 1250 156137607 156137623
    0x20702010e120c040524010c03020c04090614100e010e040213060b030f0702030a0c030c05070e0709140906060702220f1a030106050619031103010f14090621 69
    0x700228160a0b4041509403502d4001e030205000b10304001c007003410400d04c0300c400c03401c3c0040410069081e800354001100d002da40c0c81425404c9d401000e1402e40b841d1514000c0e80031460103540c0c04652610402d089242042d001080700a00c5185480305010280403880b500703044850a00880149803550300000b01c0e415405c2450301142c901d09640029001e4408002e50320404140a03241390310340d50b403403042e61284621840000000c0300303000400002401516105107190040045564403500c3d1540d0032001c02040e541c0001260f400c9408100180491034405000320099440380007505142000c180b941c09200f000910400c00085007900310380380c00743c082c20030004840041c4005002080304000404000f08180101c10b02078080382e070070f420140075060855002419151511b400c00c1700500040303a1700075050042603199070b100d400d1f0341c044c1e00266000c0c2c148540905c2c0900e00c1d080000c40503510b00f0950368040c0000e0010082c040da1000300d141082401003521811564151400e9070500e4a9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 156140107 1250 156138857 156138859
    0x30901060f180b0405060603180a050d0809070803180d02060904150f090608060a050405032b05010e09100b0a0f0906080105090a08030402010e01091d0417040305030d020702010e 78
    0xe010750000e40082c82c82401c01902d03000700410000088035000b4002a81e104550842d0005010000308446140208440c00301200c1001500c50004c0e031943c500341002000800c070000034800205003c020700b4140014030051a40c800190f1405180c071700e000003020204a40184204c1025280c1002d6484401c11941660b070018010403002074480641584001140203000c80d1060041000c58181405d00c1000140d4020710018980c41c1d40d6981703d20043d00c8001d0046032240000c3c4000351200300304081d00903c40081c22411b162254130600c60348225481644842c920310000c805200c1034000c00b19808500d9122800d0214400c15200042070341d0902aa0010003811002d141c00105039a881d44a0001d44404074000d00450300c900c068541d46004440c0c000d04545410004600150300807850540d1209042c10420501503854124160015041610401d004c2c11031007000100300400e4026508000800c2005040c0390458aa441c0e2700d01501c41c6d5403000b07a41c0040d0036415a8060001c01c810514 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 156141357 1250 156140107 156140129
    0x101d0d0605040b160c0b011e03020a0611011401060c151508010b1002010b01050406081b04030b040506070815040f02090a0f14041e051005120c1903020d0803090106 72
    0xc240c5005125020308403800d885850a443c3c1803800e2a20a0004d198510303001ba81004159003010000802605180105902c04461201c00001601d420340420001c00d10703501c0d003010900f01da44501c0c1c20743d86030070b0a0301584295540184106074006002204040d08203d11081c442001505c0500501c3d800e034040c8a42c2401c6000041c0d01d1b10150440c814500c0240c0701c0c4020030181020503401c1e41c0038402d045010a10512050003c58441d9501982c41141c1e50001e51000064148200c441d600503001076540d04400c000300300130701108100150b0070514a00c1d21100c1c0307250200352110340020303c030001446141c039180054560003d60b01600c5080400a2030003007200e41e610540420294903108400a103241c48109040601e03091150f03145400e0b04284144000e06d81241031001028000c0031f000280701e140c2c1000c50903449045069030340c80d41e0715008141101d400d80411840441c0103020018001c5103101c28401610f0300c04480c50141d9000d22001d4403a01c49104e42805084180c12407441c6074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 156142607 1250 156141357 156141361
    0x3021b09010b070f05071e0b03040314071104090f02120a05060109020c0c0918060a0b0f010c0503070606230d17070f050d05040e07020f0706080901111602030c101d0d0605 75
    0x4540e80e008654030041003503d11240310fa0788d80c50804c10340011100940415402d840803040a43d41c10028500c046c0f0840000c017400c0d40b04400501101c2070b0b03040a0790140c1c9592402002c41c24202000042c807001c82c2c0050440d040f060f40c0f00b5a40d02c0c01402410089030700414003003000d042c20000340742242402032410405160241c03c0c10b00c111907880300803411f4030500012419004107403180c3e500100c07000c0c01c1d80310b494a5400040d500240c4c195001c131a10301c410420030700400c2540c407540c0043d00204100c225210341c14603804203d0032400113620f22480031800035600140c0d035400c802c2c0c0480f24034254641c4500d2241400d4842a02041c00586540680c4c40b900134241d40c00001041918104a0f40003010384035040200c0e624002d00724160101d81c8109000c0c01039a0266012903413020f00d41001142013040c3c01c00d403480381d070841c58034041103004a2040e807003145414003c03c254800700b42c03200c3c010b08214607001003400c07130032002e404240f185c611034001564840320b0b4040d1520790001c00c180454 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 156143857 1250 156142607 156142619
    0x60302060c060f0606070f020d030c150504020a21060e0c030609030307030f0b010c020420070302030c010608010207020d08070804050405040302031905130303080a1d0a03021b09010b070f0507 84
    0x601c403c86164001c4014000040d400d850480305807041903400141c40742c4605402e90904c41103040b201740590170710031403001d003600091104401201403070407407002080038105441402071f01d201c6600520364582042101504948502009115081d0044004035040f00032025039030421040440f166010b00440b400c00101000c00401140546166582005031488942101c412100c190603528006401c18a260300949417a400c00c0601d26804540960351090704c50f03c164040d842044d048016800108115002c101c082c0b190700c0046c00c2e04c4009502d04803407035000510302085000c00508183e03000c200c0300d013408201003d44010b0803001e4000c004a04050a0103992508501c8400c031181022030220f1006921500595505250420000b00e0850440d541925254001458400c0c038940d148001c244c6047e60016090303092080c0c0c0b015040d8421f0300d0500038108070407180101c16140c2349918002254503001d036900c1c1101d0156550586541d01d900d408072445460b9003019002d0f01c148140860300d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 156145107 1250 156143857 156143863
    0x26060d0b07021f0c0509090702011401061710060903170f07080c06070905010f0e0f150c0f0c06041401020c0405150307051e04050402061303030503070e01210f060302060c 75
    0x410481c20302c8150702d0143e110900400c1e01e4205441800050042c0030203007886c103001ca00c86400090900000c0f500e032042410050300c0c28000d0340b004c400114610410b090303a04003200e02c00d030020041c1c2600040d5030b0a1a401408024403444020030300c06c13444403a502c03407400311802ea94070940d074158616a90111030502161035005400c0128190090304013141403a402114a00d08648041e144c1d40c1251103861001d03107003d4180350f112500840c12501c3c02c65190341d000003a00c03241c003102001310388815600c4100c510300800d4005100c190b902c814001d408507644d1100340c808407213046982104800b05a00100c2c01c203000d02010075045400e0a060103c1c00030300404105140b001035048484860f1788004112140d840fa404804a290350803c4601c81d80c18a600200d074030074006800203107000c880d0a1040d1902d01c690340282c0003d2008000d000d0f5883d800425040308450918000021700c500103070301041644143c10b60a0015075840c05071003620341c141c004d0343c01903400400e0140c03280184a4801d40b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 156146357 1250 156145107 156145123
    0xe01110d020703020f10020601050913021f03181110050f18010305090d1b050a1203060303020114060916020111040f050a060801080604080901020a020907020a03020c0126060d0b0702 80
    0x1105d008102c00c21002c03402c044200402c0603044c2d0b40281141c0e4070341001e2180d41da1028001c0100e50a605590f000980c680704509221031034080f00c4405c4075481c00000800300c0e180f010050802c40760011044010540b02e071110442d000c030031600006050702003034041e5440d01c5089210740701003601054074000c220201c00c800c07824201c00c0c1c90520841c3d031103d00184d207500416201401140e0506511101070810005800f11544200c0448078078081da038960282c180d60b0418491f0029440b840c041c0308155080c05404000020722540151a007802000154103950007450109a075040140007010a8800d402280d6800360380c0b0300741030352180c42c0c0340120120741070343c01950300550384c4a100250452140c90318a0480300c120000c1e080b40d071550b9032040113a9006c1c1060724114400e42d0206409a520307000d1075401030f40e4a0b001003018102c149000303400c240610000f541440042071141d042d000312203400c45d1030308013500c44203e1590789440010782c80240811002c3d11902c0d0040410070b480d500010a68 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 156147607 1250 156146357 156146359
    0x5040b060a1a160c0504051003060b090103021c0c180606080c0304020a0b0a090b121801050609060d02060c030706050f0a0902030c101b150b0405160e01110d02070302 73
    0x1040d25442e1007205108107040c0c01c105000010420142c03416041d140280881c96102c0d8140000942c4c1c2e0344001000d6480c1500ca181c105403180703804008018091146880d012010303904201c4540c55074002850b0082c81840c0e02c0d120458822040f07040201c400302000140030640490b02000380160404001000940a8280400c40d4000401d6000e4042c0c800d40b44650340c010302d40040d41d41005681d0032182c1000da0b000741440201500800c400c103540e0080d0900901d80320360b6610500c0e2803203a001160740052848000e07640342005201040d10340e5010340740d000409036807880d4948524070109200d4412504180c5003404041144010011140c01a5014079006e1071502c4c510307290300740c007002125004203001f50b141d8026241c042d80e83c14412080c00400c20607040101c070b003008114118800d131030840c1e402c85411600ba50005200b14242c4100c000c00c900a4404200d98509100001504480f1030201d04c144100c2c0708010000e42c0c07203a408801a82c3c0490103450b0242e13410f07c0c0c06556952940412 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 156148857 1250 156147607 156147619
    0x30308060607121d0f090c0f040f0618051c02090907080a0c0f060801080616030f020c0a020918070e06150a020d20151506071b080105010501080a0c0302070605040b06 73
    0x30891a0407440e00c250001c005202d0007403507c078140d000390141c0c407544000f515000180400100b00c3e4820103080010503d0383c036280d00d00720400c1d0350040740c00715641000d0b200d01402016134810410081c1d007c51011340c1519000d0054950340f92203458074419502842c260700ca030081070b50410842010140c1295900500e54000c90f07110a030580d88a02c0c24000c0c4407030f6500c00b00008012940501c0c11a200c0501030900003190480319080c01c1c00e0780d02001c01190380364000b001100850801045850340580c1101d50900120501c0c0711064803401544511078179001c008003c42c907943e480c011090044c00c1c041150541e98000d0311000327510f90100c10a04030100302040350407044040c034480300130824106e0001411000400201c4000803441c003900c0c9a05071000d040c3e400310251143c10042070f949000f04822048030340c2c0002c03000b1241080703402c0b01d0000c5e4144801000745980042d044c60f00400d40c40d50114500b603c44000710700034000d400016015038103001c1803105101c05991402c1c0140c030145c41b9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 156150107 1250 156148857 156148907
    0x44b0504020d23090a151e1407020d02030409020f04050925020303040c03020d0507090c050c0c031b0904060f0216060b1801050111100e0105061201050702030403030806060712 77
    0x303d5107440c0d4211030004c06900985803181c00078140b0303c6500502e0051180000d042c124445908668403074240c0b0780c00c410340d50b5075106001e0000c035802c51503020225100521141100a100a44034003641c4035400c442500881c45035043d0381c1d6042928051b101c081e04120030b0f40350180d00c009104040050268000340c8001090715860701c08000c0303074441c54001c5103402d462480c2d80d0900080c0e0301c00750415075103030080070f20104080b8814000c44642d0070403996425103030a840e90200b42804007401105100c1e6001102130680100e5a1403060513a0701c04586450195a40c1d0a08401801511610703103202840003541745203401000140c138032054001e4000f0444540705000b8444642c24980f4500101b1500100410441d803203500d510000c000c04800f61240001c4030f030040416280312403c0031150342d441e01c0800030541011710132500c1d0030590304020300036400e02540103501c13031003180000740401c00d0840001d4041e40307a00c0c040350310300c5901c0711070511280f0300f88bc0010840b1102c0b20030200003072213941e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 156151357 1250 156150107 156150161
    0x11100513030809060c0403171207080a060602060402150f040b040b030f07031418010e071410020d0e010e0a0305150417090604090509070e0705044b0504020d 69
    0x144c443c0f00d050b5400b040c1e49082c0c107544400b582c2c070f010b0708003000c4134400402030514005c045904540c011001d035242c0c0e28042c1054000302007511920341103981154840c108000c05641c0e900360700126800001b070f0555a4401c1300e0322100c010b01c103d40220b03039100c000140c00101c03e8411401184141c044502d62804c42d02c900e04100c05a4150501014660b0b17010408200b00c0c42c0c2070242c449580400000004114900f558100e0504a0030340c4010302c01910390031307150094140708040425102841c030140c50107114400002e46a1012078001074100320f140d40d00740a02c2e489442d6000c02941d0440704840502c0c01007071100340e407050101c0e0200d0305004e17116520412013035200e055a20400c40200791909040c100a206001090000d00c40c8003944a00c60000406502120400b801103542d95501136a60342000d00312074100300004502981070001c60300000c10200c003c2c85034000780b0070354050f80c1c280d4509428000035000c5250001c40c2c0c480e10000e4502d008104603403010b2201440f4150b04002409020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 156152607 1250 156151357 156151363
    0x408030c1912030b0120030d0c0807021005040f0b0405060907050f1014070804030308040b060d170706061e0f0e0103050a1509060515090f06060a11100513030809 71
    0x60381c0140620a08821100d02c64040c0d008031084442c10f2400880002144c00e00400d03544442a2030491900300080c981290000350255045460003410305000b00d0920038030003035460100c000c0042241e039881c0003240400c010f912001d06002d802026988590134a4181280c60703000c01e90f440d0221f40703c1c0310710005440c100721388940341c189001424240d00219140098540701c00740344820726914020494400010000c0010303001440c040d0f991110f05180ad03103000c0102c008090241da200300440c1303040400103600645801550702d038450040762a031001c0c0c81d104000e40007613000b020000c1d2840c0900c0b801c641c5d500c2c812900300e5a0040300c00076170a9403070907140c2c8020020b000150039070f0007070074020010615010390b141c0040842e400000c2d03640c51940362482110410380d0301c08200c0d044000d04d2552071515030b014a400410580d82c024403401c11500181251041461442c18062080c0f000701c0b1808040c4500d130a59030501c40c003446203142020307036980248101d80e07044003c201004003043c4410000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 156153857 1250 156152607 156152653
    0x14010908120601030c0e030d032406022a1309050a200f010c080901050a05040f09050a050109020315120102120903040504110408101d0d09051e0d120905060408030c 72
    0x40c01920452848113400c4010704080c0d00404801c091041c2b00e208107001d2030490328001c0c4016805421101c0d013088080c0880c089001456200d03030f046c01501e804543d1080c0d0b039410380407030440c0c000801e10428a055400d142e5004005001c007191005200103030620014440e50a0301c007222060021501c10005440380c454502c00508003100510681345154010402400c1181c4242481c82c10650760b01e62044548029401055115454000307110f43c1d41c405008840c0946044441541540317000810118007811075080d1a101f41d01400c80404030300001e40c1101c02c0c05042051740003091419045065403544a07104280c0581e1418544609255610054505551302e1602a10580218401450140c10900404064203e003c020880460001c0210b04005100d40c1c54440b4150316200400944010b030f00340c041002c1c140c0d0a01200144e940071040c0260710f078802000510b031040f0345400c880c0d0306401e03040240c10000006010079600000405001003619003800c40d9440802c12001030301001e45 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 156155107 1250 156153857 156153859
    0x1f030c0f090e04140a03050d1104030803041b050a03050309030c0a05100f050d050906040c0803040b09040203090a060216110102010b010503191b1701091814010908120601030c0e 78
    0x741d00c80a014805030b540c04503811901410b034600e544440029003900300600502c0407000f054000803000d00450761805080080c07641e101226080c2450358885503200c0c0300007070004041031094298446204008581c2e040a403d000e0014652079440b860003581d65070181d4032251003446022112561417801c4041a41074520180060380383c5031450f5001d6420248006190b0103000d030912010750955510700c030701c0e032040c05441c00510310703410641802c44a040711034000c001180c00c100424460303640c0301c60803030303188181c260380060b44c07556082009800d14081c11340040401d40006800c107446c10200400360241c90050420002040c0541d0044e400c0b80c50340030245002c0b034020700010744c540304814034190300c0c8220502d011541400e50240050340f00c80e440032a1011030460b0b0b0524410010042e035003805020000310801c101d04000600070150251402c0c01480075805441400c4194420740101d00706942c401010b0307480700f82d0382450640c8100e049821a00080c903107000c10015521035440c0e0090354034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 156156357 1250 156155107 156155117
    0xa0f1805151c1b2705121006030b0601140301060206010b03090316030504080106061701051507050610030b06300c13020d18050705100e1f030c0f 64
    0x341191064a9400c90380c6600c80d031a081c1d0304200c200040301d008080001c0512440d0003451207071094050050040d258655480c42c03480341c10003154613403a00c0000c007910700840b0011a8000d0500d1074074601030002c1c065106203410070000100308800314144600680c000d803100160384010b0852004240024480e140040e44410010021200c114000790341080e01d001c1541d281900260200e50741c28985001180000c200140421540e4028030500024050034500403408000c40e03004050140010b02540c0d124000d035080820714110500f046a141c142e00c07c0a82d403907813414a42841c641c000c54402510700d480240001201d40c030707001a4040f10100840c8040080c6049424250301d0503001600004451040300b50201e217a0380c80c6d000c05040c030500c40c0400341c0e540c0c0c0788924540544801c444070203c46034400d100c202c0000c03404a259002d41e4400e80308202c20b08045142201e000c5852007000b41c0100510f049418418004121094294240e413000d125500c03c078601201d0a0440c100340d400028 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 156157607 1250 156156357 156156379
    0x140c06271c0201060b21190216060c170c160c06020304090605090f0414120c06090106270e01020d0203240a1202060c12120405070608010501080115140a0f1805 70
    0x46c45540b02c90f0700f2842046041e00c810510a80550172680001640340c25410803692400c200900b601484031542841d1404c904030310b01000760309048000180c0300d441a036501248140641702400b281d04504d54101d0071000c01c10b03039220b401a44907482400350384152420b001c00400d050904c50001400b84d0004140c4403103d648540740d034802101d0404412000f80900014890392110700d4000e40a04844000036040508120050600b100d20f281c1c80b81030721551000050b4440c40f0404900d640042d07054001284500c14080d101e80244103410300804507a102006100c0003030b01144210420b411507005141100400320100415401c0c6403103102c0c640140701d40307100d00501f40403026040b50207002d17049444003504509506042d030804001c807007a0a0900c8100700c248803080010320020842424010003035418100001c28604050241c1084007500c02641007003980b00d80c011a214141c41c10041e61034000c03100e001420303070407820481c8000692448100d0603041511410070210b40c0f004207462414 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 156158857 1250 156157607 156157657
    0x1e0521011712031005060901030e01020409021b01110913090c060c060c020c060405130e100902130203010b0f070f0b040302030c0c3015010e07140c06271c0201060b 72
    0x1c0d4000107d20b070426450310301e595140c0c50240080c002618000c100903072100d0075030000c203c08202e810340c4080143c0c1403184111015520000720381c011602540c1d40e85c52000308842000140014940007041c2c450a8400040d0555004510520341d501c24041403201d10200343c0c0403669400744081096101d00d04110410843c681146100c8010303030403120218416070382d21002418451051070354900302e502d8840130320440c0f40103010102214803880e411070171941000c1c0910450701a00c41e4150507001c00040050134480c4018098a07015030100119034980340ca860003d48a4218540b03a00f4544504407c41c211031418490804858043c00e0f41c15141124882d00040c8400d01c820211400b0b00500c1441c02100c0b02c031942140c045c1c8210801c1e00c81e14240000020b005041c03e00d2602640070f418081f6000d0038601103905034011001a00701507544030005081840b4036140c44c800c0b1190f2003602d0780505654072410306021210200d070020448181d46003402400c5120f105026500404007141c0d0310f8076 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 156160107 1250 156158857 156158869
    0x17040203060609091213032603040206180d03020c030d030c0c1b21050d03020406051204020604050d0308040b06030c0a03120513060804020906011e0521011712031005 73
    0x8050904002c03514585131014880074168045030f0141c829206c0c4440510a0040c101e202c20740b03129640300345289100750328400919a01024100920801000900c108002c640007980d1750103500041200d8070329030703482c94040e6456814403803460080c0114042c04076024004e11801505501c03071340b81c8190031011070352038003802820b0070300070301100c2106000410041d4a4401810380315031380c60748070762036403030582001d520f05110407000c4410140100000d00400d58080c0a64040d030418019000300c5807078034400951070303000300d4101540103080c2c0b1307401d02c00381907014060034016402058890340d02e44510042c1a25190031910141c0c0140f11b2007420070020741405000800f0403030501d04941088044400103482410b580c0c003141c000781e590018030007585000030509802100c2401e002d0b0b0448410300c42c0754030340117190142e07000340140416405408000c0c00541c0d2100e14401700c00724159a12201d0760304030000340c0c140182c7c81e8402c0000641d4540c000c007088900034400f104114908600d40010420 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 156161357 1250 156160107 156160111
    0x151401050907020a0f0606090c02100e03040b07030c0c03050105131e1a071103070606140102070810020903070e090d0f020a020a090c17070801051e1e0a0e0702060717040203060609 79
    0x288180c0d503011f0015005a49101d82c03103a00403142d0141241070321139407421040e2501c011640310703c1d40040008106681c10441110075803a498103001e69100c240707041150f40745045a01c05861542000c00300003040031060501007595101e0f4040c0814048ac2d4074a44400b55003500380206205920303219000c0104880c040700fa4020300f10300c0d22800e481039041465086400c29901103030a1610b03644284480e802c04a00d0071020f510030f100030015076242c105042e5035400c400440d908460303400a03140c080750b2030500099000d001d403102c028046003040707200d0955424130010b01c100041c0c0080080a071b042c0c40440d0f2468600e400410314590789045c41e0010004180c2c15170264148260300030140848405d581202e4881c20b070544542040c2d600d0b102c280305840e9502d04175041e030384200700a514056690420b030035942c0c2224410b05280e40d18142c0108401810f0f40e0001e545040c17038a010440303000e50001e4990704c03030b05203595110b4807400840e0003080b01f1141918003d40c10b07000080003910504100d2380480e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 156162607 1250 156161357 156161363
    0x3030a050907090609020d051315051012390e1015030b040c020f061b0c0a05160e040503030601270602060402090105030708060705070807151401050907020a0f 70
    0x54442d96440d0403810071140e040e448944d0380380c0c002c5003001c0c4a00c41440f403154054005d402112199883e0b503076280c1142082218462650794980c041040385814007685006030443c18083c06445801c1c0c10082d020580380346220008090069951041c0101300d8062204800080344c130300b40e010b04181101d600c0c0a80102048900d90410341e000526001c034162061800c0c0180d1000156411048240000e982200f040c030801d562002c51000c900c240001601d0b070344024088124120202040c041d8135061094240d0301c40c0c6407007032a102d90309001002c6120160307090002400c00c40d040d030704c1c0200c00f81c11008490140040c0c2091001078515400746118070404a80c80c540055602e0442050b070000c0d1740280c1003100107900c5181003000710304040060b0f6000d00400c6008200c00752501000c0c0e542c400c0010300e6401000800f0449900700104401690801765001803c4840e0558401d9070000038056041150060112a4000100342c00c0c164842030141055034054400c2103581e4644c403054051001c011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 156163857 1250 156162607 156162613
    0x20f0904020f091801050d020603090f06040305030f01080106050105190228020109080307080a111009110f010c0b150a1a030103030206070f0e1002030714010c0f0903020303030a0509 80
    0x6484654503031006011200001940988a10081d4140203400f03440d0000d1003080402e2000520040c0e80b00c00c00c0c98100c03507040b40e48582da40d48000b44a410803034012a00100c900c100018070007096005800385111304000102c1001503030b40c46195078280d030309611640b400b09004102e01404140301e03110007044072400d8012101840341680100b204c460706004055107007104841c031079007150f07407094000c0000e0200c0c100450030700c0b01030344030038909102d141007500c14000b000c82043d4007504140100684441000e008005035038450501d40c1e011502d0700c0002d4400c0c54101002c0d5295801480040111508002c000c05207944854500703181001590426500c00d29114001030401c61068030642c42c51038001001d52654514030f0301030301d401c00152012051280c023603500005190b103d1031020030340c01e0448841085d002100b074240d08501c142a030190204141c08104420700750150042c1004010560b6510284c4010300001c031400350107408004d5158004101217a0b0024058108680005801c015 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 156165107 1250 156163857 156163867
    0x506071713060e06190b09010302130c0c1b030b130b070e011b08070b0112170304020609120f07060306061704050f0a0c06030605060901080a09140111030603010c020d020a06020f 78
    0x4200c4c60902c0c211a12000c03842150001d006210700703402082c0001e030f0103a0301d62a2650569000940c85030985646544055581b1780300301c0d00038410700810910130b811102c0003216003007078007072000c0c0c0e10060302040e520300e5200340c081104880c0480b480c40c01c2c1504061714490989941074100d80d001250750b040c1c0d0400000f504094a94044995840e1941e4860714400355611401e150030101200c05078405100300b2009907580011801d00880c0c00c0d4002821020319940742d0b01c80c8000344040c0140f1506a4002c040601d54400c61140024241403003465501200c414559500088066039081d0003000c1c00141284120b4408428265075103400c54071503130940d90300e0020f40418500e0300c07003581c4060314490030600c410041c8a0309440307240041c000c26030302c03035250625035000a0060600540b11651180e07031403c000c000c0c080c950141d000c0d00381d0414001e00c50329008c1220781c0d90310f0700240c40c1640f081d403900b0440801a80000303500c01e581078254001d00080092a100c400007034109020003000d001c01040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 156166357 1250 156165107 156165131
    0xf0103060b040609080d090b0d090501020409020c01020d0b060f070611090d2d030e010513050909100b0d0c050d03050409020307080106030b0103050f0c0708040905070507050607171306 81
    0x10b4000b400266442124041c035282d541498903c131440164203001e40d100003448900b071614211003480c0e40c022404241c107245450810b00a10481c0d01410740c09101048a503400c1c0c0064004040d1944911001e011200c0c103082008820321805105401b2520304000500c0001d40940029415140004900f03090200220110700b450290000442d11a444441744041d00e180014280310a03e1301e004c0c0320100700c1615079002c1d04c0000645a25030500401044404004120b58241e401401e0040c003a18060304100441650700e21020a82400302410225065103908000708005501174100c1c1e0740000251604c1c091103900070382c8040a40402400b0407010440b038030b06000843c001c00c1140d460300810340c5051001403c445c212000e550405090031b003440014103040700c2030390f008024187d04556810551500300074078480c80d0303c84c101a42c100400c002e51030350040040c00485000c0d9080c0c0b5865519010300301c0b400c0c0001076070458030300084004264007142800c80048080d00c950000180c14071245 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 156167607 1250 156166357 156166379
    0xa020904060207050706050a0504141c030203040504110705120f1201030b040b01080102121501030b13020a030509070b16020f12070302010201150e0a0908090d0308060910030201050304020f010306 86
    0xe5080d6a001c0c0c00060380c030100101000814000d01540c1f4045007403076601e04000300544217910a0602c112800854100c0694501d4014031403034884840c60114034545180c00380d207980062040c6d51140d0310b443c0040306408010750880710510b5003c6d02904580c84004140f1199400120800176001d409200072100700f072480e0107982c065401424448810700e0b0610780509401c5050300880c5071a40103014a1a000510304a62900721030841c40141045601e8001203008102d01203202c0c1d40700808440381480c5403065070050501000c551340920582c1c0d61542c42556a8174644140621849c0030018001c00070a16041060396620041c803850100900e079002440020b86400a0741860300404400c1045603024851030b11490918849500030074a8511040b81d10b607001030189080545900501c0c0400c105441256480c11004142e4182191642001010804100c4250b8065034488011490b050350001408003100e0f816582c1d03500d556136950034400407694204001d41032644408010502d49140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 156168857 1250 156167607 156167611
    0x10302071a091510150c03020d0e060c07032001020307020102060c070206090a0602010c020d0e0117040203071e091404121206030b130506010f06022d03040f0503010f05061c03020a0209 81
    0x801084d00c4490b084c240942d403180704d1505510184000c2c0303000c0c08002034011424401400b01c0d401c00c44440b04045c00406e006103c0c0b048a4070490060031408404c010440f48141c400d103401843c1c1240901078031006994900c24100080c0c0580d019030002100d0701079000003000054405011181410341e10804100080816040f00c070140c0d441e0741c040d444195040000080c4a4024030b41150324990010028101c021014111040c1c40c1d0682c0020742591000c202d014014071170030300c06403010046455802010681c81c02401d10075070402895602514001c0c0e8880d01842e04a1040300074402610019030702e880c00303c0803036102d40741c5540c40000441c2000f84040e108021031900010f80c0d0349030307160030340c2070040581043c100d418410400b800300365800110100d141e240d103c942c02e5540000030940540c1900750480482c0c2e4403000801090384030f42070344088100e4006130020b0200c0c2c0825400c05c000d6440403650030340c003d05109128180300c400115041a554042c0c0141e40c2003400c203401041541000b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 156170107 1250 156168857 156168871
    0x3120c0f04150f020c0103063803040309181406060a021f05150d0803180f070b04052b08090109050913050f031213060e0d03090c05010302071a0915 65
    0x300300e56543c2000c0d018000900c10300024070382000040c0c100b0000c000c1510090006103625001c030040345164403107291318000300c81d20340340095449240c545801041690103008840031101070340e80c441031520090041034140c0b101000402495562401448401e42000d0721200851103580006051034000303444c10703044500b4090000c211464034401c8440c3d09406030308698090f078880d012400c0440c200d042030700d4003c1541702d15460554a139040d01e82c5451b20610888a5078061082c1c00600b80100350010400c90302d003070354014066194080e08118014590051040040d201001c010000714900020102c0090506010000c3ca03201c00100340d80070012103c000d095210b1840c480c0600a080250240312007800008615280d541c0c1c4141c1da80354005000c0032669914103807007008200c265000000300b15035100403510140341c0108000c001e4540210291003040c10f41001041c0703940719000300c0300d542c1e800c51506000521540062a14994002e2480762680126502d1001a00070340700018001c201c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 156171357 1250 156170107 156170117
    0x2031201032d030e01020601150207030206180306010e0a1d0c0d0804090c020106051207180e0a0803040501020702120c0a0501050f0c010c0f080718360c0e0303120c0f0415 75
    0x4d0a80019140a8044c0c00140e6100d0740007155103100e540c0094024150303a07054074a2622072040c11244408240f100d07060541c58041c01001084600031414140d10610181d0001c0c0702c040101101c050381628607905019060700400e070340e903e65042040ba901041c1d407082050074506561001d50000325140e0509502c0141d4580c1003c01c001c1c03800301d4411500400c0580a04180340c9029110035a030329103145600c104a869082c40b0841c4403040c00700300001500513444580d0707803605141c2035000350311202c2d08910617403254900c40024100052416803102d80035041c2d0000508143c019a02034001c040c9110078402d0411185002000a01800e005000d280d03c1d0f1000e0100c0805010b030400030020444410800000341e002540d00b8002d541d0307421240b13843c3c03686031200c21008142516890090951901040300500b82c2109540d41d030008400c80c80a6039071b4501c1da40984101510380c811f044400c016545100042115260944000c080e241c2c546418645455076a44c00d500f04110110580c0e00400c07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 156172607 1250 156171357 156171377
    0x41a12010c09080706020c1e0a0308041707081f091703040c0b120a0902010201140f1909150b0307080a0c0e01050301090c03030813060216021002031201032d03 70
    0x16400481c0c0b000645102009003034558200034009545100e011801031040042402941540d206062141d2074010040d080d050110b8907410210081d0b4800c1c85144c43d8046607040302400c0d94404200f82041d10b28a13405004040040028000102c0308400e00440d01903950840b1000291010b0380200d00603600711038107031a4a018101203141c20002c1c1d00c9506035200401602d40c0c0303003804d000f907036500c0144200000740721601ea00040b8010049800d06a546200074014002020002407425224a40c0f00c41000e6070f101c0014a0750095074a404401402060746000c0d40110b040f00350429880108041c00300c5a1040d51100344500d085180300040d10746c105a8035044c407094400d040e40b43d014100980003801610840e40d95001d03088a00d1001404104070600440c101d4013100c094030a100750040340564445031950711945e41c55080e000100d12450050301c400043d0350001c0152069681c5082200040da07203942c6500d00784007a40340340304032004101c00103171071550038079222002d2417802035403558049 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 156173857 1250 156172607 156172631
    0xa022d0c0613020f01050408150c120910110c030301050f030a0b0a0c0e1c120302090a140a12080403080a02030403020d051011041203120b060a020607030f02090f041a1201 75
    0x74130080f04440341005001c010034004604001084104c0a6200600b682c2550703800c144a203d501902030340000c0504001d05000704990b00244510501101c0c020170031000c040000300c2d6036188035145002c41d1742e420a0004100070f10703100280b00300414016055841803041c50352646a0002d00f29000760209170344204111405a00508000002e98241c41c203d14150031f20350340845094800100030490b030b8080c1250300104d03220b034050b0366000c60050500d0440e1500c034220a511201c5c030204031405160540b00028000f00e00b91506602c09170448a2149040d09686a41e00c40d98042c0c11440d09508c0208030000050300c4a03001002c0d414024409024444ad1078050401074070001100707444a6541407005000594440240c00d101c603616061080103060803081030b102800d8031040d0382d9407000b4089194408ac1e40c010400c107105601341d5604000c0d03400c0380c40c0c6000890054800054210484000603403c50a29034408030907510000000e45402d81c2c000000380440383c41150016099440d18140149 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 156175107 1250 156173857 156173869
    0x3010605040e1e043e0301050c030708041709060d0501030b0603070501021b1c0f05070806010f0e060f0901150212070807030309080c01020706060e0a022d0c061302 72
    0x484240490383c25600d4064409440c01c0700040d0000c0d0600c0c604004e42c0c0d121640442c1e2400c52803090100350302d001000f44521103441e11903c5103190081d401c2c4000640141240000c4901c200c07225124030520f070f00c850700c07003440a0a03c0b008492a009082002c4c4000d90b0b540d0000d09500c0d0f842c0b00c000701d0107604604c1c03d02441c48015041038080e07444001b040c45180c1e00071500507020000783c040300000000c45c3c3e0005082d200039903169001d0040030302c40c0c8414002524211000c1900a800702e40440e540c460310180e40d401e09104030007205e000c0c4481486100030301d403010b07034024600402e5800307010001c80c00141d118000382e1240c041e02c41e2100c01ca5040b00c2e010311114014091042c1c2c0070b418540281c494031194425888004c042580e50700b001c2e001c0002800c1501c19014058000f1034a07540980761045c0288000c1c000c041d090200c4c01c1c00100c4c038250310b00882e03103540b07210780307800c9080000040c80340c514000012800003104028071102458000821800748101c1c0c10584e1b0101c42050b41c014002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 156176357 1250 156175107 156175111
    0xd0e01090b0c011d0c010206010302130603021804030215040506010608040c09232413061a03010618060221040503191203110a0e15120405120315131103010605040e 72
    0x807078004142c510b41d247e802007007160440c0e40560f8001406403621601c4401061660002076102d021600c0c41c07201c0d0000543d8441c0328501c0303502110743e04401943c1c0d140d002042154001c1055002d1001031044500c11300c2025006481a81145a115191a08841a140a03110044400980c5070f0f170704640d00341c084a9150403851a00150400b2142c090000c0000341080500c5c80c02507070140c1c00c540750710b58280e20450082c6041081c50b9945065140c01c56a40d44c0b00303105402c005051203584c0e1400400300b200f80021030300c0c1900140100e18201480c0300c899280340302c82045424041c000010b141c0c9051203141e0044100480c0448440b14900c2c02c04a204c42c10704030541054a080b2602034004204022283c185d21030b81050307964640d1a40001c0d140150104840501042c007245403100c2c00742d030300c0340e2a00071480b03a0262030b10310620074901141c1c0c0c00215009138840011519103688d41c10300500700103c00b00651004991000e11909505440d4001c2c3e00039800100002020840d06030440302c030507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 156177607 1250 156176357 156176411
    0x10020301080307110303041a0301030501050901180b1314010e0613080a180315050906070e01050901110c030d02060105100c03230d060f060f0e030d0e01090b0c01 71
    0x14119410207014a94078090301500900c4180d0001d40380581e0f80c1c0400a4800904509007150300c465010710001000303130820b1104036001c0d8201070220b180004180070f90003a94883c0020003c071800281c948501d4000040c20b12100840d00b002000c010856032580f0100d05000c0308000b142c44107154102e20301e002d90041ca001c0032801040341d00400034101c8411501a040700784cd0884a1070402260007400c031080c1d80c00240350550015003840f16141d87d42002d4807a40a0f407040d01c950755640d02c007d80d03565090344074880c0004d60801c0112140e40c080c8410b000415440400c48030b0703442c821000300c2e00e0000d001c0c60003009170b80080010000761030700c00c810070745401251400480c44055aa0f0143c9901005084140c40480c0408007842c600c1d090001d94501980c001414000a540da480c00140103046008440004802002c0c0a051602803c5c41a10080014000341809024030707100310346032107400d0105030400c03410590000309004900041c02e4035003024000003034100c580c0070a0b03010b0140086001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 156178857 1250 156177607 156177611
    0x90608040b06010f050d020d090b0106030209010801150201060e090105060406050612070305071b0c0608060111070b090418141c020d03090302030c0d18050406210c03020a03080a0210 80
    0x300080c8034603005a04000d0a083c1035100041c030040030f881030300038450303d904da85101198040542115800240807070f0f001707504061341a40c072008101c5c182d1241080080c00f08107648010029420118030800c102010b520002072916103900d10703e60b2200301901d032940b850b9182d00c24001645820b1190b00020042119a40d1400d071040200724140172004200340c0a060b6190b0004216902840e8092100d02a11004c8820315001c0e2400a241d40740c54010500040c0c00c020016120f54003401c0175440d00c0c0000c00c001e000c500d252100404080d4000590103800c030342c8908a4034003003051002c000038901c0c40f81c803080461201c0980d0319840c10350404201c0208820a2030b0b640c0145401140300351483c5242c0c50046000919424182c4c5140303e003101419443c46400070a481e03943e44800e0fa03030000b1000d401a42c460a039500700700b00c160350150240c0d1000d8042c5008185801c0d000d4444038064a1003064a0403140d580d070340000d4150301c515441640c00342c80004039980315a03410300c40780494003448001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 156180107 1250 156178857 156178861
    0x120105192624040b010608070210020702190807082a1e030706050c010e030406020613030905040609020904180b07050714010608031308060402011d041d01050601090608 74
    0x1820108000c6280e8480701c81d01c100e86080491018022040441424192480c24805100460322500400c903429183e880030840049001d41c40b50f2011402140d0315402003060841068080c4000d42c031203c4100d030b01c10b03c4072840803090703031f4283c600b44010807504000d000d58510f403000445c14400015020300700b1106102107104044010000451016800c1c4c0c2c0103101d458004152402e4002c0400703038184c0c184550b410003e08594098003d05400140100a10904144c094100d80c0d81c00396000300c401580084c0700080101c1c09080341e03440414040d282c60b1544540d41d4000c5001c450668000c2c4074507540003d1000b00a080601800c1c2640b9400d4502107002e824584405840017000b600400c200200001d00a00348842000c814085080c800c0080000c0750360748078035a990354440781003607001c000f4000380043c41c007202145c0c0c58404d58041c0c6945190082003440c0c42c012421580c182039105540e07520012890360920740c41c0701645e00303810000405091000024003a00b070180c0c8154200220101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 156181357 1250 156180107 156180119
    0x628020705011e0c0b040816050105060f0a0312110a1a390d2a0206091204151b052802011403091c0203030a060b040501051b010b030312010519 63
    0x1c5041005811441c5c42206880300c0ca4504214403d040c22130b9190342594501801340f01c819840f080c0594004c0716000030921400c02880781c01d11321440701501c00042181c18882c86401b80001080358040c2ea42552000301d5140c1d80c038800d40c0c4448410720300000e404130801c00c1c0d0b02039180d11010480f05290250180d80140740c1d50f8030381c068070315020090618010407100d6485409420000c052045214402e10f0b8040307200d40c0702d074601c9a403880c1200520510380454058000407a41e241000c4240006a01d01800d00c0d000c000c8a01100000204001001002c02040760f203425403c600d03948070740017a000710f64591000c032a580400c0250304485114680c80341d00143e03008021b80b403440d8030390042c041d141d07a60403d8160600000000514180a0381c040c81c0c40100d5000c001944a038481d0030013044255110340a0b401680594080c1c03d012840401c60f80625181c0341d624003903a096480008901000440d000c2030a42d0803400c4000110405400140041c3c942058a1807403406000401c0c0021071401d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 156182607 1250 156181357 156181367
    0xd08060a03050c011d0418020a0e101e0b07030f09050102010209030706031a100210050c030f13020d080a090f09020a0c02120708030a0f0f0207140628020705011e 71
    0x101d1060501c6540c1c0c1545c110300c21011640900614000c0003040414a004a2500d18071024a4224030404c540725001c01c40d640000180c0b40600c031420403090a060800c14070400759400710039541c4099032000300c00505945640f000b00131983c4256607600c1207a48400d8040c040001c0c0e50800750659005002d140c6041d14001215011038410f80341c086103846003501440c9041c548600c00c0da8128004086d1680300c0e80d000156091081105481040699203100300c5194500081c0c900f841c9403244800814a01030030b0058901d000cc0c0002c100141c4041c8179600c2c020320b64800601c5c00007052441c14108000540b44500300c004002c030710700a5103850b420b100c000b002819242c8000707216020032100350700660700402c6200c010303107070440c100da43d640d10020018000503480690303140012012214200c602d4404102c50003125110800d1496582250080021903040892100f44610b81c1224a0041c40400a184c0002c007481d50042c00c201ca04050004060750700740b81111301e06c00341c1031404005d202c1c4d02c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 156183857 1250 156182607 156182623
    0x30314102121110304090e060a090f020907020f0a140d020f0601120c090203070c170702010e10021912030507110a020103020f040506120f0108010b06030c07020f060301080d08060a0305 81
    0x70b03420901032951100e429a6074000c05a0841101d110100d030115408a541c1c3c001403000d00c0c103070708580841d90303003c80800580d00150b03001004480700388200c00041c01d00c503640e0f50300141c180c01503070210001c541d140386c40c22404600544e00408500c5400038180000d11103806803040c1c43c03001d0421081c1c081c000030f40d9100180b15070052510309010070000c0c4a50207180a0103071046501c15950380c145050024404001c1403015150400d0301c0000a000400e424102d80e1351550607150004207400701010003030b50f0360080041c4400d601404458140441c1103840c0841102d100c0d22032001050942c2600074101c5038000c10b01000c0c0f0124500c4549451400107211803e140d09190240c0d44d10081c10a1340140d0227030754806a003001000c21400f00c0c600100240d14400e02c40441490403130f0381e032030080c142a0b42d126000b481c6c02c00c00810102e152201001e0040c030f80700e80041d042815400c0540081121948240d101c808180c112030301100803160f00000e00b54100404580c0010114115115680c9510107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 156185107 1250 156183857 156183893
    0x40516080f1305060702030903070b0a0e0108150d0b090f01020c1504051c0302031503030306060f070804030b04030804150606080a05100b0a030b0a1a0301030209040303141021 77
    0x120005208803030b03507142584507990320070143d80b01c070304003220060755a800520301d180c401d024054012620380c0c0071100f52140b0802a40d02e1922407a401c0d0015101c401c80601407481248102d40040c0c2c841c0c5070050108107807840f030b4000810501e40200b043d4203100c12904c50a006d64010000c54025040c0010300006070301109900c407520b520b8514007141b410b00a4944004042c1e6107001c2c000341f16405a01440c811849031007241e00900c1000d00701074491000301d515a074407050900c03000c000034240f40042e2402c00d1003808814540750316070312190b000450495003100041d00440070481008400e0079011108540075030b0510160341007132009000e0000040c070344000c1a587e000000c00c2805420010002081c4031601140d036405031402c0100170f440d55034885030044401c003500082c03601603906801100c5054400c1c81d030546c0d00750b908104041d00b0180c001d80030107855072128000504030700c60803400740d40200c4c503070b000c2280b8000d2a0b2090201c003413801c1c0107000c0302c0740183c004500c603c1106600111 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 156186357 1250 156185107 156185131
    0x110a08150d02151c0e0c0d05031b030702041107021c0203030306040515090405070f0e010b1b160906030c050409050607030f2d0e07180203100506070506010504051608 73
    0x400040c9481250040340072161610b40351410113600490541d0000d02d070744c11000141c880d070054400621403000c50811000700039074803c0100444002c01c0c410081c62402071070341903900c0d20180d900000d09459100c0e01c02c19150000250380390440c0b80c0303890110004901003550750b00402c1c041c0c0000782c613808000c0c4004d0050743c880c0009201601e10f09480218034100400c7c1da0b20904003410191390b160002d0080c002c0f50000001c1c01b041036100c10780c2c600d049030404640030b0b04d03003d20140c0403081c0001061240b480d0b0305c40d03030f901c1403402a05800300c0d10250405890001d1900d00d1030501001d03081c0964003103801145030a440902291000c12120780c0306106041c00309a291350b0b6440703c0700504055105d00c906a80d110141458840703440c00c6201d00e40314842061000001079051076480710254403c20141ca10321283d80c0146544c260065503100500c84c3ca04a641c90340c03940800d1082e408041c00320b545400c2100140800c1c586881103617004901e03407a45107250202c50760080e000c10320141c2442202d603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 156187607 1250 156186357 156186379
    0x50a0312030f1e050103050d0c0b1302190816093e040e04021003151a090a1202040606020304050609060d020705150403110a030512060a09110a08150d02 67
    0xc400d400860b031483c0c0b00c0c0780c11241c14102c5018940284401c0c0000c071590300130b40040030b4036684610301c1100b106811100d201c101d5221078400e41120580480100d030070500002c20000e021550102c20303001042e80e60301402881201c1000e56280c0e5a05401801d40140f0700203c09100480c040d140c1e600a03041891408481e004241e185100009180c000307481d043c1c000240440d41d95922190140035501c01d840303031143c0e40710020055050f146822540d0301c1e00d0800d900c003004501d400c7c0f020000e950301d1150b546498100194082058400345e42c0142c28132025040d981d50840c180b92156400800c403e00c051418681840001010f520444520520402020540c85084000c41d0304035082c2680c004101c40c03020f4084011000c507040102c2e01070b000b00711814110550760310081240075045030305640c0c0a141003d00c01e00c1e4039880f07001608080e045900ca042c00304014280f8412100010f802c2c07140d0b1030b00e90101c018002c0051400605180c09101d0400300c00e00291594040e1141e080e90440300c1c2000070b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 156188857 1250 156187607 156187631
    0x60315010e13150302121c050f120403090e1f0603090203030c030a09080d09150503181204090f1509051e040f1e020f1009090e0c010801050a031203 65
    0x941034940b01288814604549160781c581036190801c1100d200380c1e415a0340e960300700d0146484c0d0049404440031200d80041c1082030521038402400601040000c950600a0050408010400445044020a540150034000450031402099000c41100c4441c00c19800d1007001c0006c2115500c14034041c10b13140c0720303002e04542c0c09000f0f90b004071070030710101e0303454104038440200555554030402400b402100e60b903454a134454035588060301c5603490600318030405444102c030303d90300c002c1501c407107020841c41c1c0308440d131002d0000000340d13880440740035101d42c1452200c1c01295882809850181c2c47c0c03444488100d508040c1d250708907811002c0006090380e8405c09120a951240313000c006541c0407008000401c4100108a1192801080e000ca100000910107a0460300710400103903100700002c0c0406601c1c41c04a0b144000380256140041045584140300b40a40e01a10501880390308021200c0e20036581c0440070900610007100c04445981c51500c0e000d150000c904110420952074030b00741901 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 156190107 1250 156188857 156188869
    0xb060607260705030c0304031115030403140d05070815040b090426030a020d06091806200c03180901050607110402040f1202030618152d010e06060315010e 68
    0x8a600f010641c1d40d034400c0c00307402c0c40c0c4030f6000e80800c8941c41403000c0305040604060041c20114041c0096861454441e91015150700082412182413000e040180c03075000c001c2402028000d40d0b0a88a0807890f01301514907882d011100032050740998608900000d031b40e503c00c451607800640003000c13100c001d603241407449084000000e2440c1601000030074010390b808298000c014515070400100040b44d1540110411340700d1481440d03280255840b048000308520382d00c9540801c0344071007200c040c60680140f62240d40c1003031145041c4c68101146505044224404201c111041214000f44560400e8009191401810400746c000345450800d4803413500e560381140c01030300e07500c4200d41402c0da8034624091561002a0100d000e4025503003c01c45040c010740700e02000e85800d10240c41400d0341210340031029031000300110b0740a810924060303c01c1000c140c040c8100000200c0350846ca60600301084046a0054003041c0034210070404c001c4580c80e00e1411a411202c00d10f840300c49861b200e000902 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 156191357 1250 156190107 156190117
    0x207060302090a0f0815010906051f0e040507110c0d02011403073e070515070501060f08010203040201080112020307093206030d09050a060c0311060c070b06060726 72
    0x407018035404c002081d240000204a5246144001c102207141e894802403030030340c2d00700e00c90b9542020150400e61113811080451070740e0740c06c051403c0d584c0c440c2804000340988000782c07082004141c146c0c6615401e00b00c1801100b07500e83c8140c1d005694112240d000900410b0300480c0424412800f00115044034414050200c2813140400d0007040d03c01043c200003a030740d400315000c08040d0002c11408860b0400414000100d41c8014001007031002d9980140711a41e000341c0f030450b015561803c0c007142d4182d031816201c001e8030714200010f80f40c2c034281c80054601f00d0107030401e0040020748485e000040e030300000c405003a54045103001c941d141000c08400440081d00b42c013070750306001c5001d04d0461794040512152103007404408640307102d0041d0100340c0710714200e8021030b90403002460003071164600600d102c200c0035100e842c2900c1e9801d0690551400c0a83c00d41d00c016448200091150902c030b038081c0b00c1a0842c174121a003510b000025580c2c030403100c40c03200c500043c20041030900d0080000203800c5c1c030307 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 156192607 1250 156191357 156191369
    0x3040c0803071505150d0803090c06041418010e061003140a050703050c0901140313050a0f020a050a1214100606020106150302130603180c0312030608010c0207060302090a 75
    0xb074030b408103454240400044415007001052801d030016103007105160303403400604c2000d803914181001503240d0541302e03031000708901050320403000300b4121501e80400800003044000c50080c1566008400c128540039003140408100041900600021464089850b041041120b600165000108003070b00540031250ba074003041d20001c810428013148603007259108040c40d90781008280e40ea00e0755000d150155480140c001048248a42c6041090390001c507040780c0d120a14107490251035441c240383c40d0940c0c03021240016039890310030440c1000d2241c00040c003011196141014100201d2081c40c030686031021b005001000300000c1b010307030103008150383c103c0700140500610b80c50700d40182c042c01c400c2c0f081c0240050840165041075110340300b9560801241e0f01c1d60b01c3e00c10302d4003100b100980766100d501e1240622a8a08a00103420104400011881900921004a10450b02038111071f10380d8801d0106034100014070b4202a40424204240e03011814010b07118000030b03020415500c1590025 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 156193857 1250 156192607 156192613
    0xf0708030a12111c0e01020c03090103050907080303100f0b03040807020d061401170616080708070905040f05010501120603081c0b04060b0714010b030a11030a0c090b01030c0305041703040c08 84
    0x90141561301d50440c0d002c40c3c1c030302c80041c80001c1c0ba81140608070320864150030380640040c0440c100d15032194000707030341000b0034100301c070303a4540c030f40841e603017541c0c4141c03803080350031002540801400a180c0c1e086002405e40300c885e90301314034041e00c88646c50321403850028410b0302d2020b10042002403540c40043d403211400d0311030a0560711800d600880b030100720345808040c440c4000207490580200c0303039240e1502080c0c0d1040c920b526080c0003a00d00c40300207400b16040c4102c103280460161958070039003584d0b8a4406001ca0113524280014141c4900400d14480090600c00180003181a80c8222405c20b41d02c05000f00102c500043da82c0020b19034616250303031241c18010005011800e41300a80903590059140c806444103d0300c42c2422600e0905a09416410255600d00415468141102080005001d46610350066600d540c05182c0e107812440f50640d4502060240c0e503494421441103400b681400c220714207041c2c0300c0c00e40840000100e004210f00000c0060208494018201c0080c8510422 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 156195107 1250 156193857 156193867
    0x6091a0408090a08160306050c0c01020a03050708010e04030f0503060303040512010516110d03020f0702210609160509070207030f0305031902074404080f0708030a1211 74
    0x2082030740b94005041103128400c10040459206404150f49031060b081500c9840d042e495030391340c1e901610008010b00c4111405019400100000380001d1183da601603800064500d40359501034171904041e0401c4020f4034070b82c002c010020350810000b800c001c016061164490380c4030070010749103219640006421024009200d248004150040c900901c010507800700895480301d41124400112f0200742850351144003a04203da009900802060151401442c54143c054001c05d84400070203802c0c013004405806004070015007031144a401912110192480412803071021400c02d50703070b0003298403881d598404180c1d1240200961001564407030b00740800c13009141009801c503001298800e00380b08590121480502c2c0c5071084030840356200310011501e10810780342e40400e644d4504030701608812600084901c928000407010300b92604072500341d40b1400c1c040b60b07505104031001115040d5010442c207015901002c420b407442003403140342c8112102c1460080a000d864100500d0b11490300001d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 156196357 1250 156195107 156195113
    0x4140307030c050717100504020307051f080105010f02070302190801060e07020606030705091323010b1305010f050d06060f0f030204151a070203030702090a0b01080a0b010c06091a04 80
    0xc820b81460303000e01c054403000b6549507103a00284a44000c100e8454120100410003002243c2c8000d030828009801c491001d620350010443d4440c1030501501e07044159210800042d07480512907001d45400c0c80c3c04d0504a039840d10281d620030440c04000d12584d036441400d21400808021300c40101801c40003400703280e566440150041d07509660460041c007031a00028000d0030000b4504045800261211010f81c2e0f40e076200006508602c8002c68a004411180b8010341750072051400804800e0000051270144203010400702000007843c490203203080070010445598202c0941048030400d48507902420310503e8890300500668200e940d400f4482a000724090309010200d0b4140d034400e943c1000720000a46544030b19085610510818075200442e403605010024094664030b44003038210784c20f000c059800104080b40c12151801130a503501c0d081c0b4046d681c00000581c00c800030080412136030101d800002c2000c600300d00d0182c40c2c3c0c0d446540500c2001500d610043c22241c1c2c200c03140c021810300745 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 156197607 1250 156196357 156196367
    0x92003070e010207081c030c0507020a0e090c0d050a06020307200a020114070b0106050a0210060905101203020304060807050405041409010e0312061c0c0914010608070203030a050414030703 83
    0x1c0038403801803194000c0411030740f10016004641d00c2074900040c1e01081c1050b000c4010705070075075a0702c0401c01c0a000070703401615880718900c0600b0300c5944c42c900915200800c03c1c509030803c19540d10440007071042401140c1c002ca40705441c3d6401c0300700540d5960f0745050039127401078002c03910321406100140700d00b5032020100f80070002c54401d03644c030180c141d0000000c4405000d16100a0300890011004100c00d500940050001559a0041d130300b01ca40040c1d50642101c07141d501100c1d01540340c03c10450352009038000c16010702072052900c100202c25840003547e0b40107501580f428806d140700412011070050007a03d0081000400070704c020144980d0301c4038003500c259944003007582050700c0c4048903d4040b055400540100140018075500d0008118010a1220300032020a1115615801040e00c100a00010b85010304000ca0813425030001d1b2454000141d108000700310580080c400000c0d800300850b5000500010003281c0783e183c40c00d08034102121110440e0041c4030000d2117908141d004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 156198857 1250 156197607 156197627
    0xb030a1404020105030a090510091a010510050d0b01170a0b0f040612081e030106081603020910080603010b040c0f0206100302100c140703211809200307 67
    0x10241400041010060300000500c103403802804180c05100003403400a00d80c0c80345500342d006000315000c039414182c62604440b04003a05407084451803503045100d0195070381087c010903041d162090300c912641401491406031040f13a1341490f0300c0c0d01c0018607a0f80302c0d110b280d1028101007140314040c14400300010060041050742c0780221100c0001149914013031090070200e80061f00000780d10701d682d550b421003581c05013100142d1480740319008000394020402450103001c040e12000c600b42002d40c2c0c40c0c90080010704d4100c0030140100590405074550590301c41401e0120b040401c2c1c680c8a0000290150141c0c2c14525001450118281b01207540000300710550700c0c0a800341c81a6880b6840c000d11b01404070301002c0d40003c425440031808a02c40c20b030f102d10090150f40c0d900b5a500c03400c031500b402c04049900550f131243e4180707500d94013003d00300404c415044807070400411420718241941c0d0111143c1c407a000b02d071a550392995a400515000b240904202d00204a07074034503003c04d000c0c00b80051 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 156200107 1250 156198857 156198871
    0x7050604050d12020703150c0e010905150a200c01090902071104020903010b0d1101110303100312110106030c031a10031101020a05010618060f0e0a0c0e03030a0f030b04020f04030803060105130b03 86
    0x6427000ca0f048950090301d10005a400141010001e04175004503080c3c15888072010310208401402040c00b45200c3c04444a46441c0343c0e0090070b00e4611001c001084070040c0d810403010203204000b0100003a00c1201d171010100030580b00981c0303856400001900400b40340310441d400070302d166580360401104c18501c2408140c02d8942d4a00c00703d180040554030701044401c40300d28000d000c0d0600103c0c0301d80b6840c1d59030508130f03e0080c2e9000d03c5564820b09450041c2d204440300c0b440b5400070700c01c01884041c202c1c1007500300c4941d9011071801d00a044a60320181c800030340031840500f410000c50340b09100d84840c55400070028810283d648144c040c120720b003c0e0b01c2404240c03404902050700e02c2c92a5680b011a076210840362995100d042c003140c020321203c880041400f101010b17015594809001801030300080f5240e0050000310208007a00f603941580001e44a180f04002d20000d4180364016181034941008109440e90f6800005807010310408521042510813035000142404420008502c00c0103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 156201357 1250 156200107 156200117
    0xc06090601060908060c031f0305010603030e09043302040b04080d0e180a02160f0605060f060403031211030112060612020906040504030e0603150307050604050d12020703150c 77
    0x382c0d9000494020b02103005207001038005402281040c8203150240d60001042180e05c44520f03c000ca03541c0044074103078011649a519400300b0014181c0104004108003400e41340d20102e0328250b074030080c0951800c252203170030748000c140d40a1a070012001c4280201c0208404560f12512181d80e4000d81e0042c5c0704011032403040000d4004600d1149611030300301c41c006481d074008083c000c01500c0d200c001c01400407420321703401d100100d0141a0340340c2d0180003600424a00389a2503407030400c1c4080e614024071741402654407070700c1407059441e00e5080300e04407900352400d510f560700c250501d4005400c00859806000802000110386050200100b648030744c41403070f0810846541e0380700c00700012980100030390300401000010f40c1c141010f4110071b9119110f0701c0c01c6824500700c000043c5568205680c45448031440c0505000b00d07040c05c001c1c00300079090032602c19003444e00e0540000c90340401e1080c01003164452508040740c0500800800000c0c0d0b51040140e50308034400038254004111018408000803 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 156202607 1250 156201357 156201359
    0x7030b01051014071104050a020d0f0b0901050607210503010f140906040e15040309080c0307030206090d0201020a0f0b04210e010302130e0103081b12070f0f080c06090601 75
    0x40360030802680b0070042078444542881540d0381600103038004010a072405142d4000303880c281c3da02c81c441e0038480d294940c0c00507140c0b0404003043c421030b00350301c21303942c903081c50448110072607aa00741549044035800c84d00540d5072070b81458081c0b11100da51303844214500454041c40e1031a0b07080006103050320f4020703d02221a540d01c8100c4082401e0b5411400d401400383c02c042010740c141604048080b6201030100c8000703028207920b4281a0008843c10343c0003d8011a062082010602020b01d070000704900a0520505640002d0712a100313607904103102d550201c1102045900074000c004031903800629071096400e1904041041c02c004460468009841040519079038400205605420406541e030340d42141c4048019002940b110b00700e60002c03108131000180500f08000414080c0d885220304076107810070203002042d0403164150f44034554012030054500003500030705584040d030304031840e407240b00c10700d0a062980750442c0002402d8000001000706600a0010f4020f0240b00c132441100e0540e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 156203857 1250 156202607 156202609
    0x5070506090609161d0a021c0b12010204061704020a0e07031e0903050304030c050f010c03020403050c062812090302011d0d09140f060a0906021006140105030a0f020c07030b0105 78
    0x1d009000380013401005c92054104045140c4245611200c00c0c3c000519060001c15a01c403001c0c2042400c1815944420803902e01c3e0070840d0365171011201d00780080d420613040c000060885007540d41c2400c00c4415260000d41950380d002d91110040c8184a000380250a04000c0200030740200700f0911181c89411589204a880601c1002c404941541c0e45500319140c40d40c04654420301008140e8984c4500112100006828270800c00d12400d10784005a0b118038502c1d080c0d04001140100510510090040ca4149080303c0c3d0090100ca100c1103c1400e24035200300281d4010003120307105002c061070403040c1030405405610450009a281412000328019562290b55940d641d000c03203000591140c60400c401c1440800e0710a03840710003000d801c1c803241c40b0381c0030a20503001011070703000140280004111682d01888a1446020f030003000780a2a400c1030041a40084440306c10b504000000000507131052103a402050034403100360381076645441170f030011513031204203000c01c0d20100d030048000201 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 156205107 1250 156203857 156203893
    0x301170307110112090c080c042405130f050a050108010e070b1603030603050d1e050c0c0105030403032d0e0c0307030201031e02031009060b090307090c05070506090609 74
    0x50581d2200202e40340840d903400455510040a004441c40e84c2c4848902001469000304000a080030100a00b14061000c2c204015100040b0201310040004001c641c0d00c620700c0c7d0100d806070303182642c40c40400300c5003100c0d01d0001d1009040c1c1c200302508e440d09001601c42c1390f4202e207040344c48080081c05a040c00c00304844d1982e88600c0781d25410300040004605102500e00c20350180e501078180054070940d00d0f114241022810340d40a400500d010304194000c00034440c03090540342c078900c0c002d070030401d400840c02c1d03481469503491810b0090100004080600c20707006603111b10040c05034120a40140030524407048116038240504500b8034107a5030810380d000500245440c0c000f4010420240b0f95001540200309181b510b5481d41945100600f21007020300081d400f03403043c84180d0010901e08a103200c200c400b560481c4141420402a05020ba40d00041c0711065a03030706140003480901c0b221050b0380c0e074466008000c01c00d0042000708502004040744030b501c03a00110013a500700d8400b180d60005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 156206357 1250 156205107 156205117
    0x608060f040b0a0e18030c0102030403110604080301030615120609060b1008040f1112060a05060a0b03040312020415050c06070c02090103080306060d02030124030c020c0405092103011703 82
    0x3400021004081054003085603e01c0c5d0040d1011411602514100c3c1c01e85041d5804202d1040c400d81d0000180010103500c69261290000d148000d00f480d41400e55801245210620014121613141c0789180c5c801ca00040d1020010301c01c2602040c040d496034907001c80608100c40007030f0790140c680b0200d84114140880400508441540c681019540c1d80d503031007410a03451941035640181c0300501780c0c2682c84410800c00c261340144001c0003589490317141582039a9000300500d0251401410401044c010001500c0d0031603410309040c42c0000d41d58580000270f00680e400b003902e031103440e4020002981c116000380f014420b004240c030200c3e13403001d809907901c00305d0000094100e18030f10010004105a2006517070406e800500d00340c90320040d114903d00740e07003007a00071140380341c28070083c07407035050340c2c1d0595019244880c2820f01c40000d141101a40f2803c4103010f56008a480b840090803503602440044000340c601d1500440390b14820700380008680090046c20701604016450001032100003081d19 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 156207607 1250 156206357 156206359
    0xf080d110706020a0f0f02030607050c0705011713020d02150a080906010605070f050111120a1b020c040c11010908030906130804030f1b0308090f0a0f0501050f130608060f040b 77
    0x44c04180302c0d43c4007681d0a48480c41941e4001603614840d0041e81c1c2400700c14001c0031143e4a0940300d0010300301c076030f04244c013544c0014140044950043c84000e803e0301d000394803c050750803040402d01640007040d40300000d9000294400c1d000180b65442c40341500250801c0a05990340c012203030740e4903212076510348080c00790001254050140c1c40000e10101c0c0103620041c4284c0c000314083d017050b01d10380c040c0e400c0040c01d80a960703001010004a002d40d0712821195805038132a2808000140724040e4440703152800d840d01698907100741980840c018900300e41d40300c201c2d000800034030940e07081c141300f160002d4a08503280d00582000c00c05c8000b0340c2451005143c0c000d6441458907181d030351343d0f0308060b00510381207074040312110741c2d0100d11140000b03000055006510443da501d000404000b00b24041199484c403861850b42d09014246134400b00e07405803002801c040b607a42c0000c1008800758092080e51240800c1c030a01e0111300b050380240e00a02542d01510340c4c00ba14031071b1204000c144c2c1c88028902d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 156208857 1250 156207607 156207613
    0x2060403021005120403170705030f160c0206070b0405120705060a020901030b03150a1d0717191a01060f050d0902062709060f030307080906040f080d11070602 70
    0xc0c400352070020681c10128205040207481e0107944910000c001c0c00840d01540860745e003070b4120000345080c00d40150f010340c044c50414503502e0402018001500c0140680740c0c082d40d91010081c9007409440e0428071035400a103c140c58140b0b42c580458040c8080720110355a01410a038506080341450541d842c0940c00006425242c0c0c40c3c050f20300007500050b110504240e1603500246030303030b181440810260340c03151426462601d002c410850582d40725900c0c1c14500f41c00c1080c00100c41c04007049440548041201034a80c5510a2110314a0312050302d504045c04030080c00c00c4d5040100071410883d2100c0c40c10080b000d903a03a00d607000c3c0c0300c0c0c11400c1004e6003c0f500401c0011170035151640a07081c0039100404541c2040d000460101040780c545510059030101c1c205000c40030300e000384e409584800d0440d0300c0c1060064040109841e4090003200500d55003000c541101140e484905903000b600e0020b64480d4100c0e542d001599403140c0100034080030400340f00c195902d40c6c00104850781580d90310780003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 156210107 1250 156208857 156208859
    0x6050304120c020409120f02011a060d050c07080c03030414011e0c17160806041506180e07080402040e010c020618070906150915021902040902150c070f03020604 71
    0x400ea90301c0012030b00c2241c1c840d642e104150001103800000a404c05201e517070b11081d05241102c040d08403000765040302c3c8258401e5010340b005940d800b0484402040c0c910011940c2d8845000f005c0e03050144140050a92070041015001c02c40c000018501c82d030f01423220100c0c2c454001c0242801c03a2400b5000001036100c07040c40c500c0351401078005004644591624928480c00c021000b060000305848a0070302c0c40c113040342c003c00b4940c0412a160480ea00300d400300550545680c0c0303140c00c0711061007a20103000500e860100480d404000603002402d45d03c1c1c4846040c54074404c000e00c800c030112070807449036141480100c0c010105121390013286500c1d130020449a15003c00c2044d404a0303a8050f5403003407043e40c00c04a1010028003c400c02040341e800f4085540c801e000b8081c01e82c2451383c110368502d502003840c1842e9250b00150180c020f400529454115510b5800402c01400324090041e420295217941e100403600740000400180b003104059900d070700d4550640c150300706c0303403480083d5003d4420b002c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 156211357 1250 156210107 156210143
    0x1201090b0901140609120607020115080714030f0109030807090605070b2701020c070303020706021204060c020d0503131412060c09010507170c070f05100c151a030706050304 76
    0x1c0c001c3c1881c440140940d0500188000288410300da150218000c1d801c80414001003680900940c16140c1c0e1b01c0d01d14030403607030422070300360b948060300e2041d0000114032004407100780d2020722080b41c003450340340002d0024000600f0f001e04241c8003625034400060f4560000100180720b034050b22030b500d502c00260341c0c4589503080340313208410111481c43c0c036691405804124162003480180428815600685510340c41c604000e8208070444d0310550039908402400d2800b41c5100e421102640d01908080d5a24200f90001c600341d0b1604480083c1305100003d01d0360300204154001c0030071284200c00c2e00c00100c10180501919440721a148540355003d000030804c0380408102400c54004c0600d42141803c100d0b4580e10b041720303100800002032500c0014903010300c80d800e0110300d024202103102100740501d408042802c0c5e00c0060b15041c200000d0f00c12607400c206030210102c803900050403090203103c1007503803072041000141c01b115101f40700b0380100242e10b03070241e0300f070300e1003281c02c000304c1d03410328a02c01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 156212607 1250 156211357 156211379
    0xc190b0d050106020d030b0d0f060f06030c030c0e0708010905040f08040e1b09061c090503070b070230031003060615020106050405041a0903040504060b190306051311120406021201090b0901 83
    0x1a002b2a905038a9401900340702400380300e6940107500a80c070b202d0209246040203d8101000d4201c0c26011248071304101d1115085802d141c115070142000142d640d445081030018013074807a500400c8503000250001360b41d2603140c205402400c00c2c14400010a090740503034036143c0b08103100030350805e1062141c650f002d41e00e2036079100300000d034200c04184018980d494604550080e1011680340404d03100344019554100905140350103e03c07241450304c42091005600603410705540c5035032100010008008140c2d10440c8401164480c8051000d82d48078003a02c80c82c1440504400c00540c0b9040b4001034070f1802e0700400c1c0c004c0b43c00a040b07400c944c1d0100c28403014071100502080081c80200000140360b2a1407140e0301c01450040445502c2c1c800c5201d501d202c09600891103420141051420f00107551015504004590340f000e0000c1c100300c4c88c00200006e805804030301c40d1480c0d4000704000c00e1001940041c554000340942412040c2e803106010341c12240c008103440d401002007801030005d80003074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 156213857 1250 156212607 156212633
    0x42303100f0e10020304170304020a121407080c181608072c040612032a0605040f1205031005010e0f0415050f010f020c190b0d050106020d030b0d 64
    0x80403001c90002d06940c5054540b03908008411040f80d8004100418810301d0300031a691054404206495400e20750005050b0b1242402000e010004c0d40303102804004144042c0300305070f035441050300c1c90703260b4496002c1e46403009034000c58000c100d01c12002d40c046021320a003e03c80e0b00004ca100916401501c400c640d5101d000b03004809101c42d9481f040e2003608031a400700d069192091050134030718107860602003965a15401403150500801511001940204560307901070f07024000c00350703c030404405050207a823445001403e014509010700052044c0000c103c11304c203004800038019000c0790282126148001c039140102e00810400c207000a42c41840241e0f04140010245980c0380500000241210003280b02040c01008201c81041581404035424550311401d0801401d0b0b6100707004040d40b100e0003107184034843d00180d80f000c407071410b111992501401031228100d440304207040114000300000e0040d05e000d485030751105414148070340203000c036024001c0c002288c502a503541d0f0070038007102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 156215107 1250 156213857 156213881
    0x1050318070e040b011a0f03070f050f1b0d020f0d082a09040e030f0901080402130501031a06040606050a05070314180f0319020d0c030f060204230310 66
    0x8a140c0014481c542d007501a006501680d010106545070070551481840c00302c40300c180400e41803115103002411035055a500a41a0501010304900010202c1e180e10a800c1c1000c0340c0321000c036035a03100007500c03400701c0c0e513402880d00ac50344038103841d03c01640d03610000514401542e016a10385580d00c0d124884840d0065013202d240c43c0d080f504500c504440186400b1080714800f0045034621a5113058001c1c180321502800156141007a40e9480c00880d10402403c1e5040c0200d11020900310b4403081260b00c01416084010031807940c40b894400500d1200ca0b2400901b2503205c004101e90345054841c81d01226903944078a460118030110944035904820011360601c004460907004405409008181181101040e1501c2d01681c0c02000b890650070554030b4020b40c09881050307800c00d00100a40b0034650115085001d8a19500d03017000c840c180e83c2c01c01001609048855010842c080d0058001d90311281680003140c1c480700322050070030404480303044d4194000c60390131120101a60040d030030310304 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 156216357 1250 156215107 156215113
    0x31b010f0c030c12050c03070e01020a020306072d050301050103050717010f05011805030a0f0f171c0b030a02101103130620150c041d0402010207120201050318 70
    0x4025201044480c00807825010a8542c92050280c0d07600246203058045000c80030070590501e0100e081007400000d05003000e110005803000056802000940703510382d40101120443d00e05008000e02402003807000045071014000150340016611284400300115503480f02c0c15603281c0301c011030103800050034074020b00c400c5401c42010f01d10321030300040c00703401d01d201d5290701c1074902030005000000541e000681d990394074105202d40d585c00725202c040d02e904100340640702142420082c802040c00724006180c410b65000c0f0034900e03000c160107800c2040304c820000b01401e080e80d9201c0240e80e050040d0b2030303158008140d030800501e40b024070001501260b01e0300800904203841b42c0e03481c591000740c0c2d02c01914503c0604003c0c2982c00081e48050700d2102940c12000041d01c2021541c4140046210240130740c2280001d040b5941c2000382d6005240e02c3d00d0a0318004124401440040400c3e034013a030041c02020350110f40114168800c00142d581a5605072850384c80d01c884901c480007403602212680 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 156217607 1250 156216357 156216371
    0xf1b03090803070c0503100204081b150c0601060215160c1e150605150703080a1811040b0102030406090504020c07030204091a0f0708071b02130c140c031b01 69
    0x1400402c0a400103500c44c4601e403040f42e0600d0300b01480d003032850f4003000700750f4010401031080c0000401d1220310701d030842e10174001450004000807501c00c16001035440c0c0c0540807907040c906400004081e0304858494003500c2c2c501c001112403541e18001140c220000f84000030000301e44900c5059080041d9025081b031800110245404032540c50304640c00351402c009954524442012920078000200300031660502040084440f0350701c0c900402c1c802400780314950002800c50081790304113210118440301c100c0b002182d2894101c00052070040b071540503e10700303030480719594000402ca4060b20000d031a00c1004514040820001e54001c84918240d40102c09001005072101c0c0030f9200e0381c911074110280f160160340c1140d1480000104200c0200070350206120015800c500303d81c0e0400c00307038900350310030242c05c11b4580e40802007100c00075001780c8642940a000d490315130149250322903a0744d44a1581c802011042e007580511811080c50340c20404c8521045040400d1007250540c06d03100102e210 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 156218857 1250 156217607 156217619
    0x4080418060504020a0c0204060b070209040b0702010209030a080d0f0b13090f050627060c030402040f0b0d2001050702102a05010b09090d0f080c0f0403110906010f1b0309 75
    0x1ea00042203400218020f0006d03141145418010b600c081c080f200d07403803420030303446400103804032602402c0980a00074020200340414402e404a40a007a0040c08945424000e403802c882582e0041c480d031031645150005010320300005009801003d44003d210031b0034402541c0300000140070240080360b44030b440c0b81003000015000e0203a644900480356002101240004841043d1015001000143d40190317080007d0028088252508150180c60024812070b81c604844020711040740a40c0d402a22450800c040000844000b584000a05c036284000204e000040da114010b050700207500042d440c1541c0340940c800c1500107024030b40500e20446030784019004203400c2107100d40584090351a0303c1107000c24223040801a41003816135004000f07904054070000d0441c030072249141c04000001d004034040115849c00da0b0000d401ca41c0c0c0840d500e030b5507842d28515141209034140d001e5541500028980c2d07000301e001050781d1490f621080340c0729400320094981181d0140d003c07014019015008246 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 156220107 1250 156218857 156218861
    0x140609090a170c0c0a080d0e06040918030f020109050a022407060e010b0927010b150d0e0d050406050c070306060303020a02150913110c0102130f0503030304080418060504 75
    0x403801c40050581d034004040c841810556404c852902500004004001032040010306068600c602d1501070300c06004840090b1051065510641a0504040014006907280c14400080d41d101c0e0b01c2c0c2c0c4103a00c0349414141c1c240c960504d80500b007900403004040150618103c1d000491a0726245500c3c4c45100e0041d04605401c481d0083c0c40d81d80e80c401d40e1003108079003440350340c49491084030380142c1e600d0240f40745003038121411402625200351000c809041c010941000013015002407038801c20301c00005c9020b000740c110607245039040e410a64031000401c00032440b030b002041295140c500d450b00704202658181d010350100042882800d0300000415890310546001e14400d6000e00b0307500413107004001d200314440003202c60a250401140c84c5035910002c503891100031607000450004045480c1040340c1c0241e210b610525400051090340304c403220b48200e0180d0b003041c0002107545440e041810743c2d0b80804c0724004c011a00c02c10007440340c5e240748000b1052001d000040410040d44400c04281 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 156221357 1250 156220107 156220133
    0x90206093c0906060d11030117070e01030503070b04170a080a0b01111b010311030108060609160f030908130b04060e010512040201050306060d060303090302040f140609090a 76
    0x81040003040d05000c41c80701c1050954154400862051050054034000034105036000e0461441041d0000308012100c0060300003030381c08074a0840c0582c880d0794440d2540e5100c0c228a800b42c6850241c19000304203888407200441c181ca41250003035041200c00e03940c1c00300c03400011780181c035800f00c1e4014a42d59003803240000c009000d070703545d68041181442c0e0800c90684051101141c180b12800c990b0880880e00003031001038281d203078408460450740340380045c1c1c02886032103941c3c0846c4000000200f00440001101400703400706941c40c01c0a03513900c1030103405081d1111900030005285004210116100390050390300306002ea00202d1511906140030300300c00c070362a40004034868011400708001504001c00d80b901070400c0c20080d2914060b01090026050001c2000381030140c080040340c40c686541003611704c1780350b070010100601c58903420b001c2c0415042e840b04a10517814052145a4034889005043e042c0c0c40710f00100d0526251072041207001c0c940145085424800c0c0080c1344086110344028030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 156222607 1250 156221357 156221389
    0x60918060112060f1e020307110a12022a06031504050406050f1501050715090c080307060f061211010203090409200105070812100b0715060504060f030609020609 71
    0x650401e199142c81c3c816554584406a0342515011a0300c4c48803454207150301c06880324400060f40d9079100132081e190321070741014125882c0b0070b8040342410080d105900081c251215000c8404004203d000e004001c00d002212401440e04504002014148076019540210b00f0700c01c8070a1080c2c40710003041c2250003c0301c05a51088c0c0f28000c0c4407a020048460744e4201000400c52403500300e002001800a1007415402041c0d24200440e0380954085a40244081c942c08040c0703142c02030fa00e81c2e4690781c030f0700b0602c01030702c041c1d03c0c0118507074844d40c0d24404e5501301d60b200c1102d10090147e07900d900005404541025040d1300003001a48003d40e03d5100314000035110703401c091410f9546010700320700704c83c3d1034201606001c410403074800400c0030030007139505912207049030340c1c0c056840c0d03002030b035600c2d0143e0f020484e5480b0208185c410820020701d10031801c000c500040002c82e68132010030050301c60521800b011800802001d0003c120309401425084d40080e0107940340070390080c0445c100c0c07100b2229007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 156223857 1250 156222607 156222629
    0xd0905330a1107022b0b0106030608160603020904240305060f0405030415020703020a06080f1006050306041a0a0602030c0d0503040b0c1c050a05160207030b0609180601 74
    0xc000c0100c40200603a401c84030428003001941c092032044542c6114182001c1c1c4588030800700d001480c0110700034052a01c1c044545074024a250346000d001d5110217024600c0801d040000208003200009140343c0744400c0c4852910006280c200150001d610a0041e241c0098540c0102c1003820320030008055500d00c1560700b40c01c0b4a296040c071909010780605001c82201e03004062101081001040d40c043e16240c45003170442e02003d0310b0070303450a520359000a40100510000040441d0052003d9114008200c0719420303d5031404d5079040c1060346801104046042800880c0c000d0800c1d600414051405c89010075108083c0f4001441607002076100a0050340000741c918900780003880f00a0500c8524103002d030442c00c2075590640c1e0400e0041840d0384852005c0b8201c0844800150003140035060103000f0411401d2000e8143e002e008202c0b10105070844580210100d1440003410408680d003103126400c41e51500e80800c0f8002c4409071038001c0c4120244608202c002c0c040c410380317000300041001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 156225107 1250 156223857 156223933
    0x2130509100f0b0d080913021216021905060105120d0207031209030f0b0603151003030807050f030421052107050712090302041a093402030c01050109060602030d0905 73
    0x81245946400207081d14132801403009d00c4e8104030100c203040e081502448018000c07013029200706d14002c0d806207185101c2800c10298428003d01041841c188c0381c060766440d0030980d4110310346541c0d010044504005a01c440c030100046403c2e042c00c14a40b4001d41340520140d940c1c1e4407000c01c0c070485a941030750003200901c1400b4191030201f05c00c491b9121496106061898002202da0002445102c068207000302c500000d145580b0610899001e14010f01c001c84d100d0400703051541c18507566160035a00302c10f07503140011a0b10f009809840e40c07200600703543c4402c4402c1401d00100310300301138458814040203100c400001041d484070212131600329034404004c2c134074500400c0140c500703610b002c0020614110b44820281c4030307022242da000329190030350307000d8400da081d45c80039030726a03560b13400081c0408031030110084d0781c00b100500a0518a4000f4082a6241c89070442240c076244110b00140c0c0c001c016400740e00002ea08107007201d50040c000e4456400000c020220b82d94070548000d0265a14418 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 156226357 1250 156225107 156225109
    0x21c03050c010b01030b0a1206020d0e0d0f031109010c1502072109031101030b0111030309070914070207030f0f08030f0a1406030c010c0c03051902130509100f0b0d0809 74
    0x7043d00868002460b041c09944040741c0401c6100c1c0441c0510780b1580045030000051103040e030100d0300002008001001400003031101030b9100e0200d8141d141c00648102c942000c402d10030701502030310780760322803c0514003d0900b0065a15a1102d01d0844203e0003401203400d1100d00c42c40903004ca103020b08455681400f220b4511b29081ca5034076042424841c80d0a170510105003915012170540700c0c28280000c4051001c1c0058030001400c50f8a007040744000410044407500101d4100708490312401c0c14881d444a850f428182440e00f21000c0006a00200080000c681c000349201c031118012020b000311000715440300300d01548103d03546441101003100713001040301c151180d01c90403a609222659181000c100082d100d003c052411410844690500000d004810307054074010355000c000c440c0c00d00142c51000498608a010070f034810283ea4081c40b0030100c0ca800b40ba4800ea46100182200701842e940500c01030158aa030010496581c5600710390710380382c120807400447d003e10041922050410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 156227607 1250 156226357 156226361
    0x1020a030510080a0309090b030c0d030f0f0c050312041a0106090e091f0c20011406150313030c0b09151005030a15020c030403080910050a0516021c03050c01 69
    0x7903c5101940d010301c00c2400805da0222004068500c0d6100101d03010500000091408502040003640081e415505174101a000f207400d60310f00f1324a80358503998640300035043d603200d1000c10b400390840e0400c112072820210004900c07a4803500c5580400207062700c9620020051109030003010120300d00120602c00f440030400030a0344410070400824002a04030b084046003000020074000e102e880712013681e56540a102c9028051402c500c0700304121800c2400c480c0078000c900300c842c541083c1e040110b102030404041d00880440c09001c07051954507204009000318514a5099040011100c1d0700c20025100c400c00c1401403a801e001001d0070030780d143c004901c618000e0200b00701c1c403081c1c560420458902068140a864100c021000d203107812640040c00b034401c00007480b01318000080c000c070810201c0000b41444010658902855138814001550244180c87d04503000c14018031400d0504284216110705692001d4400109030300107282c00c2c0c4c0c141c200360200700c000c42c03008200504004024 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 156228857 1250 156227607 156227609
    0x22030b090c13051608070504080f0c09070f0912060207120c05060c03090a030c02060d060e15010306051c0c0e0a090519020d1412030403050d0b09070504170c0301020a030510 76
    0x38050400031403c2120308000c01e100114034101c1070000c684001b4142c41c0c001c0003540c004003415415a00202c1091101075101c501c1c02d04007600c104806008502410300c50100900300300340d103440309030015007031070110040b40b0411101251210303020044c010008441c8000707000721881e103880d100c40380740c02440c0503828610700074070040c3c80103414800c112540100142098031903400d401c0c462004840350000c95141d20403a02c030081403600388240010b0b01008010014482c0c01d0b041e42c0380120001d4240114182c40e0311b8456141d2200140300360a41d2a12011506440b0034401e0501112940c0d540f007080c80340d2030041785c00c02c00d4a9a100d000c0b009104080c070841080d6641080b0091080240d54000750b01c02400c1c240280c0f1140c200700038031822080410680d07043c40501700c942c584034589880e008202346d1241c5100044d80b81400c1d01034000c6d050540840307001d801c88e51201070425003811407245100d618038440c02403920400c1c02c281f000d42c40078402080c0e00c0000d550041040d141844c80c01c4016021 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 156230107 1250 156228857 156228889
    0x603030e100c0c2606130507060302040e0109050a0f05040b071101020c07121a01080c010908010b0306070e040f140f01081902040c09030b0a050907050a030822030b090c 74
    0xa0140300100003007551888006841055141c506066004c41c41d8003d0b000c8002ca84040c0c900c105401e00051703019a440030100507101c3c404440c07000f0784801c0101c0c00e80c013481c8113020a02e114840140001412a0401c035031104c201d520000e4101a002c105c802035a80a40342500c01031090014044c03c00e80c8410740401c0d4a44400003035103401d1603841c030980e54412360b01c82d1540302c545405200080181d041000c001c2e41d2075801c8802140c0d43c4a8003010b032140710391140c0320301242681100184125060180f1582c8040080c0600300c81c1da2808070954940818155582e882542c1d0182e14009001e0b80c03250041e002c10b883c031014030a01d0407516180c100001a0000000796200e0715200c840645d00502c03440e400743d4180c80100f6200c85898058030024420b82000345100400c0003041074000040c0d0220307202c2c0300200125411540d5510501c2002e4075039000c05002c102d0100440d000b03d14000c4445440540c0e424840d50403ea92600e84480511040d40c10600707076000b101030301141c0c1c0b41071000d4591003d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 156231357 1250 156230107 156230117
    0x80a09180204050913030c05070b030a050f070c020f01020304270b010e03100906060504090f0201030c030b280b0301030f0c090b13230a090606140603180f010603030e10 74
    0x4180f00000c2c680e40401000300102c200b00608100c10903200c0c850541545900c40110380c0c00c0c2e91100081c0c400e94108840c80c440840c41c110002e1042260802d15600482894030740000142c041d40034010108001c60209056220401002031450070704500b841103001d003460142c1680c80d411842d1001d44030741c040d9440c100021030748000c0390341d40c02081030040e03030071313048030004109180b898020042e003120f80c407465020b45000c141c0d41c103228002000100f02c9100342e0381042200341c801020342c1110101045150404100c1d0002d001c030410500280302b128145200141d07209944080003801030340b007600102e520440c0c0040030001c003c41c0d00d4000003d0601e0010902c006806040850003042030309001948464a4000010440720501c06031101045502001c018a04c0c000629802a108000084418074a0800c001507052245101e140c820540109024610707191400e442105e001b00300040802c5010301d03c204280d50600344209802507100e5110851401583c10170050313540f0005c6564400c0c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 156232607 1250 156231357 156231359
    0x1030f2c0f120a08040311060403120b03060c0301050f03070f1202031606140a0c0b040b060f040525180e04200114031b040801050a0b03030a0806010305060607080a09180204 76
    0xb60100b010360340180110b20701140340b9a9a03040444403905a0200d41a03140901c00c14081072541c00428001c034442840b1081c04095444418582d032100211284da243d403000b40014041031a160b869241b100c1001412250490748880c0701d80c084c0c10306a480904510384c900003040450a040c8501c120342c04a0f050302180a519040c0040c0010080e4640448100030018010f04a9400b40502180054006401c00d10310714161a24500608054407010301c1a102481030000b40d1500c1d01542c1d10584080c1c038034103002c0c081451489828014248080188180c41100c00300d020341d4480b40c08002c186955108016040c242040c2403403000d1289465064040c81542c005075981106003031a1102c40c00071401d0740da540d00454410760308080c02041302e0310071000400050601054020074021020220204103007d201020140e03240324105500d000305e500000091055070013540819404117014200314a0305116075034844035540450b02c10b40c00706101300f1042c4080407041e060a4101020360303204510f81 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 156233857 1250 156232607 156232633
    0xf0604030506040f0f150524031203040c0b03090a111203090d08190c0606050108011d04050109080a08040b06010801290d021c0c0c0c0501030f2c0f 65
    0x140380b0081c8050200e0410202c96800c10641450910701c0c0c80d040a20007040000c4040301001900c4103031403104404443c00d04c540403502084081240b040750013030041c40081810ba0004c6041d0300b0040c426180e03044d0304100001c0d001080001184a80d0300040030b005d03c85030618100c645500b4015003140141d4081c140c103019842c00000711512000c086a008007100d41358503003280548a00c2000c40c1c1c0520901c8144102c0035003051050300341c40d2041c0320a001c0b954880c2d0044480400c248114202d00e450402d00c3c0041c0c0c00d401006a0700035004200101d014842a1614001640002080000240c03443e0400040c00006a80707560803802c2440d190080b54902010071490601c4c441c8002a1084050341002d450036401084824442016206542b00c00780e0004c44800c1706e40407504080f41508010684031340d14450340c440001164000303100d940c500d05081c011070080941d070000a455079034601070032618590003010a10800012003604090310444c0d80c10074140091111030143c11340c03141e0401c2040f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 156235107 1250 156233857 156233863
    0xe10030f0213111c14010b0a1e050903060702010903020607030b031608210702010f050d1415010201060b090a0e0606040902030901140105030a05070e190e0c0f06040305 74
    0x11a5001040036000c0d02803400000c80051000c0200e501c594035245800c001050282d010380800483c0d2044c130f64103180200b4514080d079000108a2000c0641ca40041c450012500040c2922003030516108100212046241c0129030390450410041040858000700c14034081284a601c207075544000e1004a04503580a951703038001820010525882d01e00182403a2400c11110030200c50800714001c0039a503814500d07031241118564074480200f07010358004030040c0ca00c115455281d044e510392804103038010b411689900b0103110030742600c0d103e800c545181c0b05081d80f03440c0107a00c0141080f8280c4440750019084409030b80c410040d0040c00d21403809680d985d040074200301c604194045a5668400c000a405445070360040104c5510210520004000540c085140082102084440ca136203d0040550f240c90880f0000e1403903004801c18051603001e1920b00e034004c442102114200100c407500c140a450340040c00251540c072003124001d05140080404081b100207450b094509070640e100e90751 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 156236357 1250 156235107 156235109
    0x702010210020c0c060d2307090303120e01020d061e05150d020c0a0c0501080f010b030411060f04030b0603060708040b0408030601020c100807020c01080c1611030706050406090e10 79
    0x15210b0b404103909010103020321048850600003805990740302c01c4030001400502481110074081c00480c0554410415402d4a01e80140142d8075011401840e50307078105d4110071499141e00515460384085400610f090000d000444082240400c00c4c0e4281006442c954000c42c0040c41ca0b124000310801407030729402e0f5542c2c019120251555a07070607580c41c121019110340150408248214400c0d42e003800780c04100c3c030040e9035007681e03500907545440234500b030390000a020320607501004201081c0054500d2030140580780e001746c6450300700003c1d15038960741a041a802611540c181004001039858180720203503000700700b4100031400c0c1c10a51104010b0f0040103000901c01d40c0000007042890303001b007014951040e001045090b00e29100500102883c4043d83d455001d8400c0c840c034a44198010b09205203d0340d9034000c0a82407600301a202100710f54900b8094481d002c0140e02901c4039281404050058082d540f1190b07900c5140c050010070042141d44170020340000c00703080c40070620140300d000d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 156237607 1250 156236357 156236383
    0x50106050406110a0c0609030c050a1a0c0c03030301060504080f2e090602071a071d0d08040806090319050903100507050903010507090801110306030a1e05060c07110607020102 77
    0x30358040209031021304e0300c2c00ca07820240244055940c0010314507400b071001803e8900c0f8902c41440300d60340300b05004e00280c65010300b00c0c4001d0b0004555500028020180150701007110031296101d640202183c2580d000381c000070000350b80060240003403e03041001c1404031203418000d2030703080758500c0340300740e408075010a40c0707581207028419403003040040d0800da040c0c0c0e4200004542c5c5031198980920a402420b080d51250001b84001034a03003805025194881f0b001c000401207001040700c1008402c00c0349031801c0b0340c810010b010124513000304024081c071620121000319626100c1000205644100c011000100901005427825a0300c002ca40c1140318920703e0004540c60301c41481c03d0712140903d440c2031703415600c1c240c10087c900e07038840740d098200d610a030020024a00d60348118030052008981c05901a0f010895040008094100824085224210b0103140139040d1783e500d030410303005588a0031103000201e002c805110300c1c2540301442c020100c0d40b0a10f849032540c000303511048528044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 156238857 1250 156237607 156237617
    0x50a0c0216091e0204060e011119060b01210204060e0d03050f090402070f0308101d010311190320012c1c0309090501050301090203030d0507020313031212050106050406 74
    0x69605112a401841803010b25180700395144c1d41c51b80b6009196887c1540310b980041c100e18039400c041c54003c258400c24000d0031044513281060f5403070700d101070030150303107002d0400c0304080042034084c00f0451a80d444030b01800000d43d0b540d1811100034241c8030f403c00803511903461440e1030000240c10404031050041001d46560b21240c6510018000740034580c8050720085200403600201035000c0e041034814410f02c05600d02c0e440e11100f550700a0a8030a2084181440104c018408a0741401e0a441d054400521013014901400034038104410f640e802107501c0500d148c807001d407100120180300b41c1550300b0310f0400264001e03074181143c580c04205907050500400c00008041d516440c402502c03050a6031340350810b4490078940140021258420400ca080c580400400c0303900d818001d0320482a0014010741c1480303588061007004010240075001035200810041c4440c0e10b4155110000310701900d0301a0300e8181009010700035184441859661f18648401400281d800000352001d54500d8988 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 156240107 1250 156238857 156238871
    0x30c100e030a0c050a14181e091609020c0706030902060d022b0b0603040609030c06020c0c0a050f0d02060d09060501030f03110610060f1808060108070e060303040311040b1003050a0c021609 83
    0x20040c1d141c00c1c008044079070041c9608203c0070000021340300000e040030602b04000d880da1040c4960481c0100442013040b60072108040005074826000352140c40c0c00208001d103891404409201242e21a19004d01c800c0c0075844100948000c4c46505102d0109a0f041481200c0031100015014880100000c040c41d583d01c0420b000d0500c200010b030346440e40700100b15521003001a22660b11158030507078520410203035a003c1001d0909182206604002070018122088150b007003100c01d80080ca828503090f070351107220401168860080600039409810303400c0380b43c2c0007414003c00c0d00415410a1030a580071000340500344180c921520200c5d43c3da0300d8145d120701a41c04046482504041007800749042001c0040790344440070403150b04035020101115181c035992191212a9241140c0080d8980c005000410110fa85091011200c850091000034002ca0741c80004115840e094076200000c1c0d0b580041004841d82e034480c00d459400b490005040c04200160ba07031031040482d003d050603090b19900 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 156241357 1250 156240107 156240121
    0xc090105220e0f0717280f0b040b0105121f0e010e0105060306090601060905130f18021207030b010302040207060b0306041b0b0405030c100e030a0c050a1418 69
    0x60907110300d4084410310100782d51910750341e41c8101e501c4000f10180182c00300054220091440184d03181c09040c080d02005030540c1a480301100b42c641000d02007a42c05810320000341107030304c1080c400c6100301445011401d1a0810b0700c482c41058208600940c1c042c101161100303000101c01110100d44c3c18810000c00c04545420054462540d03c5002d9608001a5420f0800c045d0801442000180c00700c0c0d00a6444064841c0d0b510028410f0700b011030075004062140d820b0012071000f041c09107240101e0f0840c0c080319060122101c000c4403a00d4030f5401001c0904524240007808501d155040083c9015402c64458904140040c400244525030004040c801c00c12907400210554100030140d9419140c281444100c03c0700750b450b884c4041113a100c000c201404910144c4080c1c540140042c0520080c0005201800810252100c14030401442c442000e51342080301040c5240302d00c22042c0440e2174003041c8264500310ba0002500d82d5401100103449407581071843d00d40026403105050181c543e01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 156242607 1250 156241357 156241399
    0xf0c02130b0a0e0105120a080a030e16080607030507180608060f120a031b0b04020d02030115090b0a08010e03031308120c180a08070513020f0a030903020601080c090105 74
    0x5240590403224207040081d10f01540110316040719025100f80d03400c0415500d0054681c0c10400000b05201400c1c0412134215100303501426041c0e40f114111031882480b079115084c2200301d50722252056000204010304503516026454001105003001501000901108201781e0841c1c092582003084520005a8580c5d5200e040c0c0401c44000d80100a8250040741040d103420811130150302003401700042149407507000801c51b0840780c000d13407880c403240c51f141e081100400b10a002a81d1564881451212601d60b03030103a940180164000040c2c05417844040c4913000e55503500a401c42d03490211040c1c5240c0c000300072203130300c55503044440280109600e000e040768080d0206500c0d41101c2034040081c01c441401c01410b00a4050040b820680600000c00c1040106401126161b4110500420460070032015200d11172040d142c1c0076007004004c1d0203003021600300d28202400070b43c0360309603481459018003280d400b4004005c050618660484041000041c0c184100b03405241c12603500701d2015001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 156243857 1250 156242607 156242621
    0x30c170307080703020706090f1d06040b040e010b0f09040b0604090c0308030f0a05060904020a03140c04091211060f06010c02120d0c0b01091404080703030605120607020d0f0c0213 79
    0x1c10708460f100c0a450800940d41d503454012400801e122060207d48000c488843c00101e40c4041049540071580104281001901501e01034102c1c0e25034007807035410b6441d4040c00c0c1c0c2c04030f140c0000150300e079404c2040000340c003c0000c0b0346000d50480c0084c0004500007000f040d9101d41700765404034410380310340390002d2841b003240e1000d01402d0000c03050000340c6045410320790040302500b109100c0d51702c40c003040152a92042c0c5001b0b5000c40002c0003040001c0282e066075203200c002e0016664280145000304080d00d01c0c9d00c1d0200d1314030400c2074000f6007440d0018103c0500a42c00801407540c0c0c07a0580203011180c030040d060301c0c140200030200904541e43c0d90740c0340b41310406040944e04c88420050010b0050f043c0c040e81240c00b80300355000850340384900e10402c250909502e200610179103498465006e82d0780201c900345e042580f50dd4021600da16001d00d0001881c0140b0b00511807460205002810310918008a80c10001d008000700181d40c1d01c044101001c507011161044120504802c41e00180f40c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 156245107 1250 156243857 156243863
    0x315091606020303060405060103020406021c090f0303090509070c020d1e0c06030f0b1e0609030f1f05011a03161206080c04110f12040f05031206041401030c170307 72
    0x40000840d500750b0220145010301c0c004e90b0244156224140190281d0007035008642c010303800880711030407510314000c40041c2c444090601809060b10b402005a00700019042500844d48001c0208098148003002941c01206854035503120328090303000032a501801031002c0e11000d00c80c400035120289041801c901964000c0055180d5551800d010300039000744100d2200b664a401e141400c070341010300d462010702d40c8194285402d00074980400400e608201e1010380c141c400c1000c0200c0b90b000811241c20500c0c608050300f8814040102200c00b03031001600704540001e100c0c10540c3d206c440841c15240c00481d203100100b0028203000041321070640780607046100d1400e000000840b260b010403c8410418151024400c0d0f0b04a0f80307031080a0300c28011004241e240c10003404640352661625580c0040c40303812081c58408064a03010300d1a000b61021688421b0004144410742c5000d03c00c4100b00144405c03058030320740c515150740541481e075100e181034811102101100c000000e204480f56158 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 156246357 1250 156245107 156245143
    0x609142d090a050603190803010b0d0647070809040b15040f06080906150303070c180f1a100e060708031f0f0501050a0e090a0509011a031509 62
    0x24090510401070f040c141c03078503130180c00f42e880c05403000420080c1c40c4861a401c00711503481c607481c1c12503081c180d510420b00c1654656a803600030503c80707884100900542600300c58010720410410a144002011f168068000a0400c13850504c00400c03c064078002078015032216264890800030901a0880300c864552110700c0720f90083c1149596401380040d20f1008840f0014540c841100b80e0300c2030002d5400341d07801e5000c440090076a80e04452005910003029080d43d0034040c40741c0d9000d80710026504169150800c0480c103144c54902e520448d030303906d040c3c66070902403c0c11002183e003001000600719030081c441e82802e01101360003583c0c141390130344000d420190745202e0b90034100313103d40080d20110221070384812a1074802c81004524025100050081801c41d881d2000568140e40025031031400d021009029205603928204518030130308002e9000300b4589052040709085891b0041d2843c3e01c0240032000032483e4400280705070400d0040c00f51503103a0b031252440c00c3e240420305945400032113 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 156247607 1250 156246357 156246361
    0x16051312020d020409050d030b0a03051207030201061d06180c0d05041103030705030306040501090608030f07050c1c050d080c16020f09090304030303150b0304080306010c05010e03040609142d09 85
    0x80400100514901f60700d0740c040204102650800401500e0707840068903580c043c0c070804641d90342040040010500c40d000000c0c10f80d94600c100c130714203111440c1c03055000405404001c618100744d810055503044640440ba118509800d100d0b4082c080c000403d001e5554800000d01003128510622401440007012291154802e1a02d140e880d442100d505021701c1c241800098156402e02907075007694000405141041c0e00031141c1d800715002584199402c1c03190b80e182c00440d031902a000c0e000d403503121601000031005030902a103441500c141c1c44081014038070400040c051024144d0b0280b49000300d062541804030b000040c050000d031442c0d20b510204070f0003809180a000001081140c0c802c1d2000e0040101c0400a00f44100c518495a05212030401c005000900c0c0c45004692207201410230011500b19910f9650031120003020b80107031648001401d202c140c1d00302c2e00c04401050f042c1260403506051101080c03480c02400e0300c841c801c03005107139880b60701e6000c6401210280c6000d084001c20f4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 156248857 1250 156247607 156247613
    0x80c1306080925170102040b040302061309051005041b12020903010f02130312170601031d07090e0705090c04061b0b0f0613050405060115021501030b16051312020d020409 75
    0x18070b03911034042000c4032a4840e21308102c041c02524221110707440c4403812301e0725540911034a6480310300448003c0e1404e81c408142c0c075155201e032030700a900b840c04880360682003105010032180302039040c0098080014011880c198030003100d40200c40c0c0e841c40561900300c2c59000c240580380c200c0d00c00110b00d0003c034150744921031850035882241c2c0100401c040c03482d41e4400c207460101903180850009102c0c0c0740040e000e54060f8201454820b00c400d071605114042501b15030500d41642c0007962642c0c5c960316800481e031004c2000300d02030242203a641c1c186003009060301c00c19200b684140000c0c000b40f081c11101e0b5285140d07802c038465400c01d000d000d6510304401c0d428003604007241c1c181c0c031a00e0070040071240100e2900c940e40c4a00d502a008194070307401d10b80801c81414100035100b003144501c1800c2044101d0102c402c40c02907205203903039003042c05d103520300c9001421900381c10010400c003030040d10008002c030b40e00c10088448911104075100294000305a0030030154102039001418003840c9020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 156250107 1250 156248857 156248923
    0x31b01020705160b161e150b041e110909010603060302310f06120501050402040c1106010603020a02011d0307020a0f12061a1c03080c13060809 63
    0x181d07a220301e0503030300004407080e000b81c0c070143d0a00650210540a000d980076107105480450314140c05195038075152002041900c020241702c2c03100300c45c00149504000503006030740c0101051807408480900450b41003441c5001e24458402c820a090390b2520b542514119040080750070346980640207100700d43c0c4440000d4064140707480200d001e2800c102c0100c01d500594190b1940c031002180c104040c0400308440d0401601c4a1103407103a1455981c20300043e841c2403901d0101d1524441d0001040343c0c6060300400007100c0807c81d0a03001e10101c0211140300c54404510ba0b815181a0b0900580321802038408a00402504c00002c0051010a959012000c400806404010b10132a45050840c0e02c5100060403100b103407140e0645000e4220484001650540269451a07140001c0702044801301001030041654060480c0c21540000c5d1a00d080c50780c420005603100c0b5820f8826454144c403d41404041b518900c074981c100110304021070001c40e800c4c00800008502c80300c4400340c0c1040461034400c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 156251357 1250 156250107 156250117
    0x9020307060c030206090c09040f020a05042f07030e0d17041d060d110103180c090605100203070206031b070506010e07030c09081b01090e04080306120a02150a02031b0102 75
    0x1500c941700000d14202d00002c0c1c4003c00d000f015007600d0060b00c1341e0792032140000b404a002ca0384004001030108441c0c49900c08d400000404581003065141010801c03004181003040002049004010362404681c018199042c828003d903406410010203081c41ca040c1c6550704440b810040001400007914103000c00c00b24070038204121002c0179921200200000000304039002000d00102d0400c0005c158081c3c1d2141401c4044051543c001d00e0a0742d60310090b660700d40d08014100341d034600b428019805c0c10030110740e0b01d00481c001189004040d07000500b0500000304070300103030780d42000c102000002c0a000d44c2c4506a10000316059561945101d10003404115032481c0040d00d0300c403103001554842d0a02c00c04032140c01018042c2450380042580d007013441401c0060501c0240803000842501d0003454a10460040e0742080d12410b004003007000d01c841015140c2441c1c1c2c4800c180c4009603513524260040303a440755442d81d564010307029090b07045011352401d203020342140c0c1000150680d41034000745 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 156252607 1250 156251357 156251363
    0x3052b090218070e01210e070e0912030f0a0b041b0e01020705010c060203130f0501020c070603060b030a05060111010603050708060a05101707090c0e0a090203090a03080a09020307060c 81
    0x7105188070101c0c800101000b2100c3d04002074008944254030b5002c2c0080503ea040522030300201d000e2101c02e482c00347e030031b80c001c4120b0075404074108004c40044080480c1e0082107050241031240c14081d60040380d03002c080e01000e04056290081002c000b1958012581c2910180040c0800c8220340c0b4250700300b00507c0c11603800704910031070f00480da40c40460039500f541e005868010581c00b031610f94a009400052511076842d03000c0c180302c03000c1070350780a0704100c1c40d01c2400003681e01c03038492200314101846030b40084141401c101c030600c038992041c0196548403003094000102940c4810040b6000c074082042d0481c43d518008010041c8000403c031310003035034030100443e441c1c6d4807101100d004880c0100d650b0200d0000700b4400384400b882040700342096040650454095030345511401c070441705512100000303c0c0c21a8680009400c1c00c2d40c0d02002080c00700e000f10300350314115241ca51600c40c620760083c00c00422000003114100d071541300d22210398014007214400d030386444010b49218072080d401c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 156253857 1250 156252607 156252619
    0x170106122411070f02040e0f0d030c080106050406110c1f0207120f0b150301060e06040e010c361412030307020d0e0310050c1b01060f0303052b0902 65
    0x500202205018145403844004409443c0c52059240c40804100444003264400d4646540040e450020412404041c0304000078080000009401600f1940c9000e000f80521800c01c0042154980100c1a00d04460090030b1491141228203003442c00c00e0020144107502c40e060701001440307108000c5101c10908200d03001c40f01e609464108040307005100360300041c00300d10084801720006100101983d0418090040303030440000d03400009003500d0030f43e0815010324180e4402c10185191500425856040d280020800035880080c024010b00c0c1844000d00394008407003201246c0032000c5140c1d0a10003591070180001c0340c60700680d026029001e6aa00d00c1038442084e000440354000c41240c2c000c1c4203c0e00103002d40007441d9000d1ba05660a17060310759050242c4a42c0715070300c42942c00388038481c031002081241d544049401c90a41c2c9240035407040c0d560b80c5400400c3c02004046c0381400262030300740c10300741c0d141c0e9104189018400c8040019074000040c00352010740a5800fa04010f030107520072a4a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 156255107 1250 156253857 156253913
    0x90311070f0602160302060f07140a0302060403090e040b221e03090e1909140307050c0909010204031a0a0204050a03080a090518130c080f0f120306090117010612 71
    0xf16075a061303c40d00001e90700200c00c102e05810904104001c0c04164800d402005610702650320303403400e04000420640168000008000c101603005500402910321013205201c10f0074152602c4074000d8004098510b8440296840c0499009103d5091106640003005001c400c0c203c40d440113134000c1c591021004686c48080105800f0058101d81d88035840c0c00d40e110841c010400c080350043e15a02500340c80352450300b4111035143d20180f004103806400b580003050740601500501040110041c02c0f40700c00e0348140b00920028401d0384003001a002030386503107442501c030030364654024401d40e0b00455025030b081c1c03c00000c110f51000605006052034454a131708541d11010b01581c61321548007084800780d0380c000a03003203009600740b0404990142800503c030a8071500158a0800f8011040c1180c1d031250b031001a00072802c00a601070703059942d05560a5051103808103a40f200c0601844a01300340b900c05402c500c03c0d003540b00c40024151080b02208040c290705260391410380c00c54a20304840210310b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 156256357 1250 156255107 156255133
    0xc040905210417060c07080702040204090204031b0e09030901111e100b040b06030105041e1a130c080c030a020705010f060501020c010201050601080106030b030c1003021903090c09090311070f0602 86
    0x920911175251090b03018034003992955100c46581c4040317400c903405a8203205c04641800144041c1015510694109554150b211f030400d6000c011640080c10200d000b41c01c2051500000c8141e540c1c0c2d10007030070f02d441800869100b69007828020803c6010041000c0e201c131020031400160b07040d010f011000d080112140c90424002030f00c0d482e8906a421120400040186091941c00110350f021b0303807c00c0007103640b8a0402c0409481101c0303812005004c51941e00800c5207010a00344400030800d04081104018021001c0c00070900104411320422010000582641141d0111403045130300a00030010300350460032040040045000c0c0c0c034014852040a24603650051040c00d005400503120035000c0c1e882c004044001e450088607407500360044481c2c40007641c03100e8610100300d83d8591009070301c2c0e6101004c81c428501044c04078400b01420206101c010031030a017001e00030f079510f0a5010800f00903500741502c1207510540211104e10648038005a0859103250240980c2c40c00c1e230a0380d510806102d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 156257607 1250 156256357 156256363
    0x1208010305030712110d030501141c0303020f0c030d09030e240c07051e120604030c0807030908060f0103050609030903250f03030306090b0109080c040905210417 71
    0x40002030481c0c1c4100180808a246a807501000180f1317850b01d01c2816400580c440e080844403103952000c00c1d2904014020982862070b044e0481509850322a880300b0b00c207003481c490400280014091650010b080510f048070070080300c1e0650862230440755141016640e42e0014240030a090300000d0907924450040d1404004c1c13030076004040038022804d8901c3c3d164194055209440080051141c0300e0000b03a02d441f00c201c0980b50342d101c0310b81500814916814801e512007000d00e211041c1d08180d080000081e0001c440b045841d4020842a40352000781c50306680480490b08103407072511980081144049007200303400d050f24440e02c00e80e0300a45501103403030f0340c2c5e009d107400700380e415001301ca01402c3c2e01410151660281e00300d8018058126a211b4000c074081c9100e4000382c0009403103007070a2118400900130744803154420301c0c0c651242850700504a490364000182144a1922a10070340c092080401600c0c023607030100540420504200140030750306a0191280000020000481d075070301d55404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 156258857 1250 156257607 156257609
    0x3050a0c050d051b0109120303050123010903080304020d0609050141191103090f070b040902030901090204050903071103070312050d140109090b0f010b1602010e040c0309120801 78
    0x4180204240d241c4200341da050414401825410441b0704000019180c04641c03408604502076100001c80f54188a40161502015071444402c1844036040c44504c0c2d0b4044144021260001400364490b19688001a0701d070700e00c0c4a0141ca40350034900301400b40103044d4014207402040c81c013080c0490842c203a00903500240480c002c0d120310f803019002c510707062222440640c0700140b41d001d039451101c041c42e03140c200c0754080301d80c84c04010b001c010011411020010a201101140e0003044803e107010510a0584240e0140320350f0310740c02201003040070000350031904a403a4010801c1c0203d2624407013055403904100805d0328980800e02403141a4100410400c0503250007030064650240b68810545442e400803400380010b51b95610081d42c030030800f0b0440ca01074900c4000100c5c501002d402d140464240142001d8588020f0900401c0400000c01c100c804004807945840030009a900050f00c803a2484001250090304100a140055500da8080b1194610480000307034820380f8804202c0f850303702 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 156260107 1250 156258857 156258863
    0x2030601031427010e0105040302060702070b19121808092103160c0f08030409110306090118180602030a181a060d120207031103010905300403050a0c050d 68
    0x24100e514204000381407041e500c0c20900c0008118200c8545d401030071240110b5040d401071b0400418040e00c3e560611440c2d0040400c0507a10742000d84c958491090540d1541103c01400300c0071402c01140c0085802c1560421421704061030f041e100c40c1003656483c0c3c01902c0c15841513aa95001d003828203020035042da138129050000390708120340c0c1400708004103541542516680c03100b0500260f400c0030403101c06c01400c00a80550b4507907240400007001c0d204900d07600c2c002007405100b00030654031555419811035000401c0c20001c1c19140007640010008000c00c20f007001d8a80165a0034055290011806100c10034002c0000b0f041e0504400400c12090307000134691001c05120070703400c50f104840d19404c024020301c401c200b0f040315526281a03050b40b032050405600896010800e200d286041c0c000c203d401070b4003d015404866481320744500e011200e00191407050b0001882c440f025280801240240601141d0703600c0d00d030b08200741d0340ca01c5040d04603055400381d40d0200d203504180102c0e081072a4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 156261357 1250 156260107 156260131
    0x220e0a0f0f092103060e0c0406030f0605010206040209040201140c03031b13030809040209060403060911090601020307080315060703020714010302070201080103140a0204020a0c26041e0b0409020306010314 90
    0x5031a07403482d4500369003d12080200364580f100411503203d500203541c00703006d400309495a141e01c0c160000d0143d03002499140640c51034035104200c0703030340c012608985c0a581210441c0d1a580c4a200680e11a0700c480c0e4203499182011030419694640007008600a011411030f54030601da20061001d62846580400d0010240c041d01c01c20000d00300c84050b12000c20001c1c009810f1602c1e49000c103003190010f600035a4003c0d102c0f441c0000340652079904039084907041d80d9810302d610703040300042d60b40d00c0340c120014054540040020680391a600818001a00c000c00303c4e59541e8241c20000d507100058007540031238065294000d16590300074800ca41c030865040e19402030742ea1031a02c400841c0701e0340600f00c5c0c0702c90050303103001c0c1c005030303103a2004210403131058440710003007003503424060454040201d442000389010304521451404140c10b0740c045a40c0720110300c0700207200d00d1104030015000d602a0341200c901250100300b80320a07402840c428002030380d040000404001c68400020340039151540849 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 156262607 1250 156261357 156261383
    0x207050105071a0a06030605060f0609010f020a05010501080d020708010b09060f03160605180a0803030a0902150c03040315020315040c050906030c1207080705220e0a0f0f09 76
    0x1501030000b510103075019541400030754812078003600c0040e0b0704486900d00655180c0040c010401148915504000161480c0d450481494040355941c843d0b0b000860600c00b0030500c0d10780c031174420002c014000e68050024846c0d540c1d036414203030361442442600301c090700070038030045900c4605208201640c200140301d040207444182c184444201440c40203030301405850440700c480713403800580c140145000e0362084d0741d80c00c408001d4040c844c09004c00d607209015000040110380350020903290050347c510000245542948000b40d1041c40d60800f0482d001008204040c541c88088050400c803805164041100000740208100720b00c800c4454000013100003111100a080c1340e03000743e6545002d0704206140450840003e602500101c5070203000300c2001032038690300764148080c0e6030003594a0a09030160308240901409900954240c04941014494041d4000b040100c0010080c41c183d20b9840703580c2002c80464015001b80d0304000c0076070b0300f0b1140401440c5098803500200f40e0300403041752000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 156263857 1250 156262607 156262609
    0x1050610021c031d07030c05030a02130e0a050f06070201050f0601270f090e070506040e0a02160609030c110306100b090303091018050402070b060f040f021603080f07020705 76
    0xc40300c04081801099500e1243c2085001c61041c0d90700b0314013241000f05407103842c40c54450340c204644e030850303030098001c4402140140c50b048011000c050750b1f00000b150f480440707800345142103400b02d400782c96842001e055042294010600d2401101d855000b0b1009603510f0184083d817510566101780024010040c800300007070200c110b250882e01c00150050080e07910900800488101d030083d10840b80d541c00528070254042010030000d010a903401400c00345410304200341c200b001004013a00d20380024182010060b00e2004590341c9604c944100102e200030700300180301c0f480d040b008075801c0b4054288001c01389800102203214074002607800b04d6580c14002e0103641c80d0042c420710f0b9054401440070818650700d41c180d0342902007607030380d44004020068080c035006129070741c0030f940180d204004010103e81c0049a207a071198003628074402c001c03204408603006020703000c6001c00c00740c03002c43c089001d059410061040c180c000e54809c5000e88882c201040301d00030a0700c3c08009640028410080d07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 156265107 1250 156263857 156263893
    0xb06030109020d02041e1b1707090510021c090e07020a05250803030a05040314070807030e0f0a080706020d0509060d0c0c050a0c150e0a0b0d060b13080105061002 71
    0xe030f03446c004500c0c0c01d40508070651109803038a181c16960000031542c4018074403a405081d002c4204c030b000300e014180d42804c80000e8545091802060b01a900c1707070550141e481d00801061101421301c0c0045e003550081c03610002e107042c129026070a4400d0114000c103075802e02c00148500007d070000003804112600700002c0d04403c001c1c03503c900600314088400124401c0170300c050b52184d0900745020a03075140614000f40500300c03d840d80c08034680305000c2131300401da001040c1c4003c0b03030b810f06010480e0f6034403074000364900c000a40e010b6031041c0f0341d240106890102080504c100c035210340840c6c0940110400a981c140204806030f5000502400802c40d00b0f9220781000800050303608108114003050b80f03410341004d400703110640d1500c65100042100c41c1e50000100624141ca16112094482040c0041c00040541c403602400d0200801c0194000000d0380c003500c02002041d54440e070b20103601303010342aa010244a00d008a501e0301c0001201c40c1880386d0700460346807a036809016254048414442 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 156266357 1250 156265107 156265121
    0xd030807080901090f0f0c120b0c07032106150507080d0506060f0c070608011a1b010e010603030309020913050304210206030403080405120f0901031a030304060504030b06030109020d0204 82
    0x2042c0d40d00d424448001c154240c005a0b842c034054581d49540b801281803502066540c1c0c0c1c40304000ba5511290140824210800c194003c004100f000356035001c1c6007030440c0d20305440400030101d00b501f129010100740c1c5940c4604221040304410208500300150240e070b89010f1290043d250403010001c3e0404c2807042c0e800755034058002444c0b541404c48820780303110740740c201d80c80d210119032003468244a0183c00035082c0c0c0c01441c4002808190701c1003141c1903815805007445103075449500c0d060140000500790403403075040802100800c080369590800a000d021101e2050740100c0001000c1101c1202c5234215001d1a82c1000c011403815142108001414814ae401e070908070000c8144a0010b0340d4840085004901955810b000c504203402c0030760502418900ca40b600d5401081803140c1504440b00f41c480f00342e0709003030004642e110000c515080002a04119516000c0001c010440da60040042c01c140c9006041c80c60300c5540d490107160803101c42e11000f0358840c4500b010100146020340280e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 156267607 1250 156266357 156266371
    0x60207020a0f03033906020703093b06030d0f0c0f060204090b0409030905040e100c05030f0901180b040201170f2e051504031707020f0d03080708 64
    0x894440d0b40c1c1002c0c00c200c400b00d0300114005a00c590322501c15151100a01c603e9054900b42404a00c02c075603181c13140440c40c0080181100d802160311004d050141035104024a4803545000500078890428040f0f07101099103445144540f03003006c8401308030821014880c8402070010403642d0082002662088000405001044a0002c1c0c200004400302c0319603003900d01c10040540c445041003800c2d0b05a45540b0301d8203000303501d42400c0c1d8020079404000c402c110b8109a6000a2400703d620840d03081c00750441441e003d0034105165151351a41c03000c019480b070450300144804946686440b50b0031781e5041240c403102840c0001000003c20300c0c40d07075415000341c4141014580b92051b02d5502c160464116080011010410304002400d2440d15402c0346c0300c00c644500c03420302030410300d42c446502c41501406000f05142c14001d0740f11020b080444000d10b803c40d46c0c00c3ca8000b54a0543c403659440703607104030300a00c100c3c00354114506003420a00540ca9240c0c998107115640d42c5401c4406a1006000fa = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 156268857 1250 156267607 156267619
    0xc0405190f06020c0a050f010e060306030a050105160e0307030323040518010602071202090103060b0303160609030905040509030d2c0c04060f06170901090c080a0204110a090306020702 81
    0x3440320310103890700340149119005040d040204408228900030b90341d10440c0114050f0180080681e4480050485206c2c101c0301c03641c40b511448003192030b00d04180c40040c050341c6044207021a0343d091314090401c41469981e40c01c1b0186820301451b0f01d0741c250340320080205180d0380f00b80300304c0100c00d071605520314969000301e420140e4031030000e4240d0303544070404c40c2a00c00f10710050100076410301140020309096040310f8000c040550104e40203600510025202541d500c50250311650705108440d4400310280303855900c1151030408000602c19542c0c21000b0400b15800040c05003083c0c000c01e4400c580c560040c6080c01c103244079501c060401e081200304442103041d4130700c030030300709151000700010461401031911040702800d12041340c20a80181000c07880b00358042001070340c1b1040e41c40366454030b026181810b4840b000b0003400761440c55001802008842c2002c0b81d114400100c4000f40750088800b4032042e000700031340f050288564040c2c0c1d000140720303007024802700d600c9800400481c0d00c0603040c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 156270107 1250 156268857 156268859
    0x510030f0908030115090501030c0c020613030602030405031b150403030914030408070f0b0f0306150f040314011a15070c150c0201020d0206010501020a0b060d02040903051c050c040519 81
    0x51111a0f03000342c10a5801e0005054920b10040c1d0121030390f80545001c0c2000c11984040c080083d000d494501e400911a09000481e05900c0054040345402154058020354a0341000d2070826200e03000708441c0711000c2680d03480e10b925058005141001000c06c1a6001410f490783d86040b80940b141401c2511004a045d045016582c0b0400040009209140c0505031b241d0a001c01c61400400b2540004102102400f80b00d00c81440c860881e900035038110f80c500815103003403950b903100d80602c0d90004c00c25140401c000080c00424000001c42c001044000c204886035002c1c002202d00c0c0388000c1c1034000213040034485590501c3e03001440c10a000d0301805460342ea56441d401d02484002c90319200051311012407504550301040710140c0303d00f590029064075070404c1f000039540c02c400311010b400e0071706038408605592586c041c0380941039000b81c802d1100389000d08010f042a403120028031400c00c1179542c8514480228440d0134043e1078400c00c7d0754030f82444c02040084115082003460381c803c801d610 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 156271357 1250 156270107 156270113
    0x3060c0c021e15030f280c0f0e1903020111010b0d1211030a120c0c060e0721150b060903070806010806010603020a022a0310050612070510030f09 64
    0x207061030b4150b0800a8012030410040c041c0900340b940d48212008110f4280144022020705040c13040c0d2012100340c0f1b40c0c10031046400c0301c44070207465070481c000f150710b0007000d40e5032640d10241c0740300c40f5100d6071140182000364400388104140c03600110a1100441001880198810042d1840365003d0000119025040700d00141c01e11445000c1154004298941100b809401203100107020b40024091420000c65810182c241c0400f618000c030041e41d101610068240101c0b103d0240c10740001e810401c640130010420f036954a14020070072591145000384440307000d6a50f004080036400301c401510003025203201e8026040aa80c020384c410000e00c4001100d840401c5204001c004c0d10b001868194076106400f401c0a6040c1c110100305401080789569142d00011202c148903420f0f0601250550450448803500d0003070440b45a050040000d0f40c1210340c0f55411442c0030f45011140340c001c10448054007661103030315210310390f040211811403148403070083c0d000d0301c1401c804d050081040580d5039 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 156272607 1250 156271357 156271369
    0x21120b0105042102030c0d0c151b05030310140607020103020310120b16090e060628050418020408060415060305060c030a0b010207030c090f020903010903090513140103060c0c02 78
    0x10b03c00c20041c0300d541c0380c015442c04110320640540240d50004407003115803203801c02921113004680100590b0f0100020756886841c105130540740f090301103880e22226103170450700ea510556040c0000b0705000c4001c20781e20395048140d4809036004005514203002a801500031350402465913032a8010901d001440c1d02c141164152280d1051080c4c0700ca601d0208030b44014408044200000c0100480007801650001c40815410400881d181c81c1c0b035045820749003a980c00304a03124000c0029420844845540000180051f911016803459110300c3c501340c640224061781c803c41301281d02c460085070202c0d807501202007180320344070b03070104160f600ca860f03480c40d1031410350350030300440f400000700700202005d48a4488000303024030203450160320710740315600070032031900a074040e1a40e100402c950a02095040b500c90300c20140c001d10040750103007006080740e501da10a5500407600701204507040c2c801441a1101030000ae44000416400c5484030002440b00c00154030522101445410145e603c034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 156273857 1250 156272607 156272639
    0xf062a1902030715050f0403110a02040606030b010e060c060105010525050601062601030b060406080114012603030703110d0203180709020a170604060f030303020721120b010504 78
    0xd500155a206524540a042c070001035214201c900d2901043c046a064840c41d11900b06e0f41510b00310310303260082e410643c103188203003900035481490b00d00300003406600340e0040007c07440e098859039400410401403052900c070740714440c42e89410041c01407040e0360281d00600007010f62085202e4582c2c0c03114009a0050304018010748140d40b2020042201c03641c41001003401d1842d44041202c1c1c643c00c0604805070b00418040140715500f0b03240010066200c1d903004100800d007580c000e015000300c4c0320f8902031008080c001c0080c0c1d4103210209102c520080c008010082d844900210310356034900804400030034180d0540c0410540c1005201d10286141c000385d4003401c014604100715221008005182c020154011440d0f5401480b00a42d0650440b2000c1c3d60040524a000c40c256240310000303008119076000b8800c0c20072820b80200030f0582c10f6000d414068803500040e122208140342c01000d807500e1260620008501c0c104522080501360001940104181440d90415460302d2000c0f400c00e0131 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 156275107 1250 156273857 156273907
    0x3031603020319090503061006020a060c03020c070f08060703051621060e0a0e0d02120903010204091d011a130e0115060302121e0c0c071a040302030f062a 68
    0x256034041c07020b441c00303103c501d41103e08d002d0950491480c0080c041c0d1640440035018200e1703a581d0001500072800b81d01141d04480c800341c207841d03841d62500c1c0103040c0840c0740c1c02443c0070f0344550000640c8841c0280702e010b0060851900303103448624041c0c41240c61518000c9020650507003112054903120290003000068642c1c00d40840e41482e1100010040700c0000e0141000795000842c105212030300452010706004005c021156244000700202c0c3c06807140b980848200c514219407071100740800c04100602a0740d000090200c1481411411902080220f0340c950114000904070a5400036900445945000000204101c060b0040303010903109513a00a9011a0300050349600c480078002481e90302081600d51080c00040c05500e140050100402101c1082c400160602740842d00f0801c907402040d505003e500c140c514415010481c0d00075110488c000d00c6180c4400da040400442d000e0f2003175006200006041c1c481758100890084d401030260b440400800518640081c209468407003544 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 156276357 1250 156275107 156275117
    0x20a030f05011b0f111f02090402070209010306060512010c05040e070309060c080108070905010b3c0d0b060a0e10180b0c060c07050d08071b0f02040b0f03031603020319 74
    0x303012000170f0325818500c2c290300c21a400021a404800403114252450b2450700140140c44030225000b0034002d218170314000c3d40c0003403001c0000041209035009001030390815503414508450800460342130b07a8241d0300c0e0b407020075020300040c0b04090b000d83c000c0c5da0207415445c010401c0d01568450f40c084642220266000625a4005201c0701608201c001c005100101d820061989400104680390080203002d40b813003121000394400c03401c00078420210240c00701103a61508130f64003540101039403241c00780001c2d490134001c0720401807600790250381c5025182e44540740188143c50801c65003c0050300c4d98010302c2060040d00700d0340040085094040c1c201200c0580d6100841081c0e1450000001c001d00d41c1d4610401c0303070000007240850030b5052205a41003c650030786030340400756800110070794410b204400d003000000500c407920b41e03d00da0850090382c0412a54900c03074140181c12400d640641d0b00350b801044400141040c100e0710507070a6000b4819a4140b0410041503101101c0d01c01c0080001784c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 156277607 1250 156276357 156276377
    0x20a0201050f06011d060a050c070602070302150909040b06040f0609090b0901060503120a021e0c090108010c050f0d0b0d05101a130509120406090e13020a030f05011b 73
    0x5103100e02c110740000c03003400e00716000314040307042018200310b0352105070103000e0124034164814010700503500f10691f4002501c10480c3c81e070b40c0080d0740713059920042e8400c0e40700280d41040c80810200f162401d000146c20503c1e195641e44480c62040700107002d85400582d2441450300c1540c89101e1040036210386840031a4009c641d0900c211103c001070640e62080c1d2603c04100490364000074404200b8500d6854544c55400d401e00c10382c02d118200139026400d10000444a060940118840445003801c5449804a903259450b1034200c4000c8001040480c3d410070401202044102c090031032035907030810114601801401099428030031880884442e8803050b40c821a4130320354007540c0051080074402c00c0500c414840001e00301402c1c0120414542d42c2c0310085502c0c0c4000703110b0b80f030030314180000442d51030307a560500600f101d85038480e00b1450040304000c60982140d1215003c030058004260801250843e15904004011160212219984c8410313594185040d0b46da107115000d99038071003030060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 156278857 1250 156277607 156277621
    0x2010c08011a04030b07031503030c02180606030a020f040308070b06150a0f030504020f1005130608100e0c13080105040b0609070c0b1e040c05240403020919020a020105 74
    0x20000c1038200c88407800918800c00300101000080c0d03411240c0021101d106600c420405400900750100c540007002e91500c408014150025a420800c904c00d940c1c9442e214403500502800d200141c501070f034000010000301e030400c083c0d6005090b03440c400b00741d0646019920759548401c1d50005d90101c520380c414100700700c0d1a00d0944084a40c21010341c1a440c50300ca01700b040200101c4804000c4404c1c1603540000c9030641d152581c048601010103041c000c8811142100074090340c0000725110300c8180304440c04585c0f180301c0c07030025016018031140d12100f00d003080c0d010801200c0040090b00310380300c1803082c1080e051061105200600f550800001c460a05007000c0c146804000d103042c3c01a076550051080403a0710504403800c440e000150b24140c1e40318114826013800da441150000038502c40140424401540b05a504485044800407894900c01c0c85003581e09890343d118110008081c04208058141155800c3c0c6c0903040c00007205224210403c2c2a0881c0c101110940050f0354032405c0101c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 156280107 1250 156278857 156278867
    0x9030f01050f06040c0512071209050d030902040b0d020a12140613060b0405070e130e0a080c011406030d050c0304030609120906050c0304060302090310020c0f2e0902031c02010c 78
    0x980071755440e14614120056594000d07a100141c0740d003040040004140d01031940a41c044004140d200b01600c0f100140d03c1e2000b001303088600400c1e88258036214107900d151a00010300540158050316001c0c046103065426410110128001e40d4140282d9083c40c120103414440c035031145004000c0e135800c0c00041e041000440c1d802d032004902803440c0c81d0504c100d164014210001c904000c0307400c0c0751841c002c900c0c0711020b45042500180c0710300c07412180c00b041200c078074041c0c800c5551000007049400b003026141c54415805a440300c0d09078201d114204080b070700c61001003040f580000202d9151517139036a125012600d0034070080d20300380588220203000316440f4054200900d81803030054203251118145036142e00c00c9200c4d100a150340001c080e885500c003408641c08001c014041151546150214180c441100a0745a44103000c0c0031000c0708503100e4810840404000300d10745021b103a44040201c00200680f200030703640b510030000103013109035406a0303c2080c400035500100b002100342d100540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 156281357 1250 156280107 156280121
    0x70e0901051012050709020d0e0606091e220303050106030b01110c06090a0f0b040305060a0e280c080106081908070b04020a0308070305040311010c0b01030809030f01050f0604 77
    0x4103034145401c0c00b503180004103244090f1030a20320800f00350215440d20a240004c035600c241102800424240702200b00c903441400b000c2041c00036120555600d070208401c0b000200c0304108110050304000743e24640c07144420780e100007282e00c10f1440b2140c691a644d4651091001200041d0f154030050203501d91600414100c1042800c10080008070907035203075140c1c1415603103980a810040340b462800d55806058800031702c200c0c101c82c8c1d07080703849540b403201c5940240415511303481501d006c075109142c64401c08120300002400b80c5520365103001a16040407080740400d01e00c0034100180408280c2011030135009080640c0002a101d2a2903e0b00342041d40b5020701c02d030210801402440070611031402c0301e014a920080c00c5190750307a07500c00950550350700c1e04064400080400e480d0200350b0014024000d503802410359001c40300d0410300460b5500c01d030798402070500110034010000581140047c102d500c2c0010b0541e210215241982c60031500704031003003610b10401364240103940c1050b00c1001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 156282607 1250 156281357 156281371
    0x3011503061401020d030f0b0916110312130305040e13050c030c06041701150e0103020307120f02010c060b1c02130501081b0402090a122a0e090312010305070e 70
    0x1002e412190000c0e46455110603010300303150310b80b001c0504031002030740300205400b070040c200c0e0002d040203050340e440642e13200341142c045404130b01d40112202000041d42c072820125072031205141d41c0c47c0302035034968950807001c8003880010700000c81c0d903003415913111344510030303009101050607100c0c10310501c1c180d0047c80c600e002e40c1000c82d1180c2a034440c3c0c4e003114241e03408503049411102c0058105401810f0022110145002681001c030f00e440318482c0007812a40224102c0d0070705501e550203100086d400e900000c02d501c0c090510200154065990f540351140500c000281400076807002c036003c201c0c664807100381102c280024800318a000407064003042c00340c800c1000740350f0500040c144da0307040802c46071280d044182c111b40a82e07a2290115030034640040d1420300595074036101c07200c0e0350b000c80c002141c02c0347e03a65515128000c01d008000070011020001502c400b8507204040e40c40030b00203041046140030401a445440134505480740c0214860b40050031b410f850308115401c3c07488050030700 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 156283857 1250 156282607 156282629
    0x216050d1b0609050a050708060906071814010201060302041d06010e0403081308070501110a0e03010c05030705070305091503040203100b01020a17130b0310051c080f0706020301150306 81
    0x1003141d2000d0031002140e8a41d000c00005824032050402c50b2404c1c3d42c04000030201e12540c03001046007040800d1460003040341c0c404450854545200075664112034440001000e10b0b0103804106405105850281c007820600000480c42e88940108041d585d405000d9142c19038000b25449074035200300000c600528503403004c2540782c20f0030354006250310806411580d800d0441e80b013000603c5000001c40d0080c9611000810810644180d2401c094221400741c00102c4c50f0180c01c0c19050030107005445070b050302a80e4003451f43d0b0f60980143c07100d8009403070650400c08240322a00c800e0f101c00351400c1029514140e141d03100e1500c0c1c13040516080c00420811405030415003c004281d800282011403150f0102c042c20707902d0b038190540f010a001700c45078540641c4c0c018070000707121022034000358014203086120011031501c8805101f1003400300c0e4546a40d14102c0b00c80c0748007044c010005071003040b0351595200c1c644070703058580b0016600f003078200040d03912503c1100c0103502c2d01441208011b00075003000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 156285107 1250 156283857 156283877
    0x206251707020c0a062604080f030f060405010e040b010e0705071e120903080703050f090405130210020a030203120c040b04090501060327170c010603050304030c09060b07150b040216050d 82
    0x1101b4000d00724088000490030401c00420108844034064442100e00c2061080d00c0b0b103003604c85910514015a0701078002c40c0b620002148018030b0b1400284220b8220459a03056441c2550300d402507040200031008012043c4400800aa840110109200c0c1c03030034050110104c0a04000c06500c208030341a400740508a202000022411001d5440c4560076044c9241c41c2c00c2c520a191009200300c40507070f40e00c1454102002404481b0710703e070b072a8290081e6280e0010481742d400130303642d62528203006405644240040c4500d01c08110b07500783d000542401c95810196038110854003504180c101180c2291207a00500c801541440341c3c2d90030b056004013603001081c2084680d04901c4004801401a00d80045402c684200d003200711450300c1001002000f1007952410102c0c0c49400500081366101001d000c000781000c084e003d03140c20f80c0e042ca20800c2c540829641c402c20b900007203410825409440d0f5044040e66034561002d8403002039100c903804041c00a919200f41800c082c41c80c0d080a1061400c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 156286357 1250 156285107 156285137
    0x20403020a060c020f120d020609060c18030f060906090c010e1e0d12030c020c04020c070611280201030c030908040612020906030c12070206251707020c0a06 69
    0x407200d400c0750520b003004102c22803603002180d942c60f185c51040d90054084c16080b032140000040c1c92010700c138280d0a40301c80e51142540e0540b40d450560300421811014007402c550503640002c142d60b07481004080381c1e00400d00c040141c1c2007200858426109411480403c00d40389001d00400d20701d29030903e031000000c41d0000004c3c84a014428031b042d0422045886c19241d40c0b07500354003241207600f12240d0a41036110480c0140038240405032070005014402200320389007032500981d8000d00d400d0000e00b20007811301400311110309225200040e244950610903007100144c0340094407907501003881c0108070103180005001c0c0c580c1804520101490091808082080001581c080d0345451400e034134134907801d8621a02a01035081d206501103400000d0004818507100109180c0740d29122000306591501016a00d428085030b4407203061404681d810420519080d0040d6002c0c12400c014910f44540c2995292002c070895107400541d10083e695009898031803080002865103107850307055917102d0a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 156287607 1250 156286357 156286369
    0xf05030a0b09011d1c0503190c020a061406090f0f0c03070c0503040806060405060603010b07020f0406091a031209060409020706060509041b0608010e16090b1611030102040302 77
    0x514060a0340d540c50000c82c12a42003900021000d206036030311260745511034030007540c550a0100201d030a0b5003029101c2c41010b80114187d81c0f0845040031010751050342c0e101020f005c0c003010300c2a50114000d040529001403510311170090313128041c00c901e001c986028424003188400141040529101d003508115440e00714030300b626880445800d00b40e80f40d4541503c296400c0705450001850741c00007141c0420307040700020307456120300f00171101031103283c59142c140320381c0744028016506407020800003140075041c041c0902c3c480030005400014400d40e509010b208503030781002e00c0301d6041c8007071141c03c0543c03400b00070742203076103040c24081858660501c00040b5144594400c40f0181034010810b01d0034400e1303d91000b4001c0c0320241c080b0810b450a480c0c4030701d00007140f4805060181050313a020403076611801078903050b0380a18181902e20b4840032030382c8401401005100040080384000403540400101c080c080078602003d042c0d041040c18a0078400e600310107800703603000b03078810300040000d83e80718 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 156288857 1250 156287607 156287623
    0x2070c0b030c16030905040603031d010507120525030305060f0604050d1e1a04051203040b0f040f02151c140f0a0b06070c0305060a06060e0411070f0305070c0f0503 72
    0x2c0b407a07591103c240f4094441c5801c030b17403110b5070003403030003400000780340e0000c00d1284070401d45903a14454400e00c1c001520700b4003482201900703052980c2400f4500d1030107003004080c0c065400803084480000c10700000c25101c8050801c41c0042d40300c01c14000141001ea948401c4a00704940e0103040074101404250070310700c90714014040180403011034401e01061514080d0154229800504100001244890f600b5050b1005c540510410100b84600407030f807410780b8085ca50108480380d5a8840e1544101208806801034a1082c101c15105c8016641e1400307400e51440c0700d1140741d1300c0c0e940b1010300c4003031588841900012070303003440c0351025485540307100c4903413100e04001080510f44900c12548011700d42c13010066004440015104103108599022000b160b118000700d0304240d68043c42c0380d09882c514450347d03010441c5540c900c1c2071454560404080d4090300300100d0305240711134554511030b544080003038000c10400100700701842005c14100b005001e000022030425841e220129580d0150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 156290107 1250 156288857 156288877
    0xa02070204090209041119060503180f07090609140c300c0909071e030c0302070c030f11030f060a231f1a0904050c07020a030602070c0b030c 62
    0x1000a0520840da1258804641c1a801400368035040c9080c2c40d0010381e10440d00c510610030410700801109166040131100c041d03406965a20b401c54454104210701c10341c0001120307801d40100b040c080f20a541c100040001415010400b040c8546085205811600907030120543c40785040c0401010010a00403130b4006480818540c00404008075050f41071800f6803a000c03100b0724104140610000324401070255200103c9104045494842d41039850031001d285500081b54540412503501e4040d910220ac00309184c2005031030a13100360784541c040d50b0715800c2164440c84400c8803106008080d81e1848108800750000c0c6a0705031903401003540d031103004000040203901c54030368071910005120300b506401350020300aa000d08100100d140ca03003240ad1641100c000b0310039000a14040d114a00c08080d080e00e02046180114050905c80540f42c000c16955690004011920058880403040001540550380040c2c0711481890140c0515180f5844210307406010f10502c031151402d10122004c20034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 156291357 1250 156290107 156290111
    0x20402120f0604022b09050601090203070f0c0210230a0c050c12060103150f020307081824150306090a060c0206040201090506030a0e060a1505120303010e10030519020f04050105090a 80
    0x4410b071500090000c0000080040c0162300000132500c400b9000f46000b0f40c0e0070380300c40955008413001240e0660f00b40202079070060240c3c480c010500e00074030005020502ea51040c500c05211203508600f1544420550740004580104200a01106009506140741e04a9100340e052400703044059507600c040c08003410400d05120146600300c49940301a0340c0900a110964891900b00745c0508030260482c0c107200e01182a0010312080100800c0802800c03610301c00c0e00c405078034442022950940c1c0108194003220704510821050750701001424410302c046002040714140038a07005043d1090340107810290350200082c840141c0c2c0103013504080d07030810743d045a181d0fa2405545400303091440403507159402030809011006000d0b40041440728404a421110382e540c84046c40701c9a010300030741c0352842e0014001806861101324055402502c1c038292030b039030607440c1e4551a06204221904901c2108505001c208500306444441145401141e0030003140d803600f40440d0540d00010a03561600d6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 156292607 1250 156291357 156291427
    0x5090603090705100e010813170c070911071a090606040207020d0b010f080106081203060103090f1a1006050c1e0717033f0c0403020402120f060402 65
    0x8400300b004000402c001010341e81c40c9182d481014105520061401c0d0000d00c4040004007081190324400000719400401e030500d241994a940d0025044007101014902510400064641083c00780d120741c0204c50903c180c0d10106c074507014007024030030f00102186800340f0040000c1d588004c12101d80c001c2041c1e80259462400b071001444489403560014902858403001241d4181089001000c0d503480300020045d10751500041340e0345901801c41d070a0020020070000704103504c01e40103000322a100701c45815066802e5695844002201c0000391800c0000317004000204101440400040840f4203066241403094001c060721030090b90541c3c0700110b06003030001d801ca0030400c4210001e102c07003802403641d2608a02d52a03102e911142002400a45101d404008001501d940b0002c0c4103400320044443c10324089440c004842c02060301503010000c0c4000405a2103d0005203c1c20707141c0e50a1020340d241c12500c2c9440d045010349024022441441594107445201101d0111518a2101080c0c1c40b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 156293857 1250 156292607 156292621
    0x1806060d0e01180c050102010b06160f020307080d120e0a020d03050418060f0503010212010e060411030a05040201030e0609030a030e10020703020f15130f0212030a111c05090603 78
    0x54010503078020455840c1c03034008400101c683d0043d140141c81a40c500000300d540768012070981d80a1030300a640020204442140280020101da00041c8115154990506079400007400d205090380040900d40026820202d140c1d400f000c000c00200c82e0341e0b4100440d004103083d4171303501e028001c13000340100307103116813041454054415180101301c04170151240a42090010000d403d0b0b5101e40028402c0c2c000021a880c5010300039951881191686854140e103410742c0b080f4804409804242c02c0307641d0304120034280c011540103610800160344003042c035040620005040300d00c0000715183d11b400040a01110040c003004440b0034140f1450089103480c420141c2c1801c0003880280c81c0c9515100103022820142c000c07038000c00e6042c8031815074015012100007498201d2086600045104507281c1440014014814400d03080b07001521804221903100b080500d150704c808440030101d6038491403086809800c21556100142540101c0812410020003608e00e00400c002d451080201100040072 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 156294964 1107 156293857 156293861
    0x4090e010204050102031e0408030403082a0c01180b0307110d05070302030406030903020102070c09050610050702090f071806030b0906030a0f170d090b01060e1806060d 74
    0x11f400403040b0300c10044c08040110050b075050a10010860034420000760019503c541c40305a5a62114100c030740041c6c0515103080c03d69003905900c00c3c90600049410302c01c01000b030070b15a81c0d03814040c100502860841d000020480808030400a00d01d5001d480e042045000c1c0041d580c001e55180f0b4121858801c2030006809079004100404c4098480c0d8000041315001344001410050076030750b02c441401d00e03580408149038642090060074078101c00d0400680d12141030803841c010540d400700b000040024852002d415840000032955405034168103a85c40305800f0b1030f19029240c0e80c003e0010941002ca40d4059002c20b00094110304001454820030b40c1c00c031705c08004070461951a500c107144000d10000c110002842030f0108901c0601401c0310107403081c0041d0302c4ca9814500014040810151030600c68118055100210869101225000b403425201c1b503a540700500c0d41c5c200 = true := by decide +kernel

theorem cover : BRFrame.Cov 156115107 156294964 := by
  have h0 := BRFrame.cov_init 156115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 156115107 ≤ n) (h2 : n < 156294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
