-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5531
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:09:54.750626+00:00
-- url     : https://prove2.me/submissions/c47a121a-f481-48a7-96a3-8e2adf5a71ca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 994604316 ≤ n < 994784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 994605566 1250 994604316 994604323
    0x3150603070302250f1506122a0e060d05070305010c020d0f0905060418020c010c030c0f23071713060e2d0102010b04111812101802031905 61
    0xd000240c2044e004007018001421180755a12044d08441e210100028250610f405018590480c0c180b69400d8100b440400454480c4103d065142e40042071941e8802145050b000c28144604041c201418002c5903280c24a100100d500358000d005942c8a19140d0711409d01f035829195003900141c0c001d0030405140340d4410780d800e107000300c1031400f080d4140c038220010342c030b500031030244035009110214031084840d1140d0440e400c405c08000240b086480044000e03006140d071160100100c3c010b420044ca005110f55040d501600c0d850300300d1184421240b03199800c0e07030003150044684e8171088000004103080400a40080364400080c40445410002c00901c40b40d903008049000f8209050103184030b440d0f00e2441080344541c84201403124074410300403405010101d41140c2c12034a46181c3d043c220004a001b400107031080981204141c42c55070511083d1081108034003819040388054141c408803a40020001030440341040f19680c080303400180c202076482c41004164082902c860301007107800d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 994606816 1250 994605566 994605607
    0x2010f1404020a0e090607260702060417040b1e0f120a0b0108070206070e01020c13051b04080a0b061908010f0b06090a0315021e04230a03020603150603070302 70
    0x284d40500716041440d0000c1d940ca101510a4062006849844a20450501c5912071402080c011440306060406029407544401d440a44004a010310115450b510074400c4804403550751142900c0d0807980155208021900f1783c55041c0000100203d020b10310340e2001411904250106003007480c00d000b42c44a080741c0580c05514103020425081017011500481c050740d1040f03280c05e190300343c0c0d020700c1d004074100242c0482c11603000075464040311b000d05082d8011440b9505031541b55a0100c054210119240124030075918141e100700c4000c40011942040c043d0403072805000542c0b04501d402c0103c02c01100c1c0c0d000030b074a60303540f0110104031206900441c038202c50b0035500603261815084c04210170000500003d407103800c4420101000150f50740c100d50034030310540007445080c0d2541410b9901c5902070300c41d4920400f0b81110b50012400c00600c04050290b00911218a080c0380d5401d00000f608020100d504009280b10b01e210b0a840d08801588188441da90060b03440751080340c0005280ba14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 994608066 1250 994606816 994606829
    0xe06010f0608090d210b06030703060e100f261e01050601080c09040c0e04020703110d05030709060e01020312042d170c03070f23010e0a060c02010f1404020a 69
    0x740b20504500c1d40c110030200381407400c2104c580411a200c035031751710140c1000d0039010b4012000100f008902940360b4404402d494941c04026007a84600c0e050b02c41803901e5014010300a0340480040007003007603184180d800c011440b000313105440d902080303290400c0e00c480030481c09400301c0920a0140982842980c2d03200c0c20908049103d81810540d860701d40c00351094480c051680da2030444402d500071021340004800041c000c0d5541c110b01d00e0014a644640502d1420a100d940c2da9201c1d040e0144040da0300c289650b80c0c0d484a002c3c90f000d0111541c0070341c10105c41c1540020000700075411a10011144540c0c000d80b20044011001c52164103440c3e0010501c9400407401084000040c0180d450300c1303400d49410380310070317180c0928402042c150301c07444200400b50000c41c411501004002c03001255011004d82e0170b2413001e1030f2140c2107800e0300e1700c039011400e41d608050001d40014440b50320410301c00c011440001b845400d41540001180c0243c040002c1c4115018104401c600d449041800503085 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 994609316 1250 994608066 994608073
    0x3040f141f0e0307180f0b010c0f03030b1309111507020a120204060e0117100218091803040f17160603020322081801300e06010f060809 60
    0x155010841071820114541c1c003000524981c020490707a04109000240185424035441c18600700b0031003000301401c5080c04403650405030380151381d40c007411450b10f0b6a6080304218621070a650b40450081c81c3e1010115070180c003c000d090722500c0140f0903100700512070f80c9929460620f0380b0800007d00740403040c03c0007135070003040384034016120400b2000840c1c410302c8440100001c10310002d03000e0101f507000100c640d408080001111400300344a80e4200c4005000e40c0e17031100700d084c1d81034140e21515405c0c0340c0e90102c0a24030101c90818001450313020166680c001c0003000c0f602600360540d40103274006d404104800720140000c1d0708040d111056842200700508040292901010040d8403d110703403c14568040000381c1a4016041700201e0200303014030042000c1064a00f03460f2541101e500140d80c016a81188416940500004d810b482c1400780340d4007141003840070444400021400101076261250499981e03242c0820216000e400e001c0500005503081440040a0900050281c500c650 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 994610566 1250 994609316 994609339
    0x30705060a14090a09020a02100510051e0411040f080f010c0f210606050a0e03060405071202011812050d02010b0a032d0b104403040f14 60
    0x16008a005a0100251800b1036103c40f154000141210403681c040c2640c0c030300000300c2280041c1c0c04100030302d01010a04007001203440700080b0310070010301401b4043d000301010844001120300036401040c0303000e00030004a041e104190418003e038100368440d8203040c030009402c1c0280302c402c2c08850801c0c01e4803402040144d0b04107030003d03e04400d081c030500c203101c0d03824800303040445256004034840640d8001848115522100104658050840030002031400c0380100240c1c0703408a5510b01880c0c02400420146091002e441c0b030035252020120305000b0182180c12802d001c3c480418005d061104c0f1a4400d0f03c95410f0280c1800c584841c040308592400d116982d0700d81e12003000c641680c0c8c0200c110814038249918400c1d681910018a040110b81828103104100c0a440041d00c02c0b820300c01c08050443e5500d180d4030741411040d80c48100c807ca000c6004d1242e0191514000e2040e802c5961070006500030305840b800d41d80641c00001041c5071200c030a00c400047c008084015190580e848000c06 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 994611816 1250 994610566 994610587
    0x5011202250b091e1b120615041b02071a0913090b0708100e100306020d05010618081b0a150c02030d0e01020a030f0e030f011a06070b0a1107120e03070506 68
    0x55444030240d4030800b217200044991a143d6030128524034440d1400c40755182002d0440710700007c00e91204501ca103041001411a0700d5a88820040211641e0024000503042c40f1800280b13125400300300441100238014500659540e0074400202a0721440014614005003400368841200078000c90a1040304004e1000410030001d80b00201c5544131411104e945401308010080c075510303030020744020700105080042002981c0801d0485000c1e40752004000d28002021100144501c11b00e00107800101c4124890f8081c1001e15005242c02040b84070b18a0721031001c0b22594000020311000a015480e000045041c01c003c880745180c0c1c182800f40c1001e22a00c0001c2d03850340c0f000c50082c02c00c40c0040c0403201e80c81c00f4042d000203681e0010180e8054201440c5464000c0c4001c200581c0181c0c4198a80070716401c0039411182140d412481501180d82c6003011000038085141d2084505c1c1e10420204000c2000e070416100c52210541d9000e2400c103100d0209441c010264204a00c10b401c108050140e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 994613066 1250 994611816 994611823
    0x1f0b0d05010f03080403060c02031201062012040501050f070807050a1b18091406010b130b0a090b18060d290f0f190902030106020d080105011202250b091e 68
    0x1b1207501440101ea20351342008201e096000700f1048075110905140003080d01c40c0c20541950187c6050507190005413852130581d50340384082c44140750016010030060159512a0004100042d06d8010342031030549203594045480c2c1c04400103941c9500034440c00d00800003249105a40410800c040d0503185040065031861008401c203008503842e5104415810001d0420541d14880d1000c0169600c03036030b41d04800d102940c4107600344000e0009884000c58030040031740685010280550740c084280707080103481c00496101d440a0003001030b0840040002e5581d480040506a04a010119500300c07107900200c1905070461104160741003400d940c40060b11a003240500e5548102d43e9a0704440002010401e1500d10b4541c2680903100e079040400c0b00804c0c0d4000314103c035425821910410154401180d01800078001c61340022038000e40c041c030a100325000390a2a1444044207441004e460801000040f40705504659100b001c4041001c001802d00c031407103c4180030700e5084084541203c40d10f48 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 994614316 1250 994613066 994613069
    0x9070503060f03010504080a021009120f050c0610030303140403020604200307030501231b25030c0201090f0e010b03040302030c19060b100f081f0b0d05010f030804 72
    0x20850084005805035071400384541c895080900200840d0130079050001850380112900d00151041c09601d00049400703200d0701140715081580c079010400e80c600c04850300c0c00e05080b680308000341800181300510040c0000b40c002c5803418404000fa40c03841c54080c042d01d1190400c2c00505585c9410070002c25004600a075002c0c4d404007800c014845844d0044214800e0010495010300c81d44e0408801c10505620a00c01c0a404504031000090000201c0c1c00340b003012114220000a5511780c1203141c85284003400c4007010f0350f41c1400d0140b00c1541241e80b00d82c9482000d42c000348149002e04150350b08142208040c0200210201e003003814400d2114801c0010b2050700604c0300000002010b02d4400c0c002c0e12892034420040e05c440c024040d044440c504040c070010741e0440d107491504442483c00d46404c1e400350f0226101c0009004c191034090f618880010700c0391004880307240f0300300134a04c0042c006a020304120b48445485001804403a4110780c03058000c1d000843c2000c00610204469509403030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 994615566 1250 994614316 994614331
    0xb270f0d0801150807030609021809060301020301080d21230114060405011101061a03010305010c0203190c0507050616050723150403082a010b0604091a10020106051e09 74
    0x1d426488605c0b003140109050783c4441c03a50f038030200c0da071010713001c1ca456048001c0c1001c984d00c4004d601d411040500300c2c2300a11071031160343e10a400b9007949a0180c45030510041e40c1e21004050002c00741c5400055901e480304034000903500400301c00c051542c007244c10b4050700328546021050000c030004991288a5405400d040c00b000000943d5241d80940201000c0d007950015000141c040540042d541d401c203000c03c50b600c0d42006245800b0610010941351a01c41c8010290f40d00c1c0b140c03810907201a44001d20995540c0180900842c0c540c44020040c00d4452200880c10440001400d00600301031458000f2140d2101d58030f84500c810040d6680071005c000219420154802c10006900d028400d82d400180f02c0300e00468017038a81c40301d2149503251544c4004800c000506030013516400c0341c3d02480c403143e000001380300c18130801f605640111916400c1072144014600240001060444944078001c0141c0d15000140000e0809900e03903030360355aa0600d0041f40510701400112400e00040055 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 994616816 1250 994615566 994615577
    0x9070e060d0807060606020706090b160b06041d06150904080909180a03020705100305040f0618020910090e0a081c06091407090f030f0b270f0d080115 66
    0x180310b01e00044509140e0302030f5081100c0c5940701d07006900c441207440f070440030480c8507400140428608003121081801c0d1500d201c00b0703503080c1c4c0e1205c3c015400544125081a50790150000c1c4012000e464003503001540e00038075041c40c1420001415407a812006401a104c40d07003400001002002500c510180481d1004000d130389043c4402404041602980050321900340340e04203054010941c5429104242d41102c1b884104200035010f850041e20001e121036644000107012442c69070000c10080120043c004d0348940e117400107901c0440a545c00c1005441d06a82000050094403a80c512039980f0300181c6515621500c923040c0d1402112506201c240c00039502c2040d40045a01c124054160804204480713512107044950480040320084082078406c0000704203403040b102a241183da00404100300e4000d1540d030781d8000d0501800e40c191841001021032000030000c040104141c0b06040145140492164500c0c500190103260209000400c001401a4041d000c9080d11014a07420503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 994618066 1250 994616816 994616839
    0x50606120a0b030c0306010608040b0a052e120b01230102150417070b0f0907120f050307021c0b0a020702010801230312340f080408070f0302030609070e06 68
    0x1084c01c1040d000703807141d03050007004000720300360f9000300c4c60704c0c0142c4c05a61016000e070750702c000e02400c882040d91411141e4014288504500308501d041141c2c0c2d10304108200d8559545c2c0000c102c102c1e818070740032191030803603400500110010141c114007204144e260100e06028520010f9215004000d05c040181951000981400b800d440050701000c407113003c1c1e590f0780b9040d08211701c50050503520b60200189540206860b42000501c0c00300b0354100007030301101c0c40314582e64a0b51050102804407164041842040e01603560942d241c80424001c0744441501c020354684451066801000d075060303580f05008000150342d005072000c0c1500c0da40c0240480c481b217103c5400301d030055005205685445603170040c0080014400207400000e640428241e00c01000c1990b9545085145100501004010500c00045085110b03c0541d40780030389012407500352a10f8000342003400c50340000a8490901c182001141005c02c00c0320342c001080300c0585041c0781052482c2d170340c150f8064811481114450076 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 994619316 1250 994618066 994618069
    0x6130b031303110a0b0c13180f15080c04020a12020406020d020d0203030f04240509031e090d06181403070b010e0405070e0603250f08150c1b0604030e04050606120a0b 73
    0x70840301a0503003603d10b48d00361451080d00f17070240800fa019101020300f4803040c40c459900b50810f034404c0d81e1250002c0d009240c90070045c40001d4100c003500d20104030030a0703d4122150940e20042c00a041c4650107071120306961480a890503442141d600304545c420401c100c030002c002842c050b00142e0081c821a1050200708840120600441045600f24540810b100b54168008010101a5419400c80c220030b52400f5580e442d5028207000c0c285c02090080c01440000c00e1588042e0480010001c6805480d14a071030f000e0445010760392441d242e5000045036400c0c041c003428002d00502582002c00d0720b07842e050395529150000c9102d01d0000c0f14080c40410b140303503401e02c061080011001880c2d505048a0030505000b04000d10030100c1080c0c0e480004207549601203030607592803032000d828801075202d1907440041507000341c0d004210f640b4484000100070800744180e5004500981e6062900b4243c0810441202c17070141c81c03184180410003d0f00380804c28102e143d980700300f0030040000c140c4140c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 994620566 1250 994619316 994619347
    0x160e01050c0d0c06290603041a010b0a1407050307121211030402090f0601081f0515190f09060c06061e090f0506010c0206130b031303110a0b0c 63
    0xd45815005030144051043e81c0900c10914036809440288140c40305020141c0301201d400d40b030910000441c2c0203946542c03c0507402190403900c40c980b1040640d4411203116031103c820f03000801d207a00c0000311039120710b0f0300581030710b040c50302c070700d2428980001c5a4480303549100b25200144503c90090b09426880d000d80051a10031102150500c070030035610008003650340c0101c0d0700701e100e841d04201140c52030410003106403003030006841d08040e50300c85084444502103c00c9100c101d45c00c0c03290001c0f03103070784031051046e00030030000a5058440111010304680c08030b501c549002048a5100003000780e40c0e10850103400c5030442e0a110844840c80e0030100083c01c025000102219400d00d07522402d80c1d00d000b00301e0101e4240310810000445800000c900391103069401c0381c0010301c4540f118005d40340000c014600000508044400a40d880f26811469007007154036a40f22101140018207042e08480340e00035204a42c00541140161036840c522064005071448545803008150301030981241d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 994621816 1250 994620566 994620577
    0x906010309050f0708070608160813170d0605040e0a0203061603020906160c0f050a060f02010b030109050c0102070807030b31060204030c0902070b070503092503060e06160e0105 78
    0x940030350f2030b80c1c0c0c4c8417510b040c1d5903d021b200c2c010000d03100d0320000d540c0f140d86203100361580b8600d41d5403090310303100c00c403004109400c5420103503240d0740e0361041c0f48441034045c40100324154002c640802c441e03140c00e04010881d040f4480413407180e04846961001039034003080c1e0300d0f440380c0758001e24045441e0814045002b40112022540c00c504005000c2215143d006001c40c1180d03c15200284820380310301600c900c1030a980b14203504001e000e602809018092029556014030070f00c000038100b40e50600203800d40752002000e5940790042003101c0701b80d50741440304a01420a1030024880140346541b6036084600c0109203044025070700002d020040588040b25507400b206c00300c403200407089030610f64000c0d40075100842d06501480000668030615000340d4040ad0b4100c030004840355603000090300c081c0d1008200c425180218526581d80540198000b0442201c0049c520340c900e007180b9085003100c04140f101c83c01a030000c8200014005a009440101042440c0c0b01c2140303404040180c0c0c0600a8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 994623066 1250 994621816 994621843
    0x60804020d0227090604051e0703060c0e0409120318052508030703080f130515060111100218040e0d0f050403151514030a0f0c05040207080304030e090105090601030905 74
    0x51161310000040d5030b9010b1030103a0f0607912101119001c5d150354180d20305040802d504032040410105940c0d9000e40380d14001b5060100c600d8810f0303000181205c030864022a404c207031060840c142d0300d5052142e0540c0d10903c2d0109904031203651600c50b61030b40640c81084000c51a40c6409483c2100000210000d190b607000305ea071915141d1401504558044030b00c0c11203070301c1e42d00004000c00c45140c0249221504807018245440043d2088034078284010442414000c00381074044c01104100004500c8580d0040e00584900751905100c41c0456050b960754420b50515140d08401000403405081c6074200d4200070040c010983c2c0300f030b02c2c80e000701c0e40b015100c4507110f80459814803090f00210031008001142d00d07071640d02d07640460802d40c2017414050b0540c0c0071000300c0000501380319404003218028040120700c0e0b40d54600080070380c1c0c0b019000316007030f210100a2000300b503003104c0c4400114108580c00d030415030509000c101d1424000b4407440c10541c40b10742001c180702d000e00158081c60b90 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 994624316 1250 994623066 994623139
    0x9281e030204200a0503040302060f25111b011d061c090b04030906260c2a0123060105091c060504050f0d050306030c0105090a08030403150501060804020d02 69
    0x13280440902950800c907016400b40c052031000030600111400c0b80c80c45075040d18840421320f04000c0c081c0070050450729044c4c0500181106080d0420400c10103144903900441d10081140c0c441800140100c10603036140c065854251800746140d03a4217000d40d40c4501d420094020054909154107016240181d07010f0524201e1806010503da44072180300b007907503016110754070000d0f0544201601c00118122030b4110003039650204076804040001003424682c141d41011056141075440c00c59a20680c40c08691603545070410410070b11082d03500940d0f2003000603407600c1840c009001808078451501d000c0e11034020101061184480841101e2a290704064108030324130341468400d41e0b501101c420842ca074400d103004e41c0995803040781124442c3c40040c0260a007600710310019109600701d40c00e81130380300c02052004140000e040000c3c000841c010002950511035105141d0300326441a044070041184030300410000d03844080720388640e16410703100410b40150400d0341480b003122060000d8600d0300d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 994625566 1250 994624316 994624327
    0x90f0112150504050c12060f030703150b03160b0a0f1e020c1507021e01022a011e050a0c050c0d060e0d02070602060a050c09281e03020420 61
    0x704400001c8180c5800751020449511103001c4019640620305240c40490404800907269003040d5500e10b04c0c8440140803a16000e0316981c4540c554282011980741076591070390610818076040115803d0130880301d04541c1d480d0308001c00d48846100d03003a240303000d001400711070031840380c41080746085445102891115900c02c25800944440e8440c81c168415041d06000040d01044801282c0c1e078503500800007602c000524640b1261500d103e404581036002e1040001e1007a01c10042e0680d8012820340e60070075681401c1e0001d000c80349001111260180558007480d80e440e00407040324515215810080002030192801358684001004001d402c203103002c039501c04002c4c098004c40002081c030780c04d0f540d101d03c01c064121780e181418801d0100681c820004184d203074420b0307400107410011807d007aa28045401e40410401c200b0203030030340790960040020b20301641c1d0342d0500d040a00300b5651540c03845100c0050303074441c4400d6400040d02c00c0c0d50303552445030550140928081e8000caa2080ea03a01c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 994626816 1250 994625566 994625591
    0x20f12070303030527010203091e15041e120801080105070516020d0606080304140f0130111b012009030a0209040c0f170a1401140a0c02010e03030606090f0112 70
    0x8d4000303650400442c4101c2110801000c0a440103071003223950f51004003422403070440300c40311666000c1d0060b1003500c464a549400f01200340c242c81d0110380900f101103d0507004090003001c6110503405420280d140031b0030f01c2038407513003d0201c8401c86904d4504002c1c600040c0001100540d91070801018180303031680c0040c00000100103030044581241110b0300507140c040c1030120382079803030380b145000695030315203c502d010f52075a82000000c003081a0b01d90b04404a43c80600700c1d040c201c0040b00c07c0d24046003e54040d07041a4501c81e1542e0050000e1103041200c40c0c02c204030301c000010481c400f420201e103082c01920100500b460b800e8000301080d155041ca800c1c10118040703680a40e140202102801142c0e8104c0c4070310600c44848090001c4c07034061302c3c41e203506c5800c3d183c03400b00301800e540f541004e43c9148411038072540540e07070201c400035941d03160b1030001e400c650302c9000388040c0e504188108402503a42c54151a0032400684061807100d40150040b246086009148440c00b454a010040745 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 994628066 1250 994626816 994626821
    0x6040f030c1b152a12090f0801050f0a020a020a03080613050a0204050f010f020706050306040f09140f01110d02033606010501080408090d02060d1107020f1207030303052701 76
    0x201c41d154031000c0700d040084ca14210103a03400031a40c00007800c05444903000a5584071320501424940c50103004150f15084040b004803002c0c0d001540d960745402c24007004200c0788403c00d400c0510300c1c0c001c40c0382801c07410001c0d4440419000180a22134103a0018415450304002c0700207188007408100311500d0440c2940e07009403c5400f034140146488140140a54011505110340504580040044910780102200e05a00083c8041d400ca81c075044104c000b15098012003100c10b10540d500501c2d001d02d05501d81c941001e2035440c1c034060b1b043c0014401800c480c1c8044820f140101240980c4e280c1d1000484262111541440c2842c80034407034501c07140741242e1100348110a0103030242c036200d0b42c0e6840111a02d580588001d0404001001762400c2443c00300e192442252001e80381d02d0410065030102c400312583d0b00114200042d0006440301145017802c0c0c81500c0f400b08072a90041c1c0c061001001e50b0b034034a80d00004003895525404290030403c004060301d0300301c100240320842c0c5407085246501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 994629316 1250 994628066 994628099
    0x3010311100201021c1a180a0b061204050c011701050f1e0910180605060d1a2101050108030c0a23120a1b030f050f1c020307080906040f030c1b 63
    0x107146d041840304c80c6091800100f00e070350f000074a40218460752140c1111000070840f01e0201903001c581004900c090020a0f0b000a1003180240098940d1450301d1001600340039810840044003c04040184005d68803600310011001083e905070f0300c4000f050742002c0e0218a03d040c0c1c1d0b50b00040c1101002001c00c001c503c508160750a0109945840840340342c4d030400d80c0c04e5801080d41c004c00c1807102140c5c118040e07101030b02a60310311241031402071028010824081001600e000d507030f03880020404c041042405100d004110300b1004500c2c103001994029112052140e000b840031044a40c80001d0640d44030036404511600000d40e8100901301407071010503400560a00007049451604a030f0506e00482d94840003030f0140c444030542e484c01201110290310480026407a08400d1003401c8486c8014600d014010300c8410005980b0305156034054030561004140461f6030780613504210029550385e401641440e49070034003083d0004145000d84105c45c07801c0d065160441c06810004072401d9a045225 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 994630566 1250 994629316 994629341
    0x70b0a09030609081c020403020306040b091c020304051224100801110d05130203070306021e030112052e09141507030b100c0b151806011403010311100201021c 70
    0xa000b14041c0305009031f004d1848040e40c5a04a00d001070b0104a50b8001c582e442030300a8140e40708000b00d580c04072180490f080746000160700108080c802414101c514014000c4513400070132000b4100d208a0542000c003804e04400700c0714502c081a1300d0040c60340340740050010031000741b042c00c1811100050740c2e0801082c40102030b0400c408220321022400c209203004e900a03010b04042829500e4410103544005401d018031034844000480c900010f101540c06486d80251500f45403996061042c07401200480c1c52102003259000d50801d008001d91089501c0380508000c225104281000b4400113040760700344040f400303250b10729450f074012800e80d00d03c140415182002000450020b005400384c0340382d111030119014000c43d03400720b103020420503071041e84410503000079240302c800304115800d18910760001c4148142801081e40c2c000d40d400d0303000c1e00180000e90075589541c4071405aa89098041c0303004072211604611114400c1d0101c5200c4d07011650203128400903015140020040b009080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 994631816 1250 994630566 994630597
    0x40602030a0605090403020d0c08090d05070e01080111190e13140702070b0702041524020c0d08040608060307090608031b030a050a0818010c030605090a0e070b0a0903060908 76
    0x109075440d088240a010346c4d095801820f041c2e190300e005071030402610009442c5080f0038420307080c4a03a524000c03143c8007071250f0054500071340303000d00000e28400103803c18240c2d641000140300d80c1d410080e081c2c4601c0116400080c0b100612031000b9504d07502c81284484e00002c50200440c56070215400c00c03401c903c0d0400b071288480e500c04204a80355021806002003520301007042201510340b40e04031194500405408644150340c45c0f00c1c055044000f942603440c2c1c03842c414022540c150301400019410003058642da83c0d0099513554400082c4590b001380c0080c0a014008a0011784080050308003401101e101000000d84503420a96079030085821007168440032000c0e441e05c00380110548500601a0711098240718142c1019075203000000c0078240607020307091500030311080900540105031801c1d10001440c0e814107042c0070b0702000040c0f8000ba02400d120f40b000440354001030701c0c400c8800e881c415a0700c0751100d0340104c911036040d0344040d1030750342000b1460302409069402404c4442c40710700c0d803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 994633066 1250 994631816 994631819
    0x5031e150f0108010e07120605030304080f07060c0f0f1e0303021e04123314071704080a0504080a0605060406050916080601030b090a0e0c150f090303040b03040602030a06 75
    0x46440302c1c024014011030003d0315010030131b403a0080c3d01c4001d5603142d041c00400e110b5190350100385160402c2e40071145643c001701c1020900d10003405450b01502c020305e4001c1c11584561111200100700d02d50052449100040705400e215030079040340d006048088250418081031f04004000e5001001e10385040c4020301e402c800b103803c40204440441d401070044422401e4283c07213010124aa4005079080300722428844c1c0030042100344242440a480e060010b10388205025000c074000c8010402400d0045140d411880301e221003050951007a4061501640c3c1caa2031203044030b49025652140889200e106030120402500e904005e01c2058280c60800130380f5550070130000c00a4085c0c40d24500d00c42e0b00078411890600c12420507a00002c103050104403184c18074049660b041e000c4a0a9040039907901001c0c803200f2051081c0c501002c0215103000c846150440700310028401c004007002c41250000307842c4002e0b142031068030020688a1a645d40340d28050034140003941c01104c000030301d103142220 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 994634316 1250 994633066 994633069
    0x105010207090b0a090c0e0628050a05030a0902120a08031b0a0f0c0615081f050907091d0312010f08120406050703090801110406020f0a0b060105031e150f 68
    0x543d440018014400074a10349003011520051144600f10020050380303501c6a015901d89200800018250300000d00300e0441030f281010340c0c1603d003814202000010000040340c20307800019650806004800080e245100d4130005010408451000040340166110b50007400741800c0614441c1150b61f51070b50425000700c0c0c113100540301b0030110001158640c020564454070038480040c0c00380c0310720800100c1140d001100d66200540c0e03409508580c0c015a580e1500804240000d520220004018081801c103101c0300c0c1d80700d40c0c1c1d43c0980182076a41e2001d28082042100c00c428520f0041c41c240c0395141d40094410102003030901600e000d400ca0b03031500050307640000404805c0751003d100041e003041d00b031240445455000e450300740c003000700c43c48000c100702a00b8464030701501e0705e14100c070350340e6407a03d40040c0c20b0040d0b2104026040d0004640f05001c10b811076205070740f041007403030039640e60358520011884420940180e00802112602080500c6040724041c5103141001c4602c008046480d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 994635566 1250 994634316 994634321
    0xc011407021e010b1905010f0c030e0f030a1e0b0108060402150306011e0f03240e04020d050d2303041101030e01110705030d050112030206060616050d08010501020709 73
    0x481a40040e404000300b15040341d410001d0180c0c00541900100b00c4540000018983c6514280780607240b603d007410800403980c0069a085091034142089040c1c0b0000361005440070840402417030140382d2010b0b0b5040556810304c007441c0300d140d01448422031aa21500c0d580307102c0d2088002220303040c03014030000c1103035038001a00510455000301070714114108480311504c1904050f003014180020320744119401c00021074182d03c0b0a03115544d900c200c00141d200181a14114116042601c80d1860000440c01d00c04400c1c2c2c0a035050350b90020301c1030311148041031085a458501600b50b0203560184c0c407485900c20b410000741a1000404200181048200303080385c881543c0003883c100004c5030b00e10303041d4025040200b00c40803002c00011160301e00c00f05e1078a01d07403040748101c9064000164000311403585208030350141c80e058076210303102103d645d0040c0d034a040140c4070300d11030600458020000f0242c81c000c0c56030340f03038448155480e10710103010281140d002805401c1c050302896402141505451 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 994636816 1250 994635566 994635571
    0x2030c0604030c14030715050a06035c040b06031b1902030c0d05070f060f020d0c0e010305071b080d0212190b0102060c220e0c0c0114 59
    0x50010340200d8681d5a0251800a0b4007601210740804490301d20351201d10070300160204074040c4a8104480c0c3c5043c9201e4101c03000142070340f00251810390b060000c242041030441840900e81d9001407444400d10602c0003044040b01940500444220f01c3d0342042d502400c161a401c4030030a080544040c2c030400c020a91700b40000f21500b040051001034202d2500c00c0380400c41e0701000752079910f0550048459410141e000c02001c0150f40001b440001c0c44408100e007250000346860a0703400c1c11240ea548084c55030003140081e0181c0d4845800c401c44c0506517048031804440d1500401c559000c0c40400740c4008048130000e400710345002e0010b80028050340044080400071120a03000440c565251584e542109a180504542c03c5c01002030034007004255034012001244c41c414410360040c811001e60700b041c000c95045402000c1401003100c140820303038004402c10895500601403c80c00d00199404542c00000c1041c1314505115000c49402c0040c1222040d80c4000e000c10341d10341d8101c8441540a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 994638066 1250 994636816 994636837
    0x30518030a021516080a020d17040b16090510031406090c0a0c080f04060201061a190c050f010516032018130501030308061e010915122a0203 62
    0x18110f400c60110540020100441e07000200701c4001d9440e2036100e52500f1804100c4050f0340918044074446402503148402c0108022030f081c40c0f0305c0c09a0b900ba112034401307005644281c09041600c40030030302840501014010107000824560b100c200000c014060038050344400145c4680415080d0a1552040c0c1c0f15103000b19000e860412000421214410b4004c0191351042d4184000410000400c1c0100010001980003082c86820910a4402040c01c101160f0440c40d08108030009c04004c100e03220809035107400d20303070311940c1c00e401d010b81843c045c2001ca00e019440d000030498101e8060b00003440550b82c607a400c022003a040c010103068100403400e000b1030094188044401d00400c1c0c0e00d2501c2c08940a01440c036500003420707551058400070f070000c4001c00e1880381002503508080d0b191a07240d182d030070741c000608903640001a00c81c0c12207000c1c48007000b01c0300c915416018000c001107201904410010002c0c2c200510658404020100210b408064803441d0110114400002c0e90440300a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 994639316 1250 994638066 994638079
    0x1703070c030f020106050604030803090c030a0c0e04080c01020a02010f060510020a0b06010309050f1f09021c0302010e0d050c0706030e061f42020a0308040804050d030518030a02 78
    0x5981ca050701c0600840c00c40204541d00c03900c0c0400d960700c41c00047c0000310300ca21800c0d9240c3c10070710a094202981c84030040c0c02a4003800d5020f0211316442d4201003100c090100008481e1200d050220407486440c0d01d00f00658000a98011965815400740c02110600e080030800c3d5a1200300300140f00703c0c003410040c012392280030700c040801c4480300e00c10307000bd4050600040400c0150380319818254014030b10241c40d0440c0c3c1e04140e4140c141c0c03105643c8009000c07003c01580901d60b0009032840c55071102560250380e806c4040007054004d601500c44140218120350005010074802485940014980c1801e4090302000103001802070007880c405916510140000c1d540c0c070007078041034000200002ca0540f1032080e00080b010403150043c1031007885000104820551600c81c8082e00703c81c43c1c42041c9e105081442030b9099603002c1080e602c0180c0c14504000e99460714101000300740074540000d54419403143c1c04038109500032004200c0c00346a040c0e80c1181c144800d041548980c64071402941145 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 994640566 1250 994639316 994639337
    0x1060b09010f03180204150609350109080309070f050411030105061804020d0204170c010e0f01271a040f03080d020c0a080913050105130203270a170307 67
    0x502036005840c044139000c400e0b034100021500001d080d24604958180341d4140d004040c08401c0c1e2041590000c1c0160031070458451000900e00d25140030b000882c840301e10101d0b030052041c031001b9041000015040310030f99403203082200442e911250140300b4030b54111510f0701c1c00151401c1a00030300d88054100080f49041d070f8138040a010346580030226205a40c0000d600c000d0a5035200c1c0701410041d910240b0042e1104e08001605806030b80c0b4010181041c3d0040814a280d682d001900701051310060310b10000048900c401641d800040b00d1105040170314902846c07031140d1880000030304403900410714040b030301c10046c1c00f500344e44a0b9002c4c90148450740d80d0305102080301440140704c7d030101e12400503c0d10384034028090814003039240c1158060000501114545403086480c1d000c5e4510140030403007540f4001c001400300c144100341300e1440d50040300080100d10750004940f41d000090241d03111855a00503003940700c003616034084a1240c1087c0e500005e51ba100001c1c0c0c0d110305010b854480040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 994641816 1250 994640566 994640597
    0x60e1203090d020303040e010612050a02070209071206080f0c01020d0c0b060607080d021b0c01030209010e040e01060e041a2d180a0302011a18011809020405040807030201060b0901 79
    0x1d440c0b00060780c00d88400c00c000140e941168010078000c00c519516003200d12915007020b82900c00c040e1040d0346581c018424240540d071503203181500205282020801080b0318060302d0041e188542c0f045049000e40e441428070340402244681500500340c1c01d0b1000404a640d007034503444405d03034014010723401100014811b420940c0090000c24011011181000d4461400d14107aa00074039036601d04c1007000d096900c00302420040400c0c008002d080039400c1c03180120000341030603500d03045580b00f06d4648003207070091340081d88007d0140205d040e27800c070b0500d0b090419013911074450b262440d909903510700050440e41002e00090702d080406408410079100360b02081821036001e0003807469450403035205c29441c4800c11255005604c42e800100750700450100014012041e111850b00829807204900c0a43c9046410941500c0010b0b441100d01c01440c0c3d110001441d40d014001d4000345840244004d02c0b99480143c000c6520950003480802c4e158280b03660540660b82c0c4007408286201c5891205 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 994643066 1250 994641816 994641829
    0x7090506031203090f1002191803050303040803071205060f040504020301061512050906060319061b080117070521191a070206010f0e0916030606060e120309 69
    0x400c000804507010445000c030620602d51041c1c80f0b0f40000d03484222520034902041c42103414042044004504185506151903180f41d102d43c21007040101c50600c490a491001e0002406503406c0790890f038a910381407030410b0045c0d00c280d07112004075400c400e030342135110b9242c000c1a00c00d010150125446941000a01015010180c4100e900d03540f144400702d4a40045001e083c149151565902c6801880340c081c2412140007504842142d04424200942500c000811360705550104281c0341800103681040c00080400075080c3c00444242c5881507803143e4481d404038140c074180e820002013514450012903491181e80300e299040804200741c580003c804402818031f1840760740c281e801d41100c035444484c01e00d10b040400c8480d9041c0d2007100850800c900b020039807000550004280035414080841c0e410712552140d0401004280e00064014209218140559840c1c5043c498281d480b45000c0c000b4202d07500807240001c0f0319143c61501031422005941007901c1c0580074528001180f8140140c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 994644316 1250 994643066 994643071
    0x11107080a08180315061309440901120c080601110c0909060406050105010903080910200a1704030c2108071103010c0c0209070e04270506010f08070905 67
    0x22105114465551818040307880d54103d42035400c80d45e440c04100b0400940004c000f8048132a2a1041c80c50001e42c0c85513601c003a003000030035104550b10442007407031100049181c060150030042c400d0344c150004100c1c041c002018090b00c1e0000307010742c41c1e58441c080b0381c1480a0800004c1c880070105d203a41d401110440076081c0c0074402c0c0c495a214220100c0c0c4023800c159540703151540007104101c2400076500c609030140c0003d1818103c964070b16215003161b4081e0031804d038032032051900942525401811007458100e01c2c0304030340c1e00341512540803c0d03c031b0003004800d5861080031010044140d6840080b501900d9000502c50800d504050104030540c401184810050a1054441303000c5114100640a2240300340b294030200c020543c141070035a06040360368003d00c008140d0860044c0e80f9144d01d90b900481900d41903081105d0706000030046c1000d480568010301d0b2001078201b00010000051810f10700910407550702c1c2c4d90f5180c061607480c0071442107408940101000344071000c4240c01558 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 994645566 1250 994644316 994644337
    0x170c0402030c1812150402180f3c06150c100f0905061314010501050d06020c1203240604030507030f0606050a090b13050f07200a080306011107080a08 66
    0x102034070341d600c4101e40340201051a17008182da461040004601d0306205c01094401c8403202416681000095915414805000c00d03440010008800b80c0008021f0a00701c0c1040136041c4400740340c550022104060030050b12601e0140d54000702c0200b00604140884030001d02d10001040c2c4241c1d4888020002c1500303018001209032a40321140115100300040c41c001c0082034035501c51082c0034900702024020803460500641d0600004122503543d40b00c0c0040c006070130050140c4c4c1c5e945616410b41c10501a074008118002c000f00512000c1031020307143d0010801540020901d44000c0c104129030ba0140e0320004215134021481400012140c00b4902001c0d4401e500206605850302d001514a2a2503001107004c1c56440d55040028940849401c0c001616640c08102d20b04140710100540d03d001002c10042c40750440008035218184004400441c883ea01619081d40d01450441501d03801910320074000340101b03403001241c0f24003081400441e6038900041114403029a20000c0d03a801220414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 994646816 1250 994645566 994645579
    0xc0e0a0501050a091a0a1d03060c39010e06040209061009180c0801050d021e01051c0912050406080412110102120109110f040306091704170c0402030c18 67
    0x2400c240d00c0b1a01c2040040c45c171a0b082e880b9015204018086000d01e0380c0174010012070b1513189100e45003c40d1f90341d084210032200b581d48a455855210020003c62519200040c069010260060511000300d40381540d100c024081c0510080707070790350b8402c000c1d10060742c000c0d000c0d03000c03890781e01c0e004107013001f03100190a100c43c00d26035805880c210465990f10174030085440e00216085c0c160b0140000740507040456423142d07401800c0d00461241004022010500705503442c1030f00c0d00e03a00030301c00e07605c149540207490041d80d444c81c40c40f08060814023108075070944c000102814104d0103401550b081e9051981c5109059070780d516003800c5002142d0b1550309001604014505900c1e0030b0005107080780411504020035403401c121203080314504092050000310074060034809141c10400c4034101d9030042c901054061003418031600d00280d500200540e88030000c2d0004c1c12a10010030513950b11035200c20340b00708605003001e20081c1d200c2201c0c4006145003c00001c5d000440d210042d120420002c0c004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 994648066 1250 994646816 994646819
    0x60306040603170d140c0d090c05040f0b0406121a07140705062403120c01020f030f010303030c030c080115022d011803050403120e03010906020705010c0e0a0501050a09 74
    0x71082203024103055000307020000101000b90141ca402217108101c90040c07040b55030703d403060034410b05000d00348a048546c0c0c0c481901d0000d0000302007400b00070b807600400800002145210b094002c10350350028500841c10800c00040c1c10380c04080c840c6070380d50003039401d4414644078040d460814100911b03100a00410310641154043c1c001d010301a03a900c5200240103c1c240030100085c0ca05840040c80b081ca00200385085c2d141d140030564881e5280022010764841c560042c0c0c0c1406801441c08112071010048100000001084002d40c1207901a171810080e104405104500b5219550320a038080b846000041140c000818090f02d6109014815030b00c0001c20b0f07848698000022610360000f02c910510f41c0d8803032401c00c2c414182841c0d03a041c030009807007050b542c010f0b0580c015840f0180070300131280d808160340d0b0301030141208101d100a008210762506460302600035046034009503078a40c078142c803071030f0401d009c0d80e070b44518000700400e003d62482c54403004664540c0686029410880c04580 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 994649316 1250 994648066 994648073
    0x100314011404031809093e01110f0604030f0f0309020604030f08070b070e0f010c05060f060303070c1e0905100e090309030102030426130e0709050303070b01050909011a060306040603 80
    0x111a562480b440c2810514110541030900896203007891151f80c156440c1ca0891110541d8032617103202100f03090054900d2098400581442a841040c10b201c1c000d05040004041d0b03c9401513846000031345901c0e05000315003408904440c00c01a00035000345080100b032010602400321a403000b8410726140303103400c3c2c1584c0e070020b4010b02aaa41da02281202d2030b940381a280880788048409030030b1804e41c549030f030f440e15a255542000f80040041c0c00c41c100100d649500c1c240120340c2c1c1e0b641c11808100c800d0355510001d2403085d100d1104100c2c0004002c02c0880d00c5510741c0100c901911504010a02e8903040083d07a1541040140807500548010800481562000c0c0083c0d4031030b90158201401c98000003030310622010b440801590003020800c03440070f1015407042c1d8202600c585040444d1540d0b29504140d0300c0c042950443c0f40e051001056030010800c0d5420000e050350019105401c45888880282b400e07078000e03a00d1420006c0210403c445a0f00b04030380a1640800010000b0808641d00d84 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 994650566 1250 994649316 994649321
    0x903021909091b091415042c100506100f2a02040e06090a032a1203060519060507020f04050408030403110312010b071505100314011404031809 63
    0x1e07040b511850f56000b0f0281207003448080ca4014035140703c0c240300f080c4904400302c11092009040318005c40b8900b4441c0c0306a151648010b0215816024040039202000e00030440340174032000c501c0b07252046180104c0046040c1c0503580c00b0380c0c030142002100c440c91740c01c180c0e282008031100f1010042041440f0b49405500c0714000100511031801c244003203c0350041c0007d580036048841da0a0740301300c0610030045000184080c6060305031a20024885a03034001c41d40d419032020002c0c0220704e007071b0310302420702a00c4001c4a0038009140c074100000c0d1303914400d00841400100c1000185e0f4184101040018015801000c10318801840280c8264004002a085072020b40c0c0a03500f074403012041204040d08001324130b4034410302100a5007006200712180c0a00d42050140000aa4020899104001c20b045010403280024901400b41d89070120b00020b540d01d2520054481c03080e584e0190038110818400c42c403a4825003580d141c03417581c481c1c6041d529100205800304940003114400508288180f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 994651816 1250 994650566 994650581
    0x635071212140a1d0a3b06060703021c171006120c14070302070513050405031b010207120206070f05040806150d0b0a09061a01021e01090614040b01150903021909 71
    0x703040c4603103d5558038000000340301c030381206403403c0b0310340100c00c04212414246c440c2d100400315040e547e5014945001c07030a055400c1510301030003240c9401198444e8102032b4001207862049030010f4650b80d0b609481e40910b01c14072449010030b0004a49044400d46500155480c042c1030424001d44040460449560780c4142c07403e50041e000210103215070f10b000c0140030600c209607082070100d030a0a88880e9207030312520321100c2121a02c215602c461007420f40603150815001007604c645010003001c06034a4103030440700c150000d244104003103686070058040d0b606031811000189499510740d040d10201401000d4980c1c0c0c010b183d92902e000041030680000d20400c42d0043c04200161350b450024265407241c44d40c02d9802e1040c405203642d41c0d90000340c0d82d1000004045034207104c21319626079401016018000743c4918140000564005100034556000754810104011700760707a1030003100c07a2094008801c0b4002070a441c820405440c009086002c0380c001c014041c0c610b035036180051411502007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 994653066 1250 994651816 994651829
    0x3100e341107180b150a081302040e0106060f03090302061506070b01080d020c01030903050d1e0f02120a061a0c01060b04090c02100635071212140a1d0a 67
    0x500e607080c1a401114044e030340d94041c098401424000c2c1c0421245294011403046030100090700f00001d01000b101141c4460803178018008009603402804410302920040c05180c1c0031590b180316941882d03100b071040b001b00f981c2683c05403c080d25101000031452030586c034103c1c1d12500074042e480c049007003082034034003c040c0c810017815101c81c40403002c0e00f004600c00031541417500d060710308801300740c0000071148118002e48001560b40044d46000008001e29000a501c03d0f152001c03000f9260300c0c503801000c1080c03001d884a6000e5980340e0110060341d6940c0160300030f5040c900414001c03e40860043d180c0d48503003c00200307506455414040c1c05402c03590106105944135101042d04640502501c0048000520144006410a212050000445590711101409000101c40c850b18601c0402e10700000e90403d940e030340c03076640e010344803c8016030307030151111000c04200c540f082c1d010351480c442040403000c6140c1018005038043c0c0d007021419210f55000c0b0f060780b45d000c0c050340c5e8554035800501031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 994654316 1250 994653066 994653089
    0x1a04021908010e06090f0a2915090d0b1b03100302010e09071e02071508060111010e060105040f09060606050d0c050414101403100e341107 61
    0x14024000c04100d0103a000001079903498040c061152660817913990300030261000d80000703032103400c4940b005011080c20b0001d001404942c18140f4456800e50151410703046517030030000e1581d001c850841307104510500b41e00040740c04140c00090040b80605611424424050990481d80c0303081d5413050340221803020000601a070305008542e048610f05090716000e0f90407080303903d807556015202e82c0d010440007440f03581251881c900280b003008413601501e2200c00b00c0d400200c3c60030f40901900350682e40355010612502400c04081d01c14030035540700b0301d4168020015646440140002080c010b0000509242c8981841001c201240207080062195584081e80e1398000c15031001101d02e1140030004111041204008241020781d60300b0100f40221001200352680301000d8030707a081005c04244a404001c4200000c08190303102e480112a0400b40c0c0351303059a0340305807061a209100c1281d29169a45d0804550004140e03401d08411b10054140808800400d1031a0b0740351600c0b0b079014000d541c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 994655566 1250 994654316 994654357
    0x50708070b0f071d09091e010c020105090d090506030615191d030703170c19020406050105030702030d0e010608150a06170d0305040303180f060e07050a05041a0402 72
    0xb194500656070100003450f202d00e606280c20003280859112010f8240b096900ca004034001c4402070080e8500040741c0c40c4800c9000800740c0b11103001c0c1c01d070200c1e164055440c11000980c0307600080341c542915074160b55942c1d84182014100f08894002030f01017600300745402c1581703d4808a040090481b1050f2865121044051800c01481030075200407200d07032014222004608d54500250000070383c0e51080e081c82e10840040400301c1180641031070280640325002408070340305072080e00740c1d84040c000c3e1000d02940c4e45810042d5500c0c070050b500c0c140142d004101621440b0900d5000f40384030f0700028004201245e41d4046140b40c00da1b0404100604184202800b58002c02c522889000b840110001c0e4030723440c41d900b0180e40303c1400901c61000d06840d03400143c100f41c400c1e400f4550b07a5608008031540d2000c0e5041c0581e004600450440d070b000e2401d0072140c060103001810b034003102c00007444211403070f042105010140410b014070200058007804200c0d403665860000c0e01060b00c25442010441c2c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 994656816 1250 994655566 994655581
    0x132a1838010507080c060718052d0102010b060d020409050109110f07030e0907080610080c0904092405090d03140408210f091509030703080403050708070b 68
    0x885208858005840c500c100c054035003508048403400c0102400d02980350310060074007007014030410107042c0030b601904040007035041d00301464219502004401180b07080e00c80061141400464126180c075a000d22440d401b0142c0604040e203000a0600c0040741c0d141003003010403040d410183d040517003140c0115040c010000140b00700d80c01058001005d1060208bd4090301d4018840e82c0d00003c0c01440000768a4107040c0a4840c1250380c240c0944484514500b02d20300401413402550f61500c106441000040c502c0c1c0b2039000e00b4082e801000200d4503048484042100804a40c40219814040c109004012120f04500301404040d49040030420b85401801d140c2001110781c440341c20304d4640b051002d041d602101e907070f661042c3c0c48440380da5680c03c2344030f0b0812503c69444240ca0340c031f50341c003080203507a0402103461400b41000d03008803032224000e5072141d0040c55013281d01c1c0c00070394070a00c4407401103803140c0c00310b64000b4000e081c01480c00055840e45003041d800b040099a00402460902050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 994658066 1250 994656816 994656851
    0x605090306130312111903110f091210060311030105040309062156041d011401063002120a060503100209011d04021917132a18 56
    0x5498510782041111142c00c0303802a14040d044000001050211f10042c0c07540b150701410002f054402c0441d8421403190a0120141c2a9400100e4400f03150903500c284904050041d0342c003441e4551989045a803c0240850b22080160180103a0001d10303004002003041c41e102e550f10010f049803800d12001081003654180070604402201e0641c0c035461030f8203045040c2241d52820603a0398480d5040b0800c40700c001405003507003202014902d2601e440112060304154081e8034061402026000035a84c2c400d42615180c074a00c12410107041e0003801c0f46092406984814a1080302100050402050b0072407818101b40407220981010340c1c5980c10301c11442c2c10001c0255040c1103031419480c013119000000d2040c10b040d00c109803c80725032007040085076219015075540e0090868140e450030b0000b0302c003c02d240601e00200381d4681c0e42001040c075800c2c030090611500d940000400c980260204001c80c51541b0b1101800c0c2042c81144e0041444420818064110b420000d00401d11102d01000003e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 994659316 1250 994658066 994658107
    0x20a0b2109163c061107030c080604260f0d1409030309100507051606110f070605060a121e0827010903170a0302040306060e10060509030613031211 65
    0xe0b0803c0c448195204015400850741c00e4400510b03000921100d070b019032529240b50b5401c010518403060340c0100b41141d00180d0340d80f149001d59014034210200d509082940380c00e1981e00c81d1646001c002c0074000390310380750040004840c01c1c000014200c03c6000702c6808420190b40c0110785030000014407900b40404c2083c3c02d00e4a10200e82048a810118406000c070305c02c40081c81c003141d41b4200b01500740301596100e220000000200d6036612008600c65085a900c0a00b084641d6480d110104480382030190002040d55101c1d210840414440d48038020f5114414006400202000542c0c0b40021b0104014004115400c1c02941c0f02900daa45580c0300d03040c01180850401001c00d000f0400700f400402d802208031134154403240d0728090100c0480181c8299040544910b08004000034209441c4207035034410610745070b403045490313200d4104032210300c00c001c103866166000d43c0c081018a103001d21800c1e2101c1c13190800341c44080891503400242d641a20f2406080340c00413404004800183d40d0284 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 994660566 1250 994659316 994659389
    0x918020301021303140d171e01060503060a0602070503101107080723010b0907120e0f0d0f08010e160e091905060616110307050604090207020a0b210916 67
    0x101c0006c8081c005100d4040b00c0c10305045010351202082d41444810700741da0b0581e11000c02e9003855a1070f590b01030429031080c0c03156401001301e640002804d03840810200d051754801405403912500e031003903070005481c02011489403403204228207000215030b24000d1110318800c5482400070910710200141200c00505070140590508035005e590b6555604c134160b105a03030307041c04024001c951401780c00415820b40498240d00c60000c4007040102c2c001901c800c041929590341d0307009080304000b114101c4080c442c0440c810754a0300407449401c0300140012141041d86040b4a08445c81e0000442115041d125818546458800c0b1b011200a500036154840d41c15903800385401025017210111340310f131b54005490100c0d15686251540e4050202c1c01c01481c0c0104025142c0c1d03100e010820080d4003044c800c900c07542c00c01d1000070304d0f25040700a0b901d1070543d03448014201600610300c060b008070000e08442c1b980c0244040c44600e80c003d0011040641916954980140000d10144451404903103894 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 994661816 1250 994660566 994660573
    0x130b060402041203115b09080f0a0503181f0e0705061b0601081b010503060a0315090303112a030415080f0610020304091802030102130314 61
    0x5115082c3c0319140c5140342513140c6400ca1040c0004080181054910400c510740c10205641ca80d1106501d154402c42c51012503800b04611200c1031012111820529603035206003103039620001c0c01c801c05034080d102c514000c02c2c9541c81d00342c0012114640380c4c8458940004200040180551039902c0c8035a01c13448600300009080c5040b0612107a0224109040d581403020b4a03001d811850032400d001d0340000300b00103020b5503103d10102907022000204540e000c079291141030000280400b0000300700340c81855443c044449900060011210340d8401000d40c1d4110003a250000300241e5114043c10905404410002da00101d81c60000c0030b0760328295400f40352540c240681c0091083c2c41c40030040c1043c840810b0030050040c0da4115080d0b028580c0503d445d0100c80041d0456250800031292190035005251011303540da40b0100441c1e04030030744803c0f0040c1d20903c41030100086603440b00d2003258580591170360700c808a50000f8203a0340f125800c122205c050034000c0003040101c5940c0d291900c0325001070b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 994663066 1250 994661816 994661819
    0x120a020a0e0a062007030c06020d1710060507140d11070f0e1302011112030109062903180a21170402100c050303150312040f12080909130b06040204 65
    0x2070110a01404001d2440550704ea05070054008100d54401507521864034a19695910000780d156084c01e5503c00224001c41c88100c51908207074002031040b0403940c80706076024280703402140c4503004180c1c12a0712031130780303507a03200700c4d040422015106690070b0307846540c120500c201c0c04d030a100310b503800702407100c10f4940b042c0500404044e0f1982e200ea40c0f0300c1c061510700708034001282d116031f051901000364082c0c0410083c820340c104000714180c0321700550901410b5070300c0c006d21001e122460f1020300004000c400c040c001e1940c5000440e00304a40300405000e0390b049a0f00e450402c2070303110003102c2114003d00c0001c810600e8540701e800003025810304990316010010000d040440c018002449180c50281005500340504107041c880c540000480e601e07494084500e12b05660280481b611922a002e4139041400c402c0b0101e81c2641e0304141c0082165107400f4055119034041c0e501110039402c03d02244016071140c00711203109800d150840c1c0d00d20100c0d802c00c1110180090300c0709000d180100300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 994664316 1250 994663066 994663079
    0x5030a050402541803042102031b03031903060807080105040506060a0810090303090f06020307020601081b0d140102070c09050108160320040f0903030b0904050606090c120a020a0e0a 80
    0x40181e440016040c044c64108411802d090070f40c0b1540e00a20643c05461002c0c10012003540c8076190050301c20780854107d07002c10804111017003050310701a40d01d1307401080034203074804810b00c001d032007281641070110350191038081450410741c50b07821009007a95600b042006100c82000b00c0c5400207002d4602c070800a05000203103485006050342a1009500e402103003042500c82d41c0400c240a1700508018002d00310b514058000e5881524490010b1207900b001040c0c5210100e0040034110841c012a880340346010b0600c244091180c00c140e40100d80c0c1c950341100600f0038001000c490b44100382a07a01142007502c04001c40c0c1c4180c12101c1c003a405030690071405070100c0420402e480c0c0010070100c02000c404c0c5290700e21480381c400d940c2c00c94180060100311031415000078041b5846034405010090031202448030095080307030b000d4003030750050000c1200c0e410b080708016042a00700039034900d405240d000701c107000382e0240c6000f011241d0000b20b000c00d056021031000601107041307418031703c424a0f0a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 994665566 1250 994664316 994664479
    0x2010c0e041b0c0c090c050d051006050319021c05070906052d0d0f020310050108060d0201030b01050f070309030213090b220209130b090d05030a050402 67
    0x400410610035800143c2090042c40502d03c0300801107044148621110344100600c43d03048941d4000c03d442c2000082400460000c000000fa606160b031983d0640d9a8200c0d4001d8010300c40010209141e400c00620210480d06000350306080b1a5003c04203950421603001070072940190b2212082000902c13590505500d05840c40b51a9943c40f60f051888441c0c0840c076900303e1140204000c8124039050301381c1100001900918840c40406821010480d076500041d126401c0072038040390300c80314907240c900c0158025444820280b1040c907141d030401d104030303014015950014400343d0118024030381c03c2046141c00003281c81c0c50702c480324080c8141519955010100a40984150480390101d40800c40d00703800d07001d6020400341c000b0160b000d00c1c1001ca86180394103140000c259690403981001506000d4002185011007045941e1245940e076804410b100a14001e001241d00c0b841e08020070001082e1521181044095400440580b42081c0c22a511850040c480c83c000800000098644184bd45 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 994666816 1250 994665566 994665611
    0xc0f1a120403181508010602010f0b06070b10031703040b06041a0904030509031204090f02120c0d02040b0f2101060f080603160806180a11061c020a02010c0e04 70
    0x14104500003c40000720024440030541104200c0308005460300c900b5540021001c5c100c586a4008000c030843c4010148151401c9059150304421304000f0103002410480e002c6134400c0164162010550712607441c07020200042600072400b25000c01030006000070188a150050741c02c07502001100008c406801c0e40707650000d0a03510a602d9400040e0a140c0140201e07545180b000b8161030044a00320310404541d005030043c0c01c0094030303001442d03c1d444044c0c800c5648200c0c200101890990b5103102c030802031703803040620074015602400000350040084000c3d0203e8281c0c3c1459a407513020204c55005021501c03c030303071000c2c050100010026560007441e0381c4900d851303e00c4d00094940d074110110b8903000040701030108034107568100040d40e6001040e21406040704ca06015410b202c400340d282c0e9a2a0302e41c1004d480342c03070200960412864880e0082c6501c00446a4800010340d0306030724501203030011642040581d440d00851b005c07582e8001805820403404031000c06c0186c0c02c45000102d1440780 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 994668066 1250 994666816 994666823
    0x3060a030b070207030b0702151803030c0c07050a0608070206060a0f05150903070303021516020c0f010c050718181e05190804090c050a1e09030c0f1a1204 68
    0x111011840440c420f100d084d014582044138820175061000e4001d5039160390310b9207135207038141480220380031401c007000724007815031100700039402d45d02e815040201c1984444410380151103950000103590311340e00c01090040241d81c40c0e43d00207180560000c1d04101d4024000d61040c44032040030b100c0004c11214a6051b141c0c241c40840e25031001c2140b01140c4d2180b407461940c544144a800002c250740040c200070414521b140070f00c3c058a49103440443d826003110b1980250300b0010400c0380d0790828444e1294000c0301458404000c401d60740394a410280c0c5074008540700368000803220681c0f052070090300131014403c050f4402d07070f00440d150780c442c60110001c1240512070816000d4144502000340c8901c0c2c0c01034403400c1600e03c50900d17101d40c2c10b6100f403182403000c604000c02d0b91002c0b801082500e60404498880c8141c050386102c41141e101c1983c4042424021020408004280c032441414050301ea00c91110003620704140358074134503c981e0011009503060400601d4000d170075100103e900241d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 994669316 1250 994668066 994668083
    0x10903080306040f02071101030605060f0d09030521242d03030301121104020306010f0e030106152303060a1a07020d03050703030f06080d05030a02040e040c081203060a03 75
    0x21610002405001c1448040741e2181c000b0806e141800b00620742d01d0050341098904122242e1740d14140280c2d8010030414020f6608180900d007128625a00130480161103840c00c6031400e0220344205048080c07910f10307407501c8400364041220310080e404010803041c01c218803000c03000d0140d8002400481e9440c400110f00c198402c00708180c5181c20310080d0740d4410040542ea00e960316015244c0d01c0703207003c0105445c2900440200c400f035007064401c172406024182e5a500c4119441e010a0b610300ea08002c40540640d80e810000034048484900012417452540d142001c0c1110102c0c091041c80d031041080000311400c005000250340c5d0051703010111000c0303c2c402000c0d82500c5022400a0190181c00381d00840d0f401c450000305540100280b0765140309440800c00090402c01c0078044500c14010b400540e400311205142c960300880155922982501e8054981910390884401c20101628101c2d94200304007014800310030180190320402181035062425441c007000040c40801035032102805541 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 994670566 1250 994669316 994669321
    0xb070809130905060912040b030a0b1521010801020a0e120f0a0807022403130203072d170a080a0e041a18040803150d150207120c020109030803 63
    0x40350681d8504003121450000c00c000205401e000d500c0d040100d80104090082c5038181d2150808042580c058600d9110401d0840d83d0b54a40440103000707400b1000e600002103004207024605010082c4003182250003c112000400c01c20704407154010707000910281d00500411b1140b5600450030320600b24122000350984c000401090300300030300100143c130640284811282071114240c01000c1c000c1c82590ba01c0641d0040e2201014603001e103d1030f44646041c00c1000c501e4a00f404811081d440c1c0c002400d071013105650b2035006200303030505591100c5680003103d8120034200040240001401092501c0b42d10703d091b41c0c81e0985602020302c000f031085002041441c00c0703910504402503228000f50040000101801215403545440d01d03000744200c40700c00c1c84c6810360340c44042c100c3c0501d80c00281d890640d21118030300e815180c21544d040e50006034042d16000441d80895010015094000c40107a451959043c01440008250503100510403035214010060b40c1c40442d0b10b049135002410360b901da4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 994671816 1250 994670566 994670569
    0x200d0b0315161814100f141b07080c0f010f09030312020d021303140106030f0632040c0f05100c03050c010e0c030f071805090712030f1403010b070809 66
    0xc041c03894403240c0384003506000b044251130055400145503048038002c404079440301c811244080d0354081c01d0005190b01c2d00d0808030320b4240000d0490100c2100403400f007110500f010a282c50060362081c0003030f0380001d0303e0405c43d0800003014146c0640a190a40c001d500112005d020210f0902c401410003030802408d1000358601e0313064072060064110255a5040d0b40b034940340d01c1c2042c07800190b409000d40d01c81c40c0d1000805107c1c110440398891607254100fa00c0d0344800d402442c2c4410590704802d100503450aa03081c130081d165100044000c4412101e05080c10010301400540d00311031502000c5410920040c0c0d913500850004a40d82c1c6800301c1001c4480c9400c0325140140082c4644941c24154142416800401c100001150079012200740a441d030280641c1c03007007d0700c1101c0d103484440408903641c0c143c41d0007040e40f14184070101c0c0d0036a5035441070030300d070f10800900036000510078001c031800c29130b03004006500c408144113184c0d065505269564400f4460040001c010b26400105072505 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 994673066 1250 994671816 994671827
    0xe011203021005090a0b0f10090f0b100525020f0409060f050106050901080f06061b151003060e07030201080a0e070807060c050f030705150a200d0b031516 68
    0x440c0d070110303018810f0f8109862141e030f43d00c1190000711500f040080020fa5104800360515102c0c0c1003a40c4401c1c5a549030248082c02800c108051700950303901c40d039901001d5200d0f800444800030041c0d80e0700399949800e01318118030b1240c540107440e00213000c0031080b025942707400814a04001c2140d000a0052103454600d0082000b00755102e410307420100005000707a0400c016085081e030a1700d410040740e9a00c00300640d5940d003151520380c0039405000c000341c1c010008100c0c40c81c101040f400c5403400300c4c0c014001e80030301600319030b9a2040aa1903009200700120b40c0203000c071144000000300b02413030440d8006401100000c0a100b0110b40d00c11100c00c5a400c100700c904001c003400403c0d81ca1b00c81c3c5416006203418110780045c0d07010720a9a01c503092800c000030071900c40907005030107860300c034a426003107241e40b4002410303841d0003944031282400701440c8540c544011050f149141a13070b4041801000065a010300340640c441d03003180041c8000c03038407140203180e4001300c0950030300c1440050000a546 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 994674316 1250 994673066 994673083
    0x40f0209030f01060501020c06070c030f03020709110405100201020304020d2d051b030a030203091003140a090c140f040207081908011d1620100203010f0f0e01120302 73
    0x5041c81420b0745110812019072000007519401e900340c5d00101005414041d4070701c00e40360014191004a030007000800c85883c9840c201a22030320685010503643c82d800c230140c9202074000741132400c00150070060391415595840b0031049600003942940b6103030b0000740c0d00c000760000150414142014203600211401d0303c000004c030f02041054400360042c20301c1940c85610818841c282100300c0c50010981c5800201c030f00c1c40c19031640c0190f1401424030240306504d601600481d003419207454160860040c03941480d441410180300c0040d4a00705810030680ea6011035020b0701c1302034600f1002d100c294452101d01402c00400380c8004d03a031900f40d40740c40104d83c032600b008044481169010114210307800016030303048074008156400d822000903d0148085000d0381d120220b400c1c8080a00b01942c0110b03055020030040d041c0751440b19080c240c403181070104030501c050801b80c0c0000144054000b01c182030f000742a0310703400321031000d04060307030100708002c18080c0c0000d04040d0000541058030030001242d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 994675566 1250 994674316 994674319
    0x50405031b031b0c040608060405030d020d020d061508161d06160308011d06060703030c170a06030303060801020a022e15090507080402011e1101020a0216080102040b09040f0209 78
    0x2c0510f981d0051203a102c3c10700f8900b10f440350342050300000e800580061240d024a030418080e51a00840743c0d05080294000d50744c08140580070300c528440c1c14158411701004111111081c1010020802e00070407200004107800c4041c1002181074803065448030a501510f00340280c041d02e03441c07100e00001c00c02c0c05000d001e9032240c0d60b82800b9004259110b1103403412a00100d981042c0c8685540300d2242d001412904503400000034440b82e408640b013030300160004400b42c101514000036034100d01040714400ca0354940c4154890380c0030410150305108a00051100030001c5050071400c01009485000c05a06c00101d04181240c07502056440c91540310300b42c070800c41c10010660040440d6481c07009510410031aa403401000401c0c00307006d050220b1140364140d540c420001c51060b144d5402105280380d0608001202c894480044000d00c018054200c0ea41c004013140d038103941070413601c2d800b160050006640144000c0003003446010540700007220844003c603108030000c5006009001340307403640307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 994676816 1250 994675566 994675597
    0x3c050309060a0c0e0f030709150f060201060302010e0f2d010f0201050c031b0f0304052a0a230613091d100f09021e0109120b1501020a0206120118050405031b03 70
    0x3100892109c001c28110361200d1410890700b40d590905a0881c4d03030522000e40030815400761b00c2828580040c0c201101100101000c45c5400885000f0741c80c0030700c0340c0c050340b10941585046000d560b0002c11820b401b120620003030051349082064001103001c064003001c690011f021f01d40039843d800703c0a1b1240c141608d942d05e5204c1c909804c1142d50342001d01e84401c401014011500e11940f00c0242c030815000d80a090010118500030f5071503108500c0b107030002c008241c1e0402e200044d560301402001c0760040b4100710740031b07181445001d50480e03614150b18440c000c1f0703250200c0ca41074000305801d5100801e038040010f840f10307040340e8200901815580298400118245c0540310103040300d00f203011007001c0c1d9078013030038640b600c0d0001844007103100c2c00b5020020200000701240980c1d2186465008184152884030f030030f59002c03e5990300042d0100d001c0b1510702c03005000c0c80d0303d12130031103060210460b002d01c483e051a40f10f05840344502190041c4844013007560ba40403507410001c5801034409030850 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 994678066 1250 994676816 994676831
    0xd09120305071e0213180f1106120a060504050f070e1c150f0209011202070609020d051e0d0806042301090e06100302013c050309060a0c0e0f030709 65
    0x2a00e406100f0580880c0300c0c07640c0150402d4001e00314414040c8042c50220200180d0040307032120f94200e0207508084540345519180340c840384d100c07100640100a400c0c2220b4001e41045920081551318580140340168900030030021a00c0121b210300c3e4018800d03042138001c041c6460046000551007880101e80c00d4101584041008800c800130340203040d81e05010401140c484c2c406100341c0c418020024001401045004515026139000b801d50b248204000140442964085501c0a1005c54196110303000a0500b021542800010b0f202800d008000b03400302ca034034040c010706600005070085000384d5803015458402950268442201030108800e600c10b5030f920170440c409004e101c0341884e8036004070004240249038003143d040980c3e44c140c47c0d01c00b01c1c01995001501c208034040b10700c0c80c0c01c02c103502664405600203e400092040940c5c5d06952845c08070340b824580040500a0842c3c0e52070080c01d8800c040d403009004c1d00c5080d04035007a00300c901d403000000b032038030803c1d401c000040b0703181400323 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 994679316 1250 994678066 994678103
    0x5041e0906060c05010507030e031e0d090303020a0206220605060303072f010219111c0302010902040c17011701090515060f0904080f0d0e0307060c0306080d0912030507 74
    0x3d00140c03007440380d0002c1c021952001e204805584e0b08030715114050340140448a2541220000b042c0c03113100c00001c02c1d00b45400141d640f01500c0390b100302600806e900090042d415941032140c0c41d0b010f000000b48005024094410030031101e080c44000d0410350b9034201140d002e40e4140b040315042500103140039003200c01103050340d071200091208106405125040001c1c2540041024a414403043d50038410860343e40c1c0764003c80c0b1241c0c43c034031540803070074104454081c400140042812802a4000030f00b0711101d1050008544c0151100405e1110b20003103a510010340d60382c0d050640b00b500121100310710038640b07020301601a0700402006401041460a8119681c0000d140b0846040340e120321544998810710142442c1624050408001042a821031b69442e1008001700302c1c0c1800001200280461990706507005403804480140d1144076a614542d0706000300c6014090702c00c09400d21000510000d05200d1071131142c0e03207086100e501c5100074035000c1c0c1c0035528072036040340700c80100403810b24 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 994680566 1250 994679316 994679327
    0xd1104021c0b010e010c060504020102010905100c0909050103020303091e2106070e09040618080307030b040e0f0c010320040e07020610140942060a05041e090606 71
    0x50314061070900d81006040c29620485103043c0050045e15694509491900e9039409050014030503815992208100d600280b0704000f50003031448004030000703c0c0e1395550001480030342d00754482c0501c030b403d01005001682d07000c0221010103c04854109141084000441d19014103000c280d03070289516103400d5620095004d84c034961107001054a005030b94903001610398845032206540c01c00d44010000d00000d21560000a08041d07100710b2051459950b601d2504a601c11950000040d0702c8240400d5542054007603c82003c0100019101c01c480c02c0102e42c5d40c420b0881c648a042503241c7c00101424103002e182c00314111803010790b031551242c45808003d022681512040c00510403d4000f0381d02d006201060015205032888001c1c4e0141782c8000c009802c01c02405100c10302c0c004103940d01400b2181841a0540c00500b07012841d141459590540501503e5409900500d4200140505035a010044500780c8907200200742c08001180b403103042e04056500b00d240900c0c41d0000125100f43c004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 994681816 1250 994680566 994680607
    0x91103010e0312100f150e061b0c09190f020f040902190504030503030f091906060614120604021303120513080a0c03030f05070b010e010e011a07020d110402 69
    0x6a0041c89500d490080075404019881000000c800d611400d11202985030b2076012000c0381441c10610101c1c4206c001010343e03000c40390040d401e2208035044d074000781040c040c5003603401c4100d54a210a2400c521310104004200104001c331650f1040c81300200b4440d603066071080e264500c415500d40e40c452880400942c01040300f800d802c0da111603880c05580c8140100d40540b03612602842c00c607120f5104001c00c04001500014045c044c081844500c04203001d650000740d8002d00d00070564034901500948041d03040c03055140341290411580758400412440f06810070b0064400580d00c42d12240000e0328400e00c2d801c000d040014074428840d04a5010001e880b2680c680749416800702e82c0c030001150b1b9204c5081004100c2c0c2c20106080011034000c51a040b400309441c140384d403800c1c0a2b9620015802c409030030101420f0348003c0180807017540c50020901606000c0b1644c0071a410b00f2495944500500e01d00034402c580c0c0f000013800300300e07031540f01810448001e1300964550003c00020840004078 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 994683066 1250 994681816 994681837
    0x1060806010306150e01060905010315030218100b120420090a02030610031b0c031101020703090312020f060412050712030c021b0d03111203010b071e0c0603091103010e03 75
    0x8540c13010a6140b44c0d00b1503076049605a03203803403428505c0e0000540c00341c201e45c20041075040c00400000050f0b150080c1034505080707a094188854030b0586403c1404000c00d400c1104d1030f002c1840f148003c0000f50f020260015040862110b445614444685c001d19220026580040202c42880700e00312194002d54001d42c5d044444814262170103204904450004c203001c948a200c0c181108403c0d070041c00c0d084440e600030b24005035819440c124442c00d9a212100c12800511000070800c28800500448850505680301a01000040c42c0085548001c0608003501c00c20108810616950064040b140007030703445410300504051340140036000703046180e00c000c0507004000d4808020304440b030042003044001080300c5118452a2400c407000140134160060301c0c410000507035104801000994000c09135088110b90350720692814102d030002d441c000c05072030f0f44440320403000104400e090b1b03801d613605031400040301801428010400d00b80541c00c1e80d0954070b00003c1104005001c002080702c21070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 994684316 1250 994683066 994683101
    0x30a060227030c10180b04060e0301051807030210050d060914130314090a091109130c020303040b071e020616141e0c01020a0c0204050a05090d0302090301060806010306 74
    0xc5510501d501c3e400c0303802c0f22035440854812050383c00c5004d060b400c01a68042100343d81029201c0704046800ea00c203412020108000003c41c40c12841d0901459900400c0420b0700c130002c1e104420165503406050100070701c10b00401261009091040080d40c1d002e4080000070310210347c0d81c00d00c10000b001007094000400f85140d0000708110f0401b074031204d415505980e140d03800345581542041c55040007550541c030440110700090418000d0040b5503085214500f41903684240e44104201c030050080000b04841c00c100b41d450765150003005803544680c0052040d60581d8504004035601b104100d55031108801204c04507012607030004802d4401c100d481042e404035100d101050b100c0c0500e40f402400060801c001800c80300c104600c05d00c8a58902c041114201f42f880f414450a98100304a4200040c46c0c0100c510150324040c000ca40d0008801c0c0000c012506107034242c01e4a031452841031205040d000202e00300251000d600c000002c1141d4025209a941c6902d8000080e1480c011035000481 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 994685566 1250 994684316 994684387
    0x21603151a0a030b0717040624060206040b070318051f0b0906060a051b0607020c04060303170408130801020309060f01060504062a03020307141614030a0602 69
    0x1030a41080e2211001c00900161205141d60b4031082c40305402000c18040190011030054072001088400380980d2040a003c645506803507541c401c070403c1d0340403140068510b03804c204281d640100340e09030815000b111024103a0398600c030030782c060301c02d01c01c0c41c400781c0c03455038141c8040c0507000c12940b80c1494103204240c0c41905a0f46104d003a11210786c0395a52005911001c2155440c0403c0249100400c500701103082c080f052880808004400310001040c2c1c0200e4108040d10758107002d10448081d045a0801c540e43c21920000e203082c0d035028221a00b1481080400c2c2070203410703010780341c0079924407003100e1080b51640d01c5a8041e4000762030144440c410600491035010740401881d040c1d5603541e503603604103450904105c8040382c1c554520720380c032000e2a0302511400315030140290320500030740046907079480703034500b810124011009120880d002005c0850b074510f80c0140d182c0840f8504003080318001c19120000c0d00b0661000300080c140340c030010b40e40c940f54541c004600241104140c8441c80c08 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 994686816 1250 994685566 994685591
    0x120803060a06080c12040f0515071b0b060f2e0e04050103020f2b0b070f090509070c0503041503060e0109060509181603061e090f06090302160315 64
    0x720140d0f0714801040e414800c0c1c41c2c2c0b41c030801c1c17031059006020716075540d852001030b2105410041c10304082c03036820300000204900b82d0b40000302c41e4440548660301e4803040459454443d0381000c09011141b0070b250420044c411a611400c000141c80c120342d45074407201401000641d900050301d841040440c15044c1181444d140504c129412207030090491a42c11242400300140c815440034a1100309112a9000c11040c0f9400000d041d03044c881c5aa03081182006840905805000009242001a0080103015984581c00c0c02500008c5a04042c1121089440c2007401c0d4002c03500038165803800384c052003120a41c581c210104560751202030650b50b0362101c05480c151841e43c090a82c101c484000454543d03800d2074094400c403010f10702a5481402c1003140c1216051041c1c1c000c0e60141c0d00d4648080021091071180c40c1643c468240402040c10b0a03622810403902c81d00014002503900e03944001414000e01c136054002c60041c030052801c0c0c0c0c41e46008020700d0b2200d04005c2d10545003210b08500c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 994688066 1250 994686816 994686827
    0x9071107060c1101081f060507140105090a03230c0102030a1d03030126060915180c090a1401060f0e010e0112272f011413120803060a06 60
    0x854120404070381d6998003600540380b25401401940300340b0305400e13560b0341c031420020000c00600041c0d92303a151707190280e003002c5420042c1210180c1044e49080c0070300c10b801000003429200c03107605080105178100040c407401c01141c242d8080004201000a114007140c0042d4003d40c4100384044080143e50b13a408106044007417003c10701d4403940d008000600c0020030410711101034941c040070b5003204d8503944aaa0382003407003d440c001b610754003800408000007840d104803603100c0c807800e0100c803031100c070040041d0340c50044c40c6e0b031740c0d01414100000c1130118899420000700400503000200595039a0071000788070303021240c002d600165821070100e80540c82003e445604001c140e513898281d14442c81018010500c0618500c008480100c04c900404d10018079081054068484250010903209a100c80d404000c1c0c40c400040b40b0342d1460080680c2c1020801040ca049010510b0b140c098004400d114460141c04c03440c4080f002d52004d508019006c8003d501c5408281d410310a8a5a600c0e8151003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 994689316 1250 994688066 994688087
    0x905090a060b0f060705163203010605130f06080309030709090204020d110a0f0f090501030c0215151302070209190608070b0403060c020d05040533070b0c070308041e020907110706 79
    0x236540405c0050514078900e610710658400c03c028000540503607600005040580d141c100036a2442d200d16800340c501c065481130000504402000e103161650700f400203612000d4030b00540f12402d64541e810810354545505541d004420004c00304446c8500c521070b4070458001c0b40b9844002104045030500c03041c0318082040f050307225910703815001070038080158040c00c00c4840100841c4200050410791044002410b4010002c802c1020900d21401041c41032203160840400034090040000c3d8005032910b0030142e0740312015203032034a029408140f00c1030240c60190301005051140c9000070a8007210340c07009104580c40b400302040007400c800c034180c1c0c0700c0801840ea600825070921041180b0705103489a07050100c03000300c038404802e5074030b1404d5000c14900780180110b00b0b070210745502004009404550480c3c4400460340c1001c0141e98010895540200300420604500641d14a00c59030601e030701c4c3e001c0c1ea009203041038618000d20010100320085110341c5052250080c0011481c0c01050b0303014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 994690566 1250 994689316 994689359
    0x3070e131401050105031e0c0301050307090b03032d0708130801140106030c03060803030a0905070509100909030c0b07020d14040f2d1205070905090a060b0f06070516 73
    0x1141d0b60318150066607190801458a440701007000804a02d10740a1450300384500001d000003a00c0394140300600d8902900d179005440f07501d2a2044a02c0503030350000944002e098029600140355502c403100f010283d9641680c07090786407001c102d00e010002d410300070700019035408612002141e501c403811030a0b500444441e042c0340140c0c000500499200e0f4008001504d07040c10003082c0300f80e0792080380d443d5500c1299402c2803e07941e102d0020401800740100401400c003114042d1490501800d01120b08030140b069071607540c0d40d00206800c041c00784c10782e2440f80c1d411006540c414908000c0182d00c0e100310001c0400016050414400e40d4064a01642c050714850304001d5034050400006044011041150b020b003200b56200c15800b0000d200c80d00d001500700d403c003c500c86540d600c0c010b4501107541e00500a060306080401941140c002151110307590800004a40ba03941140815a400c4421400316003002d0001080710030302400060300d0018403802850410441d680d42034980301501e1050400c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 994691816 1250 994690566 994690601
    0xa05130209150303040f08210c120a0207030b0f041a090307260403030909050703060b070308060109030b0a021b0604020d0209071404031101021c02062202030303070e13 74
    0x242469100022001c0c0c0b52002030201e924203926485144030700e5419911450090740301605101c0b82508201d40522030380c9100f40300505044004050310b46481c009400c1408020b4040340c1601e0003803081041c00000c507004010a81d1504161500e111022002c8a00303036403030311300800510340d00c16584920b14482c0303460f003018504103c443c3c4c2d80c0340352024880e2452803505200c0c011040c00342501c5030062004600c1ba85403030034003910f405140c01c143e03071008000304180f524004003001101c1e403103c110b8000d268103181c0f041a554034040162120b00e201e8002030031116242c0308210720020294028108859400300c00b034500070360042800d94400007190000d4001d07401c0300454005040203400d658100b49641000741440034001c820a81c0c94000342d00c10380720001c039101d0143c0d0658060028101c9100d09401040a2080701c0304065900c050290840044110485449100ca0740b07da03030350005594006e060720340e40c0c10100341c000c0c400b41c078002015109a0007401c5150019206101d41d0340ca125001031103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 994693066 1250 994691816 994691821
    0x2f0f0f01021902030304080f01051618091e050403031a1e2413050a0b0307081612020c030703090b19200312040b071d0405060d0210080a05130209 64
    0x10040030311054404981500c000c0c000030803c007c0521650304080012800055545131001c0d1120f6520001d04854040c4030000556943d0f2241c545c0c0710b401a01c0c00c020f00800d540c8240c513601010044401c5416200903d0241844205a40f6400c000c40030707c441102c080d512aa0300b000c006024034000d000c8696030341c021650703924505202ca4800c3e45100003007100e140307919421403031440780d601c045405444031802c00001d000c00d1810500c8a400707401403a1000d0305514014501030440c84c0c1c0030b0980c001883c1c092800300d04c1944100307030450350105164000d6449140b40e008441d600d4000c0c80040b80032801c002c4010410300c600304159510203003071071001811100707000d209903a04950b60100e0011611500c3e607d8108010410041c0036001d101a0803840500d02410410345003880070300700208010903c0301070800c040c0700341940a0060000ca07000644c0b1b4440b000019102c00e0034000094008200c8a05840c106030400d00c003502c210045c200c00d1146656000d500040501e4101000b90b10440c810003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 994694316 1250 994693066 994693093
    0xc0203120a0f11040b03090d09080c0d11060a08100605031b0f120f0703060902090303090f0f0a08030a140703090303080a09050609010f14090c0d2f0f0f0102 69
    0x40401902d04086002070401801c020102250703101d500a0f004103900081400a848010840c01003502028500a84114200502940c40e100301d08003107441003d00c0306012050141e110403801c035040303005040990711074104c1005040c2d20000c0b08e8840c0c00c6135540c040003070b65a000f401141d200d10aa04001800d29403810201078498100050b9001440c4080c801051035102c0c180780c0358054030315000c001c04949446540142500c5075034000798000d500500a01800b61000401ea40da500411107501120348032030004904d04400811480d070380448003810001310490084003d00d0030b169165101034101a00c0101e0603503610446000500241e0844020404648150034003038000c034803100d000c2040b0803a52503103840c4c05001d942c0c004040e503441c2444184982580302c0e841c003c80124002507240d14000700080c1c1c96000e0001c5060207000000345d0001085002903c0c0c1102500110303103012410b001c041c1019002020b88141401000400e6030380105191058074048080340c16802001169480d98 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 994695566 1250 994694316 994694321
    0xe1003020613050915040f09020f0609030c130c140a051c021902070f0e042d0506040c0f090e0606040e010e010e0607170c040302012f0c040c0203120a 66
    0x100d90110381c0e141000c02203625644c9042035409a1103884e201c034860b680f4901000201c6900100d0554502c7c078065031300c4e0068403a004501e404000889407140c0320160200820b081000d241a1765600a2101100e800b0040c41940120740f0401941e85c1c492201c02c0003031a12805100c1d41100d00c011900c1031013108212103103420818852008142c0150421503800c1c0360440c2c404140101d80c0150708040d40a0085080e0800e140d00201110b004080103400e140e101c004014501000016020f075501407080c0095202485400455520204694a47c81d107810140e43c544a540103885440640000000b4509647e000d80c900701c11015003d803405031281810040140000c00051485549032550510a03090230302c1410424107450340a885145800310000b0b0080c5a803040030315007003040da824001203807214402d039001d4941c20700388110b03030088000c030620701d060148400b800d030f07058a1481c01c02c55200128141a1001082d60140504c80313042c04280d07201d0040280070010410340c0300c0010721164058 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 994696816 1250 994695566 994695577
    0x110607020a030f031e0311070b220c050f010e0f012d050d050c0f040306020a090b07150e0616080a0207060e0304063506130e0f01060e10030206 63
    0x3040c0d9204281d80c3d650f02074600810740c00580204152000071015039601d00e4561090300100d01e020010a030010300d040e10917010f801c2c0050151580034000405000700030310b80c8135405100300c0e10707171411001a10b082c2c41d0780042e1740506401000132091640d000c0d4002d80e13510406101c0280010804403041d801141c0d8209103884d0303442e12060308802c1500300c80807d011552009030039655160742ea4160000398003a0b0b60b01900000340c3e944c0400c103010300301c607100084e103040d250700860141c0d0b100750100c4121001c403a80e41040c1005d0350b00181c180d00b0810031500851082d01703250010310108101f8029a5103524086841c556990482200903030000d00c6402c4266214010320390050508401b070301e50800b12054080449110361001409010310782d042103500f01c0145203a1441c01c1828000419010342200e0310390109020384001c40410300d80c0d030396007a052021000c116020040310000d01502c0707598410341c4078004501d51910f00040784c00d5000f4185140320b8041c80c0d10329036001d40340d50709208a42d40031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 994698066 1250 994696816 994696819
    0xc10321015030f0c0c050601050609061207111209040b04091e170415021009081801050c0f070614090603041106041d162c0d0209040602070c050d11060702 68
    0x1101580800c02400e4880e04c0c14901080c0e48000c24050300d840d14515000040e00300601c41c0e0f00034442003125540f00f01c1100d81c4946103035100c40d0980c803010800e445414a800340e107141e501030703a0700d12141c9410523005400c0264040728148038513048813040c40111003035604040d2105c0780ca540c3d4071201038a00d01d421600d1034890746604004a0310b6084110294016030000008007404042c2d002c1a40c0c5c1c10001d5079413148a44204004002140d614000c072407144050440d104581d2032091a0310f607009405440020710b0340010758480f00c4c0c480039020b480d42400c0c010000458000003501409260380819144101c00180c206c61a41e1543c0d161001d1000400004903449002000040303030201c20294040c801a0100484c682c0e981840b1142d007099451274602002000005a0305d45581161040c0005600c0300c91000018085404804501c9030b0700c40c508003a401c00345100070f01c0100030a6a004041140c0121400c05019440d20104141804200c10142421114a40140240c40d00500034002c2c00e20 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 994699316 1250 994698066 994698071
    0x405060609040e0c031e071203091d0a0c02031309020d06050d0b1617060906030f03120405070608070504061110060e06101b080c1032101503 62
    0x144900050a94030f114082d000c0c55007014050071800e05040042c2c1120002e00c0c00e900810b034104502440e43c45003a07109a040e40d5611007210b60034103010301d40700300181252030380d035041c1c44170300325581c058125080e41e890030240d01d0303c0301e140c10480c4040300b500c500101e0b012116400d1482c20707180c03001a412058003101500d58a5400068580d0760740b107081c410500c00c1620100a01c1d040031001e10001c008251b410610040700e040441c95020204510351100b000c5909040a880b0780001c2880c0c00581c58803c0c0040c400050307104c441c1d000b18083c0c6480b80f442102140c40445d100c3c802100d41c0705003030b580721011803c2400f080c40388600544031412014180c4048031185440c1e245000107855040c2d201c0a0713418034103003c0c0b06103418448802c051150a0303050a0641c1c0040b0201c400f40c04801c0310380900724100100d040b04130081c091004801640c02e084c1e01f404105041c0b00003480e41c2d05080f102e1420114039100120298102200440c0300d142078101c1803200910740b050300c00c402c00c581001e003802c05a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 994700566 1250 994699316 994699327
    0x140607020a0b0925060e04050c0313140f2104210615090b04050603060c040b09120114070908070506070f03120518010608030c06040821130c0b0a0c0204050606 70
    0xa188a00c0001c0c07907003101d8901d030412031070b141000e0304502e08542101d00031810042084600d02e234050482c1e8004449004003141c0a5a0f420003101100200140c42844d0007148000375841e080003c0c0c0741078111500d5a540030400355114101038a100d42c0c4600c0700401c10360000860300c07070100a04022058001d050100d0601445088002c529000ba08120a01075481480c000581010312030242d000800b44d00030800342c180126084094012441181d803080303800503440603107880700210010300801c6c840007030080340203100940f6030151003221000c0c0087d81f001000204000000740110031180041c0c8030350320300106a12044210600c105c0141d040c40603411080c0c921261318460300784546c00709400c1c0c00100c02c0b0441d105d03007560010350044507030744e0080c86081011303100072480c160480d40c007030103150f1f0380c0020903405000d403448c0f002c0711092a407000782040100640c11401a804500c40d404a22416480d070415440d00c0c01110308180018042c1e103100d00c0141482c0c0d10041d04440000c01560804 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 994701816 1250 994700566 994700593
    0xc0305040f0e07081f031b080307060506030c010203030f0c30010303020d0201020c100f14091506101e02010b0a270501060519050405120307140607020a0b09 69
    0xa2403a0303205481089000b001c1001c81984040c0c101e80000300020807020301d0203202c060400100c414040905403100507090480c042c404c20290900501035402940d80354155410000b0003410100c405500031b004d0340000c05540d42c07003c0101c078415030144940c6000d54803410348201c02e94110314000350101411081501031401094484c416600345141d0014640d0304602e00203041c42c80300b8020100303582c010f00081c400703500301240007158545d22600001c1c0010460b40c040003d0080d01d206c5a03181281c0f60b0503c2006403002c0384408002004180c0205942c40780c905002c0c44024401c411700010b001a5101c52020603840e0400d03140d89401d100200384c1803a140001112010154052070781540c60080e114540800d400d82615170030b6040004100544c94414003a05c40e01c5001103241d0004400460a81814060426980500405070080d1190100a0207e5540b540503082c140c1b500042c280f40c031007050b03400043e014410300144e405000c4101141c1d480070f02c0c2c1c1d0000707000958507002c0c0d030322251840c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 994703066 1250 994701816 994701839
    0x61912090c090515090c18031903080a150b0405210f07030512131e0915053c0109030f0302070e01060306031e0218010b04050a170604030c030504 64
    0xa0302c2002800540c41c00e2481c80242e5400c1c0680c1114058282402040080c6130b48405440b01c410b0032100750b00c40035488000090502d02055008980d07402060401030625903c44815031048404820400640c0c0c6005075181c52500a40701d840c0031520100300c02c2c0140c1c03c000000070b01c190509040d50f0f5000700200c14441c18101d035074000642da0340c820784040090213400c0050000744c45540d007060749002141c805241001d201c034060680404003032110364501d01c440c00030280040c085090304106919901210440005452064034410400040b0000650755001c101e07410440640744400c0c900802d000c07400d034060303800d0003000d41800004400080480c800743c4040703605910903400303000ca4504046904075003040c1a0404010189001c00c2400011040c400c00c154039140c42204a0414001c0c1c030014803d0104103980958801d4080000160b103405035028000703030383c000c55844020b01e458500c411640d070310307100290f90141d1103031010034042800350104007891402450810315180c3c40c5c0401d0403c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 994704316 1250 994703066 994703069
    0x303030908090306191a0d030c03090b0c0102191106010509060d05010f09121103030f151c290606030901060305060f0108070e06010203071b170105090c061912090c 72
    0x17a4000b9040c00a84110650710602c605881c840d011000e58099a0021070300300c0d0f400680003814002010a03a00c00e043c000c0a65000601c0c00303400c00380d174034139224804901039080034a0540010b8004007a88000c00e0090120480b15003030708004201c20b80c60101000903007040584034541007902d0114110109800b03004040300800c400c4008101c008a6242500700c0d6521101480300700046e4a40801a081000c411a0f8112002c0c0e201e1648544680ba8004600040e8004c21035001440c242d44d1000848001c2c12414a140144040f00558a046141310000c1781d80250860125500d00009006d52410300042e5400070180c200000380f250300c039514280780400685a142074441854010880b40c00100440005480f400781e80c18003d0401c540040d60383d0150b00401001c0d032091044000060600c0c20750342004011081c13a5030000b00c110b0a1207402450706580324115802041d45051a07400c000c400c840c507596454030b81d041c80070780c0e400003200e9061320702102c008003545507000c940120351030b8480c503070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 994705566 1250 994704316 994704331
    0x819031e05010e0c0c030307030b010306050a080d0908031603050d0f02071401060f0302090a0b040915020c1605100f0c0b011413090305031302150409020915070c0303030908090306 79
    0x740650600d004508207020092000307101c0101080081c03100c1e107000c0192500311800f8140030605940090068001e083c890b005a40c019011540009295000207543d072074410694840030b0820351200003240d202c2c41507085480109000318041c40c0001e106000030480c14a00200015898181b0a0f0f0103040c0c3c0c2c844841500c1c1c400c403408a00781c5600c028031501c40140070303540890b004145542c1c00304800c450000c0035240036607500c00314040ca649894200f011181d80c00100040c10901d6210044001d41105105106510565a1322809810000295415540c1c004c0ca04965601e049078211030400003450414100a50081d03010005a442c40c49503029141c500c42d100c1d10034160790b0500a0048112008403d0241000d0548011903002422650002e510722100007407540d01c0d002180b00c2640d41191146102c9000900180c56000c907405020051030484003000c000d03a0141c202c0d110f41c015003501615082e580401000007034002e92007500f6140c070411005040c00015400241015011103004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 994706816 1250 994705566 994705571
    0x207050d03090e0708091507090501080414011d160b0d0e120c0705120604110603091e03090f01051c1a130b010206011e03060209030f0a1202070f030819031e 69
    0x78007980f00b485103092903d6001e0400c0301f01d20300000000c114940e503119440c180803410000c20107000c00c0e01100206100c048000340b0071808040b1001a0000d401c664006c3c1d0f5010b02549184580d107070f100b840c41100d6814040501b408602250f00b80104000580b400a61142c1c19003800102022005022000e59550140a4182c07074102440325048644400c40d8107a04200e04100c0003e0a4a1904a0015084da111612a40c491b01110b241400600040441650308841d800e001274001006144110040e202040c00d1030200006440c0360007424580406808140102201410580c1c030140e4091003940319901c0880000e004150310a151508911410703071590310030708a658040103440d0045c00c0441008030f058a68007504000200700d030000030f0107141c000030701031800e5404110040c042d004081c1640c441101c0d41c601420300c0007501c94000c015000c1c681000580b500d002c2d0800c02180d4100d880c2030301e448013810f00340810414080204044c15501d481d00d0003038002c0c6c64041035001c00c040400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 994708066 1250 994706816 994706821
    0x1f0b04031b05030604061d1f060807030305030711070312020a03030c0207080c0618060c0a140c010c060c0c051006170a020d170903100204170705010207050d03090e0708 74
    0x395948034102600a845054100c50401040c1c40001e04e2640c4180c01c0080054142c03482c2c0c1c406401c8500c00311302c00d401445044041d82603042d03040904c03501d880090600f0041d07103540c0e12540da250403591001078080307141400020300c442e010b00000b0711600c00c3d180990341c005440c2d40d92030110f106c8004142c00180d0044c6c41070030425405100c1c035440e404203070001301006032030140411707541c60f858400540521400301da20212803210110b2501c00140007070035240c07118040c0106d150f8072000c04100396484059560700c003820460110f1468251113060707654039a900066100c94025090a070050010007880303180102c00320384140a656403400b09101c01107005440d0044c0c0075030301c8901031031717103401a04210707a80d40c01031313644403c80c2c0d183c19031022000d0441d12915080a0f017502403003140135010f0061584140c4401d003c1c0e40200155181003141c004004c00104506079581c54a0003070301d000d070780400d070b05004031b10340001c1c1c2018443c0300b484e0000340c40e9224800c0c00c0f0325060a440c4100030400070000d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 994709316 1250 994708066 994708073
    0x92a200d05120a09150e010e03030c0c19080306040e0c10180e39040608190e060a0f0e0307261c091a0405071404020a1202031f0b0403 59
    0x111908180b100c04180492209501c0d00c03170460402c9004030305643d0399040d244070102c40070b40011510503a500140e0313440e07152000c05502c5540c012000d1203c103001e800000340040c00c100400720102e54200c12100c1c1903039100e10501005041c0100e0418803840ba60105200543e2241100200c044165030780c40420000507100c9681105541c0264a86c0703801035040200c415a00d1a5261100d000c40602030700c011117a140d4411605005440d0510542c40081d01082c6240c01100d000c0c01015414000c2e4215100d14080400b220241c44201c7c440d60006008500c5864003038000c00030071005400c00007110b03038001d1545880c1d540445421940080320060351018020300205461442c2d090030685c074500008038812048414101c12046559a912010703a0b090003605098015580e064400e48421418642020380e40ca101074840c2d503120100390081515542040e00903034407000001c0e141c90310b110103802684c1c0e002c2c0d000148844440c070f4401c40c1100c030002002c10181c00070140303030b40f81e0b070307601c50841c00c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 994710566 1250 994709316 994709347
    0x10121a0406140a06080c21060106020f2a04201209010506030114070c0f06060e090f031303060207020f04090b010e06061e070218010609092a200d05 65
    0x43c1a03244040c68408100103802c000f041d82c01640300300710f50140080e088520800e82860119110408034480d51001090341c507000a190b40c41618100c045448240701c0301000215200003161040c02d02d5246003a510250038190400c030031300080011059010350700d01042600980041c603401c03520341050300900010324000e1041e1904240306400034001c8400c1c411204007071840240c15401008882c00c0c0340740031701443d410314412203640b1a40900c2250b0356861481d100c054151400c01e09ca00840c480100321a40010444102d0349a001024584602d50b49901c00250442d91041c0d030401080700100129070790b10720640f078070f02e845148040e50300d504004c51401d901c0d034000d04060003240104160740040c0a11100c1020308550314100d90347e1454184049a030107800c040c6000c204401d03400002c116580c1001030501a207010000c00c212800c00c440070810000031213402800010820000703028003502c01d803c10f0408a4403c4400001d420085522501d01880c10189000242c0c011503e0702201c05420f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 994711816 1250 994710566 994710571
    0x3060806130206030723070201030b01111b0105091201061805060d120c0f0b1506040f0509131704030c290901260a06080610121a040614 60
    0x92020307140800c001214400d003004040e22500d0084000b4903d00e11550180070302c14142d810883c148403004010100542011100724082820030084080304e52040c461008080081001030090111101e010840f8038502214079040140400902d119521403601002103801400000140c0b00d240520003500d00500d07400c1da6105904200502550395101ca4601001c0303a0480450320890314584c0054452802c41c1c20020999104c91a990007800341c4244664442e440341c0b00c030b00c04890a0340d01003000904c04e03401411440d004c003220511075403c001e6481ea80c4003d0341d0545440c100360326124441d01e907044184181e144000040c09008000c00ea1000174014642c00881d954141c200390311141004040120b10140810041a0540c0e1030b0700c12036a0708045541d402c030104006001c1c0101101030041103c0581c095030405000060042c4006101d038403c1c6020311076000118204a040741d845101c03a841a1030303140198850406007049801e155004604c500000039600b41407620522520000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 994713066 1250 994711816 994711829
    0xa03140a0b10061202090109090e0c0306070e0105071b0f0306021305060c0c0f0418080903060c0703081302032a040e010c02122808090106090b10030c2304060306 71
    0x2c1000704003494206940190f8200100d50260301d03507101d00d004036100c10241d48141c82090504042e41c03456000813980d00c0e00c0c480280c00307440156942800030340b014041d01104600080d400c10101010590442081110610702076903019041c1e0345e0f650b00b0000c09402d41041d1102540098050681049100d804c0010103003615941d0802c102c410185072103c2024900314059916602c407a42160f980e0f0b482950244d50844801d806c02c200d0b4144400250041c00380301c0c3c0030b48a9000420814501c0744241d5000795410381c0c50500da99150440924030040d05c4900302e805210b8040d144048800074000300d1022920000ca016080c0321101c1000700391242e06501401a924100e001c600e0590302245041039688803032076256955000d001c1d01605c0200d0a2000d044503419007040ba80c08503804010316020f1407030171000b0320805403035010040c00c40c0c1c0c02d21000c0b0340c01001040c0342010319000707400150302006a03083c90100b5004140350505041d00c640c00440c40c10000090610003c3d415102d518044c190 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 994714316 1250 994713066 994713091
    0xe0307032d090e150303040b250f140c030d030c1e08010b090303070203010204090b09090c0105180f1807170c0409090c0305150f0906160e0a03140a0b 66
    0x4a0740010b40002d140340030b00c600d1581500000784c0c8138408135011610801014003120b40d1a541e5175174035080c6400907110500945c64403940d1045200c20b0000004032903030080240100158265100b0f4011509070880070000c0c000c44030b100980780d5090007841040c0d07016403800b00d02b1991401005101019600c0d160640c00c02001d2042241e0b503008100505540c10040356664803055480000d02d9401039850080d4998000940440c4860050300040c1d00d01c41c0903580c4940c00d44840350301540390060400801e00003842840074050781303c2003e0b884101e090000e45954540c900c0c0b08041441c0d00740040154100c000848144a0310b0383d8403805519988480500340d0240781030520000c5220703c55445180780c0300b610350007040140620090a50700855200d002c031200411003074246980d031241104c850b1003151501c40019202c00010407080c1c800c1040304428080080040001c2d0754558400b5103140e00700c1e000c10b502000003419040001c40d0001d80d032004140b00d0090740383c02415a00e0042c1000c1d115803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 994715566 1250 994714316 994714397
    0x301090c030e0c090c070c030c080c06210703110c1c0f091404060b0a031a0111211c0b040608010b0a1710050a021c020f1c0e030703 58
    0x1c542c034400c0f51002c441001041d122181c040e030290090302c8018207080c0f007841d0000200300c000042801141e00351020b55500700040410094a401503c0d41c902c00008824103581c1814038103d40d85601c1f0300e19040000300b0a40300c03948444150881c0ca407201d129032007600b10249000012520a43c2c03401c1502d40003800c035112603402885e072042d03842080b011900d01c15015a095455807c17800c00b818168a01030340340c1d001d8400040203070407420b0110100d40250301c1c0307140c0503501c52080121001030b404000c0000710b031044844c03010340d04100e00703103c00c05c031040c04000c01c901401c42456040409140c1d0108001620100b044101c41307056119681580c90203036500855250090241d045500203094003484014030844a0b0500f07040360840e14400d80b400e410021111196405403514000c000002682c0c04119103030741b0100d2080c20012640c02406105150100401d076400904981c007031079002c12462440c181c01ea20319000320104a020910000c070015000800ca0039040c00d4281c03070303510002c0c40c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 994716816 1250 994715566 994715591
    0x6040f0204050d02120a3002030f0a11010e0102040f14040c08040f0515012421020c1504032007030209040f03021c050c0f0705060909040312090501020301090c03 71
    0x1241e41c01c000a000d0400480a468002014050003020641100031007d942506055442c0304c0c00014409028003980700c1c01491040e031000042c0c0c0d0002242c0b400b6a803401088900c291000105d0800010082d034032600ca0a049003002e001030001091040d001410b034504050003400700820802c5124091850084500095948110584d82050f082107c1c00c01502190911904007403c50303400416042100c1d00006401e9003c8031903520788884602c0030300442c240d0540c100d42c1e6001c4a4a5444a0003110a4079000240d20b07074008e0040201c0b40c1b0444001403150701e07401d001e072501141e041d80400c8400300c0840e0b41139002c04503141c0403080c0501400c12141164001442c282e0050b0014003103800c04204681003500070440b04018040751071480398601d2208000803d5a400016665854041c2e1032032107600c808002002415074000800c03413030074041d090003403058403d40180258208a42900500c01444182c840c510b255400b5800150342ca6041c14071001c141c9002d0900f540c20940351584011a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 994718066 1250 994716816 994716829
    0xd1805060c0d05090d120f0e0105070b0c09010504090f05090705030a0512090f030f06071d01090e1f030501060e130f0209040201091d04021f02030417030706090b06040f020405 77
    0x85003d050240c0c50780c149002040c1c044400c0e001c001c0070511182c000c1c0081d650002c10880b56a00f90356a02c081c0711445200440321030040007001040041c01320701050100f1104000741a0605d03046c54104d0a00303640e800c580c01038901c2034401e40076a035916001d0260758038050054001a02c820b6005011940b11a42c170907594812022444d0344100300071681c44c60301c0d51369002d00012800014211001e4401082c501602c444003500e040011482c400ca41140c810070f41c4081c02d14030081611440021841d01c5240245d103100104125128198140241d06246030688138401443c0600000203002d0b0030000401c0082e0000b44c8450351141d141249000000d24848d25001c80d1a815039001640c0e44031407005030381210641e0002c104146440c0c6000548c0540e00d03c1c3c2078401c038002c8907014405003114400c00c548040101c44000181c1040009020001e410500f83da03a140407542224600740060b21901c080f606000d408035070011031941406414a4076000705021103800e401e0440c07425161000180720b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 994719316 1250 994718066 994718083
    0x1203040c091a041e1d070618050916080c0415030b0409170d1d120705071d070305152b06020708040f06050708120c0c0d1805060c 57
    0x10140c0c5a03412111401d800244403841c01c00c001d0400d01180c07181c2d2400e094440c41c0b03003546140b84d52414040100c0300c0020134a4403c488070080141c01c0d66824090101c50303202071342415400945007020000381c50303203c0c11030706c0784119145480c0c0700c400300c48060f00810b010030150844100000c2440144542c0715a44021120717140705040006621180c2340104001c0d00c2c00303020140001c610442d41056800200c0001d202c3c4211000c0100301608130400785198000842d840c00003903510040711820700205600c01403030618010710880b02ca0550340c910031042800b0141040020042c220700744816240c150103200d4020311030820403071076039650b800400c400c0da0101850031000350450075090b400d071103804880303800280c02c09030a55403402141040751040c2d1161080640980301d0036000900790380700d80e040d904d0750356018010525001d002162101c601e1070140c41c2440c8880100110102000c00304039030920510252a00c4101c1e60034032240c6420a001d50f417015000e681c080103000c882c54000b150416 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 994720566 1250 994719316 994719329
    0x5070b09030f0303070f200601060e0f0307140f0d080301030f060f09050a23030c01141e010506090105120a050103050c1816050f040801020301090513052e0204171203040c 75
    0x11f080d48017a0400d092801350380c2c4a1194107001d01c00011a2290f404007e06081c84026102c00e00c11a6000f01410343c0c4076824425541049120b1450a04e585030074014400118001801101c1c4541551211010380c4d00030780c81140c0300a40340356002c00b0041103000309500a40030501c10009640d483d00d40c9511845220401441710701014296095039800780c5101c11120308400c1129141c2441c07844141c000e219121000c0c1207000a00c0c00900d00c00d01080307810118601d07020862030141d1900b003d000850300b1030b080c8141402024000106510f401c040700e50310031407500501181c1c0754594107202d810450500c1c4142e009036502a440c0b402c04016202464005010940c01440c03002281400c481b58000e02e0514000558001800281e0001c150040c0d410b8808440040105440720024141c0d4407250250040560700441c4680c501040c5540340f04880a880b003140e22002c1c92480c030350a0881e841a0005a00903a00d14242d5080d48002c000c110f0801950508061442c1401d03242d0030103185032842400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 994721816 1250 994720566 994720577
    0x50a140f0408041505072105070807080f16060c020613030c170f07140105071728060311061809041104060b0903100b010f0e0a0305070b09030f0303070f 67
    0x107800c00030388800b203600030031500c00c841c0400b00340c000008200354000901510700d034078809a00c240502c40d5a015024008117911094a0242d01e66140c001c140c0004005451900c024400745507a48005070040408150400c0302e01445a11072800404981d01c90140d042190b0204007048060042200d10054154040c20219403c0200b49494035039004241e10251142101044205035001d0f88009480d000d882201c0c1c0c41401e43c41c0c0007a4508031081181d0410005207404150351908501c40c41003600b00c0c4008460300129610381e650f0321410b94803170b20031912031541d80e60700304140006030505405440301129070624041103001641d01829036a900d20b481046003102003000c211140000607010320700500180141607a54090721802d4201981050190041024081c42d0000501c20650520707016100c201c40c0301e80c062011907200007a0201190801c5109102102280040140d000140401d07030406a0364400030040c142406048001c5092540c414400c5c00401174000310410222103051900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 994723066 1250 994721816 994721821
    0x1060803031918050d0206010e0c090603040305120c0a090905010b03060603130f031206050f09180304030f050319090b0301090b04020f0d06060807172406030f0a050a140f 75
    0x101c0148100b040310250b000030183d4100c1009000f040e039421002541d000c0e40e031640c1c0c0e141060359815000301d03000314103100c040043e1130941c81d15078041d5170024060701e040342c00d00d59070744011080c0800654030104510408210002c07880d50008045c805000e00103824070555140c9104424640009410144a0100407002540242018030708019440d000740144846501c141000f0704014002c04551411030305004000c69207042240758904104000f419000180d581c0e522210401d046500000105001c200000401305403410030510100d03001d41c000d1591042190b00c4500c0520300c201d192002d22066190810203400c10f0b100360790442c2e40c5400049196240800010000d115100a80c90070700401300b0f510b0080c0365190301005c26501c3c543c5076000142c5800a0945440303507020407103055440f90000040095502030301180184003c0d100c0c1e101d1404201c00056003540045403852042c943c1141007081420381b41c0905138210044142c2000240c01100209505401c02001904a443c00a01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 994724316 1250 994723066 994723111
    0x14010e071a0406090504180c1e090509030a081f0902180a03020a0603020304020d06051503010c0201331d09250e1509010803041a04080a150204091d0f0106080303 71
    0x9000002c140e1061090869a44812105003003100d0003950134402101d464000c903180ac4148034023402108201e0056081c20f507500000c86035040010221140b04a1700b4024000c82c20b4404000001303003400c10005a2034420102000c004203030ba210030b0714819100b840c41080543ca5040002095510510b00543e4943d96400840d02c0540310020003410145402c003000344500740c0c0c1d00e94040c03800d0220001e011550803c02c08901b078440101c45a9418030103d00907120240304c685c01c00202044100c011061240d0b21940745c01415199801940a41504020420140405e201864585203e0501c000011009454030380200141c0d00076160724201c507a01282000080c00c030400510407004115507495a104c11455803250098810a0780c0a000e4003001c40001c0420400d4038107031030f400c500030300c03c401c001d031600c00c18840d00c1c0d88004c0800b98204004100082d1070300461140f040100300c1d40e100011010401450944a081802c1d002e9240a00600003080d000c011a50411303040061200c42e003c5584 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 994725566 1250 994724316 994724351
    0x60321021203070914030105042001031107060b010f1103040611012406200c0f120d0807080c1e09011404031a010e070f0c14010e071a0406090504 64
    0x2180310610301c080100044981d2020012040d1019968207144403900c41040c03609998041d1801410840219102c07081c500d100006404035a80504d40401c40007513800031401190b21a040a0320310b2074450300000344950700425200300400c01c44c034001070604c051640c0b083c0c5034003590040e081040381100044401c201c0c04d400040303051917100d05d510f94529400d40c44400d07866081c0b10350301c00300354030701d403904c1d1050046070141c8081ea60410181c03010300c40d41c008004071180410304044e44802c101c0106815a0410400118000359644580c2c1e101d0038a0f110161201c10018030780721240b8010084200ca120808440310032940c00000703081d8980030010010f0320250b01300c8900000906010400005021041108144108800310b065240743d88600c80d41015100444001000c1500445070a071a00d2113022035110325070040c062911808100c042c09400e584094481c0b50b050381c0104000c0c001041d4880d0420300c01f00020118038941847c00c04060801141c505c20341744a1b40d41c0300e86007400c50701c03402c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 994726816 1250 994725566 994725583
    0x170304050c0906180f0109060603022503020a08070f020a0b0307020c090601050c010213050f040e1216120809010c08010518090a0501050f1902041a070f0501110a020c030106032102 79
    0x142812500d45440f46550545e00700c00d20175549440c0c1020000104d0306e000c0d1080b11202540d14448a5008140b915441c40303800400408504503c6060785000201d20380300c1c003030002e02c0d2140d148140c02c1c1825004000700e03a000c07034021a00d000010014010307040d80002d800c841620041d00c100b0030715952000161554002d6411a8182d54000a03200c0e40d21060741255100755031048994850b0007208070140022941e926110200c162f001070002c1481506030000740034600000d00541e48101e00070343d5800d14442d13001411a011a09040034018102801e002c0d00e07280410a00d00501158904000134020083c4409c40007044604d21010521058052040480d1141c00000a0282e81000401c4100e00c64040f00d140ad0410404018801c2009a0f802100c044425912040440c103005d10900e45003944001d0080728101301e80e4000200081c0203006144114020581d550b80396103200c103000e41020381a0760300d941b01c1d034900003051001552a40c4144410122100c9040074a450500183d2920411 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 994728066 1250 994726816 994726849
    0xa1205090a080d140c030f0f0933071706060f1b0f0f0a0c0b160605090606041805070339061713140109060203010b07170304050c0906 59
    0xd5000d02148468110244204880c90104071315510b5008075016400243c0c1c106000181c00030104003040e81c1032940a800907605015125507000740e110f581020401007280680f0755050001d502c0b106c507034010364950304c804227040142c4101481c80701006080ba000f00201c0c41100040340000000b0407190640e80490300005c01c10290328589501f80365108561505511148909000b030f200310031740800c0341444581e00c02072002c0070780d04000c003100d11500710720300c80c0c1c51010000c05200042403960140502821098024001c44e0078000300b84829100726800800d221228142c01e41c00054000034500e00b165080081e8004c541440c1150841c102110464400f00001e92003802c0000d20006504504540c02030b01c0b0124441d00360b00b03211820540440301007507200c042d0300d002004034500c18090700c220f4500703e00004500e00c0c20b690700812a0000e030041d0183c4030020a607601042041c40040c0ca0103416801d40c0d074210b141545e5a1503803000d0700c1c0e003818080c081c00004070b80c2a40744e25062001c1c0e01d19 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 994729316 1250 994728066 994728083
    0xa0302010f030902130207051e03070609030e03060a050108060615180406050d150506010963141302040b0603070f0906030b030c2812170a1205090a 65
    0x1605c03090401942118900380c03680c2c00352201e02e00140c201c04482d200001140300207103003080e120b915010300a190002c01074003400914001c015040d501170100a105a80761080000e131541001e071454a424030051040d40110706800001c4150b400200585456103000c2c0030b541a1038034004041005400203901c9180c201020110b040100050042c25038005c0a03d41d4040290b50340d40b0004652114461040c1c0c1c480b90b200340000d103900d07444100c2c2d000702c8000540301801e080c4001404406c040310080d440141380070030700c5081007241c1072403050307071200180941043c050309452500c0c0194950015043c10240000d410200046444030b401403420717004004c0000c1c0d01c920380540301170824411108450700082240c03c0100b40b640c060b101d00707610740c0d00c040c00400780340c510b00090011801c01241c44001c2c40c6a04070070070284000382001c0d00040c0c482d801400702a0801032030075500c900210201d034008644240b04d048400c50344107508803d81d4500301004201078a58009050415110300c201038032045 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 994730566 1250 994729316 994729339
    0xb031003060e0304090506010912080703020a0b0115110703030509060304050c36071b0f060903050a0908120f160c0303050903121e091c06060914060a0302010f030902 73
    0x2d202001a0049408840c418825503841c5401100c9840c00c80c014403034461701c002064000b240c0c00381c010341a90340c0b0900480f942c01c2c03400d845113007820070268060414401c11104c841041c0c1d51207012051100742c880014604282103a4014159026040c1458004c0d038002c00040c0501c80100301220b0441030180003680e00e03440080806400031030403c001140c0d80c62044c11072a81c5506048420701c20012aa01c11900341020078900c2d240890f072040946026506190020105d81980301c0c0c40110741c403944440d99901c50107040505280d40d20b40c003459054111705980c88041d0b2440c000c03685840c120b855055610021202059040312100c00040d007a004440310103c1095004002887c0c4480f00303c0031500f0205c0314500c46001c521407840ca07200001800030070074544058030000307480f07a408001d2000d5040180000200c3c1c03500005031046e10703069142c8504000744521071003140c21044481c86980e20300d107004808100824041c1c07000030304004a031000d000c9090710030760260030980e900070070342c2c1c10b8403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 994731816 1250 994730566 994730591
    0x150506061308031312031220030a09020102060906160c021314041b0b0d0506030f060f0403030c14120903090d0606081b09010902030a06030f05030307180605040b03100306 75
    0xd4002d00c80300341c113940340c01c6004105030f441d83c1882140700f40d0660300d00320a520000d98000c05810060510b2000d2840c400304903080742805d402661140314440400140ca2030300780002843d140010b003091101c0d03003082052003501d072820040359800504a08000380d40c1401840440d482e00704004900200707525000d044201901040b1110b03001354011164808002200c0080900d00f8500c0c1c0314035400c40c00308001d101031209454001582c0b081006003580c044001c06113042d0b041240464080080007403410402c8109501846001c1400903545010035100c0015021aa200d11519001410b202030810004014141c20030880310010302c064620b907580d120901d00030014000d140203080b0140070300d911600c421041641e4403000c21030010640500c40e464007004030000c0d84050103900c841e80d11501d000c40800c60747e580103108984610011507491600329070041910040d03100c0100c0c15441003804100c1e055000381914207583da0344136180c0c1c0c0e0740c40340c01613414080e816500c02000d85007000c2c00d032a44c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 994733066 1250 994731816 994731823
    0xf1b090a0909020907110c0d08091f1b080306010e03100c0e031002031302010c11030109140606100527030a050d1d0109170c09100807080109150506061308 68
    0x742e61083c0c0e81c226140d12581015070b101281c07402e844000d54800841402d040ca440c2a4141c4041e0040801d0346c901481540071958418408046041181541030740366403003540040c001850f1884000b43c1c4034561041e503a03525051202402450401c040219001c44940e0300703001e0803004291080041129241d03440c00540a030b0b00c0320990324424020320901000760701c020b000301c0703105441035010003160849e00c2c1d006645424000c0d9058a440f00200103901c880d403003d101d075072031301400b501a801d484982c41d0f920780d2030002d0081601c0c3c09606640390207000d03107410406680e662400100c04a100144c00c01510324090b010341403daa040c41a1400e09040c860007048412001800381d85036039081030b05401014204c1c01d41c0c2c070840d0010300880070400401200c001400d100c1c401a00c15902048072220000f1603400040e07404a13042e20382e18100704a0000200051402490b03044024015180207807203000600d11034640f05007a03161102d0001e0865903410003290000b5034070051101c50903031151019941c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 994734316 1250 994733066 994733081
    0x315020d150501020c010215220606180b0d0c053c1822170a20011107080d0e0d0c05190819090815041a0f1b090a09 51
    0xd03005c0d6a841c0c1764994400b0900a18218003010302003030316140c0c103420303890100644604003008011150b1076400246107006090007883c09802000c0410500106902203c514058081c0708420003044c20f00040c10300e0703400030100d8408075104040a158042004925030940e0098085240841d54070310200e0000240004582c1003641c42d10f150203032031103161440a10540b10000380303200c855070102000c590b209811090b41e2003411002c03940e030b00a1580c800103800040e01035000c1603800304c52114000700c50700a000003440c540d009001e40310f8840c44140003485514800341641400045440b800c3c5203680110004540f01000c03a00800556080100010ba602008035054051810307543c0a088490074005500d9411100141c90018403010810382488040c1c442814098140000181404c0522002950250041d004120f170702d01840c1c040016100e44050b5000d1160201c2400381c00b075120184268400c140300302020505090032040e10b2a40115007505600801400340032548a0007a002044c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 994735566 1250 994734316 994734319
    0x82407030b0a12150b0d0512130e0c031b031b0c010b060a080a0524090a061a04060e0d1a280c11010e03160c05091e0c0c06010315020d1505 61
    0xc28810351100b0010201039281b0098815401030300c00000907a9803500410140c98200b0403500c04c659144c0030032541e4201280c80341000f800110802103064090010041401d075500c07581844c52a00c0c1c80401c1c502d80b60440d102d140385a002c2101c6a20140947c02001d1000005110030f0b01e405101d00c005282c20401c1303030000b000b1814070000c1070001c401d00c2c44106c101e070a1380c4251010002200280b00940701c2c000c0040a0103904c1d510b00040f5000d0100c030700511000301d44403131680d8034140540507241a4421107081c0c024120382c0442004035101c00c1006041c0c0031001c40090558030f54030180e09200042c0188011024200c40d035680020040c3c3c0d200501030f001e1a02d5040707500300004640c0c0e0880304402c00011080d0420408108158542c86a81c0300d0544a0740c003001360203841308003083c540d440c12916400c10411080392610f8080d0302d903810b540c1c014009000f280c80d080100014a45551041c40010700b104410340440c44000115010340b12030256582040046449442001104a01910071709 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 994736816 1250 994735566 994735571
    0x2f0f030318060f0406020313020d0506100501080f0402010c051f0603110402030618070201290405010e1902030a0219020a0c090212010b0f0919082407030b0a1215 71
    0x40603901c01003091440340328440c1d0b045445698588444021b03520040c80b00c2500ea110b100c0280c010303541d031040341d822540900e000786064500507115030402011500540d040c8000b0700c0030401d0075640114240d602c142d0a18104030180c4461428510b8500001d0600111040e4101d10601104450303000708101e03400758085802c54099003050104a1009440705a000340c000c664141141d11030b8642e880d0800e1441c8000500b84405040c561101403400842c503483c40740d070000e641c020346441e010700e902400c107500e2481607900f060701603a152400c210820024050b00880003844001040d8141c40803443d130310412f171810140f9044025259801c9103812130707a40135100408a100e07000c42c429904511954504401d0070b0b42440caa448135a0080034225050f40810001d56110343c07182d0100d6180d05847c030380c5004089007022003160506415031100480d0140c0e00004021109019401b41c0d04240542070018000d400031000c01c0d03502c030054100010706600310f2080c000b04604801144504403254404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 994738066 1250 994736816 994736851
    0x20303091203040f0b3a0b01050c2401080106050d110f090a0e070e010b07020613050a030c090e0a030507200306070203090301060801020901080105060d2004080f0109032f0f0303 78
    0x1070062081ba404224503402410f04101003458100c0d44074411000c4141003a9090003070100301c0504d0f051588200401411101d205200b100424003005030140c03101000910000d8100400720301404160480070b0003200883c2e40141d0070f40c0310a004200c265001828820407442c000f07855002507c03840304241194401c2c0c040000d210050030200c0d505891304101550301c3c001540d020400203400c815686d4083c00c284100005180c0d6914076040025481404a0041c891030001c014040740d2920b000d49085401003220140080e82c02400ca900940c0e01030038078203614600098215087c40040366454043c80303407a09000001740c00101410700d10008030001e000050700c03a048142030f8054000d003203001c20139010044c400c51030008094503407241820700000f0600902da5082d01c000c412081c001d8030b00f650024051000c800248102e0304075400d80c800038480344500795402085650005040c090110200b4944029600c0b180c80020b8941c1400d41150503001012216a0702d80d407090300c5401200e22444007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 994739316 1250 994738066 994738117
    0x403030902130c0243050312070c0b0c0f150a1d060a020c10020403111815040c02010e030c0606010207050d0309050405040807050a240207020303091203040f0b 70
    0x40c3c0250204180c2c05030006008100300244056071607442c10001001501c003d510141401d5041d0340758500e00d10084001d02c4c50304c010b040c2898405071100c904020704200d18800b1400d1101910100d51014070400e40e510001c41c40b45043c01c0b40c81e410f49841e40107840b14091040d45507107480e4000c86400d0410009039121450307110b214805141c3d01c0c0801d400401c0011650b80090f405004000000e0046d00d00d0b00100100060413a03010760402c450300c00c141c0340c0540280c00d001074041e1039400384805038031860500c0400965124400ac4103544540e4640c40e011512502c01e4000e2080e010015046a444080c038217505601e42204658107030041c0b00d0120002464501401c4014456070580c586130004d80c1040d0920010b0a0010402d66108804028a40008808010400d121400b40441050304904a91001a000c0e11903c805440c41d0041c0007000c0540c1d404411900c048030103c0340003802907040c0c0507a81c2503025560102c600320102040c0081d480700100c0090280805405501400250358031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 994740566 1250 994739316 994739321
    0x1170c09060706060e0f060a0803390a05030a0e0d0f0f050325060c020102030705041203140c06090606122503051608010c1d100c060609090309090c051c090803040303090213 76
    0x41c04bc03143c40f80074460b124034103081d03200b11846a8140011042c0e200b01d104500ca01c1c00300034140c00c9501d5800065040d11060748080d15071503000046a0f400d400400c00c1e1540020fa445045000e041112401d4113041081810000c8504442c1030a071902081c0c00650004640340c07003400002e9490350304000041074143d1040c400c403031041880f0348896081c142001d1038556180307a0f2510803001d00c01c5814601c038603061494040c0c03d6841c0004020059841d20280e150b0810401510032402841140301c8134007a40d40100d001c800307914049902102e8030640c5c190603120345680380e201400ca402240e0101c0c079400011a07500c42990603510092111001101e0200c441d615100f00ca400c545220b400041c410b85001c04004900c0441490074451228058860804644280d40044881981d640b500000c150304081c1c00b000130010001c040141c0c2c51240406081441100326240000c5241816040d03100520f900c0464800e4004541a40f40c0c90b2504d4050014240c001c0c00740d2007005c4010004000034401d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 994741816 1250 994740566 994740577
    0x31406060f161509060b010e100909200c0304150e060306010e130518100504110118030804080d09121109090106051e01170c09060706060e0f060a0803 66
    0x580169151071014140c1c0400e10100860407107020050843d14642468540100340429004000000d103508001d8005005000380081e060302606584544400483c0c100e6210400c40c0c148020120b0384400c248041c0d03c0c1e0042110010190a03c04202c2d50080340c000000fa1042e00d642100344d0a030803501d038070180d0b03140100101c21030340481c003080042d501d548201c0d45402480800307042611014007080801040c0c65040307070101ea003603c030104550340006040203900100b41d4030714403c020340e080a0301c8880000900030025070600045400d0303c001e4007102c0a030f001c015038104114940313468668540355150407800c0365540004d00104004513484a00303a08444023903a2081681058090b00d20034400d08020081240c40107540e54100080c041d25560044901d40c004085000540300c1e0b00702c000b500c1001c07485181407140c1108802c105d003a6250038101c4078a0641107640f01c0d100d0043d4a0904003400d1b1680043c00d584c58400700b440380c2140701d00d52280c05a081142d101032413a88900415a580c002c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 994743066 1250 994741816 994741837
    0x718030f03200a0f0303090206070f0c06110a0f0203070f031506060f0e040c11031818010e010b0903031b030a0e040b01050f031005040606020f060105010f2708010c03140606 76
    0x200007040040d52840300e400b20300780705e401e01051409150300003070b0403034008507000c0d06c45c4052244000100003038039a101c800782809080c0240c1042a8510780da039121060789000304079001d0b0860210555030200000001050760a40140316581c403485c00a007240b0824031803a90090a1000c082503090240d0f442c009404516500d5120000f04c540812000e004800c4018041c4101c03500341c0400864148010440551217980316a40300c041b90052107614044046452030030042c803c010703c01c0d841c004811604603415070381c40f10346403641280043e00714806c0011407204031035101182d01e141a004006081c0d076400c152100c921030f248400c140030580e42d2101ca20350000d8410042c4504031a0440091500300804e91045200c694962010034100c031041d4200d400580d01101001c01403503000c010181c0900001c0c641680344501c2894060008491102000480203060200d4008000075038804401030003450b00920812407011f41c00350040881c0041c030003e800300791000070f01034108501158100d000c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 994744316 1250 994743066 994743073
    0x3110609430b040317040311090403051909050f0103050408091e031002070209010f030b0c0d020717030a0609060821040801020f030f01050405060d030302030718030f0320 75
    0x20800c0d1603190411900e9440141540444203448600ca070700c00400340500074201e01541e41d03d05509110011181042007589522001c1006100041c1410b0b0740b200c118505690381c00c01c54680385419500e600980020440000000e814103900d140d20144100449409403048111441c01000460544008031000741144004205220b042d0400f4012801c000c0e801c003041c3c0c07200400010000303080005039900c4404a9030003041203000d5140074443c0703c1c014400c04002d100c1c080d05c4c50f82c1c4d280a851004040002c0306134003140d03c0d008421940c044030391145e48171000c41413441c015120600103403c15118886002d14003000850354010b207106450588100d08003c1400000c1b8402d000d0040c403050710b208001c00018040010780000c240054100031000710a0541c4a20380b26a024030388200c164003a42c410360500040c0070b41c82e100d4000540c482501481e000d40c0d01d951b0701805507040190507404042d90885003070b000042c40300001e80d01d00054800c3d510080c80141c48200041403800301790320940740c3d41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 994745566 1250 994744316 994744363
    0x90604031e02150a0c0e01020d021002031321020607020109020906090603030f030f01061b20031c03020c070501030621030329010909020a2f0a03110609 67
    0x1009165007001d00554411220307051410600c200641000f5200e140340d40c0c0d210784601d44040c4c0c0140600820790001c2c8001d02c16002c4d1980001c1d62048050140007032103a0000106140008400441d80040d8102941308140305034203450410182c000034480340107006040114281302c0c8107008050050390014110161a01c42c41c0801c1540100a00741e10391500c8100110401c500c64400514410100c80d40500300c035614004020342905400408500f44403182c01640d000654410b4409070703041d550220306564022074a0110f031424445408194036a9502c11490802560640041032000e281d102a42c074002c0c1d403900150700fa40c001d8042c0683c0d002e800d204540e410340803803542d1059140070b85008503031120820020103400403000280b01d00c022017014290300950300010308000500107141c0851030210f01500080000000c1d2078204800901c01c0d07000001682c01d2a080000410f071101681d10f200100d24001d0b02d854000f81401c1580e001e000c3c002185841e01189400004c100840c103200d046c1c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 994746816 1250 994745566 994745597
    0x30c0601051905090c07050a051b04200304050f16091a01090302011b06050408091e060f0a03060b0f03010512060601020a0201030f090b01091a04061809080412060c030509060403 78
    0x903140100031105e581002c2c060341c00441d1040041407403c1b03015802800c206400340c02102a1076100c9000e2900650030490100c0d00c240711640d91394900401003d1031500c90f162441c0060810042d140000c03103500c64915100450300c1c0e44801c2e4011502a440d007007000910279100c0c0f110200c000e05c000350100300c0180c0c0404c01355010b8440500309031214801c10a160b0015500d4030111003060b141902d5260001c1102009800c01e02400700012141c202a10201e0720400c3c00600e0520960040c8042c071140810888074860198018401920307800155a440d180041d0303400c8943e0b0024490381e4030800c1030210f1040c0089011402e11701584041e80a0401c07000710742c00540c085c280b07052582e000c0c19502c04c41e10340403400317226450b406880c044402140707084800042001015461403411721503890304404200741c1c03602e0702d0000c1c00d10445400c08105400c2e02c0c01c018000b40140d5011003050f8100044200070000d01d40d00000000005440800c0503031103181c011a070300c020842c3c008021030048240000403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 994748066 1250 994746816 994746829
    0x121a0d0c0f03050d030f0b0d24020414032b05071104021b0c010f0203031618030f17090d11040f02120a050903070c1e17030c0601051905 60
    0x1140581904a981030351601410340e100700d954400c0c0c5081d00003141c0380c0544d40d0f05010f8182c1900a090081c0004241c140000d400340e0a030080003051410400804520340c0400c43c12400440a500411515a03075250521801e400000c0ea06500c80d0080710075000604a20031401182c4290f8661200d190304a0380c00b0558440c0d002e0071302600e241e8200c6403889256a55400101203404030300018407003c1e0702c51164a81f40003403804e80d0320305001c1c00d07007035210200d68000141c90340283d0101c02c11414003810b10094946000000848145c1282c0050100c18401080320554016101c1c0c0080e0261100c0c400c207103201ea000b80000254400340c1d400d607a0000c0303511055002c05258004100298141c008514441242e10041c0180c89680e00d0408001a641c0103114480c0c2c80711181002d1340c64441c150741c40480d64180c2c1e00a2050084900800d6214603c00904030b03c090100714800d0300e4007031111403c05541c1d8101c10072552291160500104071400d1483c01030105140c0250f00861144c10041007160 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 994749316 1250 994748066 994748089
    0x14060a050a03020a18090903140406020c062203080c06091c03090c09181407062111030a0203040506070e010e01120b19081203070207151101090c0501121a 68
    0x108032001645c01c0c081e003d0540110024103007100009161003051070301038200704c0700114880050005100402c5025004118210048002c1300c240b40d031004036110191180070385128007100c8800441010041000800007881d00c95951000c031041c594904e00e0b07071070b075a1841040464658090810300008140207800101a81d4841d0b10030b510401e4031000c020084a56140d000300d00300340c82540700d8040c0070301c0981d030903594009440606a1070342046e00217402c2410019544c211512851140c00f92110b0380c2d4090401c0c0d00b100b00c082c40d6039050413142240603400543e01500d07180900008036107168002c0a000b0b0340d550042c2c681f6030001c40ca08005441c8440701740b08009080346c5405001203283c1d00d640014444d03c51101c1d405010300c0c140f0340d100d454074690004d0011844c108100b070001443e00010f80c0c40c1140e02c0400e0200c443c0448000c1103030504030590f080446e40d802c10500c00304010305820f01e8016914281d9400b00f2650001011005503441c111420f039613041c5260000312642008041c0c00da = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 994750566 1250 994749316 994749337
    0x41202090a091a010f060302090d0b100b030106050a0306050906090f07020c0a1d0601050a3c1d0d151a130b03070e150d140d030614060a050a0302 64
    0x141c0301401c0e40303c0c0c0180b6140165048051018240140031603100b801803c0d000e00304601d011400c107004900030a441d51650304000c0d04040364030b40000d40303181102c6061000b03081d003080390319241c0d60760707003005010341e0859688000401d0900f607010a0500f00203524510496001301000b0054580c01c503500d140b464041c0120007103020300d0204020503210134800000402421900e06458840c4001e00c10090502801e00c504200c02088034072801a841003003940800e03540780000c0790301a000144098003408610850745858503034050007000359000f08400007103016618071110082d80700001c002d540303100d400b0000d00c140c1e6141d25564400840741d0244100e0390900102504100425000036107280c94619052100364a81101d41c0e81ea08060101e00c0003404030b10f00003003080c00c180c0c10050084c3c00c4140351070700808c0490700c7e007002c1c0660313160380c440c40da034140e011b65514a20b007017401409040789018480e0002c114400808035814080308a0361102008e503a034500700409080e04030301a41c40150701c0e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 994751816 1250 994750566 994750571
    0x90e0c09130c180f051e01021b0d0c0626130807020a0b04081c090b09130f0213030b090a0201020c101211030708090a0c0506090103090812011a041202090a 68
    0x34800f20480b000e000b0081c20012540c04102403030581040031000000560121200f049028100280d0f0000340c05580c07400741c0841070041540d06004644c0c03400111401a003c074030401c50000ea010b4024100c0c04180c80d54110700915400ea601d4505030000b41683c115580d55030310000d900105401e207015002e42840140749007810b5560340c9009102c1c1c1c1090b0800300d41900850440c04c6d0321040d0a60b1b02d101c035001424000ea80720702c0c1c840382010900801c0ca801e401352010352014010550103500c810079000709810219100c1d10120007110b040505408102e403540c00c0c1d000411945800068070f852a594141e00900a40d81e140d0700303102107402000c981c44240260f402c4100801a81c038013802c014440c41284541c0c4030306c0c02520082c03012340c000c0d00101d505c1d0030001c40328002c91100042c02c0203640303041c0e864503551400780c40104c006058004000e000d000c40407500c112030212103201d46040350103a441e42c2e08041354400070700e0b206106512540b0601c0f01600104001400d06165141d071044907000c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 994753066 1250 994751816 994751837
    0x60411041e0504050c03070801110f0c0c030106031b08011103040215070f030f17040510050603031c1401050a08101d0d091e0b160c08030a090e0c09130c 67
    0x12102982d4058400b1900d581244407000c1d500d00b010820340c802011541e00030f0000b42d0040d00400a507100e4800c1281c201c0000007003000c40c061042280500c05070001e002040225900c1c200b001745842d13581103005c44440302d00000144200140900c02c5440c425216141c5117458036400c2107082d00407240701220341d032002d0100d0b8001c1383d0710081007002c050180d1a1000d14000840d001004450342c82c0d00ea89008141e8014000031420000f0000190103403243c001400e6294080045d1179800760301c488070107802e82601051504561a0030401108100051900035a41c0b96820480007191500886005902c000e41d6011a01015005001c0191000c07807981c164690001d03075181810100c241c00300c0842c00c209000c0120101c0c8031801d01c400316a03082c03c00c400c0350030801513410b14824080110049402e419804050100c0002e050004200010440e581c030580a840600328180034460060384251020000f0300d000f1f8075038120340726076500410036103000155616044c000c0001c01e0a140400c00071106 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 994754316 1250 994753066 994753121
    0x120201180f03050d05030903070b0a06050310020c07090b030a0305071b1d0a11070b180307150f090c150908010204060c2f010c2901030201030c0206041104 68
    0xc2002030101c400c0c00c203103618154105945400c0d0b09803020301c100042001042124280071081e20f1507594802c404403c076860b0350702c1000c0074002c00d4111a0b0305014184104c1940d0b0100d070b00404100c00950240e5002658890352181120b10b201d5a5070b0b0107402c0031403000c0c0002e100c0c000601e15284500d44480b6941301c601425000b1803544e4000e04220703420000308085804045400070390007000b440c000d00c0301d01e11410f0211070b14000c0c104003d000c0c0510714007007040d50199401c0c2c013000d4000c0200302e85cac582d56182442c814041041940500e00b40c58082c7e6440281c009005059515401c1608030250714902101d49503104540c2d460078080212465000c41c041c4800c0c00280018402551403010441c914141074900740d8004802c040e180000c03043c4050407606e2059a19095a002d0030213400c1c1000b0740c00c3c20040190028424030880c141501d0000b03411448045060682c0d000380d804001b041301900c4141e9441c2d40680d030140c446a401c410a103001d00e055048a45042100d8845400785c0c980204e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 994755566 1250 994754316 994754357
    0x8040b0a03091b0f0b0d1b03050f090303010303090e0a09020a030302010b1503090c0402070213020c06011715180102040519090e0706080402041a12160603020c0304120201 75
    0x106400000303441c2c1861030305021074480c142c0243c0e00140d00841c1d807280342c406001c2c03c406140c0f003aa902c01001049000d00d140099000b4418841c0314400030300c1030024408002c00034582120248071010300720000c50060680001624184c0e40e054460804250800280301d5411400038944111141c076004c1030001a21030700d00040c000c500c69000840c4990140c020450424a40c2c0c00941c98418180f0400c01c280a00041c00700300744100740c0d0010fa80300410b001169140455204c2001c4503800003415520310f500000d841130407555400020030105500303154103500c540b4144450304000480c0c402051014900703803034040903059000001460550342d9004036001001d070070751080920b0103045e010040c9901d180500c600764031049025001c89424048080c00ca03000190007e8020b40d900d5884148094803030480804e405d200400361032580b1900311600b96036071420403108041e0184d00f1800034440e03000340241c0b41d12203854005542441c0c10001d1081444a01c01016410800e1040c1b00341c5a158041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 994756816 1250 994755566 994755577
    0x5101a031005030a030f0e0d1502030405030702150309060105060901121e0c0e040b010f08070c02010c0f110f04331d0103050706141b0f030408010e0f010c0f0c08040b 73
    0xe4480c450400c3c0c6c03007100a803424503600710300c5000d1842020410006401804112481500300000507125196810f195296000380400250040101c1810703800d807016080255100744500c030215861aa00c942c240144c0b8028291800d000c100e40c40001180c846554000c150300f02c0390070b10b4821700d6a211900340400e072070302c0c0300610000c1003400d0200780d8a030809024000b001c980a0a00c1c902d145002c20004001410040a0038100071144c00c4110441e0700c64150000d0f40b03a00300c4400d6020112604101d031030b1048001c0d860b445441e154208116900742030240f0502e0b4000305c1e00020209010820003450032510101c1d408449400c1074021a804000d09200e0b4002e8120000c107616643c1986003c41ca804034641101c000e006100d030301c621030042d03454101e0341c0ca680141e60708140c5c00c10710624146054011082040a40404103010903180e205502c040d651030000000c9421821910201d64201c0d142d8801c1e00c00050341242d02140c1890190000101451007076420030301d403c1d41c400742107849402c507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 994758066 1250 994756816 994756823
    0x509040504020f19060e0307080d050f09040204180c170a09050a081914030912070809090103061a0f03060114010c0506010e07031406010c0201030b0102010204050a0b0d05101a031005030a 82
    0x41180500505a03c9005041b01a01c00d0300209507a9040424080e03851000c80068000c2080011314080204409030a45010a00c0074109544940c0c5400b2280014132130072040202091400320300d002c00d6442012600300d03101d100702c60340100b5114150603101a01c0d085a042e51140300310fa440b400080c02500c01040030020200c94403145d008d0000b40200501e2400c01410760f04071051007406000000030409066403100b070440b46580f0426460000110302507480c109034041000300c000001d12419820000c030f00071001e5189801c0e1081c4508014000740d0200381d441e0180e004400505c000503003148c04c200e440740e0505015800070031540d0740034a4140300360403078001544008140040250107009010b10020285880c103558035004c00024201c00b1110400ba04140e01d03840d0001e1164000c0d030403030b006408040c00c58140385480d407809040c00c0d442007514440c0c0625200c001401951030801d0388043e40c884000300074094521030303100d00640d08003400700d20340658020b1000500b80d500b0801520014031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 994759316 1250 994758066 994758109
    0x8060415062f0c1c050705100c061505041803081605070506071112070f3507020f060a080c090f041e06050907051b070f12150209010509040504020f 65
    0xd18402c0c814511144642c030f4946400f06003084c40001c90110b40c1034280c0701d045c2d980070f155003146a01102c40640c540400f606c00b030318004040d085002c2460300c2001f9601c041c0c4040c00b40710309d60581c440005d4031074040600002d041384003240000c5d12902110386011850b290072410040562511400c00d0380980d1a02c020400c2c00052602c0008140061054001c11156881c20701d20b40b500d6003414030320811030043c125055811840e02203901c1440100030042d8007490105403a080d100280c104e41c3c00420140e20903000c2072540c00262401400f118070759a40c42e41c138000c1da5160700c2c102203447c0d0000703802994009015540381c241c0e521540b05d0040e006240780c03a440707020480400804101e4249801c0680901075001c1082409038003c011a680401d000d070350120410303041d14043d818080e4941100b661052035480015804e0f03201c2d11810a8a8024032040c0080080c110321081280700314054580031a90138400d090541c90944c0c8450381c042c4c00a03082ca5280200d0500240074901c01c50001e03106c044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 994760566 1250 994759316 994759333
    0x204060f02070b0f07020d0219170c0a060f0c06090501050703021b0a02010906050a051918080f1b030a150e1005040807020904020d1a040308060415062f 67
    0x80d41081a94000c1400f041c12034a0f10600f0b0114244a20032120041c1c022205556004215281c1c4104101c100320f001c0111040103450320382940071070540d94504001413040700c1c0542c0c0c0c50718001038900221070300b6448200c4a20300e03d440990304000e030b07e54140c0e82c941d80c600d4076501142e800c1c0210fa12030a283d550069403164419a407819002e0182d6081883e83c0c00340584100503600840c00c00300355905802c04c0e5849840c81141104c981c842c0000c84010070605002c12400d4940003020310005100a00054152540b2408015500c016000610610394030010700070003403020702055043d4180d000740139219901c4254680650342e400c85005010916030b1401210700c11401404a02070481d2021424081c900b017a8030b81b01e0b160f00560102070302c941103001c0403070b04568030030003810a070a0f48100c2805c901548000c860300540d008950582c003081185000070343c2c80c5131910800d4440c110940e00320f108541050310484991058240501d4040000c46038024052030b0070445422080303801d40284000b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 994761816 1250 994760566 994760597
    0x911090a090c02061f09020d091a041e0606080f0610050402090a030209061804080a170405061305160b180a0f18091a061021051504020406 61
    0x38503250710403107000340340285010201da804a10b40d50407000c0c2c403042ca03021002a08400d8500c1c0c01c0ca81c403407011144005840085812a40c0045a0a0307009007540c20740d00e064251802040041120014061003411040d818000728071101e000110b40105000642541c6520300d482c907248482540740581e0b44514100000710701001a0240a888151020740c00c007050500803680500084c00020b1098140d900004d0303554076283c4000302c1c460002800c20700a17003418113202c18a644031a4001d000500141c1d401c0b102c5000300c524031030213250300800802180d99021010103045400142c119454043c04460742e1043c84200000409400c00564280c2da4105e60310b00078040d151805100c500502946000304401105800360070103c0300e40c66000500340e05010b407008002d04400e44010081121820b64407161020001682d1144d0802d542043c580b0003018000d0750400480d00c1c00741d008140114181d0254180d541203507800a50405050000000340000101640c005805c000001484a552000360303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 994763066 1250 994761816 994761829
    0x270806060f030d09060e0316320f0409021906210501050307061107080d21090b0c28081006110304030611070204090605060102070506030f01060c0804091109 69
    0x28510480040c010065400f2015150a26503c40c5206002c160301c04603007103860901101002c2c00303184d80ca00d458151201d07010344010344030ba0780803a6003240b004180c1d80c01c2c445040c1a0b080100000306903010001682d420440070340b803441c00c102c0e0045100306001080428500003440a80300c02d40f540c452200c18034003846540100700c400240c515051400410503524081268815101d40346030010000c0354408040307103081001e80c80282e151289008619940d0351002c40203034404155896501c407414903050500507a2940b040c06091410190042024a92090020b241c0301294046202100e0441a0046086000f08503101c01150643c0f007003010074002000d0110180109050070350000240c80030196a0340154007006000c0d65492550a040311003410645245950081041c0f060042c903280c04000b800c0150380319405446030342c102042d10302c0c0010681b8411400740c0100d1845a00c0c118040310441600c04040d19006000c00c0082075408050280141c1d40000480c0780d942d0b0200c20090100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 994764316 1250 994763066 994763089
    0xb10020115060c05160b03061201090201020718060f091b02070e0f0c120a0b0405090703030c060b06090d1406010b04030305030f1503010c0e090f090d27080606 70
    0x11a45004000707805100245290001d07030310245000303c8200341e030345042458440801882240d03288007a900207007050051005521a040c1074901005074221019407d003a56044c5000070f01617086640103104d54140070040380c0d0360700c01410001c1000755032042d41140504040e0400c1d0246500e801c40900c0303240068080018200c56440144006898020200c56052000d048200c440b0001c50104042401d404160768440c0c031040440c1c896800c1940c8803100402002d0314250140341800001840d0340b9005c40c00c98207d0b5059211400c041c0259917501005000c001616a80080c0a10903c6026110203414050803803080b000303c1040000000ba151600e00168089011039404110a100095001003525003000c203102d181502a16904034101c10800e280d84101c0d010b40c40c01c0849c6142c06d52190509031490f10980b03100500f0740322008030b4074070000b0885420503a0742c0044c40060500344584000e0f1801c0d1207040883c841d215981c48144001070305070744003541540c0494140442850225450740 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 994765566 1250 994764316 994764349
    0xa06050604030533011d090f1f020c01060e0f0f06010e010f020708060c0a03051311011218140d031e0e0c06030a0c020f0d12180c03060b 60
    0x50406296589076076a44005500700034140840c140130440f5004441d90907440100ba8480c074091541e169030520283c1c101d1070304080c0d04102410089490b5403000b1624690110400020b8480ca1518260440a0039285d03d4920610b541c01c100354007050f8004c1c0720390340103000d404640c0c20003410065411120641e000d00f210300c002041200b4441c890f03810020a204a01c821f017031554062006820503802d0058981c090442805071000f00b05003525000001c0c240d04041e0340781040300361682d00c10742a01e0b04414400504040036210355162660007540032145020fa41500030554010004898081c004d244104403007030301500b001c1408404081c4200042d5a0301c81c50104040c6495844864039103040710b0048003080d940301109404000c2c2400a20075500001d00240e43d2428518070040052640c0e204060050007182c0340301d08045408265402401020307622600c001c1c0d5990804801045450302c51740030341284400140024000421200055014aa0000341d90107440103010304401e6000c0001c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 994766816 1250 994765566 994765579
    0x18050d050a020712061409030910020c09011e121110030c0903020f04060e040c030b0610090e0a0f0c0f02010c05091e011b060e0d08010b0d050c1902060a0605 69
    0xa49641e5400a041d004603039003995080340aa6103820b0141c0100500c0b030305100c0010100042050307021000005020028050740c00c201030700302d400c1c0120b8451003501e8149030b00214450040144030300f004040d00743c42010903940c20030f1300d50f00d40c0c0c0c0b8418032001080880d04a00d40600c1c00380300b85010500205c002c1994113003404101c0b810f410003041803049002c000e220300e9032041c0291198680d6804040501b00c8100b91558609150070182c44580040c44111201c0046800145480c10610310441c03030703416140ca980000714102540c03490991402455002c01c00d0b96030503140350010850084c0100c80c1850f445000f5054452900203003564210003460007070010801c9558141c0d100c6941c4043c0321b141c68000c6090a80050780101c40c0c0641e401441c542c950b00c0f80c0315010a21034182e21000f0f000414600720340980310703040c2040d181e50809204221051401740540d400781c00c0d80d40c1005030b01a5101201c1441d0080340800c0300180c2110b8004000140d0041081051030035540c404c150140400329000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 994768066 1250 994766816 994766827
    0xb0a020307050714030f0d06090f0e03070b0403030b090c1801080115080925060801051008010e090a02040518061b0a0516020a18240b09010504030618050d05 69
    0x98100e10941000402500b0b000444c0c000b161410b105469250b0320f82401c141d40c6440d00400d00300500018060842c48038075114201c209018140314401120510f10301a604028540d11030000000300107000740c007031680b12000f83c421075481410f514410815400441e8a80c01009143d0790044c410421060600441310018016850340022103002103a99140600741c41c1d480c0c094060500100c0622030000d004462150010718085900e00c800b83c5600781e80300c0b49280e0f80c810820800e5606401d8207008119084010f0200141c0a408550300c40e407400200c9180401580c089421039104440390b03280f8103c408500801040c3c2840440c0d0001500800010b00300590300c10300001740310b02c0700b030541401800604511030081410300c006883d90020913002c0f40355035034050010385441030b410006d58245009600403004500c40d030f11001705180c1e03506d003901207030600b0090a22a070103045602c1c1400030611000002400900400100c42c400a42200018040c2d2070a140f4111900c83c0d4501445018000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 994769316 1250 994768066 994768081
    0x906050a0515190503010207060606021903120c110a0c210506070315080f0307030e01031506030c020307050102130e10060f080c040b130302121b040e16060c0b0a0203 73
    0x118102850100c41e030b0320110f0f039408860300d40001c50754022601540086000000d124555000d0422501d0f00d400340c2c0d40c2c06d540c0340d011440750700d513003180100403a600101190708118554818909000d40f400e0514211030038540030781c0741c0a00500101c3c0c000b1606403003408040351a1150b1140464400c101140c810001d0791219203542c80104039404140d514698850701d659007030900c40040101c1d43c01e503200301e02c6001070b8a4481c0c1c46a2015400300d05c003440c4020740365109200d00c1035810729081401c0c8440781086400c134041e00300f00c101c00c0b0031440709100c0074001c0340081c40100420002c0d4040d402c0702c00d03d4000234810b66103000f40050043d4117020b800300a50358200071785030340708101850854115562035102d040240100e0300b1a0f40800e1002c10781e220400fa04001c81011f49000300c81c521a40ca00e00d0780000d43c0c1e4141c920101c41c21303c1c800070356803140b802d003a04510100b0228009030390100500b40c0c2200032400305540081e000036032044000c400e10801e4840d05400c0041140190b14501e808070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 994770566 1250 994769316 994769341
    0x180f01021506040506180406020a030c0e0f010c171b0c030c03100510030606060e03160f0308030a2711040c08070e0a030b0720060412050d0b03100906050a05 69
    0x6040b94041c6441c0c4001400507130340d00300c80d400c000d803407003a4590481c102400c0510003034210148540c042858020740c09010f80c02818509203042c0300500f000c3d4401d1070b41004641410384913904581c00c003404605040d1003115a0007a2106800100c00003425181070313403160b0301c1c0003852003002e03000b03810400c1e246015880200710380414500c003203c045042e80344d0b8440b0b00d40110281d440501110301c1e0400101c0c1c03240d8030941c2e141000b90202c0c2294840810440d01c107503071441d641b04409003801c14240070030001d07446070007460b07101c1501180002c0d84080d007006003d0280005410b13810149500100c3c0c410408610001c4040f13000a94041000407050700018003003680150060b018460038408020039540c030f640310307600070b1980112450350504062101808260921504071042e02e0600c600c8005a0340c0090341510440d0040e100780a1140a100c2c00c0c0d03450782c0404c2541e901c55031a90505030651720100b10321030040e051440700151003945402c1c508101d40020b850924010308107414410b9000482 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 994771816 1250 994770566 994770571
    0x11403042f10030c020f0d020607110307140c01080a090b130f050a0605180109050d0807050c0304260d0c08090130110f07081608180f010215 62
    0x150450301194aa510703100c22100300700210503500450b0001c84400c0c0c150b05400510071003200350200c4070446044002d003516880741c4540301340140d11810024004610400541040d20f58003420f40b80381c000b483c0c032a030f29880a00140100554000001540e103940d00076a541d40c0306031034100c10403141d00c803583d40448012004d030004070520024284032003400031204c1c0703905101da44003084030a151031a1521340040d203400c40300054144003103c407500000e00c042c02010703107007036100d0041d08800d0080c2c20240c0d07800402900000402406122995040f0410401000a0410311456094100c000080e52007850440c40803661640c00a1507040a8141c000410251155021746a285c440f40c001c0c0040721441c480e505a0901e10210012b200000d41c1a80490300046d40c0003038081c0000b102e030791010141c5102d03150000c1d490000400803100402c11242c05015a056052171001c0c0c0d141d06901c0b10400c5410401c02013154180000d80b0b0102031030140001013a104083c0050215460b91080c40c2e080310000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 994773066 1250 994771816 994771853
    0x609030a02070b03270c010905040207050c0d1e2a0b12150d2402041d2710060e0108031b0a020301050108030a0801050102010504150e0106080607030b01140304 70
    0x1201003030801c1d03c40c40d0040c2c0e1030351042d1070160091749200c1156a403190100c4155020807803c400200b42400c140c02254855074200f8010036004080400b4000b4110b40150300392000c030304040e6150a2821039030360045141d4062000340300314090000e4106020030007182c0b07061042d0760086003001080914019200c00c00d4121511080c2d0784d0381c00c01078046088a00304000c3d40186903071214010400c1c510000c030551700380b410407140c40d07694042700e03401240b2441c003440c40e50902e40d42d040800c60152104107940648bc007070321a80380b001400f6803944800c40c0b01551000c150010500d5140c4444640302d05401400100d440c0040c039450210402d0b01c80c400d68410011000c646480d04d10080420400700d4a000d038050007c101c00c2d079403480100c0e141c4c0c0040b01504d001036002d0000280b150b10502406000d03d402c00e1034903002503268850100213041004442d8101d540701c80c00000e5100c410311103548981c3d03145d10041000740e01600010440300380f50300260301c0c0d19414000e1001080c01c056080507201e54 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 994774316 1250 994773066 994773089
    0x6152104080304051207033e031206041107080313020a0f150804110d02040204050a030305030103020901170303070e0112060816090509030f070309080a06060f0b0304050607050a03140f01080609030a0207 89
    0x4014580c1c5100c003510050781c40b4595003040070723009044070000040c04a4986044034580644030041000147c3d0580046403a040c1014410940400c80301c40065400c013840090041a00c0c0c010783c085a0f00000c242d005101001c0e24032010071217109001000c2452201d24640082145040d544001c0d804c40405001030040403016a44421515280d0403107015007002451040b43d6a96490010851741c000d0208030300503042500001408400003141014140e1044059400d65850350400c4441207900300f4281d04208a05541c030360701142512032800070301a80c10140142145128000304941c44603840700c0b4407180b4150030444480f6001c8141c881000c014203070141d03180303000c3c1411600320790309401c144e100340607120b89071007000001d6110404843c42201e15200710366503602148000e00003100d001e0142d4004500041207184590002c00716485542400030700d0b000c450000005100c4100c925941c1030044800600041c0000c00810b60301c40000d000540c5001c900040003515030074644101c0c0d0100c1c0f0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 994775566 1250 994774316 994774367
    0x10509060a0506010c060509060105120307080306010e131a030d0203041a0c15011401021002030f04020f130207030c14060606040e0714180411030615210408030405120703 75
    0x20702c45c0d14040090b54218100384454140503001c076032034450a203e20b91150034070101642a486003c81910a0300d50060074a50a65030307a04019070341613030381d50542580301004598208002555104200b0000b450040350f01c18011040c040c545029402560681558402c0c44100b01c47d0000c496004c1e40408031605541d198230202c14200e140041c02c200111400d4420f000102d114100c100c003419008000364210354005500640040c01c03440b040d40c0241004030800c0020f005424000b5010010300c6010300340508040c444001c204c12a00044011000195910b000c0e10511000000c2c00c040d078691540030300b03a2030402d43d001440c40d21441c0320b144030001c038020008550601406840e06a01443c0007040e03640c4e0080b4140c243c6a80e400c1488910035450a080b072000c0030500030503031f407180f00301601941c0160180303010480c4682120703841403000e0340031201d42104590380c3c0805600030352041c3c0810b41c0f00c0c1003601d4880c0c1400d1044840c100e1a000c184100c2d00031950180d810000d0b4021f05940c81000d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 994776816 1250 994775566 994775569
    0xf0402070f05011b08010605072109080f011406100c02090c120c1b010506060d091545060f15030b180a02060a0e0d06060e0a0e010509060a0506 63
    0x201c5414400303030655180914a140c4601c41e028250320b411290344d0340c05026030720f6032002c2d60306000b2420302400c841d0390105441c18140150112403400040e030b0030319880a0795144209407070280420800010360b51207503860480032200d020307841d030400001c46422000381c9a26070001d11421520601034894050103000c00d40745461041140d03a403c00c10503000402d0b14102003002c00311780c071030400c08400c00e420460040052006100e20340c010302004010602d024404c00c840e0018041040d03054035000d01c007080c1c000395201944592203010622540402208541c1c1c00c0c60704407107005510000b548440014001a2221400b8421030041d030321003c0014001c202260a4008181c0c0024007120b0509508010092040c0001550300c02ca06100c10300e50344030395503a0025100c0c501898000c1d04044144403480805010300250300c605000600400c9003010141c40300360a54401c0c0e849101149584010b2041120160051905400030200207000e581810001c6030b5803000014800c404096640010030f0f441e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 994778066 1250 994776816 994776833
    0x3040f0501020c0c0111150408030907092412030c030804110d140c041401090207050c0a1401020106060c0f060f3b07051003020a090b1b12090f040207 66
    0x5240c10100864894010240e0b041d030b594440200c080c08164610a0844141000506280901200f840002c441e407180c0d5138202580d08040e000703464a00034020049450700c40b9100358500180030003100c08000c0d1040000d038001443c150020042204841400400300790408a48041c0560510308410b0560303ca003444406000f00d1900541c0c00303110b0b02208002c1c0480c0c40d40d4181d410400a058401d1810900100030031580d40d001c0c5030104950990040240070301c264050302c0d401303008078240d81c1580d0b080b00000303507118000d030000b1220382481440320520303503030910503400030f405542003a40310781150b501c0b0490003c84254004200584409980703901c400b51b5000603812a20503804600a8121a031204c0c50648060312403c0511070558004407401e0400103079001201c002915403a425403086000700c01941c007001400c818040301d003800196000103000240580c0d564074884451000d0a025607234101125400c807004030030310031301140d0350380d43d91441e43c030325041000c0394016554615881d010302e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 994779316 1250 994778066 994778093
    0x1020a060e0105040614090d11030921010f1505040c1404060903060e0c15070c050910060e01031b1d180f0c030c07060504081615150302150304 63
    0x4100d04046141d040c400701508a1401248216424400b0300c64006078402800401c440900b001e034804500b5112140c01800210901d40c150f4090b0380ca8000a617010401420722440c140c1c0280c400504201501d9500307228170302200084c41014000054890001c000b64440d6016070361155035110703c0c040b404c90150207a050000345030100661510350343d50002d00120000d200984010781820064015200e020903402c620340c0c002012a6080e176052030171040c483c5c001c1841150340d10031b115000301d019518114007a2140c0300c3c821400c0e0026040100041203920550815030502d400c081c440442c116a50400303401e401c98920b40713441c500f841c2c0c2c01010030050500c0c031090707000b5080b0030750240c0100c0d0500009101e601004c4203200039071144104d0381494030003112035089903a801c0c0300040010b8100d80115800c24000d664060424010705071504110400e110100c8a120000b03a50000c100d03028000e4020014030340b44500d0200b4615004515900300039200c11140070f01c000b00140800002d0b0040c0309 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 994780566 1250 994779316 994779323
    0x50411250308160c02150c0d09151106010323030d0b2724040203010306020909220605100b0a020f010b120627150f011a070b04060b06071115070506070e01020a 70
    0x8c000c0b00b40100042c1204400d802000ea002c10020410b81402d40504110b20a45c00341c08003d01c003503840c40d204d011007803030700100103034410248024101955900304058044a50500000034400300c007482004801144050407284038108600150100300364010403a83c8024003a280c14004c126808603411301a108401140d8070034030110000c02071200d2603000d80300c07034003080e600a00301da242c0b48035164880f1444040504c0603411744181d2400110a0b82140780c0140d02c08074440e0040391038141074603954100c050a04016400040c403903107202000d001e4001030003415506080c5040c00804403a40395100140203060000340801c81c103600c003c070390701440b80c2c43c0031540c03c0d1900701c1c8640c84415129907059841440d80390741c2800214000c01052510030603081c851003254940002c40c0d40300190140c0040041d540e181e42c9103a480c0c0b05031190030040610a200300142e0403c0c1242004105408190a20801d003503d41480900009000090500d0700f03d841c9050138070058401c0300040745031161026004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 994781816 1250 994780566 994780573
    0x2b0204212301062102040515090a0e101d0727090203070f1214031c0b0f09010807080105150604050111120d02040e180601050411250308160c02150c 65
    0x5201505801c4c0765008090f00c01c0b902407156440302000d0841200704a40010761085800f400704107850036550003005660030070340c00c4d50036503008080000100d0f0702420458001040454003030036083c2003405494041c11040d40c0e81074031400c0303810350f203000c3c0c446910000c030803a0b9560400e582959010082c501c024141143c0100f0b01030740702c0c0064520100522400c032095a141c20450100c40740110594000603860387c1d8001c4884075400d400f01c080d200f4080b842c1d030440400b1803074565a44420b12014068000d840040c02d84d203141a04070340c21950003e003403c0880c0071804001c0000d6803900d013258212136003445e000d00c0095100d007105082c921042005a440c6000040313481810302190041d108a91041840500703541d41d444c2050b0703003c1084408603405402000050005240c81d030f00c0103004c0040c890145003409900141c0500d03c49182d401d441d0f03c188405180010141e019444c0c5601c02100b04421003120780c40103000e02601e005580003442981072600d410003c2e5442c0013076a001e0341c0240101c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 994783066 1250 994781816 994781849
    0x30f02040f080c0915030316150c05130501020312010e061201021603030e030903062419081204180908070b04240905030904022b020421230106 63
    0x40c2e5030b44402d40010f901500d0201c0004441e00031010001c80d40ba68060301440c542650854441d001c004d88000c1220240504501c40c1b012400c10710601c00c02c4101c503103409590742d04000c1580702100f01a4170140c1154002c01407210b40501540c10700317044a1b04086c3c0459107440705d90000b26a82c13040882550250b00c003142c024207581d1001d260300314060180d2410401c505862840d030b070322803085c51220707500741d40043c2c085005251440d4036234901d04100c0722050280d5401702e0002e8480e4a281d0885012030050203400d005e60041405203c46141000311308610f09460925400c25003202140c0c2044000d0b41c450815081c0002d5408441d42e00b42d0201800969150919000c000640d0f0000ca55800788600311005a180c40140300d01c07030a07590000011030401c08140100710196010080ca04002c4150341c0c20340c44899000902c0340f1000d040c2e541c0250b151428002107040012400404000b00017100c0308020101d01d44110850303080c0c90700c01d65044d4200801070003601503c0d2651203c4083c2d8030310140b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 994784172 1106 994783066 994783079
    0x7050318010b06130f0618030b100506610b0f0f07020109022d091815090d050d09063e0a030f02040f 45
    0x2c02c50a00000100d2107035002001c0321108814003500600020980042100140490349041e400d00b87c100d1a002c1003510302840047d00703808490000caa5020700151001c0302400d80070b0302d2280d480c0380c040c03920350355a8022040c4240d6651003902880c04180d00354944d00782441030810f003004859070305000b0b80307103064480300c540d229030a00d0784008001a1450981c41c03146551802c82ca080b4074040081ea020803400404410844e4942000800140d41e0704002101e040c6040b4031800300f95521000103a0080f0b0123130005c0703604c11103800401158030b4420316100368000c06c00e0305075118080464441480c0b000140e851004036045112031131049031040014000041c4040c0c0041008106501c4203802c440c0c070030b41e0000524035095221900c0030b007103003120310311840d691405c01c56800300003990395018091610030f10f041549a44c0a014080720715015034001e0046000800110741d075030710 = true := by decide +kernel

theorem cover : BRFrame.Cov 994604316 994784172 := by
  have h0 := BRFrame.cov_init 994604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 994604316 ≤ n) (h2 : n < 994784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
