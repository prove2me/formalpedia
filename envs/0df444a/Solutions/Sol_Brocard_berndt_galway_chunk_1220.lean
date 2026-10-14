-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1220
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:49:54.408607+00:00
-- url     : https://prove2.me/submissions/29c68afe-4d10-45ef-b1e1-bd8eb1dd739d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 219244604 ≤ n < 219424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 219245854 1250 219244604 219244607
    0xf0415120506040c02030706320106030b0f01020c0906010210020d02040314010b010c0f0c03060f0507022109061309050f01140103050f01050603060d080307031e0209030303180f060406020c060601 86
    0x600002400f00035038000c000500000c0d80d40c2e00701e034542d404544011030070b050010fa540f402d405a01c207850444040d1089c01808429054030580c3d0b031442c02a01c034041d040c442200081d43c2c2d07000d52005c00f44110040c00018505a03c01c101d00700c5813080e03514046d03449070300c80300d1510044c1d0054041101e890718000041554920140302d414000381e81652980f041d00035984a101e804010640180c6481c041f008002c808641207001d4940840e40c07110300007a882c90211002420400b01c4d0801c4045001d9041c20381d0441e503403131000d80d000e8500c2151015a10240700083c240d81400590001070060304120801070161642c1003014121211038008260004110004404039001103480c9400700031520010302030390400714095030340801c020f4094010340b46140c486d4585600102c0d200d00019031941542e4149048007030111000342c0309146c080d17080c0381e1060002516800003e10307401d51300150625800031000700300241d0303101540590540d041c0d805c142c1004006584030a618000e944a000d010440c40e5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 219247104 1250 219245854 219245861
    0x5040510111209060f0f04060e0316120c030518040f0c0807020d081611010921140c0c01030507120c031a0609010c06020d0905251d0604020f041512050604 68
    0x105e40300410000b40b07039210b14120815480140050781c20b04c0d50340d0220410260100010f03c10407040c00c6020604100d1407401c045079000c661012400c01410300810b90000c0d811409480d904480700d40d00740102e10021000c40e000701107410281240700c3c00e010504a80b00e0700001643e004a00d139a09440a0030951031064814840c01c0c1c41c120741c9490030b100280403040c82485200c3e200c1031410b00200e07401410381c6a440800c2c03108a00e581c0d0488250765005212a00280d8801840e2402040e0034285203030480c203551214803010300746051548650004803c1361041c01c1c0c030480021000340400101d0556140100100034103090351103c240540340b101a00e281c0841074418050059442401c0a034103951800301079085040b071064000d48034440c03070000034010f000c0c007600c02e0040848005260780310161091240303c01d40c0b02e1542400148440c038220b181d1900a079900000586000d41e03a0203081c0301c1c0070a6441154444d1103101c2c603100d5040e1505174044c1d0003098680504c04c061055448140811046 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 219248354 1250 219247104 219247111
    0x506030109170a0e0123030601030f1505131503021203130f050a0b04050d230a03031416091502340501050903030403021509060412260d0504051011120906 68
    0x2400603605412202c89059001123034485810324002c1104644802e003482030f1241c08400c20f42e84c1c80b01c801c050220341040e14820b102e0000895040c001c071001c00c20301c0309030702c0c4160101a00404000341103032550f10301002210b0714514411450410603550304138490740401180265882002c20034030000b81040c801d4292015174030014440c050950856450906100300902c003e014a014680d0050704000d045c0041c0710312030301a45000c6540303801c1c0b801100c80d03910000c0031426103013007210346090050751044c0451f0075a216a08030b40c1207a0b000c11000d07031914140031644100303201d11505c0605a080003079450f90070120b05140224840341c0720700044d0746038092554420341540c018001000945403400c07000005603505242d951501116001044103030b800740c0c005440713018003880000b08020192a100d8070031601c0712180c00c030050548100f517486229008840b41080d4803007000c9003c0c1720f02886504d04801c100d01c0100920184200d07603e00d241c001241540500750604c000510401000c50014403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 219249604 1250 219248354 219248387
    0x101d060901080a0506030109020316050406090501031a09030f040914060306010320010e0a090b130506092701060e0a060602030f04170304080109110f03011e0506030109170a0e01 78
    0x80e603643c21050700c004100080100382d1641d01c40380c1c0c500158806002114203540403a10301d07840c860924003400152155548000fa40914040040011130048400741c490302c10040300c3c078a10b5403a0960900d245001d035846107203050701e0005d000210500c481c1d000c04a4000200e104450550384c4804254841030244406018200400e40600c81c895101901c50003441c030505221203541c16140100d00b030681190070050200303075244c2038101145841400100f840002e41000e0113686041008a03d10042c060f280002d0501e0300c140060001511a07840d201e4900681e0082000c1341e91f6070304030440d0350350640b00340003254034211010a03040d102004075402c48074010005850945810300e41d000009080c4c0c3c0c20580340c0010700020908036030a02401024500072400c541c09082c5220801c04800c1408214510907890120345401069846e15400c0d15010100b0300003580380e5400001c1780c05131144050080010000c4c88440a00301c14610290480544a540d5410262501c00041d501152081802007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 219250854 1250 219249604 219249617
    0x60c050717100e0c01032a080a0902120a0b07230706090b07050a020d08090c04090213020a0c060605010809060412050d02030c1804020412110f101d060901 68
    0x30411055000101c000e01240403100d02980c42800c00048414055440b02141c024a0341c480c0950391600440e01e0401562070100041c0102031580d10034808000d5032081403229004c0020801c02050b0b000164007500070382900d1400d1086024640c03030f06044c1c4c0e82220b0800006020944552180d90032000d050548030707060141142140018685170892101150720301d1320385112500244221100900071000c5032119501c1d40000100603090010f02200304041207101000c1003100ca00002c0d04551302132040e0340c0090407101030f0001c60700b907031040039004005a00000e03903410760030303400808803910a029040420080d62503100444e686c01d829103e0300403a074031100208003c20481090f684030300402e410041d00c0c0030b90f441d03203d02c166001240c40f403c0c0f07510042503690000c0800368040c400070b681101e0851030300c1d081c406500101d4251840c0940340119540181070140c44081021081c01801041c8041782e80c80c2d060000d104070803680460300154200150360b842d90405100ba2a048541611000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 219252104 1250 219250854 219250859
    0xb0f040515040207050f0609010c050d1805071d060909030319150e041505010506030a020a020a0c1412070302011b030c0f0501020c07080f030909040206040e0109050a06060c0507 78
    0x440a4900a4509440c4603601207484a1959aa100408139075114101502039079101380f512a003000d900800710803841e410142901a01e40e800f008542c864042c02d80001081c030341c012200d0480d8188000b009143d845071a034041104141d940302c4461000100704010001d6a4030418040d1550064038002c80d00d1303205101282c0515407180340114a0009401c0010f40c400700e008c01c04443c04002da03c0411001300840c280414000b00600c01d44443c0c0074000c0500032545004042251444010200b200d03440c0c2c046924501c0c0c520902c14203034003580011040c026142c81d01c1403201485205040c0310307c5544c98509030020700d2804a141d0007280d40507101c1c8141c504850f094929000c3c030420084003005002000440010f85c546541c000a0f4041ca000503160354480800700d1520f03141d500164903d0b8824150340000010000031039941c04c60940f9032503441d407154400b00748140925007180c030001d040f0100118104a255004034800d000c552000d00c6a00d41e642410b07242801040e0020385079400a0106 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 219253354 1250 219252104 219252109
    0x5030c030a0f14070311010e030a021e01032a021c0509041e0c0305040b01080c030601171608010c090b091f021e0319020d1e02030d09050a02130b0f 65
    0xb2881c1d80e028000d40c0c03502c81002c0940701c0c24541560001c8500b0030900c400c3c04050359220030040800a0150020030a4502a400143e010746a0b6202480c201c00c2e4030300b492205912035000452800380040360dd001d0706101c1441e420001c3c0f00c1940400040c804d0b80440803000140c1484a2420320040e01e5840c83c00c0c049005201c0030f803d81d007101c950050780e02c6400707845880d0248038080d03021466690000d8981040d103031510710960182d0012a040c1d000000b2101d070341c2c1d000304429044407403800e1a6600504030384130890a10815880c1c904072480070003000210180306400c2204c00b10500d42e03440030019202c450030101405015546900f2540450440e004100c1c1040c40b540d052800d8011150007102e100040c28144c164600302a1950300045a100001d800440840d080c541190003c0c2c00c03600031414000301002446065075003175902d0a009040f03114000c4c0104e800f50700310004280040302c85410030a940e0401218120f005456a02c015082c1c0384543c410030a00c0900106840f420b615030404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 219254604 1250 219253354 219253373
    0x703020a05040b0d06031a0a15180203090109050706020303100b0a08040212010f2d0c08040305071703100311030705030c0d020102031b0d1205040f17070b04030306090605030c030a 79
    0x74100405582e100040080f481c46001c500d40e8004041f030701d4150303151003450681640d0040700301d2222020503110911030b0107011000f0303030036420b90703000f0044e240e550303808280d0b000d4010004050080d0003005400f1881580c040000c520814038404660900e96540c21036001a10a030044440003079011401300300145030aa407581e00d40c241c0c1400116028440c1119402292400b9000400d9000c2d07a556045078045182d1607000b07190b59140e41088140f103a04000750003108001c3c801010030500080305070402098241321800200161001d40c2c8074a0890008560301e01180025a07880680041441040c0f40004124041d80c5014000d02650040e41040c13201421041904a0540c001401001072800754100c1e004440c440403002818611443d00001d09100100f1b8070700d856132070401007040003007001150805804c681c082c41080050034058085111400f400400515803169070080c4400d05515070422010345003094000c01c20b5030340c0d84040660703a452164079160941c1210000303c010800341c14 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 219255854 1250 219254604 219254617
    0x703030f0f170c031b0c030a081e0403121a0a090e10020325090e0402090c09040e151003200307080703061b03290310020a02150703020a05040b 63
    0x20b000403610145400725a001c181290f1074040e42c08080b082020000190780544916581841c0c8245003190114065840c3c3c800c00844405001b45000861031403219800210000042d810040300e0a08007840c0c0201620310042c520101c40e8102498074041342702680e255258400c0080c22074114510701840f0780068030311003c0702d06690090400341007580606000a6200c0e5070034003605480d030f0002c2c00c01d42c0bc004a13074507040d00c00c00020540920100000006654000760100c7d0303120540c0d600d03100900480d00c00c844202e03801c242003200501d1810350019804c1080d040c160014001540c400007000742c2101070384009001c03d541406c0c4442d100400191600b0255409001c0d00c6400c5c2c5c80301c210514100059004070303401399039105601c01c9900c640701c4c41600c481e107502d0b00340112545e403102e942100e414415100c07035030101841800155a01002182900c04c2018421354645104200294a880403200300380701a5540d0400140e4032482803085a840344a40e485141c141810a10014802c0d000302 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 219257104 1250 219255854 219255857
    0xf06010f030b100e09090316110d0c030609020a0b0315011d0a0b0406020c1905010509040f0e01020909161e0e030a0c050f0d0b06190909230703030f0f 66
    0x40d0b41044183d25500b000c0312440314181ca4201082c103083c4103009030071500800c1c00d0b030560018080341c1d00c0d441d040b20038580f88681000746d8401448021002481303c202c80c480042480d141024000100324864005051a900840e08019070540c1c510f08114548401ca0300c080002c04a10342c00c061943c019014201202c42e00b489204500f400400810164906900002c0c000c80000c030701088019810000030039100d605031628100ca10b0f851030b0100108030384e402610b041c00000f14400c005502c0c1e40c0c1c0070512100c0401000d00050b548201224002d50000c03012074000e00a040004041001c90308021182c8001551881080c00c10f60405560800d000c2c00c0c00010021010f1440499590800414032000d0107400c01e50340b0309141201308005100740e00c020074043c00740707400200042282c401480c0d51100c0300350389481044100b15400e81403085140c0061054a00e0910103c0600090f9100a1000120a00d44960442403012015665280b41c40001c0c0083c94001e400b2010f41d115510103482039520707 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 219258354 1250 219257104 219257111
    0x507050c040c0201091401060806010e071209080a020706080421020a05150a0e19060b0301090807380406020a0509060a08040b0601110304090b0303120a090c09050f06010f03 76
    0x100140030b5500441c2c4210060391038100380c0342400700001e054000128824001c02c042ca18004441e03848002c1481040c0c018002400011481f5024050780c80a240700c4c1c3c0402c106000f01c40c50030000c281c1004003804014402e000e80429194085d9403454040c0350400f603d0321542400c5540c090200400041c02c2c1c086020718101a8001a0208844070b9141c400301c0300d604d62460402561002c0360948403c0b01c15035481000b16400803560340d02d041500b150040004a40c08840e00d02190141084080082c154500000c0900600601c403012641c410600301e6440781e00d100b04e4183c81d50f801002c10f00002c5040d900404180043e80a50003041e581e0f1050501c1400e1020343d2000448a800000c0394001150303003a02004100483e04c1540f41d0300c80c0090034a203081d84c180740943d80e1303603000301c0c010300419a070380d44c04c282c01540e010020b540100e540c0e2400c000075480c00801d200c1c090016801c003152a24503100c00800c143c545801504c2c420101d605404d6a10b0b6211030044681d00502500141070655 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 219259604 1250 219258354 219258373
    0x70525290714030409050405010b040203041e020a081e010c020109050d080603070509150102011b05180607080a11070f0b0f03063c04060510050a031e0507030c080108030a050705 78
    0xa00f400600005c00080c0000207051070141070080c00d5546003072105115520420400c000103454440582610b40340544002103900b81c3d00c08a2404000c940120f41c5510039032141c14000344000b11640d00311711800c8024058000415810ba00b0385038a5880100690810b040220301140300b240b4460740050001c088800c110381d1080401d0781c00c0d109440d540307241c503201c1c400d0800550702401400360080d012000d08e0804807000760000c00c1401a28600c0d05e0902d01d000d082d85169552406850306150440d10300342c0c0d10018040c0c05008910741e65402c1e84940607550740040c0780c1c081421101c0884a1041145103000235496001003640d000404041d800400f9025480070800d40c10b2150003066140701900382d2008040c031200351018101518180f0031400d1440074805500ca2038480e41e0300074042e092003901c4803c0c4031400c1d0301900a804114480b1a003040241e59050200c0c2c002c18001c54981d201000251070204013100c14907024050141903901c104003a45105205400519042e0b0203003050311034102 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 219260854 1250 219259604 219259643
    0x9050d032705010807020606090c070c05030609010207020918061b070c090e10020f1803030705011803080708150f040e060c0702150301080a02090402060705252907 72
    0x5101c800d01c00c070794002107041400b031960041d250740d8100c0c5450000384442c0c03030b000c40040c080f10340c0108110348405001c1110703000c210105410a02074103000f815624140381045181e4000d42103d682039104000750804545011a05000c005050145401400c0295100020181403601c0c4444100c06050200140404645a900d4410103010020008107441000c2800d2901e02050306401c580202d10420032000c114508200300c54004101400d04015000d00da80082d0850050b580c0182455007030074200002e9601c221040e440c07036817081e01d92007256240e03030b034040303070442800c0718200c09100d070a00180020b4a0301410490160500410100e0b240b081d240388941048000e03146200010000f00700c00c0c0861074004070f90005911305000850031585046d8480381e4941ca6010044d020342c00150204003951038400440d001140c1010496900b0507a8464400d50b00c0d40640503a60392a004010110b400c0003844044200b91413800c0c074824819940881c41041644140000c4890180c14040440d958 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 219262104 1250 219260854 219260897
    0x40201030506014a1e03070b0408060f0f090606220c02010501050f0f18070c06060626070f080c1308030a11030301030308040303091106030109020d0f0c09050d03 71
    0x100504c01c4046059640e0400c44c14282e86a01281500c0c1c40005007085200d440c1c220041040c0c0a080c3d039415420800000402e08009107504202c0386940c00140c04900c5000001d490390081e50340ca0098141d942d65100d4503071081030280c51800a07034000790041402880e004c0600f19a0754815200008810540b450100446280010580260351103000402081c0f820382214440718501752141e000010060340059980400300030021076002220021540f41889000390f41d107402d6215408111513500d540000e4600f007011040c1c0ca1004500b01c40c803582c4084807440c140d02800054541102e8000581426a00014010084d514034201880005540320300c0d8101c00000f07003101d0015550f5281c0141c1c0c02490000099a200d5259200300010400203038080300040c0d1154052a000078003050701e00d00042080c8003408400d0b8860b90100001c030b442c1c2d19aa000b0441480814003c100400c001e9001300140c98418445c200840c0320780c00e04004a00b030070700d4030140041c4a0b2508a03c0c2e12000000d12005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 219263354 1250 219262104 219262157
    0x71809111207031133090d0c09050a060b0307050705030c070609180618050a180507140f060a20010501060215010e1014031006030f020f060f0304020103050601 70
    0x382e82c0400401c1080c40100d4554004020301660a0003003506504804c161811015030045441c40c410860000c8041151055071806100240310030782c3d0400c58240748101c840503019034120585402c2c082804040c90788185000c45002512245c11945c4a4200303036555001404162843d0008014a03269241c043c000c0001800301920b50000031810510085c254040c00380c0082c407803c1c5040e01c00e0140c80f400e080c0341c0c007440f40c03220300c082801ccd0f54159048000d01000d124044034801c460380180d04120021440d54142d039020480c8103503064a80f810410b40c0c08030061840e410107420010214000d101e081d04000d0045460310041d20240810101c60848909900180040e0007450340141c45d203107080010390042c8001102e03140e103414002420b0040c40c07c40c0c070400d00d1784603900107101c07440d0303d092003680d04081d5482420082c03d0303940c1c2030114034006041c0e01244680c0c0e82201c015410307d0700c10151441d0015514400e400e41d520340d4010743c01000701409040c188852802c000013801d0b0141c2c001d400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 219264604 1250 219263354 219263389
    0x1e16031101090c0b0301030c0605120f07120c110d0201090b06130209060a020c01021c0f110f0d0c0203070909050a0609062007060605040b03030a080c0408030a0203120907180911 78
    0x36250307d51f05002800d49056003040c0204502007140c5042c030300a4071504c2d40c0000c051b9440009984501e03009680b40e0840002441c2e0700781c01c0581900e071454112201901440c04401601c1d0458003009049003200c90b2400010703e0010b03c103020866034184420030f44040c0004a0005140070500c400041d13039504012000340043c1d110a03945030705940d061101c402c220448000c40d03103101d40c2d413100c06401c80c200c0700c1661081002604ca03144403c042005880d01d40e01c0750b02c081c0d480702402084010201c114031501a4064031840d000054405181c0c400c10060a4001010f046000d08070703560900600b01c03d00040c1c880540b90300620060400150903031160300d10504c0d086a940780c80e460001d09a83c5c10303a010512480c0b07460500710b8592408002ca0380306105078a00540340d550b80b6071110b110307401141c201082c01c1c8404100d034070409400000501d0f196601c804c11440c01d80c1c40c0100c00ba6110fa80d406074217000a480d484c6071800724103d401003c03290f44030390680c036a00d0074170030040b0b40e600790907030700d40301c1c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 219265854 1250 219264604 219264607
    0x1903080c0102041d1f0b0d0c0e10030b0a0e040b07230a050a030e151f08060c03011e0602030d090302150709050f0105180d021804081e16031101090c0b 66
    0x2100d400e409602d01d40010b8407170040d800881ca4080050268010040840c109545940c41081d11612030700ca000401640141120304000300c5440c010000c1c680c01810a0003000c134858041002000c0d0300800d0320079548840510002d40d0741c03010450794040740150000220960b071803030342904031225018103c03030800740d40c0d195110942982c000781034070b0b424082051240c11400210707140002c40f00c4455800030f0020030300303110000c03c1d240d12040603000342d01400d064051001805a0074944d180210b04a030b101c1126006a21100442540c900c0600d2184001690080100d0081d042079038010059072070090040c0d43c41e4100405400e01c0c401401c07208040092402d2100b4040d40ca0601c0f01c4070340d101020310301241000c000007125082d0b00742e602c2825104821a10301d0200b15030341c10040c0c403c00d9208000c520704506003841c01300c00c0b540203000d1200c442c4030384c03003c00500303190345c002135a03003000410529821104042d1000c2c4c0e0240e1110300500700c29500c40d44080c0c040342404036800e005240002070103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 219267104 1250 219265854 219265861
    0x60302090405011d0403050a1107080604020906031605010e1201020a03050405210306090405030c101a011e180f1205010605060a05030103080913050403050702010e1903080c0102041d 80
    0x1c42100d005070408000e440d03c4008011401c01c0859105502541c9801c000b9030354040d41c00195510820718121203a24843c81a02192848000c02c995010794801d030381b107074910340700d03e000c054850301403020060f04400e00395400c110545c40317082d4000100c04042d1400090214250010342607070301c081585400b10703441c0c1003403004001f000c00c00c49140b9105400806540d0310701c06035018461001a1106115042c001d01003414081c0520848141200d500201c072180840e07882100050b00c04112100c03a00d00200d0102200380d4002c0080d8101d8280b92032503000044802d500c1a65810614031070140c4c0c04014090101c1d420040c070090b18090805d11016030b081c11646d01d421800d542042c0c101c00c0c00f0303c1003401001481900b04003904e043d681c1c0f116075143c5504000001c00c0c500c80041d0003030f5078036500309010711003451341040c003d003142d0b4000e03a40c0c507a110b4001014050704030340242542d80c400c0740144007040810304545c013030300503103a5040016160940d035003814034141c0e05810150075080b0038041030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 219268354 1250 219267104 219267109
    0x1308090a1d060a0b0a050c0c090f040b0a060f030201030e0c150d0f0204050d0201140d05040305040e09011b03090f02060415020d0e1e0303090a090203010501030e0118110a09020406030209 82
    0x300d0382d018030115052070f900c6050030500301041c05807440250505c5000b0907190758980080c0300c080715044018052581501d08422031010a82c000e55094540c0d50800d0b0208101120501a400540f820400501c4504e81b031a4011070041901d00c02074010340c0620f4105140d2039542510107025007403801e0200d0f842ea600ea804100032615034288916413a0720400041005450f80340b10011b140341c0900b4004549107461284800f18840c0c83c0709440350301e00e048100300803d600140580280c80c007000000c0c515a45a481d40c43c200c4944041081300100f000107001141031003a0002c46800d489824681e00914180e404641560041d4105003a001200d50601255030350401040e4072201041c5070110807042c10801088018200d1501700c2c48110f46c2050341a0f05441c10421134070303100e0707002e040055040c0d601d01c90341000390000e0149a0020307041c540046410501401525500c5104010b18985103100e9074644420000348400507030009081d2a0001da80003503807000d030004240640b07000da540e1010104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 219269604 1250 219268354 219268409
    0x3050c1003150b09180f0a2414061204050607030e1204031b0b0307030b040506100509040504060902060c030408011d060a0c020c0402040f09050c0c061308090a 70
    0x204402014945001c009100041071042c104981c02e1119032660381110002040400e052200c10a42c0b0380716000c18010382d22111006c01c0e10a0b044650100504070240c0d8080e032090010344d6405c0c803454000706003846030380c00300b41c000c0c044100010203940c80c2045402402d5079483c0c084809072200c0c0c01031802c1204813a050700403400c3c54150000075140340c420700c2c1d42c882c0396802075000c094500c602443d11100c0340d401400300e00d00a4941d8403001910380c5006e1800502500c075003044e56000d1030a090204445080482000501c2d500e40c0d22031038100301c06042444000d0000603c1655225182d02405002d0380340c0b04028541200302030091070ba1103003407031512800d54003240b111203440c407441c1c04100d07002d03800860f41a420400304100400c50020b800012890940c2071810a40e029200007000261a080484040c0480d294840e0074040c69462112840c5c0d90700421080020603000000007581c002d190310082107090b8411000355003402400400320b07008401581100078103140d04058207200d00070940c0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 219270854 1250 219269604 219269629
    0x72c010803030903040605130e0f0702010c0504060e010507110406180608030f03040816080c070303020c0a0f0b250809041d031e07060c020d11010b0109050907110703050c 75
    0x5000303501d981080315501d07136244141d20030442002800b0032107007203e020b4200080c00030f2610140c040018103028800c030200c04000c2e00c80740050742ca042c1c4d5078065503000e5010b07101103038102c1c0c441000300c070440b40064610340d02c034410440e00464850415001035440344078a5004d005400c89640c09000742c100040111803182d00100c00da5403091280d40007405412044036446a44044015100d641800041e24200c46484009142250214040c01d030380c040003a180049078040e508803145618014140841840c01e80900d100c2c0ccc40c2d4202c400c2c0300e00c101d103000901c1609091040f020b001d0b205104100c0c0d07281c0716280226401c40b4000741c40c04061600340914441456082010200d000c41c040e203903a640e21559403240170790411680a522002c0c608000d81e20801c0e0060b10a00100340d501000079141c0c0504041c072004140e1180078040858014490707000b460300180c5075624100d08100c2007000fa00c4009018000700324001060b0f03c21924280b2100c801184030381e0040c65001d83c446d040080c4d412004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 219272104 1250 219270854 219270869
    0x2040b0a090b1606020705030d050a0c091211101e05070312020a2003040e0901020a031d0703030509040204080f0d0306051c0b0403261509040b060111072c01 69
    0x600040314050205868851490313804100160340780380510f0702e54150b0003980c00304500c6a250030100b02804146401410b0041c1d069900c9003801500c6000c0c00b6410740b5101c1005e0b000f180a483c4440e4181858000a10307440e0b400d080c500020244d012183e0f5124940070703117a500003240824a08105508218031a00300c0300014429410001c520000810507200311204001141c0d252160242160701030044801808201b181d40385070385444256607020354800000300b4002403520030305000755542c1c00741c82c0f91101c000710b024013074403841c40c5c804071101d40140725895400780d400c020000e0305d0380741040820400790060010300f01411242c80d02408039800c641c80301c1d0040e003203600315403c0803240c0c428207a06640c0c0650340f44095119400e0841d17440c0b0f00500c01c1a49070700c000d610a03440608a5000601c0b4018124510300b0f8003060340c00348032181106660041ca0011440c01050b015800b90195511100c44641140e95031941c82c2e1100c0841100546540602c10a00c00e60000c4003441e0001ca60151111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 219273354 1250 219272104 219272107
    0xe040c03061d030331030309051516050a02010b0a23091b070c0e0f0108070803070804050d020f090c09030c06070317070e0307090b1810120807050102040b0a090b 71
    0x928a8070740d2244801041d1040c2145c04880f0410010407020b80c3c1882016107402020800718146001340080912030310646461003055480c019800250441e03074440c1e031207078621241c00c1d41240000e407041e420102d04503095540320601c0d0105a00e40404a0008002c80301c803003103410100032090a07406400040080c0110100b0040082000b20b5200300e0704039800e40034149030b8816450400c4695080150002c00e6440c02180c2804400320f41c0081d15816038000c2415100007542e2078000a699100b0b00b0f000904078501400208030303038035100c0c1c050303c00540041d0140440119500020303410b80c00440c4d441c4401c4401044520741814100414024400c050b24000c2c41d00c00b081d01c01030703c1500c0d10307170004014601c01e4000810740d500c41c1d003428090040140480c1c0707425498840306130260002501c003070f005003c6010000c400c2c855400f8440e01800e00c10124525880c144807001c60200241030094038941c1c0c0400104001800c02d00c02400104400d4042c15281c4015120042c0f0600061b032144058020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 219274604 1250 219273354 219273401
    0x170f150f0703151509090c050a02190309051509040c030f060e0f01031e050f06040b0a05060904031202130806070906020d02070915080109050c1203070f0206030603070e040c0306 78
    0x1d4002c10f0700c15100008070b4280c1c0701150200440382c4540c103401001c2e81500301a040307404207420101500c1c5914a40c0c0958450f0005000d15001280c040d440203000140c0e00b031000c1201d41080780d00c5c07a00d40005007601501d044405400310381520f0300380c5007940000b1f079101c04444242086100380409030039100f0260f000c3e800d03e413a03404211f0106000c003521100403042d810141d16010841410610b07071000560344102180483c16841e450215001c5d90360742000301c002040c01050344219441584010580320b07040d1a2901d08a401620140700021255400c0001c800c01150030000e020040012200602c49458251801030510151368031a070255401410b640100640100e085401c0d204255000910a60319548d049814202988004125441c1451400078403501060030300b0710310000d840109001205ea25900c0e030300d20540381e018158810300600030005182001c011034001c40024122040c2c15220711510402030f10544040b83e0f08440340345e04004026542c011401c0b1403a02e1100c0c920b4009 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 219275854 1250 219274604 219274631
    0x3010b01030605031c0e0a0803030103060c0918091b0905010906080f0a0f1106120a05100602100f1407020304060215041a060d08030a09020a080303060307170f150f0703 74
    0x8841e011741d128800e9041034011540d2056002008804004201138070041e5070384103c1d51039078000c0c00252070361030400c0e110254a0b40034040c084102c070051800c10f031003940101e8255004045189085071100c0c50002d54400d141c0341d0070040c1020b850041c900241c15403402000b41c2c215402030340106450b40010710010404440030445d081a550440049140e0340d0031443c0445941d00c8200d44c00743d001002040400c00c00c40010b41c91407007100d00a0741003107079803610701003034161565601c02c0e1001a440b403400300b0402a170039080400590052032005c03941c242008030845205000300c0740c603c0142d002080401c00e4584c100004014428400e01410f20760400c1c0e1543c8001d40365507068841c002d0401c0d404a81503032185031402040ca038116651980b42e080135401070000d00660b4609a00c540e410001c04a10006e000c022680903260007801042c8261804c071003054540c00d0410b81c092035008105040310702e0402405a0150200c0c0130802041601d00103581340600361000c2c0c400d008041c5040c0c1d5040584 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 219277104 1250 219275854 219275863
    0x4050105091810020a0801080d020a0503030703020d09060c030504031205060d0209070203070209011403100e06130203030408010c050a030e0a0c0303110703020a14090106171902070501020310030203010b0103060503 94
    0x38886164041c0107000c01c0d800c0c074500a240ca42d80f821041c40095024403040c2d010002a050700c2070802a03805c4e0700c104800c104d0b5501c03c080b802a0031030308200042045c442c040c1d40184112540e1003000700e20381060791034550132036659507520804292640100000c00d548a08503412805210030200b12500f440c2e4003180c2d03003140b246002801044042c0c0070038130481c001c0042e100c00a5009240340780541c6c481180504611900c1002c6009201d0100398546201442c012411500144d1000b0021640e8000d81c69404009120042e80c01d030100b0480818010750038002d52205066646800b0b65581e2012001000c0f40c0e402d6402c0d201640110383c40780005040d004541d01100d405d4a4488032014040e41002d01700902688004d61289446000007555021021945001e20045441d40700036a40e9944c00c0c1c0c0c40c5c02510036195500c19140c00001c1001c070b024000c0e0540c0c1403401c200103060036616510325089034015105180584113041041086217000d001d01c0004120a180521a1724540008260344 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 219278354 1250 219277104 219277111
    0x30d0507030e0d08071101030606030c02152206020c06060103020a050702010c080d090c031709010c12140c010506030f0309010c1e0f08071203090b0423010e070e060405010509 77
    0x100100d41100d0210ba9580194907900302e500403080503079540162030103104585800c0caa45001c039080c000f0000c1e00300d00901c904410314241c0e8010744142c8001103c41d60103054000e0101d0992071504114080120300c04180080d0548100401070707499003254441480d00c03d0051569040500400c400820564000c0c19600c4c025070a0904010b04041490058864041c0a904400c00c0d03251032003400c24840003641c50382c1102e00540e8003401c0104e0b5650511620301c034034000ba80c0410541350440000441d0420b03034003201001490040400c403140c040860321940304070108443daa450b601440756a18061041ca031200031500021403804041c076001178101c140c0d201d4080c0c01e404940c808680411545a4201701541c5e00070130a2070260a030346800c06140e00503c105940c0c141041041081240c004d110300d000203030f00007034212229030303451742c800801e1360701e50313084c1e80782d0004d000c400c0e14a404090245100849205000d4041d03e401c000860042400041c41c840c403403401c090041010341c60701e03600300b5007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 219279604 1250 219278354 219278357
    0x1020f1803030403150203152211030f010b0f270102060702010c12020c01021e03040b090307050c060c0141060a15050f1602101d060310030203030408100506030d050703 74
    0x7202d43d2015109120034081d5002281c00443c0202250074101448001441c009c40c11001000000300b544035601c15408100c3d4015083c00755400144201c01200c4c019100502d1150204c61601c14441082c03098001070300600399131100304d01d070185069a014084982d100072180700030816103103160780007401c2c000040300f1000c4d103943c0081c620003c40b01c290100d40300d264104102d01514052401c0c140c0e100c1d4021541a50150110b5020403503490380481142e81c0d164109000b400140e646004100e200e078092a0050f55641d40c4061098007401400c50030100c0106103600b81040d0200034640b0741d00da150b0f6500100401da148020040d0320f940300d2400c0d10a0781c80501004070615900345c800e803554400c05040c070010303c00100d0040000320381003190518141c070030380344201701c5c41e955081a100d1000e101902440d1240c011400c03030540c2040c0c0050b66202c1030410085034440e980f41c01081c02d652007134103d1000c94000c1c14040028040602649810410540044c90070f6100d07900018a42e00501c0c40040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 219280854 1250 219279604 219279607
    0x7050706030b0d0c0305030c062206020d060512060a05070c0203061f2d050904020d020f0a050a0605030f070f21020f0307050a18140f0d0501020f18030304031502 71
    0x1025512407403250380e0f0042e0300c0700062004a4990500c1583c3e0b41001c1d66080d510312074000090f9100400700c108480d14101c84d601c20440da55196079000c0650001c950b048401561360000141ba0341d0382c81c0c030b80c0b024444140050482e0742082c2d01c6480c10342c3c5c07004020f0420700c00b03503a0b44880142c5000486651115503850315540c0c083d001d00340c20f00b1404055001c034040c4016680400e04078268505824254954040c950344260743d100c00340606800b044601a60100080f10704c40c000d800e242031a00b0710340c400188141443c40c0c0301e800142c8000402c2d00110300060004c001c12920700c6c03490424680110700c5080200132a000101d00034036003809080e018034541c09089030b4500020040c0c040d1060b2400c50742045480345401d03e401000f50300040021000180320381407041e41c111180340c0702e9042d180f5007901c0d00103848a800a0000380707400c0c44421600402c0705484e00000c03507400e2002d07091807090801360035520014426107441210a90001a00c40e1b0002c000800c0060902c16140c1d5440041c0741002d07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 219282104 1250 219280854 219280871
    0x1305040204090803040c0806070906090b07060e030c1506040506060912030706090b06030610080c041505030307030c0b07020c030607081e1008010f11090409050709060b070204110705070603 83
    0x90140034001c6005025090110500c020801b01e44000c0040e1801503080780c10300d560b811411a00c100c207521981e00410f607215400d00110100000402e020b9004002c00f107007040c071303ca50940c910b5004802215040c3c120442040312001d1186190750084402c0781c00307000e2030034000001141480340000f003d210380c03454000c1304c03041c2d074040c0140c40180340c202c0d400f000b295980341003003124950700300c2e5007510038082c41f03002451180c500604c0318182d13425000140a1000e14000b800002d002c0000700e012a15110600000c2d903a0b0104001c03c13401c0d1195840842c185102d141109040c040034020000f9500140d0040e007980e02c00080c80d50b0311891703c2c607100d103403034071000c0e802c1c001030a82c440481501c030b04540401031221540c4000c0401c44150074001c20049201d444100d00315004000b0034000c0d02020080d9001d907140581080e00401d015030300340c9100c181e035441506c0807a07810340d210302c520000119a000662400b803091050078071485030100c0c5008401e0b43ca56840d0302642c010f50043c180d40e582c40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 219283354 1250 219282104 219282109
    0x60102160b0f0717120402210a1b0905010801020403030906020a0803071b02031b0901060c030c060507020309030601081015060e0409060615020303040b010602030405012c060f070210030b13050402 86
    0x1a251300b2420146503101030300448a0011041100c01340c0c040c5044c8000800004011225001c1c12910b900c06400c040c121a038460320b880154102c01c042c24081c9a901040c455414030071b26000b403462500041e580c902c1c524026051990a40c0150155000800300c00301040940b81140e82c004103a10b0140c00a078103540c103520800c921018080d400d403141440e0010782c000e5841c8000b02c1090f040350a804903030ba885804136240003c3d158001d0006002298440025449800090f04120103005490422801c100844c0c60060242d129005507445810002c00100700c52181d400e0500c008080c0240960802c0300140c00c0d02841800e60340150350790340d40c4105100040d400300300a441c1d1028910781045a411009642c0c3d0800c1e90284c500c0d815035800025464000000c407000c03500103854204404c2d84043c0715140310396001000300e805d0800c40c00c0c1c804d802c0d9191402803255203490304c54640c50f00c01e180140140c1e5003103200303d9030526280c00104031a5a5581c030210802c81c46541000ca4581c0d41c0313102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 219284604 1250 219283354 219283373
    0x9170d060306020d1a1509091e040f0303111303021c120e120c010819090b07050a020c030c1f020102070f05060105100c02010e0108041110020105060102160b0f07 71
    0x40c118038070101d00b0084c8042c880e000210310380849181200c10f4035a640410000c0848240124400d007420880109a814000500e55001100550340c1e041010382841c00c0542e060200c50071131b40c2d007604440034401c064141c8200001c2e07020000d609404c0c030340000e407441729440c0c450001030b1003103d10340d41440d0145111181d01e40c81607030114170b80a0340b148140010b4107003a9100c003130074031030010881d00705c0409100148508031010141e49010aa48561900f2800702c1c01c800c008078101d41c1c50340860800328600c6550b0743c1c002c14182d41ca0540c1c42000a20007810084c0000314984079400840b0701b05170070358440100700c20914002020000020324004281d009205a440040030701c41d00d20320134018840003107045412110b00340c803500400c0c0b40d8070b0021104440c08590080c0844ca031900c0ca4a4507500c90080c09034814481c0401c140440c50030740004050220705140c0f407005030b44510410074196414040c10141c1c0311907100103507409080054500c814001c40040d08801d900c0480c4107001c0c00807028 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 219285854 1250 219284604 219284609
    0x20a02060f010e13080d0c0206010503100b06090d02190815070201050712050a061809020102060609100e04020105040302060d05061e0109152604020102151320040609050103140109170d06 82
    0x101e0400c4621407c1401a4403002c2c01d201e0144039004008554070a00c50a028440d048040103080a00e031000d03103010410829403c900980e0000030381000380d60a001c0c800701f9040034219400c020300f8840b01160a05d00110700c0100742204690420042c04ac04079000044600c1d90f2000820101d601c0c1c0e42c031044400101540c0d80b02c201d0502080d003034220b01c03508503800710004ca4000e80c00e6640710741d40c28080c4104100180c0f020b11140e042c11904101080810340c2a5030414414500185000d94a40010303420740c00080307030300d41200d648100780403441c50015030490681c2c000d0802150b05450310710028001000511903103d400c0a1020840100d904c600881c0756584020300e00150300502c010b00b003810b1654121001c07070140c4075140320112030400500085109184400191001741d01e943ea075941c08003034088840381d120f4400308007452a80e8480c050000501a0628009070340c0d80741d800c3c11007c01c102004140c01a9140041030740126009000e006100d4032010304031559841645000b800601495 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 219287104 1250 219285854 219285877
    0x4060513050c160b1009140c07030201060e07050903010501150e1c05030c0f0c01031104150e040513290610091d07030b0109050303090d15050703020a02060f010e1308 73
    0x102c29031400c002c00701e192a400b44100d0172589422a03160781d021012110f545070043c544003605c0001500f407010b0b40000702140c9100b440040303412952032002e03031480708003903031f074000891000b040d28280c904091003203d006080300c48502c1811034001c1c0010746804540ba4405020b404003800000020640076010200c0552180031283d0b9111071500c226121000c1c010b4844507030040c1c070300042d4150310900481940b0148200842d190031301d04102e00c18000000c40d14003060003113660340542140e5551080c40d101c5c802000c3c0340d9050000624084913541c1c841541c007105600f90340030000100703140500b0b0541c407200580f0700c0d1b0404a00c40406480b0266103500080c2c0141900440010901c0301c840303094000c0041c2e46050003c4100c138001511907407900d001355601a03009001840540c03030108103068580303020300c2101d12007041801380b40c815110100d680b2408260000382c50382c0d80c69410402180c1c01815980da50b403a03035041c851000312004003e440814800c20090f540c10030300000201b100d0007082d65 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 219288354 1250 219287104 219287137
    0x409080c0604060e07080106180519060605090310050f0c031806090a02041119030b0d02060408060f01060c150f180302011d01060b1e04170303011404060513050c 71
    0x5142a0f4041d0408a0006415020703c40c000240201c0c140200320503144d002d242c2505110b22203051500500004000f5070840f0385d64414071180000e40d224001c064000c035580c15a82d001540b09041c941003c2940390359406181900300520005110b0b05103402c000b1031020b03240c0c0c940394142c049203403000b20000c0b4480d034040c030700c00d000080c000064100d102030b20235602400368518600c124455400b540040e50b000b1000c440140700c90f030340b00f503000c0200400300620340f001c802e0198010030314980245e0011b41c910380c088410302c04462120042c0e540188181c7ca00a041d20b0f0581d503400c603030f8000b646003094a440e2100d80b421101115a00841040140072042542d030002504000780a0a9141d6100141405040c444107803030406020351360903605414801c514003100c40d51005810110101c035687e100400340300106803550b200b044c6010307100b0840020354036541802c00b03507590800740300c8001d88105c0c0b4150303080000303455000106c1da01020348580025281d41d840800301c1705100c1c440803040d90061 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 219289604 1250 219288354 219288361
    0x10b0a030e16080706080106020604030c0507080d03090b01050d05070b0c0a02120d0306080c03030a180806040c080705010e130207060b0a2601180b0c0f1306021b0a050409080c06 78
    0x40125242e02110740e00802c40f003005070f40b2001503c010724203024170b03801038200394005408240214075440b8058410340403556911340d1002054103081280003194002a240e10a100600120b545424050041114860700d4a03100d03503211681c0752014400c1804403840070551041c0c40006011881045030094400d0486140400c800ca0311551021079250102c1d107004004280c1d04000100519403800280c005d501d46151040245c0340e00012814041310f84007412030104244400380500c40c09a449a8000f00859040c5400241014516080241085900021600d03982e03580c40d00380e800720900c20340060b6140054240704010308007021250f034000b0094600000c1d204481c10b4003200c211040100080c8180c481003000307080e18003020f160b0010090102c0b0040100303000d022210341002c1448800703498503070f5030100580030340c018000c2d080c030301c081d4400e040040395018011184590124086007582c04444800160070314a6802070501031035980b580359041007101d100700c61401c0d250108680c4d8518 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 219290854 1250 219289604 219289633
    0x15120705070510060614090a0510110f0c011e11010c11190b010b090d060513170a120203070318050a1e050a08031e04050705190509010b0a030e 63
    0x5100c800308449501c1083e42c0c0ca100805184150020358020f075071680c180041e0021090740c59040400340507885003043c0030008242c0da641039680c0c4959800e4980e003125000e01c21a036404c0518004525566401c040c014a62a80e48050a038201e1a413010360641c0070342d00308008503151110444100250b41c40c1020f43d07410507400c40e004142480700e0340101d80034002c2d00c0001d8421510b042d0310003004425410018004041d80b41c024100c0c88601420169400301140c5564040d5802950450314040007000c20809110224140701d0042035865402e074544001084001e0005c1e951008416a06601201066003030f44039030002805125010700c00b25080107103091003500c0d007644034402c5501500600b10940b800b00640010892190044090408240141c541181c2c0341c2c07000700012a0801041d80f4403504405c10060980140e004200401180e820b2009220a03074050b0320303212040308501c0c1410000c9542d440d94041c10340c0c19020140791100c40f01a4160084c5c0380d1030004607964040c42a40d9050754 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 219292104 1250 219290854 219290857
    0x609060608030324060c0a06090f23120702011d031e030301050406090c0807050f130905040308070e0a03080702060d060b0c01150308030402270901090b010512030915120705 76
    0x1030380c12042107814040f001e82041000d1007880b14001094220955040100c8c403d0791020a100307019140103114440d1540d1104c2074408544e1040501010034020003c41807400c0014048172082d200050385004000d400103400c80c0310041c3d030303840ba040c0b10404154680c0ca00303010a40e01115200074003801c51001740d07a01c9499030824000c5500a40c54107a0010340c000480c0503080072190030351030786200382d1500c1604951551103641f41c2103003c070b010011b54002034280000e62009101b94040040c0504151034014406000582404100003e4200e00d004c81ea41d25030000003104e0344001c5103595400ca51003c11628001c00c640301e4a441d02c0c120000a1400000d00103000c5400583c0080100038205020003881e40c0043c00090709200081c0300090040c1041200c81c080e6050b40c81c00c218100408141003d00004100c402088a0351503c442c00f04020260a00074003604080b1041c410004510001603a2030203071254070f6200b10720280440e6040c00110081750001e41d58207e400c000b6190051001e8880d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 219293354 1250 219292104 219292141
    0x2a030a0903080f040209010611070506040b04031e020a2303060702010506130509120f13030302070f170604110a08190b090d1d011206180c080106050706090606080303 73
    0x41403074800090800c00f03440f02228810350340240004010703401c0c03402c101c035103400d8030000041d80e20032403c0114807507980802800003000481405503a840c2545003c3d2200d03d0260107050310009489441001613881d03070301d201d0a070341603102e00d000a1003828041c0d034a007101115006805004250901003019419003042d80305001c00c0d1554640985440c1c1050110307141122a034086400503150015401d070390500a01c01c5001c50001103080000a14055242e038803e5401100560712181c02003200a411400010040c01034085040d80f080c0c0c000301598890074000d01c02082c003d0250412503043d618540e0410140c140501241c001c501055440f0040109005040e11080850710003c0c03400400005c1038440240c8507522003c0b1700003101001520078404c000303240c1c1170140c41c420344e0b0244001e03441204014030f03d268509c0c18010800b4402000c544520185404100d0b10310010701140b0380000031181043d602810000f114012414850020100ca8100b504103000000600403041e50341d02d01e05c1c12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 219294604 1250 219293354 219293357
    0x3160c03050d0f022515080a0501050a030201120b2e030f180f0c09021204110402090307030f06060f030506060a0f080c06030c090a0f1401030605092a030a0903 70
    0x10050420b503030684402801610b0346006a2081c103640410010700d0f5422100448110b014000391510b034800e80400b0006400c002e40000c80c84400c00c943c824050142134010312050b1694441107045400007001607103000900650503485401c015490346030052010525026807031810301c203002e1003403403410148842003000000317030521003450340d040028414095420411010180541e859036034a5550300c030224000e40e08100482e0001031034034290300060180107200d0300c04118601c0c05150070321600c005541d480d8010703441030000e2000c4c1d40340054200c09880d0020b00c032681d041d40303500e0801c000d0441c90300210f04203c6100703400000c00c46c0000d019030140c401101e1a0400c035031a80c45003041ea80032840340350442e130300030101c442090802d80020354110490500042c030b0136120102003000e5a659602076103440080e40d100f04105011041d2910342d0440c02d1134184142c0785080000750400101804218004800c000c240401100b0703a2205000c81030700c4440d81b0b80700d15210103400000c22900e10240d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 219295854 1250 219294604 219294613
    0xc0d060b13050411120603120c01060f0b0406020c061b0d03050a0e01090b1902090a0b0c0706080c1e0702150c0d0206161115090604140d0f080903160c0305 68
    0x305850705015481203413405124080c1044400c09030301c2d01c0c058001d000c0e01d80501a4050110700b40840c3c40007888000d03085000840c050707280c00701400c1469a56030103041508800d10081c421217038003054414030702800310341030390315080003562404003d010b03000e20200d01d11070000740c0800d0743d405412040c482ca10076141001650031f1300b082c0307a00b600c0c1c1c85100103003414524000180c1d90380c0c0002c800d07480d0f1401400014104580c19001c030703c4100c4541c2142c0d130035030008141000050b40800c0000041c21145c604203040741010080882c46000300ca082040d100103c03c4080c2900014100f0b0302c0c20140c00600f5400d05110b0503900c16450303840580b280655014403480740c0e1310640000341c102c3c0944200c0c80c84240d00e106618080340c40246008ca03211090181000c012103644001421b18000c13900c4801a00441c180382c5070402144150910b10f219a0700143c007084080e9030803112211400401c2d0030708007143c0e03445090080c2540b00701400d0454049400341c41800f40100340e001c0c08190b074410341c200c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 219297104 1250 219295854 219295859
    0x5220317180d12290f01020d0206070e01051216030609090f02040522110102063601060510020a0606090b0d08070303090b07030504050c120d05030c0d060b13 69
    0x2840148640350740c1e24060740c403049202d12814881c0f5030102c1040328500740000c0311441035041d4200f0301409902203120b100a03403070110003445d00c8000c080c0d01d40c40900041006840c0c605000c2d4403100e00800340f4003132003201c81909490340d00910440e1a242001d2680d051180340c01c40314030110348403551111000928015004c1020401c901c40e0510803a04001c5a1034074008507402c02c00903200080c10243c03403030780211418010b00c0b105040e504020f84500c1040c005181040002454100014241305c1a00007011811211210000140001044000c401c2c0d800e49003880fa0103000d8030180d4495500071021855002402d503011640f60200c501c01c1c032003480126612040e210503241391000703095011801c5420a800904c607140144400761103401c1c0070503400c3d2107480300c9141c010b0031208040880c0d101d40400c000c000d401e10204030701c90f01c2103480060313221900742d0095407108029190700c2440303000000704602d4140c03403041c2e84000e81c0c3e028080c8111034072040c4440246e00300c214241401c0c03200100c00b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 219298354 1250 219297104 219297121
    0x6010e0615030a1d121e0c1c0e100f0f09080f0f06010e01050604180f050411031603030e06090f0a0303031d0708280c03140f010203060306010905220317 67
    0x14252030307840d541400c1e81841061b41101c02000c4884441541400c41080815145142444040020024401c0c1804404e0130b8860245c519095281308610a00390310303007007003851078012100250000d05c6141c44050500230040564480c01590000c0c11f061142c4003542403810000190380317050380741030400d5440d26640ca0120381003842083c000d0a61015003440140300543c0840c2c1d00441340c1c5c3e030b42203001c070340410801c0310f9008642c0296030a5840ca0801144401e042c2000c00111550b55290264051300d01c2c91070310700812400030901c02620131800000c40840c1591101c10000e401d9400034214030595940c0d140c09001000e03a0502d030031003900c44190b072851640022030800d0403240c3c4400a00b2520980c0052400300314a807070001500d6629234a035210100740701e444040d002d580b10308001d414420003011440d1074400440f080101581c0104104405520080b070f16030304503903509002280e161a0003060440c0c1c55640700c200c45210441d2034002060541c41109200d01081038070074240b054440b20311 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 219299604 1250 219298354 219298363
    0x212010516110601030308040f120503010f06021b040209030309060d0c082503020a1407120e0319020904050307201c120819060801050901050c070506010e0615030a1d 73
    0x540d800b0940000d00104042409924030b10b41c802d00c269a009207050782590313001500c2400d103804074001407020006000404517014030901800ea50300003030018010155102086000ca005103600454001c200c070062600d01308107071805000024021a1140080e007031000007403080081c0c920000b803021002c1090611442d8440d01c81c40c009000755680f4110311441500607620408034101000320002c40b20302241e0728413018180e0148520300c440308004441400070b04101c2c2c1f0171000303481b0307402c107080f040b0101234a03450103025298141c4e000b107403a90342c0c0d080c25407c6005041004c1c3c034400021903410b00c1e401e849540a0342c0032a0171151100d200003103040d00754540c000c002d0001d11090000d214600345c140103070303103283e0701503000010a02c0781c12038800700304144c480c05d0307100c1c075003070780d1180188402c0000c28040c0c564481d001e10000c5042803880d442e40c5507202c0e0180f24405000d03501c1000f24505850704035a04c00b1070707100c220419030f13242407500e01400100f000d0705c0946103800981400809009000c00d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 219300854 1250 219299604 219299627
    0x3050a0612050d0807050405090403080910020901020c01140c03070f0b16050d0921030f0509010506060901081e0c090f0103090203100b120708030405210a06090602070212010516 78
    0xc005200d080f0903080e042c0d44020340a005e100a0060a00c400207a507601d0400c4070b48034920aa6035446a401c000c0035140c5043c42c034204140180e401481041f441d6640080c100c4004402441c1c408580564203510b10b07801d02c654002c1c07500030700001843d4028010040510011284100d4001030964ad4042184c1100c1c8200c030580c1001903400c02503507000703e069030000400f2030b018450301c00701c5010080304100d402050600105c040390329211140c00503c0e0a03c5004e0340320307403402c00a1046152110000d1a5446801011814445920040303107003008150b0f02c119000551080e04c0704a800c00c0112020030781c00010342c080c45545444200545540b1902907204550383c054010b000c0c60404100c0500506400342845800c1b0503032061007032501c2400c12820f4000c00d01a0301035a9a282000e040c400c0d41b68440903100c02c80007403062242544034001400001c2c65401a00c0010100107a00e4044d010f8840c0c40006540002e8411091400407010351000307000d2601600690000d030f28162042d203c0c1d02c4c81c3da = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 219302104 1250 219300854 219300863
    0x1060207030303093e0a030803040303050c0c060903091314060f0301111305031903140a0c0813060f0e060f16120201050712050903031501030e01090303050a0612 71
    0xc10204002402500300d101540e200d02212180d0010310a5440142001c6a44012075042e00f21141a40e2410521303a4006100040e00c03841c10180c215103680d0f13890b11004d007006080507078a20014012a001c282038a0f41c41101c0c5003170382c840c3c0c200584120307907a82084c406c29100f10400f600b0484489440c2c0f00e20301c11001460f0280c0c0ea295900c07001c001c2803000c1c4108094042d52100d0803a1900c0c03c0800c0104941c203406e4071102569070030b080500d8a80040010126041c070140da10a6000c80d82050f80315002c00005031040390b8844055504a68a4511520041c007964010560220050140c01e26005031001540c840090030b0302240102d4120b1440381d03181da01b00c0001c220360000403030071034000d00c0a9580040e03451407a0b0641c1d0340703c01c1c940c610030790a0340c0141d56039014401c515610240b0000c0c0c108007184c090049041001100f0f80740d100140c1100701000c2c400804074103a03402a088034402d042c410008126055103800cac09409404c0c100d0740d8940040c0b5200d0081850041802403d800e240c12 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 219303354 1250 219302104 219302113
    0x10020703030327110a0810060305060618040b0604111b0c1005040302010c020a0b030c0309070e040c0509180d0306140402040311010c06060305070605121e060f0109030b070521010602 80
    0xf544404016405103079809400c000304401c0801e080c0c1c0d04202e00740d5030340300c08400050201e244d070800a04052014201d54400c05285104518100311100c0c5241c0007038108581000c19124180040c00910300d041b00e41c64035200104440b1003460402e40103440118120b415100c00131404010420340d5208101c040780400e100303001c1400035502c80c0703080440036403020b44510081c2d6142c00343e803100d07504116026213500000100304035480c06c00f480480000c01e00b0004030030290400780d40d95070003500680252030080180d81c0004041000c01118459458400425942c890700741900c0240505007078010001076121605500c04079060601c01c80381103d40051404400700030590046030b64941803c82070340e1403912204040f0100310144030500040900e6210355999003005040c4074a8044010010003040c0d4650301c80c0c3d255180402c092030781c0250f04503988841210b029005860400494101401c2d05840d00c2c02c1041e610380010081800d91921200c4e40b040c211140c0e20320f1030300c2500340240c0700145c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 219304604 1250 219303354 219303431
    0x504140f0a082a0a081309090809130b0d0809030f0a0807030e06040810050403121b11030f13030b010807030c0e070311030405010501060e03010605090f0a0902100207030303 76
    0x10200d26840000803d2444155144209103a940350405650b400d454180d00051440340c003014409020000b031440701404c0c0000740003038960f070700b40303005410381c8034000c403a1445800050784072984506850304000340358148000305820000b1041c0c1101044a009100d40782c1300f6044100e0008001d404a54041d200da440c2400c503a4080f14140c0c0385604241c2c000e035007400080788805060150150b0094040c4002641b45400d00b030041034891310141d03445005140203201c1c415088100302007015840340381814542440050748451942c070403046074600f402c4021404501107115001d664007141d000324082440c03640c80302461500e602c05880b00034036202c0c020703004021003821420a83d074070046078280000c0001103080d541045905c100c5048415955440c0140010360700032481300b901940643c020083c5a081c100414140348000d0100c0c0101248840001e401c50505c0d00480180780d8050018860601c1d814406981e9030624041100072904081005400300c100c0394100c4804061848200441c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 219305854 1250 219304604 219304627
    0x8030306041503050601320607110f1503090105060316170a0c06050903060a0c050a050f040f06080406050a2021011403070e0c0703081005040504140f0a08 68
    0x4a06101c0b00560350014a0001c0400c0c418480a4001d0101d84080d51580701411502c03182c00f0340c0203076406c44092207000b0507443d03921000240e0300034a0f40542c41c0c0a16a648a000403100254006000d510507803142c1c1224060040002450198412a00a0119840d01020076850f151012041c0307188110b81c400c00c12040700d003c628680150503c0c000c2e81e88030119904c2d5454007880d290003800100e00006603503482d5007030801c84141c4c010082c2108000003084100010070a00c104032000c000c100b4081180b41080842004039401000503103200f0580302ea4580c4054140c00044905880c03161800d0000340d08001c16015000c8131441d000d071003400c2844440c040480981041000e00156048001c5e6120701003105500c56018003880800c52380208510410940b4100300350f00060f44000d444003d1241038401d031402c1d14006130781801d282042395500c0c03540d00c2e1380c1d08496118590140c145400d000c28490b90390b860070401442101540c2007102c03107140d803a6894808a200034000c50041111840c0413 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 219307104 1250 219305854 219305861
    0x1617070e0402130f0903270e01060e06040803040905010509011a040302060a0e040515120106030503040b0c210406080f06030601090506010e03010509030a1812020409020a05040f090210090803030604 87
    0x1140f428500003421408600c1c000d0484075040d004802280740018403003500c10089211059640d8003d01716040d5a0800f10b80e09800e12042c4103000601110090b1242e07182e07140c3e010f4802410304078003140d45590740d826050002c1d01c1d0a202c2c1340d0046c0d29510000c520301d41d800000c00c103501c012045661415266a00340541684031100007001c1002c03800d0030300301030b42c1d03180992409100189003d50284040c0c00c03c0050140507425540d070740360f140c80400c000066000c02510119494018001d86920008070351a051001030503900807a0103842840c04403014148011744150307859a5181c51660b1745d076800142e4001e1041e11030903403503445a0010003040f041600b040b640220306240920400c01c03200040781c03d49030700b80d40c1c03000707590400706892040b154400301e0702e03842d4a018141c2800790341c40c050009400014090001e80156280c001410664441c10b0003e00180301c050410004131602c1650b0382c0c0240404a8200d10400407207266241180c4104406000d0341e0200740070b1882c60302d0310020403004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 219308354 1250 219307104 219307129
    0x7050d0309170d030f0b01091e1805091b220e01090305040512030a200102120112060c05090627060c03030414010603110108181617070e0402 62
    0x8020701c0a2010509251520140b202000c080b401040c100303003d0340300a0f041d1030390881c5801c113680c900b0443e014680c2e400f0100004440c0c1705150072940075100d07404405a246a60441d40c004420004e00600c10031280e8041846503004d881030703c84d1080300da40740300d201c0180d81d000b072944080740d1103541c40c00541005150700d074407445500c0025400007103080e082c04d40d40400015004030310041010802030801c0301c52801c0d451000d4000d185001e96200c00502080c8003840c810200106115071910b4501096045503102c1030a184844038540c4d54450858130f4100501c01150360a06141e10385483d140500240c840c403090040c882403c10f02045960781d603482c00c007040000405400392242d840c80c2c0301c0c42c0007800c40d90039400140d42c0c0d0703107040d040401081c80601031008107030313242842c2000401c009414203c00354200b46848040c6071a0a0710350321465400d510130413054010360901c0d05451100004080c2180d00c01c4124602480520b0b0000ba120a621f105407881ea05920340003030010f25008036504c0c01c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 219309604 1250 219308354 219308357
    0x1080619020310170106050405060a0f030f050f0106090605010e0d121b060606020601031b0803030a1e0e030c0d030e060a090312020d0603020a090902180601231207020a0507050d03 79
    0x2d43e2565104007920713400b83c07034030300d1045650765a40512039030900e0300640d13610a50a94920540502d40395070351401e03507802d100143c4414041c003600340c2041800d01000c02c004803030f400288162074070b0b110004010842440b403940890300441c811030060804501c0c80700581d070051185149100c8104040e0368039006038600909201c440c11910000038140c0c45103402906031035008290960640c40c1032003071070013a0118040c480c0c1c600101040320b040e00200326940030341c101c84042862500402c1400c0e03201c1e00658a5400541040c280c800f0f40d07040000904000d104440446041900e144410303411030390b050300783c8502c3c3d801c1b03800003848200701900304914840c132a107044d903407030250003045034100e0308405a0900c0503600c6000820551900000d2000039144144041008540550000b16141920354516000c039100c80d0000300180e014072000c0c110600c42c0d007a101009004140c0c0a03900354001d207884805401000041002c01d48000f070420300c221b070310100601845040000704424030404800440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 219310854 1250 219309604 219309631
    0x90509100b07061506020307080904020a0c02030a030c030206060103062303070b030703060303090b0f0304140c0d06050402100206011a0705120f0904060b09013002030408040e010806190203 83
    0x348030461140284841c6002d54800030741d440181c0c00d40c229001041c5d000c80308652040c44024007082c1d000003111842c0e82c01f00c400581c0d50030885400d44070641d0307000001c0d6042c040c003c3e112040c1500070361880b4145100e6429901b144da00d540c0194111803860050361201c101e020f0320220307140010707140d0810901004080300d05031640d0f0002e080490b4822120000025140d11080040540200c0b0520103441540c00702c3d41004002c20b02400c0078040100301030664030380f0000300070034040700b03100b10010044003801c10000c4420074107008010700001e440881c0100b0325410700100d00b0344046003182c1640c801c034006d00d0040029040030b0500d0341004500741c4560041404107000c06042c04020100c40070300300d50213500c1e8000f99040000302d41c0d49a1101d02011002c024200880c0c2e403000c2d884040815030040c0c95a41072618084440ba00080300d960b1810b10b02c000248024400140060000c45411050140d80c2d40c0c3c03110041c5455090030f1310b01906503020b00c042110250f81d590040c6600c04c98056210307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 219312104 1250 219310854 219310859
    0x301020f03071106090715120e060703021810230c01050f0406200301050d050c031e0706021c050c0c032a010c200607080c0d08070f09050910 62
    0x206254002d45007400420766555800501c0001840b4030350384000807078090301d041e601d0300c80034003003826081d019441006011700403820300108130b91000c8a50719544040f90304608c1c09000c003400a6010071100d07040c2141d040d14154851410800a04c0410807a5898245403030014481056414510450941c0b0103000c0c003a075a8020800d124045c80789010414080c902d040c0780c1001c0c01140d081c4e1240700c0d01407804180d035440740f0701154102c90468206466081703800d030480c01e0403401e10441e0520107500d800b400f031441320000f0b52142031001c0c1e080c180041d40c9c18103944400c107076643c003000950308500100200b50480b015006002401070502000c0a594401c5450000a401c000d05603c565488904085281410707880200105420b05c60a00740098950381a4a580c00100001d1104e22100c0a45005580f5152140010b881d07000e94031546868886004038040381e12041c0720104500040d03110000503440da48581c070005411070568a0702006c0354207100510101c25001801c02e50f0040030385000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 219313354 1250 219312104 219312127
    0x60c0703260711090a050403082206020d05040507050307060c02041104180911100c0602180901060302040602060c0f0304110102120c010204030c050f01080115020a38100303030b030102 81
    0x2002e80702d01c1030700c00003e000003c00401c03000351000b60000844903d013034100070000e5004810a60081c441d800c010b05152070485580501c0303148990010192800411280d41d143c0e040c0d00082c0c040c6200e00191504180c4a4040c15502c0a10b4451000000c1954000001604169100d007002341c946013215032820361039180c00000910801188055560342c0c0f0b4000c1c00340425a43e681090000480d27203c2400110803500401c040b421210140c102c680c0094130908120b0858602d00c0309010160a0072115a075869026000750000d04c50302016000d04c7d03001074481040d0008944040103140300040c2035849940355262246500c0d5409819840f03680c0341d0703130384500300745001e01071040b6804009a610350551401d02403582c103503405207005001a001200310350f80c22100050544002c001c0103c0c1e40c0500c188200e01d44400c201c00034108465840191650741c3c030720ac00c0324409182c00d050680c461001c0c18580d90500c1412502000c400b0380d04c007405e00010388690446e68200c68001c1c00581450344000d103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 219314604 1250 219313354 219313357
    0xe01021e0a060e060c0403062f0d0e03092d06040b541804060b010f02190206071e0c06020102090d0f03200d030b060c070326 55
    0x310680307501040300202000000c0c09008820b8807428050122824007802040c114021400000d03ea15120030b04403035001c0072442d80c60421040312001c0c14005045006103140c2c0e601c240c1d0640c1407507040c0f048981e01050000101c0c0d45104010304285030210002081c0f0b4502c800440c581540d450001803d00d19a075903840191018000d50304400703503640f8000c03148080b542604902c20104100b209207183c520a00e000660001140c810001c403c00a50948208005c0c9080c00910f640020940c0c0e540e0b140700b04640c00f9a1046110321400c01c0a5250480151181c002d0342d511403005031710040f41e80024402c80000011641c1c4050006401e050705980c0c0e16801c420300c0c68810351040f401100d03035014002c2c4140510020700c0280021883c000100300030900030000004013a20f4040b404905808240c81a1141404810302a0b040d85120781c55800c4951103a1000f41403c0c0081d081c0255140365150a00c00c80e50a454140010726000b0314580e500181c551624401500030364501110350080d80e140340 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 219315854 1250 219314604 219314653
    0x80a0e2d010e0705190305031b0f030409020a030c111c0e0312070203010606050f04090902060d0509070510170a0f060f1403070e1608060402090d051507020d0f0e0102 73
    0x40103050520305010a1200f170800380d00102c25001492401080843c00120849500001e178480d4081101b895840b40780c80c21402c0c103482003562000240001d08121030742c1c0030344685201690706106e6080403c004664442c0f0000601c140d035041a440d00c1e4117240a00f01d07200f401d203054246205600c0000d0700090615100301d5140d407400e00005008411441d00317100304006404141052030400d0f440c442d080040c0d000d14025441040d0b44c1e00044d00c299030300c0388240ca229070100b10701031003140340a296241d1a02c61130302c10a405401c1482360b1400e240d010b81200c0c2369551000a840280b0b0340d60751001f102802c1d864020b900341607a9554081180c100b0514814060114140341040402400040c0b524003450365021480c0350100300305000400b0692459081140d29620304001140c40e100300041c000e1040112a44d4400d1011030300300304003c1e0100d88902ca1400310b80302d01484dd6500602687c0321641000c41c4400600b1200301000c0c280d001d0400c400e00780f0010f00c100c034156591060780850042e07044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 219317104 1250 219315854 219315881
    0xc04060803042408011503020904020f130506090105090f0a03080a0504030b07091401030b0307050a080a03030509030a0504060c080d3e0405040f02160605010303080a0e2d01 76
    0x4042c0681c03e80d0380022850b10861000340c3c400398800f46030091900b141030042000206050840481d010721030f406980011030001d0045580300401444000180e12158000ca0980d03844040005d070717854010181c0e03c1000701a1655441c007480c2c04200042c8070601c5011b43e500150302c446c040003044141000e060b111001da25665030755810b6003000d140380c0c003004288204206048006021034518281d100990300801c0c20042003240c20807000078104241307070b04816008240356000044030500020100c00090003518100a01e89400d0007194480c8200c1c1c01c0c002c042034003000108000c904c10000a040f481c002d0ba009404c00c180301c3d4180b42564a0358102281c120300e0411480a141700b440410081c1d8080500781540369030f40004034003940e00882c401c2c180314941e01c100780340b85000c840c0c04030351404c1d058937921950380d285490030100904080c0021790000301ca08000900035a114462100024014801020581d01403070301c400b80000c0c1210020041c01010090080c0d6040902980c000341508 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 219318354 1250 219317104 219317107
    0x15010c0c09050406020a111b04020c030909190c0912020d0f08120109050c0c0d080901090501180507050108010b16141c08060d0b0105060d0e0303040803010617070f110c04060803 78
    0x20458001d00e031014413070900c807030f5030080c1341644500c8e5a0508000e850310380560f400f580300c42d201c01c0303054110b0060041d42500017990b0801c0012a258144445424901c48101045910345601080310045002c0c0035124841799440d5046000d4070f01428928402e81c80381c1d0503115000354682da88240d80e04170a480141800d510070041c0007400250062560280c402d900c81402c0642e04c100d0b01d0354440c4981a1641401006008240584030a400c109546034010009014141d003a030420f02244980d80801c2e41d4601a012000c50290720840180d8121544907940c24101001c01800c50381811080b2000c4a21465a003003d04291005101500100c500708181240300c001c183e00140002800910091142c1d03c6814242c0c0040c07800c82019040da2816101c09859007090f200f42802003282e4880c001142c4000720400c010443e48000442c107969007039495071503170b1900d21030510814609031080703000719500750038504540d44695898101420030b00c049810082040d000308003201c170b00342c0100455400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 219319604 1250 219318354 219318367
    0x100e1b070f061401060806030a030305040606080a0c0306050a02030108100b03100f0b030106080f1515060c06070306120c140109091d010b0a0503070b0d060312090501031415010c0c0905040602 84
    0x81c0303d64480d00400703581c103000b01540b800400103612108010300080916903140c02060030301c2281d43c4820060a4106c3c101c4500403014240a0b00100305480116505030401e800100404d07060b009890403a01400000e0050840e5042100041c1182e84201b541501c160340c202008000302e07000d0780001c621401400203403c0c503a4018182542c0c9143c01041407584288808213011400064400500c85820100e0090313856400c20515058070106030180e02000226402d0755500000c10301e2409000a600c0030080c03035a84079508143c3c07144052029210394420f0908101c11841c00c69841c2c02100c0500d0a6004a5101c0e00410704031003101d0816444586281c0c5c64401c080727003d00c126401c3c0f000c200c41c403003441450305000a6490080d4003501008580206a41000d8005604881d01031a4090046274101008100c010403000c0d00e4031450340020b04000c034603c0c550780f000510b81c3c00f07081210312486411704107000640b000c030749804040307030708031181d071400288a0481d02c20b003800b44c1e00c607007030150f034811 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 219320854 1250 219319604 219319631
    0x1b0501020d050403090305010b09040201050d0b011b03050a180f0b03060402090a03080d0609091509020d060f0b090f040b01090c1112030403140f03040f1a070207050108100e1b070f06 80
    0xd901b2765009000c1c1441c00f0078040540c5e04841940d0381d620800c0c201161140401c40101c50a90010340c0f4103464100a4100b8004c25820501802c60314a1559840e1640ba00001001c4910780d040d124810040380184030510090600384000c43e448000504054507010340c00010a015040983c410780b1f20310300201d8100c4140220b801004010008188144a582260740350000641c0311842012205035850300d02ca411512010340c40020250001004c0041c0c29038031003200003500b02128094400c594510014040e2015080818001d5403c503541500e1030b820b2044040081026405000c00d00c00c81c1c403011084100308115095848c2c1d0340011070754480c1000c0c9009885a456100c00707170800380040c444401a4001e90f4140d0798401c0e00000410754296590501c400912184051054210811000c00c10610f0300050390307508854003039a500341141e0301c1c1050329a144201d4083c8114041c084004501c2452014074444400384c2c0c0c1105641c5401680c2e80ca0307110440c00904101c03079154889001c6001074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 219322104 1250 219320854 219320861
    0xc0b090706031d120702010e060f041406030906070f2312010f0509150d080c030306030c03070503191b181103010f030609140f0c0405090d1b0501020d05040309030501 73
    0xc400000f610124161016445802c940b030f07a4900750f8004145c100039a8800d0a40a40901d0f01038420b5a903144030f020700c2c10003075005014440065001100c09000c0d401c240084911030720003440a003d440c0c4981500310f4410018405a00800c20b65085e0000301000c55012a0403100020040780d03582d4070340d0000012001c0c2c05a0040400b039150304801c000c0c070744501d450740d40c0c0a03c11718052880c2e4180e00000681030743d002003014180c214082001000c4640c000021401080e00320304840c2481d140e0400c02d5514051400303120f4054002518002d020300b07619905030b5080b4850700d5002039003070700d07540c8200703034030440e80c0c00008803801c0c034201003050300c21030b115000803030140060403869503040c0404525040c1180c440100003940c1e44810a080c004032410402c01c007118142034441c0010300c0d00c8400e5454542d0781255100710320704000310341805c01c001004e000c1c002050720360f003103040480d50343c80341d011041140c161900d54003080308040c01661445400d00c1140b0944510b1207050031360401a085 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 219323354 1250 219322104 219322121
    0x9090307240615110c040e100c0210050901060315091709130c0e041404020f06131706040303230103020f06090603011211100807050a0c0b09070603 65
    0x45800801400e004a1070103002a104141c03071208400080d0081d1010000800c0c1661007a0f2105021005514107650b21842000c0102c69800031135001e0ba030701c4003c02c001ca81181500c0d203110b070300212900140d540c4941040d03c1c1c0741814015117500840d04668803090320401c5404020b036075076511062040042c070480c503400d220140f40d0200000d02d5190354103408960022170203003501001091441b00d1307640300038001000301c411a80501901c400703400d01618101d103041c201442a400d2000c1c0400820800b030681b03200f581c00404000701716084006004050f03104142e034500c40c800d40342012480506071800341200942c1038000b40107514042c180181210f6141c07220011070700c1c1b021501420b09001c0d840c0541543d0301125112429812000054905e00c614410190410f9021000140d0b100c000c220020480340504151200d00004208000d50820100c4040000c6803020000c118024400c10140580c42070301e003400d022a01094481251074141280c0d03074403607a840f80d0001d10025505001d40502c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 219324604 1250 219323354 219323371
    0x9050618070c0201030506060405041e0b0411040b03040318062a02010e090601021623030c060f07050a02040f09050f0706230909010326030c16061b0302070209 70
    0xa503060440c1c00501182c0c0c1c030b0801038101903c500100c0e00507a9101304541c01840e0042040000030212064031100d03a0100750284501480d0402d039841d2800c007402411400b01d40300c0750080c038103800d1440b80d007201c4d00041c0c000c0e0204502211245a80060214514013800c0b2940703506080c070300545001c0c8500c8401a002d078007148004100e40c40142d0700485080b11402c03044840f8102c0755034900040340340c5440c0f40c0300b007415404e124400286110090030001e03a0304905c40d583c610004081d1050540d101e1170580d10a800c41030070445140c0a9129202034804c05100700c2c2961820340c000c1e0001025100c6054050004503650140641044803c01170450031481c1d50014000342c074a4103002804d0224041a5129481c100c154040c0c0451940c1c0f00306d03055181c00403c0c44847e940c503410000314282c5c41d0790a0300b8600a0035102030001c0c000440569100d44506821145441007611080b05101d03021001101d0390794035002c071104122441c441d1440d50301d1072a03a0050716481d00d40104842d01001510100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 219325854 1250 219324604 219324649
    0x2d25050103061508070c0b070e010806032b11010f0c030f090b06010309020102070302180906070905060412030c0203060a020d060b03010305061305071512050705090a03110406030804090506 83
    0x802560f01c0310300c002028106051003940c82d43c4000060f1440442c401c00140001507000c2007065080e0848983c540e041c2c8282d0b02d529141e5142c0342070560b594081c01c410311000c40c119207014200d2801456624111155207005200809034902c090309503402d11000100246e1940850b08825034540f18500d08850001c900f1f000d882103c1c0c41c0c03854030540141c002410075840c0c40c904020b590080181d1030007540d001c0d00b141e80e04035510460048640b015140003046004400114a016200e14003840542c0d074010640b6160078900f0a030000c0d8507104490032014003464100c0300c00036a074140000c40c8980d240031005a07031450407131504412298150048102c44d82d0510050000c82c0000504035805140d0b00c05142240b1007a0a1540c1351103541e030b2181c81944c4041301d90342c20090740070090b0000c80c1d80d480d2040c020f42d140c0080c1507815000f04044260040760322a41000402e0402190000c10280a08001078447d02c075111026180c3c8503800c002c0d5065100c1003444114109803400301400c2294850070b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 219327104 1250 219325854 219325859
    0xf1306050a0605013f110c070e060109080c010806010c06050a0605100f0c08031f12020f0f0102060703050a060504020d020408060705030c030112061103090c10050307022d2505010306 80
    0x405d413100000c1d65040c10140c8205840c96064040c1c0d10000c21400c0503502d5648a03086420082c2e030700e2031030b809841c460074080c80c08941594002c41c10641581e201d0703800340000c6850700c1c0c011100520000e007058108280110440042012842128028082c007040821740070b061a06200c200d0041100c404100220280194001640034031851001948222401c2e038a0b00c0d4210b022080f061020141c0003900540800001c03c00d11115020201c0e5100761906001005d0f544104142032200d205805c0c0541c2205000540d1f142c4258000c3ea400b200c08040043d0540e11003000c035040780c00c42641ea0300c0c20380d4002024002c06008106850317102d402440e01c2459482d21040190103070106114902655010b04210010010030790060700191020b0341d10b075526031038020011070b41d5047ea84072540c051200d490305030695903c2001102d01c9a800e640041c148000d000350144170504041c0c00400030f031a004280300e0041032050000b4100c00c9088c1901c0001d00e03041c6104c43c01d03401362690003203051600e080ca08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 219328354 1250 219327104 219327167
    0x1806150b0f0d090218131416090f2702121b0d08040b0a0909050906061f020a0507030c0f0e0103020d150b0a08100609020c060f1306050a060501 63
    0xb101c0818140e82804290200ca500c00b080515040030401c41003510320b10108401009542c1c4410100c602505200040d15845c44400b07844221030048152000c082400c01c0c0000b45694014460700500d40c11700180098002840c5002228440c0ca0320001c282e50000003019032030440c00c81e0660048040141580c4c0d407618401c0301c228000704101d0f80c003400c3c0408070f500a00c003e140940700144050108030756144550000107051a00c50f0254071101450309001c00c03070704500007eaa071705c070300c0000d016800c060880c55000388954802500303010440c4a0300e803000740003d0040c0301440c003d510501d0401e41103802c095403020b0002c0103820400c0001004801040581d503503080c82d444040d0400f03101408198441e000001802000c5160f0703400000c241000111848000ba80c0030305c0d8540000308000280d00c82018600340d11482c0c400c601c85610200100b001001604011703a00308016100c44160802c11b035580a00b030b40d5040350414080d540e183d50401142d41c10584090810880e4040301d00700b6800c3c0304a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 219329604 1250 219328354 219328357
    0x1806280f2a1101110102040609260c01110f1b01020715020d03150b070c031103010603030801050415050310150e0f0423031b1203040b010311041806150b0f 68
    0x1d0141c005400400b26000b2a4003d420b0010000c225000940d03655446020103019000c4a2203003100c11841030400034100d0881c4980250801c030b1880c06080002841401110743e8500308901c00d8a5004049a4620420003004111213045a08850403600c0341e4600019041640740d6016030000c034542101c03107150359804240f00c0400030903410002009002d43c403174070f49500d080341c01c1640c107207000042030b00600124540300b400312440352101d0ba01d140c8410040c5800d0f1800d0707120090100e445200140154509600701c07100c11000004c210320f4041c2c1d2100045d00c2c200e004601007000c55034071041300004c20b80242d0a070019111040d03550b88141424a9031501c00400200003410070b072030f0340080110300c00c000d588240c400604203041740d8035005104000c00a1001200201c0f111780701e10480942d0546603c1c09581c4200d4000b000000160f1039504e0301c9814101c01038407a50300c507640310501c041190704010f00c02d00d1035000d10340004022783d4512242e001d4140310b4000101365042070058800e1300302c4040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 219330854 1250 219329604 219329687
    0x60803070b040302030d0603030503090f010209060901030216060c17060a0302011409030708030a050c1603050a0803040809090f0103020f040b09060d020f06030405030306090109021806280f 83
    0x741416002c0e90380e030078100e0035401000006c140c1e40d41060400024075074080081c50081048034140e42901d440700070b401d0300301d00c030303064100f03030003e0040c002900340d503019034041c1060408079030082ca01100155200c0007190030201c007100c04100602005042d04200a010544c000c8081d40c800c8149802c5070006800c54280c3c8800c1c0200d04d0002888188035102070004038000c0886d081183d448084420019080742c00c00a64551240b00d4080703900040381002282000300c9800c07101500100550b51144181903100604c280c076a04410031000300d090705c4400713403240b1461000d02d0407602941588100075004c010009000c2c0b0440c20306070707010503943e100c4500c3c0c0c1d080441110b0f8482c110849202040700c5016100003281d024401108000901c2404402140320740d408541ca030307000d0380e01c0340e46120032400b440b24840229840034980c0c1d1400c1c100b00009160074028804010040a6102001414161034201800016003034201030390040750400c0c4c1d060300c1c1e2000c50499000c01c49980c42e4502c101031090707 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 219332104 1250 219330854 219330863
    0x30908041206090203014808041e0615080303152103070c03020f010504060f03050c04050d140d0903020906040b04090203191505160c0227061306080307 67
    0x480304507041041030351048005540c041c00901001c068600c000503030704040094441080e014030859460000d5100304a4000d14040c0300190b070795411100d0848032100010400c88d0248107008810703e030302c0880e8058119491080300301107110640f0f4540039111104a920810f00e0764001c0c4188030b0605507042e41020044010b40702c4210360f00249400c1c040c1000302c541c250905020004001052000d11604c3c030044d20300130380d1180c10070f02103030380111810300c141e1017480001240c00704c1c1d44403024800d4200719000304402c1d4025003003548034400100c505001c0c0c2d6089494010440ca60541100140310000f000c080c5c03414241c801d580b540d000308a0f241d200034003041c4543d50700d10149006540b154001c00341c0c250003034201ca1105004613018101c0c00101513003a00c4684406c01d60b0504078880380126440f039641140c50311554000000c0a69908803003980803a03100c00f00d04c119114203590010034400c02c4c2d8001100d0181810a8020300510144580f802c00c8043d09009042c044104000304495480350b01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 219333354 1250 219332104 219332129
    0x8130f0303060504020d090203060c0c030f090f0a080a03020c0303090a091509090c06020106080a030f0f0e090a060f0b070c060c06061d070f031b0c06020d0507020a1203090804 77
    0xd103401c40c01460650851644030703102103120203060034141d00c0059258800d80c00c694942d100c64000c0c1006018068402d40c141d8801c1081201429110028085498001d000c0e00b00c0001da61002424160464001002a902058458092690400048805070401c1d0080c503c1c20704208042038060541780a49a21540c640800b0810242a100f403140188658442044441141e2601104142c001d02c5032200640c20120089000c1c1000b280c55814590305032104080e1050720072060300e017240000f14203001c0c8407030004c81e0181070f202c034801c941c4143d011b41c1d000222030741171900d05d8841040310f8004040810003802242c0c0000d140303030601000d8400a00706024520660300d0000003074a0190000303040704001441d03484905200240f0f05000d400380340c45051204c0080d400071000c0701c031000c039103099444070300c004035019500904c1e40465090190202515007000c00c3c80741e105a40d02903a4010069120010200511100446820300614140b07801d20540381c4070707100c0c4a42ca000368010b140c01e0703000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 219334604 1250 219333354 219333383
    0xe180601090501230703030e150708010504050402180f010602160e0f1b1215011d060d0e15010302030616210e010915050c07030c06050a06080f16060813 67
    0x10b044d64100d25500d028413100d50b181c1e66860002d024215100f0304080a01c0303014501502640207011091180345941d480648603031810f4100809010b0140043c1c0c1c00024034052451807202c0d0b0b0441a1051100c7d140d20760766945464030081c600300800c1c007400b140c000d0361801402380404030b00070030303402107039032032502e81c094a07151201001200d01405813100e031070700003480c8400c6003001c4940c40d21a00c0594000d03220403110200660780d40c20540402c2002c120200b03004000b81c64802c0281c11011a142070004850b800d40c00e1042c03070700014101403145c03481c01701c0c01081180360402400364003070207141c00c01c0d13000311400101600c1044a0b5036a6000301c4c82a2254441c0080994002e01d010301010300280581c51050501119540700301001c80e0f1403505207800a1101c040044c1143e60580d070581c0c0e9400d0080c029220070740106406003111008541320345000400c100108429039012400e00301034082942040d942400c107104546c011010f00c02c448003000400300d110080c041c5019000010742a400d04e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 219335854 1250 219334604 219334637
    0x6040f0e0604121b050307240f060302120d09030b04110619030b061306080606090312041701290301060f06020d03111219090b070e180601090501 64
    0xc0c500e0203091544501010003090000c440340259904400c0c0d252440c841d0a16603204882410329a0081c01680c170401c0303541c0024200d11156a141075018054100303082d000d02c2d1144c00d8410160341c2c01111510381c0303030074015403904810007a08952600001d20f5000c2a0a40c0680444011b00c401b80020210304001014010810b4805524507401080c2c60340d00c00040c2034499089000d00c0b03580303000a240480006090604404560a260112204001041c5000000c80d541d690040c00d075508240140103190803034900f0040440c0c18140b10f0300150326942820b8010089600c101c0b50f6854503030400c0c580c0c5010003000c60341050a020000c0224000042c1a00441d014001640c40035042d60000800001c0c195800301e403039107640d0300940d0144a03490503049030502c10302031180010444007040000c180c3c1d00c8071003500718141c0102c0d410007191040d5580c0f2051701c01101101c03071202151080b900ca42d41850140311440301071014040401150820b84d000906200c41c034041c89040c405c0030380d50610040e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 219337104 1250 219335854 219335861
    0x11e0b0a051c080c01050c0a0201051303091707080102040b07021008130b0604090f05010c021e07270e1501090911060d181124031f1805010311030a0201050306040f 72
    0x154113141c000d00841c188000442d285900c902c40510040d46803c01044284500c110314540c01174240d0f580200c03090801040e0321079100c280318102c00d18401d000001403410b000f030001e040242215029261610f00f02d0050040c03146503080385104210300142000381c4400243c01240526070042d02c90110303684c0380030225000701070840000d40601c040d503244030704200054000c400c403041c0d258203031141040e11051001840381003600720b16440e08440001d2240f05402290301c072100801030a41c0c0c1e21a158024064102c811254060b0301c40c2c1c0040100f4803515400680407401407000714020800002c07252200040200b0240c00c640c07060a0010b4210f480384250303085503801c500f0602e414424032809240614600204100c0c2030300510070540f040714030b140100120211058076010b0343c0d02e5075840388080341c018282442c208a11100110021404050503021000b910301d900c08001100e50460800384030380b540181416200e503110225000c0184d0340501920341050066030042041290b12002c0c0024 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 219338354 1250 219337104 219337117
    0x7020402070602070606060207050f0d060e070b18210604031d040f02090f06090d03140d0c020d0216080a060f0207080a170709030c0e040c08011e0b0a051c08 69
    0xa0b0f0010800c001441101c1e4030a03000c643c0181c01f151103484d982d07400c0c000041c4180065680c85115600c04001144880c0c10248400800c50140c2e200c45481e44c1d50010543c12902e83c00041c044a0040141c403400e1119100c07144c00fa000b1018000098a004410340d184001040102004600c230041800f02010682c031502c66072000f0000e110100c84d4815943c004c1d007100b0100d511591040c892600700c1d003400b0003100d00f41200030340000988480d03620160784a085903004085900700c00c00c009818800d451103204005106980644004070400d08002d240c40c4117510f40c2c40c00141007842c05c01c00c4200014502800c03541c4410081020032030010440028000c01d0000313040c1c3c400000304100c100d40e00903103540e1000041c2000101075251458120b40d078107000d00004050354a1030106101d141906241075500c14425440800e0481c0c4408655094400000f00a200c1101309120080791815600500b89031100039121403580a15100c0001c101250010b010020812080c00600030700c2a890111200c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 219339604 1250 219338354 219338363
    0x1a0703030b1f03020d0b09010b040e1302090f060906010810061110020408070501090e010501051204051e1608150c16050304031b0b07050a0b060316091407050c070b0702040207 77
    0x741c040b41018058007030762202141c900c40034946241103a40d490459003582c143e45040ca126030815007002c20307019101038050170414402020291400050340c40401c1140319a015900410701400c0030b20510941ca071000e081c0c581032104610400000410072040e00084a80300c0c540070364032030f0744c030380307c49081c810100800c101c010700005020881c1031000514130301310f403800e990f82eaa82984c0c0b1050035444505c207000301400980e0401c484a58408801d02d0140c11600900903a410785401038407004203041e08080d61041608940c04288580e041303038006030014500324029080300030318544140340d0311200915040b100500800c0c2044404104175400300300d5988002120340e5141c690801c01e19180500c100082004d485000100d01c4140e844290340703c4036030207402440c0d031466581c1d034040e004034014a12609031042d00300d50003640c2040090308000f00920900000c00315042c0c440c291070b80000819117818070408000c0d0070110180015040e00f241c4a0000c44c0e6125032a5100140280c880c4903000340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 219340854 1250 219339604 219339649
    0x9050303031f0b0705070302090415020c010533060d1d011e020703080604110d0c0e0a0f03030909050417070524061c0203010b03030c0a0605011a0703030b 68
    0xe10140900c400042c0c40349880b000e642019540c181d024814410503000402c0d5800c02e4000b04010305050640c02e811600c80c00748103002450b407182e010100e030084202c6080aa444000b441801002410f002440c01e0030040740c0007410868500701304140d45403101803070040c88000342204e0f00c070607154000001004106481c079420740c000016103020b442c4015039000001d94040302c50403011030a100700c42e80c150b0306413140206903135a4410031000b400381812032842000200001181e41d455071060700c2800100b500e45003400b4150030240221001c9980041c540214040f0046c00405d800c0308040d400c684541e50089655911468a08010380d01240e0f456500310010511100b0008003054201c50420285100300022205c0d441d0000794800681d456504841c14003568102030203664588046940082c0001c2400620503020030b2540d40b04040668040d0403021608080081030701402d40105184200c481e48594030100400d05031142c1c3e48001d007855622801e01c896901c0b1100030411580d804004407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 219342104 1250 219340854 219340861
    0x30809010e0703140f1f0b03010f05070513090c0903120903060c09030203010c090f05190f030c082a0f04390302130b0a05070803040804030b060f010815010905030303 73
    0x10b450784e4140d441505581e00840142d01140c4c4000100640035402c44402841400030460840e80104404481280c0554031880f9000130b000c0113000d0f05000d4000b0784e03210342d82c4083c21200c02c0c05008054020162080c01c1000c1c00f038049501c1160b00d810340c0d420150341501007008800990f6441f04a41c001001c00b401c0c800406640d540050803c821640244c000b407104441280c01100d8800b00c90040700114101c500d0f01384442e041042020300f124025490030010140c6403413080300103240a41c81100c6007501490f0600040c8001d110030940042d01c00c2814070540b404980340508000056039150003035245415484c0d03e50b840740c112290039000c2d0000c12910f2504a078000e94503920f50640154420350019050302c0140c0b1031320840701c0b007180100d8028901070034019206490350007000d05908104091180c640031984e403c0c011400340740300b185000d650314654581001d0004000303001074030920382c0010308050b50340c018030b840340c0c4501001c03800307120f03907848600585d49d1902c0341d0840c0b0741510010040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 219343354 1250 219342104 219342113
    0x20108100807180c02060610110f01060b04030c0f14150d05040b04050c1507120509100306050907030c050d15120f0b090f030717090d0b0f0601050306030703030809010e0703 76
    0x80ea450b84101010504c80700300441c0003a41d50702c40c140c0b420350b0414014281a50158403030780602058100300407d0300d09420b070038032285081d50b0841c4c0007014100c4c00001c0070004c22080494040042940001c0c3e585043e01d00342c0385507200000c00c25118000c013020900411241515001c441910350808010083c5060074108030079020300466044442c0d11a1747c840d07003102d150032105040242c4180d000b840c504070302551011600020380d1000410b000e07061000c809103a9400003130400320a1240d80004415142c64100060704102519210625103002e081209590740081215101c0c58455000301e4000c101054900c0304000340c1d4020301d594103105164104204600003045aa540603400110103a01d0f200011920b601da82c4074070001c1a8820049080014560317881301d8020201d10601d01d0418660101003210481c2d01d01c0220303102101d840401c95550385d01c40070f20350410030030320b00341e030a601d032032800300742c4c2c0e100180000b0f4180b0040b1000218101402d40001301512455420f551045549281 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 219344604 1250 219343354 219343379
    0x5030a0503190c0f180f050f060c0a0807060c090e01090b01090305011e0e07050d0308130c090c080a09020a0b071b0b0714061501110a0b15040e0a080304020108100807 73
    0x206100061540000c0e040b400804404440540716200f02c041100d80c904010031108d00f250f0189070307401446c1030106c0d401400301404411202405002d0070341d56003032686028022561107640201c1405a800b00c140051403120031424107460203a4000500d1204180c01a5840c60ae1540018019801c210005c0b602c0760140f180f148440b500b402080c05038520300619140c403481c0364010340d9000402200d45e0004070348584015608140c0d00044400707103600e02c1d00d400d90080c1107600300600540d1940d9031110b0311a484007000703502085ca00420000150103a0008030a00c60f944180304c03a025000c103a10341445000d041c0000034454a0003a02d9200340d54186050040c0c000c000140e8410300004190001041c02003030161151804e032203411100b0310604010348405024401308a08ad21035480350b440096541210140100d1086030704042003000041004251003200071001055081b012040b00001c0220050340e40007642424800c41c10b680782c0250800c004e84c0ca6224540e18854900c1c001003500340400c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 219345854 1250 219344604 219344627
    0x6110f060c130b3a1415011704060e1e010b0f030601060c150e19291503030c070b0405011404080607140921100905030a0503190c 57
    0x314a0720090f641c03416103080f03001c2c18464071200c00d490042483d401c1e02d84141840100303000c000510301c041e94010040d040310450000f60001c0d51074031707040c800301d103040c07030f4003218a0202442c0c840c061075238522034103840180240004180c240c030303011607424580c0180140549a01501840d007040400c01c4032a42c042c09640b000e080c0a40410313103400416080108126050755099207810313a1300c051a0755030509009840102c0000c61f561000e03401e607501c409100d025406540004800241240e40c10014160700009006940c1c8110b048290355604a81c1c0500710750154209140b00150003510004c44e003184180c03030b845203260241c1f8602041d010082d03c050b0061355002c0c1e80f031001402a554801e403107481540291411035202c0d40000720420300c10301620005411150140703042001c0d080204401140718074014144514010f4940051902040703540c59040d020341c800d0009400c10b40703841c0d0f1203105410b43c81082286c0080050845004e422031030710162084c0c802000007421001c8018058003520 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 219347104 1250 219345854 219345877
    0x306052701060807050f07060f0504060b0901090606270317030103150207080913060314010f0f05060603040b04030e0a0f090e070605040b07031b1112061006110f060c 73
    0x10020402c1c07842429142e11800c0c0c140c4440b4039242140c00d480c2d03040d40044900301ca40325107034103100282000034000c0d00d004a12442001c200144004200070425205030403004040f80341030000c001c02940040e42000e90014520480c80800c5407584c03c48824050790400380281a0300d100ba4681300c2d05490046040728000c0f480c211064440c03054010036440751000241480300c003031002c210380b4544042c1c52400c6003603d510000b0303000c4e9a5a101c003a0b0100340c1c0320030401655aa031544e00002d800b8090000b18034942e140c100320910f82940000c000d4080600094a20b4030004006010180140701d1040d82c0c102c020142c200560392914407141850745405aa44543c0c1001005140072000003003035019568140c84150416007080004920385d008040306808004d20540e901030504507546040c007000c4c0c00f85812501811083d41031017030b1300180710084041584101c003000021038604004034162402c80c43d100104201e000b403001d03d440c9910403480042d0048000340074041c0740c0038004100d100c10f030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 219348354 1250 219347104 219347179
    0x10801090c0801360b1206100e0403020a060906060f0b0717160204090606211a0601030e3406050d090f08070c18020414010f030605 58
    0xd4004240c00d035521022080042418a8014060040c0b039045400b40d035918003004440000003103018030040c554000d81c81c441d040d541e200b0441c0d5400c040920502d140d00f618000c050034141030403508110320640c400e0071140c6900c1030209040501c00d0100008507900428180324a08641c00c200c0000c10062140491a9a04e810001a001503003000e540722560443c3c190700c080d1203502c0c2d0b41c150b80e602041d54120399009030440d0b00016074880c030600c8611406040005007460a05e03800c600c1d1014400d6690b40419208444035000801e14003884003419401140403c0d1521030340c00581c060291480120910f004d1413998020b1401c00c4036802048100c02101d841100b800c10250b40ca412045003e4140091010001c01400d154207800c408140e074421102c0551071f10141e21004e0149c2c0040d070084030f62845520081100305403450350350403140d2107d0002c46c5002c2c23a00310000740c901485a0014188090701c4004492036000740d04c0b40c4000c181c0900030306d40384c48144620149441c61034044402c004030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 219349604 1250 219348354 219348359
    0x6030705180f090106080a15050105030703020307030609020a050a0b030601020c01111b1c08030106021c0906031d0d050a080c0c0a020d08040f0e040201020114070203040b0705120c0a02010801 84
    0x2000d48800c0e504040c81c25508041c0d0b102e0105101003001c00a080e0900c0d0b640300d02001132054020405d50140c1d42c026440c8200d00c005a140420965406901c803d1180c0d00881090000d40d5000c15210105c030342c80100010a03d0640c0302250311180250310503a80801c001e040000e52403200c3c4000c40c484c81c070076405c1d14694005200152055982e4010580ca00c0e0702c401a040519a034545181d041c00704010681142c1950940d410702d08400d050408aa01000200041041d150104445060f00454164020340f10309032100040004800d840703600100358035603860310140300100d152101c00c101088190f8a01d40c2d120140600260b102c1d101000010b80b4240000790680200029698403255400250170f80301110340070089114043d140540b0901d2082000042030180c18560ba80100001488520f0310302e0180006401c42c0c5c51141442c5038110030a080041032580842101c00f0f0302c032800005501e076251410302c07510340401d034401d120840c0740000317001f4401d0500040d4800068802d03a80c031401681c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 219350854 1250 219349604 219349609
    0x306090906062108031932010803040312050d0902120106180504050319110706020105040c06020a0309150905040519061e03020105030a0b091302030706030b0306040f020d0503070b06030705 83
    0x10900000139012000520104408400b40744200150701c41407500495080d0400c04405503802e10380d00f420840304501040e085804142d10380150042508001031400c04e0301c1d5407201201c4011443d0b8150401900242d41c0f00440c41d50b5001c1c40500d50003a1038414030410507200b02d402001c0501038421455101d40800b8208002400340d180b1655105d4041c604102080c410300074034071400000710062240e4168050400c5d04c08002d480c004184170760022986061500b4041c4000c8507581107901103401c040500b41c0440c0c0c01081003000c849004c0b00c5040801c0819104441c0c508594010700d40c814244818411240031400300c82d0480c00c40c0300c10410000307a95820342c0c0b030351110a0300105e035040040c810404c0990301407c081d5510218040c40032404885101c0001e400313003000c9510020044640e01100b041d41020001c0754098606800d08001403d103d0300041c2e61800014030040800000038040c0c001c40d11013842e00200541d1000c122511910300346007410542c00c08403040c6020340306803070300084d961 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 219352104 1250 219350854 219350909
    0x18180e0c0402040b120615030405010b0f10020d0e190b04050a15020d0e010302070c0806040b0f09070e04051501061e180b160b011806080609060f07030609090606 71
    0x1244a0303608585045a407204517800120020003156100e158000c5822141611000461103644a40c000181c491110010408a01421010580104005a42503062036000140045c51901c04d04101c400000d50300f00180015542d17031b00741c180690910b007000840c449200007800644608554481c02c107074071512800d00704582c104042c4d006902c51001d0b100001c0c00360256050760352040c074000d441d001c2c0035141d86180030144e5001c03000f180d00c4030080206003c04200c5254101050080f00e0300d9901300155215903e070810301841d141801e200b8049820094100310340100340610103400d841d03540c0c0d101c030040c0014002c6803100340320784000b10070f1455032442030450007860300c40c0c0094100100e082c5080450f080c0c0002950254481183c3e0080002c00c4065070b103e13008001d2559502540643d030048101910020791101089500c00414000c00b480c01085155001c0e14482d001e220329616290114003504041d400047c6082c034180c03d501c00e1211913040001552107030074070407040c0301c000603d01484 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 219353354 1250 219352104 219352109
    0x60206091504150209180702100905100c0216062a0309060e01020f0a0605060109050d0b0708040201120e0c090903130302010f0e03120306040501080a0503030718180e0c040204 77
    0x29044000040015403c0ea44040f0700c2c0e118814014189410040481c00b07091201d4844c680300480300040040300f52341004000c4040b0312129040c080810117075242079450220400400907540ca82c1802003805208009180c0c401c0402e403030700c031083d541d5444040c3c042c004c0030000f541010b021624449851140c4218010007d505a540f502c403d484d04000311100c0500c8106141103000e1008542803081e01040125007250062000150300d083c02000500401001c0d40f149000e1034031022580c1c041307510b80740303d02c1d404081420160403d42c1c980c4012a801043d2010094005280281d007034401d10001403a00e4507a2410f031466070254403640d00c4c0703654a010791600c801c1c04000c1703003030300344010b5101d520240310000791401e00d80d10416805000900b808408007034114010408420801c81c1c1c50039025040c01400e4080c09070800c10b480c1d480b555102e100080014042c403c400203030881c641204083d000042c020911455045010400d00c2e002422141003503030128407031207400751220b181a200b00d504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 219354604 1250 219353354 219353383
    0xc03020309040b060f070302011b030b060906210103050d0201140402031e120408010527060a0207150e030a080f0114040f060803190f090b040b1b0f0706020609 70
    0x8050304501044090140c0903007258100d6802e020071414a50170002034881d041c802e800110b50368607001000003041401661000415041068046083e00c0d909c00b1500070700c005039100c079526540c90038017580c80541d880310848881a4800008144040451310401c00c81c2590b0007400036843c0c611041c2c614803800e44020307605800c450101001800704d80100b20100a050040d100e90940340700c185440d9030481d81c0821410794440d420808482c030100607818030003540182d150845802e40f141b40e44c3c1d682c8010800880682e001a0801c1480070800d42e02040050510050080a000403111a180e80056200c1d501280105010544000400030b5131411b843c51021700071070301f03002d61040201800c070007046c2414580d45c800c0086083c00c0184018032446001c9141550b0100c813220307004040c240428804030400c074002c0300900c40b00189500320340c03c0b529884030107a16203210940c10101200000d410360014416501050b1418030042103800c102c52050702620803590b80c035094591640c1500d000fa4a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 219355854 1250 219354604 219354607
    0xe19060b030a0506031f09031206030506060904050c040207030e010e040b151303170405031b06030a0b0112050709080705040e06220804030c0905180a080a1713020901060c030203 78
    0x1444942c95038042a40034070b0080c02c64030520002040c00d844481803c089075142a20703101100189604004201c841e10031102040003590b14548446888440185c0464410840000890240403040190b0803064070000c104540d1541c0c10300d4054440c4451034500c0c1d002c141d410416505030319041c4140040d482004d0030181d996600c582c0f40322000d40c05041c68a1108503e4800400400d0b0a02d072032000300100000c0303003a9514100700405240550038442c00d000603484030210040e07501c85000340c03134001340340e1303440450306010600060b2455217202d600840e07424035190401c41e800d0f034419402e1080b0307200c1e02c05441c00c660b107271000d00c000e0f40c0a1014644059102902049125044848000c6041700000c0242809480ba03075030110103600561041c3c40c1002c45090600144101d4810345801c0001502d14100c0c118428410301e4444510303080251440001041044000d40540030f03030451903841c0c5101c40384514100030b107803042002e400c900741e00644914001190050003000040f001c2d075016002075 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 219357104 1250 219355854 219355861
    0x40608030c07090b0a090510050108061903230303160908030f0412110904030c02030d080601021f0b040603060e0c010c03080f0703020702120109030806090615130503070e19060b03 79
    0xb40071040c02081d000300320004002811b1a0610426001d43c2e5440c4454031050700c0d2400040000c407020301001d2007108000880b0f80b298103001019801c6aa0020104003d40304800c25464070b0000c0720301ca440580400010007074042c1142003640c0029415444104081c0c0e10b4001c01ca80d2030007400b20304070003800200300c01d100880c450500c1245540c881c040004190802e200841c00e10315040e10220701007480c04614604625080c030694008454171b00d040800e030b00d86500002c1d61156200041c0d001e001c0d81086a0b003a40d156908a412080000360080c04055560f05d8030030010641c104106810b400380c240f00c00c0640d803040702c0741482d068059489580d030f13458110b0102441d060150441c01410741c00c100441c01602c49600c80b5103c094601c0000840c0720b1503086c0540881e000410740d9204107080410044c0780d41d200702174000040c8200c21225160180c100c842040f02d10150495a45407254080c0002d9004900d500c5900c100b12038003e10030700e40021581c0c0000d071421402561103201050001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 219358354 1250 219357104 219357119
    0xc140316180f120b09030f0301090203060f091005011404240e100804051509030a0c0c1a07120903020a170307061e0b03060f070c030203190806040608030c07 69
    0x494403901d4504110300311203075036115203103080c00b0103a001ca054607070280d10190500010310542d5134007068140155142542c0240c600f0301c5880140128001c280e0302001150003500d500403c01072104020b0030a00003400c01c042403038401c0f1402d200c1c0b240021400c441c42e004409d084001d441c1110054050700906011a0020600c031040007081c41d41000102200112580d03641a8007220080207a2580700490509041050600c0c50040c09519520440414090825000811a00074420500c1e15000c2d90034545081c108440207640440c3c20382060960441100e20108010803881d48500341d000b841088800c019218886244070103903001d0749001c0104001114004c21248040c8840140d81c50702419075619011510006d4003c84030042c281040b00c0c1c80003180c4a00801c2010031801400d4074078240c03011001c1c0c014020714050403c070200140404150080064074900d8821030a900b02200940d080104415030445140b44514207002c80040c2805c0040100c50018060401900c06141030440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 219359604 1250 219358354 219358367
    0x50708010f2c0a05100504060b060304030905090c1b100507080115050706020415020c24090f0103060b0307030b0a060f080f090709060306020c01201b120705010c140316 74
    0x2c41040c0c0d80a00622140060014010403d468034503800009980c1000e04183c8211403948580c140103842c03c00a00000c0380c2c0000d034070b108880f0300711940540c943d102c1d4903881301da0203502c00c1c1c10b90072a4020351202c22104d021800f041d03c40f006c04801c001640c0d4104088400510038400c00c944039220000385400c66101e400100101c0f4007421015180554810705114440c4620151030016000002c0885140c54800c40098a140c45075945a040d003c0413443c1903014401c1c004000d208514501c0b01040d6a4000e401000007011021100c079101d00d0240c40c040c01403d218980c43d8450707002880c010416900a00601840044542e5881032a5540140038144103401408440c1c580c81041380c0091000301500804002d0b41c4240b05c00741e160034020850b640be40d10a510f4400c0003406210341e01001c104100b040d00c06111142113905800c0003001240f60400c01e0344440321483c104002560000c0c030030150401d858245550303072921600310360b840390070106d0b000940e48620b4000d01e07040381d000140c1c8142e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 219360854 1250 219359604 219359681
    0x11404080106033026040f03090623130b0f070c0902030112060f0605092a07050c010f03020d060e1603090206040501030b1f0f0206011706060103020d0906050103050708010f 76
    0xd41756500c9803004000381d40c258112400c42d00580840048820540d01c541028014651783c24010261080f43c4030716a880002048048032501004c190030f122140070707044400041c000d05081c1c40d614401038100e10202e038002c02d02510b41c00000800060f40741542d03c00c5a04070390901d40c0500c0121415907503240640b180d000c41d00b0f91a6220540880c0c1d42e624488070764001ca19400d90340504140800a01e02c01e5861200c3d50307101d0950500008010540200c1e0701000d02e80e017460280c0b04c640d00300e03070181d00900030a00c400c4000e52030044045804411842000d005a1240c1035207187c25a44160440c01c8d03482e1886d0082d0803034002d000030820789d4020f41100c4140440105a030b5400c4102811803420078121071410800074200003114003415130103005290240001d20603910600b2002c1c0b012a42e180b001910f51410540e001600c0e940301400c41d07115100302c81d4084403d01a03540d4074107041d65100964000c0c01c0e200d510b0003100d01d000c40114825500012901a24000d61400303a4000300410341e200d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 219362104 1250 219360854 219360887
    0x509010207260906071103010c020d030c03060509040f050708010903030c1d010c02090a020f0f030a0e0601030503030f13060c1205060d021e0d0c09050f010603050121020114040801060330 82
    0x1070000c0c0e16687c00e0241c81d000c50342030f84c020030a000001c00e0003410b440164001409040c6043c3c410300490b110380040700c1e8019008640300348150b1803441c1c010316000e0107600005165180600a100309541600540c44420a66641402c2050f0b04d0080e008086040700301e0380c0c08201c2c240c1100740142421406503504c20849500141004400c4045605d00e0348281c0d41c000b101c013000010441a6555445140d558460100003417441e5070441c1c1c0c40550320310015040b045143c1c00940000e02807130740728454075110780c0d00c05010b01c00002049000b0740000804040810002d0420340022894202041c9205005030010408000309030b0901a003003030002c040c422181c10411030000600425840303201c503c000c0c1041e00c0c00050b1450030303800400003c070781a0070070001c05080000410400000b6954000800280c440342443d41c2d00f54401078034602842d05080004440c0420700045002042d4081d0f022a4060303002942c8100481001c40300110200d00980b030309100504821030014030034a0218a41c0594 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 219363354 1250 219362104 219362123
    0x2a0a1502060a1a130506090a18060510030212012f0f03040507030215210c030f0630100216030f120212042306060f0103020409050901020726090607 65
    0x2044502921240c6048115100d106004450401f554004d40c0910110820820f4445894042102e08041e00000d8801394840340412050750b400d249900003140d00a10540c00c0d04100b40f0000d02908100e0503006244804a00c100c1c00c86403001362010200f8200e00c489407424ee132244140320103400150055a0610410401100603258003400da01c141501180064444652642500c04500140c4618120190407014000302c441408252504102240b500c40030320f80d5500e021030005500801d00010203d6040f112600c810750780204405e44010400503560361194013540a0282e109690302c11655031110040d00001c07901c0780c4411908020949840c605a0704100e1040c816a000212555041c140400c01d0000b0081c18500d51440c240880c01c440c1e44420503038084a4440c800100164054211000340d10310b1684250b048501412100701c0802c611304084203914000d401500302203c02e400f01180c6210800b0b052002106103d105840051034a11220103002da070340c0089404503031582d072 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 219364604 1250 219363354 219363401
    0x1106060d140303010b070b01150801090b010203160b0a060807030b0703020c1f0b0109050f0d0312020c0a0c03050f0f030d0f0905010219140903070510022a0a1502060a 73
    0x702800210f00034070001405645a202c1410011504401a4004039000120a51501000c2c3d00004130760f0445142c880002400c01c0c014006030308503c034405e2035500e11260b5401c10300400c509003100c180501d03500e5808100381611854000d41d603815900010f41a103801038002182c0364420f400901060300154103440070104002e103a00015500c40125100740c0761981640419568400541e200070401222103141e0040d4031004540c0c0001a14400b401700414181d4130200328510307030100e07402a20b06904440310a1a1030800c1d941c0e90080703010442e9640030740e42c00030005e100d0001c0c2e803069a1005401451401c0070200c3c0d41303030003000c07181920704543c1d44512510001c1903003071007d040107030070000300302051000031300000301b56100d10101484c55080902c42d41080d910000741f00c41c103540c02541c02d00d200600740201070349002101c0102100307c0c010003441000d03c0322101c0388400074a500780c0e04002c82540700c18610700300b05500d555400060703000000207450341c402c41d08900c02d800700300040d9120300382 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 219365854 1250 219364604 219364643
    0x6051e040e0a0f12050301050d020d082101080d030e060114031c020c04060807060e09040c0302150c0c0405071707170c090307050a060e0607050f07030b0609071106060d 74
    0x2c0c441c00140c80000c64908800d0500100c80e1240c442e54941d440c0072881d40d0b051800044070310002c00d5010f13004038007100401081149040c1188d0324095401e01402002011040d0302c89100000d005d090510301030140710f031038014041c0c024505541c03200d174042d10f680ea0034864004a910a00440c0300c0c0d240c40f440c6407042e00a0240721880041200c190301600c1c90109840c144015240711394000c605a5000190800034503900102c4212000c100716114038954460b8140f42111090755040607500103104620500318211000081450000d5481580c0c0520501e108210444000303e0703d00c800700704440003540e102d520080703103641e02c00c01c1800e10350003865031040d007900c0003c4c0c2158181c15030440094024403d16040000c0c50040c14211002c03080c2906101d0000c003003410700d061150141c41c0214480d01048030503c07850b240d00c0004001c0700c503c80d03524109101140c0054401e03e0003015610081030b0740b24810b55580c0300c03070480d500081c10ba94440c0e0040c02594003200030191540d01c0b4040a084110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 219367104 1250 219365854 219365863
    0x306100b0c210702030c0306061e0d140303010501091d13031803030917011509110706050406060e060402190e03070504060b04060f0f080604020d180c0f050406051e040e 74
    0x81c251980416160f56841c0f041c940340c40c00400e2014445e078803440421007282e031010700108441042072180c0c807a201801011a41b0780ca40e04100401c030080e440c4604071820b00c0040918105c81090340c848101a555090019603c00500c0409030400d6004002a2081242c041c03c903401d0742c40303890305038124901c81c01c10701c940c18040c0e0012000200a0002040141118560940e174a4000002049801e0b101034400001c00501d108502903540c0300c1005410b01a011019120b099402402c03d0000d441d00d807514030028806070090440010b0711001154450030144261403500c222041c900107040d94110040d40c112001084a5030b02d80b00d40f0501080f00e482e24090381d0000c044148a6a40311402c02c103000d0544c8038031074803803020001c15040302c0c00c0e21a40010401d4103d10240d90040c1d031240840900e101800f05420b1a0b05030302c100890207070411100300100c004607545d00002800003a254000c00040d24450703c80c071940b01205810040c0128040d6250030f0f484038008000150030006044100d084c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 219368354 1250 219367104 219367153
    0x7030903020927010b13090311060106030212130b13060209060a11060601050c070b031306060b13050102010c12053d080c060f0703030e030301090213050306100b0c 72
    0x1c107000d0b03c0c65211510b810b0603100c0c880300e854000e00a00304810f02181ca041c1005151030109038a8941400525024180700c031414a084c2060310040d40e12070b44080c010b035001c9282079690a5200001a81403410000444c10341ca901c03401c040d01e151658001851660100b100c00c0e5540c941c00c0100203115903807d00102044002c1d03854402c2c080301c1c105099801c0a00040c0360505101c23003003000c2c0c25410300214100003503a84991117182c480e1542c1d454194204400c0030000e0902d45440008140100940050040c07241014001c13000f103621800128241d840c100d4042001c19405400c1c1180c00019030042584040324100c484803207110324514458001c13034901140c0021030048064404001d58001d000c1c0604580001440c8111140303000c0b4200d481440d409540c00307100814480101482504008900210308003100c0c4c80e940c5640c10724000398060b00c0300b14901080144005010300700440d480b0310807502c814003124414a0f1440c40d60140d8082101549140114400540d003009180803000e40d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 219369604 1250 219368354 219368371
    0x40f03060b2d1309020303040b0a0c02030a030305190e0d030f09060207060b13020301081b0d02031203070314010506040b09180705030411011d040f0608030318011b0f05070309030209 80
    0x3a01c20b841c0c080c0150022844803c000207414290900c001d070f14000200c7d0100d82404003500c2d500c0c0c160b080c08403009000c0d030074000d50601540d1700c20414513030b158020038000c04441101d000d1110b51110203504031080c28940040d6500540481031819001354801d5002100741c500120749130489039545d600300d81c00030303c003100c2c00c1c0da940741802c52505040b495a01012555141140741d03504010403180e0320034050b540307081b10440442880f400d41c0c88a5100c3c81e105540a0101c441b115400b5004001c1a08100c500400191400000540c0b021001c80ca441c1220b4024241c10729090401d01e000801d0351100390496000f28000c10700006c2811901c0d021403080c200d50355803039101e0416140142d07040e9514a601410001d036080801a03c04282800b240e41c4602114000780030fa00244600300541055400b039400d5010200c10408944002c14100000c0c20410b0000c12000e41562100c1d0300804990031540b0001d00e00480b100803060007070b001803049500905200c82d48a64903030005500c0c0f48125000705 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 219370854 1250 219369604 219369679
    0x30b0901051614160c0812070c1e0806150f01020a11060a02030c100e01110901120b040609140a0c0f02030417030d05190f0c0c060b13050f09070b040f03060b 69
    0xc07440092181d05a6031700128607207071500b881a00c80c101522020b024640c80355090b0b034081e844440300c007945407005003244013340c0d4103440e019091a00e5013401784410390041c0801030f0304101030741c40881c1b0003443c1503002c82000d000400305010f1200c41d4006441200c198401003041080341e00e005c01400408103510302d03001c200c03046002002030035126524155955600300b4054207503640c1c4c01070081c03200880980000140c502e4160002030140c0007035800003034111715050b00800842c1312580043c0c41580c070790034140201540e58104554180020300c5410042e0014042800341da03214145c0c3c1010078926004407402c0c4001c002283e0f0440398140c0c0c8500081c94500c0a980010a60b405202024200140200048169040040c00c0ca80045c000103002503510001103c051740e450041c03c030745001c48803040065150089040380b44100070b03140c0c2c0d2041e110781007000a06105000445042c0c0b20240f9801f000c0c20700e195580d8020304503c4600c0d07a400248a80d000b603403007420340b0786884050f200a807000d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 219372104 1250 219370854 219370859
    0x904090f03020c06120c180613061403040308040206071109010b04060809010b0307050420030a050105210a020d21050a1805100c0201021203010807030b0901051614160c 74
    0x70b031811094283c8036001c3d400a02060803140c22040350b090b0701000340c0074050790350034020311100700c0603d0801c6460360100340850313101c0240341c800f0000d50503120a504d8428030729900c071001018600040718000c0003d020300d0002001030030641c003d000c0c058426808400064401000604412001d811010025101050800c0003a0744100115000300c80c0300000c001c1d000082011039114641402907501480c1c8502c4581c2c0340002c00f1900202500341c40c0d200d03d80300e080080620024080a100302840b543c01052001d083c01e5002480000841e60304005007050301099003407000d90003200364143d0b008000000011403951070080d0441005601da40c8003a80c0704005072000c0c1112041007035402c59411000700034001d9845504014400061500381500b600d0320620040b854041000d620000f00c4102000004103104e001071104181ca00c140b60b24841507a0f002d0500d8200e0348101e40215401000c032040c0511a40564003070080800c0050701285803144d01c02c608400c824103500c007120a007507150004c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 219373354 1250 219372104 219372107
    0xb1308041d070e06130501110a0503040e090d02070f0e060d050a14100915020d0e0a030207050916080f1005030a05250b04090c090512010c030609150b0d020904090f03 73
    0x800e10700c0c8604550485c14001c3c8104078540c0702c10709018613414000c03001c00302d00070614100962811030740c0c0941100d55403911003417823044044056402c6c4225208141e00101d00900104408060340d40c00084100d8080c070b0031070040c03c00c40c4003501e4107070444805071000010490078405142e41030b002d82019400700c80d012120178904400e0212264510386001c1e1311400040014004640c0f90109180142e25140603822410007800340000982032171140c4035054040580210300c04003216400c8408070443e07070b151000803035910b04003020000010000f10014001c0340c40d01045c80d4100c40a50b1911031b01580322030100b450b00200d00015543c542c00703101c94a00740c00b0203001400c0d0a15141c0300300c1c00340c039140841c40c00e0705014500402d114141c440c80d10401e0035100709201401000000d01401b2801904400305000300316001080000030704010010071103807c140170b48004200c0049441d1205460700482000c15044100305101464007004000c221307a0390390044c1e01307959002d8001ca0b145e88a06180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 219374604 1250 219373354 219373367
    0x110313020a0e130201050919030f050114060f060d06081f05010815040206071707061e1a040f0f0e0105010503240105040903110106060504140303070b1308041d07 71
    0x51a410525004100c0110144003c10740d10301d90a00b017454036808031600080540681c00d9910003400d141075400030070f0000002001156502030360007008140548607a501c440007088a41c987c210300914100c07881e500300320008001c90403010400103901c60311814850700f04211581581021411200005600c207028444c40340100324041c01000f07022180c066190050000610207482154081442c100b40003121080002000e040c0d8001aa5147c0c9850031000a141c50f1107c003042420411501585210511400750300520607050100c650301c0d2181004050070068092401480e21803012050713802107401001d01c29186040081351540c101001e1500d03040e0b0031090480100302201181c10716140d08581141035460603a80812146002c0c00c00b030380d2616100c44040c00640c80c01000080d130582c0304001e082a10794142c9962800b0502e84201562030088d00c1018003a50b22200c080760484425003801e10740644140c0c0402d0030543da60500841161204804001c0305a8550400c16501d600a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 219375854 1250 219374604 219374609
    0x5220606030e1e0d230403120807020606010c02090c09030106080a021807050d0c0311030703060e06121c0903080d0b03100e03070f03050d0c1e050415050904110313020a 74
    0x143ea1001610110600b10740d0380308444404410310821031456000d50000a401c0e4590507a02520030740d841f6503d2410781096034100e00303c10001a801c60109002d548082121030080c10141d65001c0042d40c43d4082041c0004041e03c0480408000c002151180e2400e00882c402441c10b140a8401d10495005004002030301c3c80107c03840d9280701d81000011500a02500d000d050409800240740369032030302c140c00030002c04c1407032058644003104002000c1d50541016003929280300c0d0743e550b203491312814411191071101c03540c052500944441ca040322406074851500c4426450b024000c80d40d23780382c2040b19030200d018041d94649812038011a81410804a2880f4010310000c100048108090a85030700078024020517810402c0d01f035209041c0300e841610181c402c405410400015207800251030319801c61064100001c4d69807185003094021000e50f4222461a1803000c0d0000300200222800c3e48640d00e4030794030580d40c1d00f284d40000b06110146100382c811881c4004042014010011070381c1081d03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 219377104 1250 219375854 219375883
    0x108101e230d080c073816080c15010e0709060807050a0c23070806011208070f051002030a0b1c0804060c1104090b04021f0905220606030e 61
    0x9401e030009a0b11882002900c82d90042200358640c4100c075215404c203a642d602000440025401d0302d50400c40030482c1d0400001111030704820100840342214450040c880c0440300b401d0400e1160000c0345240004102c00b000c2e4106844008034000741e2111004002c0e044040030012810400143d250808c44401c0a0100c07820505094644020003c2c25485041100001c0207072280c0c0140800101c0656400d410449518541601c080c00452070713543c200e10702c11420b15200d081c000080d90b0210781c0c0d010b05a1908032290a1070700d001903c4001c0a01c4e12580104e601b03124800700c0d20480340d81351020b903008000340d24001c103c1c0c10300401084604040403495038a10800c8042c11030004a40a007180d084034410705280603c4219424001481e5418440b1290040d0600520f0f00c100a40c2440d80c5104a20132a40764000e0304020150820316420f818400300450001e40050103d40780c480d81d0160501302c0062a4543d00034a60111001d5545552001c2d0200b900e44002141000c000c1c04810701d0b65195 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 219378354 1250 219377104 219377159
    0x80901110703051b060a1a0613030209090a050316061103090d03150911120c16030302030606071a010302032a0603060d08070c1d04050a020108101e 65
    0x1008a14152007510802018480006444002c026503a4a00c5681d50004001c0d074040d45040507130a00134014035180d421020322924000740d42454031606881c01e00c00701c00f1256014908541c203000d07103040081c0000089100e0804030030009202000240520021848551020302c05458840700b0350f00a201019410700f805e0041000c0c170440001d09020304a210b150105500407074100c81c504071825500415203281c1402902e044000e04c020003004503a40584a50225684869045080340141c8090920400d6100c0c0001d01007440794010790341040c0e000707201c0d516219880c3c3c0d60540011100c0d10b880c000101d202c004000358a0280084070111140400940c2050101c100d400c0d0b6070342c040c805c114460140840800e0301e0341c441481c0d004505d548200843e0755080503081541711018a84036070314017125140c00c0180419040c00c1900d0240d40d0240c020700001c001a030054404001c01481125880303035029000480c400054983c06840d850a40c0c5918554184130441c035025101e5404600ca1482 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 219379604 1250 219378354 219378371
    0xc0d030203132a0305060114090606040603050703060f0e0708090606030c1c06020301080318010f0503060103180210030603030e06031005091305121b010b030c01050c070b03070e01080901 82
    0x202c80341840030035075005480009a9004181c82d500140300c0502c122540c0d0708500000c401c018002560340e0580301000031709070390410082304000c8003540840300c60f50030440c140410000c1070b012344c00241d0405103034100418101d0b1184d2184000d00c26992000380d98518400030700400c19007041400380c024a644000e0402413a001010a41d030b103041e078030300900844011516a01e05101d2940b140040d541c00030056549503501e04001c1d81e00d401001040c60101000300c003800c8558000e0643c9140150300e511190304507074403180154010221003080d0101500032031038400050f03407001d1f41c03e45483e0546e03c000030b03198218140100310082d0020a00d02030f4104000340b020100c52111074400b11034046801c40243d99610348440c1c48414085401811480b511081030740010482d000390080c0c15060740c5100d41640e44c2d070081c0703090360b0300200d6170b54064000201c0004c8a500c00ca0003006c0d080401c81c1280c00c21582c8081046899104030b0f1030130000b5041c2902099590307803200810390172180300e1000303028406 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 219380854 1250 219379604 219379621
    0x12060904030f0c0507120305181e0d020f0310140c03040314090609131b03180204020a27061e08071101060807030803100b0703050306060a03060305012d0c0219050a0c0b0c0d030203 79
    0x1891240060bc07031845c000e1140308541d5013a244140b54100642a0381000d004070b8000005030510902e002c100e103c2c41000942d815040e081500e200e5034060b5280100c1c01d5030680c42c180303da030080b0901038202d4000c111400c0680c60f140c0d960701158441c144005030007200711000c507801810034002e403410941817810000b01d00001c071000303400b60354048500680d41d642044050719001c164188050340721001a02000c1820582c0c22164200c801c0d684801c0410184400011019105415188045071f1150301160141e841000c000900f0040e42c0c0002841644410034a031801400740d0085802d400f00000304007110f5080c070541c6000f0f04c0515900c90802103103a402030714500008000901032078004c45c202400900c80d0300030f00021354001008210100c003005013185420110002c0252080e424026060301040510071401010100d902610720021588108588064890f40680c0d003032080d000e214010401c41c01e4120000d2821600c1140d440d100c541649090074040114602030501c107208112035175 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 219382104 1250 219380854 219380899
    0x2030f0405090c070c080a02041409030d05360d03020f040303030216120c03080f1b0f0c031b12040f0b070204140106030212060904030f0c050712030518 67
    0x101d004840300b45056440040c9803030359004004024024200c004000180301e10b011900a100b0790003070f64103103d61243d8060280d180704040d19100306542c0104104011042203600603a085071005405590b0320407540d07c0181d074814010403c044188001c83c910350710707440800a1400e419110b00b01542480d0640520075450302640c400a41410707000103810075130301300c0300c040380c50b12961240b120140d84505042c02001038400301c80450105080f4404a18131003403040525224400c42c0701c4440700354407179102d0b042654011482403035a4180520080301e1550050000e0000e1501080c40d094581101c800d000d86800c3c041442000d07200000c100030b1000800c0ca4403000103591030250f02e650f0303440039071021800400c0d980b0b80111040002c0300000c110154180c008150228443d294210f640d02d1320010840303590b00540d00140498110500241d02e140a02d41580d04640180140c50340c096660111001014501d00110005400000d003200100d81e0a0310160240d00146c40c0f215690102c942c110064 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 219383354 1250 219382104 219382109
    0x2041b0818070e13150902030c09040b06060706020d2a090b030a111303050303150603130b07020a0606080c10030e0a021207091e0b060304050c011d0306190c02030f04 73
    0x220500000a0400c00048504c3c0342c007030b91041c05040c0f4030f80c602e48290024034204204030b2090040c0780d4101040d01d4000742440c002c54200d4180050b070340b40c4c0010000700790b114180498589409104042c3c03400341d540710710481d411600902c80080034036024210007414090380800140a40007100307001188441d015654071205035400003908641c1402034403040d021300b02600f820200140f6001c403c0010100c00b550083c4050030a603015104400100601070004913186004842144000c0010900d01203610fa04420240142c2c0c0c514010385d01d42c84188c0c0d1040d0486541070780004c80e0805a410b00c42600d042d0f51005140410044000e000600d8441f1880700001e40b00b030001000c01102d02800707101000082450300c1080060203038040503429180800c81c0c2d084007403840c000141c000c40c1840812684035581c010003405801070004019240d0703c0000011651501c000070b0080034a882c10441a0b00560150901c0c400f03c7c90300000040c1940d0b10004d0b03180c1190402e01c0307040003000c0c44d101902c09 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 219384604 1250 219383354 219383369
    0x215070e0904020a0b0c0706020d020102070f06090f0c0803030603060a0902031b030106211101030c080a0f02120103030513090b03030702011d060301061211030606090909010902041b081807 83
    0x5854842e400040d50a0a40d5080b100034018006030315020300500103120003c031403071358003907901d004140d0038140c0c201c3c0607030b50018060120001d03150b070004070203910101c1950b11035401c88010200680364806224107503002030910358030010a200d02480c0800500760f00c610045402c1c8080f00299010a0302c03007603514114010201e0044100c1b01c903a078203411020181104405c100c418003468000e50022912002c01076a0221800030340080951207400350168060803501c810714151114000c0f07a0040421610f80040301d03a00703000f4200e1091141c1a402d000758000d595198a07801680b201e40f0704c03040590301c175190031494880c509103281c43c04400e843c489902401c0c03101ca405000403400b0b488841200c11141e100d17000100110309a41c11007039501c41604440030800008486000b00d002c14030040d03c9056008509104018061404682c001d503c441000004544001264040340956400443c00754003a100d00004642d031551104580740d1144c41650381c40190312159401e2901c41d80d00d40074080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 219385854 1250 219384604 219384619
    0x91204120201110a120c03082a03040c1208040513050702060a241511030a021c0309020409081c110a05030402031e01020a0e03060402130f0f02040e070215070e 70
    0x84055007881241e0b20160054103283e21100800d0001b000c1441181046003c14560030216090041c0c20381c05925901080403000040d4803084544c5c0000e40001b40226001001c2d4080030901ca044015148551489108459120350034071003005040100003041c6e4035410325200070080500d600046135074004801c0e980008100714141d42c82c60000c11107440102201c4002040001d1500b0035041142d808111039941700c07884200709011503182c0c401c0c0459000107a103e040d20020030302030380b03851f01c0e440186400d000400c0300507a808101602d006030026588a031010505a000b015100e098098040100404001e82c000700c4499a0350750043c200b01008011010000400b103440420a040c00d001245034010000c07100da084c3c042c040d500140750100000c20b142d404200609001a07950b01031a0300501c6004d408000d43d4504004184960042c0701e0030740c40c2e8024000201680c40140060042c000312008030b8070b030003940a41351100948400b401034951500b0040401d92180079030345114000c0f9000ea = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 219387104 1250 219385854 219385877
    0x105010e011205090c330d14070305040c0504060f0308070206041220090402060d0507050d06060207140d0f110102030d050a0f0e0c010906050c10060806091204120201 73
    0x102c2d5815102d2140c140c9092801e000d1003490b40000501d450311207001c9500d10074135a98040c00d0b8802d449020454002c40c10720313a8000008020f00c40c0505030a5403503d00009807181c00c0d1115402440040d509540403a031303144240401d0040c003002410180800b9035040c4440381c41e01c0c1b0000f0710074a041c84050505000030034410111760f11751044900420441c40030600c10f01507803c0006024407140300102c510303001480340b86094140443c09521541d0010003550510a072601400003800c3d0007800c003010400100550441b0110b14452800030b450142d00400c850b03070034500308004a01000081c540720b1841203602d080001d0070a0404100c155001a20880042200700103030320718003504071201512810402007100d45401d90b80800d8010311a200c05020510812004549540396501182e0020700055410310090340280001c0c0880301d545422501014801100d06085036882e4208000d00d42202050049464040200703951642c130b0740d20191715052070984041546080420020706000114100d03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 219388354 1250 219387104 219387107
    0x11101020f0708130f03120c05100c02030c071d0103021c0519020310050c09010e0f0d081308010e03042c0103051f05040c06200a150605010c05060105010e01 69
    0x55444012840c00034640740c071418a0480340fa40c00030038180e000b400951100140203400619aa011260403080c0350403203c0304a201201d10307c0841c5400d80d45845088a082488040e91241000400c400e034041d42c2c03039a40000030503083c40c0c66644802050015007201020241040c4011411242d04540c480b5182200ca00e9031140a0301c0c204001d01140181e15240c0c5441104901b603950342882202541c0b08a10000c60010840d107041c1c5030a50312003014416140f083d4050045a480d40c10002d00b0b0b42034240420b00000d0f04000280d0b421a079080d40801d256140e42c0d81d05940c200604410002480f0035801200750a6403030203140f00b0303001c84900c0340d032118296502030142c1003182070598031004d19941c0c483c10066620008045812070b40802501e0b08512040c25108407809a13612901c00a040c42c949a4102e5051000d038031404810b14080480c15201c6204010038075003584200c5040c940e51402c01c00120469013180d200030305104603180c80100156006c10681e040d9070007400c10b01c0c400b040d002300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 219389604 1250 219388354 219388357
    0x4052104210314030f010306060501050307080a0e010e03190e0d15020315030102070c080d0e01090e0603070e0708010603230a2706020702030106051f030203151309030908030a0e01110102 82
    0x3c00c0300420300005200300342195485880c140da01a28007807141c03503507480c011201444105c03403220000300d2400c0400d604c8621a003204074040c1d060400410780016041c40542103511490090703800d1003140100039070060300950700380403281d8119600c07440c0110f1a116054407841480c041c442965000001a0304002c030541060076081c0040cac02103440e151079240c81e00505809004948881c8144a807601c03102d03101d0180d81b014154183c0d10540c90619052a140d041c0307101401e040d906016003038001c40c200c0f44222100784100819135a41c846549401c1f8094111a02c2e0b0000c0d2041e003001c460391200700d07403030904038640018101c2d00001e0780040381201e0508846112030500c1c2c40e5620300c045c0800380403ca4010740950b0380204d008109480c2c0c0c900c10083e040b0031120040e80107103001c00362860340e9030203640035590013402280350389039182448000400741684400b070400d150b0f6940d0400e20502d58000e81c6e19000d007107213800446c68004a4003010307040c1c4045020303450400040c1285400343c40000e40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 219390854 1250 219389604 219389627
    0x4050106210507090c05040b0706061e0f09091113060503060112031803021503150603010f06271208040e070807020d03020f0904051509040521042103 66
    0x10304030041d4580703032045814004440c502501d0354801c250303021454200d40d10810114800c942ca6841c03504c2d19108030058103400640003681c00583d0b40c0070000b1a246c0850003549001803400c00c8816207030500880c0b480003031050b00400d503103501d000410340c001213411002a10070142242e4014116030200c0c9450050001342e0400c0b6018018030000140031840188000d030720a20035280c8652060388804139005519480c40041e50000c417100d0404a0501e20314001d5400120895000200040c01400702e1030940c000ea002810081558500b08089607105080d04210091921152440050030390105624862405038140540c4022403005c10081c040302242d0052540c0c0c614440d6030716040d031018002131001c17105080540146030350008030510920807103c410205a0540b82051560010700000703103070003062a0642d1038100540401541c1d500c5038544030300d1040000b4500c80e0b410700d011400b009840c10288000311002d12003442143c880c0e840400c0e440300407044c020140f49040c00c08440414406 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 219392104 1250 219390854 219390869
    0xf030414010908190c020a06030e0f071d01050301050402151303050109080d0c26060111012a050c0a141e07030203062503050a060b0408061024030504050106 69
    0x310720003c0141080142441070400101c640d07513103400c21002d9881102c500d01c0254029074030001804014001e900080c0c2208004048486501c00a11100d24241003a04542140d0b051545e0401341c401001990602410041c0c0083c0400c1c00e15a0201d00d44100d50205041c0b050b10100d40b0808800d40c00039400c009680050080c131118a01c0d041c00c1d9516408030f00e8058090b410300118185442c0980110300c94002c03545488a11000901501c0c82c00030005040c6904105010065904010090142e001c0b50480d9404080303841e00b00307600740c25440a41d040d40e581442818010120341100200707000c2e40c036940000e00c00800b141c1d080045400d040054006661100c40b03647c22113440c0c0b80000b424020740b0301c05d030100c42150b229111013048c0c40010701403070000b131481e03400720100780d1384a50016600013500e03030070200300c9513110ba40d00500d40c1c105400c4a1410382c01441001050149030000300f005000301216549280b0001c820050300030309541d00c560078191a0350101e803c2003003d600803002400603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 219393354 1250 219392104 219392111
    0x8070b0705121503060a0b010332090a020d080a170a0f0b030105012108071b060908010b0609010e0f060c0c0109051504061b050d08090f010e1b0109030803130203100c050f03041401 79
    0x28040da140031070ac0c481100e04455581c0000380c990100045c00d9405941c005010f04402c08482c0c0e0f0310346195000044d100304008810741c880c100c41c0301d14001c00c0c1c0213000d06040840c684c0381c889025000c9554541e4002e1090703050000401c0b0311069100240c200343e1007201c17030704d62440d40390809602d41e1190241c010034501c0c0c80304d220f00030500e0000c0424281d44081d5240d004881d0f03030300c000509071145481c40750f62105e004c0000440640c01030b10b09040c110f201522004a18001000040698002100d1180240c00103a11008150703071080019019080465101508252001151103e0301a0f80152018031a54081c00102440e0741a50031000f0356000c0111050140031500c000c010080c19604803d1034491810944a1290180242000080107000410841c40d102e01e8035030500030304640c214144420450040040342450008501c940d29095449000c003c141c4141881c0100c00c05510806d2444c07c1000000720b42d001d0100c1e40c400d8244146c81d500c91f203a5013800341c205ca654101c0c50300c180d0710303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 219394604 1250 219393354 219393401
    0x40513200712080114120a0b101e0e0106030e100c0201060e0f09060c0306040b060309010b011806051c06050d0f030320090d08070b0705121503060a0b0103 68
    0xa15030010090030380300c0c205200485800b07500030783c1c9407042801198810310907003480b66903a0800316006c20780454142d085030b400101603215110000b2080d226442820710b064818401c0c405541002c1c901c4e07100b1081070b150043e01d030504502da800018021082050b0b100c0c18005090001040468904402c81804005001904030082d0090405100d035010050903070000615462044417010b120f0001c7c08060401d55965900214881c0d00041095620941da030886001585840000d507100b6182803000050350440d000c00581034104002c00341e0303120709070204140b000c4c1d640311094801d9600c05e030354501c0c51404151a840b01810003038000350b07000040b8105001c00d000d80e4003005290140a900c0800c4807082041210724015207100440c0000c0c40c1c100590100c500300400d501056502628440d070600b420f07640c44012601090751b001c0c000070300100300d0a17514004c840e00c06401100302124800800f0040000c46c0c1c840300010700380325800303641e00802d48060b4000d800c000f0802ea82840c00c00300c03a24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 219395854 1250 219394604 219394661
    0x1110a0801030b0a0c0c06050408040b040b040503010b09060a09090224130f0b0702060706110c1509010516111c0201020c010b0d030806130603020d11120a0305040513 73
    0x4400d12050b9502030083c1c0109801101602c10901310708401c1d505c1446268090302c519000e80b0015104596200f0200400298102d420004e80064004c000103150f4a0746440c0405094a001d480c842d84070385d00351010b202c2507945000600003214651580404c140040b800002c2e0b4896140d81021034015080301c4014607019403000400d02e10f4000b1700401243c90300e511b03e44004d49041d0180305070ba8042042248094a007180207445098491080812551032b1202d65402c2c41c1c01c80c40b500c3c0d03244c1c2d00c4000043c8e1400314a806060b030000d03000b03008200d0351401052508004129210000a00c4a00c07000110b030b00781d00340800390000d106c401c031480a0000806000f4000e600c032009402040d46002180c11440c80d1402965140c5909980c0d01445034803000b04010404c0001d074080d50313038941da81c0740000050300d946000c91a0b1a0064800c600221001002c0c82805012042041e9941c1c002c000044000b90b000000d540907154180d0b4810180c03c5a4030000000701402c810711107807014000c4070000d205 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 219397104 1250 219395854 219395867
    0x708070f060e070503060c090f0307030602120a0207080f09060909160f14091005041503020a110c030d110f191b0b0f07030504030b13060e0a2301110a 66
    0x561148004102d031110600315240c442c6090f0040340da2682194001c983c105d07a036800a018a210020107e000000e07040000030f1030403100368011190340340c0104000405031080514250b10007c188029440d114060380ca03844148551004820300c010003044030303c90742d03d403642500c010f0364000d00780040504140020b0380003c84815500000186080c1d000a106881820a40d0106820440040c10052711b00101306a41105181000821205200004204010030b01c0c0c6400040a5200148e544034043c030700400303e400411403081583d001001d00d090720b40b40051201404961840d00d503261100184100e420030706900c00b200791502c00c118036100802c864011562206108554503203582c0e00300c640726402c485070b5100d500841c40742070104140c9060800c0050240500c02d2620a241036281d58440014860640d80d840406003029606020480703588244078407045980014280d052655480640009102400c03643c09003028102d01e0310000250480c61001400303000319a240c840e1503100801c1da = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 219398354 1250 219397104 219397133
    0x31306090f060f11030609090f10050f070914010c0c0906140316080604150f050a0b0406060e0604062618060f1509190609060f050f0108010e0a02070807 67
    0x4552070f1561000960700d00d0703c0b8148180041c5900141103940d900204400c5140c010000e403160700510300d00740c0c503d04060041312540c0820340000102410106108025a54020701d4541800400e080c144041c142d0140120606a02460030203607800540c03406034005200d65114045e60381c200700c000b007168050b0b100c0c4c001c540c403400c1e0100c40c0038408000c2011000c0c603251148410365004000403d010501c05050b2180c00c080280000c81e11f020102c240000b1100304840c04030516a442c0d141d030600707160a00501000304803601e85076a82845400c00104188502e10485052104080510915844411100c1c20464030002d140c0703114900034055180e40071078580088803e009100010341c20303107040c00c8580d0003200c81b204a001d100c841c80c0c051101c83c041c0a44100d501c901000c81000f0030107000d026040103081c0c2024086006840d01d042d2020091964200c0c0b84201000340300740781c01c0e1344c0c03100c1c40c20b0440f1350aa050480507140c00701000000e00c038840e07000c0d1400000207464024041040c0c00e1982 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 219399604 1250 219398354 219398363
    0x4120501050c03060a12031103040e0105091819050705030d0305270c0d08091207061101050c0a05160804090b0a0801020c15150307030b0a0b01140906031306090f 71
    0x816030b10341851540b036120031a0034503072084c45d4075020701c0b1080340710481840b414440c1c10038003a19000780002034955085540858619610100188210b0404980494218400a9441035003049040300c040d1240b92034a614000c0c81b40c18088103061100810001c0d00030310014040da5101144614020007506048468014180c0581c0340c4410076410320340e0300d000245090b030242c0120007500c010030001c1c01c030100042c4d03100e040c01e11031076140741e48030308280b1814409000107080d880d01c1e03c1ea01074100807442101c401c50381d240404200b13455080004542c0340014600e002903a54081e8818402d400c8401103014100b648041004210700486500520b0b002c01d048846281503903070745000c0c07400d074442c2520200350f80d001441c121a042400e6043d4680200103c10031101d15011200403a15124880c1d006231000001c0806102c80941603101c1c0d4207006200307103001e01402c0702da003400a6082c03180e404018000e4800100052100d9002c008203603006501010510100301542002c084149400301c0590303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 219400854 1250 219399604 219399611
    0x2d05010602011808031906081f0c050a141b03040801022a030702010e0f060c0a0c080c01050301150509090403020d02060901021c050a27110109050a030b1b04120501 72
    0x7021554100c2040b88540d80c40502d40340b17156074807100040304452249060101c2a110704012940b01c400384000c00c00b0b0a03d0141c000c807a699506501400e45a00450302000d20208115007052964801c055110700d8200700c5520796120003994504240000031001c4640d44c1c00f0106010030941c070117400a181144c4001e007908108980b10024806111544201c1401035204200150065004900c2c0d0801e03c1c034028462045076030b482c0e01061450b8001064103985810000c05201000211003004002e040010011300c20b940000c000600144018090410910448009044028802d0f002c690b80c0c11409042c460710341c00d00c3d00e0302a42e255001c081c19800350049400003080d1100501c2aa021030840d1200004170251280c6084000d0401030140320646860720750044403840c0400601d00070030030400441290200b1800c00c000b540003c040708604100b4002e130108117940d901c1c6c61000039281c2114400d00c0d2921501c240903a03c42c52203111504180340450005546a0101c8041210034001c40003072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 219402104 1250 219400854 219400871
    0x1202071508160305090a021905041505030607110712030801061e05160c080304030b10151205091906020a0f0503100b0703021203010b0a0e03031c2d0501060201 70
    0x2074801d114115000c041c00b850311034004140d244281c02040c0c200b89814142e445d08581900851910000b096562007000b200e04003c21460900348204c0351003101c81041d09150741d050400190716000c1c0545020200700b8010039081340c02000344401030081c103042500d2484d009052034080c101000074880d4001003041c032041c0100303a00540c0305c07540501c59281d8420f450510503a0100800000c03141c015a241e12900c2c5000c141210208010000381d0f0042a1020692414154040065029800118500c000d1540c83c0c0813440d00300250014070700100e00b001c0b07450b030383d821841c61802504ea45144001c400205110080c01044c0e40204500b1180b5500d1150010745800144c44a00c825196542d01d1121034108016032008070018021491180c4103448001008110500d5541c000f80c021000407100016007801680d002040320314420340580146050551500d4034948100811310307030990240d110050000000400c41d01404015109551071004480c7d81c0c082000034802409000099848d01d000c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 219403354 1250 219402104 219402107
    0x614030105090601170a15090c0b070b01030f0206071509050c0301060501050f03091204030302011b0c0f32010609050603061003120201020415110d05031e090a12020715 74
    0x15107104180110090100d80d180c03c03c10703180c8400042e810070a030b025401004000841f1000c4000701c201d040d0b403020408100b60300b06100c0c00c7c105a8000c0c14441400c02001d0b00050080240318116900f081c00c4011aa403a0b0010861038483d00c540208001d01502068141c144a54880c0701d0560040c4d08039903d007409541810300725115402018003251090050f0303d025148100110340c044843c106071103001c48030b06400c0c92203400541040340540d460b807442c607010803111a00b034000b040c030b107180c2002c140b065910703030304181d0030404070180046a03583c20701141c00203804503074107802e1002481c1c60300303440c40b44903c54024003050054454185c104008200945000540720340a0b000701c1145c00c50300e0385180e6070074001d280c190041c00f080d95001d1000089000012a07201d40f8120706d500c0c0d00070005800c1030980d0030282e00c46008010f00009009000b0117900d42d110b010711007242c4c0358405c415a218031005c185060351030000103015503003050034046d5041d40460700d1411501c801188451070060003d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 219404604 1250 219403354 219403361
    0xf050a0b01020309090a0209030a141b060d090302010e0303012306180d140601120b06091510050d0203100314010e0604171207020c0f03070b19170a06140301 69
    0x180d07030059005000d11011817510704402c41e00040748030001407070035200c0004241042001d0380290b840104441000010110912024000c00c1d070070504035030555030b4000018468080c0d21030020380c4960b10204001014000d40c007000421941c03030201c80c1c480da560802c003845140b0651240404281044111109084c0141907440408203854110301c03000d030314070610152407100001650b0071898001022800c030410320403140a4505401168406003003400c041022410181c401806a81081d00b0130404660307010582c03000503070403194403170640042c030030071035032130145c49210500c00744004107014041c3c00c5414008210b13841a180e00d9039450104c0038541c00c840c05c0480c0b42541c2d410160006002034420f181c1c1e511148203102646082c92801405090214000c81d582d07000f40c0c1c029890750050345440100090340c00c2048000b00004ac0c14141d50766100c0c0513021a6154000790342c041e01420b60701940e05110101203641e0412100c0c81c110340c0940142181d807084034001c0100c8950f0080f241010300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 219405854 1250 219404604 219404621
    0x50115050a061d010309020a0911030a0b0d02010f03110d1104060e010c080306060a09090905010c02250e0901020729010608010302100825080105090f04051c020c060a030f050a 77
    0x2982c12503505003500045d009020b8840040b41d1150700003501141c1c3d400355111307803c400c03860800080e03242d1422108410880700e4840d6814810204841c9140050703030701c4402c401d068141c0c0d10b00030030940e0466a400103240981030307a4451a13410310402080240b0040054811103495075106190341c9140350054843c211480400382485900700300003407260804c480100301260340340c60800700e200d541e80c04200442d01c556404403a185d454680400303041da4100078500300706032807411f8820142950078803c400e180d802d1050184103460300b400915680c80c00c0d81030301d4500c0d03000214900e084c0103000c0b50100d01e00c0c1c14840a1a4108110000b08003548034030300d014140c0364040c01e01d510101c1414401d460940c0d0051219039003071115003107910300d44154a06090108419100d40c8802e50600d030030800c1290b070061034819000c80d00700030000414800038915000c3e44409030699810b0001a50072401c0c90018041c60742c1210000800003825a030640c0450044000c500b0200040d0301c4032a00e1506035011007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 219407104 1250 219405854 219405887
    0x210060902160f1506060c211706040b0d050f010c0203030c0703050d0603061109150309031b0f06070801080f07030201080601030b01110115081b0a0b09010507050115050a06 76
    0x40ca00c080005003195071104400d40666002003680008054000c00c3c2c4d2103640111001444601c206420414804c14141d030451608c1c4107800e0300780c0086001000100050031082c034200c0194046002e0f43c440380d012040c0001e01400707a41d2041e400e420490b40d40c03003148041e90301d00d41c039250194040c280b0100a070307406034454440345072910500e61800c0b541c41d04819500d004803035403908000001078176403250f505a101c1c103500054079142780f40708102c0390b00c08102c06075000c1c40c070410400c56403203004000c458404421030150001c0c414150645854101e01c1c010520305031269900340110160012034180c100c400300012a00c08038100122240caa0480f4400240842c15007804603495601981100e0718152040c90280b0440c604201d045083d643d90400c001481c1080300340030301440c001840355004040080c00c12a0282c0c00140202d000340c443c81c85134018000c80420b0001140c0c0c8900200d0311400d811800a001680310b4400780e042d03038540340c4982403185260310030000e942402410700c0224201207 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 219408354 1250 219407104 219407137
    0x3051c0b030c010809100912020f010b090c130812030a110901080a020a020c060f0702030c06040e04021e0d11011101060b0417010b180a06170307030c0602190210060902 74
    0x3482c015a4902e9018213490303494003900382220004100b500c00d18050500511020581c040c0424020342040ea442d41010781507414207034840c1c01522560404e0b50820b01c95041e065a4080c559011404084241c10503052800f44018107841345282e40060743c001c49481c0c10030015500814012005803148820300d0340030524030000581c190b02603034046e003003100090054480b110100c0d0001103541d40b21014102842002045040a41c20200a0505810001e6400c01d1405041c102d40a100e000c1c0100000d1040504c0c82203207035079002000352003240c1400035100071104881c91030724140d48162002410f0006a01c017400c21000704050141c1011200c006078000d03d854141a1001c5110b042d60009484c40c0d0740740c2c3d01d900d80d1707522105034007502c0080f40c1040305198100a000c1505a68459000c0c5044034030141c00b9840da07000200456140590505010700c06100500e03040020b401100301400e814207846219001c220b40100d4181c2030300014040070020652550600400c0707002e0400d128040485 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 219409604 1250 219408354 219408373
    0x30406140457090603050a08070206090a0e0a0b03060601120b060405090c04090b0102030708040b09130510030b0a4101060504050f09040512070f08040303051c0b03 72
    0x6542c030500c0d98015180c9a600c00c000e4a429828003800041e81080c6034120450501c440d8020120000a000d40b542d0b4205004892860b12035541c3ca000540340504100000240c480c21503a8103800c46152010140454500c0b9907a103809040c1d584040344c980350340c3d41c00d01208156514010031218440d0130f050310340100c03ca01d007420040c001c0a180440a400c100d04000220b0796030b8811040f80d219610144540d9600c07030074100c0c2c01d020788011061660556200340901030005000a09540c1030b00c5204103040e4451416000050b21401e502c131119526510b00814050750103054650301040c0c80c0500c0004000c0c1c0c4580c1c50f81d408484180808a51814042c021001c04200041c14441030b540d480045003610050b011701079103800e00aa11100c0421000642088039040001c004002c070f101c02c40c0c00d00b12a1406072034054654021200c1c0781244500041c1d00c100f005403080c1c88000068210020a480e652240340203001584140050f034441d030000402101c03412014007a0500c6000050040c214080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 219410854 1250 219409604 219409643
    0x9050a141b040306050c031b16081612020c040b011b0303230f01150518010f1101140f09060114060702040204120302061b160f020d170304061404 64
    0x40218140101c80c0004000000106049000d01030040351002040d42d680e00380b18000000079004c0c0018035138940414003162005800c1c407a45c10300b602c1d07005100c1c04d0352906500d0b044a103072214101d00400c84d0302e00c285005413050f4001800a040c0304c090310100020709150b001502d0105500715100c444400c11200d400009200f80c204006005c0d440c0c52140303000000e400345600c0c0c10003c881250717201c64401700401c440024100302c1655001c1c2030420910300540040c14025411039004218103100300054000740303c40c032440b000e5a80c00011002049000c1404918101c1010151024951000718802240d003040f0003040990495100707941120911000c0c4051141c00c2c0c010781d0003640d000e54280320020303400100f80c122101c020b1181e405801c0510b07105102c10310034140861942e25060083c840c144e140c1182400d502805900180c14092260007440040c02d92203603002d00403c0e6081c048161200b4407039000183d8000e40c8580c00601000401c1001c1d034414080c00c036800b400341d0003c100d9228041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 219412104 1250 219410854 219410881
    0x606140f060906251202100c0e1e0301020a081f0e012306190311040807060804150c02071404020306090a0e01111603030b03060f16030212070909050a14 67
    0x5004134006102c1d0407202a400c00a03020006400c0d91030100340d00700035416a41c14400894a2600704e40104010216080c008007a80c17046d071026801483d41001c60001c1c3e624004c400e06015100a0007559101c1d02241c00401c160781c107495035400c2500417510420311043d8021b0740026103000301440300d140e80ca00305112481042c018491495041c44c80b00e04e00541d100d96005010303200c0c0c80000340c0c9000340d0055008045803c908a52040188140814000240c0118441d800ca514601c7c1c01c02207510b40d0b0501e07807280da400310382c81e032201c0c2d00c0c0601151b69260042028000c5844603022001030030907170380611040c0d10045414541c008802800160506d07620362041660765403100001855101060300484c06078410410604107016980c1e035007007095414000d601d00745e40b042e03000c2c20280c145007a024803040400b800d119001c803003040c446007019110358140e43c0307460a03c2c00402e1042c142540c001d09000382c5030150400399410540080c090307070100d015004c040d1005034a406082c0da82e07001c3c50440c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 219413354 1250 219412104 219412117
    0xf06020a0b0711030a030231050f0303090d060902090a050405030f0711040c030203011a0708090d02031903120f0c080a020a181409070207122d0606140f060906 70
    0x60001c492031010711518100050114814031b501c2c01661402c1800d420510355018045146011074007032050140001c11041c54011a41c0c25280308128025220000342135010700c1200035001410541c8071410701440e90040c03c0b08600a50303a42200c0e840c0c055041095410803940a0310a61080180e6070000452a00a184d50780c051104021030910b61000281074030720141d20400040c1d0080018040c40c0b0120304220102216034450b0361500d40f26507201480381c01803100c0c851003414000d50340303030948d2002e00c0018041115541c0700d2402254925018216150080d0601c03102c611f080002d0b0b08001c81881101061213094981074401c2e59002080f00196224085200c1002600801c0f604440c010040c100040c000c104c8243ca0000580001d100c14aa4000c000d202150700400781000452452203881e03c8540e00643c00e912001460020504101c0d201715004282c6022914100b0034003101e540228140c2c0d40701220310700b0306640c40080203108950203509650008080000c0303481858110000d010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 219414604 1250 219413354 219413357
    0x20a020d021503100e16090302040b010e09160f0c02090411040f06180c052b02040b03041101030b0114040509090106050409030f14030709050910080f03070605010f06020a0b07 77
    0x1024000a0601d4802d038205882c0003515003001c41050000ca40e404040c0c0c1e80c800f40f9821410703010846024000d007492031610000c0d003d00c0da40c103a110b030203074401d080e440b424030800740103419523061100da41940f81c03000c6031a0310000f540c003584960400d07228038500020301d9002098004981c0311a1940d075280c0c030310400c0f007d503c107540d03124400906010740038000c014016030740010050507a0020a206031084000480104030003040f89010245402500d408201011008002c2c91041404141d009103d01d811000c0101c2011040100700a090f2200d4072403c0c2003030380d09010780320384640195004010080c0c0d00d1000c1d04244418800d0381895200c85500403091070000c07403626505d03404201101c0b4402400d0f0009900914203941040d0802c180340c404902103072005280d850306d59001040c445d5240203642c4034030051000305a03025000420100507105070030540304404050701c9140d81d60790001400710380c0c10b1308040000518555022800003214900e8010385590a0156910b0044402c020800b20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 219415854 1250 219414604 219414619
    0x609050603040305030601030b21161d0c09031b120703021e04180515090705010909022b2906030c070f0b010803180405060d17040e09030a0816020a020d02 68
    0x200d40cad40c41d071850035403c4100d4045941d0182c0c1d000c528604000402e544010180d007101d404001d01d0a00c004149030181c040e00560142e07031105403550b9164031455003010390600c100408074000500004c01c2c540d90007001c88140c03030a04400e000e03442c1c44400c9840040e503c0043c0c0c842c2043c40b14034000c0d5884011200034000140d00364207070b250015109050303105451603404600c000460344000301481e038100025100400c40c4c6854100000e0440e0224050b00f6901a0041440b507890592581d821410903103009508191485910840d4020300d00e01884890f286181c50001034141c03100b1000b00680c140180015281d581d50081c64061944528001c03141c8010031441680403491460225018003450409541e0380c50707030043c601d0440c1318144107144c41035143c0300500c042640da494001c80b0041d40220003025072200c041c074805039405030790b12007040d98248804204500b600400200300001168030341d00540e072607541010013444950524000541d00c00100c804c00b6140c15041914050310050010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 219417104 1250 219415854 219415871
    0x81311010e0105040b1c0e0f0d0f17070e03070b07030e0d0507080a05010203060a05040c05030703052206021b070b180a050d0f020301061512020c0f15040b01060905060304030503060103 81
    0x2545c00d940108020914507218855090010708640110316151b070035070005210714030301c42c8003c985601c1100c2001e02480002081d0703100d0b19000e0458404082140750f03d83c1914948078401410103002180d4440c840d000d0442d012803c14a00e1080d07034540c50701079a4005100400d0405d000c000c41e80101d080d11329200d072000000d5544401c001c003e102c140705a002580f24144502480040099070304500d128904080f810802c05a11000340c0e03034003051074274020805465001c603d904090b000c2203070240100c40521040300f0300c207154006100b038044141e2840162088511803d032146498040c02e00c1543c4c08120105004e99841a1128540f40040002c540d041d079400c0000e01940b07603010101e610310110783c030040075880c01788241b20090280b0000020880303c1d095004104070f4009000b103015603404914513007410010042c1c5075083c28604201c41d410111a1034000300854215000c07070340117030000008150903210301d006000b00c6101400203419503c41d903405403900c1d000180003e04250780e40581 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 219418354 1250 219417104 219417119
    0x6050406120e2b08090a02010507060f060905010b0a0801083c01050a0b0f0f06030a1503020d05010e100606050706020a1b12020c0904020d02090c04030c030c06081311010e010504 78
    0x4542841c80307800c424144042410304044c1214200500c101459000741308581d0140c0d81040c12201d28a41c0316000148590031900b5100042c1440e40000d507005283c040080748000140300106080401600c51800e503a98511005030b4070300010f6403905404460342800038100c4103420000707443c140e10900c203c031074040e079030003290031200c0450700f10000c15120b11085105040080d0301d417910400c269014081000c001c008114a440040c001401c11a911031492403007052030140d00c0040c686c02808032079998805d09000303000c0c01c0c604100364400c0c0141111803103c10034a215401c100c6450b130700d407103090140c2d0340c844100079040300d4988018401079020314040c0394041c0000b00403141c45150003400c180c0350703030302e00901d050105148140206040024480965141c3d00235104080e811200c01041d9515030703580300070134000da0b0700042c800e500000300441000384041c1d40d030041d43d5180e920300e0746650301c2012040100d60003d2000c0c005201c8042106200e51080c4041001060b06040c41032405554448 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 219419604 1250 219418354 219418393
    0xf271a1b0102040f060c050706080c1201030803040c05120604020d03050f070309150e1507060b1203090102240f06061c0b0a0608011a18120a020a06050406120e 70
    0x200180d9036540003a0900030b8440038482000942668078108000c00c58558400d40d503040c2c14000c03c2c080c08001000a8100500c1c007048540c55106d044100740c155a481c60101c066400c2582d003120110803422000ca00c1d810100710200c9024107501c010500c540360383e024040b004020035800c0d0104035040000c0c040c03020b11000202040ca105e9950449624070300155402401e00d11827400381044100342e1694126030720052803260f200c12081900780c2e40c80341440d0120080a0141926401110301c0f0000400800044050a07100b2401e80076502c0144407001d03000440c05005014102502504002c20383d0100d8400b8ac0c03660000014055501e080c541e1020380c0036819460b03c03aa91030070344500c031405507418000c2020004162608113604030394180b031400c0c00078809d803144001c0008404600312403c0d82c101304070381c00c803d10040c055620500300140c0f13aa8440c6814441030340031f0f1404100c006200c034030803021a01156020b50390751010500c540301d0030019190103451841144150291289070300344884 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 219420854 1250 219419604 219419647
    0x4111617040f1d24011110090b0411060a12230a020409060e0103030509061e04090903030e0a0803070c02030309040609021c060f0509060d06050103030f271a 69
    0x491940e00045100e00800e00903c010f102801d010101080c440c02400000c140640300e4000742003c6250800303045540c1d2428031400c442094681c2002e1550040c0294801c0d43c5000f02d028158013450280c81806000ca58840c10680f400001c0000c07500901c000c0380e95104900c1c407102d0100041e424210484c000803400300a50300c00303289950002d001c108041032840f03080d001303003540c0c40d040d41c5a40c51030710b02902c2d80c0500030b0f105003d440f000503440940c071680c0016403c00c2249e0800030f5121601d5440010040a0242c42100030a2625a070903004d00d42c00115007186640c4002d03c5403940d03654a60841c0d0140640904a03050b10003800300b192665610300030704010340914140140c035802d0300001c0065015403040900f03221403500400f8841c03051002d240d081696410384950310642c445d42c001c40c92900740c00310080c1140c0c2c174040000c010550301c05115480403140342d03200e118446079044180001c24440da00060396036111a401c025a00244082c47c283c0d1f2030101c140382c1403800c04400c90a0320440070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 219422104 1250 219420854 219420869
    0x9180906050106050a03140115080702030c03030406091a10140a0815040303051303020706030b0d0f0506190b03190f080a0e1908060f06030309030d090504111617040f 73
    0x7007140c0c445c80f0783c9841100040035907842c0c074010a51600ca200c0d0f080003140000807040015071000503010900030000c40340070030300c1c5104803543c9146c14141140201251202254002a10500042801c4030b40c8801809048101d0300c0d640f8652910700c020f078024441008003a013100165900080c60601070008030101c680301000000345103800d2600800f107581c010845418184003468810200c2e0b400a070078002d503003142c2400148114500005145401850001010524019112400c010300410b803140142c44940140d411960404000415a24405c0301d894159105010040c010026800c1c1c0f848051f0196156031110045602c45090341c0c0e0115120001090b0403a0b0102000e0400c1602d07842c0c000403000e44105502c0c10a20301584890000e80023078000c00d10388000c113120380c0d028411521411401003c5852a00c403051016250710150b01c64988100e1800c400112820300c4041185c00801c500d01040d050b2281960b216440050303944500c2c800b5080c00d000105440782c010350510043c0044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 219423354 1250 219422104 219422107
    0xc1009020316090911150a0807031b11101109010315050402030108060f0708061804030e0603070f021603030f120e01111c0b0f060f0c190210030504030918090605010605 74
    0x582480c1890303160042003140540d1100313000305104c0203400e09880750340302d072461b000323000d603d500e402180609005960305408038a02204400c00b150820400c0480f5030000c400e46801e03c44003402c0408480c04e003000f46c4058482000008090741c480d5106a0804151800c60542d164540700032804036042600000d290364400800d1181d800c0402814550120251800401c0e62030301d840400c0c0329900c7c4090a00c0b22040200c00310f0105030007030121068031744000e0300140d140e01e80901c005040b21100d0746440b015004042d5160315119203001a10196130309502c1c0c051000614401c226654580c0c00c905034026985c0d206c4501e50380c4000c0c09001b080000001c21141c031650720041300741c01600c520142804807484c01107844a242c5425808240442c1c007112031743c0e15040205000c65540c455484c0b86aa9401011011480008400c8030b556160b4002e45058112040e0740d0f0095080320016a800780110350307010000c003c200e2000d091203240043c0300b040828030b41210358a903000d4078420382000300801c50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 219424460 1106 219423354 219423371
    0x61507110904060f0c0c1709031e010501210b0105040c0309050703050d30020d090206070c0e0a06030b010e090a0506070f12020c100902031609 63
    0x1424001940c03900345000c800a020b00940b0100c0a454890f0249100e0301c0b80d221180d44952001810b18070703451f040f9440c18150005140319a06120311030100b114404e94500e0396180500b54800407419504108401841c11007001d500c14100e90804000c0001c20051002030b411107806a8000640308c0b440d007411400b0740101e9402803c80d1003041000802c000c0009264603144c282ca5990308518403410003280c01180740f00c00e041501174074940c1e449080d500c140d402444e180905000000300300c000fa50126440b6000490147c4002e4121007003009820b54182030b05a00903a11001002003500b19614007e00c0241070050078409003410000401c40e410800600441c01d4000301114050314240c000107104820080251001071113a04001400480380d0094513950b8002c2ea001c0d04001c1d02c481e802a0007009000c1e0180c0e414403c2e44101800d801201800c580500400480030039041e4 = true := by decide +kernel

theorem cover : BRFrame.Cov 219244604 219424460 := by
  have h0 := BRFrame.cov_init 219244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 219244604 ≤ n) (h2 : n < 219424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
