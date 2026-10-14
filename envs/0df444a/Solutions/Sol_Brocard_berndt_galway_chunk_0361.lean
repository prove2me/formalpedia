-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0361
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:25:12.897983+00:00
-- url     : https://prove2.me/submissions/764bc52f-575d-4178-bb69-aba45c344f3a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 64748204 ≤ n < 64928060 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 64749454 1250 64748204 64748249
    0x3020c0307080d180e0a02030601020d030b06030f040305120414010b0a03050307060b240306011215180906060902030402150307092105010f0c09080a050303010b0c160308090901 78
    0x30f01c104120810807006402c00e2600c480040901c2e001042d00c940d007001581031490062000303610655506001d40301c0c807100381030003078040e02400c00c55110040400c2d003159518000712401070f01c024000c500300f08c0308110003100c41032800350b03c5004502070048213201c40b1009334440d00711125035102d1481541e50110410008800104445c02250300090201320820402d000c41c08960144240f40149403e20101c24845826500514841c0b04240e030740c0070840c4000d88040e030481c0e04036a071090f2141d8110b08144241e074030048200e040c01c0011000001c0c95141911140e040351400d4121284080c0c0020500081d4a00300b0f40b0841e02e80c0c0b80c180b02d21b1030360406210207440b15000740f0420010b8a4032751030740f039004009241d42c41101a0000000e2002a0307080c4c80701d0000b0500010708402042c40c005000c60841c0e030010b1403103203a55000300190315690a00500b5007443c3c003c07412400b010312071407802c000c07440256072100c40114071400b45161170701c0b8075100300310350789005800203046650414518120300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 64750704 1250 64749454 64749463
    0xf06070216170309060406030b041404050d0f0e0d060504110603070f08040201050706050703051008010b28051011060a150302040207030915050c0c0307030b062701030308010303020c030708 83
    0xb01c592a80641c202418040e025045001d1004c56960001006c600007400340d4154019a03500c03841200d081090000c002c40621460100f42e50240c25680280a0303140c80794010b1120440704011400c0c0752828242c52000229840043e000c2115903a4075642844100b0400d07080c010000070040322000e040d072810b04001018246040d920710b0400501402080c2964081e0302107400803030700f01c10305001ca0310704403401a01801081d51841d01c07030041410009108403048c031038071440b010000c2040e2520118000310842030a080001401d400d5811980040d0659031058401401c0070359445600780e0218011900741000b00c001d011320840740c2001849606150204202c03815664100e800607150813590404881c5460650020041e40700030400c3e078060070341c01c0409442d645401d40c1c120f81c040c001d00b105050701c86015110013049201d013000071a01501d81069149000300f0038912070b10940e00ea001941d18100403e9209501050350600140706140e81440352a154a80503001415503518095a00d60b94 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 64751954 1250 64750704 64750709
    0x10050402010e01140c061612060302060a030902010e0d0b040b130201090b07060e0706030204230607020405040212060a0209090105090f060111011409070f05010f090e0a0204030803090f06070216 85
    0x10031011103414020503000700145c1d040300c01a28111986881c01c07404001c10340c0c40280980c00801c008102c00e10b5480e0310ba0007500284da9029081d1400c0c8030302c81500391301924140750100e060100e01915400d01c1d8440000407540b160040002014504090410800c1034401609210005440d841d203200943d802030484800c60710311040055071081c43c2c3c18584000d2250a808001c50300404900240c080da254000d001074800c031088404000d80f0107a900701c88a6455418290480e4091080c03c01518040d442581c0c4107002514446000e40d40c2890a03041c940100d0ba480f2080b640803542d103003107092206d5241e0140c0801d0700c080509041003510000f00400003041541003124130701c040c440c800d43c203401c010491056022980c91505000c112241c50320824042c24600c1d402032040041c4541c410031302072000c2c001c0d48d04c650002c1030514208070760115004200c0211140c00b000004001f41ca214000c500c2400000042c201011018030754604105010300708000710350010880085203032030708016404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 64753204 1250 64751954 64751957
    0x507030b0d05210d09050a0201020c0607150507090308120f060d020102060604090501020409060e04120f0507062d050907080708190c0b0c0a1e030905090601030f020408030c10050402010e01 83
    0x4404014030030b2400d5481480c081c03420660900a10808201b00050138550382d9200f6000e441c04c1e641d990044c4100e90290401c05821440c005c0d80040c9050856031090350440f48902e03001000e641c694581c5150b6900c1488502d28880c203403030400c03410342a40ba0550f9001502140c6032440c07110a900003c2d034551000c0c00203441150b031038483e80108182541110020448900c0c02c0c0800c903900c44044c03d000e98200c40a840c524222014001800d120b00d4040f508401c02d03446a80c240703840f0b515188010300c00d01988102034892240310342c9159003d141220114400c050002c102072610030b880c41c0c181801030f4400c108541c044c50041c8120540030030f070402003404198031001c4140706420884c0051800c3d910002c4c8125002898540d104404070b61a152140038001301c0c41c0c5d05030070140d00440e407058900080e001882004061140c0c0c47c22212440e003121051402140c125070001d00d000890384241d0140b8110b80c8001005084204c090081c5500019450f01c10003080c50503400103001d405000c41c1990 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 64754454 1250 64753204 64753243
    0x705060f0d060f08070306050901141602070e01090501090c02010b0a06030e15010801050916060c0602030c1201290913020702030a1203090c050303030727180507030b0d05 75
    0x10070140c03240d02a90007041caa103040441c050340c035110540c485506000994459040c507001400e415014000c0030500362080070800030030750783c0c5500b038010070b001000480f0850013100700004a9005030f000e564060903c400340029294900300244c802c8403910713031540c000c0da41003864074402030741c6402e140d104951160901064000800c0a40f9040000840155000480c00d0300003051000d415808a40301d0145041200e03104007500c202500e142a10b44035034400220f20b048144005401074002d1504500304145160405081c81c1f1506040302090300011300680b03101c84490f001502c000b160740540d02e42e600c8071a26000c0d401c00403500d030211820340081044e0b00000c002c0b0031510100214501140c128003800351004002034000c000e41001d50007600e1000c18000d0115880ca0080b0403a40144126122003003450611402608054036510701c0000401032000005501d0038540396501d60400b003401c2c001914030380050050300311050300002902419007980200001140040d140b895540c0f1102c40a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 64755704 1250 64754454 64754467
    0x1a25020d080a24121a010b03010b070f0618030207140d140c0303070c0509060609010e04090201020f1f050a1104030b04050a020619090501020c030a0605040203031306050d0e0705060f 80
    0x80308030004603036040400122505000404e03441807200300d01001d04c40c51000c403082c40c0c146082d520f4404203000314841c0c000c041004004a00410006148151103442c019618020355140c0000702c99400540c80c0e0f4100d010042c01080650500020000d05514070100d59491010404034000c0341010100a0100840030b8029200354030070010b4851521000b02100c1d41c4002c50301e45911401c03410f200c1e0314041c0601d90003051040c901282a610320b028181d55210200d141401040003422039201c090341540a10300c0921a075000501c4850701c207600140308403940b00d80d803072550003c81d54014070f6a2211884c1030107180c0955900703c211012a40c1140c05042191107030f0800703a0405135000002540918000f400c0e00352504262516458441c09845c0c184005545900580e1180c01044000d030349500a203143c880062041d520060300035001404032801c1400f4540c007a0a00d01c2c1a411100102c1d40214000ca5030001c14040c0340c2d04910b6045c00f030310045140c48040f88445c09140300742c820411000c201c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 64756954 1250 64755704 64755731
    0x60726060a03051608010c0207050907030902040b06040b07050f010b0102060403050c1006030303060311030a0b0a1a060f04300b0a0f0911100809030301050d1a25020d080a 75
    0x1c8101070b58128040e900401540a040800001c00f40304800d069428000720010302c0740040303403220803210040c0031140c250780c41c068101c0c010004040c040303030700690315018440070b03407100805400504500b1219968442440c2425840c0800115140701541e040c0400c04030582d03404500c50360801d500d0b003000d58495120440c024104517482c010707401d1071494481d0020034550306410600860340500030001c4203500d140b041c5a204c81d1031100140500b030102d404107003800142d60148100341c04981141662209a0002988643c000c140a180c0300e500410140040e0f0342c0ca0740c04042c0710b545c0c60019002c40b0703002d905008820302c010720083d102181d182c0018540300c3c95600701083c528580181001201014580405071500c1c0e108254040d00904c04500b02950040b1581800350207654021070850b80782004101003403401c038008807290046042d8021000d91034261030f90140e10421940000091030780c5417201940d80c02200c0004560000480346042500403038804d4002c400d011020070902121141c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 64758204 1250 64756954 64756969
    0x1317031e1e0702090c0a09060e0303210a05070c050a0209040218070f0f050f0d02030403020c0a0e0106020c010819050402010e0d08030f13030f050306150705060906072606 75
    0xe0544600442605081c01c045015000303101451084803486402c0e1111500b0b605140180c01b0000c0101e6402c1209000a50041c100c0c1c5450b054000c04a03890a0704012550311000c1032100000900c0080c001404071480c0c090051681c00b0b0030fa031410001407051a00e0b1f159482c8115003000c0c0c0520310940c0442c066440380c0088000049821143c81d078182068040145a00092155035000030b07050010240018410350460348000e42d40c2e4135035404c01e07800000c1f1400030750021388224190704c51171940c5a0700b13803200140310004002900c0740c2680703985002d2002c0d084c120052441030410058508101082e03000b1110900740320714460000401c1c7c4d50b02d00c0140d0720380000081c05c03070380908285140d004121b2008020b40c03090303e4004240304030f5140c881141c03000c4008800d004005c54541e443c51484a4440d5000c1d5901c070038002c04c0c40d4841e1001c543c03101000d81c070404058502e6000f900401c0094070042120640283c03680c64104603052141c2e10103410514858030944c0c020000e203002c02c086594441 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 64759454 1250 64758204 64758217
    0x50f030c070c090501030809010906140f0f040806010b0403060612020916020c0306240604030209160201020403021804030810050901260105010602010603050601080a050d0806010c15021317031e 85
    0x20401c20103540c482c10240088d80100343c1103030015003a8000850318070720a110740002020303d20022400e055403da00104240c000c00c0c03071051280d1084c8000103586408202540c02041c0507204140c2d03a50550034a007056656a41100c00518246403000e801611404582c40c0e11404c8a0000d82090301e44a80483c1050180a0034540c14480c5801b4081110214000e506800c0004074200042e00e4000c41400706034010fa104c045c3d4000501e40c0050010004486800101403040c4001450280c0703d50009204580503a00c20214440301000c00040580109100350060740181d026400c10f46000002200303c03005008113400891402c40d1f602d648100c02a2815020384840020700c015070315200001d000308000e02c01a9054403450f400000c41400201c2c5403004542c001c000703000e040103a11800d03070740b1080161003241017001d08411003010403205174015285d064804000341c0d80f40c203c5078642e1161250b54200c05d01c040e1080001008225000040320601d941d80c1c103400b0250811000c0c440c0ca00d02890 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 64760704 1250 64759454 64759469
    0x120711031306030203090d0305011a09180108060a0b041803031a060d05071b0302030409051801050907051003110702090703090b0415050a0209030c010806041506050c0d050f030c070c 80
    0xa07507022809540640181d0b22404000f4100c801d42c91071308008030144c81c0c0a120307020000c2c04031040036508641c000000c00e100703d80038080701c01400302402020840300d003da0181e100c581200741802140c0d101e82c040e100e24044115000c0c0951600d021642c400d000c031100004050642c1c40d040c14200d201d05034004540c0e040003e004545650100c1d5000029001c11105000050000d080d054046500c0b4400b641100da01640214102030412910000400001e0014001c0d1941c0c0800d42c0b40b08031090059500c94010880a4010945010240311428410300e40c0c210034036080c0304000100756000b000b03661619404644002c1e046e203441c0c8056000b45940300000c0c007400080d60403c01070081c80e40c01500521014a0100442d9840c030008900b24010420001c0d4160030050408080e9885800035903001200207000040c40c0390f102c2c90f560000000f42d4094804244085021840c12205010600d82a4660304220340360000d10f907400e0004d484000d01d4881c0920001c00e400d0148140c50f101000640000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 64761954 1250 64760704 64760737
    0x504052508030c0703111503010e0603010204030807030c0506010605041203231b0709050f040b092a090a020301030507061101020d05270c1c060b041508100212071103 73
    0xc004000b503c0d444140010f0b98459080000a0000d047c284c1c140c1000d0240c41024500316401e0901c14003d0b640701900c010350542d004e000110105036900020128070b031003a26118071b800303214038100c5c0c100302c81644040b080c80710070322080010300d520701040e50125038140380c2147c070030f04660042d0700d1440b058240406040004503440d91030480d0241c1c0c142403140d40d801102d000d955030382141c10940e2011034580d015450b490002ca40000c03103000742d054201c3c1d100401d498950701017010340680c00c18510010800b99500e06141101070610030015a002039400320258a15030550f1a040ea42c0c00c0d0911031001004101410355154000c03c0d41a10800c2000110034803403403d0000340012407001100715030508400140d400c12541800040c001c000140190038101c00c072848520105543c0d1200384256480c9444d120b19901540d25032060100313207007101903e40d4800f81040010b6142802d050b08042101d4410064405072000d061039480d806034a41c42c000079080c000c01012803d6001d042e04041c0ca080c1c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 64763204 1250 64761954 64761967
    0x403110d02130e0f0a06060e0c031005010c02030a140c0109090b0f0904030c08040326120115030b03060907142e030f1506030e0d080112020406080d030f050a050405250803 75
    0x2200e400060852300201140d503115215010200403910040e903c2c840700c2403145108200f1540940100d50040d400182620514141905c44601c4031486552540350384d0046a00082c075980c100030b440c8041c0010841c2000300b44039078004a140c926210524510490254002804061103010000f50f89907100382d0140e1565904c2c13a0038070340c1141d0385440114a803030b8261102c4000d40e10300196404200c042c80710100503441c041d00d043c1c440440c1c848860030141c450141c0da03801d031420803145008100f4400244041460141d400398100303c4005010300c2135107a084484440d038207011407021801c0d110894011000351220302900240102080300b01e41506100750300a000c80f08222030070481d40e25490600c030680c5a20741c002c0d1a881121800740c007140f80071b00140090340b0b00c3c07040f1b240300c14405000028010740361146039190680720a12800000e4555004900c064600d00070190081c105110901031401c080c3d45882c3c035900761184500840128840b03070a428100c1c0c0700070000820044040da0758070350 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 64764454 1250 64763204 64763213
    0x7030c110303160b060a151e09050a030807020f01140a2f010b0108090622110a031209050d0b0a0c0207170d021c05040303120b040f020403110d02130e0f0a 68
    0x84d00700c4440d84220b96483c00040c0450f11140405070300903060740c5000c01c030228403840401c0744800c0089071080244204010072191607185800020b1400b46084540b19180c070720400595160f0102e41604200c08032808100d009101010b4500d1707401035041c40b48044041c1c1102040c01c040003030105800000d000000103444006601c98154440e003130fa900c00d910741d1070007841590f8400035585d22004000705a909030314508508401d0052511401f000204620001c0000308000b103240c20503603d045036006d101c40c000350014a040700900058404020220440d1120900d1120041601180b1910351807400442403017409030300040c028118401a00d001c072001000d0f62188030184500c0948600c4d8513401c280c104481d0b8080a011155071410b1074981550b6003200c9408114501800d083c3e00d440403000140d40e503004500c00810b51000060b22182b5600b019028050041001d17805006100018809a101d100c4402c0c03604d041c002c400305c4d01c13824100340d03980341184c90300c1312003c10700841d0317105020003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 64765704 1250 64764454 64764473
    0x803010b03180d020303070e0f09090601060f02010e06010306020702010c02090403050c100615050a020f0d1e030c02060a02130b07061401060810050120060a0e01060b07030c11030316 80
    0x180d4440140300d01000c0c41c1502c40380c1c0d4000000182015a00900000701110f12400341c040003108080c0502400c44600b402144113280c0c19103449086401000051020139440154040c41c40114030007488605080005940c989106000280c0b0190300094128256405401c501309000c0c0e029010014078a081d003070041050300152060b1405002d64030306940401c1c403038000c0c03006680524030b415080021806081e40c0c5588410580ca082d80902001c42007550070038000f20500c0a150388501c05da401400c2e4044400941803070422007494a03102c018000c80750b00044c0503071f2000e80e40000607551040100806a0404180c2c002d940d12200082c0c42000c004d5503402560780d015448880c501d003a6204d020965020301c082700c104a01a6a000742000198030a20052002128038844020f4161042c0892828075004a13038405803a40c46142c007a410700340910601c001022a00341540c1000000d41d0020300c420f00d01c40014003240803104038881c0c540d909000f211501e0f0b1000640001c0350500c0c1c50142ca10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 64766954 1250 64765704 64765711
    0xa24030e1501090b0105132903150907031118011206080a2003060408030c040f0303021f2c030405041811030105070c022709070e0c07020d0f0f0803010b03 68
    0x1507400c004e4840702650160b41900d210151880d00c0c504440e0800c040003d401c8601d00401000494019140c14422004c800642c050a00030b00c0101c4e0714240d00d0103008442c240541403000b00340c5821303040d2503808034620564100c0700c800024210f41100150040321400e0010151780c03145484c0c50000540040005601074074140310714000c2c2400348a420551030009208485103030150000d10024001600840003994408000307410103040c41e844000d0303410b1100003500202d02607448420010450fa2030b00c1c1400c42c01c170600c2c220600a82400d4141c50700c911100b80503048440185800d44050003c0c20300c1075501914002c0e20400c0020341c001045005c0c90720915058500302d00c0224448920f041c18001c1c80d2065445498961010919a003032000b0014112001d1460001050703921461084552403140205200c10003400610309045580c00301d290080d10044000004124003130058560f144141c0c0655001420110366103114248008000f07040c01c0c005001d01e10010022900000c000042c600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 64768204 1250 64766954 64766969
    0x11010c0e0a080d082809030f030e0a030e01050c030d0f0504020a1d0c090d06060801020c010b0a0509010501082e060e0607230a0503030c070506060a24030e1501 70
    0x1503556801c1240c0f21000f651800000a20070b1000480154216000303908090905503000342e1020a913030618200d40b04c90340c0440000756400d010092440e07041c0500e40c3c4071140f14001d054550750a0340c01a00841d000038025040c090041855540420184160b40c6d0319011520b083c04500c40000900c0000c1000310360481c406c202e040e1020030048003181c26411010707654001d01035030751200300030920f140e00051101548a0700c0c40c5000000070782a4080e0701d000b040418005610782c91118929420342c2d0401d28682c4c02014542c400b00700319a83c034034140e4119003081c00c000c0d0484d21903240d00200031313580c00d0b10211030301720b2448803180961001d11108102d440d0b03a07454100e0480d5038410401c0a21460002074013800d0ba603449100f0807035900c1015554100000304407030b084031083d07803941d00755002103480030300c0c075080810b00400307000c0d0500c8920707030001c0d04488515416052211200038141c11982c80f10581482d520615440d500946c42071b03105036071a9007141c505052a122000140d9024080d80341c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 64769454 1250 64768204 64768219
    0x1002030f06011814061602040f0501180c0c0b0403031d030901090605040b18040b040c030b0f01260403091d0a06051005040303140409051003030206010509220311010c0e 74
    0x44401031900074019140510900e1100c11665000c000b1250407107686d040b1000007080d0414016500c078407a1540c0d80c20b07400c101007402d48c0b408201814040d00102c90380001c82c02c008610050a5110903620040c41c0d10006a20b40e90325681000ca0052410002c1500d1a450b045021004008000701901142e8003d03030b03880010039102c0c40111514002c5208031354550f43c0a03c0080b0042d00f006050000c1e074580500b00140f00080a03000606550540100d04046907940d07500c0b14031414050710130501183c0078200460a607800d002c07003c800000b488040341025040801040030035100c0c0e00c1600013024130f24a10043c031083c2200c59401d200080d02c000e102140b0f08480086c690502e0068a1003115068440d5401c2a1440e1800d03150703004081c02c0454440c40801002c1400e801701d00c80c2078010010300040e9240281189400303480c198040c1c006602c00d00c40501000484110070100007070200b03c1c1000e00346050310318031f001d0300d8802d0035100200c82542008070703a035206940321100c122640340880e41710 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 64770704 1250 64769454 64769477
    0x3030206090f01060e06010e011403010f0306060e01080613060b06030103080901080f010311101101020414100801050f1e03060411030d0801081e030705070b070b060f030604060506031002030f0601 86
    0x10b6089411030b11916590300b80c0107000901c03941c000c0240040004c0b060510301410400740303030311b0001076000741c0000c0f807a42c0c040341092017801040e11501c406480304c1c803030301e040d80d5041012041e61844010300b940d0004040b503086204111850300300105423440038004030703205d5841c0c1ca00584103801c6035042d5400212140009000e00c40341e0385450741260742043d0b1001c50001d00000740001d01e60b2982c1c00f50140004884008000c075824802000180b0344c0f221000c0c41070489100f00300078403403000c041c441006131003070060085581c3c1b02c00d8151090021070700d8103160752251007260a14115100d005626020306401c00090040011082100b111f08400b51907040021460a4403008020b0040024950011110f000000711501088003d141c4041c2101d040c84125036440380341a0321908000039104002c40c94000300820440d40d1a0421302c215500b032402ca00120100b03a480e407008201422407922803010072481d440034070415020007030140c41950381b450011000e00410b20300b039541074005018002c0c0b6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 64771954 1250 64770704 64770733
    0x303030f0903090504020903010b03070b0307020706020304060801140d0506040317010b0f0306040218060403060218060711010c08160f020f121005040510050103150507180b1e040303020609 83
    0x11440c0860b4141c4408410b981881c091100035000309001d15015941c40d2880600307079508104100040205105c0c10f0b580746401e040082c14402c440c3d000b1400c1d5441030105009090b000310704541500e0b1058181c90844010130f0000d04201105000500f90703008842c140b000303040c7c1c040110880000680b0900c1c40326661900a03100501c211a0340008600061000c141c152505030010100050442c4070f50010380000c0c40001c1c0c040e4040d0744100e554950006180401c003804000d03094001200300c0300c2030b081480f01d40351391b004010040f0740d00e0f040100700481e440811090700113840400545207119490710903907282800304030b0ba2090060f8841c4005540c44505443c0c0b070842d2a2980382d28001801d590f0750506051005003c029104071100e0003140010b0310709a01d81e00c500b500850140c0e003940e0f0310700341c242025005c460f40a0011400c01609402904034a441d00c00c1e18812a40448c400a80c4d40c409800400214030040b00e0314100030070300203000400d048d80007407442e01941ca00c0c815680001010b440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 64773204 1250 64771954 64771961
    0x60807080a270c060f020307020402032703070317040b0402060714010c12051f1701020403080a030207020f0910170703050d05090112051009091b0906080d02010509062a130303030f 79
    0x1517200180c0c02003107039030700504064000d150400f419030141c04602100c1d004580380004002c0303941c1c04980c0003140d40c0b001d06031b00120030148810f54040e070260509007512740f042c1100d00104040d000304c074002618070412401c0c1002c91142c8001400801210b803210000070030584004210b0b100107428070303010030360300032048450071002d100e0704e40300d2001d0910b084401100800c0900020203155400e010010100b000c140007000300c048207a400581d2a0150b02c1001000302d02000500d0240142c6410482c015807600d00c0da13001d8a0400007020905e190340b8030300524054031500000c1a2307002c0c042a0a070700c5078204e4043e0142e00800d0700c032044008a56034020046a10840e01c1c10a4107040c11010403d00c2c0e200d6009012160007400b91915906011800c2c40044001e0351040001c2541c9010420100e0028007220054904500c0244500c0c208003848a0360303184064150308001c0d09200c0824034107030b003070242d400340fa44400000684a41d29910004264140c902c03055020905005441001805030b10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 64774454 1250 64773204 64773227
    0x7080709111909030b01061e020d021203101206090c0501050c100b040209040e07090f02090105250c090c02070b210a02090d0501020405040b0406060807080a270c06 72
    0x102e080040d0804580c1022240900c80b1090000442c4003102050b61600031030701800258941502201d41c01d0b00480c100b084050420302190030040d1070341c0720143e0100d1120074050306420415240d45814514282201c0a68088a8402d04402100b030820003a41c108a042c1c9000d40754070940c650355440192903c1c45041040c0711700e500201e080419a402e903074450716440002074001030800b00d0b8940420f044410340c15110160340d00c001020042403009000c2c180d8604c80c1042d00390f081501110019003540500c64580c4180c2d00940c0700039810f070000101550140350000031018500fa034501d5000000c280e000c2c018401402082404564500b09800b242c0c0b2411241c010014804424012901a10b6002d0701106841d50200a842c0b150744d0b90040f40e07000c0e107004000040e5221710f8541000115254110404d000703c0c213112040005941100d40300382d00c91001d0800020355a240307a40c4c5c5004000c54030302d01941c9a9000c10003002100c8000207400c0480c030a51000c02c9907512914161881c05151 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 64775704 1250 64774454 64774481
    0x603010b1302030702010605040f141612020c030d02070305070b1e0103150b0a080106050a1212081503030a0e010807110c0118080a0602210603030708090d0b0907080709 74
    0x30541c440402440d40c01140e01134198800000c507aa119000541940c0205580c520011740b100d140b94040c0c1110304140741c010000103840d01174481d80380c001030305070001c0184007405d445d804100030051304003d100302c075031310140d420f81103590f00158a80501680c01c80001564882e80b281c00241c40c1d440c00c410141d4400900c0045200303107030310356594a140603030244080c4100b96110210005644c40c0c8035803100103014003400209145041c2014054408016402800c0040811050b030000c5404041d036a494820180f901011542e901c1e10302d891100b0644000c0c07501840001b5220b42c01903440401d20301032040980e00c41d10f43d91030711001101c0741d01e01544041c1c1703980c000e01c041c03d9096000c1c014030340d01940035502d555059075555000c03e0410252000a8403582d40000c0c603500c0c414102d0400284440c2240000821802c1003400b1030b40d60700551030700070310150b00001c070440c00395624502c507d0860781c0702100c42d01a01c0c1003003400f40c407603141e1320950606209540d004516540709020b007c0010030701 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 64776954 1250 64775704 64775719
    0x6180b07030503160c020a0312030e0a1a1e1603060602010c0801091a06130f05030706120f0b0301051006030c020c03060402090c0408070f030201121b0e06130e0402090603010b 77
    0x4a510301c010403131920100005000d445045000140c031041d10a0740150700900b181d200702c2c2550f4070b0140540c0c040303100d105100d41080d100e1400080c0e07840061111900400742d071070703003982d41c442e409102c04401e6190b240c076450380801000391a544480a062a104140d6814480c240e5264000d90a9481e090f06100124103924014011244c10b544034907001e2180b83c910009005000000c501c180d4040817480c8030400303285806110840c40c6403904801410154000c208031450071304002c0240c0c0182c010b00000399100c1d9103022000906401214030039400400030010381c00d080d14000c551040342e21840001c20300303200f43d4150b150b0001c59507030714024020f0f000d4031883e601c56080100ea18802056400384907030a00000c00c1d0800200446400703840741312800b0401d10b065000241c0b9a0f01c901300c1e4070003503500b0801010140420450640c101c00020300305807204089070000180d29005103c040c01d640488600001003045242e0f000500171402078400c0100d0f41c6916046c07500340d41020501c960090749 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 64778204 1250 64776954 64776961
    0xd080702040f140f060418030305061c050d050309120417151504020d141f1a090618040c02010609140601090302010503090a020414090d080105010e0d0309080706180b07030503 77
    0x240003569640882c5c0207000042489013084454220320200c402030b00000c0e901d1041081d203042444910b0140c0c0360304072a0070041039444d51110f96a00392601b046080050220100f16044420410254101c141c805526200c0b502c40740e400300b20317620300e5035144a03070b2103201c0c003d890340c0c200e60400a004582e41030b2006074006995040c17102a50102c069019038130350f43c2140020402c04409030034010200e6001201d01c1c0c002d101c42c481904042904071159022945005040003003d070b80455251110580c0c0d43c41d05d4884400d8800d00110035041015000350070b01c5c82c01c01c08182d065010320282c542c4080b0400c5002400011941e484004591060201d10b0f040f0040c005580541c000e181d00101c001d0460301c440049074042001e944603100c000105e14118018084451001c0c004945410b8251410310955890803000a01080507014014056003844001e0418076118038007040250011004450900d960780000070b00d190b07031001d24011a00b42c01c43c2c0114841a800040300c0030a901f50790b4607800d644 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 64779454 1250 64778204 64778221
    0xf03050c16020102031b0a030906030c09030b040516030303020a12020f2b090303060504051608040803070302071a04060b1e01030203100503190516060c060213050d080702040f14 78
    0x1515890030b905512051001500b203c2c880002c0400e24201000503008242c031515000d4001d0f40d0381d411000905041c1a80310040b030340d1110900d012a5004145082c02d5159820a00c2c204142d41d135039070300d240400300c0010041c107805030024800211680d0b1085008200f08004400300d000e00d201c0c4084102040104200451601c070b0110048d40000026000900d1040f03030302c0c811620380700c10440100f40c440790100003500d454030595038400b120381d051400d6600b404500505910b40100003c040b90004070206100a04c01e50655218545c00550030017148040700d801c58401d041180e04944103410408111824203001d000010b820905415007408582a01c0064010350002800b00d81d0401984400080c01d03501004144164030300907840343c0060401d4100181000c240d040b4203d1000d03440d280400c5100d60040b000301c04140c00c00001030b102d040105035100c200f16940d2002c0d6000b5840906041800454001003159a02c01c40d401c100ca83c814100720030958950b03801040c140940203000a034942c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 64780704 1250 64779454 64779487
    0x9030418110f04090b03070b0309061308090607030e031011190521041a0610030906140108060a0c0815120705090c1b0c03031605150103030f0f03050c 66
    0x41c01e01d01001030514800b00000400c940140c2d20401203951164130a40c9035041c00d00900c03000d01403481c50070f403951408030440307940d903080907100c01c910440410800c41401141016146e1a5030014031140d620b0101e4180101340710f0700e515503030384a03009005e600400413210744070b1640e00c503c02054103400c00300c480002d64808003070031580e6014810100841445070744820a00c40c04400c0d04801e603412030426003008150090060505580e2080100902105944080c0602440442d92401040701c00c034915148001d0070008541140300d0240c80004a00c1000100e1468070074403d0310401c100a440c0807030704441c800403c0e130304060080c902000c5119141020340f021400c0b5455042194400c581e104081004448110b07134500c0c0151001c00c0d04003001c3c4545101c6e00f1344c403e020005050460103400081d40b01d1051040c56007921030b04840c000f0030401c1c00d011401165083c9a011045036039a414042c20048100d0400c2c0009003c504d00703000c803903000b482118094100c101042e82004210306100340c40307 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 64781954 1250 64780704 64780721
    0x515040302070303140904140f07020c060d0218100801080607090303170a021201080309030c04050c0a181a07020906041803080a0f0203041401051303080f07110d0e01020609030418 79
    0x12071004010001d81074a59010b00400345107500c004030200e180c03001640c4610b0201520ac40e0031074000c00f4841e03a89540f03060503a900394842a0700140e0ba1411004e2400c02074810f03c11513900300329110514145a178210751024120b800900030340f119513031103009c100c4030810140070090101f2a81c1c001409228402c20300340380c0c0440310407401440c00c10b5400103510001c000764010b118039840014000c0d410b04050002c441101d4041d07030107200380d0070000742030300b02030044035644020480c02c2c000883e012400e850003c0b0050a0f0150950060b0002c4110764403550b02c82c20060b8020781595002c9a254141440703090009035801c554591f020b0b0880c0d50403600c50001506c4010911b450354030400e03075a21380344010b6005074400c0440b80600248200c071035003074900041141c00c20859100c3c0384408a0f030000d10480d0300044040c48000c0c2d0381d460311810f4450010603031542c0c030f55108400c1243c1c0d11a4000c0259213000d00242c00711010396a69030000c075943c1c8101d000310308076805500845604c1d992143c00c001e10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 64783204 1250 64781954 64781987
    0x3040212010207050a0507060314010e060105090909010515090906131b0b0405040e0f030a1202040e01060c0b0f16050c0109140d090e1302010807021006090204030515040302070303 79
    0x30100c0d100140909a03000110252219003100721843c040207020807000d4010715041c14180004880f102040b1603072041441042035089110340014480e070300c201c0484200c076000405004060400c0540c0b0b5000301000c0301e0003202d401048141036510719201414a1050b420200100b100d9542c0c0703030b20003c8081c54107600702c9950a82c0d544c0c00706040705802800c00035114400700c640e1650300e04001c01c030035250f0b509120002900103401c0031810800100c121100f00b007550516114482d41030614900078841c941c0003c81305500c3c90700119516520100302c2e42c1850083c02192243d032519135540c44414401d555021406c00c9200c200c125070380c0510040e06a4bd1400400050504829100c5620650b0151401415074020651107500240c004015101030000c010058000d4a04804611070448038200080d062140150024007120b108100064a00240b48414030085a40d0302c0420080d400c5400708076140d01a10101c0c6410002818103648980d4050340108240c0e07181d41c409030350030f6400000051 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 64784454 1250 64783204 64783219
    0x7052808010203070203070b0f100b130b03070302030a1406060d15030b0f061003060302062b0603051609020702060d02070206190f0e012c040209030115080c01050f03010605030402 79
    0x99800002e1016600c1101c0329000b641d0350b142c0a14044150020044c11544408094403d000c281041000700310140d0700404901947c0380c0240c40d09105a110303c0d0310002e6004000000c0003041549a00910301564103054107200217040e1140c0e0542c6002e0413100303141c02038820711400c0e070513484542010049885816460506540342d07150206000c4080301c20049201c030340e405111150507d410000710640c09490300304102d07800c641c001000e070301c0362551622294110030103540d01650301000307071085560001c0f41008900d54920f04640c40310300c0701505002e181ca801600040d0746489008803850303980e004048504d0029100503a00080d04813031016030304030340300b0720120780180d01120700443c2d2a070683e01d46101e04006200002d10f9000181d00e11410452008140c1d1200002c0c039580c00814001035600038041d0b2107000100e4020b014140c2816030644c00e02d001100304428400395501621082000c1c0e442d1410039500540b8030f17204007542d5031a995010801002158070410185800c1f1f803000b04002d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 64785704 1250 64784454 64784459
    0x1e0a0b060d020414090705030109020f16050c0102010e19080c01180b0a0b0a0302010c020906011103040f030b1503071403030d060311031015030204050402030a08030106080702010e070528 82
    0x1540300c0d0440c0e80d2100d003407a030004062003203044460080055840445040c40d50b032800e07450041840c041032258514a07900454403400ca41001800ea44000c844c480240a68090300d00f0981e58508054001d0b90240d4039120b04c1c48000702d0003240409601038800e0341d107500c0600c113035244c044541c01941c2916071550b1f28001c20002041c817401089906000308894032450a040c00c0d1070003210317000340405100d20355544003000140d03007080c140200690122010006a030b112401a03078880d00941520100d070100040c007003140e481c3c4203901401c1e03a00418010801c0c0c1c0d640c1240c03866107005001c00b00d5055000d800c04004103601c03202c070f40041d200068142c86c00d209182f03c0800036288207030011154507182c10444243c908003003143c191050f001210a10540c212100070010162280c08041c1c01a6107940000701517480400025110380d44c084131590b503941e580e54004000c6072050300e03114015400d000e8900080000060300c001901d20040600c0065901205291511003a1070b890340071010780707291300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 64786954 1250 64785704 64785709
    0xe06070b070801030611090907080a060b040902070c0509130f080f041401020d14030a0f020f03040c15052106030f150a060e01030c0312050d05160809061e0a0b 70
    0x11240103500640701c02c1a59415403514409480c0c4440b5031458600d82072104290a42d1050b45d8181c000c3d1a605046002c1d458070001d6030054000d94100c0350354030000041c0021903d11503401841c00c640600b0a83d41d25940b210700708000c80310309441c002c0d4580d5880410f400881e903c1c0c0c0c04040da591081d10b401e450000c440030403200a4000360310280390803400d18080082960140411a00c5050528215075800d4504941c58101d000262801440c2030362805ca803090f071f01866046550f0b031544040e0f035940345d1a01c0e142c98034204084d800380420a10308031450001c40d500510564000344084410f564501c0041d00d12440e0790071008007107503814031440a283d440b030348003801004010040a59800c400b0b213801c0292005958850313200c90741c601d180301d0042010032241204942520740c031040340c490200280b07900b150340b40a03802c1e0030b1441c0c03440c1105205440d14800d90002306142c40340c0311682c540d610170717084c0b07912a00e0441c2c41c1854245515003504800108a014940c04988081c0009903429040003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 64788204 1250 64786954 64786973
    0x103020111071a0306130c0903080d0e190501060e04050307080901090302090a0e010c0507020a050d0804030b01080c1003020a05070b04020102100e06150a080d0309060906050901090b060102070f060e0607 89
    0x6001c0c900d03072000424464503050444030242c040107078200130304c003a110b490f40040c0182239512000e02101c41c046a0b41142c02944c0e0881103100d00d8040484491588482c94400301d20007a940c22030340c56203030080000d0013100402030984100e0300803010314102040754580d84581d41c40500b640b41002049080800103a4800310322070f001d11440880050700b81c601c9401c840c21100d0154040c014024180041d0700180e81c0d150441007034480c19103a03051000501d2405e18451701440d080100440c03150070004c00c0401c800600f06000d40c1003242c1102100c8181441078049126500f00d07080007070320070013801010035940704107140c0081c410b104440c04035501c42d4648085807030410381082560021010700903001e003900032000c1071101c00c0301e2000078507103459245607440c2203a038005410701d81c85101c0381c4140403165000d407000641100080c440b038500101d040f07000349942903013114421005008941e0b80e5200240035000e0700e91489000346140d0501c00207403100321007121400d81c800e40030460341000550910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 64789454 1250 64788204 64788239
    0x304080904140702012702010c0c05040912120c050d050601020a0b1515040e0f0a02070807030f08133201020703091715070e01051209060613050609010302011107 71
    0x4888001c9041c0404000d0070f684a103510541240c0000c1c0e0b244142550503154501b410350309080c010340181e2141b501060003c0c5c01c2e030200d035020385001c0707010042c009010024a2101000d0340e42c84940205120f580c0e046a5180003100d001400500400199503482e0348820b030004c0050044821140350345d620040892421544c00000044201603a4081c2c01c08070381d00500009403208840c01d1908016a25581c081c0040000b0440b048280108032034000302d50480348003a4003c00f5095444015060140a94031201035400014010000007020f01c000002000c800e02d0344022001c010040f18040d1401e22540d001c203000d00015a40c12400500c035091000f03055040c0329031500d00060b0700d410020603556034480803d8815400509600c41d02d2890710ba038440e401006402c0851200c070003100100d81c41d01030501003480e100426014441c0c88180080c17070350310540701205c0c0003004540100341501a140155003142d00f0a6044005200660080068290b135141490490390255511103a004003107aaa0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 64790704 1250 64789454 64789481
    0xc0601060306150203030402030d0e0a1706040308010e0412080603010b0916090501052104080702060a090503010501050f130c141201030605070305060f0d050f030a020601080114040203060a020304080904 89
    0x2c0d001003008403000003c51a00c00640c0c0091821864250042611450051b148070100310b03582c2d0038040030346d84054024020f400544110000324008101c010307a2400e050b0b5054010400c11000003d051051054551050758000c024030400f1812500179030f80120f014002c01e6155481d0898201603850b11100320744a030000310303821842d18030f2002020f06050000d030021410001d0410080c0d1005001c241d544441d551000320f0102075503250300b03001d40030740940d00009600110000d00e01c0781c66640035a40c5410ba5500310020002c6980c0d5408024410882140e101e030408020300640011540c85d03400480b4001443c104070703401e0005464116551340c422040b036056410044018028403801d8859154449801e003020041ca040200000385444012a200352141c54801042410010309106c8104070b020700600b180e441707030f03581c0d0b41c0a0f4584a09009618440d0b181600d04002d40492091690080d5009005848561208420b5001a50004009581e8040c040101e0103403074860707203e4050402d065 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 64791954 1250 64790704 64790711
    0x607030509190b03130c090e010b010306060e030d05180a08060906010b07020a030f060b0301020309010b190608060d0c030b040809090603060106020303131b0e160305090a03030c03020c06010603 85
    0x4490422940b0641149011000041c440090240c0541c01c0b08480d000b40d010301e0300441210441ca0403115075030302c4d40c2060080f64241000c5620341c8605410505400c1806d803000c0c004991100f004803102d1603c18101541a486244908003ea02400082400e000451400010034020601041c09522582e000204aa11640c10480074000501146024040c1c00c4e040c24030344400d68001a075109018000980124150200a820040e413507000002d0018064000d5403030785011594503008004e40c00c4200e0007520000b46d96080c1c030000c08841c0094074100d4403002c145844880c140074180303240d00400c41d09184542008004544c0820300640710381e100300f9031284c1e103505800900c032a04002501c0c1038041c0c1d200900500840b0b030040b003076941c80243e80e400c9001228450402c0c0c031052105403000d50b41b9862401000c1224400c241c3c04030b1241e200c1040c4c46590803107961045007181d808490a40894010440800c000b91203908072211110291401508141c0714045031400c001003030740110701003a074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 64793204 1250 64791954 64791967
    0x102120f0421020102070603181704051201050c120c0705100b04060b0a021002030726060f0108040314030421020601080106050301090302031b0102160b0f0a09030c030807090506070305 81
    0x400001d090485042c03400008194211030740080d585650714080c1f041070645454000024840210309500d1030398228140c2042514800032601003640107025060150300c45029480d4820340500507280943c202c00d0000d071500c81d00405014100c0d41c00740144074204010031080010503020004d0030100100120002a608031150802c01242c006500c9250700d0003041c80384004981e0003060107504e40e6070040015a90740e40b0780c0c0e400c48003203c03050380c01d000e8086250315210120207899902e071f1040c50241c410084205800d070065420540c03c0701e00800280c103207120440c039002d0b07071030156420510404c818920403520281250110144000007401030340071500400108100b4014030004003403c1c2c000304101402c0c0d41f402500c0b4821035000301c0000e01022118261074100758100d0b100c002d504d06031030000c030350345107001c60b000c0100360341d0301d0135a114100202c2d0030b9000e1131285288042c0e145d16145480b108690702500c2504006103a83c00303101c2184000030b45502c0341001040310394400d0b46e4480d941e50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 64794454 1250 64793204 64793219
    0x5010e100303050a0e03030405060c0307050717030301060f050d0e0a02030705060310050405100b03011805060613060f020132090f1f0b030d050304061b020c0f0102120f04 75
    0x5401418100d00d5500c040040002c250000f0484201c900715180ca200c802c0e64007004179103148207580c0b14a40200d0002101c0c2c0300c0307030320101c0a429401e03c9a8161120282e4034010391440c0082100703040501c1e0010401000621300030411a019a0a01d0804034240009403000c4030460705048815480c68104604100c210700d000d0042502a000c100d80b000d0840c209080031024004440c0607e44c000c0fa5210041070103d01c3d9448000010000125075030703070f02d607180c00c040c03000210440c0a4061184c20603020501ea464040c06175007580c282510a601d045280c000b04079241d2241e20100301c15035507a60200c00d11580c07000303400302d0f603107a80042a0101d004200c0482c01d03200001455000150000241009c10800100700c0010134640100c010504404001d101c0c001000c0d688642907040c459840c0c40c030b54164000f0050761040c2c1c022a020001b5210725607005110000a8403903000580000821024920700402c03404c81408040c030407a5410041007c69505940c852026501c2e0034401040420451 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 64795704 1250 64794454 64794479
    0x310050f040c020607030b010e04060308090312070803040609080712020d200c0f0a170c040606030e0a15021c150512030913021210031523060607050f010501 69
    0x482040e9402c004440360000c0003501c80304084c241000b00f60701c5880c082d406a00c110300105c030146c8000c0080150b5a0b41e441d0074015640700340711a80c041e004d540c60340400855041306503100c1e42c3c3c02580c583c2c69a501c03507a0780c00003002000030466054005001d2400426040059960240602d4000300301000001c0030192400c040d40c0d9241d03c9510303400d2107205e413806000c680b90314440010788a28140001e1400001c40d40d1585070000c081216203580c01c01e280c42c00001c1c0f02c0c09800010340f020000740f6240e034070850944590340c1d5010401e900500c8a400064090a60204104900900103040c0700b0584000342c01130101d80d034144031090706e1742014040040800740c04001410110b0302c40c42c00d021912890703502d9000c3c088100c0d00c21400b0401c1d1f02e0801035141c04807480d0703444054141c1002e00e02030101160803000c1c0d01060764030000c041c1460b828082184541444503841d0803203020b400d000e1410380386030744800404417a01b0507000d0141034006541080800542003150001103402e6060140a0900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 64796954 1250 64795704 64795729
    0x906090f0501240e091c02060f0606040819051002040902130806010e04060504030207030f0503130b0406120902121501081b010e010509040b06031303090b0a021c03060b031005 77
    0x100000009201450381540c2d420700071107620b1001d10802d56110103030203003840d584940c1d940b0300302d46d590080004240d000c11400d2141c00f46486940a0ba140d10017404124005c0f03000341c3d0a00d81c0074188003403820300d0240c504506a171040040300c1610101d06d80c900700703036045580061407543d0082441c10780000d03000410340c040c05010008001640c944800013602000c003070130151101d0794175000f16007403507c24481030300030b950061399582c007541d45031800940d44d03031101d80300c5101103484032804191001108100c0781250030035640d00603440280c0d0700c1c400003800d08400c12680403000302ca00c0d2503074000c2031100503071005ca8420300c141c69600d4420284e0030050640591554140c4614030301803581e802c020103041019081c60a2925000b941011130001c209080c0601d900c41000300410400078000104440c1c0d00d4840c0c4c0e0b03098202540d4030714000341801102151800342c0c004003c00340704104c0700448681e44154914001c26036940d61880c51410303a0003501e243c1d0003000800b03014070003400d000414412 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 64798204 1250 64796954 64796981
    0x10091a0927100b03030a0f0c060204030f0b06130902030c150705011506020d031e0504141e0706020a080306040c05040f0b070c0506121501020f1005040b16090e0601030906090f0501 79
    0x581b601440004108a02000c868070900c0040e41030101400030340d0b4155070140d0350010050b4040100c6007071000340c0100c121540c520400b1030b418103d03986942800b038800401d501070000c0c41550180002c002c4051558451001581c8040c80070001007203090141c0c6050351201082c80e14001e042940003403e281c520107203042854140f46003070544030096201e40444082c1064002240d490b24507112000e07040c8145c620b0203e2203400303201115a10101303d0f401d0300c001004104c0e6078082e03807010700342e0300c5054800c0060800c0368288001030007410039400c07180a9085c646003142c541034842001002046060f007002209100101d0440300f00720409a80a0161038216865810039401546103002a071008000142c030b51444007003c95540d00801140401c0018101590310702c210150300301000340000c41c4c080e10001c0f2984045024990f81020b044003071101a90b4880034541019406a220340313003d800b05040503500c880b1080411960312403282c41030711030202850111214188182521715a013007013103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 64799454 1250 64798204 64798207
    0x2310051e010605040303080105150d05040309051903080717070506010305160b090607030c02060f040e0f0c07030f0804170f0c01050702190b04060f0e0610091a0927100b0303 76
    0x102198007c4802c50446d41c04840a04d02c03c005407030800614081e80c03120f80112420030702840101a0041611070985070706a80b442042038042101c1411a00715220241c6200c0003001030f407011400244284035450580228145048030943d42c503850000240e0042da0700740c000408082d05031403500104401024550a514180189403001503034a10820900500b8050103a050604640b100c80544445a038076110943e1603654a600070080e1401c100c8034103800050400004007604850026281055010303581d255001031002403d94011201030016990301c3c40040c511248545e07001c008203c03141c02017100903280c0306207015241c01e64030050040002d5400143d011106508001c001500a68000070540c0b80798690307040050040c0300c105107030343c0040e04042400d84010f000040003806070441002c1c1c2c002c840e5440940c0000c8500010140707008100296098001d49400c0d00f4054009076074401e10000c04003941050300b07403090000c1c01ea21007a0009220140503181503c2030080340078094000d075 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 64800704 1250 64799454 64799459
    0x1801060e1f080601020709050117070803030720030c070b0a08060916050703030f02040b090901081603082a060603070e010f1a041e0509060d2310051e01060504 70
    0x40014200c01e08074072003006030540005031103070b1007042400018100703c0b00c01c11155840f1000d2100c41d5415060302c42043c0b0400e00001080c0030004112489036940755114903c2001c83c3c4440d002401c0f82c002503204600c000d004285107500300303000150091000c1c0500503510000088090b02d001e00c01884584144001c0c400c020f6078044c00d04144030754425520f060795a490351072505800401200016510580c40481c2c0450041150340017032294070710441d10311303086a0740c445445a459114010541d00018811340c00c10001e40d244014000c2e489042a50040030811680062100c614800c45180a6406002800b280d41800d1003c4d81c0a0881c5e5440d0702410340c1000104040b00c1c1c100d20404e40e110154010519001150b0030942e03003d03203c06219914004003100401c013407113a01c1d01031a03216249003000b040b40340c80c001c1d508803402d9610484030710314042c81001da0525010350300050701c554000e509450700d141401d840340c9840342581300360345814280c0c154000806040c050f08450240041044203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 64801954 1250 64800704 64800739
    0x30403060b10091e09150503120406021221040b04060513020108060d02120d05070314090f100909020706050901060501141209070909050d02060a020f041802091801060e 74
    0x380094401c2440c1c50801d1064280d0b00f0300f010130081e844503007002d14104004105500c0213034160304865084007219045803801c4e8564245100300c0c0b041c0e9000d6485030400c09032842048000d8014601b004042102240491100825580e0100c4007200d01e031302a40100000c0000d03502c907141d04044e070801f074480342d0384503940081d08805000e4181c038400c030400180c003411592440d20145070282d41c10305840089003919030240050300171300404c5001c200700c104400700024030351080d981d0849000308028000300c8041c060108003101251414108003c000380031407030304118001050200d10410700003c0364a084000c003421590150040e504118070205190903c03a00d440c10f9410311004021034180b980c0300c542d600e5207040c010354401400c0b2030030000c3e44000d00ca03000c01c1200c40c1d4421502515000d5544600c850101d03c1840017150050409010030b0081101d40c2d040704641c1c24480e40014a4504c9800c0000c0d1203030168801c0f510b0008804006029141d070007520a903a035802500d801d05509000c011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 64803204 1250 64801954 64801967
    0x20d020105010807050d060207170a030509010b10031e0203100e06090103020607020603070203121e0709080304090c27150801030206070209090c0a030605150316121401020309030403060b10 83
    0x40910405d01000008140505581222030700ad41c411401c055a50181c104448290480a41180801e103007000254401c0410701803024800c00c024100c1a80801a9209600811490340302c0c10400458840460454040b440114004c040400d0380d40e8840785002c061170f0f8000c1d0010241c0e07000d282242c1c01080140c90f000f0940c0c01c150782c1102c00300d460f80c0d940300e402c91460155482c20b40c89188400c040c01100212040c1d940401d81c28041000a81c0c2d80d01481910030310100c1c4aa1005640100700400081d0358551100c0642101450b0180c00c0100216507811110720380411100000300705441000340c00004141e01c11501e007103040c170703000541c51500018090701a41c4c801078080c1c80b0000010b8441101801607400c40c19009001842c42526401c0401c01000300703d1391555800008410402c00b0302d4001004408945c00b814101010350500f09900040408002d00301e4441111a4041040d10020300185106103d042c004649440c51070070007000b5520000d80003030083d8040c083c03413041c6035030210 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 64804454 1250 64803204 64803209
    0x50411210f1f0902030f0601140909010c020c01052101180b0909072c04050607031d07050f060c03030406020a02060c12060904020f150702040c030216030e180f07020d020105010807 79
    0x10300000c0d0f00c0c14140086802d0103200218080076000c2e1600214101c0342c072010400c0040c600b900c0f5500b107a51480542403c90700d070040140e01603401600000e00546c8588000c0441c5244001c2d20781000da000035080c6800c07130b0b0a8014105004014107002a0a10746118103241c40008070b40811481c1003080d81603445100794002c010707040f940c1c0780c50f42e08100c41c840000080100f82d09205045032034075040c00c5465030710039100030b40024200258841544241450780190552510140c801c0c5880d21013000601a10810108c1c2c00c242c0511650b2036200084c030181d441280a42e070056507070212140001d0810400500d12000000c0500941c09a2106800e400d03a108200762414203040d00c8a0000400c1d02c6c52400c1c005503c5511032031081032244500010340840b61080c1c40601000e044040150240d0245000700c5e20101e6244ea86100402e01c140a40c0100d41009468680a40b1400780880260740044488000700381d0b10310207000001d503040008240800345880200510b504100d0b1840e00c5d8980703403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 64805704 1250 64804454 64804513
    0x60f050c070b0a062d0b18130e011e0e060f0406020a09081207030e0901080d1b0507270501060203030112030302040801020d0606090b0304050a020103050411210f 71
    0x40040c0300c140c00760b4444030103401c9404094011082c0c00302c07507005e0400b140c0c1e46560035000b8500c001402581d44010f540c1c500c0300c104000c01186c21a01c00780910f00038221040c2850a032070b0b51403100d00708020300c02c0341c4a101d4980c2100c1410b1000406450694400c4400f940045e0702c448104080c12070081619500940d0100300581d580c1c0c5041000c031090342003074000f01c4560054501001c1ca08565030010250a80300340c50780c2e01c4400c1558204100c00409204003c07454102d600c022412600c24180309260003c2c80c0d04000b061039003130300c0320b5103014200d03000800300100031403d00300010000b002c1c004413000c01413424401581410f100940302c1c0010f11650f101c441d2000344400405000345c041d20050301c9140e0085443c0c01c40c2e9030240b0080d1500f8840c2d00040b402701d0300007148503c0003400b2648100e4205000708001c0f002caa00440080c00c0080c41941c1c0004400c08201c0b10b581d66800d070503030a150600000303c0d0f0b26a0443c0e0780b82400314200094030a6404440441000c0180a14506005601 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 64806954 1250 64805704 64805723
    0x50307060c17010e1503060103023307080301090509010207020a06081008060f0f130308130f0f03030608010c03060602190303090b0c1e0304030518030708010207030c060f050c07 78
    0x80c1d00e05407102204a040201e21612110003c0b50b08085010300034030400310030410a106041c04000d0648654013800040c0d0024021208090391028214a0010003980e0000741c46070350703d1078581d1105617001038004451040e800401040300361118007656802c41d404400861901c00720394005002d8031084d104030024050700c000041c1501080c5810900103100a2080d14a41d150209004002000445400001c0d482400c0860100f5108420f0000382c582c0c5604c51003900d0310781c1d8084100802000900300d40e60340082c0c040600043c000c1c00c000b90440d2090308c01042950502e622242900c0600103942d042500e4680100304c095400111a600881022400b142002e4942011800f408007024041c00c0200050240300090801500600c848852a0584240c154500383d260f809880213a80c0580081c2003413094140302943d644030300024600003400c944074030f5a12000a0b0070382c0c201d400305501040c10703410b04400340071840c0a42a007a14441804021034078108103603407507030301803404080d060300c85 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 64808204 1250 64806954 64806971
    0xa061409011809140109030306050301050c030708013003020a0317091504061103010f0f090204030c09020c0c0405010612140709170109061104080f0d0807050904060902040b070c08030705030706 85
    0x4d040000058225200e0024400b1001900340503018003d1031040c2406503280c203002072112540c0c14141c0340601c01503900e01003264a40f4481d84600038400c06000d40c46030610314003100c01607100d075002405a01c02c0c1c01800b1003000d5030a0240011995038030911409140f0f804010304980e012910640b148100081104a500c650400a0041503890b0714124a00400000885d0004401901f1021210f03c002440c00040d155410303401680113a01c001031104070001010300a18055030094880d00c00f01800715503101ca03c0d1310000c3e058a00a0380300d20082010f014081030100c0c0540035400403202101e9a80e2054109444001c1c400d550074030400324044885400c41070b000130300703410042d101d0380c000b4030074468072103c60760303201e420b0340548952402842240ba488400303440c0401c0c4014213000707030f403940005907031958401d42d0681e00241038207610695400010032500400c1c4042c0003d010051100c07600c47d41d45140120941001350012156603200703114050000d18000100c070b005a92200303001c00c0042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 64809454 1250 64808204 64808213
    0xa0308070212070f0f08150105061b12030a0e070605090d0f15050703150f0806070c0c09021801110129030a0602040b040527010902070809091303081008032205090a061409011809 78
    0x213030f90584014611f000000d0141404030b81d004643f10503261000d40741f031030340d481100366494440c3e510215003018552010f00c012610440d5407200c1140119441119030441e00c400f04121042210000f0101c2d03569007140d11885240022100030f440400d05000205041c955403a03030794003000700300e2010446280b04140400c041c040c089001480200c100b0341d26480c01c1c40d413441c1d80109502050340000c213611028861010140038807030b9000311034018a5000b00c418503010441401d080442c0d5010700ca0745503117100055040c0b0040004103050000c20b03840b10b00700410000d000ca0046100500c18040c01d0480c0381c0c004403001481e04550201c040140e41e61010310301140240555aa02c0b94000510010480c2c5c640340c411100c03c0a0703210b5a41c0c0038156070b0301c0c40e00b006001003e0003201120762050103910204110a40c3c828226210750b0b52200502c3c2d5a44005504a03800b200c03602c01194480d04100030382c1c10804508010444100c0320480c0325810f01110103140c441d40d8500902c115102c6504200f4030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 64810704 1250 64809454 64809463
    0x2003120301170a080d020d11030408120414070e180f030a0c0507120320120405061b010e0304030b01080705010c1509020603240a0308070212070f0f08150105061b 71
    0x103503001d80b4a6403510b00ba40501c000a400c00c4048001f1281070156440a504210702164402c55200080078200010346140d01c4005034010421154842288040b9006050030040c0380c0c01020140b4400669261420b030b200034909056034910010303800032503000f000d007101106072100d105030303480e2164008680341000361500c01c240d0710603405c0c104042c0c400001c0c15400318000b03841490700141c0084080800c041c440d0355028113044003043c520188810300c01850004001e00b1000d400540300403004c440d40d000c440c01c5a801d08611444c652000038100100020b584031180141418809003028600e000c00280c2555001c1400401500031000382d080c0308080c5d036010161090700905003641364900800c1089682c8200300411445403407500c5180341d42e00d44403c502041c0c030b41c80000e103810110180c0c02d000c444a44640c42d14603900903200081119020f100400d0300819003c01c400a0980c5001103031418075a4410030411800c44800050290351201e4044440310318100c2e00002380850f028001c02e080c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 64811954 1250 64810704 64810723
    0xa110616020904030905130b040510030b010b0901030b040218030607050406020706050a02010e07060f03060803031009022d03061002060709030213060b03040501090201020606030304030b040b040303090807200312030117 96
    0x9100e042030087c8a11540c2c0100300381d260680701006039444840440c681c265840c80024031060308400148408082c24009c3c01d812030044c1800304000d00101e00143c16a0450354000700d00d41c100801840c50362504020483d00b11210b42819848c0504114000391504814010803080c8800081c0070f0180d580300754800c1b04074952013000d98120705d4481c000141040005502e09000070300340f40000c2600c1201100b00ca006181c510182140709140816100103034112031502500001c03185145040741d40244401e000f55020303c02259640e240290401c6107101d13885480c00c0855000d08200300c6403035040321610042d43d80413501c1d0780088440c00300314401390400345c0024803824004414401000015000101028405d1f002e65040740e4074070060603680d025a10020341003103001408500454248001150860301900d00840e04540548800300150712100c0101c6054034400e024620b00e0100d403c10050a241c1103015102240c500c0c0c4251546000600582000c64041c15101c1d09204041082145 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 64813204 1250 64811954 64811959
    0x408150601140d0e1c0905090604060e04050607090e060603150a080a05060901060605031b0d020904050106080f180d1d030a0803010314010c090b0c010609020c0a110616020904030905 80
    0xa42d80340e0403035680003034949111061444d10402c0030f030303500e411400003500710022220386d00d40307034004d2901041241c1e5a4024218980007941c500c00450410a442c2c821441a03002d40002c02c11401d0481000344032001e280c2c0714420a407040014821240c3c0d13408101c0741c001c3e0f00f1000e01800c0c12001800034481c5100c590103030945219903801310f010003101040c000d10030030301800200a1299980742c2a54148030864241407207000030440910628032042c040d10b07545a80303140040c10921084003180031294207130002c0c80450b81940403c801141e6003040e1a40c09440341300500b007903da00300c0d0043d035150604020b00d01030040f2241f26040c4032200705075220348410010215001590346083c61501c0354421300060391070b0000c0e000c203000d00c20b20501401c00c003181c155980c240d00c6494011135140681101c00042036a54813050001500d50b1903001405e2491039000c06001152010314014400d509c504100d00c0c0100c0050000c84d40c02d0078000c2c9200c0403641c040d00c000086035078510303023211607808075003005d0b9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 64814454 1250 64813204 64813207
    0x9132a0201060504050f0105100c03020709110912160605070503070b0703020304050d080601020a080f13080c190b0318030d240501081603020904060906030501021806040815060114 79
    0x408190341504201c0c01c58030156410001c81d110000880300301074007401083e400803080030307031141810302c501003602010340a44160740005886003c40010b550308001c81d40b0000c5008103a20b503407403130302c501400c02c940699001005545480500c10465030114411081401000304459040c85014801c0f10281079010800c0d01003490801c01c0a070003500260380a0700c00c0d01c00e01170340110b050300400c011401030300c05030000c00c4440182c3d80c4840c440e90080481c00700b000d100303100c160a491070522a04ac080e002201c05000303503e1850040c0301c840f40c1e4100880368015411981000782c401c2c0c06007103d0300680c21940c10000711494095052840c0300394000306117410720341154903d4088042500c3c81001c980d196000d0b600ba603a0b05c0044840000643e440c1144030200601c002920380254018a0a0329002d04082449951404c001e02103403a13036842583c10380d40009140c40700c00e103085c1031310f41444400c4410324101030900380740a99800f0505101e40001c1501c402143c041ea0080041c0d650002c1040c0d00c10303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 64815704 1250 64814454 64814531
    0x7060608010207140d050d0b12060f060102010f061809020a030804060e030d110627160306050603010207050a0303050405010b28091107020405040c0b0304031e02030913 74
    0x20700070360061005803450010500c0000416102080d21054400c140d5103c5d824041649a0304008004d03010040d603001e194502e103258440c0081c48990302c9900001800038661920398006429240031055044281d85024010310078031010408204980d4a21000010050315a1011541d100c8189c0c001030001c041c04900010082d9000c0d0910405440c00c0d42900d501114401003555582d01514001095800c000001074000e01d114490070141c02e05605c190100000800b00c0307a007001151403000e01a001c943e501403041c40707181d000312500b00c04e058000f14902042620f4560700d5140c2808000c4c20140c031907012070700b07005094120001c030b60300051011b048107401c4100c98108a051034101160b04094020010f0721903110b2103940350008422081e039242c6541c0742c0c00c000007450003d01c05c0b5400020103401088000c1038201440c03081d8425142c003081102040c0f00e00c80c0d9040300e51980360840d40200f02200580c2c8490410131046580d90901203868680302d40c00326410058550340070400e100e035502e1b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 64816954 1250 64815704 64815719
    0xc0c0f07090b06030f0402040b0d0210050a110d080f0a06050a060e0102150105090c1c0e03070201090f030c06030c112a060c0a0f1b09050402010f030c080a11070606 72
    0xc0030101c03240740c0340821208118000340074442c00300316608107034407000000040c05401e003a00a50380251000f03204075a0901a42c0c0081c01c030090080733014001520108186540642094810f103240800f04010104011040300c0200655030040ca400942010800072604000c00c6800c0752016003c000c0610180c80d40b1030324001c6c2150700c820300c1c0c07600512481441400040141080754141c600c042c1c500001c0359500e078402d00d4240d000d02d0502c0200c050180da010398500c43d901c90b800c60b2401d080080c40e6a00503500004141268941060510204000e401c00000fa0b03417082d074008403141404d010805081e071550a8818508009108440b0702660311400811880300360301c1c603040c000403000e1340d4a070020f1800f4000180101c807440301055111883e840c0205449294110700c0c01d03c54060b60704e0401c0c2640c24402841d00e50b9110804158a603020301c0304540c2c010345400301100d901c0c0750800c20070003290030080800c0b82c090242245030703a46281d429034a03810715007104c00c00ca0700b110302481050b41c1c9040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 64818204 1250 64816954 64816963
    0x509190201200a03081e010b0906120f0a0e120a030c11030c06040510180206030c07020d050703030e09040b04030804020307050424080304270603060e0c010e090714030c0c0f 76
    0x4400207000000040c074404150540a5040c1203c0f00050601f82c3c01d042c800c0d40254400401254401c0c0d051003690301207402040e00c203100b0400c1a4213020641880050740e002d07101c00d10303980940c54000003581e80c000169481070350145400e03880e0100c1c0e4002052404d1301d14803e0585103c032940000034103c0d505240018680340918031541c00c8400d01014100360300300b02e4020b1207401303003080600c407a50380151900304091074020141c012014074081107640081c1c0e405040b8002280c007508038602c100180764000c5070800c0051402e13900740c003d5107070541d1080601580100700800b807004c2d00380070400750b440400c03a410203404050800c00074190902480614102004609003480b00c888601041d0710002209440c1111410440d00c404142c68030494810b0190881d2084103850f510000040071031540d001c0c942003903101401400780b58000a00040c10355a00700c0c80c00d800b07101d503142405503180d4814004c1d94204440c0035080d031281c0b10f10105100510419940441078400d09001821807400800c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 64819454 1250 64818204 64818223
    0xb04030807090605070f06020f0309071d0112060e120d02040e060303070209180a051006051003060810020a050f0403052404050606060307020c030114011701050919020120 75
    0x122516019900d581e01200c004226000e9400064010702440c00042d007109000c1c020240700711005030a145942d0031400445c3c004468442c0c1991049008108642600700d03038101d100b40c841e60b4900b45604020502e01480c8440c1c40c010106071795160406100b000a02c4106800705c1b4140c4030544c1e8540c1120300001940050140c40442c103400d1003c03480b2803800104455882d603000c0c2c43ea014580d41d00e103240f140000601e04040c003c2c003038954200c00090040c00508042007411030006071250808003803055502c8104032103418546021018018414002085a409651198056500d003002e81c021107482c000d00301c10060011000c1b8001c000c0001c00703e440411403500d8413003480305801581c020f01036100c050302c0c0078240b41c1001d0081100360404a00035a440940d50044690511901c40800c0c21103004042012241c0401001440b00710159a00079080212500080c010341c20000c0b903c3e0b4450002258003024101d0034001c1808590158246400800a442d03041001c4a245107003651030b0032182 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 64820704 1250 64819454 64819457
    0xa06061d0103050c040203040f0b0f010f09050603070b0a0e040911010215151011030a030c030b0d02030c06030a0e03040b040305010c03060e0601080703020427060909030f1d0a030b0403 81
    0x1805910540c4990340300c903034120b07900680101040394800d0103100c02503001070030540d040c0080c0d440700f001017041d524810380030754015000c000c0f40f50324021028003002d40e035410030400c25041406110703450360001101ca0550780591043c0d81c0d44c503030f50182900d5100020401c103420030b00381480c0300d0901444000008800c8800c2e020b90b200440321240b0b002c2c00c604103c80c00b400c04003041e100002c09040007580c0c200c0030704160500d038510701c0c0c690603410700d1500581c0407040047e486000c3c41100c140d2501590920303007401d40364070b60304440d142e000a4039081e810505030302480c000700009180894542210b100b40100d101540e80c0ca0380c803440c18170055030040c001621250708044880300841e1092080b0703812503510524028494451800454110502600120416809010104001001c00002d50001a502c50040c0c8080e0b81c40480d2801d95071258801172410f071421703080700082900500c079404c4013109490109218184000940e02d5140b00c02040c50300310132801408003c1007a40700e403050046010307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 64821954 1250 64820704 64820729
    0x108071b0312060f0b0d020306010207050414071403011a09030a0204020403030801060206010b09060f0703120c030608150906130c08011104061d1c0501090f03050712021b0f030f0a0606 81
    0x40b10900013400f0707018840d480c1d00074010003800444640c03a03030245401c1441403041c0e48860340d07681300103810f0318022030b5240c2d11190b52a0038414696001000e07189110fa032400040d0440d0314094000164061a00c00440c0d0502d00140c0c088040c0d4050200c0301145600800854a0303030f4503400c0007000540240910005441400c00200d044045c0000303498210b030008140300d00d40703000141612003a8000b41412018410000302030040303030007a4052801c80c07480940d000600d80f0311b0400103a190000301c0c0c410462813a00102801205400820182d42c441081404400452458030300507a41141070380c040812540307040400b506840214006000b100c03043d94400f60034180001c0d030786014181c844000e50384071600460740090040d458140c101c5031402200000b0703200200b601c0d103880601030048100c00180380000c00800300b00d411005001c140d542c0c1c0c40101b8a03901400140141c8010400d00f80d442070309407440c00c86103a5410002c03403a1456142040e03400310211450490050305040c05840300c401c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 64823204 1250 64821954 64821959
    0x603080a11070e16050d020720040b04020c030405010c0201020f01020d020a030609020a0f080a062402010c0206010f0e060a180c02012007140c0604030b090d08150108071b031206 78
    0xd4803c109400f602c450180e08103682e13408181a24241c0c4682001c1001030303000e1040700c1c0030030703c00c1103541d47c02042c9242d40030705002542c04020846003104601c2d0310840c8140b24800783c00200200b42c80903140e003030030000c050350311a000613854866030780e521206547c0002001200020250003804040c8085c0e2002c0c03201c1d03502e640c960801d078010b42e0340030800558001c5205804905c01c80f822600114031240001e007507a00c5140100e0200000d80002504c0720002d6441c6030740301d5091107940c98401c03540c03019155a505043c1020051000d5106540c040c4003610081200d550790400814001e00074004c418408501061000000d801000d861002652800c554001100c4e40041080380140c2c054912a01c2d00c1d00580d100c07a4000e020200b03400561103400d4002c0351341d03100c10005001550140408024030316180345034620b001c40b6a00001c0400c04c0b508140b00d00e01207140c9140c4c14200302402c2420792030f62044011503004440c09401810b01c48544508000d250304003c08868480c60310000340200754 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 64824454 1250 64823204 64823219
    0x70c05010207050f130510120b010302180f04062309150106081501032c15130201050403020105070203160b09041118130207020904350f07060603080a1107 68
    0x2c104c00a898000d007588101050110382d0b6031102d5030160703410b1448403101c6d40b0ba02021414007002d180c00c0352803040600050080d89005014040c28200030002d4501c1d6140540d00d428800401401c000c1940d51038040400b009014002500040c000414561185240034048540e903a05541414180540100e001040d824402d007801f42c480e0600d284101d020507003076001100181030210304110446e001c510080b0207050304450004184225034014030001400d1410001108006029001c00d001a0b040c0c00300140d8000094500302e80d0242050f81d120324580c00482c1c205002152140500306a000d40440d9072041e100c00f400c0c2c1c41100b99020014501101c00030b40c103e204154034800c04422038940c800350b601d4100c0302da61102c1d565410150400c41303d03034082000d4180c103903011500c1f08070000c2241300f40c9020249440d861000d030104000e240015491020b103601c500b00c9000700074800040d15405001040d00a0801140d102c0001d90761020355a400600d20305540022050302e00070180f0004411 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 64825704 1250 64824454 64824469
    0xa0903031406010e011b02030319080903090f04020901030b030d0f020f07050d121101020a022406010806041d0304030f020301050106090807090203181605010e030307110d0501060308070c0501020705 87
    0x2c0e001070316884041300c8040015540741200301d400c020090480009003005803010b001602c0b0070300514440055441d21141c0180c41001c00801e0000c0301c0d0b000b4000e14841e82e4950107030030b5001000703070f4005039203c8034000101c000d00751900c0c0d0315425200c0c682100c039090340e0044945500d01c1c1180c1c04c0d2440401c01203034070341d01e03220301e88a040d61201e0030600c490040b0380c604200c104031301700e03a0412003d01c00312903200c41d0998000564190158010103900d0b0340c4c40b0704500d022a4950078022600006140090000e4a5120081d1113540955664012003501c5034181c0d420041c070708440340440b80c541d03960b0300d03010100400c2940100d01039400c0100009065020354401d40035a5201d801901d451810100c4190080d00002c01c124852004030a00381e00c03c940071b0244d00e0100e40100b0b0410038850034000050040f08141c100b0740c1c0603038810007500c00814541c1d41c0d60180c1600c2101e4901d81c254003814410b01600340b50700301500a260028a00c401c01c01150404000c0701d40a80a507a811940e40d010403410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 64826954 1250 64825704 64825711
    0x50415080303010e1509090c010906080106020d0309050705030304030c03140c0306070302070303060f12051b06090d020a090518060105010c0b0402061e0408030c06180a15060b030a09030314 83
    0x794418001404408400c42d005980040c80041c0b0068012039080051102c907000d45800b006504850301481142d40c1c024081c2c0c0141c00d2038103207828294900a0000d503201703c818410010540c0d0341e0142420444140000c00050400404032500c1c0c51300c3e03007048200310389140b0085a1710026201255152803001c1160008810020090f00d07403036403100000c0d80a588112403c508150381e82001090721000d4500460140249501008603003815180072031a142e40800f0601c0c440305848800b842e103a8441d82200c0e1444801c0e00c50030b400b91018804105040c500e03070404000c2c21308000c00c000110400a09108500d64407004981d040d0766280d0041d100504a801c01900b040c11a800003005420490024410b81d22059280401035103401e0306550305820581103042c032900001442c0d60005000c01642c1d03000501c010310f1800382d80c0b90425040d41e41d441d110f0700501c44c0f0b04030101c81840200c035a000d80c0c000d104640c3d00035a031b89403680841004040d1050100e000c40d2620105600c5820f40540d01480b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 64828204 1250 64826954 64826969
    0xe010c08061302090a030605040209132d080a0c1203060b030f04020d02090c09030705122112070203190201020a080c09040605030a12020f060408040915080f07050415 73
    0x46900c5207000e12106141100c1c400d02155020080a42d1540300c0b8401000218081d081c0002c00d42000d104010003110050401c17101d1003c401000408a544c80303144403215001100003404401c011025100c440c8090b0340054001040400c140c420140c001b1508540580724030050b82c1442c0061400750308942c035a0056480d000c0091000400207602c121906400900041c031010141c2c0c81540040c012002c11603a2144030500800e214001d81130400640010389411102c1c219910714038840c507680ca4059603141c00351030302c080d80c1c0303500500f001c2c0c0200c40700e120095407400698500008040e60b25030151071320340b01e141441e010100410744180300f41c89102c50159107104890312212414503403900142c071010350240d07503424005030a9800700031161250384140210603249002c00740180c14a058014008919040042001700240d000c100710b509032000302d9000150f243d1108080000b80d4100d07004118244640711842040550014a1408484c811201031100400365042e40b20560700911505a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 64829454 1250 64828204 64828217
    0x308070206070f05090f0916030b060c030706020a0e09070503010518071e03020c0a140c01092105120706140a0b010903200418050c0103112505010501180e010c 70
    0x1044501c81d4004100225008000190100728440003407e940c030155200380c41c0030780c0b50364041c1c20743d03405010305009205e04032607181c14205040b420588a00c00c0301c034020000341d4006525000c20303004244400c81c000000d8084c0405180c50075001d0706692082c02858805c10b1110307400c50794108078030796061140c2507550301d460744008040c00c0e03440010520240c000034140c003030140010044080040040c024020050b20010701b05c05007a090429039180441410044000030500011038240d40007072181c0a190030041042d1b00341d05019041c80010002144500030014901c410b000d000c1c1c0081000038644880c60020343c0724600030000715803a0340c6445010030340c1880c1c02c1010070000202100040060500380c2002c001361170010b000ca138004200c0140200c4e030f000030001408003c10012045002c282020022040031002600450007170b808000c1510706601043c20042814840c0c0c0000d0176444002800156119034545120305081e28241410f01e20b400c0383c4d50300c0307060b05004d680c10221542d181c80c0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 64830704 1250 64829454 64829477
    0xf040632040303060b0d0603170c0606060c010608010203070807081501080a02070c1a071202060103030801050607050a0209180c06090a0608060d0f060902010f0507200f0a090603030807020607 84
    0x100030404000c2003035003819542d810005080d070300c20703005000c0b80446200011304c0c1400c600e082c0ca200041108004604d031001d0015040c16400080c0c0c4d15003100045405a48840c41112820b000d0a50350700459010750000c0b051141c0030b504800d50302e025070040d46503001c407540e4440d526002800582640ca000034944404100b00308000d50080c40d9080c014080b00019039100e614400c41c1e131541c0051001407040004044080c0981d08502d80c5551145101400c015413640e1001068020103002c2c1c00c0c81188002203100410070304000402510f54040d00c590101d00e01052503954004c21550003000700e024091040c000d038501141159039507140280301c1060300b81004012107006400503d06a00310790414038040119001042400141384210004600c240176440010541a0b80100e01780500005010000008094800d03a2045401146002510340380d00c0000441c2c05c4004291150004202840400c1082554000744c099901030b449540980c0c50708203080f655058121001c2c000901c156000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 64831954 1250 64830704 64830791
    0x1513030b1f050f01050d05040c0306140c070206090a09050a0b0f0109051807090807120c1401050a0309060b1e15030402180402030a060e030a1404050105040326030f0406 74
    0x1842c1d584103141c03140c2401e1b550651300046441c250b80542d5854a41d0340100208202802428105c0076840ca0721a02402d2041d103002c80c50240780b070002c2c8200d40214a0b92244e03200c1c1c4500000420703803410103008504007804408010300c1107512203802041c180d0909203055010304020021503002a04a5034a206400c00717460464401402d140d0800030b9481d000620350000300045c6001d001000d070307083c002204074542a07504180a0748501c0001000038511505607070000280c481c154030a060102d81c2c0411480c1900c000c048580307125078070000910300c1017034444207140c400304080c1b41600d40c80c4071500d0040c05c0030b1190101f01c80096000000c0036001c00c113034460b40030750f0350810310203070494421070102c0c0e40307060903103100300c115101d07541c00414000140c41c1e000001c0310303124108640d0036182c6401c0800007402e910450201810b4014070100444c1825580c190524244601c841229128180b03100381107110340041c0da050726864145045903c2c5981c0c003606140725002804c2c1e420100180d002c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 64833204 1250 64831954 64831969
    0xa0204090203010902041b03060e0f070f020106080303070207180b090112050106090903050306090f0403020706031a0402070b010e011706070309050c030106090c11030322021513030b1f05 82
    0x3000c036019521024070400584450003400106080544441070440d03c070100102100d025900c03400d10419401d061004088408800c3c581144041c1f81c40d503101d005150b000d9015254943c417030701440c4000010040400c0e40400c259080d14100030311031000c00301041001c2c0954042209607a40005013a0041042078500c602c941909842400041001640c03804100c0031141039070b6068000c56800000c0020614107015880d5005110015040c050305003603c000b0f5445e0440c1c040c200505680381c9041c004034400a120000901000700199074410704ca14104400401c207114541401112000101c3d8410843e4641c4442c00340c40c2d80104000d03614600120090302071603800b41c4031405180600c540c039440130301505001d003002c860041800c4460041c014040c03c881710007801150028014003018a8442c0c140801a01c0040703400300b900700c1140001203054002d003c03650301c2ca940020300c502480002c00140c900b10390044240e021039a440ba180440b80101225481180b0401703a0002d008910b002907 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 64834454 1250 64833204 64833221
    0x513170601122d020a050405070e0618060c030a090506041a070f0b090c0306070509011211132714060d06020d0606020a060b01050a090312030207080a080403031104080a0204 76
    0x15107050b401c0b092403143c48491a41e4400003040d90340241c0b50032041d8100020703204010318056070108410321b40030100401c80590010651721490300001e541545181680f41100c24100090005544201944034959a603208406c89404100c0000c800a503030b00e408826541103136551841d18050520509042045600090040366041106140d1320f01280f40a4100380c420780035000204003c4074000c00305403400000400c1c02c010081c08002c04610380e40d003c00d60000c000080380340420403002c5d40c40030501c54010b02030303194040c40410000040000c0042103587c507100d5070b031081200d00070750024440280c40c4885170103542040c10801040c0c01d810322011856207203004200050401080d441c0d80300c20345010380d11040c010f0740001850340c1440110303c10300d42510000d00f05103240105181001c7d103080c3c41444040c0080e04c1300820001114002e4048880160713200303c2041d580e10034480042c08005041d1401e0f8006481c0080022001409108030350980d100d00340240396950050342048090044131 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 64835704 1250 64834454 64834463
    0x10f0507051e010209010201060504110d36031710170a020604060f0e190302220c0c030e0102010504030806040b03011806090b0a060501080609040501021603051317060112 75
    0x11042c4034042c090741c003075054400c9002c0700050b0341d03915850002801c0d035080c2c4d0007040c07207140740c041480541080ea100721100000100c601250852010041c2d1620304007000180ca0365241340d9411000c6c404044400440140c4a91100d9404845100880000f1982143c2300c210009030300f5418800721f10000c8000202d040c0240888034090500d42c0450307040d40081d40610045a4031807448403040e9002841d01068900c203603034900e52901092440094692184004ad00481001012540420030b111440c801c075111502c0a004441c01c4040081ca54403030000c00340c000035030058100740b40350310600a050150741c05035030f145499100c04003084001d081e004005645913503180e02d401300c2c91083c503116070b0314a40250400901d070700660402081182c401002c54042c0c520306502407085a1b0048800360300154207071041c4a6030b5990340380c807a00a1064841d1080d4610b000358001c401c040e4014000c00d0f0902c0341c608904041903680c1741c864000c1c49026171009280c0c010100500003030b5206e1040c0314a10703004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 64836954 1250 64835704 64835713
    0x30f03030b030f0d050408070501050c03040306090f08041d0f061008070c051c02060903070b0703180501050a0501210c0b09011701090207050706051603080402040f020d020d050f010302010f050705 86
    0x1684401c4d28150340183c814003c22004941003101e00d40034854100142020700b45a481c001140e00b80036103900c00c0c0c2c00000e200913544c05928051214a212002282d503000e0b5600740d69544414044195000d00d0290b400c50b0020034001682901042b204c1d603000b4034001e00301c0800050300610684290030001c2401013000040c0b0095004202e080000344541c407150300018400c0c50f100c480080c10a4001446440694820082500010808600c440d40040d540c54001015201d02c0d034541c40c001001403019242d90b003040e040c09000d90700380d4015412a202600d6039419480b03000d080c044080b0b00b06c0d00c042d2140c01d103418100000074007a40109076505052401c03400d00044028031316505403080c1c00040300300d0b0b4049402c1cbc0421008000c2c00c005000503040403800c0c0403040c14070158110010350000c0422810401150031501c1e15042000010f41d5168199261030301a1800002900802121901c0c035042a02007000e803c21030410724140c80c0c041c1d40c0d080b02501f0343e140584040d80403440480d8184034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 64838204 1250 64836954 64836973
    0x15091e0120010f1109041512080d06030f03021b09010b0d021606090506041a190c031407050a030b06040305030a08040305040305010501030b01031b060f0e04060503030310030c0f030f03030b03 84
    0x400c1d100313182d4007500311013410f610303940d0003002d200c1100d07050b560f81d000d50a4800c03800d02030701c8a100000c0c1c410a0707210349640e82d0b072050018014041c0c0510b5100900401c00da644440401d90089030502580f40100d015582c210038200800c04042028130130107800400801c030741c824140c0590000e10004050074809400c40800c0d654081c11517020500554254000506010810032140c5900700c0100c8140d0900c1c0040c24080c41003c580f80f02200300e50811a96106d0521000d8004e800c8041d0f01110b00502c60103510b0f00c108050003950103207004400107490440c0c400254039007101600c00381c0c5c1d04500154100644000291036146001c5c02c140c0c280f003c01c6c0710000000e1024042e880c080c6200d803262301000d5246140805041c860034028026a801068007444850b9003c4084680305d0701c50314040c2280851440400c0051415401c415050300000040041b84a0701e00fa0300d0741103a00c241d42001c0c140d0340c1c405c1c132100c10552600000b4448044100380c0703000300e4420341103800c113100b008007507400201 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 64839454 1250 64838204 64838231
    0xe01030e190605180109031b0f17091009030804050105070812072d2102120a06050f0a182309010c080702010b0306061003060515091e012001 62
    0x16400c074003118016140c0d42040540ca00040c0c0c582001c800c001c00034448041c1654000d4041d40201d41c0015282c000c09480206010311071142000b4207410031400c0184078140c0182010b030703a10022841d80216600c202c034858040c030601180303080b030f80c00448042c1094100001155240d01c240419580c8040601c5401595a00340d00030740d000d08810f0b10f521a603091000350b4854107400400414030060522203540002c19040b8050f41890454841501202d50386441c00800031300415902c0b60401c9884000c10111489640c80f4030309132002203e01941042c540000c2005404860180c002d42c100c1d1440c0000d0b4010894001d1210141c2000c080e040559941117003619400c4104d41e01180da079100d403040c074117640c0c1041450f5003102080c4028040d050100c0b01080e039441d0041d1220b800740036000e10b148810742c842d5001d2005440000c01e110311084e4401002d50070358121043c490b1007448080c4448110070589500351000c8041a100c000000d5007200c03c00f41c0c45200d0b1f24407403405548510f401c43c07640 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 64840704 1250 64839454 64839493
    0x30301150e1002010507080a0204241b031106010905010b0a050702030c06030a0b01030b040c020a030e03070815010303020106060e0f0d02010c0803010902070501060b0918040c0807030f05010506030c010e01030e 92
    0x102d02c5500001d09450003a0f4002c080303030006014160807610411042c0101c1001500e0500c0308860030551080d2000072000031100713141c0080782c00181c0d505c1900b0103001c05a02c5100101030300c2960003260710320b980b03c14640c011140c0a218100c11680200309900c5164010000752551500040580d42100b0710600401d495a10841e0b0303489005a603080060083e607094400c00c0e1080e042034038100019408139402030341e00c4a000c0300183c140a09814102d207035580800000020300104010b44504240010007659050004c0c0011005542808004524180300e10000302210784002d204540001e02e0760305101c245150358000340d0401c000840c0032004101020011070081143e140d0041e9035141c0d87c10035508540041d08000988242045401050768a4200080581804130421061030721145000c0e480c0b000c03164055103441c001d02c0d00010500c2064102e101c0294060b900a0142e55607140405d525083c2103840c0078003003908802c007404154440da01080c0c054480c841103901569900e50f8445c80c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 64841954 1250 64840704 64840729
    0x120703030c1106130801050a09030e191203020105091009030206011202240315030c030a060203190920010e0306010b03090f0a0503040302031c0e09040804030609050a030e01090602030301150e 84
    0x184030404d030040004071801d1040b958001e003c00301c104803c000590f0010b00c4420900b40c81446107868036000c0342c500701c0804881e030040915a880c1c482d0759a040c030380039002e041c08030f0309500180a0540300000e0b282d0107016070510b44c4c1e8158082d0420307070708000651041e00c68048042e070300700c43e50b244100c007401c032034244403580c190b0908100da07101d207002d070f44d1b5041c9250020002800394200c00c04401c1561000545005050b61003680903890780d603021144801d105003241d4188280382481840e905100c5820f0071014090031a4540340010341e04680103441d1340c2034560301c41d81c2580c003d1004020300d00c1c0d03141c05150041d01d103c06461190614403082842c04110b01800e031030a4100140400862400308045889520a1800e00400c2403403003002601039102a45014096002d44000a00304075083d422a0f02a40e40890104117481039030529a0303641d00c20200c100d011030104c900c2c500996010742c2d400002c4460590003546941e0900d10780045059464074100180146200c45003451f46e51000d66100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 64843204 1250 64841954 64841977
    0x1104020705210715020309120406090e010b1602040b0123091206090327090c0c010b030705030a0305090301060b0a050c010c0903120f021608030403020a05120703030c1106 75
    0x10611a4052010741260002002d07204100002c900040300c0c0640caa0301140d100d580107172030355200d00003241031482e8801c1c02040e458002074081403054000c00c190054818110b02c00c05241c1c0c9a00e4011179a21815a941a00000c90f451400040c9081d400c61150a40189010b4803118000e80000c0351065444890f090b0030715000c55000d00500b40031349008074001c615001000e03e81001049240c8a10480310841c1003611a445601e000e583d2064030114955405040da465502e03100403007940d41c1c0c0181c03002034415400d001703106070317149000a608015100c0c004c0191030742c07040d65601511a54420b4019a41554883d60005946400da4000c0d2484042d203480b1982e440c100c4000103400c6405208000b8140441e00a042c00840c1036044002295451800d02d40b440c5d0307100801c2030785408010600e00440c259400800710b1031810100c040c108880c42034409a00d469154010041000d1101d40304807019804004200046841080200903840c0110442c110321a40c1402256003540146900320 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 64844454 1250 64843204 64843213
    0x16060f24050f090103020a0b0f070503040b0409150501020309011101060506030a020c0d0206100509070315080706120506090f071106040501052e06030e0106090f0903020d05040311010c1104020705 86
    0x3140c10100c00c000000001103c20003034035815980011310030b24043c021180320280c04511035001c5090801220312551f004001c0707944840e607030903400080c3d0384280507909203d4107054440c02d8480d03030722181d00e0a07030714140c019600b804400001155500c2007050580b01c0d41d0740310f0000150b59100c0c20001c40c0950b00f50000542d44940a201141c079190018120070b00b158040010001c00032203000c000300680364100c0d40d039140740d00d441008030083e100c213211a10a10760080f10005000034002030b0001114081d488440b0141d005061000407104122a4150010314010015180c01168001c40341c2c00805c071b040c88000c0040e0715a41600e4600c04175000c0311940e56503800c0c048200c0e200c0192100288441d010400c207001c000c1c04c071103609201449440300389a1200d03105a060842900040040d2407003400c00c03c4055000714101015140010040c0c01500911a5078403c4d20700c24000c030350660750001003c7c08113408244c011107000074010400c1c0ca5441e0742c0782c9a0540e070381c0c1d00e000401400b40a0300081c07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 64845704 1250 64844454 64844459
    0x60a0c150506090912030601030506011205100312090501020a1e050303040b090714010e0904110d030c0b0f060a140d06060b03041202030a1b0804030503040e010e060616060f24 77
    0x2056101a0031070109074020b265000110946900701c80c2e22002c2864040b1301e03511a000141e5042d203410040551150400c801c020720901e200f500802202d0144703004d20964450300c101681e400d06107000c2c407401a004030030441c0200349010014a036000300300c0c0618548074821f445203030440e0426502280c05407151410b0140c080710400c8001e000d000e00625811241c082c03840042c0090b8808601c03a40260503034030001d4180034039810800901ea0b0041c058110410086c60b000b0500c80039040d080b910401c0c82c0f00801e142d500340421a9100701d0003d04003a03241401c00024401c08558080c0311540030301041454400101d640c05144003c280a582840d20303414585003c58480c590602d0100c21548203201c40107030280d110220290030701e01024450304010050400d24010f100d039400182ca180700000f0005901e85a06c1c1e400c40c101e0b40c40d0500144c080d00c5040402005100e1350f8014181c403a0941407010105800d9842691134032141440000ca0a603007038210303c5031400344101082c0201802c03408 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 64846954 1250 64845704 64845709
    0x807060216110a05060403030c210c0209010e090703080d0213060302042d0b0702010c120215070c03020a0b091e030405040b060309030403030c020310021204022d060a0c150506 77
    0x480d00d0b020000c5803941107441c00c150104210380954031004e07042020076464542400b0a44c0318881c410401c0c03500705c2868002d02c0038054940059036500301d009a610000000d83c62140c2c01070180030300c49107070141901525544030310100741c2204410004050b03007000304004061007840c2003402054552005078949142001d800b281501070610140c00340c540d141c0410300c024181d45410103039150196419200e20203800101c44054402800034a400301c502682040231b0b400241f0a5100314500b01c3c11078803a6184101194030161401c0002d026a01181c103000008030041d18081e4410400c1c01283d004849401404008103414a000d208a42001809001d00d04080c020000360660a0710140c0c50741c01c010a0071a900d10032880090204038240c0c0102045507400c2c0700e040070511a02009540f201c1d080540c031290024192401c038070440100205d43c2000c801d00e050034200c04040e682c81086241008103005555108613601c80030046240309820001d5581c0c1c0070a070b119440f10100183c2e03031604806 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 64848204 1250 64846954 64846973
    0x4020a090b010804140f0106030f170703020a121e0305040606140604090b060702090a0e01230a0c020c0a06030e061f092a03050405120309190807060216 67
    0x100150505507071a94698004128540080d030180e0b4014074810740350799040c100700003c2d150310159400d09000100340403034860b40c080028016800080d259540441c04481803090400003400740c0c0010030038101089090503ea00149881d0905c2c8d2000b40074504284800410380042d500407aa0fa202808180080b43c45008080c0000040e8001c07510b00020001c0d00c00d004c1c0d03202e690340007030b124814a03099880e102d00f0b07204001d40c007501103c041c0c14980c00300805044003881c01580f40d880e2440102d2080801e500d0103400201140a8180a0715424010307400f030040040344000b54400c2007441922030325074201d000000c0c400355600180d54034500340002d0500c800900301c040040252070442c0a0100d40b04004d0b41121208100002c00d00c2d03996445040e003003803510300201840010008040600d07015000948200d1146041e6005050110202940f501080e1092480f07030b4414220107043c0008420340b1b508540c00b45080900740149580c2c1c01040e81e200a081035021310030307032104800700101c419 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 64849454 1250 64848204 64848209
    0x105060108010e0901201206030c06071403040b07082206051c061502010608120405060301060807020106032103050a2702040b0a140a0611281208100b040b120403200604020a 76
    0x2d00ad0a80480701500103401401404005040f03400350040e050807107002041124010140300714681d45540c8107080031301c0d00360403030110640e44044041c40300100303854507500001900c0c80c03912540c0c1006640049501c00249080311640559902e05c00800c501031014042401c1e0a8a40d0010031030314100010682403900c1e4800d080c514007000d220601855aa410641c2d055425a00e0041c0c00341c0e0302d080c0200c2c05071046910292016502d45905180c03602e00c91100d5092545503102402140c41d4840113404130746180d034003034800c0b2004000f0f5800d400c04042048032400d00040c40864500d40301000117800201035800848404000d04036101581005464100140490f042c039000f5103c40c00c1c0002c3e20390071155031010510710348603048203c01d00e560f15104051030304100a1040c5c0303603c0090182a46030242c5107030719014240740d400600d20002c0000c540070386144030714543c1051950302c2c411011510141007101031104507080b40c0141422405003814001111000f4003c604150040c4503c1040382e8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 64850704 1250 64849454 64849459
    0xb030c0d0b061c0617010513141c05040f0b031b0d060b040e0103120c0f030806061207020708060a0228030933020415200709060503010e0105060108010e0901201206 72
    0x3408c00c41b2003154010351609054000a0701d01c00408214600ca05047d1152812407000d81104041b00586500c50040e0003070b213000c01400c00b45181ca6001101d0107010072540e00c0151021408044480c0d80a00003414000c0e5030903074041889a141c4440440c40e41140d00030300c0f15030f2440b030010802c0c08030091142e10500341c141801c2e1484000c40d103034103907490041180602400045004a0702645819003142d00242c49607410b034020303080c0f1201c001d40710052403103485200e00c103000208100610764400c541c0e0403aa00d00b4001c03500e0380a9002c0090000103042e440052640c0d541a880201d031580850480c20380310904055034403c2000101820481c0c0c0580d900c030751601c1800280126030461031740700c2510f03502c0e0400740c40100c0421248901503042c141c080e03c1a028200c40010b06602d240c02074401e464085000b8401110010072090032600110f60150004143e01d0041290345440d81d281a0001c00e907038004034404664400701d40022708141c030350b2018a000003400c800c0c03000d848a056900710404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 64851954 1250 64850704 64850711
    0x180c09050c03010e070c061a0907020606031f0f1107151b050d1e0e06130305190201090f1211070b090103020906040801051608010b030c0d0b061c061701 67
    0x260a9041d428001402809880c101c003a01046015000c0c803510f40d4815070200041c000d032480641d10f00f2086070b90603004da00500d001c001007010f441c00840d0051044001800406514074212600007040f4820006840c61903524102c3c0d8107800040d0040c20080319805200a42d00c1c48a46480e01e2940031100f28200200d18040c1000d81c082c980e1411910b80350070b2460032603110b41201101d04002c211081c0f504038101d007450484a001e003860340112486c01180415a61180d540404501c0c402e41900320040010f4400c00199000741001081d02c6c1e8001624070001400042a9492400d86c17a403151065451b80961515a0440c40d84072010780784050018001d00400e80c50908100aa800707810350683c14503402007250181500e5105c00d4a0052070264000c0c0001d041103034081c2c605007045da900c0000943c500001090080c003a404aa02804100c0803071407400018500c088000c2040203040781e4000800c100f84280035180701082c0c1c1660070341110004946240a401000a000e030720f042a0390f0b81d04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 64853204 1250 64851954 64851961
    0x91f210c02070605300a0c05070c050108091c080f060d05070306020a03090611090315130312020c030a08060109080a03020604141507020a02180609060411040801180c0905 75
    0x40c0442c02d88210351603410400d031100300030314011462080d2070b040145000110208040e0601129001c107001c3e880c004000c11185040e40c00444041c440c1107000380034511500c1040041c1c1d44640a503583c86815802903400418001200e214103060343d0904800003444e50040c442144032120340543c20080032248000551444c0d90b0303003501c64000348006410140d010411400580c001d4006440c81b07640407008207c54a444002d241c0700d9004108424028880e4540c1c8050095002284e2409081e00d099208816001560126404071000d0049011a5003c1c8030703461180c20104041d01901d462038a4008240c90203500061070a10590b000d8001d0b54003020b40040440e0300031448070f4006401c5100a12080c10040c062803410088500303651b80c01c0781d481e0030800c5460b070114400080c14800c40742003204000c0f1030307080408480d00350341882d40300d4030000201e4000c1c9400d47c08512003a0340302d005c1c607052940e925502800c60796086404130200e010380841000f00070301d621807503024181100c2d04118504 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 64854454 1250 64853204 64853207
    0x10b0a08100b04021306020105151507080a021911131104120620130509010501090e13060501080c01020f01060b070f150c03020c0d1d06091f210c 64
    0x280c407400700340780c558646400304142c950760100d80d81c2c0e00322100e540e140c480c0c1c1e89400038001e1a0444001c040d904d00ca80d00031625190059480300010300c1c1e010454103040c10703900c8250700b55101d800b2800c00d52184030300d03a16181b40d101719821a00c1d80034205041e44500303100e003841501148001d1038a2640e01e800720b80d1144038802c0d030079641a01c0a0006400000300c0328a80100244034080d1882220018503c22000d1000013100814040c01d5120540c01c1c0303590741e8014065802d50a014840c04150b92200c184003112454402075071040f8001d01c0c0f180158070700e440b000c04448081e04000e0740c0d9084100b40000c956010041e0f400000c01050082040c1450030014096501a80c4c4005141001082c0d009003441000d2201c81c42c080b017014400c000c00b0384002c00c041c0081d40003814888040c010341c064469120301854603801d118015100001d000369020b400c020603035012414640d440800d2101e0742c8461484240005e00d0460151111200b02d00c4100303100ea100340078160130805440c20442c10811a5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 64855704 1250 64854454 64854463
    0x60103051e1609080a0809010f0201090b010b250b0928030e0303040801020c010219020c0a0b09040e030f120f01032f040c02010f0612020609060f0c060702030705010b0a08 75
    0x218441c00c89022280c0c0140300f200e00c8841c59209110611584d4203020501010200034a030511090f02c50704216814078400368207032126800050020a507800040140350340b140028456425490100d05006141d1011151300e03222500080d24142401410010013070010840030345000010100c00c1d10b40305003500319588000d0b4030003009040040c00307840824507031020420340e0041c02d4407500a40d11042074810380f0f8001c0d003203907440d08204c15180d104c2c454541c0c00860105142c40020304002a0036080007045000341c1c2c8006407140d00a0368030442c020a005080c4081d1000107042400240c0e0780c0440b4040c0c440700306c000f400041c40c00c0400d900410001b0b8030840c07036075244580c51649804440c0c44012091040078985400c40d0003034140b50000c05141c1c0d0640c81041048581c0b10304102154403820117519800c60114001d401032002c208514142c907040c40504411a00a4251480c00414200b59800d051094840b000903130710102d0a0020048217014281d1030707001c180d52800d1503e00e4100d203070380d44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 64856954 1250 64855704 64855711
    0x3021206041113080a0203060601050304050c0d02190b12010824060414010303050702030d09080a061a0d0b040507050402120a020a030e06070239060a0c060501030803060103051e 78
    0x1c0d07a41d140300030003206401d402d0324090085000741d80c0705036584140b9282c5030301003064100e1003406040000b0340c3c99801681904e02454100300207007107010600042c0a480018190305036882490403450507596499503558601804e220100c064172188404007065a40f44103070415000c5400c916801101c840c01d0300f0003884074000c07a017060b01c200d4880f80081401003061100f6616140c020500210505801c00300801d01a403095045a82d07003105200100c48420345030107010361507040340040f000403545a030442d00d400c042c0e00c06039021400c0c00c07400103200701c0c0110904442d440550800c000038004240000c00080c44140c0f015454514580f00e082080c0b50010100d041c03c0d54003285174014030744a07520500d010100300b03040710f403142442400a0f40d00c01c05800d102c3c0801001c00704c8242ca605000d1542c02e240f500b21013249400034407040400855803c2220102c0c03c1041c1c0401400100d4424001d40e07001314040c40c021075407405c048000500b81c0c2c0d00145084141038403007070400c850f03208880100e0390 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 64858204 1250 64856954 64856959
    0x10212181c05122203110108060a08071806150207031403090114180301050f240a05010804031101020d140601180302042c010501060e03070f03061512050607080703021206 75
    0x5944042240004102089042c1c0800003442c598010003041103017017061052003400d23220400740f03969420800400390014000e043c40354102c10800c0083c1850a6000d4400e0403c2da840030500c82e403500320502c4a0390b504a11000142e010010070001e002417081c400141c03440040c055468045030100282c5080d07100c1844220700329002030000c0741d020b0782c050b68101380c101c014001d0111707040c001c440c101d50b10002d803a0200c031221603260790360100b011a941d4186600d4040c020755680313807038000155041e0400510550030300920f6101d81d0642902803000b00105151128001004424030100c04841031004101e0340c18040243e052401c408040105501103c0c0d0442d404640e907a2a64130302d01c020340c400c19080d100044d004070b03080e01c02c44041d04024182c4032075503250440640c1c10010150707a4100c0d03105031100c0a000321014400310316150040c03407655049a914090a035034801382d118080f000107400340c03480d80003502804403850340042241c2e08018189815030609101c40100d60007000d001d0251031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 64859454 1250 64858204 64858207
    0x50a050405010e0a05040e0109110609012a0209010807150305070818010f09080c0f03070b04030804050a08031306050a1a0613030803010b0309010506010315090506010212181c0512 79
    0xa694514029134058600170300280022596501640d010f401002012100005100450798490514409840c00010b050b9111950780001d4460036002d1641e00a0400400680303400385400360311009012402009003800604071280380101c415680e14005802c84100f50502c021b00039415800f802d40c03504001d00001c5070712405d94007083d8600414409040642070f600345003001084c080403a0203040c5400401003502c04416200661756240d10890000070307c1c101008002c940802c0c0710f41507542d0b209105100315041d040701529010140e03042160032480000f90182d042d8200f000900407950451071b8003005000c00c090450490f4220780f1440c0d5071078000d1501081000c1008101401d82e4021900406e45a81d0303035031582c4200d4078503841140d0540c3c0c0d41d0300b01400f050042d486440707500c5003024250240000703a81007007001805098050f01c0c40d411441002141c80304068900010035140a08030500c0c8043c04028042c8203090b0000d40c8080d00052160713854002158002c20341d00b06210701d102609 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 64860704 1250 64859454 64859477
    0x90a051002070305010e031c02040608010303180e010905040201020c010206070f21020f04080f16051302190203040617040206031b0c100203040b010b070c030809060c0303090705010906050a05040501 87
    0x100d252540c541e03c098065070030100d044121100c044010903400c1411091100000c00c910f0a02d01a80703c0e43c0318120001e8408401040403911480b11035038554004204140e03110754407a6001580442a00005040c035600c80070f01c0119a010000003007000d40a0019080301e160852001d0200b201548000040c4100aa540056030005066903420010307a0031046484804108034000103400c540203404130b5100e02c01800001440004910481c1a0701180b904859800c103401d0009080304040c042d14155000d1040d081c0000100d06609005000790340115161890100001e24845e01c200759040144041c00500c405030300da0743d04507588820304441c6442d070240740d0f400940079803007004c2d01c01086006020643c210b45035150001c40c00f660050034540e100d0391f243c0f0701500a0748104103008002d449200e5040001498040240000e60001018141000c071000145030455008841c1440701c1d1304458802e0001d5078100f101000a000b040c0340c203504010b2054409000c0707104600909051102030b1085 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 64861954 1250 64860704 64860707
    0x30218100206150109050306040b040606060809030403060c0309080307170c090d1407052715010507120504120605060a06030e1510090e010b0a0501050c0c0103200703050703020f03090a0510 83
    0x17503d0061501a0486171103141034281110032040a880860750281046000201d087c400c1301054000e20303074803000c0c40c6405e18542c1c58070003d0100d100d02000b4113807144880004289020041c500c03e0003907403503010b190401e4a503540054100241400207070001403244103141d07110b41070803514055000702100d2510f850014403914025040d4085a8080c100c5d000000c0e10340c014a40c1141020248000d48510b43ca804035402004901205c00f02d0020f00c051052070080780b115072070711f00906450300745213103050340b80c80c0548024010300109985850701c0380b003401942e01f4a441d01e000108031a1800704854441e46030041e445140c46840c03402c9090701e00b0040340c00c04950150034001002d0080701040350251405a4601801c03140c1e44d4140309041103400001c05500074030880b00c42c002035501406240820307100642c0100f04d005400001022040313240240c80d60b2410051a03c24081d40310152584003510700240340000200346060250010301028046480c0e040c23440041d244211403201c803076540d0110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 64863204 1250 64861954 64861967
    0x5070204051e01061713031b06060e0a1d010908190302190905040c0206010312140c03040b04150c1104050a0b0414010f060c080f0a020304030605070302181002061501 73
    0x1d4242c04114844000110700d44c10501c00c0d045149140e414607111784c3c40000000c0c81416100f40074003c0f40308500985003898142403800e003103910030000001c0e1140c03030b040780609801c000c4a0500e112584d41c060411b04080d00c0480c080c080300e80100904c42040560795401c000e0103804003284005140320507009810b80a42c05599000825008089105040060041070740c5247c0c070825001e5440c10142c09035807403000c108141669000403030a1078a4810110403290303244061120045400140940244d1082c180300a01c014040d10440c0c640704c03800c01417000a031000c1d42c01c075807050003126081c03d8002840083c03c2d08204c40300f10b80004856031072182d12800b40c2002c14075560300920b08108100d06010315804981039078092080d4001d07141d2594815a40c09900e07a8024150035001d06c003903007006030080010006a03440c3d1044e2402c1964070340d1010b09580080e1030003400700e50042210f274016410540389075111403044407003003001000904080d4440b000500044600c5a400c041c00482d41d00550 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 64864454 1250 64863204 64863241
    0xc030d050f0c0a29130b060324010906050306090c100917060a051b07020906060f040e07080c0a051911030705030910020106050108131a010902090a05100507020405 72
    0x9007078030f042107094138104051a000084405050031448560180d481a29aa00348a00001c2c140b5041140a6489841c4c03c000c00906440d4144524501004150301481c0b03c107041a41125008141d541001c04410950b4500c1e00aa4000d511680c100100d9a00002e0100daa0758001d560740f01018001441c112005c10312134105140d0140c101440c0d002c1c0c5040040d03003a1041d81204410000c40d22640e111480d1078144e168a03403800402409007070701528008445580002c402400d161908458211511440c1c00c00e40c4a641003c0c100c4c0d0806c40c0d01c54125980c01d074041e00c840a01440d200712184003034114065815076154041018bd413030700d011400b8445480b00b25854100700d0342c44a6482c89c0c442e40c0caa105078043c41c010712107080e0700c000541c0140a0703075040e1751058480344160b6a549201c07003242620044207030b034140c0d8a1903a400400380d0904143c3d0182c0b00315000941e842d0000c10500800010940c80785000e14030500e4080045603214040e00c100f0799040320041401c4d211503040e01c840d2000320 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 64865704 1250 64864454 64864477
    0x6020d020d1b0206070201020307121e11041406160602130306021b100509030403031b02090f011401080405030412050f01060605070309080a0201020c060d021315110c030d050f 77
    0xd1903071242d41c90100c580b160612565085860598a580c0c1c228240c0c0426624040400e0403004202c4905840c0e42200c3c3c8561a141c80344c5c0989901c81a40c08180ca040065030b08044400180c2400901c0c00c4520241e4050001c0d0b400070320b890505084c54118070b100c10400352841e9404100c400318000c1e41c1c80d0040013075401900540d00d950301e030610b000c1100390f846203240c1d8610503e50850044110b5006440c0700d030138000051820280341d62807d80d11941d910f4210348070040d54200f1000180c1c1e558003281d005034140c00c0c191401790b0404500c0301c0500c5036a603a05060180d14010080040c0d0008101c03000d075040315040c0c4032030540b540390082c0707011006c40d2609403a5081c00404100b199018024203040e41c02582c0b4680760560304c0a10300e8459611800190042c0c0001c00340d685c59050603001803140c5131441c0c80061805441c1c04540c95600000d411440c805070408054450040d80100c8145111581c4c002a03c3e5290200c40029900c2c00040d00d10001e010300811182642c1001c14141d618803d500d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 64866954 1250 64865704 64865711
    0xf0f0d0c0801020c0c010815010804020d0602070507050a080312012105100203060108010b04030803010b0702121c02010c4d070503010f020f0a080a020405030307050c24040306020d020d 81
    0x49400d050b010f500018100310080c882e0a078080141d602c42c4000501689400700000f072071107100d800448040030000d2090b82c2105c203050325000004d00c20306c0100320307140c080c101500c038960410341044401310f00c1390f1144071640c0c02030140103001c030460768105044a66038130761400d050116504502c5612041b041c090f015001c0c602401348842c0d540d40084d482030000740e075a06c00350380c0c0354003483d0b43c10b001321300020344014414001448010618001015540e00091000d4400004004080d20b40691500d00c800c11003480d02c0350450854090007410f00800701c81c2000301e0060b40c031a00303800d02215500c9498a0342070b803c1b402e03a8108060503100840e024050301018685c1c1c001d01c080e06656480c10301c1801c2c002d610b010b00780c80001c65903109444000c02d000601c146000c100980407200d880000d0728451420381d0800c4000360b650350400081600318030070000750100c0180d1408210f074000c480441c164582d401607203401c014491000231035058a80c090401030f100e90750904140002e008050400c99440c3c075 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 64868204 1250 64866954 64866959
    0x5040e030c1606020a080903100c030903120b0d06050408090a03050d1101090b01050108060a08072601060b030f0901020d0c05070501050702011407030e100603030302030405060906060f0f0d0c 84
    0x40014400303071401e03030219001e00140701d4041400702d045103d648010b801142e8000c0000c0e004000510700e0a00081c00c442803410a02c2e08502140d42c5075403c80e000c070b981d80202000f01074208944601ca880007002c104440700310007000c540036202c001c5005000c0fa6a0740c1c0043e0800a80c94296040000d0107898011560380724070b003655407800542002004184103440032007810105000e103400445c0e20030f0070741c12141d1a00c401980e00e98006880e00344d2281c1001804174440e5010090340d4000d04008940d0440025401c400310454903d2000407201d5904001c4c0602c1641512012283c00800030b0080580d17503074441079002d00900840e0020500745050450751350003140d00c080640030450090000300301355210700100341e088448a004108103203022400003880035000780d100c03100c0580070900f503600a0004114142c2124055082200400e03404400d00060040800a440e44800e4440080003c2e00380b940006802801094495110b01c2403540900341b22f44620990488155201c00400780c8a40c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 64869454 1250 64868204 64868231
    0x806010f08100e0d030c140d05101203050a0e0d02091015090b0301060f0c05030c0607080601031b1206090513060b03060108070308030606041205060703050a0b150a0318030c050613150e070504 84
    0x81c00f55079084005490540100f0344510a40c1b104060719131580341c1600e4030348000300c00d56070458fd074008a0750000384022443c0160310742c1c024240c802e01e00b5141c9140b40c5030904010003000072925400c1c1003001a0b44505002c81c903003a10403a41595040d052403403950516910460f0f42d4000d103000200140000f240c00c4000e81d4001510f64060405a118041150f8503e13004400302c5804602c0c04502510300b10030705c101a0b0113072a240110032454800485c032107807920100400e640d010ba82480440340d2000b814828000c0314411b1194080e030885c054a000d501d4140d80341c3d81c030300c05804041c0c80b84c203000000c50020350321a002c41d0011300702541821404056410400e46800003294040702190801e40007652000d803a01c11031081c540c0051603426903480c10b150300c00c1c5a40101c0c821000385a83d98044040900c2100c429004241c803a503641e065510b503030b00e0300303038140b42010304640c1c05407501c100312000155026000c04032244800e4000254103003007402489c6402c06680c01141c02920b418100400071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 64870704 1250 64869454 64869461
    0x60d0b1908060406051b0a02032709071413080c0a090608030a031503020a0e0708090d0c08071e050d1116050d03030b0a09020c150903220806010f08100e0d030c140d 72
    0x60b10306480e0101c81440e1080005d40b00b92600c001c58bd4005044000102602d000d41311b414110b02900d0125810003001c01e03c0e8080c02c0805420149043d44040720440052030402e0020b005040b41d04400d22205142c40310403070303481c025041e8070820b0503118a001c0681c148a82c40300300c01035030020800050140e6540d0740d41071490041c0c90f040006031880001510006001a02e4080e00283d07a0f552002134865442d4040d0641203040101c40303050305034113420344580c10b041c40342c450747c0c4c0100080d014030100048050a80601c400c512010340d0004011407076035020184da01d6044410a480882c1c5079034051908070024080c0600c0e9541c0b0150350200821640ca465002d0441200ca820464102002c078900c0e035024640100d403c0b005a80c0104125506442c3d2040d884903141103a00501145546601c0d07034604291003600080c1c19051a1401007201c400104101e114402400d5400c02c1500c680002d030b0343d100e00782d1801500500d502c440780190f82c544112088107000316885071032a1a003010503904d0019 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 64871954 1250 64870704 64870717
    0x80601020f010c020d03110c0a0c051e01080c030408070b161209080a0c1415040c24080910060b04080c061303020915060d0b1908060406051b0a0203 65
    0x1480740980464001030140308046508900c0d400030103072014a00001c8028060744030750b000e40300c0c80c01d01c8002480c0c0c1e810444070a10a120704141d920070f07400d080c28085051208000452500380403064144540d0b0462001d542000d88040c1041d40c0796a541000c48880c8169907006082140752820810441c082c02015a4244030903138410407d142d80480040030380b115107101504425041092104003400707004041500c034032401c07500b03000c402030f101102e04100b88002209003221601d01000200150003490030058a0002500c403207054414514244da40d0b1052020b9060091040209048110801c0465640140304c41c0030321980344c40b0020f60015800a1041c03984c5486103c2d072080841c500b690545848440c1c11088641311846c40e020000d203903001134864964001e00d45041c080d581c80b2200204102a0289408070b801241d10082c00b007140051000c0e61a880c1c85400140030501c000b141403a04507402c5000850a61528010030500c1030740305800d01118140029120b00054001c0040e104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 64873204 1250 64871954 64871957
    0x7170c07032112020c0c12010207020918030d0b010306090608070e010801020c06041104060b0d05061e0f0108041106041221050f03040c1806050901080c0d030f050f030106080601 78
    0xe8030760b0340d000707641004403514152004078018441c5030681ea0b0099000d8410081280300f15808845014042a131054170301c032160680d40d400060a60560508109050b0404501d00703500003c0205c01c486030341c07280145d04146001c01d071981c41000c0703e68401c0d00060054210b890003045030030b0359400601e071f031611641301e40d90804030801c00000d0604c0040c4280c0b0302850240019107101c0d69a56a82c01960f4a802892503006a031980045424092134000d8042e03229000e000090f542459000c00a0841c1652000a0040a811069441910344d2000b0740d4580c01c0038200380c0000e80712440d0800310010100b0410780c0110011800284202079900c040007000d0050b207501d650701c080b030030b81c0f54540448840c2220102d241000b02030211a880402558000d001ea000d49903240e485030080c0c86071000080395003c0c86070f2203080510613850000c044d21b005000e40002030041b5000003000c45c041c02e0b107062024090281c0341c091806028010401c41c0c071003141d441c1c4c10995a60311081c0180801505131030460 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 64874454 1250 64873204 64873223
    0x903030b1c0201081e0c0702031e1b0402040306020307020a020a0608040f030c050c0310020c0d030216110109030b04060c14090d0b06010516050105150619030207170c0703 75
    0xc5941c14061203405040089030058081004a9001035404090241c1301c1e1044d07400071403810001c00740a800302c50007840007020b01503890310b840c010186411a0b600095040b05000181c42c0410900000c400e281d03207022450846045000c24000f400a029603400a030449000104108545601150761040544226214800181c44040c00c8036101001c0303a008160800c16120036011078052400ca0026500c101d08403601844510086070403c1013020b244820033780c0104942800c01014070034106002c00305c1c502181040043c03203000c02c400300c1c00c08001e010681821072140c426440b5540300d101a64216043e02802c2c2400d190400c028045e40030205c002a50201000c0c1c00440c46000b101c1c8244001007141000441985aa40382c1c241e000c1e2005041c480c0c20482404880b40c03c09822040341e0184000142c01e01d0401d0b196020b900007011300c0d610411042081002ca100c4108800c284140356180058031199030345021a101070740b40114100050000c516a02500c90000d1200c00f0380e0b119102030b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 64875704 1250 64874454 64874471
    0x60902010816050a140702031c030608121b010b0a1805061f080603010b030a030201050103050f010506101407060608010f1410030f020d060e030307080c070201080103061a060d090303 80
    0x71100d602c54891044000b9004001401c0c640e880f40e40300041c08045c0000040c034110065000910700f9240c1c001c5542c0700b44095800003805501031190f40001c00a40d4003601244610712400340e12403040303042d00400e3340840c0320781c1110602c095204004600c0301401450005444008031030340381e5108611403010a09040c00500340b400c01744250040c009426000c00079001d0081c9080c0c2c1c2425004090640641d038494200810307690411401d00751900030380000803c1c1d411401c6c502c0c00e210581c0070410340c61381050140903103034840400d10718814400d441c04105c90b1800040f9001240700f8032601500f15400c01c18003041301c02065100d40c445000d440710400110b0389020030b0420b503001c01c450f810102502c01e0820004102d413151304484540c030082621400c260590f50340c4003191100000150507a00110400c41042e410030040d5401511110070a400c110706030340003c0900405000040010351540c019115102c040c10300e201800320000c0c000760700c840303103298010010400c0520540000e414899003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 64876954 1250 64875704 64875721
    0x504020a05030c031f120302010f06060e060309070b040906051002070302091609030501020325020a050601090b0102190605060301110301050a03060209120303040303143d03020901030609020108 85
    0x200c681189031601e8150459580d180d0311891a040101050000106615546482d084041c40b000103424003070400030014201e8103001f400c40b541102d400d8541403810800b8009540c002c54241c0500c0000c0311134540e2170340e6074181070741001e5103039200e1501d0140108001c600c03441c19070414000e40d1410b8442c059848a0004200d0350ba54040c0f0020390484c2410001c90003100000d008808a078605086c400011982c81d07079a0340c2280d00c1140e900003050030680c0045070768428107040717500c211098402026020351544900e51908010301c070314040669200704414841c0d00a00864065032074220000141648900301880a0801183e03024800d51815507660345a92158003524181d500c0034060064903401d596894000b540328520480e8840540151000d440c0c00420046104d648a654046403044a51510111800b40604504808511449207690b01441c4030006c81840c10580340030b00006071414a0010071100c2e076000a9045080f00c4000301c02d0028941103840c0d00d42c0700303a840f0001550390651 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 64878204 1250 64876954 64876957
    0xa030516180b09060411040b0301030b06040b10050a121e150807030503070b09011e1b171f05030d1106070504050901181103090109021e0f0603040c090c020a0c050402 73
    0x180c2e6a40154280301044250502d68032071001011240e640e14507180c0c4480700368034160426803044450361010410007080382032502440d03d03002e0040d55010707155504000c01400c2c5004a58001e0b0820800c1b402e160b144030040c1d0041d8012030541200daa52107070500b110311016043c440000014240035070800640b05900040c902c0880f504500035500707140b4180e0700c6420382000644021032541d2612403561107059121b502001800180f400020b4010411410745403440c10000c0703100c01e001142c0703500d4801030403029946500207945040460381d0740080403030b2402e10200e60846500f61107542440049176070040709082c03914004004031012551050000c86643c456400384a811070035260040001250080d02c1c0c0b00c49000d1004045424690800180b001d508100c4107500c2d0390307450745800002d50618110314400e4054402c070344d181e000684d4010403080ca20780f90b1000d005840000010702840000810362001c1d00c180f44080c004a4103801e030003543c400402c0000c0e03481041d0003400207001d140510 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 64879454 1250 64878204 64878221
    0x10b030106050a061b1419060b0103091509050a0b0a0207020906060702030a030809010209100306051815120a02090106020a0b240405070219120e030609060c090a03051618 75
    0x343d40706034100c0d9030000340c17465044110084aa8142480e00c596070340c00d003030110401c9a0404017100658007071504002090360040d0400d24181803500c04814041500b8000628204451060200d0200e40b6464102d18203590b048014048074900c1d02404240402c580013440124001c40e00e0403619280c0204200c054451140002e6055100841c4400002c1c0600e05443e4003800343d20005081c0306207940400c2280801c4c607541c5c000a556020306000700d15040c081303100c1c04141c203210b444851801c0004108c09003032040030300e8880e01451498a0b00300700101721a42815a01600c03507d0f00356501c10b00a99600704501040340c11700203240c00a450620102d400003e001044c10002c0100c0041506210007000050a864214040e84d40c800301e07622213a140d81c0310300902c580c170f05102c1c0c0e020704400101540440d0328a14880d0b00068180b0090007000204282c010000c070755070750b0380c1c1d007000310001c1c8c00000c10760703c020024003130001c4803496000f014112108480d01401644005041000e0290031142a071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 64880704 1250 64879454 64879457
    0xf0e0604020d02012304090f05090d050d02071b050f060313170706090c090506040209030c30030406020606040504030804030c060f0f020418020408070303050c10020c010b030106050a06 81
    0x6000180252030924412042e0318010b060850080303080c0406140510900d20b622101400300050030422040c45106181e83d000d42000100150b050440c5195141c01d40d000d101020050301280d01108140a9411540c9881d440001030460000c0f0b27210a051501c0f541c494288101c040742030f054854100003048910030781d018042d0b000724641356640d0b030400402d44c15201c84110810701c08000002d10622809080310302070002241c41d103192103180c0e025910010282401030b40140a0100107440c00140a0020b110884101c003401c0c105100d41a0108a551036000c590b010003030f00b00d5070150011000700140c80e503a0b426214907940700702c144000d80d0015038008001400321030000c0c003c00d11035407215245500c20b10000c9100c40240a0314010b45041c000701d803104542c0007170104174509511081c038802000100c0154103042c54648020703101d580341d100207803d0100025003180354010074001c207010807003008400c41d100c2c506241c1c214024603d0b04036641c001e41c43c000380072030f19141450f940c4007141c000703 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 64881954 1250 64880704 64880713
    0xf11031003080307020703060515030c030d0207060e03010b0a030308010623030c0c0a050d030e060f04030206070c080d1518050906070309030306030203150f01090605011b0f0f0305030603010f0e 85
    0x2103030340b0400958001001c0740c046000300080400012801e01580d03008218072403041c2100c2c84400101401c00180f41c042038860340c410b0f841700a000303801080788000c40d0404e0a000000144003008a80900301c1c500c806a0f1082c0701c50000f00c10180c20040685c181d07070b0556039210300001c0e028242a80c01070b07101484405440140002821150400018549004000c0a984071400141e84040c6041c00c0f0410140100745c8550b903200031802c042080c540c0c807020f6102080c02078105628083c0d101c05024000b0803c000b21441f40c1000d10111100b200d40c940130004042191451441d02c080700c00c6401d001d5404c03002d40820826076a860305003e0706005030305c01070181c00030781c441d01001c0c0c00411000030110145521542c0020150b41e080c8005440300c200244003228900d008280301c603011105800c946015031130404107200690b801204410200402104000d8144603400e06680d0b407004003200030030580c280300e00d80d410980d001c40654003414040d030092050015140d03000c01540d02103a090300c01e50b0300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 64883204 1250 64881954 64881959
    0xa030210120603050f0f010b062508030411011b0201080a0c1115060907021902060f040b0a121104030b0406020304140d051810050d0f02040b0a030f110310 68
    0x3084045040003864a00302950a030310308205160954040790300948098220543d090601001401007480d044040c8008001c1444c6590006140c0d0040b5858002c0d03807031040c883e00c288699222802d50b14660040d180740d0b107030710f030a25201ea1001c00441d595800150306003c01440d00580c5203004801a41c16118031a0a45c1d480707210400410f18900c0d100200725821511060004083c403c055440f205050f03064040c0c580402402004400a0000030465101103071b03040b00400c000b9486a40180d0443e1015030382d0712107442c400310500540c0c00800b1121030001c0c42ca64820b03080744004400c03a55000e0309001d140705108400d00c5500691001918010144001400148080d1b0080d940703e40b04151140100c031078011190300d0004642c08207000316030001000041255003403185030401c0070407251010840711164004009004103120159000c0e120500c04800c0d0304540c06950103003004190045d11a545600300038003411042d0120362041d480d04d44610028184a41202e00c10b00c101c560100601c0e1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 64884454 1250 64883204 64883209
    0x7051e011d0a2a030f0b011403030d0b1302040602061b0a050d0e0708070303020d08010b0304020112020304060902031204050406080309030c010f050706050f010806160e010f03091202030a020d0e0a0302 88
    0x10f43c3d07000c2000f100c1030868034800e110901080c504042d40c001c00744c145d0440814540741400c41010381252080c1c4d40556102e584940e00001110210400003c000c12481120008101d00e00503181c01d0249075400413401058040e130005119200e6001c000200000d40c0b104660f1224a21807c002240041d40c1000301c0041d070f21182e005030707007010100c0c0c0845540d00d0342c45c140503041210700d80040300140c1101105c42c824961180205002d4100440054034608041e4000b030f141e690440e0071101c445402200040502c43c2a500c5801ca5036000740555101e540041c09250b9680d01c0340c0a144c0c4901d1420902081406000040d81c2080700c000e401064070303101a00040d65802c13004526a41040002c00102c00014828001c0d00c4c003403081c0c0c075802501941000c1445061103002400e0089168000210310a103540c800000c000021080c240301c0c00d074401c801c034100d02402c0d8450b4003500848040c01d00c90741640d0b0000040c00920800e5090f10440c1c8044502121824001c50a4581c80717540800300f0320151 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 64885704 1250 64884454 64884473
    0x501140c0d1a040c090510090803071e020d06020a0f05130308031f09060906060e030601030308060307090e031908010602060105010810080d020f010506010302090a0e0c07051e011d0a 80
    0x15031803001c1c1c21080103816400103040c1c4d07481384600b2001400c240801c0061f820050a2100c124842c2c3c18150001ca00780b00603039690340a82d4001078108503c99002001d011101204e052055401a20b4450918141c1c02e043c0003960145406030006200d035000c8140741440707003050b144c000214a03484480d8074503680b1003820540000d82110544a440f004020380700031044203410043c9003261000c130b00545050029011580c25912039800d2140900c41c805c039aa03400f141c4a410b40c2e905060000d01c5868280109180610a030800c00066142ca510720050080000142103440c1541d000140030b000410300c02c031108442841464056408840140000c0d0300400a583d4440810035030800c5095071004085e141030360a034007204c00351304114120b04400d0000e00585501c42000c5c00c00354035103c02000428102c60030761044540b41211003010542e01031100e07049461554106003103130210228429810984040380c24041825131038400b01e50380c01d40103920141001030b809006404505a540c990800c1c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 64886954 1250 64885704 64885721
    0xc021207110f0303190905010905040e0309040f1805031305060f03010308160b04110102060a0b0609010c06060302030304061106070201111c060509090d090807030f081815070501140c0d 81
    0x35002c00c3c00381002c40820741401c002c0d00341042d03a801b80550b03d040005000440142c020902035401c01c01068900c0c9070020840b141c40006440c0099181c140f50070b10f5009040d103401d2071841e942c0c07421805040c880b00001070145200d41802c03901c05140e490040012030702c82c08205440707100040c401080400c03640405401080030303000903038000a038550380c3c3d07400072001100c003219140cbe603084070354038a940e04105003a8840000c04040015820b4540081d50798001c070300d85070f4108184080f41004100171a0820802154080c04686d211600c610001c0d0101012035041d461a20031070f0700003003d89105004200c000a00100c1a030b02e803114900701000d0b945401e901c40c0035155110f51002800740c42e8450824460042c03100500b044010303041000306031078107a40c032080840e4800c40060021403000070321401420b41c0300035019543c0038215002c6214900d0241d00680c0103200c102c00e03e41001d91f41d00100351051080000300121000000c40115440042d81e110112100a2000d405903500d20f40c0403146 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 64888204 1250 64886954 64886959
    0x4030507050604080408100b0109120203100507030506010f020123060d050706020309040f06030203032a03030903090a0b071a18010906090b161202090103060312030c021207110f 78
    0x24124007900c850303240c004261000c40308803000207410041d2140c00d006100040d0482803060041442580008201d1b890900411800d07074011591201155800c020f92000d40721488020700007071030801170103402801c0c2200d205010904045a586004c0d10621502850344044c0c42d0441448140c0745100d07041800003451250040011401507010130420040c3d01d00500c410382c000c42e91000c6010901c4195400c044000340751030b04124003403005aa01205603500103008210607c07040110026503015a0344284040080d40400428000c5110f004001011914826100410b0300350752110190014405d4840141205040c1143d01c4e50500e40b2041b12a00040070080a10300e103410304908500f100ca64010171240b0340e6446c0d04201c10400a4078182d5800300740351424110040c860703d40071b006030b204108142c10b8180d00051400450f8040d40c000c2c000b440d00484400000100c03940040c0051941400c070b03c015110300070390001d010000e0422241c3c80e0390310550700440420204240000b9403012481d455 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 64889454 1250 64888204 64888207
    0x806090f16030f0905072115020d0612030503060316081b01210f0506040204030f06090f0c03120e1005040506030903160c06080f04020901120201090812041a09030a0b040305 76
    0x221034420f80c0c001c9504607030160b0f028242c00c5283c440e141c0312a50044984c1d4422404000c540c0c404244e80d00d03103d0a444176040000350f030360145005404000c043d00d4003c200c445011950f40000d059000003d14400da40a07000c40d401100040100091052a40305d0013025074800071014903d10041007085c41045418102400b10030281241c0083c0c1c40c0510306d50703e29882d55500103030b04c200e4681c01866007103e01500c0031844c184c2035440c1c5407036111803c0e202803e0030341c0b81d03008031003001a02c5181c0091181c01002402040b030f182d1405028070002b03040c0290000e2a625140305162400104140b42c0c1401d680ba040e2501e4a000103002d4240c00c01080e6100e1400144115800250407054800c1400c0c420300d001781085d400d001c8060030205025141900e010002170800c00140ca0314040305064480c0f1611443c07414400d44012103400c6007a8000002e01e00482d86501c107044016005041503501e03540c907020744a540c81080451070b01031301d00302a07410352202c4401c4d408980030000040c0c129000e49042c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 64890704 1250 64889454 64889471
    0x30e0a0302221b0201020a090f06020c01180503060f0402040c02010e0304050d0c09050c04050a090b09040f0807021e0102010e0a1713030503070309050f22020d0b03100b010806090f1603 81
    0x6040400e0000880004d40d400007050806280e02117036802c0580000d2000c0002c00303082030b400030343d21440321080c0b034148602a446141c0b90511425294014180102124028a4500d4010076410310666040f40a1400c00e00d100c0d09090040c040e4156094011009606040c904000c00103442c82d240400c0c1c2c0e0308070028101040142650103654800d880c40d0010316602c9241506010800140382e0001e1071461130030348982400c1c0c0c1c07000e1411f81c02a0700240419014801410030804c24459010000e41c071589070742860180c1c03403e0280a03084100241c00802152410b01c0400703071100d403041c0c1c004050080076403454803a500b01c40c0142000d441c14175043e114071130f04d95503024503603800340c0e0050780815040c1d02e0411091900e0700581c1001c240c2510703903650031400030141d121030049101c0c003c81d02c0e80c3c0200c0daa58580400d60f110307010010000f403c85006010354524040140260343c1038500056180b800140c45003002c0342c1d12070041e40c0c2c580728441c950340d45404189041d1640004142050741381c07000c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 64891954 1250 64890704 64890731
    0x904020d060e060306160203041a0910030e100b0906060d0b030703051b0d0305090907032903010b0d0201080a09150203010303021e190204090f020418030e0a030222 72
    0x7810042d051504003401e69091602c105841c250b07005150811440200d291400300c03a902006607402c46038142e45594591140510392040e034081c1120740b6400c42c00f10100c46106503415001003c56115200071750f049a00c0b012400383c196050355800396004980785001c134a007030400c03a0061241a640c058009091415080003900704181a40140c6140d07000c02c000794401c125001074891005c008541b00501c940301641c01400c2805a0b5801a00c21051400005c0e66207000b81c00180c03c045901c2030f000520b0f510092060150a034001d001170003980313050401e01d1581428650540140d03016111403a96580e40014038014080c1000d00b105e203e910303078540d10103024a070300107103010794803940140a40c00c00340030140f04a8542c1c9460324015070300c058201840300800300f1480e00c2c4580c041c0d50128030700c1c246007000d6810f03c0d81040020b40180c94070030170700c1804130304000e0541480d2096550a05000000007003020070300050002030351100e1000c2a10982240c0c040c6a03000c0316120b803502290f0300300075001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 64893204 1250 64891954 64891961
    0x703031202040b0f0c010b09060109030f0312020c0a03020c04050105060405090405120f0d050906010614130515030615030103020f0108041a040605090d0504030c0603230702071404090b0c0904020d 86
    0x20301e11303045400803800c010030100a0180c00c040f0101580c420000d032410400007480e41809100280c010b100e486001014103100f50580181c410b0403080a654951a8031032840d0385924044003034005000d07100d460501450130303014040c100d0714010041800c4c41d080808210300a240908200d07058846ca1041480c49490700e00035080e1082d06d4000c81d612410000765410030f1f104010414010ba8004c0e10041c86042c0d04020060003802d01d00c42038036281c80300707204005c842801c0b94100c9948298003c0b1f0350b41c5c5005116004621450043d80d0b0040401120005c401c5c081c002030000030b41c03120700505c1c0010554494200c50b40d100e80150f4600905420302030f0500b0401c0701c1502c09450403034441c8108580720303000300302e41d550744251807400c0c40c42c00b40f458440480345429801008205501c171003400040c95085484080d15141d0400c011407141022a00690703070301c119200e01c04c00451047c1300340340319207820b01c0303820140350304030405030140d54510301d00041940c030840003681e102d0fa00f807044850f005075521 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 64894454 1250 64893204 64893217
    0x906030b0d1e0c1e060206060d0602090a030507080106152111090d0609050105090a11090c040b0a0215010603182307030507030203010b041b0c02040207060212040311030c0703031202040b 82
    0x1355010580d141c0c6480102c00181a002401554032841c144039182d1a030010607584e96411100068641030307480006142058150b102030001e10510307002080c800d01c19440b8508840b110410745108001004003034071018058200c0b03c3e01c4480504d81080c00e10000d4010602041034000d140345000900000035003455103200058a40300d5031002080d040007000d10405802080040050004450700c0e41c3e80700c092000b10360200d02801204010480c524154401e9a02070401004002e44075244d41000032f54489100000c072280344020b200008009001c3e100e00d00031852154092602c000c45134a0f0744909522051060781c441006000c102c60210052140340b01451040c000b91010910358010076095801000340148214500301d4580d1012100e8005419020485c1c03d00c40b0180b0b407a070001074000c0c020000041c0c005800000c214601254609025116500c00d4446c40c081050014200399203024203550240705074480c95050000ca4003d5001d06540400c0b800054a001d4480c0301c141444d0300b010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 64895704 1250 64894454 64894469
    0x110a030b01110601050f0d0203070b1605061b031618090b03162103020a050102030103060903120e0606061803030a0c0201091a03070f050705010501030b070906030b0d1e0c 75
    0x1203610035015a8030001d4024104800341c010145541020f0004801285c44420240303d01101400d000447d00c0500c0010f0003041740c46004c035151143c2c1c0c00c11040c03c0001f442c0032510b5020300400500740c07142c0302c41460b803044140200f041c103587d030b0407401c101380e8000c000800082c402c009403030041d60980c2d0f03070341300f405410401d80110740625800b051503d0701c80700111880440c0c0008030244101140390001c0d000c1d8402c40d200c089464025420241c4c14090146000307001540000700110a00001d6084505944e2107582c80c0f040c5415680aa071003100c00048240145800403004104c040c58071001070030584418032001c00c001c518010000e4650342c400c1d851b0341d001c5a004070855043d50b070030820542c003c002120160481e104400400081c5110003400c02c4144a402208009100d1050040e10039aa80c010300070003095840e0308000c098510300711000c00c00106c80a4010030031511038001d80794081c1c4003030039001c1a48174907503c2588a2800e04880f900203508030084101142c651410b401c0140100d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 64896954 1250 64895704 64895711
    0x60d0203120a030612051c05160f020f1206010510210f0510030b010603090c0302040c030603051603030804080304050a0b07050306031e0303040303090c09021215010c02060a030f110a03 81
    0x20302d026003a40c0b41d07030307104100c09881e160300f1002041002c070301300580a030b0200d03e42089601814040d29140200d05e9030b40050400c005040003041004003900d80d006008860b41c200b22800302c0b003040009a98000300c80016001400100310b18103048407141c8000015083c103410380500d0f000119448480c1c45065940261501094550100700340b1805400002c600e440890b40d03402d503115692180418828141010340c2c8041a001303000460b00707500701070f550013030050220401e4900c1c024054213090100b5109070190100c10070010140034101004c41e83d00d0744840155541c2c5445014030b80d0802481600c030b5010b541e800200148a0782515885003580d625029242d041000074140380002802c000c01481c059200c0c60141c2513400400d495010f40d2600d0003140c0720403186001d054000195000c15251400030a440842544d001441b070b114108603e03480b00c0f038100010044848880c0710b280a50032100800c13041d51444c2c0300e600200007030f050300500031915052800c42120590b20041120002984c1c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 64898204 1250 64896954 64896967
    0x51203040e0603060402090f06010504120602070309061107050d080d05010e010e0601030c09090b0a0503030c0a0209090102041508130209100303032f07020312030703060302130c05030708060d020312 87
    0x546681103801c8003042d001024940380540c003113242180c01410600748543c609000424032b0b031154003220084c105201d00c003c001142c0c1e14050700a074119140440109842d03a001043c1c1d03034410070440400c4503001008000151400092011418003000243c0c1c0d04402003089078071141c40c901409001f000c00e9160b214441d850504e641580680140000d410181410070102c8441e5000c0051001d503071680c0320004026108100240942020b94042500750102043d061052040406c00407415030007660b00b94890780e00c030400076080340320700c0c0103100741d00003c44a134100032480703098800d03400300000c0c001c0303900f117a038607000505840012511089440412282442010b83c50f00410401980078a03210031021100c035034603c40c0207200720401c54601da01042440640d82d08020440101075500c4e01540d8905241034000c001d81138034001a4042d1401d01695084e00e00707a0700c40c0b081888500d44d501425521054000c4888510180165600c00401105440580d070140b0484100c004100b1029940e00c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 64899454 1250 64898204 64898219
    0x5010b030405060106172d01080606030d020c15070f062a0503060109060e040f05100602070602030f0909060f061207080105040908030402060a0302040b031021150903020705120304 79
    0x740580108003007102a42c484107801d940c00c07204d140c012200b0307110041041c0248000c0c5413001d0303c003080341f003490000900020380c800000c60b0160050380e0030340a8400039803110300c040c2c0e60381d05a68101034200d4089030726189440ac40307402420415205103183da50b01038030390300c424080c0e41440e002541c180c40c0e021101c41d03011441540c0000420100d042c11411403030108006428441140b00b100c1c2031001302990b0300900d644541c03240190001402042142d0704020084442e0381c000360054502610405002064090000065907014070719243e003540b512026005020b050800507207201d07084900d90f110594141e0b6420064050350302892941d00c048d25200000600307160041c0e000d80e0286192a50300008151000101d0382d202c5e8059400b0783c1c1d640f0034031000300c00904c0b41d944580001030002c014824082c41c800c4d4281c00312080c003131400b0640c4252038402c00086180c80d0004100509000c1c201c000c8031703015044400d0075070007070054891256480001c41e1409056500c950b140d03400c0000c041c082c07130 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 64900704 1250 64899454 64899463
    0x8070e0601080a11070f0303020c010606030e060705190e011b0b1e010f03030c1a0c07050f01060509060f04060b0f040f15050f070c031704061101050402060f07020a03020405010b030405 81
    0x2d00c0c3c0180901070031300750104103400751007291006400c4001c842020740c14140603404446038285054020040550348840c0180203104040c1c00d640c03a0b0040a01241029204030182e8842460070010b081d62811055010381300c1c401d125204c10b050144490380510544801031400c203040703004010500451400200007406c40800207100300840381d20600501048110100e040700f43d03903050800351810452400c0480004210310441c580c00a5503d041000308440d210144c08624030074403c8a034640041c1c00d07d07600f41d9005009542c3c200c0e00d880c1c0014a5072070080704205a80e00c024100007440c5031a400e02d81d001d40e01201c3d058080c43c00003e02000054030107120302c00102000c0c10302d6800d501e840c0b40d0081891041400748280e550002c10707a41c1c1400148070458000b0359110100b20300504601101c540705030001e2103010082561082941e140c0c02041c02807911484d80202502d01c0c242c400c2c010481e0940180c0016604075124000210068960f80b0a80b0b02911640803065240d280c40e2905a162 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 64901954 1250 64900704 64900711
    0x30c010b2704240f1508120d0204080105070207080d0806010f0806042406140c0309011107080106120c05010c0b0a0f0b0d050a050d02070f0e04030e03030a0c05070b09060301090203090708070e060108 87
    0x1145c25040040142d0400410708500c0601500b15650765203840241c410081d000d82d80140b90030394a00000e21142c0c540020340342d403c43d00300310709070b812544100030251603144c82280d04c907011401185102c3d03908c0c4e2188044e10307440703100208002040380c2090601941e0044041102000030103d001c180041e0713030000c01d041441f07400080d030b0504d40070b1120115a140d0082c05031103814415107042c0d5469041081c4005000350075000003c1007020354401141604101c17110301600c2e161a00c00c404520b40d40305000c030601e181d8219500902a45400007000000c0c101d40c041040c4003a5181220541e5035104a2003006440c080c03401031942408a04000341001c16001c1180150340c0150030410480380040d10740703c2100c031b041c400c403541507540341000d85050000c1c088056050200150b000903940d044042e80084034021801c542002d034840320300d10740c90700c261000194070003805d10040105800640045071302800b0b06047d07800181e40e0b44451071501125400c2a003407283c0400811427103503480b11000f5417 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 64903204 1250 64901954 64901981
    0xc0a030e0916091202060415030501030b0a0e0c010806060d06030c2d031202030d050406150605030705160c1a030703050f0105060a0c03020717030c010b2704240f 71
    0x1a02c01c0740720303030140002506205098103542e50003a01419599500159001082109920301520002080041c01024240001c64807041d481000c15400402446020022b8400d5001050002e6250006484011006050580c048802c0221303140404541c040e4000540c414100c2c0c0c0da005003000c5000c008100c404900911100f03504066050020111034580202c0703030008641200d164107600101c1c00c510480c10000700340c60030710b02070008114959100c01240454038003101c101039150700084800c0e20003a617a050004e041402070130030b90348844a210701c116104520010701c2980c0c8881e04801c0283c0fa0804021100c404400c1203010f03a050701034a9030000c0ea18440705015818070000956030b0084d603141d5805c100907044044201402080380c03801030300d182c04400040b21000c43c009039503030b400308030541003650030320000e0107481c2480d44d0100400d412001c0b0300c0355180302c1c40070100c2e0600c000070015180411816050702001f10707042483c4100c882140d20100c0c1c8146e5000c0020b00f6581240c04808 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 64904454 1250 64903204 64903231
    0x60301020306100f0c0818030f150106260f090f0607020304060f020f010e0304090b03031312150f0c1103030601090902090102070b18031e100903050c0a030e09 70
    0x881035031a030f08502103203c0c540c103000307016401e507183c200c2e14030b240d880d4001c00305000064051400304a501c41511802c108800300c560b14050b030b1500948401c4c8601d90401c1c00d401010041c40024010032140d40002d009610388001c41c400081c0103c051001524801402d017951020302004c00c1007840080c400ad1076003002040a42480036000355244680d20882007000350041030a010103209000e2100141d515030001d00201c240c1d0241d29440794005c3c07056030b9901e445e004102002c1c2c2004420b03500b111031844101140745150203140710080b81c006a0445140040e02003101c2e076401d040c0f103401010099020002660b48a00c0c00286c0001c070f00d8051041207a00900c208401c0c1c0c5c1c0d202c070002094496505001d603d030921600141d24080268100035508500868403582040480c2144000c40c4011000c40b80c0504811034a6121205282c911420642207005110100a000c1e000106024464903003a4900120421b0060801d405e543d82100011400040d805052800c8a141604246031487c80b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 64905704 1250 64904454 64904461
    0xf0c0b0304050c0609120604030807030e010c020709022809030506181902030705030f03030a0b0105040f171e0313090516081e041506080a02060304021309020301020c01020a02060603010203 83
    0x243d5031403501c510540b0500c00012412404d0b1a040078000100315040100c030300c01d08081c43c000c0c2032000100c50b8880000c0c6008810300c3c1c50780c0140580d40418040e0340140c40054100394dd01c4002c0d601c0300800c03440703004442540c15032088824900390410b2500340d9558107054194904541002d101401502d4141c103202c40e640388000f0040f683c81b0036030b00c03150124041300a5520200f030501416034807030303035040c06684134204a06070040002c0d881661aa9820840c138900d840064a0741e00807030260800d40c2030b400d80180560220300e207144601c0511070b01217450240d03210000c3c80c170700021406a00000e80000c0344141010560710707214000360000d0607041c0103c2c0b620100e80c0c0701e40101d008402c401c1044581c08144000c144c0c03001d40182450380103800b1884e01c2ccc103090501c20896032012014003545018400942400003049070003070a5401000f043c50b50312a0340030031030364440800f666080581d840b040c1e030380165002d200400005090000150310752601240180c14001c2c0200f0071070182c0d0040042 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 64906954 1250 64905704 64905713
    0x60f090303121515050901080f1302090901020d0207060914011e0c0311030901050f07140d0c110d180504090809040203040f080409060e0a0911010e030f0a0f0c0b0304 73
    0x40c1c04164041d40d00015001a10b46140103e0844540c0000d070001264240c124001d54484024614510280ca0b455410f86600b8404045130a00b00c60f144481d1840d842c85800600c2c00c000d1954110718004005824207414501c410102c0e80030480440701076550340300b900200040c0340c4020201c4520300001708280315015512116594060000d200d400b95101d5602c2c20242c083d80c011032a0200904000e600d03490181c056030300070a804e441ca44540070ba200300040d00c0521519610903500320381c8604500784942119403d01510f403003141081845905800200003880810464200034400d070358180c003049030030b0009219590a500420301031402c0003916000704642c1001c032282c29030306072030069403642c440c103101c0d10503c14100e00400070746000500040781c01e001d0f080402528a011201010740c0c845950300011900c40a40081000b50710601d6441c096000380c080d041e4400c4044c0c1a40d208182010015007006461501100e07030740003000000c8140300203403502501500084038085c1c518101030300c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 64908204 1250 64906954 64906967
    0x50a030c05120714040305060c0c011d030d020901090e040f060501080c0f0915090a050603010606030207050c0d0507080304080609010e0f060f040602070b0702010b0906030304050a03080c03040807060207060f090303 94
    0x140000b40220300b11035100080c03140342110005c541250507980c0a01304860403101c182d012981440ac1c540c24810340c034191610100c2d142d90918050401186045040304c1034001a400045001e0305020366080c00041420980300c485100300d1058256040381112442c0442c1110010703040307415039600044070200e164646003001640044211010f0784141c1c1e07000d01030000d102d00f0f503403441c3d0070001420500002c24455045503024510440080c40326507201c00c070072022400f5400024003554002d228110b4203003000f8000d00c0b04140240165003155480d84825851680a98026011540b101082041030f000078841c1001b03100c00740d40503000400c01403c1003035942e04080d080c0d0b900d80d0701d900b001c2020814541d04840203651b0007011001d841c41c220300c001e0700810042003114090f46509000071400c0c0f5002c011103050b80e400600020303038070b4103540310076560341c100c1d410440c00b0748003c0001040001d81009103100074280da80c002c9c8a454180344006049508001407441071003c230503c14400203030000c0c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 64909454 1250 64908204 64908211
    0x60f07050901081b1c1407050d0c0c05060c04050f0f010801170c04110702010201050609010b0a110a0506040f03090906061b020619020105011403070f0909020102030415050a030c0512 80
    0x10f0a90030341d0b01c441d911403c81e2100000d21440816001074101342050030b9018044200c80100300800103c17680004c040e0300c2800444202001403401c115018208485510071321503140c4034a0600c24405141c1c3e220b0746468016102d410031104003040400ca00e00e03200d24607000e605002d5070030185000c825030001e0544441130103031035182d401c0544107071042d12040250021852008000b4498402c2da4059141740d644000e1050740154203040000d90075013004611941210070419101c0c2c64009002402c0305c3d0b00405e143c10000e00d02a604d5884085030080000d64050fa00031650034060550515015013032111a0b48409402820000700308500e80d0403d0f03043d03601b03101045070780071260b8461001a40034840e004c001c800500b030300120b030b206056055000314180c1e40000f818448a0402900b0560744141601c5038001d1902c0c00e0b101881500c010f508200c1d60b0b00c0c418011203081c00e07115604a03d40744c079401d80180c00214081080708030945c3c54014081c0d071800c5410b240d4642920b081a0072003140004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 64910704 1250 64909454 64909457
    0x150e0d0e0a080a1505060d0804030b270a0605090a021201020901020f0a080403030c17181002070320010315060807021e0a0b060303040911070204110306031e07030b0a050702060f07050901 82
    0x601c0046c1490b201e9101e00403d081c1e201002a03034490700c3c6d01d0070780b1109900341c5034580c0983e1200c00c10403c10071844c4002400c0c1c0c060400406003100659256000340000030800e070704601610034400010386a104200a0041440c000541c07079030301480c00241f40c514150030300111940f2800c18400800c48a00445069036010314126003502c8290410b08080701060070008200440020103c0780800d07140151555840c00701d4103408400001041240e650b04107000203860300391f80d8112444400340020118004450604010541038184003900c0d85886240e80400c021441240c100613046606106c500c0500151144510b07402c8125004113699400e1032000500303c14403400410407c2ea030030015a0000e101ba0750081c0000108190940c40b203820420040b8000c604007a01840b0820505060300d1040328094010f04011411300b422598545000d03c440c40580500140440800d1f0b41e02100c030f02c2100140c0c000300c1d00d41000140289003500c000d040d260304240030420310954545c41812501200400d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 64911954 1250 64910704 64910711
    0xc090527100315091106030a020c0d2102090a03170408012016060b1905030613050d050d0b09070c15091502070302010b1c05070b0309060103150e0d0e0a080a15 70
    0x403403170451070f40d20b24264120342c4a64040b00f00b14001ca0f1540060018203004000c6e42c0c450548501e0a035104400c1e1984c60715000e072901c60426596405902429030818001c2c0920f458a81c0d03610340401040740259108051400006c003030101700d00902984803952049080030f400381d250f480c0c611203203008003591110000700b03900c2d848081c403566170040c1085410042c1001801210b4844140750b1402520502e8003a004460005007a0380c00004055103254100020b4090344500c2a8219610361106030ba00154039503480050b411502c0304103102d846400c441c0c83e01004c440311428800b051880811004034400e042a40c150005038841345010481d20b14410090380b5184949026805030800d409229046140e0020407207405015054814601b8050b4054650564690010361818031044403900300d154840380040000400710b0070124560002400002a6142403800c1c0300d0401441d403401d00300040061100740c08510317010304441c00401c87c8000038141c5d0f019a542d92140e00581d5900f1100c090f40c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 64913204 1250 64911954 64911971
    0x115020304030f0f0b0a0b18090307110d170a081f03080f0c15010302010e03030414060d1b0806010e0301090201021e07050d0609031d0d060c090527100315 68
    0x21340303c806000355139000d20000c540c1c1c684103010070000c141d0128100d200340b42c2c034440740e61078581084c0d41d5400f42c076201e0301851900780310751648003801c00410350351381c0c02401c40102080031402400001802c1d900c132000c6640c4d82d1000e42d800a04145010307000800000300e00b171039040341c20304a01e0594122544040d1003a15a4581c0c490822030703026608003042c0a020740c0c1c035100300d00101c0031a400d050706d100740c0390314490007078070414981c0d07900075406100014035491807a03a41e54501607021b00300300c986a50000c5003961464014800c1401386042c1040464460803c1c004550382060840f00303080400c0d00200112945070700000d44d80e91142104410a100514200242c2c1d030051046002a190280113140448540e03d0180020215504c0c19800030702460041c60200d030340c04001581000e8010081d20b080440758940750000c203c80001e030b00a001010030001840c0d10340003100400b603a0180c8030031300030035088182d01c514034034010200410300d40c4940041c40098000030580440e481b0761780000a6000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 64914454 1250 64913204 64913213
    0x60403080703020c0d180f230303071a04050c10020c12150f04031202070804050f0a0905090307020901080c030304180e060a0501140405041502071109090f060115020304030f 76
    0x4244022181103015244900c03d07407941020005242c4903000c6c1b80102d0362903443c1c00c01c1c20f030500540150542c07401e20120460f00d203051048103e0650900806070b91400c0d000c0e5484000444101c0b01801c1d001c0490700400050101c1445120201141601c4610118602c2e40000707486002000f24680f2900140c8054424110108a950b030040ca202c0e01213000f43c2062642c801c40d0800071074040b80010046100c2505031952402556240c40e4007002540c202418441003080c080012030725590000c21009001075040224082d01d80500045005150b40d40141d0045c011a400140c110b020300f0740c0081580c600c2510004200c8049405040c0307800307483d090210000b40075014220a8440500c1410700348042c008041d403241c0c0c100d58000c0801080080108288025540211800303410781d101c282488102559035001882d40c284101240e1159500e150000b81c011502070b00c000c003032907110900220755080c081113800e000d0002c9035001c42c562405850001d60701d104501000700007500d005454130801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 64915704 1250 64914454 64914457
    0x5011803020301020408010e0d0509060405010813050105040804090e0123040c080d03020a030605040b0109030b0603010e0703050c0102060106020a080703180909110405131509021203120109050c0c06040308070302 93
    0x19035004001359600e07640c0300745060281c80400c00d011114003500d2021071a06000300110707510500090081c50a01e0f2a0000646840200074285003e031260964540002038081c407950340324a214841d8a80c4442c02c2c861407008035044001040c0b1560b2501524080c1070b24015032001a030314035080c0840c459680e038a17001422030140d40c4030160030304c03917540d259407010381640141c114043c00b55020003000d59540c0410064130003440d0114041850380f41c090000c0b0b00031140d2039501040140c000324880d010310500a140c885c01da802598550080468651150790600903903005160f44e1008208000950f1907030305c864441c40b03100506003c04600031004d08210a6950350092221100400c600c4006082080a1000305c440c3c0750721132840e11001540b0407861081503050250880c80030321401c40e040c0d141400400403540c2c1039900c50458408404540d50410007020060103041018089524110351441503c3c0090582010583d052107100502c81000841660041e01881c0c4803205880310031080c0c009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 64916954 1250 64915704 64915709
    0x213031506050a030b06031e01050f0f01030305090112110a090e0112020303040e060310061502070f0f14040e03030c040312030501060824090907030b0105030c06271e01120c0207050118 81
    0x2140c103d1407040c407504ad400588100703502d0300c0c08442591503025040d06000b007404002e000c1082400044940d511a10305920304031800ca0000640000283d01c8036100c2d005030000d800002c444003424803444411440d41030042000115040b010401ea074002520b034007590282c41010074100000a00541d0300701310160030b4043c00350f810854030b504c4040c0e01303074001c0464418801500c14428000750200065500c00211103d056100b0001c60522000c40d44c05142010001c0c0d009440d400e1102d10312005000a60141c00c960b28120740c0c0c2d51a40c58510f01c584403010075402851b00e0310004001c5142c11900940d8861f0920a44900682c400b8400f1040300e040c108903290403060301020001d001e90001a00420359009008610b640d80c0d8034800c0542c0d43e00824602500b000c4140035039030a400c00e24200e00050805400301d5008a081e03070000c111300f0039a00c030140003c420010700a0300d440d6000071030404288080d80060100c6801340f031020359981c0d0345102d000d041109600d18a0002055542c3e000c01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 64918204 1250 64916954 64916983
    0x11070201050f1903020406030c0c0203060711010212090105040201170f190923150c1b07080a051509010b091803040e0408030103060b1215070507060213031506050a030b0603 76
    0x801d518000f0004000390424003807071000c240741480f440c0f9800d0280f4a40d4030302581c024000c02542c1d96540040314001c1c10801100e4080d902840710b10b441d410104a21031052016400008180c40c150000618104907404481a0000d100c81408240c074000c0030143d0380280300d1201c0000d412050300401d0001d00040c40c01a1056008824004030140c841c0c002c217400c0306c511030032580c0c0c1c210310150041384400160342547c03294104001d907015241071085801e03d6082484252400d00d5030b55286541000920601103450b0340141d1105401c110342c108106803c4200003000304600505a40458512507014001d0b49040d003000c0f00380300c041c3d942041206c01030304030f11945140c00e003400d1822001d00d802c01c1c00308491060500d908005141803070481e41c1e200010300e400070080300c04400301c42130090070060310401c00c0041c10005400481d0740c5000a1904503040c01d0140040340c40e6041c188040e2000000c491003850078a03008100980c0d40e050076105903a00420b1207609601d40c01c0009241c000031201003030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 64919454 1250 64918204 64918237
    0x3140702120a0506070905032a010e09010605030417030c07200409030e0f03210904110a020d0201151511250314012c070519090f11070201050f 63
    0x30060080340141c0505d8490b00d500e28882d440d1002c2584400000301001d82454112140301c401c1d8103004c1c05007042c80810306110059200400110742c240307600760400b0300414000028007081003070703007002c01c000c2420b40107095003141404808454a8425031a0203401d26101c02c1080c1043c4082d240941d5132010001c0003009054402d19003e40303142d141124180c410106448001564100403410280c151104440510480a8889000c0c8640c110b0700641d43c201da916008000303008a00c00051460495640040c454401245002030a403180201d030a40302031a40300e41080500701d0740c8001104841030b81019808020041c070f00d549010347d0039400d103007510f040ca8421780c90a219040c4540689005601c940c0100307030400101c40c241d641c442443c03403101c0401510100c0c04000803602120100040303060700d00860780c8100088041c180c8026140000300d401030304000180e118030498411040703120040c011001042400c5c40c650041d2000a414000001110a120080101140c0002c0805948e51 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 64920704 1250 64919454 64919473
    0x609120105010807030c0f0501270503100e0d0906020c0409030509031b10020105010b07080703020c030a03080a06080a0f1113020403052419110c0105040b04020102070b070314070212 80
    0xc50350b800e054801031b9688190f00c9000b00d842e501c00768000c0300369001a1074038404007010030020b0100c55040800b902c54450031040103d20703541c0c113009202060b07000000c0410030001c4007000c1400d201e41800d42c0001d00211500400c0b80c4c2e80c005c5117014159004680015a1000c0d5080688541c0304526606030300d409082e68408156050580c0135440c550141c0741802c01d059140320580c01c030340013800b445105540500030310300001c601e2001055182d220388103454440c000003000c28541f48000d07100b140031602c140100321007108184908401414403000070200d2046903101c180c000620000007a01100f60f1000c0801c0380d460394041c0d886554aa130104558803540c034141247c40d40007003003a0000b04003d07000d94000d1016102540c500400d02c103c180c421100100328100000c0c50001105a8100410300007000380d06428071034140310324050f1061443d04d01c1d092000908290542d00605181e05040c0504800300e03500c0545240b9410310702030b040e503981c0c040d0f0001030f00701840701002110707900c10241392 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 64921954 1250 64920704 64920719
    0x80a0b0d0f03030c181806120b0103050c030c010e0402090d020d0b1f0605180406050a080a062307030c02030d09030f020d1d01120902090c070512070b0402060912010501 74
    0x30703011414000d982c2040303943c40440c0d0880d50546401480d880c1c5800640040c088081a2072010b00d901e1964a4006205551004031180d82207404005940b0405100010410700c041800480c0e050002140540700c0702c10000c00280c60025007a5525000b41da011804a10070f84443c00c0021000d80c00511900440920340341a4580300f030b00700c54804011800d072142d48810205002040d00f030f90000e4684030b00741340314102c00711543c0c600c150356103a000d5210b640010310364580410000181141401402c84004141040c03404d6a0202c0d192028200144191989084240713070301c07541106503441d0118040d04c809a00301c1c41c5020b0b46c0c2c80000c0075860009410200364001815801008082d02503036004020b42c1c0c820343d50719009420440e0484a0344150400c907610401c0b11010031020020009090341c0c030303900400c155610071030b0031200c00f803000906003040c0203041242800307204030401c2c2540b6003030b071540e05d111100c0700241000740900b001203180c0d20190348251074402007a214200070011503a48004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 64923204 1250 64921954 64921973
    0xa0203060f040606050406031127010b090114030105011b0501090b10060305090a0201051b0a0602070b01031e0c0b0307020a150b150f030f1008070602011a0301050f040201080a0b0d 79
    0x4040f900145001000a01c070700701401030000b03d0743c000f854184400140024040c442c0e68040040401c1e0380c4a0252295051500006a02804420039850340782c0001c2c0c0c001510500582072038284041050004118580e84441034419403801500307e01d4030b07100d40303181081c09420560001041d562110040040c441c5210f10110308440d0281c2d001c0c06551181805c00e91100440c0b440070380050010000d031100b001d0f080d0050041e25003d8421102d004002d52509001c98000135000c40d800c51900300100305002c0b1145013400c259070385807001581c0381116541c0c000009043c1c03140c0c1d1100a000320000700300f0350003032102024160b0082040050070303002c80d20751402080c803c0d10791031107201408540c0800070030300825035003003c040b070008a10390b4860b180e410301c207900c0084ca12900100380329000b00e5080c000f440700c1c030000c0c101900081b8a465425440825001e000c139061070003685001d0400182203020000240c000b50207082c101c01c6502c0b82005500038001c6009020740141e01001e01408001607480e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 64924454 1250 64923204 64923211
    0x303051501030c020a2303030109020a082805040249150e0708030a02030903011a031c090b07030e04050f0403090e0a0207060501270b1003020304050a0203060f 70
    0x40c0080040c000300401074088403403004601c00145c1c4031300d41301c5000400282501030003030401c0d036220316001c440100503403440e402600f2a410003600032400c241000c0d00101001c1d04040711112034641c9544070f45000b45600030112400340016141d4010034295103030b02d101c0c1c5440d02e101903800c44a8102c082000790100c100200302c036803a24001410400c600724060220820168090b10714440200d04921340405001400c120707107114010601c00103000c2504000400410145801440c0c40b420b000d0101400c48269002c8605076446250445145540c00b00311001d00c0c034112030381128945650b200884500b01c02e500a001d08000003c3d4100034560403165001c140c51003150207101c1c95a54141c070003066001510000d010407610b020900c5001030040c0d16070f41c4500074034001810641c15480d42c60581d0400c0c0d101449046a030030840307181140e00d83c0b00c00e81100035803200380500b0089101184444400040741c0c0c0425502002003010414240440011507800404541c40c6041210300c100c2000b0701503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 64925704 1250 64924454 64924471
    0xe1509010b16080306060d0203130314040b0f0a020705281409010605181e2805060c010608030d0506180106090b070807050703080c010c05090d020f03100603030305 72
    0x1000280808605040b103101e09562507180002d50080d41d11050b25070400b40400e035000009003e016a10802031018506c070702c900800d8500940c0c1503090180c400c00c6118a002c03002e100421040c46900701d01030803500b1960380c484038603a4034000c1d5442203040a84c4c540046600070300755044c001a5001c0c0c00803040c850325211407401141940c0700c0c848102e144200c00e115800c0b2882d00d004201d82c5024601806101910b4507225003004a460006580d40c001c00141444a400001150805040c892714000000080e129810160f25500038100d91603002840340742e104860018148210304e90a400070300080580d1405ca03608c81c42d0241856020f000100c1d40c0da80141035a035000c1a50500c4095403a0494084c0c0d00c60007100c905094903090694040103080d40d400c00d04009405c00640208900b0b00254040c40030a178450f06101420750079200c4140f150000c00109000c61b0555075125400ccc00f030415030440310007000c0604640428103208010503c034800070700d0040000b0500d0b0305500081e2081203003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 64926954 1250 64925704 64925719
    0x9230c0901050f010c08040b0301080a0b0906070c060513060207060204061b0b04020103020a0c020603070305070315050a121a150406091404020108100b0703020a02130e0a0b0406060e15 81
    0x4006002419100b4400d5650106000c040b481c1ca95024585031040c550150040301d00c2c7c6a1240b280b241160b10a0344000801e43c0a03030010428086240403042c0c00000c2d0b80058010790a1100005102002181002d00459500c101180d02e0304416181da0300050b40c0810706544511031410202c00a411911611002c0303000042d6280d01e020901c21050801c0c1c1c0d10410390351142d191034004500039003241540c441400b0b4210004401340c0e4900001e1845a0a541e0b804511792070811802016186130041803411b2600d00c1d1024070940c1d440d92a0481510170139010000d055400d810304c0e1240300305009086000e0a098000e21a401404810700010350300c0c250750a11000d69900d1018040f81c401000e092151801307680868019031040004540180c2c01c1500161b8198550074060480d500014080b0b02503404070b424101182041d10066400044515080025000e00400766403580c1c1881c5008100300103100016003000440d41c000030107090082c441200e18903001d214005031a181030b1920b03218491 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 64928060 1106 64926954 64926973
    0x50f16050619020c03040302010e041d060702071a03010b090a050604120c091a1003061d0702061008070b0705010902030d030b090108010506010507150923 68
    0x58005024507040040c00c0c41c2e55507180b0011a0990340c014880d02c007842c0404003d07201100e80a007020701d048900d140c005002080f910207003003010b04114150441a11000464038451403540c2c084401543d25041141141c0004602c43d9104040420052290790f002c0d4001d4041004040c00b10581341d92114000303903450f0130039001902098481c42280703007413149440c01d20006040c1140100001d5040706058140043d442c0e001c0350203001e064108031203080c4258030840003490401a002c40c1c000c3c0564803c10b6510742514050014880c140110321150103401d10981140c15010040008030714003100c1c200300f5045420169103d55a4422980241e2400d2040d01d030700c407140781e6002030074103441001c001d514807046c1c2080d089a85014104182c41c0d03045011940e10640080102d00f03840e01101c1c0c00c0001d84003c2c42c0080c140001e2103070006017041d5181c01044000940d1094840204 = true := by decide +kernel

theorem cover : BRFrame.Cov 64748204 64928060 := by
  have h0 := BRFrame.cov_init 64748204
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64748204 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 64748204 ≤ n) (h2 : n < 64928060) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
