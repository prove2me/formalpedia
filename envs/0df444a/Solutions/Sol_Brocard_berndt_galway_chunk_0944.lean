-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0944
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:19:38.186431+00:00
-- url     : https://prove2.me/submissions/478ce84c-7c3c-4428-9b8f-f0dee5366bde

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 169604316 ≤ n < 169784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 169605566 1250 169604316 169604321
    0x1a01140c070612060f0305030c060f0609010329090703060e060f040807060b06030c0a020c0f0a050607080408010603030c0507060513120609060f0209180402090a0b060706020403050304052d04 84
    0x90381c00f5501d501e544001810310480b0101c0c0f4040c600c10000b86440da0901080d051404000030403524020155000740040c5440d5008154152604040010010848003c964000a880e80c4000b0b0060705801c2c10030207100000301d0114192841041c051024a200400840e520b400a5941d02082003541000c100016035400c0145113480c0700308804610040e02e04001002c54004071131a24940c1c1c030005492039400c1d8140201c485d62002160003803c80b1f080c1101040c1e598a2a0107014016000040c1110a100e007000a840041a070003000340811a103910b8000d100d001c0300d1104a41c00d104403103002c40c1490040b4190f9054460421554011303519003086000070500e0100d013503c2075540c403818400803903014050521040d030560405a503c01c460003d0102120303503d4014841328140310207200c0160340d40d810090f001100c004002c0b0310248035200048661260f014010110351000a0002c200700000c4040d000302c800440d00321151810510501541500040340103820404a43c3d0003046440c095 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 169606816 1250 169605566 169605587
    0x1403011508070903050607050711030316020f0d021c06290d080706020a111c020c040902030c030a060f060b0304031b0c0911070b07030e0d08090c041a01140c0706 71
    0xf40307450103140e9900d40740d0034103210b401e581c1c1d040080c03000140e003024440743d8603480804a80940095251880c8040e03c1080c0f50900c2030020f1250742100e10b2810599511b0301003411064009045400c0c03d0350050840c001c9000c03c0300c041790300c6030401456002143d40c6030083c20b171814640d50031a0710700400d1000c21041510340c480407100300c0746c284004c0d404141144040c013101d008944564a581c84c0c1c01140784d182815075007540c418041c2031109c0c04402c5501092a0000003415280480c0104040c80081e0502104000b007a4240c03141c0e04060301409900d0b000b010082e000d034002080001d4446ea000c00f0f03140b000300c4024000c80c180c1c18040724540d0304080c9080c5400d000c0c0b040c0450003610b81a60301c0c00d50f003104003002e50250700811b00b1780c20321003002c020980001c1c0e142410001280440b444644411001c8801428003040c0d200082405005000c1e019215030000e00400c10302c00c0000202010a1079508118001503503860a031040c50109402c4603083c180341c40007072422902c0e01070103c6110500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 169608066 1250 169606816 169606831
    0x308070201090c0905040c0e0c0d09020f1005070318150503040c05150c010b03150f18010c1d01020604200d020604030302070e070305010506070809040209090106030c1403011508 78
    0xb03400c44400841c51184580d4058106654042036600309420306008150064100d140d281c1c82d00350034819101900802c55000c5958080081001820b5000282084080030308054220f91004184449203502c14018640940f09456904882c140004809803030813440c09a8200d41e201401d80c02e5065028002450380588a03030f582d80a140c0d1500702107052180c071500f20303154402000c80c200c0704c904002c2c020801c0c40d0303200350024120154100803054844d44c1c05440098148940720100386207181c01042c66102200b030100070310542d0100e940040c00c00105d10090350312510040c88400d52984045401d80c0119080059450000d4415a0503000b030702601c00030b25032145c010201d280060b122440504021b60294010380510791030304401d0807009034020011400c040c42d02e00140903641d240c50903100c01940004409072243e02e16808038000b80714101140780e0019048000083d02c50703041c1c110b401c0030316007642d501c160201d8001d14210180020f0141c03441d80c1e030200e541903020720311030045264410f50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 169609316 1250 169608066 169608071
    0x7050303300405030a0c0821010512030306030303043909050106030c021002090f03061906060f09030308060402040506070f050706020f1005040c0f081b0a030f0204050a0e030a030603110603060d0308070201 90
    0x108c0031640340091100300100c19071034007408010052840d09038421292800e10350083c502e0f41ca80800000d40b40e100081004100480c40181041c21400c4404108d5803250a1202d01d004001007017440403207284c0a20481d0006810100041001072081c062903c03107050036001005141104001c00c03001e500904038070b941125110240514a41d0f04214050003406070403036000c01403442505580a483d401d030000800e1000710300c049150154007a100b5022070380c051810790101c1e180d42c00000d001e8070031503000650229012a8400c14080c0d04413000c01000c2c0714070121906140c0d0350341c041e62901c04140901030309130081c01e100c0301d0143c455040240d00030b10403490f0b200c03e99240d46040841c0f6140743c020420540c805030441126401c03105028144c0307081141d100044c0c91131070341c60180c1c641c0f00000090241d40c4035404541d1401c0c554001072150031120055a071615199040140240242c0c402500c4205013000d1090040c1016030440c0e0140c0c102510070001c1c0070950720b040c0d83c4007501030a400119907 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 169610566 1250 169609316 169609327
    0x2031b04060c02040f1811031b0604032603090f01050a0b0a1a0d0c020715050301030b0a0c0e0303160b0105090408120c09060d0506090a060b0d0c0207050303300405030a0c08 76
    0x146d4540c0302010710311981c0e40c40e2a07a1030101c140752500210b40a420101400c943d501003060340d8860603541142d910607000601c140c80708005181e9403201400d100c01003140030090001c8614041280c140810004008010030b40e42d560960302620107681b00c00343c000800070424402c1103050014501c81c07807100e00403d4a804003000e52101104c207840c2001005030030611040c04140b84828142510041c1c0d8032b4a6401d43d4110b81301c1a90032030002c1c0ca0281e84039901c860260509002d0700348011490300040c1581e88031214500c0c41c46091080200c01c0b1102e010b2000003140714a03000f92403d01464020001a003856490000d006000101030480e907001c1e070050000340d8043e9240c00050001c459415000300c0e03a0709242d0180034a0010240202c007001e07080c00c009201d002c2042094402001e036807400841d0f00407180800780c6c2020410b8118035014000081c401c806c0d05410075200040580007040e440200c0030455619041c940140c50041464000b0440c0c0100144107486148440f40203030f00d01450701 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 169611816 1250 169610566 169610591
    0x6050702150a03060e09010605130b010216061206060206150105032e030b0a0e0c0405060a090609050603061e010e06040e010e0601151b0f03020102070b090102031b04060c02040f 78
    0x42d0802561000029250380e018130a40c2c2d031412140b40c000da1800004e000f064204800151424605026210034640d10041c0b241c007603100f0011036954080a02c041c00100e510b56070003d1404442e42030000d40181417800000d002480004c1c9e030b0b4800c034205a41105d9042c00d81c001122594405058410100076510000c0d000c040f100040c0d08042d21006400341c0c69628600e0703c6400910024401003140d40f600545a4917a20041010b0214210440d400070700d950700d410000c0d04008907608100e8007207140440104040d08158416401a08200d01303e4040e540c4400d0001c503200411074012507038207041001004601440301403150400c000500c0403840014400310282121030303107005400c1c1503220600401189002044110a541007460300c000718100760414516808000400140003880c540408001d0500c00e50585180756803008080d0760340d08081ea640c2d4080d40065070481311404a032410b0010700030103102114216401030302e403003008000075000c11000b428903c1c0e6109000d901c550044010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 169613066 1250 169611816 169611859
    0x4060e150c0a200a06051513110418020315091603020c070b0a0e0108010b090a1202030c28050d03170402180703020414040e0c060d1b050301060f0e0a06050702 70
    0x4070500a0000c29802d41300d4100345003a04d1000e0410102e0000308907040e481034036016800c014a03031680c01d01040890240400510500c00c940c0700381106024805c001481c03182580046004400c598000c030000c0d40c45130100040068243d50252015041507902c92580780650090140041c1440541c0c0b11195900023282e825480305403000000b50100280c41d44541c1c2180e032060140c490b2011190401c2645000300340300190350b0003400b990365420b284504c210f40d404c000501070340d00050f0003403402c4030b029051540d03c0e424001701c00d0000c0510700c0300070940d8200800001600c5030569030300c0f15403548482400402d1000600140c0e0070565003003010b1410300c000705041e809940d0b1b5540050769240340c2003034079401c00f80640501d4812401e00c00c0e01d0a958600003034041d044201203034000d07a01e1040d602480010001009102100e1038a0b02100c1c0d071194000d00558100c840d10b40b204213904008002c2144c02d468840b0401d0742c84810240240086445140500b00644c800382c002041c00c1061a0300c00007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 169614316 1250 169613066 169613117
    0x3040201081324050f01030c05040b0301020403020a0e0f0903390d080a150f090209010c050a0302030a11160b0d110c0309150a0c02060304020f06070b04060e150c0a 72
    0x3e4040d04042c05008040651141940c000d052010f416030700e50650340d510030502c0c00342c404d0030700c83c0740c4981d409602c0e0f59081d030417600115801030010f020326503282e007800140c0000315800d240c19a00d0f1400142152000300444007120106c03002040c9198030380c81e030060610380e0302038261400240d003141200100030030021001c0c288850b840d04072052900c0390140040d5070701c11803007035010030b40311004002c000b51511003039068656803c00982c45101c02c20041380c1d5078a8030480540315101f4051845c050680110003400c0c1c509150b80d0f4480100c840507101591440400501025a0404001003000b071003040090b040c00d24007400085050b900c103031b012521580004855005541001a680b109880d201c00030b407072000790024442c1d09240101002418a421000000e4000e4070000009011542c61007610704050100801c065160342250814040c84c04003105d00303c480b03601d05402d851442c8800644510500200c42940180759154062080303681c10400d0f04a0900001c3e1007550380f0203004409045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 169615566 1250 169614316 169614353
    0x80f0909130506090304061d061917150f010f020309030106060207151701061b0b0106020303040b0c0306030304053307171305060912121c060803030402010813 70
    0x31404050741c10424207041001e00a401c1c01e6108100411085e60001d03403185511462050600c407080101c0040f0b072151050420442c1003c05514440040301e800c44001040701c2c503c227041310403039515100064203002040051507031040d00328200c50990340c070403a08c0200d49d54492041d6030400c0703c2000030900b51603003600400056009128103000c619203681100e641000b451401d0300542110288594064006008800400030410246401f15452880040301240d205075000038a603512031000351a60030555003142c068115070003049001102e0001d80f0701959000380510315143ca400100072a03400202445900038900510214032100d1172181000f91404841485548420a140c00030307100c11034001118107641c050007412400c00e6880d101509036042a180c103640d50340d40702e001415912582ca2800b0062040724145a4943c0c1d26401804c0003021200d04030450b40c041d03103c000152280e034003032074910f644207000080156110310221604043d02c03003000083d02c1c07401d884002c41401d0302043c55 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 169616816 1250 169615566 169615591
    0x121005090307140105070e0d0311121213050304050f0a0b07050d1206080c01110a050706030b180105030303040b0c0403080720040516030e07050a090b031603030c080f0909 75
    0x51089030401c00500001c01da008102e6440c1801d4061f05522600414600802050f2010810140900007140a103822001250401101c0f84120840399012403c020740c0c132020762021680342c90901c204943c884c0d6010300030f036003880c2c201400d003d14058500289a400f04403e140000c0700860072006012890107440075080d01d45ea01c04020b0407aa00d50440740300383c40c2c5424010415400e010840c0c20113580300346840e40c0b92605c0c80c00154602070741801c000e4440c1c0508003001030040c1d0561311040e4440016100c0000d400d000c80d402c0484400248902a0560001c100141c0082c2180b41c0c0140c0c40a0094200b034101a07da44408446401c0b0f820b0448900e0901c02c02e00b9004000710a0641345041e084a040c04035160001e00740540c0d10040300d120042c19207807070307001e440d4900c02e03c40030002c1c11014001201503a91007101e00050191303004102d0082c011104240301007510b070103c80042d6a007588038558440d407507a86091041e400124081902402885090798503030f40c0c054000e0141041c0340e0701 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 169618066 1250 169616816 169616827
    0x201020d06080d171e060d08030f01030b0703022106060c06101d070c03121b020309040501152703080a03020d061512020309010b060f0d0b0d111210050903 68
    0x180510325a8075030550850541d43c01c10240d0700078950101d164445d0020140300948640f000b0603030303000000c80000c00010f008010800081d00d480381243c12240210017507012515624006c2d0124442c01c09a000010258021001c040c0c140c3e011590b0048806405c142ca041150317148241010001d485807011100544001c01202e000180724600c2030803141201c801030b092100000c1d1003041c02150040521051918013001c240069022980000300b0f140d542482d10048480291240e0100158138440c074074081c00880d04031124050444041060717200c01861814402d001c1141845030b94210364510f030700b1b01000c0002400400500002400e680f005621012800d40000944103030740c000c04520940001400c1c09a036019000d89101840004010703134a486013403400f40504680104107811000002c1c00300c0d821b0441c80005d00482c1c2d034550041005405c24003c011159546402c081e201d0311504145294a15000e001111440722010407070b4002c151051055066441c101c410040d00d4101280 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 169619316 1250 169618066 169618093
    0xc08070603060b040e0a1e06030303150f1205010207120c050c030c010806040908160b10060f050d1d0a05071406040b0403080705030708030f040320070905070201020d0608 75
    0x4801409990400740142c60410720607200c0c41c0198441c1194184250000c40c02004041e88001900709020207410525100b2000d140050000c900c82200002c0c03402442c240f285207040007180076030382111300031405c0c41c5c0340680540c400080c1c3d007007c0e41c030740d5401c20400002483d0405074428000c05070312111100101d6060103810b00002c400034038060b401100c040c07101d40ea40809841c1d800310044a00041110792820881a10700034500c29814020384a6a0351050254180075207100751605548030b8010740c2c481004507048120811400003150081c031090040300c0c002d8112085600002d1941c10851900e1840d82d4a00703050040e058520b45c105540511032101040740c007402420080e03465030300d028030301081540306104600c005081c00c038000c614030702004802c0c02158642c40e040460543c4a0030440000030b103140d1305a50880201c0e900d00e00585c0e040f40074502d02030784064104090031a0519012210028180040c80041155070030444c60345410f0642c810b00026200031401041c000001c3d80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 169620566 1250 169619316 169619323
    0x608060106090b03090d051b0105010306240308070201032a0906030c14070f0303060506310513091106040815060a05100f05042105010605190501110a0209040c08 71
    0x41010000700420010080d85d03120000d40c440c9500440c0c5041552034404000b503c00c40c107004140c034900742d42028000418425140c20000895484101c3d19440c28010408419010194071000b02030b054103219110242d03000390301a14030ac0c0c500b010f100c00300200201c15501d84000344500c5001103101c03483c0910082c0e0f41881400d101801c1410072900421180b003113602a4060808010f05002c010300b8880b04140c4250418001440d01814035511030101c007508000790524210341d601e411440c00d4a1010403a00040d00500301c4101408100c5440080070680000c0c09a40c4010344074901c0d00139071089a0340f01d0400410007030400740c025058100500501810b043c502030030b410311849268405105c02e90301c8080b0111604500d0400500300179583c0010b450f60f02a940c080c02c081e048807150412401e5a11843d40f45031032241000f000102c0e0fe94040140800c01c00c440c54400b080700000502865004110036800380c0d01540464441e02d6880d40010041601101e08807100c4e60a4581002051400c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 169621816 1250 169620566 169620569
    0x8130f08031504180b130501060b041701091e0507050621010e090d0c030e1005040501020f06040c050d05151e01080703030210021602040c02030c0c040219031e060806010609 76
    0x1118203001c2800300d1032112804d4010102c002e00700c00300c4040458512441600c07004a0700e981300c0004e001403543c403001c12006402520810b072340c2024450300004031031418800c00c60410303401800ca8002c4101d0100020801e4606001220341e8840d100c40400c503a070355400905030a0341040c244207801220511040912a01030f1710610000c0d10f100e09111911801080b030351291000c034500742034280e007281000c88020ba00d8600890308130754020084400503601000510595000703070210b9800303520540b203440c0d03030f180e080310b015200c038086a23018005464903960080245009d1001c5949095400603001030024084e200054801c5500b071008958400d030110f09401400c90f0400b070940c8526544001c3d403100000c034048088164001550507440da8000302c1d0030f420035000b5100b0400d9100441c0e01942d20f03480149541c04510545250349000d14250080300c6041584080b25014802031600c00d80240040c03811000b01000130b049040e0310141c1d02c0c03040000030300d00e85004001552400b017001e498190345 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 169623066 1250 169621816 169621819
    0xf1a0a05070c03240e0303070302070503070f0c0306062301030b030309030106121703090a060b041b020d02010501050a06120e01020f0c07090b0409080304022806020309090a02090a030308130f080315 87
    0x1068170802084401006999110610f0700b40540d40c0c891902e0102e09522030440018440c40b02d82e0001e9042c04001e0300b6850560f48615801c0054545401d2801605c1d8207801024039044c1004001301440e503c25000044010800740482e410480540000b03401c1d150150018100c040040720f00d60148003085142c80090380b40320300d14034030b9400c107a0841a20b075522090040e20311610350200340100e40740da601031030340d120500c00c1e40c4031240300c0303000003d440b0000036859030015800c190000c155468480c5103441160302c25159124030070300414848003c2c24416a0000e01c65501384000c0009000803001050344110740009401d40e942003640c1c98040302c0d4000a2140a40d14000014001400300c904172500a6011291088081400c5c0300d00c0403171495002c0c244080c1a50844001042500000a002421811034192160f86d45040b108001c0b4043c039106107500c446015000c201081c05004d071190011b90350f025008500d601c1b9152030118000901044800072000401c006107915005500b00e00700d0310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 169624316 1250 169623066 169623071
    0xf02060c191a1905040f0b190506030601050d0204050a0204080a0f060f020310090b040f1e050912070b070e0d0804090c030e060c0f07020918070f1a0a05070c0324 71
    0x3c00050500d0040151426000b0031a80c1c1c0c1e002c02c2c240324445038080c055590208800030356117003510714180d0340403603200e00381c1c00300b810140410040e190200303100e4140c46001c1e010044541d200e0b0200300151801400301242c80d40e00f0007001c11014802d0101c0c204180c090304bd0001101010302d8100c0403180d460b543e202510f0b1043c018011107c00c0400c0401c200c030360760000465940c0e05240054000c0c042440c401c0040344c41c00d81c0b00321481b08898082c10400c0142001042155543d03c0720355200e4046509003800301004201c81c500048404940c107070000039514200b604483c00c200800c4200700812401e03511a800441c0030030002000d8020509049040e00c1e0070701c1900110381100f59611400b03041d00c408441c010864030741240c030003800d80710446d030024500002400c2403c80054180030b4031198000711300908d00040b41c50f80700351041c14115852000c00070324081c00d848204900e03800600320354003004420414200802d130341c4425140514010098141e0320b0300d42e0b150380107800d02140c043c446520b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 169625566 1250 169624316 169624321
    0x111060108030f0c0c190f0803070807030807183f0308090114040c08010b1002060106080c09130c0201180c1404060305030c0a050c0105090d0f02060c191a 68
    0xc825103880f409809070341a120315040300c0c0b40307081c1402c50207919008945008110300c0700e0744030007140c2e04031008a0540194942c68040382030b1248a414009414040d0420a0f000040e2064034034642c4070300c41e403a111b01403502c203040f800b040212a600681c84203240c1907048510980f2040c484002c1c03e03508169024071411085801140c18550001900340650302001802912003908408001c0c0c040034000e110610b02072070308800341c60040c003844805628040000165050070062521140043d40007058242e1030140c3c21103040d00000d0044844800034000301000ba180c881c06500a602411004143c01440384c1d0020b084441c03503070401e080c6121406504011030140d00002c0240c0303040d1070b07580c80b643c07070243c0c082000b41c80c00780d1000303015100009200000c40000f02e55104042d1244c0240c54517142d114004562900600501a5002503410300ca00009180c800000e43d50b98405410242070801412a1a0500d6100b0301c800d0a450005402c2d40b0400082c0b2809043c4159039900003041c90 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 169626816 1250 169625566 169625579
    0x70309050706170423070609090b0301050c19210b10090b122205030d0b01090e0a0527071802070b01061b06111b010516050a1b030c0201110601 63
    0x40c031000c4c102a15911403d07010500501d00b030f0010340d0740030313a545c000c8403031441d90b80c2c900a2400c8090707ca464009440c110301801c40d464103006003030041d504059803900b05003d409103844604400b0540d101031040c02403041200c110b0b410141e4000081480001511400040c10300c04040c1d5450081002c002c040002880340851038800e40d00c100300320100f85922650352050202d000725101640c81241e10540102e0410031038004010300c100b840a4401707012a80024006441402c0c0d540640c00c82400340710005042c904403648120303400301c541c0704110204c028014045038521050204020b16400840c803d0000340c0501c08070001d500d100f4a411460000c541d2210f5081545c10302070f1000700081c9144d100b0054011103000240c00e900070700100880e8280c0d14012031590b00419001c0307180d968444100300c03118411302c545842600c04195850807080c0701d9000f100d096104810400c01e004580c3c400140008160340d2103a5800c0c400d4640300070707619060002501001032803403d034030300354410001440301 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 169628066 1250 169626816 169626857
    0x60b01020a030219110a0b0a0f0c02240904050115020d020c0609010f02031b0706080a150513020c0f031b030a0c0b0720060402010e0d0803040809030102070b070309050706 75
    0x10308001e00040b544c602140303801c010215849090036400084c0000104080100f00000c00c420042501c1d0742708003580210050380c0290700e03010f02035849840403000b03408501462039803001548000e00c45514000c0014005401c842003a0001d4040300c2600f0500201590100007000083d54a800240b4007445000001407488c41b40b008028104142000540d0a40340200141c0e0900380c200b02c030551850001d8400150f440c40c02c3d1081c0030015032250089a40c005a038816658103450004d808050a4105014010344106501022080703650030040404005030030302140140391019006540c2d0f85030050400b01c0b1500000c4050310365600100101d0b0003c1c1d0b041842d200480b80d22000400c52075681c00801d45420304a00120a0705522224600360380c03800228501d03100354800d80324920392008650501440c1141442c0c01045140104085008564980c028020100004002500d000091b0703443e00d0305038100f9210b000200b070b107509110701005007d10001c00548000e240645000710318144100d036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 169629316 1250 169628066 169628083
    0x60914010909080403050a05060a0c0e011d032401050405100509010905070512130308010e100e060604030215040e0604090c030305160b01080309040e01020901050304030f0e0a0e04060b01020a0302 86
    0x45030b55818200e001c201e1140c061301d00860f0054240e85090310282000d9864140450f40040320600d0151441d5200d40200602c0c041c021043e9281d1002494040076030800c1d25120141c158588500401c0c0d1494088020302c1813011041041607074840d500d09000e010540f140034041800311013880d032044c0100d03100c004c103c904480c0781c3e91000c90180c5400070161210321680c0d0046c1070035030b6681d040010811001c004403100910903a2a50003a030f81e00c240e010002402507075805003c1c100c0716000c0190801c0c64000c250404070060149103442c0c3d49a000554503061904151481c0364041400c108003d40b004005500231001d5500340002d01d2155641e000171011400014107120000c5100c001d890328102100c0f00c0c1d15030207800c94400b96103c081055680c1c02c0075920310302c01d50400001100740038041c000d03980762040684646086454070f80c1d0540700820050035840c104201076500c009142e8a0f146004000c04010350070300310310b00782400d2410945001da05103d0642d030110300c0840c002580000c0d4041f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 169630566 1250 169629316 169629329
    0xf050603250e060f0c0c040509030d0b1203070308010623041a070f060204080d03090f0305030603030f03010605030a060e072307080d050619030b1306020408030c010903020106091401 80
    0xa100c11000c1c02d50b0024092250039030041804a8414541c086400c002d1810310040022108110420740811040d180c040b118840b00350402d00c5541d10103540d03600039103005c030f10081c00f24a807400640b52581c40c5400981c2c055002031000f4004100c00d50f0088a62030011107070340ca20118043d041c0f0f480d1a0396220714803c1c070540481034a40c40164180308070603200d07800d030f2010951405114030b09010300a50801e00800c107260207a171040c107240502910481c40010340c41540c005060f002030f10305440d25000180415098041000803a0013001d5040045010b00b04e1a21215141c0c02c114614504a0b1241d07040031600318020024098440c0c0c101c02020f9081840300307000c4040c000907201080c03450203945002007182c0804541c107072101015030005807250b40140c40c200311040c035008030089101031510000d004906a200032880a4012200e100102400740c00f0151400366076050040c03541e4800200c3c0c480596481c803400342050703821f02486004240e420805e0240c5000107110114495041c030882 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 169631816 1250 169630566 169630621
    0x140703050912032209091106030604022a07051002150403051e0304020f0303190518120a140c0102030a0e031513050105010803071e0f0b09070f050603 66
    0x100700c2c0e6450854042000540b01a01d03201e566490100c4ca1082801e03400d00015003032800d0106180c0064490b01114907003000d11040c2c050399010500c00c0a82c00a01101e8201d80c0800c0709400d00d18060301c0002121034145003461074585008085d90402d440d5402507403056140328a44001140d0005507920301d02d1605400041030344540c541a1080e00c14640310310050040e850000041480c940d029500c102d00a1ba840c84080007018101501c03849505e484a048040b110344031081035100d20050540d00b492180c403001c4843c0c08800041d0000100c01d40b0902ca944142c0c030000410040559040350503003c00000c010445000300040d44a0140062001c04c000307400303210700d0042c0da0402c481b21400b044022a100581040c0c0f02c009989031090406884641c00c1c030b0000100100000304560030f4582103038120001800c1070085130020003a100301500e03d0301d074942031500403403107281e6014060f4540400814840e883c1002e55400d841466010602c522018010070030744114824030303402c0727002858800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 169633066 1250 169631816 169631827
    0x80d080601110c121e03040b221d060102010c02010c0918090b0106020f0f1506040b03011e0209010e03070806010306050415020f04210309031b050d12090614070305 72
    0x1414540745104480aa2100c0880810702542002280e00c0d40d120104038200342c05c3c400107940340c0d80d4074440d170f00c42c0d07005480b41040f00380f0071544500580b801510030b04018201540e641d2400002d41c03650310030f40c0302c2a10342d1007082c4141507809210f1044403e0b1b003230000340414000d41c80090aa03070950f01c65240c12441e0181c0710403d001441c1d00003a00b59910568900c49540c48420096035009403200600f007500c14409811180500020441c08502c10b6494030f82c640c0da60301050001406070349401d030750903640f68141101c081048241c8a498108440c0d40107842c0c00c3d0b508001050b913040314200ca4002c1d0024402880740120105032281582d4200c400464161a00d01c0c14a0b8940361036000034048910204800d0301001809000b8012100c0003036000300030006800d044080040b04000040215210800070000240c0810b00a0040d0b0405101e1002883d620008100701200d908412900c1c5400760454101558000325100042c00c04c1e4505881940c2d642c6510071303020321032981d0140500501060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 169634316 1250 169633066 169633097
    0xa0b0612190b09150a0f0f09060b0a0b1c090c081506030607030b060a0309020316120204050f160302131203030219021c0822080705010501080d080601 66
    0x1403410048403411601084203051030079241605401007251800c1c502c40106080040c00141468034100c0c0b0311082c003881d1a03511801c001045508401035a90b500c480e0340c51034904d024803078400c206005440114450750607808010420445410007801c00e02d0906c600780c03038134650404100700012209800110300c00141058944012954008021482891072070304101080d902150b0280b0401d030210780507902c4420013075041e645c0c02c03808603422860a02030301e04007520030b40021903007600140036611a0110aa088080fa0805030000380151007540c2d1440d085003064440e0a60101411240300390f1800e0444104031040d075400030860030141c000c1165400c400701d143d100e0000742806410380100201528020700a50410501541c1c10300551078601e0740c05001287c0040071810242041c1c85001d01005c0948a6000162072080d0100140b15080821013080442e044840c0c01a00f03482e841c1d006914100b800e44405070000180350b084209000360507900441e0070f0f5001002403e046081845060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 169635566 1250 169634316 169634329
    0xa0b0904151802030406110a0f080906160804031713150209062208030409050a14010305061b0d06030f0506070507030c02041802090a0c171009020a0c060c09060f110a0b06 75
    0x2c2107288185000100300c08c80540004910a40c00d6481d00c944103655a45564552203407001c4075500103494030070301c0e0b40100c1e610811055034001d100f402d11800003104042c100a101c40d00f1940c52849082062208040c04900b04508034a480c0304503066140512190100e10a8040c40e000c500360002d844005000c92071107840c11101800b0f4040c100c0780c8560340c0d802568050401910448512480e0055507450a01641044c9059941160003003065444204c62200e03101540f00d20050081014450184000058010b03280150b02031060f01c00c1c242028100320f030400344064000cd090000c100a13510010760031000201c0002c0d01128001040000b00f032010403990151070b0000e500c1041d140800c000004254000106000d50b560350008c40c004035205124903080035141d2041d200c0c000407081111081580080062401c546020307090110f0300d607101000c3d81d18021103900807855055003401190361101c5810b006000d00e1070044c01d1143d001c030420b9222150800c0c0078158480140c0004e80e01d03100c40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 169636816 1250 169635566 169635581
    0x60a0503032503110d200c0d14030c070e06120708120f121e070e03061801110301240905010c121808010501080c010e1806030a020a0b0904151802030406 67
    0x101e0940d0070002d09288011b0607501c0540803884041100f06420400c5000042c8044a290f400f52a1828480e41c545800290008550701070350244010450ba03441444c0502010004181a00007480641429402c101c031114521708200c0140c0e00a44040000010005658660b00041e501d069650006622004030300e1046004050b000044803041c030140313442c4210030781c42c0184201da0381ca02c20707201c03400202d984008504150b98140e209901154485c801c042c0007c100303070800c0c40002800c032081040c0c1070254000340e0042c6004c2c01103600d210001019410303462004643c510700800704508280003c1d02c0f201c02c65201034450405940107000541c0920710700008450446000d0109035503038070f034890281800b401031360701502403210010659405404029000781000b002d64000c04410a420900004000e04140d8035100b40000980580c480034240400340a210301e1b002d0762540760307030180002d481c80001c4261480100001c01c01c5034600504030f4208032a070100016036a42c845090000150042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 169638066 1250 169636816 169636847
    0x204030c0608070e04060807061202070b0f041406040c0b0307090801061e0b03060a0308280f030b0111030307050d02070602180307090207050c0603061c0b060a0503032503 75
    0x1030020079031076080041140701c0d46056a07070304880204201840240c440720700c210841948a02824854540035203030084007004d00072001070900c1e0036900e440d0241c3c0403c0c1c407090080d0103520140014080c010b1010400b44001c24001d02036401d240c0d44000e4642c3c00c5200d1000340c0d22010001c180324511600e61390000b000c0c0c001c020300c00765448014480100040040d08031900750388a4001501202e03042c183d911821004152112680c03545d201d00b4285d034050f00c0d10402d8142050711032690750390603d68185011445550340c078136241c5100400b5049404010615040c408140c4e85200141000421268440b50f40d00d09180c403040c40c0c11220019018103500140047e00224420782110107041d00c3c0700c002c101c01c408450180b940c0340c2d0b40d9030417440740031700251413030700035079500140c5060100045400510150001c1c2c1107500c14040342e8603103400d502d01144e80a05000521515240406044026040c100d019500d00080014462881364180d80d40308520600c131244c2c0e009160040f098003010210 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 169639316 1250 169638066 169638083
    0x50312061206041110110d2607031e050421090e0a092d021c02061303030e01030b01080610020715050d1d030d0504140102070507030b090a03090308090301020403 71
    0x5241c50001d2007080c0300364041c1d00580341720f042c080b551071044039074070b1045080d20054501020b032100101d4950068555144c0d461000385c0b41019118146d1a0031480380c03c2d5554000f5040f00700040215800c12500a0b4240341d500303010902020400407606070585041d40004030008003040c040036520360325280d210030f41540c2800c0c02c000f8a282d090300920005480b0b00340544458002e425600d45224032584001c01c290800e4104c400141000383e81c80c06210020300d071016515000b0743c000396881d0311000c041450415048410010581c0042403e004c0c40300c2400c05010443d4458002040b03514010845440764500c10b4110031400c2c02405100041e0002d5041c402520400701c030702800a030f0044502c256560720304101d03806d05440a4105034000103100010314509006801054007400010313006640e11409540701d00c0e1050004d100402e01907118030041e0441a107581004058020006c0811213035800070040c1d440020303407116184060700e0340401d440340c4581d2003c0110b8028001e0382c1000b007207910b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 169640566 1250 169639316 169639321
    0x180d05030907080604050a030c210201020a02010506100e040b04020702030d0924080103080309070f180f090c03080711040c03140615031506130b030402120703050312061206 76
    0x9502000452103900c0c40000c07112055070720f054042d81e5540440303000d001d0390006903c550000381300320074420455004a0760802e410900100802d070301440c1d820fa41c0c3c0542c1d030029030074159a0302030184a603c40400c5407011604c8004000241c207100c5200040b901c00c582d01c000e440400c2d6180c0e41910319158001d4212490006508000340c108400c50082030907480c504401c2880c0380000d1600c10f264080c6d1503035404016440c43e035940c042c9410190202045014800006c03841c002c000300c1751070040120320024041075002807078180440750402104425103041c01a2100840d0b10401d00c0c0003101d5100701c1e51952001c150600000740c9460210407039100d4284990515490341c0758020b0318070308201e541d98400304e4581e1805c020080b5110752803500d0340c01081c0001044014281712003880b00b01c02502c55031603c1003da80d014101d8490740c10451001401005010940c201400c18a030060003880040080c0b40c1940c0b50b10396640a11040c0c6a80807600d5800501183c55034012584c0c59100c00741120021f0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 169641816 1250 169640566 169640593
    0x605030c01050d060e0a0605120c06250506070302030a060b040305190201090911030105040b010c021e0d08030c0a020105280908041d07080601030b09060d020303120106230301031a18 80
    0x18240723441080d1140031444601e4004240200b20301e00071500040642c1c0c917100d00340140641c0048040b0344096800780691500300415401c0c85801e10800721940d005990307103003500400c0101d070120b802103407a110303050005200040c40010112901d0510009000d607040340c9200485103190550003400d0143d05103460034a01d01801c1016505a40f001c9805100c01a0b07039000445059130010006588496044030b1040d101c0c480c3d1f8542e1000d1000644040396405003911030018a0f8410303200b21500010008000503020740c2841207d42100400c080b032420000f422200ca540042c50050b1075008668490351582044545070445005103405100404400105003004000e44012180503002c40c802ca4005460b540c407d1140801c110717802007010680340ca40d1418402002d0072400200e81501c4108441006003451980c41070081c503917595241281c40541810400c541c003003228414540e50188010300004c0e150b41900300c10f03007000d07014184030f90340c0d6140d151104074408590fa190a009a803100b8089 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 169643066 1250 169641816 169641821
    0x4050909011b030902010e010c020105090906040e030715050f0c07080310030204090305030703060603051b030612010504140c01080f19201b060903040b0a030603051203190605030c01050d060e0a 85
    0x10b05e000f622461507040b0300c040190f48490a0010090000e0320400984419140004030541c01080180c07000074500e07040554185503a2100d40700360344050007115881010403183c094039074400c02c1c84d40d4440e0a82000402448a8050450010726069000c0005000040d4201d41c02c0d00941c0c00400030301c80d007481c03800c003d007941d0302c01d5402e080002e00304a00130076124041e00811f802950300c1c4030081d1040500485204c0140c1001d40007c4e88454218a00800d100302400703603e01550040358031401454113008507600d44100c0031760b00d40c18030181d0300400c1500c401e0242d0240c0d110991105505910503800c12404c0280410a540454140d20b00f0b8071072503c007840300140c030780c0e0461940071071001c10710040941e540d05001c80300300c00182e104000600040407a14050700c8401c059040104040380c483c1e9407039090101d9a00d1740310284401104001980204901c002e0100110010402010b402d203400f20781c50743c24100c9003e06010000403010b01143d2103600ca8030050101031404801c50030010481c102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 169644316 1250 169643066 169643081
    0x50d0b0d0804090b030a02010516020411030a02040509130b010603090f0212030408010e01020702060f1b0f0c090601031404021c0b010b040501020c09090729070501090b010f060504050909011b03 85
    0x12811310748800f22540e0308002504061642c1c0503100e03103042400600b2a40700741d2041541c03c90700b041c1c48111414001421001950051040550140c0c5590038081480034100005240600b10071640076054041012900610b055541614011030a8811400c00c0c1c107101e942c160000b0b401c192080c841d01c9100002102400130344860b400280000e1003640714450903030041d0701003e0740c060410881d040805140900400d0706803031616201c0030341d0041b490f0207400e10084281c9950b11350089031000c4203610b1300461075644503500f400c0070000c02e491024006400303500144000e01031a03650500441c140000300c407091103540d11412281c06903840e00da4182c0079801512840b409840ba050001280346845081103100c3c2c9401d0300103004c0c0d030b45045c6d915802803a0740a0400383c000c1c400745040480c0103008004003011401400003040407951890078221034001644062546446c03050180b0041d80d0120440702203c100322200801500e13400300307550040c040031408186101002035a090f1494140e0411007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 169645566 1250 169644316 169644329
    0x910021212071b150509030702061804060b0d020301030201090e0c070f060b0613031401020406080712091421210a0209030f0a050706020304060801091d060a090c0b07050a03050d0b0d0804 82
    0x502c1d200c1b140c0b41941c0780200d55000354460b02c1031040c0018208210395070240600024400304400e9990340018260303a0000d540120305075000001481907580020701c0b20000e2019030700300f44803854004070b005824003424100800e0742411501000a00c070780c540101c510104000c1040b992180c1d02c0b130341034200403a1440104da040080c0d03840030240300d00c18070945080301c42d00c4d110320b00e40d40e450702d1044941080045214402a41c0ca010b04070204440d0341940d185c1000d079000030200070000500541c55250320044a2403220741c104400c0440107002101001e2100280e00d442c1e15544400020700040e000ba035842c0ca4140c801d40e680711030110b2000402c605d001c1c0c0a4001c2d80c044e40c0c1c946404a881e40308034041c0030003059070540100f02002c8594402e8450105544032107114810744100241070100645403078102c103440b441c400c0700340031500f515a00140b20000e6010315228150351980d460380580003024017071240c0410000b04080d1290090940c000f070040108070420755901d0514500e402c41d00544 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 169646816 1250 169645566 169645571
    0x60503030a0504050907090b0406050a0e1219020a0e070c1203020a0903170d05011401090806010f030f02030f0f01051006030b0904120e0a09020910021212071b15 71
    0x140508000c4101c6507070380d22035030303400f0700e450b040500f48055402c020f816001001000e40000507106070141c09000070b041d02da5111a5610b5890700e009003d000912820b5100d10880040070401220009110712104c25030710340355001c02000d000040784030095509c001e807250408000c010485502c0000504010b10a80340c104d1416074400c0210101c0c01200c40140c00304030104000c1c404516040d801d1800103060a000341d14200f4441c41c51400e4a6003070380000004840800c1002c51982c0045841010349010340c0100015858440d0080c00603040303100c0a00703c55001024001551400e000c88043c0200441c111150300d882e10892034002e00007100d6006005200e00e4011078510b1280c020034040c01070040c0203050742d41740c684072100140450320026007880004e024006040c0c50311003040d40200090b540050300d0b0301841c0140441085000745101c1150882080040d5036084402501ca44107050448881560b641c41c0040e00c05c4284100d003001425819001a41040000300c0028030554007034038103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 169648066 1250 169646816 169646819
    0xd03182a060c0b0714091905090a020c03091905030609070306061211220603053003040f0201020c04020d1a1c0305090307030b0108060702060f01030c050105030604060f08030c0106 79
    0x100c03080300c0302070001000920903c004c210f4aa200e0f42d411a81d00d41804a09481c01c80e000001541100d02500d04031200c604c0e005041049180c20403159902110608055141902e4a40b45c80e480344201d280c494405c2080b84c4d020000c003422041d80c80040c0c60040d049407500e05104080d00d640d02158030040b10580d061400114205030344510780d000e200c0d40030340381ca10348940517001c012046041e0b50000c4a43d42c51540e0609040066004200085004001400b0080950300d01c1c035146c0042007454410b00c2903002500e41d100d0101c0021a41e0282d04400c542c40b00c0c400c1403004030305044641d07492036031060010850081800039170f8000074003850044188070605802500b84050b480d000c40c00c4200703086944c41c450300401d01640003408050300081c15115650380300d50b24002901001c3e00015071541c00401009012501000390582020362030481214641c955560858990068000c442c100306010001c00d242d40c541e0f410240107004221000c000a80e01d0304500b0355240c001c90680032156091000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 169649316 1250 169648066 169648079
    0x1090c030908030609040f020303043003080402100c0812070e030a02030705040207080715050403020d030603020a03020d1e030f020d03180222090602120609090d03182a 74
    0x160700e0a25809146107040d0307a56002080400d15008105407044c0c1f60910704000140e4081c8020000ba0000c610752003900d0305421a0500c000118248207806d048818001102003031700000401e41c0244c2c101c8000da112180311504031814064000c000340304d580041941660902d8100041e841043e2030794507020b0a0a03640200b55807a00760344006509600065000d000d6820709400034040103000c1d00140f03180000b156204682841c0a01c101080c90741d90b0390600007050b90603c55002210601d25081c030072141940c00091301c03075219200007480303030244500c0c400412089822090f44000c1036800440d401e0280d00b4041c06a001c86c0d10200010301070000400b6249029104410040c0d10740c1610380d014029503401d2004401c21000d407050f24501c0d01c0d00180c2c51481c240549008140f2400c0c0c09600d95400a1f91342c000f01d400502000c1c8528034002c01c1001140c0c00080240c0440c2e0355140110f01000c20068200e96984242800b62001030141c4140b50200f4240c072800150400d00d12110811507503e03003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 169650566 1250 169649316 169649321
    0x120201050c010929070e011d120304030b060d030f0e0a0e15120d02030304060b010311070309050301060f060c03080604060b04030b1e010501020a110f04050f0402030c060f0409110c03030403050301090c03 89
    0x4403601702007032082c0170b05100c9511440220301341007040f2100c0201000412300041c000560300e001003c55a0000034144100020160301035013002e800e903110800584c3e150383c041e21107118103924904102c6c649100d907010b0780e00c0249110003401c990076004124100001111382c042190920f660207041c009440300098000041d24442408190780950b0464135545d44510180c125100b10604250312442c3c10300d558224040108001c5100c0e4403071200040c680000c2c0b40c00d48200740d00c190464040c50700100581c0360002080911140d03d0f1905102c0d640c0c945000400610a03508204a80b280215010040141440b01d25018a034048000c151381c458203a02c0e100c43c440240540350045e00101030010001d03c4142184454540046c1060010840c04010400b218022a0198100340c840002d00c0b066003400d01c0764103031003001594035030319110f604040b9410f10b10952258032600c50380c8840401507049046e09841c4c09607a200c003566528101403c0050550b01b00303000d140c10442c0391042c0700050078007a2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 169651816 1250 169650566 169650571
    0x30509010e0613060507052d010b010c080702060c150c0a03050609010b04180f09030e040b0a1a0c0f012f0a1709011508010219090807120201050c010929 67
    0x1c141c40d441d03d810b01d078044030a0781140750116144d01c103081d07000e0f154080c5c0e1512200d864080191402050343e008a0b5a400c0d0380005000358103201840f00003c021031700703600840c0e0100b901616203503514148001d0651600b006406125a050781c1c4909010a140c0a1801030849041c3c1d584c0a001d0781d25031f0030800030550310a00c11040e84c0c04003007000b0000180411407194040c5940280010001d80104221056549035101100000c2c1e03d40310f8500240390178459481c00c5c4101b41c50410f0a1410030340c0007103005410a104800801000c2640ca00311101005103c00d8041c800000b441340d072290300e085240b030380525440b5109001d4126000c81c80449150196080c404660f590b6603d0800802880941c1d9000a0594183ca54a59111082d96010090a4001844464001079684d0041070380b800300641a444498100000f079401040030a10008101d4242c0345801074a0845807042d200581d264411030006808650030651502d00b1710013248070b0021940d401d10a610101c48000e240015101000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 169653066 1250 169651816 169651837
    0x7021201330b030109110d05090a03090602160605360306091203070507020418120e0d02012106050a1203020c010f0804060b03030c0a0605180106030804032d030509010e06 75
    0x81c0010817280b1010b070012515035142ca13070f18915008448100d8401c0d50411908039810750310280310001056400710501b00204080e1024204a90307125296034140200c0303208440030040042401004200c1480700c0030b1505040c1010096076284e00361000b040724110b41c003203034840d0150f00001200960007003500b859058982544c00d16507a602002540c040e00840401d0740c11a540362030742c4000c3d003410b03104100c48a000b210000101c5601c18001004500c41002c01c0e40589c83e240c9501d00180d0300b098502c0460320300401d480d0103030031441d40213034002c1445078400c9074802c040c681e0000d400f00140d00c500d00c845000741d090301cae102ea03040c100642d040f40c85007148200052140002901140d42c40d8001691070390000d055925044164200070b151800c072200c251440c950350301c140503100480340c074201d48144840c00280180e510313640380d81205004500c4040c01028407464401000904503614442604180e1b05441803540542070041058002009507030105004600d14901031070441c05840c0109030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 169654316 1250 169653066 169653089
    0x8063c100504120503070c060e130b0a122a0e0105030a0c03021210020310061b05030a0f18030f150b03030406121104080f070b0a02070b0702120133 65
    0xe02116144150f0b412141079a482c0030510084000840c44041d120040c103050341c0301300170469100100980068100c1e90340f48150701d0b08a8100240d1140c1585104460342c201d940000c017800c50038125259000010000c90b1540c00d00c2c281e04541c03d03402e0503a4155a41c0280205076a030700e500c01e145d41c82c00d10360006441014030300000c200504d0721040035041c10b5501ca080d50143c0e00450303a2101030741c0007614202800000000140126079001c0703810000c0419002034170400d460070b511215180e103c3c0000940400c800d412402c64803d00070309030000d03e61443c80c2440719007503507818141d0145160300011078120a100071000741a030003500699000a81c000c02551815240c00c2d41507821000d4685281d020036100e0034044c3c07901806034058401002c07014040c014810070350303165606010140c0c01401e0460030501c9043c8aa40e40059901c1c1507420000940340d4584540c00001c0914060b041c100c0c0031903082607400f4242c0e000360980401680e240e030046e455003000c130211f41c681d6101f407400341c044e4410 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 169655566 1250 169654316 169654319
    0xf050310090318030c090b0303030c030705070212030c0a0b07020102090a06050306010216030b0121082a0109060c0e06070302060a020313050d080403140306090708063c100504 77
    0x2406510903141540709083c90306188564250111040401e50f20035521145100010401403003180144680b0180c214003030f520307518015a040f2503e00004e4206070030028040750103c01c5488002e400c0045218a5046944030328000d583c40e0340c3c40c07a419600315070041084011400c583c1c01402510001c680c02401c180c4824280282200c23942c100401070390452040b542c0300c03440d10b00310448442c0594020120500716604120340030b89502ca001050140b0040401c1d042c0c4003040c01402a51203aa08003200d800c00000c1c644102a04031440001c18885540f030007258004001466116513110852512008043ca112904000c928001c0b0074025001d6000301d000103d260590342c3c0210780c4200e09048404805070280c586610302030404001001083c00c0e0010b2000307142c2c0000640986007601c14207540b45180c00c101142c00008081c00341030611112001007502580c0385000d80901e480b02c0601e0700420308443c40c1c00d640b40c103212581e54000b00c00300c100c8560a8140192032040381d02d25521100d04d8279 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 169656816 1250 169655566 169655593
    0x801020a091a1c150308070209130803040605070512090d09080607050406110a05030c070e0109060b0a030902010c060f0b010e0307030309210b0a0507080a0e06130203010f0c050a090f0503 82
    0x440200080003610780d0f440031130307848182c00040b04001850103407405685585003441403044080f4041c0034a1146240a01184000b84510003201d60040d44440301017055150020305448a0080c0da0443c41c1894440e41000405c3c20001180c16205443d076540300d030803568828402d0707281e00701940c0341c4c400a42d0421040c403119000e81c1c954004011200b08030b03038004409483d41c50942d00100855042a000320904105000494200c9805480781050410042c0d00c0c15483c54850f1160342840014035484603d0301e0309580c041c000b024201a0096402e04c00c204600744004010450580040e0100341d100e038103203c450600203080c40560b81d164440841e141c0c1010190205001100c00c00d12005198045900001d01254501d6000e2440c04034003050314209010044e21f82c1800600c910b240c83d10b4000c0e079540c04440014025041292403080c3e48031011315001007405403072a03004000e10b1900707001c40c001c0a2907211b401010a81d1044c0d0380c90700f03c2a1034691041c0b0130381107441030581c503900c17940e15651003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 169658066 1250 169656816 169656847
    0x803010e041a070e310c020d021b0d02031f050105040f0e0d0c05071503150b0a020c060f0c03040f051008040b0103110105071401090507140a210803010801020a091a 72
    0x1440070301034401d1003c0c1d900348001c82104005c0600d141d02203840d075110f4036401c0c5c6c042250b04e4040c0c3c840c0c0054000e0309003200052a450070f01e444141d10906492401c00e0944d00e090010340c641f108641500d5034284401b03540c50740540401c0c4074044c000ca1400d40f800600307100314450789050708040400b03015004513124003290b0350300d8001010b480d9401602c4000660391484000b00104180035100403e201610146114920304103a02201d402c650402580d4030850b07001c11843e10110048a03181d07190208101010070500480341043d25078480014040b44900008280208840c0c0c100e0307010507111b955040c202c0b003019003130710002d000149441c010700014030303c00741d2064400030615040382070007c0350302c500c68080f00130b4103541c50300d035914000c00040c020b0600400d07014140300361100821900c51008941e411009100302a1003c0ca60003105808201200300707a0300454200005545958440c44028000c0d4040004a004a20b284e540003a405051460301070358020b0031354001c0c1c140030041055000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 169659316 1250 169658066 169658089
    0x3031b03020c03030c0a02180115080a0f09060f1104080312250809060f07140c07030606060807030e010c1e0e040e071e0e04020d0f0803010e041a070e 66
    0x754060550003201640f82040a4002065000000c0589080c20700601440d80a0b11450410907140d03500140301c210b8141c0c4201440c440c00340b400700000d94522041c1401040d41c02121160300b81054a840b003881030076003041000f040300030b0082000d2070042d44c0d8000c4c907202c3c51003180384540007844042014019040c080c1e0748800f010113541c001c00c00d080361009161428003c805c001c10440001c1c0090044d04020b801e5000b03d640111003001d00b0144000ba08966086164100801c800110b192a044e400d01c1400001c6a204205001481c5c5034640900030200894824000070315107040030025035414010084a0019a1030781810091441d020040503801040c240090100c1810034030642e45540c8590a1902d41e90303070252803d070f401c00c5001c1c1860702c8407050f218285800d80780d040c80884012042c3e15000380d4121101c00d10441145881300d5081140140500f05102c044000200e0705189545144200e10800b03021041c01c031940420f19140c3d0058424000050091000395000e003044050881d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 169660566 1250 169659316 169659323
    0xf0115052404360e0c0d02120a030f2601030b180607050a030b04060e130f080c0c01030c02030c0c010509120f0313050d05030706020703091701060f0501030603031b 72
    0x51500e03480d511039a0310844021064105218100f401503c400c8504118a841c441400401e210861340c15039103a990724245c5541074402c0941c8107400c02150750f4403009048030400903054441200060401404441c110340d40c120100704603080d46040000a02d0021004c19030400c5240c1141c0d0035038580b048940b00c01004840300b01d1401b240c0400c0c1039000c000c007600c5140c0704e60300c0c6030ba1200750140003010381c1d00700310136940136605100342409018600f1101c01d5000c0d03000d42d010310707a031816400e060020010302c0320302800440000560008170000030030140030700c150a0300d0510a929220200701e9483c0304021700960b11340c210181180b1150f1040000b0092064020009100884c200703400d2030074402606400f000715840061400b140128800b1024018102200c903808450800d03114613480e403289210041c40a0350004034034041600038281030010700692000c2c0e60071900159015030003040c1600070911110803545c000903c40d03100303000d07241c1039a500d56565a100355200d54001c0c4030104900049 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 169661816 1250 169660566 169660639
    0xf0f04200d0609031d0612070c1505010f0e01030510090524060916020706080604060e0108030304020a080c01090614070515010e010603060b030c03090115080f011505 73
    0x521150307584540c0e01c0301003405642c0009490b0050300c0c02070715880751212442c1c0c40a4040c910300802d550b8241c01c1c0c0b5080d40c518044c0c4030355507440b603208072003423020a40010054101e01407112000c40c02a4041c50684180b002c0c0170000700e8584040080d41282440002d000303902102c120380415070643c01400d040d52064045981c0c0600c00e03003001109851072294203088407000403c0001e1071411009640e044648509051000d0000344002502c0f8000c40c061082404440001304206440c0e03540300c2002003c01301c10049040d611262000c2d242e600035035042e445001c0000020031074400103d00822245016100c66600c1da01d40360060368200512880340300192001d00001c0c000c100d040c0800440450400c0d00c60754690f040a100105140301130300840101860301205005403680c6000b207a40001142649a40b250740344041d040c0500b00c841d00990746400a25800138040a0005d244841003c000c07009020500c85110000d580181600c10283d0000004843e92a20021081034114403400017805 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 169663066 1250 169661816 169661873
    0x19060e011404180b0406030c030f03090819050105070921020d06050702073003032d0c0207270c1b082115040209040605031f050f0f04 59
    0x350003882c1c00030b07400b400100c80e0800e0041000d4269105007680300360111410001c250440d181c0c4807030206240801005c06102d01c4400080c0760180c2024402018000c0481d549800d12080c401c0702e01100d01822030700c640c208000f1400d5107000342d508006071442c20010300c0d0818810300e91580440a844c001380c0c0c0007410b41102c40085113050140e43d21a8500d40c000309422450440103c1c07a01c00c800c03c4168661095a802e5888148402000750401d1b40520b07010480013990710141e1754401501041c0e0303984030342901c404480e0152540010f440112550203445000b91344440302d540b4815040c229207842d0424035a400d02440e4958081100c03aa218030300001807015246041d00101090f00b003d40b078608020503a8030a1065508000c407444481c3d408c841600d00700288400c0c50f2a01440c0340c0d84c80740790003040c1c2070300d162a1540102e004040c01030485071211342c030049012200621555400030f80d410940000c16046d1111130490080c40307040c3d54503c090b500c1361101201d88500400d03200c401c3c4440c0d0318 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 169664316 1250 169663066 169663097
    0xc01020c01060e070c1a040204140403030c031503080f0c0a17120a020424030e01060b180d02130e211c0c050702060304020402070602040e1519060e01 66
    0x40e0800000c0280000b50b407a0030030f030071400b4401000b400c1c00b0820444001060000d9107105880070003030040440701400d03865510001e00544a2a0302d280a03000d045001c000c14194141c00011000c5400d440402203120b800c40010390a49443c00050705540301005450000100e68000b40607989691007a20080d1082d5522648032402c8e800b080d004079403001c240078116407141740c10107820254480c0304500c0c15280101c9200004110b00f485c1e140345c3c001e8032400b8401800381d000810240340a000804c0615140c43c01070792a071f0070168480c0000c81541c8502062410203c00c58031115800901c0d01541c0c0d07044506c442c000d8800d0350f0650f102c81c01520418040f6100c1c24504000c49010407000a494054110310b102c20340701c01480311858141010045042c598000d01221002078050765000e9072030703850707001140c081d100f40030008101500c0041c00249580000b003510780a2160000300102c0100c80c041040507147c411054240c9540d2400400c11029001e402112a1001c0606140c625003190f901e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 169665566 1250 169664316 169664321
    0xb15090f06040f090b0d020907051c1107030e042d0f020d0203040312150b0a1808030405030f030414060306040906050f0a06241404090e1f050f0606030c0c01 69
    0x180720380a80c4034560f00502c02483c2038000c15010b4001940c040140144070740004d51f4441c005021750043c811b00160038805110180031011403000d80c010300b40042481c40c5901c2c0440c0e4040142038001903001c0e4505130040c40d00e40146403040410004550f58a109001c0341305800301440c3c003100301d096480507103500c95000d50000d4445038031222001a203034034203400c0240c41d440448105003030051400544079125030741c040000d000d860f0700f04907694555012190596030144034691240310001951400580078030004018001c2d25820b40642e00d410301890a120b0f070328000ca000f210030019052078500300038148140a1544000000c10114882145031140812288140c50603032824000ca03040110381c1d8070324020344004000d0001d103455000e100e11300f91010110400400410000c814440320410164141079030040d0121280401c440844010000d40d2100034141c2280f82c015025a0091400c1380c511543c0e00c5030402101d2680b050340c40000f0171403994402458507600d0102400b0503c01050240f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 169666816 1250 169665566 169665569
    0x90907080709050a0b121c030905070e0115080127141e07170408090a08070618090606050d0b031603050106140f1819050a050a0e010b15090f0604 64
    0x2c1800506804c00210440c00d41e40c0d0b20f05403c1c0250050000c1814181c00000c00c0903400544242c0080c5054180200b2409045172007001f074102c0c0324807100490a010082040c5d4101c84100c0003012881003c10030a6400000c24450003181c242e144030013000819a41222040c05009070034000742d400c2040309030b494406c10aa84091049480305103069070300003c0218503400411300d0411458012510450b50300c420401840104080310126118089441d03144004011f005083e0594030b1981c3c4600000303010124014081c042244986000542041c46110b40c005584c0d0700d81d11549404c1d80c0105040180c02516881501071040790542c0038001c603030304101400385104000218016140810307414268207184d407502d2080110441000d2036a40d02140703140e8503408000d00750310325682d4060982c20308200c4218043d085081c00f04000b903540710383d4403d512808074460100306805840da0411300322103442811a07001038007058851405507414004d080d00d003c005021410181591001ca082ea4205 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 169668066 1250 169666816 169666829
    0xe061f030c09061805010c05010b0d080d05010603060e0a020c0705031c090905061f020705060a0c02010f0f050f09060c0114011d06180c070b0412020d020109050c0909070807 76
    0x26a4100089164010b0400c1c00070300143c50000241407a43c01e0941058080788919030511200c0c103000380c00c100081d0010b2040a40c002d00015884142e410724140a40c4082420640309161600114049000b403150005075409278100000c1036640c1000000254044001a10070348203100000800d60390400052580d400b11081c0381091412150010b002003240d41c0000614508040c104045c684a19080b40680f05120102c090f154801c0354040e41800029042650016000954022416000b40411a1203032003030341c9401039810b10341c404950340c0c1d2040d280740300000c004000070000d1003c0c0c64060120315600401c46032a00c003515007203900310344041035040440361441d0010844c0c400301841000701d1115141d100b108901e02000040d85140400c15210340f8040f01c480401c0b48004284151188a54010201c007218201810004003807041c2a840c00014401c4c0342c0c00702011403041c041c40703a0169011004040035a12402000074041c2d008103c0d0b08284030fa1000061175600400812004207171 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 169669316 1250 169668066 169668071
    0x90201030b03060106201f0b1206040305071208040302060a02310f0f1a03070509121b0409081b1f0b100507080a0804020406120804051f08010e061f03 66
    0x2049210043c5103150340e18020341c9130f009003a9987d15401e081c101b03211a03084248000031808106030000d0300c03500350315070446e00310310a0008100406400c00000c0481e03500400300402c0c070440c0c2c41011a00c100048400800681000c1c0114800c2400c1783c0103050081400b070b0f44100008000c6100170b88600d07400004143c102006c42c410031007001e040c00004080c003620625000003c1c00d01400c1c841d00f60200100b0f4010301d0001000855252160301a5406441d000341180044092008011395440002c41e0318902450341000103038481c03805200350700c240c40e440b0b482182004660780c507208903071010407842c91181c041e0b0007a03003185960700c3c2003425801400c1140020760106d543d0a01861000c0c641d006424840f0810031400890820815a0104007243c5000e00c05079440380301143c050003190340700c805401d920f00e201a04025040001d03100b6a501503842c1070703283c1803c3d0070007003c41e55004d0300384000c280310200510001c410034800562000300a00b0341001c1c40034000c00b211080720400510030020744d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 169670566 1250 169669316 169669337
    0x405010e0f060412031404080703020106090905030901030c03020405010c060b03010f110721120e0c04110901080c03010312050a020114040f02030607080c0a031d031809010b1606090201030b03060106 87
    0x4e002e806402a10f290385070400420340003c00883c40c0440142c0084d0040c1001f01d603030780415100b5000400035007041e450501030108945002035407070700300c1490385010078200445103000500c2072094504469050703690071040403054031504002c06190f12a1070b007554a49071143d0045c3d41d00c1c0500c0201a00d41c50000d95a0550340c144080003210404100302c107980003456031708035598042500081c5503031020002508605c0c001c00c16180c2a01358072901d80081c10701c0c50785a0058010030152400c03c4080e04c52840c2980c034140c14402c01e10090000510281c2000a40800343d480341c0d02400c800328041c000002c070101090182c2004400031101200d42091003080c1204504040c482240c01502600b4840442d040c40d040101c018014041070b40105603035015046159100030b10030000e90f441a009817965448c1603542d0b8130010151300640350060084100000c2d40b80c1e009000c407510840c102c4607003242801c05a90b4074000d0304c1c01000070b034101500c0301e034140043e6600f8090f00d4024447c50b158140d008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 169671816 1250 169670566 169670573
    0xb0d080c0609120a0f020f06010f080705040b0d080c070306060f03111207140f06030f0901110c030901120b0616060506030309010806190b03090f1507020d080405010e0f0604 76
    0x10010314440c0c039500411083e051400103482942c9500c0388600f07002c1205e05440c20b04074500098403c3c40d007603d00c925130001603410308100c1d513181601c034108241c44410b51240c0500c4161201c83c4a440d07000b0203840c9103c07012544e014058200340c14240300340c6600e1596500c0321015503440c1c1e080078050604c1d43d5410001c1100300c100c1189406401c1e1460281c0c281309605894880007544209000040f00f011001882d41e200c0529804010340141150b0b02d80c00e000000c80c224a8040f54900b40070361038030381c4031400300c1000001d9070040203510008624004004d401158003c8031001c0c40d517076441d00c580803c0710315601e020151500c110304070b4852076415010701b032000c107135240a84418004d8108002c403004c5030368403004003036100c0400d0321023282c0e5100c0124003d955500541c0004c0b0700c0f49001c8244510140041780c1003003026002e40440340520f40600340e8503d680e80c140c400d440540d0020b4000301c80180614000d95009001d40000180e5101842480d420550590707049c01490304140104000c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 169673066 1250 169671816 169671823
    0x303060f090506011b0503040902120603120f0414030c0a0b0d240308091c0b010f0504050c1b070b0a0201020715060b07021c052e050c090111010b0d080c 67
    0xa0403250810b000d24108080068074107400014600380c00e07a0000010424407400f00201c8000340700e80b9104564424003030540155400302a590b25203c1d004003440900d55201c184280e03448610104403091505250000700444403003080b001c03039010b0054030a0100c09546500c200e8008000016130745503508802c0e00000700321481c50080c0e00500d4440010703034466917900410750302170703a61101201d5501c0640b0800201010f000400700e500c660102401c50f000c1140f05640c0c5412144441d1989015648030801c11040c2c070340885070407520134801c1c481c0c3c1000701c1003280000d1038006450155500c25480c1c502800f07050b402480400c0250b0740000d00c60b000c2003c80701000d4200f640041e800c001003800c20f00b000c0c21920440c0f10292041c02140c0320002d540c1302c1d0401038804554400120740f28100000c0703040c0540003071203200450240801240440b40102070149038402d0790036110703142c6055120401500c02044d0080c2c0c5500a66a810040b10b140d140c1001c0c50b022180118001b81d1030f00391400d2010314 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 169674316 1250 169673066 169673069
    0x70c080303161209050d05160c0f030b0f070c1e020a080618010212010306090c0b0406080a0c0206100e1315050a0b120712060e241617040309120303060f 67
    0x8007181381030f11960125502083c0160b485105c4d14146a403120007280c3e01400c200e07910400740003007041c4400010301100b101180c00889100c1c920301741890340c8d098131000e0b02e801c0c11500d00d80840c104031000c1e80041c501c41003040c030340c52901c9900b1401600300d402061620700b2681010b4400d81c42401489072400004030310580c040f054600951600b0300070740d070040070514180b00c0209265141c034010801c1108814025014041c1d684450703032140e50340d03100104884c4095500f200e805140404284081d8404681644507030940c00f00290014a1309098a03145a40184104c14003441c8034591400514500084100d1040d10000440e603410940d408070112884010b10340e01c03940d07605089801406010418000b15400c1000c0707914042d0031418890041e011885444050b07010701c201c450b0820701c038040743e50030880b100480b031491079866101180704a04811060f40c0031900c0740000c80301c10462a0900b5a2113882481c0a923031665030382d0099201101c070b000703049002c030b81ca41c00284650355000fa40b000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 169675566 1250 169674316 169674347
    0x2160b0901120c0905091305032d0a0c020103060609080c0f010201020c0109110906030a03140a02010204210b0a0b1305040f05010603030909050c040b03041b0e071206090b090c070c08030316 83
    0x140010306c0d03684842d0f0b03d21035800174ae41c0070900d003140e00e040360340903000142c611100c00190a41c0d850000314000c00703450147e101203010a103800408209980b00700d515a05a442e07035802800c1c1084880100041441103411044c115902000041c1c41d0352001c0c0131361420207100b8010003162201e0304040040c0d2010003001d007402540803450320342c042940812842110240328280e295030309880101240640700c4e5400000100b020b40650840d28480d880202a14a000313088024554440501c074005039015460186d07440407411129074661601a8001500f00d07100c0c04e11400310607045d60710503095400a038030a6000c03c080300d900b00251940c80c05025400b40b6074101040c582401d100c00840140409031002d4400121080c0400c1c58901500c1c3c0500604242d224405881c0380001c5c006224662032260741907000d00300314000940501c240a9034880500003091240c0341d0740c0c0e400c840040c0c0d41180c0380030344008401ea000007403038440c00c0c001540180c1c036549420003100d01e291809440100d00700c0c0d10b003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 169676816 1250 169675566 169675591
    0x19090b0c0601062a121b020105041511011406010810080a08030a1e020405030106060207050a05090c0f0c0604020901080607080402090a0b150403060c02160b0901120c090509 76
    0x11440c0c0301010510505440182c10200500b085600020054440d070ba4034040c2e8000854010308184a003005030300b90459056610b0304644502448040c0050040c05002801f080c0188414040040311040d2424031718100c1c41c1c03026261285800450070b458904090300342414002d8248070280d640203410741c1e40300481c2021081d0701c9141c07074036060351600d0a00d40900b9010000c0f000c030f600240d103a000701c0e842c0e102200c2d45200719024060400002d5000e1f02c00d40e4425882c10340f0006581e400440c04000302d41c4c00130b203045505407500701071100401001f0030684403001e041145000488040001d0b0800c81122001081d05203010b105001c2d0245060704681e81980c485000c200d10f241c0d01151f0030b540301d46d064036604c0f82915030040d5507019202c2c03401000e5002040410044582c08060050011039001c0c060501c203c0c0303501c80080e03894000b0103042c906a85255001404030809080040c00c113000b062400c080c80b04a50101c40045a009103d001b00156035400d0400c03140c074080f584544c20805109c0d20307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 169678066 1250 169676816 169676827
    0xa0806060c031602010c0f060506030c0d050606061b0a0c03020a0b040302090a0b0105090d080d1113060c080f0a05070b060102030309032a06040b01060801060504031a1b19090b 77
    0x40341e80f400f42940803200000d60b92107000859200f4201840c1d12030740b096200c101c40381c2a2a25802500c0c5c11542e40c0e000388162041c507111440d18406c1401c240790070401821003030700c2d18418405e280d4007078162491154403840072240d101004100b0405014050481c002501c2d0552041195110040c0d02c2031081210600060025a03a00b4110356080100c1c80b100103000d110140069410780140e400c4590b000450701c42e00400e0120a03001440e08008808040141607100e100000850203548500d11442807040c0c1c081c0903160082150611045c082c0021504102003202040c4141c1d200840ca078000445c082005410400100140c0750056002d0018500794a0a0000b00741e0f40c0c0900740012422102600d110700c800c603001000880b1041c1c3c507900740ca40c1c0345841e0074401b00c286000e114030400a20f01400005a452003030041c0c41c16241c0c000085030601103560f80c91049158040d1540030000008501c1102c5900580002c2200b0390240040c0c0e80b20804204014000c83c89030b80c400240074404000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 169679316 1250 169678066 169678087
    0xd02010b01030212070c031107140f0907200102040b0310082b1b0507030f030206070c030e06030c090904140706081e130b0702030d05150d24020f0a080606 68
    0x41d0075032017141031501d00007031503060a00310754910046c0c84c5150769025281d0081020480e104141c400d224043d0340c444220307000e0f0401c1c48240ea20403521000010503190ba42c620064401c0324001000c1da068002509054840c401d00f5840da00968a00000140180040120744404d0001c0010124a068002911105014185442c4500c0110701c010400c0802800c07818200c000031108010742c0041c103c824084e02e0740783c890720325a200441907000d881385000048803a807090031980c40003a4507958013a1505910f1040c04180c0d04023401c80c10550328184076205d803d4a9540e4610320550081c820b03004540b0a20ba00c03d07040c4251a0401c0081220001c00c00c100c10504403503410700c004080300b00200982d10007050651120718503034000d203407441c44030034040c4e901d50000150560190491003000716403201422121480202c008403500041003503551408151501d809840c42c542d54032403400030b03500c104044805ca0340040d50149a02c6000314040300c07115070004083c1d612120540d50a80380c05c0c190513 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 169680566 1250 169679316 169679347
    0x30507140711090604110712110d02030403030302030c04170a060501060e09011712130f2103030507091a04080c0303040518090114130203061b07060921020d02010b010302 75
    0x19107003806103c0d542c010441c10340381c0380d11503069100e200001c2c3da1100e81c60325000004100ca903120700c00040c1d00703000192000c140030a001002c5e056680041d882c0c98038540d800e801940005142404404040c040001d10004055000c080c040100c006041ca2030723540e1030180115041a0021000c10144450071400e41d103e80714098151400c80609020300c2c01c546560902e000c3e0300484100ca007200c0420407940032004030031640241d13280500b020b012036032a40807085051210185800c8688668119040864042c0d0300081e0004800d140410300991520813000325001e20300c0742c04c01b08c80c00000f02040100000c0c4110b540380402200a14a842c0c176042c000307541d9481d1628204065158003000c40c4017074100754002c0e0841740003080b00101501e00344810000500440c0c40c180d0290241400003045072002980c0b081003001e620b03240506101482c0c8a51004105401c41100e4821450300801c1c110314040420701c05091050b0f005184819400c0002801e450000340d01c0c90505005005a0302c07900c0c1549d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 169681816 1250 169680566 169680593
    0x120c0a030803060301090501020a210c05030109150305030c0c0a05040506010e100e1017090c011b0204020c100204051804050304061220031f05060d05060105070b070305071407 77
    0x340740c4640326101c6000080c010040c10702c0c02007040d880001c00307000054005000070002c00c0d8a410400c404c2040b041b6030001e8960b01c184000001e40100014030a046d41c544c040d940c1081121620203946449039a02d81c5141e001210303c0203650b000800710051841c0450460005d0502580c0511090a0080000c2c10b201910f4120511070300c0403540304d040c620700c07032a40307100203020052481141c802e0f44003010317000910781c024081040ba0680300181080304001404549500103a4400008036898101c1a0103640840c00403a07000b80c00300000c5010b40720070000b1805030038038800700594407490b1004100344443e6464500e00d040c07a01c8410000842e4000c0180c80c111441410300c83d44c0c90007011000d4004141c2600e8040307405414404c141d040c49030362005188a05400301040d02d04001c001c40b00e03401d480700742c23007010340c0300c00104061a9140103a401160b044417040c10401d00305001a640c4100d802000c940110003c1d50740c0081180c5290f110008903d0003c807020000d00c0c200c26a190070704c4d4a07a0781c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 169683066 1250 169681816 169681823
    0x204140f1f02030c0a03121103090c1203070501050a02040806070206011505130e040b04060c03020405030c100201060b0706050f0f1608062115010906061215090911120c0a03 76
    0x201c4189000600a01c01c5901c4a00301c0010b480107401d540c6405000500c0f110144000185089807079120440164100c1c1c0c06400008000c00a911030b01003008269680103103000b0316030105000c0200003071000d00a0350702a6500800150701c0300d09007442c0d98a4031600070102030455000000400688288407013040c6502941e20b030955851141003952000e086d4554050b041440240e010001884075800314940228403401080c84040c0062504078140d020328003856501d90024442a0014500b901c00042140f8136800007140a80d90303508141700700d8209102c159562038030f8004100626070188521a4084c500300501078541c1050500f40e107292413014610380500c812080452150b40d9010209400c0712043c2c1743d601d401001050010761500c094100400515514a0010505110324022281991010303034400c4d51510564411001030611002c0c0c250b0000c0310650045250b28184c05101c22ba0760292400b0b0309038525541c14000d0310850310b0b1484510303800003131403005240c4e41e10148100302c0742c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 169684316 1250 169683066 169683109
    0x30504140a051e031e0717010b06031009060503010c12090c05030313050103060b070b041704030204020a0804020913170717030103050105090f0609070e07030e0601090204140f 77
    0x105002244140c905508101d03804105a0352a0004016442c103c0840c200c0a5055a4040214080e40281503203408001280c5420052052150501524941040e58004400411184400c0010492035803083d42e5140725512003501c00c0c170440e606805000b006010950003084200c101030401403180b814050350408003602c944d984006c0c40110500603000d444c0040583c0e694a00c0c5ca648400e40203824030585012a00745100003c0c2c072001a0305568400360000182c0605a8480da14024a1140b4140c0c00000410900000c000758440748081d024411942d00c0b05a0142450b0040000510008008521003110740e14002e0000703d40401d40a40c0c6100031000c59240c0d511807400140c080881c40d400b501c56400400000306102c01504854045c1c02090159124525010700250311f07280200c945001c194000c0c04200040072036000c17070680c07040462600242000300c81844a042407401c0e0702a264281e008507050055030300b038120040c0e00103802c031943c00d00721054002140819070004425001100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 169685566 1250 169684316 169684349
    0x80702030c360f07270303030f0f05060f3a020a06020325080405120f010518150606040e0103050303040b0a0c08161e0503011a07030504 60
    0x440030030551520038001821a070a1020700751400c00d000d00910140075140c0024045800004034103192180501c1128190b0b4485a4521030203039640340c0000c1202c008001e1140d96000c401021701c1c0c1100c060f501c00e40d0003142c902c1220381e0f00000d0303e0800740454849403426050120316555024452440703030041e40c17183d03d10402c202c03a4480c0868589040d59048910105510707001c8680a54151894401c5aa0b03545240e200c6000703d9803801840d03142c040f44904060501c4c000b0003804001c100301031207901c40c68a0b02d502c036404140c001000340302d130305600c1e48800c200d880040803c1c080d0b19800341030740d2051039420104070356181c0d681b0505c01c00c1941512091380815030540f03451003160050034440745081c09e9940c2da450100e50700d0b441120260f0f580c030900d00100703040d075559000b04180a000c558407021f141c4c55494840080c0c000c0d9005940a000700d003190150b400742460845400301d241c039103d02d5142d626224111072522411000384203920001c02000e40006e82003415a401c6d00c220b0035441e01e121 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 169686816 1250 169685566 169685569
    0x411220515060c030c070e0c0f0306060702040e0f0c030f070b1b011d010b011403071101090c080f0f0708031b0321061215061203091011060705040b0403080702 70
    0x140c0442440d0b5005840042d0f03003120000000020a2810b200c3d008882600c0e540b003154090940080c2c1d0b2070700c1c0002c81000305002e1042608091504410010b045c0e0303180c010b10384c0c000350440b1800410b14405400c2200c4c006058a0b082c802d82d00002001d50140400060080d41d0b2512036060340140d400030b46021030540084601032101c41e40020000c0300800202d00203000001e031003450f4600c030303580c99824a101c020065110751143c0002190703032001c06055441e00c07002680c81403140140da005640d40d4940110102380c02d0f0014100070841000544082071410300218101000144801015845040c0411264a0010455030592042c4c030b080344030300038980100341c1103100da84508005425024408050040000d800d02e009060440321220703000c0e260f050301c130340700d102d09072503010f804100c5400203000c2e0400a0100d02c3e609001000e591070212124001342212540c00e0b4150001810440c40003200d10f000c05ca5070f60441d0392420714606162500038030155500c514000100880008503122045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 169688066 1250 169686816 169686841
    0x6071b03170a05010e070c0f17071a0a0b0105070b04060902030f030d0b01090501030b010f050d140103050106050414160c080c061f0504022d12070804112205 69
    0x105891644104450700300760582d000030301428010b0204081320600812080e902901445d00f5144c4c3c401071a9840401545410030304c02940071641d031124100300000d50001e00c0c0d40110240d42008080b8941c4c041c01d12002505c1250150a0598103010f020000d02d070114501c044107503030040d0f1148001c02c2c00003041c4080b0b4100050812055035612001c42d040342e00c405030307412000740583c080c0c2e030341c1c04030542d560011016210060312050110304031a03809514a84204000c2c030840c03207a008085960728019a0560005a00b40d005480303e0b5520007091044d1b10702030055080f02c840c4400500450304008499031581c007159200f08050080e14580141000500015209204140d00540d80d030740c5850005180c50b004845108401c50341c00c0200070800b898940300f0b448100c5050b0090302c405145030b08041036950402c0040a658210074409038485015265041e44580030b50b5548030b03540c0c2001d06d41600c44002061903030384030321b0110441d00203428183e0380884000302c0441e03000c40c403500c800c4441c03c82c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 169689316 1250 169688066 169688087
    0x20d061203030e0607140a030b041d100c0801080304140301091509050c010504140904140a0f14030a080a020a090510091e050607080c0708070906051206071b03 70
    0x20440c08a0030940141034055100e0400401440e080d076110303555035242100d0010101034079070340e4540c050040b11311070b6100b07074440890300c0c8000c4d1000031042500f00940c6a402c80c1240c14101c0f170303400260348003072041c1c19014208000c1d607203082c103094a50400c1101da80b24080c2c1d009601e5200845560f046d16075809400118000b81c010420f0070018400a2260016185480041c0d42c103103e16a222036407544114100c1c0c003216a89410210000269030411004070070242c010780389002d400c4a1140c0d0000d080c0681c4990034403e03a00000140c1042c6070110848107803800000c0c40c0e80041c41801501174104403000d5121140705001640c5240b81081a1901c0700103411203500300c1c0034001102052900580c80105840950700c04420840c8101940c1910040c01c0c0102d91300001c0c10f01440e030010312040003070545064510300307544001e03403640c0ba01480c0c60313840e601503c513680d140d6204000d18200300b5401144403d800c0090034140c40c0c061800b4141c01d040140d1120442c814028a0041c1071040d6940714 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 169690566 1250 169689316 169689329
    0x1030f030c080f0d0507030b12060a1e022b090309120204200c1203040c031101110d09180c02070509060a0e0c0a20251517060a0303090504020d06 64
    0x90711341030a511244014041200c445012a103080c2114000345841200c850070200e1910080c5440d0b034030312407458085c0280c014600b1560030702c05240303014004540040c20724018441801059403c1040d03802540d44503507400c0e0a10149031411003804240d0001075031086e01c01880300200321030482d02c040383c02009012030891798418601d20b161407aa80b410010700616445400702e51006440c1c4001c60140d1000ba507004041044c90403007040001c0a034401c44a0f2440141020f4658084800e041c5050151044060700050307011032060100d441c0c00d0081c0341c1c24961b244400c1100307182d40d110181d503c0031680100b9201e06407413000555a96144443c5501410f00969903504504241c6080b041580040100703034003258070203d40e540c000d4481c02e16540f0a8201000414590713180c0d55842c80e40014074441c60929010680c4013007200101c2d10104c0c04490b010390b48000c2c601400f840e0800310751001800041c811083c0c103804101180c1d00c4200007041c1c981c116401603a0781841c4e050800208181e62001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 169691816 1250 169690566 169690597
    0xc030c070510050709060e060d1a03070e100e04030f08060a0513020304110301020c0619140c0702040e010b0a061d1809060c0702010c030c020307030813091401030f030c08 75
    0x202011042c070b07001035010700040e840740710005855140135100d00c25942d1515800100600c10307111291080e41144e1a0071501100d1000a14031100109051001c550001c060398100c02083c8070076182d031826040000c154544080405040c141c0e0002d01c08440310309441c1c01c201200000c2a42c55640e0080c60b0010800280b607261300a50000345900030790001c4070140c585044101030320060381010300858018007180000340039941da0341582c2c004201a6030000c00c08aa40d27039201c44581c0c178602e0b444a4000e08006041503298015441007005468203050f094905074101080301080d43ca40d54046015107284d030406000401001c2990050741c44400c0c0d40d9544842c1d1003a280c5901220b9000f031a00902030032003030361410382da0140342107164880c1040c0280014034a59004c40801c0c800e1740c03983d070340a2004065640d5a666600e40b68159041030b09655103200e002c5004200749095880303105029011524404203d40c034645038080220315218014050040030325085042000442c1101d41052101d03001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 169693066 1250 169691816 169691833
    0x1710090606180815011a0f070c08010506010c050606010f020a1505101505070201050705100e0c0102100b06031315051003110301090b2d090303040b070c0b0c030c0705 73
    0x81014040d60100ba580021048010400400c0403480000c0c1032a00c03251010305901e0100014004041c04294000d608018030154040b011400c000b005490300500a282003181004146402c4070400340095060101e91110080020310200d13100e5845442406d0040310000b0142d0286d0178181030413002000180c4184014000b1246a07100c2c40c000d84100c0c035a01103d0741c0380d05d10409194100111080821001c1c002d203801588540d00506c10340d4401c00030f42d040d400100c40c200302503d50035203500c0d40d56049984c00f2041542c2c100a080500142c603242441002c42d0400400c3d802d10010301111400c0124210240501040701503100d03c140c007812003003209250011096005080c140411605030071011601032245c40d0501541e20000d82010b83c1c100c0540701c2070740d0310940000d03c071f503840b1800c00c0400101001a104000480c42102d80401031543d900d001e01e00041c2000004019005000c1d00002440205030740380b1a6030b5018840e04541507070fa0f2114641c50015000c0c3d0100184248102402c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 169694316 1250 169693066 169693079
    0x8030a180b010806180705040506011407051506030c0904080309011503140624012012030619030506070c021c06020a08090d02030702060d021b070807060203070317100906 75
    0x280d40e0480d60750f001a11803d48a641d181114403601c4010b40e41c060740201800e1210740340591205030041c00c14105104442d20b800e9145015030070a030029107054102409948400942d0f0100c9a8002030840c05802403529903400200d26080242001c1c1002d0350110024070902025401051407410181e03000c40701c140e80e4a00030003400200312260503d03000304004901003410860090b107200035052558105441c0000c01102e600700354080900c4010020403160b001c181050198880030030001500c039a4900c2d001042c0070303821080c400b003990740086030142040031540c00318603280c00181034a802030031400e080c000280c0c80d010200c20b0b2a80045450308032070400c1070035401018001d07001c0e00d070002e0b141e0f00d00c6103160b1140c9041d0034031300158104104041c01441c048000306058001c41b60010f040200020107400b44d402105030350492684040740030700042c0070401040307008100510045107000100d0360001c00d0039810b078a6207154826000042129a075001c02d0090141c5282d1004110042d600d44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 169695566 1250 169694316 169694333
    0x70902031009021603020c0d2d0b0903040302040b030703080a050c0102070210031a0301050402030304171002070c0303110613080d0906090507060f02030408030a140c0f060118021608030a18 83
    0x104d0443c058401d0f603040003501c0c140b030000c43c64019000400428943c40852700704607000200c0c031038a10004410020710001911076040c0340d024900a5008544607800d40c03060004460320082c0c091300c694401442000013626074070482e043c030805440c065803180d900501040c064020f1220003903100c1c1c4040204201507500d47c0c01340750419002c4001c546407050340c10901d42200c070f00307540183d01900200070900001441c400c044004018280450300d942540044540417a00207000c111090400e850b0300b007080c194000b284201a101030409068541400c2c50420031180c00102e000b032150202240c05100408036030b100103142d0750041170074032200a552500a488000e00d00581010512540120122034070000c01c0e5400e85210900842c83c0c14154003080d600030908004041198004104ca0142100d0030302144894009a00092249504007140d0501c05c103030240c80c40035120b02c140b00d4240c415210801c41c80540e90060803441e80c80e228800d0002c054402d410304186030901c8002002e041100c4034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 169696816 1250 169695566 169695607
    0x6130f09090303061e060302210c070b010608010b03060d020406090f060e100509190e030f040f060806011e020c1e10020a020321070b07020c0f0a0807090203100902 72
    0xd0f42e0030003503140c0320700c0c40c0c0e02400d0034903001c880c2100d4202001d1195074060360045c81c100c4580140008250a1240c0c14007031071000b02c801401089000c03c241040021150b402400b6140324101144a981045401d400701d02000b410503208000d5034600105548036503000c1000f40500748814424034009018a0010301024860b00c1c82020750a400102c02c030303c0b0074680c00c050740c400801c026659181e42c280d102014a0140f40614111380d01d11010707004490400c020411780c01c05011490f05c40d898034024644803040c95001a0030701084108104081c1e0b8041d0380a04900340d00c06078140c0b10031418004034500300e001039142d03030003041c80395202104981104064207000000c94036403038640340c034400483e210f03011200300940544c44000207459000814410030420340340c8208842c02e007000b0341c660b0320307a004090b6040005600141d9424025040181c02032115501c140c4e96802d01c246468000c0b551001e8600c644012254084041070b00030049013000360040c43d40000654503248403540907034108485 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 169698066 1250 169696816 169696823
    0x60e0106081e0606090607050106050d240b0a03140c03060a0207021509090c070f060c030603050c1504181b0801180e03030103030507081204030f1b1106130f0909 71
    0x1007200428010324020859072080d44041c4c40c060400b1000302c140181030704554401c64065484100200d010303111020303828900c9000e20640101c034801401d00d1044a0034a0070140d40542c02e00344610000d0326a50000021039601c401440078124141c0042401c140c90f031751620703605004000620920444540242140c20300032610315600043c0031441207424810001410741024503c00000c030f05888040180c81d145000b465010b5121603640c4e41c03881110605520103001c25a02c030814024840208428007072000199985084807000700411075844c02144540034285001904210000d040354106541c016981c000808a25440380e80252044409004072002c00004280c880d49070031050180c1c40c0c1c030800c94000f5510303503400c5031002c45544c0d0003150103aa00c03100802101c14040d030030003446440703540070f0381d03500c18a0070000500400c200c000c03203c1c0c07010b05031020b568000410964154032880200464070b441c2e40b0500184c156208481540c41002880358601002403400e40d00e402c8450311038032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 169699316 1250 169698066 169698091
    0x50403050a03060f0e1605131e0b03070c0b0a112a071401030b041e060906060203071505040c1e050a09020f0a0f1b050f0c0103200706060e010608 64
    0x40313900c50b68402d1501c61040c801c000500744040340d201c01c0040c0c2440307065041890014075061f00350050500c00700c1310b40c3c0300e031000700400300150607480350321082d001c05406032280b800d14504040c200200313041d208080c080c09403803804000c140002015804580070199442c1104d4035076510060b0700c101b03050442507001500b00d0142c81c03904204004110781050781d8001e440f43c003240c0d810400441c01856203c031880d410560b14070b4000e1969031021240403155100040109207542000250002e6481540c4003000350344c01406004001445031502050101000c140040c941d600d07418815201499070380700c1c00f0041d150030413200c101d001d0051030005446096a80b2046d80b40d94150f294220300c0b803180038000201e010301400c054244528100300e0f41c280380e0300e0f005510003004410200c4c0003400c07a000b2a925800524a82c2018030140320322903018400342010081405226856074004008401054080ba8000b858208020081d0702c00009801c009594540e80d40e1523400c05000010140d40740b002c17000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 169700566 1250 169699316 169699319
    0x10e011d0c09010902031018020a020c010f0903080306040603080f1902071d19020a271212020a080a0905090f160f02100c0f09081b09040213050403050a0306 69
    0xc00c00a01c100c05618040c000b4186a864503001d4002500701170280c0034581640f920020310f04080003450803807000300550041c0d03240142d003006484d0000c040300041c140702c0c00c1d46240810503000280c6100701e90b00102e10300c0c0e41b5a1247d0000d4000c0c210740d00020846138000c14000d01070400c1c03a01070448844401700010b080302c01010141d83d58001c0d0b100d4402542c00e032032188441100d8504140b90084080d50164243c0701000c542c1c1401c0c0e0708641d01107000a004500a141c681e1519540d0807190940c6501c2c056041d41070120406071143c01003070103400b600e51125582c0506200308440d1072040d420400040d182d00b03e008000300031200350b1060710321802c80c440219200c000d1002c0504d02501240360800c0020004800c01e88500c1049081d050660191090355804041d050040c602548210303981c4941c0b4000303240c03015010520540000c01ca5034400d4500c2254980003030322a041c010811281c2c0400d5513124030000710501407800207001d10342c0c01d000500040640140c06400c01c1c40c0a03440c20700025 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 169701816 1250 169700566 169700621
    0x1090f1e0e0115030209030c0306071e030908070b070516260a1d0102070e2a0c100f0209030f010603171806030402150f0702031e030d0b0a08010e01 65
    0x89002c0c0144590484007040001da030a000707600400d01b180f006410303603001c43d00c031000190078080121140c0011a00f1101406560411801140703040e8680d410104203404d015141c0c000180103a81008150500c02c1000c20b08980c01401902e4080804202d00c402e1041c0a2401e000d201e11000214010404020101540d20b40c0d09800d03071b0910003903503032151048000d13201014454041c56050b24154050000f022406d01c1391170400a00c00e80003010a2f8191214419040d14600c8003a011036044001c14401d00300220f80c04240c01c04030251030003021074401036402440c0300034400e0509030781d450322901141d0340c44c041c010742060048034040c4148195840700035103442c00c00e1180250710409201610300392100d5140c01c00103560007034000342662190b10070456540000c3d60003803000e002004401303d102002c40c602000910080700d0020304449041c45400100e9660380240015914980d84980c5841d00c04d486440e58003000300101d5000b403144486c0041c0e0640213004003d0314900d81046006880d400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 169703066 1250 169701816 169701839
    0xa020a0512030c0913110a022a030706050a0201060b04031b05060f0d0207150e07030c0801060e011401141c06090c020304031b0306110307021005090c040b01090f1e 72
    0x40420903551407400c80e1190801081d417a648440c4060550b0350105920080c44100241a0401c0e4540080c000e5110b203480100c50400c564804008004c0d4407068120340c1c1d180071034400c04580403424225207980100000342c1c0581050341040400c5000401c00000380280f004030004810f40f0040311610f915180c405004180c851603c2c4c0b0708200c2d4042040079201e01541c2d00070141140100800008489009089015510b04144a41490384610814030500190307004000040000000070070140b40703010840d00b0003080502c40c1c01e007100c1c0c0f000844207540c1d024402c3c4e8002c03403017200c1026a468a05280d4044211801d15040c000240380200116000c1c00500c1007107a000c22a800650038285180e03500c40c003186000119079000300c01000c001001883c540140d14803492034a10780398981c6000c1300024605800160480b03961420201404103028001c60300c980c1c5c5a0341a10003248000502c001600c2408260788001010070f0780c0400001c8403000381d542c2610a48080d0740300d00ca5681e407001c11607031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 169704316 1250 169703066 169703071
    0x907140d09030e01080c0a050c070e0108070e0f070804020904081b030a090603060509040803180a030f0f1d010e010507050303150a0e07050904051017010b091602120c070b0a020a051203 81
    0x10300c1c06d4108035400226000c0c101401040d0200c000311248940c407140e02c030301003c1082e800b0351401d42c0880c07803e116543c48a0f4155031301c402903500005c400c0c40e0044c1c008254100280010f40160400030210303007800034030f904803444103c60030003414070b1000208038203980b54410030030240003988182010501a229000344012500d00070846401c940341d03900d40c10700315030015180c2e0340c0140c0c4800700c10320610f80601c100c1100a0182d01c911455140c943c10140c84d030280c401880c0e041214400c142500540c498000c040d01400038a044040d800000006907424460071a018140d0300c004030810103110054400b0645024060310550354803640d0f87c0080c001036800752aa01c010070002d101c188100e05059116650052202c0e155102141d030b90301d1400c00c41c2c085070243d01e8480c0d4540c0f051350820301b021594541c010410601c000000489594000c2d102c80e000005044c0028000415036250341040243c00d002c0c1000e40042c66035403c8420300a9901d1341141021250350254000c0d100c041c51242e41641d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 169705566 1250 169704316 169704331
    0x1603060803130b0f04030210050702030606090115122301080f03070c0603020a0504030c0920040b07020120060c0307030c0f1e02010f05150f15090907140d09030e0108 73
    0x200c2e80e402c1000c164510f0700020781e50200d016080c080000075944448060141c1486034a49035982d60050061508141c40100301e10700890355000104145c41c44142088541d18540c50410000500c2c20031234000f40c9040c680a0381003882180700c1500e10b0703001c0c0c1c2c0c0c858101d80f04c1504440e60a02c80004840d140d000b17555020780036036000780e8200526402900140115071080c039001d07207400d46035610714031804d000b60000141c40e43e442d214402124010148490226003040a41742031900d007242c0d020a03403186c408001e04108407098407414420b85100d40c01098200e2000343c8031075181458058007160011074013000003a0500701d600c000341c2d0003841c981d230b080485542c43c1c1c0c0f010008121095401c260010210382190b50790011100040e140d84200c90003145404411903110018070200b015441125a1051080d85002c414000c100d11401c00c95024040984004500c1d540780c2000381c80340318003200c0c03003140007100203950100e01c000c650000c8c105900c281c45200c0303044800c40044910030011600c09 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 169706816 1250 169705566 169705597
    0x1305040b04030c030908060103030f021618020703050405030a03030e1e0c120f011406030114012904090501120606060c0b0103021201020f130e0106020a0f020904030c0b1603060803 79
    0x90101e4807030b11440b00b84138001d0030040d500c81d030360b00ca00c54a07020702607006900003212000308902d201c2d0306004003140044200c1400402508025140d00010000602c000c11154009000760800d4000c205940084c034004050702c4548819040180141802c6241c50600c0d005d40c07a8000342000380c585010f00d60310441801000c02181680c284040003c042406124510603801a80d020701001d0190000586910140400350b04000342030609441c5034075070b00c05581d41c0010041c03125215a4500018540e20600306018000503503606c05654411500107080e0b0a04200020403010034403002409400d2061100700005655003070f08a44000d00220001c4c43c40381da9000420251403ca0355070041e1092071000145001c0340c100400502c1e81c03000f500c11100200c400d10801020400324000d5006080d02d0000d000342c148103643d040d040103d5100024420981d03100400c0c18144240b4042d400d250f03011030109004d090140002e5900a600c000400c00179003054030104010380f01005845000c140600d41 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 169708066 1250 169706816 169706821
    0x506010e13150f02180114040815040309030c09020711091302152703010c0f0f120603080a0806030c040612030c140d0504080c06030411040c030b120c1305040b 70
    0x307600b800c0c4500382400000e03d490300e8900980c00303400c0c40202454810358460705c5288842c1800900030688420311b4002d0000244001c00c1029000b240317440024251403060b11255445190540c0c2e02c00180d00040c200e00c8441c80b010440c0035181c3c2c001c15107035003d1192034107030122200030000380d08002c030b41c0c08081001d812465001800c080c15005c1c440041d0741c607400d04041030350f2190180a1852410b8400204c047d0060105500342072094002007100d82c07400000c0100351500207005c070f0505144810410494044807003080440d580848003441d44406131558072220114011b15540382510400d10a004031406108585464850341c0f08035504900ba48034650740c00d4400f5220018220700a0750348a416007903481914800344481c9075140e03034949406072140d0800403020b181450300910b00e13002d1b03c000c1090201040034100c601200000450b0003048460000000b00c014024802c05613411444000004014074004505482d11a00075100c9940010f42001d048050b1013044c0c50162864038400d02 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 169709316 1250 169708066 169708073
    0x2060a060f2126070311010b0a03020120061006120b090a020c010608030d15080a020310020d0b040501061e03151202010207080d021507021c110a02030f03070506010e13 74
    0x1c8104000d4001e554250010510400200f00310400103500360050800250303480c201904101080c1003015014000c01002c000302001c2204610903000190510250b402812103103100300700720721620301da90f8042e50300c242081100f8005051540c000c00c40840c0c0403d01e240c1104000748520b1140034001480c01440e921441c00c0380d0300030740c080c0343d004986540b903080106981104200826124055000000d0580306500311001010341a03080040e0303e0304a480d084e009a6400601414504c90303900c40140c0c3d4448044250300100380d07122002e90824101070001a0b0560015401c50842c10681110b500031060b48004800301c409002d140d44034000c10b0041485000d10444203d00041c1c81801124140340e264854030345450b034100032180043c0c0c0001c070554000c10400c04481e8010256000500c40340171075820a10b408581c1a0f4041d04101d00c002020701076080030040f50050036006030688104c003d03011645a103d89c003541041c1c40b43e118100000400b180810107051040c8405442c12541103216503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 169710566 1250 169709316 169709369
    0x31e050c01080709030206181215040b07030603060e0f010510210206040815190903080612010b0a030819110a1b0504050c0702010909050705220e0702060a060f 70
    0x80c102c004003c4124404170040c3c8800004040c14480c411149409400280810007012281801c0700c0603070300242d080d28195070b161400b56401541c850f203a404950740b0074004800a1034640e0024250504010009218000c007080341044080c6040c000c1c000c0340d8401542440f201013038490b0801c0140302020f1a43c043c07002010809800344028011031500740d075400351b81e1810913001b03a090f440448031014441c00d0454100480e030081c17480b08003840100c1c00c6032401f900a40b0010003c03402000e0b00c0c4844080600298415008054000c01600b100c903240d0814803100d400c48a1031914440c25842501003071409031854400e0319005000a0981c4002a07440029602003080041d883d042d201a011589031740780c1c0223541c41100c145031125251310003030000400f030038016880550410301d40350505c1201680002110b101065070740c8115161446080380d00100002035100b44001e808200605c40100e50201382113018813400541480081c2d100c00042000c4c014502c1030f208180d40142030991542c1260 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 169711816 1250 169710566 169710571
    0x906011a0c01200a030609050f0a0b0a090e03130801090f170d0c050c011808031f15020705031608100b01020f010c02071e05100503091606020106031e050c0108 70
    0x44001044030541e40304083e49444071400100b650744004180e00500582c58800e075070040007040c205212504002d000602102001b5240341c400c107444006001880d1100303c4200000c012201e000c00140c8130340c2e00c81c541c481d04624507480301c064841100003401c40c814000c050207540c0107039456a6040c0f46507100320100c44418500c403e01e11040c031000c3d00e00d9819210312441c41707640da105c0c1956009180012802c40701110720f40034a042c3e000a0540c0802c400005881d4400031203403000100b0100e4408280051038207900c00c00d041c2401c00e40100d00f055011601c501190340580403140420103100da20a129091402020125031002c902c4c3c1002c44500d801140b04c00d403041c01615820a54011040c0c2540c2d0385811503805a404594100580c08626260001c0440380b00015250181050001317010704248003004010400d020000c00d0f031948062002440c082040c2481e01c0d696603442c10060b02034042d9100907501148645010720034041c07895034410321542c3c80b001030140172580f200151140c2002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 169713066 1250 169711816 169711837
    0x1e050417090a0e010b040303110d09180f1806060b040b0d050703092306010506091c110a090b030c09060603241e0906010201020f07030c020f04050a02120906011a 71
    0x10b1610000d100311480542502804542c981d25a445043d401c0c003a042d103070345030200d840944c8071407055003005503c03421035010b540418040b900c84409604203900505015034100c3c2e055841d09814031740d4a5107541d204030b00f5910428051003001d590b413040426500540c0304281c4800700030480e807954088035900c0241d000c80141800251011241c44040380030b0002c107480e0311365440f01009034450340410031003107004140c1110954039040d94400451110181d815000000120014500c01008030585041000c00300c090800720249031303650f1428002e048440741a5000c0d004880a031b40d00e40c140b242d081c07881000c000c1c4ca05491915030032443c00024000388105810303010880d106186030341d502e000104c00800720717400f840e0104444804105c03109034044c240a0541e84100000300d08842d031131050f11022601820427000c0711455001040311401400080c9034441d140c0410024000d0050f805455820398100c03c0c0c10b00d0381d4690700c0f5955509401c0c00707208091075070b246d0000342c218103003002080910310 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 169714316 1250 169713066 169713079
    0x30106080f030304200915150d090605010512070501031116030915090f050609040617030a02160e010e070509030102070605070e0d05060a020a020f010e061806040312090203010209030f011e05041709 87
    0x90a69031080302750450030311004030a80b508040d0003841810700446001d0329081b21000880c0381110140340ea10380c182c2c8140c034181a21050410781600042e819a0710780da05a070845401c070300c400e1078024810301c02802400358110447c5402000c062080030100c0a07101d070995007501c00303410501001110707003185540d00d61040c0c032018041001074004101d8040b0303e102100031a1212201034020b0f0409104455100111492503003c01a280752100501c1c1103174980600e101840e25800c01c00c1300c4030321030180016010340c00001e1130420000300c0d903c10740c469407881c1d40d0007002d02200c0080144a00d031400d4080c0c00d9a0002000c5a25903201e540288540642e50040701c500b05003140c0424252040c21100b841d1980120003008100e00720082d40380700502c0307050007800c40b07450039a0780a4403c109000c1c0140000d56942020750071902d0950484105500c020110b447c01007403442014064405040030540d0032445610015003040307140929030055038060168114084400300c20f08064200f1100f16a00c0603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 169715566 1250 169714316 169714339
    0x5060904150b0301080f0609060708070c0b0702370206090d021e030118080403201801050f01021f020304060b060f03091603020108060f030106080f030304200915 71
    0x2004004103002000181c211545079032501716603509011510f40a000c0b280c1001e01008401c010115034940c5c00911400c00b4000b5807900002203c00c44043d01008081c042950140445e160700040c2400405d040681014000342d4410740c0c1140300e2451030415801c00c0e401e07010007801460510060904003078064110480d500d070540010794088111810814840c2654448101600302801140000c1408106041c4800225130300c188641c819440050018840a64030354010b00b103040301703000c2400c002411a90100b054006c88c84010341d0030700c00c1520558070b00007071100950000c2100744040d4480e140840b200f00c00c0003d4a0003a42c4020001c5072150782e5410010b07495a9948040d00650907282811384c0c43e4501116131515002d40203003440d05c4401005c0003040140e038018203459101105945020b40c80c01d1080100e405441650070400305030051f62800c2407c61000005144242d00691044c0b603400501505240700051200e02079403c03645c2d0400107002e20082a071001c000c2d40000d4003600015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 169716816 1250 169715566 169715591
    0x80c071d0412020115090906060609030305030c09010e040e100c18030b10080a0b040308070302030c0403080d0f020313020126010e0411060304031d10050405010c0f0f030c02090a0203060a05060904 86
    0x16503180c06c0004103959030f1803450280041d621800d4060a402d013055000b090464034050028040100009404100050407050300d900c02e05a0b0540f142c4060310a01031029140813803502c84a0a64030781c5c04036403800515070500343c070030400c4a206100100c1e008040d03500310348800502120080501c003e59480e800001540a005c2010900030341c007a088000c510b090603d40100b0340070b4054859020180117009012210304818201c3e0216075204410310780d14601c211641016025200780140b05c44d10200030050010414000326440d240300f680ca18000d81d40e4030500660000c01410364503882d40200005104684145004942050052000914085011000603803c0d441180c08400041e040c04009450f5104500c0401502d030044075200b0400202c00001001800342e403045a041210002c0004c041c0900030100c0103009822249003807648a1a0030050710181401078128016020100050702c203040ad4800d031790054070002d0622320294502403c000854021248055120350350b1000c0c40f020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 169718066 1250 169716816 169716851
    0x5030c0a300b07021606020703020604050409030e191508040b1303110724050703021b0d060203010e060f03060919080c03220b070302062d04080c071d04120201 70
    0x5800726130f00400c1d0f4a030409105d0549045554071000541d0b000e18014001682c8400c255030650300d090764009051085402c0884118821014090308034000044040715440031b40382c0c0f00b0999030341c03000702c0150400171401110011401c480103054100406d010851450034035915141e01c60080c6400c0e600a604080324a04000072756005c02ea0340900d40078a400111448000d070141c2e8a401d00717000e81000c0f00f5440c069115200c1503001004400b04280c050a655a0440240d260f42c1c3c21072030454980da155030150b07030708500c281d8841c0d100b081001242011494000b03040c0740f04500c6000601030036104211440c10844607542c08649540c0c2c00d000880f800382042010f080030050b49140c028480f542030110a0702d030003494000c0745801d4000c011003070100750009072064016a00c4c902d109504000d600155001000340201c0c801c07400c0c40e200030300c030911400c031024180c290034402c2a201c0a9035207440940c0b184201e01100c3c0c400600d2000050085144005070160300030fa14000400c081000c0000041c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 169719316 1250 169718066 169718071
    0x30f0a050717280504080709090501050f1b090103180609031403010b040b03090304080106030807030e060a0804030f0c06060803071a011412010605100905030c0a300b 73
    0x34a0104084050001d4407840d01d5001031218001443e254040a20302040003002000341d203040141c080300c401d003920a0003140c0080c9000c405580300ca40d01d03110b00501030075818605840c1c941c203150218803250448003809020341d8030350070640004020403680078602c4e0064100203051580c1c0e500200c01e030009070041d112080e03218070b000089024861402030844102010709424190f0244018072015050310f003141d0541e5031640c50303a40c887d0380d00e2800710700e18801d541103400325500b805000020003641d0070151043c18482e445400912400005221840c000c080000001509a4010401080c014040c070600c0050782d08e000f0441c0c440301d80f2450150740301503120490b2903100080c0c00e000d01c00c0046003a41035130000001c00ca025450f010100200b2040e80c800c1030702c140103030280130202078001d50041c0000c14002e007407005422828000038140c9480c0b03101b2139020703010b058120111442c0c1194083e080d220002d014904607604138106140415170601c50b81240307070b008412440420ba032102040e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 169720566 1250 169719316 169719337
    0xf06120213030f020405091c0e0f150301052107050d020f21120315010807120e010c0e040203040210110c0607050c1002060f070c03090b0c0109021c03051b030f 70
    0x141c0f0080030310600044420007044030310650810341d0445507030380d480040781070103820501d0640c40c15610f4200046036403080f419100c4d88440401e43e81003406080390080c0d8101c13082210551000300000d0884030416900c0002b0f00c04d00d801680e0280018034082d85000803041c0060b00e031400121114000c265403100989030301d03140520009050720012003c01501c44242c1c203807224103055040240641e81440e010042440c103000c101c40005080ca8400c80303c0b80380041c8540024003c2103c40c2c03004500801201e14100d00040d0b156080000c0c904085c001c40340100d50141c41001a407529001c11508118040205010350080000512441da25a40a0449240039501510048105000b0041c030001e508014a0a40d04544100150001c42e211120380c000c590b4140802d40c0305d684c1c501200d41c2845504032a1348a4801308410084000551008102034826903501020303865581003a51101c403080c0008000130710411824041e045481581c1c954541304030f00b168200b89440400d4001604a1078a42 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 169721816 1250 169720566 169720583
    0x2108120a05070e03070b0d15270606020d27080601140d030c030302091305010602030903010c1e050d06030203060c13060c03080f280204031104060f0612021303 70
    0x100d05401288901500a00182040011181c2d50f101194465045204204051078003043e10040b15200c0e0b04010000100320b02009911a15290001c030070400a4000801359034040d690320050003010700c140c500f1b4075442d0b0002c0003035030120b000441b200c41c00042c5000c0b0007210b099640000410300c5940d003010300001e8011b0015581441101c6040c02d1075000d40601ca01d40342d040c8000400c4d0050410403c040d0903181c0541d5500300180403030801483c20007251121460030000150040e804000384c00700e0502140240f0010207194402c03103070a02562400d098042c00d6010301000d403400349000389070341d007a01007001c00d0361a5240c00180c24118100c0d0039041c00f4400044011911200c00404009403401d0705101e44461510788000b00003400040090704906080c402107002002d400d52031000b54100c00b10304ca01d0a01c0c1205a580282d005031104843c1d50752070401d83d246525081c09440f05562017502a11959807401000301c03442d50030300001800e000d1b800c0001e90740c11020f000052021314060502d5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 169723066 1250 169721816 169721821
    0x10c08181c1d15090108071701030b09060601020f0c06130f09020712090807120807060501090b040e1c0503072016150c08090604080f0a03030e030310210812 69
    0x1400380c000c59141c1000d200d5240f50680c083e040c1c00c10815500640350a01c0c0464032a59801025034944001c04c2214240e6884a40000300f00311441039034a200320407050944540392030382001aa61a9500420010306401031003900d041400d03d11302400b011042881402c0c5000d0303036003081b0408003225802092070307550000780e41c6050041c40360341c074008920949400303030441c0e29003820300fa11004a40200200b00040311400400d1180b4001998441da0f004042000384d560b48000c0900180894100c0710300580c01c28401c01c80c0c0703600110740214243c0c20821140c490b42c185100407a419840104424140071260310b41c0e84035009001c880396410380d1000024a0711000b1090b000803980300c143d00105800f045034240e039810383e600c00400d10030380f648890342c1a1030340140700000c4c84074095500401d0700c0d41300f11511900fa102000407800c500341c4c020f842c00c01c81403c42d402415200e11080b01e10f0a20150a45401c200301c442001100381d400d000b00700c402e4442c04455a46609591100c404994416000d609 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 169724316 1250 169723066 169723097
    0x4020c0606030c0d03020d0c0f060507090f050303070305071104150b0d062102040903020f150a1a101d12010c020f1c0302030a060b0c10060503010c08181c 68
    0x3c54042214121100e071004d10311690020740d1601044c2d4544108881c041390142005008541101c3c0254003080a00c010318100c0001001400c640c810a0840d0303021040000f1079003004000c585103103030546e4500380303010201c0d22102408040854000c0d00180e560311002100b200b203002d12005041e40c004c015070b80c0e40003a103070801901d1564000b50101d074905500e004d07074589800c0184803e507a05480c0481c402c1c0041c01c00781c6c00c00850800b003036164018600c060055020a6410520450032850204540c40d914108640d104190b07000103a0030604400c01c2c400c1d1640910f4207400c0481c425034109407901f0350400890003401700084456103503034448040c101401e40500400441d485810001c06804154180f16460010101c1c0304d01c0500d80d001001c51084c0646070801d101400c0c15800055650090318505941c85001100f44421203160403408100e514043c06044989011661400010786550040007410100311070750718900d11a6090b200c2e4944031749c849220f03a982d44d83c0c640300ca0740b004606 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 169725566 1250 169724316 169724323
    0xb1216080c19030308060a09020307050a02121303080f0c1002030601021c0203040b130905041a100609030b060102010e1015060e060a0503060307120605060109060e0f040209010e04020c060603 84
    0x21003184101c42e6501c008140c03114040c540e07000c503070705440c0034803035900d07914040b1390b03c2d501e960000d100d42400041001800390300500240004901c40d4221001031076405174042e0140111001481c0d104001c03001040414200d501400100c025500414072b088a104403c03460704200b41169001a9008010015150780511642c05000c0c004880b414400500e400001c0d264456401100f101e203a002c03a010743d40700070708400d45024103400d800c100240d0515013001400d881c960f849141c240161500000c105d03401c1c004440c0c048907520384644054600b9561044910f4100810b0541159030300c89003011200800c00800100000309800010340814810205410750b590743c11160034002c5141080c2c4854403090221181d460840c9885074490303e8000009082407003560110348181201c107010801c3c0042640000d029034000d803200c4540961392107040c0e42c20751401c680590b200c0c10031226404035003410340081c045928145802c0b1005400c81d00054100e0b00444c0c10002d840e44110304002d01c509042 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 169726816 1250 169725566 169725583
    0x40b0a030f0b040b150d0b0d0b0f09030c0a0206160204091b05030106051e040e03070503030f0708010302180405010f0e030d050619031e0c03150f0c0e040b121608 71
    0xf0381e800d010040c14000801d06065411a640001d404000f440c0c62401c1c2003544484000d2a000f802c0060001e0b450420b204007030019942c10500c8a5140301180340311400200316895035135104061312910403150204030340c0384c01622a12494103190350f11400166110302c03071000400e04ca2040000f2501151881e82c09452140e0080350090703242c080300b44440d5407881c80344041c2d00c24500340299020780386030204018180c0040d401a66100c0032a01504115012004d144101d502000c4c0d120b8566800700200c410013401c0c80017a4001c503017621404c0c0b50700840300c3d079190b204d809017001059481413142c1c02011103400d01300d090000d4001242d5804910f01c00e0052640240c8201c42c180d0348071481c411404c00c0c43c0348030307c4010500a40310010885074003600004110a40c1c0140c543d14080b0307900d041c0000c08188414000644600e440040c05c00c0010600c03030601030500b5540c403401000b15032170a00c0000c203010003406502510141c0c031020000301c01c00462040140d6045400600d174540b404251520264 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 169728066 1250 169726816 169726819
    0xd09090501050a090b0d0203030313060b0405010b04150311030c0406080c03010b0f1c050f010e0f011a0d060510050a0f03050c09090a0b100201150801060b04050103020c03040b0a030f0b 81
    0x24000100501d41d103460031030b02038421a50b00054031000810001e54078260341b04000303405001c003000300416002c82200074803807075004950a010741000e410811040303690900a5001e0707444140024400c1c1c1d0400701e0000d2500100341000140741450030700b84140d50b0411540d007421640005000d1002c0c607844981140c000c400d0310011404d550401c080702003a40a08186c0c40f00d070800c00b18443c4144d0342242d590719080d40c0c0c4100c0402450400700c0007065294001d004000042c5035a5000c6090b000c210050941254481c19580c2124060301e072124000b6841006603009a0752284404600e55544c001c1011b0041c5442d00d032903503a9100710304050048041c041010051602d000c082140e01e01a4904503241c0075000c89810005660b1101c0c01e070014001240d031550404202c0c4446200c641e0150302400f0070780740740e01c1200005640c0360501c909039195406030806841044c8000c0001d54003036009400a190b14000307481c203180d105c42074444603401c1600c481c000a40c440218100121045c483e84105410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 169729316 1250 169728066 169728071
    0xe070807091814030d05040c051e0907180b0408150702030c03070b0705040909050106180e10091a0703020306090703090b070e0114040e0f0a09020a0605070c170d0909 73
    0x1c56a400300c81d809180c0c005012903e0350001681d200c18280103d40d14101c405804000f10b040605100307821040320300032107009038001140300184d5041c4d03450301403a180c2c00030075030001991075174002c0703800005041001841409031000402d900303102c10040e101500440c0024201d0221f280c40d803807622007010f0f01c801d0a54104010b090740c1500d01104950b209500400d10a1b06038562640460b41803140d680146a21882d01c241e090400006400c42e104440d00c081a00315558200700000084800c2c507041515198480141564000201d4103c10318a90113403180c00001e543d0040502800750b000c50340c01c4000395000040112524280c0309240c2c010580b0b10f03041200c0b2200359902d680c441c030090100000d0101c25500301c0b0650313102e03035100c0c2840307078100c1045d60f12541e4074850b8002004054070920f6442c100080000c0070300665200e450f0741150020503082c45a480d0500a490681c480300058400384150400070591030000e5560003100d00d482002080d0b01800044003c2c4288140d4008181c540d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 169730566 1250 169729316 169729331
    0x20c19081611040603050109110402040b04030b04060615020f1209010f0806040f0c051305060c0c0d06180b0601022a13021c06030212010c0507060c0e040e07080709 72
    0x4408505855540051080d2024008001e090002c01c0d1201500340c07a62080c02c090300030040200640200c40002d10132140040d0101050042000b079004900401d45500020b10003000810203550010360018002d100014106880350001c1d080f40300442c02c01405030380106401200807004210483e1180e4021072050f00384101c88000070040121207500d00108181e14000c2500d60b03442e94440001680d1200e004c000b1044004005003c0f41c008038584221140384817030000c0c603814210101d5061102101c041e08c1440b02900400598400c840d6066030341940c0c0e41c40510b03600124604000001c2d010390007a80591600a00080c503000c40708004a061920703182a008501c4140d10803d034500343c049403011034020308501194000e0054035015a910b0f50707500031184501c1460750100060701d009a07600c0c03030f1048000c04c2d0103090f640714050038000a882081290f01040d010f5000308440009450480813802034400020284d5404241230289a00100340c100310803401009090010b18070880b0a01c403a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 169731816 1250 169730566 169730573
    0x10f0b090c07030c080d0e0703241802040507050403080423031b15070c24020304081b06040909050129011e020a0503040f090b09090d0c0c05100201020c19 68
    0x30542c10b5401005d564000c554a40c402c005500a030340e054402e1811205030f01c3d580d0421143d4800c4041e040d4005030242d403480802c6402038058107000a214107100000201175600384401000000c00380000c003c8188008400030700c811004000409203c803001c40761040400c001d40002c0b41810722648070f0b40c4074107010360601da40c0c190b48500000041b5011403a502903c0f0b107001c1a44682d40d4018102402c1d10b81c00328001c030048400900c50b424010f4208001d40303829800340d941e0302c240c3c0102c8070140d12182000310700f0b003c0303030078030001c2d51001510281c01d00395285114015a000024201d4803651201d0700b0f0010325161a550300c4410f88540e1b111080d41c0100d100113442c10602e01480c410824448021880c0d45000300040390a0307030b5210341242d036103554401c108003c550482c01038410701820168400042d00d850405140240c91000150044028181040ea00e1400580044444840c02c14002035207983c0c4440c0030501d42050703000580e035110380e0b40c040350400904002d00000c91001b200041c022 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 169733066 1250 169731816 169731827
    0x306091f0207020f21030705060f010b030108070b090105090a0306050a0c210216120f08061012020a0201060e100f05100503060913060903050d1d0607031d010f0b090c0703 75
    0x1134080548802604000d040400c0e11070a0514a040045100c00100041004000180741e40306060031010380541d03988804e4035451510081c800d45031154009a020701594416600030101018141825440d201e02040402d102080640c03007035030002e070b0710010000304003400c1c06401c55412092501c84500d0324001754030112880312080c024807950b400f1400034140304503402a4181c40c1d400400040c00e0544200000b454014044035603800078202001003071b41402c1461001da582007a0b038940581c0c04041038002002900110303030100456403600c6c40001d400300300e0320300d007405400342c5000601100e0500d11643d207600e10661256016144129621108551000980350048011034441226440e134042c0301d8022040c004014084504d000400341c10990403200505180d00100c1042c08034450f03042400c030180f425a0030761030054119100103140d642c800c0c3c0c40a42c00303015031081d8101444034807210900b100c4006440100d090740d00d98040c20349140c1130166940c032104020416207041c40541e0020711 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 169734316 1250 169733066 169733089
    0x190f0b06040603090215030901020702030706210b03030d051005010216050303040b0a14210a0507140309030d020414010e0604120303050402060d020a0804020f030a030816030b0306091f020702 84
    0x200340d610182042103551b581001e4100b02c441000ca03d440303051180095000b07502c0086c08138421301c50b810f400550240200d05031030344a003a08030569170711510003600001502010500590601080100504401c91071007841d008040461800c0e04142c01d050003e40ba00e01e1081c003144000c0e040300700820035580c001046606030784c0030b0f040e02500c50901540995010812811011000c0e4000c508915640c0c08001116046070041015195079241c2066560440c0d030243c40c01c03c0080c00305201201d1005424005640064905040300c1c948000100501c080380c015401040b00070580c03d400580540c0d101c020649103040890b10145024500b80110400c841100401024180c981c0c000809544e20441580c0b03c1d400a14001e6683d8100e1003001006a9000c580491103581c21162054a038203000555801081d89502c6101c1140c5a29070342d0303069108250360030000c26889907880c1c0e41e551802c0c03000b0f601a4541c00000c000098044104040242c0c03d4045903480e0340c41404004050f039140d200485 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 169735566 1250 169734316 169734329
    0x9021e030604170717190314130203100e0a172d090406060825020c12010f060303020708010f180602071109130b1005010c02010f03060509190f0b0604 66
    0x2400c07224220f03410b4819004015001d095038469060340d49860301150001c058000280d200060100c80030380041d4102d40c034020024210484000014003031401900191029a0000301207859850384142e42e00c0035030341251101c0003150010144481042851003126008000c0e8400a40c00c08814088071902d58800c0d44a0038000080780d03c46055198070a41154044403020b00140681922954082d2540200340c07000003090f4606039281d0790256882d20442c0f6100d82681c060180c950480d0f080080542002c0010003e9550310255507841220b9841000002c5100380c015140c030b2031500c081c180c05c541d584014409060304000050491916849030a011581c0c80240162500f0f214203010140c10300003903007950072100f2441480401c200c40c02d000c4200300d200d4826529150b459540e88100c0301d100d0f10a16000c1041040c0e4000158024402403140400c41e1400180c070b1a9200c0000b10040b1042e1030300450508107190600301c8158034024090101410035091083c41503030340104607284210310641 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 169736816 1250 169735566 169735583
    0x8150f09040f0602040e0601021603020913061b080405100212040308091507032903070b0c0a06090303020901260f0702031b010204051207060c02240307020109021e030604 75
    0x241c200000810650592a0030420864a03281c545a01c11069481034078401c0c050310071401c89c0c043c0c90440c4800f1030242d03980941205190b4468403404800c000221008603200707034485c0c40e2012801c1707001110040000859444a0050400b402c05c1c0b070a15501400b403440c1103004010703054192201200e00d0340c11a605182c0300359550f5580020904202d41d00000c802d6201e003000c14412038a034190044a0952424507100640040b2a00700c4611040d51a0030b00360540c00200381001103407044030160a10800c61000d4540041540e40e50300100d40104108401103030380441d400d032295a00a04c8a001d55900b4046034200e40c50310560320f0541d000040443c01c80301c0e60200002c980c40c0c820310980b108038420b02d90107250312100000c2035020b500b2a0207001c6c0140c2c81c40c1400600f02c28000303050f50803076001b9210324840d0601ea800b88600c903460b44404160401d081e40500b60f214040500440c07040ea5194000140c0d0310f10b601c10480d00050440c101100c0740080c02061005590102d44541c1255004911 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 169738066 1250 169736816 169736821
    0x30b0601230313050d020d1d010905060d02030f220f02030c030a03110d0201060608070c050705060d09051506030c0f030c03070f03150c0e090703110f070308150f09 72
    0x101106841e41e03108040c100a008002c0c441d0584214816410007071241054640c1c170b480ca1780e000c99585400748500c50001d0080d840c05903a00d0034011051050301010314080303200a4803200400e600e82c2c4400100c0c081c03a0740c00410051103e07411508103070480c03540e40c003600d81d402c00c0c200007544c0030031000b00180a902c2405403c0c800c5603800c104501400201400303a0b16115098107000c0c0843d42e8000d40041c890182d801002e519500c1132280900791412510703240144d80f24548129100044240d044032a4030034010b0200c0c05a950402424510f103160b01c011825102c1d0345001402d111443c0304031543d131045e507400d008055a01058002800d40181c0c0d04020301c880101c0000c0c5021003614540d505070103400004074004180300c1000f000d6078011800c0b65000007034002003408403800e641d04403000030b59400000c055481d04c80441c0c1c0d044000d510380891200e050402002d2264060b184281d0103c0c00015410100b41e0018505903204010b1769401e180074520303034086684c019200420300d00c990b030101c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 169739316 1250 169738066 169738097
    0x2120904020901090e0106020102041a0c0d11030c010614040e070b3f0603060f040308160e0a060306060212040f090216060203040c0504061502100209040605130501091104030b0601 79
    0x20307030700c0041505002000321547c0d50403002c2d000398054051440c0c4d0b50404418203020302c0c440700072030b0f440f200b030034000b01412841c0440031141c0c0f01e0391001c000c580d804100035000300e80e031090164a001d00410424080b2605a2508000495111102056942c1c110307400c1041102041d10647e0141c2c81941c1d041000400380c44000c603460507103484084045224010780764074104035103200741d10800741501201c00d40e4491012440194000301d90040000303684d08001a0100c0c54100711030140c03a868103014515103040c80c000b408030301c1c47e07801c24000640c1d950f10420089504100800c4542c014102c03c51900e400c09940c810710560b10702800094a13000100034040440201d0012011078000d00115180c0c2020b00c0c1c10b41c000b2440344540c0b885030b424001e0205022254141014840308c2c6500103140200000c0b0a900107500010201369001c0d43c2e8002c00101078913140c0c48283d282000c03150001d569810040e5900c100d42c2c021074000c0d5400700030720007800022020681a90081c500b4240108485060032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 169740566 1250 169739316 169739327
    0x60e01090806090102031b042106140f040b0a060b030c13030203070303030608060106080903121f090609050c0f16060902060403080d052d19051f0602120904020901 72
    0x81c00407915102d65810041043c4040d03002e1030190410206411504030340d0490803540e80100c1c05250015114800b0ba031844030307d6240c80140480c82010f010800d15800440d02c21180b4084800d072110140715001c00080100c04c18600d513025451201c10042d0509181d04130200e800002e00b042031083c4005000409400007080380340c011540141180c1d00da540b2403400034081c1845110742540ca102d0030001040341070042005610a1045400460810010000c1c50007083e0010b881518001101e01c5800ea2508070f800843c40507100e44c0c1ea0100c2c205190030075001c1142c20081801c00d40c6001031040026020101d4100c07500d440140020041510284c00c10310018042d9000003036102000080000420002a010780044601c807101001a6611108075200011a888000408032000303c0d00c0c1842e8030300c2040039508803521a0303014180004500040c1c003128000c0c0c59102c0c6030000c04a2086c04101c0e01103190b40600840c0c4040c0003041001c1015240c14011803085912603034000c1094140b0340d00c200d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 169741816 1250 169740566 169740569
    0x61208030a0914030d0b1c061802031212010812070f0305160c1404050f0a1d030c0c030f150727030b060406060c0807030f0c08180a0501020a030207060e0109 69
    0xa066035100800043c805031350340d01030759809124a040c1385242c49203140c02074421020b80e034030350b0141c101c0310780596440004000364a1002a00f600210403600945c030100300301c4529a180a4030360340d440c00c20800380703598007a0503840b050080d07110580c1003100c401c1840507100c5141d444403104e000c222480c54151118082d07604122071840c80102c0102c02d11003008040c4045441000d08443c0190f003110900090381c00c2114506445000e0002003070401c09568060612251004400c9103a40c0f0820780141c04c3d5846aa040780959101d000044910700c0c003030200040b03040f60b1000078410034a0300d1000910051004240000b4007031034664000c4110502c2c0982074600c460840304880c01600d0303140c5840c0d4000181c880e1030050f032074070201051440c002e00c2da44200301c1e0072489160400081c0e40e003c551802c8030003409000c02c5040d0058000180d4207001400ca07000d6044c2c0c0b10441005014148102450319602140c110351016110102198000c0386460030340e10b1502c2c00c0e0b403801c0c2d101c60060711122440d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 169743066 1250 169741816 169741823
    0x21815070618020a06020607020a150605040501030609120801080604110409050307030917070b07110a0f080a0528060b150f04090c0903020105160f0b16030b0103061208030a09 77
    0x305001418100c1081c12002e0602c1e1084520048007920741100b00e90b41c0c01c080b1403180241c1d1101d00d0705000728511021070b07801001c0000e00800c0e0541c8038404542a40c1c02a03204588540c0c0301c007148420451848011110f43c00300d442d1141391580341004081c0c0d0f60001030310240c070342d030700c0c0c641a60750781d131034503000806403a4000d0708981d518600341c0707801040b02e0344c01c0c454000110100c4501100c02c0d01c0100c0d200c03045601c0c010341d00382070184544900c100c48820840c15580005a0310700064403410b9042c50710000c0a142014050380b0342682401e5003814000c028400e100103403400c0c3c40c06000c5081154a44480e082400000d80701100320100d0080307401101c1e0717403030b841d2400b041c134449150300b0400600507148444014000d18110307050170340d184030345804004d02240c01840141c1072281010800b00005010b245519010a40c94a591003e010151600d4910901d04420702c600c0e1600750180708030131a028030381000103c0c540f401004c180901903600603c1d105000003c11186400758111403c060380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 169744316 1250 169743066 169743071
    0x4030e0f06031e0108010c050a030525050c0c03030403031704050a051603021f0504031b0308131d0115050a0203070204050f04020907081501030e1603030201050a0605040218150706 79
    0x10400c14400b001d032294220f5226444041001283c0f00b0418001c182d1710740aa81c880174204405203405030094100148150a14480a0040549031a1704410288030441d00d0322400d9440440001641c01c1031800302e4245c0c0280e204100801c00240c0c0550f0300010041180c1076814283c4a5180c03503030401240c9030f009080c520803001482c0200640c40309000172a4400c44141484175599111005021080c0504002090083c0410030104505031100368032000b503812007050b903030740700d03615103c00350002e421001c44116200380c18490300a02c01d4101040020b0700703011412540c0361903510843d400b07151042c038041207800700305104214020030079a008554010401d101c11310301811558407070a0100d070b09034400c0c0e90340d10205000b039005201031030054401c01d8042c0ca683d502080194040c08001042c0c00162107400c00c4210441d4000a2100c09035110780c1c0041404d090550012023555400d0300000c0c070881c410041040c18408206441e1211403090700c4910b00680703001b000e40158051075901a18260 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 169745566 1250 169744316 169744321
    0x1909060b09070806040b0102071a031b04080a03030b0303090310020c010f0e0102030708070512010501030c1110050105040501081225020a08030406080a141302040623041b0804030e0f0603 82
    0x240c219209502c606400c2c0c5d010000710140760012a614415486200100403101803d40c0041c1d58080c01550710540580c4940800c28034038209602582c8264020b02c4c4503040900c401c02095814090300c055044124000c1d0308000340c40300002c1e250700c10313071035854603041e030002e60708100038800c0d000b000c0d0102c0e500d00b00b0042e600d1002613143c080c0d84100c80b0100028106c50008002c98000c0c1c05403100c2c40300700812460241c0c00c0100660083c80b0a10160040c030030409196410b0703080800c426240801e441c1d5000c19a035250038140015180306800001c0345411000b44c400201b4540020f8540440701c0814000c0c450007441140c1c0140701c401d11021307400204400c0c000c01e4103900000200211402540c0c1d49c1c65070b548841440044690302c0c4403840d58102c1e000040b42d611020001402150341c0000c00000b030391903842030406011440300014451182c01c20306075480314036207803007400c030144942d8501c031490044040d001802020000c000609012008a034607005d51204520001d20300000741a1a59a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 169746816 1250 169745566 169745581
    0x21c06260c0406091a010c0b0115050d0507020a0b0709060f120e03040b03090c041401030212151501090f031a041401141503011406040c03150605030603151909060b09 73
    0x100000080c0005c9410baa02080055522840f800480e0a40002e0103034000d90801070089904440b682d0490100502405004005882c4d8400d490041241c1d40040080a84038038000801d40780080600060200c8038408204403500082c0d625814032552038a40600c140c803040080c0140680c800402c1144404140800c031511140f00541c066074a60080303440404c0e02c0d07000c110035520641e42840400d0a007200400040c14200c04c500002404038059030702101c01220204060102211241c1003400000d0718940c042d6007050300880030f4100d4804843d03d181c15502c49080c042c1d00102203484549450001034184030482030340322454450f2030000c0c0260380c420780301c0c80503500c41510382d5020025120342503103d41c60144a4078111040185c11161030350f845008110082c03c42840a80a05460300d00210300340501c10098005018262181520f03828013034149440c0880c1303481700a450301d01f5a014441c1072010340c419215455201c1001241414092424070054a03003051103d8001035a582400703410b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 169748066 1250 169746816 169746821
    0x1009140d0201140a0b03030405010804081c02030109060b03130b0403050408030304050c0406081b0f010507050111071e0f080304020d080d0902030111070809090c0702090406021c06260c040609 84
    0xe1540b582150101d0740399800c8000c205d0b64864403150341540200070402c140c1d40101040c65102d40204185030409581020171065001c1601d10801c0c503560000050003451440d208000181410398991800c0d0302c0d10b01d4800030000580300c0081c1c00c01610b0303400142010b00c650115809070408206990b05d0b4109481c155581d99440c0c002a40300b5401d1110200c1d20408c00039498002c000440c0300490407680c000c00344402e0b0405081c4440c1001010080c0328080b5009000d920503061444181650f501e48905044000c4510000c440103200a13510035403000c501007465100c03442d030f000409255252900d100180c000e0b0400240100b142901003141444502c0d150300900203a8000d800a01c00031110030035071035242c41081402400d0780070a0154100900344a80e555500002e0701c480e26180034090340004800c10b0342100d0459507a0703000100e040800b5210329030442d40f040307021400c1c0050390810505401d001040c68000c1c0e00c7c4012030103156040b04040202d100b161074050b01c01c0000645542da00c001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 169749316 1250 169748066 169748081
    0x9030201091221030605100c02091503030724050a091703010602030f160206040b04030606050a06080105101205071106010e0c0306010f0c08040f0305100506031009140d0201 76
    0x12075001d0500241c1d00045041c1d002c41164001c03c440241c01401e1414024000b00c2c40b001002c142e034032900407929032110846541c9485040d01c8162246145104019090200a11812a204100f200741005d501d00100340c4c0c010072350104041010503220745002070140a4500c12242d1a81000240080b1000c20303803065549a00400390f035516410030200c0c034191480280304140040c0c0c030820401c070b002c6107080b024000d40d840c0d0700418040c620080d00080e40540154001c2c0405d010001010000c018103032040000a00741928000070741480c00801800c5000144959400740307204041c00e50a00380b01e034400a2400a118004010a081a840007000307100200d030841030078401c000010030b00d00b1410348101d1107104030428051030755442c2401101d01c841017600500c1804441800f0b000080ca45d040500040c007400c05074803090502c1c605020b484c0600082074014101e140409002c2592004140c12400c01c41010020407400604e14265446d0014036000520900807803020701c0140b40e0641191710b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 169750566 1250 169749316 169749319
    0x2150f01090b0d150e031201030507080706230a030e060906071b020d0305130806070804020a0608070c0b0912120f090d08070c1707060903020f0a020109030f1e03090302 74
    0x1040320348007000e220300850f07002c001078403500215005605114003604607107003c0301a602030702e0800340800404c85481c0d2081e08101c82a80090000744036042040003160020803041c03401da1070810250081c10710a0a02c4411004e20040004000045a0080e00304880c01c41421044400f6850100c14254a0310010794100000600034503100004104040508190b0b5800501d40440c04202d9641600d00385e11402083c0420b01036100c000408103400d0103440c0c4102125120f00b40c1c0c900d000d204219503d100c6420600600500000788015280d00801c0c42e94035076444401121551500d00319546084400704805412600c001900c0c4145500700d010705001c0c180c5280c4851140d124010360a450348032041845000801080000d843c0301d1040684ae5503013801a4072030205020408110805607008640645545844a01100805504010b0301d611440703141d01030940310300f06a00080550b80b05210190040c41c003961440b007480031034170759584000c2a0b0f803a01d200d1681d00346005814007200e81300aa = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 169751816 1250 169750566 169750571
    0x20d03030b13020405130203070309020d05060f060405090d0309030302040803131e120b0a0b091f0e150f060c010236010507080d0e07230d0f0b0702150f0109 69
    0x301c20102c5009880a07038000601054005c1d14a040d200004c1d00020144410552100417001c00f58903040340800400d4006c0c40941802d18005410380c11400d000b420072401207240904020046601180700c061031802c602e23000c20012400d080480c0a070040e81c11069441c04006070000d0002c6004000da8100d03000e641801d02c0622000200011403141803088104047c201e246038000640c4511304680d00050500001844060380000b0a44600c000c03110011001e84c0e8400c3d9402d042d40d5901407074002c10000358054010715041c0301c0c060b00e8070300c00c40748a80103a11845140ca51507039280240c41101000c40000c41d1a0840c2c208424400d003082542c07800c0348107008050095003000700704900485c800613120240344c10201d641e03425913a405110420031440d1b171003465010040007130140500901002505c101c1c80c11034000c048456661012070f03640f24140071880c4100040910ba0b084a0380d0ba080076485140d9034070380c030f0264142a140c034103583d0500940400c10810b0010700342a541643c5004508 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 169753066 1250 169751816 169751839
    0x1c030e060301080f010f141315020703030203040203100b01140c03040e1609090917070f0b010b0d0605010305010312031d06070f090803090f040b06070602030c040501020d052113020d03030b 83
    0x80b80440e403043c0107501f6030044120000b28082d580c2000c2c640aa840b80150750080d0449041c841c0c100d0300302150032400030750000248001d51804109111100c40c440c1420040b10304000c0010b440c2c8480b011001c0928480032070725440b00c05040c002e4400034821245040c9940c58220000518144542c1041000c01c6641402003142c414521400c02ca03d80d0001c5001880c103120b00d9840e280381c212103030032100300116448840000d0041d0326240c0c000c1044607080350f25035040034006402d030341e41600b00c7c80c1090b10700401040030582c40c0306490307410000fa003000998401d12042161b000c03401600c0c0b580390752003100140240194090f00e0008103654940e07540e00c00b030b5121400c4580303900c1000720300b59004800000c0444031385440c2d070010b048210020301907442c0c0411503503014144c2e0811629a013001102103410041941c040c8a81014048107190140c900400c895000c001b001e60604004021039103200010322055032810345034000c5400505880400d265458001c0c050030f813030a4014010041843d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 169754316 1250 169753066 169753091
    0x180a0501200a020303010608130501090b010501030b040b0109050906060415020303090717030711041b03050f01060309150b030a1a04060c030204060c0602090f18010608090c1c030e060301080f01 85
    0xba0782000c52298082d524691a040741129900340186c14411040d180c101141d001401c24400e01104620980c881e91b03e0758034082c009011180007418842c0500e040c11040160303a81d0003003450f01a61000ca07070248603600d500c1d000c01c41034003d940140f6a44084090480001030f000006107204480f00001c90704040e4076201111948100b2181285281c1c2c02407111070300107403e0314005516039002500001c0c1000008054142e03c0740c1000c00304000c26600c0c000c1c003085003044000c0c036025010a040510821400740d81c0e003a036200000a040e44043d55038240f40072281d42c103006101000360081d40d445000d4185200143e0301500070707181150b0007498249013078143c03030003030003a20111002521404a80c140350b460780c030080e610001d0301990100706415680420340d10152410400072101d891209190304004001e881c4200c003910a1031564081e460490350b03a07560800c840552003141340c07110f260a009180540e5121003410784107078004400700021980300e40009401c2440d00c8010000c1c86048412413 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 169755566 1250 169754316 169754381
    0x60901090b0c030612100c020f06070c03080903040f240c030203090d030207050a0603020705060708010311100e040519140f01140d060f02030103031421180a0501 71
    0x510040c00c650107000040c20700160007020f168411000740c183e9008202444003a0308010030100064546980c070101c54040690410841c1d101c1c2c8500300040016040c03402c0d0262040c040b02030b00408112031840041e90000701401524020002642c200d4030725500c0300030745010403802040301210b51071032544408a85100f4401c10000c0d41e00758016514001900301401020411080c082c0c080d131242c190b0002d0076846e217042c42070083c09103940058480031300b460064207202010f804002040a04001403021401c85600b18001030402c0b01c070b000710901d4a074016500840c0f400d80701c95029182c0800c004803501c1c041e10707806040aa100f01000079004444003845044001d55058001c25081c10051140034902a54060400b4000307000e1214100c2d195503503002d4541c8401d83e07000c00c03038011004004041e0804003003000d202100c464141031400200543d4110912800c00c02c08109140f40420768651002605000c080c100c002640d8000e6810b08055001e0006ca030002031071105041161001084c940 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 169756816 1250 169755566 169755581
    0x106050405041410060e0a081c09060f05030c090103060521010c090b09040c09030f080a1d0303090f0402160614090607021b130203091b0f06161e080705060901 70
    0x1102003410150400e00211b40c0c3c0703601908580d4000c4040d0401081c501c604222a06400341f04a0403110b20500b0121300500301d1f0700d564425800d00201030003d0803400d4005080c2c136448071804540302d4456000c100100c003d001c0e1b0f039024541104402c011443c0d181c101480f04c1e100000907400a1004138000502100c02d0b00840c0f06110319170710280540800740c41c00707410081d483e01581c1740a00d441910303501c07200001c2219040445004400150020100c4e130082c00d0b100f80990b00301100750a200480022079160b104505005100381502c1e04420203a60b16503040d20b00788110103175109501c004a04d410b00080110b13400780c00c401e0030003030000750f6003c03c0080c81301e1040c0c550b54054a82810000c1c85640081d42107666035520010310504070881812a00c061881340c0c155800030080350002909007a508c1e480085064001c4401803805441500ea000032189401094010281d07002010f06241c41c62641500601002514100d01754042c05403e1015018150068058a890f034a981e00b210342250880c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 169758066 1250 169756816 169756831
    0xa060c12061a09040f0e070e0a0b01020601060e0415080717010b030d0905060f0f030406091e080a0e030f010e010203040506180d050a11010603051b010c0b130c030b01060504050414 79
    0x8100e201980e00f00394000130345d44a00c505010419040d01160242000030302d421601d8400901c03c1000741e807594074080c3e2481d485003030001d00708950402030000c1c0b1150b001c440352030080e034951f0110800040f07495803840007403003500152080326480d469802080344020307840c4451582040800308103072601050b01c0804840e1515039507101c516003000d001c89078000700c07d44601d40c8001d100d2042c1e441c1201d8000e5100d01d1081ca00050030172098506480f030400304290103d815211700506600250850040782c107154018207024884410a00c00280782c403120030703c080c000c4d50130001c4000c2540015009075001d54800d00c20303920310355900c1214041881c001000d001c2d03e45d1011412103a40e5024400810b11082c0c1850111103504e81c5150040c25554503038000c81c2c00350701c01c100d500103151f40b181044078154000d29016000c1007041e10b642541040281800f00d258512002d000100203c0210810003146e10160104066a40700d80141c0075410074407038203008504040c1c08000c0c4c070034030200b000c0c0f24209 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 169759316 1250 169758066 169758119
    0x6020d120501080613030210050708010906091a01050c0703050a23060709060e04021b060402040e030901080411010c05060a0c0e10020d0c0311100614060c15090a060c1206 75
    0x817a01c0d800c40d02080110010380c1540548180407004184501031244220740c19110305046516054000707049440580c02003000904c0c0010102d003445c900c1c3c142441a00c8246015916100d44908544c200395480c0d2004040c1c1c822441c0d041c0070806142c0e6003034041400c1c08c1a80c8804c0d181801015182e49080301c0c0c0c0000980c4090041c40100e0260701c1600da21000a0001420810a00350382c2c0050100b8135038a92540e48450100700440c601401031201c0384506c1d101850411403030a002a110010181004000342210340702101c590f4807404851401e1904442180c0c0282040010b080c0100748a00c45000026a08641c0c1c11311424141074184091745264018422072003545d1084800308648070048042101075400e031082010100210003c448126400148580c5004030105000307801a0001d070180209220480c0100000f113000092101ca0200c0502150344030407506060100380d40004104038035000414801503400050300401d140500e504001e01500c0b12071064224041c1c041d06007440303d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 169760566 1250 169759316 169759321
    0x1206030705011e26090102090406060f0c0803090f0a030c030806090402130b19060207261911040603030e09060a03051e0106050d050a031815030207021906020d1205010806 75
    0x18800c3c1202030103040078403131841e071001c3ea900c402285441c040c5c44688250b90040341144540c50144a50781c010004e904000100d100c010030042c108021a1101502d11500400003ca025009009110160100c030017591252060b600e0081c1800c101804140e00141030900003030054100401c086004640042c82d101021820183d100081d00264440580044d1090051401510b00c081c80402420003034001c1c0000038180340c000440a40980d41088060050002c0ca40e009100403800744a141010b034004280c1041504080c12007403499a0300304d8000d80340c4032000007403590100001117928022200310083d500c8290410204070f02ca4003024040e5044186002e1010301d158000d400c281d075410700007040300c907556800500e0040b80741c4070070341d43c98102407a0b007806c05520100841c0400c1004203654a05420a5800c01c0310928011620080c9503001074280159a180c131400111204c0544030400c0c00c03502da0b00c00a41718030b9500c5c402004918421407007440300c81180561810390f0b110a00a04255 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 169761816 1250 169760566 169760627
    0xc07060507030c020d051603050d14040312080606040f091505060a080114120109050705090903070b01050613050402031302030d050a0c0b060a08060106050304120305010605090108040804080102120603070501 91
    0x52942c4008030346c28440c0901d004001c440d21075400c3c00440c0660f02415030702d42100c10241010800c0e12001c95866000c100600000340c0c3c4060000250f01c452600d1105a592913002c14124440d680002201004905001548845541059119806070f544404405588409000c203e000c1c240004010800580c01800301010385012100400170050000d0901c441454405d400c4494041c02507580d50410740c4107000608280020f00d4006c0d41e904011407416030b060b2281c01d500f03581170007020311032800011901c10300450085440e0282c00d000300304650b24200390303202800407a444a0128060f004008603a00680d0040d4161a035088054441150103d00c0c1e5460107c5420f006007815404004101d010030400700c1000214040c0440d516150743d61b00b040d0078501d080900c400e6481003094200001400119070140a0300d082500c20300742070f103441d1998a40860340b8080c03904081400d61010420403402450620b031113004804c02e0f400d0350405525400115001100b20700307050b4020354000e41c0d00707001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 169763066 1250 169761816 169761829
    0x10060e13140705130615020d09090c0e041b030b060405131e02130321090b090f100f1e05160302010e0615130501080c010f02010f020f0c07060507030c02 67
    0x711414040ea600a62280001421414861310413408141c0e103260900c5004802603905102c45414002006412008003004110240f10b01031180ca541d200c2103429070700d5005640b804d484090080042c881c0031422440700d03448104207070401001030300707100031082541080b2040798103549000c2d1880220b00c00c0030000c2c0019000c031100980d000e6a00c0c84011410640501c05001244241c0502500091541c10101e4041407100c0e10221454141030000603600e8100c00f5500881e07849001c225214040030340094142c4020310111900585040224044198003e188407908411511400784440350403000c2801d5040b00402d81000c2041000040b40070502c054007001400e10a20012403020790f0049158284101560800d078a080b095030800050310300107002d41e44c0c03d58007000400c46985041c0c0b800365030b0001340103210b040c41041152200401c0c400e400054010b500c50009645d43c0b099249011401d9201d540b481900b030050a902103400e900c00d004440007650950f40d8856400e0482c2c081019 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 169764316 1250 169763066 169763093
    0x12060d0c12020d0b0114090114030307020f0d05011a030f0307020607030e0d0c060c0b0f090604080d1104080a140a11010503130b070f030606020109051002030903091210060e13 77
    0x3e200300030a0b038600c001000e22420354080c00d00c564802080300c0443c01440b500b0401a007020003032a6080c0c400c0500c0341c07030000c2600c8400342c045401c0d5824090740b6021500781040d191000d40954241000001034442031040250241415002c99400054501303680c0d4503401001c4000b54000810051000070038444d9518520300840108405001d01e103030b035103c40c210724051b0307c0100030030704030503402e401d01400c0200c8584c402c0c4402c812031010300e04219120740f42c81c0c1c02400144603000218134005400f4199000c15094031071904500c1e0f881e80c841c94010781c0c440e07014400301c40080315000c10885202000c034030050140e92010004402d401410b005441d282c03c000c01c50000002007001d842c02040003501c4603800340c1916180c0056a904400000302510480c0d0400d01c00e6a0424880c000010030000302c0010100c0c40220042e129207540751080d0461050041d00ca0b40540c0c0d0110360440b582021410408200c0085001c00080350382d0701c4546040300c1e0868618498030000401e24010501d554140ca4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 169765566 1250 169764316 169764319
    0xa090e0313030f0501060b0301030f030c030e0a03201f0c060216120306051c0303050c2b0e01140705130504061e080703020619020a1712060d0c1202 65
    0x20309051810507191500c01c4941d0060318030203050f034010010700c002885200003a00c424404503141d0742c11500c0303060701280803580007420022002c0400c0c05051260b003043c0d044040c01491200c07913550720b0914996802e103c0351280602d0b021131a41090314507101190000c950700c004010050114129030235104124034100944206408000c030200111100480360001c3d1301c1407034a1341000b43c0d40607000302114001d421080c090704252201c9003078030800410030001c00f945454041850f50b50402081075030302554209407040c1452159269000720080c168500c1008000c13000c0200b60035400a090a940d00c0701d100c08a034030004c6000c0b60441d88100002d0085040e410007a807070143da11008901115600da00035450341158024481c616042c107000fa03c0100f0948009140d00d42c1507400140f114825034244000c1d6140c2c1500c0790607418002c2c001c00c0f40c043e80201541640384044043d59280ea8000138030308407400c0c4c003c0300080b15468980c1d40100059000400c108a243c00d061028a281d42c510304140e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 169766816 1250 169765566 169765573
    0xb090c0402120a050a200d02070506090106080d090509010302150c0d02030a0905150d2003070e3607030e1606031407080f0709090f0c0207060c020a090e 67
    0x155155150340c002026080700d40320040019140441d140800c560000c0c0c01d2001c0b084c201001c0030b101d11405c1e405c022641c1c841e05003103070742d881c21030718a18000d00c00c03664014501e00651040182c402010b5004000701c3c0da00c2c8007902c40007a10808102d0b18002140201507101440b61700510240c00c1034100340d240e45c014064038516010981040500d010032034030039540140e1000604001c410340c81040100140307401c0d00c0b008450000c0403020704503800380390b01d0380c1c40c0306a070303003c01c0022540c102a40d0119881c005031043d640b0f040c402402401e0074104da030081d014500050419455142c5040c00c44110003c0e2800c0610510750301141550440c0c020b06803e00b0140c17101450382d007000081c001c24072082c82100740e201c03042e482c090b000b800742c880300e070928100c0070300c1350040280351508480e07101d0b44082c581115401c103580e540c0051740c2c928099003101c81030600d0030240d07030002d070100e5000d000c5081c01c179001c0b41c0d80f0385e40d180c17421607000b800340f00e0007500001c90780020001104540c225494041d00d61054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 169768066 1250 169766816 169766833
    0x703080a02071e0c0807030c140409080d0204051e010e040c02010e15010e0a05010f03110a0f090b030f010c02030d09020f060705030301061404061e02010f06080a06050f130b09 77
    0x30b8000c1e240400c0080b2603200c003240000c00800a091384600014100302001d03048091171a101c030b004c3c41c07445102c1e05503500360a51181510f541c4590080060541c0803616540b50f2064510b950000d4005026043c051002c02d541c40700d07409104140d680040005039280c05010051100b40303c040c10701c451441c02559207640f210080c0901c00e005556400601c900466211740c5052441d40311804050000308a040c9000010302400700e03090142029030390041021651140c0384004502c1e0103080c2e07445400f0b80030000c6408201e14650381c006c580d020100324200d803962050394540b9400c0716200d02183c40503074401c10400e001070405412900c51b5a00007030108503005a1900420342a034404501250741e40c1000006112132604100c9600c82101c500c074609081500704040582444860180b588907104075140c0000e030203200350028a14034031f0512041c050942c0c1e40140b07595800d01d141e021190107040c180058120820a25114030613803600454415214050719040c0b030b44c04024008002a0060218 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 169769316 1250 169768066 169768073
    0x31503020406060302070201030b0910150216060503061e01020c0f040b060301030308040b0f01030206030601030e0322170a0809060306010504170d03110a0f05092205040302060105150703080a0207 86
    0x302401014991009a074406c540e10004084a141e841030920070f403907040a10520340ca4030003501064811507040c0c800802c42c80c5906a1429900410750b4140840d10900400c0281e031040c003941c06908180c9140c010581c1020540c500380c644820751300e005a00900000c0c1a07843c120180301e007000070184c4000703a054041c2c1c02043d2554400d030025004100b40c00240000c1020490440c0e0b401901181c0100a03541103600141d114171002d0456810141ca0745c2210705101d006108540340c0713041d541e10440c010b041c0030304072082c007034194031442d250b0f0085101b003502c41c000003242c9c0d01c1d401507018003001e1510100004006580d00f000e03020301d0402c1810f10002c500c903141d02c002d46510701c65003c01801702881415004043d60807440c0105000c1d103041c001c83c982707903170842c2004415400c1810a9030b202c889280115503076001c004001012413003024180440e034401c6502c81e074002c5010b03600380c8800e41e03265024005850340c510700c2c21b900c1300400c11100e40403d21915140340c2080003290090300e003501a86 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 169770566 1250 169769316 169769321
    0x61914010f020604170a090e0c0a080622050a0f140a0c05040b0d090303061d04060f020a0e040c140a1d01080903040b0304051e010209040605040b100c0515010f0602010e030f0a0315030204 82
    0x80d45c9c4802c66600054484016400940e41540305404076074942d80c5010810015450079135141c0040c40c0c068031140410306a05d041e4100e601c2003054014200050079070001000660300f825541800360b40d04c0c0005205a880c4a00b003240e0943e02c405082515100070401000000c02c9444820b500b0035a88400100b80001c0e081c0044190b41040015031070641883e0502c01c00701e03506801c04c140070030b1041282482c4c80740c10100e95401c03000c0c215000121110304490607204d45031100c880c2070300074130f0000320b4410494102c02c8500b01c00900c5441b00e01110115001512049030a0b169101c4039482400204141e45c0500c1c01107910a11900a582d0a1400d50040c40d0b492180d2402464240e500400c4240e0305040c688600002808100ca040c0103001f03074000401c031804000d4480ca4100510780c000f520502908210031840002c404038207050340d60359104010a084590700a410044d403d01a401c0c008050000541e035610f08004c40d8240b91000341101034004062210240160b1100713100c001025985a1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 169771816 1250 169770566 169770571
    0x170901170709050d170c06070e01020309130e070b03011205071406070f0318090e15010509060d031b0b01060906020601080d050c0a0c030311070f0b12061914010f020604170a090e 78
    0x60080c0188d0038001405040c4000b080401811540203122081d00796031019413090186880a50000c0c090307540700541e13403e0030400e4100c040400b4000000003800c0f00d413003100310486401601641c14154440d41804904c0a80d5400a9804001406240c0c0454412169070050a1107804d1041019203240c406401d1000250b006015081d51003609280c00202481181040791110461642941c1000d0001c0e080100103820940200000c0a042d420940070f000008001c81c42c10352010844007842ca031801d900b0000740110702c009224640001081d500014203035050b1061440a1b1041c1c2d040550100c4460b0040c8294131040d02c40c104450000c11000c2102c80041c60007076031143c05012208991030324022040c1d003c0c0418000301c500402c0084041030a999009400c111100320030380b545000a080b47c00a010020b04030369034090001010119401d0704081c07000d00f80c80780016845444402d0fa100e00040310040e142d04c00e250604100c02c0007210041c46c4004240c24030746205501c0d201c0c020404d1804 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 169773066 1250 169771816 169771837
    0xf120403080a0e03031003060c0507051b150f09010305151306030b0108032106030a020a1202011b12030c11010608061b0c030403031b170901170709050d17 68
    0xa2400b80301d9846a14080c5000d008010740003140f841c1041064403a80080c2e40c4000380c8407075604c00c61030310140d00c41d500b01c54125400000300d40301416070804181007403080c2c038003a0344034021102c5881d064402d504107403541078030a07800180c04c000c1040f0041d03010b0800208105e01048030070348404441d55508541c04400b61851400044060561030004e03010300043c0c0000e0b060345e00601c4948041413250310007141003402c0c00b46600c403a40303078280031031f20b06151800025400006018040358a5038004401721407503000340c1e5104d42c040c880680742d0004400b600c401804002d40280c2c03220540380030340c0240d200000705240c10818039000403406401c54082e904501140d40000703040c046a05c4241c08010401010080514900282001c0103581c91265100c008d0510104520010109910b401d407814025000744881d4400c4607000020101035100c07000c0d1501085c61082e00102141922103028440c210715190280102c1c20301d4204806a4840b0306c080f203201555514144980060030098042c0146 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 169774316 1250 169773066 169773077
    0x30103050309030f0c032505041b0906030203010509160c1b0914010608011a0c0d05041d01031e0f02060d140906041502160606030c0f14030709020f120403 68
    0x2109001c25052040c44088010706903c6240210b505d039501040000782c88440103401c44002040044444070011540d10896202d403520010a01c01110f09003d0080c0c10040d0b611030900d140c0303409080d8100c0c002805080d4103c1d400b00d00051911014000900c481d91300d5051103070300a005130703813a1007500c3d095200b50340295100f61010046040d403030142880c29810501c0c545120740c103003500100b10980c1480354842080e1010f0710700030011032000c2150a81c52808013510020040305002420035805481599010640014459881d40780c455143e4113a07131313016112410350321011840ca82401240c0c881a20f001429440113030050755403000814030019001400300e00344082402201c011000104500308580100c810040011000440001c44464200c401a2641919004808801c0f00d5100c01804549000008402c9c0040d580404086640c500d0b07030680803a48a8140d5800e241d21840c80e0f43d0540d000e008207100c0c0e4002900501001100280d40034106440009801d24480060307800754041036 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 169775566 1250 169774316 169774327
    0x71a04030306080f01060b0f09190e0106080105240a050d0905010504050607020d0f0c0309080f07090f09050a0204020d0b21060708091c022d010606090503060f1005060301030503 78
    0x40140b0210f51306200034002040868600b21115055210340f405d030004900000400082d03d81e29640c026803800303105600e11050545603010b580351810b0a0140c5404545901c2c0001440d1a007807100311004404c02d005260701401c0e00c040c440030303604806151024000300f44005522002d552040075807440c0202d00200340c606290910780d043c140c0180c8110300319041400030107441c0e50004020b01041003103207462aa4a209824225010010f9402c0043d1b2806418540d03980046c1c001000001c0e140300540c02c1000c045200320143c1100c0700040000e0440d000001001d0151805c0d41c0900b00141c41d105c00401c04108000001c4d5101400703210280300c1c010101d20510341074030200010369000300c3e903040903252824a039500039626501a850301480201050064000742d20900c088010360004429a000084203440e03004c81c0000041520042980b900100040e82071091684008071038026000d000d060301d402d1034013584440024441414561041c50005450300c030716008600031405480030303503240d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 169776816 1250 169775566 169775579
    0x801021c06060305130b0c0918070806010509010914060c150405010c1407080306150a020d11030a0e01050d0209030a290105010504180912020a021306081002071a04030306 75
    0x2030300c5070b41000301058500f00030841c0301c1280481e422900e80d0004008540d55440d0905102c95202e0710400d50781040800701c3c0c5003580d820210704140602139070384488181e41d8075480116404e000e101d440c24002070100c0b04c00c0128140c1118040040c0c14060b01e0b16150140341c062461400c024455905001c40c603031010030082c443c0a10582060204510340003031039450f070303207001040e50060205c040c00d20314000010924a40e41d50720303194410014050600c2c1c45600100d8060345445401c01e484022440c43c482d01c0400c64804000c4400080380c2d42c0303c00d600701c1858001154241c002c48650140103500308181080c1daa020044442078034402e4001c0044061803140080405081808840e25006044014801c5030b0300501a10140da101051510341844035070021000742c410624003414078007841f4107020f13110350b000c98401980e50096401c0c242c0d0691074450002290194480ca5101c0e401079486103034134034425001060800e002d10f00d03a0840462814a480c10110152421408a036540b001080729 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 169778066 1250 169776816 169776821
    0x7030503030403020610090e0a02090a0f1a04060605030c030a0c02100e2109181b030a0204140111060c070804150201050405070906030b0406092f0405061c15060801021c 74
    0x6083c0306a0240107007182401d01c4d139502c034080c03400241700300042f40000380034140355880400403c2c100131041c00740300113030550b07034511801004140e8041e6041501c0400d006001d40c0c00c403401400c411140d03520b196070780700002c0e0041c4600184441180101e0040c00c1c441103d0f4011040f082921401034980b4008000b0154901c10b013040c14048400c9060103142603e50b2501000030385c612250304bd12a0320740e614000480342c54103406902026880101c103200200f045580500103031801c403194101c002c1030400040d41d0600040841d0760403540060300103940d817015800503200c154440c0241d00c4c1480e03150740d005e08102c03407500e04040c0141e5490b01000144481008050000c04c11200108501404c42e1038000102c40020806071001c0c4d2280c0b008403c006141070340e06541c1443c82e011042034900000400000d00b00d082180f8416401c000118210f031410342020300710011358098881a03003da82d0f41e008400e000051894616a03a21000012000401c2c001001d00c4481000c40309200385845090208 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 169779316 1250 169778066 169778069
    0xa0203040510080f07080601050d140118020f040311041e0b0907050c0705042307020d0e09070f03050a06031e200607020d11102105160c020307030503030403020610 72
    0x4201842d0203001c110740840101c00e4005d001840d101069640c1c0000680307451040900042d42c1614050b2280f01c41c40300d126041f0f0590301c2e5400004441c1d451f6040d00b0060f4010f4840c100100782e4100800c00000b08000402e101507800a040400d414440c00701c2900c82c01c1104408981b00ca40f40c0316403540c24589881803e50003081c41c10414204111280900d40c1c980d82c5005240c000c50352a440b01001ca900d89503800382c045900d040b1309500d45040c50000b92602581380101d40850309001404000b40b9041140390720600007a504c441415820000c01c070098007002e08004801a55801c0200105080d941c028020303a0401103015420403851424081900200302e00d020700045440d82e480a9550700000c841c012034040740d40d45600d11090604c0d48100044107000ca52140d00403841440c403540244c1e22401600221111419030040304030307200d0958a00321000001c243c4002d88030b400b401d000c1d000ca00c024900260490b0a59601c1c4d0b8ac2d0689542c1c800d503015070240c0e01210412802c1e00c1a03904400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 169780566 1250 169779316 169779349
    0x12010b0402030c030a200d0b01020a06050711070b04180902180405070810090c0e0405100f09020a0905040c0603110d0e03070b060d0308040206030c0f070f020a0b040f030204050901110a02030405 85
    0x91924980300c402d46c006005580c40c04500c107441d4200d1501681c405c128031903105820080802141c01c202d44080d180303010050840019014030741c000a0488190000d5604543e4114440d900321340340307040c41e40010204441e00301da000048100c0d9095846500300c000744114464070040006500744a83c0c0340c6000c4610940000c0c0505206a0400044800028108a03612202540442d4980d03142c0582000c01c001b0706503040a00e41111806603103115081401c0050080e0f8002540341c1c2c40380403002c152501150301501d980c400c0c8604114040c80b0b540007036078501c2d442e8070f0107040640315040c000944022100300c80390340c1d00118030541440040510707141c01080c211400700e0b54001c070b59405415840000c101a01c107110100c0000ca500c0c0d8400112041e4150340308000343d844403549045000481e4501c41a40107401008010914071100720846080d2004c4104442a5529503420800606001001e14089540750b0726003040040980c00600f00e02c00c0c00c0c2c0c024544036801c000501c402000840c030000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 169781816 1250 169780566 169780601
    0xf12092c0c091c02030a140c01090501030204030b060f0f0310090218070f14040e010602153607050409200d021309020d080c0d08010b070201090512010b0402030c030a 73
    0xc1006503a00100c0f007a015411110440c0b48496600000341070000603040034121070100c08041c100808086880c0c0c122613000d07200c1c405032545031401142240601d0000800d040800c801080c564a403001000d00d00c018000e0511100c0d000000200c1c4c10240c192640f00c0300355485850000c1107140c02c0300084032500300c1c3c40e50901603141c10f160041038581006410740a22070380080c070b07201e040310f030341c040304c015005000c420303201c6581d140002513403a8544990381d103000496001250540048a684030f402d020403622660190140040300744103c000700480129920075110300244589072405800e41e5240111901003c2e0040c1c510f04c9400d10341b1045005100704000c00031800142e4541ca02c810701e62000040004000c2900d1000c1401d0b41101100174100500204c0c0d1420081800143d00c0042940c0380d50700a042c1e682c5000351540c501403440b000b404109400e00c288624101788070428018600c00d000842c20740c2d0110049000c0380d000780c4200110700030020400030040c0d010b008441180c81c00703007800e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 169783066 1250 169781816 169781827
    0x90c1e08040206070804050d080333060c07030c091e0e060f09031c0c03150b070204050c0d0c0905010e09150405062206140108040f12092c0c 62
    0x30038020300104020311076540420140140b040c01c0d0156006070002a002c15078403a114108108a034004440003808000b0007007084444000c583c44800c5501011401d802880450500b003000a400c5003840300814410035000201017510781d84001c0040150580001d100454842800040061400310703101490400c06071701d070343c550000340b616030000f148454604c013034036480520742c154030924042c08048800078a1150080910f94030072400704443c2d0701d042040c0c1710b800043c059450114811010066800d11040c805814942c100c42c0c0d226200700710452608059805039011190a02c0c207000011301d103201c041c061941c004a04590f084406c80e118074131454409000440a005881c2d01402a62500c022a02d640c4500070200740094440f190b084c441c0c80310700ea181c0c0083c80544503100c5800555150001e455020f00d1411340640e4019400300c2682d901d80e21101402c0e020030015408100100c0b03000154042244032102600c0340d00e0100c078089441c505840c0c05110740251a400000c4c0003000b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 169784172 1106 169783066 169783127
    0xc080a090e060f0a03290403050a030c1106041101020c030a060b15070201080c07030c0b0112050606040e03090121021b0715080a051f090c 61
    0x3004800780c0e1800104604040c0c240205904076400032010720100d09046e010820b080c9010f0102c00005170940074540c904a0b0031101540022004107001d89200c0e450301803102b60001c0c070325091122409110741e0f1910b903d4058002002c041d04800c0310041e0343d0081c000c208011a0060070b60728080414280003028004450f82c051207058440c0c680354803c01c41c0c3c400c1d56401070701a0b40d07462055031040c0c10745440d0342c0040320903000c1c040e0b4005c0b03c00006000c860303403a029100d150042501d0700898a0441c0c640440900051712407410440310320310818001003a620440824a8109105002e4200400560407180d001505450000458000d42d5081c01e80b002c50903072050003202c90307030383c0d50b000143c18800401205100140c5408045031004203590006a0058504448051420301c07289101010200940c40f0340801500c0761461074900350860007000b010751094001e000900460398 = true := by decide +kernel

theorem cover : BRFrame.Cov 169604316 169784172 := by
  have h0 := BRFrame.cov_init 169604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 169604316 ≤ n) (h2 : n < 169784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
