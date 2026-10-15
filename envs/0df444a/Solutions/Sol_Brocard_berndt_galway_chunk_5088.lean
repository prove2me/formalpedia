-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5088
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:42:17.163177+00:00
-- url     : https://prove2.me/submissions/af9f2bc0-57ed-4496-a500-ef31a71ca807

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 914928057 ≤ n < 915107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 914929307 1250 914928057 914928061
    0x5090c07201504060311031003030c020a0515043f0f0209040f060b01090b04060e010203070807140708060603030d1a030a0516080c0d0b1f030303060501270b0a021203 73
    0x1000b5660824841c0d4004242000000d110040590f070443c0d10400380c3c407100720307286800c58030b08a83d00b00c0b09802c100e03003045030703050f02280903903a0801c00254040781340451913a0300e0600c02da80c82e40c1040c0d20f8100e85c80d2620716042844e0b5055400b03249504200c2d0221400000c038890400d42e400003080c00010f5004075034101404244610804811030483c01150244501d1081800444003001c0c0d81c450400b00340c1c802c0c00207001451140d58082104401441100e00300081d81e00d27800003591140404a4010505c55802c3c0c80f51038041c04031a000f085980e020b400c0520b400c90110352139104d041906480d940c1d40b41c0c10840d590070030404041d0710000c00340485181c0309051038241c0c1e6401907400900110000308500042c00c94000a400821650103000b40905800681d40c1035180f05010700103120381040c454000007a40e42c404003c0000358007c1e40d0106080f860100094540c0641308103540e03c060314920f403001e280c0004a10042110303800c80704a5682e810364441242000d054400c4050803990001c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 914930557 1250 914929307 914929339
    0x41a061e0f03040c0e09070b0318011a1804030e13020d0c030e1e12030901180609020117040503161509030908070f0e0703020a0306150f0905090c0720 66
    0xb03180306621403d0214030b40c545a028921748544200d5103004a03620010050040f011010091a0030441d07035200e103404080d0321041c031400c1d601d2410b01c0c4158003014840760000d52a0210003000e6820060070914501c5c1441d450003441050b284150b603003c3e0328244203c0747e003540140d04407209078111000c10088689010401400361042c05950a100e214440c5200e440d1080300700e0075102a001c080c01483c5541242020325525000209090070f903550302c0c03209040c0b06e2205d84160343c803070748100000120308805d44000b40c0b20650a06900100b8132800003000700003600041102d2001c4140c090200303103070300c49150800d000321001c04001d91003030074603005c1410942c21200c0d62007a81c2825082e210890386030400b507074803407420f0320a10060a00800104001d0f40c020b030300500200c0c030a8580030803030607280d8841c0c407042480041c0880001d044510064a00b55102d4101000346c0411188812a130400860980007070117407000150200385d03840c040300d9440245200404801201070410815441106 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 914931807 1250 914930557 914930587
    0x506030f04050f121215060f03010801051f1809152003040305040e130f35043501090506090a0308010e090a20010905041a061e 56
    0x80e0301181c81c2c0c07140151141c007182e004513042d0058407103071180a0401c1206510003000c1d000140108280342c4e21410701d064542c40d000c00a10344800b1060302140d42c2d5242007043e81c21034000502c0d003a45101c0c2d1083d0b02e59480c0041d030f02e034000c4800c03404d60381d4541205001c4c0c5e44028800b150300207119542203c10160050741f10b40080c88006e06d142c00c412400062044010f003584000c07200100010310800042c0304042c1d1400d291504600015001581541156030f01660348850410a64890420170010314001041c6101d12400340421a000446040340e40c03c802d8090081e4015842c0d80910800d1a040440e400201084a068139485807038185404446c0da50080c2030318a02a5118011000060350b04200082e4041aa650554403c4843da19041c0c2a40c4200b0019010008034025603038804081280e80014012910603500800e10300c030010070003d000c404659000038019800d002c11711040400d41c19801c2c811440a4a4403652403201100d4607109135000000c100745018085002c010000c0c2c0703c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 914933057 1250 914931807 914931811
    0x100c030f15080d02011416020307141525050d091b0e01060c08030708040f080c1e0f100b0103020f07030201020901081b1b01020c150604061d070302130506030f 70
    0x94890f8240300300401c9003039424425100c4440b082d0340000c5550100721981d691030781b042c58416281000c28655030419a500e031130240c100a80d00c0114051403060303541c900c2c560040c4c080051030013101c055101c603011401c0d000c551002170040100e001c0304659090340020f81ea10717031b02480b07855002815019030903003d0480c0c0651121728460100100d8540d015000a0440702e4202210358110380d42d400085481c54001841102c42a01c951070b42c00010700d8800148c190783c8010805400640c9425412028503417444806005592110389075982404011a91000452001c030700418140070041c0143c001c1d11030b0f14805041c1501c005103003014590b041d40507220040d07090340c4104040c1c881e11901000800e4040072001603c00410a1102c0c01d141d000e549801086400c00150501d50300303640aa06040080413100300c5400b90404006242c80d2521452000e840e141c1e2040307104440c070f03e88190032484020105014140d001400003851050554420004c00008040f182c8d2880d02a800e09224102 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 914934307 1250 914933057 914933069
    0x60405041b0303270506071101020703060207050f0f19032303100f0501050415051c0e010b01180620100609020702180402030303130c03050a03020c120708100c030f15 73
    0x80f8180001d40e084c01d44483c811940020135050401c1000d8641d10001c1010860f114103500c10303c00000005850741c00a0507605000f200138007030114034600071a0402000e800c804200d80c20400b00f0f40110510703100741c0a800d541500d03041d0030000e0a981c030703908104200c2004480c0d08502008003d08484801034100c1030302c0c02d01405614155450006480380e0050b03005a454800b654010350041038071990103400031019100d01c0040e004d61061441341117035180d03914154030746d450f030142140f1560030031407606040b010000610842460301100a000440e22520442d0108819107120100042040900c80c00c017103c95040010690ba501280002e50080c40100d00421240f9200c068400750100b545125a4000e0050342c41e60f0381e00301600e00403e080c014115070352505803901001080301000000340e130701c3c8260014010740000c0410004052020801e40c5003550040c9018009840007040000d0100c031140b0340492a03502454094000d06540c1f402c1000c01450400d401c80020401030035101100e03e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 914935557 1250 914934307 914934347
    0x50105040210050c1e0307170c16152d0905090601080907061101110c07030b0f15010806010504080d0f0909020c03033709150204030b060405041b0303 66
    0x22650a09482900036600c004d10340d03400440b201c0b1000d031074415001c0071880c20300d03042d6841c20740350b5525001780c1c55505280c0c098541011030000c0d0814010403050703440441200699400364a0302c419001000b502c2d5a1500800980c945200b84501d0b000280c0310921a4110301c6081410204800401541c00e41c42024171811450300851000c0d405040a5400744010002800f503950801e081907405c004c0010500c078040d0351b5002c0070b4409151500180c0709054404024101141c9542001040c022020b02507080138041c0c04241305136040403080640a070942070804086c25951000140d403d40900c2d80904164010346500d00800740d4010303003800e1502078903107660019544603101d070012401036800601160f8010400b043c145813031a41c02d82c032050100240d40b0b82d030b83c2002c20702c44004411780c001d10032420780701e200007070400031807800444c161803031070504504003031039a01d4501204030301805060085540d40c02240610001024600c107d041100305071542550360718001702411550301407030340302ca4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 914936807 1250 914935557 914935579
    0x901090b1c050c1e03150402090108040609150219030509012d0908160c0501030506010e09040f0803090a020103150302101805032b03060b0d020c190501050402 70
    0xc0e51401c1e940782190744a48004114140304000005010190450445a50900401c2d08068130341d103140e600540c44690030303a1281007418852019003d40c0103054840c500501107054036981c00204a0391150300b00700e001c102c441e024140310103100c20a200d04030b05140001303020701200d00050482d5101a4003a80c0400040d0780e80d1000900701e6160709070609280d69080300211b04032056601120132440c1310380c40016800740540e14150158803041307010503281c800c190a0b4061204c10702c0301d04003d12007800c082c801450070b000000c0a004134282201e01c5282040042001e1201e0b1010603610154000b8807603680f0304003010310a03610f02c00b004040740024241140e14000e02e0a050f080310469501074240f1129501c9032609a400e01001d86002c43e412500b50400103103aa0100b01c070522091a24081c449540038000741d40314071100281c0c02006050609000300300c0c0c100c002080b5042800341070340061700c4603061006641041c120544480046110580c803206104c01944001d0040340308a45002c414 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 914938057 1250 914936807 914936819
    0x16050405182719060b0907030510090c020607051c0f0203190902030601050111030d14010e0106110d12090b0109022212031b080d09061d25030215090109 67
    0x244402541481d6280c00c0f1904241c89120300030480c1005078030551020030040f9000010910f0410200d9081000a4a0f5002d0008814000300030304080c01d1178030001e22101000c1c0c43c000c4e50340c0d080500907008100e000113402c0c04450004944840f010000300044c400c4070700200c0440c0181d04243c03800b10a02011480b40800c5984a12808607281d070b01170301501680c0c0c80e000055800502a80ca402c040b408108000109440e542c4155403140515454489146d41030641c0600c0c00d400503008041408000800d103c400070000031150030a9120f840d210920980c40d45840001e0890301d60010207511a44002082d104c0c8660094031400f841c548048410500107402d40c000050b851107054011143c4840c040003080c8039016610740c040304903c003003041c0f99055607110107550015000034086035840350400d0030003541e0300455100011100c4c02825448001c0c28076600c4000f101c0c41800d003241245400005103c0e50b03a0440c0c01550010407404103801c00702042800c03a40005061400603a8550012a003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 914939307 1250 914938057 914938111
    0x5030607030e0c0402043804080a030314040f1101020124081c0c0308090312010e0a1505331c060f030b011214010c09060201050105181605040518 64
    0x2164451303080c8800031f003080d0700c410203500101c0580c02c9a191711040104444503580f80148006e01100c401024490442e08000b02159079800104c0b600d9004001404007156001110800303050b0400a070710011320000380184d00402d180000050a52a81480e0600c60503011010b10129074185080d18030102c801410481605a1812580c010410904007000031034403a100312a0f01800c1d44c030441c0c0c1b50012204184403000c409074031400c450520360040081c241210700034040310040350a840e0700c240781880c002400b02c190b000c50008001c050689010164000c0da005001c4100492191603a150215030b8500c00081007a80d1544a003400c040c000103489a520205100303c80c1c01660a52041c0d0a210000001c400b0249055486081e11041d41c09007800030300c2890300d804006d0b21a03e4006190107806401c0d507405910a5201c2e080e103040110108510b130540c1a480b0f1000080c42241840c141d0054071180615004541c108042c40c81f41803d030034070520170740d0144004614440504541800001c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 914940557 1250 914939307 914939309
    0x60d200f09101a070c121a06061e07062a050405090a0c021515100507050a02121608010504030305090c010c1209031407030b06120a0f02060405030607030e0c040204 72
    0xc001a00781c2c03400c115518950340c3d0550a841494409468140b058441200108041e08103039084d07481180044108842042c000a00d0719260000d2400ca24000300011000d002d040c050003040440741006908202440d0b0440b144182c0c8030b20200720740384214071819000c105100420f00c0c2141da180c0b0f2884200d0161045d1421204010801001a52014112400741c4015845003095105084030b1205007080c9016052281e25117011072020742c029041002101d0b00795021840602200300f1021000c100003281c001312117501592a6074948501907400c0346811010f50001c241e0210003140801c1c924019040180511701940e0280a10344640c0302d001c0d26915201000e40c08036004203250380004c0e00c9001e41d003101000b181082002c10382c0c1e90315150b1310129030140d04a242e030840c00081c410401c04103207080e0080d400352449070600e05400000d40e030340d030181d460140640101c448010119a00c0c901105e01400340a0140e850f01d05000300c01030098881c101c00c0010902802c582020b0b00d007424400d680c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 914941807 1250 914940557 914940571
    0x1e010b01092411010507080402010219030e0d020f12030a0f030e0a03080705040f08070e1605040e280906060501180e060a080f060a062c060d200f09 65
    0x100c48031540118901c11940000d60b25050001c0c2c4036182000003420300c5920f224241ca5180c541e0a40360902c002030070850284c1603203002c0504030801a02090b4006e900001440303003510390410541141c000204803c00301d110103948803c0144090714000340100180c82441400e07200c4108510001e942034055440030300b66039905900900b02c040c0443d1207080300e04d42116841c18000e00e466240c0003480320800c5103821044042c1c0c0180f4080042c201102c082580c048030501e01c084141d80c1c030460040c00ca20403480742c0001c1032140408180d0307040c007074400c1014401c03060301205141c0e002c426143d0090200e66000b0b0700c44070725100c40006c255000d42144510240701d0000c0e04861400c01c9490304000350702410300c030341000e820302c00814100d4041056015070540c2000803c0d251405501c40e10603901a50410141c01c0e02c4040201c0c0202e60750b003044c8201000c010b00004c295555040030403420f000c00d107006480350041c0800da0383c0142c0c1c040c06a4106140548007124000407140600c40000c50607a01a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 914943057 1250 914941807 914941829
    0x50d121a0103090201120612140d0516051501030609050c0301112203080714060a060602100b01230901020f060f0f1b0715050610090504020d0902031e010b0109 70
    0x24034034a40c8030f80d0110f40c04510504040303071208090740800c82158000e0308101842403a00c1d00c090180101100c1d112a501c00e420010051222141001051405aa540d002c0d60121042d000010000c00b130107401c41103080481250015270f03407424010301400c2602c0007031307805010b243e504006a05040c020807050100a89259141c91605503130004142c52580354030341001a41a000310001c0e10301030060414a004800400011383c411322081d0030004040d24080c411407a029081102603004154518030303248032100029424202c100503039000d84445a01400e1980d1108107503000e25178200900890082a030807190302c01d6440c0d6805640b000156440002c402c00517000130400d00c841a00c050b400300c070700404010350b071742d007115040840d80102078119503010a000d0f0b20b40000040e4400c140d07000000b00d80c854000d2300002c0d0040e19103100c2d0700400e80625000650040e201c13805d90410451240c1c0034085455190100b400183c000c0705040c01d00056500b801c41c060415840380c591101540c50460301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 914944307 1250 914943057 914943101
    0xc010e1314040803040201180305060c07110909070303020d0e06042102060f04152615060706060f0617150f0603010801150b04080d080a020c0a050d12 66
    0x400161904020030350354415220510880308140c10720046014911400325283c80b07040a10015040980802900f21054250701082020a41c0004e01f00c0d004001c4024007640d841b81410040200c443c900030031900031640005020b0443c0001500104890080e42982c01d02e919030001201c05148128102c0d902c002c0070301090212440f11040680102492855000b4044c0d0030b03408141107070000107400207441c401090800041e1500c4104000e1842d291501d417800c20394200489088614000005010743c0b49000040d00e400c200040e0900041402441141c940d982898440d002c5d003801e004003094241c00c9070002451f20301501404032488559000314080d541d40c040310320079101d142d00510303a01041141407551f085d00c0da81c00540c0a040884000b140c4840c1200c00c590714104c20354000d845078001007004001e00f401c003003401d1aa042c020310346a0615152040b03020040e004003540c07030340b10f809036807807031010403000041407640940251941c011440042000508072100024030010300c1c550050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 914945557 1250 914944307 914944309
    0x3091302091c030903120c030c060b012106090e0307020f0105030a09060612021e01120e0f0d1107080a0807060b12070b22051c0804030611040906080c010e 68
    0x1034000c009014000c80d4512030b00c5069006586100c980690200f289140e082c424012408040e04c00c91099046c1120b46440d560380050002000c6280070300b4590365010150764170781c8180b01810441e10030441d0251a0120040040c004000f28421140b400b40360412031490070002101b43c4268a400500029440146100550b05584003c08585c0c082d1395030f201400012b443c0d4881c03140038006460010050322850310500c6017010b5419507c4191b0b1084182c004803c1e80d1002842611000280300412000400a2010f140c4ad01d00420354401340141481e40d00541d610071080c0a06000c01001c81d04a1941c1d07201a82c5c5995200b8409805000c040200002045098000078031000014050104440f1081301090401c5200e40101d80c0d00c1c43e0005e00022801c220686001d40c14201c584050085480c003800a85a2404090040f10046140007201c092101e0001590010740e0000710a1114006c10f2010403456485406805580e034500755012601d410300203102c8007d903078180c4030924201030000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 914946807 1250 914945557 914945561
    0x3020a030e1903030c02031207201603110d06290105160605070c08120105131a0f01140703080105130c0f1d0a0e0a06080309150304330e030913 63
    0x10008070150721040044120120100c0b0300381d840b2303001640e1480028ad0888011030301400c1c3c074200c0405030307902c00000f0341d4a04114540480807a40d0022581c501c0401d07040104641050820002c0c182500c0c0c62462a508207070707072180d484208905040034040000c0c4c00015a218026000c1010200c9180105d500014001d036010039040395950824444003461075a482605600c16800b9045613080c19004000508140054040b4044080c0c1e0500c5180401c520b1203604952a500144c8116205070601c034075a401075242c01101c1800b05d02c1c0c6550f1740280d00b8003410859082c824180145190b2403584012100c500c5001d412070065542c010f00d40480e960b04940c2104c40300c41c1c00c1c800d1121485014113985c4e603420540d000344800140f0044a151203030084048030110792203c191a0420004008642d43e180120204003031108005030301c0344c0b1203043c460002030231111a610b01c018040c004a481d0b1324002c2402207500d80004081c408003901c4040709483c1d0141e24081500400e40701148116200340b6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 914948057 1250 914946807 914946821
    0x50d0b180106030b010602162c27030c1005060108060d1b06030605040b0d1205160804060e030d03092d08030a091703010510030b0d1203020a030e190303 67
    0x38400072030764903141e8481049080c02a40700742c000d0381c050940700040000702e001c08001410032030101c60303001490708d10302c0c00181d42c0445411048011800010380c41d020904070001941c400300807104c00118041c10799035a039400400480c9091044e0101d80001a40760b00800b8444d0606a44007002500e80034184405140d00301e100312400300b21035265011013088020b182000b4981c55401142507880c01c1c090108031041840c0709400380381e030341d0507000102b0000010180540c8440c43d20740d944030141800341c010020310650062140a00040014040758460404174440070100e00761442d035907141300c06408482030101c005100c1142140c11660004d01d905044a2580030f0344e240d030119004030783e00c1c044143c1c4100e800c03620065a450400e4144004440e00c1003c0e9000c042249255504080018042712251000d003020183c4940c011405a10f03100300200820768800d11000d5029044c0342d001c1c020390082541c61000130710b40080e100c09040c0c0001d405490494105c2e0b0081382044586089001d4404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 914949307 1250 914948057 914948101
    0x40506040b1008180604020a1401110703080304060609020715110705010905010e0c03070b09090406020409050405150a0c0905040b03150405030c0616081302010e0604060503040606050d0b 82
    0x81c4078500310071911091490021101c0799600c1c8111460040890070440d9100500038015610040070400141c031106158015203c0181d1901c00342008000100d40da8146c7c0c80e4054994028418000100071441c40914040c40c031801c0144a05511164018201e01030a1005058000d0344103100000800d550300920100801142c030702d20704403454860f45d00b91542c2c2401100c0b280c1d510308510070502e0089c4065050507030100c024119103864014013013414041c20720194495100d00300031a0800c14a81e040320010940901d0a002a16207824074a444503074420596000550741000201e401070144910849d004040e120b0100150404050100501903084003940510601c400007005010f141c01a9200b0784c49200210703651001c540c4464180880902403c9950002c0440841d5207038005451036841100d4114490540303030a4001203c8a44600400a408c050001408105c480c2d000004601c40c0f40100000e11800760340c1d0042c03011203d045080036003041400808100340c000c05042c01028101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 914950557 1250 914949307 914949311
    0x10c1401060521011103070801060806061b0c010f140706020f0904060807060210050709030b0717010611010e06040f03110c030d050a031d1015090207050c0102070b0a0c0204050604 79
    0x189810200312401c0c44000c281400344490380151103005000d0080d224580407142541c0d0447c2800c0d4005061104180940300038410b44000161154941c001039801118010b182e40d08000e02200029465444004041e400155014160300c0801d000b0340e585048400c071120381e90f16080302d40e1a402c00a41001070800610780040081c45004d42d240d001d00005031011301c010b408450300d040400792519010601e2600c1c44c030704000800c01c116070051007801c220794028205400c50f03611800111455684401643c0356200700c1c41c008596554458410201008118001c0100e0344401011a50703c0c0030455000303140c0c1e0307041d00d030303c20000c0c0c1314140001210300d83d0401c035a20b1042100000b800d00040d00b09020001c0da0100305424643d52500591145a4880b1001025602800102a120343c02e039a445000380c0d88039010b0b8035044640d909017000800d601041103489508510b02103440b6060003206034014400c0b00310120701c900094080741c03131912564940070562101c540c20301c006042d000b007886034082c2e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 914951807 1250 914950557 914950559
    0x20109020301020f0423030c06090f040c0206160c0b07180e09010213050d020a270912020d0f0819060504150e010b040303020a110406050303190e0f010c140106 70
    0x600c090015210b540e0720003944d59256410300444d01400112542e41100f04907600e90300083c3c50720003090303040c0c8220003a00c907240c1d508610008140900c043ca511150003c0c0340569210000d42d0118001d8021001c00c204004079001000d01150800305031030000d4500001180454603190003022500100d40007000c140495555680240000441c104c92050051350005125603080b890400c1e040090802200c10049007240381e00440c008010500614204285d090280510071b05140501100000c0340c1509102c07080f800c0c42e1040811402e0b91548025100309562a03034068010001a40c0c49641540c88414076610b010a040300c1e10b52055102d40301d141c0c1d4400201e00c946030341c0a01840c01c4030900707003011810718010801c2d0a500d0140e000c0c14000c0c4d070601090001070340c003040491241d60400c007943d20481120002800912081c0c4c4903a0385072000042c143c507184245800180903030000c0d01c50f076111412000a02152440390034015001a0030b9011000000301280e000c00c0010784244000240b036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 914953057 1250 914951807 914951809
    0x606053f04051005010f24050d180b060303091f033b010213050126191a130e01110d0f11070f12030e0313030201020d09180c02010902 59
    0x50242a078065880350070180306011000d905000d1a130042c01c013422260700710342c0f401c44122080402154180301101d00050200b4401c0c1c41380003a03a0329443c1c0c00c03800b00503503040342c3c1c1a070040c3c81c0d980004841044051002441520b404400e40d0506100508000c2c01200d407002016840c020059004041c15038407000344080e0301c004800107810750f440001e6980124100700c258400f4005181c401d000310303801002078900080c590b1000c00103c410a0a1020180032a00c500b40b82c0301a05403c4400c1c0c1c625107104021003198444030000e00342600030f90800c04d07449440c0b075604610400c0d0b0b1140c6d400031840c10688040c100b00d03500034041000c0050000400f05500c505d0700b1025072048043d03a4032691200b50030781400c401031048803094603448003414503160725907844041c0a06c0a0741c000c0c0c8964100c91014040c01e0098000d520004da20000b035940d600106a10818007441c1030006034010703c00d40c6404400075000c1c071112005d845194001c0860403003c40440000b50484221034001c5542f00e1200f0001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 914954307 1250 914953057 914953177
    0xd050f1b0a18030c06080603010903120f1d1f0501030308150105070b070503090d02010b0904030311040b0715140912090102010b4f0c2d03060605 64
    0x180d4462002c5104c070604c0d00d01e000304030720800b0300f07014441d0b45004003541c00a44c108036058000d0700b22041c08580c00220325a4180200740281c5c00800d800d81c0981100c403080c4001c2000c00e048500c00101030350540c0c2101034841140d1090100801051040380411300e18807001c1c00007040941e05145c05451304402396109004480b082d201000860343c007000740007a1b21402d0148070a015000e10080215080c060000b0f001381002074006400d06645041c4c00b05000d6000084801600d26000e2296880b0718a240040f12402030402c0b0540c0c070351612000d40380b50b003441c5000d6400ba0301004003c01038129481c428034400e074890b038541e50540d981c0d8030343c8070442d40381c6001c420201c55008a46400108403c45668903c1c0341c11104c44480e04d40000c2da00000360040d0324401015030203001c000881c510300e03070030517500205015072101003528a07407039031a50907408c503138846200d02580c1e50038000c40b0b03a60901641c4070300405e00f0301902d40d0400e0001241c1a0510007001010302124654008916070f84048158 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 914955557 1250 914954307 914954309
    0xf120d0603120e0102190b04080c010908030702061005040606020c120304150806030120040b07300f2c1c03050408010e06010501210e01020a050d050f1b0a18 69
    0xf003090040310044035038060111424052290b1040d1007041e08035600c00010180092004040c440003107840103400b0001d60011003080d0748490215904c0c10075510103959010100e9049600503003402000c074480c10940184030481c0da881e00203002c00c4102104002c900c200c8002d2210303481c0310038080041c0980c21240d40d403450079990340301c1c1411410203005060a6449404802880f0000c0c0c4544000e0b141d60041107500f112080711505440c1c0d542c2d0301c0d2070340791030025400300c040c001101d50312508010540c0710400440d20403621800c6c0140002c40d010fa800c00c400d07800700d0056194081d484500c00000c8103501845050003040c2c02d42c089003014a540040c00a840d0550010b50080f6085c00001c90902c41c0c5801029484000e0189615010000b00708803040002a07080d00a00c041c5114002800e4000ca041580002c0003135440788403100008013a0b810004041005a05090105120716219090107001c1e00f00500320500d00103c0b201b4600c40743e4056040d560410074100300000d064602d2000c980 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 914956807 1250 914955557 914955593
    0x905010c03020a03050c04050607080304080c07150f090609120212030d0e0f06060627030d020607090603050114060c031b030a031a030604030318080301090c0906020f120d0603 77
    0x40c0c40c0c0c4080f080c01011038000500c0c0b0200b00d4800c010503c40e07580c03135100b514421684610300903580d949510700403c1c0c6004405a001540c400c42001242d6401120b800296a41c12503855245076604a40e0444030390b80c15100310b0340406c90b0741ca000d200035001003111403103190016000040c2d9000e04041e0a1540d4801011010410b9a840e41d240300c02c042489007039031040b41080148014180900050080c2c802c01c4500e0309240c008455600303040404201c18600098001c00b62101080304c1035010f0345408003102c007280041c0d0303142800f2600758040e11807207041e220101294040d0242030f00038041150700c99a02000c09120a101611503031149d42151080442440c000d162200c0910102605940d8511201c1c62202d11002c03000c15252400181039a21a40500e400708907600d05980106404020301005015220000000310340d000498004a2206c1c40c82e90b00c142c601d5540d00c0003287c590207060850800742e04003c032503103139913100840900003906e4001800102150b03281c0c3c880d9009440220a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 914958057 1250 914956807 914956811
    0x130e0a092114071106160f0605040c0501230f09030303100918081614100506182413020c0109030210020c07030b090313080609060c0f030a09060905010c03 68
    0x258194048504210700d40881101801c0c4212661145900128508264001e610111b0080c0382040403400c0840c04030b400900581d64003615080400203403c00b00d600303a6001c4446800010355520556080c0100c02004200c4a450004911200102e50007802d007402040e0041c403c02410756000e000560146000040c22030f01c881c58030308002c060741d0000188800d400140c203803039008074021408484605944807045107240b01d16280c540321000360901d540b0b540d446540401100d4460320750000380100c1c81194134040204004084441e00201118410f0100d0000641315000c0c0c0e207001c264202420000700f0324900c00e4801d401e5542240c221071800c1c15660b44030500d5900781134040c80200210440d241c0154900780d0312411043d0b48800c588401440301820350b0002d20081401d10a0f01c03407074404110a41c242c0707a510300c919030f510743c0706888840711030045101149a904c4000f00700c43c9542c880c01340140c1181d84160000d0010000258162410b41c4ca4512990010344288548049500f4540740 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 914959307 1250 914958057 914958113
    0x16081b06040b1b013e0f040302121f060320060f070c0308071a0708040309050111070b0d0c090602060601090302010e030f060f0a0c0c05070509060111030a050301090b06130e0a09 78
    0xb60710305e050121400d0f00e0740c000400080b8803030401c41c4100d07425a40c05480b04084a0141c001c0c2074600b500000005260004803460f01a040c030081e002582102d002c0c0b039845c120fa81030318107840e034108501104264002c0307042146060085016014080c014080c1c0206011550390782c1764000d080e402070b0411600ca6107090000c200380111100d140d03800a045192440162802e0b6802820b1007205018450500c210783e07415124200013000240c015107000c1d00b00589072801d03c08043c020b05004002c090204842a8010645a100241c45842000141e4840b40303640e11b181c005449800905010903050f000d0011610300312001000258081c40380701c4050003151038603041c800c0c00c890a2106003010001c1d21991640444c4000500205440c0304071100342140d1140001a200c0001000184510713010200da001c0c61280c010b0041e5040b20640e00d014800c0e82c07540b03400c100451142d10703a4102a000c0543c0180400000080c0c2941d0005440500083c076210a13101d20708000350100c4136551140303000351 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 914960557 1250 914959307 914959391
    0xc0c03280c0312020d3201080d0c0605041416030b0105030a1518170d0f09080711010329120d02060a0203070216081b06040b1b01 57
    0x2414111202868007400d6004280d41c0280805151542c0b0309480b90007003643e54402c0301d5684110350809814403540c10b100415052180c48608004214101510800c00010020004a500c04010090b82d5500c6203e040f10742d2800000d0001a00549904501000e490702c88030341007003045c15905108114040703907442d501c0c0020150105801c4903000e500302050050001e03203401e0420ad13040b0b01000c000f0614546c003640e1011000d0400001610850f000648410000311980003071030468103c050610041c45d0b28002402614a603000051409004100b02c1003c5030715010091464241403401003044a0120117841d6100f203101c155410400c942d01e5090b18520304100c1e084140385014016158102c20b20001a403260380c02001000f03541d800100041000e4401d00400d080441d250101c2880e40e078680140c07980e10b80070701031240f0100001d007100c07040780d00c2c055040c1e0b02160800d4503c43e25000060002c024509001e01c90806070b0364075003c141d034006c60104807c084100340150b5880c90b02c1d111070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 914961807 1250 914960557 914960617
    0x403021008090106171e0c0607080705070b040b0f07060618020a0815030d1b050106060801090e1219090308030a020c1002090a261b030d020309060a080c0c03 69
    0x940a441da60170401001d001184000c14000c0d082c02c280101c1c0e620411401d200d141c1081e1302103800710351110300090000300f0000c211000d0321074140121b044075003003603c0d142c00e030315103110b90300480701e1a540901901c003003a00d0840041a500340728800c003207503680d5100256000c0c4a4a1044002e0b0303580c000c01c228000c10b50000407154022041d0b110102500141d002203a280c0070b6803d400010080c4c014040d502d0010009904560f003940100208851075507142c009000a0082c0200c4103c00d0030040140e22000d07000403131007005180c44a03418501030f01c071031010072880340300c1c9400310a1207001240080450b50b84000b6504c120305aa00c09680e41400d41480d40c00c192240381807000c41407042c81000840d031201c05800080e1a043c500007100c0900040c80a031b400c0245443e43c1501d8070403403421031003c004d1250240c0100c0e0b402d41c00c0340c980214000040c0d85034002c4007041d0303030000c106008401c103a43c882c101e0b081e04200c100f21143c0c600b1604036281c0703040d0f81c40305010000740c0c29011108840003e8031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 914963057 1250 914961807 914961809
    0x7060f021506180c040b3403021213030606030803060102071a0307030209040905030a1d0604030302150a0612030e1306060c0b090c0409052409070312050403021008090106 75
    0x600c12009207481d1450024003140841250f040012288000184207030031300c40c0448011704000e40c3d105490301585a540c01c0c6200045a01207105018544140048421080300350009681030f0007a1200351001c5078204400d4101c0203000340809540540000404c0c8280300703004c05503004401c06642d0f490004006464150030f81c0c031a00003c0074103154403025030045000d881d08048680b4000d0781d40c000c803900080203803040110140240c00001400701081e500280d103030060016030110480c021a0504c100901401a88406805a0800b41042d81c0d03882c400403400380c1c0201680070010316070307842d4040316804403d030100c00c070040350a00000c4445441c000110000d51168500c06101c19070030481c000b891440700260060451040401003440103a051104000c2c410b0084c00410485245003003107030303482c0f06011980310711421803030700288040e603c01c008030f21914a18009219052460340d0710b02c1c5c4620f990b080d041c100002400003100503542c3d441010104070b01c507aa00710040c14520b0001c0c1c2101e0031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 914964307 1250 914963057 914963083
    0x708010b0909070303030b03031c0906050906100303080414150a0501122a080f0c0f03060f04030c0f0602031003140a170702040902040f09140106030c0308180307060f02 74
    0x1c4200300415420300088080a0f66070610b40407540c0e00003440442d1941c0200c900c10303508141314400d5140203d800b640080030b02e078000c101c24012503c5881c00315413610815690f00c0d214104506082c00441d00a02a8540040c4903882040070300c8041c101c580d041800311409076010300994424401c4412281c020103014041100d0200c5200709207a60b074060f500300c81114900386e01039030048450106941d42c03500c0e0060a102043c0c5445107400c4c040d031a26910000c80c407500c81c03070803e000341071907040000b41e0030b08c603d00701a01d9801c0358031b642d1005d42e103a40000e0404c803a4441c08070042000a001400514042c034106200e00002c2c90552408080e074000d49606641c080d4400c81240780415544510403801c0035003000101d680c0c2c020fa002040c00703031401c241c019404c542015030b040b518541651250810300d0090900a605900c06030900b0300f40c5840b888050309064546800b4004155244001e0030007145541c440218102d50f07101282c24482580d004601245884412034011a01802468141d0346 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 914965557 1250 914964307 914964319
    0xc061103041b0803190e0d05060106020706030b06252012010504110906010e0a0f06080606040e071b06140f0a2a0201061a1c050f060108060f120708010b 67
    0x109101400b07607280540300d64045071803100f01c410b00120703000b80d049a0030b140002d49500400c031f24505045541c0c0000380700d0100103114114000900c0f51091145407802040201010718242c00ca0350380c41500383e4100381e100189a51000880000b42c00380564040c4c442c01c5a6015032542c03141d00401804c040028500d26140e4104420172000403e1101e14800303000c01101c03c1c0c012600c4081c012203180b002e00c52540c0d002503511201246405909004a044031a1613584420036526802403000320f009503c19038100f01040710100d01c04a004060521410100704a040c50100b156101e02d401d0b50b442640d0540c9414406007409000c502c3d544a0030351201c140041400740801001d030000700d401b410051401099510a03884110358803c0d003041c0000c0601010400b40104080002c00c2e580d48a0042c1c4841c0d46d4008510001100c0710307005003840780115890401c03113560b41e000190707801030340140310070360040d40c283c0780d40800c0e99400d041d07003140104900181700c034609148180703084850801030180f040d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 914966807 1250 914965557 914965559
    0x604081b011412040c0807060201020c0124030303050417030c03040b071e14430809041802120102090a12121805100e01020105070801051c030c061103041b 68
    0x2050b80c0b800c07a102012030750102070039580e4a0030502103441564200c040c050142400004503189d05401400b04425000c00030020048490380801c020145219211072840c011a400c00120b8043d42c0220b5009000d201480c921032600114000b60b64421665683d424001000f440180320304000d001303901402504021807041e0f0190b521100c0500b00740ba00f102008425075855400d01d80403015074540184548460030280b03c51071520000d4000148940703034481100036010045041c0074101c0d26110b82000708540340c0301001050001804641100281d174901000a803001626965280759260216800050712682c0800400c40c80d0340e43c60b804000c15a400752807010104080c01d000c0e00d201080c0b406d0040a50061080410855040b0390086600c800c1000956006581100f41c402e07660500768000c100940d111501603500000c00e000c0d868210006102e5500c080c5411822055001e01034100540280c0d1203641d650141c0c1c6010248128408011082c0710070040d08201e8054a442d49a060107905 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 914968057 1250 914966807 914966837
    0x90303060e130c0b0c19050c03060f101809020a0806150409080a0e0112050403050702090108061501051e03010b071403041202060901210608060a2013050604081b01 72
    0x3003031244c025000f250000158242092008000080124503100c1d4004000089420042d480301c400740348450081c0100400030b40e500d51410511031007440841e00c407281040c10000c40c820440003061407811440e585081c1c0002503a40c404000c4003c000c84170061400d840c0c4006480005103680401d2030080c2d0500c9000e10003c3c0c0208240c6000c00d81030325264402d00380601c01200e45c00c1e414045182d0a62418041c84141a1702c400104282c07402901d016043c0e07640c80040d00c1e542c0b03030100c4180102c14410303100382c0324540c23140c40142004041d251040c4180740174080d44a00c198401ea010300d440000c0001c201003000481c03c035100c00b0008081c042c5040515120340800c03100e501c003400074403400700015011110fa01492100520003c4281101c07040c0b11030615010040c0301c1760040703c80c0c0303108240024142e21014000d20440402c00044081e40e8900001e05950640000150541012440d6804282511108003520061103504010041c1c003080302203a0000221002c0e001d4104401080c90b1601 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 914969307 1250 914968057 914968073
    0x7081209030a080a17090604031403010e06370503010b040e070902070609060e1f06061b050f012c03040308030c09182707060c03080c0d090303060e13 66
    0x401ca4000c0001941c8a900c160f007150080610175010b0310001160f0b050002c2e0034000075283d44190300c41d45a00c8a030001c0b054101d0303400d02091107000d48410140c00042c00074101400c10b4078a80400311140f804032802140800c4184100755160070003840055001c0155141c24020040d410100741d4080144072900c1a4194542f0a41d0180c9144290006413110400215500000400350002c1c410800c0504119505443e44840d06074040319120300d4151103402c1c01903100309003c9030b600d9200c01c00c00d1118494060a450400003007070303805005241480058140a000d54441a9850b00310724610080140140d06500742c85100215103500900c414000290310000b140d4100210180c1d8039100c18040c00010086001e94081c507640c20690414411035050215031101810144039186513040d48e0105407a6441c119485064000343e405140700d80401e0060380690707080315040e001549805148500c050035140c210600f1000a55a0341c030400a10900002541e084150300c0c1c98079481d0301c250b40311004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 914970557 1250 914969307 914969323
    0x140117010614030405100c0306050108100b030a320405100509070308090f040f0e0c010507020d08130308030403090e010806040f03030b060d050c030405010b0d030203070f0201200708120903 83
    0x2105907000004c03605100007001070b402035807480031080c4518450440024050b2019104907804601e039540468000072034422284142c0c0d9103101468110b90b00c135031a000150541000c007d00c2c2055454241c0e5114030b070028612460805048502145c0c10700d40b03003161910100400c0140c49924040a20101820110f10b06044a0300b002405407900c26103400141c8403201f000b00290710030700c3c0a5089505035a0390300300280c1000c420701950fa034403000c500151014400d141c0c2c0203500c070803c3d80c02c139070000380c50a000d800941c200000c1084000d4030b943d0781540035441079900b60040380c503030350040000e1001040c807035001d84450000303800f407401c00c2e681e81440100c45990050030706460b99070090312502ca81065031541d94198000340704500b000d0408500701ea0003039600f41d5683d401c210a001d03041c01e05c2c00d04040010781c10b0b80114686441d03034441d036407082d1081401700c0c10801130281504e007458614a105040800c100f004d04900380c5440030580c81c2c418120ac000c1c03218a414820040203a8003c0313810300d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 914971807 1250 914970557 914970587
    0x130e0619022101060f11190311060f060103060611150405010605130218040c1e051603030b241813020d050603060906060a1a09040207030903110f0a05010f0c0204061401170106 77
    0x94407c17891400703135021000c0010301141d5100e01010841070305520590756029880030f032000c0001a84610088644940c06480202c2c01d900400e1529000ca1011044071383c018050380001503525128030008070640c210340da6600d001380e004601030405220f020b011502c1c140b41210304101840c1640c02c044c2501e4032000390b5089001500ca40248606c0c081c0049881c014040082c001d012805e514000c0c00411521011a01840c00f020f8500c141280c0e0103050f101c074184155a407818031140085c01c0307070080240ca107801d8100411890810032101c050020b40f8140340300e003c020030140f901009040c174204c401082400c0951141050041035114503102100382c82c00c00034040c80340e02600809141c140700c0e0000041d005440018a00f09042e80003031890103492090103e083c03401507040400c241814080d4119a12540c088810403080d802540c100c400e480c031609040300800110b0300024110b8001d80d1003080c0d4510709540e002680e41c0e2144520583c4160350080c01401d5041070310040c12606a82c01c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 914973057 1250 914971807 914971843
    0x270b010f050c0f011506081008120c0a052d010614040b1c0302010c0f03020702180a1d070609230907200c130e0619022101060f11 57
    0x218034103030042c09821141d5625000174007900c0340120709825010103910070000020070b2000440d01a020130f51000e001c0b40c0d2000001c04d5084101c01c940f541e41d42c08982e14110510400740e42c0400100244684036880b51881c2d0000d95210700740780b41280c9176030109a007070a180d03d0480141b00040480540c48180c40054400041c00700b43c62010421541441e000c2031043c142001c025810568150003840c00c04440e5641c10303002540c840c074240c05901454400a40c0441c0f00080726402502d90307900a40e01c06d4400c0e4002c2010401848107003d0320100440a04185c0c21281d800c0c0102c541108000d8010414a03d00c1000c4500841106000b42c91160103c0d114850220104185d10710071158490b081c40c80c0404001c42e8642095032643c0d41d451000e545020b40d00085d1141c00c1c0546900c80e140c2210040806801c59a8401c2d42424441c2d03120040e220802c1c1d0300307005080b010074229440c3d1f200c1c99401489000c05504040c005413007521610244000c00540501c11a2007240100d55100007a00040710 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 914974307 1250 914973057 914973067
    0x90f060a1a0910032604080a0515010e04080703140d0605010e031b040b0a080d0c030206070e09070e03190506090601050d08180630060915090a021201270b010f05 71
    0x1764241d0500080c108070901c0c101180106018002186241d521407080003120100d00892011100d10102485010a074400210000d13010614240040c4002e5104c1d14201c0483d940c1c2040c1010700303801284183d4019680c40b4020310065820610400c0c0d03d480c00c5008103580d840409035560f85145600b0018002c076261350b034010164640c0b10780d040c0038002200070794011072030050005003907440443e03054005104410100307480e240200316030b0010314401751145400e40e0b03c0c030006644121400307107207603014440c501980412803175031f01480a480303120303e01034042030800b002024500341307047e00041d201d42c10558208001418034400c0701c081c84401c040059000c1101c4d0b0000d4070038003805503040c80d0000310040c201080c12801075840307100b2084241261280d11610705011020204a4110201c20391070001c10a813481c0140d41030307610803115040035107810100e690760300e1140002c1c0c1c030108203c2805044001c08503105d005400c9241035a1808002900101c0c0009260607a0a10100c05002001038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 914975557 1250 914974307 914974343
    0xe1b070203161e050901150e0307031403040810050105181f090e0f0d020d0e060c1e0d0c11010507060f151815050108090f060a1a091003 60
    0x1110034140065400400c0301181e0f1030764030310b00b0300d8442c40051500701108580031406242081a050603104e500b00103445c040d08400059071880d500020460b414803803541c001000426820241070074a61a001440d10760345081e2005113402040c1c60811449800c04005121a88510919142c030b1520b591000c0810b4480403242c980c071000d86a0140840924030102040070718003500400400d008a00c00c54204140015080341c4070341c200520f1b8001a000b0154900325184a03800715000480014030f03c510f04419801c40600c1d0180c03005e1103000c83d1450f001d41001c02c6806010392000e140c05030500a040d0720b1560340310a2140c011415644c180500480d59000b030050b5980300c02d1004e0fa0221301080b1040c0d0f01900c605c1c04180501c104c03910409070101001c0782d600b0070702036402e9080b40d1000004119003004d00560350301070000c00c9a03150b840707060076050720550304200690050043d07000006101b0b021901850303001803401c1c00c00c0e000d44440c0c802d0080021500701668112501b0817000d14480b4140a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 914976807 1250 914975557 914975563
    0x903020f04050709080105040f020a091e050a02121e1b2b0c02150105010302040f050d171207200d0c0305091005030a0605040504080a0509060912030909010e1b070203 73
    0x600140c17501d6183c48108001c1013140c988800d080d070b000b19802c01d841a40d07441e091056034052039544203a0702085510501e910181e03042903070401203000300503081428840b0000c2100404036100c115641003200403c2040305c049a0041c2c100c082d14110f1005144508800749032441441250300e940010003a504908030500715005d40c030106041810f115403030620100075600c3c01c40360000c0c000010040000500c6600034401c071800c03541d00c02c0e86004843e1400341002504c10020905032001410096072000440c14100100510001c0d41c0110283e414200c100600303800d81380001e001061044111050070900000c2d981c0080092407505100b40c13581031800f108d0a024903041c0c25042003000011403075864000c0e01840c40340c0300c2c0000c00c10000e85e8a00400c81a14010f580281140744100040002d41e407042e0700070990740300c01030702441c5000c007400041840c08101901740292a000070441641e0307403620781d44080c01010701d4825a402400c20400d441440403031240c0000807220006001400c6440038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 914978057 1250 914976807 914976809
    0x3110d17180607060c03050c0c07050409020315100303020705060703080103060c020a050708071403011a19180507110609060c09040f0204061e0f0f08130f060b01020d0903020f04050709 81
    0xb60156890f6500c0345041005426100c5643c0f010a091000180110000300f0a80d00049542c0008004007440d02090000820a03140b090740c0602030400c05a4502881c0d4120038025045d4441c08840c03a40355080c02030034407100d900840d1003604100500c0300402d6006181505481c1c1295000500c1c405105042c1d18040600d80010094000c5803000a0b041c50042005000c4440c441c0c00c69036a055200101400c03203c1018651440400700807410085050072003041c0e905c0c1c0c016042d0740381c030903495407110800b80013904841c040c1c0c0c81d124410807038480d0740f011610102d0314440d402003c40d400d0000740c654540b28000c104142100c008615558140d4842d00b0035096011300c540115555603d401c0010030380450016000e1005203c00d0f10182036612408280c100c8035019545e1020003911501c045664400150099455420046e207040c003103642d41c40743d078041c03601c2440300188414001e40068100000e038410f2200f4003d44100800158803040c0070090840070480d000551580c070b1030710665003a001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 914979307 1250 914978057 914978059
    0x215071401020912070b0706020a11011407030b0418110f04090b1609081203040246060503040623070e010201050c030601050d2007080403110d1718 65
    0x4164a88582184190b00410301d0880c2950500c6006480c4079490b03035103040380d01c02c801c2c101b8030401946020070036a501a21240d001841c103003082d2500d15403800d00791400e2034064106070451009110700d0301e4241c03042d0360b80048165402e206101200402030511441d980001e05540040190520f81c1d07924494814001c00008004102d00c102a08288141c600c04848402c007103030100d01c5281329540100c2d1036404590303056000300366403254181c1c50040c40d04090002c80c1c100500d8214580110410303c92111003003080202e110b030034080c3e00c0c80c0d40351203040341d620361600c5040d4003c18040154070400712a40250064004070700001858480002e5202c121540400711180380309111250760311003180000d6007000d81c000d00a0b504c4010702c0f400e13940b0060720309901240d0104101000700100b604080e60401c4044542817050384042010b060944c00b0250440d0890710000e0b0600070800c0003490f01c00b1401003651140c20018580d9244600c003051128400c591201c0480c059041c040700030843c0f614140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 914980557 1250 914979307 914979323
    0x14010203102301111e0c091b1602060d0e010e0c0103060b0403060908070503040612050f0f010618080d020c0118080a0b04060603121d03010506030c151207090e010b0307050304021507 80
    0x2905200c5444100c108011403140c0c070001d021234420000d100003003140242c041c0041e443c010002c1ea1019025480202c120303000340e8144906265602c0c240729040d085194080085600c030b16044038103080994200400b418180361550501c0b446c903051054409580c0d00c5100012402c0e8230341040c100f54007565000400b02d00c00003a001c43d0007544211000d000c1c1200312400e00940d1102030303035500b000c00c040300c074210810800030040010030700c075051001a00c010303a140c40c1c0401317071134080040c00c1c581c01c00400809030f0b1100b40c60010959004805455150181d086e0106403820301c00170359298420610701a04003e90701001c00d0510000c3e80c0420019903018005801c0400724500240200a826500c0b090008901f00c1030f00c100d04040c05207d1050390f0007009440710072001130421014288001256200072024403c9c45040199040500c0c001c40d01070300d9040b00d03a03142110852002ca0305801c01c05a02c40c09005000d4615004410760360440d034101c031601c000113004a43da030b4241c09820700c05001c0d80c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 914981807 1250 914980557 914980603
    0xa021606051909031e1a010f0f0e01030b18150f01030605010b07020906010f030b030114060406152f011a13060506120901091401020310230111 63
    0x10707044402012000700076510150710841d050016166003e079440060300d21143c3c1c00c22540c00b000c5034001e501c030091017552070280490320fa03080c01201150980241c11500d5810009108022401c2d418000521b1903607078090b65581555542d24030500054211003807075100c4e583e0001e2203102848070070136460034272641e00c8403441c01d8100004450310030300c01038a00d18903107400410300c54072580890710510f4001d80302c000251203013001140d4640e90b141114040607034604c481d43c01c568084c000d044e0391510080c408807440c20b00d4001c100855401d6800b14034420201c00318aa030454024440c41065021a002000010280344641d05150326176000d08007107501c4d00c601d081c801841d1007441050108142e451500c48211101e0050850702c89000c0c840e84018103010f0700e450240c0c042034071507010b40303004c00100b20340381140c4d20003642e000c0040d10f404554350040204650491410810002800401401c0300c2c942001140d04070a00c401c3d1801d241000741a10020742c4821040146440040c40c01c50003580329 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 914983057 1250 914981807 914981819
    0x2010e121203150f0f0603240301060b0d050f10030f05100c050703020c010905060405040b040e010e030c0d1e2610080f0706090e0709181a090906010b0a0216 69
    0x10f0000710301c0c450700c0b52840880c950b4160801c090070400e1514041c1002d859916002c21120b5801c079000150540804000c40c5400c4607182800340c20000e000c207101d0281c445086d00b4036a800c9d158010720b1ba10404500d1010400c010710f0303100e50303902142c1d0020f01c82005a21141413082c1080d03c1080610811802e14883c41c1500b54008014887d080c026800e07548180303042c07001165092031034410075a0000c01480144814030700f03584440c0411074018000900c00c11032202050955000010740d01c1ca42d00040341c032000c0d8840a100040b0044082e26011800c030303440d529262200c103404d143e01c0d000c100707503c0b040c0c9442160000b448015500d03444c0004007070707180505000c0c0398000280518202c50042c07c40500140030300013103a100340c0c0c0c0383e44c9804001c641401c40440f220700004240d00c04000c50107800080c411030710380311908290394044002c15014040250707007200c003a120440d540540d5450080040618000c54600e05644010603495a16100300004034500807441d1811032080414002c00030386 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 914984307 1250 914983057 914983081
    0x5090a0213050d05161410030e06152101020406110d02060112030c0f05030408120f0a0e1f05120f0411010503100e010b0c06010609030521071416090902010e121203 72
    0x84d68000b1950001d14940695089040c0c03603c3d85002e1042b6404200030900c1c40041841031010414041e080040036800300641035001c420307096842c1c01a0354000f605002d029400041e40f801c060f0594001c0c0036484400c400250355900522411403500301f0500c21804051060000002c800d0300300100e9103c0b03010504020391685d0051007116001c2c4640c1856040c002102c83c10380d8070707110400e8001810300f50403841c203031250746103d4003040c3c0c050300517091314240306104981e290580130141ea4664544034841ea01e040300303800150403041c8440351401040700013508026030b808a00c5081ca032441d01c0340c880303081c903900c84038494100d105101000c600101c0c50605120103400060b00d0001114280d90f83c0b00c1e000e45071481345000c042c1c01600310103245100d18042480f440300015504512a1074603000d0344451024800c0c030b0285101681000f503c03050501b0944202d40098041d003a001c001c00e2a243c1e00203424000c1e00005103000780080d101480d5002010712004201d0144143c0345580d074038080f031030240f07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 914985557 1250 914984307 914984339
    0x605090c040f1202010c0209270a020d080a051201061d010e0d030e0a08032808040510020f0906041d060307053a0503070c0b030c0d0b0f0a060905090a0213050d0516 72
    0x454100000c9c1d42c220224400103200c10025009841e001d80d145158407004420350115000a0500c9401c00500388102010380c561030003004641d940d103640600c00c1d09426040203403904d616042103603090601c1500d5441c02040c0d003060f030780350902586c4119100040780a00451340e202d801036001c080342c03120017407401d10341d00d81045034584034500c01c8100010003070b50111001e55001c0c2c80341e44005442510100319130700505071000c0084000e803c140240c800101a0750042e040309403454003000d0fa82c0c0740301d80e010408a400400c11400b404030030303041001055450707264500620390100c0f0a06802441c00000b407042d00300c4800c62560303465000c1c440c1045a901c1d03100010858000c200c0c0ca0001988003489030569008014150030603241810750361030303030020f0304402c510142c3c004040454103102e47d8400603504014549506c9000d070340f516240c2003180b15807005001058460041103001864040480b0034070540d07030222121494100903050039484c055500c00c8807110444d001c100803446801a0310400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 914986807 1250 914985557 914985601
    0x10603060b0312090d030207030c0311041406060a0c15090b19050105030c27010e070f03050103020f120a08070b100b0918091501090605090c040f1202010c0209 70
    0xc40007801c40c005166a8000c00311040a8008092000d100b5614001c01c1c0c001c11180030344100e8612a880c0d0f207130880380300d219910403641000c40c030182e01058103007801039159040c1400c80200b4507107420804600248603868242c01000244100c92080101c002c104000d1020351190400c40c010031403502440010b01078800044e0100f84480c001680700399409050306907400074000d4803a20301c5001c14000503001c02e03500300b501c1e4070800e080000500f041003190750007800c89540b100c0c51410452006801c1200d0745400f41c0c10103040074014005030b142c0100310500c0401c280c500c004402260500d5a0521191030310040192200240e03200038040d450000e01d0041003001101c20409640c3d52031151288a0502d40d16000a15401c4804e0000711040380306602c004e101013503034040080a501e80c5081b42098100300e50495448005015509044014070780c0101c070021618602418040002140c80a0b84100310300307942c1c00c1c800c481c2164407400a05143c142c1c060310121007400d00d6110101090400e0042c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 914988057 1250 914986807 914986811
    0x82d0103021216090f02090612040b1005030304052701120326040f0204021908040b010605120f0a0207020a0305010e060c0f0a080a1b0f0e01020111030f04150e01060306 74
    0x41945540101c2c061014614a01036030707030018501350a6070050060703984080c20044c1d080c0054540c584a1800414040300f41e0020520145080e24004507907400140c0000045000742009001a031000022142514001c2b07a81114408000750305a0781c12800072040c4500e24080400010900c42e03071200a04150711a0b2109100c02244603a00181c0300290115100c0c5240c40c0c03008200842e05d81c41031f40c01200c1c00504003515144000507444d42e800c0b0b4440880b0002144142004144603c81d0300d00390260007a490145c0c90408401014882d120002c0e01d0745882c0c04610010070482c05640d41200c0f0303d603a01400b004002542da0811500134168012204007900500000481d2001c90100700c8240f402030100050410140c088211200c04004003440303400c65890f00750540d415000d04030003801320504d0383d0f140d0002c502d03800020485054001c00f03a0540e814206a40d02e402c3d40002a2580710307019140e00c202580d214201544188000f000e4a0201d628090800d4604001034001074141c80c0200c0e41 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 914989307 1250 914988057 914988079
    0x5030d0504030308070305100909021f11300a020f060a021b010b1003091e0506092407320301050f06090a060507020a0b040807060e01020f070303082d010302 69
    0xd400ba40d4048a003150142300302c2000344a0303003441c1e5020f030b52002c1c00078021510003880d40b807400000c5030141c041d090201c1c4095103900400f801c1000304c03030700015221070591010154247d071442c0c2100d80307841c0100014004511444498405c000c0e40e42c031248450116040c80c100000042e001f94480500071480e90041d20b501c9005602c14000c025011902414203200c0d008120021002401c580d5030444952a01c2207a044013038007003c1e41c0c02069400f6101070606410603619042ca003c0241135118030071a50380003e14a5074100072072050740120941091401e4443c40340b80007040101100989160040d003e9124182c1000307100070390f042c2c0d003080da10150030540790350410260b03004012600f503000340090b8003445a288290040c102883c0702500810740203031a07900180b110380058100366956440030341d0400000f40d02c6080103400030303002c1c0003915108041500d8075489a07250700018061103d064082010351700d06010296505552101310820300041580c4030410580c2840168070034071610314 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 914990557 1250 914989307 914989321
    0x304120806010915030b041b0306120b060402070f08070c06021b0904060b060903070b030601030f06080a171324050a020d1128030311030105130b0a05030d0504030308 73
    0x321590007500305844070030899250000078152914103942c5a810541c8800c0c121020752194002c210b106001400010710407403c10300300a0407102d00d0b40c0040c0d56a0241c3c803242c400b04154092003504103034255000f607642c2e4060709041e12000d05011008012210001e03c4100780400204200e050b101c490342070300c1007129148240c1d4540c4c8500c0e52125031058000000c071740000d249500c12802c108001d002c16081030080d40c0000c0c01c0040d2076111110f207260002c01c001a540e49440391140da01e101100400c869070402078a2940c4600c280350051100758a18003050400300102d09503420700d4041d0724511041522080b00c45101c44003c003107411242106210350031414011419034a900c510356006290310504050103e440001d60254820b4a0160342410b038100b11085000c41076106842095600202003864001c00712240c8035514540300100340018401c03036503020240310001c030182c4400300741500d44000084a05686500c62a414810610010103064014004c2d20450780640c803520070030f41c4c03058 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 914991807 1250 914990557 914990567
    0xb0a1101091a0415060b09010e0a1d0117060103030e04180b01150e03150f070516060204051e061e0f0703030608160501140a020a12120c090305030a111c05030412 71
    0x6c001d1000b40d01007444100e0380c651003a41640b00141000300101d10312030b80e6014160542c00840c1d003003d0040718100050080307202e100c01510340d181368003004040540c51a14014507010015408a2149484804c4410760115078181d4800d10f42e088000e2410707550f59096101d218029081007031004c078805040c040d80a1070f001c80e040210400700c0300001800d58070355024581c403040051030407080c1303d02840510b04400030350595030780c4039101d03440040c0d8640c10f1800304030500d0440c45e514000d042d01001c880405886d088144e401740e012180a04192040300c500802d002d005102d81d264071558040f982e002070650503002002255140420303142d0640f458101e1200c04ac40da802400d010914410001204051083c000c04010070648140c1351801200e540e800c1ca614804204100000c2c4c0c060f08282d804a040e101d602c0204610b401c104941929654400d0380328090440342c00e0034048104510090700c2c07014414000643c01c102c00c0e1514107505418050001e4105482c141c44e25500e5043ca1a0503a01071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 914993057 1250 914991807 914991809
    0xc05090a080312040209040f0605100609081f0c1b0b1012080f1c0207060504020307050301020c100f11041805010e040203100e1e030304060f060b0a1101091a041506 72
    0xc2080d0901da80d2a000d10941b49006401141d4100101c0000000300d1114450030f070142e181401202d40310782ca451002400d0341c3d100c0d0080c2d800d94200e10500700070140701a50710b030b156032180304011455000c019020382d5048044d12043c140c0d850b086a9031820800d900358150300c280c64a01c0342210180c0c6540ba0106118588500141144000c0202202d40c110100c080e115084040c2000d00c0f040d032200c201c60741070780c00c050001c480080e00d8806003c114a0f0900c942c2c0007508043c0c000714200100b000130580c0e102c1031030340e988491558920254035000f407180c04c07110071a882082290fa03a1996201030701507014a41080b00c06c00c074600400402e805000a2440c0d00071a0020020580e0304001c5241c8c400804100044415038807c0010410a09641403c0c84501450301d00c055030f140d20307103401d0410585503c501178448581c0f801d074081c4070307000c1c7c1e8002351102d400f00ea1409680d08814032032098010b16036280003074003012410121075a1113607070060b25449280718070301c548070301508441001c060b1041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 914994307 1250 914993057 914993077
    0x806010207121506080f0105010503010c121a0a080607020705040207121b0203010c0528080f19063002010e0123030702030304030206010e07080109050a0f0c05090a0803 74
    0x100362020000c0c0c5038409007203a0201c3c0200d03100e11034040494a400300700e60b140d0f40f1050749074125180e100e865140138070071240103020640081c4010305c90110010100e203070101074649080e07552039081d5140d03240c400b9501d2441201a2010a0182d00c800c02969210b000b03c0f0200014406e44bc0301195905140c001e80e502180c0c00300300c1c075403044d1912005071a50280300b2007918074030859400560240e03400340100710444145d91500c968035a0000d40805030844105164001d800328041c00409250748502c04c507511002100d100e00081d11040350080788000340000b9100410704040001c1464014201045220300e003046c201c1c1401c444003001c0030012109400042e020940000c1110502d50141c0f01400b8110036540101c00703901c0b1506490083c0b500103990341c1c8016803011041000700340c0c0402850f0b0140240e81114802482c051000525003441405812017260312500800c2190020741c00010141d0000721040c001060005001000c1c2c1d00010041d074880d05800400286449010040b140181d071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 914995557 1250 914994307 914994313
    0xa0807051e01030b040f0b040b0103060b0a2006040507170d0e090907170726070b1c14040b010f0b07080a0e190f05102c0607060203011508060102 64
    0x3207001e51164950205040d032605164540030401c41665452040c03203080000c2030b02c0040d81025481c00e00c001c840d1000d055038107062400c5800e002e40395600050391032821351803600600311101c000c00c3c6480006200c3c0d40c0d9803140b00f800c1c280300c1002404244201a1160790005500d400c10002c0031035511000c1c0114800441c0d912240228142020380d102c2d0b901109a0040b03c001c590740d10350420040b03060760203c00090b0009041801704e007000000c04004500e0521009180e00c99510481c0e441d1b181c3c2f886204c0703110900184c40101c8200e0066030200c0c81c00d00381d004001505554041003484402101e04440b00e07042040041003e4801c10440303c00d42d034a551038103003404d000356550040d40c2d22010030071007030210200c00f885e0107649002e810310035089540d1040401902d060070880f14120150085842011100100c100c0f0940c401000540501015852000f584102044800b042516580e058001c18000307544414800c885c1c004504813198004000045111040101c91a10f001d50b10070340103070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 914996807 1250 914995557 914995579
    0x3150c180402360312030f100f090c0309060e010b01020d1b080c0a050601060f021207030e0103051302090c1206040905030a0f1806031a010c0b01050616150603020a080705 75
    0x505004100e02c03074062009103501c800800f1400070786060822011200d0609001041002050007a00e0132900041031950f40f420980c140016072241c01d40354010310304034039551a651800d20313109400c5400c04640050080102c03019115003907010380010780078580944100c100c3c01c2c0800d48524060034020041003046904d00d42180d880860603848001c080400d417080030601c40200c0d03c00e1180d14002e01c2d4507180c6102140c404000a410407042d03100000b402c501c02e00c20640440e03009104a01c40020918000909684141e6020040314003003002035003015800741080a4981d485005000040c6029002c1c12207640d441c0400c8207503000e00350010a5504144900c0391094040c850289038010a400e001e4a10441002e0182c2949007a91126000a854a4040100740b01002e04c5400e807000a103000b0a0f9007056072607020000300c0610a86000390400103c070040010007501c64141540e1218030912112140c43c80c1c4c8024202078001644944058180090002c00002d03104088450191031b0413158 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 914998057 1250 914996807 914996857
    0x18030c0d0b06040b0102030903010c030501180219211b17091c11060411041b09150302120c03011403030c0d0e0406181d010b060f070203150c180402 65
    0xe084c3d40012a419484107200024075030780c003070248046209280d40c00040544c548501c2729240108815160601441003004d0315522030030301c089035111040d1b405d00d000c1c0c2140c41203e801c0d8106000c10500001460440a861940380d244108480301803240d5039200c002030000c01c50310321400c0540f18420340f43d00ca4000b0011400781060728001c0381055040030540914600c450ba4102441107400300d4100500f001407808628181c41a0390300b0703038400d05c85020100448040980030480d41e000c2c603190345045481e41d9445074425011a0b995038807140d43c9141c1410b2084400910750800c2c000c1d105800401c80c4051081e040000c240c1d005910300340f00404400d1107000d41912211502101c0c40c2c1c0040d00e80c50046183c49991002010b940c6445800266500100183c603d15425402081d01140d0404003040c3d034603554441039500400007260790903900c2c407080c070000c0d24040d686142042c103068540200a0f20b01c443d4409810f004004a10214a440d40c030400c001c102d2080072801c0c824419080c3d550840 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 914999307 1250 914998057 914998061
    0x30d020a150905030d0f050c1801140f0a0c021810090506180f0906101a0d0b0d1b050105040b1210030b16021501030b0c1e18030c0d0b0604 61
    0x28206401c400019101201c1d00c405007140e01085021881075160a1a2150101184501517102c075940c115142811b8075005030035014013010034014100f1400002c0862030503968130480d060009020401c0d5903035484900050203035454420240d1183c140302c1810644036469040d03540c41402c80100d00c410b05802d208810380102000b8000f250801d480303107a80081d06884004060081c48030305c0a200503843c0c100c4444d85000e41c01040880d403049030b02c0003004075416580850030041c0b4101046500e841d4039881d028001c008141c81300f54451041618002400140e030304d0a6070311910f1500307211030710341c80d00010766240c440c500c5441c0c0325140402035480c02c00059850079411540448038501629582c1c0c0358101e5468040d46c1c245190329604403040e1125404120b14901d580c88118208510340c5036448000e420f64000b80f101c0300310100042e1007988045042c541d010b5008803980c02603240c45086030f6051070030090740445406442030840c110114a450424035200e25400b601d8440b0641e01c01c014400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 915000557 1250 914999307 914999333
    0x5040b0c070c0801141f0302220e0604111002010e0706030f090506070302190806030303040816050a050d030605030a050c1003060f0b0304121103070611040b0310060e030d020a 77
    0x40d142c050710401042c410303400e00a240700503140c1e1140e500d0b541804040c101e0624418800610804106081000140c80d4242158030980c1c20b280356601c0c208240c1315140281c000c080000d4040e0144a00b00300400211009146096009845c1e454914068560907801c803886202600d8455016a000300181e5110780c11440b0f03100c228100c0422141d609541d00c9141180070303540b15021a4000c02c1d103c04213070910b4201e42d6070380914a0408143d040070300100f501d030310002d40701030140440060b00b0785142e00342d005403090b010b50000c101d8842001d01d040140d1150085c5c1d1281d00020f0a20100242c00e1400148580a41e5001006044015103002c100520903d11350000001d050f203d4200150301040509000004c180d5038103511354903c1e1a01d0300f03a02c901044005030041c40b0322140c01604060001003a03554190b40644004ae00c40c0074413240060b280036076405040115400004c215461040d042c0c020100d0b02d150300d84003d14041e0408264607842440f05e0b54005a0007000c00c0d10104504ca10041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 915001807 1250 915000557 915000563
    0x3110f04110a080115030b01050d020c030403020d080306093601150605071104020703090b0901210b03150108030d020f09210705010509060306040504020f1c0201080a05040b0c07 78
    0x240c0d024120780c441d0300c01c0e04841001c1c00402c9050700100901e0302d1491a04002242c40c3c90104100210100084c004c0e00407202410b041da980031400a00006040040324003540e0000d20181882d0868a8094100d510443c2d070b21340118816070200300307040f15000c0c01c0310040307801050740b00220400101c08109100040c0203105659240d120082c00920000a00c1d4007416a95848540d03440c03540c207001c1c542410b4110594005c4c0d10400030640400d9004214109582c2c1d2403810f19a120900801220101070380031000d107209510000a80d41342e004da40c8680491041078066820706680100184503001092254106940007044207102031144d42e4000d20341c400101004500b0840841c0120710111004500703036442182c4180140c034104020401c940003880c091a1181c1761400f454041070040c080039240c10b02490300c42000c071f401c659030729a408001c8140900344031a0741310421056102c080031035105901003980b03a03001c240d00041a016152003550030030440040c64561450f04d0615901c502c1c0300f5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 915003057 1250 915001807 915001811
    0x110d080703030b19180e0c100518030d05070b061807180f121a1605090102151006030f05040c140a030b1e1303080105090604090602040f080c010903110f04 68
    0x1801204400740071400174100c1070301034130011500c030311291080b1240f8a080d0725681c2c1c03040e0442615030f80d844e40c20082200030761604540b01c9060300c0c074030001c0c40e000c02080b40d07141c0940300c0112021980b00c406058464003424660040362241d4061107555180c4140d42e111112542d070008001c0c5020785c00c04540395000c8000083c3d40c981c0c8000003c0a03580c17681201c40c00c07001e51840301062184234820021000000e0549003900e0500340c61307680c00c49181044000070300c100032800070b500d0780c001d100501c036a0f4010305400b841c603e41100c3c0400100210301881020070728018440766084590b100d51442a40d00c03036800529076040002c40c5c50f0141d480508141e101c1d2002c80301000251000e803480d401100c2c042ca50030b14803070300c82c108030444000081c800c0b82011145030720040482d5024000d00d0441c1c0c0150340181e0b15494400200d4040e02d08400702804044c00010f000130040b52815686080340c000000ba0f4081a041000442d140d01040c48054600350000401c1001c80c5040d14444900301c40080c40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 915004307 1250 915003057 915003079
    0x6031503030412060606110703060f0b090703061701060e0123030a0c080601060c150b041b02030d0f0b031507211d030f0f0c030d021303110d080703030b 67
    0xa1031070b07005801401e000b04503600000300b0802d89006080142c102030900408061401c0d400964030b0301544405040b00d80c881c2103048841920f5801503d40400181c40d411543ca400d5001802415691003088092160003e201046510620070182511042c3d880220340c0c0c1d10b05003030240d2a8408440c1181d081401c02c403984007a907800c1241074540d91107052968115442c0403215400c00070142c6c00308083c04494407850300014524040500c0ca00070b013a000203060f450050100700200341c9180015a071042d001c1e505c149860300040a0515a0092013080c0f00307075404580340c1c0703050350b1030100201c2d00360380003c04181ca869003204080c2d44c0b000003458106811b046001c214041c008201807007641069942c0110744411803120501585000420001c40c076101c1940450b41c100d200e96200869910707004a030242480388140f0031038000d616544000d546402c1c8501006400550a1208560b04801084001e006041c412034030390201e50804107403410071400380c80603405044454585503010000c880 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 915005557 1250 915004307 915004309
    0x9080d0522030309080c090c19140f0c060a0b01021c210b040c0c080313170316020706140f0313060f051e060f122415060711060315 58
    0x4081c0000b98042e50365808200e03c2c00c003a550034408800038603409041c0c00300c104034041100c582160010f0388042c1a120101003610412207103000200c030380c10541d00c1c0018455003400360903030192089100c07607003da03070039911000036240448151050460160b000b01d03180801084044ca1006146003903410030048103a0f01403802a0380c01c49800c0310055a07507480503900c4650409102e2603900c1041400c011001144070f032100c6501d03002c000c08401c0d0b12a10214031303000b00144420b00da10285156003440d40c4a05008081001c0003080301c504200500c940c50307001408910910701021901d2480310218644031a41080d000a6803004102e03046041040550500091700c9210324108001e59560020b698240b0040100a40e20910000c40100b80e030082400200d50316440c081281c000308135501980840c101307804d2030400011040d0b1581c02c1c2281c980d00405000c400081038490204409408141c049190401800b40500c45000d008901021010b44260400000840c0c0041a03c044259035081e440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 915006807 1250 915005557 915005617
    0x60603090f03071211031315030605030a050106030311030307090b0a03092004060f0e06060702300616230c010929091009020a05040c08070f09080d05 66
    0x3ca0221801c00816015002c803c0d03104030500f1194400b14080e510741400e021076021036800900170001c45040106446d4480d074001d0b030251001345806025980d41440710304029000701114402500030800680b00c10300c0418000c41120b01c00e82c1280c580c000b1060900c241c0742a603030000940c840505035140141400705c0d43e140c881d80d029103149100080c01c5480030742400140c4040354021070598803500024003d00c2d480c01c1015900901c143d0380d840c0c88445074000229400310090301d9542160054203680002a507071201003c2e90140f040c00c55205461b10400c2c11100032039690500300003a0f46003500e801420610b019072040044d074400c4603003040500d04540782100c4040c03c044030b1559802c0c8149005d4044080c0301c240204006406403294607005502544031809008030403901d5503600c1d084000c40d61081341700805400050000c1217909028000a000c1400a603039240c0410305171801e802c003c0d40710f007142c0b00654030326a01070504110f07940c00a0310f80780c01035010345c40d18031080110680440d0b021 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 915008057 1250 915006807 915006817
    0x6010f081f0326030114151e040f0605190f1709031b010605010c0f1e200a1a0c030d020309070f290306220b010e04090b060603090f03 59
    0x2c3c640001500d50180601e00d031104821102c03582114040c0300410000320882100d04140c64141c483d8030480070300a0743c03c00300d0b204a50390404091000030f29145041c00105c0a8401d42e106075410b91030154403004e0030385050085103450380001951440304400f01e0322502e50654460038074180740a501315005003d120b80c03141141c08030f005074004184003040c600140300e80340b210b400b00310081004070704000000300040c0c2e010070040d1071458241c01f4001003215010104803200c4070040c1d108a5480541b4100040d6030b480342c2d0304604c0703c401c6204e28030075140c6440b810b405c80d23209010260200b907038080190002d820445030100240401c1c00816140c017401e000540c0320304d4100d405070500e03d0400b00340c80b640d5103007500203031200f80009888031142c0480204080c28100c054001c47d0300c0341d42d0000010800d200010b405100b110a2003040c1101c181d407a0403500c1c110500340c0358038081154502c1400125000306a0242c9440d10f61408540d103401c100b0001e540150b01c84068401031901c081a10b882c603404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 915009307 1250 915008057 915008063
    0x2031c0e0103061a2d0a0201052e06030506040e070905040219150815030a0b0a050a1413020a080601060e030d080106020604020f040b0406030c03050106050906010f081f03 75
    0x340a4414001e607494030403140903200007400007a11040d030030184180c60143c14000c4200e503119170598040d400010031008132011110552664030103c00500a0103450140c1e9641795544c811355905840e022500809092950706507a49000c107450018200c2c040c0c08046c0038280c20550781e0a03140000c0605002c554060708411001054604091041c805d60034010101c082d850700c0034510501041c000ca43c2e0010b030450541c90105c906443c2e5000d1700c06520301c00361226502d803089810010400c0300160601e407088164280c100f0841c0d07038503602102528543c02640c036080440b580010520080880c80c846654005801d03800c440c4d8895403c1481c20300280c2000e00032540c402140c42c5246000c20100101150340c0c5010101da503d48400070350f40b0640600000d00c181c100603801200c58880d644101400640188140102a941e040540c074060450009480035400c04202060324149120709500408069454024160080b4001c44041502405908084071350307181c4a0403800030ba80f400e201440c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 915010557 1250 915009307 915009317
    0x51519050a05040507020a031d060d05070315053601030b0a0e0d08010b0703021c030e010e0102030103020f06032508060909120d02130e090c03151302060702031c 71
    0x1041400700321034a040c82e80803a1096003040c04018500d680403071003c0145034141418079105140c207520010440d0f09800d0682c001c0e40104458142c3c00164000b01e00a0315542c5082021034964008010942d00e2400340c141c01c41070703d211f910004e0354128054205110441c1c00348c075441e4010060642c1141c3c080e802a81e4002501e8240700c0081c09502c2042171904101004001164281c40050510f078814440d900c1030f00408500c5d40300703060003404900399100c41040484695480580064000c02c038150301804c80c1d610384128a0f041c0101442200d0507170350028460071141c001402089525070000345400854488000d000a41c10025000480620030545420310a85000c02c103208401c00000c00b8220960b2161050055440d010380440d424142031610151b51240049090441d100301944504400c148070750400c6405500030540c40342900742241034074031a5034108000000440c00340d903d00d180301c0841c90020014a8864010803001e48041d055032480d01841c4d0040c4001d40080c14100d011030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 915011807 1250 915010557 915010559
    0x41e03051c0906080907152601060905150d0903050d0905010c03110a0f0e0d1a010314060c19090506070c0503010f1a0904050a020d150c0e0310051519 66
    0xa9005942c500181c692490701103d14908042e07026903603c2d503442058140c0082081100289100d028846030000e103114803403403840035984a013042d40e0320901c00c8100203090080b02007100c2c40c0282c092036401503442c0c001030400007011145c100801d00034000704c0030700400b00641440f031a8076005054542e0b000b4070000030210000701b006001c0d01e00340320203402c002508100b090f0f0801d80008902ea0011114030740001c2d101310540c0810102c08a010003d44400d004256411404519101040c1038038840c880d49040b0400c0c1082c0c10342d4460040e2545003111406107c101c01c040d00204110220828500d49510859a15404078415501508080d00e004001c0c0b00140400c0c00d09000384000c0300b0041504000c80c0005024200d8655403000f4558481d007208004581802010090004419002043d04050b4912460b1009041c2d60b170019084402d4100400f210040d4000c40e40c0580520010f006481c040f070b1082e07104c1c001003c0c014100c1216450ba07075a0f8101c0d648603032200b20460240780000100721 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 915013057 1250 915011807 915011863
    0x130209010212090108040303110d020706020903161d0a1506030e07140d03080c0c0118050c0a180f11030a0605040f050705070f050118080d05070207050105041e0305 72
    0x100c1c0110b501050140710411040007503907400603200e40d02c10f40501d4006241d42c120700c1641000d202d0400701d00072041c001703d05241480f1407940100440c08044080341c90294207028000014a00e51040041d2100e24030100c1d402e506208001c1d683c80034001c8400200855900400545480350b078002c0d00001e42d0f64100312011180400404e0040c240c01d485542182d540e1200091070f50341980d400404201803440402c18003d40c04e010f8581102c3c11130f0007404503400c0d83c84003440c003030040c0000351098410185121070034108182d8a1054851041c07000310600e02022041028103088c600b82e840041c1d680c142c2c041507005075005940110b030348600215081d490314040000340c4103200800811280380c8814407070216001005c60340f1056200601c10380d0b1440d0b1781002c600400d19101504d40e00b900d174480c08410404080c3c0241811031007440100306549941408a0303554645008550108204100c1441076100106c003c11109140160b0768a6041e121780d20903041c204007000f58542c00303440c2d100c90710704 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 915014307 1250 915013057 915013063
    0xa0210171b0a050c0a050307050d1d0102062205161a0301140d080d020403060f0507050a020a030813020a09020301030302190f0f020a170709050106020a05060114010e1302090102 78
    0x4842140500001c1e8030000c8400181c8034005103607041c04000600c001d684502800800d042d15081000e1740d03110311850810581707400c9804074010000e040d00da40700b01c0c09c0502ca00b00c43e00caa40c043e40100700136a940c0c89980008003016a451915000c40901c40700040d4042040423100b4084181c1c480300c551921041d13082e6500b007026107408101e401c1c80180b140d0881c0442004400104845401480080341080302141c0701c0c00303100841c8a0300000d004000e010305900960f045040014040080d640e80040444680c01540c0f121001600704140e5200031a124051454101e00004498001030406500268860a81307510501c4225004001007042c1a014403850503070071804230034041c07002000c0d500c1c940035412503140100890349030b07000c446c19511041d07000b1000c1c1c170701d504220f500c030a808003902c1d80e500710341e10410141c241024000b180301c9101141d40581241d105006042d2a401d1040240400d83e01c0c00700f0904011020104004544e100d1403841c451250f02d04005941c4c01c0c94100082c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 915015557 1250 915014307 915014311
    0x2061b0d0e040b0406060c26030901020a09050a0b0a1107150215010603050115142b0b011d04020f0702041e0605010527030a05010c0203130509061804050a021017 71
    0xc8130f2407810f0010040c40350440c8940d140c0310b5001c5e000b0036860403000380c900d40321401d0000c2d0320b8030018048100700600b00158000d01a11070141c540d00c1c3d100780d60703004000707841000340592041c0d0b081c05d0100000090041d12000101900001074846050b11264440e018041501d82140103078403842c00c51000c0f091a44a190150415145c244020340c10640c040c90844d547c00540820040d000f080e030300140c0715000560f000c0d42c4500d03411014000000a900b0700071612403a00e103c0712482c0214421056001d45c902203002021400302c2090b03044c1103410803001703400c41c0803000c0700204d0802200c0c1c0180d6440c4070b61180c0c00c032000c480035070502d0b03500244400c5074040e80013a07040c41010030411002c02d01e800c141e51842d61045201e0040c0c5910705000c64140f441079330f002881ca42c00d0450701082c3c1034000c805010b8184003001d907100c1403640c6808100c01004141ea8494100b00d0780380b0b02410b0251420710703455000d40500300311850050030b5030124602c2e82d000031703140b00011750002c500444181c80140e516 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 915016807 1250 915015557 915015559
    0x60912080406050708091507150c0909021608030705030f13020609211c1d0a0303080405340b03093708031006140702061b0d0e040b 58
    0x205520190390312020148200d010b40000e203c00441c820081041070412218074103400f0786017000c411200401c4507078a4011500488030120100c000c00180c2e01144a00d140c540480d640f8072031024a0a20344400039070100e050301c1c5480c0303818640b94011404003401180036020a40d1003664919040f041032104050140c00c084030f100c0c4e13803940c00c405a9030b00004d880c104030045a0f00d40328600100c0400000a02221400300300b40104841081994001c0403100c0a100440d01c0f041080c600c0420900107000c3e00d4040d00d1741c00310400300d0510109100b0011950300903c6141200c0402c0340342ea0f40724240c80790203901c528a0108029a030440689800681402401e0060b40319081d07081c000001520380d201000c460303105400700503512090110b459544403030084150320711581c100460604a1a90b44220390b4400800d03800c00000604074850042c0340d80c041e503000c40386401c04125a0800c42113034071140d107184e050348050220a036241002d00403a286c1a019440e202c1791200c0c0705060000390b40562041c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 915018057 1250 915016807 915016829
    0x212250503191107021e2713031107090603151806050c09151b0708030d0c0201110c160b0c070306091a0f040b0109090c0b0c010f0f02040609 62
    0x110a101c40062641048120414008510524101d050f415540914003001e9032001428061940501c6080b4540d01c01220913600c1090101c88034070702e1140921114110700e01c1c0754000340010034052403404070b8400148203180c29003540d402008464508001c9811251495a0311507040081001da41c007980c411040c48401031100045285901a031901e4000c4060842d9403102c001400040009084a20082c00203006c102c0c1e014128180710341d10740080d04034801a51007851a13115040c40010004119521741c4000c6d481e2041180041c0050b204152182c025917496101200221111401a042001c8400c000f0001064510003018202c0091303401190845420040b00031b1240c80403a155054036000400030809586a01c0c0c110b65030494681e55100b05080c14007400114042c85c98040c0c010707130081b07108520310b0341c0303484d0140100c503030782103000304040400e880800004604a0140c280780b0307000c1000207038025920341d1049c282d542118102920796400030b414000c0d190401d02c4d14002c1c200b02c0c500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 915019307 1250 915018057 915018061
    0x302270a14010b0c0106091d0f01060b19030b03030415030f05010b0a1b0b0408040602060c0903032a01051005040c0302131e0305030a05030106081501210212250503 72
    0x14010a07000e0600512000360b400199510711213800350031882c02426031601c2040808004503420b1101041109001c0450241581c03244510505004034030076503030212123080c40d00c040ea00300307803000c002c0050320340d000e05407941d070b514025a0b0700380003900007080303d800200400b00d5103038001000c40c3c1c2c05030020f01030541703001e0051000802100c00c1e00c0101c000ca090043c034209041018100d0700b13072050310040103598240d080004201d0f0381005401221034136001c80d001502d0351310b0003010324042c1c10030840d019407081c8401c0200d41d03101c08029401403c1c5188292500015061050a44130201c3c4c0c614140e50b0406001c200e039003071078450b2850100907484c00314101114610b0500094100380700b40d440c0c1011480c0d900c44a0703070000341180000e50b403201c201c070b5540c1c1c00c511001d0b003990000d01c01d81c00451920303c0025248849890800015030741691007003071301a450300d6400011403000c02042c41c0d1503404e101001c0c201c170114120301d01504a40220074035140b120354a100c0a120034803108400c000d02401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 915020557 1250 915019307 915019331
    0x8090a0f0213060512030901020601060503070c201201061a1314040b0a1211060702030303040b0c0c0a0b090606040e0d0e01140406051215150d060302270a 68
    0x25403800590484806514010366520100680915004203034440c064031004046500004020142860203809071901170380c0c0c40074107403824001124004089245400c0302000070700590341081401040c0b12504151030800c0780881e0071905908102e030816036640e88180300c40310002c5200010030454048841c074000c041e030b40e0414001094800e12016404401001d0350b582e8458106c0309070228082d02c031043e001d0780c420300201480610013003910000f2010350340d564641805c03821500401d40180c0114515140e680d649011027000611800c0b01e000309020400c00c800081c8440c5100e01e0080110303504604004440e2420060080d20380c42c4280d1900b012440450b4022a43e03030300440040c18040c00808a100060b68541e81c60340d182e0b584e0200008001c180030b500310703001c0c00310080070007200710b410383e600d1038070b4484445440c450541c8521007040c605803903441c0000402c600318050b40701180241c0d580e40411144e0710b08408400c1408842d444260106000345c0450343d105142c29030a020b000383c500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 915021807 1250 915020557 915020573
    0x80906010b031e04050a120c0311420a0b0f04050f073014070e090109150503070e01050312071709012105060a0b0c06060f030f07030605060108090a 65
    0x80003c031490301829000a003801802e00c842c1c8101c0c0e82220300619414602c0400034007503900300c0c03021004074451018182503054005100016840f21b0740503290701c04d0b0301d0401c1d00e8a60000100c07400515004c51600304500d5680303005540207401d6070368041034040c03400e010400d404040c282d0080c041c610f00710401c0904c4c41c01e40c440c59003080850a1031880c981401c101882c00805040140c45c2c4070186c2440c00001e022039a1200380100d01030101c94001c2d0301c4260003103070b91105c0c040e5215880b081c48401130005030041c0d445240786c3c1c40b1446c10f07104499604d501003420075900b07500440010445c40010806030070180041103601824074609850310b40240d50f410061000304110030901c8002150b00740181e4058814660421520b149146040c0043c1069401600d022111713580110a0b85e0800589540144103032103961a188014284964400052001c00c1881c24403180d41840381404100564006100c1b01010f1b5010b44004110780c6030410024102e500e0240440030b4903480515554085a010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 915023057 1250 915021807 915021841
    0x702150903070e07021e0a020901171906020307090f030503070b060105090306040605041101111005070c08070f0b01050d02061b0f12030f0106110a060c03110a080906010b03 76
    0x2040698440c009100401d02d059915000301150040010500c12016000900150301030785a042c139103180c1040020540d11900c0d030340c2c8000d404c02e8040c001801060f80410741c071020b00000a048403009128440100c0c804c1c14140400c3d00d0540e8004103100d80550301076448005002140d64003c056440e603990641d4034070440b2000f8105c0440600403c0030750b0310134021110420001401c64886081034105800100030a0354121081003110540364229402900b01c5448101010044c107004d1000c0c4401802500c8010400e41c2006080d401e070000207800c9102400240e4020300e9a52011801d600e000180d07e24180c208520918220b0652070043c0d1745c601c1225614040900030415171007200300500c0c5040c020170b2800f40f2030300440303c2944001039020080c5100f28071402c100e101590b070310b000039030381070072400701c400e6003904540c042030003081a542010360b28003141d2800144004c07401d0300600c2503800100c03e14001810f030105004850800300207090152140d202c50614600f000340e2000c80120fa4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 915024307 1250 915023057 915023089
    0x3050d0305270c01031a0a05010818071811250c0806090307060b0d0f08070c0e0a1d15060f04090f0803160306030305090d140a06060801060b0702 64
    0xc500014040322080001d03000d480c482c1c1e001248a85a40301d03140394035a00c1c00249030b400246807503402e041c903069034103941c1d1407039001402e14100207082800460315481c0042410100940019104c24141401c00a0100506000c1080075880100f561440140c3c0c1100c5040030100b40706000d03030001c00d03002c4608140b6034003580303000a41c0803000e440c00100380d08070743c2c3c07006010b400380c281008003140c0003200501419108950810010500804120140c040c09801520050300b4003151400100c80400a00001c1d00a5006004840d51452858a861030071140420001c0c0c442d00307080030185145d018050600180d5010b00100f00c5030345d0a00ca1040b2000305001c0c0315945004045840b6102c0e94040110079405c0440346040441034180f5404541c02610005070355906650710451551181c03041300196036050359000c0c682201c00d810002ca01ca02002d0070f82d04030070304000502d40c11608000307410722144a1500859080c0c0303000600c1d400c50b80700e64441d001d0603400b00450f8005a43d03400c0c00c1860344070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 915025557 1250 915024307 915024311
    0xe040809180403050409020a0e15030901110c06010501141b1e241504020c0102041d0f0a1a0306180706020c150a050702030a03120f1e0c030b031614060403050d03 71
    0x8902004991070300302c009c229a040107401e10199000d504100047d0720403000040240007541c81e280c0c881d1082e101d60102070040341c120000500c40d66100e201c40582020100000c0c030300b04481607031034114414416400c0c816980c00000312811961030154501e150603000000b03042e50310b10302d600d11940ca0b10248030455a5442d1003002039600041140200d000300409802151a8000a0b005030700039489405000c0180c1c2e560311900d105510760f803000502c40c440e681070b0310800d40c4504001c500600300c006401c1a20318030070280b07004251403c001c90f500c0381d20071580150f89103400010f0a030070500d49802c1202150806202002c10352100a907101c507400502c034800e40d0342c200c0c80c0c40484250141001c029031500540e070034081032650000382e40d80e0000c08060104210150059031204540d01200d07030101d55411559041c010043d00c0d44014610000ad040120307003030a08130700090511080c62485608000000014000034113084c01145c40d0203c00d075181440d141c15034440d51f64960046840f2801c03d0307 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 915026807 1250 915025557 915025567
    0x16030b0904060b0312040b041a070c03080d02041212120203010f0302061e1b0d090f03021c0c0611010f050915102c060f1f090e04080918040305040902 66
    0x1d04c0c20808150741c4000c2c8061903482d00c0d00c8074101203003540203115500c0504191011621400f041c5d030101e0700e01603400041461a40e1075130b40c035410950403c045801d00d403a800d00000910141e00f0280300201440b5002040505106203c003038252250382856858039441480140f00c140c109015102c2600d4044500a480340c401800b001c0b040711400464890a10010901d0341502d05801c240001d800785030800d4031b801d0900034604858002c0c00c1e00c211240c4103410322080025052103d4807064640911074454400c09103612004898100d5910840000e540c0b010006a460401c3c0b10304c42c441c0320b01e45000c3c002410102c0d01d550341d800c5910b20481141482a012a107004d06403a0800001c122000141000c0510410421038140c00b00014148030100200059454546011030460501c4010841d590510540068010560300300383e6110901160100109850700c0d0100750a1082c0e100303014107560780850409000180b07984c81c92014000d8001c41c240400680c20109039001e550aa00f030060f02c1d6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 915028057 1250 915026807 915026809
    0x11d0309240721080f180102090312090f0301060b040509100f0b030a0501081c0e0a0315051b031302130b09040308010812070201020c0f0d081216030b0904060b 70
    0x50303a045007001d03000d240001c0c80104200300740c9080c0b81884071a8024010200303504a00342d82c403131800c4030003079003e00c0744200003180d181c9580c0604284000c00d000042c01d0040210100b85400903140c110224060003003880c107054502294080003910054000b801180d2600e5111003c2d0f000f85d000e00b512500c60303940018189200d03840980020110030468000302555104503945582c07080d110200524141000030500400000302038131106030040000c0c1c0c8002c07035460b007180c424140503a40c0f58815004a000000310f4407031500c144900b06481c4002074070b0f0810a54813100004c2d0301040b04914a001c0c410002005407001c0c4480181d901071f60300c16002c400042035030005000314503003250320605503c00e010906501803c2d8a06031360a0000301c85040090003960078090042e020000e0060340203101d008103d0800c00022020780101a010720071148050f5070703da20a8100c0d800d0031280070311300b0080189410b9403003220b111403141c5007000c0000c000c23014046841c00700014000b07851075880c0d000503446 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 915029307 1250 915028057 915028099
    0x6060d021503043206060d02060d0c0306150c02090a0e1212060907110d0302130801060b07030e01170c07050c030f070509010b030f18280302011d0309 66
    0x501e262032440954910b0103250010208506540d0404801c08101c00342c0d1450064a4a0000d501e110038000c0800360f48101c00c110b455a59068104c2c5c000200b40010783c0007058600900e0030f4464203890200e540c0c4e0802589086d4140302080000c20041c3d8030408001603150800429005140000e01040c074801c1e4900b0540740c131700448100c0e001040c000401030b042140c1c81c2c112170702821046410307900c281c444031030440d200035a07103c00c0c55140e04800c00e4451850301035402401c0300d290382840d280300141d540000c5400c42d01e861744220701802000a24004069111410341c01340f003400d007894552600400612721801800501803104284001002070a000341081841c1c003061000781110320403030007060480e880d600a0b102c0c1e035014a141c00004950414190240d0344110b01d500008003481d910903507111411403400c404001da0740100c0116043c0134034150f52140c0e034200d254070321182600052c0b500a08580c940041e034801c1c02071092401011348408011194981c104a58852160f031500540030f031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 915030557 1250 915029307 915029329
    0x3040311130219050306270a020c01090204051003051e070909031b1104150311060a18060215060d051c030605091510020d0906030903050c0303040c14040e06060d02 72
    0x900ea460f00a03114071954070400440c072034801522901c002007089004d51101265a400c2007626009140c00509616140d80c085c1100f05852800411551804d4005c03400f254825240001c6107000c0c00c8007442889820400900903050201c4400500e081281c80d65840d54814020202c085440c0c0d440002850b20803c0b14a40030b05c00c1e40a11200c902c1c40e85040010b950361006624001c42c101403c0e100510607924043c07088075009800145c07170508180c10031607554000d01d5403c061200c02d80c040c1d03400c05c0c1c50742011005444030f50010100710004100c0010300c050000c007401c1c4152101190b101c00500301095081c1c2900d002e0303050070410801c06106501030407840e008a500860004c00300f24849118540b200e00440d002c0d00c0d068004207121004a031960300e051900c0012034903a2004001c1c56100350301081c1001d0180c90300710b00b492540e082035030035a03001356000e0750040f42c903940500440c80010010b0110342030032181041050340c03450302141c603a170000f444140b05462650b501700039500d0b00c24000b4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 915031807 1250 915030557 915030577
    0x15030207051b0a080a080d02071b0806094e07030210050112080f0306030109060908030f070516080c1603050a03181211280314030403111302 62
    0x801854400481d80c15440051100520031940f207000083c522030302081010003950000402494600301880708006940f052804841d0000806520400c0b5550110302d10b0107010b100010b403c0506004d085603190110181004448003548a00c52400072f2455015880c4501d94a50b03000005004001655006403110074208065500241d00020590b000c200000c42203192030040007141d0300c41e11988105008490000c05100c000c005800c0558030540c050b540c0040000c0010813141443e950303400c2a0350b60107400701c0f501440482840384120010201c0c41d40034019140442c01c0a14215141c0c0b0000080d02003c0e0070910f0005040384207100500c00c7c2e108003e9800b2404040554038941982d4072070801100350002000c450850f00100816078400e0100c50f180a2590701c45101ca0303e502c443c01140002003039000d0110424200745542ca5030b00c076081d1511003030902c4401469814844808440b121408002d0f81041000b44001000a044c0c441414000c3e01c148a003910000c0380b1000910a4107181 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 915033057 1250 915031807 915031813
    0x3102181e100507052b140d0204030807020f0139050d051e030402060901080702010f0906051009020903032b1104091b0c030806010c020a0e0105041407091503020705 72
    0xc0c0c0340705504100140501c0703201d00102d601102080f00d084002d040d017900ca80c078417030188031a1003500900c510403000f00010300e10180d83c50300b252910918100d9200b0752044440c100e020507030b5800d5140009003030804803020300307160340d5020000081d92b96421000c001002454000c40c2520344c0f0000c0040d49007038040d484030071507642503120100600260461185d01140000112141c0000307242c2c002601c0c069580500214102603040c0c0040d105020000d02810456603500803078400090036014103907015000e030400140a00780b0b0700060300bc01035103030001c501030340c010030031000c49480000888980c04080f0040143c03c040350502c880c107840c0700c2110518803d060030040007820040c4001801250802e031010080d4121521003844000c3c0400c050201007002d00c0d40311404240911092980b006052428400543e5a41e00181f110036540d0000718003102c4200040c040390606201d00391218050900c080c2041c03a01b0040200440f04174010001c9150f80e00c1000d141c0180240c0560703007082c0c3e0120035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 915034307 1250 915033057 915033079
    0x51905070c0b100914040506010f080703230118050f150604203001051f030b03030d0b190b03070c170c0604020f10121a3102181e 57
    0x6181201b91015210343c002c4000001c4c842648160325012560190098480c441c80e6031106000c84010001500041103100790b4041000c00070b203e98030030182244103007402c04559081c0145400d10360501304c481c40d80126100c0011003041c01880ba40300100b2540070600d4420004210804400701ca4940c21610020031420702201008686100408000b005440c0d070b46001d01d84170409110030f105076a041076070400c0719181d0401d540181460300000e42800b203880401d560101740b4590106404a0046070303038000c2a5600d24004201e814042c021017607a55860341000020640c0d0700c0082c14a405024440c0914001c1000d2603494006074010301c503003070707458030420850340c1e881d940f00f250128844c805d940d4007460b40d0301d4200140c80310101e10780e640b01074003900b0038414130007824809920031603014110403020090380e034212404110a82e15040d00401494080f0030200d210a901700d0004450060092500c803858100c01340c0d01420701250401e04950340e01e040c1140b06640011829001052049 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 915035557 1250 915034307 915034331
    0x302031509010c080403080403050705120316030b030f15040302160f0e0718151803240c0c0609030e0a060f3507021c03051905070c0b1009 61
    0xa40c68071072060701009000c4002d2140301221035100072070300100850020400710380424800d00141101510801c211850035801100700303a050b400444070032100f0317680780c00132100055250040c407c803074406130000c080285000400725100c02d105140911000300c4000040c1c18580f0070000e141c0708601c2213010f98001525040340d02c45010032409000320212101c000f05440c548212011103190450500d010030050a001c0309480c070316011400182002140343c9a41402003560115400451242410340c5001d00c01c0d0806200000443c40144542c86c90100c203100b840390448440c403440c65225000040c4500c0c50318040d0340048810304226000740f945200030802ea5040280050304880c20b4940068400c548402d009035003206070703801d040c042038503004400340c01c2c0700148458100c0d13054010380d00d08800c002c40c6200170421341003005000a860b10180826049410041c0031003207810300c400c0c84a03140c5100080c0c080740149a0003400b0108a42c00101c003143c04d03030318507000345c10032120501c0458130b251 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 915036807 1250 915035557 915035593
    0xa120216020a061805120f0f0c1807170a0e1605131509020f09120114070503010305030901140c0a0303021b01140f07092c09071815030203 61
    0x48030480c040e51036404003140003401007900e0b4884208502440203064105000d2200c1440091004441c6100b2284d2094105100740242170005803070400a002040d4003608101c0144809210000300c0c22501c0144203801e0b500500308641c0158070780000940c0d460704d02490340145400c0480a0403801640081904180c6220101c3c0403510100c4044841c030120940850480340150b81c40140c100d040036007040b411103280c0103003004424002e03165040041080102d2242e1000c0c81041406954034218603a02e05021003c41e13405c00158541603040d5811580d83c0c07130340c920501c81518140034004001ea01030b0b00015003203804100504007a6164a00c0c24a0098069000007032010303610003d0542c41040520140700340c46068400c0a07400344e0540b034400c80b80800400103049601045a07500d004521144c180080484008000e116003c4480229a07001c044e10b0019000c410329801803003042052448074024002c03a500d19190002e002807418001b9800404030341e00c000c0d014001c10400c450101c0c80d003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 915038057 1250 915036807 915036847
    0x117010b03090f0d05091c0f05030408060112020a270f1d0109020108070c0c0918020f0901030c0501050a050c0d020601060f0c1709130915140f040204020a1202 70
    0x1110840f22003100148001d51181084d461801c0001c00500c031650881c0703000000c42d01003100c1605280743c0700b041c6413208000d001000b2400d44040e400060104100036042000ca401020800302c51041107a00e680000c1c600142031040a41d40c504040088001a81340040303206d048010450400c421500242407a0280064000e01103550350a21a50a004401070003004402a4140d40341d02d500c9e81e4210050b50120b162050035034660ba5040408614040907100340144909044691500c0d90a28410000ca91506c07514483c003a0a0744001003000525407805181580e400f401c10684643e00c940d0200c449001e001542403040c40b40c5400c0c182111340114031641641c1d442d0b0750b402c24648407520280c40701c0382c40e030b07900a00f110006c00f0280c1803450f018019054204000702403072461502c40501100b540c40c0200144c1350307040c50f04015101c0101c1ca200320710880040d420f26071400e14104504448140e07000740084c0c0501e80000300300d40e500b44102010304050b01c0781c1030115164056003d05414800c14 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 915039307 1250 915038057 915038071
    0x151c0e0d0306171203100308040303020a020f0103090f03051605010204031a090a030e06030703020f270a0602070312030914070812120703150b071401140112110117010b03 75
    0x500b250200300041d49907407580b28803100100a01100319034000304011035100610b8020200f00908003c000520500018401180294018214406940100410680d40224560601d440c0904d690002020b4110b80002140c150415a464103542c111044e00c0440f500001415944005000310410a802c4a841001c64440070b0317003039131303541c40c20a860ba40d0300c81c9801c043d006c500e208120048a04e8030304029503000e2040c0c580582030505c08240e0401a41100d2500c1c82c1e20441906030540d041e1185c0e180005000044825820a51401d0800382d1544501e0001502903154440e00c2001c05000780c018200455201c0755812021090604044d1035071326501501c40d440c0550003c3c400365034408010b8650301580d018024403d500e510000b40c006110120a50f000c5110104000646d011100050482a4003d030a40000340764801462070841c0d08a130000c2c55031381449001486030a004180c87e26456500c0300b90116441d05d0703100180e40c00850710101c0b41e401e03820707440041514082000a507028800d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 915040557 1250 915039307 915039311
    0x1d010506030109030c060902010e0a06031d0d05040504091a040507171b10020a083c042607060f0e04090b06151909031a0105151c0e0d03 60
    0x3100000c142c203840301ca000150000d00804039940c007190480c0d102001e054814101030300c04115440204104018a030301c5540404d030f840501c0000006240042040d815003034000c0c9c4410860620007034010b000b540a070131301407a9505408001c200050004501506072081d50030001d1800c0e00d04650b84001c0790050070043e070303411210078066120000b903441009181e0b21a9507202c200d8034040c030001c0304020b0068401c51140c3d8a096002ca82020002c24085410029890b01c1160302035070f50f0202882e5030500b120321041c0c00700e034140d0744509109580944091580009504181035500c2010b05880141c001290144050025095410201480c030191083d1540c01d0f4000c1103204110860f90014005000c840003c40000c009181480810040000c11410381c1d00782204d05c0c20003100100360124102c0450382c02d14061040c000c6c12500f404503420400005083e41d81814082200c0200200310303441c41140200c1d2031000d10895809154101541d18001c2041420249083c0e41d140b8003a289940828 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 915041807 1250 915040557 915040561
    0x17010e150907061b02100906020c09090d08040807060609050a05010503010b09060f061608130821160b04030801051c030503040f02030c03100507020616022505041d0105 74
    0x1051491a41c4580440300250a18910381036083e1481480880c00c04580a003604064006903611400000b10038143d80c0c4049050341401d90187c50309441200b0b02c0c0c460010b0004022906600150700d42030080780385002840b50b00ca624064541d809030f64001041e03e81406000710340320406521040c852a180c0006000702c0e640d0304141802ca84041c0591900000103500064050608101035041c1d4000507190394540303610418020300d60880341c0c008031103440c40090030800d0048180020300141c08a040640f0041c072402c1410002e08035003801a4401401c0403a0707030b19000034011001c5048540120101074203107003514008100c2034007401054440c401c00701c030f01c241386102c8401841c0500c1d450380310146161116180c84180100082e0100c1e070610a018030000180c400740140c1102c05415071000c240b40c10301c00c4029080c244024405d8440f141646904844a94002244142810204951821119410804040c820040c1c001d641c00031300700b00c0c1121441e030390300c4c65201000c42018000c01c081c0d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 915043057 1250 915041807 915041833
    0x21e12030306030105181b280e070215040b0402010c14060702071a1204021c03120b010e100804030908120702010311041a0d090605330918030417010e 66
    0x1070781c0c0001603001c140c0c7c4402910720800070307840305035662000024040a43c41c007420351000c2d0311075054802c10203124081c01d000c1001c500b05c545001d0700503690740080c1c05002c505052030b452080000780094201e81c034400c04036040d0b9000c0d041103011160400a01040e0010240c9055550f07082500c080b0014490404000f524010b0342c0340746038920156408544c6001c02e1504090580307480170300180d130310002000c81094003c031848141e02103103209444200e00c1d0319451001d182113400c200007440c148103030070403814519958251340304681d0f85039040c40215925103050803602038115400299070341c0704d11001c41480d20319050250102a01c02da906100c62284051300d00c55501552050340383c0e02048018000305401100060800301d88600000195a1020346906040d90425101090700240a0320070000003000a4076405281e04160581d0880d010707104003140000f407004000d888881544900c1660346003040c02220020101c00c403285070284000c0d60f2090090440e121040300d01d104100038860740b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 915044307 1250 915043057 915043081
    0xe0702010603031d040e01020a020a15020304030c06240602061f1a07031119060e1504030518090f01240507020415091506021011030103021e12030306030105 69
    0x203603649550b03511180c3c5503d49490701d41c0400d104c1000c2d8041d40310700d4009000d010901c09030201d16907650042801400c00e0422090300340c41014041600e5004008000c08079030090781c50511035500030710014500c0c03c040d1b50344030f42d04044003071100342e086400030000f01d566000035142d01500c0d1052407026801494000caa0383d180ea58844c1c05480c0d01140c42c00520210340d0701c09091702e01d000741014901c9a000f60902c6041079220300000780780c41d40d01c1103180c003840355503c161f03041c801c0e0006c0100102501c0e84400340b146180104018100200011004001c81444002078a0b403c009014201d0b2030a002d020b810501d042406408900407050300b0703480c15010000c012219804681e1503844c60140e480e000d000251092040042c1c401c400382c00f00003070380303900c5108000c02c0780a0709400711001c1d809c100c4020308105444000414503800c0080301c0d0b000102c3c0c5411281104e42c11603122400c050907004169418200142c0c0c2648141c4440c100580041c01200841c40348200718000c10140d130b41d803890201c4c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 915045557 1250 915044307 915044309
    0x60e0c070f1403130801020705120418090804080d050d05090105060604060c0816030c0209010f27090605040506010e01120c0e0603010f1107151a1309050102030a05010e07020106 78
    0x2000d050500c0d010070209640220b0358050441c14016685000e80e0000a05034008465002c051281e600060704000d10509010761040c240401040c0b91402c1d280289042c0000c0781c941c80d00d020682d81c2c0f082d0108014080007124000c10041050f43c0c0c400c0c0350042c4c040c01c960002d4000d0382e101c50905002410021741031152a208500091031541007a0070480c048500f201d24000c1200c0d0703044104194801d9898030706001b02d04911982d11513080d410640b040c0291820103900061000070414010700481c0c1d0101100a42820604c1c00550340d810000000d4000d04001c11000c0c00861034801071105000000c1103041c107072801700c40214040e903030f1094120f041d41407601c0041e2610784080824048920f20450b90b0340c00c48002000403c00501d198401c1c0d0854082189107074801c0000a080c004101d40b4030514440c101c00c0c81d0042081007103203000003000010a00d510780c4220407084e020400301c0307016800407000c603402030002c544070714004403241d0040c0801e001d0b04290b0b14003940003032505441406908 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 915046807 1250 915045557 915045563
    0x3063305030712110301090b0a0c0810091e02031f0b041802030a3e0c1905070308030c092d090606040518062b1e0b0703060e0c07 57
    0x2d509803400320035460050b0b888504850f40c4d6810608034210b90303001d0140c622968001e000003101d6082c4041d1040031a080c0c100d0740f40c10320500b0401c11010038070b0380340d00e10f046541450000c03900c08107210b44901040c20180311071152070300c048144021400c0805420404141d024107206c21251503002003100e5004d2407140c800c07040142c801c401640c200a4000e181c0003540d0dd18003003886240d01c010300d0342030044000e1201c0c0986260110803900480d1198003541c0140003801240303404409000d407500c3d101010f841d03001c440c13000303088002003000400507000115001100240c4030708284113000b1141d4851101140319810914102c8503550600101b0140000741c000c501c500c40400c101400241d140c0108043d500c04018400040e0903150380c1c0301d58000c3d4402c0c0c00070140f00d01d0148104006003a0880040c00155030191600107000303a504055144590050940c405c4029054850904240041001080744800005200b249501504036406440300525554a5a69201010b00780c6003d031602c00303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 915048057 1250 915046807 915046813
    0xb0c07020f06031012020d0206031603060906030804120302150406090c06031e09080912010b040c020c06030f131205070201031d03070b0c160b010e0105030102180f0a0306330503 78
    0xc010405c0200001d0440300e00c09840f14000c200a41c0000e20a41c104960746002c0085010010386a02e80c984501f402603c400c0c1401c00c49541551117010560195004800d09142d0618001c41818020040d510080f07213080c465584078902403800d078029210b004021a0100d42040c004240c0310300034061180c08a0083c1c04c1c050413114100160406810080c0080c0c2da0510104a56034142e1201900d55086d849990000701d000d04140d0180011144021840c40840d041036081c1081552078004480d004030710f00a1144041c0c0360684039030354403114401c00801c412407403003650142a8109011740074450003601c0800110290b03060034008980d14040756200c68008111702c00020b02d56061140c2c03c514655030040c20000584181900f90a4006040e00c400340382c00e004014a0603100281c81c05040f09600039030030480069540c04850301c0101c18144100c4040030f0443c40e50300c81c9404c000c01150008001e00c0422400c1c68082001c20f0f00b801445031200d11002000016007000301c500c0100c460140c01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 915049307 1250 915048057 915048059
    0x708240601050a1809060e0f04111315090f0e06010b04090e03090a091407020c01080a241e050a0e010303030213240807020a2d0b0c07020f060310 64
    0x11030b59544080f0b0204140b012184000f05500306400886020301266880024a541465500e4115010007040100c00b11250b0042100013010610002a2801c00780d40e096026440784e9119009400b01841180c81c8100708040011024216009500a52000f0307904200700041c485074580c40d25024007507482210010041080180030720f42c0911070002c487c60940b428a051440020100145a4400060141c413001d42d65107001d92a1040c541204841c001000c01c400c0d014006032a40f88010310300c910482d51180c91250504001600845502c62918500405a02d51002c00661106401a00094007861034045100d0070200c00300416aa022041c8100303580c030316601180070f9848456417031280e10f0050000a24090240015036140003d0b880d403030110300c0208402041c000000304540215404503c82c9004243c1111600003142400c081c4e040e58a4051014076501c10070030341c0001c3c00c100702c1e041005040500d803400762181d18401c0701c0032012a041c5400b0003002c2d010075160a807a604803008 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 915050557 1250 915049307 915049309
    0x30a0506041b0503060a09111e0418060c170612030712090b0403080c06061503040b040305220e070201140106080603190b060f0301020a090303030b0a05030d0207082406 74
    0x16104600038941000045240d40f01d5011905025043c0ca80045054641d00d20b502000960300030181e03100c006545000e004c2c1203420700510552010b001180c090b13540c1e8056141031005841c0d0b00c1004542005c01402a4441d00c40010a14054200c06011402010022034010324200261503100064200110b0900c507240d16500ca150f02203010940078442d10000000e51051080c0103400198003a038416515800c0412195080c003070001c04036445800c0e0b4942c01c40c100030a0754242c941003600407040741640e654a00c0c095441e40708a01301440d510f60045240e400c21101900c41c04161840c1810044160721150801d074240c6400d0f01d13302c041a11200c0050048034422a44076a020400600f00e034900b112518100020614451051b110008180c1c00c1103843d04003480d80d21440d1409030300071443c00c4100b1000818541c210b0100900301a218400071805c0c2c0d48100084014040040907654242070242c0e000c0e5580f885c034400d02c2072078021b8180300340b001c1d9089641141d50f210601d01480391036642c50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 915051807 1250 915050557 915050573
    0x120f0613052d0406060e13060b0d0803090708100903052704050411091f050d0f021224061f0c05011e11040b09060714010509100506030a050604 63
    0x200b076510100c410840b1040350105495028003200242565402d0608050034990281c85042e0071401c000d0f40c0c10000e004160322134401803001d042c0c201100041c0c003e05640024020380c440e0713a000c1c0495034040f01f032100600d00401c2c0401215020b004071001d010700e140642040c1e070746004024011490900c406108001818480f488491420803448006008d040000d021144281c4080c2e5281c000c00c000ea01241c140422410340181118500000c0503150b540c1050b50110b540c0141c9006803e00340590040000ca00381c0ba1100503801880300fa0000c0410409170354a003d42030f801100c01000345004502113542c01252030190030050f2940c1103c2440001140010311300750030400812105c47d4441001c18002e11a590b00881095200428443c20010344019916260104a02640c003040b0802149903544112960402c0030b560180e00c5081c103040ca807030b04080516811350b0650a20041155150b80450607003808800e40d001044951901410326683c0c0044820040495002001041c007082c01d40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 915053057 1250 915051807 915051811
    0x825090207140102120a0606020a0b0a1a0406120605010b070b01061b020d030c0201020705040c090e131502040e0a11070b09010612030e040e0316150f02040b120f061305 74
    0x650000c50b40444003a801608a03404007140000c1000342c0d000b4800c101c0b1301d40c01440002e016520091003548440d03107601450440c080e0100c6d854540d40c02c1c1882d0032070a48110040b8200009104200d1603690b420300c2842103400900c211100f614100000ca0500b00c0102510000ca4010b090a005a82420026620403450307030b40790310306020006243c0005965520700480d8541c840e41d81c411000782e540c400a40303001d005030400c0e8481e40c100201c003120702d03503c48954000c45132002c030b400c070494580174a1440e051400100142101d85441c176144a08000d0390018000c462042c1c40070101e41d955495444212245c200d20299401404c019403008204100d0505030864040c0b0000264a03944100710080d000400c0400c0300170611801c035406880c98117120b0b40150031482005180b90040c0780c07100140e403580c510801810741d00000120790180109501518041000d203004556031603c852954590303400a40340c07c19807403d110000f41080c4000c54540d806800060b0110410b2404642d0800240c400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 915054307 1250 915053057 915053063
    0x1e0d0f0c0f0b16080105041e15080d0915020102040506090d020a151d0f030606060c1005072001140112050a0f0f0c0e0405030307120b040903090825090207 68
    0x711104000204818602c018011040b9001500d00e0003e0840054280344059000350310552410741c800f000000b941d10000d10419170113800041c04114184000d100e41e5407074105c109070b441004020303a0310b41e82100a003000d44a000c901044801c1c082c2d0b10032801d0740704600403203400039420311035a1042d080c82c89915210354030062255003c152106a0713414445200440c040009044061000e5002542c0400040e410402e0f203c40718101c02e0707000800d42e6600041c12841c00382500240d100039004082c00502c000307000f13113101800b003401c10200042c606140c191003041c004174884100c54035000305100c0d04001d4401030302030310101c0e807908595000361001020f040c0c940d03004160f031030780004005003000028284507051400c10045503042c0314810400b55006800204081c1f024031010400000a9a80c450000d140c96016681c42ca80184090101d45581d00e8000e400c00c00c12004140d000b4041c2400e690004044036007100b00c140d12400c00c01d0000181d0014005608002d10000c04540c00074222940 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 915055557 1250 915054307 915054323
    0xa03050601110d020622020306041415101d27010f0f2003280b0916021006050d06020a142205060309190c080d021e0d0f0c 54
    0x29660380250f050a0b121a00b030700058000030300b00403008480c2d07450300b07090795001d85e903d5524030401d03404603135180d4010b0800340c48071444044203d00d1240411400007c020800b480e0003032410b03c095196540b5580b4041c1c800c1400c0c0900002c0604040c009459105560001030f4415414007486040070f014019103040a02d952070784000100c04101d40162213540481002c0041c0d034107480025124031042c140d80f110f81108080040c0061029071614280400c145030003080b034066a030400704402010768500341500241c1540400969070000510001402000d03029200519149030414085614500070264008131100e00d02c0c02046860740542042d41032801c0c8264405a0b810b806403058001c00032031a050710000025141c6011881190340040c0000d51b1400d08500b042d0b0705003621006242806050030b44844402014001912101340041c1200c505590b031143c07032031500944406180d50044150345541c0e04071200700c0c50000300d40c034104030144e0310150300d0301781c40b801210001c082c0741007030340c3d107003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 915056807 1250 915055557 915055577
    0xa050d050c09030102040e0a5109020a11030a170406020d02030c0310120209010501111e0a03090e04111e0306101502010b0105090d26070b090c03030a03050601 70
    0x18030244000c10241c000142460840d140c40407020742503580304108218002c209d0540d9039490702c8141d01400c403a4181951103560075220b0254610301280c40f07801c425001c2c0f078590000402140f00e500070701942940d03545000c0c92150002d000c541e40d100b6010210000344020f0700c0c4d00e42200b410f22603030b82c1161240b0307030252a01600c8a4104140e0700300307541620302e020000003440692900110508028000014200645815500011012841445094103000c0e41c543d105c1300200d01480445d05110441c20440c00340000142c0d000e03500c00707070900704401103041d0903004240141d01250143c0310750307403202d0059000c2041c41c041c4070b100c2d0302d001c007000602c4c41d10141c01d44040c1d8061210b03d11440e040d040c41190680b82024400756510355075a0032040d0b914240704010183d80c0031b4119940c8040541d40113030804464a0110b40a0071040801c2e0a6818a0400500b003d18000008d0222600070f40d8461220303110a120280c9410b281e0f41380e03e42c075500811040c142240a90081644414141031000104c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 915058057 1250 915056807 915056809
    0x18021608030907080609010c120e030c070b0306040b040204030c05061b010513061112011401020c0402160b010b03090a260c010c08090c24040b041203080c0a050d050c09 74
    0x1e4006480002068108040910200c1d50810003141e10010341002400700030081ca102030a130544109070100c0072a01d0300d134203c0307003e00100304940300c1c1c403011011100c00315620002e240d040c0d04265201c510407428003001d05500d00c0c1c9402501d0549410036800805d152408041081c2540a00d03144006151980106664280d007889514840c4032a00e05041c800e08052401c0c2c2c0c1214102840e6001040d42440030440b04541c1314106419100c3e0412031104298000c0c006030301c2d01c1024502203611500001c4c1d498a40d2128980c0e1140840c811655210983d803941c0c05001e107800308440c1341403a5807110480d000421480c09058040c81e144038203a081000b002e5100f20001c0e40f0040b0300b40b12a83d103440c0304981030369000b201281d1000600d405811201c4620700003503a00010030140c0460785450b1030716040d1030b090302001c44000f000f82610171559281e41d05900c0800f04403000081d00030511940001d244280130717000302d4100000a54072a854070b0360344044d0034000c00024100348a100c8080c084d42c985 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 915059307 1250 915058057 915058073
    0x3060515030a11031305120a230423030c310908070b09060604051003080f0c331005060c010914100b03030a0203191b030801051801180216 61
    0xe91480040a00d400c032142089071601c0341d844006002c1c2c07c1d04100580f4441d51010b44040d040c000b954051400b0346011030420401d000702d401c014100c20200d01d481e008031038200410007928100740c4c180e51500401108011005003401c2c0074140b941524802103030300d00161000100b0301d01200c54001051070300ca8890001581100034100d0700c18144409000d0003150401200b40e0081e0112424090307440e0042940004100c90f206c002d191001c0446e0702d044c206840410341e00e048030341500702c2e00c0b4115400c1d04401d901c0756291580b440b03145c9190070684842082c0410b02d101e81c1c1e00f503515501c3c5916240c00c1c40201c0c4d20103803c01c03802d0355035403d010000891b000e02c900300c510003050081c004064103c2c000011a0604d0180380d00c40e60003003003116005c50b0040700f981e1f16110860740e03c0c1d961018103942a07402459501184c4400748007480e8036000c240c1c0001c1914140e40c000d48007124160045e07843d10500304400e0041da20f030768003203a812081c002c074203400501c2010380c04200080208581d50314091 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 915060557 1250 915059307 915059311
    0x20106080601180b0312091c02090c031009020a0c080705030c070920040509390304030e03010c0c060203070c020a0306060e0606131a041e06080703060515030a1103 72
    0x703c0000c150f0060300c0a281e60240000071002240600b90030408072100004512035001d2041c008c0300c0e04080c0c1620004180c03800c0c0c0e00c554000d02141c1d147c1c58640058505a8011215841448600d20001c40c4840c00345c070945004000ca0384954001a410b6200c0700e20503041075004441d644001c2042420006051204200800ca500c40210310800c1e6445071741d000035a010061540c03020140010015955803414460b048145070b82103008842c04540400075451403615560700350001490405420071542001f1841341d030103030381e85075540041a4101803d80d035540104400140803041e01d00046200c5500031504240036003064000c20309543c1c0071881580c400e0780706607203940d610074080009002075514203034411000c5941a24007410341c1051070b6004040d004001d004082d05145070710006403581114080d10603002d0403807000300900c549030b01c044c1c40f80c0a0a03000400c44004500440c1c0039014804c2030300c90090400c24422071241040000c0d0300010039140b00c00d80c031104456014410781d00214 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 915061807 1250 915060557 915060569
    0xc160b0402040f1e0b0111100504110a030f060612030f031a0a0306020d0b3705040f090512130e1003080f04060801140609010c0201021213030b0a060f1203020106080601 74
    0x40c013242120344183c02c40d50071801c3c060510403030742810302d045403001c9080400b010f50310a000800751030340d05140201e140c105c4151070700464200004801d0150500031030f59140d09c1181c1c02d00c07200ba110303005d59a40310609180140400c3c181030f640c0103034034007940000030004100050f00d0744080c500c03000503401c80540c0c5d200759080e40e80009d19071112912070040c0c4014030025100404210704688203108002151040302d440c0c3e040e211803640c00018214240c4004080060003401700084400d41c040003843c203440129201c3c4a42e118003412001e44c10140d44c41220383c14016180e8520b401d0f09480400e60013415903110260101c0301000040d89480a025200316540da015107843c1040000744c25128180c000328005c00d1000b840c503c46640d08002c8802400c401e2030701c10800e4205100503131421081c00428009980041131030005404c0d80544041103078000c5960001c25158001000c1c100d4006001d140b40d244080801030001e0111a81602901c2d4440d20000492541c4c60342c00780d0030454283c00c80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 915063057 1250 915061807 915061841
    0x106030b0403081312110111040b07140124140d02010e06091f0f080709080c150d0608010510060e030325140705090109140f101a030405060c160b0402040f 68
    0x711b20307942c0342441400e0010b200b29028901d00303400e0070907140050080b101c0c02045401114142c204108003904403c00c42642c0c519003401107040e65040304100c907101c0c00303103540c8107410150120861134069088c258254040c1c44100c02419010140541d5900907114180c1041c40b5040c2c0d00350684003642050008815070b80d82c903600c028804070003000c051001c1d0a0324200700b010700b41844024400f1503082006a030803100300510781c03c00e01100c0401d014951008079003a10704200020000819040203210764485001d4544444d10307424181d80c01c80b10645015011340c024048800100702228001e00e030342d8214500c0101d50241d50752034941c503c0c221415940c5a80242604100d20705001c415075000d420300001c1481008400031825840c06401401090024401c60228007240b0102040070b001c0d2030034039040c001303002c5503001440740359000740c80032a12403082030005002c1040b141d082d04d00680d401d594103e80307807125850b240100e85016000ba41d1050b03841c0315000045000e4800c000035400001c0320 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 915064307 1250 915063057 915063077
    0xc030703020d020f070e0424060609050316170c060a03060f0b0f1e09121506091006080c120f06010801091b210608031b0106030b0403081312 62
    0x2400c11040380380c54402d5501005180c03030b455402003012003d1b21000002c2c0f00040da81c03410115844034160b511041c0d06949048080740084440e009130054542da62640c10405907508185a0307030380b40181510000d203114030340520500c5220101c01a0f40c0c0b484c0300468200c8a035100000e2020b0f0f0019400a020a0751260b01f048058015400000104410211681002c0301c0752041d02c1e15225410303001c04624525105e5031013040720102903c8552102806680c0210010007481e642c2d001e602081c003503d81280d10015100d03140100c01a403042d0140f8002988051404800740d84600f0b020b04507968401040c8180054081645400b61044d5a501c0c0d1800ca5070070f000c4000340214406801c4201050300f00302e15100c80c840c500900e0b005034815494000d0000e002002c1705d210181c0a507090790b207024207003000000d4480380000501500080e22480ad204408410041d5007261301610005100f0f0304181d0001740400d0042c03007201c0c3d220385600500003008025640b80160041142c0940000c2240b42070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 915065557 1250 915064307 915064313
    0x4061409040b180a0605060f0f03071e0504060908280804091a0405062e09030602070605180118020402090111010524012a030512070e010e010810050f04110c0307 71
    0x5a0002406c3c143d0f00c0600c2c064030144c0174401d5200380c146c200000040000420300151280e900100a07a40400321200310342801d0304020b009600902c907d00015410400210b41064003061131480b54a07100791011107084a40360f108039440e00e0440503140d03000c084c000000c10711610702a403280540103041041c02d001d1a6400c12046a401800650041c00030b4540312003200c55100000c14000e000c42e0610041c412a81812101c0c4501508014005800420520308000003a00a07034003d243c07803074801420041000f0240d089903940e040c11243c0a40c0e120b401d00250038980d004240c0b034036062500f0446110080c4109003034504c190f076481415040341d040350708071547c0d015828100030024031700b5030380380d444100801042024100c1b050700b42c00c03960042901054010f00031540195041581c800c030a1034481c1e40039000b0101d02d0691808980e061006207000c1d8031407101184141d05200d18150b0290501d800c3c0000024a80b00d00c40e00180e4560300e10518a09060152900c0c00b00c140046d40c0d0741e08145 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 915066807 1250 915065557 915065561
    0x319030f0e03130515090d050601141207030303020d0204051806240706050601210501060219030503070c0c0815041b03051015170d030c020304061409040b180a 70
    0x50240707865900284418605444900a840c0442c0c2084550000342c00c4000c10201142c4a03a0100702e6024030b00c2a40c02d8208140030401c54106d401010441403101a07140c00d001c0041d885043c8401740d60450b00c03080c40080d01a901404060100c51401400c060725900801d520250304284040700c583c40104008081c9003500c000120b031200148001c011540108001350240283d00f4010702d02c45c1c83d83d0004465911484030b40c0012440030040b6080021a540100000e2500b801448018041c1075101ca80100c5c0d841e05106403154180c1e6110f1859580c8841200c0078404984100d8010050076000a6002003c010364a0282820381440c4414185842e08254007055030380710a00302000c410040000c0f0380e0119000c04680c25620000c01d5580d0103031000301d1807400b160080002d0101c0c042513550881d1000462649039401234034104111441407005907641d000754403903100000c4981c02c241007180300000240c00e054101400200b01e41c0d203c60000703030560391240c1e20f11403114034001c20000000340300c3c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 915068057 1250 915066807 915066821
    0x40c0e0910110c03090d0203010f0603080d05160c0615170c030f0f030304080d060315060302042901140d060602010209030d0809071419060216050306060607060e0319030f 75
    0x104103600c1c24610700a56522401000340345c610400414030f54005644080d085122420101d4200700101500c914040c1c46a4001c407904121040c0341500144200c3c030000241d01c03020340e030b548910140c0035203a56400c0c050108a0807a00500c00c0c05500040e0342c030309000340e00d0f0501805001520a0040503801d062408141c5101d050b000d622030010018980300101c102ea1b0000d07001090799560380300040000c0b000d86500c0d4401040071050302c94401c0b81c1c020580c048000e49108840c140446400005560450728244c0d001c00c1c190010100210341c6903000301e449084c6444c00f0464142001e1130000d50b102180c034560701003400f60b500040d1a0000c0d2500f13202200078410035062913001070400070400c658660789030182e03281d4800558400d02440c0d0310000d03c3c0d0301e0b4404003889681c81346c2e21a10002c0d00c0b401040b1701c8510b0410101c001240601d008280280b081d18050b0440782071942d191181c4001d019030340841032090004100003050558000844954a44c2c13503100440c0c4503020700d01c0c0c2401c41d044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 915069307 1250 915068057 915068081
    0xd0201110403020a0303051308030a0e0414060307090b0d060501030501090311071a030a09050a1b0b0c060f0c0c06041a01060503010b0a0309021f0309050601081c08040c0e0910 77
    0x8100010b000513900e0302e0b4940c0a50707416280c40c68983c5844042d000c001101c1d5001914140300204600740125448400c48005c440166401d21108241d041501c03c1110b05541e202e0303150708091070510540392543e00c9101212401400c0c10b505003490340350711007112004e80044c1c410f81d4603004410185a00032030030148000b417240003410540c1c40c001d40000d0290381202c40c12071410780080441c074030b507210390459490175400074282d400d151900c1c94001403890600a000f821030701100400a90010b44030162002e82c2c941201900040d90348882002420000420441113210107101814004404016070f5100e58401e03014400242400c2d5030b40250000141c0c400c804110040006011388242d000c16141031900d181400318140005200003010000b044014402140741d05501d0300750290f02d900105202c900400580310300366243e84105464420b102c41107000c0c0203180140e07000d501d1040819a5010b40100044210541c492800c0c81c80094260380d500c1e15030744540350700300207042140308510f84414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 915070557 1250 915069307 915069341
    0x601031703161d0a0e0601020d02030a05090405101a1210060f05070501110a020703110a030209010e0a020f040905060f01020c01020c13020415111b0904171b0d0201 72
    0x42c00c01107003520078107100e0301d03031082202c030700000700109031030001c5100ba210005005a4805445110301020503808442d607500501c100041c882c142030022089896401d1990f6400d031a0055160910000d001e0280c8880c8000c8000c13440014040c003a91404080c07042e03400c21840c0d0f2441810780e0a00d05d8030300038200f00007001d8806410080c050700201e44481d128082d0501c1034540440781007442c01000c0e0048505074100d000214030f644a80e020038002c0689200d07481600300c1c50441824802c0c00d244034000290400080c80060260300002c4401c03035400460450054a004001c1400a46a820661152400341c3e101e40600040d0314100d251400da081d070070310003001c4008032400000d540d8071640307884c00d0158004151007080c00c050b0343c0403540940f042c0031040802040902d00145841c0115010400e54050000d07500c920602c2403002c000311190084c0300c224070b620303180c903a4005201e12918412004404001c01d0002d2551420301c020507101d80d001600d03d03900d02c04400390a4544425550200032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 915071807 1250 915070557 915070561
    0xa020d17010509061e090405010e10020705030306090c1c1a0429041404050c030601062c01120c1d01020106030201022d03190f0f17091e0601031703 65
    0x511180e14443c4d004a00705c1d0340c4100840410f20048005450800d5241c1001c564400c10061283c150000079112100c0005c95508103030b1190300c08102e00030a10020200c9e0010008a078450ae020300c44540c01c040340aaa00707140c11200c508031000058000d071803100345e40e1601c0c0002c00c04112144203d21985050b5030078020880172103d0788081a2202c8403410551410102a0b544c6407915440280b20000180c001321072400e02e414980c0d9100c00c0c894542d40b1030700c200d40c000f14001d44101102d100804100d80509400813107205650b241d0311a40341c10030304100025070f034140c0740d600c3d901468840c0390302615400c408203034002905aa0821040140307055a041c00320400c0140d90001c1c4030360340d03459061307142c81c0d00484055600a1400038404c201d190741c840410903e0300e0080580c004185901c80d61121516000645020794506404003403e1002c03921072105505203a407a1107506038007141c03071403d881044c050f400d406080741d218103a640d00b0a41c0500018820000c125654000c1501c0d03200c01c0c50300314 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 915073057 1250 915071807 915071809
    0x30c0d1109041104090606050907020708070e04032d0905030c010e0f0402040e0c03190501030201140d0b0301020c0304060e15070f0c0b0f0a1e020303180a06020a020d170105 76
    0x124008211580a07440c850000740522080b5040e001094a00400620103420207091002c0079294502561340b00b0354581d8017203007a00f400080c850702101c09140140c043d081c5402d246071038904000780305605020211071181c21048401c1035044040d04001040c3c04603641903c00100044801c0e001039000e5440310505041c10303030b000001c0a0303040b1b20840f009921001d10f000070038083c0c01541c2c0950010542c81d800c0c0b151514200700a10b21a070705c5401424401c0783c83d82c41c0740d000c0c1c070028400640401d82d20b03044594580050784c02001200030b50b0201181803d001008242240c3c42130540c1d1005400125080c001c296000300307400300c9088212043c1003844d25030301e2a20040c7c0b244880040540b00d03e0182c030000c100188410780024100c0b825501e840c1e2580c1c0e4000c10700c076800700b100f01d030004902d03036100150000030259051994086a0065007141e481403c0da440008507a100001e1030f02c110740414000801600007012030a2107580581008070341d9080c094040030705440880780300303000c000040c405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 915074307 1250 915073057 915073073
    0x2010f140403111b04020a030b0402030c0301051503070c06050a1506180f0f1202030709060b0405121507180302090a0608011524050f0c0703020a17030d0c022a030c0d 73
    0x8000b100310f1700103030368440c4a241907000304140100b82e60083d0010041100c980d060340c018504a0340309031440108005c7e0070002400ca0311003241c1c1c07600443c1001d03078500080f40c41c0e40d2103541c1c1300b00354081c005840e6183c44030004c92a9080e500500006040301804081100c00031000d600800000c0610400c1505142260311001c4040c080d0a000c81060a60309080d9035080081074014800b1810130060b8503140c6600e65103650260103070714002e482100410300c140d0b10000312120010f441c90710701c03800d64558080c2207802c031409030040c140c66407100c02c002c0096504c1d00442800b64040090010714507141c680300c1402d60300f6404050b0b00040010408019a2204055111001c008404100c00035070103c1070070384150103648840c001c608030105000564810014107081a280210b03650b0131865030310075100260000384280e401c8242c0051022208070b0b5400e401614080c104d5006030344140d04101e000000710315001c80155501071402003d2400740c03e0900118440c40004d44500303400040d107031503400e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 915075557 1250 915074307 915074353
    0xf0b0f0d020303040b0a020604111819110c0a02191d07021203010306020c07080327040b0603040b04060b090705031501030f1b030501050f0d030f02010f14040311 71
    0x4000c00011000104655041c0121005001000011515072410a03402540c500d01141c045a40c010840c3c5070b805a4035010180d1490708a65034010703200d65481c3c01c0300126074440710304104c40b404c0d1121219148a0407600180000c911305000a204070f204a00401c42c000b0309062954800c000c180c0c500340f1000101c130410f056605038091128a00e526468070403458800344a919100102001c0008810810f09400a10503440054203c50810b502c0b40c00030380d228881d0b400c5040e0300099160310000341a5000030181e140010007040054494070b070f036000c102d06900031201103d082d0711440c00c0000b001039602c9100591401a54042d45c20701e800b51002d011480050070714145200d941600f02d000341c0c42500864583c440c201e0051000c00e140007603034480301c3c00c0d1044000202e0b04240000c10581080e003c3c03105001801080104450030703e8506584000b509044030046548401c800d109285142c002c1da05100800d42100e00709190608000341400381084140146d07402540400d0307100d0401e060010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 915076807 1250 915075557 915075559
    0x120a0506150f04090627060807090902120604140f07120b0901090f080c0d210b0a0b0f091201020712080c0706091110091a03070306030203030d09060f0b0f 68
    0x1540c80b2001440d40300580210760001c0380543c1006404100e03081da00035070313245c503594490b1856140c81d5030a060405841c01e6004241d899402804c08101d0075005800620703040d400503291441140c62850350300c5c00e000c070842c0c098402810540070045036880810149241f9196013000d0040b81e418019800c5800c6410803010780000d0071b0340d0115411000a40c815003d16a110002c2410721441d803038001481d030400300c21201c15000e03280e15024000c0c060b2030b4036072600071402c046240308050101c00000a1040030703441508040f5044010480324007400007842c5003081350348101d495080550030804c1e102401588040c440e4018460703000003808c049124880c0e54550b003000907041c1c2e28410b10440301c2c024040040d0007581451941814040781c0616035a541c04161034240404036020420b0310844814032402012031005c61900a1071003016001c0e640081282c07601041c0f4654a400080c511707000a804080b0042d0368540d01010082148a061180d20848906109080c0140001100c0b031400054071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 915078057 1250 915076807 915076849
    0xb0703020a17040905040b0403030c020a0f0b090120120c041413020d150e061504060e0109030c03050102090103200906070204150305060103050d02151611030d02120a0506 75
    0x503038030706034501d0980d00501340d90002004545003504100c501e0f2881510142d000c20324144980f40f200380701040082c8042d030000d070340030800c41c8641d50704d1a45400040041010b556100c901b10b01c00c01c1c604180b148080f2446050540302c20b0301c1046020b8001c40a40120200c4004000420503e00340d45c207806001482150b14900382528115840080d10582c0080e0924900e40310411000003a0480304500340c416042e04800240d807010188600ad90800030b6100c9a400248020400d031481960020101a018581031404643d03a43d500c12001c10240c20865036a50040381c0341a2a5a061040005083c0e11100200c00c0004000090743e6900c41e40c070240d4003c0b800081d403101036440345d4120300416106204121070060b5241400da803665400c0c0002c0301d05004540400ca0f03090f200160780f03038041c444900450f2040d2503036010b0b017040302d254180d1003081c000380d001800d2030148144007402506903200390240c0e441d0080081d51806100c0100044a060700e17100c103003c0c0c40d8441c554207805540160800d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 915079307 1250 915078057 915078083
    0x1401060e070513030605130b0604181211030318150601090501030b2106013b041412370c0206040e01180c0201141f03170c070b0703020a 60
    0x2401e58003040f9404c007601d4a4201400d00c8403461350b054950512601501c4000c50607100c140401054603041d403004040a0548484280810400d01e16180c0e010094107040100c401c0b428505410354004441c5400c41214000d0440121541404507000794000052081410b02e01030740043e0200949008407410140d6400002c0400d403210505503003800e911400520400d804401019940e107024010040120303009403e100b4465002c2404080b500c103100181c8800105000e19010452801401610741d04003840e1189001d500600000810360400c1d1f2003103695040600402440c40d804207512481a08207018849650000700703014020100c0900c1c042200407840d0000030140d0041e038216802c540d0200000050564158220600c04505000b041c000700c5201001a8201c5200344219045015940001030000010f5001c02d106c10713084e01700c124140d503226280d60316900211440460320040018621a03040c104101100082c20503840c030703030b1801d00d09075402925041c8143d0300910308410200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 915080557 1250 915079307 915079327
    0x80106031112130224161106030f01051905060315041b03020901031103060906130f091b080106061218021c030306170304050108090304050a121401060e0705 69
    0x840c1d006034041c6240b2582c0c1e04041510601a0422541c200c0c465200d900084040c00c0b542030305441c10000800c0e540f400c2403001d4116161400900c4400ca07034130a0707130b110582e025640d00d0002e107010300c0d85082c8400c503a60400040c0807035240915a10b01c1d150103e031500300324a641d41070469900007481d014403540c8003940d1010402401500c585018640342c48805000c4881d81a03020b016a04004d03a13042c0700314030100690700d146210949803103420001c0140018450b040400c0101c01e06200f502c000242d030307074002c14803008854031080112184003401c10400003640036411001e01502c0301c84002c100c81da02e0041c01502c94020042c00c1c0489586030504a0080c00c082201c0c00d1216402401001000c205001500d03042c40445c10128042880c11a001c92141c2c5000300841440c90b901000b1803400c0d0400c40159030131980280071401030b102c20070020420362942c1c2820801030050303825041d181e095901e01070320030010208808000d030380f40490811020350b0200d485600b104d1541080c1d0340da006029 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 915081807 1250 915080557 915080591
    0xf0d020705070323060a05040c06030c0e21072408090c0414071b020a050d1e0303020a110f0c060f0705060108030d0e07050607141f09020f040c08010603 67
    0x1d840a4540304102005a0b0460203044e41903600508030340649441d82c4e00c1007600d100b11032091b01c0c05070a071f02c2044030901a07180a40d010701a00e0085041c410f1407460000300040007a1032801407131003030351509102118041000c015500203011018105000954440106580031401c45520b4042100040c08101c05050070301c4581c200705000782041c05032035440802140303c440150361314000646e401245a0590003030b8031034400b2043d03009000202c080c0c60441000344c121448035060311030340442038420f0340700b4500591003445a8481e0301c015031606d0f500140500152401d003203082aa4200c03460913104144081500100100d040300c0640c2c0342e03500040030344510301440c28001c0061180d400085141034000002e012808401802400011107102110380c03540403501c00c06400584c00c6c4600b1000800d101c0004664405002c1114040f018080d512200c650180d803440001c00d40e102001c00542c1032550325120501c0094800340103500034440e001f0000c140500c602000c1517690848003030204034070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 915083057 1250 915081807 915081809
    0x60e010201020322030c0f29070210050709080106030c031101090f03060f090213060806060a0821090616020415050d021e3105090a1502120420060f0d02070507 70
    0x3200041c85141d04510703040040c48e110071800014069651000b01c2800080c2003500e00c218025800360001104403800c40000d010050416002d1203490344001c682482c0c02d00ca40c60003903000754103210a6078998108a45c01911502d82c060401049400a2081842c010290710450f54130081c00034007183d01d1110100185081c0500030b50110003002010480100c035000501035034585015203003603844040c104450300b2500d2207000c0050300000c4c004400e00400c030080b18940c1904203845071501c4c040300c000640550240ca08101d03901e2043c1205000d5040a10032407a821215082c40c0c404241000000790000789035000c02446500d1404451051105154085a415102034142c4036040c04c900300d071004101c501c98508404590300d0500800104103400b40900481110018280d010b820f03031a2814412088010340d44100d408010101c00c110056810301d00c21405005026500300115003010b940c0414850134502c5160188680c0840c5004003045880701c0001010060323a031001442d0403414407481d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 915084307 1250 915083057 915083063
    0x60a0626040b04150b01020a021c141c03060b030f0601120c0509090a09020a1203110706031e09050c01110c040f0203040203191e061b0207060e010201020322030c 71
    0x4080c05100811400c0c03031035240100c4c03182034412540401c58070030100300c07040c8516160069201c0240703800035040c84070072040390b51101c08024010403142e07110f00c0360451120000440c140e100d8074036103030a1402501c030328400c50303d00d03d0705000040c0b9015010f10b00303000241041140c0d400c208003280c9203a006040c810341c074540310202840081450040604a5006140401d01604c0d04900142e40e6031203a00c152510154000c00303208615007000b0048040c8066000102e06219080780c210613040c1d0104219801082a17a501090f00300c030610384180c4052156042401940c103103456440010400728060700020700a180506894541c82156441c00c080f03440704075002803a10610700525080354008500c224000d074106c80d580c0c0665818903020030f2000101401d20326280f100007000b81181c00840202e00e02650000c6560f800e0518420040658034142c0009688101400c00519400c4984041030780030900085003546014180c00440101415818501c017000e507014500b01800f8404d420f0f04d40d50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 915085557 1250 915084307 915084377
    0xc06020a112e02031303030b060c07090501180c02070527190b09090a2414040b1005010e040f090507090b03060a1e0b01020c1203120609060a06 63
    0x8000d5202c00c014402440151400342c104000d42d070384149802160302510140f503507048080303813984044004224042d40c0d01c0c4c3c071410030046200304074400c0207004090482034000045a5247c2015000143d4044418004040c10408102007017500810310008451055491415203615000f289a9290035412a890040c11010901c02003e1440d40041442c0724007403030402071100c1c12001c11020417011241c401e051b034081c0880500042443c20a07401307001070f12a0b00086003407113110400c1074840c000807480040b41c0b103100300030501000000c1a50030010700c5071b007110750906080000749851300c02040d440c040d5884512140000c0000e501000d8000e401c00700f0b480d4042c4d00d491441c0301804206840700d00c01e118030b002007269000d548c8104110074a2085034449100e1448807058081e0080d008814154000e146000c8040e4132886c1d0308096843e03148000c0d59a07107092240c003041e0081e000d00202d0107a00d60008000c045e440d4520713008142e4103a41080c1c003400c212a0100f030512840b480c11000900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 915086807 1250 915085557 915085573
    0xc020f1e0a03140d020a0c1a040b191409010f08040f05030f0406030c1b110301061a12012102192309060103050c0f0715020c0309011d010c06020a11 65
    0x100300d1007020480069450103032011591120750480c0d0319920b5210251180000000c10002c40e0904d03802401c4940300231150b1400e2a644500ca41c509403c25045031211001e41444004a6035108151440419005070401d0034481c40c0000240307a011400080d006016464012809001c0c80f10000d0b064a0b503c9403c0700d0340c1d8400807410f040700303400510038100840d003030040700c41c13209004070a01180038800c0c051610090a0310303103070500c230103000810b85034255694150102d26a9018030a4a509204482c0013035510b507440349a0300d90043e13050340a0410581c000082c284400c0c90038035084c3c03610b5012120300150418181c0f882d000507003260702000c42c140401c64200c2d04442c08980007484464201c41c446403580d6944015800c0e2001200d400420b02010030940000b09600000f170301650303000780d000b0b9050102103201007089a01c4411458580e0344041090125903a0100c0e0f101a2174070980407004e403801c40f00e000a02850000240201025004a50720030083e100e80e000415003c13640f01290b11607 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 915088057 1250 915086807 915086813
    0xa050601080a12021b040b060d050c04052407080c1911012705122d01051014010e0411120a0509010603030914030c06031504050105010c020f1e0a03 65
    0x5040c22642c210707000b03511060304685050004c60312400d100b40400713440700d988504404100c0140042c2425a0340f04070140326005503c00e05105003446110411109a070b079034108010011071452011007401c07050806003850031458201011f60700c4280d0300c88141c2d51a0841001c4003410702c1803428811489120351503c1500f07000c001031180c25031a9003030b212810800c8060080550007401e01c8076000e0b04c0398000d6410856424902d400803200c9080c0c1d403e841c03030200c9110000306125602d5901d0094400804041c0500c89003c0c4549900804100c100d0712445203012000c10300c61000f00407003418070203291140c141c0c0c2c0d12a504615641e000c082442d90b510006151042240c100c00e8070703121011441d040002c0c0d81c0c28814806d990a40ea0503840d401401450214002044020314407074a4140c0035043c0d013403c00d52941c50180d400f8401d000c400c1d51001c009902803001b1104160b00a40c1004100015100503803200a00d182003500c0c140c480e1001080034a6078001400611507542e03403c03000c061400028 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 915089307 1250 915088057 915088063
    0x302030703180e150a26010e010203041e060225060e1207060e0c030604080703020c19090b0d14010c08010503121b010605030d0314070804080a030902030a05060108 72
    0x521030789400501501203000886141d0b260b0080c150800c0890700814501d641504212442c408000e040c1d007200e50720740320400e991300840740042003000841721032840740d08401c1c0a0b15020a004c20000c41c290718290b1680c0c0d03004101e0546441c200301900101c8018410b1540485503040f0030801c03480200b135135150f8a4070510041d00e400780c03400f0b4502242c3ca910300c8000f00310712001e01d035000600d500300101b41d2681001414006404686840781e0811003003941c40911011380705902580e407440c4c4a18003030401a0500c0b4400e0326151084656048030b015450640c201901070304c50100000400c0b032040d5010409a100c01c041c060302d020500c030044039001030150082109210141e0304c402469a942044c0340d6521000d821000c4514014001c03504105400003046981e01e60300c4001180700d69484000c42d040011014034a000680c48000181d0040d04114145812054a2500704950701d41503c1e507240700d000c3c41c04103200701902d8a507010f003959010090140e110707800400380c501c3c40d6912844259 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 915090557 1250 915089307 915089317
    0x605220608180d1211091002030c0d030b031009050a060914070e0c071202071e06030c0503040f060c050f0d0f06080a030801050d031407060507110f0709051012030203 73
    0x400d00e1802c0d844070301c004011400b180d4243e0380b51608980c218a5104030400f401c01001c41c20400c1e1020f01c8081c80c80d40d034040340c2001c012a03680145035640500070142e4101800302420105047c2018500c6034940c6002135910040710107100c000a8090301482e00e40c2c1004112600075108a0900088406114a01b8041c0040340302000842c0e6a0070342e203621406501400b140d00d080280b005020b04004260101202d0a0b160094815591101d030bc501858000001d420a00d8003003041c007a4082c0070454252150500068103030804508501d019903035040c5003020500000c04041d1a64287e5504030300a10a0310075210750181010344070030001401400070680c031f201c800140e50502d84c0c000380c2088081008440c1036016500c207682030303082000b840460035660300110100f081561244e4401c16035003000c5e02009204020104860400c0e4000610000740c8080c00c20480e0490703241024240c40015600044490a40c000b103041e0766860a40c01c0000f0855004940c1d102104007007404059022004103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 915091807 1250 915090557 915090571
    0x1701031e170a0e040c0c1e0c032405070309230304180207110f0105031501050d0c0e030706021603150905120c06070c2d080a11060c130605220608 64
    0x241c00c5c00c0d5402110f00c0003000c00c000c0e00c81c00469180c14050785268016650150044c00c141280a65998a0b40f0032007c1c81403060f414112100200c04400342603020b059007010342c524080c444903103c0e84804407040c40110b0702040c8940c180c062140301c4407050023a1002404010909070b903040301c03800e03401c0180d407020208490b10501c803040300d0131503d01505170324882d00381a9141421551030390b81801ca480f030307130215150510400b071201c1c00003030b210780c000c80c18038004035503c0211007034000050510700030264005009542040c3e0b2502400c0300c9142045044035080301e01200400d2194804200a0920170701c041c1040c0208081d64205610720001420b0f40c0180f201201c00960390800201d5500c4c1d0100d00042c042511814028015100d001481041c1282c076024011001850f07914207466500980f401c0e0042a10f1102d0103080c448248040d40c1d01c0320441c040c443c58070072117030301000d003150550081c8428400e02151820300d07245110340c00303182240b800100440c2152112805003044200311502 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 915093057 1250 915091807 915091811
    0x3112710030507081504020112060806070c23030327060406090308130201050406080c0d09140f0c060d0c1707020102040e0702191106070f060204061701031e170a0e04 73
    0x121520b000503501190031545c10080e500351165401141c031101c0880d24210056112000459089005d00070b83c1d01460040d100d850b442a25441c1130701e0200c81182c0c5442001c18024840c40c581c0d0000700c00c81f9400100344184000d102c41081840d17802c1f540601c10144d091003428100002c2001c2c0341e01207400e813406a21100d030140d559013813852400080d21002800500180400c001d0076024450403500051b2010609080407038110507141169800401503618070103c0c1103940c0781020a0041540090304100607103148658180416074610641803000005a40c4262032010b003071042c880c03854080b00d00c0e524031485040c00d4134028003075003140c041c200c001d501e01c030046240c0c5400050034165104a51081140ca080d580c3c840c00500b0b80c4480107687c100a08200100002d5002c00e20b50031242d2150100680311818800c000f01507022000341d2944c0140d00c1c10040c0081000e14405605c00580c0d180d00d0703940500c032450400c1c0000c58062000c20074030030100c0ca12100c0e80c0c200301166200c0d03805a40c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 915094307 1250 915093057 915093059
    0x10204080303041514010803042c040f110409020604120206070803070c03031406131a0a0e10050105030105090a02070f060603110f01080c0a03090c03021503010e090703112710030507 80
    0x517400800c00f017845440034076031003080108959140e54101410501613255882d03034812a061000f4015901190f0480f1200041c0a200c0c04121880b11060303604003081d90100f04103119a404601580f0070b40c010301080c0704d1908004c40c00c41d681c8108a03040d0a900030300007034a0382891240074010004d00e200440c0480c0c14880002294001040001c1c450741c801080180f0b00304048050340c0040c407640c215003c0c08007010380313401115140d0a030400003c0c00106016404c0786024a0102048045504040c0c10440300f040100015aa25110306030080c0c105170006130b90b00c506103022050381013900c00c01054581000400030510000d810369480701d260a5440720351045050004403440704080300d8084c0c1da0075081c0090452284243d21109000e031041c1c40c2161115102c0d0002440c492032a1110542803100100500c6250482566103800404a500a0031601c1c00e5a44511103900c0e143c03521809240020230003004607600d120009a200780899462049041088135813404080d2400252103603c10468 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 915095557 1250 915094307 915094331
    0x3230a02060f070309080f0304031e0807021021060e07020d1d0a03060f05061009050102101806050403030501060e01020c150a0c06020a02010f0b19090b030102040803030415 76
    0x1480090103600800ca20b02d80b01c02811000000e070403840b07041e000c004181d000828902c00c10800e01d901914014002d5031100e00d180b07090a1044030250742c06128140710214440050041400d0b15860340d03040b030b20001c58801105c4210341c6000030b4600082440c000041a5285a0055215409070b8060034a84a0703d591100401d0380c3c0e03982401401b100040c0003200c00c01d0b070241500524403218200420700941c2694035104d11082c3c400c2c130704200f822541c0d0307002840301a1400c0c5100510000140c2410b140c0c25141c20f0010f51204440060f000900c1e4540f1404942d500701c0707804a02d03196500c90010803e500b001d00b8000c0091409014000201c1c2287e844015958000584088901402000c085068040c6100070f034240e00308500c5c5000703100380916440c00083c050b0001e00104034155000040c1403040404402c20784144c064101d00403001324920140784c0ca1340c9102c50003038610140000c90700300c0c50b103804a40284643d5003c03072500d02000c02408100840b8140c140d011031000031040c480080c200c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 915096807 1250 915095557 915095563
    0x21306081620010b0316060306080a05030d0203070e0d0f051002040506190c0203030a0215181504051006060c1109190c020c100816210e03070c0323 65
    0x620301808116079070182044880010800b040c580721140c00031550303031000404645084419804422a441d140c41c0502c0705d19894810a03004102d03e130000c0034151407070303101d01c0e4591080a42494000f6000000119076a008c0c80c08103013400d00140c1401034052103420444407511300303a802141c180c041d2001c40d000a46940c0281c5059400003000ca518044041c200560a18410200740c3c040c40a4912003a015076800c0c0080c1040e078506402400e03800084400d00c022017940208110792680c00100f400e1000e030000201c40491f2190301e030481201e41c9503410031a00d000c0040000303486140c100800440c40d264010014003c45220314009580c64481808120440381c040311405134140702e0708940a80303280390760858900c008640c015204248001d0000c19190840c04141101003145242884521141c01c0f1454410700d0080c900341a203200d801400c2588082d02e80031414070359465514102088105000712038600341e001d43c03250456a070341e141c0942030902612401c650001041820302c1800004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 915098057 1250 915096807 915096841
    0x1e1203050714070f08031e010605070b040f02010909020d0b03060c120c0d090602040b0309100504020907050703110f07050a08030705060c0d0e2a0103151203050d02130608 75
    0x190302d60404154101ca1034159981194006a46144071800e08101041c490f0000318001c03c1400503402d800c8070185208000340e41c0c1a070104007003020801000c4040749a40c02e1b900d401c164062190107580d9000e0004851031441342d04208041403000031340382a401c0c1194000d109002064040e030b082c80e9101c03014000540101d08a160355030703001400190380007100328001c04010710345000000e1021034035280d03082260843d0f002402d086800109202807401c0070000b44121259a40c01482207181c1783d4046098140050268400d100001c5543c00806000c2c081028081e8100c101300c80c0d20320800c25520380d440c8034a102d55409510889030100b6801c0b00842180c80c07842e08007000b0005a1180320701800301e684850300840020341c0c3c0381d02e050700740b0100f408446a46090300400c04540600988011503c1c1c0464200f14103261801c03500315101803003481c00c141110b03201d4044a003042101c0c10282d500d071091303c000702c00703252000074844e58103a10701110385e05854003540c03210401e580340c11612025180c9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 915099307 1250 915098057 915098071
    0x908060403270b04031a1303080903070f050c0a0b0c03180f100c0227011802091f20061609080d08043810031e120305 52
    0x880000100442e000355041e8050100390b614514503040000103284140342c19402c0015940c400240400c18810003003000d5413000c0301c1301444005401e0500c0030403940800e0b0394006042c040c1c04030004040700c0c0240181c809090f00720b002e150f031804080c64116180c2c00c203400c04d24403444102c2008200b40a0700d509427400c66000c14025450415502080c1000041403600e03c3d070b0012021101160b60b458544000501c004580c4812104888520400100b081400b07402000c1244000c104080c0840b400f0399207044a5450120312074170124002c02c5400b0f440b50165240d00880003185895644028840c107900f4100f903a501c15044051020100806103000e41c5c0000b001d902c418040794171400c5c20389900a1055a40c200a050190384040b180d081c6032403007c0382c4010480c0034040100f1b205c01c02000742641003603555044610030700d8010940c1c605000c61484215804941c0005030b003441080c5060703010f1904042c100d42d695010382541d211100603800121814001070050303c802900a000701d42c0150741c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 915100557 1250 915099307 915099313
    0x302030a030b1f03050a060501320f21090307020901061b0c09060302040e120313110901121103060702060109020a05041a04030c060e3f01020310060908 67
    0x3003800300300c01612a80c0d96455118404440c810f03034018801262103104012510042264a0445010000c50b501507010368148200551032201103c4d601e0f080406140600304686007501700103102440c075010351949918103a00000f05800c0080c40500da03418500080c03d02e2500d1a80c0380118542c882c0180c0d800203420900060042c4419401811622002121408040700d6103005444500ea000c1c02c0c1ea2007601403640c0e40030140194103050007041034a00c907803002409407040c0a1300220712880002c2040c07405481002000d42080340d890003490056000416000140d41c4a00c10683c16450035841124040030341d030020b10305c074140450494450f41c56030700a00a82c3c2c0c6014151406035208414003420010104404a80000000d0180002c1c481044865481340e00b07620700008490142d03006141400000f4070246415a03c00c10300c3d20f820b0000340040c5581202c0b820207030f4041d810451901c0c0c014150840000c0f80e5020540c00b4603c20b91f43e1504130007209035100015601c0c1e0381d9600034500950 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 915101807 1250 915100557 915100567
    0xb070c0f060b0d0507090510051e0906030709020403030918090203060c0313051c090f08061302041407110705010e0303030606070c0b1209010c11150702010605040e07030209090109030203 82
    0x41c410340c0040350400c0050600e2048410f40d650362414070075640c029a90003540d0b401807101159607540f40c0006000107a4078403107103c201a00e5007000b8100d40c00641d1144890600155050b1000c4c0703e40c1700208202c00c42036440d9601c9140113400e820345c0b4020890303c030604041034803100e05a0f010b05900240c000e000741589482c1d0320220f0302c1d00c2d427004264001e0aa0141ca2410009500300403d01e0484e448101016803c0c4200310003d0100350140d0089c1c2e40c0c800b410805200a00000c141550041310511115500e00928804074001e413401013022500328a03038104001c0100d402002c0d00c881901e142c4e003500c03040e50b02c0340019540100b007000d0701e54250707009100007906410504002d21a5600601403503a040d552a814214194048100e040f0307200d081d8418000044030074056094100d2403414044401e804424040303580d28a10800d81d070b910209240494001030003275000002809000d80306001000180119554079140752004130f02440c810780004e111480180314055503142c0c160301651502c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 915103057 1250 915101807 915101813
    0x10060605121515091f1d1807081506040f030b060d0f1b0e1e190c0f1706012c09100602011515050c0f0f0a0b070c0f 51
    0x20701c06540e82d040c48506291a03074906020b46080c00702d0b8280c2681e42c1d0984002d100b107140302007044039240c1604100a1105903000411126400300014004050114007400101c400a07002c101d0500c20841c201030041c500c0d801701030184079504a1760700c5c0c0c0600012005003c40d502c140c5c403a410746420301c28018800500b08500450700f0420003442600f090800b40c54501111105001c207c540c0005160491184805041d4010080050f0071707100f01285000481d0201000c1e80d00d9075407200b80790207000100121064404400c83d42ca00e40c104100796034a00360702034685802402c00c1400309603080d45040e0300d5112078181620032740040e5140c17410300c400c1001200502803060103811002c60312032450000e41d11000301c1315106070000f0301c2c1110800d10b458006070131102844003802c5612500802400f101401542400300100245444c96849000c410b070a420031190346031035641c5008040c41e1700000f85000a419070300074064110100ea07a118101d0039100d040919400411540c0c100d4205404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 915104307 1250 915103057 915103087
    0x60806060c031c0207020901120b07050d090b1006090e0105100e0d0506040305092706060a03090516060828050705120a0f06090c0e040b030a0f030504050310060605 72
    0x200781900030481c2d08149411100940b03503522825500036040d070209985065151032071243d0300414030301c0401c1603040b815813280303590303040014030071414814005a0085000c0255021803005500401600308500b0210002038034843c052140100186465401095041a000c85039049500081c180b490840780540d090751005001d40c441a8024201d2500c14040340040c0081446548030b47d80ba40c0c0d03240d07208030401040351001c000b946521013800f40b1030075444a0b49020250003503c00c03580c083e1510740f140d000724060f20620800030290300a10000510300b2580d00c0b011010b0f40c1c050f07299100503035a40c10302d40188040c0071241d0300d040795141e0f8081c0c00025150f401640c020181c3d1070a5440c142d03203291807921300c200a0b40c902c40090760b00d08202c2c45200f818401c41000d4205d0060520844409000c000c0091032108034051043d80e540b0760320b40c0070399020004c082125a010f0b42d0810012098200a01150054800c1d28080e00900069440345103c078072903002918410349641d401c5c140340c2c030342c0412 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 915105557 1250 915104307 915104317
    0xc0207031704030c09060f060804082b06080a02090a09080a030f060e04030f09060e010e0f0406090c020a05060f0f0103061a04020408030a200c010809011b0807081006080606 76
    0x40e00c008100b0021003c40d070b80410b40d102a026035031001c60560319048244c00840c0090f0300040420000d43e00740800119140b0440e00c8400c03c05400429814069001040072110038444802003494900700087d2110301007020260701c1c0c0200c4880c5002d5a0765110441543c0340c401c03004004200070080c041003640658050f09050207a0a40040c10a0321180c82c86540075040c1c0c1d068011a03120041c92080c907610840d44400f404c1a4608420f80d1501c40c40040c1c40f00101d86d1440f482036084a820a0103a10b407940700701d00601d80c2034801c1c04106690744c006500c0d5050130009458a000e0300c40054031410060b48540c2c06a44400c1c00e8030026845c0d500c078080248030040c0e1140c0200c6203168072600c180d692b4000341c4040c0c03031520040c5954002040c1c1c081d00711345421a8a6250103003000c030301ea0240c00040340b101403505080c20203444650317415060300d0040401c8400c170010085402c0360b00180703950210815100e40700c80d0300e90041a49a440009210071105d10928000541d490009002030170103401400f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 915106807 1250 915105557 915105593
    0xa05070314040e010e010302031e0709020904150303051b0304031a0618070315050406051c020112020c0a110d21020307050604050c01140a0207050f060d1506120c020703 74
    0x9420291a0f0031080c490b82000c0c0d014440344002000180158501417224040c0340342490010700307159420000d010744401c01449030030400c5034046130181b91615550400b0503444c51f000f010307642140d22840c0c00380c1250003071184c4036415650307060740c0d00100030000225400c0e01d4212908a03a02c0c0c0140c42d8440b203d640040c40700f83c0100000c5148010078034222003150160202e51000301d5000d81d181d03010300c050306072503002605c598180300040005898020240070350015600e1601c0b00c0080d9400103a501c07050a55030107071414800201c0340e200f40030100d04101580d206801120101034914104040d1569031070300071b0460a6280d0804003c0500c1d180c40842034011801580e0605041d600d520b82010f00c203c1c1c0680da0ba410001d58402c1560744202c4445c10b103850202454188403141800079038954036801054040d060391800001c2950356281511014024a88144000c2134561404403591a5511824012440080b10111007400c28042c000d0340e01001d81c010005c0b546103440f40c90210707281019071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 915107913 1106 915106807 915106847
    0x911040b0d240b03101407140904090327031202120a0f0c02060a0c0303151d040602070c03050a120201020316050901021612060f020a050703 62
    0x3500300c0d12000031200200005065500b8001c0080c54462540352040c180410a0034816030060180c0d44901d03d180302e00d036114028203485000300c103c20801c00050910114416080950014084601a1074104072011480941c01417000349104856401c9111b25010300c180510344c0c50301e00a000c482d01c000c201d04401d140079949035015481820302000040986d040240388140f801b1207500e81c000f001c1903a11200307114050301d10200c80d282140806d05040800313014060708d0f1512022a011440f004004000010280900504c01007040324036030b07420701c03c500c046000e00340808091403250004003960200c2d400c00d000341d00b008000c0070003160700402c10000704c07401214480c1c941d000dc03410010340314825040180c0c101040d486240e54200c81c1c0d10400160044644910780a8a0140e0400c01849006400d85000e81c030501128a011038010809000042d01c140921300c4545022400 = true := by decide +kernel

theorem cover : BRFrame.Cov 914928057 915107913 := by
  have h0 := BRFrame.cov_init 914928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 914928057 ≤ n) (h2 : n < 915107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
