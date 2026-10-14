-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3564
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:01:27.512739+00:00
-- url     : https://prove2.me/submissions/b781c8f7-59b9-4b33-ba63-c2056ee258b5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 640827338 ≤ n < 641007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 640828588 1250 640827338 640827349
    0x30804030516260c04050117010b0d050303130201050f0c1c0c150f09150212072c0a080f0a150605060f0304021801141e0310050c22090606020a02 64
    0x303408043c0000644034800503070070920300203001488640c414101000001c032080b041b040984d000701000000d00412000303a05004181110903c010701542c4100700054507200c040450318152803052400d41e00e0541103051381c07621908036002c007425603042548842d0340c0c00c44202801c4c003c2c2d8034030b0404082604881c1c803107500c69038441000b02c0c480e03a1601036400c040402e03980040442a0301008082c1c001a1a841c0500207401201c07a840c0000035030804650841c0c01020200e401e0701001488494000740c01c1d500703118407400b0b4041c8582004484002080303602c07042c0800070b10040c0d144003e0005074514100407180e50350f400e0030940c0142c60700005106907140c21045800c01c980c0b0320055039680d15940701048a0340380e01c080410286441c070002103002e55481645003070345001100c44082c42d94451190500b80c032410400b041c0c1c942d12044c1c0d05245085203400840c4d2284000084a00706500100006d1081280003040701059852860074424407180e480307403030094400b1344001c0900ca0a180d0201e02c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 640829838 1250 640828588 640828619
    0x402030615041503030c060b010905061914070b06010807140d02090a0e09060a0f11094011090a03020111070b0f1c09020916110601030804030516 64
    0x4094005003500c40ca0305841d40d030401c149900722070800750f4980e83d0340d050081450494520440d0081c4c00c0c0b500307005e0158400e0900d6800c0d00c070000c12251410f000249071511400d4814603203810b01c01c0c48012a01401440d00181034a58003c042007061445c00400051010500070042000d201c040040c0000300740e011025104907003895180140c0e81c050090000d10a00c095900810700918000300f0004148000b1031028083d0b900b6800030b00c40d811400103014103079599001000d01b901c0040c001c0c4061032401c0440c50b00c3c800175072519654900902094505404016052812480c07840c4c010820300c04403510848200302c825007045410906004006040c0002510021381003041d1140001e0205d0824400803004200c103160700c075a6a11444204040d80d00a0344904a10013510341d150360a038241409407180c0b81c1ea0050140380716948086072005008615080a002c100002e500485680070422496010754080d86003140c1b11469454002e25100244c0f0f070b08030340e5000402c0c0c10400e02d040e05020780f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 640831088 1250 640829838 640829851
    0x6020c0d0203280f201005030703150b0a030618140601031a03011a120105220510050106020a110303070302280606080a062a030c1215080f0304030b0c03071b0515070804020306 77
    0x104bc2101e061840c846800407681040c03100c4e0800062042e03000341c05078072540c2100c1d100700d01001d50b1082d071014501201e0340c006807411680d982e100050042d6129030300c40303031030702d03020440700d81a040494001c203007150382e103401880501c00900b42554180c074004010b0344600043c2c5000f4061440e111001c160700344401000d030b24120410005880400005100e40c00007180281410803296030340f0300c802503036038000d140250340b510440c108010140c1804800c070341c4c03101e416800600007050303d541c56507156001e4002c00d6a030b5041c00303000c1c000002c84c0d5016441c010817040009100c942d200b0b0920104503600c01c3d0302078403e2928612290001c500d03081422a8a02c034906000846480403402910f000a083d408800090314151407403e000180c0b15000b0309956000b411034076440601a00c903a030701d01c2240406800991740c000010301d07440f0b901c00250740c444a2403030640b0054210a0500e41c0114511800f19071076040001c0034042c12440c0941144d0100351843c200705c442c242500401c0c1c441c14050942e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 640832338 1250 640831088 640831091
    0x60109020f04120623070f050307050307200312152d0a030b04050d0306140109030f0501060305010501060816020a030c0b0a060b031006020c0d0203280f201005030703 73
    0x240014400585d000e01c01510002c005044c0c500800c0d10000310816040352400b000ca00320700407001c28a131003007003940d03c2034085441d024910b45602c2c50907501101c50305481000c20454641c1440c0c0c82009102034800c020362540144228180f11880440200886ea03200b8010103401e411180b180c2c81142c11504101000400e885080300080049000740c6a00c0c2c0002c0c0c542c184071402d200c00c218000501842e10203e9603000c111250310303100d0301786808240e00c0c1028005a000b80c2c1c140086000800402d9a071031142000096440d901e586032803e46d03500340e00c05400710303031120100a1100003560701240c0822003480603001c10030081e900500228960040a4550540580002c0500d030440e40204003070082902e1564803850110070380100280e03240a00c5006004a01c0452020b04080078040c07885c95004018002185409030022510590100c4840c12400d000100c00d01060b819201d65580a00803580103844600c0078081444150480103032500940c921041500002d50110541ba000350720341c0340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 640833588 1250 640832338 640832369
    0x12070f290703051809070509010807090609170a0611040f08030c03030a0b0319051c1d011416150b192c0a0e0f06010605040b130b1b060109020f04 64
    0x1125606440c204c1d602500a1046420701544c2c40d003007000b42a07a000e00342c0c1e4117006544c6810080300c042e0a5440b8203004242c1010092018128070040c1003440c0d481c10302111501e41c0c564540303070300f80e91a81d01c505c014200c0001d820f019440500c4100000b41210a00540c030f080c810ba2002d0340d41c3d00c0001c001049440e541c02c41e03099540d80501c41c0b082151a080407204524116081c00d544031080c1ba032882000182066580c0c0c5124002c000e042e0021103040713a405041c0c09004010744103801c000c24500c2c05c2c0c0c1400c010384807554254903805824a07000303124000701660304c00d400104940d450b50645100b041ca40c10405e003090f12204402003592844001503124070308a00300301d030746201043d1000a1340942d002c1041040710155009400043c220021940d071404801c141d561189001c2c010b140c0021801c000600c428440304008205941c040c0c17441105113035417100300c9083c540080281c004102107000e602c8041d40000c1244130701402406504510301164511072810b284603030300c20294410181c10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 640834838 1250 640833588 640833607
    0x601032409060f06060905030f150a0b0a030c03020901240e0301020904180c0501080c0d0515060406030f05060901050120210c01060b0a05071112070f29070305 70
    0x2000700040c241d11000c00d0051800b0b14a82401a203442c0c0a5030001828a240c00103440c500002d01d0103582e80c0002c090000c9240a0300d41101da054001d24201d0309030b465044401c40c0d40c489046010085000d081d418110605610400c05980e030182e001a0b01e416500c0078030f074a00703a00035907401c00103800703401c0c4880d030542380102190180c0a0508110f174000e162a80e00c10340c407011621884082c1303100da02e81d00010f50301e0703d00564001c0300c00d5030456140c0200b030054030a007061540c80305410420340d02d0429003540a00300080d6050703206400460000b03488135400d01803071602d07002d01600454210b807510b90a6060a000070000407004400c11a46803516944011820050041042800000b00904c5181c042544c03140400e611100ca101c00962908200180d001e81345001d1b14034001f0b441c0e40d0349243c03500c507445880381080d4004025a22800000945092940403c000b0303000b0040c58a0b50a1038030b10b030646110b00504014913000501c0300440140500388a20002c4950303d80d80342c00c2c129150408074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 640836088 1250 640834838 640834841
    0x3120c0a110f0d02100603050613060f0906020a020114010303120c050408010e0a12230f120907090c05030610030c051e070c170d0f0203090d0b0402030d0206010324 72
    0x1880301c980140203901c0911611000030400c0943c1420a40860b115000740d070100c20111140d45c80041d0441d0003c0000c5201422507100d16120700e4018171012400c1c544420b60402202ca94450464240e540010313014106a02800740241c100c0d081a0192619031443c3c0f0090800071101029080c6035607500d031110a894040c10a890280105030000c011610f8580d0019a60340a22101603441c0b440200001c012030b40315a00b9900c100d480031083c62250003040868511540000155095260342404411061b220b800c203220b200f6840728000300f143c1480e21110008a952000004003001410020002240c84591400b042000a450f0025411444045c119400d0203000c100958142d00b8000d680d0a0aa5041c003034074030706010390032203034510755101400a50751072611100300f5150403000c8151529400f8881d0840c0c50500780c01960329100c0f111000541100300103108403035004400e4140000d50408011030906032a440c00140f481d07505503200c40c0e00481807888507080328400c210082003106620f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 640837338 1250 640836088 640836107
    0x70c03120204080a120809030f04051e030d0806040c0e2b0b07050307120b10031518020c28060902030c0907050d05150a091d06070207061103120c0a 65
    0x20398241d844c06007003032400c0c454401003034801c14001104e02c004200114804421985104200e506903442d180c5804180041944d81d4040b0741c0c002010850413002ea5241480384c1e0760f91004c10790b81c50b003a620345402000115070701101c1071030070400482c81144c0c0c580c072812040d0001b184800d01c4102400a0700c0d0310510f5645034004003c00c980c85c8032050009141c0c104016500903801c0352a103106241101000700101d400c1d02c4040c07940101a4201ca6610b540240d000350910b80c0452020b1140e41d803a880181d8400505101c050a50b40c4e00040521124606020084590085561095031105030102c90417071012007a00242c01d0650341d11602d4215641041420010f44014040f6a001d2070140303030103080c9410103610000b10a081c4000106c0d5013900c0403c44100c04001401049041d00740703286000204405540d800000c20107030304000c12400100320031840380000394000c14a05080100c000e088600c000300380e0b905c0da0b0090000c841c0410000c00099032084890700c00a03200c101c0b0b42c00880c1d08084 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 640838588 1250 640837338 640837349
    0x2f07020114041203020f430e010b070204060504020a050f0a1b03080f0f0601021e010905070f060f1b0602070213060807171605040b1201141905070c03120204 69
    0x2807890f031141050b0300850301200305205103007070342e080c22200c04c3e0b030035075400d00d098079444540c0c446100954094440c070500e1014483c0506020b182540307520100426007001e801c82014068045420310451620f0f005420203480142c41c15405c0c1107031403202400b1401900c2c00b0040d240c6020030307440c02803880386540c1008c0481c140401c8068510b1810043e110020540d840022300046900040494462440040c01040706034010003c6058144807076040b00b00040007a61555210b50f45040859402c101d11000b80240e001500032480c03615401608041051420005001c440003c0e84140340070103210b5981d40f03070080c40241e500ea0792440043e0142c4100400603450601c2c0a00100e903901c000205541a2905250205e400205150115070703210101003464003401940c100074484d03030410382c10402c1d89110181c02d84100152a031030550035551f401c8a00d14055000104020401803901140006060055410400703400c1c50500201884003070308000d000d1191002c41175103c5505941100c00514 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 640839838 1250 640838588 640838609
    0xe0f210109030323040f080d060b03010e09070e0709030206030406090f060e37030512010303020c0108060604152a060b09060307050919060e0a2f0702011404 69
    0x9101e0302c1c010380209030140381c041800c2414105412000007080e1207500683d00a00c440d1900c64481e6a80c2d601a4006c8248070001d544aa400103078490354500a0360207420315242c295450301c0c0c1b0022503440c0032203e40c04807032002d540c03001340141250084002000c0c2d0f901603461540d00e903218100000034003021000200b03881601084007040c000c0c1d075072101d0041c411410584d404003903170008480c0824000920350030010b400e441c1c14200c1201100041c001140719007005420403201d8000441985026481500542c0100c1c008030119a40224050750101c002c8a00740c3c20241428581c0c2c3c0c90520881121081c1300744000c02c0c0030002c10014a0001c40c110312003680b8105031a914040c406000e14140442c0540d1007030000c01c016142c003042c0f11054510140c101002603503440404d038281c00038640341140d0180c2e5001d010030b6803408801c1d043d2061600440110302254821030f500318480e004d140c042040050f0200085010311400b04807083c507602480c1031050940e1034a40c1c200203214583c09102d119 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 640841088 1250 640839838 640839851
    0x9010e0405120f0a020f160e15030a030c060b0a0e010306021332060c0604030c1a010f0509090f0303270d0e12010618020f070f050304080d0e0f2101 65
    0x305990402407903824640e03406e6030134402d51040035513960080000c0100714505c00c1c010520a07110501140781c0d0019040e01025000706183d4042401d0000d04030042d0001810b100c04c3c1024440a805a00c03203448003920204031280c50880b80ba01d50107418000180016000070302400c0010303129010340043e0080c5540d00680d400009242c12204c1f0a4003c000701c0c525091440f40c2c81807400c002074070300458000002c2c105a07940c0381d404840e280343c000003c40e03017004a000300c2008d00708040c0001e400b80c00000b554420031802c0c1803c000c00003400810508240e405420b9401454101100344c0c4d42200340320249540915000b180c0703c0415050403400c00c8144a8503424860455204080180c0341d141550440c403000d2104d5202070995006008011109840c00c6500e444072038540d008104504041074450f090078000c3e83c400d0030500c85940700392450740c0041307070502c8440b00610007501c1c4400c0c47d0400351042d50200c3c000c2030380300e0382c54402240704206813100348183e40011210004010307800d01c000c00c0351 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 640842338 1250 640841088 640841107
    0x120815060919170106051e0909070b12010311060304020f0f06040e100f06180608060d0503030702010507020f03120c030406061e0603060f0b1c0f140406050601020c09010e040512 78
    0xc00f11a007001d403c083d800e101c80050306003030041446d2070701e210b00000304003007440f000c0500c141c0c990050710028480c840d40360005640b681240c0901035606040c003800843d0751450400c0103111180010042c4030344401c1050000603a03540028a1140340f080c0c404812804012000a80e5400313540e11680ca25138140041001442054080d1000d03104505814441aa2602e03411200d003040a4140465940c0c40c9000f481018055840107600040062030401e1800c1603503101e90031070308280d4031040581e441c1c809200c8000e03010300c294624258080000c50400c09510324100e6800720141506418079400400306060050300c0e004080070b41050380c0c840c06900d0300c80304050444a4035205c1c500000345000307008281c41010058820455044600841c14034240c260103580d80c0303000c84c82c010300c0b155580d0400c042c104024040c5d107025104c001640303590392409042090a40e04000d03c09070440d005550701448595890b910746040d6203a403526240c6582e0b0760703d0110300c2c100180c1c81a50a51901280cc85103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 640843588 1250 640842338 640842359
    0x1020705070e04020618040b0d210519120e0106060c03110303070e270703090c08150106050a02030c070f03031d09241804120815060919 60
    0x2124850303400c80388400d559540001101d8400ea400079400003041103c0c030264200c4141d0280100c000134800250341000b2000511640b0b6101c004441c0407030420090001c40c0300c08514403030003005c9420441d1500740c01c88200001410000500b00500072440451106061168003018031860a0710003000400e4981c44050a00c1800a80481c005000e0030a6001244c0021040d82d0160806844610201d4004c500308403c81d1108465407a0302c0400750114649c804115030182d000700510b4400040510407414802d03149001c50300419110307401000035a105812040e0760a04550755807920319100c2c5c200c000c08034203510400c01400f0507442080804148044824549021a840390315680085542d400114106441100c0c006d9817008032000082c5040c9910340b000030441600280c85031101c03403403d000400c0e030044e0141d0080b034040180100000c106081d0524403040701903041010280c50225804c0034410300e00140140a0340010500c0c040326141c5118404402500341a03035800103444440030b61 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 640844838 1250 640843588 640843597
    0x3091506030615060f0c03080705072003010b03010b0a270c030606270308130e010e0106020f12090f13140402040b01090503570103110d0504060b060c0102 68
    0x4000503c2d0000080c0d5640500700801d0401007a86403000b004407152802d07280c1c4000200701c001844000c100d00c10000e841d42480c900942e2484064181c01c54036038080c50300310b621580415000b41e06d00303900308069a81c0d2107210b1301211030a644484044200c40b00e50441e007103410382400e24081c20403042001041e0150060307000d6412555076813038142c0b414070076000e0801c603900400e2183d40c0241c030300740301107103008000700f408461490313042c00c5641d6101e00d04c880610f000d034010500c07400c1180041c4021981440040c0d010a8400d000700081301110010428910900c0d400e544608540c14002a143d207031150490703000d8100b44810060080b040c0014040c450007101d04134800c6240864003007907913000700c0010341601c101500a26440401440c0e07407404160020402580420326244c00032841c40780590541c0300619900b42d51034949040074820040c0ca010101c56042c54108482a021901488143c528181c070b00714001c40c2d191101e08001e0020001ca8040319009800010307021141c0d90b0540090 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 640846088 1250 640844838 640844861
    0x6010507021e0f010509130902011110051b0304031b02180a1a061305091302091602120f030a02161e11030a0803181207060e0f1606030915060306 64
    0x40038581c02c43d4011a4107106e81251154007103558500c3d10400c21441e400700c590140b06042a1486240702940c581c0b805181942c4004410303103507000c2004c503007181c45031951a00c40884840d03007541480d5601402040420300b040e014080100c6504055580c0c0013540f0304035440c4040c0305070190500c41082c00140090b4030584062054400341c1c00b0309030400400f1582814060102001100d04100801445c00b5002d40b50514540100d40c0410141c2d8550502c0c50240f4412940c22441112015010f03041400c0c00c5811208800184044190305a140c4101c80d4425100c1e04010780c2c40200c0300c0b041e031903400d04240107082c1d21241402c0030403460b265040c040f1528026082180f211401200b056034130201800010042441400072070181c01001c03814880d4a60303044c0c151206c41468014800c403503001081c0070b40700107480e07050b13800c4203072824803010086a00b208040d02040b0f01c926800b0042840c10b205079020145d603045041c051008800100c020500803003001e020300766690503c1c501400d04100039 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 640847338 1250 640846088 640846099
    0x11190c05030610050303041202040207120203190806030d050309150c040614040b0403030c020a03080f030402043905040e010b0901030e0a0c0e07051603020f0f2406010507021e 77
    0x4070b108a24444040300894000a00540c60181005096120340a008c04102d030000d0702480802c0020340b07541c14080d0a40d40130b5009545a4a094200503ca414072000103c1409801000d110070303a10b011411080c2c0b00031908101e0341e02e48800309010320781103843c080910350540b0141403107856130010000b001204c0d1143d403004585080c0506010480c800e911400312600010881000068020300082002d503000030046004030b0340c0d84d00c0e00c0c040b652140715000d8091100208000031031070540300e0703200c1c13441e048108e10001c40c041f4142c03000d4403c0403a4440008191640f0a06040703882881250050700300018003400551750f80c8482080b6810851426020908240f09001ba203480000da41d1001d982000050003558907204a1070301e4103074080c05082c20000208020035950b02d8802d8456401c9100340c0c0104444c0c01c03510009810854008080c07002c91300800a00321200460301400e103280b040c8800c552140f51640030050791288142c04000390010416004050303031007070500b441fa4124170180e49 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 640848588 1250 640847338 640847341
    0x30206060406061e0e0a0608040605010e0403121109031501080714090a020f0d021206040b121b1801030f11040b060d0f11040b070314070c050111190c050306 69
    0x801c01501e01e1030140c40300140e10086075080da168490102640380c0414103041c401c594200003c034805d1000d41c1c001c9400b2134000424032080081d144181401007010094112007401c2036600189811080443c000f0b00c107448051780801240c100302160040c51b8024120b400e8510382080319001e10788240b1407402c150081810000e02c11520050315004804000e020300607541d00c00034a80d000790001e10031a28450420f10420021040a1000300350034500018818054506001044141d5002c003204c50301a01c40b021048400d90000211510050500803a9004002e2032001154020380800c40e0450100d0045000006102000c0ea170030600d180140c1000d640d101d90001800262001018804e81000c0c2c100113007029252544d1140c40c02049210000c2451101601943e0303030760f04a0f40017002100c0d4002100c0d0f0405d038000d1030320b1400a80510f161410906292a0228446034134800c0d01c1c140075060131005002c40003844400100080d503c610380050015041c1620058414091140644245e00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 640849838 1250 640848588 640848601
    0x20f0f0303090a032303010906030204240504020903010908191e0503010303200105160201151809080f070302010f0509150106031508150703180c031205090402030f0103030206 77
    0x4482c800d503045801004094515034080b9200020031103440708170301501c01802c113448182e0000b5402003244090200e0804c2c10b40c010081101d150807a4142c030910101d0441c54010003803e2040304886044030010f886480b00d00203c2d000d080390b100004c02c0c070b4800003480c40c8844220020030000341c203595110500b181e000c0f800c914a0603040d01010011800c103100410001e0300c00c0e8800d420041c841c4101c000080c0450809500b914400d49014110078080800d1607081582441b424018200e07408c45141014030305030703903010035451840001d00a981c40300c10210500c0403070412110301966904110740d4450403401c00900804001c03094500d01ca0502c1c01240b00e003980042c4882d5162404480e544050b4030b0450700341d0081c110072040c101744801240c1d00082c00802803010541c00d000390130340800380d03182c40003000702240e003201e11000074225400010800728648900380802e036076200b08442088404d9010664090249440c0e01d80c2c054000030421850b143c006202d14100da00c00e400f107880e1522080d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 640851088 1250 640849838 640849843
    0x1308040305161d1b0c1b120115050f01020304030b0a0906060f1503090318080609070b03040512070c030606140f04020a05090f121606180b090919020307020f0f 70
    0x6440030b0b20092041400700d0316084c500540d01c1001c240d80414546886412034000c5d0508801c80d2800340b410030014600d440900b000e0540c103041e200103000800c2506000003868564803424040d05000c1c0b020320b4994034141e4000c20441e0040c5801c42420003440ca426a10a4040d101458003101c01e2400c012002a80646108200d002c6e034040c0b003125020b9070380e01d180450050050354070640c10001c0402c480c1d200300c00d15010389405001c8000c0509401e00d0802042c52801d0460380c41801d80c120200b0401c00070400200309009d2070508545416903c85031400d02d0454050b030b03500040c1c10079240210000d500c00440113007003c81c1d0400e8644410203600442004101d02681c2c040c0e0300800c00401040102c2c0c0b4010a6480b6401c00040c0f1a540454140c4c0c1c4062400ba442c0c2500c05240c401104180121604907021003c8c0381d07400a44828290f080c01280c541501440342003c0c060500341011031303000114004110320340d0321038500464892800d44c070000c0d03440f0803280750940640106d249541180101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 640852338 1250 640851088 640851119
    0xf071805061008040c2105070f0602070b03100b03010f08061e012606090105060307080706050d0b010203090409030816090e040222050702010b01140304050d08130804030516 76
    0x40c20400b007034110040644500d00000c0044030400d00345200882d00190001404410742400303d55400080d0662504070b141c6403603030300b0662074000003403c1005201d900055210546116280e0707a6226182c80c01c52810800082e0005169940044004a80040812841c0c0b00300c82d0500700b00c5000e0b03120480c803000c0c100c602c0d00c41070320801c40c1d90005003c5203e0303002d01800d000c20201020302064502030000c509001c42519a00001e075101d40a03c00603240810141000e80100409044080d2800c04040c01134414404507800c07450f22a896070f04540e00901c01d41e04262000307001403212110500e001801d0f0b1a040701c5401032004d80314400c10b10684101c8520301a030384401e124245546031a000c1011001d11903100140c0461300201b412542a014001e183c00f030f400980001c15a044802d0014100f261402d010320100c1c0001d0007080041200041e504060005500340055591900c9800d504c14030b40d030304070180c00e1030780c005400010000d00044000d2007880204044400c552078000c03075003851a9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 640853588 1250 640852338 640852351
    0x614060f04150503011a10050a1e1413030611040b0702120a02060c0d031805100509030903012d0615030b0105090a06020a060e06070c031101020c0f071805 68
    0x650802403080e40c1440d5000041c00304003807000d480d9030b9a031900040e0a4500604007040c070400c0f4820144964140994021012030a03030620314201903400800529070480100401001d00c12011032a4007240200c502042003801803101659035034a14030401c00143c0341d0712049503160300d021407000c54010140152000d68107444401c92500c012034081182c0801c00d014081d2003802078500140c01669540020500140b40c040600b0b01d45000b408081e007191880243c068044261440a2000900101d0a0321f036280450100180300d85450070300a2640c024404915015032a1003115440580561440c4e090040105030725100c0602c1c401d00780701600d505124000282e082c00c000402414041c0c1c21080c034207841031506600340003c3d6400900311070340a520603000f58000e00c11013014000300d4024103e041c40260000d05039420290700041909a0032900641005200115028080d2080d0100c131900f00c451000c5440c1f00210500032511000988150011400045000254280d090080380c0c41030700d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 640854838 1250 640853588 640853599
    0x90f03010513020607110a0609060305070905010e040507020703060e070e16020d230d0f0507090302100509030c06030a060602160803030f040201030f0f020a0e0307030206090f0d06060e04061406 85
    0x4120f582440880c2e0411a0216000f0203003502a02035625084d61200c028031032555000185440c0410103012194040e041c0b80400581100030311540e60803030045104220141d8001507a030b070b0b40600172810400da83d00b0080615003010840b400e2501c0004004042e111a0054000c40741c950040c00c1242408102c7c00101503040307c15040d4a56020710708941d200c2900c1d41c2102c1e180c4000e4038201401d40e020000240455a949090004c50b03c0c1e02d00c5020b03406019400c1244000381143c002444d84910501d41d1020040d00291464050724140b240544621010703001d6078583c01c3c03912150007d0716103405464014070a034a0040280705400c0316210803101d46101851454030384101110100e00010002e90516840d10b10b00041c0caa40b51055140d203001040c3d0060304ca980140c030040a05140c0c000039446688604400d0000d07039601801c60320004000c17101c0d228681350080208003480502040900098a4628005544c20400b445030784200e00c00c103000c002d00d03490580c001029003010707210541c220 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 640856088 1250 640854838 640854871
    0x1050f0406020310170a110103020a2106030b0a0515100903030c03200105180304060206390a03050f041110030e010f06090b0303072a0e0a02090f030105 67
    0x7640540c02181c015256203c21500140c441d540b071310102d528100000c07010f910414141c814000c030390000030741d110403d18080d0714100c40c583c0000c2c1200d410000c18041d403016084c100e40348040c640d000800840e4441065036491424102080007458100d031a1411425081c002001c07a1504200717a90790700c0c1407130300d0f0340d002e071070664034104e601120309a4201c05111b5010500210942c907070518900c01b0024030008511440c0044102c0340c0d02d411800303042100da00a004c2402401d40108546910520130a00e403c406080c007910b4260441019180b40305070303010305017802805240000140110780c1192400c2c085a103178a51004220b07101200d0180c041c1c131544540380c09901c0c101090b1240c0641c94500031035006e0b954040760382103402d40c42c28080d01030317a0396608010840da1401240c86880040300590f0500700e05031a4041c1008803a450113000415111b0004021130300703841180f000d04140a408200c03860303c0700a8600039481900c80b03d00c80c2003031101c84401403405005032031052090b000748980c903 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 640857338 1250 640856088 640856093
    0x501080624070b0405030c07050111150907030c06050d0c0914041808191202070302030a1809050c0a031410060c080d0515151305060d140403110f01050f04 68
    0x101c1d2410410200e8419041041c0d0010a600c40d41c83d41c01680250050b5566040c6184003619090b02c5a0100e4180408000501c0c3c40c2d01003c5681411129080c1c200c0045648410446003071a01c541c200034844180704102103070a43d480780c007a21641c03a0341c840030400101444000e41d00a4440d104440106050b000ba820090906030081403c02e040b5404400d0002000c0c0e039001c0c1c0c1500400440f020319161070285005042c0e0103003a0040101420b40708518000c40b07910029100d01c0b90050600910202951812071802e404001038000d003000314040055084c050b11916081d400100d0050001c0c1c10700b202d50130f07008080c004240c003600e19844003031501803400741c041d11a000058026540b141080c80a403000d8140e1740100c0788105054113048016040c1a41082500e1013102805444040b050009443d080c2c501907546084c0d0794116035458649407168818006004609248404005c0c3d0100340010190071440c0581404000010f035101d00d80c01d007004e1405c84a0481300008000c0110010401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 640858588 1250 640857338 640857379
    0x10061d0105160c08010c0212250f1403030609090c1003050604020c011407021c0c0807020604092f0f03040b04060209060f1309060b12150409060905060105010806 71
    0xb000701c0c42d20070382d00e08841c00b070300c61840440c201d82c4031224a944400c20442140d60611101c040d00041c281d10b581010b20680786035038100c204000605c078490044440c0828014600d5101005a40c0003074032404c0d1502444506d0340726041681c080303008a5200e008180786d8080410054030300d00c5c01404020b107101d00c05108402030500038006d141c006500300002032800801780118981c03034000f0075501841d8100319400910f0510031003229034000050145d055500c9902589100c0110b40080c0034980780c00103400018110f1003554005004039280c04040243d40c04012030300000d0100040f000300d01000d52180c03115051003044c4602120403020400140041e82800031950030a00030040182000c05040c0812501d5100410a682102000c5454000c850f000d805c800060043e00d80144040c07890058400d0690140900e041000403009001664803140c00c9402100900020800c2c441c20b005801c1c883c00810a02100741d0b9140940c60020030306500bd00c500d5401200094003100004296114440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 640859838 1250 640858588 640858597
    0x903080d0c0908070b12100e13020f060a0809070501031505210102161103011e0c181404050c03130312110a031a030105010e0c071b08010510061d0105 66
    0x4180b114000c004104203004101e000d024104035010b041e038950b0303803040412001c0c40c020100300e00000f8030700c0c0a100b0500d002c22004d4101d20303100e42441c0e121003688005061803030900502904580c0114510140c10f030300040d83d0340644a032405848840f51580011403d88850400c0003030101d480141c1004142011030700ea0380d9403050a45080302d207000102065099074442112242060910702ea8801800300c800001100c800045008028007404d43c0b91840300c00224160a8840c030f85e0712580300400364012940900840b00003d403080030700c0c2e180c2c1c40584c0a0035545050900640c034000001d020b5203000d0040341e02441c602401900d24900743da40807556004014141203c242d12150400300205002007d040505c00c240c401254401182102481c0c02c0c00428040388240c1c140401000300c030801e01c80040e08095105006a510a481d040411014148a54040d860701d91040c00043c40070041d0700c464026001082d0b00b4900306e0b139640702200e5400b0242c000495480203400716041d20743c0101d0042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 640861088 1250 640859838 640859861
    0x101d0d051204080f0d02031c0207060b0904030801060e0a08061f0806100614120a02210a140f0403050a0f0e120a0b010f180f021b0a020307060903080d 66
    0x2501c03500041d49840325140c206a10000003503000c1d00c81d5034a520720030b00048a4190043c4000c6081a06071011808240c1c40645841c102c82c5c0d001074140140103e43d04001c0514002511000207800d040c0340041ca00d41c400d104003000200740420400c06840c1501251044400c160018651030715448460600014070003140001050900d00c0040e801c0301c10f01ca50344c03003104407101520b01035107000320140003406078642c281040241040202c1d95002102c2815403c52042500182c0b1011074004000741300e40c6050030b00010060310010480070f0f10180d005150501c1c0505860072480c1c40e111803d0090000c01d40e8020041075050007960001440391800c096502410b1074000c080c04801c6010079801e0103910001144c541151004505000308100d00e280142840c41704240001c1c5014075880d5140740054031500102d031a961107020800d03941d01654001040c248140c0041c078070410a8968800d00c00300c6c224001d010700389000406c0b80c0649060412242c1085040c0d24100328244030000a00c20a8041c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 640862338 1250 640861088 640861093
    0x11070b06040e07091418030a030506030705030a0f06110304030504030f0606050904030f0225031b030b24030d080a020903010914070306050606090f150d020711101d0d05 74
    0x1840e02c550380820190000f0490b81d500045c00150842c5c0d8900314500007050688104401c0c0015583d40c5400000c48403a0801403900140544179000000c0c203011450b400a81d0521903424502d080c01200d4400194040c49a07901304040b06000d000040c29000071500500451020720041003c51b0399941d105071207510030000050907a890320000703000c00d1800d903401e138001a04140d42d407001c0d41d01000000760192080314030700b103110082036441903100101d0000a020305051000e404c48855400d000c50044d550104809015107451100b900140c0c800e05445480d01002c260100d40b1404d0200d08a04031503900c2d5541013a9035541c0700e00d040658040900326400d99a1015140041036018012007261060600038220b02031550814100362100600a5841814100703c0b881180e074854401d40c10301d21066403120b0038074041c20040d0302e55000700b40c18418814000610740b410010020789540300c1e60710481c2c44088114034603000311025040c2c84003c0c01d0800d41000000b07581c1c50408002c0043d42d124004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 640863588 1250 640862338 640862351
    0xf02100c05010507080108190b070c061415011812060e1c0e120606030703230303010315050109090c0b030a110c0d0f1b0831050f0411070b0604 63
    0x207409007150b004031103180c0010b50f94001030141100a0040e0b81c0c0311001989561100c5900e03464000342203001905410610040c03001e40b0302080f220303130031581000100e0201c4103180c1c41d004800c00c4021003000c2800340002d010351003041c11070106011810a1314000100d03029030f11007a0781c8220043c02e0b6030f00c40c0500c5206030481400854401220050341c19015543c0c01d031500b400d1400c7c40640703d100150040e15401c91070401542c1c0e1400107111080341c3c1c201501c0942240b1740b0740f0014600005440c40005400f00000110500c0700c01ca100d206000c48610003004181e070703034960300c00481d103401c40c0041c12040c0219040054080980145070080d00b03ea00000f001c01000c40003c500d5404080604c03510303088880003588081d00302c4107140c00030580d400e04980120100884c0140c0000a15000700b051501150340706c07081760590303d03100020103154450810b6a071050802003c00c00644140d600c0b1b003c03108048003550819004500480a41d81c01440c00e01d5103035a1149007044004011540140d507455 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 640864838 1250 640863588 640863593
    0x5210c0f0d0b150406090b0303370c1506060813020a150804020a0e0c0f031b0301030b0a0e030a020a0b0603010b0607120807020c060301060e01020c12010c0216030f02100c 75
    0x50b140707014245290500002e00156414802135841d558060444146460002e01c0380e5100881101c40c9140707003400c010484500703503007250342207410303481d03c0256107040b40c00080d580c1e0f40210084504900680001100d480300a4041041e545540030703190026000320702003100c040c0c2c3d402c03210105c12310080c084200a81c4505103131100d074180c0c031403540018450500f0302080d41450f000c070501628500c14140d01038503181505180611030108203500390240000050107030502241c3c000c0040110881c1550b80b940d503404c1810300e460040d250948050b25140c41d03656011070002c111031034507040781c010f170002020507150491104c10041c41f1903055500c80c41030b80d05503611180240011340c4200b00034003604c0b4103c80010015240180598103641c40542c07076401c5a914041983e04491880c54030211f0300a9000040b81058a1242c8503900080c070b01710034201b10380040d00311503099002582210307040d60540792106805049444003038415038041d0340800c05400c051440450a03821804e120700f10b10400e9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 640866088 1250 640864838 640864853
    0x6010f05101e03060501110c0d1403040503030403150c0804031b030509030105070f020d03060b040308032a040602011503230a0f0506040b070c0b0a020901030914060105210c0f0d 78
    0x2400c82c00000e5441d1801c1c8615a040190709201c030f2a40700c002d1580d055100b02040082c0c04041004d030899280d907001620001781041210007406000d0190780c2c0761035030b80c0381c500308032002c0120450810741042c4010552500c036009540c810368142c1c1c0c54544120002e0480c3c029000c4580041d010042c0810106440b91000d001e10340c0144c07000da5440c00e001d81509002401d184e0907a15100802d8204039040041e9031603a0241c405498002e03080c1c42e030720303102c0045485c01c4500200201d20307100410b244110301d44460002400840f03507682c009110000035028070102c01e42460000034050042043c0684404060100c1560001c4015048032105500c2e0f8464040c01c0c1ca14550490f00b66014078108030420a040000c150440001d0603c030f090300c0820717501d19022010040c1401100c560109140354544c0c070a1704552141c603004120340c07404005004049171034035800d0103024020604001d80d807040700c5410781c04050342c140c0d0320007519000c03081c80700700111a4070700c400d81c507032003056040300e1804240f00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 640867338 1250 640866088 640866137
    0x30c12010e07080f010522060b040221060a0f18180512130603020c210405060d0510050108070f0f02030f04150e0a0803180a08070617060306010f0510 66
    0x814024100300d03130600f81140c02d42d0307001001511014680f07010040120300d2001e1032190107074803800c042403c0c12020b000ca0000c0c0a0b01d0311400c1c0e403001d86031010551042819604d40100700582d0070114864842e0b0341c415810056114003400f05500d9001c8031890022030384416581c2a81608035900013009480d110310781200f09000f0348030f2600018600c441c0c5000324910000408090030254140400a84496105e0701040001c0c07481d82c0700c030507080c8590b00e072040c110b4000e00002410203071580c035131070b0151000302012620500e04ca55641404100d542c084c4070a43d205030243d903500c1c41500303001030041342ca100c034060903102503100a1040400402401c006840a0107541d1309802e45035542140080014441710189401038080040c2804502e801004607200540b1152085110046200204155403156403203c5003d01522501003200395003d09424181180c03a03031080110b41300d060416403600d5080c07080404a101d440020406d0303081c11015000c0c0c0c615a8100003056190540c4a9400c2584 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 640868588 1250 640867338 640867349
    0x2a090b0a0b0c2d2812180b0a02061509130311010207080703031503150b0d02030a0b043003051806040302060712091a091f020a0e0f030c12010e07 64
    0x10100c620100d104020048440001c0791600c0030011103106040c4e558402c40216000307840542c00c0c20213548a41d0166190404480005c484a140d141c0e640400419603040642c1c4517006000d50000b15081d01312030b0545000c000002855507199460f03000100d00c50b00d100b49070807801e0000d1348501c0480c00a003071018021203401030301c0c0c5917600c4510303180c0101142c404110907080d100c401071013130000c58004441442d000501072800103149810800154000f56400c00c001e5252180280302c5042090007040302d0b0045108224229940032041560181c400d440800c0d80c03581580d4007811a00300c0d01c00c1c4c0103580c2140c402480c2580050703561075a1030038198104c600340c025a0181050100c032680c0001d0000d14562106c034100a40c903045d543e488108400000d4055800c04041c1c0821038424060061004243c07511100348161806c280c5070344040d400003042c950103d00441c3c5c07211400d05040005a55802c0010702030a405035a410401141074035810030740d1915036940c00300e20107104042000802a00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 640869838 1250 640868588 640868653
    0x90c0915020303040302100b030a0c0f1409010b0f0702040b040e07060912050307230f0607030507050708030604090602160b0a0b010906081b072a090b0a0b0c 69
    0xa05040c201400401468101000c56204004000101340e0115148058004004010442e4556030b030000f440c1a8a41c4806001b1081c0707140005008031100c240481200d150303220389400c002940081049010092040c0f4929420812110f41d0350f041200c01401c5040c401800041c4840754070000c9412540c04d0504802d265126031801d0100b150032440d800010300e030501c01c1c440081034641c0e46540f240101c120060040e501c007c1085a4020800b042610318a5180100c50200c5464802c90b03a860209440003404a403801022481e0351744510129a06690000482450350711140140801090710000c2512026428488802d102d114140c03c1d02034140035042c01455030030803038165822034803413088060620038094802c01030990030085441c0c0c080410100e440098941d40100d2880303115840f0300a2042c4d2001c20000d50744210b04440446145060707500c4e0060035114070008088900d16000700e0f600c442a900c00b046804c0044004201e84d0281100f9180341c020038400b100740c2480c1c20f07020303041204d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 640871088 1250 640869838 640869857
    0x15151202040e01150b0d0b10080103060507141215060c03040801060e01050d1403160320010c0921080301030b040215090604061b1b090e030322020109090c 68
    0x10701e0140244014491210000c101d21258400d0003044100140b0034844000c00200e65400c414405a22401c40c40c0d0001e07212502070718210740001d00034402408100c41d403d2901001c9101d040c40fa000f00403a420042c98600e1030142141c010000f1207000400e2141d582c0715518100c00c05856540240c002e90444000640e01d1b542480d07a160709441c0f00e600300710000c1c0f481c1c0c4010007195030f03060314102545030001e098451803003054810a05510581c1c10070b4540c2003142a0010415900c04004072103803400358418400c100c0c0c84460305080c1c0344212079160001e40c041505000c019581032a0b0803000c00f542e40305104803103065403100007a0700268019500c1443c0401004258184000e141345045d207201542403400d100880066054001c900480007080928094140c0b00090f80c900301320f030240c0021044d0800c610145403401c07514094001e0f51012810003c0718480300c0d000009030b074014000d40d20090b81e9a000c0c234880c643c503000003000030381c10000d009100140f14026449401c101c00540d03952080c91 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 640872338 1250 640871088 640871093
    0x10e041b081501140a0c0c090504291302120a0606030b0711030408070e0601090e240a030308010b07210806030c1008071d1002030c010c0c02030604151512 68
    0x8110310204458180099203850311300000c40407041380c0604956090010340d80110741001b0391000141d41003220618504014003060040c003542c0da60050481c1c1048800385106180d0300c1c0155441503030716040508444840f0001454001c8040d44c0e000d46a404555404c040754036154141e0301140c0c400e8508060207003c0c02130207540320032048138070841c0324011440c0520305038100e07640e000c04d0701c0340e0600c65400d8004078082e60b00c55011100141100c210f000d2860405806044110088500e0b25446030300c0c03241034503401d0400b8020101180d400d03449841c2c0d140e00c0c200311060386600ca45070487d1105087c2c40f10b07100f0205600828144000c25a171400303414030709002071619180107140840e102d20b01d00807045020b190311044983d400344c90361921a00e994251003203020045042d8209903400246444c03130f03018565001003d007503110100d100030f226814010500b5111258810000394240d045840090003140c00c0108034131850000041c00194581c0e0b040b42442e0304151500030101700e8540a044005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 640873588 1250 640872338 640872361
    0xf14010f091202060603120a0e0d031206061d1c06060305250f0b0d0f111206060403260c16031208010510140409090803190605030c010e041b08 63
    0x744a403207000404c0c1908240000a99514010540103c0070900088541444d80f2442e61079110a9000d13001c29140380c403902c3c1c080d04402e02d042d000c8944510300030380090704074416405151081289441d1000b0f00011805000c1609902a421034019440040c00d0000800e6440780030010f6019801403c104003103101001ca001a84002c00c503050703070f00c03004103106404540c0b610008450701301c00e09540c0c9900d401c1d843d40142c40c2d0790243c44019440c148403e01001c2c1c16a000300b00c160b03420401007003250303210010400b680c01280000740c15103941e01a4400d0856070990080c42500c242103c16007080150b400c3c0c45d282090140280d040c0d510800340c20401c0203a4001e2001c0c00710700303d0900d0005d9604100100ba002c40c89256082c0c00c1242c905900722201d00e80c03008550280200f69801e1240300700340c3c28100c000d6402a15000e9a41c0251039952a111186200d880151400240070788210500c2c6401112000020320220340c0c400d90f952140c141002a07200c58002440460b01d41558a150001c440d00703 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 640874838 1250 640873588 640873613
    0x121b170d030e03032403011a102309190f140102010c080609311103030c0d030b0f03060a1b090501050f03041a070c0c0b12040f14010f09 60
    0x14240742c10101e070010398100110035240d02c541c036070707a10301c0d0200b4503413029407180c03284c0d04c3c0b00c1c54040d4070307100c80300d038110801001740d40d03001d80141c444401c0d09042820456041082000e400101026020b240c029400d0300001080c0019008004900c0194140300c0280205096480f514a80341800810006500c85900403400090240020040c20380700960150005100030a2980308022402c0080c3c00399510304910700c6c00c4c107811410610714030015240d004103031807484016a407854030308240320f0303051900104840c0740c503059102900b0300300c4c1e5845043d00a4401501081d61207840c042c59070103503171010003c2074440e03841110040348501205080400c03110300c854452007080f10a000070300c202c0e6013110481d10485580ca01c42a034a035518200040340916100120703012600309401c0c401d4071a4008184c0f40e189001c2c60056000680d185c608541510480b0b4078000450b1403080080d01003540003141d03054403809981c01210740c07080031000c5800c48062041c0069195030751030b2544207218541c40385c035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 640876088 1250 640874838 640874863
    0x20904050705090f04270f020a0812040e090a02040905010b18070c111c0305120a0b09071b050304060c0b01090501060c0f0615090c12060b04121b17 65
    0x3860459148040b41911241319102801a81c5a000410504280e03900841c007000503045415100d51151800b0050707444c2006003039204814407000031403840800300345020803042d051031443c0f810385003c228103450300b00140600e001c2d000c1c901c0380c0300c00758455016409000784500000a29024000d08004911089182c4001c01d0803240040113101c5402c20000c0c000b450b00f10790000c2044d003844c80018085820141e00e5031400d003e44600108140d00000541314202c4c03000d000d03038450f5a0705082841102d091034510f5500a80040104400c140103902c8500b000c06020005011500701e5225186140d11940c004030016151b005002c080c03000c1a02d0190140030518010310541d40b510b8002080c4605501003c3c0c0410314440c3c50f8820861207034405c100c1540d1b00e0b02903c248640d50351080c3c006180c00c0c1080800715103410801c9801d1052442400d00351800014800d040a046c0400f2940c00070040f04d0460380d80ca014030310500d1441c03100740040c5c020441030344420ba02c006080080c2d810111580c03602c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 640877338 1250 640876088 640876097
    0x40b180d2c031b04020d0908040317031003020904022805040c1b08030910090305070309080607090306050705040f090209040608070e040f0309051f0305091603060b0a030206040602010209040507 85
    0x10000c69a01080c03d902020315082d03018503000c50100003500a119119004500510f4690403500b040007490162084a01500885403020b1b2030a402d4a0310384400c80d40c0d040000312a0030244011b24000d8400f81e005400a001c510540a4a0400c0d8400304c601201c28141c01a0128080010b03103400e024043e42d0006915068000b0340c1c00c2e8a111845911004005280181c00310014142d15010403100a4064034090f0511040040b810083c5c0385500240c815800034840010204810744001080ca000340c2c03003a600d1241072840c60710f9440c01400040c020324100b110400000541c0b040c2c4c252600044d1000d0302c00103070780701a4101000704461081c0c0c002151900080b000300024084800c107294000c0c0c00450b504903c64079440d04a0750301d1850f0f0015540503138100903007518405414080082d4000b00d03201003040e51200c1110550350019180001000701000707c043c000034905410403031107000054100e1150303640341e60008516801580111005039030100361582c0c5440d15014031a003206580c2007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 640878588 1250 640877338 640877417
    0x3100302030c04200c12030f0601090e010803091201060f03210206070c1e0204062c06030d0c050c03030a0503040605010b070f03032d06180203090303040b180d 70
    0x110032400841c13001e8000d000101c1c0d10900701005100d008010f403054401c40717030f4034a04181a00007105040c3c2d1400d00290026101141d2165000c040702d05840b1820300960800800c1002c00100185031200340895541f5034000080c5a24032000d18409184561490700700115810300405804900c643d20000310740c814001c1c010140d400078444001030390001e01400c46186800d60644c8500f1280c40c0c008c0d00546800d100245c1010541c1032080d030b111087d088540c1010b00200c5c1012408400d6a81d80c0d8142c22040703401d0f03560750050b140900d44500c01e81c00e9038082c040c0b0400003402c5400a4118101007580001000308020540c85103130b001d8907040400c54205082500e4183d09d000109100505041d55240ca003410301c883c08180d16a01d8a1942c0700401105007142d900e000b9056900c54800c403104070800e19403003840a4000e59108248120017503040d1760326074641d045141c901604030f807070070000c5c030401140f928814001607200c0e006079216031640000c50040d202c034114030007068070042c059109 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 640879838 1250 640878588 640878611
    0xf050103151d0c120c07060b03010606080a0b0301150602060f090d080a1d0a030e030714240c12131706010b0a0318050a030e1e040c050d0203100302030c04 68
    0x51000d0300a1442c03084146240d5202d0180804500c02d01c0200340701103080b0400c00c1074181c83c403c0240300d02e41c8a0101449004038000626007a180d040c0501400f00d8020000285c201c1c4080d07200908040c0300030004560964a645803800c803203a150800c40058120000700700b01c03034056000349900492140000c20740398000003001002c01c0300191000180326240c9407404003440010500c5000c100141c400e48940241c40c1c41e02401c540b030600152800b0303008000002401071625020200c4e0010302821000c40b2691508110744001c0e0031040c030b43d002840a001e4154007000403c0580c800210b0380314410750306c940a01581813108080da00558200780260020560403c002c2a17031030441d141d003989181c4a1128003019400b506152503950103110400c0035100a0000000c0c244034076034081e8403410001072141d401d204240070700c2661000c00001c408042d070aa4201640180902c00362884c0081c02d01e03007a080d008003603a1096440030b03c180402101401035203401d1103581400300044070300b00046480780 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 640881088 1250 640879838 640879859
    0x105030f060a15080f0607020d02010209010c080a09030b01030620040602031b0f0d08040605010b0307021b0102030f0304080307171905060f060a08071116030f1406010f05010315 78
    0x4000e607070800e46481007001c000e192401100091300c1107100b900c4102000f00c210555541c0f0840300080180f10382840c80540034018070894403c000181d5514240130740319140c1c10746170752061407483c0030007004501c0000800c044004082c084c510422010400282e01d050b0484d050810100e00303030300d1792010081008825000011120b4490744031030075251007005004060b00300011045080c059004800d40f4101c901d900224061066100702c804004ea41d0300c40c019206036000880b00040035902c0403800b00050000c141103480c00c220144112031800406c0c100c0c42c00a604280e50841d44c03104003100f4050070a401541485003040c89900800c918545500305068210014150364080c0e5500e801240d02621844121280b40d04050900313a80d07003052003802848200100c4400c00010020062165800d1010a03400140341c031050840c4007607821901d03244443c0179614030071507240d091411400301e42801480214000e05440c03032015400c0303281c0707000034090310458840110395010a01042c454085030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 640882338 1250 640881088 640881091
    0x312060e01140a0b0a050c0708010b0f1909020a1e030504021507030507020d0506041202070b180d020a090e010b0105120112050a0609120e040e06010b0c1203041203050105030f06 78
    0x555480c0c2604403403103000c14140030f165002011180f0000440c042515005001091000414411200c201c0c0da107841c46422640384030625580314004042890070780c90104030600f100c510041031145d03555556100c000890b071050504070003040a86188884010410311642024500c40c2070521592500380d00281400840c90800c45c1d4401001c10780d00d0130b25210f90309984000354040c110880d5243c42d41080ca0740d403901141c0494901e85480040c0c019980301003202d100b124221b4541500b002c400c0401c04055615903050150000c030f840c0e0300c0c1009070342e40455a4005014035000003c160941c1030709c1e9402c0d1402c0300002418404100443c8140d5010700048504669440e129001c2100481c42c2040c01c11a5411001e8101c0e41045500030911485000710034404c1c00c503032200d074110b091510501054480e207080e11085e80d0810700c0100701540b2684010044014000169420950a06800f0b0450780098400340c840c2c80b6080c400003c003d42610a09015000480050081000620780309a99400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 640883588 1250 640882338 640882349
    0x14100503070c02041a0913121d060304020f131505030f0a0b091501080105060a05090f070807051b1b0103060e150d060e0309010f0e03280c060206040312060e01 70
    0x261840b0720050300b130114031444002400108186c1050070122000f03035003134200350b0042d44c41c0d04140810592040c0508a04520040004c0b203200301c08400500b0019039402c02030050360401002c0c40c40002d143e0340d2040024600e03039460800140000c1c4280707211a0820340d80c01080c0281e04c02010500128000102c803900c09a01031811545940ea107803900341450b100810a40510f020540080b80d0300c841900b2103449040e0071380b81600d00c2651002040481d01040d07500d0551b2004100105d0441c034858440c107a4001d08500f0190300d4084203400d450720342c0448102c01105504260342001c40c6501d65000961088424602400058181210703236800c020f0141c0243c4442c8a0b0510010a5488440803620392640100d0b00f042101c0356080400c1d00c035840b5000301c5000801500d02d4400040c0105200480224050001e0900051030344541120b159041e241e44032641321000c034100020000c000e6031010b0003090340542000d0816141c0585003100c580100c0c01028203103001441342c0c0e8141e0250f1411a02c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 640884838 1250 640883588 640883591
    0x5030307091e2c040f0b06030105011a0a0e130e070506030405031b0c04020708042111040903210c1716120f110915090907050903100614100503070c0204 67
    0x240721404005003070403d601100500390042040000744030400f030089003003070b01800700c1001079600d050400d4200c0b0400d003d004d0074101c2205109003000740c108050021080e95007020302c1441c00c0740c0300040e032115050006440d42c60b181c00020710190401e002c0a0000c12003580e40700d05609155039660f840b03001c5c642d40840f150b6204560700c09442e004010b5a402240082c2c406c5580c2c0b04a801c0440f0702e5882800f684801d0301c1c0c40c50105e00f1320045c440301d00e260990030541000c1c0600c07036201008040c05500c00309030104026072001c90070080e00d9100e03a600d100403500000031148114030300a402031079400310b407009844c059020425000b101c48500d641c1f00481d031400d0190481a1004031380140044007070341c40c026107820f080d20f5550008200400e040c240440741c000c154541c400703000a181c0b0480e80896007045150780031810341381c048c00203810400002000d5401c05240003c540d000c4030034036480b003180a2090b079030541c400c1c1850b0b0110081d1052600d4075a01d0340c40c19400c050060100c5150090166 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 640886088 1250 640884838 640884869
    0x10e06040e062502160e0708060909070b030c0403080c07210b010603050c040803220801110d020a230d0b060c0a0f0212010e0a05070506090a0909050307020d05030307091e 75
    0x43d4802e119880708100031300041109140c81d11262100181e0450305440880d4519000c64034600c2c100501390b11600f90a002020b21500b0511080001c0c1c00140045130180c43c1400048000340706040540284410700c4000c01c00c50346001581403200c2610f284524030001c4411640001c20401c24000e41542c4842c200410036480700d0355003090b40e200d0f44e4403065841c00b005c2018041985450481000e8101b64030940c1055a140d514807400c03920b1400c00e03920f00d00e42c1045604100d80c041d4000e03101100d440e0034048100d80d800182c0f2880700c41c0304000c00c3c09206000484568041c8103101d070010342e06081c0c507000c1c244642e07040b00999505c9403020242204884500c06000c568406041c00151030b6000003d2110583c0003920366030711400c3d0802103c180c0207041000c01c090400d0000e96080403801040048400d181c00640c000414803440161030a02003007003e88056180d00104404c03151040008560b41d14040c5c000900d4038074650026044d15900904030810b4200b050040010741d8018125400304 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 640887338 1250 640886088 640886161
    0x3100603150902130c020c090903162a0b03041e1505280606080117060c0f040b03010e01031109010e1f050918060c03070207031118010e06040e06 64
    0x3882140310540c0c404c0e00742603883d504154040b4000100301015603558a4545582210b141c8034010712040886000ca01c207071038804104112800e0703501406404000003001568999621841601c2e000789103c1c00700001800100000345080032500c24850300c1000c82040343c1d0395400081c612810310b030340a4076102e6010402007402120a414609051010220403c1000d15844060034543c4039071030208130030400018040c2c1d601e508028007100c812015004070b0303441079a0801c040c0c03c00d00c04543e00714002d00c404901201243c0056001e0101070941c080d0343c0d855031034003d26131452101d80c0c41c0540c0f03004c03004000c180c58451f040d030303004418503140ca4190a848080c03a046060943c0c40194030042003818408821107802101301010780c682c040d41c41e01e03520007140030b510f840f040d40c3c0d910040e031006c04104042109100141209034005001560b81940a10043c499800c00e820800e00745001e07a050003500d01e4244500c16007903403220050007607032804201c01c54a14040308400e0b2404064210502c04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 640888588 1250 640887338 640887349
    0xf12050904092312030a09050708030a02070e0105040c080106050d020f07060522030207030305030604020c031207020106080c03070513151403010b012a030201021309090203100603150902 82
    0x3140300d4003800c100041c41a6040c16650300c42d01220700c020090032001842c41c1204085840c1e245641500703056491070311600c2c0e80d44010304028000380c03014007800300d0100d04000700713000800c54042e460b4010300e1080d00784403507041003d4041e4000c0703100e00e151403010442070b6000311080e8110348250070211380350520400600d0192140d800c0750056072000003000310400005a100501901811420060345400021110400c510b0107030040d0140c0d100000c20800684505d0040d80c1c04003001c0e0004d0b040003180c0040e00c4c99604408804071940010000f08000300d9070910900006048500041042502480110381c6900550040500401241c5544c02c80e07039090fa080408586205400d00544a90f60084d000c115010450558829402e00e83c010303080c1d40c4510101b810300303401500c01c2044070320b850f00e10f000d817407052560840642d5001d02810581c084041e09040c010031041c00c001c140c40c00c00e48100350801c3c12081f0f403071100e946040024004a40045203984501ca407401000483d10030300d0000a1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 640889838 1250 640888588 640888597
    0xf1107030c030e041d1507110319170a05061002070614090f0d05030409140c0301092307120e1b060708130f140306040b150109030b0109020c0601120f1205 68
    0x1c0820741e0b540038410309058009000400f0004440f9590300ca6200c403042202c0423800120a0f20244d4024080b04540218440c644540d541050400c6002c80080405102070040308841002550b0703550010000301c2c5c1090160701000784241d1010384081420003030b0182562800c07545590300e01e180071480b03806a0b102c0c0e803001900680c00500910042c41c4900e40b03182d60782c0c800d0103251030450900b05c10212600c884100c07075002d448044035031400d680c20002c2c01c100514201c0e0100d404881c0200e00c3c5441004401040b5015051990301d00c00320300d01280b01c0710181c4081071900c810bea40040b00c5d000005000c0200b08141034000c0f03d200b690b034001030501120901808030f1095501d81c1402c2c000505a8039588030000b281e40030313003c1c60845010082095101d03042100d026019034200700000d102820074101a4640102c14141b81c10b0300d507200d480704880c0d06000d0b0450110b041e800100c0ae0b491070010080c01d401841176494203001c1010365075030450112818040103100308800601c1c0c00c0300034050300964 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 640891088 1250 640889838 640889861
    0x9030210051f0b2820030405041d1c02030c011e0b0d0b060112061d0405161a0f040905150a0f0f051003020408100f1107030c030e04 58
    0x500039030416002000151844810b155020500d031800050441000d07000c1e00e012035140f1211203856064201500d880220450041d0204407500101503002102070003c3e142098180c001151102d0500342844201e400c2c0b00c0780d90491002c58142c01d20010741c00121040c0d142034986400105450119041c0d10714002c4102c6a1069400d00b9220000d00d0b003c0507880c500314420460034421400384805100d9000408034019200c65460000240254020841c107504818420000070b0714980c2c07042c040c0c407040044100385018104c224140000d02904101c0120200b8085018030344071850400c0c0245140b2003800c011510560201c0c80d800006c07c58000d4800400516500348120f182c5656588240e00b5051081032140240241c041240000c02241d40161000c041180d04450300f000100300e6001c0c0c03044c408004058081102040400050010464081c030440300400c20b14000d10f00f2105071002c6c164070700b0b50084180500c401181e170217005e1007051074142c1809940542607102050103403030310202c003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 640892338 1250 640891088 640891091
    0x5060c101a1e040e06090604150504150b0109080d0305011d0f0a0906090605041218181a03070314010c0201020a0c020607210507031403010510050f1201030804050306161209030210 79
    0x70481b14801c0490341d02e210300d200c0c544101c480701600d00c82c401182c909070380c040c21040020005107441e9886070700980d18808141400380f030484d0f480c40914588040e483c01d003000030381c4500040060144030303138441407090400c3c82d8030321482c0b0705004a5030034554010600b074000340d291038451061184c0e03540320000312a0010403e004525141c24070790101e104036210480013403401050190103900100f50a010303101d8490282000c40a032a103000003801a442040d400b00400503c0d1001650307041010303100540c0300b03044090f5108503015025003140c542507600c0c802c5d17900400c9041c0e0300769802035070810940c9c1c0c1100e0345034884015040011010b000800070b4150700c02181450480c058210000e001c545119655407480c0098215424030180420301c00c443c0c10003000341040304968048c2026101d540310711542c1d5402c0040402d01d0300d5102ca002ea01c15601c041c0001030900241c2014080a94013124000307070f000c03900c0c0ca081d40080040e07400a00d0b0034055580c0740568030415209014120031040000300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 640893588 1250 640892338 640892341
    0x60403081510111c08070c30091403150a0e01060608090f0a08070b0c0c011a04060603021305090c0f03040812012403021305060c101a1e040e06 63
    0x80030f080c0504400300e5441511a16080200d1001c800140c05088692540c81d0110383d11100c1c01074507801e0514a0844040340c240000c2100000b0100190051240702a5880c2c1440204007010f00072011030b400030b0300d08103190752012501d0745000a24000500c182c2e01d44078181e60300d08410170000e042d4510440a19405d20000140301e030f61101080e8003413031111080e1070041720306418a030798425030b090005207126030a005000c007042c00d440d400c035440840701603014501a10000c1e00b6086449084144a001ca400c404601d0031307003428860440540b0b82c600301149801681701d01d66013450742510840744140c8100340005d52038403c880640702c045111412140d164201880e1146158020190b01c24400004800001d00784001c2c02c2a41c0a0705003040c8840c01928001c84120301952140703d0807600466030240c00501a00e03020020098801e02002400c03100e40700101c1c120580380c10700b94240708140d010302d400d41d0036036800d54035105244004551680c00b40304040814042e20440509800d076019820 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 640894838 1250 640893588 640893619
    0xd020405030609070501082202040b0d050d050d0f0b01050d11040513060e130314030709120503030a0e06060105090402180a080601060305131112100203071106180604030815 76
    0x4d0032010382c0c00980315486590740d652299442000001d02c0c60300c08140d0f011088015091a600020302880c000c0d1001c200b4140d81d4460b2844c142004404100003040010308003059801840b50031a03007035a4400a001c1400c00d80002405802030f080366205a554400d40340b020b586400084600408010700b107180d030103020f520304030010460b80c89100c0c0b05590410029440e5480c04070443c284581c95100c0401c88446150480815080103121200703000c410f16021400c006d0404208241344e11603001541d403481d010800a00342c41d880691200d840d4020400e101c220f0380c03c80280c94903050207403070050303c44038040c405031442250718003403540186211402041d01c0f00e0106d0024182d400c42d0b10f0501407611555003507403070194a6400580b8080000140d10041e180130a0882c065441ea41d0848640c2c3d202c001d00e44089034003d0741c481c00490a07000e00200c0d589424080550321200c04103074000d086545041d240e4544000602c001e003089000000107030440800341c4030300780000300034012045410000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 640896088 1250 640894838 640894843
    0xc0806220e0109020a090908040605130302030106170c0d08040611010b040f020a0914184203120301031106040308042c1e060609030303041110230d020405030609 71
    0x43c2c109031301800c4000c0004c01c030301146008a10803654410358840c602450940c04490039044206251088204c486001016035401d0041002610030035a010500e5114204100d141003480203509000b072501c2050400400d10355425101290a6820540d500d00038071080e940c0109400c07a40d840c1d10901c0c0140d0212201c2d40b0340c1c0940404482c0f501c407100308984905000c503000035064001035100032481d82c14001048030344600b603000f4009100d202e03c0c1ca1422485e580304400c0c200e810401a5918002601c08004480340f4a004c2403000d80207400a00c80e2401e10411a02c0b05010283c90f4491103580c00310ba40d00c80008a0b0f0056403c0302e100d41d10b850b121a40c00c1c8041d00c0c080c4110784508003a095007800e8003823903003103c0d002d4001a4811602402d161541048014005201c5c0d0380c072032820700010205441c24001544614400d002114050000c134040203a00c80303c8031907034010006100b1850012a2008601c0200148580181c030380f02c081c45076207500a8800d80d08519098021035041c0644003000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 640897338 1250 640896088 640896101
    0x6120c03030807080f0c0f0c0102070317010b0c0303040209100503031b01110903301612020f031602130e1605060a0f1805040e0a050d030c0806220e01 66
    0x1035602c140303071612a20710880c0c0b40e010a0b1005140c0510400100d8a003000b410010100c2c04515111242448010f405403801c90f0810b80041d000701d4801c0b0400e0049460b600300b00c034050421401e4090410b0005001c03030b40c4d28040104002d025500100104411240924030100184402421070750365003100740725021000e0310303016010f003190f003012110680103010006548803a98007400901c5111240300441d140e4480b8154000d08000744c0d98585100c500000d402004034031855059003065003894508007402031520014001150806940c1081e02c0c2d0011084986003e48495510301e216110f00020300d59610b0210548031042c5000251080850081240008144015001c1e1441aa5035051142610424903458000b0740788407103030b01e904c80c004c0d1142c1c2034105241c03070007140090700c45001c54100d55140b440343c61680e100080032810800308000a040c1140645400d00c00c88060080103004040d019003107600c203c000030380c5801100784546803800030b86070400c414084201215141c9000308017 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 640898588 1250 640897338 640897343
    0x3030509030a1e060b03010603021810090c020109030215040b0c0f222d1a19020a052b05071109070839071e0506010f090c0207090b0406120c03 63
    0x5c2001000203450184100400c9031340140100d01c00d0b000210200e0003090f4000c14140c04880e02140210355000e403445500c85150842d00009001c5049050103850045260303800c04c07244507040108400210f0400c503c2d500000c1200d511611105e145d200d1052a00078503804150b1042007402c42d044143d07000480200b03d03072100d140354130078841d8a4503035181d40d0300821120385010700000d410421089507200c0300498203074400c051030410840d080f403028140d10104e00d403401640051011b10520030180840c05600a41c0b50300d080c4401070262091002d808070020840500c60f003c19a0f42c1400418a4801481c6100070310420440c502800040e110550650380510742c4c07140c80503c649020f004802802c1382503140e2228900b040760400b640701e081c0d444000111800d5000c00d01c12038107501c1405108001d203205401602d110360406072030301c4241c1c80a5024401c2641001d800c4452260040380ea032003618689500895803094560214000c0d00075a0b101204121983e2411024044c040c2c0420003540d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 640899838 1250 640898588 640898591
    0x50f010906060c1a0a0b0d0f11030a0c140105070618140102070b0a0e191101030b1c0b0619240306061b051515040b03061003030509030a1e06 62
    0x10340742c80040b00d2110b410038004107407103c1114955500980c0c80113032544a50218000302c1c656004c000400d001001c6268202d844010f002c41c2c001c2001a03500d034130031580205900904051a013030f2141c8000980d18840e505100120720320b00b1019134850310803a5880c075006101400150005c41c0d0790520007d143c03000741c51003030080107044807102c2e06000315011190400a200c802d602c884845030b000701700280204d2154803400c00160740044400c541200f07258000c0d082c000c1254000e10000d0180d030301030001d21348602c580c62540190f8920729810341d4149038121083c2c01a0381c5d5420049190403a0403681a03446440c1080c0009085d01d080c070703101c0035110140a443c50081070144060782504c04600070a00402c48107602c404142207003c0451000d54001e6040756100c41c00f04140d00c036202c00c180c40002100c010b400c825910350402d401001d00400c0240d0040000b032401c01d440401e0702505010003802c00c01c00082011082e54108018502280c0003540c2c1e41c1010086036401d02d0300108940115050f9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 640901088 1250 640899838 640899851
    0x191109010e1507110a0909030801080610050d2604270e0d0503040305090a06080106020f060f1602070905070f120e060a05070c050703032003040807051909050f0109 72
    0x3420620110107600000800b40c60828400ea40e4029034952203040c415004108000000380d00d4440b8003e000e1001d0003074450999950402000a00b13000c8001e00b16103a11300910020460307611600390681803550083d4079100030800800aa040ea42240310040030f8114003c2008101d80081481840c000102c002e01420a21006000b00090b140c24451401098220580e07550313605000324000d5038400e12030301c1c04900e40303000d00c00040c950021680148000070380d00001403060a404210152501244800401d49031601c0e2800ba40702c01c000401034100c006241c1c0303245100728020410a000780500c07003c20f204034500300364001d01e288040000f510005003204c94001d024034075442003011080c80300c07024180d90764540c0d0391000907040c003401400410004c81c030480042241403215401851107599004c0312140350800c4580e4800e0070070b40e40070042d0401c0104005208000520000302c40c8265003075241c1c0123545403006c1400306150f102824240c00c10381000842442c0c5030b081d40c1a03519608080009 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 640902338 1250 640901088 640901117
    0x1b0b10090e1204051002030d14060f042c1905280308010902090d1b081b01090512070b120402210c0f030715080a05130b04060519110901 60
    0x48140704010032003504010842132150f030402e101d00e020b102d10715004a0b85407a00100c0004100d07800701e500314664030303a07176400d0080c07500d0f206419440100081741c0900aa01c1144003000e50201c2e880303206135131240c03c40b0203d009482c0602010b4070800e60307141d010b61104c2c601c0c02e0042d181d41d81440510219064008034009081541071100c2c64190142c0d0703120b203182e08000b14000203502c0034448940c002d1407090b0510000742607040c04c90382d07061075001304440c03240703802403481c6800c980c421411040740881025007500d0341d11088007000c07907a080340e80c401c034010b03d00140350500682e600708940500700001c00d00c459444000c17460740114401d036141c4065043c01e220001801c0c0c40c0d4550028a40c02c20301025500d460440e42c81421540010162035440c0c1e51007820003065120000b81d403000c5030001c42004070ba0346031481281c0d0b0260200150700440c400d15514006c10442c000d000070310869546000c00c801150120404005070581e02040000605201c1400c046400c61900c15002404183c96201d5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 640903588 1250 640902338 640902343
    0x203070b0a090e0a060906080309030624090a09140d090e25021002030907090b0402090f0909010e1506030d1403070e12072408070f1b0b10090e 63
    0x10362080c50342d5500e050504008450701d4080c0c018001c607440c1da450702e2010840440510900c001040ca6100442d91420b50000340360510704010248600d03480f41075440e1010600c0d110b80c5001d000422105035605075503000080f40280b0071480080c004c01400440030b80d8807075000032806040261501d90032862982c808441c0d2030140111001c6110450b11000b0410744205841c504c2c240010b103005075410040b1a542000882e00204c40045059104500c00c000a2607076200d0381069030400d403015440d00b40c0d00c2021645000300c00c80514085d150301c0d400503005200c294068181d4043d080180c400101d044100c1258040c0c1c10307a04c5034071034000d985c01940c0785805621207540810b8a01001c0303043d070b6510380068a01c0a141070325150408a00c2c9041c001009050100c6c5004e001750f8070408500000c4200303079290381d25412107044180320001041c0b1505940041400e007552509141604400070360b20005041c06811810041003a0150307414090484082403122050b6a480542000840c01c04407003140e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 640904838 1250 640903588 640903597
    0x3210501061e1b08120c0a120b060708160803070c14160302010e06040e0f151207031511071101030c0f090510020c060c01140105040209091303030e0d020a0203070b 72
    0x4089110b080300b402040740142414184540540060b038146101706544414070380048030145001040001c80c5040150403074040e0300c1640007400200948500103003c5086441000c5000d0704402021681d4000b40701419121150b45038450101d6440c0c1c140390502030308241d04140c0440300e0300540050a00c1004000900c201e000d03118550442040b0f203540c006540001d4000c07007451300301d00d080101080300520100110300903005840025034503d015214800d90007035080c5071a1064100564802c1000710000310030090303030b400c28111031000102e032040344010039800c5203444006d000404c02405000a00d05d01c0104810280c0f818414074624040484510791038a036620042101c100c01030105050011100c1c2001c610f600440e03c5964103036000075941d070408007030b000490f03455000e040b403400b4088102a00404081e981982441e8800d0001507401d80000c042c02e007028882100c150a051090300b00384120358400007600c48168150740002e440d0318023078006900a21900d00000f0300ba05041040b41c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 640906088 1250 640904838 640904897
    0x907110a1218030b0402031504050d030222060302031506030c12040204140f090f030405130902150d020c07150e010f021c050c06090619090321050106 66
    0x340454405540d0759100201d150055400b0003800d03001500c01d1400082120b006503018500b072400e546001d104040c64000c0c10714001d118041c4039414040015000180020b88000c18100540c968070131080204000d100d4880e01000c00400220000d202034042d4002c1d0701400e02910034441c0d1441800c10b1002c14031050703501e281e82c030b602001a400001000b0300b10940041c030003800401c94000380940703461001402c1c0c2d05104071091641c14002100404c119001c40c68160b800074506143c9460009001c255030040501c910341d07140e4950508550710103210048203138000e440302d034890fa82170640c5d10007074000c0f4021407090f20130004042040306105000e000b10300034a9a07503140d00c1401b20b00448801440e03166400030361142012540084016145800740c2404965030142c580e0851070300640713422409070605055802440601081c3c0300040d04180c40341a0030348010610222074a0b0442d0003124401060340020690034101c0b800070800c0e000641226159600d00d601002c0b08000500d1815210008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 640907338 1250 640906088 640906093
    0x708070c020306012702040305010c2c091e070203090a05030601030b220503030408030f06040b0d2a080f0c030607080f2e060f02030c060103141c030b090711 69
    0x400c000e08170309402030004540c540a000d82c4040028901003a0f80290300121026511040d4220f50640d12590401742c2a0342100a4015940400e1700340c244000345005843c001e0310801d00285002c80c0203400c0814980c0b036298007003030350701c0c1c2008004d440e0781117200014810000d1241c0007569260004040f4103998008041d840d082d22640d02444400707102c9640400c08040c90006100803440a00c003552280b4081e203882550380c80c02014240c550340006220501c2207141071900035076030320386e040e405540c254071107408803460768007007040c0c110a04440314075134130202030340030218a4640c082024481c24070b400084039010400c107020036480d024200d034440c0008105030000351302154100c6120381c1102c8950841c1220326002c54607030a0301c802c2c01d0a58982d04c900750b00104100c0d030380141300c0c7c4018041880074506105c09030710f600c0d0b2680018030025000c0701420020301c640001c00d01c100c0322100c10501a102c0344500c1d0280140c00340c0460400300740b1410342000081c40c080d000e070350b60550b490075a001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 640908588 1250 640907338 640907341
    0x102070612020c0f0727060b0a11010f060612050121060b1518240f1803031309110f090915040e100f090f0f030c020a0e0708070c020306 60
    0x740c0080d000070082100c5032040c2201c2650b4000140803100140198a40c0410030b1908100a285585551820426468586401000030384581e40580c3c24000c101e14040c080001d14003010303805001064001402c1920f040000501141c01c03400148100800325014081a030745d8041c50356003140f4260045800f031071182804030024141d64030842e030071107004125142e58624805e80c212a5009040104510014941c0c1c00b151450a1740d41c51214003031104254401c11400010f082041c015108888540712001c240742501c401514480d00f0f1100010f011207441e00700030030103003000348100d101da02c0b149440c09541e102d180146030229811090344c02e503501d16000c54001840425400180000d1561b00308080c001c460351b80301d0142c0740c40641e12600404c181140028400102c601400400070a14a001280ca000031203400e50401c03025046103c095001e141810152104021400002d5000d00c5100000c03e04842c0810340d280500e03519079402c66641c1c0d0f4080309071190a0341840103507140d03000302c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 640909838 1250 640908588 640908617
    0x60a180201050d0e07090c020f0d14070204060803030403022b080103120320040f051c06020a05040b030c07061803080408090409050a0b010504051003150b12160e0601020706 76
    0x41c002c001e1400328900000700f40b15100b840d207041c03110075004030324a41c0c1c1f66078080405550401a0100c00b014030005003141c44c82000b0041d04101050140c5140c8a001141c681e00303554803584154000c0a104054135602e1074503160003912088101d400039940019040590404080c024804a208400381c40e6800386034215160601e15505050740c2070200343d100d109401881c018009030b004840300e010304803038441d81800000440b100c1d00d500041c1c010460341d42400c038107441900000240702d0700034400590300c180c4000101e4441c8150340040d00600380000500c003000968000a06400f03018a0080000300f408907900300c15050f8014014002580010200b404034840000a000ca02001040001c11501741c2d1b40d42c4c0c0c1800c048800640c4c40000c55030040010381046d00440340d001c02081c130040c4a050440c2c2e540c02c661460200c800d031a082e920700070b661080c0c40d41101e0342c43c44090390301210440003034002d8811040c00d00d0300074028465080404106654000107206040c0c50030b54903000720303120802 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 640911088 1250 640909838 640909847
    0x150e0d0512180f0c090a1404080a03020405060a0c152c07051c0b0f0c0f0a0212160201030c1b020d0c0506280f09060e0a0302030f070503060a180201 65
    0x203010780c4206003006409102000b410801400e52049010143c4110155401000043c100041c0610800c904050328003026035241800b4950190340071190585480c07034810700f02c0003030085801c041d412420005180c034040da00701d040d202001e8818030642d844101100040b8044d100042e086503034207050360508504050701d0b001141c000d014100116012031f540c0e44005140c0d540300520686c440f000c01ea21003001e000000340000e034058030790310396105c0e141032990302a1258441d07240c111f02d40a00c040f580c8420140300b40018000c417203640022548465522180ba003415007000310482c007107450500c1000403240140c61540824900840d8010031280503028800700c03020740c860071190101c4948010441da69260050b050f5009022070540b0b10b000c240078002101310050000d40b0601c151000901d01c41d80d030265a810548080e49864941030100302d0100320500442e0700002d5160089003100f0190b240e000400c0021180700b10125002d9444400c041d908a41007040b107041d030019900054005540503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 640912338 1250 640911088 640911091
    0x291210141008042003011a040b0301090c05090403090915150206010302091305030412050703140a080307050a050c010912020d09140d080d05040507030210030212060f1302030103150e0d0512 83
    0x20000414a40030301680000c6c00c5401e9089448011a012040403805041500c140c04000800780c00800c88105d06455903180d0301c140c2d10801c0d100300104c50004003010312070b170400300081083c108103105180411056091001c100d0142d0480d40d2881e41c400c0411b40d01c0021158101d83e001f8140c0020390b1140d085c52688240f00d4007060b2503500c41000001420131100e03001a1a940c05880a4990396056240c0008105034030303804840c0c250b005085004c0415900c0003241e0b0400c100381409a542c0990341e00607a054000d42ca003000701c03940b030441043c09100315890890740915a903800c1c1c3c0c4245a40c102e0580d007034001340c062007514000300a813098160600444080d02140202505800c00c144000e50509070303842181d040703d11390000071041007141840d0040c1120040603080941c2040c1c040710340c0c03002d422002802588a903812400c004460b480c0c010000107401c098007010356496840303052181d690512194024400c5141402c1c2c41c0300310340d011130301d00b500400300c1d0345507441d1054000c41004581c10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 640913588 1250 640912338 640912373
    0x60c1e03110f180a06110606010c030c021003090b0106050408150405011d100b09070e090c0c07060504080c040e070306020904020f07151529121014100804 68
    0x7010040050464031180252041e4089220082144041407040c0310030010254448814082c40302c04c100c86900c004107075564429000e01c1c10364654076450030700315488410042c0107500403900c00108800150b045c0c0214500340d0241408800d581d0340c40078121000e108502c9680101c2c0c01c48200e007000213402094080e00031b402200041800e50f41d8054801c6921529040c070300c12075014917800c443c2401240202c01c1765100840f10180c403864103100240004082c50b1409114480e680002008008608107682911004104a0b800e182c1c407110040c00c0c6070301ca4000c2101c035104815030900c1d40e2400340031303017000c490088010703203407140c80e65803010040d4022a10b1194050f4003403042000c1481d5800142c05081d0090100c105002600c840010468903681140031604410a5003805460320a49001152125504100700040340e0400d070280340c0c0c007031300c02ca600c101e00080003800145550581c2c40c009a03002c010300c0e40d0480306101c0400484d06502c46460b0302054940d0001004100c007122003481c0b214 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 640914838 1250 640913588 640913621
    0x5100c031103040e012603070c0506030402040f050c0a090e06010c0b0c09040f05071701080d0c0602090a0602060103020913150b0f2d060408031605030d0e03030103060c1e03 76
    0x58680ea000c042014090700319807003074045160859840102c580d85032060031b01c40009145011029112072002c40614010350f40102d2002000c10115180c40e0700030f524001401c0000c0000d4102406403481c00c2e44038a502c0c80c0080c0401d40702040c000042c6c000d003409180140c40b160300d40011503440c0c4101840c01000040c40460900440c6101d4980e40169940100d607003c0010702407502c0e4002404808031450002c480300d500070300605c0b1201000234061580e60b40c1d400d001030703409000c1c54068064840c0001d0b0a03003106802900058450300020800e0580b8402c454201460b6692504a007030468079002c007800c411100c07005a100d4a050342e01c072241010024005005081c90310020030080100e014190038100000b01203118071201107140000080380c00c880d5079240c85c1c50006071550300d0203581540d812160400400c1c00410104000702e56600044041c1440001620034900780c480d0000d12041d1917003400e084041107040d10507001d40315000803c4c0313009450600c00c01e600700c4c01000078140d0340f00d401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 640916088 1250 640914838 640914847
    0x6090b120c010e1903050703140102070f06020f0f0d1d0d022812021b01030b0a03080904140705030f0c0702030d230c160e010312030b0f04050109050a0605100c031103 73
    0x84070f0001141d01450242c001400008e280d4544a5012a510300415600364410b000c48800515104504101a81c203c1d001580700c107200780c0380f0700781032048080c001017050740000e01c0c03903503440150000c0300100a6100c0001c1d81c41004602143c49400c2c8681c10070043c7c03c101e405034110341452009546080d1303048009111041159503034140c40b00f80700462030140e84000e15804801c0e4040010203e0341d9428030701803041e9408100421140c080c18080103101d64400b080031100d40d2110f901080701c4159095152280f0b003071080c405004c03540f0649001000843c074800081c0d800b401d0b90708841402e640500181848100d28004681d00341c0d00c0c0e002066114001c10301d8000881e04d400140080140318030140ca100b01250b1719502d50010325601c80070485c0b80003001000032071444c101404003480b40742404206030082c1800101d06440d840c207000d03405407407c4008219540c0d10f41c032680c42013902c1c0708108103090f01d03481041030344001d08540c0d40029040d0ba01d190002889600f61403001000b040441e03040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 640917338 1250 640916088 640916119
    0x60b04060f2711120105060a020a110d0f0b0403021006050d02061e0c010b090906070f0804050304050a03030305011d09070902072108040b0f0105060403022e0306090b120c010e 77
    0x140c9070440351081074140c000c108030849001361007005004100c22a0360034030f00000c25201a40710100501c01801018000000c040c01751159040c1e1291140e11004880c44000189401c03ca80001901e0a03001071085401a000501c0c01340300d41403c1e2907009180d1061120150b0810400d940100d002200001e202d003504c000200d41440504802c00c150340c00481e81160325814080b0110b002404070081d540b201d030900030740c1074008240390ba1156a500c3c0201243d41c45090542c0385100707076409503410014450703001040c144d141c0c0c49141a24512600030b0703041100410200303c0948180d42003000c5410002041000c5081507004011052154016a9110151942441451020300e01c607d0205510300104010400c2c030640740b076849061400c0101042d41000d0105149000324040280070b059848404c2a4032010000c960310320501c1400003890904421300010050100b0b4821101928202440040c9500e0504c00092040b4a2000240034001c00c500044802d5001e442c05143c01c220b843d0220200f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 640918588 1250 640917338 640917341
    0xe161d0a1d010203061003091203090203070e0a051801090b070509010c020d051b010206091f0906050702010c0e01050a02060613020c06010803070b07091d04080d0216060b04060f27 79
    0x2a40780c1030350001038903417030028180200021680c001c4010586000c00703c3e00010704800416000c0c0310380d031074002904c07889440803034504500790b0000c0c135640006d0300030401e00c5030044d00322503c9500d074071007002060030a00c04c070340782640c1941000500e080858400102c1d018850710107400904414503002180340d801b600441c014000c5140140d81c0c82c0c00c03141c0e07001941c4503c026032000d450808c0c40107211a1030130f00c4d002c503282c00480b03612905084c008100c081441845e600507903082034120604000605054101034024000d01c488100803400300c0303850712520343c012010f481e00e034001c6030060704482e03036050200141400c01540e00010903500b448451051081040510b010b050008000d42d07840055090051744504020580001c10007600b030244900500d444030031b0050488100340444c0c42d21035207080c0f200b502030a8502c182c140d01c0810248002d0003843d00009115000b88010407081c0020400d106c11340341540914060310045e50f8040043c0380a2407a10f105040914440514000c0040e20800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 640919838 1250 640918588 640918631
    0x3030215040210180f0e0108012406080604020909090c03060901020301150806030109060e071a071205090a030506100e160906300f0b030d21090c0602010e161d0a 71
    0x1003646c1050050003851024440c49118501d8001d488405d01d030503980c00b50b085490b0303000d078404009880313012845684854043d52380010f001001c80c0e0032890609400d40c4d030f40580b040c440b0722a01c103440c00710b8a489418821241601c0c4000321034140c102d0178940030350340c5200c081c03c4d00c0d030190740c1e450020000c1001c0b803080c9230021036a04044c0c00e40034508803400385078248084001c04030300c0041088100041c1d4288c402600881a400c000c0c0d11040c00b600040c2c05420f06500141c018054030302080812842403242d007050780c8140007107101e2501c440c80d000e1014181e400c212000b0684260307041c89003074010b942d130402502c00c00440201c21054440e00518885c254046070068548422a481c000d203864010001d91030f105400034030741e00101e5000140948110700711450a40c045034000c0d0b102c0d103100e82094203101d0b0000000b4008030394a0100038002d01222999010f14040c900d601c42c510000b4400d01811108103203a180c10495901419840340c08018140500703550350380304903a03480030b280714058 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 640921088 1250 640919838 640919849
    0x3050a090305160c1a03061513031112010c080106020d031401060e310c030e10050c0903011b030b1f0f1119030801060f05030a0528020403030215040210180f 69
    0x45e512410b1550520003402e00700b003c14100c041c028495400c0d00600c2440900880c0d4010070584214445000460014044035a60031003d50070714004180b225001003405048400030b40c21982c00200c00d0030110111001c0346105207914040d00010031502d44210015000508024883c07250b400300200b046608041650102e4840c80039245002401440303881401c0c020481420117001c02c00f08451038036100c84404110840c000d96600100b12a441018144e960810000d4001c0280a00c00382802c019484135540d0380000030308044821880b418242200c4801c090f50380342c081459424600f003038848401c003104101c10022450001e41106408014004004050b68a9880800b10b0350600a01c4444140c00c040180940011001a540d078002c003200d40c000c0000000143c9602c510351200c500100580c0c2d1501500f1030316050318098400c43d40100100c03407181d02107030480754008a859000c4d5008690195100d0b41082c8014070079400380422202841c150070024121030740704da60060319070445030801d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 640922338 1250 640921088 640921139
    0x4140c0d140406090b1311121014010311060c03040603020901032c010507020309030c1201110a17060d080906031f18110301052209021503060103050a090305160c 71
    0x80005000503503004540003424030b001142c2c10000341c0c45010291f82d2500003140651000080c10f203404034180102c2041c0300b141e00040c8420b0350560500c0c3d142110a0205903840344062030b900445213014800c4509811740c48014604151404809400035008450143d05040d1580010000403007086205030421100307501c007800443c403402900b4211079006045005550003080b8808490b540051042d682da039040724021f00d250b6206a425000d48840000121780c040081a403100c85c0d0f4000c0507500ea07080600d10489820382e5210b04102c40c40c0580240607040203c2004007140b00e0800b2402940c2c032203001c200c4042100511300300c4609040c200d50180007000d031010720301080300c1c60b24042c071801d0340d408201b05411541010000b0700f00e43e4000600a80d440001080801494041d8100100e844c0d00241803d8030b40c8426a00c22609610407165140000c2c94000002c00c80d40340c6100700e10070160940c1d41e860612421040c1c19020801c520429541c1c0041000001416031f202070107000410b210f81c0e00c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 640923588 1250 640922338 640922351
    0x8070806030106050f1002070e1003140d23130306020a2606090916030302010c030c030504170a02070513020405040b011e053f0604140c0d140406 64
    0x10010800040901124802d9041407420012039440e05101200c1c2542100e48621100c241d481c180d103402c010b5480184e8071810031041040703d0609410110480307001d00383c680c40d0b1180100b0010380310204031003294085400c5583d05c116950328154800c030b140c18050b041514207401c400050b00c20030101d6004441070354001402c0c141c2e90380d1090707146684501d44503034420302405402c0300c0c8110302001004c3c0c078001ea545070300040054108000e44d0003110310319055105296180d0500902801c1111191b10100b0b0a10051b403e13981c1c42442050b21030b40c4c01081c3c0500c655145844400e00354071403803540003107200b03c44d00481c242c0d82d01c889020b04921110300041c6d0b80c520b0324003407000395810248131a0510401107800a403110f171003400500801c0b260700d0410346c0c3d03044807010080004c81d000b4019034108401004000d03c0001202c1c410f80d010341d64a41a5401e5030f4143c01c00082d62040005100b0a2040102080d0901c80b210301078824100b841d44c02041c0144c101c19003038503c050807038041c2c035419190794 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 640924838 1250 640923588 640923601
    0x12190f0f110a05060a1e0c1a01061d01052722060506030708070e0102150a0e0f1b0402070c050d0c181b0c051609141f050105130f030308 60
    0x2c4200e009000544486043c00000e4002809806540a42c2d290304420041c91220091041c806600700c2e603805240300c10041c00341c000d0091801424040c1c0000300702c04c504122010310080c11204a0a03034141d6074246401114500103600c1d0001d058100702e03400c586807200000359190394191034040e5140411181c00c007080c03500b03c0155a442c0d800700340214010014002081e80c810b83c1c1c01c1e07004140b420549096440391004030310302010181c01204c5107003010f06000942d4140c1e040001e01e0701d004011034148601900c100d0f134840d448224489000c84020b50124102c4c18a5006803044a005482602141d030f614408a6030555007080e00325584201c00000348400800c1c2c124080d4122140313030040141043c01d031280411864203051100c00e211540b0a01010003508100c2104901c8080000301c2a40e0750701c1070081d025120305440500000b0b06500019050380146000d0001681c6001a00c0c01c807511309401501d485e80304101ba0003143c4c40e130403c04182080c07440c491a000750320a9844846a2400c032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 640926088 1250 640924838 640924849
    0x501140a0b040803040b0f040f0303110c030f0618010b03061f0e072a0212012c282103110903100f0e011a030c12190f0f11 54
    0x30380010a128005100a003c514000401c2d14240c6284903c05640d444a00b11a1403030360007a03a0040c940507144420101c105940581c3e07100c91022504103e54480185800701921070030468041d00300350f400800011088048070868110058030600001900e503045c402180c1403460454481c180e07610924500c180907064005490010700c0b05440c40c00c407505000400420310201c2c1600c50b503620006401960020010005690780568000c140c200c070381901898541c060b01c2080c2403900801c3c64000d490b1707510230001c0d00c00041800c41602801701c4016102c44264402d21552140164403044d103814000144400c2499000f0600d82604000000f08010000d00303403011100f4030f03800100309000103071007504d00007110384a081c2414800300b410451401004003c01d25024042910f6003400c140031156860342c0d0000410640c00d070b0a41d1500140582072144810340b444401047d0350141c2054a455010300c4840f8100c17074840c020311030740301d40d003070f00d0303000c0310040c44070065a024100d40c01001d101d1805 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 640927338 1250 640926088 640926109
    0x1a01030c0e071407020a05031f051503030910031407080f011211010305091f0f0e1518070f060201020c060a061406070f020d03050a2c060c10050114 65
    0x80035000c0031031400d29001003e424241c18003400350200820312000715a0740c1d28041020300400760444800c0341d040d5645402e8103071043c0c01c07c190140340c180411090b0003500d54500403014003400840c034155030305062240d60030308100b2070810035030342e03051081504803950b52141c010701c400c1e0340300a45401d0464a035140e01d42c041e0311900c1c00c0c00140b080c1d18001500340100300c120340707005d08000905568481c12107041000c6000b030000750560741c1d401c0c98110002a03004401c10040e400040100e05031641910b03590300c50f21042000409106c000090095181c1d012200130781242c6000e40b0385050703031805646c194400641001c27000d40d401180700042c0d13900c10407005520901c4110705200d40c510303040d14114640000c9094901070b140001c3e08600348480030600c1141d85a01404045d110907840c10018280c2e00501001d81c0001e60510150180d55085101d09120000204e00200402444c03c10008030ba40140c08410180c090986440c00c961440d21545008100c02c2c0c1d1a59a000181401c100d01c100301c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 640928588 1250 640927338 640927349
    0x40b0a0b0910091d0d0203070606050604030803061002010f02210f04020a140d051002030403120509070611010f150f0611120f04030f050a0c08012f071a01030c 70
    0xe07080008031100005030500321038a11000042d03d030002294003010030203105000304070344600d5290700c0f09a0390010041400c50300503041040303820380314000c024040c411031001034101c0000b4400300b100da160a159078400240d6a0000040c5c06171910f450200340d81020803960448120142c0f0000b1005908400c603a0080c000c03000b1000500d02980040c1e400741403805503043c0c00580d54140800b41e22840f02944080e40c10400b11210100c4403041718000c0d5200300c0d0110300249107402c0280c0146141d010b00e0340217000d0711010b0800e0301e05040c01213482000c07800e10f43c0314540d220039078044406200d00c00c003850100440c1d02c6560311810300c01c1c0803151101c0d980c807020400002c240c102da5144400b140140a070400c8046050703a506409403010f195000e01d40024251a00e14110102044400120381011724819415034551940d00c0300014201d40009040b07411144c10784450080340040407030941041c2c500f500c2c090303040c14015102c8041807024000c82c00c0c1c0d2400414014414031444109240c01000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 640929838 1250 640928588 640928599
    0x21332010c0203060a051e0c03100519030314271e09010e060d08030c090a0504020c1504060e010617060c03071e020703080a0e0a05090106020a0209060d0803040b0a0b 73
    0x10710070b6010075942c140042c5a20801681c03003010841149000305003402e2824036000001850412202d5044c3c1e80d4025240c1c2c0c1024000b4000c0001d050504880c44103204003604c0070111240c1c40d40e1425030b411880c0c40d100e8035086108104085100c024148102c03051044500c40211400b01001440200f040944240f01d4064501c2c5084c400396030346507a080d040d07400d0940d4041c51506c88001103000c10003103078401484c0358804810040454401e00282030600b00869140f180540c0d01e001f8402240325044034a40190040c020003404034401c0500b058105200e02c10024220306a100f1183c01c490080e0003a0089101d5003049111906003005966004401000c2080c41c601b05040007800400810301060004070503000d05800040c002d105440045030490381450717950001c02802040c40708848640c5100320150b103008a030508088840c5070681e4001e4009010380382d4a03808011000e400208902e600c00314040d5500d0000e01114061401580b007401c0116031030401640740400d50707540c10a8580501c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 640931088 1250 640929838 640929857
    0x311030f0136240c1e110f1006031104150509070203090a0905090f0d020d1407080403050106050109080313032004060303020c12160902133201 63
    0x41c1d6102151011040a00503202d14020140ca601d089400c0c2d2000050801c500750440509080c0200340c402c007201840c01020440ca0151000030b5542c40b2417050100072a25581030400c40446c05150645000600c0b441240d285000b01c82e90240352100c0c589814103100d0b2104000c104002c5900f00c0103000b040202d80510030050070700d41c83c1b00c2342c01c00d03441441c1c414414400850f59041c000c1c01100c4c0d0886003e030403200030988680d030741f40180c03070240c0b0295500c0c0300700704223140d40c560040380400960a8540c080c060284030910125916130b000c0c480001c80a10410511b40000c440000030002148100700108901d403800b00003400103103d5522044040d001040310018211032030f00d807141626407003448002000d06494841d182c01d01d0380309486030050718008002c81032580002c0d0701c001c81c0104660517581404414560ba856040701c3c51820822408a1014401d800c2c040d00509000000e0940040000d41d6461707004001000381880d042c8503150111000d40c41e18001d000704206440c0c2070806c01e010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 640932338 1250 640931088 640931111
    0x1020d0b0405040807060c090f090204050a120b010510260117030c03160821042001020c060c0115090e0c09040f330506090603010b060a270311030f01 66
    0xd03889074140051140c0d80d550042c005540c00380c1109400b03012007402751061a070711401d181c8000e5000d401028415503048000040b8030180000e004125a40300e150800164038080038020b5000a950401090103409111410b100348060f03415101200300754038281881d490654202c3c3d09018140492074550070401c01c203e20f200c4000304940044c40034169411030419a401c290005010300c2008824221019980c158030580d0748407082d02441c0980103844049a161006481d8411400300250150b008113041c40303014501070018003180c45442001140c01e19911804415181c80c94002c2c290755a940c9038182c24094081010b10030f003000642e00c00c00395041c01c0c2c68504103d580f002c0003c000c8410000c030b5404403c20709419500e030050400c9218a040b03030115410340681400c8440d24001c08144001490618050060348480000645214038240031000e08444c041800840c44004202d204440069804400b640d14010b5015007404144104143e041506041c107800c0031280e0b903070504800008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 640933588 1250 640932338 640932353
    0x17060a1d0312070504030f03110d03062610020c06040c060c080301330215060d0b01030f05072303060a1a010507050c0414010806010b0c0316050c1201020d0b040504 72
    0x2c0a00c501450031207240e0300c80c181101c036407065401c02024904006004000c244e04280e404a140c20b0560030740e0064525100d08604890292044800050301c00240002c4814200c07840c01d9444002c0007514259041c00c404407003a680458140c640c16440300c2c0c20881400421240100909014074150702d02d40b031261140c0322a40010701400b116003000d4605404044028140003108000004000103a0681d10001944907198540380e04510b00c80007000904503d00f04504c104083e91000c20b0600b10b03401c60b12203074081c190701841102c9511401714041100030400d1443c044506c0211010102d00744844140350034000082e11102260f810841e02c0c0305001070320404411820028603186440d0385490800790f14000201080580041c81c101c48050300402004600c0c0c1a6250941104d003c1c0e60b882d1a80030144c455001d50b10081d400034007e441f001c0c84540c80300e07400d00d40104200c03050800c1c5640001d090100b0314400013010381d4005200ca043e050b0318054210228402c9608002910b480c5d1a503a8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 640934838 1250 640933588 640933597
    0x110109080712020c0306100501030f0b0a060c0f0803090a03031b020d05090d0b0f010501031103040309181b0e04050105010207060c081e0304050a020906090c090d030917060a1d03 78
    0x10020b4001c100c1c0710042502c200112100c00600a0855886041c0620704c0d08200e00f0500410b8000303414581641680d1030300d40102d440e03411000e00401c0d40d461400100725095200030b5000c6a5142c0d01c004c841002c40d4220300698007580050025003401400703403a020f800c031000d20795a5a0007080c4440b91056003500469919045170550070920b949400600006004c10260500103002138255400e0050b00f92213018414160303102a20200010300c002c40d07202c48036000442d0b004001404100047c006000d0703019850100ca8276442010440807411440c1d03603034a0040c000e00300300042080e030400540345054003800d07004040a0001d840300310f007007100c010040b110020b0054281d0000065403644400b801203800c00c3c0b00f08140341d9030b40f242400d1610648480744000281c1c482d0007504085000b918100074010701540302c1c2000c00303113000c00280910030030b0031070a10705070280807524900180c03462040303220007905005800640788511300202083c04440d1000007146a50f0120501e08001140000894 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 640936088 1250 640934838 640934843
    0xa1a03040f021207060e030610030b01120206090d06020a03110a05090105070816080c060c160f0501270b0f0603190501150b0d05070e0a05040f0917030105011101090807 74
    0x40e1510780340d0000c9100c01801580680a5100f010703000121742c0e9001c0c101001004080702035a2080d00c0b00351141201c0030b85c030300020b002c8003145001001884100040c41500e18406080c007400c050b07039600042c0860f000100d083c0c455580004400c00d11551520800000d000302c0400c480c03d04a044d81c0050860068040f128184100040e0510038804003c0a4440b00031800d080e84002d54040c0ca424030f06c42d00131032480d10941c404e440c0812180b00b00501070b030b040c00320303200e80d00c2c40d4600c030380d0320380d94881ea0050070241c0d0503541c1c90024580c80c28510000d86104212103c05900c0e10034140340543d01184000c00340a0b604150806108640e6008074040c0d10f102011284100040c0b0380d82403043c0103103001940d10002031141d10b00006c04012680103416102403610082002c3c0e07640180a4030381c8511011300d15401040e40c10280070a03d001e50011181c01c01070140050b0740101d550b01c0072181c41030384090640020022004005640c1c0c0040b0024064650300001c1c802c1340c24580e102c040700e0182d901300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 640937338 1250 640936088 640936103
    0xf010c0e040b0d05030f040503121e0a1206270213092007030e0109050f03070302090a060801060f0e090d050328020304030e0301050105331e03060a1a0304 68
    0x1440031541d03d00001c0050180c000302a20759940b2800d03c200c13144c3d07000c0c1c8a00390007401001d100c0306000414409442125050070828101001c032040b41c0ba103d81d004802e0802846860118031071780e40c9861040030b018210548070b5248040b416030f050340010091411a211560040080380d24007030310000b489040307070145075011a544442c008003051807080703842c821400000c00b10390001816800804500b8003402a241c4220b03a50300d40c01800710407458142c81c00d4040d4010031003000142003080420b544600b5500c40000c840b40c4a030202400e5907610390010412070017803801445202c80108440d500040c419000700742100e500c200103044c030f010080079a201e1115803540d02451341c1d4200031108481100c908119560715280c500074054a10b0480c3e1240658a008004190b6040101c0d0405058540140132a91010078a140e05220420394108550298083c062004000707544840301c410070f4164105c1e10384030b00d0014140202c86826611111409041d10801490141c00608032a000340e0424031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 640938588 1250 640937338 640937351
    0x304050f040902030f06040b060901050303070b071b0305070b0c0a140703090f120c0602030f12060d080a0804030f0305060d03110c090a09050606031c1b06110a020f010c0e04 76
    0x60082c4103909000c1d4045c040c603040c004544030041441440f40344607a501c003a03981c42e56400d002280d6403d015994142d0300400c015004120740000c02ca51104041c58050707801c030809903018030a04502c00c0100c02080011440500700700035100d03080d80c03250310b04942c2420001624001051840211454100900002214410305100306c2d03a060207003c41d07142d409070b81036071001c507030004204411042d01c006012010100d1410b1021080701c051440303c0030024104000c03002d80d424000006045103911800c0480f40c4e900084a160180c41d0061590710340b440700d460541000707800d0526070208481094544010400c1607615070301764110b5941c141c50108240d4600300e00c0c040c07801600d00780e00c56100c000102041200c5140d50055080b0500c1481980c5854440206042d03881c10285001d0100d0388000c0c5c64196045e114100000000c40d01742242e2080e00d40b1911180210741c00c04550ba0b0240354000343c94010190100151000f608101c4000c201c42c00c1c201d20000c0201280d0070180740705545840 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 640939838 1250 640938588 640938619
    0x1e03060615120c03011511060c0c0106031514090622060f060f0f060c02180903070b040f0b060d0201200f01060905070f1812171201060207080708030405 67
    0x4056803070b000d0302c115244806081403206106141c00910400002481d41e08109650900c01c00704681e0282d58000180525201d50b14464004d80100300d1000c105e41d40d403000040415545030349034480c2d0201140010341c07030b07076410b6100041d0304000304401070960100c02400300d8000c5008141c000f4013400003120003111410316165014150744414101c04a06244c408145011990208000c80740340c000302c250040d50384e403800d580801011602075400812041c100b40c42d060b409500079840f021481c1034914244055503011115141079805680044205000c2000c0005009402e40c0000088440c41c0d14203800e80d00081090801c10000d141c002258000040c450720100031890441107410001d204854803092500c0080c90200c8176100000c1481800e40c2c0998018103561804103101c15007035000c20306203004020902d0306c10b00c040356001d659031410320b00145440302130140d18640f000c522046514041d402440c242c0241c00480c0181c201c0c0c04100600c5800204660803150255403107040c0401d00d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 640941088 1250 640939838 640939879
    0x913020d022107180b011e030e0d0819062303070810020d0507050405060f030402030c06031e011a0403170d1104081b010801030201080415060f051e030606 68
    0x1003054941c00904111070190382c0020420f80107030340070040200d4002405003030b14020345002c02501c0380810007802d106006164000031103403d00041d4140841c1300c0a030503450618015100c00800000350485090010862441900118251019105001050400003110b200c0c5141e0b020b082a041100b4004410301c0e00c1c103014140c000c0141409031240c0c05908920030000c0e40c02084060b041c14903080c002240d007400f8006a5084e42c20290209050454002d0407520951010340145e1b898440d90402008650341e4000035031041d82c810314005c0d14020f42120306190190180c10500103209294503a040c03c1e5984801d40d0204c980180b81c11207001402c1c24840351038413070050340001c0542405c201071280241e40009104a41c014005c8581100d08200c4c0060841c00700080940040c42d1080100090741c0b0885000d90400e002d0300101c5a00590400c0280481e102c40e4030007041d128840c0c1e0208407516001c01003003e01500908511003a9044100094603030400402c3c26114403082081010078280d403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 640942338 1250 640941088 640941109
    0x411090d0c03060617100603050d0804050c0409030507020f1e06130305030c010606140903060a050601021603030305011d0402030c04110c0303070c150e100b030f03070606090b0913020d02 82
    0x2c800c040105544030740754984210130740d45c3c500d6194460740d592a404003250348104000c5a80140c090404181070070740490302d032100600251a030740703c0d54405010650355841200f00c40381c4a91101e40d81c5000b94814000740350401d0501c84e01c16841000f41c00340c400250002400c0240080302c401d036403000c1c403008030500d20406400241107407001042c484c2d202c080540c401e00c2a0341c01a16004811440c0414030300b4640700344026290540c010740c0c00b150381401141c0040c2e400c081c0500640e608a00e80140030500c06645510560000341c454004002c00c1048010b9100d48905043c2030002c036107820b8002c641c2d03d5200c0c00ca111301965580c5081d152141d00f01056401070a1002c05403030741c1c2d0916400c01004411821070964004294180c945080d56552003410406048103000d400000a0300000200a0809500d03058041c00b90740400c0f401540140028010340c0c0c4035000007e030150504080c0c44c1165036000026010714008400e00c50500d0703100b18041e1841d82c1c1216060304101c81c41c400310740001c10703 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 640943588 1250 640942338 640942343
    0x40905010501090e0715050f0d0912270f120c0b07210e1f110124060504030b0a0c050405120f0f19080d02071703010f050411090d0c03 59
    0x1030701d0000310710101a6008405030402c014115009540c5480310386100c101024145070108408000b0760b40346d4007030380010708529000d03080001031245103601c0d03a0030380480e00204803001401c1200e18280e2100b00c141d180c1ca10003221001d00c403030141403491740c034808080f9005909000100ba1140c83c1001000c44500024000d180041c607200c0740d25107414040803c841026211800c021040000c2c02d41c4280e4040040000051400c020390f05000151051030100ca5008000c100c444c00303160035085802d0013a4080c01040d00394034200c1480d07440315801c102c000b5401c91340c10400304010070000b1890344140039412034610500042d14084400003600c541c801c40d0300180d0271550203241210061404200b550302d03100b1000030340b6800070b285c40d091521011401d0300700d80034448402010000c0382c000030140009565640340145808440e407500640002540038540e258100000140100107070501e03c00d0003001c00780c0c0c050003000030115048006005071070416004801e030102d41130510214103692001142c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 640944838 1250 640943588 640943591
    0x602031b07050a1e050609011403061519020705100c08030702070312080a14040c140102030d060e16020616141209031e1c050613060807030b01082a04090501 69
    0x9554841d007030400304d107145003e41c2010085400207200d0900e20101c52070440140d444107980d0b030074010b81a6a41d0000b81225410650003424803007000c2c400700050079040d55824800b0306841c48280024a0040c80da00014001e40e20404030b80701c078a4116600c4042e41d0340c07100c40305840c0d035100c42d4100d00d4815036034009440b40c050105c2519020307400050b034a0107070354416800c1c88401194040c109031120241d400501c0304214010400000306004201349004d1014030580707180c50302c00036203a41a182c1d03540148002e00051000c0c800e14201603003041080c0d10150018000a01e0610095080e280040b00c4c424180400101208000310307545c17080360034201001004003040e007056010f440c2d1380e400c1600b0700c81d1031201d0721303004125004940d829586070f850250f203c010704070002d84800340070300405041d55030821054401948020f8081c01020007503c0b1500041c03505a240d17007483d10712544103a00c2046540c201c80300e034510442109016a0040b08414054400c09884c540801c0042c40d04640182c040e5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 640946088 1250 640944838 640944859
    0x90708010e0d0f0c05300c0d03020c1005010806070f020a0b01030b0c0d020705070602010e1b0607060b060403030c110603090a1b0810051e0c04030b0402030709050c130f0602031b0705 80
    0x32000d140440000001c0b1588210441d0006c451001c15102d11a1443d100ea4000e4500500da18800c1d0000d1590704c0c4113106441d00842c4103442d68003a0b420030303088200c1c1c0e0342100081080c000d41c083c080070f038085103520007042107580c2d544070703440c0460041c000940489030f240001458000d44204990641c03006441c1159190418142241c84070014042c54005500303004564060410002d00e406140303a0001e03030446402c03503500c1041302e1540855803c40d00d0944401000e44140d171400c01810086002c0c0c4c84e00039510b070491910b1201c0da210803001c0f51045005101340301a84c000041c000c2c042503403012000d1640300e5a01561032001070103901c903494030304c03425103405000382540c2c00c25030083c1822020301e2074081c001d00c10b00d0000701089540551101051004002151101d003c06800c58005400d460880f92503103825130698a0450b802091480d00041f50b054686d21409001c0041c820440c0000c0b8090138202e009403644242c0055201090314840281000d21051207004010000140060036a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 640947338 1250 640946088 640946113
    0xa02040b0a030912211d0a0c030606050103180b06030a0203060a0b09130305121807090911090402031207060b100206072c041a0a0e090708010e0d0f0c05 67
    0xb50080050459030700c0c084101d00380f04c06000d5010f4042c2c030701c030038000008020151032054000f003649000c0c0e241c151030070b4520000d84c040700380002c1c0e10b030318002d0301c0940c0c0c654110304205082e1415507010034101450030070708800741c201d6022298071035030b8841c81016040e15050000707403510341c141d04041d40c54011442400a4034003e540070301d20b5160280e8001445903034040d440010701e0158180275010840c2089440c800d6030300400c41c56444142c0410174003100007274082092510300c642d00304c89210703559a04c41100303200008103032140c00344040300c0720441c3d0710f42076001c03d840346004400d951a9040100b0301e241048200d400c400c3d1251006860407052040310b81e4000e41c0c941c401e0b100d0380c001c43e5110450b09940102901c0014260140000000344040b80310244801843c0c0243c90808104c20354820685569600114100804207056550f02504004d181c0c1410940300b54006001030780740c0b20056a01c82030201c5c1417158040c2c0b500b044034054108180688124001003401049400303641d104151 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 640948588 1250 640947338 640947341
    0x130204081e030d1d0a0302030424020d030c03020c0a061a100c1209090e06041506060c02040504050a0c1701050a0905030d050405011d0a050115050105040306050a02040b0a03 76
    0x1110080c0d0216601d018070400311054510207a03801c0c08854004000c14000b07801039030401460243e00b1500b0303641600c0f50026680c10b1418406003140181c10014003080072440c0d940c0f88100c20340700540340d03803813410010001954500d511180c1d801403544030034207451003500a505803801220034005451342034065140000040c02c0c0300e038902004d504e5441a000300b47c03c1403800f083c50647d045c0c4903042d070146641c90341b44903820061006410008981c80c04994110309020fa039004802d404008e09035414540760541280001a81018540e03150003410000207522400360132000c0c3e015907000416441e203050003410810000c81c05008184541c00000c0c02c1580424560040c04512008010644519044e0416100d001e01c0241c400c1d4003c2c80088420480c80d0300c4160414410000060307a5030201d118038020000b4800304d4030558000038540da041c02800c6c0030707401d0a0401500300c00c48007410000042c1050151b0302018240682d20f4000030200c03941681150b0240007003141e401d444001c100710060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 640949838 1250 640948588 640948597
    0xa0902031e1e10151806033c06090b1612020f0f031911030c031611060c0a03050a0203010b0403030c0807080f09030d09082802062802030c0c0d08091302 67
    0x440105c4403240c58040365500d208080680303501100700f0b80c0b112003014201a00104100003211007401e040f505010681c0031031240c240301c511556000c00d41441d182000c515188000303282d80210040c1c24006943d095003c5612180704080b0800141c4609206000d8070417405042c030f014006135030000c14400d508801d4414883d072941031101c00e2150305015100a5224001070301c841240100600c041078020b05a50720f442d00303100c0c442c0303400110f1007e030f90810f41c50210706460b40b420780b00300000c0320180355901d4001c844c0d000e200a0400e5145525240a1402920483c4809410001c001d1003100402c010b810440303014541182c0c0b840c0e110861070400004560003109010700c030788a2004480d01c540d024400d081b044503002d20140960721861000038610301c02071480c402c2400c44c0e094040c0016941d0502034007000f000c11111189610f0310f00b016001981803004a11305540c000d0210380a8142c000460000b80354066604901e4115249058a418046d1464442e80004551a080c80f000c005a0142 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 640951088 1250 640949838 640949849
    0x524030a06052407030e040e07090204060f080402090c1e0f090a0e040b01050111010902150318071203051c02030a09060b010f080402100509090a0902031e1e1015 71
    0x4019083c03040e074006155801d01c482101c81c148107110305408240102801e820503140a04081114202c450801d400c08083ea00007000c01503006c50b050018540c00204000701030142c0c01c01c24007900b8150001440000d000f01a188845400200c90b46948002e00640ca141102c1d43c0c1050b4a8038080c40e84051143c100443c00384c09850304501c0042c05249000c40d02e03016035001781c0300005076400c100044a02d84d8086000c0a025034130394441c200144c490300b400301c024a02e1480c0540d1207007000c00b0025a9444088891b4406501004050254141000d00da0100c554103040c40f035620f40300115485540d50103042100300552000c410030895014580040400d144215410000c101240b40191064404c07450301d200088c00301000600141060580c51031002c101e03041c11800d280445002482140301181c00d1300b02541c07103025840c1142801c0082240014110f0032403640e2041d0b4104045c1d0360302100201c28441c4140b2011200000c4061007041050001e41e030050103880340c14800403c0404061142 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 640952338 1250 640951088 640951099
    0x2060403060e120a0e0d05010e0703030507060506060a0909020706060e13060c02070f05040b0d020d080408060108030702090c07020f03070b0c0712080430140d02060708010524030a0605 81
    0x3d401d494840101c410030301042c0c6500c03200c90088420b00444000040c42140c00b13641c0c900c2008210041007208000442c401c2e65066a50031f40303854024155000900020700682060000c141c14942082001c41620225000180c0f6100182805c0014128648c01803003d112030a09200e820009041541b01c40780c007032503090224601000049035903155034450001c20b8000c405045c012844d103908038030403002c0010b009441d003405d1900021140c9038a01d104540032480003c040120380d900340203541c010525640034501700080d940108601746402842c844940c86e0000c1d4820031591001e410f14102e8030054201c4000ea61148201c5040d81d02c48001c02400d4418814006070030085078420303005a03507120582c0c0b42000c2c80c2c41c210151001140000459044040707d629440c922541040c1038028010180c60406d1300f0401703003050610211209080464221504100071b182d042a485411510181c841c016100b480d141880d1031104402c400003100c0030000b0910042560350f8100a080c2c4804542c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 640953588 1250 640952338 640952353
    0x30b010b041e050f0105070302120a0915030e0a03080415110d0f090c0603020c150709061103030f06090901020403060218030f03070b071b12090303030c0509032802060403060e 77
    0x1c04a21120921642d81d0084640c045000113501c20f5000d040000d1103070044807007a15880f000c0c980d141c1c111180c0d08000504624cc10005110b12081f59a18290302d82020850100c00c00c80a90701c1c0e01c3d1140e8003606002031040850200039107800c4040b11011442001c10503500011180016a440182800021030528410720052034a0388180f0748025405200c00404920b45617054004e50008070a54105d0f02a01210121118202011510a0100756606164582480d00150484c40b11564903e07050380140f0802c148134001c06003068010b44100e038501441c0d0b94903c81c060180c0300e181c000a142c1400881d6003030450300044090f002010342207065580145103010b9055490040880c041c010b440240c3c041340c40b1501803510300002d0a0701c150744c01a080345075210540e01d0303c0200d03400000949001e108000349070b8103200301c551084091038601e2030b1000c01e00010b03a6503aa811f82b46c1800c4942c402d03102c041c103000c070710101c0002640a0079443e10f480d941d080000c010549901032500c0d0740140e44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 640954838 1250 640953588 640953629
    0x504020f040606021e070f080729031f0f14030d0201052404060b030f04060c05040b18180f0a0501080a030c1e02030601151b0228030b010b04 62
    0xa0200f07a41d92540103207440040004100c100c4d10009546205031701500c580411044800a28200641850f8000345503240c64801032884804424035090340151005003810808414403040f00c0c1c1002c56800d0150210301c0005442141102c80d901c00340c070b406c5403442d00107000c44403131940b41c034840000c5081c0c41d44000034503416400c0c1d8108a4010782c1e09100007099441d100e0a10080d0140454040c1000410644600c0f126202d60700607a0150341d40a50b840401c0100300fa02e0113511842c002a147c464105031808805a00500035901000c0203280415007502840d122481c104d4101c0341585080302c050700713221510003000002610001003d80c00c3c5000404c3c80b100c00603450440740d6041d514410840c00c02d1b140c0c1001d400300040100c0c41241920302074800b50b9400c012480c0a440658039408041c80d1700b4038041e000c020300303123421411418500084005640c0d10b0364480b485001c203100f4803240e14111500746442040c0e5401c004c208c511044000704160703082401901c1503503449040d809220003000d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 640956088 1250 640954838 640954841
    0x6090509070516060b0915100e061b1609020403140106140607110d03180e0f0103030509010c0510140f0f04060b0d020616020a051518220504020f04 65
    0x8946500105104005000705a0102c00c1128505030050a000550041030000202e41b0401541c00b204007201241c820809450681940d840c40104c60510484940391400442c03158054500071038440c0380454017076842084140300e80342180d00c1c0040000b46d250788405181c0d00a402500058a07948407400c040c51081c0c07014820b00c026540c2140244d5040d000d960100704003a0300001c0d00b00d0308112282c0082e9038a80b21030040031280c1d032103034072061502c444a000120791000b0962110030000600340500c0341c0c840e040726550b815030f40c0526100d550381c420400162840803c01000800603c01d2845c4c86038141e02c41d9000304100551b03500100030b15201d200207031440c118150340440401c0d41250128000070303c1940082d05c21070000d0026010208039800007030b1950490f0314109501d21003c28403004601c0c1c0b0022007005071804503180c5032610f8042584d00c009006201c2e030801d5541641023802042d41c3c070448a50000b00301c00c01c20203076943d0f0310b80903540900000d580403409030007140d00c3e606452030103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 640957338 1250 640956088 640956091
    0x503030405160e01031b0902030f0a0c0306030201081614070c03200f1201181104050711061f050916020c060f160c150504140301090b190f0e010606090509 68
    0x14910f0140c6680d0860300c2e03e902c2d03d4404071040308584002080064180024000f4500c142d800300c03c5000549000414007042d500c04228042c101483e02e4402c2c030060f80c224904642001112010459070040d138007003664500c8803d22480e03c0c0c00700120321001000700409403101540d00c02c06e8541d0000c0344191031419880e550b1076949612a000d203410384928148080c82400300c03403a8100118054294400604155200c0f900c2501c1c3c011602e40042c1c03560905000755a080306203441c190680765091300e00c0b0341c1c17543c4010b048100c1d41260010300001210700f644200d000360000a080c141c050808d541000c40c40c43c01a00b0fa10054040e400d041412403500e03c041d01c2c030700ca04180340d491808400c58801514040792078422510001614800309500d00810094030347d103480c0781c031940e80c0e45040401400b040080e444800b8400d07030402d580c030000244a02c03245900941c00c2c0048602110103461494040c08400442e0320480f498140140d4482005400c950f00710b84880c2c5850101c60303240d0f02400302c180b20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 640958588 1250 640957338 640957349
    0x408030106030e1005011d1515030a0b100c0204200a05090a080f150f090c01080c07050f011e092a0b04090c030501170d11010b0409050303040516 64
    0x90004000e070038001d811400c8a10581c00941d190f2980d0b100d500c6003100d03000c0e08819541100c0451180c070b04205030349090b400c540d4114020740c0f60030b40c100005e681c8910001d51804502c10110114a80d82e402d50001c0140d0417006002e00b90382c0d100e14800070050a902101640715a08290312600e40801424607100f2814040130014900b504660041d03d00e98002100640c2061f0760850000c0d2030a01031121256440301c4901074090012020020540800017424588904601205006a00070001031240074084282001c00140e5501440c000746400303130040c044d005000314011205aa001903006a07604000e070700d00e030620403410f0046030040b1601d10030002e180100e80c036072008150300160704100003070403e80e04002c911511074059800035000369004500c0b25840740c03c01204250580581405800b150b1040c0d483e81c0803411031103640304030640400042c0030300420707000c0318000d082d04074101705c030005441400400d506142c925900d510032201030702d04d401a8618a07100c11181200441102d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 640959838 1250 640958588 640958603
    0x6040c030209090f130c03050a050c031f180b15130b060d18050321060d020303070308060a05030307031706010503040309030b090a060e0a061a15070c0b0c0d02010b0904 74
    0x4d4891444011200001d4000908503145412080010311606418009036214002900c104042d42c503100e0300e0011001d580f503110380c0000750219a01403841c7c6002e0404003112401092451600c110755100703a48010000d01420751340c030100300f8004c800b0781851038441d2041d50b148919410365030041040320714400d01994081f10800c000701c0c03d181c881d00141145c02c044458400c02c5e03070182c0d444610310740c4805515600004143c0e03000b084245406100ea500140580d0f40e080301c40580c0c1c0c006501c9104200d401030900c1140f0000c5a8a52074038a01c40300a81000b0f0122982c4101505020305200622802e01030300380b86250015925507c0784040c2ca005984c55260f0920150440c0e44e032002444000703003111403500c201031070180418030038000c901194034401c01502840140381412002c0d144000c214003400030314031800e003d564a80031282d040c2c28440b42c6840380c503821286040406003501d03620105840c0c07808070b0f000d8208500411403141d0f010301da0b00204150501c88050280002d01120301070a0784 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 640961088 1250 640959838 640959841
    0x30605011b0c080609060a0c080705071b090c02010b04060902090a12030507020603100806060103141807030c0806101703031b0d06080d03110f0d0c1b0b06040c03020909 74
    0x40382841c5810384540d101d5504042810744921545182110490716402c4030761140003440f10310800c6205404010307450303290464052070100000f9295100c0d0910007001c5a0310516468450081d00c45d140323000d4207034084184240701c80c0045c0240038011400380c148c4120320340f80000407407808a100301da0520502400d0b10914034540001600d480104d00802c1d01445020401800181da8890095100e9041ca074080c045aa041a1005180c98002015603050501d0a01824000c0b45400c124650103c4c40810103050000e10240c010b08150045d40001c000001d01c26022407215804150a0b00c52022145c5803550035981d81e01140c40340c50848001c3d403160f003040012403c0049034080c1c0359420030715070394280d203046005484013040307600f103074050724807900001140c09515a05009107440a00300c0c01c1c0380c0d07040440c2c103014000684144104c0c00286640d600051482c64021082d02d8034840000200742c0c83e00c3d0260900d001c4000003110114451498048203a1015000e03100352004454007500c6050503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 640962338 1250 640961088 640961117
    0x5030a0f02010315092d020a020c090606070f06020d11070f020118030209070206160e03122206030204082418030408030a0203130f12030309240e0d03060501 69
    0x510b207aa80752400c8441c14440856480b92038058854090000b010407041807071107030000c49012034240821b6070358078010450904444d900080b62004600b04491840050310f42600050071442421401880c0391440d64101c03080c0404e0368040c081d540c4500000344403112020402d44000d104a01c2c00400911403204414055403103003072180e000345c42c40e07001c10740c83d161a41c00081c4440030840300800186c0c460404c102030078100c0480e1300c0d4202d035942030038014103058900090b20b0b501e416010688801022524040b020f09020034540251103100403905901e444840003000383d4170900484d0b1892080d814810709282108011a1203c403690381302c607e00d80c503041d00c1d01c0b00c0840340220740c68907440148004142e14005000030014003520360020759881d83d01c1440c0700205400d5511606482d104413001700702c4462011080403181c0d61501d400221088103103400c0c0f0094941c65409a015940354041c0c1a095605902200b80f5106e0242180c401301c02108c801c8003074231424003c5a00254400034030005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 640963588 1250 640962338 640962341
    0x3041b030201050d11090d05010209130204120602030604020d020c210a140903011d1605030a020609130f060e040b0a061a130b0a081f03020f13090b07030f0605030a0f020103 76
    0x17000d180c00070045182c0f646000010390f000e211400c043c1c587c1d0b50300003203a1005207000040c00d007040420360800e5050501e01158410300c4210000040c040036000400100591340f01c1d0304035192050044811900c50b8120b190306030f0340740c1c0c400c0e8941d10f241402070300345602181c40b0b20942c1c51a80c001e981da01501c811390b400806070b58001140d07494040d900c0b40821240102c1c13400c001004c0c103860a0081ca45805114852183d0115540c070090290b0400301902d03001d6120300c03080344c1c1c0400c4292030020060f00940007130340092014807803026001d0300c0c000c800f003000c01909445501490003141d08600d039494512081c0304071040c510607564003030304050342c034407085040c400a4065070300c03169283c0340705a58901250501354020f039900d600040501081001e035800c01040c160b04a8002405030141500f10b038007003401040c0c070810a601c1400c175403a104070010703801d410601803e036000c84005641d040105000d005045022030b8990614244034010459050018502100c980c110b50100300c0c2800b103800660 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 640964838 1250 640963588 640963601
    0x12070f0b150a140316170111181909090f02040b01020303070801151701080c01261308040518040b01050102010e100507030b090103050d170c030a111b0303041b030201050d 75
    0x10303013500a06816100d030605084000e0014030260600e142c0790a80d071001c2da42107e080c1c1901000d6110148480c00e820b44040c40ca12080d0801601c1c41034401d0000e0030f0f09020502d4070303407040e0302060030314000d2020800d24842c1ca8491501c2603a040c0b003250820001a80c0728001114800300161446004000303d0802950f0300414805500701780d1480310449000d940081400d802c0704103980d01c400210714880d41d100b805000f20903010400135071140c1045e6125000542c0c080d002d5905884101c040c581407181c098215001880f00420f01040b1161441c00808001011581920703121400c07c00015594010702441798107504500140c2020500c1280840090002410120805540d03080099071515169100341c083c50007000145040c0d0b042e490700814041003e114000300d18a00d4040c40101c030340620a81c0c0e0042109800441c680c02c81e0711072500c060203010002204040420516003d002d004001107000d0380c0100307402030700900b210001840045040c40000d000440400021100c04825400b98 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 640966088 1250 640964838 640964879
    0xe0f0403140a030510090504171e0d0b13061409040f1e06111602061612030b0a0f14060310152d0e1212070f0b150a 51
    0x303000c560000d0000000e9030046018400480e0742e03a001e201d01e5908075002d030170040042ca041403140307182a43e1504c00b81c0000001410038034101103081440044800341403040048451381260f04c0f10078241d51040600355503180d4034090103000e00010002915801800700350303a6545d03410001e2008000034440c10710001842650800c0c2c0c40185c40c0c0c0040d51850040925803004d41c4e41d408051014281201103c40f01107550303444070010040382d0881030000c007c610301240c048601584400fa40180748082a030100c0c2d000b001075500724480c5c54101d41590009804000c156000360502c0c1d110848041c0038071130307802589035845520022072520b280400045900265490006100503580d015130130380100c80380380d184003117030381c00e4a0f0749000012201088141c0140c600b41c4216805565000742c0b01c800180d00c0e00d4050f00c031940700c1c0708060300100300c241030205402d0b00e002e0790b40d1101e09044610f08074009003122101c1c46580031814082070003a1580c950300300100f140d50554540408120034400e0090b00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 640967338 1250 640966088 640966097
    0x30804060c1110020106080d020d0903021201020d0f0606170103021806061207050703110619050c09060403060b011112040e07210507020606030718020306150f040e100e0f0403 77
    0x14245191240708410103030040f03a4001040301414603981c2810318842c0c111040865100e07812403040c540d03200c0306020499030151054201d1150200e419070180c4540c1e5140d920140c20540710b101046501e80c0310700104c90701d50781c0e1583e003000201c5039440e81d11021b1001075440074164080c68151101c0c041e5442d000754004082c22300d001c6403001c0e4045910404c40d4500081440405c682c018150080751114550396075030040d00042c5407401010b00a40b42c0c82d501028032660b28400100d00c0c51111044a00440c001007541e912183e032442d000001d032600001c030a001805080c001088080005a01041103226500b924109420070400840c5c0071801044071042010704a005a0010354200070b290503445000c0001c00d807450492006850110007400280c06603021b5002000320140161105502c20b40c11440540d5a440b103000180d0860351650244911080c00554412003941c604010001c541146560602c650b40740701404400d80314510900c540044407000040211003400c69550344280b09040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 640968588 1250 640967338 640967363
    0x30903130b070b010504020403030c24060f1e08070b071505010b0702040b01051e0d06080715110c01091e0905090307050c040b1f2c040f06030804060c 66
    0x9180c0351000541d03005200300400002c40070705100c1c049016502414007603405614052460384c0003003a61400300e401038298a004817205180840110110412480a20003400f000762a07503000d0350700180720700c15500d81c00301900901040c445500030f81c004a0394020013801613a07140040c200302c0d5520248045507684004c040e400d000100500c610f5000c0e0a000004984500030342c03041c00101c1d0202c040c2581800300500c174400c60000e00f0750261105040320015161109215480400a44032641041400d40940c0f00c1c00300b103200c014001c0445004159496000020880035441c0e10b0b00f10140c455030001d0f03000c10701403140c3c190b480e00d07021242540045070400035542d400d03100200c0710203695900741600006800c4051007420044003040034401c0b1410000e45501e00001000b0b84201890700030010400304440030b0040c00b400100701040301c2020460003109031000c400b102c1c00c090282142c412443c04950b1408220144290360503030703070300949a40c0b070541800403d0342e5184910310100e411007420039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 640969838 1250 640968588 640968607
    0x1d0a020f2205010609032a050f030f010e06040516050a05060a1b0602130f0b07020405100905070c0b0c031303030209151204030f3018110f0d1502030903 67
    0x2c52a07000f000b155a6840340c41341986880c3c416100102000202c400f000c5088048603200d00c043c140c115842265401d400c00750990100b03051648120081900d54603110f400503c8002c007044042c4118452030070340313801c290080c0708030000c020350f401419001107041c541030004c0d04104000b00542070440c101030826034100044c44440030340c41d1030b040720700d07030b030040b5022000725407560034000a003681140780720042d81081ca83c03012034002e080000c0c1c07040b40c6440110b03140e4000000504090090301c5820701040c40c08000c040e000c032101120032185110b0100c000303a0001046c0080c0c0b401402041c3c24004902c085407030880294110f00c02c034540c443d044c02c0c003032409401345800078480c0d180031954001580c81c050401800309004010078406001c50001d09290484440480032181c0b210524074020070420010054001d1141e0302d070000d154080c0500c900305002d018400a180200125a5100c82d074480340c060065030340180758000e0200410800440200505801959001211008881c201110301 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 640971088 1250 640969838 640969841
    0xd02090d050705040f0c02060a0903030e03031e0604020705061611030a0819050105130e0c0a0b0711100f1d0d0308010603050109090b0f100302060a031d0a020f22 71
    0x4030421511640048010071050030540121054000e162104010260403404d0194407481d00918000c64039030b540031a9010940290b00544861701c1d23520842c1d4507890075070362041c94100303034900104c03182078030b04009181031400d8021680200da022000c2c100300e8a4501c0b44002941c0c01d00c07a80c1d0b083c00240803c60340503500c100042d00c0c8902c1d00390342d07195027804c1c8140701c003c1d120202c92441c0043d41c00d000c0113000304d403180140c1c8060042151400102034030240c5415061100780c078002540a00010f5000407511a550050016580a200180e55580e240000c01c115212840c50140100d44503c0114680c60701030084002000c100001481805800f04c1c0001e035182c03214441280455904001070199551500c1024003401070b800c1c2c00c1041c025562a450086c607001025084404805800a07402c0c00f00c1000090066501400480c0c54a00d8864082c008c0c01014415480308620f881c8000c9070001c000039040c079200d8003d44046981c407120018402c1c904007414071a860703003c04115900c031200e8039 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 640972338 1250 640971088 640971109
    0x150522050127080613030e0a0305120f04080a08070b070e091b19050a08010b040803040b0a02010f06080102091e06091c051c0f180603020c1203010b030612060108030a050d0209 77
    0x41c100700a0500d2020321b00074080004c007283c2e4a0160030100c4040c000100000741c0059851003040c541e17925040084803c070300b00c0c070550304801070a015000c1c8810807c030665001e0325200b48507145d042c8250303594020895007615005103039a880320301d2034080340581d0100005440c001c2c00409410340f83c940d0600d8020b0701e411040e880107000403000161045503642c4241001d01622400f08160b18140c6841c000943d00c1c010350294960f020000503000502600035403144451014000e803d100e031541e98180e1600079002030060764020503100c061552045d007007100300402a500100010b0510310182c1c1400944e4500b081c0480034100400c18200200b001003040e1801c540004582c901c00c004024801000c03001c10307582d83d405100707510400c41002e000721000c0800b44c0e140e030320f030040c0c803044ca11049a1410044043c0c00012640010011445400181c0158030a10058407103040e1400d8496410743d4403907091084082a8006101050340584074000508018100316005810030440d00d0000303004410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 640973588 1250 640972338 640972351
    0xf0e060d05040c090c0507050307060b040b101815020703060506031e0106030303061508061207120516050303070b011a090406090c0f0801061d06041505220501270806 73
    0x20383e4004102494107809140d0308854107240c880c0c02d01c42d684c0d4600b50b803030040d040010140340c0c880b0001e004586840d0300c8404242c2d401002c148003084c4003000a08840d65902e100a00719000e02c1d004a2401e042030034075010000305900030700c0700c3d0345551074079401004050700701503150103480d150400155424410020039454030000080d001c2c41d600d40a812149244c0c44a0751288910045500b1a40c00c11074450340100140c0f4440040e02c80410003500300189038000c00d0011680003040070503c10006810343c00110b94002c807200c9182c640081554030b014203c40104914064401408a061074100216000d00b1400a00f4189000c1a0019041c1c8140d40c101014866035003001944a90788018151010840c038101511654140240104010401c0c00829169002d80f1002c0e02103442e11012200105141d042e08004000704900040540c2d1082009050464841d42c001150a0781000d8040c11908141c50310040d00c41e4176011000d40b82681440c5c0d071030091003201f000440340d400f840102e100d602d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 640974838 1250 640973588 640973603
    0x4060f02040b12070206040f0f0501270b0c0c071502010207150207060c030603150c020319031407030e0d0c03050c01090c050411310f0312120c0f0e060d0504 69
    0x1418020041c00e4114004c1c80c0000310360200042c0404200b120720090081d0303030001052803880c111402e016000d8400e41b914034403072201c070107101d9002c0300381c0c40c1901c210248108207192854a660340341c0301c014000c0f20b154010b1500001e404101e80140d03600004250000d03800050b06002d001d46039003400803104003007140d070282c0008000741002000d114420510b00305080411149055484d20100190820b94000e0f5a642d100d0106c031700c00d4002c105075a0015284032030801c41d5601d00344020f003e0822143d440c070f206481407021a04842c000e0003000e2103c0d25160040241c0d005044013100e42e07452206054060000811010102820a0160807010ba000c0c03801c004005103407000b44021680e020081080e503d17800d100400034031100e10001d0842111045104020360500c0201c0140d0440c107600c80620000900f02c00000c0245d4050340c2404801d280d1560010004d94588110035100d1030b2050700e0000d481c0c5200a0720741030090303141541c9500c02521680c01c01c558885540100c4000f038800b5108003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 640976088 1250 640974838 640974847
    0xb031204080601090e0d020c06030a06030b160f0f050d05070e0306040b0f06010905130f022a01050a02071e030210060803090a08150a050c0d0f0b0103150f0e04060f02040b 75
    0x226010b000740c4010700c4480000b0700000040b01030003502d980e000c1da4581d01c250000000708139a400260440cd01641d00054071402a0070704411340914494405262004501070b01d05510314039010b00620541041a6204d0b903162100140c00f240003000c1c000d10300010321041940440c80d0b91001c0010502c81d52290058031030508140e410200b81c0c40d001018030381080041d01060065803224180ca5050410500c0c01061400c456403a20000e1b02900d906190300603e40340c0400d4a0a0503030b000701c04080c203103074000c20641d22050440b009074401c09402400310b400c0c00c40382c000b90050340c600140b00b0602034410359040d0b8070034a1158040d214241e00c43c0881d5400442c00880601e0100b16100c0140201c100805026002c031021800880c801000c009c941540c03040050026680704040307440441d80b8410401140c01188924002442d4180b8144c0c0080e10b020044150906002c40003020390b100d03080d0000b091840c04004800c00c444c0244110f540716101c0c1d100d1440c050442c00680003a1204041e884e854 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 640977338 1250 640976088 640976099
    0x60b03040605040c051009030b090f0d1805010e150c15010807030b0603031e07030507052406040603020a050f01050415050702101707050705031e0c0c041406040b031204080601 77
    0x204241d17400c20b40c4141c81c0c1100c0d5500d99a0000c0401d030850303601078101e0040f5981c0074000ba060445103a281ca07400d0240c55612000b40da80a0210060740049140a900503601d4900441c3e112201510305a00142e029412841c4208120b010b80810440441141c04202021007580e8801784283e02150765640140c60034010440040080e69001009800550a0108200c8800400400070312a03241018000480800745881038044500e9035401c4001c4403941c4201c030b1200320703403001c195000c258128620700104407a840d181c0164411a900200000d508a0070a020000522440484a810701008100004541f049002108028103c40d203c4d591900814018030070444003004500c020019140c4000615401d001481c80c0c100034a07141560720b0f8442d031f18009285105a80c84030340c1141402d03815881d81810180102041079020b010b0f107940030904014001512040850740701984400c40c0025801d06003503100680c074060080c00c91700007400a400a14443d03220790080c1d10203401240c0103001d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 640978588 1250 640977338 640977353
    0x2130305030913140106080705040306050106080711011b0810051e010e120613060f18060605030111070204050907030f15140103050a02041a2107080c01120209010201060b0304060504 80
    0x41440f9030302e00038000302001000409040805004070b500f8005510302040c1801c0c401d0301a1f030055940300000300700d1540c403000e000e02000c10417260f410024034080801c006a003418003480150b460204184c0c80d0344038078190156203802008001151060000b500081e050391001c00b4117a541c04414005032520080d0b20006080e01d0340d602400e801080c8645680054690008040360310007440f903001c0641e440c60303181c808041c02c0c41d41e0001107030341e0074100c0000c04125000d0b400b0040358805c40003000220744d210185803d03610901c0b50201401c030107102c05005803d1642041394008051003d80c1c02c4141c890351102c1c280c00b645041a02c022602d60304044608040748104804000385040392403040d8034640d500c03079492207140c4000340510344a0a02e080c000b85001012030801030b00170f02c0c84c44803c003982090751081c03802050516083c4640d4100048442c000706400c941d603101a9150880c11a400020002a50046003824115941c45100242300743d03122000d1405548103d02c041001e0409061640 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 640979838 1250 640978588 640978609
    0x10305010f060b0409020f0d020408010b09180304050f03010608010c08100909150b030a02040e0a1b0b03070c080403021005120f09030a0f0e0a0b1c020307020a0213021303050309 78
    0x607111850404280031610b000401c0c0d034122880c0c880096501c20301d41d0340082d40e601448440703064550000ca4041290501900410420082a284481159585030315011811440d070900c00143e041040280710f1070500715410500144050b0001c10038940d1452001d003154074026020000844d0719003070104000f1204034200c010074148074240301d540c119031140c8401c125804001440780b582d80258519540b001d0102c045000c2d0000c0c01048490320715410103445000c05442150300359545015010302c5a403019070082507401c4500c115055580c0c42d00140c51094010405803649201840000300680d140070b10316914203256503a860f268012014100c200181c0034001d1800c0182d40c10030032508840001c143e44803105646405200c0310716840301550304482c60781074a074202c62140408540045048020101e0181d80070380c1c00d90010007032445008900040c4e4540d00140c21084400300980383c481d0104030700c0201c0d554014980110440300b10a411156401180c60303400c081150901c5151094444 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 640981088 1250 640979838 640979861
    0x120f010e06150319020d0506090f3a050c0733171e1e010e10150e031e0105060d080d090501020915030f1612112101030501 54
    0x500d03400c0c0701d440000e46448400d0403c2c030004444810404c15550b070b03c0e00e014801c58100301600c0c00c500303106042c1034450550700c2d20581c25200e01a050040000c2039520348401c108018494007404800a10f682000040b00341c1d42d07c1001420301c207861440c40140280c100800b12099008404404c2c00c8040103000030b002c2946207a040614110a10150485c4000415101c070080c0c1001555880e00c54a00907070800310182c8910000b201005041010032070503586200035100818541d0780c0e07516150720a64021a5841800900800c00f00000c42c80c201c80c0c1c804022850502d0400c0004c8100801e1070806465913080140c8051501c08040c850288180e60704850142e0740a5001e0180d62120100e1340b1075060045040c50b0b603104101c0a00c542941070743d501c60700081c0700901d01e009031000d408071600103a421000d40201100440c180a6030322408000f04070440d129030046c035650b0034107240101003a802d9000c000030303f04030101c280070703507506008181003044d40704086950450400d00e08507410032804 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 640982338 1250 640981088 640981111
    0x3131203050403121109040f15090204143102040e040b100b0306030a020f1201151e031203020702030705060f0703021204031e060b0d0807121403070c02120f010e06 72
    0x8120701c00e0f108883d0181b10035100072484c02d03010803034030000b4050514403004201c12013a0110b40c525290700100120748542d00428101119641046000a40d03020540300303078019040042d0500c03154500d1601500c03044000103040c07a80d10514142128801c6400304c580c41c4055080114420581d060340e4090a840700006095141a0740400d50f141c000c1c3d40003030703c81d580d0507180180b180d46500c8000400c0301018000c2c000380002c200e2094292103240159840051001b11307000c041500528840b040303d400001138054141010740980080d48001c03030580e05401801d0002c141e80d1102c9009104500d03804807840d030f5800150400904051404d03015040005040004002088028810385c0c084e008051050080048a260030002400d855101039044035401010006004520026010b6107006900300641c200300c6203c100c8640c10382d00c0079602101010320109000605c15182000d01a00c058a80c89000d00d81075641c034644820014075841c1a074407a500f070b0359100d0050100e00d8000d0880c810 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 640983588 1250 640982338 640982351
    0x1a0105010f020a03021908130b0a110a0803010e19051f0611030f0c070e090106050a05010318060f1d0a0210110a080a0e0d03020601060201050c070803010302060313120305040312 78
    0x30003c0d181d46d40c58080c402000d40003544c41c4148070385c01c130071149512101413084450503910845641150070101000d400300d01540c15560602c0c10100b50b001c4c216501402551440e0b0030b0030940440460050411030784003101d0780031072800300c92a20845001d18018052500681c007030041905070142a5080081003100004c11520030f1500042a58180d40144403542d443e03941c40a10103240051075800303003841e03150100900241c8130040d841003040c3d03081a0f0301c80c01655155001034050b01c400501c43d0034040d03e18184080070919a6000350b1010440c0c0e4404078080c999595692144444561702ca24260032242c909811454803141c191001250b07030428150104040a8850300c8075001403028107100c1002440d0344c0d40a04c1050220a1917000800300146100d860030001d6441e003090192001662801010074940c892590541d424103505c0349419155a0031507084c40120740001e84000d266114050503103001500803006220800d070b041e5070000303140c5403604004181d00218018003064519040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 640984838 1250 640983588 640983593
    0x4082e0e0c0409030c051b0109090204051003090203120a0923030d0509150307030f27080705070905041b05100914010e04020a03240609051009031a0105010f020a 71
    0x780c0c9641d910044034001104020f50900380c80520020750024040e004008110310200700040081d001400203031703590790516456504690892189000b42617008408507582a48a40700760490b200407840542036a406074000100d034981500641c03440301c0400e00d203100078801c890f030f42d56400d1403000710510600181d40f00c80c0c02198451348042c80302400c00000080380030082d260050100c80b10f54074000110340e24540344000034020000c0410f003100181c1842800142c100031204014041c420481c022001c10810740e441205691003554101d41c0c0e4000c1000c0024000401d10607070340700d64001d008000c00030340a241f80036101d0410380c001074491400100c0032001d01741d201102130140d4011420042d41d140c1d9490045e82d6641503040c00c5c81d4024000100c03451096032540100d00c09642c501e5014003c02240d00c05c00e40013160300d000300e00016a400748100601c1c40e2041500c0d134031351010b0404003081c540302c0d203448049102900ca079402c008000f0004000e07550307104007203240c2d00701607102901c042c04060f03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 640986088 1250 640984838 640984843
    0xc031b0f0507060b060409090614060604090c09050d051e0615060318121e0f0316051303060b10170105011115130c0f141504082e0e 58
    0x19400c20040140c00300d000020420745034040841c0c00b0300144450380b16070b52410010050101e41100f1981d4500380803412940038180740711103020f90702c010700541c0cc0ca030601c132000004004241d425030410242c4400003c594030b5503071030412954000c402400b219071000b1907510035008140583c0d503450740b140707080044144a00810011500040b142c1c1a80c0380c4921139903000d0203802244000550140d5801c502249020000030071900c0f060902210380320000c188000b542e801400d05100c0d219104100051040030204441c283c50440340c2086400c0200c8001021607015254108440690341e40e50030b12481e04e040c242d0310800c0c1250f4900000c4110000501c0c590260040c800c01e41409210405c51039884000d10000c0c00c1c030160350034090400d29190062541ca00310f149810b403041842d00c1c6000c902c0368200043ea1054138110450b032107078141c0200c2480142c540040d16190310038014007010a50038014031003d0f0107480801e01c1c0000070751140d40d4043c000d0074030b107004001c0280342001510442401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 640987338 1250 640986088 640986107
    0x40b2206020706060801021b07080a080d02160c06050705060c0405030d080a0b0409150506120a030807140a050306120f0a15020903031b01360f0b09010c031b 69
    0x80303400036803101d8152529034050882e0f60462078940d40041555444a1409201c445081716075100b02c6284568a10116860f209103c070040c1902404000d03401c0400780350b400070301c42811429040f80740d220030780d25240c10080854008000144000030b002080c030904000054020348035007062481d1520b0301c80001d950310b00d120482c6062025a0001a01002071a0b0000710700302c1d40544184055006403400c50a4020206034a4208500e0040815602c1c01c0100c00903072010001c2000b01441c4565880590b1840001001402009080c0c102104071070f0700c4501800074a40b070341d203c554884c100b6404025880d101c500c00c0004c80c1c1d01446140d141e4210000c6c02c080a140c11403c060084280300d4000b034041e11406520a030188000600300321021320018600d224402048000c00800785640d20402c81071609104c07041006800c80c040005914180c140780070202e20410480d103080c41c03103545200e80c0e0007040b10720310364696442e0005020160980100c480a180f41c4801102c2d000034100d0180500c207a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 640988588 1250 640987338 640987343
    0xd09090c080123060d0c0201060b090d240c030b010e030f2a1e0a06080402030606011b151509020304170702120102030c04051e0108011a090a030803040b22 68
    0x340444000740350200260b803e4480000b42103543e66941159400d406408030f092101c005620384140000c525aa1000383e900700d0400a0000086200031341360251703865502c4041d0010100c030b04a1801d80f4102c144a4003240d09a1601c0c0854800f4546002502c00d0000d840c41c0c03800798002c56a00c012084000c81c0c1c4402c08c09900c2000380542c01e40895681c509031104104a8020a8181e59840e00c0780ca105048150144215411a1110703250081201c150700203035030081d00740c0e1200000c0f600c10b6000e1010300692980040d10025420010b89030000001c0321032a81000031991003401c42c0b2405041d03014a80079040180e000d526600f850ba4502008a060b50301c040795551000c030300c9804641c0c451310f1410264141d03100941d242d00300748080c07180c0341d4824441e0503c11011202d0801001071000c0303401c010040d05031103d411070703803a101e080380901c181c007522040303480d000300031014040c0d603601c4160010f180a08081ca0304c91619240c10090004054140d207040f481c00c80b9000c102c1841020302c84c01c07080e0f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 640989838 1250 640988588 640988609
    0x72319050c0c0303040f091508030f160f0605070306150221040807141014030712061509090b0d050604030e0a210318080a060911040c020d09090c0801 66
    0xc020350421418000c0c2d101449605000c0020001291103400000205803985160100512600300c004890650003a00c25102d0580052000c00070609015003e0143d0030a0400c0c0300c1b030250038668405480704440802100c0083d42c41050140080e030511805000d03121421210101c0b50404102a503034484001080284110000301c60001305c0301c0c1c2c01a9001044110126402c25849180c01c0100d41810040c00b13000380c07248040310b00f03103030720a03504202e10010400045142d41c890030401c0b0b62074070b80818022440d9031a02070010b5592640200200d152800f552a011036600f4400620183c400364a00d103840340708503031110004520046403454015074182004c0a01c50410310114003401c101d50302541c03480000080c03070840303000d00b408130360b01240c480e1303458080101c40391404d2013032140e40380180b010540c00040c1c034200140465005014160285012800d050500d800250960305061400001600700c0a841205030390401c0d070722070207480303180702c1800022000503008110600510440c854070b0f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 640991088 1250 640989838 640989847
    0xa0b0304110405040c03050c031501060305070221070201080618010b070f0507060c0b10180b06040b0a03020a091502060a020f0d1401061106090a080901020709020307231905 76
    0x2000c030004030070341400c01a01c18821441d10341031103562004c2910081d107031750046600312641d0f03250200f10f54420192090204103180d003400f81c00c500a02004215205620440400c0310710803030301c2c1151580d42152500040d590300050710006204400290006000e007100c1180819208582e036101815540030110180d192066410403880f41c1c8a100030140841c094041d010450640c0419030f0786800d8001d20240d040e075110191520a029200d01c103102440c02460031420b062007149d08080c1741c81c880104103a0406407290250841580320b0041c820210f0750000b02c007590b180e0010525801448480800101d41031040320194460100a119100d1240d000860000394040c00b426580c05e9680b1207810020344010500ca005141801c1c0185030100d9120150a10904000074150740b281d80c1c3c40024044008541d0340f040d020f078101c0d950036410b60146400100391010284041c500c50000780c1e85500c0d41c240c19034018210070400d0281003102000c20000c0c80c11041c074a101d170034041b41c00b42c5820b554a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 640992338 1250 640991088 640991093
    0x3c030603020d080f0d0f091e030e0f01110102030c040801110f030f0c0c0f1509010b0a0e040303020f0d09120e180415060e0f07020705010903030f0314011d060901050a0b0304 76
    0x64801d0117a4682c0e104e1402c2c1c03002c1070300051907110549071445180020850348a2401856800f102d84034024000b4120b44c001d40010b0074203400d05010f00da018101925440070310b003031080c20380c3c0080340c50020340748010030f041150000900600007240e400c41482440c0c09142c080c09501884001c1c0711300c1c00c0e80580e0021441c0c0c0752140b81214036012210040c3c640d030901c0e0003000c81d110702d8050b8804010136100c0c0f020602c2038906205025500d40000c056041d0b540c41d008100c2d000c55001032094003413550070b10114000043d500014400150009000949a4450b24100d04c4000c000d000f140104850050010950740310030000c002180303041c20300f04c00140e64071b24100340c40040a01d00c94100754140380000810615000e00c01d80501d103416002a000d60795010300303d0740c2e0b03160b40c070925000aa14400800c0800e00a020300181c0001b28600824a00c510803005600b41d0700a0b848004426490346020401d00f10480d03025811160444034884194980000141d65041c10301402c0c4080030000b0101c0d04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 640993588 1250 640992338 640992367
    0x303051810020319090b07030c0639020d1b020f1c1e020f0907110703080903010f05090309100e1008010509010803040302011d013c030603020d08 64
    0x403001002400d529024200d440c00a403690083d40155001450790080c80c0503807409000020207844d5800c552500b40011920300715029000c01500381c078101d68900014428007100341e50603003070070440c0c100030040c285c50040e215118003000c3c00c80c03401c64100d0b80221007130551000c055403a510302c40200325602902c0b400041d0290541c0b02c906540704424001104070440c0c1e5242541105000d80500c2c50643c0748504400c05a610031000254044a4032f68018505d10f401100301c1e402540710728020000103507001500d49081c107950001c1c0c60888001c41d4010b0145400d0044201e0002e07451024002810b14400b010383e0703402255125449070b4005200d28650600c6004905040d50000703201e031711002200e66000e05160390a00495001c0c034540c00001c40c40d1903002045408496040e9101890341c21100c101140900c4803640302410807000384203040594004048108402504012412400d2061421600c40c2043c034051a42403500304801000036985880280300015042011941d4800c02060303141c0d07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 640994838 1250 640993588 640993627
    0xf021011010615090512060103030305130c0914060f0901060e060f040b03040201020712110613030f05010c1e0e0d050705060403030201060503101107060c050f1206090f10030305 78
    0x4030107619050000485603180f040101201070300352181c1101c07544840c05e00581e00c2c56104001c210754040801000001c0c0f190780120f61115072028844145e070344542e908803004010794041d040b102d80314040c01910f8400170350000d800c0321080743c807100120300c41c40120307480350014800c0c40c0c02d01030110070340e0581c0d0712094121601845440d038419540c0742c85501c2c1d20340b01d4006603000da005124640003c01c04000300383e010001190060000104501c40d40c1c20004540e0140d040201ca41015131030000000e07244800c01c8080c00d125000100e58081024402018004450424031000c0002c84403080059084a440e851124041e1019543c9100c01d00b0074916140e041d60041c1e41020b0005130000c18950306511003000d980c0b0031000c1e1504405ca03445180c090b03d054110f032082c3e0300c80c20444000002d145130300220001540303086c0641841d5400301d8103140e0707800070284599064582c3c010401c0038982600407561010b01e100052015007401d0102c00d44424207404010240a030000381810003036440348112 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 640996088 1250 640994838 640994867
    0x1305030f1303170703120b06040b0307020102030703271103070503060f07032d0f0603020a12110307060f180b070f0b071119240c020f01090f0210 64
    0x940e80c0d00d2410646000800c054070007034450300d2000f0010701c503440c001c40403030342101e4241c0e940c4400080780c0129074008000e40105a94031801c20880000c04e5908000514410a441d400061312480c0c504009401d482141406004104201240c114005026040210301680009a040c5070007290404240ba000d840d8021681c144102003c004804070740c0c3c55400e119120503a02801064440d03500c054003650110151250901042c09103005007200340d001c6c448400f500d0b00d010071030541e039801103045244036400480742e4040048030542807107000c080c000352407542640142440c52030320500400a5200000d002c0801c41d108075501122180154050003603c091010030707541740000e1505481000810301d003180c0c1c181c0448000380303009001d0810803080061010241400ca030300c0c4039034191707030204082c000c503110a0911040b00000f0040303451901c00e5428044002038a4110540180c503020000e101050268113100d0f8102c00107041140c100e1013103905079440403402c2d41061081d04d4004040c2f04a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 640997338 1250 640996088 640996117
    0x1f0c081201080d1d0d21080a0605090402100e0d0803010806060406060c020f0909070b310f0b07080403051b0109060c0c0e09070b0a0f03140609130503 66
    0x1a200c1050400d044504030794100007168150340342c0e070f00c058034107201d01c0341c402c4203240f4556901d40da6801e10380307204510a481007000790807210400d910782610b20032140003c8001071000080000c6040345116100103050100c41c440c10313604d0568000303841c82800401d0001000700403c0701c90b1194035440340482c00107034080709943d141e613142c80780035540b09011200c1e42d210394248640014401c0c0240984200d107500980310f1400c0b149410180041a03134003803c2c03203c031446a0344001400c1103400000d070038031041900003d1800b81d59516155010b421200c00300f518202c0888080140e80d803138413038040840d50b43c1c0c200c4948403919420600c0c82d43c001d59101400900a00c48007004d0b41400240c4d03402e81c0030007601c90346070058440318219054036101600400c1d003080380c0c10520184116081c41644400c4440031140441d4640c404140b45412404118003c24449604d016a480d014004c6a01d8207601d590160000c0c601140003a081a002800c8403014a048a24890502500f4800c0314003090400b180d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 640998588 1250 640997338 640997347
    0xc1608040b0a08010905010503031209030d11040807060801051e0f1003020903010e0601120308040c080a0308101505070204020a09031b18020f0301170304030219080d0207051f0c08 79
    0x11058a41e48000a00c000240c048000485d600c010352003100e05944000e00218140722010101340030410700034041c00100d10085c0325040070080e007406850306031503840c44100c0d01c0d545005c64a0f0301d4003002e508030b081071041d000b0040c08a621207410880301841c0440800342580d09003000b00d1404034110095036040003405003103501c0d0a030035070010a1101001e500802c1a805603012098a07203c080c0030381805c60556121101c0402c1c07188180702d410074000c2144084981e42d1b600880d1811032101c40c220701145501c010004e42c400c1601d0107400a001024000035031007044c1e20001d1044c402e03148000d00c502d0b408200c101c9054811a04403014540c080e005003101001814400b13030140c5544185035044c190002104560790352030094501d0384003504803c1e07045909140d9603d581745000d242c003281c01c0c4028000000503943c2d18607140d90001040002c6035503a03080103051400e18020110001c1503501c00402005692500b420780b01100170000340447c490f0f00c1800f01298042c0720428084c010140106 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 640999838 1250 640998588 640998599
    0x6060b0415021603080a03020c010b040e0a0c060e01080a0c020102090a09021902010207020603060d020d06090b04140a0b040303021b0f01230907060e0609180117030c03030c160804 79
    0x1d41c0498001101e408542d02d9143c030008001202c03102d030100400c0c2c43d8050011801040c020780242140006210000c02c01080d00c20100c0c003100c8804c001c442080c1d0000e15083c00384005098140c01400c510f1a003503144400781d000181001c0805485c074225a50349842c02c0c1c0c4941d2007035060301c06a10b4002c0444005580e0b4100040c00b9410001011040103180c1206003109401482100d138019400340089080d6590542007200c1c1e801000803c0e43c200c80e40e40070510002d91944600d01000e4811980005507042508011a041103182403c44c1d0540c001050b01000c140c41200d041c0d032087c0e061801581d56904040311102d4220684000d00c0c09120b0f02904400041064103c41f00701084081ea8004c080301040094204450540d21b0300c44a4202c5c41d0203000682c032540c901c4070a04005003981c0d00d80700600c80484c9000d070b00c4c058000700718808040140701d103540180d1541e20384601c1900442c104030007820000d85921014100e40c64941000507210840c0c618402451001034025403180d4803240e640 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 641001088 1250 640999838 640999859
    0x90c010c110d0b0601020d051e0d06030b100f0f0602030d2d290d060f0b0d080309060a0203071d0d1a0a050108160510030b0402040f080f06060f0d06060b04 68
    0x7550241c1c094007c034a41100900d201e04203940344016040c0070360203801e00b280314030700c4654403203a5800071098941c20040041490b001405000e43d08414028a00900d040054040300c20b4a0300b2001d02c840090000300241c6d640081a00c28044083c0c0c0f00040050002a8000b00c1c0480d12003c45658448880b5265a25441d80c0c000c1100e400c101440c044001060714500c1c0464407801800c80d03101880c102c604005c6050355008080c42140020005000018880000c1102c000104121003246c0000200b09801d1024082c41d0340040000c013081d801d605101c1000b402d00c01440765140e00034482a81144819960300d235200700001e40100d108441c0b520080700d204500390302165030411141c1084000a01450b00003800c01d151500300308404d21480c105001c2000f010807510a030010180c0705c541d000215a1188024070051105482e10313403209140031305803801c040030694918900e800032010031825417180070300c2030360541c1d0469003041480401e00d420380041000303070404820031001050102e007042d5039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 641002338 1250 641001088 641001091
    0x30a140108010c171e0406110d091e08041203020102160c1d0118050a09120e040f05010b030103030509060c0a03021b240307020c04150302010e0306090c010c110d0b 72
    0x1a681d00300d0592142c0d2284900305819140f1080c001040d200840b00c0d81e00d2905c01940141c07107400c020440310180d40000902d60006200c0c14007141c1e686e00060300b04140c9511100b034940307000004035180c1e0f00c513888104850107a403099144442c0404101c0c0c0400d4400c0d0b0407100004402c07502094019041c0c10b000c0e8130440c65000f50b210b004042c0745912801c0f00e19011440c12611050408500400b035050100301510001d48840c1805840d0f400990004a41d44c03100450821035a803140c1c803980c405010001550701c04000ca50045103800c0050000301c546404480c1541c1d09410155a2080245e0100e0000c3c4241d030320040c00b40c01034510f27010405a021484240c0d010200e03011500c030201c40703000c102208218209180b4100e00942c4404025400c0741c0c00f07540c1c000701c1c40c011385070304400342da005c18159046000390f0302c1f413000902c40078021903800a2020300103a6040e4005d251901d4000c0ca103650360030045940318184605100003108012030909441074140b409086c003480c2041c2460400c0301c1c0c040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 641003588 1250 641002338 641002361
    0x80601030b012903071b21030c0504030f140c0603010e04150b210f030a031b030207030807032703121d07030305071b15020d051e030a14010801 63
    0xf810003034068098401d0800e41c0c0012903505991441e200c0740c03c2590000c0da07107048480000450000702010845d400340383c1c5000b440405803280050b103c0b100c01800c5a00100090092210a000c1440410140040c0c000d28507801651a0b64481400002c1c0e0301c0c00f000c1c4071615901c00b20000010908910030420240200e00c1508411003400b081c1907105d041c0e80c003003040940c222141040da001c06942d180d00b003500b000483d0040c1e44260035951480f03402c40e40102603001c003081d00c42d5051004403265010601e1007000c98030b411800c04103540d41c002d18209000d4240030400d500d890700c1c990702c80d000c800b0361b0000d075042160b10b030030300b554a1130b028141e00ba40061031000e03949010000ca40d040007081d100d00d942c580c520f02500989045035001d40d015000a01c05942401505440ca200742c4500e600c11400341c26441460502c0964907003000b450319030800c8089042010a00003001c81c088580c268401c0d00040003029a220782d5070810910040c001d2885202c2c0e803801c848000507145406500c218030009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 641004838 1250 641003588 641003609
    0x50d08040e16110c1e0d021e15040e1603180b0103020123030705181206041e050304120812070f110303060d032a11041a1e0406080601030b01 62
    0x1465400441c0e21120065003441c0c01407507100070171501004500c0e9024440e480240002505030194011a0750b5a144480a0349401516070b02560b05241c82070040003805200d08142d0b241c1420150700d890000303030140010742c2044242040d0070000f4007a801c80820164094071640c034040703981c20069034080c803e2000381c0c046021000c55035150071000021140300100b804610b499038480d0813086a1700c3d4860303d11880746080d0803010006545e100c0c0303900310312210001c009140f40d0a040c2058012518065041d00c00202d0365a85071001030004015203084400620b140082d40e0319608200743d0390f1041d1070380240c0007144c00040104081d08021422001000b41d41c80301c5004640d000d1007560f0384001e85006600035001002c10000a1045500e0385d44500e60b240e282840f0401030301d0800d02c80400480450349596400000701c018180b03407041700e50382c00d040d080f0300001c3c080010229440e41e465980d944c502c145030510070f0007180c40d1600600001d000c0c0d02c044561a607034a040c00c1c90184800e014210303104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 641006088 1250 641004838 641004857
    0x90e0105010305100e102c070c0c03020405061203070308070e01030207030c0b04060e0703050708190f02010e01032003040611030c030106050706090f0b090105061504050d08040e16 79
    0xa521a1140500c00c111307810741c079614079007081c1c01000700000051020044440d5980f001c0b41c400598a01c0c0302c82950100341c0c82c8181d410041c0f100000f0070004190b03408002c80c0754000b1001c940740707844044c11250141c074005410380f42c500105483c54140f00c840082d41c0700c0001c1c02c4007010f034040b21440c031808a50b550140300d6203000004606030f00c15140d000c3c0004081aa000010683d5a8603040d0028451100081d01c54408103415040c1926640140d4858210081c1040000700c240452654086401020204100c9507a500c807507841051038060304001d0300034014a0b09074001c2d4800708400b03680d600300e115010780d1000c04031410740c0110b5007214014208640c94564034a0350090b00e014180380090306003180c0c20100115140e401910055a0054640040c6004190716003541012140240305840e150720300303100710301d080d030310040c00036801031440c0301600d00c26203084000c2d50151641166a9441c0b00128244822980600d40020004850710010701c2410780000308100360888480d1902c4541 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 641007194 1106 641006088 641006099
    0x14060c070f03051203061c05010b0301051f0e0106020616050f1204140d020d14190207030c09020405060703030b0105070b1503010e0703020d121b03090e01 68
    0xe9808001c1e0500c03d2100c140038104c000400041c6403443e50500001260780c500c103d016000001c6100b481500402038203405c00444200700500030b200342d082c00ea415800311810800c0989a0000c0030100042010b44500c01504035089174000d015550365141c1488242030b580003040e0b080100400418601200f031801a01d1040c000c04a580300c6440c0501e071101e1121a0303074521810715848980040c5040741c1c0040c00002d003440510300590500d0f0240c810000340c1c055041e907004c03001e00d48161045440d9000501c002141e000300c0b50818240e0350303000440128840c6000d000d40104040028002082c004d0708400448241894407170300d401030f0b41d228110600c50580c1c11300341a522640a070025860309001c0d182d41c54440c60040c0c44100d16603800200a0034171010010a04050000d91100250180d2446902c04181c207000b050401d5040c5001071090109016584152001e907001042 = true := by decide +kernel

theorem cover : BRFrame.Cov 640827338 641007194 := by
  have h0 := BRFrame.cov_init 640827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 640827338 ≤ n) (h2 : n < 641007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
