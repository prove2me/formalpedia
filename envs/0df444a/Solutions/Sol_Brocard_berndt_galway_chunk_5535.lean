-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5535
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:10:40.972133+00:00
-- url     : https://prove2.me/submissions/c44599d0-87b0-4864-bf89-8f871b34e2e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 995323741 ≤ n < 995503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 995324991 1250 995323741 995323753
    0x61e0f140a0c09030b181207021f090b120a14101802040f090209010e0910060c02030f010e0f0601150509010c11130906110c0d050708040810020307020f 67
    0x180030030304a0080d0030648403990301d12030482460301c00c0d61503601841e04180c404880d4102100201e00e41e002e50034401d003107030041000d0000c09403e20070448410940040020240607100006402100312840c1c0302000d000c050700001407106800d00c0600104130400c10107040710700d080c00d1000d0540746102c201c089803900201c100850441e2211b40401070b1250030501c9a090032050003214000e12881d003040c0101d8880c40000900052290000c041c440000c2c2d03a401c0d400c0f40028140041d15000752165404080024004d0004c91310520301081140d000908403450526600c41c0c0c84e085495481e010700031900a5501446170385800c1145500404240e400e020512548000c0182316006038600c16041058410f000000d10110002c0800c0c800c500600310441c082403114200014103040340b00f240c500b420f14150240b030803800b0041c0d940c3c40040c0c0340034103c4401e440074121072a5204180c00c0f01c1120040c00045900c0d0000c00803a01c508881c103600607500c0c10a060041c1c500040c6011403413165000d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 995326241 1250 995324991 995325011
    0x40b100c15060e0a091b0311061602090f010503070602030403170306010e0406080d030c0c0c1203111005040b180c10092d08160608070c061e0f 63
    0x12030804003696402507841c450154a011880000d00080d0b0f0021a040ca2a070080c4422849554040c10216108290000204400401c2c01e031565001d0700c0090580d82012130b5a039100d0a2000041c0310f07a046107100c10114207400da002030000c07501961010001200040107229078201086600050921030005509140c41d554401842005142106803284004004030308241d003d42d00e035580f60b1a001300b00380419500e40d2200b6503141982c001d0040040d003040b040c140c89500490b03004804980042c0201c40013800d01440860b65005203108030100a01004100702e580824413001051501894003c01c0a040c242000d100c22107002c0c10300d2818416004400201000c00076021a24050a44801d802e2640ea00000e032140c002c1c1e54000c0c648050160341481d8070030205241c3c940d4458444030380e0b460183d00e9503074141d0b90748503070079004008408403901480002e0280b039050740c1c8000c06151480a81c1c02680c2e4480a40f400450410700e0001c01c1c4c00c1030040c811080c000c05550882440c030403c214180 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 995327491 1250 995326241 995326247
    0x301050601020f030a0c021c050a050c0a060912020a0f0906150509060306150f040609210308010306090602090406030809041b020a08130305061f0905010509010311120f0309040b10 79
    0x240e0313179002060002c0301034050110749522014540d8040d25072440180307442e007030902648030441c002d421140b03802070780c4440c090741c504500c0325000d0300c10554840c500d190401e1a4050b50350390200f001d030703407040b201d00c800100881441c82d26005400443d0b000300340035103004000c1c1d1011f241c0c40041800d12800313000c54034158a8203010342c0d0b449001103c5a86141c00c5404d446a003d1140c0c045940d662100000c002c10041d401c04502c0081303400154034030305c0080142500c1182c0f011801d0b4000e000039060300040001c181150421850f050240350014546041600014111803142d401110009030200701021903140510030a00710840440c0030004a0084000080d2510a0210700808407403000c500780403000e0340c030078405000d141d0000860381d140c1480c819501c591b8900352111000c0040f45032012503604c0312400703094100c3e5809040307950964255a944010071590004082e00b14044c04c10200420302e007007240b80254039810014594078025141400141c1f03100400d882d01a14500003402d407402d40c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 995328741 1250 995327491 995327497
    0x414060304020f060a0e060d060512070807030b0c04084911190f05070f060e0f0f0d060b041802151b12031008060f040809031006090b0301050601020f03 67
    0x6800c54a41740e0790b001d103600c141c40740104451455007049006c10895050285940034201380e44c0105c62014410072540e4005a4455082c081d900c00b541040d07400f000000c000720000f54000c040e2100310b40c1484d4403809910301d40380e544030b031403494802d64441240c541c6044d102c404820110302811411143c429401c5a11307161844002d440030004504c94200b4011024000441d80d510059102c1c07009a066041c100d4444c0441503080d0740d503004085001418001c0180c0c84c204941d001c1e250040c04c270f440d280c1000541c45501030a81d40001c0e0410130050550b646850f0040c90b04c0c4107070000582454640f05001c1229004110b04440a0001402001580e40c0d020180b404d03000480469980351507c0a0690403508541e8286801e0720035001580d4203444000c014502c19100d0411a0509580e282d442580c0d42005503a41c540d038200c04004507010400b14170050851711006030440310700701180c880c0602240c119074401c0c1481031756400f40482500d020b000395a040f030402d10041165a200760b5941e51284 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 995329991 1250 995328741 995328769
    0x30703200c1b0310090f060b1929070302010507020c06120c0706020f19030507090509070c0201050c031201140603100b07020d0b0a05250c14070812041406030402 71
    0x58a141201a01981d08100444540c90304c0d507418041550030745070208904018000458a1034205080c0410303d0a012048652111600700480c02c410303c1c180e03a64903060340e4800403001c00ca1000c0210000c00c0300c0800105040c078407035400000c0754540101c00900300720045001a120f08410012185041c40405005070481c0d1160300b813681c0c440c01c41c40d1150080c8181c4810aa111101091109442039940c1c507186441d851920140718580c1c680e202210b08803418081c0ca94045d4040c0d0204031024850002e00305914410b0621605e05a803511006246811a4080030703c900c0321040180301440c404c80c0107028200c2d00b130f200309046090070300c80c801c400400ca0082040c10000491003c05542d102c2103c08400f030f8101080c40780314103001c1002d0300942021a508040001d401414801452550006d030402240f290307142040c12005617585103a001c141c4040b07104600c100706020a0311030061142c40c5000c1800001075650b01d16001c40d641c1c0302c242080307406105100a0080002680714501e50107155 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 995331241 1250 995329991 995330023
    0x60f12080c070503121806040b0d09240b0114040e13051f021810140a050c0601060906080f0c16020d05060f090c040506101112030703200c 61
    0x80d8100d0148900e08031056103c0c9500d03104100c414040c00074118000d18149010b039510300c5aa4030104240019440b07584100d1100031070400c2484070809050307001d040414800e0440c4010341000d40d220412800b0740390303200c0c001c599a03201c00c0007036503030000c200d0415031805070400d5082030300d40321804410f540700829116138102c07414580030420100340686540e4090701040551000d181400f200004d40001507040400010124081094640f14000c400b1285003580c501c6840010b4207202100c81d0441d8000c202800400e0109a15030320707040c481c0c103000e07080039035500501a1070404000d082550284c01e4200c44560f0f0014000c41340d5009045410070326041641580d40e200c2407020450710414a81c1c050550f005100611841002002d4010302075541401211408001002004126007042d140c41da4424204a0702e800c04074010290304240340451402e842e101038200000210580c4102d400600190b5034540650f4070300320310809103005460101109050980302c0401582d80c82028554400c9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 995332491 1250 995331241 995331247
    0xf0e010504210c1b0608010909121b02030303131a07090b1b03030a0903120b010503130c0f03110a38040801020c070302151201140102030909071101060f1208 69
    0x1514021403c10801c10392000d8501035040c1079482082c00c203801350244a0000f4040000002c4d0782c200d038055040015002503c007600840340d0703003003620700206030701709814101d40c150880000341c0c3c0c06201171072107500c046100c0d8510201a14201c20350001400c18904402415401c0c440030503440700d20300d801c1c0e50010024681cdc4690f00300d00e2a00b80300c0c6210600707143c1d00c40041082407a040e42c0e04103c3c0500d11076100c4842503061001610700b910111240d1a001600a100003080c4001d02c0580c2d4880d540588019001c498440c50041c41411254205882e010340d000303180c01c1a420400e1400004152174034905c0442d0240d0701140c040703512900c6085200d00c000000e0245803c44910840e0010404031008558400d0350307200311034456011703100582c4503038034054240c6069408a805c07503025000c100201c0e6056801c10050643e0074080d050b2050451009010f55600c3d03440c4e03000c00502070300c0c1c0c6454401480030300c040782509403a1107810810565002d1034040000c840d40809007a001d0713501c5803c86071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 995333741 1250 995332491 995332553
    0x7030b06011806030e06090d0e01050304060e030307020a14121603030e1605032505060a0c08070f060b0a030846140901020c040c0c0c090f0e010504 65
    0x800b00210070300d08110010220300003450b80d8040d07200e042e44c4007440c0250b9103607a803003500e00f03138032155001003000c040b8242843c5503031690310a4000790b60091281400055018412940328a150005c0b0340381c4003d82e0080780c010382400344000c80409032082034801840c11403044900c40d8524010074030030010200280030400c040500940088582c5ca0300d01c1e0413601c0300039004808441900882c400c550180c003501c2100d100000e491168080c1c0040d8840b040035039107203458107000559021452400401030350160180016401c9001040b01d00c0c0546201081108913042130011241c9240e40d6510400300b20004000003000300c03040d10041c051070344000c2d051301015a00401c40d07405449a48031385030301000c52215582800f1030a84203401e200d80d54000455a904608140780c8140109280560700c8041c1d1000d4624141e004071001580d1860f0922051210796103c1e503402e8001d0304807207031071a01c0348d66503e90280d052181c0c4d484d0020340c100038061400c4c10b44131078820142c0385544011010340801e08807 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 995334991 1250 995333741 995333747
    0x13903050c0909040302070927020f010c080c0705010f02010e0c041503050703050303041e0b040f0804051e09090c0108041b1509051008071706040f15050a0608040507030b0601 77
    0x100100300c00b0384883c1c3e103481e051030001d480351924000c9144162410403c04011514481d1148104200c43c00d2150044880d40800c123030a445412403904118002400200054002018200c254400c1004014460902c8009020380b01d4200181e4210ba241c10440c088080000403801c25503031050702c2c0002e06100031035601d00010030a41018103144542200041007240000040d0f1066000e00700b10179030b000283c4200300c3c400f0f480c08009441a200f01e8040b50203d51910880b0400700d2081401031b180c19518004070303000b966408400b0320541c03081c100900b910b05005410070b03840040080135050b0b8100700030001e0910300d405040a03100804800b0303450301c0c6100864000b0b000d07100c0900d020582060b240c000508449081c00b400380107015500315a00301c2400341362002d0048a8580302e034020800c0c0d40d9030b103010480c0e005041540c4242c03108450400300890303201c1c990396100110045902c0c14100010f026060235103a00080070014140e0400009c00c20200742c90080d254060718541042e19135100403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 995336241 1250 995334991 995334997
    0xf060c050613020316080a20060a031a100206040606140a0618050a031b060807050313050a020a3c05093106140c1813050108013903050c 60
    0x301003280030100101c0c040b06e0004254922911442c548002040c041100e0411001060301d0290401342c18010030a10341e009800110901c0c0f1013030b10010004130888001211142800d1310100581c01200a00c414041c103802840058022569100300e01e181c0440071408100103442120100401001841c1003482c00c41d030440001c000040409150f1901c9003040e48150350780c038188403034051401c0800141e90317001d80700f0588038210944503942941e80b24041500320003c400303022949070040d03203041c1c40160765002422001e0301800c0281001021074030348009408180031001c05015004144650202007242c240b807055480a8841103803a80b5a1115119180d5065103216070160780d862034201702e514000300100d40c2c00c1c002e0800348008103070018941205036054811090880080100c0c11000040100c0d21902d00da000d80300340e0084a000d80745600b190420b821004081c0d440b1420351541031002c51f001c803a14062042d101d14042031184041404001d25030f041c20926032102c00056a80541c4026 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 995337491 1250 995336241 995336263
    0x9070905010e0105162a0f05030d0302030a0b120f161a1b0a030e04110306010827031309060501020610091d0a030807030c0c0f060506190306060f060c0506130203 71
    0x803e11040507840d4046c0e07850303041040c00022103218000d00003200c50b4442c40075421104090058441c10018810841c0a50300003412080059154030b9840001d40b01d4442611134400c001001d4080384601c1c09005040080c0c43c0840c0d0307255500c0c50024803401403002c0100d4041411290015070314052031900310200ca81c10540113040e0300802030300c0418950840724941070100c08903010840b0340d0105800c00007900041e5959400502604d0005038200e144902c1007203114840f41c030208403030344103801140c074541c8500d031003089181e0380800400001d01903000b0b54002d80402d0014040030328043d4070401190000340b2891602944442035180e151040c400c2c141107000c000c2040e203420344400d050241c0800b1090314410b000a2610b450004000d20500c8c491100c00d0b4841c100c07460004040d100c3c50050800940090f90003040641101140d0120f0040200194403034071000c6071440c9000262208050151701101c180503140d900140015800310b91a6845588102c44c0072900403a070010900e41041411 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 995338741 1250 995337491 995337503
    0x31b120a030215010f0e131e0602090405010e042a031218061d0603041506170f241b0f09090903070215160b130209070905010e010516 59
    0x102503003499408a09001c8001000382c42412030703680d5400e19060129140704141c020110b40000c18440c00600715906201805440806800b00070200c4032076501124043c111201513000032504514223040c02218010300240788500a039141540b2103240c50b44090306110980408038582441461700c0f42ca00a02440d0030420109100b1083c5c48094003140c02c6440b2007400300040d00000400c24800c41c5041548044110394859241c4944184401c0e50400b410440f540c802d03112a0b60001c00d45881258012704210041d242440403184100d410410440145080ca8200b0390550034048180c404181e000c1a0500c7c0511443c0d9612901341c0d02e070790701000120041380d800642945140213000282440c00c40881e2002415141c1a210725600d101c1c4060007508243c0b41550801c45e01280760242c07031800b1003001340042403a00342d0341c0c1c0510f8960440303140e100d210031103542c1829030078051311450f40310b0b40c0e030f050060000d401c141c0003902180d2000500e9041010000746814480d21421038510792580c064 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 995339991 1250 995338741 995338753
    0x901050f28030602090f0f030712030e060d060f060e06090918010f0515061e03180f0a03030605010305190b060c03070609020f010c03051606090203061303091202031b12 74
    0x40f821034041c5d40000c2410b031141440d52584022813400303641e86048039800030b00601e81d00349070440800c06543c0c141001e80502128005c100d000f17071140002004c10301c0560800044483c102000c9041406003600030408200c605005042c1e10784501d800c40e00000301c21104406255211211040204051003411b10b640d400d1107005401c1035881d0700058020102071070240700940a0000f405118092041e0302c07200001240b290000414030140119045081800b1034030100d40a20f8101e494051040300410042d0302401148003030507031510a61020301000d103428480b605000700400d401142c07110007640f20942d2101800025681c076000c48410000c9072003925169581400e14000428012000b03034064103c9460741030301507125424258010741d041d00ca035400d1140d40366424000c01001c83c4106d800781d580d0704e001d80269a00b000203d104041002c0c031601c8100c40f501c0c000f880724109a112980701000c440c1340c100181d0f03021504a00504032031a00390300c4840c40d031001440c110701c041290036041c0110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 995341241 1250 995339991 995339993
    0x304240f090c0501020c060f0c010b150c0105060d080724091a0114180405070b0409020310151205060609090f090d050405010807050703020f0316020102010b0901050f2803 75
    0x203411141d0402e004805030a0030580e10300040e070703d60034418150b5520042c2000184120520740c0003600702340c06101c000041004145000c90400442c05110071a1034001145885440009000d032690024003642c50540480366540c1d02e25a84c0a100030082800e400600890601c041e0182005070345101c40d8000d019400c414200f242c902d03945000c0c0440001e62640000c500346000504032464208040c02c2d0382c0038130100c460001c1c11004043d200301c0780390140400002da0202890041c0015084039900140d507420400b2111a2038042030340481c0c0841c0c0d00c200300b150790513000705080f035200c2910780020545a5501d0005841849001070150380b200c1c600c02405038103c100c41003a0b100305122000c275840c240368035100f52268000c070300c502c0b40012500b000290807940720b04040c0c10410702c40d0048132002d4a451241c00c0c00d42c2c11800015542d0039042c0703400019507038240540c0034240700079a030161076541002c01003241d1985407211035000b00c1c0f04191007585085017010529071810010300c02c4242c1a00e03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 995342491 1250 995341241 995341271
    0x42301090f060e0c040b0a030615050a17160e0f120d080109060e010b0901121d0d03020720120601060201050a0e01151418011d011703030424 62
    0x702200041e5034601400816a80206800b541c00790002c002d40d41d00302444c000c80050f45034858280242090b88078080000d2003140800303c660240c009450b0f9a80f980ba201d000200094039003030460b540c54002c2000d20a22001c503c080c03060007495131800003500c0401e140400c02c014141003103103401c51001210003000140228101422001c582e6440002d43d036605050b4068039000d014220b05101120010080e04110500808800070103040146e544a40b4450b40340842c0d91b8007401a41c4103610680b1a11480c1c03042c4101c40040600741030842c10a00c8035141e0003000095046030380120741050845010a94a4540c80b54001103014200c0b201503840f1400280a4181600c1840040d81000d500004094040c00780b00f2810030101c04a650700f0345425801008940304035203154105091000342d4000f280300014982c00790a0580510785038048d4891007100c10b1074164041b070842044c0c10307400320b0115804022039812030b4020040c0c4d42e041c895a04040300341c245848904551515005c04a000101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 995343741 1250 995342491 995342501
    0x4030f061803170601030605090f330f06040f090e010b0d110d0809100306080c01050304020307030807080d050711010e06101a0f0c150601030c0e04230109 68
    0x220428003807125030106403548101c40000d04004000c5030080106070768480c89080c0142c0e002105140201d400d81c0d4500114007280710540c0d0100c03020301203c04002404800040d10a800c4c0c41501c40c1c0b8a5100e0500850100491450701c1148110186005001c09a88a1098030040c1031120701c10203130356580d034403100002e00004030403141c0340d401d000b1801300500d0312540140c90305d0f41003084941c991a00c00c00300117900051020494844104dc01203140c0c0c1d40b240d082d142c000d90712548000481d00c0c1401e00d5649400c520f4110181003040410800c801a03d010845004aa41c4111441d4544004d0710342021640244241002d40e41d20305802c10206591100c00074005910b003c008007d032096583c1c0141d21580c01311200444152020400c2000780051050b0416030241c480a0780d00741402e1143c5a0300c40d0b03018040e030440643c002040010202c03420181e55800078824202003004000000c0058400c080140312a44541c1e17640788214510528580c403030050790600c4485489568548442c0c900030a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 995344991 1250 995343741 995343743
    0x100507020d0801061704030305060111010c0f020601050f0d080d020c010218130501080c010f02030409050412170402010c2a0810110c1207030933021c0807030902030304030f 76
    0x3858a200001d0784c1c0e4010044414000f416a00003040750b541c54500390090203003e0031003810014040084500c88400f8410540070708043d0b540c11400d0b45028100a2070701a041e0040d51180d4585000f905090340c580c0075400d41e080d80706560580320580c009002000340a107007200601c950000550f2904180881d425201c01c000854640071a80d8402444408940c0c09000f8680154414110784a081d030160002409400d070b5481240d191948400400080d03420503070741182c00840c0d0b5101151100e41007154084242040301e00c8000b5403429070002032580c5e9100e540a0007100500500c8e03115800c000c00d400488000120390054901e5442c2c06255a50f00301d0080000d50502e016100c100200104e0102c0300441c204000500003621102c20304046507000741c008400b4844210b00020349112591448217443d00540300c840ca104441e990008504140e400d1000d0854018500ba204068010f241c204103803000381c0340000e259600c00c082980204882407010358984004038000080000b01c039012140c00b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 995346241 1250 995344991 995344997
    0xe090106030c120b040204111c0204090501151b0201030605031b09090a1109060303070507141306180b210f150c121906090c110c011202070203100507020d 68
    0xc1e43c0d4a401ea802100d2403502c0042a0011002c007003009071030b044e00300d012150f0788004401c0c41c3c030340c60895405940c42032406206009401003020000b010b00c5119003401025480c2626001031401940108201203000c01e41d00036141d081c503901d0a6911a5100e2005408081c04840d517460b1604174026014880c040000d2142103030354001807011078003246403800d5540c8a91280903566640c0108851800700a06441e010b210501c20303400811000c02444004000a0414814200040301404090b424420385030700d115081100030170000d001c0030324000d03120f480c102c40040d040b08814000b41c0c094820004007500b146100480e00ea03080e101003141841402e900080390f440c108202d03040040820100d400000d040c409200750303041ca034001c10100381e01c858042226240351040c40913907400c1b00c110342c002c420701540c2c90525079032b280e81010b08044140c0b00e10000303040d843d4620300000d150205110710ba50603075402103500001c646081156000d494644c1c10140a2481c00c400000c1d035507612001c0c10000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 995347491 1250 995346241 995346263
    0xb130c082104050a050135041b0e06040e010b150901080105040e0a020d0c150c05011a1c0201030e03030a140703110a03090f02031606110f071a040e09010603 69
    0x1580c407880444044840250180260500c0d1400654004c0c035550074400707020140f130004174004101d8a180360307843e51040508489a01b030034102391109040d2076010741d0b810300c4002800e1017202826107040d51300510440340410320306800429203000d8240744021030f81010b8541ea282c481e40010340f0203004d501e4002c1e40c8520290382e031002000141d035126032820105070481c101d1217016041c041203608249000d088088101035441a4003d40c08204200401c000380c03594120380100882802030820300c60070400d8030015000d24100140044080d00001240c4100000c04442164003a400c004031030000001034070707240d10304030900c0000790246282c242c03040d6040800040340c03240a40306615082624452250400020200590040450080590311165203401d04401641e041208040d50040890f07102035542c94040041c10341460159140d0041e0400c1240a20400001808208962030098988500f83c09014034141910030b90300f01c5100307190750004000c106401500010112481000a022 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 995348741 1250 995347491 995347543
    0x30b0102010207201909020901080601171915260708100218121506040b03061605300a0504020603060d241401210b130c08 54
    0x308070301c07038000000e00800890319044201090220740a031100c0c400341400b4800d0305442451485c07529168410a16141c000844d14029680007180a801000c2820011000707200354110b1404450700400c5401e40070004c2006410282040e0400608071089a480166a6880782e020071311040301c0420805120542850a070480760f4000340e103400721040740000d0260b200c00c0c0060310019510510824007044440300844031241d4605021540440c2440000d251848005104c8110070030001c00c8284a10700c0c10b142000d0984000c43c480341c0c40344c1e103540e40b80c26144035050143c1d030600601c26a050608015075810000c486003180c5074003100c4000c0d44001c500c3c1c2d11080380c007060318011100250460020300c0440d02c2030410180e140401ca100780c0b0b09075000041031031400980804442d00345800c80d1900070300410f1440f0480154054400707800800b02800000c0180d48196441d49001081081040002020f0620802c0e4030000f096110100708a025a5001c0c2165211600094144000d201e048500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 995349991 1250 995348741 995348743
    0xe040f151a0f03070503100b1204060608120901030b040225050f030f071b1a0d110a080601050c0a02090c1c0501060e040e071721130e07050c01060605040501030b0102 73
    0x1d50002c508007559803543e5216441160160009010032083e105a084040f4401c4008409004c850b08624001d0358a4a0141000400c0d92030360780c8112a1500303e142280040640c2400310b41480d042824041001c1c03201c500414001e1084140300b050805a80c00c20003100b541992245200502906c21143c41d8580002c0650312442a1004900c0c90303070781000742100158500034140ca000d0040d00c0200d407165070b00c141c0409800040c4021b400041c500103881104140e4500c215081502030780200c7e03082c840700d41009494180043c2645040c03210100308148207410411015181950141c0308401c1e80c10030040031981604201c904940d000c41e038040c0c014490b0464401c0c03904a807503507620440780102003800d20006100701780c0200b17070758095903401181c18083d4050244041c03008500500e485451410341c001401c00a4221a402c410204008055005100700030000d0360110646032225403a20501660b0b14420300010b030a0550074582d00061150b0000f0140085a000fa00d0510181c29424012 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 995351241 1250 995349991 995349997
    0x9010915050105014109030f07050f090c0d060605090f100c0b0702030d0207081201050a060c1b270e030403050604060b0301060b1c0b0f0d02010e040f151a 68
    0x3c0750018001010103000c1c228a1503d903501140c460880c2c0c00d00707518003c5c1c00440b402d0050030150000c0c0002441043d241000c0081c0e414800000e00035040c00350131b14000031041c42054440f244100845800310b00000c42c5801103403040c1002800801005940d41c1c00500150810313010103200d004480060300e17050602494070340b0110702a90740d450342049255640aa4610050928411840240610080e00095100400e61309002e520318507106c8a00d2080f144542205800850081003000000c0105a8100d03c8165845a0201c0081d501c2000c0046d8a128642d49521a00d80406034440300d1941d0318004094802c0e071007090906100021250341d8070385d40c074400c83c40005d00b103900074000200400c0e0f081d44030710303030000000740049142a524107000290340c0103450035119010804841c840c01d284d5a115400000f9020745803034065100080028000d42d418800290600840f80e032003c1e4550f032150700515034610402c0d010400008003442c81d00049a0501a10044130242e10589070103940780016 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 995352491 1250 995351241 995351249
    0xd051f0e0a090804050301090c030b07020f030703140d021204060e010e0c131103010807140d0c0b030604060b1303020a0902070c120302211c090c0b0a0e09090109150501 74
    0x2040c00d41c0e1580c0009070300814000c1410f4940c04003d0201003856a02805100740050040c2582c01030705055041050800c44050032280666101e89140c50101d4404000d9035021501404c10088605211703a01030614030400058038507161000440c110744d0400680c0e041e00441c015002004844c00101550342242c21802d40e00c1c84991007000141c2c002c0c41c00d08040e03112048030645c0032510040a82100c04d0a400030381042c130094003d0301c414402801d030034661840c4440202d40000340040c031925200c0304002940961550620000002f403e5505c440d00170394010021042c3d2560359a0710700c03401b851040058082244520250a40001e940d1114020748503c0e070307048401000e1480c5030000c2c4013410004041c003102036008003440c82100841c0141c01500c1c418002c0c2400341e450400c40b4040308500c840e40b50141010385000e80e8000401d00031009402600c94242400343c0da81d00c42e050940340d48849040141c1c1c4600c60078100b180811064014440c900d200c0c08c3ca103000081c42c80e200300e082c0d1b0000d002d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 995353741 1250 995352491 995352509
    0x4080f060907170c0607140d08010b040612021201090c0f0e1503060d08120114120a12030f0e0102090301060e0f0610120c0e010905030102040605120405120d051f 71
    0xc000d2200280b034042c1c8040201e946411613020790050004100281c00c500e034140c2d420b40d4601444181c0610a001a400c1c0009501c0c000c000c031740c1440307581c03081e034001c81c02100104806101d20340340701026581201c0c0d1a94510801518640e9102124406014440001000603122a007601106401106a4612540b0090002010f0401c520700840c50750030090400ea8040032144403d03000c500200001c0550620401c54083e040d0305003092002e140401003101e038060420820100c448040204030092040e0b8801c0c015a00c0d080d4a032004c0f405801d50758480c42840e0310b009801601114158000d118180d420340090142d99a43c0d004c40c080c20508803a100c80e0005248002003e516146040080008803420514159045d240000044910213152080403990503c60000c0c59a04035410100401040b002540307002d04002e00140103000381014502d469241c4008503082040601000d012100c0020b0080e803614801152800645410340c1e600700070f0722a0908113400351040183c00f20a8458100b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 995354991 1250 995353741 995353753
    0x6100602010614130603170c0d0903050a06050a11040618090b010210090503160515010812090114070812070806011d01050a0c1b060e4c0504080f0609 66
    0x2424810750742d0303c14104500c2c1c01c5d500c0c0e1021000896100e5140c00c4201c0c200072150b110542101c002e490100120394450038030400c10340406c0051000120041e500f5407000d40800e00392a02001c01000e03124807400c110007401d0101d408100d05502c449508010b80c1001004010250f031484214101e80089903040d00603005503568116000c0d154000e5541e4500c601c080302d182c08000021641e094100110458940c0c05c02002c00c50440c6000c3c0702d140c05014107c0150a000b42c0d40d808807006803007100c070a603041c0951a488140350301032400c191a041c0f5045a05d50341d41d9800c021003001d200d803040315003402040c403040200d00340d03510030121000c00b01103202c843d64028644034011750b91900180f24010410170754502000000e0440026441c1c035100c41180154600c1c10450701501280d40c5560090155030420941c90388000b102290201003540f5810304031080301c0110a282a1101d0002c2d0764403800c10103880c200320b03250300200070003c9070424400c0e142844075420f141505c8941c1036500d07504a80c041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 995356241 1250 995354991 995355029
    0x60304030c151107060b0901180914060a02030912030403360602012f0f030601181203080601110d050c0a052a060a140306060c010905061006020106 65
    0x107026846006020780140507030032008001c4001a40c1840720320311001c101c04a510ba0070840c2502030315401c03200031103c0d5809981080040108280550743d8480e58a8441040d0000d010010304440d0b4100d002c4010764000b882c0148081c00a03500070b80354081c2c03c1c4210790b1041d04503600c84060382d00a9506540322070302011118a01501e50740c1415080b04684183c1c03101c441e04550304840c02c0c00130012a0004030303107200c900241c00391030040081c807104041e14203c0c075603030101c80100448811511030014142c0740d4640e0301c0100e8103460101c4002c51426280040403078234042c548458003030144261359440d800da440e580110b500c03a02c009404905a407003140401e00c000d003d0b00143c0a41c9003454120b0342003032400d440d401d02d01542c2880c05000142d00c4141c000c58090030201c2d14415003800d076042480c00c1405140100800b400030380d2250030b0302d404000300310f8540c0c60300101c803080e0714510001d03c04001142080340e150b0100303a40c2d00c1d46d50305c43c0c0130b0005115030060040b4804c549412000c100c003c40c031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 995357491 1250 995356241 995356247
    0x4091d0d0e0904032f0c03160905131e020f01050f12042f090105040e1005060607230f0c0f0613090c120b01020a0c062007091e0501030206030403 64
    0x1000d48124240101462040107405d00b20030f10103522100c0c80c2103034101c44429200c0300c2c00c0110a038409030090308414080c0d03c032071074144528011580709250004940d91110380300400b0015890000300803240b0054140d002466003643c100a050088501d0259103d81c02c00564891085000307032100c1070303c10700882d00e41032114640c89034018014403002c0903054800b44a83d044c0101e00c07090526003200c0d04007829a42c1000080355014000903501000b5815154064550b612020b00b0701036102505e03000068510f07103c8400703680398503078000c0840480041032002c032111010f447c080350b09180729840270300300e010034001803841c81038501034018401205614144034440e401800170f00d98040039071000250a5005100c1e42203007c101d590b82c0030341d84804e2079640050390f0101600c0f03030440d07110400450214480404e400c00f1030b00d207400c1c801941100f000b412262a440781c000380d400e40c00349440019080030a508034152070410310300b0610340225001600c9080710828000690004818400600041c0c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 995358741 1250 995357491 995357509
    0x90504020d0b1306050901020d110702010917011812181802220e0105030f2d010902152d18061b0a021002010203090d2304091d0d0e 58
    0x2d04a5030050f654201529a43d06481d000d440582072a03600150794048070740988500b22202c0040e2114602c0c04409400003061000b0070f0084020280003240d4101d42804254011501901c600c0780340f10501c840c50621030142c00c005485440414001c1146098058203484200309603402d0640c0003218041d130381441d10080d040301e40e92145d28243c59010068441460b00280000c0030300c03070701010b110b41c144014141401a911200003441c0c0c0318140b0902d50901c82c0c1d90354070034107465140506898030031f042000d014040c0c01100bc0c0d00614440c40c120340012010008000c0a1131010407071540300ea036061009400c243c81480b03e620110140011840702100b901601c1003c030b40205010b0800101400c80070108011000100c1329600548824046040c400702c060352580c0305000860441c584004081e0f240c11007070740400c003000b00c1c00703002c0414100010340800324002031580664076140c1b00e00d00407005042c01903400319200300812214a1010b00081c2c1030001d414140e8402d0300204c3d2420512070212 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 995359991 1250 995358741 995358751
    0x81c032711010e06071e031b030206071814040c0507140d03050c091e130609050405010b03010902010c06020f040b1204020a050a0602071e150c0c090504020d0b 70
    0x8058244400c0c90500c9900460301400781540312103009014002414a1402c40da600380100402e00011022441c0a003d80c04080c40000d0a410584071510781160061401d00465010420586006042c5940000c0451140d03e0544074a84600880420301001c88458802e252000f03001902d044942d007481c2d048440d6040680c2800d50512420f65a02480060240103025465200d0600c0240d210b03850700504e500800403e1245180c25900c8000c2600b40b03403031031070a12040501401e0036a43d9200e55110030010080d5a00c1001000d07254440400644010385043d2000d600300700b9201d405140611a0081e0582c0c1612200454165580c610012f0b4102c40001540f0003024040065500503150040c040e40e600e04101e2050b83c0390a00c104143d403013050300000d008404034202403140740c1e0001050700555001c40c01c600c07984150024404803d4007543c02480b44118201c22241d01c0340d0b01300c1405036000b80710307945040e0400d880d0745da03c0e411280101d80c040d5014401d01030b01804111104080d51f084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 995361241 1250 995359991 995360021
    0xe21090402190f2c040e0c040507030c0e04060f12080409181a091e0c1807090b090109060e030a0b07091701050c0d0b0102160807030606081c03 63
    0x9146940800c020307040000010880c03040325510784560000102c80b180d440113071303842c2d42c2200015088001600c0d19003901c0c05290b42d110702c80c121b598104080c502685c801002440170340341801c0020003a00b0300140440104e801c41a6200103490240201c9007070707a601000113454103181c141031403003120000c0c1064591600c1000b0100f0001d015000d00344c0d98a01d041c3c08440000d41a280c005205102030190649580c030319414010b4948003c541080c41504028031551025408001d40d41410018003425038007030100c0c2c0c02c0610210a030011188160019100c210465079103668601c000e00c1120086400160707264420300240d801006040c103000b402030203c4807490030b12b03034030520100400c0e00c111001c107202e003104110041844d1810040c0c103100b0340007402075040660389401e0300e00440046070111130315488402c0c0c0c180d00c03c0048000031038010344078241da035a039003120300d490300228041550780074184a008100c1540010b001c48d11100d40d0b036034558075400c04010803002441274100b002c5d01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 995362491 1250 995361241 995361247
    0x200108060d03030507110a0303200903060f070509060c0d030507020a120807140c0604020a06030204060c080d02070b0103150624030e10020a0207052b0f110904150e21090402 76
    0x81380c0201301fa000e04502c81e440019503210903900344103910390004c00b001c11440040101e20000d0714080b88150300640002030b2111b4903100d241042d55140502440c842d0018004200c085401c000021840c4842a84d13840800464882460490b00c9500d81d5501401104c05070840c20806441a40e0141d0f0196040c9454013400c000d52101c1000c81d4002840d1018950004c024001940b810080074002030645080440c41c1a00d021400303001801071900207001400c01140c90350b1004030036012204402c3c2c1c0a01880c0b038560b16840c00c2e003a9158290040c0c8040d6140103c0424505045c80001c1000d80d40c287c0104840d0041d028100c0141c030b848011403506000310404652140241c0c0040c010340c9140d07070007410314581010180180901d00320000000100500a030007200d08001c0d6910100d5a0801c5051100301040c0c10041c2100c9540990b050b00118610100000e100c0c1c941240c00340d00c1080107042c084d02c032242c0026a039400305000d00b400540742e50380100a400d45d2075401026266405030002d82 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 995363741 1250 995362491 995362517
    0x3022b0f02030108061b0324060705060903070309080706080c032a0d051605090105070305090d060504050c030c13090f0f03090609060c05100b060d09200108060d03030507 75
    0x40c0c2e0400e034412803466002d40c050003403030311203510000385410054081d075046207010103000c00440c3c1900e02c110003508106602c1c0c80d2640302d401c210344102e40c100007200c0a604041a40c25135a9001d54420350000745002c002264458010403003c084030265525007000703850300404050302e68805002802e2640950f2801004106d203007055010621941c048542c03107940349250398055420042c81c41e07a0700b02d828014130450b01c0d000019120744103020728080342c60300e20303d00d41626076200c0d0281e001e81c0650700050f5041082040e411003840340d4410025034400910201c02e2507940e50a030010994004040d00b100d2951340d80342e501490b09075000341700d80003401d446510b0384021300e0343e1000107800040748a10180700c0710381c100041c84000d0010b8580070030703201c0c15601e4403a11441ca1486043d807040d100c2c4248000b0b551880d0075a00d48102c0807030200700445030380c50000a4400340310f00c4010603485040c4246007542c00f54104510441b03000c0c0958030950301940e4114010140100058284032986424076 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 995364991 1250 995363741 995363771
    0x80a0303052e05011b232812020d02060411060409020f030a0e1902061b160503070b09090c09010207180902010206150619020c030a03050d060603022b 66
    0x42c044540e044080605802e0030001005100b00140705e5400d001d000c8079a0002403100380c20314070014240802079004040131603c4604064142c0c8601002140745040c0c1c10195170702e001010359007441594240c159406100041c0e84900541e852072025030045800140440d13034440a44a45040081029143c180c4601303108040b40c0001390701130707102c10340031042200281c070703a100d80503502442c030b00181854540140c04070541c5042e03140081c0101c402281c1c090b15021048030300c8811008007410b84800b010406442100e24505c3e108481c03192040da18001503107544d560488900300c0000d01980030656078003004c6105c5074001150306045205007140050032404413078071403c00c001703100740101c1d407851103000091800d1030192000ca0541803100716540700d0350341c02046510a00c440d1181d030460002c4540d0503400e0566010034141c05024040d004004c040e4000c00600c00c60f501030f001088260384543c4c0c00c8003240201c0c414440780203904c1326001e40c018040f241082e0940190031000c40c1e2036040030449 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 995366241 1250 995364991 995365051
    0x1020f0409020909090a0f031101090c0b092107271e0c050405010e100908030307020a0b0a020702180c25050d0c0206031f09020703080108070f080a030305 68
    0x840e0000da40802c3c0c19440f0301d080e10120303400406405c0200400d18094a400c58056000f02d002814030441603200b5680d60801e4010b01000c640285500580780d03651480d00ca00c0b80d002075281072040320801c8080100c5914155483c0301580d05030010300006003000040424040100c2003896000004120000c0343c4400340500790881d4402903c107a001b80e0301c5494001030383c1c84040c044c01480420321040c415039038080081c0000500480f0200748080300000156a083d029401c040121b000000c00c000d03100da000a900d214072442076840000c41d54440450804900074010007c1d4003031b1078542031410701c0904040e05600004400030580c980160301285104416401c00c20384180035050035000300303101d824410404020414185840708808036400a440d27072000900c9030110149041c0c03e00106103c0c80c5d038420240c03c004504564802c0780b800c3c00350a9000903c5139006c20711178454040385141c003407030102040341c074204010440000166019000b43c0401010540c00315651290401c02e0714002001c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 995367491 1250 995366241 995366249
    0x824191511010204050102150a150306050612190f15022a0c2101020d020c0102090f0a080d200a0f060c090e190902061801080a09081b01020f04 63
    0x2411000c01040001410700320000c041d256a50f44103100c10811170760003003829907074940c00401c5508140d0390004040001c0180030034880c000200c220780402040b0a0382e000700d000703200844025000420819649a695466401c0114041925411080042c8003d07403d8103000d44500b4038031403020344c10302000f000c03600300d1621310090318038483c540060320b0401e01c0ca40c2c40700842200641403801d0014081002d00c600301a050006652900d1809955407080d410b460200d038410a06542d41c40d41000218047e401c28030310288500e404140901203031901c00c00020845421402a01038056481c00594558050030350080021004913140c0038020000c3c4203d080d01d0b8400c4001641520290800344100c1d443d44803010203021484105103e5850b01450455102031412268000480708030b80410140001040c02500001c0c04200c034440f118403103000008281d001c3c1d075042000d648014080066070304511028000318001c20103010801c50004010714245168000540f07800799001c101e00c400c0d489544 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 995368741 1250 995367491 995367509
    0x1b2704060221040201030c110c0f0a05180105041103160507020a0302090c0d0b0102121b070e040c080105091209010c02030c10050901030e0f19031103070b0610082419 73
    0x70803c8115038262040001058441c50086c6400c401c002400d0b942d240850165449400c1883d00c0d02e0980e0340d50b4180c1005080c02030030002d4005c000461b4990003960a019442c17042d403c000d0940c040300004015640320303603801c401c1c141a060039080d0903102e0340d01c070782d1060f40c01000702d000c00302c0036031901d24009001d6528804569503c2141301e56050480344011341450440d0009640c0e100c1000d01707a019206400182c00d058440b001502480c030340313405442e41c000f2051504030403c0100303000d0740040c003d08440208000740030a5844d040c1c2d9a4075550050450a6041824070201209502c0380c01c0b8003d0803480a4101c80910940500107a01e180c6000c089800041e400550002a568035005000440341d60100900100410031201500c882c00c1d1108581c07202d41c940d0448091510410b0200b000c281958240daa60b0641810240e08040e030840c2c10601404000c0c01c0480818400c100301e61103401030482d10002c1e540150302c21064028401881540040303012181700c6941c411854003801068158 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 995369991 1250 995368741 995368807
    0x30405011401060e03010b01181e1e031b1a0901050c060a0e1b06030c0a050d06030308070f0e0306071b020927030301060203040e04020109080f1b27040602 68
    0x800305402d6550344c0741c500d2304002058041c200f44d404000041d9040d00c07141c030401c401e00a190110482010002e074024644402e80401d882d01d040c524062000c1502d00840340c99a11120f0b40405c01c04001041c030a01241c0f0f1103001100e018054038070003030800014149001860f042c290100da40c5400000e84103041150340d520760b841c60150003080142c0d04ca107000306540740c00d0152080040c00c2400014864000c2c40d00000b145c1c4100343c4910105c4150480200b800c005864580c01d00501c4864100c451001080c0c0d5400004030481c003846044e2002e0310300074014541560b07051000c80340b0300350124100005188400802e001070b944e48030301c68898404401403240c00030f40021401d5540a5519100c0b5090304100018490164080112001c0d109240d0968989443e00d02c0104d070090916401081c0e203025045540b54031074000300300c081141c1c047c0d500e00b00c41174510000300100f01f042000d0038088015031790111086c1c41502100c40d903100d80240e0005080180c1807007403001c4d00b00c11b9080d0100c100c07814 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 995371241 1250 995369991 995370017
    0x30608060a0b1212070b0a0e030a09060909050c091302090a0306090b181e1608390d110307060207090c18033c02121203070503040501140106 62
    0x10f03014a01d5040e2800004041c0007071112110003252149000c0604070260b180c0c0000c0b1035100c0707500140c4034054000d00b00ca03900d5040b01002081c401e0300b40030309400140f80702e1780016042558041c0c01c1c01814051559031500035400100802c4208041170104019024400e002c803079510750b640c2c00d006500a00e004a000c1c0d1301e0789005c0701c86880062034118213044050400088060001d0030004a5001e281e551628246032050a440c0c158600c1002a420702c4035040030070007001c0414034007200e00f0424a0b009001c404118a88041582080f074807042030458840c51403245801172030b40381d420340107000480841c24440042810104a500000c01592121400700240009841041140c2040f8940340b44600d020a07040c41600703105210260003400150940c0c5550a901e413000051502d210b44803a0000411540038800021900410392081d40840e158036085400483c54954405000f0b503914a10755420030156a1508090302c1940c0566903480e08003c039905404115002e40306e60b48a4190341c01807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 995372491 1250 995371241 995371249
    0x308121f060e0f240706060803070c060e100f031808070827030a0303020a0513081b060f2a010f050a050c090d08030601020c19060323070e01030608060a0b 68
    0x60303080343e40980c0400d140320303030340c103144d60000c040180401d98619981d032800c0c18030b0005006107400c40f090900000868908110740e064800701103e0312600c0e48400c0e48600001c00034000f045107508404130f90741506513082c030f83c0319610000c2c03001c503d0500c140c00f10180d52500040758110351000c030b803210400144442d1500120100506030240308196450300f6150700003185d107802c04100b000b02815004600004a51301800036244120f40d0060300741038565551001660342c1100c00c03c0c0201c0011086211642070605000715000800340d151644e141111103513602406015046400d400941c21083c5c20440780000e006040318081030020100d2582000040c5004841001d00003880c404401c204480341620345400e60b610141c0c01c5040c0c0c6407240d4038400148d05107080301211541c03001600c1d4000315200c0544103401c058402c0f69800b00040c165240d9501e1192448461825209041d14005100c0d0352045861140a40e4185404103010360f94002103803818205440164005031145003410141c10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 995373741 1250 995372491 995372509
    0x3040b0c0f04050f0a03060f06051003020c03180d0803042f0904061a100302070501142e03140f011a150304050703080f0703090e010308121f060e 64
    0x3621684a14100048882200610507446103d0007076410698884040e5145840e940c011034002609204411512404200424040c0503003481002403040780300402d403080c801c0d00c03085117580c0001c5103030141c14800c0c0e0b00201c007644613807580000e683c005007001030180e20140d07004500c101404400e0244480c1d1241038040784400983e104c0041c00c811051503518400c801c0c1d04147c102800145443ca14045007039840103020002c0e4002c2d42030003a401c80d059050b0b00901000d4010402003095915030380340c4090351181a502c00d104003101103080f4071120403640141026030701d009250030078141d03669502e0b800340b03100c40c02115042d040070301c81820044081c012800030401070072119510703103420740026003819412074001070105404800982007000401402000c2c45c0c0102c1140e031201d1000c99940344030b81c07044008600150784000c002803141039441e80281a03a500c5907003581000c51450032548401030040046814a0141200340102150404014068101b40e40c498002c2c103691000c1c804003407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 995374991 1250 995373741 995373751
    0x2208070617010e100b3c09120a0605161101050108030a140f070503210610030908090a150207140f040b0a1d040209060d051b0a170303040b 61
    0x103500c0c05441c1c0742402821455040d50a114031844103619140b00c1d030b0305040d1241d0060001040300090580c540c1034299000d08a0103500c0b5a40384050380301c61401895282d10301c05e0f0300c1d071115060006411618140c80d81c103400d010000100e4114070019100c102c10344005503200e00c6000d004075140072510b944000780320045940807009210951508070700e203a5034454070f030520082000003003011208000c84d40440f14030b40e0711940074544604032400c0082e01c076442000514103003840d007441025008400c0c041203106800051080079084d8072200207074060b0100b0381046856840802c00100b455482c066200060040c485c49040110014003000e842c01501d500a00c0369800031809c400e0950340c4000c600c041d101020f481c085440e050040c0031440d07240e500d402c0b035845e4090310100089000402d01d8040e04c221300803a41d081c86529114240700f142c400d035400190603074001141409104141c1404500c030080c002c0c04c100b051503520318840c03450240004510b0b00c2600008103000902c00101074064002d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 995376241 1250 995374991 995374997
    0x1f0308030f0606120f0c04030f15060807030b160e10020a0506060f1c0f08160c060504081009080918040c05040c0f141902030706060b0906041202040222080706 70
    0xa100c103600d131814404002c0102104001ca5000074680100d01401d960046501c0340b058502d002262414006e80100141c04c14507051600c4000030f04100d00007800e100b16604400c0d008c0051b08c4e0030200489241840c2c5c0f4450038480d032051f000450340c4440e03650640c955010350140c924905149002410800302410086c414060b882e45040b19a03904035000100150310b240c80038618a80b03241030304010083c40ca000e4603042d400301c0c2c130783d0340404100b44003040c0a104a003c40740c000e0b207400042e2000c1c0540c1c0500c00c0c0543c4042c610b03d07400c05a83c0d00640c011401010b9140c00e02c641080014a001149400700890414030401e100402540e900d0100190408481c00c0c0303c1045603540003441500c0300b083c0b260800c070032800c01301c2da0804a031080350445180128202960130390b806000c0e503254448141110380070310b0420b001802162100c25200381110080c45d4030701e401e01d0440d4640c920301c0d1860b0305a07402942040204008041e90303d003040310002c2c10303c0b060701d82450316119500300003446d4403002c18 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 995377491 1250 995376241 995376247
    0x31c0912030501082a120601150203030103031b1104020d0c0e030111120703060e0c041503050c0318011410030209150102060f150a0306290a030305031f0308030f0606 73
    0x440007141000b15030186034032540020f001780b401607280502d00603620fa00811401c1040d00484408508141600c0c4901800080b00744280800c0b640e9200912001d00000e0884035481d20035070303040100c800d002d40129030782588500703000009400c80c0d02012191246a9640d148180d0745600490341c1961110110300030045601d18010010407480390740c680d01007004016000962060003a07001102030a01c3c81121041c6140111a6031400e52040c01544a0f88014502e0035030441d10034015144250707030381c0d40001d041da103d00c040d2800c10110081c0d008115500e4000712003002c1012061544603030b1642481003c001d1860060050006018000b20b6480303140c0190030300d103640c000440030b800c965018000c1100d07999460300c4d806105450f6524540c003506c459000402d20039070b508050103108603a09801e0700c41a855421420a18440020940100d0182010008207008002569002c01c1d001004200c900811504074110b40c5243c008813800c60300802440f04251030041d60507030121041d0380f1549 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 995378741 1250 995377491 995377499
    0xf0714070b0c09010f1e030518010c0207240918060308031005010306050d0b010311040f02030f06120f0c060d110f0c1c1e0201180803180705010903110102031c0912030501 75
    0xc00300102490080074142c0308c5001c100c00085002540c90b07800b203800000c0101500040d0020346070130240c07266414440c4c0c400e2508940c61425486610a00c1c069107903071030341074940400302110000e9520210f21260780c1d40030004c04152004c0081d40700f64140581500380905150024084a40076084107000d001c0707980b24100050022451141940e42204a10f00701c0b903017120004000d172468102c80038560b800071062111245070440503e0092408403140c094400b0400ba04981c0d502c901d1103025515441404050310303d061242c000d00b8000040100824115030b402d04480c45079000144550792104001280300031480c00340058803c0900080a0083c0300e082c6080c0286000f500040750b14a1501d0241d004070414000d50103407202d500c032010022200c0d809420000c0e0aa0021103680da0840040d02a80b440240042056800da940503140c203222241940c130780503150042080030f507043d8401080615420840401c0341001611050404a0000340515040e501514000e00d048249030070600180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 995379991 1250 995378741 995378777
    0x120307030825020607110106180203040201030605060a0914060d060b040602010e01110319090b0c0c0601090e0d0c0c0e0a0911010e0604090b0105040504020408030c150f0714070b0c09010f 82
    0x5411000c141b0703107900f410561400040c010003280c2e1045110260032202d00c11807114035000f80d44118001d07281000a6035036070f0140326692040e07034941400607240030401c4c8500b044002d11000540d602401c2241401400403901003155800c0d080076a0900020904003d482d0382402903c0c1d0081510f0028044c4001c001600c82031400301a0080614038500e000d01c42c00c468050b4065225a0f07041b0b1011a131038280f03e034607500c50307521101c0942d05500a5600218404540d8010f10420b580e0f0366004150304503102c503045800100621040380e1515052100003007140c3d40d00b07681800750901590001c0d0807807042c80c0204c0300d04c03020098117060100000c40705e40b003070b5220300907101102d0b49008003161107108a40103e030244599081036a006102250200d61ba00000003e4502c1028000c11503205c40d0504007881c001d50740c1190000c41c0f00711090000f50f2b506101e402c00c003280103494070040e82410f231150360300c056181046075074000680c070100d0044042d46e8407a0340e07400092581e0408400c0f8400c440049 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 995381241 1250 995379991 995380003
    0x80108190201091703190809100e0a0305090d050a050303190506030c040f020d1d0706141801140a030b0f0d0f14030403020a0e04021801050d06090212030703082502 72
    0x9402d0384c00303508140c842030000e00440740e5608006407034042c081c441c0180500401420b6400305081e109601408440b0b600074400d40c03020300b4aa600a10b1b40242c4e46c0c0d01201c2c0c1d80e0003c91904d8100d502c21081c400025020011844014821400f86459107091000c1c5e40a00383c00d03184040c0240d041005101345900d0200b4492400b1800360703401300b004e0b41309a005d0400303440355081c0d0031041e070314044400401c0300543c41c07003c1d94000f080040d5031115560b500300f02c0e0008a1502a02d80c1110208030b1110070b0f410600701e5424140c4181400e901d00041c000300c1001c0e682001003154007090302c42040343c140b454a19800700321031002f110303450740410043d01c235894504a401001011840107814202000208005680085070300401000c0010b8661029100740c4000350340490003905001c0e0171004e1550710349002030503a600900ac01100d4040b80d15888090414030b40300703981041300c6c1c50000d00e448070107200810f085c6010b500d0303c2c01203003084404841d4811031400100f0070550a070003109000c40c0d0200384 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 995382491 1250 995381241 995381249
    0xa18050708032701271d1b0f030705090a030b1e06011e031814150a091e0f0204020d0b150304050a2a09050906060307082d060708010819020109 63
    0x10400c4004990141d5400307202c084d400001070000d00300d00c1b0400907802407002d40d11580b45031000030f5031303c80007002e0071076680221454054003400c244002200148a40043d1940000c001e00c0c000d29145d5070b860740c0e04c0c82d18043c1c6800313030300025203001e03441d450f07048007600c0c0d402010a1a001c5005480703d000d8626480302c00ca001c2c420180c81d1000c00d41140e00a402100038550804020440c50300c00d0000309036640c004552030049920024009040640035100341c11000707400200300b03440c14460381c0303071048581031280046491405c04146840962074a00c003401c0d40e2202d50b4400038180c5007190130060f48a98070011030300d01e00002c00070000012004030340201003a80c000d010150b81c15420002c8050303809046040c502401d102d6100295070242d54211500a9004070203840168a8080078140c58540078001d000a560085024080000c0503500c00058544803802c5418a16011100303a420040117554050000790381c04010710006605006812200001c0e001985520b000c6a00107840501d45101e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 995383741 1250 995382491 995382527
    0x17040b1308010c0e0a090f020f0c0d080703050105030c10030e01092d02062a0a060506010e030a0b16020c0316031a09060f06220903110a030203030a18050708032701 72
    0x1800207c6d140e141e01501c10050007828031545a01821203150b95980c0481c4a2000007610000441d008e54040e110710341c180e0b40d010340580f00044101d014405241c0400320642c081694503203035058400c10a128558a09104181006001c82142950b038102c2d6801140c1c55005c6000120326001039a4540440d0b140d944080e40400043c002e006d00040145003009001c100c5008100d00c507010041c03507602c02c510a45098071441e4482510400341550f44030801002003580f10305130046107803000300c29500c0b100c0d00d0091040750003450710300300420300b880020422008041451036082c030130800c0c10b10241700124400d9040c035940380382c80750f4002da0f9505c01400b050208500300700460304070f445e90400b8083d0030351800207003480d01b0607841e1084010503100000b0b4001500b044501e841d030403000b08013401001c1c0c00d54010b5080d1344505400800800c0100c04034984000c450500340001402403062200420004000c2c50301c5411800000b200201d5401c03015544892044800c03085a800100310144114900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 995384991 1250 995383741 995383751
    0xf08072103030b03030f0405090f040305070624180e010e10111e0307020c012c030c0a0e09010c0c03080a0c140c0a15061217040b1308010c0e0a09 64
    0x20600303030b00600200e024541c0600000408504101c1c0c4103005000f142c01c03c3d1564034059560403a5012140d100780d4000300001c030704001c56000f2414503003028004036000c0c105082c85900050341c4040c03d01999001d044081c0e04010047c0324010b06200d01c442ca030702010001d000300e004d04014146c4403920040c1e1090349540d503051080f041c2d00c491059440b81010b00350341440b030b8004d078070703600500f5042150b01d00c1c0180f2580b15140599403180e00202520a0200c5814140031445d0100c00058141d440401e0740501c50711601002c680d540d0b84514008003006050310301e460070b0410f003603800d4504400703240060240d01140c041c0002d5000080a5200180c0700d00081c08850580e0b08a0b81e81011404510028802143c03c603603030140420550311451044c61401508010200400103440d0b0600c100c4c2c0850721010400e80108160082d08182100350014961030540c0b5104042056044201c803018800300c602d1040c00306480074840c2c060190168200300181e40d180e0310014224900710701a8003e070b10744403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 995386241 1250 995384991 995384993
    0x306060d11030303010914280f020702130504021008010e010b090f040c030f06141311070c061d04050f070e030309061611060a0e040207080d0e06010f080721 69
    0x11070040d40200401410759684c1c0d40c0d50010880500803a05081008180000224103164a1380a0f0003946e00c04203414001c2d00c40310035495100404000711040380041d020840c20005943d003d100000504015100003451f01705030040c4800328034210b04400138051030300f0040c4110b9060300c42e801d0441d19402101580c2d20000310219200402d0200c1d441d40160a08142c0700d80e060b055085090003081011007007100c1a0744600b0248200416400305400c0914070060510341440f54015a459420760b082c154034110141d902c03900701d40e080d64402000510000d44948130095000d00206aa00f01200c040c00182401c90504402030710180201c030034442081e102a0641d20140103a52091100a04070743d1140c0c1807801c40c00301000300b02e00448081e154114140b80914040e425948000c4203541c1e10300f920744842043c80001c0d0311103502030f24607803820f20003103000111a000b0000c001201001174215940342440200308041540c000c1023158004003003d00143c0c03003810903040400c60b044806180f8102e2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 995387491 1250 995386241 995386253
    0x2102060a02130816032013050903040e01080102130b03070e0d020f120c0a08070308031906030f0f20030d2303010f0614030f04320109021c020306060d 66
    0x149501c144444d0140c0c240ca80700300d1340701c5501681240e00880f100216561a0104200c0e2800c0c524005903102982c1203104400031800d80c40a9030002c8104100c0385010348641e00c1200b190400d0b4810681a0340001e82004401803500101c4000c2150114003400c500780824060555018082d400e07000b5803200781e001d010f5640d03981d00f08908038809060701188904a8200e5030b1a01442020603015000760780001492850000f4440201da400100341410368071000782240c4d4a202c021200e4401c5900d81b9004400b0880018180000e144140c0000410407003514004400000f0811404007008a00c00302c0c1003240c50104840d04030700000e260082c07040300320320451485101e49001c45083e0220200c008540c00078a41206019075a40b07480d40d40341c1d0360a0a600c0515880102d5506003500079107004980055000060000c400b48014100181031881f003802d03468110082100c4a1242c1d1191131035001c0d0b081450054078550442e1201c03400f005c4190300400ea6400005d4000382c010b0204051000078000b07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 995388741 1250 995387491 995387527
    0x50114130f0231140402030703080a1116140d11010c03050d02070b1009110f0903031b060106110705060f2107051b0318040b011b0b01032102060a02 65
    0xc11201255903911144080701c0c00d0007204241810000d01c1c0c000c031113102c00426448184500c1d8024001d02e41d042c04c5030b55102040e041146d203d02070002011100942082c288040c10b60748401c4044c2c015001d28048604207502c1c4030340b140b0f074001c202900400300812035440099801d03038402e09002c1c070b284207180fa089a03103100d52990040054804100358040211342e01d5280e01420940e402c40003001d40f01c2c5211400c0700e502064804103c4000c1044004440c501c0014004903a001010b90303041a0000c103840401c07002150000909420440040c020b081d00918201c0000100c03800071720035542844003107002c500c107191800c0418000821040d2103d0000340310158031400c42c2c007901e403440c10f2102c03000e4403a40042441c204400040d40300e1030001c1400006640004240007903462400515038240700c008e010343c45c0b1440c1004081c6c1000401071101c0ca42048455216441401c0b841d031440c10f00702600408074410031000314071050300048055000a907190810501480165a4542040c00041000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 995389991 1250 995388741 995388769
    0x3070e011b11010e060d0516020d0e1c020310050108070f060203180406050303070f0201170412080c0d0e0a0c0f060801090f0605130507121e021e070f050114130f02 72
    0x213170b07000801d441ca90100b50880c1d4041c5001a011101a040c10a0280c1c1c8900c414034a27840010100048280903113000075883d0060003401c0f0150310040c5443c0c001c6802c01002c0c400b1325501c1e5456600420140074200948401050150400f00310745060140003901d0f803044407114590852010180003c84c1e603184c0c8442c004240c0201143e684503103e00d40010b072201080020390100e26500301e059080038004030018803691f032204800030482400d900558074600041c240d49043c5c5002c0c45404985003081c07285001c018461401000c5030fa0070b034a80b695031004587c021401c40d01102c442007140c0c0b5004401107065071468130380420103e0207c0b10310390091240b54041039000101801c0c40144000592200d070141c0e81c260346040001101265000a50700c030303040f1100c1a03245151a070445c441c626400b4024040e0a010740ba400302890b002c4071003040d04501820740c0d40040952002040110074031a1402c800c011788e52600300e529252018540301d20078402c018110540d0110311008564a43c807086c0e00d81 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 995391241 1250 995389991 995389999
    0xb0417042607120f05060709030c0302041802060a09030b1803030c030a0b040c0509011704030e0d060b100509120f07050d030c0b0703061502070e16110d020303070e011b11010e 77
    0x181c3c6403810030030004280044140e400b4000e490201d03032641c1c46810f088003900e40110060540903d9a070034003005180c031018000301228827030302c0c00d8016998034005110f076164668a5a602c2800c500700140140c03009012038a14050b54422211b8a41d808019030381e0088001214503200d03540c0f443d90001801d0705d00780050740146070201505480d074011380a010365003800c1e41c4e01160b1078084803144006600aa0300070b408160780d0b6403209028a803a4100021b807a00c17512020502914400228451180000030880800c00100701c05009050032410030080c2c8841c20300908500d1000d81c1c11a40307400f070a01400e4041c01c1004005000d05000f480038080c003550018514200713140a407401001444180501950300328008520001c0500c0007820000361040d585819103d074603018207505244045451440501201c0d010f40b40801e80c2c02d00a02e0521500303600070f5039070307850300c0000209180381d441201814451404c82644800303d03107074505400c1c00d0b4012a0440d0281c665030050707405150310900e0940c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 995392491 1250 995391241 995391269
    0xd0c080102040303050d050105040b36041211030703080429090a020114090a050d02030f071203021014040210090f030303020702180708040b040c050603040b0417042607 74
    0x8145d80310b0001c003142000b100c070030841c913603c610801050b00d6541011302d501c081255812110741466100740750000203640380070000300540002426440178100c40686200e03200c218075054458005105410002065001d986002e82d00d6034064904103020b00050a00f006400003503101813603450802400c0b02d00450101414500107180d182d650003546000c07400039101901425524140c0400d407240c41340000d15011100703040034280100800650000d903450301c81c0c1400d84401c3c90080c44040c0c064014051200300c07c40c420304000c1d02d0101c080140004082c90700d10903204c1404a1142960019412074007070024a10041e811110440325410600010b130404000004043c2c06500070006284250340c0e045001e00c44050316101e5000c2202c1c54008241c1c034400180004151143c0194000d10503003031403200702e40391000b003011748c3c10480c2c00300d5040c036510081c403040c4540386007031003020000420b00d1860701e828656035005110281e001c00300060b0000704080302e061020f0080802401c80c6406041e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 995393741 1250 995392491 995392493
    0x30f0c1e06191e240e040b060a03080f070204091407060212040b041701110a0905030120160302011413030f09081203091603140c090f060d0c0801020403 67
    0x14403881e003912401c148011030145840d60310034501a0112040e403a000c0100d05801866000024251128240812080004119151505298200c40a025460406603140c80c040ca05a25010030181c881c80c481d1600f07500400004941b641110221401d000301e1544030041403010030003074680684010b0040304c213009007003010311000604000701e4403c1c1c0c0c21500504920700d680380700f80c800c034050000c0307000041000f0302c9000c0c1d0205696800c911881300000702208009280364103504003005600004e40b80d110204a03528007402409141130595a0300c1c1040304044500100510440418007000da00e4060344609040c000e61040c048031030b81212051251800c080000c1954500f14000c4000c80d0300030502c00061413080c07420f2000e844010b001000c070400c03040f80c1c1264540004200000c644103046010003002c1d646180f03038005620485000002c0c5409032203503414001c036254200e0084921a08001c0109403a0846caa00002c06882c1440c0b070304a9802c0141c403404e955001480250f000140c004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 995394991 1250 995393741 995393743
    0x40501090c0e0d020915030f0d05091002010e060703051b0c0102130f0608042d050115061d120f06070e090601090810050a150803040305100e030f0c1e 66
    0x90070700d100302c0c1e858403890101c910030000808030303894001c0d402c1103644000a070050340044d40c0c404180c0009080318882c1101d081614034008640c60110b0006502054110300350074000310b078402c42496400244421080410480d40e02c1030014054030416483e40b003c10105000806404908a040c04c98a665039900c840b000d4040e601024100404400c46100003a54024140492081d034079a59188c42c51034980da20b4032807040d2411400d801640700d6180c1c0c040450000a01487d20040c0309100210300b05044284104224101e0380c0041c0c240031031184002145995807055107031119017260031098142c11f40b455149000750504001344288900c00c18031514a41042c1103a0324220100c80c01e021655030080115031103e428411074801e40d124141808100c2010b820039503102003860b000280481c80210360030180c040380d9000560302d420000e030900a00c803040c442c0e01e84000310414180900261700300e281d0398034410411a2100c4c000007003060042560144050700045c181e1601240400c8500c2e4400707 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 995396241 1250 995394991 995395001
    0x210305160b190c09090e15072c01020a031d03010624020c0906040203071806180b0703050415030b040f0507121a04110409050a0b031212010311060904050109 69
    0x56841c81c51480703400b41e568070311409a01c81415140c0d45116041e4a0a070440001d01103482c0394007400e0041c6401c2c820100a140841481092655200d03000c03140011002c080407604590205040114480700300400d0744c0000e4144203603076240c40e22160000307102a410310300302c1c1c6c1c2c0080e80764154200800015490032100810950082d20004126141d83c013a0b07099030f450134001151504680e840c00080c0c810719050b03000d1984540b2506024919008145c0401c1015803d80c000e00003181c2c0145040c10741106201c0c600700030700141c00a8a180010b50780307000c0d00900803841100740c13405d2101c010b0020603109400c105441c25000e80207120010a1020620143c03404981e000001556001e103c15031203994083c00c45404121412000c940c640300050102811034070f150881c00303403020440010948030301d02c603291107803030003940004484031001c0805003000740c040401615028280080d0b8221226440030b40d045a60010104c0d150a5285d0041a003d009120280368810714040000074038485907004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 995397491 1250 995396241 995396251
    0x70503030934050402030a1805060901060e0618040302030c07080304180203071d030106030519061b0206070f0311070b060f060c07030204090f0c14010806040204210305160b 76
    0x3012000041824031402020820b9a0750110600400810082c01d0a5005540004019502240e44205a5115924562125412501c4c1c2c0d00407400c00c400080284a40c03406461200d0300b44010b41052400100b86d04030070715144a4804002002c241010700800850f01c40d08800401e42c1c1039a80d89a000503182e801038850600140c00040b850380d01c01c2054822642309984689403400c15545900d0304060b0801ca00100703070303059941c6c0d41d00030005c20002c011400c81487c810490000d90056450808140c03205000c0b254002214040040025174021845940c00b410720b16000600d00c0201d41c044024108943c60501241c4000650805001140e01000e2240700c0c1600d400800070700c1d10007440403a1003403c0581589410003007050005103802e4000302d084034003514090700354001907240c404034051f0b141c0c4000d0000030b108901038855604080f0460344290111411420940b401014803448081e0040c40920b800c0c13010280c0c8109070161050b03070020498507110042d20a51840c026a087d070042d10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 995398741 1250 995397491 995397523
    0xa14250902071103031809060a0e060609030a1b0e0a0e0a030311090a030c031103011815060312020d2a080c01020f0f07060f142a030717010f03050307020d030908030a03024504020705030309 83
    0x800039920102c0c42c000e42c405000614f005081801030354508400a090700607480c2c40440c010041d603011952030301c91501c05540100d00048506141d860030a00e220078480c492806a4104035941480c1750041119200440e00000e07581d00d010283d00d001ca00901554000402040000c046480404c0d070008000030200500d80740c40103441d8522440c8440791860520401484070034465a10009000748050400c10488000240c141002200721904941018003110754460300887c41905101840c010905140d00c50318007000201000024015917000060003d05a02818402584910a010714926180d44c0440056440741800c42c1c1c01445048184000008589404000b2444d061100a00c0b411290b001008507c0c1c00001d509014280d200d5403c2501407000c402c900082080040c001000341c0d0f4a240c1c1e0040c0c0d24242410081482011070a6144490b261010012044a59040c40d40c0449a84800151611082c0400100613104c0e03400028a540070100600c0720568000540ca581c10201070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 995399991 1250 995398741 995398769
    0x308070201111222050a030f02031908040312110a030305090111040506180102030d09060f0c1d150c0a14250902071103031809060a0e060609030a1b 65
    0x303080c42d41c0e201d9612a80040e80b0f820400c0b19104401c00300c2d00700010000c50700c0109515510390020301a151568001c0d00c00900b20310400046190a001c6c100c10304100c0100d9401001860b250040c4a0159020040c02c460710f4040e02d2503003a00400303222a080b0f008100700c2d0016403180c58001c0c0584425500c0a00a40c24009446110383c02d45055506450f8050401820166100c0301040844120b68032181540400c11442e10086480e00a011a0074052000480c0705107500501d80c0480340503880141c108580720340e4980e40c01400410307261303606a0440303100301c9071285800e024000d031040302443d110a110300031401d02004858221240301e14201403d50b03900303070381241d61420402414400c02000007a01d480c24000d15a295000c0c0104a010344042d00c5014149400700f0301c0c0d5803121903600069850050405204c1ca070000c481507020100b515100401c0b03161070f10842e01058003403c07851003260045494202902c0c208030100d01e072a044448a882072081440000d030906c0300c1c4c081c2d002415503075 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 995401241 1250 995399991 995400017
    0x40e0a0f0b100b030a0203040228140a06051603020705181009050408190903060203010308090a0f0f120f02220c0302191121090a1a041a07060203010308070201 70
    0x100c04020b04580c0015452883d540d12641c01c10002c6d40000c104991211720300e0340d0b9801d081d61085082c110401d8158800d03200b2400e00c01220921304c1c10421044c4103144040041c000313540c0c460140e405041c0708551600010381540790a80c01c3c00b905030021034001074845460340440c02102c12550043d000c5d103001040442c1c448456500740c035012030300507008420411120420548602c0d030f07004c41403024900700010035241d684020590307000381d005540e1070a02045280d40c07464080b20010080090365420707448030f89800422800c003511849110201c07441200c145061201e9400040e03c103d600400350703090b00481c0740040510034619060800d4075440c040f110221030b40031344203c584007145400458140c565400c021610f4107106062819140038800c40e18541c00072029003181c64840c030030003030380d05c030300e9400103003d1f0022440d4031248514010030b4444411000e82000c4a0a60b507281900c50142c0b400000001100d11907250020031f160f200000004c284080f9074007600c4498801d03079608101141c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 995402491 1250 995401241 995401261
    0xc0c0111012003150d030903030e01182d0e04051e03030a0b0d0f060e0c01030917090a0f0303090f050d0c06080a0b0904140d08100b09040e0a0f0b 64
    0x84140a00c1e100c0459060072214408460b02556001c41800c005054019100c80410031203596814210007041c0710400500406400112501c1030200a182041d1000101c0c05881c0d03c400191041d6031424040c0244041d40c1d5446e01440c440d80d41450300b68164003641e405910102010031034017950349015044031400d440c011075422210001d1000011b40c01c0d0f03103c800c0110010080440c0f0160300c404180945000618503c0041500500883c4009018803410300784a00300340030f030504a4101450440640c0010752041e40c103c40e080300c4590000c0e10380181ca0302103910a4103580042d00700c10b0f846040041090350000c03405040e14004d22500c44a5a601c03000c2c001f00c0d103095400100340b042001d40500c40306110303940840c3d01416002000c949451954081040030209031010f80384e912038021168043d520402c1002c00100032441e00d0625464848500e480490040c001c120000070000360003401503441c4e80080c60b0743c00c206030582d41104400c0c901115481907000046030b40c400340380300103484648 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 995403741 1250 995402491 995402501
    0x2c1e060907050402130504090501090b1f1e050d05161401080a09030516150e0a120503040602042303070f050f04020304050a0b130b090d0e100201110c0c011101 70
    0x3a66001000714905107000c203c040d41042e4503c02440d590000002180d68550090740e00d801d015400029040c0a141001d1540e0b03500108803c030121040075002850318041d4050000b00e540801d1810038412000106c010316410a50020740d10140c0009550240a004981c6650b04030070003d6250115540d0350009240003540310f0814080342100c40050b138000041c1c0c000700740789446032805900e4090120132411920f4070222040c2c900c902a43d1040344601554466a07040c180701c0b400408040c1166618584541a4405404100030000c40490700f000b515030140c5010f4084800e010180410389101d0802c0340c0d81c5c030f074403640c464480d0304d40016408102c0c0c90135900342c40740038029000300c901031001c1c00060f501c0640101e850748a1840e01c1e00c04903012554142c0918041d9158408040080c14400544680500400080d81000c0d40e401b4209800469042d50140155600134000c1c000ea00140c0c010100500000c078481000607044810b0b1b0008254200c8004090300ca210140b0142400c0300d003219 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 995404991 1250 995403741 995403751
    0x1061415090301060b1606060e010803091507080a11160305060109090c05040e150c04080c01080c130311151603030b0d05030d06170613062c1e06 64
    0x204050388034501a100150080a98100203000402c06036620078084603554480c44112200c3c080d0300144d0300400c92503002e200000c0c07261f0b007003862895040844003900e030310881d9031031885065407101c04c0708080d45440990300d9198100740150340b0303603e528801900481090f641d010490003200c254003040c5c00c00d10811030949070040e0040030744d80e0070410410b005020014082e034030142c0c8401c00061a603210b0141d21b1404e00c0040180890f00380c451006130300341c08080d02d1880c540b501408184040349001810801d4100c09207040c08403a12482c40c41d09846c4201d40710701310075607201c00021060115061800011410590714200ca124040c00b6007221030207503204640b9520094251680420300c25041104c980d000104240c0011401c1d41c4d4540c55075010711408603000b070700c0d000100722000000100c4020015104003406662410103081012030440c03c60090056564020440d8040c241111084c9000040400c00c45400402d0034000c1d41e601e200405050303050917400602d10200030210740e0b0b80c056 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 995406241 1250 995404991 995404999
    0xe15010e010f0b1602091b1b0106080d050906280206190e062d0a090611040303020d111c030e0c0d020d12020c130e070b090a03060207020a05100908010614 68
    0x14a0386507003000381b00e04003c1e0010810207130460300c1490080c01c00000b41842d901018040111401c145102030070b4506d00d52245980d41c210080c104480c0e43c020003100c0b0513400480340c9540d900800585851004010408019002d00941c81e403c08541c000032241d003e02c8031500b40304890f2000c0d0800500352030200486035a20382056002c5400b0390b41340d09414008400d221052003103141c5181e1808031652040f20b2020000d07446100c13600030b2200c544119580000700b441818501401c3d41c6000e03541d41c54215046003009102c4081d1b508000c01800002072320300285000b40e00c54000d00c1c00003006400500c603001130b603014030300031a040c40c40d001c240892010b40c0070300001d40740466510b5200c015005090940194005d50594000f19910380d00c00724050800c11400058205a4840780c034076105181e000310000d0601008100c009a076900141c408891f4807980250782c44940b40701040c418525607106680000c00c3c210011556034000c50301c04103980d0124005c00681d030f51480e2400010304401d1041d030300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 995407491 1250 995406241 995406277
    0x1091a01050604180f0e0604032706111501060201090218130305030903071a0103150b011d0d0c09090b100506071101110a0b01090b030609100e15010e010f0b 69
    0x4c0c0c012000302002c02041c841c2c3d03000401d0400040c0c50030075201307000f0840026030805403c1004254125907041e0081d44041241201c844021005a881c001d50780034503000e100070340d105d00c00011010003035150301c0445405401c007156540c3c03201034044d004080040f03201d1484070035041004411181c1e22440303500032038807403640005543c4081d1030301da201407d0401c060100f00210008140c0780200d4071420a00d848040b05158514242411001c1c0c04030702c2d80c48118140000c0c0a0640e0b8410b81c110705941d0b50040381c5c0c140c3e079203480008294150b50f900003410044400800542c000720355000c006020302a00c0e02c0740603613a820031500c0c0d410030355000e2142e01c203009200300c0b400300382c210302d4941ea0340703006040404146111506081c134000c0215001c484108040d4018006070030700f801101c0703440c40e0a0b001040c3c0f03424880603458807103090b0740324135001c00e070340d514610311140e4100304414166100c0e2208a20f656140c0b69511f034440002d0044a10b110200c4500107000203000f011a40315810101d28404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 995408741 1250 995407491 995407499
    0x3060f12120a090816090c02030307080c1303050f030c07050909100510030b0412031b142215030b1e040902030c060f070b16080106030c0c080a0201091a01050604 71
    0x8090b420141d111410421101c9003c203190400f049882020ba0b0a10702d52003e81e403034940242d040d10200810741e0110340062040c88102a0441000381d00302010000494660b0440c98039040b1040b0785510160261040b08225003100102100400160341200142c80c085500e450074820300795001c1d180314409511602e01305580000940c086500300800501901e10181c2d03940302c21000300700c256415220820b2901a00e0310694061281c1016441d103030b032442e042901d114034080c0130241ca00350404903130500041d0080c2481c80c1005c003040180801c02003810035503142d088544407410b9143c1c40c03e002c40c0c80c22040c100d0a2512007141d8079003410424400b2190003420083c00082c001e1030341c0807600b510518554a405903a91005400c02d50710700724022f40c03680c2d2282815400440d014081e4106480d8904145800b030ba40f0000190540e00c86080104a61030613020072126400b40400140501001185445d00c2960641000d241b5038050707010640203103040e02d00100a045d00b0300c21241e008008101c104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 995409991 1250 995408741 995408773
    0x70801061704031202040303021b09010f0e180a030903060507050f0d0213030b0106030b03010f090b0402090417040906030b060a380d0b01020f0c0a0905040f0f0302010203060f12 78
    0x260307000740f2a1a02c52441c1e400035411005070380180d00202c015800c24404100d0381c9031811980148a5001c490b41d4070294580301014035400218003856481c3d50480303000541c0c101e5404402038009034180d048541a80d49414002c00d0001e25000441b103060405011428007480344003544d089040c200300b101d00e00003130400200000d44c01803038a401c03954054500040401d43e29a12140284030644000c10448202c1003010b00715810010051380c158600610000420190070f0800e40c403560669a044058030707a802c00c000300003002500d100c4000c1000802140a642a030011411030b4480c1155245944a581c00c202a09416000c0c403030203003122401c045a8105044c040c49180c11800003500c6c080902d0712684402c0380e01031b00501c00915180c214240565904001e40400e0419074005004112180000a00800054402d0010450711440402c3c1804140c0c42604021036020741c6020000740c5900e000b9020f07410840d5035074810003040c013201c2800d04010780f00e403041074035400c0905410380a19200d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 995411241 1250 995409991 995410037
    0x3110102180f19081b030601120b2a071202062a090a03050705010206100b0d0b22050708011202030a060f020702030a0804030b010b0f090405090c2707080106 69
    0x841d4000b002d0400c900401484103c048080c040c460068104a0b01c01d01c0401e840c034640010950182c2e008a004001c08400180d081450a50281a407200707a100d0120f0798084040c0001034642c150f607081c02805010070a00003c101c2c0034880e03000410001010b040c00d0341c613400300b16a40704100c940c0b82141c0032003a0315010145140914244068148005030004c5400c12541d60030450700c592101d076007485190b030108a1241d02c1130b84288001259800e011251180340284480c20442d55200c00d03402c81c040d0b0b40c038024092420325160310b69941000600303421000c0c4c1004c1d502030000c0b400d1a00081014007100d13001b40f03882a0050020400116161b03504401040560307681c0d0680b541c02d0250900684d8107100c503070403060191800300d49503411818411b11000d011780c0003114104003040150b001c50690402c0e91200b0714112000200c5a40b040404c07401c00d58400f0460341d0088594503011086850701c0501d0103440400b030a0103201703a4aa11080d174542000f07015003c08624401d8495445130801048 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 995412491 1250 995411241 995411269
    0x20a1413050a0e1306090503192d020a06090611030c1c0c0c110a120803041110090b0702040b12071a09011e0c05013813110c06040f0311010218 63
    0x110389c1380907802010307200c51048000c80310001540207245042120b030300021010350510890950390112010400107540d070b00154100410441d00c1d4480001404055442074081d0703100302514540d24a0f00e14103415665009001e00310b007194164000110304101072180100766103c0c0e4440303500110903500c03955460305034200902c0d072040c5024404104402d0a17411070548503ca0906c0c107440e41498039000d01c140100b0200c0078051021400655040c50b80031040d101110000c2030160b944501034000f040c081c103003002c981c0f508114000c403c032500500001d840e02c1161807041c802046403140c2030340a80e2038414680241c0c0062005007055000d030003190203010385101e1078200944444461783d5010b00b511b4000000d201740d02000d004510003070181c410a00e04090558180c401c104030030900148034602c03006e0411140d00d42e1212100c003901c8842c400c48800303030310000484010b45020301d480540344e1200035003103000969410994100a8050081d0b40c08001e00d40e400071000b0314030780c0038081169030a201d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 995413741 1250 995412491 995412493
    0x306030f280503190c020a06020a020109060f0215091f0501050d080912150109050105010f090b1813060911031e2503050f100612020a1413050a0e13060905 68
    0x40f490711500940c40b4000c284c6511900c03881e82018042c010420301c1f007003540c051801c1d50083c2451000603a4041c5500d01521601e08140100c2200602e080f80344c4200c20b558545254001070074400c0381c040c0000e400071032a105c411480b15032000c42107844103403032080c420740da000b000340d9420384001224100a40705030103000e0054040900300300b650a00d407200e0f007082d125040b9003450040c000e401a601626000d404282405040d94003013860080c13140c0ca1506ca510035000d004140c80348080c81010509a003000c0c01003101c0b100640031030180b8010401c504c05c9003440ca01d8140c80e000d88a40010580b48102203191062621000c070781005c0e50684c1006000d000640d520b04007002080c5c2c080d0904c01c3d9262440d03a03000510b482d0018140c005000702400e41050080f00500030410f050b400ba161240541141c01c0241e15403143c00c0058900c5c0e005171800580c004004100d545010039022810400c4501c101c8111007503a031342d550300040c007400640b0040180100f58880038045099a00000c01d001e20605c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 995414991 1250 995413741 995413747
    0xc23060a020f03070b1005090c0703032409061719060902010e04091a06010305150103090c0e07210b060304060c09030206040f05030c030d021504030c080a03020306030f280503 77
    0x190743c01c540c441082224501d4100060101540c0300650a00c0030b414291203480707070b0b400d080c01803c1040c09014001030405440d00c4c54614400b8200c4d0703035069086240c9003081502e548448030b0202500590007000070859080380034000780b10002522005041030210541600001503c03403c0107420718401c10713410b00600c041c61068507250b900c2500b151a01800d1070001001611500c00b400714000f074078841c1098200340a000311b40000455a000d410400d00f400180303104540342c240c2c5898003d9015030f04682e1518104045a03412480780581030020480440030b510303440d00c8000444003082d541c1d60b0080c04c14000280000c60310743c4130710348003046800c0036003c0316620b500144441c1d00a41203a8600a0400001c00c580d003010081c0e8074201c0c1044000d482e04110040b0025952004040b411b102c622804001c0307024140944000f0700d4894201030026a1442d40a4001c0c02a500c141c842c94004c1c401c2c03040d200040503001c5040704c45507108480340c2c030205101d100340c0055016050003c2e11240410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 995416241 1250 995414991 995415013
    0x80123060d1a0321130f090914010504171b060a050603070b0309030703110c0d080d0f0b06120403261e04030801050402032d0a18080d0f23040c23060a02 67
    0x90f1803031b00c0c014800728002058541c1c8a244c4100241e100c000c00d07503c00da0400041c0710010f00003182c00403070102d403c5034a03611004050740210702d20206803004803090040b402801078000c0c050f000144100c01c02d800b214000756031030821035210321003154003c80a030030501025001034841c41182100030f05080440b050400031500040010740c10305d00442e030001000440c84541d80e16800794203080c45441f4000c00c40e202050700407070b4803881214102101501032800003410503020340ca600b91100050614204002d01d0f980c030700203145106907210f944801c640d40301411140c402d0b805141c450ba034166140303001c6901c4c00d41804060342000d0318070002151001c050100d40c0d04078880c03643d0780c0000380030402841e0604d11004000c41d0413407112400e102c645c406459000c036448004680710304904c1000014048140d00601000b017258003e203c1040b07080c8440d01c0341e0007500200650007640143c8000b0303103103a641d05064082010002440240035030300c040080d1549008009005081d5260041d00c11090360 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 995417491 1250 995416241 995416259
    0x80a091e030210020418050405070e01030b1021020f011b0501020d0f060f030818040905010c0f0516080f040e010602060a110901080123060d1a032113 66
    0x341081495030036044011842410b904102c111030601c46a0811481e050070030542400c0800100713503c40c401d5403aa00401d081003020001900106120009144256100d16000c1030305007003a00e10b40c00000e42c07800085080d6001500b589520a003810644c5241c910541c00d01140241a408941c107000325a14040000078100c01c2c2c03642000e21a4000582d605100310310382044941e1f040b541c6010390300e000b07130138080c050701184450241c9030011203464940343c11813000300d50351100d05003054101d42403000351010800c1c1500b14082044e0280c43d03810004071250f030300b01d556000362211441e1122800b80c032000801c6040c4e001b498400203030003056142c95100c20b4140c1c4003d10a9002c2c40060740a80b003042285486446034280004c501000d00c1e01d005e442c1d000003408064103004201d0580010000141ca0104020003810300c1c26000e0501da840f450041078135402000c2f05804a0390812410492480ca0301e00814001603080c2c00301c00350a8030720080c406400641d04641e5488588641d02e410116003204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 995418741 1250 995417491 995417513
    0x105090a330e041409031e0d11071208090c120109020901120507090213050f0102010b03060a0605310c18033036090506040506010c030c0201080a09 65
    0x901600c030440c0381002e6034180030440b00384144040c01c09002405102038900044201c4600d11120f5038000c0d481c00b84801c00c0c041d648104e045a846c03040c80c0c41d401c00420545e00001e00501d0b4041c0328a00000e402c000c0302501d0000301111110256001848142c045242403540090260740080000902e070310b0aa005c286000c100382c100a42150101040c5000c001040042d54007810320300038290300780700000c0c0b000b04690103240102842554502102e5605034400d51205030010320040840f113090a1410903039000b48064040c5a0080e480400c01030700a0b55100d1a075100f009008401001d0030515804620080c003450428100f08181010491085040740c840200034600072402d18482c984185503c3c0c45011707a880c404a00800414109519141c0040c418092000820001e800d038240d51039030007605607019500c0424080c0120004601000c3c1584143c0c40b40308181d030108082e0310b4000040d6510070000400a00180d1008030344001544909071442c0c2201c24441d000c0b860344260381c0c81501c042 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 995419991 1250 995418741 995418839
    0x40e010e0603010b120a020f12030304060b01020c27040204060e010b0405091005030a0b060a09060807080708160b070501060314010e0709061a2a16050105090a 70
    0x1000d500140205803800303201d12105000e0485107042d1120b00180d081d6110102c81030041c0c0701d440349103201281c0340c4905c0441c2001c1c03200e900940350f9a2030240b0700800108000d085450062041c000100e0903810210008500114102400d0030300208414440e150b5210050080780c00c652141400a15040003d41c1c06000e8074120206a40304e504040130b008260b40010044011044d24860400240d01c02150100103941c01040404040d540d84010a0000d1425441180d040345002030008640c0790208070b01086e610701100341c0e0001c030f6880c0d2150b0303684d40da80da02c60070f080c41c0120010043d5600030001084201e2191001141c511750369220031340300040909109105035100c004140034071400b4081c0b0400f404c0102c90400038507080854642c0399001521500290100020b2160f500c250395140d8449a00313003450700111480c85080100361600176040c1d13442415220300102141c0c56000d80c05030b0720915405003030000c0d024034003c21002c084504850300b2800b0701000d0200440348900100c404101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 995421241 1250 995419991 995420009
    0xa020412210c08030c22090902010905100905360411240a030e0609030405031c0c060902041b1107060201142d012c0405120f040e01 58
    0x1d05600107000400010354222001005002115480010743d4481501d40240c0821840c41e220200704042c10100526a145c0c07000c140350182001503500d240e03400144000b8401e03610f0b0ba20361070f56035080c44034081200c06e40703101142c0100404e201c1c504002194050b400750b25201c460001294007103e9a410101c0001c01da18059124100014450628010261540140e5002c6814510713001203160503000c200c05240c082c8000124541c116200c1d401c0f200000c448a41a00c0c2c580c02c5c60001240c0d0780d4040c0c0304190180c010840c0700282004103c051620303031006616106c445080710b5403280024040140200c1c2d010f603a6042045000310303599244e03203104005440303802c00c40070100102c514100c00c641c0b00104681c18200c0800640509003130b025000010f41034006400d8440705e048030715000380ca80c0d05d00d51054aa00001a1010002594541c1c2002c4c2204191070824211001c8440d070400700c0700030f415507102141c1030b00c414819400600341000710041c103604040d110011046020003c1e4000724203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 995422491 1250 995421241 995421263
    0x1204062d0501060905010e010e190b12060108090a0f0f020d0b0a1a040e1905120f0322031e030609021308010501090917030c0f071a090708030706050a020412 69
    0x3c1c1504052100041c05007420103c0030480038500007820a208800003601400220100940103143c08031204003900348002500d450b4075521600710060b040407a100d5001803110008900e4a1401081e4032102c207401810600c1018110744980da96400c00e60000c0b41c00001c10910540480c8099004c540030300051800410b40311142c1d8017143d803c00a20541e40e10480c5000d08484040000182450940200d500b51601000450a00d24180031706051a0340c5004000659040425404001940b203480307a8074903004181c4143c0803441402c8800d4000502041c104d418200307071240c040505000c0304c0300d5490041941d43e00c40022200340d811005202c0e044000c11841403002003020b01405014000681c410401409192117400e0744000600c4040360401d000004110b01000c403a044a80401640d4002030765180d5034030380b0b15070700d141c03e43c080c030149007070b24000c5444040e000c42c60700c04130745003900154282400d46d00d4020040a01400d6811059405c0000081c85480310344140e00b0107005641d40c04d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 995423741 1250 995422491 995422499
    0x10b0331061b08090c01032f1309183e0a091505120102040504090b060906151902190c0f120c122f0f03031204062d0501 53
    0x8030403000640345400d00c0036003c1001a120000102149a620b003440c0204104604140c040c5400513491703070074503443c011183e6000041c40b400004000b80415880e0100c030460380c035001d10007200ea502a1600450030049030090100e0340340541c000c010440d42d080441303500703d000500c010030f600860b85c480c250341e550003140d001d500c2c0124125008008110040c84122032040c4204064001800b480b440b540c40b52090380808182581030f1809010094002c000f07120311420446110101103890328480c40c95500003601504180c2000c40c1d50310718800c0482e0030500c0e160b98411007114034030480350440c82100c0380c4540e54405010402c0c44030b8082c20408a58074140341024141007040d03000803407080e0720200e11305c000031001c80f003540c1141c9031402c0400007040740385094030f1081100000918a14182e2a2005c0101041c0751060340707280003200c50715071400020052507100d0240f041e82e10407106190001a0208129130494550099240ca040020700c0300308040d2900c0d5100e04404620b07843d980c40041c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 995424991 1250 995423741 995423771
    0x3080d140a1a060c0a03111c080103022826060112140a15020315030d030e0106081b0d081e040317121b040503011a0f09010b033106 58
    0xb8010501591030724035100200c4182e640c0d034186040000c0030082e1283c11401c8200c0103100c5803160076100c20110710341c0004424010702500007808140d10540301c0c465100d107080e112407404400e002442075100011031a014032004204078401844901d0350125081c0c040c1c1c0075041c8640e80c0604501d441103151f100082c109100d8480d81d01e0301922440d1300c600d8408011800044010754008610310015907280c3d58800031416502003044001d4161162030381d81c07003181d60540c0040a219000c2d1008001c2c0d03030342d80e541c034079511103074400d090000385684604078030141049480105d090340192515450070344500c140c5617203090440400d202c44100880d0900400460038249481000c1e50420107081c01c60310540002c00ea880500483d50900c050000c50601c0d107204170a41e401040700400802140b9084d40704601440081104140b2844180002c1c40c0c4a181c901443c40c1070340c1c03400300014210764a80d89048200c10303a44400c912241d6103012100941c030601c1f0481c001403482080c01240888407510b01c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 995426241 1250 995424991 995425031
    0xe10021c1709030c030d0c090e070f030e07060e120705060f0301030c0503070317030402010905190e0903070c2715090b0906030303070e060d090c080d170103080d140a 73
    0x82c44203401c10401d082422000100f6501500c0d41c2ea071000a400c0d1200c2000d589800b22588481c0c0140c842c14108050b03e0b800071501c0c0c0d000340c0681c4041c05031741c004400580d20b400740c1d4000c40012904e00c100c00240380c105590824032182050003114482a00c03100001c0313440c2c1017204202e4041e0300010052007080740c9071903001c004110603002400201d0a5a880840e60601030596990846d00400018290781c81000e01c0340c01001d01801c4904001e0385031001001d004601c0c0164007070200400041849108000200c030482030f01320268481090805001400c00c10000c101d00c82c000c1e2103d1a00d000f0080b45105500e4403040508040080305d00d003e0b00175080c1c5070340040c80c0d445078409800700481920040304980c2d004030141342403100c2c001d0181c00a00b40d80230f0545000000741c941204107007044990017a810a41d02a002100d2100140d031608a03601101c00000d280c0e9150314a00400c0080d0800b8094602504403600100d816181b07031251070b404039000c8462440ba1034840381400603140c0b0344444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 995427491 1250 995426241 995426251
    0xf09020910030507080703020c1515100903020f04110415021006091404110301020c0114040c0e041505060d0f0f020406120b0f0403020319180e070e10021c17 69
    0xc01d000071300d051500a40110300c01805081410740000740f45043e80340a0002e00e41140410313040c00450b0030405e440004a04c00d009241d40500d04811600c0f102c507000d05011707011a0713401445c40140701c40c82c0062101926556800300300b2281e061101260f04181d1480c001400100d540c01448110540c901100c290f81580d4001c994051401e58402e8580f00c080f80080c1e44203030071040f100c62424011012900a2140c080c03691802d52800005c29100481204090301503400b400c1c649865549400700055105001c2c0c500510720b01d01040300e03280700040e079040150320180c002c198083c9407416446040c400c529105040f501c0b0550107020b0421480c0c03034400c1101900500e000c000c1da842c0c55590b8203230807000c0500014200020034002408141c420002c603202c050b01c0301c0141130300d100b000740080c1c01600ba40f03100c080d004d00c02c50000301d02860b04010790707031107100d169903071b04900300c2d074013041c084461003903aa0300085006084814920b190b110b005130307141c100c0a6a410000204408001c0074048020380 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 995428741 1250 995427491 995427497
    0x106060306051c230f100f1e091e15110412060b19031407060509031002070804030602071203050708071704020f040509030c1207050a03050f090d0b01080f161e0f09020910 75
    0x19001080211000040c40b02000508c0c0028004202d42812103030501c9404100c11403c5a441c00d03201000503000510748100030405083c03159210702c0c0c607840868041c0303014440075142ea030390320000401d80300c1d0001403800001030201c2000350030240074000d00c0c4000e900241d0740d80346011f810b0900c0d480108610f50080031325140c15814814040d00013170b151411810100c04441c2c001c1151010f000513181107c2c011544440e0131981c2e41c071586000000f605041c1817a1001c81e251500040005015400c420700c1400c450380c0c3d6180802c1d40c0c1d06460140034024106036002541c1c05641c0c1c1d001e07221031062a000d0100b00d401103448802c00010186403040b16007510080d0700e000d100d003600065000468100859041c2402a00c40003036000d401800d0180040301070780b0404c50642241403100140025040c4e1307100000341c40040440428050f9603003024158901c59201e0306c1d000b0080200b4040c100b0076028003160b4001109030f500e58104010140d507401160400b0303400100240207203808600802c0301c400d182 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 995429991 1250 995428741 995428751
    0xf0812031906060e0913050d050c07090e010c09080d0806062115040c0203040f0b0a350a0b030a030e0d06020c1507020a0b01090c030603050303090106060306051c230f100f 75
    0x961080d80b81c3c03503078031081e08c240700001c912050800c1d024015200035201000042000d031100e080840c0c040c1c400d175000030340450a0000d0100390b501000c0303264480c040c440c2d155100079880c0c000600010b0340c081c0c0304482d5108c0d183c03080400c402548080b450701840140308030a40c0300480800f08422030b14166005800d5500400041101d5880d5458890841e8070ba065031039190b6042e00070607540d0800c09440e0061640c0d01c8442c9509220180840c07110701003607100c5501c903d42d600d540c02000c9070f03140c0c803060794550300ca4420385e400684181140600300c5400740c0f1424441c03105550f070034181e801003101100329400581e01d10030801da11044165001d001032005003100c400355216a680d0700e05c18082c440a698842079030b064550f0081e000764001b103a104044999070310b8a4000e1030b00038045400fa5900003130600c100081c00f8a0310742c1c100c130b508009903001d00e40d001c0020780c2c07400700244820303144001d001d11421101e0109034083c08407030500c80182d8080c1c00119103003c50720301100d014480480c0414504 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 995431241 1250 995429991 995429993
    0x11040f090b060d06091e0b13081204030207090f0e1c08150d080f090405010801150e1b0301080304170610060f030617160f0812031906060e0913 63
    0x100c007001d40101003569980c641204078140040500030004000c1c02400c0401c4c0758844030490703190760080245c0036105400780c0e515002e18083c1c4003001c80c00064905481030040c61081c03005c0c0051150414480e0040b074030f40542d1040c1400c1074900c40c440b00c0910968841c8494003240c0c00344045010828190305d0000780c192081005020300601130f00080d88014403050300320580d03d0b0351b001c9000c4960088a07154603800043e24102465000e01c15580c045e82c1010b00005807802d0500900300c460621401501032035042c0644840e2069008200046c1c085a0301c03240e45800030070300001c5000c0d0100d13601941e038a60402d0740114401520a050055070350059040045200840004a0555540d850806150f9940d2034085002c1e18407500482042c0e458410754543c0905d000070300381d01c1c6619091001c044071350368074010400ca0100c0c0c030440d80944c0001c000111015020001154024541120055036414110b03005084a0807038100402041c803031100090b5070320b401e2803802d900a08406003441c1c12119 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 995432491 1250 995431241 995431253
    0x60608060720210901020f0c1e04091203200306210f1608070e0408161502040f0603050901180b0c040e150a06090f060509040902060711040f09 63
    0xb050b400031a000541d01e00340306281c0c07050000a61103400000159450700540003002441d502580d900e42c0503100b403c000701072011000c1080080e000b4001c00c10f5498040c0c03031104042e090080004164401d40d9502c0740000a401143d280c069401950341c0050a80f00c403518400f912416a0124004014144200120307981c40c80301800b010024201708881d5001c084284500e4100110000d090030702400d80325040500700c0203100c0d03007103c090703000700c0320341c280c0d0352010745030190041c0ca020b05444020010310803440c46003801c881542d481b440d4107480102c00400a0f01c101c0e002900130341d05095440204002c1d9aa140c010f40f6044460382d4000c01400d198101d007052221888a80204045800340010b20340c0b06046c400d880050100b003441c0c0d01c0c50b2511900a0140184091100344217031206070011880c148238000200c01c2c0c2d000092010061418a07800f56100e4002c0c0f406180e2180d183c000076801a103030710b00581401807140080c000712030041c1c4200820340304000c00e08001c1c3c602d004100008640 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 995433741 1250 995432491 995432507
    0xf060a0f14010311030a150b0a02280503030a0b0f010f081302130213031e053f0c070918030507050f030f030703050601230a02010e06070c0606080607 66
    0x119001951030049080001079004e4040c81c50b20b1100341501000b0402200c007107402000303d150a444030101e002d83c50706a0302d41c06008042d81180180e205801000c00d0b21048905100c08481100319a018100d0540c2d401c1c0c695403084907203240d0b080e280c060400c014200080000d040d0365090070010f20b02400400000c026080081024828100c80540d9400f913456455501c0505e40c1d050b0419550307102c0021a04031400b40305d200440300342c0d90240c0140303003280201124a9509500c6405404111982c400d181007070f42c0702c1c5010681c1441c600008142e11600c0288034513000c0c100301c103540d4691152038505402e2105035404104000e05050f21801c110207101064150340e030345400c0142e01c540290504514101d000e0088000a00c40011882283c09180c000f85115003041e55040c002551100011140c04c200325840042c03560084003010442c03002040500802503862000240034a003540d003041c0303041019640d04010611080c00e184c02d001d101c1c011200034100a80041c0040e00b80840c3c002c0c2003c3e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 995434991 1250 995433741 995433749
    0x203070b0a021e0415080c070c061101020c07030f050f060108060601030908090301050406060e0916092a08010501020106061701050103021b012c0f0c130908120f060a0f 74
    0x740c2d0014504009483c80020181045043c075a0300340c4640e2209140707810745020308001408911b0101c0011800060b1208a41440d5442052101105d1402d0020344840c07001c842d0410655401740711640c45100200318074002540a0809582010828201182800c5040c2190340c0070380c120354014072180d0310005c0e0070340d003091003881d001551095038140390406001e18102a640742d42000309000038418503400140584010040502143c0c807100e400c243d884620a090304402c0501c80010030106e41942e0214103900240060903c2c501a0186044447c5038200705076030107c1c001c400188440d5909100c0c0c1e402412541c00c2c28a80b0300c14104102c03c0c20030051040d58101900064100c484a01002100c445400300500903c056007804000c1c00c2013400240305254915600341c400c80e9105000107000c0d44400615001e0700059070002c00340840c456001300241c00b40740d124140200090100801080c00421005030b0401c10300340010007107080305014060620400b0448414802c504805441a04803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 995436241 1250 995434991 995435011
    0x2120a15140105070c0e0f1305070303031512050f010506030c030c0d030917030705010c05190c0c0b0703110706020c010207060f0315090e072705090f0f1605010203070b 74
    0x140c0041c00040b40c00b8800e501006120009500e00081c0d80b0700c0100e0303028001c02991070b5456040d03444070001e1001120020f0041c0940d803000780100701081c0240d10034001e48818034900400c40f81c0b02d0300001c0381841d000350200c42e9980094005200124280700312a00402c2c110090100850070340d001a80e01c08102c0c9110f03100c2c02c4144030100030940210007a800070180000c400c0d03052049002c0c003940740c0c1c01c44181500d4550804030000e448a10800c1110101c0407081c00aa4950380341d100203e8241160540484188000280206655020390301425000e0311994a0700c420304c00101c842d40c1230040652011007036500100120805a0300480c445050758203138070300328200861208048015003c500300100383c1c8000140e000c50a082d01d0b03080706a109034110100d8403a5a074a410f90099500705044824070b41c500d950301c0b41d1001100380c0000307402c000c002c011900d0443c404a03116080000f9044001c005038080c800300c2c03015080000322213000b4002400035508251481e02c4800718030000401135214 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 995437491 1250 995436241 995436269
    0xc0f0f13020d021908251407030215090102041a090a030206030a0b040606050c0d140414040f050a1b05041d070c0f03020f0c0604030f060209061c02120a15 68
    0x480300c16030507514071241111040c20f540040700d0740a060040c0649200301c946004040900046c034400c00c0e040c490703c5840c0d482c0103004601070a0441680c008034021002c40c00ba82091042048121b44a10302807411403000580e50f0345405400c2c449a00640204142e101085c0020840740d80d844a0310b0701100d40688046076666140c0d80180001c0503100203035944103140500120f113035a4008050611151410112600841504020f80351414550140c5a500c2c070708010034005c0751050644014040c0016001007001c100c00c11800d400e030f031300840310114080c4d5a101d51038160191045400391903811400c00c5840d0a0038920b503403410944190000d051042c140000c03c90032031140c90100c4506800520100309480d0604d002074540e04002086030081c8a001c8115059280400458045a602ca0820510340d10300d540c0c2e00c8060b40008075060741c440c4090100720803180459150141c2400695001a07940140d42c914001c0024090100c1d5200e614044500208550380c60078801079440071040100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 995438741 1250 995437491 995437507
    0x30f020622030f030e01020a0507170a15051e0f061915020a0302010e01110d0e070e1816120f020604120f021203070b1b0d0603050c0f0f1302 62
    0x3915450055015254002450000091041c03c1c01c03501140380c402e81e1a0456844103400490340c3e0341ea2010060502d41191800300f1080d10f02150001400c500c2e0000d40340590100d49134584403e07a03806040d06007031344070001c01c5880070010300a84c1c0b6603c161b1039001c04504020b070314500e8014006000c0e41c044d09125051100403508440428020b10700420710390981700000c0c070025115108650f08801640c24000740c03130610b90040c00b0780e41120000380a9181814800d15107039000d0400d1900341d074114003e400021134984c5060414501c141c007045000d03108010450281481d0450b08244030a0410401d50300780030040180e82d015801641001d58409000528000035105200320b0b80301c911502401c510307400030402501040b003150360007100c3e5400003001101405480f8403c1120003040ca82c01d4400168040c030880c001d501c0b01244e4140d1450910100707041100c1200c81c42d401c00d0b0360650182d10010510b00e800c10007043c0d03600058810700700c03019500700031800410844100d000345503004180e5403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 995439991 1250 995438741 995438767
    0xf07050a02060304080702090604061809140f1524130b06180307080703120818030403080408010515060a03410c0306010e1c1704060e0a030f0206 64
    0x200306400521550352400d261500c00c403541c0c8074002c1207000d0204e141c0000d0281c6003034070400b01250040c50718144040d40d00a02200105803102045a02c82d80001101078110030800c928080c0d00c1d9100002c0c40c0b00818940044001030000304110355103038038444498580d50001180c0922004140d4002c4250b000c1c1404900c0580700310f0194940201010030b18011070100114995556203081d400e5503000b41c2c54524840c4c030760003203010140c11442000b000c80005072180660319804600303003903501c55940c19402d1046c1107038050f40c41aa000000800d0a0003604420701c01c0a811a58401c0c0e1000030b000080302040c10360107507042090a044c0c5c0e61504260ba43d00030410004100c4003032020304c4a4001e150000c8445042c50031100c592540ac0e400040d83c003482d124122409203805131199262850030304104001040b8079144540c010300e00c0008940040d50524070f0008080700940301d0742d240c42c05c1c400020941e100c1840c8040c49414960f104102144142440b005402e8041c4c801c95034604c0151001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 995441241 1250 995439991 995440003
    0xa020a06050f22080906130806070804060605041506051c02070c15050a0927140402240f0f13140a0b030114010f26190203010b0f0705 59
    0x902100d0804080100c0c2e00629050b85101d00c1084107a40c006040d1681d90040c119942c080051103c0c4080003040e0117807402c04050111402c04485100307001e615010310600740501518284042015034051100b003100a01805015100540d0708200040168100c4106003500d40318240038440300040c002c00c903200d0084000e00303101c0540c00030b40d41d800d65440c14030203d890900c10b928a0304655045401641c2c880c6d0116401c90040d951520a80e40c24028000d800f00b070066010340d20541000d8484100c060701d4080c440408526140741002807610740107116040c1000c0d030401c4a41000c0100d07464000003800183e568021082e2a000d4403150a101074501074800d800d124100d41c45500c00c0000c4076944505c00d96a803500c259845446c1c1aa01c5041100d00c1c0030a000b1422064010302102940e03521075042481250b11514110b01d111780c00001c00410200004080d8801480c3c1d0010081940900508500060b41c6040218690b40c5041c500703036824025545180000c40d000120740301400740030840 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 995442491 1250 995441241 995441243
    0x14071d040603110a0b1e0a0504120305070204141e06180115020f0a0807020409050709020c0c040b03061317041d011509050f010521070206010305100e120a020a 70
    0x82000141d440f420540d03145203c102403103100300c55416000c103203c150035058440ba10b000d400a18903240c0034400703061aa80007050354604201061000190818203d120b89481038000e8441e10703525401d074010300c41076a0f404515060728113410030901252030340c00c43c100e2510b5003c00c1034802040d01c541c800950f1840d50b0112500c1808601e20001c9240078034a01a0900301c032054007111840f80340d010190740ca03011018401f50000d04180b00c0c400140c1070035000443d076682301d4003d84502ca521030320031004036000103501c01c06991003180100b030181014071030300c0c84800046004050600d091a441075a81900f0b00004000424410080d22030360500f50079640640102d41107a09640720034030580955401c244030b00444130140220386248107018009010030303100094103130003104100c54010b4941d6401000440b49000812840304441c0603030111160080901c0c3c0d0240059500d1820030915008140c401c1c1f0010310300d07007944021010700010b40070081e11316054445407038111100d81a810040c200c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 995443741 1250 995442491 995442499
    0x4020105030c1b070e16020c09040b0415150512010209062a010e0a0c2c07051c02030f06010504240c080c1509030a12021e040303030f060914071d 64
    0x408600c100003505c07001d2040c02000c009031401904184101e98413a65400b00d5034001601101040100b80d00c400c140340c0c82802016860f403185003c444c030004481c1182c400300c40350b90b255181800a0b14211112903140c2403002c00079420145400300042c110710403a80080c288600242100811503550598581c01d80c01c07200080108001c00303140e69440e2100100101c0e500300c40c4510210303a0151b0504100d0340c030020ba06c4802218221107040300e8026401800003024410b050021b40140c4002e1849509540200300d009a182c0c2000508107064003005814141480810700060040091074030b50811100e0342c080d104030f141c104a1405690615900c000a0984200010181c0e020350001030070b03c1d070803a00c1d82c0c0ca100060b039900a4160702c034015519814009032016150000702e00d400d4020388091a250050540340c0e4400070844640c030ba105900460102e0348070203000c1d000c108244900b50040400580901c00400102c14219134004000c0a203013300c8600d007440200404001c8980354001c4001e4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 995444991 1250 995443741 995443753
    0x1c02100507051c1e021e01060e01150c0308060a1208030f06011d1e03010204030b010602070b0a0f12150b090909030a3501090501090f0504020105030c1b 67
    0x500042032a44999020303074031440b420f8000e111681d28000010794165a42c0d80f459649140256501c2c0c256040c2e403026801c500c107002c0390203a00151550b1251078205400c000080311443e1218000e00362905900c860180e44104496804850300000e03580b00e115030502d84a0029030300c910024402000340d801c0840565a012950801c00840100460003181801080d126960f95240111202da00c43e070150100b009810a0380d041031300b03240003840071485201e001401c01e24492008242240c2280d0720541e134480d07111004000c096014000c65024002030030200346000a44c02c0d028002003692121034080068004c21114001d0103640007520303448910550780e00d410390b200d01459a9410115072584075006410111308120700020440349905029220b04518060115158100f0003d6103014803028107603d070f0a60722142c410880303902a1540000010b015410104080104c2d804030450050885c64a000d000150703801800b0340381d010360340c8504240c1d00e81c95002840050441d464200801d48564 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 995446241 1250 995444991 995445019
    0xa03081b190201020606030111040b0d060806130c060c0f0b06012006070e06040e04030503090a2a0b0711060a18030c14060f07060c0908061003060e07060207051c02 72
    0x1ca600c0d03100c2e00036030844400781c540000709402c9909641c0388404001040008104442c807150160210003403200c00040c05603990750718103080101c100c40100000300304074040c0d42003108108020000c1e020350b1814000c900344c0750b540e1400c6401801030140c01041d090000444d0382e88035056901030070101c0b00420aa10200312030b041d035038040a0312640b010030550464030655040083c15202244d1a18454005075201c6813010b84e0f8a5002802c0b0503883e02464403684041342001381e40040441c000301c13a0400c80c0aa042c00b0507945401c54204900300302081226001141c501034080300c164a04403000c0342d40b011202002c0d124082c1c0404410300409071641e001040c0b040c0380c050030040310310800418610074030810410640d4401e0f1034100f289500c0c10320249020960507031101c8030101603424510000703030309da4010a2030088101c5041003001011341d014010400140101c00411405000414034a03003480380c00380d12156a40601401040c042c20030f040c2c10b44400540d4000140c000d071403043c208030a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 995447491 1250 995446241 995446273
    0x102070e0f18060721091b0f06140d11130f050103200910210515030106030f062027010509100e060706020f0a0215010b0301122102010b01110c0a03081b 67
    0x4031380310303c0100f01a0350b231000a18500584419090100c941140361a150080c0c420500401c00f408007412408024081011010544206000a400400e000d81c261910303020004003503034628445040c11200c41d040b1003101283d03141c10384030100021a200c5c0003005c2c00341c408440d400c0310400004001403d40304540c0c540403075944907078041c8094201c0303405042010380a042c00c0c0e901900c03004001e641c90700184404500c0035402040300d02c800e4240541501600e183d5540a0b070003000e00102d400d844110102c02c004070f1090800240c0000b800c1490400512a00040c05540902506414001503a620280550b50f2a0807600b034941d019904644840300d0840114332900450308002c054400e00100c20022400750702c00740c4c101c84c080c004540c07450303080000c02030741c03c43e8001045854280806000302d02902d2045070411011143d800011181d024000050285294980c0006103400180f078020680c3c80d402040020390f03030041581940d808201c0f5040151040480c99050180100d03403001c01d290807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 995448741 1250 995447491 995447543
    0x30c05010f0c0305060f0d300809010513020604260109050c12010504050706050a020c100518120601060e03030409090302032a0604020f0102070e0f1806072109 70
    0x100c0e0355000c04c01c6694020074000340103c0802000d0380b11000305451000110780b21200c00072034030781c3d000440c07a80018907aa681d0358601c1c3d24012021542c02e004001800a00344501e55102581034070408003c18590007080340c2e803096004400190400c26a800c002c80050140782444c6400007000700544034540c06d10310307211622061154800c482d004034216000c41c050060324084d68102018002042ca09101a10a644003000000641c0962800018aa907991503000d1a000c500c0e100e42c0d0341c45400f030078195200c40c0c5404102d403041241c1450b046442600150751419200300d410310100b0911902c000074070b5405641d00c0a207200c0c4c2002d0318841059400b00c042c00c891100310f0700180e04815540344c00c480b0820081c9000060742e01000000707015103046080c00c0300324441030064501664840566546c1544122004000c003600d000500210b259584010f00c00860074101411050504082c024221802d8070400d5080b03a013060b19040c0000020381c000c0f99896400000781c030a120010302612001d032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 995449991 1250 995448741 995448761
    0x170307120815060408030405090f0c1914030718170304030f2406030b10080a030e041d010e0d05090102120919030f260a03050907050604080a050c04060b04030f030c05010f 75
    0xc01180c00b0600e00340b03072b10058500900c07507040d881c0e0411441103584a01d21a400c0300807400c00c403140c00760034186000b950041d801500c5a0b5500d280c545944c5485100c0304246030b100f9640c030a0031044800c0c0c411b10100550782900d9000c080450100403d0600804c654040841c40442c1c509020130fa5940029550242003264403680c4404015601ca4403c02c51540145c45442d03056002100344000083c03042d25a100e402500920000300c6842c01031a00780109a21000990542c2d514014103000640070407032401079094034641b0526283e101c100003515500000c10380c41095001080044140c0e4810055100c2c1424035400ba840e425aa4144000c641d54039000a0b204248525111071558080031250003400b040f020720301c2d2900c10000c4c0110001d107001030903c255402600030110f0791ba52880020f0004000d10802818014503504010341403c54003421544280c1c644a01041288039a200740c5048940000001801103010b0034140e480003900700e0001c0155207001e8490760f0003419544015901 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 995451241 1250 995449991 995449999
    0x307030806040204030b1302130507180b03040c151704030503150f010e0105091c0f150c0804020409020301020d0c080118180b072106170307120815060408030405 71
    0x1a12048240401c84c401c600024201d1402c02000510901200c0e25002c1e82901c080c090842e86000d603d200c00843d902922690b00003030240e14285003180b403640c0c0c100003500c01c0445040c590304003507450180302a02842103045925200000300300f035600607406181000c9441c5507001d00c620b003074a0000d0543c0e00486112414180130091804a810103000c074054040c01030711402d080b9002c0f03500541c2c0b150062500c680c0d00082c9207810b5842c2c100b01c2d8850106542c40b64200031030541780381c901031520480320303503883d0340303061801e500c450007a40d20400090b006034040e24001154005400840d000e441000c400040c21030422407006001d035070246005040f071302c4101d9412404001c4200c0c01055a40503980c03e10940700e06889070300411004040c00303400c90001e0812040702c045000141403a01c01848140c03851a55400c0c0c1007160a80313019492101070343c400302952814149a07210006030b80c0300c0203401c00b0840007a000545024070351940c07400919000b0080c9480b603642e0a60f01d9502c0d0301c2805241d000e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 995452491 1250 995451241 995451257
    0x50f0d0c061206061706060306060d0e010509010c0503131712070c021e010c0b0c120a0902012307032a050109020f0103141501030902090411010201050106050333060c030703 76
    0x41e038810042406101d510000e0400e503500c030b05040020035000900027991199041001061131031441c0300b81244080440004900c51614041d1142100c0b1000c0c2c1d60700501204104000040e0403524004040d11340c024014090302041c1c0c024113180b40a50840e03501d0301c801070700c2803083caa0f401c0340804806a02c225117403243c05080200b04802e08001e00da001d40032400f0303928100b000502204842d40d1140c84511410b080c0303058465008100c10080d22100a441e5442035820290359000343c4d581062030061007443c01c00030a851a080061050140103820481e0348802000e61904a98070010782c800b0b002c4486881c43d8080c20318500034480b6400403449075403100b440408550281c06408002680740d40c045a0070369500030860042048000b54504250340c4e450b40d90010b0b0750b1a50201e000750f0145000203010041c840c000ba08440e01a0450800d1040134420007460f100c48150404400071402954a134400d1101c051089030f176918031005500c480e000c604800c1003080000600b4000b8002e6982d840 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 995453741 1250 995452491 995452499
    0x2060318101a0924010e1329060f0d05070903120f1e050a0c050a0206030703050a05062b11060f0309070f050a0918020904060c0201140f01050f0d0c061206 68
    0xa20061300f804c0a24034403018408130443d5600840b060b07001000d010340b180300b000d192010345000300c0340c0010844c22001260040d10350712070000c03004480c0704c9009403052845c00c1c1046802142d0f0307004c0c944500707880b01d03111400500c0390b5214102120045034400140411007404040c084c060071500c0007290300080c00c419042e1045c904032810038070480826100e01d40b41441000c000c03506008800c0040d1100d1052000260068940c0d800452080301c03c0d550008450400700b00c0c1e1800d0340e5010301030911451003422a411080d0b5802d280d130f4140107582503807130804691803500d0b800a00040001c0c41e4040b0000c0354040140c0d82140086128030301b005d068400d020b48910002c01c600e240c500640d600718069580c1444111907503840113040801ca030310300c203109240ea64001a1030a03c111400c49103241c941e141c0d40b40c00c940900a82d944070701014158109860802d2100d2810300d414454a0b206403004025482c880e218001d001420503084042400c6960b00c6d900c0140c506054920f0940c840c41c17070321070005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 995454991 1250 995453741 995453761
    0x210c0f1701030f140708030a0906020d08220203100e0147030105130c1a120a0b0909011a0a05060a12110c0a0501060f0302060318101a09 60
    0x21980880594000150780d00b0768039030b030709902c500724012258410342c0a241d250440303080000d01c0007081d0300c0d0002c540d240c05050380101000c0c07155109005541c080c101c0310218a4000b20ba1a40c032501010585240d441c000c40491000d42c20031038041d4050281505100e00034800d600510140507945c4028001c12107000b955507040400c10f1250002c2141c81002400358020f626040100c550030b1202c0110001500c4000a08449003911509840c2001042075801c000b00022000c0003040040d0700c4511041c19050620800d01c41c0151564444050100040e100e440940c010362100c2c0019140341c54a1400700303c240c1c0201540d81c009807013120061807518851a00181c00300580e500540a1401c2c0425000b06a441083c1002038245194441c0d1510340c003d1118005401c0c41d65040006210400040c100300b400c440054006500410754000b0500151704c1d010221b0b60070000c40c6084500c0b210500b90035505194098440700c2a540c2000d4008200c4800200d00d6246070301c0c129208000d81d11352803041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 995456241 1250 995454991 995455007
    0x1603111905010f0c050a06110702010305010b03010f030809060d05040f0605090a02151e0d06090506060a050702060d060f0f03030f0e01020d0c0203030d0207050303011503060305060a020a210c0f 85
    0x42c0015002c3c425072164900c01e15a851107070340300348200c44020300c071a52501c081d01c1c0303a08064003040740081072000540da45400382c24010400d030800541303503505041c40003c00b00118000038000c01c0c000140030200d0788a0000300c561300b030006c0320208003608083c80c01d03c0140710165015201a0309100202d40594004034019010981c02441824a000040b11001d983e0b00103554046102c05100440080c1c6071822008110814403401300003007a90500091604459010308040d000e034105022420015410100f2507401c82d4045414cd40c4503002c040c03080d40034140310b42211420000e0141c00203120442151034070103403442500c03007408007500840100e0f46d0f1000840003c1c0181e200044446045015000c0f0005290001c4c06680c580400882c00d00c0076a88400c9044440342d01c000b00400c07120704070083c41c2036400c031149410701c015407841d1120781c1e480740c0140110007001d9001a0700c00e07031140105140025442400c5580d1006082850303120000d126010009001c144d03003a40038110940f18440c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 995457491 1250 995456241 995456249
    0x50301031716021c23160f0e04080d020403080403062304080d11070c060f02060c18010903300302043b0f01030c0b0a02060609040516031119 62
    0x8284848103a03000c201d041c90b003c060006024203c0d020726404551740c2c406200308800c4034a20480c440100c08440e5280c00e01038120201100c000010502001c4022882c490840d03c6045400400743c4550400c0801c07407083e807805c4492544000340000070070071507402910882e801034004210340320802410001240981c288080070520001c0010300107146000030340287c0040c0307030001540611015010100354000ba02c1699044100326080019561080d01d049000d600d52000d0702240c103181c8040d100038064000400c07001c14000308900002d0b485001c2c403000031500489a4840480607103001081485002829800c0307020310306a00a04502900850301181c09521901200640201c038076240e6200000080203200f240303d22071603a0195010401c1c0c02003100144401d901d524603d00182e6001c1558442c1480c080c0602c0010507140e004030304680c3c0710300142c40310324403596030b13281644c10400304100c1d0900d106c555100100030701c0111b103070860035450280c8102c4c061402e590281207503801c90348a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 995458741 1250 995457491 995457517
    0x40e0f0402212d300a081501021207210201020f04030618210905030615011808061608010f080d0c0602091f08180601050d02061201060503010317 64
    0x908006080c1c00030556005925010084042d01c01c02c112500e040411050380c3c0000e03c80c010280141079040413142e03814039044c0d08505881d0100b2070380080c0006900070046082400c1003070444126034002e1040c50010040803440540c1ca401c00e02d441d4503180c94804d45044c070300d40c00610305500e160051084034018800035010a003058915582d11300034040d6a446071041d00c2145030034400003400703030105504035020f444408026400e034800007002c8001a61219100c0e41c0400d0074400503200c100c400c20060710003881d14814803104040c0c0701d07600c3c0b0240d600c101c20b1846051b00700700c060109882000f550208540c1c603c28266610442440a10300301d0091100540090f611112042e005042d16000c5501c541c0000d03042102c0c400001343c1854100c408824800c1180c0050202950b01031892039100481840d50b981c444001e4100c80d540b207a050140e42c3c0580380030b0110005640c4c6040554042240d0000040c49a40c0c6404008005410a1204603910750100d01c0300c1030740c06240c5041e41d0a1445200c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 995459991 1250 995458741 995458753
    0x907050a111f09110d060c02060f04230c120d020c0d050709020307091a03071215030b190207060b030601050a0b030a0c110607030b0111010926040e0f040221 69
    0x70794200014043e20100b140c0101c0b10303020040c095221103800024540c0100d100140c22503041c1c10103400e281c0010070601c51f9020f8502003100103640181a01508016a441950f00d82090a080d40c40c1c80f0305c81c11000c0e4010342061101d42460b40001d203880090a1179400d440300f0030302030410700481440d01c03000100035801848060210701d11b254003942d44100d079498903149503941e4120300302591243e00080c80c2140c070b001082206858014400c0500c00308406420440b02e00002200201c0c0c0031180801098404641c001c110f000b4910386070184003210542e0115541c1c051894084000d10340181d00c079000740625000002c5a28117000c0b201d00f220582d60030240b542d038400c20100020040302c00d016041c4500e4a4075111301580c100100ca214908648000a00140880000d408161651800d4800da814034031541c001810181048103281c2d842030710280784001c1a515901c0e079004a0700101c40d030340c00140c20001508000340010303000f1802602c5104051150580000020042c0802c68040e80d00907 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 995461241 1250 995459991 995460043
    0x316060c02070b0f07030206070908150a0b15091003020f07030f0c0f052508031c02073503060a030b0a1b031a030601031106180907050a11 61
    0x103811005000903a0310554504035100d07600000550403450075410304440100f91801015010406980c0111a44c181490010b00d000c4080717540b0340c80e01001c036560310450310110710480c0707043d00f01c0481180c0041c00140c11140282204c2c2241d080a55118855049101880d007014040d108648002d002c0c0c841580c6007602c00d8070282d402c107850310f080d041080400c02c0b41502007030088100c0c2580f24880c00c05010f00d4085c840044135200c58140c400c0309482e0382c880d03080000c06c2d400021215440b52504e1090003000d02086040700a018052016000944401000880b00c010011a003003145810b0351450406160040401c20380c001100c801d600120369a001380040303078200e6030040c3c1c00b20740d0900110380c0b18801181e00f540d04c84005840c40110341ca8101502c41030f000ba800c4100449820f074020700f100d41c9944c594040c41d100c00e4000078050070b00041c2c0081005a00614100046e001808030080b508140d50014001d5028032130503c0002d43c02c4454040000b00400d0104070b08100414180394a104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 995462491 1250 995461241 995461253
    0x501060503061c06090308011e0b0d15050d110a060503090307150b0a080c0102150f13020a15080402040b03010c08070809071205060f10273b0316 64
    0x20750500c102c24154404450f800003001d500030801450300c079559481140d45007480159002c0162004126a0f05a0500500c0b02030141810358024940740f50000c2009035400f1a8004160714075008950030810040120090010b0400d09072000b01e01034503213503074550b9a5101201c2070f00064a819107940c1040203070001080d040000e801d04d16280e594001005107450b00080c113040b9066008044541015030f01040560f01400342020040d0308101d0b1003690710b0a90140c10001d2030050103410030b4080031041c2800e6440303604509010348240101e20313842e1030702c040001c0d0400c0e40443e4224400c50030170035815028101030007140103044140c0c0f0b130101d40b03132280042641c050300018494006032140500000b2805410300313401090314082c102408441c18103441c004902d00300201249400309040904101c60303061808170010700c03003d40000301c5540b4188013000b000f130701c048014551000702e408134903129083c16681100e01c010080340c50400300c5031160201600c81c020f050f58545091a408003080c04104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 995463741 1250 995462491 995462509
    0xa020c06031014040b0d05011d0c0d120e030f06060310021801270e09010b1008070509010909050702060a0c02011104050f030304050406080d0e0d020d080c3d050106050306 75
    0x10024008a5441012404075800001b84002035455a4543c950001c1400c0d4541094a00382c0710f41000d48854040d03480461814910741e44010020f03030a070740d09085e00c28851000701071803800007002d85403401c000620300c0303554200980740316200f401801c1801142c0c0c403c40c803c0355403c01d410750001c05c90342c1d811750054580001c0c04601c184c030b021032007070610307100002c0003c03410140040e43c18210160410501450031541030800850188aa200710811415000071086500103400e180281c1d9545411004807104422640110b030b1550500c000d01520540200b01d0038443c032000d1004008150241d44224227881c1448450340745035808200c14011401c0141841064103000340480f80380951b10000f0034111059540050180c3e0403150740640115486144000c0102e0126080100c480740d42e0000f580001c2010002010240700003000908034509000c0001c0c181551006212148000c1c0e00d08222403600a5280c414107408840003e038000846c403400e8140c0c1c5a9907202030850341c0300740500080c02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 995464991 1250 995463741 995463779
    0x90303060d142104030c0b0c0705061c05131a0f06011b140303071103030c0f0901110a051c11060403200607210905060f1f0b0a020c060310 61
    0x20280f410302d44802070640c5501c0025054040180c3c0c0c2d41c61440c02c2c00303c401111382d0407110340d08504100302500000d000844100303840c0d080303804540d100003c401d540c404140c0c0ca03410303a92081c246000c01c0b1100071f4480b50301c1d141600130402801c0c002c012190510030080e040f030310030010080003008110300c4c1d4030070340d25007140c114510798440c44900640c94048111203001c190003000d501c008100f003e0701e1743c010045018401000011411420840d07006906402020904012104040b07112451a807050a0800310402c00c003007640c01d5051a0300306181c950242401129000c05030008030044d5910034040c01e01081208800360440382c4275503804a4031101746c0d074000025559a407008040c0284180840d074003d04154079002c0f85811200825102c84000680c50f0045628040401010400c042013160703110003801020040c3e0b0341c40c189815030f0000c103400d050301d4061b0715100204000300140010900c804d125000c86200d419904100b0180340b100302e4190094450b440f00c01c000031300c4080a282d51035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 995466241 1250 995464991 995464993
    0x902072303040b12100807080303040f020406030614040b070903020904021009031a07230901210c080414070302061e0405040c0e0f0f0a170a06020f040e090303060d14 73
    0x4a56103503840c04164021800d103694030700c14881808008907140c5d01d508024020344018028080c6840380341a12400010000b60070b51640b0000c560842d502c2d03500417005150b10070004c20008404568540103244201c03021030b60081e0881c0440c51a601030009082161341c01041d01c00141d0346d60b400e00001c044038520106c01c2c402c010b6400700024042d0010301400140b0102502124030b4201c0006200c48035202800e403c410030090003d90240c130000c02c40385c0001003820043e11401c01c42240740ea100b11403001441c1c44a2400318100901a48004036074080d0b4042c00c8800c0d2202c03102604140c03200c005201c02584001d041101030301b0540001d0b02008044013507c1c0440c281070b0342e400400c00707031140030340d14a00181481c5540051850b10203005018598162441140c200380c400c04950150f065000300c0c0c0480c5030759011003444480802030104541d43c4520107545980c0704c00d46a844540007030080c3c41e1000071000000f000c1c0c84001090307034400d280c003c0c41024100d500d43c86420011414090701207003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 995467491 1250 995466241 995466247
    0x91a101128080f130618060c120c0203070b0301092903070e15040504032001050c0405040b0d020316051c03020a110d05060412020f01060510032316090902072303 71
    0x8aa10401000080c174080c0c88003825200300d001d5015554245800c140c0a1040840d20f01c00842e500c8a010703064041c184c1001d5149010600020b450241c840e07000700d09001d0004000b186040c02c58001d8200641101c629000206128400701c94000e0a0780c80544c043e40103450030058407401c06620340e00412140703200d105403c100c401180079200700316805c0c0d005c66a00101d50080d0400107241084c030b47c010f400200a04e0a202450101503c00d910030f0510440d2074120000f0702e41d981e0700e41943c94a070b0042c101d400480d002e40c00001080000d10a4034030444460b0762021800445036540e0010355070560140001003030590701c1c25034482e414010780390807004603060b8100141d8200076580c061030180100300b0800201d220f000703180c041d40e503400d50b9003070741800400c02c840d40f5040400740740030b2440c5c20b01041001d2007500c40180300d00c05100c0185229405000e0103a4440c0209a062810f0311075035480d0001900c80841000741c0c0b0444800800100074003140c554410031b19034500c9018000341c0241e070f21b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 995468741 1250 995467491 995467507
    0x90b0310150305061311010e0d030f02070e010e01030c230411040506120a051305100f0e031c050a0902090a05090c1314060306010f091a101128080f 65
    0x442c0a40c00c41700a40c00c03000b50015103041c0300880760302110350242446e141d1540703803000c00454900180918000c00340000b01008203078060088c030020020348049206480303590395a48440035500001e100075120042481e0b00032130359846c141c41d440e00c03081031401c45d90251081c080c1071000802413926003205030b00041c0700110b102e985003c024800d03a040030071880c00a00b07014002d01c04031207001d40603803103422030035100000003640441d42d048003c44003680012850540d82d500c0c809413440ca02000003d000011724414203950800d5040702209036a0001c100320307920700f103080040f5481144003a600c0b00c2d04a00040030440d568020984c44039459080d1421148030401260320318008160001c07030552266460008003000015459010344101c00800241d49844a0246407800c0c500542ca129070b1240c00e4101a00440d502c08148684003a00340c42c00d04c259140010600794103510362144502481501e0343e80444414034100940820080e1380c40060201c1e901c2ca90507030320030b4440755400c1a040c00700e04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 995469991 1250 995468741 995468743
    0xf030907030c06050909160f080a090b010e0103120311160311030412020301050a05070c0b07030b060a080108010f0e03040612090209040506040b0c0a0c2013020405010306090b0310150305 82
    0x1001009691034851716002c4000c00c01100c800000d01030302c0c0105194034008282c6034403030000b0021070282c1c104410a502ca001c040e00c05000000d4002c2e2094100d140001600113032240139a040b68002c940240044d2000e050840c19a0f44141032211001001e20004800508070f940d10106940309060a50740520702c2071a25003550010f50003031480c1d640164540c5c065003003e000d07456010b01e0144007003000e80b6240380090210f40852201030010f881c040f002881d0365000350711128080304014541500e402c1c820f1802403503100c00b405101e429508200b005000c040300d40c05403003e00e0001c107016504060412800300c07070383c541031014920a2502c40d030b542e82c003586850751258080c3d80240e002d802607182900f84400080d4020340640b801e814108600da41042d441503c40411030b030700c003003000c00141001c40c680008032000c26085138000007403000340540032010b500a00480301c0070f0b20144420756461690b5004c4854211700ca507015001601d10380207011580d070181e100500780780308002d02c00b5129115a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 995471241 1250 995469991 995470013
    0x18090f1b0406060c020603010603380427171605010911010f080604092d0501112107110d0201050106080f092a0d061b020609030f03090703 61
    0x80d180d000385642940303032a81841e00400000d44018104540401070641c0814480d210504c00d41d41019500d504002100c0300c0302d021004040c10604020901442e0314004070800110500c0d043e10682c601840011800d034084542070543c50f040305402c1c0b058410703440e1441024142a0314140846040040c154010030340c4440440540c0030307100029400e202403a00e03204446414a500d414891a0004010000d0384076402c00d5022005480201d0055002c1c50090300c4001c00300402c1c01109101f0a07090408400714420b00f4500d40140000e2002d0f003880700f8100d0702c0d4031854096a0000d00300001c8604180fa42c000322a030456024a0002c0400c00c020540300d05080d440b80400e00140d45890040002960000d01190480c0202c0e10b142041d040c000c00e110350721000c402c00041400382c0c5076404161401100c8550443d0040902092030a010500e410001024144016155140e0780103003042450704c0003036402c1c4602c503114000d5241210b803980196240e00014003c6426201c1c0450101c000703000e12070b030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 995472491 1250 995471241 995471263
    0x3120403090f0f17120d091e24050912031b0301031b060302090105070f030e090a06030309141021090602030910090804060509010c020411220518090f 66
    0x4400c043da007410148000b2400d24011041142e1001d40c1c000c1d04a070400088501001040400040c0a9054035051800a0a196031078148400710380894050046506400901e1039101c0c50448103400c0c00003203107040311426203030944154001d442c0382100c100392800460f04600154190500c58003501c0104070198001d07007040300e0401400c0109a900040010b0440c050051410b0641c01c08081c0d0000030554051428040c1852070400c11800c2458094640711001080180440c5d01614202c000c0c500940490721040340003507100480020181028503030700d0150b402c0101031444107148604112a40310f19440360000004080c41c02c8107080c0c00ca0701c50300700f07003510495015032285400c0c5426801d021012003180542810804980005500b2108aa007a260075083c61500c3d500c0500040350000b01c4124025041780c42c2c1800701080301000b0029152024003613540b12404103035100001407400b103500c20186c21007800e54010304100c101050465114044000700e83c0c0c40501031902a10f49000040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 995473741 1250 995472491 995472509
    0xd0614031f1515020f0637020d06080115060203040f0b0a09080102030a0c1d01080a050a1e150b0712080a0e0a110102070602010e0303010e04020f030d052104030203120403090f 77
    0x3c03400085e26051200c50b0340400c20b20302c0b4440880d054140c0a203469003441e0410f504000642c02c0070b20001942e1b0544a1410040d003040003001e4440d04a07e008000d042031341d000800ca0380e80001400c41c800803c032800d4a10210946422a00e0305004007026040800c840c1c0030710810040120703d61b00d0034405584a10040c800101c0d542c94a0314001d003801189404040018029258400ca166040b028103030b04040c2c0d201000800d40d8175244044010101c0610007006104200c020030013804480c1c0020350600d4807825080170365a9240b00c0e4041511171104010402d100e45138801807098020044c01d035100441e90380102d0070002e030030242420700c2e01450040b50601807070300c0c680e01c1c6540d04016142c0980018002081030306185d500280d45c90005206080c50011290300150864650f1000c4007004600a006c0710360030746608801400700e41021189961200c02c08000000000c0d4030845540540d826401451818410008996000380000d00035070070302840440010301d08899845010040c44000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 995474991 1250 995473741 995473753
    0x3190318061a040b011e020111130e0609040507090b03100f0e060a05370203010b120903040f030b0a14071d03010203100b03100b0d0614031f151502 65
    0x35480d001001078800042e8003541ca801074484803640c2008291910b42d250400d50300e032408062104a0140000005482d41c550f000325501211a408260b0b8070186c894034041e0070803680e5030300c0a1010018003194068046e84c480441046074020310760140312110400f80603500b41d440c0030114002a80c4007514840c02c1c0e1035407090000a6168240941508400c4280e410320150810303d11900003414042c0c0400c10622013100079501d5007004554081d403040741804203548a69503260503c00c9030300140c6000c03001442c1c001c0040c100607004001c035415225800344030300301642541c076181c40c9000000d08801e6041e6448000721004800c24000c0c1c5e11840140e92a0b029065425588044011001c88023501036801070090041034800d1040b484281c0b110307405455103e030754190080b0490f81d100e5000c010114000550990b001881d0b8104205407000d0350807410340c070542c641c2403680d0341d01c0085203299699846403800d102e0203810742241c1840b031403940d542c071a11521070541e0b000c2004d0314500c40d40507911030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 995476241 1250 995474991 995475011
    0x1f0c1b0519210c0b060f0a090903050c0d08070215070c02040905030306010e0904051b060f03010801050105010e03062e1703210c040e0c160c17010b030319031806 71
    0x200e800b03054041001d181409450700d03d6a204046aa00544074031322401d4024150786031521041f8440c0000c00b0b11302800d2004c14010308000d88242e02c1100c0d811218024a4a610515070240121502440382c540c0207203071144d099140c0b08641e00d00540350700c0420416548030340159907203014000040e80240050b590701c2c207002001500c0320003c001c03400d00402079a0300308008a40003051041c0d102e0b60381502d0b8a56069488002042c0b4400c0c00b04008164a002c8008190001c05501c0760b81030310000c0e00d554030310401c464205641c60400300d038455515000030350780b040c03a00f9061010312030700401030401c03140c0345484454000c030520904030640344903800441d550000c1074030507010348841a903001003203069040c0690000c415220700c1c090300d0801504400070443e44040441104c4160780c6011018034408542c4c90420320788a071a21403804002d048a00c1d100607450188517050818030010015494604245501e02c428020342858105156540007900d200062031198907440d03030301c1004001001581c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 995477491 1250 995476241 995476283
    0x10c020d0308091911040e031303060b04110708030a0b060d09150501060903020108010e1009060305010504020f0108101707170f15070e01110a12021f0c1b0519 70
    0x1c051820750392012050b040e5000c030f0b0032204178440b03020b0142d9000ca001c1165030b429914500c50780c01c035130043c0c0c0494100007090040d0ba41c016003c15000b2a4188552054011859094010880044c00400e4200045a0609542da004010580300540f00a003000008920781048034001d00e003d450070210450684241c00052082c01d014040a041c2800801d05680000349041e40500401200c3d49080011544070141e0303400f61030080801e07420a01030307940c0b03a10308580606420744040b40960515182c0d22440e40c044e90b4500c1c414800021900302da240b13045030207455206464400c0302d07280511003022800764030282040100042804c014071040c1c1452280915100c2001c045a1240c14054144503040758840d80b00380318403000b482c1150101c07000c030b0b400c90300b4402265001041d4900c0c80c41481c420680104001e520040840c0410001c41014040c10b025650323202e001200180340d0500260300070003110300003450303070f8000d10841d0310b040005c03000703100300c42e0011001f81c1d440b4140501d400044d0503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 995478741 1250 995477491 995477503
    0xd0c031403120907030f080d0204080109080d0b01030e03190c02030f0a12020312010b0a0215160e0301050c04060c0c0f0b12150d030f0201090b0a050f010f0b0711010c020d030809 78
    0x1520b00800040d845c58079414014104c1c50001803c160000031070a005030a960103640103400c1a900030048484c2500e4103201c0d40d03201d40307041080c13103040c041403552560007403103520000d1041c0c00144d46012a598502070100e00700a1004060045c00c00603480542c40c1000b804007440c11400060403151030a041c4146c2440303402d880d103002c640c0704201d1904e54814001e42d090454a68025042c3c4a00103024180d003841036040901c4414101c4004100d0000580321031520303c1501c03601c034420305000b180185401d0341e9003214515483c940c10001006450701c1280c0c21415070f4058059503e1903900c4044102144a0316803111851100c0824400c040015140300c00c0c0d000a22411030303c02103c0c2c3c510215809081015016050000802c40e685003607000f03411140c0c0352603010000c2c00c8289000e05103180100020f0361104500428000086a00c8a11a07040b0040c1c0780c4092145050000e01d541c3c50841c000400c202d2030411000c0d41070700340181c40d1041c0c0104028881d8a40055a1500f0010103150034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 995479991 1250 995478741 995478751
    0x9170d110c150403090504050703050a1a030a020d0212060f04061d0607270b070c08010e060c0306061e070b06010216090906061715060603010608060d0c03140312 71
    0x4040116894a20700010050311800401d40018865500c074101620002510b5115507000340c24001041561949a40914030400340031008210301030310700c0c0303d8589081c641503503d90581d00a50720540949003486651030a644010100004545000074080c1001000ea45132881c060203841408108051030280250489031103840381684034841260302d83c1c41401034002d606016502c040c0c03048004c40c400820594448144a900485a54102c841003a0384022019241403131180000703e003016040c0211a50490b043c002030482d9110a1a0240158000f030040f5600440070449580503000c0d43c0c3c0f9800110440c1002a81c03118030038200410014070042c100340c1190850403202d405152584200c0054414910b0300060307211891130103800030003494100d0703d181008440c40404c00000021822815a0310300c0c2014217545808081c45183d02084c01000e000c83d0b02d10000440d5410074248664140d8028103030341c01c00964039100e007059814070922601081c1c10014001c42e0517907000c0020794000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 995481241 1250 995479991 995480021
    0x708010b0402070b0c0306191d0609010815070c0b0406050411150319141602101b03020d090b25020705090402100908100f0b010509010e0108060409170d 67
    0x143c03440d03070b03209802c000041440c002a440407020134015103442103a509400c089184000c240750b200c0c4200307000c83c143c141074060140350000c001442070502102e1203040303440381c0004000701503843d0042d0114110085c0001e0400c000c2c1d03012003000c42c50241295014500074800022107040c0b60420a114032415441c05004890b02401b003681c0201110460780c0c0407092001d941c426401486111018000481c4074040c0c800c0840144600921712000183e400c0301c080d02103420800e0004038000035074880c0420275170012081800031100500940040c22a24031344040015150075650b05c2031810b540503030f004429032480414040c10746142c511000c0700312006000174480586004000b41d103420006000034001c50840c1c2c041185980181180c00150170b1150540d141c8000ac10142d000078060701e0800c00b40181424010322241d4055000c552784080306030b681407010b850040c0107481044014081c00d0304199a00c0c4440041040d06800c20111408118256a01c2180701412030690340140042601 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 995482491 1250 995481241 995481247
    0xf1712011509090e0705040506040b0303181c050c010c061d070305070b120109150503030301080d090611031b1911040b010305010609030b091507120c08060109091d0106080708010b0402 81
    0x504100000d401d4201d61b021a001b0906994400224001e001c514011035010310010030f01070000d40c1c00b001b047c84804416100300d503131044840aa078264222054010741a43c108074004400c40d4465a10402d1290181c0000300318420341180ba1131701241103a00784c440d01d8010f400d0600400900744081001400181c505d039040204c02030558035038520620030b2551080e0f07620290150104407c00850083c04000d00756510380da90781c00c03070a44420400707654000107030385010081102ca000700ca610030b49215080c010740c100201800c003044480c51280b000b181ca4440d00c11500b03401d000c00705d4084059482852004002c0080c10284416900c0b020951070505050600600c42c485d8440e180b407046a0300280341d0300050701e0710140503007001c0917000100c5501644400300051142c000890000118024008010481c4200380031a11408281e807814000b0f0f03038500040106e51602d80010070000444010540110000c0b0b101a00716112580b0140c0d8640040a0801400100388100011000c060b030742540703 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 995483741 1250 995482491 995482511
    0x21e030703200a090b09040e030408031201091104060e01112d0c0102190804030803010306020903190803160314071e02070b070f0812090606100c0f171201150909 71
    0x1002013513a000350010480c0c00f1411243ca45d0f900d400c160290884002500d9851b40c4030488551242c2c8685104010203100500003d07d91909210300b020300f1342c42c107076414105030030120101e8003a80646422410481045800c98860388140a000c04030001840c90f45001e1212411204d404e1003100c40305051900000c071410400e917004a51007040c6028038045d1000b00320305140107e994015508007400040002c4004002c0008550007042c54500c218121010580750320241500b50055000003080e100702400407448081106035018091003107070034045640e244074180f8000c840c03400c0300c03004001044072108600c0c1c0500d20030f54030451416032000c1c14041e41400d42105051044d0307000144100041400c401c24001c0700d034151040148a601c0305001e0303003061141d1039600d400549407640301d0442c5002c031190440c09002c3c04003c1c550b2110108a5034072503070b251520002000324031110803078003c016074102e035040401418043e003100c80e04000b1100100c040107081d4511b54010701640d41c03510601e91 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 995484991 1250 995483741 995483747
    0x3020a0e0a1a07020d060c18090b0d11030c060c1605090c0301060f2705031b010801030602181003060614070506150a150509130908030109021e030703200a 68
    0x15600b00c40a082107940c0f48024404100c840303201001c042c08641c50140002da6450703100b045901d00013207104e240c54103a9103480103d01140d800c0c0b042d956200c0320b0395950301c0002c2c0c408500705040ca01d000341030b29800e06d064030106050303a0204c800458a1b4001d4685e5030001e030f42c2c01e40e51001420043c3d8603100c1c58601400004140d10040c0940c0b414440c2107912601045d04c00d0307052012403d0303038003008076040e414000301022a50382c60140d18442d010341c42601e07440e4400d00207541d4090005030f445510710303465a02c5200080d0b101c11000c95525960010600c265240e4a2920000e500c00d0b9030300141c03c500c0d0100051100707007a41f5140d03d42000802c65040443c1c00040c806801202c01c410b002011000800014000300c00c2d03a1004491141c020a1031062076040405051011380035901c86d850b0400c1401c544c0d044034031880c0c0091115406100600c0f4802072980944403071044504100c1102a0003901c07d15103800c1220b0241c002034440505000881490b05144124079402c07a0300760034147e00260203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 995486241 1250 995484991 995485019
    0x111b010e0a0b06040e07260325060608191b05030102030f1e1308090117090313082b030207021822210c0b0a1b021f1d0d03020a0e0a 58
    0x141f90590040c50b00c4041802007030007110a0405140c5401040c00c000d00c14a5440529a51050b00c80e42d203000390000302d4190205480e9000d0034100314680c16213409658019558179585003503070320080340e03403808101070320244003c60082900e28045e081e6460405031503102d0411041605d0008000c0c4801c0c030000c06078029000740c0e510b900c45d9a554032200b9a100480b005c0a420b00310b401d100704004240400c070a00440140110014120740c10234a035102d4072641c1d91803041d030210300340d0440c0da00400400c2000c03008411408038402c0c40d01525189040c1c00090440e150407080c0c84032480034606201c248041083c21141c1c980380100c050948d080c40361100d2000004500755030201d008400300c0e102102c2c0c4180058808280e05c54020059401c00404c481d0080905241800325514954110611540002200391039040c840e8401c290312414400c040020704240340302a003050013903100e03d010344141407065408070380c1c4e19500142c81c0d0580d248000c22410111f0001c50007544031010a005002d08084e030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 995487491 1250 995486241 995486279
    0x43309060c0602162f0306040212030c06090c0913030e0907020f06040605060109080712060b060412050604020a060302040302090c211018111b010e0a0b06040e07 71
    0x100c035076410303142803110107803080b22030960641d0707038200210080015049142e000d040703494803025070340118200b140340103032030400c601c0e94141d0141000034011301d01140318181c0d8a9010040e02c2c1032410300c10348145803110517203c20246811040071030046042601d083d41d4005d51020181484000ca520041c1483e007508644500a01c0001c000075503d40c000c010009a0340b2086080307c00300d04d01230400c680104020b0300e45a0008800d5000025a010000f80c80001c1d142c109108440306401903644c0001444402040d0390000d80902001031115600e03260300c50100d02071000b03031a991400d48101710344650b1030741015081c14070503c01407000d070700c40203501903109288018541d0f88001908070704a050445451204644000404002d4413804c0f040048084070a40602443c480803e00700280070b030340c03000f440c58100c1c200070311405040d8a4545c401c0007040d18980b00000d00024682c140314188a0741c1e240580311070b5220000d202d000e0911f40f080c120712060f40744c00740c10b0f9941019610380c000380d80210 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 995488741 1250 995487491 995487497
    0x1140f01082b120b030307030903020307050d030206070305090a0c0b130902040f0315060f0b12010510121d1e060a020f03011e23040f0b010e060c01060b04330906 71
    0x1803d10320380840d540c40800801c80c004c080745c1d01c1d481c480c40e00600812141c0403c900900a2800000385414460032180071150701d5009806541d44044044005100040540e90340e84a48004c407400319415041240103040015800781d1341d1001540101009006a4405060704e407040008110309600a00c841054035841006000341805588000300902803e030841407510508440024540740360b080100b80c8540d0200441e007090ba42d620421100114030080d1101040c01c459529801481c9580401c884056170280d1b28500080340c00d8151619107000908202c8659005d202601400c1c20440258441c0d0490f50075480d081d50754803001e07901d000c188a0b0598a01851884164040d42500c140d4050701c4050038502000c8403030700c1200c0b461010002440e014a117822100c440c040800d000c0d0000894040e19070107018a1039034203114584d03004141100d03440d5a01c803008590114440010001004105003004c032a1860092000b559060b01d0600d0b048a01500510150203400c003030544115030080c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 995489991 1250 995488741 995488757
    0x180e0601050c070e0903130e04030503150d2103060b130e060d1505010312231b060a09020906030708120a03020c150709050627010201140f01082b 64
    0x10b9241c070314000180c0c01c961000c941e01001c21030501000400780180c59038610a841d10540d403250200364803401500e01400158003000001c6c19007200e01245000c5c0c0278060011590502561034100d0901e018a810540d41000981921b032101e40c14000c10000d0412556618589100140fa6200743c03059031003403000c943d1114002402c4c598509014002070703134200131a00341e900030581c9113a0060000b4081100c80c40c1103082040c18541c81103844620415004005d002c19030300c444040040c81e0098210010380003c20400301084010510691340142c40018000c9000082c910400031640390003880e040c041d901c00c6904101043d0300050a00f02d041c45801201d43d01d0006a80440c081e12421040c030120b4840d415006400d90380380000d00d403107110175a03506a401a00c982c00c01c0303203c0c070944034800c40315010301180c5232003140e800e0084000c4020500002403000400e40c5c000404203170480b00020000011401046201c4003401842c031060940550fa0f01084528000703441120071541c20642000515 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 995491241 1250 995489991 995490007
    0xe0d02150916090203010303021605011b0206040906090905060a0b1f1b0b091e0307080d0b03011b12050103021c1b0906030303110705030a08041106031501180e060105 73
    0xc0c07202d4040e020112465046040e101d501c010040e52082c0700460041c4100c45882118442003e601c00517940140c0d00c9040030072203c8140c0b201c4608411007a0b80c45902080001020541445158001c00d0f81c5240400c4552050408038100b0000400380400241050f030806102e6071580740d84101c45040d0494490030596003c01145d804a0f540000415180054003110a01403411038803441024108211101c60a000300042a00034011004040d9684240110000940c2d0f0f10060005164900000900001c80c600080c0c01d4440f04004a000b1042500d60a039050360311850b1000c109403414414071880d45542d000c95141e0403403200040303104d4690001501006409221402245040c1d82c4034175446407510480702c010034140c4030850109152140042c0c01030740d01010394044070b400901031810030a4154090f20085401441240e500c1030045d1f2507000381e03440c1c0b0040c601a110304800c00441d08017400014050410702c255410400460b140304110032541c43e00d0703950f480361003840c0003a1200c43c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 995492491 1250 995491241 995491243
    0xf240f01030b0c0d020a0e030615150a03020d3206090a020a12090309050a12120c0c210c0504091115040e010e070201140f07050708190c060e0d021509 66
    0x40c2c0e4032000984c500014003611203a41c0105642c4110100710207446250715043c048030b07400026030b050b0075041340364400b41c40064055900030302000086804c01501d468001d01000c0c0c2128441d00004061580045500304c110704201e890170744414110008521a08103540016030110000301604161500001c00b419814441d000f007110880c0070081c14800502c2c103240107415440c843c001d80c3e00411130701c000001c2c440860205092060f400040004040500f610101d902801d48401903035480032840700095140003451015450000e080c07a03128000c078042c03400c1025900ca60740241d20031030510380c3d440d020500d1030300c0307081c041c0b0340c2210308010803130303941c0f0b10100140501c0d40000b0b04042d1080000540310160318900e849500356600800a0075440e04504000400503161200340900520000b054140038030000c01105018009990400c650b5049405103540424041c000003118441c60404004290148020890140c0068140000c84500003035031090b026026440c40501c100204841c058 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 995493741 1250 995492491 995492497
    0x30204030b04050c012c1009050a090609060902190f0e1201090b07080f070807020a0b09010903110615040f06090204060c11091e180f240f01030b0c 65
    0x41d000110030700e145000d0034082d498010344041540400c0e00031519803007949184002c00d0500d02c907180503481d00c004900500094580d5101d000342886600c40000c00c0c10340d1010300490081088143c0807034842d00345a80b80007661050b030f1150b40c40074010301020840c0d00b0701040d04e0006406914088032021705515040301c0e40c90001d5141508100704107100f10300150190000c1d01001e001d410a0082c0e502c0f8510115015142210030405004043c800300c3c0d0207e21881c0083d80190300c1d841111404102034441145011080d2020390b6241e54444010341013540001c0090003e5900c403000d01a14540140b8211404003000c04c040d100ea9505c0000b113020300034070b5010344041e0500040c1152219182e1501414044000105071070110040401041e6483c0c1040940c0c030580803550601c8490411115080503c100900b07010401442c82400c3d1140482c1040401e5143c1c1c002801004a801302d0a98122844c28080740841c18100b19401c204003e040c040d0710a0440b64070800140140c0d45008003452280 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 995494991 1250 995493741 995493743
    0x4080d09051810050a08250b04151724010206010e27030a020114010b13060305090c0d0b070f030203010b04290a080a0c1b080d0608031218060403021002030703020403 73
    0x3070301c05002040300b03c80042c0e04030747c030305d00040e08481042034a604003981d0300e0940701380580d10008110a1207100b00030014501b100480341000386400d04a5292403d18010407130f000011601245045030f505043d04201c0d2000040c20f001424040d41400456508200000c141c80c0341d02d0b03c4613500818000321046000051408135050341d40354448003d009020f05035100d120041d0410010000c5903200c52881119004114840301d01c00d501e180500a401811000741030701c0b007070302a042503c0443d448400d1190045407081111b0311592410003000352150305421306901c100762050005020a200240884040d940f2600011820108403400c0c601410444040c010b103144022460742840c40c2c1220340c00d03004190154040c020801e0740c41c022250945042107600d50312080051031001300b0030a80003000507101689000c04c02ea17072504109450340d0310412000c1749124996007045000081c1010003450b10060b04080d0246050588000f580c0e08070580d41c040c00e060f400030101d458035010b039048600031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 995496241 1250 995494991 995494999
    0x12020705060712020f15011203050c0d0903060507020106031728050903071502060a0b060f160c1401050a1d10030c080109020f070b130b0c04080d0905181005 69
    0x910030b81c0703860f10030403218a2505015210361660402d60303140108541250211000c6041226841c0c0100c400c010742d070703170070040d001d1143c100820030030f0220601c1442c11001258440910b81c40ca0352524104a0303500906000031a45044002e0000454242c0c6503601054500719080d120541074050410220785100400340916a078107a503401150010080d0664007802c8040e110116503a00d5111318524142d80044c00507000a80000d050074956408a28640c0010317006c1d43c20038000101c803c801c0d600c0768941c43e09c03a080b04a0350380100320941d4033700c202600b0304880c09101c1c2240e040000c0c01070f00591140c41e040c000c1003004e29054020142440c1c00c0f981c801040c1107842c94005c08090001c0c0000f00100000508079400803c1d09144c5000325002012a0b291103442e03c04a41c9402c095400003420800080c0070b09020355010601e50302c4d10501074003d003004255aa4507100b010b80c68088115a0b08050007c0c00f00100500d68178900c0610340c0c500660410380451747c52044072503215040750001640 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 995497491 1250 995496241 995496247
    0x7200a06020f120f0d0f090516090506030f0c101716230a0e01050408061f060f05070f0204140f0a0c0c020d02010e010203070b01030f03080f060109031202070506 71
    0x451075001441d00d242c580c040d070a9031903490086419005601c6040040d5108403070412980502040300d50280c1c0e0040c030118400074042c4442e0342c0380e0341081c2c85100186c000744a44202440f4801c100d215258024004600501100d900e40000f20303180c422104030341c2d2003903007400300c0380d20400d0041030400c400350192202000d8a1070101d07600c5907002c0040c054240020749040c11010203200352000d8800001d138520605048c18002030046801400c5055000d0401500303000c00155400104035540c0a801e003a420041c400052205c000c2c13400b41c143c1e100004114550844032455034001003101e51a03078200c1c603c80750603a01c600214018211120306070f1460880b1004000c030200c0c0240c410f50081091003810f0102e20f01d120070840c2c1441583e80069441f00085549100560003482c01e07085241042c01034030706161702a241c1304c01028003688107031003c491000e03d9008241d8030005e0680e003c2c0c00201c1c5085181040030000384071041901004200c0341840410400c403a00800440000b00801460684d13 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 995498741 1250 995497491 995497499
    0x60d0c09060e090c09010b09031002040906081915110f07051501120c2c0108010207020f090c030a0b0102031b0304090e0d080705130b0412020a0e0c07200a 68
    0x70032091056071202886a004a4188500030400601c5120018074451083c0d080c600c034020305500920703a56178184248416001c8002840c001760004103400d40000941619103002d85040910300421120340680254140e0009203204824084080c2e00c0000021a151326032a1000b8612a0700003044100d10081800c200b0080001491403041c031040c0448159a41c2c2d901483c84a0f240445000b08103a01c440c005000c144041c1c110401d88103000c4076010f00c0000e0b03c6d441c6582000c800e810854580c0d4001910302d096040c040d0070600444020b540007500c52501d1313044800315000240100d0103083d11403003420703100d030702c204113841001003000b594151055030749407060b070b0700d074807910942681e5400d240c940710000d00d0204811200310400d842c0d8255039900c1c074400b154103031310184d10070300d0412004102148a08181020b0070140c45507003440c0b41c0f540c02c28010000702100b41d9100c45e030b0071820f5030100a000c4040005982cac0c01c0f41d0152030184460801d00c1c500806900400c1165000200c1080000d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 995499991 1250 995498741 995498759
    0x213170312011e0b0901020a0305030903040e0702060103031409010806040906150609080c0f0622270513150c03090b040602070b01080a02090609060f210d09030f0201030203060d0c 79
    0x40f0410340088943d0340c84507500c50b00c00c0c010740110340d80c043c0541c010729058008680180c0045601407590400d6a250a84540c0714010052083e11404010390005006000f09034002c0c58195116034040c0c221810802c4100c002840d100c001000d00d402aa200c101c87d10402203503030040e5000005044410003803648170301004081080d1445244c0d130300c5c07141c07510407019410611864140c1e00c601400e42403520f1000e40364420803425410a01c00100744012000400c880b6052510302c010060340b0740c5044020303240c1c40c3c90044e03e8019140b041c000035020700f5032000840c26a0800100e95017507101142e154440c04007603005064101e000703021441e012003044104061540200075151050b0b81c1440f0a07602c4c3d020700e541e1001011402034202c0300c1d070008260b81c1c2c41c00000c1c0a5001da002080003030b940501c1c1e80070030001d440d00c5000c6600d4030030210070044010014403100c0200c403a946044045070340740d03450300800c0910f05500a07040c5640003021802c0c5032a400d05440141d50090440490305555440c40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 995501241 1250 995499991 995500019
    0x7230d050f01241a030415050108240601020c1e0a0b04031a0106051204020a1e09050610200f030f030916241b06050f0a021317031201 59
    0x304800c545400d80250f09500008015010780e14100c0700404058030740c43c690b403c1c0e5440500160303060340144005030100d401d140103c1c1d0103004900040c01350204201c10440343c0403400700d060a00011200c00300001030741d0000c0c004013410803c0762500894568003264001502e82d200200750031440c410004101c07004840010400c0364490b0420104103681e03214941d405401c03e0044100182c02004190710303125155400540190000f800407550a9640c0500680741500e0301c240800382d0811003040160a40078421982e1101c0e00340c1300910b1203440d4100c01050070082c11150a600c0e0504100c03540b80c10020800d07500700d10041804c494ae00c1c844513485580540048807980a40d1051205107490f00206402ca841110b20350b410032282c0800b00b120704441c030300c1c0c1e40100908100c0b003400c2410034501903c5941208074042d88002445041000a01c1081d00001b00184d410b640100070440140c01041c42d40d81c1285c04039004141201030002c0914210300c59003c1c2e00c0d01640e00b000021502d01046044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 995502491 1250 995501241 995501261
    0xc0c0708150106030608060103030c1b0621020405030c04230f0a050703090f140a06050a1401150519020a0c0308030f0a0e06270a0812070207230d050f01 67
    0x441002683d80311001c80c155402c5001e41d1015030419001080080c1c0118107145510380300c0d0303400d03200e1015400c00903c1c0303594465001e000055020308684281c62501700300c1b02c40141540308103502d802e0420000c20707500c59052200e50b02945d51641c80c00040400081d00b000680b602c0e00c1444445d05107050003400f0701c402981d1740c030001c502c0c140204141c24082d1141502c0c07658805100102c2c0034541e16030641b0340003905485485030041c00790540c005002441344500c66030305202d000400710074003000c508642c5030503045002402041030001c1c8000c0c0c0c000d025240c0805403044030311401d50610303100301d00748450070b4801001e001000002004012410020b9441900710010b414890707030303940704074071309a4540d4001c25005403c14004540986243d0290f50344418079203995104c26540e41401d40c1c80c140e4580c2c0d0943d800e04020803d01612501044442d40040b00c2e4401800c5503130a104210326140100e0002a24070100c00780411100d1712a01c000c106025084010703102c1c1411810f075654040d0070b8441d6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 995503597 1106 995502491 995502523
    0x1431060f0e0d12020306150a050c1b04050906100e0c090d06020c061f230907021e0a0b01120f02123904050c0c0708 51
    0x81e02600900e010092100e402c1c0800d0007004001201c0d000b01c41c070f40c010001c0c816503503902d40303943c59244441650315645480c42c60080d038a41c481c03911042c020b40a850034010801e40003251001c034001c41030b034080c001e0303598040400da1200001c0f50b10340030240300344009010200c80c0308a00d60340803d1550115281c964070b000010504240c7c00f004076880b503000204841d258205115103a080b440c182c8a010710003030103e14008014004d8000d048101d130a804502c16548100c4000040a0340c01030040021414281c400175160217000d0242000302c2020b01006078841c2d0009a00b1151507001a15094143d00f06410071441e5040200141c980b0456109118050780e151000e40900412101c010800754030204100b1605861850000030912040c5034a101d80743c048403000c41c1e011004450008c1c0560390344407008124047d458000401d07214064000c516494001380440c00710348548 = true := by decide +kernel

theorem cover : BRFrame.Cov 995323741 995503597 := by
  have h0 := BRFrame.cov_init 995323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 995323741 ≤ n) (h2 : n < 995503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
