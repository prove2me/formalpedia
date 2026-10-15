-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4957
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:16:49.599752+00:00
-- url     : https://prove2.me/submissions/6d698c13-faa5-40fb-b24e-af5643f22876

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 891366906 ≤ n < 891546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 891368156 1250 891366906 891366913
    0x50c03070e06090a03240e0115170c03060406020a03060501080402181f0902180a27020d020a020a0209090d021519110d0c0c0c0603020d1b110717070e070e03 69
    0x5031414031307030001c03000d0442c000324907810547c401a01e800140300e0342d4240100e24600540c014104820104000c1c400d92000c0010300c198030860749240e800740a1580101c0c400c220041c1d440d00c150340090240c5040364865418880b14004000160301c4c0c10320088000c0300619202c100329a107206040b0b1a4005010484001c024141c0c00441c0c1e035092a401411400744844220b8010750341c5004100881d205801520b0800454251020104524803400c20400005a9001d418200049024000c907080049110f0050784885c2412065042c0207189507000700c0004083c08610b0b103120800b035900c4a506600704070f12040140011244407015152401719203080d40b09100c0d400100342d401150350026440000d44c54944000000390b1401040c1402c0303402d0b489100d8410700c924000003900290040c42800e070369a034442c88506401c10307019000c2038040205031541c0f10300204800c01c0b1071401d12590000c0c040340e200c00300d03c81713040300000400c0c400f26900e09145010790f40c0d41c010112000d1401202e916054030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 891369406 1250 891368156 891368183
    0x11205010f050405010b040b07080705030c01092a03170c070317120a150b03060631090b03102007030815010201090201170a020c100e01050c03070e06090a03 69
    0xa0700c080600201d0344211000d0089903210031809a03284614446c3c40c8010030b04100081c001080c15020708102405101501d00b41650000c81c982500c861500864160410003808810802012124a0808645c213080001d80e800c42e41c5190b40b40d504e1403a00d000a80000c6103580392810100800009503900c03240c4220034255660f203840c0c0e56040024a9202010b50380c0c00980000c105e40b2402c0d070124070200b0890781080c54451989083c4c0d001404050300203204100ca81007020916420074006040b940800c05c038485049000f10248a442d040048090705024944016990000f03e0300c03400c42d0146000100311940002002494200080074042c0c100085040024180c20050b0540b2070444042c00c05840e4240358012800c0701e0403c00024042061315002c26040004da007600c3c3d9101609400c01480c1031084004186040c603841e00581000b42c440350f038840014000c2c080d05406c021000031030350a40c104800040d0002e00691903031130240340085000c00090359190f90860040d43c1010788020300c00c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 891370656 1250 891369406 891369419
    0x9081506120a171b0d0503070807051b070306050901020f09040506040b030a0c080c18151504320616051c080405070501050301081b03010b120a1106070b010302010e01120501 76
    0xd400003800304c50004100710b2207040120000c2240d00d401d4010340d039018619682c22405651054020f4000c5040000070b128035402c03031075900440303503424107c0e4009113941e6142d46000e506850000b0040035642e401480000c82415030082039034251580ac44000c20565134640110b0300608540001540c988940343d9800188010b212283e0240e41e6210140c0303400c61245424440c03c14100b103100280b5041000007d41750380101d418041a00200400044401420441440c80754005d90081c4901c2d07041d69501c80d9102800601e00603a00441d840c4032080d220b52030001602d0f50003842c040e0141080c01d500142c040000c144400c100c038115119020503801e0030840018511401183c040743e03244a00d6502181d19070142c410340c0d04840c0000c00605c107101401110490501c0c00d1403205170107640f1044040155510085031a258000e5100100012655801c00002d42e40a00c081640500c030100150b4000c92220050305041d03d0302070030044581c024800c0100d0342000403840342800c4501c1c00b0008209e4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 891371906 1250 891370656 891370703
    0x170705010c0e0d0b040c081c080f06010e1207320f06250501020f0307090b0703080708071e05030a0e01060e1302010c0803010e01030309081506120a 65
    0x10140600000c101d20824084256030003210303441615030082524022400003401160307070950162040405601c141d07501c03010145440365040d18890004000c3c42010301103540301e091598042a462541006030030081d0000c1e000d02e0301800881e0042c1c490841c1c081c0c1816040058000500300480420110245030b0140c81204482c1c1610303404141d0072400c001024035105000450110000384190302c0e02581d458112048010301545200b010300c1c08078a50089203007072001d4000210b0070f8013125a40d2621110051044c4085d0f002044903d40900c403002c0803d41c0400d04580c08802c5003000600c0d40c89030340e0140d8000a440500c44003040840c1c5224102c00e6021740618020581d4090038000134000425003400e80c1c4190003071441e4040c000c800506910124101d4201d220300605110f440907142d80c0303d1440c02c3d8426000305c4400001c6000400070903602100d00001001c10101034104030701040c1242400703480181445110740c81c01d5403901e01d594414068504100d80c000c0c0260020068109010711 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 891373156 1250 891371906 891371917
    0x80703051c050738040c030501180309061b150e012f1b07060906021908030f0c25020901080a020a1a07060501083004060e040917 57
    0x111aa0803401c070888540110141c2e90305950007030003603c001c40081041038500460030070b0280790840007040c101c80341a08101c0d01740158080d00580c00c0282c00c6041c41401d613801013070089100905171800310003190740300e0030781000e440d028031f030131841030444003032541c0000009400a081007020045070f40c51062268880211640100001d0102981e0440d03900c0c100311610b0308880d01c2c05482281c400603031090100401c042256005205d2510b001d0000940c5804c0068001c1070200701e0580d403d2001d990100308500603038109003c1414116215a5460310600002d492103080841b881c0c00f18150045420644416980001d120f880e0503450519042c8160341d42c103400e174000c14005e400441d4010010402c1a140c5401401c010210307490240c013090222508040904509000c0c4144000900c41d030049500070151080184440c0c181035060441005400700d00c0c1c180340251080c2e149606c501d00f401c0e201220b184e81489141414100045405000c00c00c01c01009110588400f01c10401030354041c10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 891374406 1250 891373156 891373183
    0x150a0b0c01140c131a250302011a01050a111f0609060f210303020705161d060307290d050108071203021e030c1b180421020708070305 59
    0x11600c1d2030303c000c2d10036184500300303884da08540550028068485051804000301251448051418001c0080c036011b00c1e05180c180032500301c1081c2040181a82405404001d54005120041108140380083c0803885980c500340c081c090020305500660b0790a02400c0e105008960800004000710040400185024000d07507424620b0b025010441c103c2030410301060300c1f800302d12060a8803640c00403502c0c29041f000d04500b015003c0010100054040c0704060b510003890903c0000d241c101000a039440c9400d5001d080c6070040c0d107041220507600000c02d042121412580144000308000c454021710408054103146451f002504803102c44030303a441a4100e82003c01070b60840e507100c01ca020480c610400000d00164025031421500381d050719081640700144804a07442c0644004030542843c00710782801c07481c000440c1940d641e906101d00749601c3d000000b0018541d902e8581c1e2900000d0010a001d50514604032004044040c02081400040d241b004102d07a000c0e5562700d800c1e6071f01c1c0c01055112 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 891375656 1250 891374406 891374441
    0x60702010626030f090d060207060209090a2c010902030115050a06021507080a06032001080a06080a1211120705100b130c0504050402180a0b040b03150a0b0c01 70
    0x304072074650902c81c420310501a500c1d0a044d070b4440d03080ea400201a0a520030303050501100090b500784020808a1b02c1081c0c0541c9807803800381003001251000f010300070710a080040510b030b0b01d107000c00385814407200303100300505039100d1001d064014060040c00941561078040801c00e0803406030000c1c0c04941040711030311600c0341ca031800ac80e162812880c441e03540c0007003000410321a60003183c50b15030002c480c0b4000101e1035076a4a8a070785148030052031601e4112101030100082d40d201c041c0c10391125056505100079450074242c1603803a070751000d0261070104a0391113101928030501e480505142001d00700d0390000a07140b445000340d440b01104031120f00c80ca107410143c2e5000390003501480361000705840740740c981044080c0d01a002901c030304820410100b20114403580ea038400b912045624072881e402c000c001c041401091010303a0420200b146060104003d8407034170701d0840740d11000c11380d0b0650012000f18007007445c44404d50002c280c45000402d1424a0803c15842205411800c5012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 891376906 1250 891375656 891375689
    0xe040b07030c050703140d050a15050f100e060d05071d040b090106050304021908030d060902030c1608070b191b120221090102070302120f03010e0c07050607020106 72
    0x35401c40702c03104807250106205000c0c407408603001d00d80d40c1003c2c1c0004080c0310300e0044681503100c201d520071100443da190740c800305004100001d80c00400a42425681e000c0000f401e54000b501e016030b0604100104203003404090141d0700e400007070342c2d80785807804010b100c02d090050014161403031503280e51034111040c40c0304112a01d00b034000c405001c14094106070745a4244641141c49a00041c0f0036600700910340040c039620b900c1c80002a0003031051202840e15506800342d081d098641d00e5004280c01401482480840792550003260750300804541c2c00d8001c0304061070204954010a4806440c103a004c0d400c000c055041040500300d822a034017410005450400041c004031901e1041650018000e600113440d85001130f4000c00304801d040d1041c10402c00e40e015080307611301d02155a02d086c0d035004100c0c10201601041900c008140c40008907044c6800b0000500103400140b103218030760340d641c001045100b00110200ca080da6080310a80e965440d00c450080c0c0a803109116011401c04c410320b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 891378156 1250 891376906 891376921
    0x304051908060a021c0f1806150608090c01110f07090519020c100c0905121c05030c03070513150e031e03030a09030e030a0c14010f021915060e040b 65
    0xc07283c5500300d1003030f01c400441762803030924000d05800c4034220310700d80e803041c400c501d10000c10561941c0718410017000c160501c0041c498103160401c2e42c00034050203921410310001080100d001c4014640c2840d014548a0440400358540315241502e481c041c05103103000b1601554541266215140045168804e44d130f20000701d10480c412540400306540105003101c0f0141c209030060f40386208145098030543c2c4d01c0c1c0000070a20410141d0700e00041c1d200c0d04000011280105074070b03040400c2c0e41000c4d411031512102e88411407100801c05410007100141c282c80910a490010b000381185500c02000c03502c10000150084000c50301070b911902c0f0303400d4000a0840900480038808101d80d000d5411500c884e2240e202030840c0c00001c0782071000328684041503031406c1101158483c0203c52180390f0710328200410400000495807181041212004110602d40000c0c07016030501c02600140e82c240308504141221661040c1414811401c000000881490041d4114012400781640c01c5c06a1102c21 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 891379406 1250 891378156 891378161
    0x2090306150904170c030a05040302091303080708040305040f06020604020a140a0303050c011d060f01090903050a1d041107030306051c0f08040504050c0408211b0304051908060a 78
    0xd0180e9800b0301d034a4001000141250709903112581d00c0049a030500f40d0342c03005642942c100280360000240e0115040055260401181fa04803402d0080002e1021864030300900c0c9000080c42c2d0300c04c0c418444041404c041c0301c0c0080b10300410001e484544160380340c044c001d44907039040da0164402c06805402207610011000d20300c02180c001010b000103145190350950340c680098481c8001950b942e1850060556440c1404095a8690000c1d2003240750604c9885000003044e00014480c80c0b6103555480080d8010040715101800d50502501c0c0c5d00c840403100c0b100e2640300c40c40c00e800904011450b88551514005400500d1003a02e040c001c2c00d4858042c0306070041c90061740c0d07041c003024044500c04a0801420410b4050042616614064036200410140c039019924080220000a401c001100040c45021003100340c43c07280d20442107800c9600038090068928162484c06030400510a0078020000c1361b0041001070446d64001c2c00102145440400c24450448103005000c0001e44112092 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 891380656 1250 891379406 891379441
    0xb07080f10051201020c010207031701080115050906041508100c1b080a111f0506030a0308060135041b0312031e090c05010e040c020312100e0a02090306 67
    0x7800000100e600c2c000801c403680307468035010032055500300041c001910080c001401c285000e0b8642000c1201904180c01d4048416408400141d2504003c07400002a000340386088480072201740071103454000005000300200b20b00c0154640c1d4059001400030008201809516035a49042108c85154030054a03901d5000c20444042c001e0b240e560000515000080c16100080c2c2c90400c1c5440c40e440e0049141031104500048010301031075100c00e0403074260003640c1e4090300c298090819100e090f070340179001c0f12014003101d052062000d0411407a0746480d6804208012044d042e06a48176141d44100c80f070395054a027500c240410f0a003d2400c00300f10b0010700e00302d03580001d0728a54210079003011401408098002810b00031080c10601e01100240284c8075154011018070030058070f0140050408038000c208603004504050078a0b0f42c083d0040300740d40308081b40780303000045980e880f4104014246550000c02400408400303003c96081c80c2e6026104c2c400099003150105c0e21910030072190600d64 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 891381906 1250 891380656 891380671
    0x5240102070506030a0e06090c040605040b03060402010c111e13050c041502030f0309100606090b040509040609080c0609010b0109050d1e02041d010f060b072603040b07080f 76
    0xa01c4100000c0c00c000e0000c542c04030003620002080602206410f0501310156150440e66005001c0442d1a1a181c0704440040c9012507042140c1900c210100e03803a4030300104080d042c0404202d4540500c40c00c29500108002c008112a40c2003e614600c10b01688641507881e005070705000305980085454170800e03019440c82d000d52428503261280100e1421b42040a620450005002c0841d040242c81c01460090082d54064600801500b81d11401c03501d42d64800c4040090368102040300c86000ca08540c1956070585108000b0350302e90a018000c5e104001005054401c00204401c5840c800b0856071300a008041c000e020000b100310044580b4507590150a610205c21014440010750100b510380807d200c1c0400c14242d000039400140458407400401016a0207002251122000c01e20a40440240184081007450b051914518490103843c00041001d208180070352002102c2d050107030542d00b1080c1000c0c2c0d40c0d24051510541e11170068403070201141c42140440c21682d002000305114160703 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 891383156 1250 891381906 891381913
    0x60803120c03040314220b220f061b1205070b0f01080d032a05030a18050309060322060609060b0703021b1306090e0c01050c0606060d0f050a05240102 66
    0x5620704031455900c510441d892480b030441c040e41c2c10861019005d002410007c44d0540c0350003101c03020312000810801e1031450003912180c05d20120f4000300c2c14800303861940c0342c5004055001904000f81c2203e491000d0001106038002105d565030040003810102c1c40740c2c589103c41c0d00c032000301840f0b2000030b018418484c0c211010050000b4440e5020700c16041e1100141074655079506825180042032402d1500090400000c2001407003003070040c20398001480c0301841141019807078403601c07401400186032040100202007590549044160b0b4103100164a40203d540c1070f52800d0401806182301d1210350500740710700041d8021410f01030f034244d150107070080d00c40c00d4040d4032440d402c01208006554404018046078400280138420440a400e48040000d901d00300128981d103085900128a410032004000000c5243c00100d0b945404c03c0081e00c400e0b8846140b4903841c005440030640da41030042c504805c204400c0c0703281e000103018508074003450003600c2c004180855030202e407405103030241e1b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 891384406 1250 891383156 891383177
    0xd0e0d0207091505100c0203061509130309081c020d21050603190b0405070f03020d080f161101090b04050607020d061503050a03022401050d020f04060803120c030403 73
    0x40b4180c005890900001040c00c8420f5210030018401d0320481818400042503040d080045007400c010043d0071420203500d501c0861600000540c540300c004011400d51121003c3c40b03400c00d4020340b0280081c080d0042924207404980704e00c0110901a41b004400521461021500c03481c0100040880b81c4081d003100b282c81c10a1005040c0601000f826668251051503104403000081c0150001c2c25403207000d110116060034102640361009030f802c0b0306540d2000010420045e51810012843c45078051603a80c0c840ea0280040d541902030001f03084400d4051580e0300c8200410404224104282600c40f04901c075141d9031904094000c03030051980142d0204022409481c0c020041243c05200380700200344c0048540f80010900c0c43c5900c00c441951041103160205601031020321805105148024000100da800f113145640041c4a5117014501c4c941100b0150345403154111005c0c00d01500902c001d56a84c80300319603070713449007089a180010740e001003020407080d01d0443e80200c2e01941d90080c0701 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 891385656 1250 891384406 891384419
    0x201141009180203062a190c1e030c030f02010614060c013c0e0d1b0203060c0a0e0607020907080c1e0301030212030316050a170c0d0e0d0207 62
    0x103041031a50040520029210b15006030381c2003101d60b224a51050055500a0700e0a0804400440c1080302c80d00402c010f21101c03500442d0700c04182e0201a113850080c01c602128205101d91401641303c41040f00820f00c00d100505411850b815070691203030751420744040c20864228202d680034051010495041ca10004041c5861000b40034490f456000010310040d4408100034644100c80000144858585c2a41408044500d40c03504150340c003401444103030b21200c1d00e90349843e02d030a0761000340114107400b070100382440d1201c0000240e014085a030a0b080c1035980f008207030044a880000074000480050282c10320006076080c41c7c4c1c0c050131407002d075164041c0030390320780900500000420005010b0545500d41d002c14602c480e0704403da940d030b542d50441c0188458134410144481c19a8820404c2c00b0301e05008014105600750369140c440d4494403028021108049640300c4041c0d103070503034014802203045ca0707002040c803a038400004010014403400c1003510f170b130140200c810258000b81400c110700d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 891386906 1250 891385656 891385661
    0xb090a05070b0a3e060c07080d020403060c02070503070803040e040b071b030503060f090105030c1e06070c1d040c0e04030e060f0a1103030105060a050c0a05060c0a0201141009 77
    0x511141d081ca0410f14180308a0045032201c04590080c110701c8020340a030b00002884c4081482140c060041c000c03c2c544000e208100744294500207060f594002002c0404840c07a9058030043c613401a000e200d0400b0000001796100c03024000c4030700ca400791804c0002c000500204440072543d481d030b4111f0056440751600440861300030030002c01e01c032b070342c00c444512003540748050810035100b0380300c55071641058805c4c001c2c0e00e0103e9404a000e10b100350018802e698002515044400c0c0c00c948007400c040c25407100300c0d20f042500358040e412840c086118000c01943c49401d00950756100110fa12003118045148214407007030760041c0c440281860b0500c680032102d100994400d0103418980c9041c410000450792641c0009003603d141c80000c2901c2d04000c0d800b10012140841c148011404c55061000081d001e2242e0850081072100004150031600003e21017103140307d81203025a180341c540a02c1c0030110b903220440f081d006504c0c0003820340d45a103200c2c000300d004440711585009200c1c1455201c500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 891388156 1250 891386906 891386917
    0x90f0c060705070b03041b060e01050d020705011d0c04050901020306060415091a0306032b030f0e010c1e0203040f060806120f01020d0612080304020105030c0c0d0305040b090a05070b 80
    0x10b40b4090400c01140010380324000354091803013003002c0c80010151021101c080d81d2039400ca0380402c11181841c640c00e07a444403d981c4034908000c00141c0d1030380b4500d402d500500340304802c20415000c070f0000e80b84204002c522031910640c20340c0c05025135903499910908034070045501c1640701d10140002d004025070030007c1d00d8802100d09050041d55102e9420b00102c0740072084d920f05508001080180a060078802000701c21020411061290300c1c7c1c802c50082207603000603035000c065480400c0840040260440100100e42000811190204400042c0071400b1b800304105622412100e05011920000845040b66150007034080e619041c11000c4801c208050045544142d2402001481c0007051049501c3e118040340010b03a0340204d0810700f0300b580d0701e42c1d204103a030701c244c5107003030003c1002041282e600c84d030709107082c503940d690390702c14030a86005c0d010414407544070360b00e9111001038259101d18025030142c10f600c2c003180e907002ea03520798444103c81c1c003e2198000c0701c000c00c0f048070081c01408 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 891389406 1250 891388156 891388163
    0xd0f360206120712140a0b030a0c0902090f1206060102070e040c060507060f02180108010602010903021e031303060203190501030201020a0318090c051b03091c02240c0105090f0c0607 80
    0x56042901400d90000d40714010840e1706500d112405016000c03c0c503214190341d039501030f03000e0803000071143c41d414100080c03441411300540d000140c503d000c1d0394405140300c92900090903031480c40c910003121035841b04100c61060140c0300c3c005000c1781929000c4010352203542d120b14280756450900400300e80c20703040a4411684a41c4a2240048281c0c2c03030f0000d4000185800c6900c010b448511000504404060340203009692600b188503012a45c0410b0003e240300c5810070181c2292543c04c0010b1942c424410304c440300002c000c201004111858004601481703d849100341c4140c501d075000422207200f0301c40207016901c105180c06c0028050b03120308000a0301c842d2844122661181d440701941e50054020001a400241520540441414030900101071074011401d00180c080480d2403160100c01d031010341104248540e08550390b0070f8150110361103100300c80400100108000749503401c82485540b031b035420040000c400b60000900580b0420540300100783c1c074502c00080c4a071a034003940e4143d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 891390656 1250 891389406 891389417
    0xb0954070801111c0609061202030d051603210c02030c100b0a03060f09060501090b03120c0a1b0b12041a0c040603020d0b03030403050f150f07050d0f3602061207 71
    0x46c40700f0184580302c020080740e4a218002d0005104141c10103d9040d6403005004082c0030b0320082984017103003c89074a0b458100705402c008080706c1540d000e400c00078aa004642400503102e450b981c044090459828244100c0c1e2111100000b100c09580b410403615401400d46802000400e40c3d40e0008a40c00540c481c00280d1600c00703494032401c0d46c409030054007185450b20100e181030f0400304460340d40850795004c04d07810070b0341500d005925030345120030160400c4001d08030344402d40f42c0180d105006094056240340d4401c1c489610010503041114150b84e1a03c054520b0360b40c82d0310401c42d0790b12805002c40940e2a0509144069009400007600c45220725a00c00d2002c04540701007000304060f601480081c9900140d20501e036103040607850950f6102d2502206110100d182c110b00143c0241090403d03d465540b10920200181030b52410300e800e0174140405480352010010350048024409188920138a010507200190281807000082d04094100682c5103942d500da030402d0707041592071918 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 891391906 1250 891390656 891390659
    0x31208060609120303100504090c0905061c061a0102012d060503030403111f0915030f051005040c050a0507230a060f0b0954070801111c06 61
    0x1c5502d010741d410030a003d0713520001c14403441110940c007038801410b0480f010320005009a484201810441c45040c01007910703000424100d540790a0032082d01214011401030700c800340d0611801400031604078234901c00e080716414001e94410f018a60403500310f4000420140140308030000750b90181500a40302d2661f4200200f25507030300340300500007036001c1c1410955560b000c03000c01201c0320f00403a41c1c0c2d520006803051a406140c201070b1200403142043c1098005401d46a404d0f006050304c40c4030403160914000c20400d9100c001045076040d184207aa08100b200003200007520309114032100040410414445480020300c0c0741c185054242ca84c20b5490b11a98542030700605c0e000030300100b03d85164503140241d00d185a02c0c031619444850480e00c012490802049803142c080511100302800d40f641c42100809010007c0000013183d42440b1060400710080c41502e91038030420003030f500300c0c05400340c00500c400050040e6240c540500c3d40d100d1a001c42807592800c40d0046220300745000f07813130380720 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 891393156 1250 891391906 891391909
    0xe030106090b0a06020102040e011509120f11090709140d2f030d0503070513050a080c120609032208030f07060f060f122d0b010609031208060609 64
    0x40da0010301c810200442c00910039803c009107490030340c02a2045a1040c0020010900703840e82d0207044038000e54924141e4054071404a0b270341c803980c0c0c1080f05070110038444070041082c400c03901642a4020900c0b03032800002c000400156020030303140400010b00c01c406c1032203041000800340314400402416006003a200d42d4503030081081c60030355500b4942200b420b144040c0b9813070555001d00c0d0421005000b00364195240600342d40000341c42001000404200084280004c1c80102e02405000b4034542080341e90b4004180e0342c07086205218001c0b049181980c1d940f100004980b4064160b4002641c1440d01003401400000c03a11204000050880b0a000502940a00042c2685404185802e58a0a150622200750360b135981d482117a0070b15100c010088002d00d203003c3c3e0195401c4a502c5015280c26083c00d5510b145a410841015414080840c0d1601040c030801d100c814072944e48448c01e681d80d540280d50300b022501c00540790f4404644900c0609200f81c0e900341c0d12460040006003000300820 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 891394406 1250 891393156 891393161
    0x90616180f1a0a0f051803010e1b0603090303060f190e0f070807020c010518040609020702030d11030901030c031b02011401090e0a02090601030908120609070512060f010e0301 77
    0x2481581001c01e0041c0600144502502101d1442d8921600d14544407002500404e0280c1303a8000b0000c01002044040c0c40c00200020807001280c028003d01000300e18920303c030307102e200c55680c1c42c0c03105a02c10302d41c0380141001003e491040216501840c115a00c2805000c080f82110005e00e6010940340230400540c000341c0929000390908494048192070700d215406072041000c7c101c074080c0258082008100d650005580395904000c0c03a14a80319208003102c0864241281c0c00140d2017411301d1b030042020600c075409088004e001b20111a00b8034009402941d01c241001600b1030707113800800412103254083d40001494031a607160014002041d00030704400380d114400c0e03400041c2d443c0d41492941500d0500b8050240c14441c07410481d548142200750307a20020640002d0265040400080d00e41c1e00035484001e0b2131340c03c030103c0e07a0382d02c000d04a0b10041d14411074069100e088070074003003902d0920803829035142c5c00c90b0001d5085291a9002007182c00d400598410381008441543d41c3c441c1c1c0c0742030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 891395656 1250 891394406 891394409
    0x5010c030b2b030e121510030506061207230f0a030b04060b031501180b0405062409090108160603020702060304020f0f031f0e0c061e0f0403120e0909061618 69
    0x540a0300031b6000558064810100280c03072840c620054031002c0c404100b001c0740705071b040031045685103916014540c0321070418a580c1c1c070074050340c0c640300d0103238070a42c0c1089000f2001d08000c48001c0468040c260410000400502000e411149008001000038055500801c0055001400c9500e040600c40c1003115082c8240c0020850404184012244105a00030000c00500488040c001841d1910100f02204102c1c0c05c41c00d504072030503001702c441c2a826003c4881d03800010b4071035249903850310122036440200800d40410a89440390002d41c2d00d1084c82680d1001c3d0b8010a090b1031521650200f2140b8903c9621665000384082c20310031a9507010001e001d00710070084105c5030001303500c1c0074540441e602d064030f0701d0f00d90304031029100315503840c1d504461058032003841240190000c9001c0702560300070403a00f42414240010013000b0700860400c00341083c4400ea88080d022131400c02802803200d015262100594400f80c045400c1c3c111000007424a604540341840080f20410030400e20448903 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 891396906 1250 891395656 891395689
    0x609170f12091c051009110414091e1e0c131b02011a04091a092b120c0512040b010302030d0f0e010804020f0d05010c030b2b030e 57
    0x90310038480e041180c0000c0340c3d0b0b154160251003800c01600c1d640d484e40410074491150340c0da201880c00411400907984101c0140207401040141220002e045103d901541ca4030340c0c51065018080e550042c1003810714244e40c00c0005880d0303a00030103120842214041700c50308880c3c003803100c1c820740360b8541700307481001d241d040c52011580b180c0c903103912201300300e50701c1d040c1003103904107060880032605551607440d0103882a01e002401003000d0600d406030b1004800f0342c0318404000070602180e403000040b0040c4554030018510418a4a80582c21105c8040c3c100207003c0b851680c0300740e40d81c111035407110300022028144a464a12000244401c002d8220b80c125808001070005200b981410004a07825085070700f060120355a4001018003600e189124060410080300005030442d281d00d032a079464a0740190585001006c01c1c64101d020b4031008000000003072400804070442c0c40c000702080d0440c09210300714161035002900401c238074891083d05900788004036a0141e6141c49511000918540 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 891398156 1250 891396906 891396943
    0x30236030a031d0402041d071b0c05060906070203030d050f0f072106090c0c140114010b070c050d06020909060a060c03080604150816291b10060617010609170f 70
    0x10601002740400420035000380f09210f0f1801c41d48002455000c403c4152441140c015413501d1015000412600c609603000350035010201d6064102d441c6a04170324081d05130314483c0030896541d0ba020708182d0748104e985400148954244034441861101c0300e00c200088100041000b035110f44024083e21001d0369240c0028900565510074080301041d600d94615030700000f4004ca00014130030490222040c0156041000c0000d135960401000c0040c400c02810042e01e2486030f124641400d2000790000300303182e8000c02000c00001c60702e1a11255410544030030f41c580c011901c1150303c0440d500b400c01050250840d580f141992002000c04882100601e200f500130101042580c0041d18002070b0750340983e601502480258040c504400ca8400180c003c90400c0764075660150103104074007104141e0501c8c2401021401a4000341c0c6401c8102501c101c0d07100d441200403420790b200f0b92900c0c00d00c00d00000844400c0c060001103864224648050240300445078828a800c010a090880343c003401c1c000801c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 891399406 1250 891398156 891398161
    0x415051512101a0f101110050a050f0103020105031f0302030a0602130801060302030c0d020103090c14210d111f050711010218010e01030236030a031d0402041d 70
    0x4003030107510641d07262024050b4003600a00c0100e880c0c07021104082d40b0030b003044043c18030011b02c5011012081d92012044500b4183c00d00b40001c003c3c60180d85544210342810001203a00710000049412242d060359264175543da5802e007540c24040440410050b1303400180000302607542005008510b5000303520060340d071040035903240203262055105068031b904140082006d60340108a1a110b9070f4203544201c081d03809440100d0040a000d0700c014a14a0381c81c10100e410341c11170040d200c0020f03080c0c4501d529460103040603480044150000301035135000b8101d4060003403007010789002440340300044801882c216400762910300b800b000f0f00801c1070b588504001ea2187c4c0821a507039100140402189400c00140f440d400c2144100042d0b410b00a03134111036070299210b0b504031b03080108909140e10030600d01002040d41020001010f12082d191105040f241c0d2a011401d0070b1400d5243d11981c9040d0f14010841d940812072a65241d40241c1c24440040c6015a24070850b02c0c0c0080103441c20b500c1c0c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 891400656 1250 891399406 891399433
    0x80703120216080304230415080c041a0f060903060a020d0c0507030203120916080c041532090103060b15040b0d0f060b0703091d0415051512 62
    0x340b22403061441d520200390204080e0002004940c15241e440e540f565541000c8034150758410719914000d6002440e00840407090702201e180d01081d0340c0080b05940c1d18000040401041d80e91205400305c5820720420080f01900e0501c20035000044040c20342d9040c00400c1c00040d0034074400711f0341c40c00340e140c001031038004041c0749100d000348200e4641050b60822516480c0256640100c1044e07610030020b003c0415820b0008002c10009151142180c580e126218904507458001076401c050240d403d01c0c205c020b4880d04400c1e20001d540d510b640802c0703003594a603400032580041502c500400c0041d444d00321080c1c0c41e500d160314042c0d8083e040c0460081400010310104008801ca0049000c00911007404000da500089540315000705030046402c0c49035101e80801010f00307a200b031b228510b0001e501e80800d030300035000408603414094166410035030741382804c000e0742003110700814108004450f10440e0740954401c2d41c000415200c0c4000b285005000300ea61203d20004002c000d42c00f0b0401520300c2c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 891401906 1250 891400656 891400663
    0x70f0c060801030f08030915180c1c0206030406140a060815040b0612070902190801060201022d07050106031104180c0537240f05090a0807031202 64
    0x800c0145030601040d89151500050300c104007500402181c0c00102180e0100d00802c1182c042209035124224203041403440f40400700000d450440745c40c083d00d101500d10740380c100c4821070010700340c116000c0100007513420022264801401220700326620031060104420f81010b5920684628100140b100d040200030380c50001e421214040000caa24208400079030701425441c0c2015080e652501c220016042c0c1d03608100c0d003600a0b0001c1740c0701041d0b51458514a4468640d8024583c0f207148d180d91302d801c4120f003030380706503010407000b07012013203408a90680e2201741c0038540020741e0040381081410340c0c88a0039542650720585140b120848508441d00d00b80c4146050b4141c103410201ca40d0f2010340d207038a4100c8107480390300d10404030050f031706000c19800700c6015440380b040540080c0c250310040d41000700386c826000e0070458200342d01c001003e0b45800844100140c92a4807440d0311a900301d2006c694a0344003042840e0000c0c0030000024100d0410081c0001843c440c09881c101e00341c00c0d4a00915 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 891403156 1250 891401906 891401909
    0x30c0d1805060307120e010e0303090601050a0623090d02130c03051005031005090c13060312030626011808070b0a0501060504060f020309100809060a02030910020702120102070f0c 79
    0x810b04080060111150304200b9685441015820100c0c8200100750524010300501c0c0006103d808008108400c2d1000494030701d0503543c00300d58000740f20f6114078003116100001030202c40c220700c480200301c140c0c018150141103100d5008044011039461580844d1580202d10401d0150b6034403402a80e802d2a0180915513214180d01c0c000d0380e030185082d0001f551098030021202c4410360b40d4012502544042c8038a141c0700074050807441009112009034030090040303200c15540103610258240e04180300380100001c0b1a10a807aa1031041100c500802080f035810b104c4400c02d6503610788440000300e0100c1c40c006803600403000c881e103500301c0341800782c040d42c0018801c1c8882860200188486a0088151070680310396241115001c106544282d165105084295501180141640b251941e0118209100b180d6213419510151201140641a030009035003502443c2c0000c8190b45889542c1c2c0d024086a80c001807210b0184080394055500b268441c0e241601c00a030056405c4060080c154180300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 891404406 1250 891403156 891403159
    0x503040b090c0607032f06011809080405041505130b0901090b01050313080702131b0c02010f0c031e020607090f120f022e0905040e0607030c02030c0d1805 68
    0x904580b9040000e4403910405400030140700100004a2444109106910b6102c1607982c0070054010000559640c0b008244101000710703c86074584a105451406030b200160303844800c55003000e003080100005000310380b214480941c042207000521340d03940b01c1ca503812441d24000009481c070440081c4030207040141c00c000201800c04000d40038503640a012039520040c09101d0b0061f0300c000d0f01d4141594803615030041e520140c0407060420b0341465610508140c03041e26500c3c0c0355160410021390b03400c6880d9202034042011501003445250050340f080346003910a203403500540c00211210503080d421680c911005030300100070441c02503001400c040250105a82c1001c4c2c140c070703000c0035201340241c40c103004141d820703540342e15070440d101c0b000400031140203c0ea80c4a80c490038001c41a640844081c004e8001403100700c0e000409090521070019408000409044282d503001c0042d4041c001e62030131101103100800c10000321180900058903e8041581c40c449070101c1c1c80000d07a04d000d295044507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 891405656 1250 891404406 891404413
    0x1021b150c0703020309032b0806030a0816080d05060f1c030305070201020c06040f170301030c120201140a030b01080a060e041101230301030c06090605031609120b010e09070312050d060b0a0503040b09 88
    0x10ae50381c0015800e69166200101a954650350380710310441a42d4110300a00d14080030800498011454018510030f82041d1001400d0103013003001c100344845072501011305d45001400c22801f2900c280c009951005d260700000d4504081825001e02d0100f0440c1d0030340d8180c5123850000c0400c945210750070054100c03045620b00b1541103407038101280c407107031040494524401d000c3c2030031a401034400001d803c102d01d1a607134403000400c0c400703800390003118610b600241425000503c191420300c101001d0790b400c0d4081d2043c0d0b035074540d43c2c2c400c5401c20861980c1402300f90180302c08039011091070b564682d43c103500300030b803a94910318180540e07006940150040c03140c0d00d802848140e80c8641a41e5102c040350550018019a061083e22070640c60f4000d03042503410008001c0c1072040210100341200c20a500318038095552007021605d510b400c0c00001c100a0040d01d241807064407500240004501400c80002da090f6542c40701c2086600480b140d001056001c4104000c0c84a20000c940e400362180d17016 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 891406906 1250 891405656 891405661
    0x17010f0b09060303042903010e0712180b0604060302040e030d050a090f0206070f080c01090c05040e03040303080910020304111003060503210d020a0201021b150c0703020309032b08 79
    0x41c4d00d902607800f034058aa02800c104c0020140390190300150950007465041d9603507141c460314290f44004403284001328401204c3c80b4161413044c840c0225044411403840346520040e0740d200603001014010b9544252909804805a0340390b100b96103d004940000303559420301c20802d002070300c1c07004050080c070b680f030004600f02150458024600e03c03541110083d41c2c0f5042c2d072508250128180c1c401408624011541300400c84055101c010403e014000040100303540f0300c104410383d0380200031400307240c00c18001000040d018102543e0450000b905645940c05105400400c036042120309079450492000c500c0b110342003520801c2ca101c01c26290500105003000301082d40d03250a044110003810305240c0ca0004411036409944074822034440541d614000781500034042c0d0024203142c10880b1140c0301c0d195a0301000910307000080c03e112480341c241e0b500c0d140c0d128440d812030201034055000804c5186141c0d81d080c0302c40080c0390400d2401c602070180b254002c11304640a01950024032a20b00203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 891408156 1250 891406906 891406909
    0x30d030204050d08093c0634050a03050909011203140c0c03010e0a1205030709030201050702150318070b040b090d14030f07110108010b07150617010f0b0906 69
    0x1002c81e2400c0e0050344065998460f240816620104081038400c02d000d0b11100b0401c05600306c80f0001c81c8081c0024000c100d14056080140910a1420b03c0100c500342c42500350b6140105845034a0390a40b14000920a0540342c50307050170498103400031000510700084c450a00d180150046000d80754202440a012142c2d9070064603410f040710b40d030900b841b008600d0121720a02080031368400a0050002d201c021496040d40e82d855885110868003481c91010b4602c54610410959101d544103030358088915186400544596200c0c20050381c20002c10804c03100c070614800b0040d802441442c40070940349203912121801c1110719000303504402000c001c1000324010801c04e890981c0c0080782c1c0800d40a8031751400c4c08454034400c40b0044203001c0495020401e4080c000607088540c002d00c1604d030703030916000046030b001100340100642d5030014014107010a009064a65200d2034101c0c0018401c0d849040754808100381e1162003000ea9141d801590708280300d80583e6001c010190381024a5040003030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 891409406 1250 891408156 891408169
    0x30e04110f030a050402040608031c1103040c0308030603010f38010c0201050c101d0606032b0212031314010203060a05150409140f130503180604090e0705030d03020405 74
    0x803c226000b0f610790005c24103542d1140e1184005180d81011244d43d950441201c100342c2c2071000444c05072a1400910200c4400315800312071140381e0100910714214110740d20030000d90005031815070150341c0d0b42180c0804d80304a101c0c210441540303100e100402d43c00600c2e941c5014005030303040d07242441e560850403507a0340c004140c0919681e090800740e8599044942c91454800508280c08900e070802017008060f03e880760034159207502c0c100c2500e6096403940306050b41c96800141c90040310202c0d2004a1340c400314008425502c2e1010700c1035809000201909071500d80050318100d00c0528940891001c000030700951602c80f442000081d42103140c10000900c4e03400480c41003074003410310210407641e659210380c03c44024003e210005c000300c101c05002c580310b010b8101c4030050a000c0c00004541203036914107950016030b5001006510f00020b41d07125010b003034200044140c01a82c28800420b2500b12401400a065800f00080000e41c0c541402c040c0340c140c50114440905104000034452900c070030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 891410656 1250 891409406 891409411
    0xf09060702011116030507020901030f0227060607110907050d0c0219142505120604170a020705090a0c0906080907120305071a1501050c060402040b0a12030e04110f03 73
    0x10110400044d01c03604080c0c850741b0038181c1c0294002c0d410800441001903640e406922140262a4208484a410070800043c6020340040100b5407a000000d1010301d0720f640101045441400c00c00c08071a07140d404200c0302c020a48803d40452004910035100414511481c089d008441c4000e05c038107440b410b100d081802200802611004241e200103a8a084c2000045080c01404221443c5500390070b665091011140c05881d2007569810011a40d518002880da8082e54205031000c4655041d125204002e90080b60030f01c066011b20240020700342e65a8917114070500c07692102107100104070100070030845a0350461000d0102040900039a001d0009844060350060b03c50050b2040407030405a90320300401d4401055071440c83da100b0345a520703042a003400b4001c01c100c410041051a40151081e02030540050303e1644507400050241c500394011036000c0704c0103404682c00c0d5848500b12600808521740540109154902c0f002032403c05200b080300c2244581e100c01d042c010b03448112411440301 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 891411906 1250 891410656 891410677
    0x40b0d090501151a21010e04020f2b051002070803041104060f0605130b070501020705070801050705250b040308040c050f09040b09120d06050a0f0f0621050f090607020111 75
    0x1284011289004030b10341c0905d9a2617603501000c540c2d44190035040b00c481160101d000d46008007644100d801c04400114100740e152203024024028092010b80303109403080151840d00c20304840020040c2a8401070680d0f41c024100141c0d20301c4d00f401c2c598201105038108500070781c0b8111007000804103c003602800d444651601f2a50340310002c070f4040e00c0ea843da80041c01d01e0100081c1038000c2081c151300034040709100d001a01c0019035100e05180c200d503001c42c1c020b40812030810601c040081060300411002d0803001540c1510000d40e107034a01c84000440e81103000c110741d0300511050107080782050f00105811556240801d002201051921202400c0200f1180c00d183c003280f4058400d02100d5241900380201035210301800c01d040303000d008c091185a020310f280c01404200d6100305c1c210001603442c45800c1c0c050561074460101c5041600201e09041100610060103881d4036034020b150041000350b501e0034a500b0035884132814008007406003415a0700d05107035010444104001d58030540070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 891413156 1250 891411906 891411959
    0x1514190e1008070b091e010909240608180303040201020d0806031c1d0f1c05120c0105070f170a05061c152702100302040b0d09050115 59
    0x4440700507107100019a000104240901c050110340801441c0203004a141d0445402c0c001c0c204184141c84043d0700d42d40b4880c00205129020701010140d6001700041c000100d0002c800c684c4842000c14401407190080130001c0c7c00740c0c007445452051190f50b0301c2d1130301e0040080c601d18141035001039610003000001c6d80520050000058043d5400c2c480b00440904014400700310003030101c0001d0140c42c04050b00114031102d00e03521115801d10584250640c54013a11800031580c003500e002085000c0390a04503583c3c4210311001d003007101818054000601c12400104481c241603d0180c505424417402038208002518880800b849403940fa80d0014500c24001900d0b03107812001c10040540c00000c8003148114000103401c00000d20a02c03040d0341c0001d070701000310b00318141203034851000300c11009403142500c034142809071a003043e0301c9075800070b00c0c10010301d05551b65440c81c9081d08101c03c0c0203500c540d18210102072000c02e0043c500000c24020215002c2030600b00d040300c1a07955003501070140d07078 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 891414406 1250 891413156 891413161
    0xf19020406080d02011d0d02030405150f0c0705131a04092604080c0102030403022407060929091b0301090812100603060b09011209061514190e 63
    0x46032a4050400307021000155100c9490580c406400ba140d0041d94410420f012620300303003004004540030304601a1980034607d0a4905420840ca1080010700119404d908210801b02802098020309901101c130024110319031924040041c6e0301540450a00440c0c201421200345264400075180f01c040205c1d000600482d0f01e00780369500c01d14110011248401030000007002800080160003240c44500c00ca4507502e540e403004a1f200c0c00759102c000d4006d0841c40200c82c40018403500d03001040c800310b45d11810b00b03507942c40c0d030000d44850000c140c45215002c02c0004642c0c0550428113070005140340303405070343e0a05140e001d584812051074204501540e614607942c0b03a90a400a90f01d00c0c8e00448032035242c0a00100c2500b01400c1a00c0c0782c90007445181d400160350307001740076030000c5405070102c1c2400d0501000c0195100c0082004050081c0d540300b00080004800303200301034400e200c20030303965072039400c0c110041b10210304905440d1094000c4040f20008452040c00d40d02030b1100030390301c140540c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 891415656 1250 891414406 891414409
    0xf060e0c0d062606220308090c0907031a1e040e210307080a140403082502060105010906020f0307170c1005062d010807021f02090109080f1902 63
    0x40c0303150303007250701e822084600d6100d0050041d101d80030f80018030360070fa9500784c03601101c1260502020341c080d490545140000d801007409044019844000c94041e1350346044c06000042561204607140c8002ca95580f49008141c00840c1c4610682203007510813100c900d0501c4d1420400340c00b200c2d940392080340c603101000940c10003444036605040c003202c07200170316185001503d149600229410000581c0030740c0003070600c070264003c0c6800000441c480d12441c0d111038404031fa483c1002040d004401e50a400300d41000820901034100752400350780904000d50500000602e50307206648244115030103007180c0300341c0711004401c5912850f8084d220b05c0d040d032000d0444159030b010798a01c9001c203006120304a01b01d00d0350703500403a20611040314800400070344040708020f408031141d04d03110303140c0044286140e00d5010300c0701d9580068850040f80d00c0031480c05942242d60f180210300a9210780c0102d43d008003560445000e90140100c00003410145504044d005c0e80e031180401041c2d00c41d00755021020a5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 891416906 1250 891415656 891415661
    0xf0d02131103161b0f0b0c0f0c070e33120d0c020f011103070b0c3c0301080d0e010e040e010203150f01090b0d2a02010f060e0c0d 57
    0x2030051001c40c2034891070320803241203214441e09810800b0818101550381684079484020585139403242541d0000381d0315031511045a840208042040030007081110345070b005a4002d0f01641e80c000004102140c01c1c00040e600452018041421070402820728036080c1c0c09001180d20041400ca0095000d82c8d507250001d184240407583e0000940202c0e200712250a42c050107a032000d500075a02c000d003204448004603a02d0030440004141a003084c40300c840042c850700f155a4004521031125810321440b1a86d09141c01e06104401070f04100c005600400940a84000c40700490030100703481c01e40d850411015140c0340940c0b00c1504110300180030780c030640e0082c3c3e81c81400c0d00000d041007055a0108548500030f5105643d014641c2e01e07109640e5400b40341c6608484100041a0741d8124828a421104030050300103512680409407150606404114840c440c2a01407400548002030324a202c46c0c06400c607005040d0745012142000810b00c03008142e841d02c0750700b240d8202c075801d0382d440591452000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 891418156 1250 891416906 891416921
    0xf0e0a18142e0f081e0307020a0b0705070b0d0c0201050903070c050d1b06050d0f060f180b190303080f011d040201022a01030606020c03070918080a030f05060f0d0213 73
    0xd40c0c83c4010700801e60240c00211a1610114061000042d80341e107044166240500c4a0007940036650800601c009a54100940a414810320072900c003241c44401d0000c8542025141d41e082032754400c1180c00c103a0303090141c190810707000c201541c5031410308c2d1200071640c582c900403203002d007406001c11410000609268010358424a02a034017040e100d00b0010941c1e4041c4071801081c5041c5060003e19a9180c0b1600301201d0791304860003a41c03407500641030000040c0710100d50134a55030b1a04000691a40785014042c6c141d103195103c0000c2c2103140140c042d00016120001e1746d0b00c05801400b60190407242001ca10100c495803070010364403440100c6c17405001c50f03406410308140301c1c080c80340042522007000ca2000240c17010b0000b81c0d2210350807643c6189601c50140c0c1980943d9080181c07002d250320640100c1010080e10b00605031075103540d00c20754072020803100060740d80c80641020364642e21404d50045000c4800ca00a0203441001611001d82d480300640f0039003d55500280c3c0705001e40c44102c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 891419406 1250 891418156 891418169
    0x240813060b031c02010902010801080303070f031107050a0b1608010b03040b28060602120708031801090812010e0a1b030e01180c05030d140301060f0e0a18142e 70
    0x115500c8103d0802030181c000c2c584201d010840e086c001017041c2801005803449038405a50311000794901030801c5019103d09403900b10461070411030000030503814000003880b18041c200c1c208480c10000303503914a8644d1a00f00c0c604100c5003000602c018295201100c0c2c01c5600161a10755540300c0e210302038006100701002055080101002d03000c514100e4204804507040c1d41c013034035201920009001603070310070341e60000e2261200300009110400000e9044008000100c00020075002e540c0e98040603900801c0035124a015080040141a009102185d80040300e0348060007480c102803006100141d524000d4004d0648412184201510035440500921120f20101c3c40c00407030750810241174903007401039038002d000300031070342c0301480c0504071903050807243e50104c519580c07a1a0003103550f469802a020100954400702c0003e60765281d420101420761440b406440c225404504012200828501e004164269003000000c0d045058030a11070a40301d034010001004010240c50011103541110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 891420656 1250 891419406 891419443
    0xa0504020c060709080c032508030705031b0102090901030f020d02041121010501320d0c020c120c0616050124081605060c16240813060b03 61
    0x7401d946000266a4002d140c19100c1580d41030f00c0d00c42c51030311940d07242080ca4041e400044070903804941011481040c0c90664541c00c6c000d5150001d0707a06650101a081c0d445900c04101c6404450052207690350303120300c42000314908041107021445107041407001030855031580566405540724458000c1040d540200304201030408440302c8aa030740c010000d0518103100c0d03c06040342000700002c070f041c10703504140c6410f11400480c2111a025414098402c5842d80141550001c4001c1c03100c050840d81c25140800305080d00c01b450000e00d058607854000d40303e01c000c030045101c80100807440b4450740b1000e0310841e90329000200e82d19010708141d00000e00941ca029048024042d0380e0100f05d4913240340e4011000d140c1d83c0ea1000715514588103c0d09000c0440300780c02007001d454010024650351020000391420521481d401c008840c2c503039400b00c50401001905140549007054890701700c04440c0c2000e1025040144c021b404042c0384050003040039603a02042d540669041214550110030b01099 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 891421906 1250 891420656 891420667
    0x516020a0f15050c07140102100203070e15030708010513060b0d0c0915081504090b04051c030c1b050708030703110d0f020607180816180203071b020a050402 69
    0x3030350707100407248207034102c0c0d07030b25411000c268038030440031200c043d6051401040d0960400508008a00c030a43c916415841892891011010140081c6225039015200c0c2c0003186200c50038044c01c40c00b04d14000140d0502001002034154100c498103041d1282568400c108040d5859050010a425040345004400110b24a00e0055031604985032140d40f55481ca608141e44511411041c41c0d60007802c400f1901490020b1403a00c503c034100f4510010092002c02c05c5d180903100c0444500003a00c0c241c3d02a0000441003016402000c0c05840c1c921041c40e0400641c49094030040c10500c00345003810380d501d440000802803120800c0404003130144075056a41d59031691a000c0c050702e10300014081103014402810034040d00800c18801c40c0342c03164026051980d501e20341107604007500d21400c0384a021110000c0385000c4100054000030703654100c840701e41030802c0c042d80c0c022501400d60b014010b00400c10081000d902c00b010780c80480308020740740f10b0b00c40e0780d2001807203216043c1c110741e41161000c00d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 891423156 1250 891421906 891421919
    0xb151c150e1906020d0b0a1206050403170705070b06191208040801020c100c02070315090528060b15090904080f161110051803010f020c0c1c0c060516020a 68
    0x1040c104c415060101b044810507000c0c04200da4880c46000b00410804202c03001041c2c0e241c111030782c024400d20740301c00082c01c0c4e030296803c1e110054800500259001c02c40008228078200b4403a0040310466180e21500d1200050032840100c5004031140f5041807805038003040300d140181c6010381600d074001e540382d0104405145d50780790354041c0c81312a9420a456182d071a8004a1520309407500016001c499031801c00180001e00843e8504a985211347d90155111005220407207003100001e000c00c1072003103031078100300702581c1c00100c00b24454003842c1211146026400200c2d022040b065a004105a8032400c100e135041c007800e095030040d42c6000450500075030b1600d172090b682502c07075400d46504180a10603ca9221148071032000807581c200032a81e00c0b03800481507141c841d40010000700e5508940b40401c000c0ea0050300160f41c00b03520500040340740e0303d400011840c50034001d48220704401e2450311082120101031040d1810b01600181e2100380f00910400b038500e0b65006460452200d60703c19 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 891424406 1250 891423156 891423161
    0x110304090c091d01051c120302030106120209090417120c040303091e1e030203070b07021021090c1508181f0203090304030b151c150e1906 61
    0x1000604030039020030070700014038480f40620181e43c03921506a0801081c4070101003080320b880301d8181840b201030b000450500d911205899595005a280c4d450418040c0c0724510008030810200d0041c00903a00f00e440d000344007540039400201c1c003a006500c4a10040b00c81c4980540c481031a039041d003c220350940c40b40014011240309139140c5038410365130b00002c0065505e02d204a911040c1e81e072000c20030110103402c40400b4442006503144682e07907030f0f80020315000f429808491010300114500c3c0641c90f192a484030345001e01d0520312050308005401c9000031111551000c2c2d00b07031751845d50170140961405540042c02015540000e045110400600000800c86003e00c03080e072580c80809000f607001c00c1c8282c00000000014940b003052054030400f0350801004c40c0c500d44428800000841e00b0140d28038006d00782e8150a92051200006103ca01c0d98910842a041d010342c4034601d000a10145001001c03d13150200000c51b101c01110b481e0400115800031050245404c4880040c46841c0c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 891425656 1250 891424406 891424421
    0x303090106060f030b1f2c150408060103030302033c01170a0807060e011d15060a0b1813020a090503060603060c03090f010c0503091911010302090111030409 69
    0x10f0f16102c8034090741450880c19500c1d014040340d0010f48940e81c0d640c0e00d02801204060030f0300700e8144105401c1c0b004201007500030742100c0e00341c484042500c00b00b8403401c040030803400c0040c1c1405c0340341c5018280001c503603540d081844000d040560000004011070000741d820764002c0f900b1606080700c840c17140d1807481d40b01540b00407011560305440000a03281d058060004070708100c04040c0c515060b10351201c40c1d49400464059542c140c40f40203020f01c40b0f4082c490700d0f25450034680c051115528a014907498460005910000104138009008007542c5050030841140c0032083d00d19070f02c582c40c5011204611050303181d1504901c070500c80040c1690030340c000e0510144079507201c0140a41c2d6900b0143c0c0c400080d10701d1501070308544003060864004400551344080c0080895044402c526900c0d4211064842801c0c000340f40481803180a4606001c0e05480780980c80216107805825201c403140c0342e0030203d03041d040c13540c0000c40d4038099018010088080003510150303610343d55604103040242c20b22 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 891426906 1250 891425656 891425669
    0x3060803070b4606330806241306050405031908070311240414010515010f0909061715090307060506060f0a1d1c0204020f0403050303090106 62
    0x402d641c8080c40c030010b80741203440b4002c00d8151000366080d000d0100540e0a0b0350f440c10100703600c0700c2c000b00ea00704520094401002c821000d01d42410b280a505090310324180030301c0e604001d0908280800c0340d440d85140c0d001003081d9411400202490940c141035441510003101d00600101e0b030004280b46c10101030720481e0400c0d81a100c10802121000240c01d8160100925851003400503e010034410120700c00a9014101203c40094003211450281d51080d5104406402c440c0104001c029640c1c503150141e0811400078400340c01c01c5918200e80c8a04810160704000000d009116140c2c40307010b003100200150b03c1e041107102d40b62134040303400402d1034810ba013030f510a01007000c5203039606803405441240d0a1010350304200c0c00e03070303070b20000f03402c000d482294064410f05c9807540107403030340000b0620b20b00b9075111040c0c03c04001c070712102c691494816041c45000e0524031a0783c554484500d4291883d07040320016612490440c20304031601072904050801c2c4004800c00162420550100080e500c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 891428156 1250 891426906 891426931
    0x2205090d03110702060d0b030c06030103120306060c03021009110406060215060d0804031115030a1401061e080c0c010e030409050109020306060a120b0303030702010603031112090d0303060803070b 86
    0xb0780c2161040148240900250003a0301080480f0000040754441610030302e0040c2590103241400d070020300107410030381003030310102d5544e03c01c1e24900d41c01d4441c140c002c3c01a8240348840c0e0039903031000303901c684000d03500d0054282c8510a000c20004e181c4908803107103800600400400761640070082d524030550303000c0e5621140307440102d0814a4001503041c04264040c00c82482e003400e580d51050213140050950f5082443c540290440300701d110055403244103440000182500e00e0860a4212081a4010410311041e04115411144904182c480410342410400d14584802c802c520380c81c2300302c4e100c2000c80c0d4070f0000700e8280d4903400700c010000c40c0d140240c240322690300c65000c04101d1000703030f41c0107a0100040107204805801510001d002d10a050000103214040501003402c40d07004454141c0181d548690610070140c003c102c1d809908440030007062075460401916007980f084480a80c811400c2c50003040c1014400c1e0030030405400400213a076101c14491a00001060080d81c640f00080e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 891429406 1250 891428156 891428171
    0x801090207050709330e0c0a090305030708030603100506011e020a080d0509100b0117090a0605040b010807140603010e06191e0b1206130e1c170f062205090d03 70
    0x11301720811942900c441e140306000f0ba031244100c0641aa000c10000e10034040103407800804140140090100103010302070b21696881c10340109410f0103503080380301904030b180400740300159070302c46051001c0d489110850700c140030006000364909a010703c0c00030100840000e0b81380003014030b034101074003a0282004440382110500101c5081d0b54003a0740050018400c8003401d80f0142303041d02c8554000301f0000030f941c802d61440d203c41003500d6044038240c0d81011030b28010401c907401005900e0091100c6c1c8000c540540d080000685248410b00c1420a400c2220003c1030256856400c54002401701901c1001440c0e82c545518040d14080d4512000d044141140000d050441e10100d44032280e000c2814225965804200040da80c420001c80340c0310ba0740c40f074040c031900c40108011b4058006150118041801d4958010507884013011100f030011580f04c284a440c582608007550407a00899400d8807440c0000189038170b005914402035200c9041c4001c0c1300038030740e002c91008071400c030369a020312180 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 891430656 1250 891429406 891429491
    0x6110109050616020c0d1a041a070c050c030304030818030c1c02360a020904090605150a050d03030203040609061b20030f0f04030605090d0e030106060801090207050709 74
    0x21080428080e0030f07c108617000c4548640d50541300342e4414858900c059103c0700e100350804100d54120349c8500490000307810002031180410100b040d0300c1c0c00314011840e180c115a80c284540c080c0385900c0c2c401803400171903510380b030f0b40900806d4072104e0f015140b00040c010b161200f85c145500004103a00a1200c000b003254100404402c0081e0441c88004100c003040202c13075261078100f0020001480c0755400c0c00407100c0d980c0c0328045c03000000d020302c8004c49c1c1804c00f0070a0484a10a841680d44a0341040e8010441600d070001c05192061b09800c0060f01c913661418200d001e41148000140801d10700101aa842a1100c0c0901c608009030b07541d20f00c0380c200607030400100d5182000d131a595170703009010043c2000081c0005259520009180c40e0600e0342d260364020a880341501d500445400810280c80d10701d60020b0195002c03a400c034001c1c4201031410401800c2950103016402c041500092030070240075040145200a0009400810042c0540c402e1034502492040f10720351448061f60101115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 891431906 1250 891430656 891430669
    0x20d051218010f050a110115060f030b06070f0807060b040f1a01020d05160206070512120901020a090302100c0f03031d01090506180f0d02031c0203090706110109050616020c 76
    0x590b45561031300d0b45400714214003916001070400416500d50740350b2694100c40c03450b03003100070010324958640d816003081c0800060f090b2451480c4081c000d01c002d0054802203010303a0402144140c03c092030b96640c0d0300d50700700b000c05010000c11403a0080d081c0361342e20720000107942c0413036940303c0c11481d00a880e000c49401280c85048031401c2c0400642c1c140312540c03442c6403030441082c41c1031000b001c140c42d104159070b80030b0171f0a1903a90a581801c10225541d00f00031003414200380e0040300c0d000210b1030680c4070383c400f030001080c500029001c2d4816401d01d45030280544180b0b00c40c19000f90804500e0a802c0c900240a49a500f0071400b503d104c20703841086407101405035181c003903809030207001b00750f560203400091084200042c03c81842034004500d0700312000d000011644c01c1c4d6174042d40d030310f80ca0700030300c001180725006030042e86d98810000c100c1c00307180c00b00c1e0b6030080d5022460701002c000e00380101e01d030240140c101c010380707180036030001c1c0508080482040e11840004d6000c0e14080800f44040005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 891433156 1250 891431906 891431927
    0x804030201032403141e06061c20060c100603020109120803010311011b03171b030a0b03120a03060905010e0907120614070c0c14011b020d05121801 65
    0x60102e154070b06100148941442d40305d10016801141d02a0900081c0c0e40302104558080706955001401030104908000e010b0116080d201d03030284a480d2004c0da180700550f01001207200031290190461030300c0d80e495900f03c400085111048810396440814000b0060855202c1240400d020300c40004288400e40213040c0c82c80d800c0112036013103a195440c2ca6451b810f101c0009410801500c0c0054401d5a44074461742007030f400381e070350515800c000c4c0508520b1142c02038980103411109840e41180d60141e101201d501c68a0325001085860344440440d21b01112018440340e11080810190221903141d0f00444c100c541603c0188181d90380c1c3c6100c82c411010558000d54640c0207100140844a1440c22a2202c90f07c0307804005074511900203403d00d4008160b035080c00207110070382c4050034010303111080f0700a00410301074941c07441107003000a000742034082c0d1070361b084c0c80c1d2000d0340348207560703401c01e901e0561600705040c0d035a040e8092001202c2907010100040201130488510b0000754030801100d030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 891434406 1250 891433156 891433211
    0x1060f06050a1116081c1d101202042909030a02010503040804120f06050f0601091715091609140f0a0912020c030706031b050a0516080403020103 64
    0x51526824070003c840d0040000c0042400780b2542004104d860208042c0c8001050307144d0140400c525600701d1122189204280c4004006414844090401c03821490803500c520888401c0989410030340181c400901000e81c03480440e20101d000100307040c15298404076130300d80b488140d90383c61580c00001d0581c01000c0042c0d03015844012010300550041d0b00840c0c10500808565042a0b0768404e0700c0030140d9069821a003031000400c3c0c1004001ea2801501c1d00154032401c28030b510f14040000a000b84030320302c00c6400816840b40090300310402030040403440b045400b42c42246207403507601c05ea61101c41000c0340000f05421032000480c94443d01c07894144d804a00304101c1c050b04e4000b900e04a2a2028003000b8215554141a10004103a4501000b91503440c1e0042c0c846007400b03400301410b00000343e110300b0034541400078480c1035030080d450f000d986040a08107603442e040041000c46103402070b402d092000901c0041e40e40188031545002c1c00c00c41b80f00b44d80902c181071840402c4280c0008803102c29 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 891435656 1250 891434406 891434417
    0x9170d0c02031c020901090b0a0306031230020f0301080c091006020d0c030509120703021e2b23101e0b0301020c19020405130f1b0e090f01060f06 64
    0x100fa016200307400401080350145085104192a0b50b240c4041d41c3c030504150707021980e9803d0400c104003c03c40b820031521510b0500c2a0450140407219400e00103501d00718144480c10003000c48400c101c0d44c195210011900c2e003081d20780d80c46141d280c0c0d48070000d50102e44985840000112050f03040d100e11b9055501c19030144c4000080c0c00030543d12250304440407030034032005201e038600715119a059454031160080060280d20310314014020794a1400c450814400c6411420702040e843d030041000240b40b03420940400c001a081c4002141d040c0303031000810700d101e01c49440c1c003542804908001d003018008240d03181542d0107a99035080307803040d4160bc0c000d04025904005685c4940e0300182440c0001340000d4503041c150100ca6041a642d50704c4045c4400b40c503020602541403522034154081030fa00010183c00342e40f5103030355059204120b0000d11001960462841c030b8200c0c003507008010b1035041c0070000f450400b60150398485c42c103007031855025840c003080041d854400134001d604844003034848 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 891436906 1250 891435656 891435697
    0x60929090c0306091c0203070f030e0f0a0f0b071a04050a03020f0c0f0f1801080f0f370c0902070204230703092f03070801111204030309170d0c0203 65
    0x1145c403070051441800941c0018401030000c2040b06c8040c0700094881d540e40d42e80b65010741e04200500d06c480191038000c1c1c5000c0000e00c0703129503802c0070b0340641d69442403044e100c560610b40001c8403440314103224600c08c8c00301c0c01e01c000c018000030407140c118402d4003625a01403c843e0060740c2c1d005104001caa0045d19000c038003199007050801c0744035a9101501b03100030000214a404003518084c1c0c010000d580c00044502424803062100280308515080038102801c44140d50b9180c0740340704091103005100d0181201107010049008901e41d03075121060a922603914214080250880d00042e4000d034241004001d81000f04c0300d01e1080c28450a030710081c00c0d154240214003d103009842100c07498624000004080451980b01c0f01080c400d14bc10242e181c24181803608155480e400341e6400c1e03040490003ca00c002080039a07180f0640c41145503075640d21800c0c103d02a140b540700240003040d000d212005a12403400080034440c3e03114009004034403601c00200d9a038803d01d0307200c014180d0034040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 891438156 1250 891436906 891436933
    0x40f0e06220215090a030521030108060a020c030c25050315160c0b01171e0a03050a1713020907050a0e0402160c0e0109110313060929090c030609 64
    0x24003c8603440d941c00c3d0141007005000110381000d01a80080c0c6265100c40c404040080c08809080b41020001001c5400c6515102032036688000181c02001a02d030049048003603000f080003500c0b409100b150840c2d001c10320070101c80e4019400e0281036001e13640c800b42d01041506000410b0140d917600b44c04041441d644402141030341c0660028400c2c20001e000e05204003083e4280f8a40c0e01a00400407040e0020380800ba0b02460600c40007100c5800c0aa11803850b4112100496442d44158040c1003640d61100c0e20541122f1703400e41c1503a1506488004810702483e198981d07408901e91f8400d40c2c006a0b1a01d0701c0c0300c141d480b802200c40c0300001503207002c003040d07041c00c254015014881000c40c80c0300602140e070352030148220641d000128110740780b40040260640034044c10b0400001d203919540343d82040e400c665030040302c1d4100607103140d484804460801400e454600000188600804d00032a43d40a15045918040e564440e0511441d8500c040501d0b0115100340074000e00c40c0180540488540c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 891439406 1250 891438156 891438169
    0x102100e0c0f0411040902092107140d140303060a0605030c16060b0306010e0a0501061e0c0c23040e1b10091e0303021524040b040f0e062202 62
    0x4588a40260f204c0d408000884c030300ca40904090010840c000d82c8681c90307941400404a1100441d50a885500c1541c3c030180d8804030303580c0c0a80d611548490408030708a404a80402d03841c0340001c04523142d5000b030410361100407019500890044502c0c100299440400325054041505d00d50012807040205142e01411844000342051041c0d0703001c01c01c0302048000a040c00003da0114103107803803000810145c600d00740710700d0703014007558203024114040303070240f8540003800f00610505101400d1030402c144040043c864009010079091705150900c4a100150108803c07003916001d2410a200c04036041c0f4082000300c48003107100b01c40d40d19018400104032084420302041c0081c03021000d8041080c56018596541d03030500801140003c51551074004e207010b10741e0701d211089800110510025901104404e500345011401590f0f15078001d43c0001c00030088047d40a501920301813444800140640001403901294000c0da007403030b600d40c5c2c0070381c150100ea000d051504049407541c4000501d000c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 891440656 1250 891439406 891439429
    0x503010b090a0302040f0c080a02030c09040207031b030509120606090606161502030f010b0703020619140f010806100b040603050a06030b1821090906010c0b0705090102100e0c 77
    0x402e0030310381541c0d9030040780031241c00c040748085031901c0301028460944c01c00110740d00a007244c20114998a000c1c00001514040c12134a04c0c86580c00241d00002c0c117114088014424054038100b20b001d40b03440c60301800603406041c620780240ea41c5024000d0b03048001c14074500c240c401400c6007240d81e64134001c001c803d612654440384c1d4440003100b40300c0440c0502c3c0120540e40e02a58005960f030600f032a0b944041c0e101603011102d000c0f020456400000c1d4045900750700141101091401d610025800b41c024000301c5141007098250f00c010800c080c941da81c0e4450484040a05480d01c0340c850380003c0a042100d80079505142c4000c01003002424400c0c0d10131948015030700d10000c0d100d9140c0c9c0d10052692400c1c1e5154001c5a45400c040700b40103014450340c10206012000c1c00c1d032800c0c98007050360071405902a0750780718403505400525281d008040302e107410360f0700c20341d258007910306003101500355080005528014801ea404802c110005c5119201c1c02400c00d2008010310000007040100100c0702 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 891441906 1250 891440656 891440659
    0x5010804022103270604030f1b090903031508070806010b03280b0a06081005060c0f0604120216030f230d0f03180b010303081b1201140d030503010b09 66
    0x40c50740c0c9191010034805000e507031400072500c50b07440e01303288007145a03160071142241c4140c800304000c02c0003600c0798401c1202d0582c484a40080005820310703903c0031508a0307100340251402c2c41403031400c0640c194040d11000b00d14040540074162100303c000c3d0748500c2d60081030925407100b330050190000d024060765222480e02030781c9440320030210840c0400803492118404098682201c0c100e14034041401c00064000c0d4600481300d49080e102c00c40381c00d182441510300400000509011130300083c8480c95421017010201d07102420685016081c100d050a0240c006000b10020058050b00e6160050200c94014547d4440b5509a884d0701c480c4610003108002d000728003800011900741e051000e251802c029465400c41c21a480302c2c0030b02a20800c0d01036030b0564035100114000903145000040c1980e03007500c0c0c144065910111703080c00c01002d1440c40740301d0340000700d2500040c21029002030705807940f400f081d000707103100c640910683d29603540004000c9201403005201d0b905144001d00203e01c3c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 891443156 1250 891441906 891441949
    0x6190207050703110909010e07170c0907050304021c02060f09180109060602100912050703050708030c1801030533040504260a0f0e040e030309011a04060501080402 72
    0x285962401c0c50090554403c90b1408101d4010490b0740c42c00017980396101c24204000d0104265110307031a80c462402d03010301010808003801001d4010001c103c4403646e0302010740108000c1c2400d481c05400780c2c2003123a04a21070784030006041610f26541c0b085890341613002c0c0600741803004424047c111600f00a80d180d0b00000d03411484280c145285003158024003100c400054000e051040c001c0c102040d0381000d4100034200100040028034025800c81806414a8025121203451604440f10700c103011001d0080c00d0040180041c240e2003000600281c800f01d04280780819108005606803a4101c2ea10410030070107120707085404c051b20860200400f003400c44142420480300000d81160016a402c0d2850a02d2050203002c0340a00224a002d00d00034110300ca0412a4640c0f00604c01103696050104100c54101c00500c01d80303403504284684020034040c0c98aa1404005890007850300d100303407615200c1100200302550030a48264429600107a54035686070350b454003400031801d2600c000f44210702 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 891444406 1250 891443156 891443167
    0x706030902120d030b031c0816030216060605040c2609071a091507051b041d01020c010621020906192c0f06130f18021c0203061902 58
    0x30303028410302c0ea14800c0f50703d000034004140e10500d49003038110b441034003400300d107001051286038020740465070100700e582c07540f062100d00f03e20440190240480000c0046448880304e010008180c0000701580c0064a0800041c416940c046454a88024064112480c1300d01200f110441d0404a01e61140710001116211036540b4108101c0c82159425905c0b203200c0030544840300e1401240d48046000019903180c1000b15035203c150701c400d124610b0400c0f844083d500a4440d44a80d040f038000003050b45051055101d48214080c040d40c80480381d48565440c224020400d00c00d841440390314824044185d0b00d51012030340c00d1000d032180143c0250b5102d00d0120038038034420301501d042c1010340596400000d65441803082aa9081e1180c1c00c2000380a200c1010062502e1001d00641d911034400c0360001984841c0c2810507005180700200d800210341080a0401c0048000710220311180c8242c4200d000382c020054a2030403421120b4000350325400c480d01180a02c2c003102400b4000401480c401131610 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 891445656 1250 891444406 891444439
    0xc0c020a09150b0306061b0a020607060c030c0801210c09090c150201020909040f020607020d0507051513140109090606030609050906090d27080601030501110c0706030902 75
    0x240c0d6070010006a031610030801e648480c0740301400041166044090131030424a0004000303000b0040c02d00e259001c0c1c54052904101c040021340d609a40140a0782d41d11030301c600701103000e4a003c040700c802017801d0000070100320344104035440c100d548403000a00c0381680c1d401d01d44600d103400c200a84d0020102d00021504880030700c565104148505400e8902d6450b00c100c03003c1813070080190034250392051142c5070a64a80c0101e10781d0050740800c500151300c0d00e40c40000d40501890401a412001c0885200c0c104075000071000b0960b20116030039202070620407402c1d0036620a22901d04a040180b400400c010178000e81820101a01418800076058035250648220b4040c0e501030350029895907001c00c126103d80c40b809400c124a00f01500007858100322041c0d80361302d0b5000106c101b00340c50740d0301640409040c00d0b0007605405044207001c00c1341e41d03400c1156203100c02c0c0016121035182501402804841d5800c54550b00c00c0031000d04010342c85c0c4407040d80100441f000c140d81061642c038100740350 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 891446906 1250 891445656 891445669
    0x170607120204082a0d0c0b0318030a032406440402150f1603050c0d0903050f0f072304020703020d032d0902040b031507081005090a0c0c02 61
    0x114407295154a07610744410b21380c03e44000420640c140200413105c0c01c5c101003030078058448159400000c811380c1e203495910140300b2100d6041d500841500002c6411b404e100d030b01d030308810303150700145101d001c02100c1c18007050144c0405200d510085144102503040501e0005030800480036840c064212044400d080c000c6882918402c210702105007208100071807419038251046499880b52180c140300b160b032207664452141c0780c13a201b2108024031481c4100b42c4070340101d0b049041000c05552035034021400191074000b4500040720350b40201401100b15680c00200b402400c81c1040040c080280b400040140d0314003558542107074040c4c44848030345c0e144c403180014644d2900c030354010520911072100040c100c507a54080384c001e904041c00200e08210058890351500040c58000003000c80c0700b440020010711186171590f40501900016101008140462911178180ca8950311000e5030340c0400009503003003034090f0300d038041001b02c040303084003d01340d01c148000d42840c108150540300c2d41d0001400e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 891448156 1250 891446906 891446923
    0x40c050702040b040c0c061a0d031106150f010e0301150b0c010501080c100c050319110105100e0a0c0908010c020309270c07080d06080d0f0315030222110702010917060712020408 78
    0x6c01d1040503680420be42c10001d903030380325210020f003c034000d60400006400940e513008850401c01001020030040c0d4082d8011403e1320007214480b85001d55640c10050540c100c050b4058580d4030309800010a54408155000c200d10000e100220041c0820400e40b40401e1691040d52076200034083c240074041a00b00b8002d0394071141e110706074500c4c4494065800e40b14010700344810010011005c1000300c5820b50b480d500007400c0d002c00b01d114108100c0c100c8000c901940301002e41d60828a01d03021094021004011101c0300346c44400103610b2406812024407461903072123816450740341c0001d20310304000001d000310610400502d40342c0704441c0314003010359000e42c000c0141600403000180800360050f803c240321100d241000d02c6a00e5031100249030708421840064007880e040402884007101c2e0408004003100001410000c848586020a0803508108409c038040b034200b4a0200d6880002020303a144145950300a0a10343d803248004c84100d8200100f120f4015000c0c40041120003041c804040d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 891449406 1250 891448156 891448163
    0xb040c0e0a09020405010519090c02010908210105090c0403060518010c031a0316090504030324031709210304170c091b190905040c050702040b040c0c061a0d 69
    0x280b0110030300402046490681c056440f800200602107194a40166480300b02e5444002c006440300742818107074003418211a0040902c440040c01e04c088404100000d1108590040705814a0f038881017805034131202921300241e1071b00140401c2001941c0c40d04207951240d20514148250441d503013106003034801c550941408a5140e4000b40001c0a51680c1904420b0007100204900d12564168044610040c05421640e989400000341414029000350002102d070021b001c1d29040005906001d02074140030032569031110b124148410341103481078501050b4010150089054490141d002810300d2140c0e586080c002444001a074142d40d2022101745c065080107003140b0a6400e04026040707000601c01100382c201c00d50890b0190300c4500a690114010881c5010500d003040000c1c1c5200c80c05034071042e803260428580608640d0703c0341c042c2031482c0c402e640c2480350040303100c200b1040c2e5260341214400101d00070166800700e01c094211250142ca072040350180b00d07081d107001c180922050031007034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 891450656 1250 891449406 891449411
    0xc0c0c140907020c1c11090108061005060f04050d0201120c050c0114010312050d140109090317010503190f02040c0201020c070f210303020d06140a050312070b040c0e0a 74
    0xd20508004030442d40c400b60760b2018110001800d070000d14103c0821407401c1480346410203032000c0100c4050003442c00e070b03801040e007845982c0d102641640c6800c203c2e0308807071500071400c0000c0c4905221040d41c10350341c41503407560b040c1801c0030240a035800b00440c01780d0402141340142840b460b10340c451102e0055095a61680e180d00c01c1800341e0940b880710100243c112840401000130510ba441c6448201300540341103a500d0680c3d51000000d840242e03160520303140c0c0800006140340c001c1d44910100c912a40b00c41042d602080136000041c0000d108046c0c041d04844500800c1200c44c0511050f009d100f0380b10690380e428241c000c10110341d145080031000d83c0d0300059810620400f00300080051141c00300d0b040c2c07135134241131441d80d0560b40c0241406044602099400415000e5010340311400300d0341d5000c00040c3d55484401020481c111100c0c2e00401c51842d010409086c0840e00520350000551a80e01d46400c82e5520300c3d0707404001704155682190b40c100410402101007143e409860402c030b02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 891451906 1250 891450656 891450689
    0xe06060d0e0a0c0e24180705120f0402010807021f0c030e01020c0d110a0816020d020409110916092303060a09060507030b030604022e0305100506090a090c0c0c 70
    0x5901c600c060400910040c0e070424491040305d659030810003140d80081001900302c580741c61400b5203040c050320041d405030100103820840014041001a44124000d80e680425130b00c6e541d10a81c1c42c0c6070f80b039034206001c542407651444940c442c1d40004031b101c1528980024140401c00010703007242c2205054440503040b1007100d801d101d41c41090100720240d010080e0110490f540d481480511070040440c1c80965180d03100c0c010b642d240403001d0700140c0c002d08103106415842c9072840d0009290120301e0710410041c400f264030728000c04019404c000f15901c1c0c0510030b90604440c1710b0b0b290358000d5401c4110881d480c080c1c1040d1014807010340528030030080400d0368030203450030341d003034640007050b0100301498040c3c0000143c1d00000c6964005405588100a40c0d04c92280040e4180365102c958007030900080040d21080d40c954460380c4965008680410056181c0042025900c10300308843da0000302c1260502c60305140d035100c45c8407110141012101804603980f0300e0403264844d48500c0e07140750f01299 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 891453156 1250 891451906 891451921
    0xa2708010903051306170f040318031a07020c03070b07060f0213090f02030708070e0a270509061006111504060905100b091f0b070b0702070e06060d0e0a0c0e 69
    0x2031340405800d60303050121005090500381401e1180c0201407800314050740c00807500380b500540000d0540103486151914082d12402c210301c0440c00000403c1c0d032008080d0002d142030703101280c05c0c0e43e4260020041c00c1d80c40d2800b1702c0038926810130740003600c8840c0d4074a2102c0e020308040c401414100520000d480f0b19a00d08000841120001e120150303005004004000300316600248090340105941081e440514810020a249000e280c001202c64880c040541e003042c5040155460454003401c0288021b941300701d915500c0b4041691400d108030300021080c01441d0048190050001aa40c2124801588088003140e070381001d94068030309650381e0305e030501800b00502040d58000d100980900c10054400041101701c030b00103000d80b032240200c00101507984000d140d07100c0181942401c4907202c241c0340c101454008401d032031000c0075100d04500002e21402c80601148142d00c0240520704201001800f0006407201c028030900c903004102c1d8079000946131700a541c0107841d8507142c00c0402d03c0c0c10712 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 891454406 1250 891453156 891453187
    0xf2407060b06030108071509060e01050c0102120406020306190320011107031505250302090d05010212011d0f061009170609070b0f0913140414120a270801090305 71
    0x2441e11f00300484104180241c581042003540700000070f107012a40c0d4590107000364024090840340344a250041130034403051240d00d80180d40141c4003200c40f01d02030040b800341e1203965500e80c84010207041d060f04001c1965001307004070844201042c1400d01c03c4040c80754140b420124150411901c0d02c5030030b200001a9000e0344649640a80110401541c001e0801103200f500c000c62900c9104150f00012040001d031200c0002c27118507035002c0e0007075456001c075000c00c18103020240151000d01c0440e840d9400c25550224180e802034600f15240b0441c1e03110803040c80b00e001c803080d002c0d030140311400034005030150400c500c040c152801807001d0a054240000340e141014030f55840001d1542c005d11010071111110342c100c07450300000b12054484103000e000742c040581a0051148006003c1c0e0b030800040c850400c80329052500c05600340c4038113245910110b00d582c01840605800200000d0320030305140e09040005c09821303c40745c0050a03403aa207015540c01c0d2440d0840450003d80041a0414955180c2303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 891455656 1250 891454406 891454439
    0x30b0106080a1a0f0904290402030c0904151109090103030e011e0e0d14060c0a0e10080c03100b0a030b0108010b211302040c0504050f2407060b0603010807 68
    0x1c160340c0c40141402000242065544c0b00c0c410310030f004590119040103c5210740e02000c0c40784043c5101300d5115a4800030194400712401d80c020b0007100d6a600061030017168441c1704551221328000034260030b80c424070081030907201046034a8410031040c0d0040d503c2e288440d00a600c6075543d544880e04001c00140356400485210200c54010001e44284030b41110300d00102200c25a4a0000c0c0c0049060080c5000108046070100f40184802d00c4003007c000c0300282005500c03a1148416410b402e0140303c10001894211000a000240400c1441502c64011a0030030060303002d03450140d803078207aa52602da0003100c503d400310340d98080380c0d50a541c00c85000350041c1b0780000c3d41c1d41070220b2003c5c0042e0f0110000905941590264000340051000d000d241074000e0b0090810090f040c0400000360465001d40105482011141608001e520388010548002e160300308908480c11050900c00381c0a4100d41402c61340640c68683c1c0e0b81298aa0314065402801950000d1040f84e01d03010240001034000e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 891456906 1250 891455656 891455681
    0x40b0307080c01050f0d180b0708060d080c1006260304080307080702010915081005060c0d0831060c02061003030804140616020601050613090f0204030b0106080a 71
    0x515010052840d010900d001c16a2081c01e004e50345000d0340c140404940724650140850b03915061030301086040410881ea4407074842d0488000075180c0c3d5034140d4451004480745980b11030440f009400040d8900c02034101080300c107040300c64100140009c0c10039640160402219168441003400c10481615000100c03600e00b90f002d145080d00701102d55489100d115006001e400c1c00040c200116403180221000402c4103041c194050200c00100410a62042e24580e6104000740c101040d5881c1075400c036084003603020020b00004c440c0f040180d5403503071300502110f00b0740c5c001d14540c1e001168040007441d0045400c12110312103001458508122004942013008551104080003200c0603c400d040041d203406003804815075542e8030700001002411010a01e103801128113100039109082004640758545800340c4015a0f280c0091000600030032040e09091107441004016084041d840485441820003000d49015100e40301c0005402083e03020b000003400302410800702110034420ba8152030300c07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 891458156 1250 891456906 891456913
    0xd0f122c01090b0c0309100c0302010c030605010507030f0201060b0c1c0c021804052410151709070503030c07080601060e0d02101106011205100903050301180e0307080306040b03 78
    0x100e08000030b201c18464050015603150009100030380100c108261482a040107103034200d0b852440100034501d28400b40d0403005036091030100c2034028041d0203141c058030010f1351080c0c02c0c10100d80382241d11400041015080d03560f95000411580c02c02401843e1080c00c0748000c00b0301e90700003d01c14010711400425801003159500e201e50041c2d66070a40e1842032403588180d6800c0d610b1b503040080c02d00c80e030b95084d00b4160820001c5500e401503607040d03c911501d403c44010102c06e40c0c1d0b0104403000705030038a40c500003c03101e4696210180400740500c1c4c001040380d0031150000d40b00c1c00828551b501030f02650040c1c1c2e0019004004d07486082010364050b0015140c017440c0c80d0714840220368280e10a43e0002e10524800b40040c8000e0302c45e40702c400351a40c80100311140c84d607441640c0340700c4091101d000c0e2142c0c0500c040c2881000da00e0300450084550554034149180c1c85e090b030348007503011014000c40d400e0791150b002400c1c07500c1c200040c0c200a401900340f1552810098100003c441c40400c000780282c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 891459406 1250 891458156 891458237
    0x50715060b27011413050a061e0215191e02040f080d020703020409320d080411040b03030c01020406050301061214061e040204091b080103110d0f12 65
    0x9900401c8241c107846807002242c5c5804003c0292280c000050704030325081000e035000002c503242e10034248410b80782d9a4410351b155180d00349040340c48407401240d060010140b0000314803c81c450f00d658000040c000080003a6121030140c00ba44403002c4511115440ba4010405122010484c00510300403c41c0c840104400045910081e459003d207120103481075a83d50000300601018140904040840580c2e0308080d618581607030101d48003201400d41180703e8210301a1081d0b01a0340111301072a086a50410440302c480100300c0035142d0001216014041804000280d0000340007400290095844031030300e82d8101500140a40720b03034803a001902d801c0c541d020b0f2040c603c0403003082e041a41134944080c1e50070340541d80700c1049050032009070018070010b00080d5512866005001c0d040d00e80546140f0303020300c400c0440b01d410080c0005840510b503d24100d00911f48400c64240051144800a0800b101d43e02e0340c4d0011030075100f920021500444903112106400c21440c082c020719070781c6129040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 891460656 1250 891459406 891459409
    0x15030f0108150c0703210c11010603030504050d14030a0206040611190e04060b160c0902040305060a0b010e040f0903081609050f0a09090f1502090907050715060b27 72
    0x482c2c06068028900f0300000c01c54181403181580710071100c200710808450742d101000c11001425540030300d0001403800300d400e6040502c103000d2101100d4041d584d840c00c090600003040326409810900701c88401000a1003050741c2c9050000d04140c10090700608464601402d0000603074080003d0522014801c1204442e45110000a046010060301d0b2090380c40e804100450700601c000d40200c82c140e200400c1c82e08403d0498044c014601c1d205600b026140ca640310740401c2607001c0d900004007690070510024848800c0ca80c00704071034400c149000380240041c00045801c8603000384002110300d481d000d07940180f64101c4686038001e21000e00d40280100b0301c080c001c1440c90700b030017040e118108000b0205842e80e200f1003440040c0083d034004009404091130007a90340d1310744100450341e140c04050707041c440744800c2c82585c1c006400908850802c3da0f40b050101c40c60f0f0f01c801000c8401c5180403424205a503524480e01c000342c0502c0d03008582d550b603407070501a0b11b5010612502d041510040565015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 891461906 1250 891460656 891460693
    0x1101050a05040807330c031404110603040c0b16050f16170708240109060506030606070618080c1002030103050721120801050103180c0605090f15030f0108 68
    0x101e500b00d400b45c542400240c81c010f44400c080d401c807402481122003140d00036030a0781c1c082e491903c002c4c0c808000701c2103028407a43c840441110090700710211190302c440d0900b440001145e00034807038560007080c9a01d80b569002c86400104001c1000c030000754160303081080400803507200e90445401051f41da40c0380b0012450340009402a120748144080c440d10f020201000000040d260150954005c0b010171480e44134075510352442e0200c041c920304000142c6011500c60710040d80c0014011500e1039440b002481b4042d0320901e011518159200c1d00d41788032021200162602600c9185682c0d603600160145500c0c00b6103200c040d9500b60310400040000030400641c5034100c85040d4262041a1054101040480722080010340041c08841060a21561100c105410f86600341c908100407000b4410310070016100c1c260051401702d884c1c4080c0003c82c001c0c0060500000000e0042004070000c1001c2000c00e19003006031600300001000380158502e40e04520f80c0544080e000800b16610030403088100c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 891463156 1250 891461906 891461917
    0x40e090c0a050f0f03031c061d0412050912010507032301031217070e030d1e031119090f0b030f1306090b01061101110a0909020903100603031101050a050408 69
    0xf081c034850760040c900d42c85498a8090958006060303036120640241c1c4800180c550407a00c004891400340c0200721022080c541000d00c01c2c07a2002c252181d40d0780e230344200e1208000c131005018800c0500400f0081c0e9503018807590040004000440d81d405d1006002e005d6414040200e02d11902d42500100c80c05a00d000c558112038000440c106220341c001d0050b070380e500c2e01c00c24680d1111081020043d4003500400c4403107121314141c08460f04511030420032110f400350f20194180130321491203201c105034441d42105000d004070b5001d5070304d0003a94070345000a8049048241004c64200d03e0100546d1404044240041020010092031b62900c3c401440308854024820480c42d1040b00b419410321070395602c031044040d4010a030002950f181c0038090401d40700f065030340728150300b0f05420780004024079007070303807403a0005845244145041a080c4800b07900924203103500343c03040c1140211103254a00800d80214081c0e100c3c441c425004101403030030759200034040e02782181040244070010302c041c3d041300d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 891464406 1250 891463156 891463159
    0x90507180c110601060f1d090103051b0904031e09090e01270201091a210103020f03010b03060714070507140a0801152601060902130e220c1a040e090c0a05 68
    0xc07071201f1138510311070b1094014001aa00704c020700c00040200b003c0000da07002c040100345e14551101000e6000c011896104581c02000114100b00601d058600c2e0402e180c0d40e078040c0d041c03010303105483d00564000c40314550404a2a80e4403200c030b86002900c4d44409130740042303019180c41c20790070850b00082d01e61501c510812400514408080c2408451101981c1110f6110b03000703c0006405010800b000c201d007070001303900c19807010300908050f2605215100703100d100136000d48005c0d03035507107002d0714004011040c4405c1c0c240304103c0080060818044c040182071118810380c0f0384c1885905205507400940c0081c0381c141c4c9041c0c0854000d4040781d030300c44201c601414110ba242c851041040a00380f01d14454100303d03608083c000300c1d0500950b000380c40c0400c491108a0841d50b51440c0800c0b00e50010345d90200844070f52600c5811401a801e00c152005009450b28004070381c0d2030801c540b070040d41c034070f2801c1188400729042c04149100c0b28244d4010043c50014a481e4540d44002440c2c0380c801c0c4a2036 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 891465656 1250 891464406 891464417
    0x21c1203110f0304141f1b1107090c021e0708060708010b0306130603120e040f0c05030103080306270f010e160c06060503010f0b180705030a090507180c110601060f 72
    0xc1900e1001c00201600c180c0300b00c0742008800c070746d040c60340142c000c49295002038034420804002051161a94141c60a1100001c20035240b500c00504010088400e10408601401d60102c0d05151556640224420240c0c02068a2850b0400707050801002509200400024400401c009415079080d02d400c400200c82c009802c81640700722400400550340700a0404030004854444c19810903a110f4030180300750f906000340105207800c03500301ea40c0fa0030800c01103001800140045500d0b43c0145030701c002c01428410b14030a04202e190141042007135002d031a216080100440c600c1200100380c010810781070840800c0c10140e0910141104c0710580c002006000d83c1e0704418444250802c40081c44050000c200c50540d880c8041c028221900e0b50501031b2014601c00e800344118030f2580c40c8200480e0782e4450541e01c40c0300c9008040d00c03d01d08191028441c2c240f000c120826546101e80e0751b081ca03040000f0703150094842c06041c541809804071169000039004216440e0480c0300c000814009240c003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 891466906 1250 891465656 891465683
    0x1303210624030c0233070e1003060b070305031003140a050c040605100e01031401060e0301110a090515040f060e03060604050613110d0c110610060e040504021c1203110f0304 76
    0x30045e103c60103030160080d80000c062259031034101030340d4020084103403240d640658210f0419400d89100788101c2880040400c401400300b8402c5000e190002103024040303c145a49071589095030b80e070400800c1d615006140201e003008002c01100040441c2600d06224903460040001c40340c00b0520b00309410f102c100d45030515580e201c0c0d400b500144034082c40c1e441055850718401000d1010540d1924020b41ca0a82c852401c000d21105442d82040c80d0364800c10240d090601b03101d454900c0c4490850004414000402c00070301e007240b818080c0c82103584580c4144003a1041501e0325401809003802185424140003880d120007014008000c0502e101044510194013185107601c42c1c1c000004500c3d140c10038040205034408074480880d640002221095181c500f2240700703d120500c0740002140c1c0064a105040c249a042160300074002000d95020300070041c10f4940055000c01c0489041480c8880e428525815100300020668036699050800458582280040c400030340050001c0c10003006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 891468156 1250 891466906 891466963
    0x60b04021603090501021e0c12070305240c0702010210020a0909141b0a050316090902031e0109020426010902030a21081303210624030c02 61
    0x122038507004600520700c41c00d00a4100100120041e002d0140103006491400c0043c804c102140c080307804d015030241614044a204121420b041003080f040340b400348a20001c04900c0a00800304141702d10442c20464200141d14006101c00041c8054180102407211a0242c0da002842a20403d2480720050750348102d2003056650211a9100f50031040c10320a0030820b0980280c81d080c014131103848400c0c581a002d21103554a4003450a000000030300501c00600e04420102140c4d44100b5141021114940c0b280080002e0380e0048031040040e905c0410241614641c04070300c80e0060035001001c504203820000a0b000440d41c0e00d030a004680342d202e06203141d0000070741c8210245c680c01000c989181c00c0e5031410004a50000a400701c0024101002d80e4200d4016101940300d030003549800e090480e041c3e43c0c2503961074140c01d40212004498000304c44e04560303d104900103010f071108041c42c510f2022007070030762100c8048800c00c205030419242843d125000034102d196130741c1c2102801c510402000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 891469406 1250 891468156 891468161
    0x30020405071b0f0203060c04380f0306100503130b15100f02010506030601050a09090c0902130e011d040b130519140703030906030b010e18161b060b04 66
    0x16856400b1070b6144102404021a4042c1c1031180751003601611080c0c0c2e80c072510f0311580c0c0118800c0114500c1c4141e0b018005012a000d021560700c4842c08402c0b00000961030105c141d000314660040b03030f141c0001840454a003005190207480280e20707200f4a945000b080f1041054400e080c01040c1102c15400328440782d5004035481140e84c4003500001245200301c40060400310030703103c50000342d443c01000c82d0290401140300f50690b00301503c0000038903c5e1050741001041e24a1043ea4090710b602400b00c0c1c0045280010014180070030100112a81022590b140440e01a40308200c8200e0710040564030180d9000c3c0a5441500038036150a2545d406807008002040c1c0d00c0000c21b1070054920040002c00b0402a00000d01c0c050046852031070b061008440d51110316020240100d000c41200b0000984284c121480014041c50301549450101c0003041c4c002900006203c241c041e00800c00c00c0c003001603e26028140403074070700501034060310845080c00e8210f102000d001d19841d00050740654440d40c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 891470656 1250 891469406 891469427
    0x912160503040b1306090e040f0209040503160804050112021204031b0602130f2705060d150501030605131505060a05281703161a010605043002040507 66
    0x6100d0307039441821401003094072160181c00d02081e650381b0f001c10700b50061031010307120b0307a44070050a46100c01902040001c0100030030403221480100010001d00300011400070040c0e11030281507840350308000014140d1100307090516100e600c1884804031030343c02500200c0d00140c060604807030030138030302c40d42c81000691050080d10035800001c00103041d0b404c0700402c50441d80702d040c11218080c0c988104a048600b1020004498681c0c801030b011811072940c23101e5040003000b001da0721460119a1054413440da0400300001c0c441d52000100180959805042d40c4250703522900c82d040c00140e5140c0c42140703240544e40310703695074480020741c00303458201c60a40906402007a42c00012072407501040c3c1d180200b0001e1202c040191400104020318860312045556054007a50074400070320138000007000340321000d0301c041c3c1d003030320b0000c0c1c00040b00b0786e0003130107441e69542e030994039401e2042d00a1610052020f4220002c003004451041203503600f101c408031039045402041c19154484202d48500d9070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 891471906 1250 891470656 891470669
    0x14180c03120309120c0609120405010f0e060c0a0602030f420411180f0a0b03060402220914060a21050d050a23091c050a1a091216050304 60
    0x8045c4810b03400003800314868003214023111142041888900d80c940139520495010030118105440300900404801908030406480c45080201613403515103883e920041c25a82c0c1c1e0350020a201c00b6a649409003544140c990952071888184400030300108904489604603503401c0e140a040030440140504031a042c0040c424030244c00880c02404581d80580b5080c060081c6413a45a40e050034110400450702c10006c11407044a413401641030b0396944000d141c41d07807081c3e080160019440362424201a4258a400e225003882d06001c0f0b02c00499094440419800794000b04015003036030342c4603449080d510000140e8150115982c001604100b00c610010480c0c0036200d00301054a6100c0f01030315585020750744e03041c0d034020f4401203801b10f0140c6040000d290701e020424454542051a41804000c891903000240301d00c003621002d08008d68100102c681100000f10300200c4080244502e80001c09400600091071400c00c110704288138201e444001400c014612a00f031100034820b0b940100103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 891473156 1250 891471906 891471943
    0x10302010f200d09060f020705030c10020118030e0328020d140703150f05010b0403030e0a090501090b0f040b0904020f210606031c12180614180c03120309 68
    0x34800d0004e040b8480030f014080000300e140c80349031030851000410404460024000d007a1b80035124061010a090310314980040d9929010034107003150708041030180480c02944e41a038114a0300c0105400c2901426004031076180702c03000c0400d0080d040c511201083d604940007000c5848a103071841082515a282d010700e409401c100006000408000b8443d50441c07a07410841f006902b03c014086900a02492160f10000d00080c80024087d400c03c1411500050881300c03030903512001c04c010f80e80240c000d015001e45600700b841d80c908182d9840781003100c04440601014400e2400310701190070040c0040c2c801c0c07221070306001d515141c00c01d54402e003040c81000d8505400c400c84480756601c100f81c407640d0180c843e040740c1075900c8a080c0e5280c048000d4941d035004a04c0450392901002e440c4890140cae000d03070000c2e046000003407401e1250402490102040c000185401d51591042c80904e2607580007d030818949502596004100322480c1554000079548944466044074030300701512010b000071a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 891474406 1250 891473156 891473173
    0x513030605091005160c15240f0b03010311100e190503120403020607060228171b040306021b030c0609070501030c120506040f050a0b041103010302010f20 68
    0x10b00402c40c400035415021041c0500e845400300600d00c401000c1e0980009801014900001210240c007080d80d51003540010440b6804456140a002e000c214052804100000c04100d600342e0520480000c00c003d0038803230708562641d00d410151404c2d640c0410f2240100c1d10360b51070b0385c600a5400607203049010b48800c04101100d004404020400e0103150f11030300c545200c0041c803020b41070880e0142c0e640a80960b041c0507095643c1c0029400030095414000b6806007881c05801030b03a0600c0c43c0d05910380e55942180d1040050340340100c0301c040d107030a0b4241c800d5000b0108043da000e084908580d0701c024016683d07080300c0c0400c03155060000c201d00c01c0780000503001e0300403040056040d010300503103810303524a181d840d0015803c6a000c000804040b40c0080304c01041d00c112640103661141010300080350616920100034121207081310342c965415500c00d9180406d0070035210340c031450418100310b103186505540010f0003007400041100100001a041c030036540342030415001e29400c91504948000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 891475656 1250 891474406 891474421
    0x10f060902091207150c0302010e03130312080105031207110904051f05040308060108060316080607090503121210080f060a0b030604020919110f0702240a0513030605 73
    0x35804000303500c0c400d0074899a4121010f0780400e042044840e50205052507112001c0c06035a501c003065016000d6569414000082190070310003400303048001e241101036141140b81c0001441c1046503110100300e0f02400521040d03d00044003180c0e200100c0409442c0c00310703481c0240321001c164160b05d800810210510041120005842640c3c1e01d510f035404140c0d58040c4e607941d08407003080300c0240c00075070000d011510950080300029002031010741544c075110035805111828801c203a00c264541d620030020000041d60003864003018100c110084d110b550068500c2c41c119000f03070005620010004030104841c1e207141002e110003082c0e10000c1c2d603071030b01d4203041d01c5496000072205205282e00f482032041ca60310300480c0c031074070031503004103080010340b20000d4004503500c01d8203070f03941a2a5100e80d841182d50709840a8a007005051800783c0d5038141a01c10f1002060001c0c0300703118640a07403580b50194800ca0400d44007613000074900283c65a00c1c09142c40303240c4840b544007600f034902c0d10090002d40e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 891476906 1250 891475656 891475661
    0xf04080718060b0a3213090513020a090507020c0d1505010e01031e150e0105091020090607120309060510050f0103050405161214070e060111010f0609 66
    0x3801c04409040002c00c0e0f441140b50040d1040b0540e1400040302c03070b074101e8225424015809001c500d400901c00790311101c0402840c859211500d90342842500c070404000700c555a00900307030302a00d0070302000c00d8544d851f40030480e541414051044803e480c3c0c000113001620800c01061440001081c1160040d01400e0850044420b9403c1490150500001248008032141200d040300c0d482540404c0c54078024040418840071110120786045240030185140303e00c40c06124a8094050700000d01d504005460a03d003011754215000c0c19403c1a01e4042054661810303141070a02e00080c03691b41e00c90620005034140f080034002054041c02100301c1588940c1360f804013885621810301000517844001e0201c2403200740e2f03c10640d00518a0942d01840d511a41020b50014815030444600d5961f0b01041110b100140c2c100c600079499000d402414810404440d10760600c1120150100310309010148a01440080038641840b47c45102854046001d42c020a04074403c03040411403141c84105d200c01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 891478156 1250 891476906 891476939
    0x40b070c0602010b060913060f180b19051c0209010906060e01020715030c0e041103071d0d0b0921130509130f0f0503030f0402090906040510020f040807 67
    0x115024030a50209045005129a0007040002000141084100010401d0110090128a6029807139050000c3d80c4848a18010090203850f000030780b10034800b0f03000c00c00301c90b803414200d44140b00303c100d4103a810f0700b43d144a1003641d100381e40d49000d482401e4983c0c405c0d81524000290040c446000008500c040341e4008030581d6003a988003800380c00140012a40c88106000c0d0740038400595000c0202a40607a1280001029500300b101e06440c50720009400c881e440c2d060203440c01e000208112120364010401d018030400b40a1003569001e22001080944880440042c08100c0c88008140c40b48402c000d0391890b8940c0b83c8500744030b070418042c450030a8110140114504108080c0861149080c0820920820b03015510070a4850161100000d400700d8030019200c0a00040c1050b01082091000f1031007003800c10340b41c0c00107090038410301000700c00050100c012508542c0921000a038045440b2044008800380544c0b9500381083c456a00d00c565403000450b845600c100040d2940250454071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 891479406 1250 891478156 891478163
    0xe062e110f0601060e0307081006050901170604030804030311032a070519030c08030f1b0705030a0c020307080d1e020c03301b010f02040b0a1d06040b07 67
    0x180103888988900d075585440744240d6416030040c400602100b842614200c8900344000c00300c0380710690301d80e040c500b0003c14030f14982201b5103640c8103208074200304040703c2c0102101610032103646020b1010035250b40007e000141000701090120303092612a40000c0e042c0980d4505090f07a03401e05000c010f105034a030203c1c80c0800c80c000e030640780ea9141c200095500d8517800070090400c00b14520640781015203220002c03403d000155440b14017003074150000d14410402440d01d26001e0910f000d144141c0c401c0f41d501904250300030001800060804001c2d1380300c1ba400b6042c400b6842c0b4031880024101022500680901e115104000513400d0344800c1c2c81c0000d022840c40e99020602d8018103d071110600150660598824004032004000c0510b90401502d00c000848100b807000c01c0700500c26510031000c146004454070450a80d106007071007000c011485494086180c0740c9440b525004070300400200b13806001c5d6201e04040c0100c03c101c24034002c1c483c003c00480da21f940743e0740030504981012400b034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 891480656 1250 891479406 891479417
    0x1b0d1d030705060301120c08030f0d1503080f0c0f1b21061009050c030403140a120c0903060e01090b06060d0608010906020a08010f0812210705090f030303010e010e062e 74
    0x900500109c00c0380d0300c541400e02d1051a00a40040c11005458409600d00d02d4607c10798000001c039505101030031904c070f030580081e0381d9000340710421450810040c030f00a1080e0000980039600c85142001c0602c400001d42d0729000003541ca4071180482c60342541130079060300400003000446403010040505603865403200b00040e07151409482d006000480b4014041034500c11100c0c00780c0940b0001d008002400d01c0c1c48820085518960b1003030b2100d001160007c201a04c806008001c1640207503215400510000c1010381040d0701c54070703615003018003854090440021a02003201060300810b0190441c14001e00c80e0510307910f003440081d0712036041032001480c1900040307641d1314600001c2040b5519400182a45034004103010f4081d4030001c0d1540341440115071045102e00c150880504c9520030744c460980350400c1109001240c0880d0003200c0c440d800400050100300120782d00d643c1034031803140440445603641004174001c2c001c8003103503d101d00990180c060a0f00f00c400001000311400d5900c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 891481906 1250 891480656 891480659
    0x91c120f4a07060305090a0804150f050703140c030f03040506040c0812040501030209121f0f181203061211130e0307151e021b0d1d030705060301120c 66
    0x18042400c148840ea09802e400012081020f98400c0c0c02080c1c00c076001c070f42568096002a076800c04182d00039844207800d20740c074609282800340c00c10b290260040441c107002c1d1501e0081e81d80200f1003000e4400300700000602040c0c0694031039040044d85d614007400700c0a02e540f801e260400d0703a0740d403204507000c54200a031414089404a40842c00c043c030002c0940c1d0305400c080c208030055011750026025503800404c2c44070801140300c400c1006244902d05100b80c03200f07580f10010390f00e095030305c1440721071a030a040a1013030100320b0000d40c01da14491b40080006540b02c051010881c06002e40c1d5100b0100760304d456191600384012002c1c0503031040412207c41080380f4441a880c010303a5120708128809400c14030074140820301c045a00c000b4a541d0b400b000548522000d50401d801c05c442c1059000306a01081c0200d05600580d803405110601070000c00301c06411400040000901c0c02d0380c5201c40c840ca43c1012841c1d2410055a030107400002c01c15500c030b40e10790709480704041d00c8110944071034205100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 891483156 1250 891481906 891482021
    0x10b030d09060504060813060c0c020907031526030316120b0d03031a030111090f0a0302090c0a0201061503141303050301150e1305091c120f 62
    0x89074088031140c0d114207041c549016015507507403038001c0a40341001101141c000c005030072441040040c034000d403070300c02c1a59060700500522002c000c1c4494281072074800c150f00344c04500301c02801154400f038142c18a041402d69003404800500b603219503036120100502c26452481d10041003410096590401c06d120038003900b80640300441c4517650440c040d07280301c80100e4403a030800d200b401840010b00c0d4100645c40702107421518401c1d1030200d03c0f4000b046070340e1203280811001d2920b84040f10340550450030b5030001084c021010f40703581c01c5500c00040c182005d82c000c0d0401b50091110b4010003041003101800a8050280441071001e6641e4000000b0204407800380305554254041d61041c0c1107a08245513840c40903542c0c80c5030014440940e0790420a41c0d90882071038107160880c0d81c0450a802c00076003040c070b8441c030000c00d01034150b50000145c3c02c6a40c041e110f054441e03600c4501054501c541100c0b00300502d40d81030625112a80c25060104080c3c4240000c80c0194500c1c8001002482120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 891484406 1250 891483156 891483167
    0x7020607050a03080a2901020c0904060609060b0903070b0304150612031106190f06052d030f100504110d1208130305070602030408130f0608011d04021e040608010b030d 74
    0x40c5e089106040300c0b40d004c0e80000c84204071b1600810103004403500e542c03014000400d81442150200c0b000364a450702800040f00718007a6000611500c1e14007400c24451070000f03900d6606500603540c80c0b400c048002024405048130214030b4060b006020080c85440b1200030b842c03001405415404a1002990941a0000040c000b0b114841500617607002d1085441e0500181c181d0b40400101c003a2280030104582c2d503511060040000c0724640b0f0b44002403601003907007401803540d500c14030a40124049810509011800001740451841c2c00103d650712031424180c60818444040d4124981c05484420081c0800d5142d6905505450b850a2684c4586120f400e200c4070280041c0010014452a170000d54150041c64000b48140540c85c24007000d900c440b002e891060344040c06080c2c1d903000c1040b4040c2c008018601400c1c04e401d103070740e200700910704c0507200b410043d000038024022408000c500600305960710210120041080c450695075000c20313800b0300445050203200c0e00a040043c01103a0264 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 891485656 1250 891484406 891484421
    0x20609010c081302400c080601080f0a0f02070b0402011d102609030a08090304032d140d090b040501022d0123070c0804170307020607050a03080a 64
    0x80c52028801c825824400d41400280000b034802002d8001c411000b204200840740d042e414014600340001501041c5c8255991100c40b0000e000e8200e013804043d9a0052009901c403c806101000c4c41c0c6410b410500106100000e460629202003801c20030490050703c2a40214000d9039001248500f080c1c50310755034000c049101e9808841300202c3c0c80302e02e01030002040041944c00364032003102b60380000f5a0f41c50f4000c5a03030900d41e4100060010125402445442d000f40c3ea61000f142001e05640d036682140c00e01041c1d218542c00341442e003142600c030707000c140c20707900394010758080d210048054010707031310030311003c14001068818001003500e2240400303031030455505038000d10000f0485c2518445201080b4040f00d806820b4100010554609005c0c81c8520540d620000850407110242048600b001506150400c540c80e070100d80170603d00015a4190351720f17104051038480f4458a940c0c51881030307010003134002c980450880c0910402281070300a26000b0380f0751400355a00c030002c160488040c3c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 891486906 1250 891485656 891485671
    0x30c03060b090f06040c02030405030a141e06010302011116380f250305070b062707020307020a030602040302030705101e120912030f0c08041b15020609010c08 70
    0x1104001131031440d00b0b80024050fa071190050301c0ca0f1580304e40220f820260746440c103840081e91105103c07072100d001c0000e0b941e83d8007a40036522002c00301c0384d002074840c5018480603040000c01d005e40b56000c01d007448214452074140b05001640c0740d0307070308061185082011000d515a1581d00200b0254242a21070603038000c8546c0b103152030289190403481c2907400228403c003000700e50b09009101d100044014140c1580207031212501c8031090300c0d1038104a80700a0087d40510024000b004032000c900f01d11081c00d068142d045070f03560b59000b0f4124070b503005008003e980611001d03800024070100341d00400a681c000e809655030151a50148000114922040400604075448581a10400404a1942c00e00078a00280303003c114903c500240c079200705c4142d03900300e50006482c08580c2c0500c54505030a420113011b114048020310007500c201c1004001408000070038402c080030650303143c1c40f48040c2c41d662428214140c15800002d548001c00c031010f0510758684460b920341d9900642ca03c510031040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 891488156 1250 891486906 891486931
    0x40b06090d0f23061006170a0e03040311130c080a0c020307060906020309250e1009091b050a0e010b070f0804060f0e090f0708130606030c03060b09 65
    0x141006100401d03999610680344a04421410000030354000c00f681000011002c80c0c6584032840245141480c0e00038011034000705800c04100b1070307a5040302d024040381e11404d11102890350307000c460030040e01e00d00d8440e0509010018000c0700700042d0912002c010b1205aa081e07aa074441551000201e80d41003401c0030219180c0b00001c0d4282000383c0180309840f0309881520f04051b9135540e04004d50b45214000c8816036004010890841010491859041408141d640c2c0c440521129881011120b01032220040c50070800581d1401481e5138901c004c1110000400440c0700e94100960702c29001d07844042000154000042c552400905a1040d14503c000c01410b5910b030443c140c09580c410b0784201c800c00301c0a04400e000c0b40362000540000d10307880c2c40300030400d03c0340301d00140303861064018144980840401d001d011501d50701802c1e4400214200700c10325132101002041d2204490f64000c10681c00d2450100c1000358004003002100d124210030301900c0700038401c00a01c18821504400d5104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 891489406 1250 891488156 891488167
    0xf080d111506061804050a02030906070905150702040e07150f020303060310020706151401021203090a141629070b160e1c11030f060712110a020a060b040b06 69
    0x140c543c0080a0300c012030242e100c2d02203080000b060645d40c04403010780c8184d030b01104218552400307210702a4010303160702d4442002c80c10900000d400c2e01341c6180d410062040070401408540342e0754000c0070048188011900034503924008225540d5001d003007107002501c240700c20f0444a000205590140d64010058200d000d0071000d040e00070f411108042e501e5903143d0b5111098650303805200c0016060320380c444940c2840310400a842c14071a503145400c812410030403c4403d110100300c0c10025075005045100510040005502d411412102d80032180c040d94000511507060407803c0c2058840c0c0b19241c0400c1d404402c00b2446802091405003580c6004800a100705d801c00d04450100e007a90300b0841c182045a001094000380c583c08000941c6025141400078413200124a20995008600501030204d05045c615103032200030f030268041c010a064415001d15658009031411130001100980390780c40c480b8000c0d5a484000426120545030042c02c0c0c941d41000e0051040700c41c070141c0f0702032410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 891490656 1250 891489406 891489409
    0x180312060f0a21081b0a02120703030509040228270b070b101206060306050c040506040626040f030f030c0e060c01020c0102030f01140a050a050405100f080d111506 72
    0x5120704044030154820440c840c00320000c2440e1001902c2c045c0d0081c4046d1000b4814000140c13641e6460680d40c3d408003004000080d0300004a501508065034003688907084500050703003440320340115a43c00302e64003180503c90355001001507913102080c04501e41541440304414203100c4030380945099400d00b04041d070040f070304195042e80c1003403400d01c5400409990300c2d0720502184440d02d0031918141c481e40d0400c240310450150f25000701541c54098a401d05d0200040c41601c901c0c41140c003401032880410001e00c195038508a015002003040b035036180703014074180314019404002100810340c00e40801c1000c500c2845002100d55294503081803c5d10301ca0304004150300000280400b46d0340801c19500901420f0024ad4041e44c030720f51b02502d095040541c4030350680171513110b00c1e02400b80c9d5902009181e50b00011681198400e48002403d03440d07006e2800c200e005a44c102d50180d1181c03100004003403d0004424008400c03070760302e9021005840d00c5040e2210f5410720a0100395080f000402c0300e9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 891491906 1250 891490656 891490709
    0x41707093617041701021908092107031d0a060c020d02031006060206090a0c0e060d06060b04060f0905032d0106080a02040e0f07090203180312060f0a 66
    0x560492007400e40140080d650740b080306040c500d50100c055080401c00300140c0d000942c0c0098130001a20003503040c070800005c80700c0564038031642c6000700f0003040c02140b42e840c014003601981c0300403010b100c40d908211128904090b03110010860000e01c0183c142070001c1080c00880e80119401441102410300d0144210b40003244044181c0e88000301144150040c1d9080001250090000c00041011441d040e0003030b080040051508407580c0100000100150f43c200c002d0003070360307880141010301d03459180114202c0c2e81e407014010443ca00d81140410021100009402220ba0a55502215a8040e941100d00288074416260558040e111004880c0600111a480703144080300c01042100a002d0590946d02503901405403604001c1440c41503003010b0040c894900c0000c2c3c010100300501c0455150f942c411441100b40e000e5021000c520f540a03904200051801141c040340c1c0c440101c000d00400b40c61060302c02a01c03429424089050300c1c103200d05158115401d24001664010314460307216034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 891493156 1250 891491906 891491981
    0x71b0b070f121d09061c050601050102010c02030c03030f1302060d05150a0f050904060902031006180203010b0a030903020f0f07050f1005160501020909010e1b0c0304050d020d0804170709 82
    0x40c016543d000004031910b1106d200801a07004400074082c55140c400060300b100c0d0240d50600840d0400c10011521160000849070001c5501c0003a881e03d65850a02280103051090001d40c800e4000032002007803030f03050700040e00030080007400b225000000010800900c800d03100704040044154010441490a0300025501c10300590000c12060b500c1c2c1e0000c0c0c28900c4c01085403050540d1031805001c01c158078400c841c042808000c0440c40c65040035610722080c002c0c2c0740c44208150311a0345134400c1500c01c1c0451080100400c0807030717014283c9200368039281c1001d800303202d0054509010141452030a0200d600398004540c607060726000201d94010031100c45582c05449940d001c0020791480c0e00c41107000350003084000d00800013800d203030000200072807258444400c680000e001800e90040044100da0450f035080303c1c00b80e0341c0d88080c408200e1050f19881c01410340d90b0b012400041921030488003842000c580c0059401d202d403607544242c100c4a00300000c0c01c1d0f0400e18402581c084900544208 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 891494406 1250 891493156 891493159
    0x1120b04090b01030524041110120e071403010c05120c131202031005010509010605070c03080c0109050f030a02340915050102070803071b0b070f121d0906 68
    0x6110079694490814030342082e84111203a50140701c8500e4181510100542d0707040a111180103141055240d600045007804080b41c8035030200300c240301e10940241c4090959510f200c805201c0c050303110540944800355071150708406030321081801c074149018425020b070360209880c3d0a05004141c1c8045050550007420441e207908204010380640900c08450002094112288490f00c51240305060410401650400c1311a090100600007503840142450640d1218036201c1d48602042c28004000c040c66400070f0310034200025003500c005019084045424011030440700122513298107180d07207102d12134010300160000001507001034500c3c1020340c996100302d0034001045103d080100304054517035000142166407401e40f050500c02d0441940020310013400500011464625025181d1140d80c07001031072151100350f080d00280324400700c1000303070030380d000c95944070f030100c0c13400d4080d0340c010010581d0650041c1900b03a2150344144001d42c660020f0020b00500018003100388640301c5400f0340610b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 891495656 1250 891494406 891494411
    0xa020303040b13030c0902030411010e0d14011e0b010813050d080402060c060723090a1701150e010504050f061f020f031c0c0e0d030f1e08150108010501120b04 70
    0x2010032018176017480945505000161799044c680f074502000d82e0b5040b06c083c10711030315042014841d501c0307a5002d1110380d00180c6041259140c1c10070f06004020441c07032841e126820a40160308a40140e00c4038403000c10a0321071003d00c1e00c401818050942000718010aa5881304101c9040d262080410359001440903001501780741c4c2400c074050038003504862032000651001d04c1c0510700c030480e03201004507180c02c0d4903040c40c01d031035040802d28100041c00ba503401c0c4030f2181c04483d8035501c2503012101055120aa154020341c4580c82c42c1da10350341c28410580b00e41d0611011030401596016444d01440c001440001c41a44040c0c40d201640150300c040020f42c0562004941550818402001c00304540c1d0814002d9040700390040044800805001c070401c0080e008400160b2a0381003820398142d018140700c030035100c01c64001c036501c610101c9030490b40710040c920b1083c59a00542090701856071034589013017400300d482c011101d01500340302d51400200342c2e40380482094056801240342e0390014001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 891496906 1250 891495656 891495659
    0x1909030c060c0302030f06120d050310050603010b0a020d0206010f03030810030b16090801020c0a17130b0304120e0a12150e0d081b0d05070203390a020303040b13 71
    0x50400302c4a42c8103811002c250000100601c00034042e2034140d00003411251024034450a0300d5540d42c821040f440581802000008907244076200c0001800034000240186d69135038654041c481b640d0001541e600c058800d401031440d01034000b040c0f031810303507820507102515189591401c807070343c0101030801001c444607408040041040307042c115216905200d4005035051600000501c0c0720003035440081103034418480311448200100d0f000c5007144e0414000201c0c000210000e0b0041d1094000d0451140107440d4001140c0d4200c0000c0d40c03007180501d040441007074000400781caa14860000341a030002500c0c00c01e002d02400804402d0443d40180810099000480b8142e0215200f81800001d030364000940f84100c643e0284549503c00042c5450080106418084010a01034a030720200c03015141d41c0010a010f108006480d0043c0c0080c19445545c034003041814100c00e000080f500d40501c4d00348500c0f03074180e00066280390702c0d80d02900071454036190117646011500300200c10742c4042e646000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 891498156 1250 891496906 891496913
    0xd03050c0105090c0a12171b030d0c081e04031107120b10150e06090f040527030a080411030a0b040308070f03091104110d0603050a14061909030c 64
    0xc50380310f00c0e004002016240c002000b04404180305d44e00c0b2000c003000b10b407079160000d001c3e4280891303c42010003d1a0720f41d4050078000b0440002c49602c0342d4a8800845d0a03c8004a103800040305201d0a445400d4191900342c5000ca501040380341c008408200d0002240000344912030900d110f10144050300c41540d1201600020401e13040380685800b501c100501900d0070410b0388140c001d140d03808240c050301d80c0c5500081e100c03164040006201c0c91300071515035016140c42501d16544100140308001501d0300884074410754802c50000b2054007020a41540358100c000100c1e060107100391034a21440c0e5540c0d90f100092100e070f0340c15903010b008168450740028503400c22180154401d450385000e91404400042512081c603040d20f00300750a00340b08030702140030940c134054403070b4003034402041d032411035039420031184034206088500d40e181c090000300b07106000c107110801c035200303c0801c28004983c80c00d050b80c1c1c00064410b40c2d07840c0702000310541c1d000c20690000c02001e2090800700c64400c1c0c941c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 891499406 1250 891498156 891498161
    0x512060a0504092402070506010b090a0f080a11030303070c0b0a0b0d030c060c0201090b0103021917010608071e150201141302030d0f081504150308040f12110d03050c01 74
    0x3002255148001d40924000000c00311032046144c081050441c1045107a4859a907908010710aa258055001508102035143c1c0c621200141507003440f1012465640c944c03841c0d5031700300a0310035100702c200f0005074444c03072502004403801524a0b942d8010008101c3e1500f008444000d019801010350f940200043c0d51542c00384070400d103010361030740b03041807125003440310554482410321411645000080e4000601054940c0e064a4041c2d440b200c0c03000d0300300c14540140d1141e41056000303502c2841165171203001500401e0070390301200c042e03c0d1815980c0c0700f1500e003ca0005d800b005d04070390960091000a4a0a2808600405a200101d03126103d51024400c040c015145102403002c0e040c00c40c801c0d403e08020007002c00401d40341041c003000c1e01031001005010b01038502108d4003285564007070150707984d4000c00d005c0c00c010b070300c0904915968600300c14154468803a40040c000c0c03a030000508400300030a6449580d400035008041d5000000c204803250f08206001c1341402801c0c44030000000b002d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 891500656 1250 891499406 891499421
    0xc060d0608121c06080601140105070f0b010503070b0405090a0c051606061a07050d080a140a0507080c130b070314070b0901180309150509030f0d0912030512060a0504 73
    0x14081240d0f030b821100803428000301c07040300c030244041c140002000a18400680ea80c119a414480d01c4481e220b80001203c1ea481412030140c0700c0340b00d040008050160b0030380b089048541c11011121202c0e607038213040d040e50040703205003580240c20000141c5015001c0d0002c05204602c2c1c64210301d00503901401c1c244200b4180382c16100e69603101c0d801d100428142c101c40300b81000c1e01c0ca103e0704217a11983c520340d80340b880c9104201041040004100c0100694014000050032080380f0036103441d1001d461002010110385160003ea403840c003140340401c44070225100d4001d02081211107608013201d010785030b0301140040b810006a480030302c5413003402d2000390081a02c00e100d05500c90410305086070942d962552200c2d6000c8088078001c0002e6000000c030011501c000d800012100d1b0315002c255082e000d00e00501381c060003030b940d50540c041004140c42d109080c05482d404410f5440d0080315520a111a20080201c1e03020030145000030160846c156010000500081255440710041002d8034004c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 891501906 1250 891500656 891500683
    0x210714040608101b09032a05060a17070905151804050c07052e0b0d0503073504031b0312020a1e021c050c18090c04060303020c060d0608 60
    0x80311340d59030454501c2d04c02551229010300e0a200d4a504648400d4900d401c001300450b18011401540050340c01d045841d08002c0000070031264984c0e004800140a007164580c1e4840b01560f40f000080b8070f03501902c85032050340e07009050501440c0040b15000c1050740180109070808445a10700c0e140c543d10f50040c60300c03501020000c2d1341c84011a04e4160328040b400000c4000c0c440b0f05205c0e0040580911003003074080340d115200454140c039030a010500ca40039410000c0c4c000d0200060b0003051156442c050b20202d1034082d00e80003010206d1204051a40094007004070005d000c2100f0004600c02e069502c2100303112a22407002559a65500d8150310101c031800d46c0940c0050030140c061082050a040046a88400d80003015411ba07001803100c804401410101c1c0c5903d90028050203c104587e20031101301424008501100b0740365041c0380a4219908081c521900c0314500030303800c0c2401141c084940c1a001040d900c00707860f007009416041158540300180d6506000556280208a083d061549 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 891503156 1250 891501906 891501911
    0xc0f1b03060708012405130e060a06020703020f100224070e04090203030901300207110d1a09030d020304080c0d1803030c08070503070605010521071404060810 70
    0x20250506040600c010092424000c2050042010004c00a000c54201c40e200410b414851a803200a40d1b50b4040d10100301c512074201d803400300f0420807400e03486001e440115207461007603958500c101c0e034806042c00020741152001c2c10214107070800e030080c40d8000c5140d005490b0500c0166204450074212900100c0344110b094061120154000c1007442200c0720507030b418002c080440e001700e66a8415810020704201510410720191041e510000710014a514000488040c08019072030181d0403036601911a580044110304542c6401034440d0000d6500c142c83c41160000e0b0944000407500042840d0f4141c0810010302d0039408140c8011031069100340d20a41c2c41c2d41c5204141850000c100103200288866100c0d1803201150300c080520413654149424000d403903291421a126000320203004200740b0000c1021810010260419416034409031014005000c0f401c1e5464090840206015007a07084640306101b0f80c0d0302c2d90b02d80c06013200003500c042001076603030740710525003045544a01042c41d0f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 891504406 1250 891503156 891503203
    0x1c0b070e0f0d17040f08010e072c0a180326010e1501050708120a1109100c06090c23010201110313030c060f0218030102040f05060c0f 59
    0x942020018084480a46080c40e00041c1c0501080c0e81c40e500c90000f90820403005000700618a0740002c030781c090b00e880b2012040440e0348408613400b0300340c4c2c003008001601503010041004202c0740340001840e01082444c40c1390b40303044080008568400341c17191a000d600d801115183e01c0d1800c1c2c050154a00c6903070303448559500351000075500000304d4010011200c2c07070801009404c401100d51a0400c40000801c00503003989001641c0901c43e440e4001c05121000c00c00e01d4014458510061040101060500c0342001046010304140f14580c406940150303040a006a000d103e0217581d0916449840001138440658071a891549616805075840b41781c541c01d000340c0b84a5044c0d400140100a000900000102407961002400024050302050410020480900d40300d00134000910350401d500b04003050b1007a040001a6109814501c021411803d299080d03060501c01c460807180019100160581080e0410999a000384401c1100d807180b4801031a20351000c3c4112150f4020900c031050020713 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 891505656 1250 891504406 891504421
    0x3052412240f0c090105030727080c0108090d030b0301060e16020712030815060d14011403070e04020603040f1b051206090c0f010c0501050a06090b030a05030d05061c0b 74
    0xd40e0300800780382c040c0000c601808144001c1c0e60035160581024280182c81e640c42000803039440c0c035251507104901c008103041014a1718501c52140554800b401940c5000000c50300540701104141e540ea84281d0180c628410220b00c00d0703125410960008001180065a0307000c1d07a1011101035070740003441c1000012a401d200e804000d103400909429a5040400400384c6014000e01802440c410701080703420b80502d8107586100c2112074511041c1020003c50030480d08900b01d80800f406511003082001049500301d250002d01c003030444070502001c000742d40d82d660901c65190009001211484502c818481c0016000c03640302040001c441c80b008007485ca82003c01c8034001310f01d950034510703400000503c40315907400b1407540980c050070755100c50000400001244c160f0107501c0c010f003995107440107203d5054141e411010444a481a081c8040ca160808054807a160f08000410300d900c10001000003d03801d4000907848200104501c10300c502c240c0b5500b40d820300703c4800f10350035180c010400544 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 891506906 1250 891505656 891505723
    0x60c0e0303220e040c05100302040e1006080601140318010e0304150e040b060304030309051c1701081c0c0305040b0a031d01050114150408191203052412 67
    0x105850b2003d02c5840c00d003074556a000e0840341c01800d0042c0c031848042500f15001e0780444004081440300c400e12403074420800040c0c1040c4d070080e03100051000c00402d40c1e42d0710500240c0020003041020710f00d15180c481400c0b41ca416140e482a03101d5495081c04281050181b010300000c18820307502000d00b11204800a00d5448081c02c04c1e880b49290194401e00394a4100c26207074070941c903060000b5021110300b4201e14000d40802032080000c400c44210125691040c112100310440400c0d55100da600d0b006907d03103c0c045095407000e40000b89001c2004184110410901c140c040d09203030b403401d5210f80e6440e895500206203e00402e0b200c04006140300d080041c000d50140c541c00c0204095410718141d05500721442c5500351003080380c2c014480d8410079400454008150030002c03241c511104001664600044a000b610102038084400588501030f00507140f10340300803203011402c1d8105040481d901e5a07071001d16a009044502d00401b01e07201080b0303060308541e500780e40390114824141c44010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 891508156 1250 891506906 891506909
    0xd02100b04090f0206070c0512070509162f030403060c0806030d09050621010305011b031b0503070c060f02041a120402060915032805060904060c0e030322 68
    0x903880e040100000c01c0c056103da14810358100c41250340c4441a04164086403180d8000c40d60110084c1020803078018009004030844000750346040c403907540e03e03e80220078892a10070340085001000c620704020a24440c55850043c4001c0682148501951191560708a90411078181d42d961080001c0c16400001881e0f100c0c804030018905110401801062140c0500c1003a00a6102080c601c6040300d40036900700745403c4020a0f464550b035a0f0410034003804400b0021180b01000b0b0314681c1146200c1c1c003030345256050040c0e010700c40b810145000c40e001c0c2c3c8000d040c1001c0002e91001040041c01600900f00c986080c0d00015071a41d080034000d86000070704c05801606154200405400e402d07420321004d80c40350701114040d468500707040110b402801e400040d25400440001001000402d141d00408007010314240e000c404e083d59505c50341220f10a50b050341d4070802d041c0000740020402d400001070301150385420116014840086440e640145003010030528081c0184d410007840d40341100c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 891509406 1250 891508156 891508159
    0x3020c094b092b17130323120f011e05150f071103060a0204032105041703041412061605090411070b0c040f09020903031c0504020906120c0618030d02100b 68
    0x30080e00b481300300d041807441030305c000906014810b058051021201c81e00d07850700c8405c3c40340030350303035000e400c0d60100035410300b1188089416880d90000c0350800071143c60181b5404a042e40070fa0704d50800d000c0021407610410020304420003003143d42e201d140a00080c020b005c0c0326102400c803c4034540105428400c1c000c1038082d0441c0b0522080002c60403165101d000130020082c1443e0f400d003000803c660509c03594000200d100744ca041c940b6100640000100100c4004000107495000c0344020001502603502e14900654040b5000c01e516003429004480e58060300c0c10130f1407a201a07000031a050b16020749009030f00720740104480c1d09110300050041d501c5001480c4040c81c007424440c80c0c00c407045c12402031000180c0e000c01c01442645017002100c600790340e49601d0208820404150038058142241c01724020382c902c00200d11b1900303085100b0400c40b070041d03015000d4100e00c0c0c0203004054001e0401d031400b48503c120800540c2d00c0500080000c0304a40c0e0140600e1a00d801c900c5040d508000c0da0b00703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 891510656 1250 891509406 891509447
    0x13020c06010614070f110901180e01110d0c0e040501060e01110703210207092d050114041109131d060603060106080403020c094b092b 59
    0x94210316441c82203d404980c40b902d0a000d075070441c1800c0c041b4000c4d00c4400e68200c0105000415400f0300d040c100300e1201d900441c10711008001c0000a03003a501a8030b548d4000b0402804460301201c039a030481400e1b8411440d0070510442c080000400b920402e83c008400b00e4055802c0c000c4a5912168440f21000507000800f41ca5166030340d0320300e01304a203c5100c500d2903143c1c803042c401c5610a0000c04001c0004c01c50500858100480d580045807583d02d102d202101041c40700c885051085c0103c40c101c80130006150444000035090002900302c66005420407102080f01c00b581c0e07540c880b56104808400310b4000740c50741d0603a0304011003007542000501d0660040081107429a00019210305441c11481c0600300d5440d58a005e92400c4404a1a00c1d4003c80c40420404c1c030102d45804051601e809803000c1000045501d4107003000381c0c90041c0054072841c0041d035813010003070142c400307900840703404201d541108010425584401d1a58031030f079650b03d41ca08000d514594400080c24603001c402401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 891511906 1250 891510656 891510677
    0x2070603050c090603190921030905121303290903041401031e05040f05070609060e0409050a05030403080c0c040612030c030e121c0206060312160213020c060106 71
    0x803800b0500038291841e1060324000700042000790400d90045504000d0f0600344200b051614007444c21000f03080d00007012151810034100c0c0c040c800d001c0c00342d241d500440608002612088030380040e5004000101c0e503011103034400400502c0b000c1009070b004540002a07801c003c900e0a04503c3d1074805802c003520b40d0300030701050000041849112001c4102401e000030a00100c81d00e00010402035002090712914205c04c100522200404040c1e03424820360680300d15584a90061311000c80e98040c040c0029000c094440d51810554000740302d1900440844003000010340e17500c6c2ca9035210b9041214010404544210000c00411100c0d1050754100e4084c0120350131311503143d90400740f0110107001c002000c0b0305d860505002c0c01900303842c801c024014000d1003c904200a940c0c00441142c031240076108150301510700c2c030106035a8024000240604200110312400041d91380100002e44050328240609800503138401004500c1c03504240c00148e150fa2418201c1030070403074140d20000900600d000c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 891513156 1250 891511906 891511921
    0x2030301050f0f1008250e01020c060c0a0f0804081608150402181b0427060803120c040b0318060f0103210210020a02031209150a0b010c05120a0207060305 68
    0x540c00707590710740d854860380030b076221081b004014003950b03c540708036080c840402880e594445001e150b603034402c1c0c00301d422490585007441118403031440c5007546504808035903800074450740d071040d44160041030b00c2401c0507100c840090a00040c01a0320030300701c40411080019010900c0002040f10140c8454010f41c038150b008035100003640d80078030040308a2400050a140e83c4c03141918100c400861829484035110640b08003864021b00848502c00000d600040d521030302400b0300d07010f907500340d0041c1d401d14161042035044581d000d0214800b60300144800300d0450300500203184101209800354242e200b0b4100810b040890240c804c8a10049850040c004102641f447c4410241d01c142d00740780342080010300324105008101030840440c0009811541c0d217500001030484160807814800c440c0d2030b0300e8140b941c0c03081c2c0c20103849507a114020020b5402000c82d800000b8080042c1030102c2c80200c5542c0b402c0c24816141603190007000041303918082c0310750400951f0054086401c2c2000142045e40c07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 891514406 1250 891513156 891513169
    0x150f06020d11100f0b040e03130b0304080403050105040302031c0e0706053a0b01020303010806070509041d062e09020a031d101a010807181502030301050f0f 69
    0x10708281400382e6109503440c00d0208101240411500744403c101c00d504081c0c0540143c5a060340c0c1078070032828034407410182a80441100c0e0034560018004400303070f1a01442c0e1015800c020000e403504901440b00001069081c09447e00ca0391081c0e016503a90616100011a00924403500c004400d00d8420b00d030a1442c40011000c05684682c2481602d40c81d18070124402c02515903040b5001351002c40301d2085c4d80548502e4a00c641904140c140210705c2c50f01c00481c0d0b42c0c01701b4400c260007513100d840070a00702030051005080545001d80085000c025000c0a142c00d1a0302414400d02907206070100880ca030303d4002242c0c40c40180444800180c6841118200541c81500600d40020340c00100200f29a009034400e020001070004116410b000f80d0301615214030040d094185580d0420001400552803101070540070302c41611014065194544211000c0d0074900c4030072142551804040341c10003c4855844804079140d006607600d40c14007007401200c1000750f24160040c0c0b841d08202e00340c1c0c0e1710352 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 891515656 1250 891514406 891514423
    0x2011418090a0f0e0102070c08030712051602040e06090f1b120304150507030206060d0c210b0c0403140705330708090f090640150f0602 60
    0x12680d010031502c807040300704020064421018002450080010000314040d000342002901445e09047c4590f41d62070b1290304da00c2085001407641b0310b5500e00300c071800e010b90080c01c0e04040c262a03070b803240c6070340340d002c034045410385c00611100b84d015008000711071000300700421507615218081c02001d011650322405d0b15051540b524441d0034181c8603801c10310310801c240d80c014881001c02c08085141500c009c0d00c15401064280d00602907440020500d04101d844495072a40c404450349840340340480b14106da030381c6140d07088551403406401c0e0010490700d035080ca00894120b004290b5640c51842c0840d946841000c02d40e45c5a044003604005654582010b9100d4100859013141d203030201c400c0300d04140d040e200100800640100b030900070701610001800301c0c03100039554040641c12540410140726422980d59a2021100400c0d03a4003051340b62100010b009074280840b40b12b850101c2083d41d40d041e02d2011803074503555049070566641c8013000325008000b40482d4820a50030420020b4840c0e652 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 891516906 1250 891515656 891515659
    0x100806010513020721120612032a150c1b08071a07031a19061812110103050609040503090f0a0e0a0606030c05090102191a0a0902011418 60
    0x30402d0003540c402c00d6404070b842d0241d1000f110050702c640d0300d40700d03030004003010100000561040d0800c041c13410030303101c1c901c00d80f000341000c0c00c000c0350103590417075000c484c020003040c002c0e4105611402d00e811489450344454840d4024038000c1c510200007604413000c2466010030009014440f081c0016031402e842c0f10660030160072076803105642003c2990002c4680000b0558194908100185905610079032001d54440201d401400c6000100b005030401d01e10300c0e5005825130413082200900941004100301c0001508000b400d980740f100b141c1d80c02080c601540c040001a10307980d403540c0c1c503200d440da0164045402e80c2107800c0a0302d4546d50303802100c01490180035074800c03140882d550b0400160040007041702041c99440c261540101820892166001080c20000c0d41031074580180150b400300c0341c044e0300034007507603041c107424a113026075004040c2c41648042000c001241c062103c42803142c101100086004140740c40010700d5030100c201c2c030112200702070180740901008000200c4a1800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 891518156 1250 891516906 891516919
    0xe0603060d0b04050c04050703060302060a1218140105130b15040605150d06050a06050a1b05070305030304051209090c0307030b040513170307020303160201020f03100e1008060105 79
    0xc0340c4020645407002900040c101d14280401c201c100000099010305415041c4c4090082d9225610b0075800c0d02c24500009502102c24080015454410300c01e14004510302c1801140f201d07084003114000c00c4103c40161070800641d4000320300d201c001d00810741c0110b500b050105038541da0781c40710200b020000d001841c00400c402d1480340556501c2d0001e07000351200414103400d0200a10b900c005550014110f001803c1c01c041c0002158940000240b045803141e49500e0700d040314140d4200c80851080c0c40380341020b4440c1c81c03024007040d8100510300c0a0f5200340c0066684c0e09060800381e03d05031400d400030b65080810005086140c49003145c1c1038000300864040760b1240c54280061f40642200c18050f0b401c60f1420082121140509000c800100e000d110a464910040101d0451900c021250140513a00400200d040304810034101d20445129200060a08204000c0c420440c4e2058030411a000d0910701c06110b1801c00410300c5412141c5608011000741c0361500030345c2c03624014814148280c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 891519406 1250 891518156 891518161
    0x1501090302010f0c06020d2306010f121104080a0c0e1329040506070f031b110a0b0106030f060611060705090111070f14010215040b072f1c0e0603 64
    0xb07024420702103521764411410354607005015610350050140c0000482584045c04a101c108400b0f082c1180c00b850069441a2100340c51283c26641281082d200211141e03481c002034016101540217040034191910182461a00608109c000324919400c90031b0078200101c2402400d82c01c51504440e8154461207880d250200d00d100086040c10260318260607a1000003040104200440c80c03601c180c2c07890f150166000d0b0041c000b00c00b111007a000b400c44200101a00c10315080c0215a000460200c600490f001c04a06944101400200381d0001012a880b41600c0313140c0100e500482014203e21300d80520418036203014076655010103030004d4244030b0005501c80c456442003d001c011441d03104100d90007a595412100d5142c09d01303119a10140300b0900d00c0b507410351300c0443c200500004408100b48a03440e207031601049164044e00c0c600500126030340e0105045404030342814485407641284082c8158260b400d0b04240100741d141d100e900900359002d0820f03401600c041d172090740984019450780d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 891520656 1250 891519406 891519437
    0x1d0f0f0a0c2106080f0106050d0b090f03070c03051b03030714010204081608100b09150d0f0f0b010b0f121005091311040b060f071109070c020108150109030201 70
    0x4410181002c0802c09400218030410410340044048541d950100c502003424000f2860803120180035041d030181e110424000484d0440050b241c000851005541041c91103003078442c81c41d8010b840446030221039210070021b0041c01d1000d4141d003501c03101481c40c0c07000c407040041e46a1049000082c0701070304140310b8009141c825030603200501600c204680e011004540d045010284074840c034100f40c032800000011400c0366000700303110040b01802d02801511441201c5468000c842200c94100103184090f01c08111007001c07804151f4002e40c3c002a00d02d0141c1005028018141c00030620590200800010030b95580300315146a15450000319032034540140d100d0141c0195804182c0c0020f4806c18841c6080e44031582e040418032490042400d040801e0a020944070b28683c8681e000c3c00503c0240700440071761008040c003610628441013050f25040c0000c090035010b0700c2c200001a180c02480b030441d40c002000756003000d01c2c0c4603020080800e0380002814801c2c1030200074100424071540d83e10a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 891521906 1250 891520656 891520667
    0x5040507050d4d041a0a0302130e07080915220b09011b020111040e0a1407030c1404030b071808031804062117040b041d0f0f0a0c 57
    0x1107640c011a03852100d0f01d0848440c6080784440300702c0c003c0100e0380b50049200040b501203908407581607046001188240390105100c0d04800c104406040d020007049000068980401000c1c00c2031007129107031741c2000c0800a0030034070020440707022a8403d0740302030300d004044100e40d9070190341c1003060070f40c154228001c200ac0216940c03005000c031b4280000e000315000d041d0000710295005000200404400b004101d00783c070141d0000c4901000200414888409200e542c80d5020f002100c000c2030703803080d48a100840c400d0899003203000940d81c2520b00ca100cad6002c6408070003241706140407420a81591540050b1881c09024482400403a00119055412034803806000308030800942e0345440c481204420303040903440040348a680751903030101c0d406200c1e1444007007449980e43c2035240c03140140d039054914400406101c3d0351420500c800519403226100030400341c0100104801d4032140500a800c18100250203d501501200308010300280300c041e443d51b003c0d40100000c101c0c240403020036140c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 891523156 1250 891521906 891521951
    0x903010e120c16030c0918081306080c0f030a0e010b1903170408030904090c151d03060702190206040f03260c031b0708010203040b1005040507050d 65
    0x4035004031810600d008604101601c40c5045041c20784201c00c2120408820746402808020009602d03441c051040741c04a6100c1080b10300c02104d042024021620340c0300950300643c03200c5a01c504040c1052140d07542c020162500031070360030801410000c0d0000e813242c42d404000e1210810308d0341d07100c440380e04040941140e10b40040250501e14100820941340c40b500741240001c0d200c2456101410071a40f501d04101c4088032440406142040c86d17400810000d0201d40e103060b25200390048000c1034800e584000500c455208e43c450404540c042c220a0722980c18001100744250051030070021a03c0e00800d40c030b441e405501501c0000350034203100090311030056400860095801d03010200800610340215121b800307443c8040030350709082e5152840c0074400c0310140a01c03500140b0800300004400d9440480c00c00001c81130300d10558841d0001402c81c2c10465058030880300800a1224001030118000080c05058030306004130725011102410030703c2544000c0400aa40f143d100c41400c10329001c00300c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 891524406 1250 891523156 891523181
    0x10090c122705060411100f030c0210050c0418092103140408030103140f0c06092b021311040b07050a0506010305010b01030b010c020a03082101060c17160206090301 72
    0x141c2044142007031036580d50112000c0301c500d8440030121a080c6400d0001c0c100442d00e40d40c2d8840980c0401c45d08601074000c1c0180802035200700048840380c881503014282c4070302489034060b91550301d403092440c6c8440c4d400d080d007115285003c0481c1c0110384a06003000503501c40c51130650f1960000380d411070003003080d01c0811100400000503c01000389440056040743c0c01660f108003034402840885444400740580403070640d1183c603082209092401c050042c0700c1004182585018a8102c046c0341c3c040840c1c0c400400380481c514074000c62405a0690400650001c2d08000c0b00b580b859101c44a44243d000340b58228034080b0340c1c50100302080100c401c0c0c440d440010b85034956564900180681000d501d03007400300303007040280502944583c5900c0002c507001000d4107a01c4c1e00d1078540101c10346c03250864241c001c44060004608251050011b8000e103211703925042c619856040c14070446401034070301112060200000d1180c3e6191030b080d401d90750340403035034150340320241c80010f80101582003e03507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 891525656 1250 891524406 891524471
    0x30d0e011b0602181c02010e0d0506101505040f05010c1401020a0e0901170307080304020d0f03020a1a06010e1302090d08030115020102120f100b04030b10090c12 71
    0xa070030400250090420041e84150840e00d103004a020000911280c00c3d10542034000449800e01540c403903c02002069000b9041542c90070650f240c450800c0300841d50404040c0058804003d45c8900070309000c500040c3d850700700e007000c0c20801411003005a600c615810040c4180091041c8000044c140c0141c0d41501c000b150b03224441c20028003401140300341c55120794222400040c40424036540348810300c1c0c400c0007840c6080b49641e9019030f241c2000d817042c0d07002120700f00000006125200b5641e9154001c2d00104044625031808000041c80c500036031a060500c0e9050000d0303641c012401c622400c2084580041c1007405244140090107242d1810342d00810320092507082c0f20500e0700840c180d84050304500302070301c880c2e64103078241d01c034036521815941c0c0941f0011f9070907a1030074641504003003c103448030042940d070354501200340c01940090b11144210b0702440000061200f440e0002d2a589130240152042040081e060462032151406600d03140c048000c094490750341c03140c3e03c5100701c4404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 891526906 1250 891525656 891525707
    0xb09040308060310141801060503030702040230090f1c0c0203150c0702011e050a050c0106030c140f03060103050c190e04031e02010b0607082512030b0a05030d0e01 72
    0x400c182031806070360544040306d10b1207400704094010302480c2c059504c00b81c0103500d84409982800000d510040303100c83c2800003009490103180407150030042720b6902004010060420303004140c1011039035000200541d100f9401c0c2c2c0c41229483c00704a0841040d410515a980030900200742800e840603040080401c1e080e081100350111080600030941c000c0c4d8400c10310001e01d18003c0c80c9001c01840c62004500148008046c6030b00c600e000f08076818007070001042c0b650741c1741d6404110f841c40b074000c900444155040b45a203400d00e2100c1d9400d4840c00c800403c1e030b55155840e1941c0300c10102024902a171081c189103146001c0b882070003402000d00c44c40400c19483c050400406288e0413841c3c4080000000e5103520006105006645498800404c100d00d000100d6807600400d42c4080c000000355100046d0140c065450800c80c0b210303c3d4042c614280302610341c1c000045c1280c40d0640d5240c42000080810702c0140c500044c6c1c04a0602ca03420941e882401d08070050320820510000d41c119540c0010b40d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 891528156 1250 891526906 891526931
    0xd1523040c0504090326070f020a1e0201120504060c030f0203060d1209031a04060e150105040c030e2b02150f180601080d081005100e06040b0c1b0102010b09040308060310 75
    0x10051f00c1000c20b959040c1c0828034040049846040d45400a00075030b070405500990100c10b030350100081c0344141042e036402d01c3c141004d40c0542e00e08490584800e650781c440f00840c66014000c0c50f00030300c000101103241d4a4254009085c00b0b0004d50301401e50000c843c2c1c034464190142e145030f40596000001e550102c041c500816584a0085a0032510307981400e04000d00c40e0800110030400701040c003d5000980c2c00d081c20700008080c00b1920a0030541c03a00d0140211034402e102490030300321341c00720390b610b0001c2e680036100303050302080381c84821076000856074802c3c0c11b5440d0110750400030b0400c440361551188218041c0f00346102031804d04500035500001004480068103140c00050790301d44102590f1914148900021140b19840e0484000200e0180c1c5902c580c01c1310242c218001c001a0a05450f00055001900000301c03103840d07580403009401780010b8840c540700c2011001d2000f800065004804500d0382d0718045e02c001c041c030000202003003465409105a40b4610000c41d01000301400485 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 891529406 1250 891528156 891528227
    0xf0c0c021e1512190204060c142a1e030c0f04020f030c1c0603030e0d03030f0f02130f0609030b1308071a1f0b090d1523040c05040903 59
    0xc1c0c1c01407014000b18810743c401e41071170007610100c80080e2581c035100e006545501d100c2140c0036010700701c0350250043c40e03a441c0f40c03602d69000041c441c00c0382c0758107031040d01c005000c0a05070041080c1c4101540707840c00d403a5a1b400280e540000a002e448022140d018140424041e000c5c40f01d0700016042c002c000c006104402c44050142883e02c1c1100d04441400101c0304001c680f00c81c003018002811103143d1180500b4800441600310381300c0d01d80050403440c01c1c51424200e0b40b42c0e45900300c0709a0001a80700c0001e6422400401403c020b44400900b60b02c1d104015100340c40b10b1200410710380c82140001c80105c038966080a1054100303403000c1d1b56266034903000011280c1c0e02c9200c0c480c2c20001000c41c1d0f240240e404206540c501080380455041d06026042d02250095514075500402e043d11040004018980e11140411820b001081d1090080017a01c0d0710b00c480c8555401c03210440040001084a4400c10000c69206540001e141816030800311040c25801607501982d51006030074461540104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 891530656 1250 891529406 891529411
    0xc0c0803041214070c05040b0112050106080105120106180b2202031008033c0f0706061217033301030e0102120406150302030d030f0c0c021e1512 64
    0x1a83d03461403405507401008400e000301c50b8003410307094103e0801d001c0c505056102100c0520141000f1804241c03205040307042c3c6400340c002e040000c04e140010410750800400b080112884c020083c00b445003400380c064041400340da49001c039103840703008030016911010304245950004d441005031002c000c10002001c1d50040e61120300d0000380304000529000013109540c41c02a4400400d496445104040041c1c200702c1c2aa484d18003200b00358100c0c3d42d003a10f40050072900d0705441055103480441c00c0c4002200c02030b0f4081125150465210070003d41051011a980ca07801030482d41caa0321100c090700580d403210f00442060341140301034801d848500c60b03001d80ba0100e00760780a002140e602c4401a0a034040c90285030140c00003400404d00046460700178034400b0314050001c800c0340e83d8980000e498a080001071602007607842200400c0c0b10841c0c050100c1c6602d9605004070020403036400300b01480310400c1540940003100d844030220f6031391401c00c010000a641059506c6e0004000d80380d400080c01e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 891531906 1250 891530656 891530693
    0x6020c10020a09060306082d0f06091c080703020a030617160b090112021815030919080a03050921040e06180105011211070317060102010615030c0c080304 68
    0x16500700180083c8280191b00580709a44007408400c4000c200c4d040340c2d02c08120072445000e10342c852004184074200040e100d007180c50f40051035542800000d00381001c2502045011050360341411951158000c41141c1e0042e0240c0f0b00181d6038031030381340210000c145a40202102c1c140c0c1e843c140b40429000034086000b0605882c2035013020740c0c2d0705190007040c0706044e2040e0201d0b02034183c124046c400d541c041c1c1150f02d00700540d00d02044149000039500340d2103c1c4d14001c80e22020040c0b1000380c1003000802140d0700c100310030ba1100d82c03807516100070034028007082d03200301070f20b8500041d2000400d100308851a54143c0580c06c10744803410750744209801500580d0a4021403c0018a15103000c41c2c030f03010b02d468100e5041000d43d003407600445035441058a20b13510b5a4503051410201081e07480145a440c1c0684e5030609800c44190700d0f102d10050117401d040c11a070401300d043c000504400c4800207548100d0400080b0801960019038860000f450013821000e404810401480030034510311030010207 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 891533156 1250 891531906 891531917
    0x40f06051005040f0b0f0402161b0e13050309280602010203160e0a09050405160308030109051f170a0b0a02040f1a03070c0c0506180103050c070506040f06020c10020a 73
    0x40c4100340b801110342101103258000901b5031462001e05156005106820340d80646556a04280c0c0356254040b200804005403400108820805030150180380768000040c025944000c6c0c3c030a81340d42e5503034042c18841034480e4030710302940342c40c0b117000360b0742161304c5000005001d8a0a5482c44064001c0d023080b00d44940400400c803007030401070b11038000c03022082c07001080c420025003003105600007440003c0c0101c90303911444da90300e192140300700702150003584507100d80382c0c2c4c079070424051000792500681640c00b00940b000d02034420b14101c086d002c1c107441c025031103c841829080b0303075180b904030450001b0b40181c07100418442180c00c15002807096400d000c041251450341c480c8000b6500d04c40c070702c500306400d00c14004509142c1c0300e13030a00f0100e64000c0c8186042162142c000450a500c0600d044c01805000e26081616503058007a01ea489100081c41500344102910758949900d00140003c3c84884080c540030b0400040358141d55007010f00100f01c402403000c2b140030a00075400400d5a4000c0744 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 891534406 1250 891533156 891533171
    0x5060301060b1605011e2a051b0709021305040506010507120806041112060301051f2d03141615120906180311190803040f0605100504 59
    0xa05004600881d0760618100e45003407507100c0c074014042c0900d0360484195484124060044941100c2810200c01010f000203004808207400036041f104400d00c01300c030400341070f18046102d40107015034040342a01520200c14803048041d05042018540040d00c0503403020074a084494001e5120b0415101e080e1410030503501d0b218010740d414020044020308901c84d85002810040c801d84030260001c002910201d1450100450221645c1000312034110f071152401c10000c503441c0c24001d03550840e98007004044d025414180c0000960070501604181100140449140020b043c0031803106276004101c089409407280b4003181d0f10040e0485145c8144202e813004c4c1100c04d115000c91080b1601131400c1800e68000c110f042d100d0714400d04880809a94618030b10010881d2801003da0350f004180c001d881700c01076841c2c090400c5031003140c0301c02c013036000d441800b44002800c2a6120481d800c5545651690740768030b404c04030145000c0c070040c0382505010034801041c9410781c1003004e44004413424829070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 891535656 1250 891534406 891534409
    0x902031b1509150a1106040605160327051002030f091002090d020108061c080a140c0303070e2103070b070305042a0b1b210406030213090507120506 65
    0x10700410b81c105520015420a040d80760307006000500c9900c00b14140540c4202c80445050306144040300d00b92022611482080030321007104007544504546810208103902c0255a40090038011140706400e40383d212446400340f1070308015108000804800955480c94039055000c080e140c1696030030785c907120300a072070350610004c0e0007654009800600040300891442c0c004484528000e0619500001a40420b40d40010081d405005090081d6600c40e554000220024028040ca00349280c01190502c00010090008801c498000e219403038100e081500c076000040d1022102d0714002c101c100e80f49007803c50400d0210282070a10b01800e40034080b680d409400f60140c5404036402004c0c1056038140e000103440d0013400d400d0742d48524900714070503a150350b10300c809a402024560446100040303d440659001c010541c2e50074112104255007200c440703000d5000d40158042e5509050b004218000103803006050714000700100e0000380560304020034041d020b050003001a418060070000040c1c0203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 891536906 1250 891535656 891535699
    0x60e01060c020f0a18050906130b0f100f030f020f010912060c0210020403050a0510110409022503030f11090105070305030406091a0106081609060507060902031b 71
    0x488040d41c0321542003120940c2080403008003008031a90100e403c1001048429001140580c1d2580400000415003805503842c1e01e003000003404030181c5a0b00c407900da40019010b0b80e01681002c04200070302c15503201d00201c810500c4e69a007028041803d0010700109000e00012000c111600a9811951065103900115140140da010314144180300002181c0010b105500c04003c500701071050b00c062007000402c140c103a9029910580d6194010860390060200a1041c02603100084004000702d07804084440c0c01809076108600006074040f8440188826444100c83c800914a16100200103607107806002450300c612211092458128014120503e080803a246210140c503400c0c10409113550464850f48010801c840141d21030081400152440f00c407880000252580d103c0c956040c440c1c0200700040080c441020300141c0703040380381002d41241d910b9041e03c220385019682c0c1d40640c14400c0281c50b804000a401d81301d0360b64984c07055031240094141c0d44608032602c2e004510021042800e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 891538156 1250 891536906 891536909
    0x50a1403040e0604091e051f06081b0109060f09030c060f120c0e040f060807030c1703090117040204141008070e1e09150c03040c0e070c06020307120e0307020103060e01 74
    0x20809501c0c4002c1400f0404e92804604a480f480484103044086400100d110500231600c072640d0b6102c0300c0600c00f0042c14003040340590101400740e100c88968400003443e0203450302c2200140014a0220021a841510000041c41d001224524220354842c2c006000c10302c55092100003034100c540028118a0324040c104c00c0d23018958440e816500c03444c1c1004020003100f10100070f4246c0d03403180083c00304818030947e40154064044414121303e481000c01307001c3d02001201201d600104030100460703800c10520b80146440103c591a65591803000c100100b01603170100c100601c01c041004039240b600528001a85c80f60300a81e004243d03205086441040141c40c013088207900d15810014003001d4603e2158020060004c48000d200000c0c07280508000c1540e0007001044004108400e0129900486004284000502001d450983d00080056181d01c01c000d020750340010200340664400c1c0b41d04014000d00103000c100100c02032594582c0c03944208022404039040040c00110b40310308049150 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 891539406 1250 891538156 891538163
    0x21050d020c01030e1c080a0f180c0501050c060a090f050313080706090806060d080f0a050409052202092a09040f060b0711031f09051006050f0d050a1403040e060409 72
    0x3455441c65500b43c5600788001c0400406507569503c2c026804070789d004555280c0160342c2c0c840e115481c1c90401c0c00340903059800c0f0b64144001048044e4010350700107584d80d0b01112a4000140c1006507103048000d041c00c4100240082c403010590f00c00c0302c40f88034104000c841d0150304035003182d07035201c00a48191580340300314560f64110340c1c00103c3da81003010402c90403e2091340b02d50710701482117189071540e4201196250004601150605c026565880340340e401000e204802c01c49200030031281400444100710080c00b03540760780c1c046414000c1c21b8070001c00e02d00c11684400d94602c04086078282540004c01300d01d10860074021210010341c01403007044181c44071401c00728980b4010351680e801d455100200607130588219040c0001b07142c1d5000d07030f0390025103c0d03c002041450b900d08010745007030401c0f0100094545800c0b001c018664a0301d6030307540c020200355214040c021590038075070300380060848042c003d00d5800380c5041d2203610100040003a40c2e030380380690f5055140c2c0014042100d15049005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 891540656 1250 891539406 891539443
    0x501140901230c130e0703050c040315090f020306090309042919090501091a10050307120615020102090109061d0105030901020903010e0c04060b0f0421050d020c01030e 74
    0x503146010452400e41d21041080210340b5010410004c4424101d06a000c0701076050030324280300180d90b0501599070040741c0e030805a420503080d9111811500e802d529100c0045079950305007c100b00161428600c0150002e09a4846107041d114054403644025001c40c801da107090322000800e004001710600500700300d2405400e182c1c2a60038461015400312036802e1000c074101c3c0c0012114514080e02d4060f003051000810a1425826400f5868030159185841003109a6585d01c1203a80070301501d9016080e45000d5080f003a1108a2500614964000303400c003400203d19800d00c9501500100b890700c000380d840c40b420590340c00d011141c80307455140072802d0000c0d0310009001903100318042c6801203983c0e40014603185403500081c0c01c5813034000f40c620340b9030841d03440154035280c03510a400003845007118281c94042500500c40941c0f0039401107144100d0041c45030280040750302e04040c00320345e01008445800c031460304065641e00924000034006424908020110440807400c10a004803031801c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 891541906 1250 891540656 891540701
    0x608091006121202150a14090a0b0c0306010e0405011e0e0702120306010306170708010630030e1c0606060c240e150912130b0d1104030501140901 64
    0x190f403828034100c03180d90218801d60724603a8214440380c82080c000ca41c0342030006580c0d5000030010440110040050880350040003112000c10f41c040211503001803c00c04c400d80d242d9840740181d5245101c0c00849070081d24000000ca10305030409140b043c442d0303823500030303040007070f40c0b070b640c448106500300c07500d400582041d8051034150001501039a0440014100801c05c0f980380d0440c01d4099200070368040641d40001030400c5400400e1050f1005000072880d0307041c081d190301c04801c800c0c0d044001060040742c00911401c050600c10307200307034441d181c00178500c40c282840c0b06224400c3c114041030996401d49421000650b59000e404001c0519034009500c00c581600490303510303c0c003034420860b00100360301c40c3c280300c003414401e10a00007100c0c803500341700700642800388444e8a00200082180c051000405c50420340c0e80640502d4801c4810030140260f607100c030002d00034050300c03030445146091800403402008000040d003160515541684940302540c4c0c55010803070a868081e000d0340d40d03005c2c00405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 891543156 1250 891541906 891541913
    0x8101509030605100911091002010506010c030e120601060206071403070801050d11030d051b120301051005040503011a10080c030c070501061703070c080303090325020a060809100612 80
    0x801d070304c0104001036802d07055484200e4000d88141040c0d501000e44c001400c2e500d01c0c40e10024842812513036100800c45854880000f0745062158240501844603c003560741e010341d60321281c2c12aa800d401c0130f0701c2c001c0d607440c0c401950b110300030344008010a5400c5a0380700c10120100640e8851580c1d90394042299107007006205803810740e0142034a1581c11400d404c2c1464904000c04112210b040e507420b41c4e603003020b0480c003c0e51203468a00c0740d0f950300702c40c07407009912905205617815140212100d00040e00123400641c0c052007a43d120355010350a202040d412544081c0300d140a07400c040e6a1890401180c201c11038821030100d950280b160428008140e003421032502a041031031082000141003a05d4a01e40c000340140142c628080358000105807003003052002c0001c0c02000c50100450860802c1c0038041d07142d0080c00000d0803040c441e105c43c00032900c072a1403510302a90b000391013211a42d03102e003070060014030101c0e1088a54403400501804103841441071808503071100c00740d41d080c1915581d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 891544406 1250 891543156 891543161
    0x81e07030b010e0d03020d1b08180619051b0d2f01141e04031d040b06030f0f1f0e060402270a050409020907030e0f010c081015090306 59
    0x200810304100d1014843d94041e2501d4550743e2900e4001c0d002041c0d0300c07102c2c540086c41050800c5503200d150142d1011440051182c2c021b035605000c218022010718a907610125815001d45581595144140e820f01c0d42c1007074204009040c0118190b40c0d802e1f021200d00d0046594240201c2000f00180d801d0030720380307403000030f180411201148041d0000e820030700105443d42910b01441020038140381c0c50081c001004140c0201c1c3c90a070321404040320540c80e254401919116a039004450044c0c4202c41003600c50361640c2c0710414950300141800d40b03c0c1000c0f0991113080708100c0c1d440d030700711140b070f00400c0c0c000700300008030000100344d0344103855850309107001449030a10142a458026409104000001c84800380880320304400c000305c2007512600c2010071103964408d9010030701461078100c4080160f214000308070b40c03002403420041840f41c021040a85080692160095154a007041401415506c84640760289003007030f0054555a858500b44c41c0204030244020300070400d440c008000284694 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 891545656 1250 891544406 891544421
    0x1e060303020c010e03100c0302031012050d0c02131e0605010e0f12070e04030f030f021303060b0a0b0307090501140306031513061a03100902031902030f01090606030201081e0703 78
    0x83c00b56030482c010b1640740c40a071f40d003400070100800c0d004410080300c00001d0032200300909400c24590a00b40581e198103440710100c60300d030400c0001540ba4903080d034540009641602210450030498040d002904000034210881c190008a04201e00050315601c1121b080c8481d0100a00c40c1c816000103000300100c00382d89941c048258014188005148212030781d180b0303c118001d499413103001c9551240201260a4064924402881840038070201c18410a20000380e961184000588464440003d01c1d00a0144d1003030841000000030400e0641e8050011342c2141c0302a211000d40c01300b100c3c041c070442c0c0412a03056405900c00081400708000516400b0742091030700d03114681c84201620380300b0a1310321041050005a40c0345200842c10309041081e0807002c210160208500c1c0103590009854607005e4818818002c0c2c8020440c0c00d41d5414016503080d80002002000a400350749411005040c041c4000d03400f191261000070307080c0d03607010061441072107013404c2c501080e981c0c00000d83c020641c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 891546762 1106 891545656 891545659
    0x31205090c1f05030115050c0618011a1810350d120b041104090504020a050907080f130b27010603020f09130f061e060303020c010e 58
    0x400c0036241528280c640031748061b9100ca408031403a000c0c1d86002101c40c01814240460359800c41040e490401100d4003d1045004017466a4100b60546e072840d90801d9000255a15446544054541c031100b100c0302c141083c0d40300c1d62000e44100c0c0001112403001103034824201c80e10380c080d1205038481045401842d1000f5110340040c42401c6448915030b9543e242d1803000c205540310380003501c0c03101581d40644c0c1c545543c0c00148003d00801d41d0145c4c0581c08004000c1b499050000c1064802c00c5903071121002c94540841102c11040000c0ca4007030b20a0442c0136100000340540c01e02ca0007610310725000c401c040255081d000150401c035901203c00d0713140440410042c6c070f4a1100d03016845084640400e6a07075005100060f2a00304034000701000c8106d030304042046420342c403018100902455400042d100035407000c04903012400040e0169001d03c880403025841002402c0c42c401c0f0 = true := by decide +kernel

theorem cover : BRFrame.Cov 891366906 891546762 := by
  have h0 := BRFrame.cov_init 891366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 891366906 ≤ n) (h2 : n < 891546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
