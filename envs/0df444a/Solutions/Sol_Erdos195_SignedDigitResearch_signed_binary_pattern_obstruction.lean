-- Prove2me | solution 1 for Erdos195.SignedDigitResearch.signed_binary_pattern_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:01:39.605813+00:00
-- url     : https://prove2.me/submissions/c8f64cf4-6a38-4326-b7d1-3412dbb3234c

import Mathlib
import Definitions.Def_Erdos195_defs
import Definitions.Def_Erdos195_SignedBinary_Model

namespace Erdos195.SignedDigitResearch

@[simp] theorem signedValue_zero (ε : ℕ → Bool) : signedValue ε 0 = 0 := by
  simp [signedValue]

@[simp] theorem signedValue_even (ε : ℕ → Bool) (n : ℕ) :
    signedValue ε (2*n) = 2 * signedValue (fun j => ε (j+1)) n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [signedValue]
    simp [hn]

 theorem signedValue_scale (ε : ℕ → Bool) (k n : ℕ) :
    signedValue ε (2^k*n) = (2:ℤ)^k * signedValue (fun j => ε (j+k)) n := by
  induction k generalizing ε with
  | zero => simp
  | succ k ih =>
    rw [show 2^(k+1)*n = 2*(2^k*n) by ring, signedValue_even, ih]
    simp only [Nat.add_assoc]
    ring

@[simp] theorem signedValue_one (ε : ℕ → Bool) : signedValue ε 1 = sign (ε 0) := by
  norm_num [signedValue]
@[simp] theorem signedValue_two (ε : ℕ → Bool) :
    signedValue ε 2 = 2 * sign (ε 1) := by norm_num [signedValue]
@[simp] theorem signedValue_three (ε : ℕ → Bool) :
    signedValue ε 3 = 2 * sign (ε 1) + sign (ε 0) := by norm_num [signedValue]
@[simp] theorem signedValue_four (ε : ℕ → Bool) :
    signedValue ε 4 = 4 * sign (ε 2) := by norm_num [signedValue]; ring
@[simp] theorem signedValue_five (ε : ℕ → Bool) :
    signedValue ε 5 = 4 * sign (ε 2) + sign (ε 0) := by norm_num [signedValue]; ring
@[simp] theorem signedValue_eight (ε : ℕ → Bool) :
    signedValue ε 8 = 8 * sign (ε 3) := by norm_num [signedValue]; ring
@[simp] theorem signedValue_fifteen (ε : ℕ → Bool) :
    signedValue ε 15 = 8 * sign (ε 3) + 4 * sign (ε 2) + 2 * sign (ε 1) + sign (ε 0) := by
  norm_num [signedValue]
  ring

lemma sign_neg_of_ne {a b : Bool} (h : a ≠ b) : sign b = -sign a := by
  cases a <;> cases b <;> simp_all [sign]

theorem hasMonotoneAP_of_equations (f : ℕ ≃ ℤ) (i j k l : ℕ)
    (hij : i < j) (hjk : j < k) (hkl : k < l)
    (h1 : f i + f k = 2 * f j) (h2 : f j + f l = 2 * f k) :
    HasMonotoneAP f 4 := by
  have e2 : f i + 2 * (f j - f i) = f k := by linarith
  have e3 : f i + 3 * (f j - f i) = f l := by linarith
  refine ⟨[i,j,k,l], ⟨f i, f j-f i, Or.inl ?_⟩, ?_⟩
  · simpa [List.range_succ] using And.intro e2.symm e3.symm
  · simpa [List.pairwise_cons] using
      And.intro (And.intro hij (And.intro (lt_trans hij hjk)
        (lt_trans hij (lt_trans hjk hkl))))
        (And.intro (And.intro hjk (lt_trans hjk hkl)) hkl)

/-- Two repeated finite order patterns force all digit signs to agree. -/
theorem signs_equal_of_patterns (ε : ℕ → Bool) (pos : ℕ → ℕ) (f : ℕ ≃ ℤ)
    (hval : ∀ n, f (pos n) = signedValue ε n)
    (hA : ∀ k, pos (2^k*3) < pos (2^k*2) ∧
      pos (2^k*2) < pos (2^k*5) ∧ pos (2^k*5) < pos (2^k*4))
    (hB : ∀ k, pos (2^k*1) < pos (2^k*2) ∧
      pos (2^k*2) < pos (2^k*15) ∧ pos (2^k*15) < pos (2^k*8))
    (hfree : ¬ HasMonotoneAP f 4) : ∀ k, ε k = ε (k+1) := by
  have hprop (k : ℕ) (hc : ε k ≠ ε (k+1)) : ε (k+1) ≠ ε (k+2) := by
    intro he
    have hs1 := sign_neg_of_ne hc
    have hs2 : sign (ε (k+2)) = sign (ε (k+1)) := congrArg sign he.symm
    apply hfree
    apply hasMonotoneAP_of_equations f (pos (2^k*3)) (pos (2^k*2))
      (pos (2^k*5)) (pos (2^k*4)) (hA k).1 (hA k).2.1 (hA k).2.2
    all_goals
      simp only [hval, signedValue_scale, signedValue_three, signedValue_two,
        signedValue_five, signedValue_four, zero_add]
      simp only [show 1+k=k+1 by omega, show 2+k=k+2 by omega, hs2, hs1]
      ring
  intro k
  by_contra hc
  have hc1 := hprop k hc
  have hc2 := hprop (k+1) (by simpa [Nat.add_assoc] using hc1)
  have hs1 := sign_neg_of_ne hc
  have hs2 : sign (ε (k+2)) = sign (ε k) := by
    have := sign_neg_of_ne hc1
    rw [hs1, neg_neg] at this
    exact this
  have hs3 : sign (ε (k+3)) = -sign (ε k) := by
    have := sign_neg_of_ne hc2
    simpa [Nat.add_assoc, hs2] using this
  apply hfree
  apply hasMonotoneAP_of_equations f (pos (2^k*1)) (pos (2^k*2))
    (pos (2^k*15)) (pos (2^k*8)) (hB k).1 (hB k).2.1 (hB k).2.2
  all_goals
    simp only [hval, signedValue_scale, signedValue_one, signedValue_two,
      signedValue_fifteen, signedValue_eight, zero_add]
    simp only [show 1+k=k+1 by omega, show 2+k=k+2 by omega,
      show 3+k=k+3 by omega, hs1, hs2, hs3]
    ring

theorem signedValue_const (b : Bool) (n : ℕ) :
    signedValue (fun _ => b) n = sign b * (n:ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn]
    rw [signedValue, dif_neg hn, ih (n/2) (by omega)]
    have hcast : (n:ℤ) = 2 * ((n/2:ℕ):ℤ) + ((n%2:ℕ):ℤ) := by
      exact_mod_cast (show n = 2*(n/2)+n%2 by omega)
    by_cases hm : n%2 = 0
    · simp only [hm, if_pos, Nat.cast_zero, add_zero] at hcast ⊢
      rw [hcast]
      ring
    · have hm1 : n%2 = 1 := by omega
      rw [if_neg hm]
      simp only [hm1, Nat.cast_one] at hcast
      rw [hcast]
      ring

end Erdos195.SignedDigitResearch

open Erdos195 Erdos195.SignedDigitResearch

/-- A bijective signed-digit transport of an order with the two scaled patterns
necessarily contains a monotone four-term arithmetic progression. -/
theorem solution (p : ℕ ≃ ℕ) (ε : ℕ → Bool) (f : ℕ ≃ ℤ)
    (hval : ∀ i, f i = signedValue ε (p i))
    (hA : ∀ k, p.symm (2^k*3) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*5) ∧ p.symm (2^k*5) < p.symm (2^k*4))
    (hB : ∀ k, p.symm (2^k*1) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*15) ∧ p.symm (2^k*15) < p.symm (2^k*8)) :
    HasMonotoneAP f 4 := by
  by_contra hfree
  have hadj := signs_equal_of_patterns ε p.symm f
    (fun n => by simpa using hval (p.symm n)) hA hB hfree
  have heq : ε = fun _ => ε 0 := by
    funext n
    induction n with
    | zero => rfl
    | succ n ih => exact (hadj n).symm.trans ih
  cases hb : ε 0
  · obtain ⟨i, hi⟩ := f.surjective (-1)
    have hv := hval i
    rw [heq, signedValue_const, hb] at hv
    norm_num [sign, hi] at hv
    have := Nat.cast_nonneg (α := ℤ) (p i)
    omega
  · obtain ⟨i, hi⟩ := f.surjective 1
    have hv := hval i
    rw [heq, signedValue_const, hb] at hv
    norm_num [sign, hi] at hv
    have := Nat.cast_nonneg (α := ℤ) (p i)
    omega
