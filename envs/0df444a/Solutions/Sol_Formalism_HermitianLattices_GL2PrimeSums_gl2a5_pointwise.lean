-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:09.171167+00:00
-- url     : https://prove2.me/submissions/748f6b5f-8419-428f-ae3d-5594429cdd2d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_outPart_mul
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_out_cases
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_coprime_of_minFac_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution (m₀ nStar : ℕ) {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n')
    (μ δ : ℝ) (hδ : 0 ≤ δ) (hμ1 : |μ| ≤ 1)
    (hμ : outPart m₀ (n * n') ≠ 1 → outPart m₀ (n * n') ≠ nStar → |μ| ≤ δ) :
    |μ| ≤ δ + (if n.minFac = n'.minFac then (1 : ℝ) else 0)
      + (if outPart m₀ n = 1 ∧ outPart m₀ n' = 1 then (1 : ℝ) else 0)
      + (if outPart m₀ n = nStar.minFac ∧ outPart m₀ n' = nStar / nStar.minFac then (1 : ℝ) else 0)
      + (if outPart m₀ n = nStar / nStar.minFac ∧ outPart m₀ n' = nStar.minFac then (1 : ℝ) else 0) := by
  have i1 : (0 : ℝ) ≤ (if n.minFac = n'.minFac then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have i2 : (0 : ℝ) ≤ (if outPart m₀ n = 1 ∧ outPart m₀ n' = 1 then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have i3 : (0 : ℝ) ≤ (if outPart m₀ n = nStar.minFac ∧ outPart m₀ n' = nStar / nStar.minFac
      then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have i4 : (0 : ℝ) ≤ (if outPart m₀ n = nStar / nStar.minFac ∧ outPart m₀ n' = nStar.minFac
      then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  by_cases h1 : n.minFac = n'.minFac
  · rw [if_pos h1] at i1 ⊢; linarith
  have hmul := gl2a5_outPart_mul m₀ (gl2a5_coprime_of_minFac_ne hn hn' h1)
  by_cases h2 : outPart m₀ (n * n') = 1
  · rw [hmul] at h2
    have h2' : outPart m₀ n = 1 ∧ outPart m₀ n' = 1 :=
      ⟨Nat.eq_one_of_mul_eq_one_right h2, Nat.eq_one_of_mul_eq_one_left h2⟩
    rw [if_pos h2'] at i2 ⊢; linarith
  by_cases h3 : outPart m₀ (n * n') = nStar
  · have hS1 : nStar ≠ 1 := by rw [← h3]; exact h2
    have hr : nStar.minFac.Prime := Nat.minFac_prime hS1
    have hdvd : nStar.minFac ∣ outPart m₀ n * outPart m₀ n' := by
      rw [← hmul, h3]; exact Nat.minFac_dvd _
    have aux : ∀ {k : ℕ}, IsPrimePow k → nStar.minFac ∣ outPart m₀ k →
        outPart m₀ k = nStar.minFac := by
      intro k hk hd
      rcases gl2a5_out_cases m₀ hk with h | h
      · rw [h] at hd; exact absurd (Nat.dvd_one.1 hd) hr.one_lt.ne'
      · rw [h] at hd ⊢
        exact ((Nat.prime_dvd_prime_iff_eq hr (Nat.minFac_prime hk.ne_one)).1 hd).symm
    rcases hr.dvd_mul.1 hdvd with hd | hd
    · have e1 := aux hn hd
      have e0 : nStar = nStar.minFac * outPart m₀ n' := by rw [← e1, ← hmul, h3]
      have e2 : outPart m₀ n' = nStar / nStar.minFac := (Nat.div_eq_of_eq_mul_right hr.pos e0).symm
      have e3 : outPart m₀ n = nStar.minFac ∧ outPart m₀ n' = nStar / nStar.minFac := ⟨e1, e2⟩
      rw [if_pos e3]; linarith
    · have e1 := aux hn' hd
      have e0 : nStar = outPart m₀ n * nStar.minFac := by rw [← e1, ← hmul, h3]
      have e2 : outPart m₀ n = nStar / nStar.minFac := (Nat.div_eq_of_eq_mul_left hr.pos e0).symm
      have e3 : outPart m₀ n = nStar / nStar.minFac ∧ outPart m₀ n' = nStar.minFac := ⟨e2, e1⟩
      rw [if_pos e3]; linarith
  · have := hμ h2 h3
    linarith
end Formalism.HermitianLattices.GL2PrimeSums
