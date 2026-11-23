-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SecondPolynomialClauses.unipotent_degree_three_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:59.541906+00:00
-- url     : https://prove2.me/submissions/a1a84060-18f3-49e7-9ece-75083b014292

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SecondPolynomialClauses
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.SecondPolynomialClauses
theorem _root_.solution : UnnormalisedLiftBoundFromComponents := by
  intro K d grid q w e o W0 W RL RV he hq hR hD hS
  unfold LiftLeadingCoefficientIdentity at hD
  unfold NodeDualityBound at hS
  have hne : ‖e‖ = 1 := by rcases he with rfl | rfl <;> simp
  calc ‖o‖ ^ K * ‖W0‖ = ‖(e * o) ^ K * W0‖ := by rw [norm_mul, norm_pow, norm_mul, hne, one_mul]
    _ = ‖∑ j, ((coProd grid j : ℝ) : ℂ) * W j‖ := by rw [hD]
    _ ≤ ∑ j, ‖((coProd grid j : ℝ) : ℂ) * W j‖ := norm_sum_le _ _
    _ ≤ ∑ j, |coProd grid j| * Real.sqrt (RL j * RV j / qProd q w grid j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h := Real.abs_le_sqrt (hS j)
        rw [abs_norm] at h
        exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
end Formalism.FourierDecayAlt.P.SecondPolynomialClauses
