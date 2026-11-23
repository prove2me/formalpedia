-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.nontop_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:15.781663+00:00
-- url     : https://prove2.me/submissions/8570a3aa-e25d-4309-bdbd-3003a89489b0

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution (n : ℕ) (κ e B α E Vv : ℝ) (hα : α ≠ 0) :
    (κ * e / (1 + 0) * B / α) ^ (n + 1) * ((2 * α) ^ n * (E ^ (n + 1) * Vv)) =
      (2 * κ * E) ^ (n + 1) * (e ^ (n + 1) * B) * (1 / α) * (Vv * B ^ n / 2) := by
  have h : (α * α⁻¹) ^ n = 1 := by rw [mul_inv_cancel₀ hα, one_pow]
  linear_combination (2 ^ n * κ ^ (n + 1) * E ^ (n + 1) * e ^ (n + 1) * B ^ (n + 1) * Vv * α⁻¹) * h
end Formalism.FourierDecayAlt.P.Sz5
