-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LagrangeExtraction.extractBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:17.2102+00:00
-- url     : https://prove2.me/submissions/42859b98-ceb0-4cf9-b133-12074df01b21

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LagrangeExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_sum_prod_abs
import Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_norm_le_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LagrangeExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.LagrangeExtraction
theorem _root_.solution : ExtractBound := by
  intro V _ _ K d s W grid hP hg y₀ B hB
  refine (norm_le_sum s W grid hP hg y₀).trans ?_
  rw [← sum_prod_abs, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (hB j) (Finset.prod_nonneg fun a _ => abs_nonneg _)
end Formalism.FourierDecayAlt.P.LagrangeExtraction
