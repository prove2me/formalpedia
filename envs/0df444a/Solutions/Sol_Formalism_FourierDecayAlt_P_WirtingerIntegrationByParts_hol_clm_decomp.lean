-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_clm_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:15.250192+00:00
-- url     : https://prove2.me/submissions/de35f8f7-f1c6-4dbb-a466-d0a9cf025950

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution (L : (Fin d → ℂ) →L[ℂ] F) :
    L = ∑ k, (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ).smulRight (L (Pi.single k 1)) := by
  ext v
  have hv : v = ∑ k, v k • (Pi.single k (1 : ℂ) : Fin d → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext i
    by_cases hik : i = k
    · subst hik; simp
    · simp [Pi.single_eq_of_ne hik]
  conv_lhs => rw [hv]
  simp [map_sum]
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
