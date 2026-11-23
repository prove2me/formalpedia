-- Prove2me | solution 1 for Formalism.GM.DetBound.gaussR_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:21.7928+00:00
-- url     : https://prove2.me/submissions/a8c3d186-b947-4d17-a293-e055bc7c6517

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Theorems.Thm_Formalism_GM_DetBound_gaussR_le_iff
import Theorems.Thm_Formalism_GM_DetBound_coeff_le_gaussR
import Theorems.Thm_Formalism_GM_DetBound_nnnorm_sum_mul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DetBound
open Finset Polynomial
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.GM.DetBound
theorem _root_.solution {ι : Type*} (ρ : NNReal) (s : Finset ι) (f : ι → K[X]) (b : NNReal)
    (h : ∀ i ∈ s, gaussR ρ (f i) ≤ b) : gaussR ρ (∑ i ∈ s, f i) ≤ b := by
  rw [gaussR_le_iff]; intro k
  rw [finsetSum_coeff]
  exact nnnorm_sum_mul_le s _ _ _ fun i hi => (coeff_le_gaussR ρ (f i) k).trans (h i hi)
end Formalism.GM.DetBound
