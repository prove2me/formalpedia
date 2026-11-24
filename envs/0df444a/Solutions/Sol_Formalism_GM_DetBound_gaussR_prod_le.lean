-- Prove2me | solution 1 for Formalism.GM.DetBound.gaussR_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:25.090474+00:00
-- url     : https://prove2.me/submissions/edce5786-fb45-470c-ae55-f536817e3568

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Theorems.Thm_Formalism_GM_DetBound_gaussR_C
import Theorems.Thm_Formalism_GM_DetBound_gaussR_mul_le

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
theorem _root_.solution {ι : Type*} (ρ : NNReal) (s : Finset ι) (f : ι → K[X]) :
    gaussR ρ (∏ i ∈ s, f i) ≤ ∏ i ∈ s, gaussR ρ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [prod_empty]; rw [← C_1, gaussR_C]; simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (gaussR_mul_le _ _ _).trans (by gcongr)
end Formalism.GM.DetBound
