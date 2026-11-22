-- Prove2me | solution 1 for Formalism.GM.DetBound.gaussR_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:00.167234+00:00
-- url     : https://prove2.me/submissions/fc5ab918-b967-48f7-919b-56ca6831e8ff

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Theorems.Thm_Formalism_GM_DetBound_gaussR_le_iff
import Theorems.Thm_Formalism_GM_DetBound_coeff_le_gaussR

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
theorem _root_.solution (ρ : NNReal) (a : K) : gaussR ρ (C a) = ‖a‖₊ := by
  apply le_antisymm
  · rw [gaussR_le_iff]; intro k
    rw [coeff_C]; split_ifs with hk
    · subst hk; simp
    · simp
  · simpa using coeff_le_gaussR ρ (C a) 0
end Formalism.GM.DetBound
