-- Prove2me | solution 1 for Formalism.GM.DetBound.gaussR_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:24.997883+00:00
-- url     : https://prove2.me/submissions/ce01b293-874a-4c2c-8c71-07697f336744

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat

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
theorem _root_.solution (ρ : NNReal) (P : K[X]) : gaussR ρ (-P) = gaussR ρ P := by
  unfold gaussR; simp [support_neg]
end Formalism.GM.DetBound
