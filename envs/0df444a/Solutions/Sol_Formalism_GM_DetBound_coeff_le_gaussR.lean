-- Prove2me | solution 1 for Formalism.GM.DetBound.coeff_le_gaussR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:25:07.341342+00:00
-- url     : https://prove2.me/submissions/12970878-2663-4b6e-8ec2-5465845c46dd

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Theorems.Thm_Formalism_GM_DetBound_gaussR_le_iff

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
theorem _root_.solution (ρ : NNReal) (P : K[X]) (k : ℕ) : ‖P.coeff k‖₊ * ρ ^ k ≤ gaussR ρ P :=
  (gaussR_le_iff ρ P _).mp le_rfl k
end Formalism.GM.DetBound
