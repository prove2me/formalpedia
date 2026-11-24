-- Prove2me | solution 1 for Formalism.REAL.polarLog_add_self_eq_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:54.497833+00:00
-- url     : https://prove2.me/submissions/ee493358-df94-478e-9dda-409be534d5af

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (g : Matrix (Fin n) (Fin n) ℂ) :
    polarLog g + polarLog g = CFC.log (gᴴ * g) := by
  unfold polarLog
  rw [← add_smul]
  norm_num
end Formalism.REAL
