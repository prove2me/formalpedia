-- Prove2me | solution 1 for Formalism.REAL.isSelfAdjoint_of_conjTranspose_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:47.201515+00:00
-- url     : https://prove2.me/submissions/73c4253f-2800-4c25-8748-8803e36c9d31

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
theorem _root_.solution {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) : IsSelfAdjoint A := by
  exact hA
end Formalism.REAL
