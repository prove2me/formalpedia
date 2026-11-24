-- Prove2me | solution 1 for CovecW.mulVec_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:11:52.254082+00:00
-- url     : https://prove2.me/submissions/aaca6b58-18cd-4a33-8ee2-73d2f8dfd7f5

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CovecW
open Formalism.QuantumDeterminants
namespace CovecW
theorem _root_.solution (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (y : Fin (2 * r + k + 1)) :
    M *ᵥ bvec y = fun i => M i y := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
end CovecW
