-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.mem_chainSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:54.963148+00:00
-- url     : https://prove2.me/submissions/e81371e6-1806-4084-a117-6430341c4944

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (j : Fin D.J) (i : Fin (D.nch j)) (z : D.ML) :
    z ∈ D.chainSet j i ↔ (∃ b ∈ D.chain j i, D.mb b = z) ∨ ∃ m : Fin D.r, D.mw (D.aux₃ j, m) = z := by
  simp [chainSet, wSet]
end Formalism.MainNotions.PlaneGram.TwistData
