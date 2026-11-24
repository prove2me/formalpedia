-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.letE_liftE_mw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:39.581017+00:00
-- url     : https://prove2.me/submissions/f4de56ac-9a43-4a40-aa66-22268d6e9f09

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_liftE_mw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K) (p : ℕ)
variable (t : D.Tau)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (α : D.EA) :
    letE (D.liftE p α) (D.mw t) = divE (D.P p t) (letE α (Sum.inr t)) := by
  ext a
  simp only [Formalism.MainNotions.PlaneGram.letE_apply, Formalism.MainNotions.PlaneGram.divE_apply, liftE_mw]
end Formalism.MainNotions.PlaneGram.TwistData
