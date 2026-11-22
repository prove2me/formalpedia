-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.eB_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:55.760038+00:00
-- url     : https://prove2.me/submissions/b12cf131-4d2f-45e3-a137-227f8c410c67

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective

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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (b : D.Lb) (hb : D.seg b = j) : ∃ a, D.eB j a = b := by
  refine ⟨(D.LLj j).equivFin ⟨b, by simp [LLj, hb]⟩, ?_⟩
  simp [eB]
end Formalism.MainNotions.PlaneGram.TwistData
