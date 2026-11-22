-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.seg_eB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:00.962597+00:00
-- url     : https://prove2.me/submissions/6ca4664c-790a-4703-987a-378349e39c6c

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
theorem _root_.solution (a : Fin (D.nB j)) : D.seg (D.eB j a) = j := by
  unfold eB
  have h : ((D.LLj j).equivFin.symm a).1 ∈ D.LLj j := ((D.LLj j).equivFin.symm a).2
  unfold LLj at h
  exact (Finset.mem_filter.1 h).2
end Formalism.MainNotions.PlaneGram.TwistData
