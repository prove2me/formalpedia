-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.first_embedding_ne_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:29.193547+00:00
-- url     : https://prove2.me/submissions/00f198a7-7543-4c76-af29-5261e5036fc0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex

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
theorem _root_.solution (l : Fin (D.nB j + D.r)) (t : D.Tau) : D.e0 j l ≠ D.mtp t := by
  refine Fin.addCases (fun a => ?_) (fun m => ?_) l <;> simp [mb, mlab, mtp]
end Formalism.MainNotions.PlaneGram.TwistData
