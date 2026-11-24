-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Good.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:19.368129+00:00
-- url     : https://prove2.me/submissions/293b6e4c-86c3-4aa3-9e8a-339d25028fec

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial

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
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
namespace Good
theorem _root_.solution (p : ℕ) : D.Good p (0 : MvPolynomial (D.ML × Fin D.r) K) := by
  intro ζ hζ; simp at hζ
end Good
end Formalism.MainNotions.PlaneGram.TwistData
