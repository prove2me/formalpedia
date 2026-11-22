-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Good.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:51.14284+00:00
-- url     : https://prove2.me/submissions/0eb1bc73-5778-45e8-938e-0f16964fce56

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
theorem _root_.solution {p : ℕ} {Z W : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (hW : D.Good p W) :
    D.Good p (Z + W) := by
  classical
  intro ζ hζ
  rcases Finset.mem_union.mp (support_add hζ) with h | h
  · exact hZ ζ h
  · exact hW ζ h
end Good
end Formalism.MainNotions.PlaneGram.TwistData
