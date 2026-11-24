-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.tangent_exponent_same_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:36.850072+00:00
-- url     : https://prove2.me/submissions/39eb2102-0b8a-494a-9902-b99a9c6cbc88

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory

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
theorem _root_.solution {ζ ζ' : D.EM} (hb : D.SameBlockAlt ζ ζ') : D.tpE ζ' = D.tpE ζ := by
  unfold SameBlockAlt at hb
  obtain ⟨_, _, htp⟩ := hb
  unfold tpE
  congr 1
  funext x
  rcases x with ⟨o | t, a⟩
  · rfl
  · exact htp t a
end Formalism.MainNotions.PlaneGram.TwistData
