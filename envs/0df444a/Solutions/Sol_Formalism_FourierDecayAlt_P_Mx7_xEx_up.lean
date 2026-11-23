-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.xEx_up
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:23:50.625292+00:00
-- url     : https://prove2.me/submissions/42fcde24-4c57-4c9f-98ab-ad3276e98ca9

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (hR : RhoUp) (P : Par) (l : ℕ) (π π' : Ty P) (hU : Up P l π π') (ex : Finset ℕ) (hl : l ∈ ex)
    (Y : ℂ) : xEx P ex π' Y = xEx P ex π Y := by
  unfold xEx
  refine Finset.prod_congr rfl ?_
  intro i hi
  have hi' := Finset.mem_sdiff.1 hi
  have hne : i ≠ l := fun h => hi'.2 (h ▸ hl)
  rw [hR P l π π' hU i hi'.1, if_neg hne, add_zero]
end Formalism.FourierDecayAlt.P.Mx7
