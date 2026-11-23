-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.xC_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:24.720861+00:00
-- url     : https://prove2.me/submissions/1f4e4018-0eef-45ef-a14a-975aef22293f

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
theorem _root_.solution (P : Par) (π : Ty P) (Y : ℂ) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    xC P π Y = xEx P {l} π Y * (Y + (rho P π l : ℂ)) := by
  unfold xC xEx
  calc ∏ i ∈ Icc 1 (P.k - 1), (Y + (rho P π i : ℂ))
      = (∏ i ∈ Icc 1 (P.k - 1) \ {l}, (Y + (rho P π i : ℂ))) * ∏ i ∈ {l}, (Y + (rho P π i : ℂ)) :=
        (Finset.prod_sdiff (Finset.singleton_subset_iff.2 hl)).symm
    _ = _ := by rw [Finset.prod_singleton]
end Formalism.FourierDecayAlt.P.Mx7
