-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.rc_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:23.012271+00:00
-- url     : https://prove2.me/submissions/690fe40f-17b2-46dd-8adc-340d6505019a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rho_inj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx6.WB
theorem _root_.solution (P : Par) (hP : P.OK) (π : Ty P) :
    ∀ i ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), rc P π i = rc P π j → i = j := by
  intro i hi j hj h
  have h2 : rho P π i = rho P π j := by
    unfold rc at h; exact_mod_cast h
  by_contra hij
  rcases lt_or_gt_of_ne hij with h' | h'
  · exact absurd h2 (ne_of_gt (Mx3.rho_inj P hP π i j hi hj h'))
  · exact absurd h2 (ne_of_lt (Mx3.rho_inj P hP π j i hj hi h'))
end Formalism.FourierDecayAlt.P.Mx6.WB
