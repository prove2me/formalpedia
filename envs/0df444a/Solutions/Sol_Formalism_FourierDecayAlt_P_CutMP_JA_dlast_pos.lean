-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.dlast_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:35:11.238623+00:00
-- url     : https://prove2.me/submissions/424a1eea-7e4d-49e5-816c-07741f057a07

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddScal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatPolyOK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddScalBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_gram_function_last_minor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA
noncomputable section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CutMP.JA
theorem _root_.solution (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) {g : B.Mat k r} (hg : ε ≤ Gf k r D.z D.z' g) :
    ε ≤ Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1))) :=
  Formalism.FourierDecayAlt.P.gram_function_last_minor k r D.z D.z' D.T_pos.le D.T'_pos.le g ε hg
end Formalism.FourierDecayAlt.P.CutMP.JA
