-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.lemmaEprimeFull_fromSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:52.727047+00:00
-- url     : https://prove2.me/submissions/b00a0b6c-01c0-4e61-9c26-39ab9e04282c

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (h1 : WeightedIntegrable) (h2 : EpCoefInt) (h3 : LemmaEprime) :
    LemmaEprimeFull := by
  intro B X c M p N hN hdw hM hJ hP hNF hPol hCw hBF
  exact h3 B X c M hdw hM hJ hP (h2 h1 B X p N hN hdw hM hNF) hPol hCw hBF
end Formalism.FourierDecayAlt.P.LEx2
