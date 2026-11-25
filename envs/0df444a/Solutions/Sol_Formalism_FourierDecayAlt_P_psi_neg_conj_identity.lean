-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.psi_neg_conj_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:52:05.726716+00:00
-- url     : https://prove2.me/submissions/e1a0872b-ea63-497e-9ced-700053fde32b

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.PsiNegConj := by
  intro x
  have hre : ((-2 * Complex.I) * -(starRingEnd ℂ) x).re = ((-2 * Complex.I) * x).re := by
    simp [Complex.mul_re]
  simp only [C2.psiC, cStd, hre]
end Formalism.FourierDecayAlt.P
