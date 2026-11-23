-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.pa_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:54.771702+00:00
-- url     : https://prove2.me/submissions/b1822243-afa2-4afa-b5f2-7f280ee9ccef

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
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (s : Finset ℕ) (ρ : ℕ → ℂ) (Y : ℂ) : (pa s ρ).eval Y = ∏ i ∈ s, (Y + ρ i) := by
  simp [pa, eval_prod]
end Formalism.FourierDecayAlt.P.Mx7
