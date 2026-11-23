-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.good_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:58.592438+00:00
-- url     : https://prove2.me/submissions/18c70213-abcc-4cec-9237-e644130b4826

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
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) (Y : ℂ) (hY : Y ∉ badSet P) (c : ℂ) (hc : c = 0 ∨ c = 1 ∨ c = 2) (π : Ty P) :
    xC P π (Y + c) ≠ 0 := by
  unfold xC
  rw [Finset.prod_ne_zero_iff]
  intro i hi h0
  apply hY
  simp only [badSet, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨π, i, hi, ?_⟩
  rcases hc with rfl | rfl | rfl
  · left; linear_combination h0
  · right; left; linear_combination h0
  · right; right; linear_combination h0
end Formalism.FourierDecayAlt.P.Mx7
