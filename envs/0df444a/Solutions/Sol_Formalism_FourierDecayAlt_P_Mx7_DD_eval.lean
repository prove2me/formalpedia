-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.DD_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:11.112977+00:00
-- url     : https://prove2.me/submissions/8b05f667-98f7-4880-a2e6-567246dc18db

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_pa_eval

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
theorem _root_.solution (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) (Y : ℂ) :
    (DD s ρ c q1 N M).eval Y =
    c * q1.eval Y + (∑ l ∈ s, M l * ((∏ j ∈ s.erase l, (Y + ρ j)) * ∏ j ∈ s, (Y + (ρ j + 1)))) -
      (∑ l ∈ s, N l * ((∏ j ∈ s, (Y + ρ j)) * ∏ j ∈ s.erase l, (Y + (ρ j + 1)))) := by
  simp only [DD, eval_sub, eval_add, eval_mul, eval_C, eval_finsetSum, pa_eval]
end Formalism.FourierDecayAlt.P.Mx7
