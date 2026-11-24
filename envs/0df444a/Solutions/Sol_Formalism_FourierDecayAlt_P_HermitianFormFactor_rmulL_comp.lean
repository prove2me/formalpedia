-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.rmulL_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:19:47.16688+00:00
-- url     : https://prove2.me/submissions/fffc830e-03f7-4939-8e43-712080706f60

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_cm_rmulL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
variable {Q : Type} [Fintype Q] [DecidableEq Q]
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (A A' : Matrix Q Q ℂ) (h : A' * A = 1) : rmulL A ∘ₗ rmulL A' = LinearMap.id := by
  apply LinearMap.ext
  intro X
  have h1 : cm (rmulL A (rmulL A' X)) = cm X := by
    rw [cm_rmulL, cm_rmulL, Matrix.mul_assoc, h, Matrix.mul_one]
  funext j i
  exact congrFun (congrFun h1 i) j
end Formalism.FourierDecayAlt.P.HermitianFormFactor
