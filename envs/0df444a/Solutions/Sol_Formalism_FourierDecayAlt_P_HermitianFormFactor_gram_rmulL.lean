-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.gram_rmulL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:19:49.132123+00:00
-- url     : https://prove2.me/submissions/cbaacbc1-0eae-44fb-ae76-951d117394f0

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
theorem _root_.solution (A : Matrix Q Q ℂ) (X : Q → Q → ℂ) : gram (rmulL A X) = Aᴴ * gram X * A := by
  unfold gram
  rw [cm_rmulL, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
