-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.dot_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:26.828544+00:00
-- url     : https://prove2.me/submissions/c024326b-ec1c-4027-8a82-84dd5790dd01

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

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
theorem _root_.solution (a b : Q → ℂ) : star a ⬝ᵥ b = star (star b ⬝ᵥ a) := by
  simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end Formalism.FourierDecayAlt.P.HermitianFormFactor
