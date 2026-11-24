-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.partial_coboundary_h_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:52:05.060024+00:00
-- url     : https://prove2.me/submissions/84df47f9-7d3b-4ba9-ba0f-af239519ece0

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_partial_coboundary_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_partial_coboundary_C_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_partial_coboundary_product
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_include_three_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.CoboundarySeries
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoboundarySeries
theorem _root_.solution {p : ℕ} (σ : K →+* K) {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0)
    (hl : cob F (lgF K p) = 0) (G : MvPowerSeries (Fin 2) K) (γ γ' : K) :
    d1 F (Hser p σ G γ γ') =
      d1 F (DeS p σ G) - C γ * (in3 (cob F (g0F K p)) * at1 2 (lgF K p)) := by
  unfold Hser
  rw [partial_coboundary_sub hF, partial_coboundary_sub hF, partial_coboundary_C_mul hF, partial_coboundary_C_mul hF, partial_coboundary_product hF, partial_coboundary_product hF, hl, include_three_zero]
  ring
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
