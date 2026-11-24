-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.suppOK_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:13.646931+00:00
-- url     : https://prove2.me/submissions/1fdce47f-4559-4b5d-89ff-0491ed4179df

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree

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
theorem _root_.solution {p : ℕ} {f g : MvPowerSeries (Fin 2) K} (hf : SuppOK p f) (hg : SuppOK p g) :
    SuppOK p (f - g) := by
  intro n hn
  rw [map_sub] at hn
  by_cases h : MvPowerSeries.coeff n f = 0
  · apply hg n
    intro h'
    apply hn
    rw [h, h', sub_zero]
  · exact hf n h
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
