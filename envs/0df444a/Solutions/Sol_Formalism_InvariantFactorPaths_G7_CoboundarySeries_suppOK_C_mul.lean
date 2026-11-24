-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.suppOK_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:35.131799+00:00
-- url     : https://prove2.me/submissions/8ded220b-6dd5-43b3-b09e-1b2642a95619

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
theorem _root_.solution {p : ℕ} (a : K) {f : MvPowerSeries (Fin 2) K} (hf : SuppOK p f) :
    SuppOK p (C a * f) := by
  intro n hn
  rw [MvPowerSeries.coeff_C_mul] at hn
  exact hf n (right_ne_zero_of_mul hn)
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
