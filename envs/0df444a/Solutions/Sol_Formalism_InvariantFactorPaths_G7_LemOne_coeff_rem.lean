-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.coeff_rem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:45.629532+00:00
-- url     : https://prove2.me/submissions/fea74ee2-1ba1-43b3-a8a3-21ca12a65e88

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul

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
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution (p : ℕ) (f : PowerSeries K) (a b : K) (n : ℕ) :
    PowerSeries.coeff n (rem p f a b) = PowerSeries.coeff n f - a * PowerSeries.coeff n (g0F K p) -
      b * PowerSeries.coeff n (lgF K p) := by
  unfold rem
  rw [map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
end Formalism.InvariantFactorPaths.G7.LemOne
