-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.subst_single_var
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:21.582555+00:00
-- url     : https://prove2.me/submissions/1587d230-3223-4e98-8dd3-1644505b85b4

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_subst

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
theorem _root_.solution {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b)
    (x : ι) (f : PowerSeries K) : subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  rw [subst_subst hb (PowerSeries.HasSubst.X x), MvPowerSeries.subst_X hb]
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
