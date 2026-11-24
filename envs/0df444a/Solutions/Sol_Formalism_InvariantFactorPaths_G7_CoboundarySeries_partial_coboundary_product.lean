-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.partial_coboundary_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:10.762388+00:00
-- url     : https://prove2.me/submissions/34fe72ce-e87a-4cb5-9611-e9b416345b40

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_has_subst_coboundary_first
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_has_subst_last_pair
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_include_three_coboundary

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
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0)
    (f g : PowerSeries K) : d1 F (at1 0 f * at1 1 g) = in3 (cob F f) * at1 2 g := by
  unfold d1
  rw [MvPowerSeries.subst_mul (has_subst_coboundary_first hF), MvPowerSeries.subst_mul (has_subst_last_pair 0), MvPowerSeries.subst_mul (has_subst_last_pair 1),
    subst_single_var (has_subst_coboundary_first hF), subst_single_var (has_subst_coboundary_first hF), subst_single_var (has_subst_last_pair 0), subst_single_var (has_subst_last_pair 0),
    subst_single_var (has_subst_last_pair 1), subst_single_var (has_subst_last_pair 1), include_three_coboundary hF]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  unfold at1
  ring
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
