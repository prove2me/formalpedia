-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.include_three_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:35.099507+00:00
-- url     : https://prove2.me/submissions/6430bfaa-56f9-46ad-a583-0c79cb117406

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_has_subst_first_pair
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_single_var

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
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) (f : PowerSeries K) :
    in3 (cob F f) = PowerSeries.subst (in3 F) f - at1 0 f - at1 1 f := by
  have hF' : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  have h1 : in3 (PowerSeries.subst F f) = PowerSeries.subst (in3 F) f := subst_subst has_subst_first_pair hF' f
  have h2 : in3 (at1 (0 : Fin 2) f) = at1 0 f := by
    unfold in3
    rw [subst_single_var has_subst_first_pair]
    rfl
  have h3 : in3 (at1 (1 : Fin 2) f) = at1 1 f := by
    unfold in3
    rw [subst_single_var has_subst_first_pair]
    rfl
  unfold cob
  show subst _ (PowerSeries.subst F f - at1 0 f - at1 1 f) = _
  rw [MvPowerSeries.subst_sub has_subst_first_pair, MvPowerSeries.subst_sub has_subst_first_pair]
  exact congr_arg₂ (· - ·) (congr_arg₂ (· - ·) h1 h2) h3
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
