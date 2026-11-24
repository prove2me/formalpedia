-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.log_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:28:33.061308+00:00
-- url     : https://prove2.me/submissions/73d38e48-3072-4be8-ab0a-a63442a4c2fd

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_subst_lgF_scale


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
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : LogCoord := by
  intro K _ p ϖ μ _ _ h0 h1
  have e1 := LogarithmEquivalence.subst_lgF_scale p ϖ
  have hμ : PowerSeries.HasSubst μ := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hX : PowerSeries.HasSubst (PowerSeries.C ϖ * PowerSeries.X : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have e2 := congrArg (fun f => (PowerSeries.subst μ f : PowerSeries K)) e1
  rw [PowerSeries.subst_comp_subst_apply hX hμ] at e2
  rw [← PowerSeries.coe_substAlgHom hμ, map_mul, map_mul, PowerSeries.coe_substAlgHom hμ, h1,
    PowerSeries.subst_X hμ] at e2
  have e3 : (PowerSeries.substAlgHom hμ) (PowerSeries.C ϖ : PowerSeries K) = PowerSeries.C ϖ := by
    have : (PowerSeries.C ϖ : PowerSeries K) = algebraMap K _ ϖ := rfl
    rw [this, AlgHom.commutes]
  rw [PowerSeries.coe_substAlgHom hμ] at e3
  rw [e3] at e2
  exact e2
end Formalism.InvariantFactorPaths.G7
