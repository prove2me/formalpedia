-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.generic_elements_exist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:20:25.726314+00:00
-- url     : https://prove2.me/submissions/c60c0877-42b0-4f33-aa58-7ac3f6ac04cf

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGaussK
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_gAbs_add_le_max
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_gAbs_algebraMap
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_eval__ringHom_eq_ab9ee6c66867


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : GenericExistsK := by
  intro F σ _ _ _ _
  let inst : NormedField (Formalism.DworkPowerSeriesWeights.GK F σ) := (Formalism.DworkPowerSeriesWeights.gAbs F σ).toNormedField
  let ι : MvPolynomial σ F →+* Formalism.DworkPowerSeriesWeights.GK F σ := algebraMap _ _
  have hι : ∀ P, ‖ι P‖ = Formalism.DworkPowerSeriesWeights.gN P := fun P => Formalism.DworkPowerSeriesWeights.gAbs_algebraMap P
  have hev : ∀ P, MvPolynomial.eval₂ (ι.comp MvPolynomial.C) (fun i => ι (MvPolynomial.X i)) P = ι P :=
    Formalism.DworkPowerSeriesWeights.eval₂_ringHom_eq ι
  refine ⟨Formalism.DworkPowerSeriesWeights.GK F σ, inst, ?_, ?_, ι.comp MvPolynomial.C, fun i => ι (MvPolynomial.X i),
    ?_, ?_⟩
  · exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      fun x y => Formalism.DworkPowerSeriesWeights.gAbs_add_le_max x y
  · exact charZero_of_injective_ringHom (ι.comp MvPolynomial.C).injective
  · intro z
    rw [RingHom.comp_apply, hι, Formalism.DworkPowerSeriesWeights.gN_C]
  · intro P
    rw [hev, hι]
    rfl
end Formalism.InvariantFactorPaths.G7
