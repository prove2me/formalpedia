-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.residuallyGenericExists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:11.103804+00:00
-- url     : https://prove2.me/submissions/faf5ede0-cc2c-40e8-bc04-7f6426640762

import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_gAbs_add_le_max
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_gAbs_algebraMap
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_gN_map_int
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_eval__ringHom_eq_ab9ee6c66867
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_aeval_int_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : GenericExists := by
  intro l _ σ _
  let inst : NormedField (GK ℂ_[l] σ) := (gAbs ℂ_[l] σ).toNormedField
  let ι : MvPolynomial σ ℂ_[l] →+* GK ℂ_[l] σ := algebraMap _ _
  have hι : ∀ P, ‖ι P‖ = gN P := fun P => gAbs_algebraMap P
  have hev : ∀ P, eval₂ (ι.comp C) (fun i => ι (X i)) P = ι P := eval₂_ringHom_eq ι
  refine ⟨GK ℂ_[l] σ, inst, ?_, ?_, ι.comp C, fun i => ι (X i), ?_, ?_, ?_⟩
  · exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      fun x y => gAbs_add_le_max x y
  · exact charZero_of_injective_ringHom (ι.comp C).injective
  · intro z
    rw [RingHom.comp_apply, hι, gN_C]
  · intro P
    rw [hev, hι]
    rfl
  · intro P hP
    refine (congrArg norm (@aeval_int_eq σ ℂ_[l] (GK ℂ_[l] σ) _ _ (Ring.toIntAlgebra _) ι P)).trans ?_
    rw [hι]
    exact gN_map_int l P hP
end Formalism.DworkPowerSeriesWeights
