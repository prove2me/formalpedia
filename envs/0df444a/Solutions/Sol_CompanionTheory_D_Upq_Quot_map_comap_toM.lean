-- Prove2me | solution 1 for CompanionTheory.D.Upq.Quot.map_comap_toM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:13.877849+00:00
-- url     : https://prove2.me/submissions/b82f33bf-8843-4795-812c-1a02259fb152

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_ExistsQuotientMeasureUnitaryGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_MG_measurableEmbedding_toM
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_MG_range_toM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace Set
open scoped ENNReal NNReal Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Quot
open PI CompanionTheory.D.Upq.ModEx
variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)}
namespace CompanionTheory.D.Upq.Quot
theorem _root_.solution (hG : IsMatGroup G) {μ : Measure (MtM m)}
    (h0 : ∀ᵐ x ∂μ, Matrix.of x ∈ G) : (μ.comap (MG.toM (hG := hG))).map MG.toM = μ := by
  rw [MG.measurableEmbedding_toM.map_comap, MG.range_toM]
  exact restrict_eq_self_of_ae_mem h0
end CompanionTheory.D.Upq.Quot
