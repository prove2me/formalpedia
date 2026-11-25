-- Prove2me | solution 1 for CompanionTheory.D.Upq.Quot.comap_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:06:49.324436+00:00
-- url     : https://prove2.me/submissions/8511d17f-868c-41da-ace2-bfdd7c6372ef

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_ExistsQuotientMeasureUnitaryGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists
import Theorems.Thm_CompanionTheory_D_Upq_Quot_map_comap_toM
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_MG_measurableEmbedding_toM
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_measurable_lmulQ


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
theorem _root_.solution (hG : IsMatGroup G) {μ : Measure (MtM m)} (h0 : ∀ᵐ x ∂μ, Matrix.of x ∈ G)
    (g : MG G hG) (hl : μ.map (lmulQ g.mat) = μ) :
    (μ.comap (MG.toM (hG := hG))).map (g * ·) = μ.comap MG.toM := by
  have hι := MG.measurableEmbedding_toM (hG := hG)
  apply hι.map_injective
  rw [map_map hι.measurable (measurable_const_mul g)]
  have : MG.toM ∘ (fun x : MG G hG => g * x) = lmulQ g.mat ∘ MG.toM := rfl
  rw [this, ← map_map (measurable_lmulQ _) hι.measurable, map_comap_toM hG h0, hl]
end CompanionTheory.D.Upq.Quot
