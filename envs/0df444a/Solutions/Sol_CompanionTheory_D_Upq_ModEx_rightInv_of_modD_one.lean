-- Prove2me | solution 1 for CompanionTheory.D.Upq.ModEx.rightInv_of_modD_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:14.668795+00:00
-- url     : https://prove2.me/submissions/caa77f84-4d4a-42ab-9066-c241d429bcb5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_map_mul_right_of_modular_one
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_MG_measurableEmbedding_toM
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_MG_range_toM
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_modD_of_mem
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_measurable_lmulQ
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_measurable_rmulQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace
open scoped ENNReal NNReal Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.ModEx
open PI PI.QuotSetU.UnitaryGroupMassFormula
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
namespace CompanionTheory.D.Upq.ModEx
theorem _root_.solution (hG : IsMatGroup G) (h1 : ∀ g ∈ G, modD hG g = 1)
    (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) : IsRightInvM G μ := by
  obtain ⟨hσ, -, h0, hl⟩ := hμ
  have hι := MG.measurableEmbedding_toM (hG := hG)
  set ν : Measure (MG G hG) := μ.comap MG.toM with hν
  have hmap : ν.map MG.toM = μ := by
    rw [hν, hι.map_comap, MG.range_toM]
    exact restrict_eq_self_of_ae_mem h0
  haveI : SigmaFinite ν := SigmaFinite.of_map ν hι.measurable.aemeasurable (by rwa [hmap])
  haveI : IsMulLeftInvariant ν := ⟨fun g => by
    apply hι.map_injective
    rw [map_map hι.measurable (measurable_const_mul g)]
    have : MG.toM ∘ (fun x : MG G hG => g * x) = lmulQ g.mat ∘ MG.toM := rfl
    rw [this, ← map_map (measurable_lmulQ _) hι.measurable, hmap, hl _ g.mem]⟩
  have hΔ : ∀ g : MG G hG, modularCharacterFun g = 1 := fun g => by
    have := h1 g.mat g.mem
    rw [modD_of_mem g.mem] at this
    exact_mod_cast this
  intro s hs
  have h := map_mul_right_of_modular_one hΔ ν (MG.mk hG s hs)
  have e : rmulQ s ∘ MG.toM = MG.toM ∘ (fun x : MG G hG => x * MG.mk hG s hs) := rfl
  rw [← hmap, map_map (measurable_rmulQ _) hι.measurable, e,
    ← map_map hι.measurable (measurable_mul_const _), h]
end CompanionTheory.D.Upq.ModEx
