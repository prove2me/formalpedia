-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.UnitPf.right_casimir_mem_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:06.418728+00:00
-- url     : https://prove2.me/submissions/285202e7-b093-4eff-a6c4-846e96c86982

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_RightCasimirMemSubmodule
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_mem_Isub
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_commute_left_right_casimir
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_right_casimir_eta


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh
variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}
namespace CompanionTheory.RgExh.Hk.UnitPf
theorem _root_.solution {H} (h : H ∈ Isub X) : y2 X H ∈ Isub X := by
  refine Submodule.iSup_induction _ (motive := fun H => y2 X H ∈ Isub X) h ?_ (by simp) ?_
  · rintro k _ ⟨v, rfl⟩
    simp only [LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← ((commute_left_right_casimir (X := X)).pow_left k).eq, Module.End.mul_apply, right_casimir_eta, map_neg,
      map_add, map_smul]
    refine neg_mem (add_mem ?_ (Submodule.smul_mem _ _ (mem_Isub k v)))
    have := mem_Isub (X := X) (k + 1) v
    rwa [pow_succ, Module.End.mul_apply] at this
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
end CompanionTheory.RgExh.Hk.UnitPf
