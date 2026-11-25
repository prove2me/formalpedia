-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.UnitPf.diff_mem_Isub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:24:29.143845+00:00
-- url     : https://prove2.me/submissions/a2cbf8b9-74b7-4a6d-a466-075a73e78cea

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_RightCasimirMemSubmodule
import Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_eta_mem_Isub
import Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_UnitPf_Om__mem_Isub_9bd49289c361

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
theorem _root_.solution (β : ℂ) (k : ℕ) (H) :
    ((Om' X - β • 1) ^ k) H - ((y2 X - β • 1) ^ k) H ∈ Isub X := by
  induction k generalizing H with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    have e : (Om' X - β • 1) (((Om' X - β • 1) ^ k) H) - (y2 X - β • 1) (((y2 X - β • 1) ^ k) H) =
        (Om' X - β • 1) (((Om' X - β • 1) ^ k) H - ((y2 X - β • 1) ^ k) H) +
          eta X (psi X (((y2 X - β • 1) ^ k) H)) := by
      simp only [map_sub, Om', LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        Module.End.one_apply]
      abel
    rw [e]
    refine add_mem ?_ (eta_mem_Isub _)
    have hm := ih H
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact sub_mem (Om'_mem_Isub hm) (Submodule.smul_mem _ _ hm)
end CompanionTheory.RgExh.Hk.UnitPf
