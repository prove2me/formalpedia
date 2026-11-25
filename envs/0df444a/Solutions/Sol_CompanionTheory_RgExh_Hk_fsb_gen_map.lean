-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.fsb_gen_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:31:26.239509+00:00
-- url     : https://prove2.me/submissions/a3a907cf-efc4-42bb-b3f3-d79b694433d7

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatementStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_SimpleBackwardTransfer_FwdSimpleOfb
import Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_pow_map
import Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_omD_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
variable {n : ℕ}
namespace CompanionTheory.RgExh.Hk
theorem _root_.solution (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (μ : ℂ) (g : Fin n → M1.V) (hg : g ∈ (omD M1).maxGenEigenspace μ) :
    f.compLeft (Fin n) g ∈ (omD M2).maxGenEigenspace μ := by
  rw [Module.End.mem_maxGenEigenspace] at hg ⊢
  obtain ⟨k, hk⟩ := hg
  refine ⟨k, ?_⟩
  have h1 : ∀ v, f.compLeft (Fin n) ((omD M1 - μ • 1) v) = (omD M2 - μ • 1) (f.compLeft (Fin n) v) := by
    intro v
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, fsb_omD_map M1 M2 f hf, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_smul]
  rw [← fsb_pow_map _ _ _ h1 k g, hk, map_zero]
end CompanionTheory.RgExh.Hk
