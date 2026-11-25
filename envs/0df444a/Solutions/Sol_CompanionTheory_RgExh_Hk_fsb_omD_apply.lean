-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.fsb_omD_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:05:54.122843+00:00
-- url     : https://prove2.me/submissions/62ae01d1-be3d-47ad-a900-356378066c5d

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatementStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_SimpleBackwardTransfer_FwdSimpleOfb

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
theorem _root_.solution (M : GMod n) (g : Fin n → M.V) (a : Fin n) : omD M g a = -∑ c, M.E a c (g c) := by
  simp only [omD, eeVd, LinearMap.pi_apply, LinearMap.neg_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
end CompanionTheory.RgExh.Hk
