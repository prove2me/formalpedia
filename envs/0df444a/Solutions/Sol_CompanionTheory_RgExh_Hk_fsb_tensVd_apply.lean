-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.fsb_tensVd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:06.992691+00:00
-- url     : https://prove2.me/submissions/08916f82-6293-4dd4-a6dc-cf9619d8950c

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
theorem _root_.solution (M : GMod n) (a b : Fin n) (g : Fin n → M.V) (d : Fin n) :
    tensVd M.E a b g d = M.E a b (g d) - if d = b then g a else 0 := by
  simp only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  split_ifs <;> simp
end CompanionTheory.RgExh.Hk
