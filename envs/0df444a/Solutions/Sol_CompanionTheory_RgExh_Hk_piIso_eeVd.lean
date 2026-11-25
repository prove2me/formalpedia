-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.piIso_eeVd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:40.008358+00:00
-- url     : https://prove2.me/submissions/ed14962a-3f33-4850-8426-a3770b77448a

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_TensorReflections_PiIsoTensVd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {n : ℕ}
namespace CompanionTheory.RgExh.Hk
theorem _root_.solution {X X' : GMod n} (e : X.V ≃ₗ[ℂ] X'.V) (he : ∀ a b x, e (X.E a b x) = X'.E a b (e x))
    (f : Fin n → X.V) : piIso e (eeVd X.E f) = eeVd X'.E (piIso e f) := by
  funext a
  simp [piIso, eeVd, he, map_sum]
end CompanionTheory.RgExh.Hk
