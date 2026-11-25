-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.piIso_tensVd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:19.026361+00:00
-- url     : https://prove2.me/submissions/30f679d1-e61d-4dfa-a84a-05a78bc3fb81

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
    (a b : Fin n) (f : Fin n → X.V) : piIso e (tensVd X.E a b f) = tensVd X'.E a b (piIso e f) := by
  funext d
  by_cases hd : d = b
  · subst hd
    simp [piIso, tensVd, he]
  · simp [piIso, tensVd, he, hd]
end CompanionTheory.RgExh.Hk
