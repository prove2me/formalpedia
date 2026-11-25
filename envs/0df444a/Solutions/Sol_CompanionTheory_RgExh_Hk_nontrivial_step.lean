-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.nontrivial_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:47.108727+00:00
-- url     : https://prove2.me/submissions/2472a40b-cbbb-4ef0-b482-59877f7a060c

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_ScalarCharacters_ScalCharOfSimple

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
open Formalism.REAL (GlRel qdet)
variable {n : ℕ}
namespace CompanionTheory.RgExh.Hk
theorem _root_.solution (hV : NonVan) {X : GMod n} {χ : Fin n → ℂ} {s : Fin n} (hH : HasChar X χ)
    (hN : Nontrivial X.V) (hf : ∀ r, χ r ≠ χ s + 1) : Nontrivial (step X (χ s)).V := by
  have h := hV n X χ s hH hN hf
  show Nontrivial ↥(stepSub X (χ s))
  exact (Submodule.nontrivial_iff_ne_bot).2 h
end CompanionTheory.RgExh.Hk
