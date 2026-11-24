-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.SmOn.clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:27:38.517795+00:00
-- url     : https://prove2.me/submissions/66c72d92-6f2b-4b51-8afb-9ea04c428ac8

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
variable {E E' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace CompanionTheory.D.Upq.Sm
namespace SmOn
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {A : Set E} {f : E → V}
    (hf : SmOn A f) (L : V →L[ℝ] W) : SmOn A (fun a => L (f a)) := fun a ha => by
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a ha
  exact ⟨U, fun x => L (F x), hU, haU, L.contDiff.comp_contDiffOn hF,
    fun g hg hgA => by simp only [hfF g hg hgA]⟩
end SmOn
end CompanionTheory.D.Upq.Sm
