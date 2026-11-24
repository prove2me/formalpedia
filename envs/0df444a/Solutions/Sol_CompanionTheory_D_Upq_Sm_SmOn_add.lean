-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.SmOn.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:28:51.721802+00:00
-- url     : https://prove2.me/submissions/4eff1a02-cade-4a9a-a930-0b6e0e1b7a9d

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
theorem _root_.solution {A : Set E} {f f' : E → V} (hf : SmOn A f) (hf' : SmOn A f') :
    SmOn A (fun a => f a + f' a) := fun a ha => by
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a ha
  obtain ⟨U', F', hU', haU', hF', hfF'⟩ := hf' a ha
  exact ⟨U ∩ U', fun x => F x + F' x, hU.inter hU', ⟨haU, haU'⟩,
    (hF.mono inter_subset_left).add (hF'.mono inter_subset_right),
    fun g hg hgA => by simp only [hfF g hg.1 hgA, hfF' g hg.2 hgA]⟩
end SmOn
end CompanionTheory.D.Upq.Sm
