-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.arithmetic_lattice_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:41.925422+00:00
-- url     : https://prove2.me/submissions/76498797-68c8-449b-9449-77b309473a41

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_unipotent_upper_entries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution : AlHyp := by
  intro M sh ch u u' hM hsh hch hchsh hc hu
  obtain ⟨_, hbc, _, hA⟩ := unipotent_upper_entries M hM
  have ha := hA sh ch hsh hch hchsh hc
  have hb : ‖M 0 1‖ = 1 / sh := hbc.trans hc
  calc ‖M 0 0 * u + M 0 1 * u'‖ ≤ ‖M 0 0 * u‖ + ‖M 0 1 * u'‖ := norm_add_le _ _
    _ = ch / sh * ‖u‖ + 1 / sh * ‖u‖ := by rw [norm_mul, norm_mul, ha, hb, hu]
    _ = ‖u‖ * (1 + ch) / sh := by ring
end Formalism.SLP.GlobalBoundRefinements.P
