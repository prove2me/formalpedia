-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.polarization_of_orthogonal_splittings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:08.030281+00:00
-- url     : https://prove2.me/submissions/fb0fc8f8-c527-40eb-ba4a-cf0fdd482d43

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DetIndexProductHyperbolicInequality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution : Formalism.SLP.GlobalBoundRefinements.Polarise := by
  intro V _ _ h hsym y A y' A' hw hyA hyA'
  have hAy : h A y = 0 := by rw [hsym y A, hyA, map_zero]
  have hAy' : h A' y' = 0 := by rw [hsym y' A', hyA', map_zero]
  have e1 : h (y - A) (y - A) = h y y + h A A := by
    simp only [map_sub, LinearMap.sub_apply, hyA, hAy]
    ring
  have e2 : h (y' + A') (y' + A') = h y' y' + h A' A' := by
    simp only [map_add, LinearMap.add_apply, hyA', hAy']
    ring
  rw [← e1, ← e2, hw]
end Formalism.SLP.GlobalBoundRefinements.P
