-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LP.highestWeightDominant_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:35:44.747339+00:00
-- url     : https://prove2.me/submissions/98fddc4c-bae7-4c4c-9c9a-5c684cfc6ed0

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightDominantHolds
import Theorems.Thm_Formalism_CohomologicalDescent_LP_lpa_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
namespace Formalism.CohomologicalDescent.LP
theorem _root_.solution : HWDominant := by
  intro K N q _ _ _ _ _ T B hU v μ hv0 hv a b hab
  obtain ⟨hr, hd⟩ := hv
  have h2 := LinearMap.congr_fun (hU.gl a b b a) v
  rw [if_pos rfl, if_pos rfl] at h2
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hr a b hab, map_zero, sub_zero, hd a, hd b] at h2
  have hnn := lpa_nonneg hU (T b a v)
  rw [hU.adj b a v (T b a v), h2, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← sub_mul] at hnn
  have hpos := hU.pos v hv0
  by_contra hlt
  push Not at hlt
  have hneg : (μ a - μ b) * B v v < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hpos
  exact (not_le.mpr hneg) hnn
end Formalism.CohomologicalDescent.LP
