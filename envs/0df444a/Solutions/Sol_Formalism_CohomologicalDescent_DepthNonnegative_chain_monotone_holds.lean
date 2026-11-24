-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.chain_monotone_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:48.913437+00:00
-- url     : https://prove2.me/submissions/9fa82268-83e2-4a07-8811-467070080e73

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_tprod_mem_tensorSubmodule
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_tensorSubmodule_le_of_tprod_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : ChainMono := by
  intro O _ ι _ _ Nb _ _ B s s' hss
  apply tensorSubmodule_le_of_tprod_mem
  intro x hx
  apply tprod_mem_tensorSubmodule
  intro τ
  have h1 := hx τ
  simp only [chainB] at h1 ⊢
  by_cases h : τ ∈ s
  · rw [if_pos (hss h)]
    trivial
  · rw [if_neg h] at h1
    split_ifs
    · trivial
    · exact h1
end Formalism.CohomologicalDescent.DepthNonnegative
