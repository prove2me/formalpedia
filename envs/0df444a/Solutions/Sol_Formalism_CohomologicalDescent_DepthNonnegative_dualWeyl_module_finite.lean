-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.dualWeyl_module_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:06.676372+00:00
-- url     : https://prove2.me/submissions/e6a7ca9b-1512-4625-b308-d578869fb2bd

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_weight_sum
import Theorems.Thm_Formalism_GradedWeylDivisibility_mem_dualWeyl_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution (O : Type) [CommRing O] [IsNoetherianRing O] (r n : ℕ) (ν : Fin n → ℕ) :
    Module.Finite O (dualWeyl O r n ν) := by
  have h : dualWeyl O r n ν ≤ homogeneousSubmodule (Fin r × Fin n) O (∑ s, ν s) := by
    intro f hf
    have h1 := (mem_dualWeyl_iff.1 hf).1
    rw [mem_homogeneousSubmodule]
    intro m hm
    rw [← lclosedeq_weight_sum, h1 hm]
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le (homogeneousSubmodule_fg _ _ _) h)
end Formalism.CohomologicalDescent.DepthNonnegative
