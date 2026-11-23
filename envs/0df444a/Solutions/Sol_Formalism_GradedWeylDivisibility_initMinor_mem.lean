-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.initMinor_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:29.076162+00:00
-- url     : https://prove2.me/submissions/e1e8817e-56c5-41a9-ba6d-d26f15f2a485

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_isWeightedHomogeneous
import Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs ∈ dualWeyl R r n (initW n s) := by
  unfold dualWeyl
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact initMinor_isWeightedHomogeneous I hs
  · simp only [Submodule.mem_iInf]
    intro l j hlj
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact initMinor_invariant I hs l j hlj
end Formalism.GradedWeylDivisibility
