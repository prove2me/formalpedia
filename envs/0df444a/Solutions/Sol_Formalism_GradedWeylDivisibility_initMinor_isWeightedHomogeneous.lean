-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.initMinor_isWeightedHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:37.911919+00:00
-- url     : https://prove2.me/submissions/c3a8190d-e428-4a11-8d6c-17f3fafbcc88

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_sum_single_castLE

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
    IsWeightedHomogeneous (colW r n) (initMinor R I hs) (initW n s) := by
  rw [← mem_weightedHomogeneousSubmodule]
  unfold initMinor
  rw [Matrix.det_apply]
  refine _root_.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule, ← sum_single_castLE hs]
  apply IsWeightedHomogeneous.prod
  intro q _
  exact isWeightedHomogeneous_X (R := R) (colW r n) (I (σ q), Fin.castLE hs q)
end Formalism.GradedWeylDivisibility
