-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.one_mem_dualWeyl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:14.874723+00:00
-- url     : https://prove2.me/submissions/c64f755b-abce-421b-a89d-7ac7330abcaf

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_mem_dualWeyl_iff

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
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} :
    (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  rw [mem_dualWeyl_iff]
  refine ⟨isWeightedHomogeneous_one _ _, fun l j _ => ?_⟩
  rw [map_one, map_one]
end Formalism.GradedWeylDivisibility
