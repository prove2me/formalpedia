-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_nablaWt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:27:02.835698+00:00
-- url     : https://prove2.me/submissions/a829a43b-883d-491f-883f-0d7994c4af16

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_weighted_homog
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_nabla_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (w y : ℕ) (hy : y ≤ w) (μ : Fin 2 → ℕ)
    (T : Submodule ℤ (MvPolynomial (Fin 2 × Fin 2) ℤ))
    (hT : ∀ j, y + j ≤ w → wt2 (w - j) (y + j) = μ → vec2 w y j ∈ T) :
    nablaWt 2 (wt2 w y) μ ≤ T := by
  intro x hx
  have hx1 := ld_nabla_le w y hy hx.1
  have hx2 : IsWeightedHomogeneous (rowW 2 2) x μ := hx.2
  rw [← hx2.weightedHomogeneousComponent_same]
  have hmap : Submodule.map (weightedHomogeneousComponent (R := ℤ) (rowW 2 2) μ)
      (Submodule.span ℤ {v | ∃ j, y + j ≤ w ∧ v = vec2 w y j}) ≤ T := by
    rw [Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    by_cases hμ : wt2 (w - j) (y + j) = μ
    · subst hμ
      rw [SetLike.mem_coe, (rank_two_vector_weighted_homog w y j hj).weightedHomogeneousComponent_same]
      exact hT j hj rfl
    · rw [SetLike.mem_coe, (rank_two_vector_weighted_homog w y j hj).weightedHomogeneousComponent_ne μ (Ne.symm hμ)]
      exact T.zero_mem
  exact hmap (Submodule.mem_map_of_mem hx1)
end Formalism.CohomologicalDescent.LD
