-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.rank2Exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:48.418251+00:00
-- url     : https://prove2.me/submissions/9d3dc407-b00e-46ae-86f7-3ed285ad8d9f

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_ne_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_weighted_homog
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_mem_dual_weyl
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_nablaWt_le
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_weyl_le
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_gen_mem_weyl

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
theorem _root_.solution : Rank2Exact := by
  intro w y i h
  have hy : y ≤ w := by omega
  refine ⟨le_antisymm ?_ ?_, rank_two_vector_ne_zero w y i, ?_⟩
  · refine ld_nablaWt_le w y hy _ _ ?_
    intro j hj hμ
    have h1 : y + j = y + i := congrFun hμ 1
    have hji : j = i := by omega
    rw [hji]
    exact Submodule.mem_span_singleton_self _
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    exact ⟨rank_two_vector_mem_dual_weyl w y i h, rank_two_vector_weighted_homog w y i h⟩
  · intro c
    constructor
    · intro hc
      have hcM := ld_weyl_le w y hy hc
      have hmap : Submodule.map (weightedHomogeneousComponent (R := ℤ) (rowW 2 2) (wt2 (w - i) (y + i)))
          (ldM w y) ≤ Submodule.span ℤ {((w - y).choose i : ℤ) • vec2 w y i} := by
        unfold ldM
        rw [Submodule.map_span]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, map_smul]
        by_cases hji : j = i
        · subst hji
          rw [(rank_two_vector_weighted_homog w y j hj).weightedHomogeneousComponent_same]
          exact Submodule.mem_span_singleton_self _
        · have hne : wt2 (w - i) (y + i) ≠ wt2 (w - j) (y + j) := by
            intro hμ
            have h1 : y + i = y + j := congrFun hμ 1
            omega
          rw [(rank_two_vector_weighted_homog w y j hj).weightedHomogeneousComponent_ne _ hne, smul_zero]
          exact Submodule.zero_mem _
      have h2 := hmap (Submodule.mem_map_of_mem hcM)
      rw [map_smul, (rank_two_vector_weighted_homog w y i h).weightedHomogeneousComponent_same] at h2
      obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp h2
      rw [smul_smul] at hd
      have h3 : (d * ((w - y).choose i : ℤ) - c) • vec2 w y i = 0 := by
        rw [sub_smul, hd, sub_self]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · exact ⟨d, by linarith⟩
      · exact absurd h4 (rank_two_vector_ne_zero w y i)
    · rintro ⟨d, rfl⟩
      rw [mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (ld_gen_mem_weyl w y i)
end Formalism.CohomologicalDescent.LD
