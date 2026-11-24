-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_nabla_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:17:17.643563+00:00
-- url     : https://prove2.me/submissions/949755c4-3d0f-48e3-b4b3-8296b64354d2

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_def
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_anti
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpan


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
theorem _root_.solution (w y : ℕ) (hy : y ≤ w) :
    dualWeyl ℤ 2 2 (wt2 w y) ≤ Submodule.span ℤ {v | ∃ j, y + j ≤ w ∧ v = vec2 w y j} := by
  rw [standardMonomialSpan 2 2 (wt2 w y) (ld_anti w y hy)]
  refine Submodule.span_le.mpr ?_
  rintro f ⟨K, sz, hsz, I, hshape, rfl⟩
  obtain ⟨ε, α, β, hprod, hcard⟩ := ld_prod sz hsz I Finset.univ
  have h0 : (Finset.univ.filter fun k => 0 < sz k).card = w := congrFun hshape 0
  have h1 : (Finset.univ.filter fun k => 1 < sz k).card = y := congrFun hshape 1
  rw [h0, h1] at hcard
  rw [h1] at hprod
  have hα : α = w - y - β := by omega
  have : bideterminant ℤ sz hsz I = ε • vec2 w y β := by
    unfold bideterminant
    rw [hprod, hα, ← rank_two_vector_def, smul_eq_C_mul]
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨β, by omega, rfl⟩)
end Formalism.CohomologicalDescent.LD
