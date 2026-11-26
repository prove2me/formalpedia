-- Prove2me | solution 1 for Eden.norm_exteriorOperator_eq_singularValueFunction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:33.20357+00:00
-- url     : https://prove2.me/submissions/814276ca-1c51-43c0-a92c-424a7fe8b44c

import Definitions.Def_Eden_ExteriorGram
import Definitions.Def_Eden_ExteriorSingularValues
import Theorems.Thm_Eden_isGreatest_selectedSingularProduct
import Theorems.Thm_Eden_norm_exterior_map_singular_basis
import Theorems.Thm_Eden_norm_exterior_map_le_singularValueFunction
import Theorems.Thm_Eden_exteriorOperator_apply
import Theorems.Thm_Eden_selectedSingularProduct_nonneg


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5)
    (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    ‖exteriorOperator k A‖ = singularValueFunction A k := by
  obtain ⟨⟨s, hs⟩, hmax⟩ := isGreatest_selectedSingularProduct hk A
  have hM : 0 ≤ singularValueFunction A k := hs ▸ selectedSingularProduct_nonneg k A s
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ hM
      (norm_exterior_map_le_singularValueFunction hk A)
  · have h := (exteriorOperator k A).le_opNorm (singularExteriorBasis k A s)
    rw [exteriorOperator_apply, norm_exterior_map_singular_basis,
      OrthonormalBasis.norm_eq_one, mul_one, hs] at h
    exact h
end Eden
