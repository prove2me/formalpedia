-- Prove2me | solution 1 for Eden.norm_exterior_map_le_singularValueFunction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:12.041015+00:00
-- url     : https://prove2.me/submissions/096f663d-f2e5-47a9-8e26-944344b3cef9

import Definitions.Def_Eden_ExteriorGram
import Definitions.Def_Eden_ExteriorSingularValues
import Theorems.Thm_Eden_isGreatest_selectedSingularProduct
import Theorems.Thm_Eden_norm_sq_exterior_map_singular_basis
import Theorems.Thm_Eden_selectedSingularProduct_nonneg


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5)
    (A : PhaseSpace →ₗ[ℝ] PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorPower.map k A v‖ ≤ singularValueFunction A k * ‖v‖ := by
  classical
  obtain ⟨⟨s, hs⟩, hmax⟩ := isGreatest_selectedSingularProduct hk A
  have hM : 0 ≤ singularValueFunction A k := hs ▸ selectedSingularProduct_nonneg k A s
  have hsum : ‖exteriorPower.map k A v‖ ^ 2 ≤ (singularValueFunction A k) ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sq_exterior_map_singular_basis,
      ← (singularExteriorBasis k A).repr.norm_map v, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj₀ := selectedSingularProduct_nonneg k A j
    have hjM := hmax ⟨j, rfl⟩
    have hsquare : selectedSingularProduct k A j ^ 2 ≤ singularValueFunction A k ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsquare
      (sq_nonneg ((singularExteriorBasis k A).repr v j))]
  nlinarith [norm_nonneg (exteriorPower.map k A v), norm_nonneg v,
    mul_nonneg hM (norm_nonneg v)]
end Eden
