-- Prove2me | solution 1 for Eden.norm_exteriorEvolution_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:48:16.665422+00:00
-- url     : https://prove2.me/submissions/e18cc82d-4282-4814-963c-1687a3e15fa2

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm
import Theorems.Thm_Eden_isGreatest_exteriorFactor
import Theorems.Thm_Eden_norm_exteriorInitialCoordinates
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_exteriorFactor_pos
import Theorems.Thm_Eden_norm_sq_exteriorEvolution
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) (c : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorEvolution k c t p v‖ ≤
      singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k * ‖v‖ := by
  classical
  let M := singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k
  obtain ⟨⟨s, hs⟩, hmax⟩ := isGreatest_exteriorFactor hk c ht p
  have hM : 0 ≤ M := by
    dsimp [M]
    rw [← hs]
    exact (exteriorFactor_pos k c ht p s).le
  have hsum : ‖exteriorEvolution k c t p v‖ ^ 2 ≤ M ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sq_exteriorEvolution k c ht p v,
      ← norm_exteriorInitialCoordinates k p v, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj₀ := (exteriorFactor_pos k c ht p j).le
    have hjM : exteriorFactor k (derivativeFactors c t p) j ≤ M := hmax ⟨j, rfl⟩
    have hsquare : (exteriorFactor k (derivativeFactors c t p) j) ^ 2 ≤ M ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsquare
      (sq_nonneg (exteriorInitialCoordinates k p v j))]
  nlinarith [norm_nonneg (exteriorEvolution k c t p v), norm_nonneg v,
    mul_nonneg hM (norm_nonneg v)]
end Eden
