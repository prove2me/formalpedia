-- Prove2me | solution 1 for Eden.inner_exterior_map_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:56.277728+00:00
-- url     : https://prove2.me/submissions/295d6468-0862-4e81-a95c-6bec935561be

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_exteriorBasis_apply
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
open scoped RealInnerProductSpace
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (v w : ExteriorSpace k) :
    ⟪exteriorPower.map k A v, exteriorPower.map k A w⟫ =
      ⟪v, exteriorPower.map k (A.adjoint ∘ₗ A) w⟫ := by
  classical
  have hb (s r : ExteriorIndex k) :
      ⟪exteriorPower.map k A (exteriorBasis k s),
        exteriorPower.map k A (exteriorBasis k r)⟫ =
      ⟪exteriorBasis k s, exteriorPower.map k (A.adjoint ∘ₗ A) (exteriorBasis k r)⟫ := by
    simp only [exteriorBasis_apply, exteriorPower.ιMulti_family,
      exteriorPower.map_apply_ιMulti, exteriorPower.inner_ιMulti_ιMulti,
      Function.comp_def, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  rw [← (exteriorBasis k).sum_repr v, ← (exteriorBasis k).sum_repr w]
  simp only [map_sum, map_smul, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  have hleft (r : ℝ) (x y : ExteriorSpace k) : ⟪r • x, y⟫ = r * ⟪x, y⟫ :=
    real_inner_smul_left x y r
  have hright (r : ℝ) (x y : ExteriorSpace k) : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
    real_inner_smul_right x y r
  simp only [hleft, hright, hb]
end Eden
