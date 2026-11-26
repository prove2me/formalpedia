-- Prove2me | solution 1 for Eden.supremumSingularProduct_four_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:27.326555+00:00
-- url     : https://prove2.me/submissions/13be009e-08f3-46e5-8633-98389c9ce80c

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_integerGrowthValues_nonempty
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValueFunction_evolution_on_four_five
import Theorems.Thm_Eden_singularValueFunction_le_supremum
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_torus_nonempty
import Theorems.Thm_Eden_torus_subset_attractor
import Theorems.Thm_Eden_volumeDefect_nonneg
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
attribute [local simp] Eden.radialDefect_at_one
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
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {k : ℕ} (hk₄ : 4 ≤ k) (hk₅ : k ≤ 5) :
    supremumSingularProduct c k t =
      Real.exp (4 * t - c * t * ((k : ℝ) - 4)) := by
  have hl : (4 : ℝ) ≤ k := by exact_mod_cast hk₄
  have hu : (k : ℝ) ≤ 5 := by exact_mod_cast hk₅
  apply le_antisymm
  · apply csSup_le (integerGrowthValues_nonempty c k t)
    rintro x ⟨p, hp, rfl⟩
    dsimp only
    rw [singularValueFunction_evolution_on_four_five hc ht hp hl hu]
    exact Real.exp_le_exp.mpr (by linarith [volumeDefect_nonneg ht p])
  · obtain ⟨p, hp⟩ := torus_nonempty
    have ha := torus_subset_attractor hp
    have he : volumeDefect t p = 0 := by
      simp [volumeDefect, hp.1, hp.2.1]
    have hv := singularValueFunction_le_supremum hk₅ hc ht ha
    rw [singularValueFunction_evolution_on_four_five hc ht ha hl hu, he] at hv
    simpa using hv
end Eden
