-- Prove2me | solution 1 for Eden.unstableRelativeTo_of_unit_plane_in
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:50:22.239123+00:00
-- url     : https://prove2.me/submissions/2e530e58-1308-41ef-92ec-1e9c66967499

import Definitions.Def_Eden_InstabilityGeometry
import Definitions.Def_Eden_NonlinearInstability
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_dist_radialPerturbation
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_one_sub_plane_radius_le_infDist
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_plane_radius_evolution_radialPerturbation
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_radiusEvolution_at_one
import Theorems.Thm_Eden_radiusEvolution_at_sqrt_two
import Theorems.Thm_Eden_radiusEvolution_at_zero
import Theorems.Thm_Eden_radiusEvolution_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_tendsto_radiusEvolution_of_lt_one
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_origin
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
attribute [local simp] Eden.radiusEvolution_at_one
attribute [local simp] Eden.radiusEvolution_at_sqrt_two
attribute [local simp] Eden.radiusEvolution_at_zero
attribute [local simp] Eden.radiusEvolution_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (j : Fin 2) {B K : Set PhaseSpace}
    {s : ℝ} (hB : ∀ r ∈ Icc (0 : ℝ) 1, radialPerturbation j r s ∈ B)
    (hend : radialPerturbation j 1 s ∈ K)
    (hunit : ∀ q ∈ K, ‖planeProjection j q‖ = 1) :
    UnstableRelativeTo c B K := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro δ hδ
  let η : ℝ := min (δ / 2) (1 / 2)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let r : ℝ := 1 - η
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hr₁ : r < 1 := by dsimp [r]; linarith
  refine ⟨radialPerturbation j r s,
    hB r ⟨hr, hr₁.le⟩, ?_, ?_⟩
  · have hd : dist (radialPerturbation j r s) (radialPerturbation j 1 s) = η := by
      rw [dist_radialPerturbation, abs_of_nonpos (by linarith : r - 1 ≤ 0)]
      dsimp [r]
      ring
    exact (Metric.infDist_le_dist_of_mem hend).trans_lt (hd.trans_lt hηδ)
  · have hsmall : ∀ᶠ t : ℝ in atTop, radiusEvolution t r < 1 / 2 :=
      (tendsto_radiusEvolution_of_lt_one hr hr₁).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    obtain ⟨t, ht, htr⟩ := ((eventually_ge_atTop (0 : ℝ)).and hsmall).exists
    refine ⟨t, ht, ?_⟩
    have hdist := one_sub_plane_radius_le_infDist j ⟨_, hend⟩ hunit
      (evolution c t (radialPerturbation j r s))
    rw [plane_radius_evolution_radialPerturbation c j ht hr] at hdist
    linarith
end Eden
