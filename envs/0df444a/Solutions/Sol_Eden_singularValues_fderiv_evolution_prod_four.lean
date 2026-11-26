-- Prove2me | solution 1 for Eden.singularValues_fderiv_evolution_prod_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:06.635521+00:00
-- url     : https://prove2.me/submissions/1e83c405-235f-49e8-a307-f105fd38ab83

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_planar_factors_product
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValues_fderiv_evolution
import Theorems.Thm_Eden_singularValues_fderiv_evolution_fifth
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_5272e4fb8458
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_7729c3bfdb8d
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
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


attribute [local simp] Eden.radialDefect_at_one

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Real.exp (4 * t - 6 * volumeDefect t p) := by
  let A := (fderiv ℝ (evolution c t) p).toLinearMap
  have hm := congrArg Multiset.prod (singularValues_fderiv_evolution c ht p)
  have hprod : (∏ i : Fin 5, A.singularValues i) = ∏ i : Fin 5, derivativeFactors c t p i := by
    simpa only [Finset.prod_eq_multiset_prod] using hm
  rw [Fin.prod_univ_castSucc] at hprod
  have hlast := singularValues_fderiv_evolution_fifth hc ht hp
  change A.singularValues 4 = _ at hlast
  simp only [Fin.val_castSucc, Fin.val_last] at hprod
  rw [hlast] at hprod
  have hright : (∏ i : Fin 5, derivativeFactors c t p i) =
      Real.exp (4 * t - 6 * volumeDefect t p) * Real.exp (-c * t) := by
    rw [Fin.prod_univ_five]
    change radialAmplitude t (radiusSq₁ p) * planarAmplitude t (radiusSq₁ p) *
      radialAmplitude t (radiusSq₂ p) * planarAmplitude t (radiusSq₂ p) *
      Real.exp (-c * t) = _
    rw [mul_assoc (radialAmplitude t (radiusSq₁ p) * planarAmplitude t (radiusSq₁ p))
      (radialAmplitude t (radiusSq₂ p)) (planarAmplitude t (radiusSq₂ p)),
      planar_factors_product ht (radiusSq₁_nonneg p),
      planar_factors_product ht (radiusSq₂_nonneg p), ← Real.exp_add]
    congr 2
    dsimp [volumeDefect]
    ring
  rw [hright] at hprod
  exact mul_right_cancel₀ (ne_of_gt (Real.exp_pos _)) hprod
end Eden
