-- Prove2me | solution 1 for CohnElkies.poissonLogistic_lowerWallisPhase_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/ed343dec-8afe-416e-b89c-1efa3852914f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogisticDensity_integrable
import Theorems.Thm_CohnElkies_poissonLogisticDensity_abs_moment_integrable
import Theorems.Thm_CohnElkies_lowerWallisPhaseKernel_abs_le_moment
import Theorems.Thm_CohnElkies_lowerWallisPhaseKernel_abs_le_tail
import Theorems.Thm_CohnElkies_lowerWallisPhaseTail_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution :
    Integrable
      (fun p : ℝ × ℝ =>
        poissonLogisticDensity p.1 *
          lowerWallisPhaseKernel p.1 p.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  let F : ℝ × ℝ → ℝ := fun p =>
    poissonLogisticDensity p.1 *
      lowerWallisPhaseKernel p.1 p.2
  have hmeas : Measurable F := by
    try dsimp [F]
    unfold poissonLogisticDensity lowerWallisPhaseKernel
    fun_prop
  have hfrequency :
      Integrable
        (fun u : ℝ =>
          poissonLogisticDensity u * (|u| + 1)) := by
    have h :=
      (poissonLogisticDensity_abs_moment_integrable 1).add
        poissonLogisticDensity_integrable
    simpa [Pi.add_apply, pow_one, mul_add] using! h
  have hnearConstant :
      Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hnearMajor := hfrequency.mul_prod hnearConstant
  have hnearMembership :
      ∀ᵐ p : ℝ × ℝ ∂volume.prod
          (volume.restrict (Ioc (0 : ℝ) 1)),
        p.2 ∈ Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Ioc.preimage measurable_snd)).2
    exact Filter.Eventually.of_forall
      (fun _ => ae_restrict_mem measurableSet_Ioc)
  have hnear :
      Integrable F
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply hnearMajor.mono' hmeas.aestronglyMeasurable
    filter_upwards [hnearMembership] with p hp
    have hdensity : 0 < poissonLogisticDensity p.1 := by
      unfold poissonLogisticDensity
      positivity
    change
      |poissonLogisticDensity p.1 *
          lowerWallisPhaseKernel p.1 p.2| ≤
        (poissonLogisticDensity p.1 * (|p.1| + 1)) * 1
    rw [abs_mul, abs_of_pos hdensity, mul_one]
    exact mul_le_mul_of_nonneg_left
      (lowerWallisPhaseKernel_abs_le_moment p.1 hp.1)
      hdensity.le
  have hfarMajor :=
    poissonLogisticDensity_integrable.mul_prod
      lowerWallisPhaseTail_integrable
  have hfarMembership :
      ∀ᵐ p : ℝ × ℝ ∂volume.prod
          (volume.restrict (Ioi (1 : ℝ))),
        p.2 ∈ Ioi (1 : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Ioi.preimage measurable_snd)).2
    exact Filter.Eventually.of_forall
      (fun _ => ae_restrict_mem measurableSet_Ioi)
  have hfar :
      Integrable F
        (volume.prod (volume.restrict (Ioi (1 : ℝ)))) := by
    apply hfarMajor.mono' hmeas.aestronglyMeasurable
    filter_upwards [hfarMembership] with p hp
    have hdensity : 0 < poissonLogisticDensity p.1 := by
      unfold poissonLogisticDensity
      positivity
    change
      |poissonLogisticDensity p.1 *
          lowerWallisPhaseKernel p.1 p.2| ≤
        poissonLogisticDensity p.1 *
          (1 / p.2 ^ 2 + Real.exp (-p.2))
    rw [abs_mul, abs_of_pos hdensity]
    exact mul_le_mul_of_nonneg_left
      (lowerWallisPhaseKernel_abs_le_tail p.1 hp.le)
      hdensity.le
  have hnearOn :
      IntegrableOn F
        ((Set.univ : Set ℝ) ×ˢ Ioc (0 : ℝ) 1)
        (volume.prod volume) := by
    change
      Integrable F
        ((volume.prod volume).restrict
          ((Set.univ : Set ℝ) ×ˢ Ioc (0 : ℝ) 1))
    rw [← Measure.prod_restrict]
    simpa only [Measure.restrict_univ] using! hnear
  have hfarOn :
      IntegrableOn F
        ((Set.univ : Set ℝ) ×ˢ Ioi (1 : ℝ))
        (volume.prod volume) := by
    change
      Integrable F
        ((volume.prod volume).restrict
          ((Set.univ : Set ℝ) ×ˢ Ioi (1 : ℝ)))
    rw [← Measure.prod_restrict]
    simpa only [Measure.restrict_univ] using! hfar
  have hsets :
      (((Set.univ : Set ℝ) ×ˢ Ioc (0 : ℝ) 1) ∪
        ((Set.univ : Set ℝ) ×ˢ Ioi (1 : ℝ))) =
          (Set.univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
    rw [← Set.prod_union,
      Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  have hfull :
      IntegrableOn F
        ((Set.univ : Set ℝ) ×ˢ Ioi (0 : ℝ))
        (volume.prod volume) := by
    rw [← hsets]
    exact hnearOn.union hfarOn
  change
    Integrable F
      (volume.prod (volume.restrict (Ioi 0)))
  have hproduct := hfull
  change
    Integrable F
      ((volume.prod volume).restrict
        ((Set.univ : Set ℝ) ×ˢ Ioi (0 : ℝ))) at hproduct
  rw [← Measure.prod_restrict] at hproduct
  simpa only [Measure.restrict_univ] using! hproduct
end CohnElkies
