-- Prove2me | solution 1 for DistCov.Indep.proposition_3_5
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T22:43:18.424483+00:00
-- url     : https://prove2.me/submissions/a4a3757e-d4bc-4c50-90c2-5585ae060933

import Theorems.Thm_DistCov_Indep_eq_3_4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace DistCovCenteredEmb
open DistCov.Indep
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

lemma dist_integrable (μ : Measure X) [IsProbabilityMeasure μ]
    (h : FiniteFirstMoment μ) (x : X) : Integrable (fun z => dist x z) μ := by
  obtain ⟨o,ho⟩ := h
  apply ((integrable_const (dist x o)).add ho).mono' (by fun_prop)
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Pi.add_apply] using
    dist_triangle x o z

lemma dist_prod_integrable (μ : Measure X) [IsProbabilityMeasure μ]
    (h : FiniteFirstMoment μ) :
    Integrable (fun p : X × X => dist p.1 p.2) (μ.prod μ) := by
  obtain ⟨o,ho⟩ := h
  apply ((ho.comp_fst μ).add (ho.comp_snd μ)).mono' (by fun_prop)
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Pi.add_apply,
    dist_comm o p.1] using dist_triangle p.1 o p.2

lemma mean_integrable (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) :
    Integrable (meanDist μ) μ := by
  exact (dist_prod_integrable μ h).integral_prod_left

lemma mean_integral (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) :
    (∫ x, meanDist μ x ∂μ) = D μ := by
  exact (integral_prod _ (dist_prod_integrable μ h)).symm

lemma energy_dirac_right (μ : Measure X) [SFinite μ] (x : X) :
    energy μ (Measure.dirac x) = meanDist μ x := by
  unfold energy meanDist
  rw [Measure.prod_dirac, integral_map (by fun_prop) (by fun_prop)]
  simp only [dist_comm x]

lemma mean_identity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) (x : X) :
    meanDist μ x = ‖ϕ x - bary ϕ μ‖^2 + D μ / 2 := by
  have hx : FiniteFirstMoment (Measure.dirac x) := ⟨x, integrable_dirac (by simp)⟩
  have he : Ddiff μ (Measure.dirac x) = D μ - 2 * meanDist μ x := by
    unfold Ddiff D
    rw [energy_dirac_right]
    simp [energy, Measure.dirac_prod_dirac]
  have hb : bary ϕ (Measure.dirac x) = ϕ x := by simp [bary]
  have hi := eq_3_4 ϕ hϕ μ (Measure.dirac x) h hx (by simp)
  rw [he,hb,norm_sub_rev] at hi
  linarith

lemma centered_norm_sq_integrable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (ϕ : X → H)
    (hϕ : IsNegTypeEmbedding ϕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (h : FiniteFirstMoment μ) : Integrable (fun x => ‖ϕ x - bary ϕ μ‖^2) μ := by
  apply ((mean_integrable μ h).sub (integrable_const (D μ / 2))).congr
  filter_upwards [] with x
  change meanDist μ x - D μ / 2 = ‖ϕ x - bary ϕ μ‖^2
  linarith [mean_identity ϕ hϕ μ h x]

lemma energy_variance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) :
    D μ = 2 * ∫ x, ‖ϕ x - bary ϕ μ‖^2 ∂μ := by
  have hi : (∫ x, meanDist μ x ∂μ) =
      (∫ x, ‖ϕ x - bary ϕ μ‖^2 ∂μ) + D μ / 2 := by
    calc
      _ = ∫ x, (‖ϕ x - bary ϕ μ‖^2 + D μ / 2) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (mean_identity ϕ hϕ μ h)
      _ = _ := by
        rw [integral_add (centered_norm_sq_integrable ϕ hϕ μ h) (integrable_const _)]
        simp
  rw [mean_integral μ h] at hi
  linarith

lemma centered_identity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) (x y : X) :
    dcent μ x y = -2 * inner ℝ (ϕ x - bary ϕ μ) (ϕ y - bary ϕ μ) := by
  unfold dcent
  rw [mean_identity ϕ hϕ μ h x, mean_identity ϕ hϕ μ h y, hϕ x y]
  have he : ϕ x - ϕ y = (ϕ x - bary ϕ μ) - (ϕ y - bary ϕ μ) := by abel
  rw [he, norm_sub_sq_real]
  ring

end DistCovCenteredEmb

open DistCov.Indep
theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) :
    (∀ x, meanDist μ x = ‖ϕ x - bary ϕ μ‖^2 + D μ / 2) ∧
    D μ = 2 * ∫ x, ‖ϕ x - bary ϕ μ‖^2 ∂μ ∧
    (∀ x x', dcent μ x x' = -2 * ⟪ϕ x - bary ϕ μ, ϕ x' - bary ϕ μ⟫_ℝ) := by
  exact ⟨DistCovCenteredEmb.mean_identity ϕ hϕ μ h,
    DistCovCenteredEmb.energy_variance ϕ hϕ μ h,
    DistCovCenteredEmb.centered_identity ϕ hϕ μ h⟩

#print axioms solution
