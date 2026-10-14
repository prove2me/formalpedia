-- Prove2me | solution 1 for DistCov.Indep.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T21:22:09.374261+00:00
-- url     : https://prove2.me/submissions/bfa3156e-97f4-43fe-be3c-aaaac40e2e04

import Definitions.Def_DistCov_Indep_Setting

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace DistCovCentered
open DistCov.Indep
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

lemma dist_integrable (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) (x : X) :
    Integrable (fun z => dist x z) μ := by
  obtain ⟨o,ho⟩ := h
  apply ((integrable_const (dist x o)).add ho).mono' (by fun_prop)
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Pi.add_apply] using dist_triangle x o z

lemma mean_nonneg (μ : Measure X) (x : X) : 0 ≤ meanDist μ x :=
  integral_nonneg (fun _ => dist_nonneg)

lemma mean_meas (μ : Measure X) [SFinite μ] : StronglyMeasurable (meanDist μ) := by
  have hd : StronglyMeasurable (fun p : X × X => dist p.1 p.2) :=
    (continuous_fst.dist continuous_snd).stronglyMeasurable
  exact hd.integral_prod_right'

lemma mean_bound (μ : Measure X) [IsProbabilityMeasure μ] (o : X)
    (ho : Integrable (fun z => dist o z) μ) (x : X) :
    meanDist μ x ≤ dist o x + ∫ z, dist o z ∂μ := by
  have hx := dist_integrable μ ⟨o,ho⟩ x
  unfold meanDist
  calc
    (∫ z, dist x z ∂μ) ≤ ∫ z, (dist o x + dist o z) ∂μ := by
      apply integral_mono hx ((integrable_const _).add ho)
      intro z
      simpa only [dist_comm o x, Pi.add_apply] using dist_triangle x o z
    _ = _ := by rw [integral_add (integrable_const _) ho]; simp

lemma mean_integrable (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) :
    Integrable (meanDist μ) μ := by
  obtain ⟨o,ho⟩ := h
  apply (ho.add (integrable_const (∫ z, dist o z ∂μ))).mono' (mean_meas μ).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mean_nonneg μ x), Pi.add_apply] using mean_bound μ o ho x

lemma distance_mean_bound (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ)
    (x y : X) : |dist x y - meanDist μ x| ≤ meanDist μ y := by
  have hx := dist_integrable μ h x
  have hy := dist_integrable μ h y
  have he : dist x y - meanDist μ x = ∫ z, (dist x y - dist x z) ∂μ := by
    rw [integral_sub (integrable_const _) hx]
    simp [meanDist]
  rw [he]
  calc
    |∫ z, (dist x y - dist x z) ∂μ| ≤ ∫ z, |dist x y - dist x z| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => dist x y - dist x z)
    _ ≤ meanDist μ y := by
      apply integral_mono ((integrable_const _).sub hx).abs hy
      intro z
      simpa only [dist_comm y x, dist_comm z x, Pi.sub_apply] using abs_dist_sub_le y z x

lemma centered_bound_right (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ)
    (x y : X) : |dcent μ x y| ≤ |D μ| + 2 * meanDist μ y := by
  have hy := mean_nonneg μ y
  have hd := distance_mean_bound μ h x y
  have he : dcent μ x y = (dist x y - meanDist μ x) + (D μ - meanDist μ y) := by
    unfold dcent
    ring
  rw [he]
  have hh := abs_add_le (dist x y - meanDist μ x) (D μ - meanDist μ y)
  have hh' := norm_sub_le (D μ) (meanDist μ y)
  simp only [Real.norm_eq_abs] at hh'
  rw [abs_of_nonneg hy] at hh'
  linarith

lemma centered_meas (μ : Measure X) [SFinite μ] :
    StronglyMeasurable (fun p : X × X => dcent μ p.1 p.2) := by
  unfold dcent
  exact (((continuous_fst.dist continuous_snd).stronglyMeasurable.sub
    ((mean_meas μ).comp_measurable measurable_fst)).sub
    ((mean_meas μ).comp_measurable measurable_snd)).add stronglyMeasurable_const

lemma centered_square_bound (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ)
    (x y : X) : (dcent μ x y)^2 ≤
      (|D μ| + 2 * meanDist μ x) * (|D μ| + 2 * meanDist μ y) := by
  have hr := centered_bound_right μ h x y
  have hl := centered_bound_right μ h y x
  have hs : dcent μ y x = dcent μ x y := by unfold dcent; rw [dist_comm y x]; ring
  rw [hs] at hl
  have hx := mean_nonneg μ x
  have hm := mul_le_mul hl hr (abs_nonneg _) (by positivity)
  simpa only [← sq, sq_abs] using hm
end DistCovCentered

open DistCov.Indep
 theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) :
    MemLp (fun p : X × X => dcent μ p.1 p.2) 2 (μ.prod μ) := by
  apply (memLp_two_iff_integrable_sq (DistCovCentered.centered_meas μ).aestronglyMeasurable).mpr
  have hb : Integrable (fun x => |D μ| + 2 * meanDist μ x) μ :=
    (integrable_const _).add ((DistCovCentered.mean_integrable μ h).const_mul 2)
  apply (hb.mul_prod hb).mono' ((DistCovCentered.centered_meas μ).pow 2).aestronglyMeasurable
  filter_upwards [] with p
  change |dcent μ p.1 p.2 ^ 2| ≤ _
  rw [abs_of_nonneg (sq_nonneg _)]
  exact DistCovCentered.centered_square_bound μ h p.1 p.2
#print axioms solution
