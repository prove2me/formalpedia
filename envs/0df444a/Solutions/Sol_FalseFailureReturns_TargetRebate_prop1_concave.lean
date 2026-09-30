-- Prove2me | solution 1 for FalseFailureReturns.TargetRebate.prop1_concave
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:28:06.727635+00:00
-- url     : https://prove2.me/submissions/51450c15-c4bd-411e-91cd-1e2cf37b32ed

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model
open MeasureTheory Set Filter FalseFailureReturns.TargetRebate

private theorem shortfall_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (hn : μ (Iio 0) = 0) : Integrable (fun x => max (T-x) 0) μ := by
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by simpa only [ae_iff, not_le, Iio_def] using hn
  apply Integrable.of_bound (f := fun x : ℝ => max (T-x) 0) (by fun_prop) (max T 0)
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le_max (by linarith) le_rfl

private theorem shortfall_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ)
    (hT : 0 ≤ T) (hn : μ (Iio 0) = 0) :
    (∫ x, max (T-x) 0 ∂μ) = ∫ s in Ioc 0 T, μ.real (Iic (T-s)) := by
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by simpa only [ae_iff, not_le, Iio_def] using hn
  rw [(shortfall_integrable μ T hn).integral_eq_integral_Ioc_meas_le
    (Eventually.of_forall (fun x => le_max_right _ _)) (M := T) (by
      filter_upwards [hae] with x hx
      exact max_le (by linarith) hT)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  apply congrArg (fun A : Set ℝ => μ.real A)
  ext x
  simp only [mem_setOf_eq, mem_Iic]
  constructor
  · intro h
    rcases le_max_iff.mp h with h | h
    · linarith
    · linarith [hs.1]
  · intro h
    exact le_trans (by linarith) (le_max_left _ _)

private theorem cdf_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) :
    IntegrableOn (fun s => μ.real (Iic (T-s))) (Ioc 0 T) := by
  have hm : Antitone (fun s => μ.real (Iic (T-s))) := by
    intro x y hxy
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (Iic_subset_Iic.mpr (by linarith))
  apply Integrable.of_bound hm.measurable.aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact measureReal_le_one

private theorem concave_shortfall (μ : ℝ → Measure ℝ) (T : ℝ)
    (hp : ∀ ρ ∈ Ici (1:ℝ), IsProbabilityMeasure (μ ρ))
    (hn : ∀ ρ ∈ Ici (1:ℝ), μ ρ (Iio 0) = 0)
    (hF : ∀ x ∈ Icc 0 T, ConcaveOn ℝ (Ici 1) (fun ρ => (μ ρ).real (Iic x))) :
    ConcaveOn ℝ (Ici 1) (fun ρ => ∫ x, max (T-x) 0 ∂(μ ρ)) := by
  by_cases hT : 0 ≤ T
  · have hc : ConcaveOn ℝ (Ici 1) (fun ρ => ∫ s in Ioc 0 T, (μ ρ).real (Iic (T-s))) := by
      apply integral_concaveOn_of_integrand_ae (convex_Ici _)
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
        exact hF _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
      · intro ρ hρ
        letI := hp ρ hρ
        exact cdf_integrable _ _
    apply hc.congr
    intro ρ hρ
    letI := hp ρ hρ
    exact (shortfall_cdf _ T hT (hn ρ hρ)).symm
  · apply (concaveOn_const (0:ℝ) (convex_Ici (1:ℝ))).congr
    intro ρ hρ
    letI := hp ρ hρ
    have hae : ∀ᵐ x ∂(μ ρ), 0 ≤ x := by simpa only [ae_iff, not_le, Iio_def] using hn ρ hρ
    symm
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with x hx
    exact max_eq_right (by linarith)

private theorem concave_profit (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    ConcaveOn ℝ (Set.Ioi 0) (fun x : ℝ => c*(1-1/x)-a*x^2/2) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy u v hu hv huv
  simp only [Set.mem_Ioi] at hx hy
  simp only [smul_eq_mul]
  have ht : 0 < u*x+v*y := by
    have hmin : 0 < min x y := lt_min hx hy
    have hxx := mul_le_mul_of_nonneg_left (min_le_left x y) hu
    have hyy := mul_le_mul_of_nonneg_left (min_le_right x y) hv
    nlinarith
  have he : (c*(1-1/(u*x+v*y))-a*(u*x+v*y)^2/2) -
      (u*(c*(1-1/x)-a*x^2/2)+v*(c*(1-1/y)-a*y^2/2)) =
      u*v*(x-y)^2*(c/(x*y*(u*x+v*y))+a/2) := by
    have hv' : v = 1-u := by linarith
    rw [hv'] at ht ⊢
    field_simp
    ring
  apply sub_nonneg.mp
  rw [he]
  positivity

theorem solution (P : Params) (μ : ℝ → Measure ℝ) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr) (hu : 0 ≤ u)
    (hprob : ∀ ρ ∈ Set.Ici (1 : ℝ), IsProbabilityMeasure (μ ρ))
    (hnonneg : ∀ ρ ∈ Set.Ici (1 : ℝ), μ ρ (Set.Iio 0) = 0)
    (hF_smooth : ∀ x ∈ Set.Icc 0 T,
      ContDiffOn ℝ 2 (fun ρ => (μ ρ (Set.Iic x)).toReal) (Set.Ici 1))
    (hF_second : ∀ x ∈ Set.Icc 0 T, ∀ ρ ∈ Set.Ioi (1 : ℝ),
      deriv (deriv (fun ρ => (μ ρ (Set.Iic x)).toReal)) ρ ≤ 0) :
    ConcaveOn ℝ (Set.Ici 1)
      (fun ρ => u * ∫ x, max (T - x) 0 ∂(μ ρ) - P.a * ρ ^ 2 / 2 + P.Rr * P.β * (1 - 1 / ρ)) := by
  have hshort := concave_shortfall μ T hprob hnonneg (fun x hx => ?_)
  case refine_1 =>
    apply concaveOn_of_deriv2_nonpos (convex_Ici _) (hF_smooth x hx).continuousOn
    · exact (hF_smooth x hx).differentiableOn (by norm_num) |>.mono interior_subset
    · exact ((hF_smooth x hx).mono interior_subset |>.deriv_of_isOpen isOpen_interior (m := 1) (by norm_num)).differentiableOn (by norm_num)
    · simpa only [interior_Ici, Function.iterate_succ_apply, Function.iterate_zero_apply] using hF_second x hx
  have hbase := (concave_profit P.a (P.Rr*P.β) ha.le (mul_nonneg hR.le hβ.le)).subset
    (show Ici (1:ℝ) ⊆ Ioi 0 from fun x hx => by simp only [mem_Ici, mem_Ioi] at *; linarith) (convex_Ici _)
  apply ((ConcaveOn.smul hu hshort).add hbase).congr
  intro ρ hρ
  simp only [Pi.add_apply, smul_eq_mul]
  ring
