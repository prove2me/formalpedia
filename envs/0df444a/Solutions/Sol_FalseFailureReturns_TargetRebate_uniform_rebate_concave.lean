-- Prove2me | solution 1 for FalseFailureReturns.TargetRebate.uniform_rebate_concave
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:30:47.477343+00:00
-- url     : https://prove2.me/submissions/7c6b5768-640d-4565-b1d1-43bbf1625b77

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model
import Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate
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

private theorem uniform_cdf (β ρ x : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (hx : 0 ≤ x) :
    (uniformLaw β ρ).real (Iic x) = min (x*ρ/(2*β)) 1 := by
  have hB : 0 < 2*β/ρ := by positivity
  have hi : Icc 0 (2*β/ρ) ∩ Iic x = Icc 0 (min (2*β/ρ) x) := by
    ext z
    simp only [mem_inter_iff, mem_Icc, mem_Iic, le_min_iff]
    tauto
  unfold Measure.real uniformLaw
  rw [ProbabilityTheory.cond_apply measurableSet_Icc, hi]
  simp only [Real.volume_Icc, sub_zero, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (le_of_lt hB), ENNReal.toReal_ofReal (le_min hB.le hx)]
  by_cases h : x ≤ 2*β/ρ
  · rw [min_eq_right h, min_eq_left ((div_le_one (by positivity)).mpr ((le_div_iff₀ hρ).mp h))]
    field_simp
  · have h' : 2*β/ρ ≤ x := le_of_not_ge h
    rw [min_eq_left h', min_eq_right ((one_le_div (by positivity)).mpr ((div_le_iff₀ hρ).mp h'))]
    exact inv_mul_cancel₀ (ne_of_gt hB)

theorem solution (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr) (hu : 0 ≤ u) :
    ConcaveOn ℝ (Set.Ici 1) (rebateRetailerProfit P T u) := by
  have hp : ∀ ρ ∈ Ici (1:ℝ), IsProbabilityMeasure (uniformLaw P.β ρ) := by
    intro ρ hρ
    have hρ' : 0 < ρ := by simp only [mem_Ici] at hρ; linarith
    apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    · simp only [Real.volume_Icc, sub_zero, ne_eq, ENNReal.ofReal_eq_zero]
      exact not_le.mpr (by positivity)
    · simp
  have hn : ∀ ρ ∈ Ici (1:ℝ), uniformLaw P.β ρ (Iio 0) = 0 := by
    intro ρ hρ
    unfold uniformLaw
    rw [ProbabilityTheory.cond_apply measurableSet_Icc]
    have hi : Icc 0 (2*P.β/ρ) ∩ Iio 0 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      linarith
    simp [hi]
  have hF : ∀ x ∈ Icc 0 T, ConcaveOn ℝ (Ici 1) (fun ρ => (uniformLaw P.β ρ).real (Iic x)) := by
    intro x hx
    have hl : ConcaveOn ℝ (Ici 1) (fun ρ : ℝ => x*ρ/(2*P.β)) := by
      refine ⟨convex_Ici _, ?_⟩
      intro a ha b hb v w hv hw hvw
      simp only [smul_eq_mul]
      apply le_of_eq
      ring
    apply (hl.inf (concaveOn_const 1 (convex_Ici _))).congr
    intro ρ hρ
    exact (uniform_cdf P.β ρ x hβ (by simp only [mem_Ici] at hρ; linarith) hx.1).symm
  have hshort := concave_shortfall (uniformLaw P.β) T hp hn hF
  have hbase := (concave_profit P.a (P.Rr*P.β) ha.le (mul_nonneg hR.le hβ.le)).subset
    (show Ici (1:ℝ) ⊆ Ioi 0 from fun x hx => by simp only [mem_Ici, mem_Ioi] at *; linarith) (convex_Ici _)
  apply ((ConcaveOn.smul hu hshort).add hbase).congr
  intro ρ hρ
  simp only [Pi.add_apply, smul_eq_mul, rebateRetailerProfit, expShortfall]
  ring
