-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_bv_drawdown_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:43:40.896987+00:00
-- url     : https://prove2.me/submissions/27fb55ca-e34d-455f-981e-67bae5d03488

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_wh_ratio_large_frequency
import Theorems.Thm_AvramDividend_Classical_nonnegative_laplace_transform_atom_zero_limit_nat
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
import Theorems.Thm_AvramDividend_Classical_bv_exponent_gap_div_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

/-- Genuine original Exp(R) drawdown zero-atom law for BV Lévy paths.
The probability is R/(Φ(R)*d); no compound-Poisson assumption is made. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hstanding : X.Standing) (hBV : X.BoundedVariation)
    (R φ : ℝ) (hR : 0 < R) (hφ : 0 < φ)
    (hroot : X.ψ φ = R) :
    (∫ z : Ω × ℝ,
      if runningSup X z.2.toNNReal z.1 -
           X.X z.2.toNNReal z.1 = 0 then (1 : ℝ) else 0
      ∂(P.prod (expMeasure R))) =
    R / (φ * X.drift) := by
  letI : IsProbabilityMeasure P := X.isProbability
  letI : IsProbabilityMeasure (expMeasure R) :=
    isProbabilityMeasure_expMeasure hR
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure R)
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  let D : Ω × ℝ → ℝ := fun z =>
    runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1
  have hmD : Measurable D :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
  have hD : ∀ᵐ z ∂μ, 0 ≤ D z := Filter.Eventually.of_forall (by
    intro z
    exact sub_nonneg.mpr
      ((runningSup_monotone_and_path_le X z.1).2 z.2.toNNReal))
  have hAtom :=
    nonnegative_laplace_transform_atom_zero_limit_nat μ D hmD hD
  have hd : 0 < X.drift := (bv_standing_drift_pos X hstanding hBV).1
  have hSlope := bv_exponent_gap_div_tendsto_zero X hBV
  have hRatioReal :=
    avram_ws01b_wh_ratio_large_frequency X.ψ R φ X.drift hφ hd hSlope
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hRatio : Tendsto
      (fun n : ℕ => (R / φ) * ((φ - (n : ℝ)) / (R - X.ψ (n : ℝ))))
      atTop (𝓝 (R / (φ * X.drift))) :=
    hRatioReal.comp hNat
  obtain ⟨m, hm, hFactor⟩ :=
    avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
      X R hR φ hφ hroot
  have hEvent : ∀ᶠ n : ℕ in atTop, φ < (n : ℝ) :=
    hNat.eventually (eventually_gt_atTop φ)
  have hAgree : (fun n : ℕ =>
      ∫ z, Real.exp ((n : ℝ) * (-D z)) ∂μ) =ᶠ[atTop]
      (fun n : ℕ => (R / φ) * ((φ - (n : ℝ)) /
        (R - X.ψ (n : ℝ)))) := by
    filter_upwards [hEvent] with n hn
    have hnpos : (0 : ℝ) < n := lt_trans hφ hn
    have hnne : (n : ℝ) ≠ φ := ne_of_gt hn
    have h := hFactor.2 (n : ℝ) hnpos
    simpa [μ, D, mgf, if_neg hnne] using h
  have hRatioIntegral : Tendsto
      (fun n : ℕ => ∫ z, Real.exp ((n : ℝ) * (-D z)) ∂μ)
      atTop (𝓝 (R / (φ * X.drift))) :=
    hRatio.congr' hAgree.symm
  have hEq := tendsto_nhds_unique hAtom hRatioIntegral
  simpa only [μ, D] using hEq
