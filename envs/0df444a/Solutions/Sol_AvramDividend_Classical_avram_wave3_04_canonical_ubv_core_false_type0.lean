-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_canonical_ubv_core_false_type0
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:50:04.363751+00:00
-- url     : https://prove2.me/submissions/cf2be3bc-7d12-4094-8347-7a2106a55040

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_concrete_gaussian_levy_source_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_drifted_unit_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_core_missing_boundary_counterexample
import Theorems.Thm_AvramDividend_Classical_gaussian_cutoff_canonical_analytic_hypotheses
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_reserve_negative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Formal negation of the canonical UBV stochastic core, using a genuine
    Gaussian source process and a finite cap equal to one. -/
theorem solution :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ}
        (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
        (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
        (w : ℝ → ℝ) (C : ℝ≥0∞)
        (hw_cont : ContinuousOn w (Ici 0))
        (hw_neg : ∀ y < 0, w y = 0)
        (hw_smooth : ContDiffOn ℝ 2 w
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
        (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
          X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
        (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
          1 ≤ deriv w y)
        (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
        (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
        (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
          (t : ℝ≥0∞) < ruinTime X x D ω →
          0 ≤ w (riskProcess X x D t ω))
        (hjump : ∀ ω (t : ℝ≥0),
          (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
          rightLimit D t ω - D t ω ≤
            w (riskProcess X x D t ω) -
              w (riskProcess X x D t ω -
                (rightLimit D t ω - D t ω)))
        (T : ℝ) (hT : 0 ≤ T),
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) := by
  intro hall
  obtain ⟨𝓕, X, hXfun, hc, hσ, hν⟩ :=
    avram_wave3_04_concrete_gaussian_levy_source_witness
  have hI : Integrable (X.X 1) gaussianLimit := by
    rw [hXfun]
    exact avram_wave3_04_gaussian_drifted_unit_integrable
  let w : ℝ → ℝ := fun z => if z < 0 then 0 else z - 1
  let D : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
    fun s ω => barrierStrategy X (1 : ℝ) 0 s ω + (s : ℝ)
  have htop := avram_wave3_04_gaussian_core_missing_boundary_counterexample
    X (by rw [hσ]; norm_num) hI hν hc
    (1 : ℝ) (by norm_num) (by norm_num) (0 : ℝ) (by norm_num)
  dsimp only at htop
  rcases htop with ⟨_, _, hDtop, hnonneg, hjump, hbad⟩
  obtain ⟨hstanding, hBV, hcont, hneg, hsmooth, hgen, hgrad⟩ :=
    gaussian_cutoff_canonical_analytic_hypotheses
      X (by rw [hσ]; norm_num) hI hν hc (ENNReal.ofReal (1 : ℝ))
  have hDcap : IsAdmissibleLe X (1 : ℝ)
      (ENNReal.ofReal (1 : ℝ)) D := by
    rcases hDtop with ⟨hD, _⟩
    refine ⟨hD, ?_⟩
    intro ω t ht
    have hneg := barrierStrategy_plus_linear_drain_reserve_negative
      X (1 : ℝ) (by norm_num) ω t ht
    rw [ENNReal.ofReal_eq_zero.mpr (le_of_lt hneg)]
    exact bot_le
  apply hbad
  exact (@hall (ℝ≥0 → ℝ) inferInstance gaussianLimit 𝓕
    X hstanding hBV (1 : ℝ) (by norm_num) w
    (ENNReal.ofReal (1 : ℝ)) hcont hneg hsmooth hgen hgrad
    (1 : ℝ) (le_refl _) D hDcap hnonneg hjump
    (0 : ℝ) (by norm_num))