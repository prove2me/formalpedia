-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:07:31.826506+00:00
-- url     : https://prove2.me/submissions/7af5caae-d308-42e2-90d9-690d1499d3f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_exp_clock_supremum_full_law_ws01d
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_scalar_rate_gap_mgf
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p lam β : ℝ) (hφ : 0 < φ) (hq : 0 < q)
    (hroot : X.ψ φ = q) (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p) (hβlam : β < lam) :
    ENNReal.ofReal (lam - β) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp (β * runningSup X (Real.toNNReal z.2) z.1))
        ∂((P.prod (ProbabilityTheory.expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) =
    ENNReal.ofReal lam := by
  let μ : Measure (Ω × ℝ) :=
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ))))
  let S : Ω × ℝ → ℝ :=
    fun z => runningSup X (Real.toNNReal z.2) z.1
  have hSMeas : Measurable S :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hExpMeas :
      Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (β * t))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))
  have hLaw : Measure.map S μ = expMeasure lam := by
    simpa [μ, S, hroot] using
      (esscher_positive_root_exp_clock_supremum_full_law_ws01d
        X φ q hφ hq hroot p hp lam hlam hlamroot)
  have hMap :
      (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (β * S z)) ∂μ) =
      (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (β * t)) ∂expMeasure lam) := by
    rw [← hLaw]
    exact (lintegral_map hExpMeas hSMeas).symm
  have hPDFMeas : Measurable (exponentialPDF lam) :=
    (measurable_exponentialPDFReal lam).ennreal_ofReal
  have hPDF :
      (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (β * t)) ∂expMeasure lam) =
      (∫⁻ t : ℝ, exponentialPDF lam t *
        ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * β)) ∂volume) := by
    calc
      _ = (∫⁻ t : ℝ, exponentialPDF lam t *
          ENNReal.ofReal (Real.exp (β * t)) ∂volume) := by
            change (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (β * t))
              ∂(volume.withDensity (exponentialPDF lam))) = _
            rw [lintegral_withDensity_eq_lintegral_mul
              volume hPDFMeas hExpMeas]
            rfl
      _ = _ := by
        apply lintegral_congr
        intro t
        by_cases ht : 0 ≤ t
        · rw [Real.coe_toNNReal t ht]
          ring
        · have hn : t < 0 := lt_of_not_ge ht
          simp [exponentialPDF_of_neg hn]
  change ENNReal.ofReal (lam - β) *
    (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (β * S z)) ∂μ) =
    ENNReal.ofReal lam
  rw [hMap, hPDF]
  exact avram_ws01e_b_exp_clock_scalar_rate_gap_mgf lam β hlam hβlam
