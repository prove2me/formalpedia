-- Prove2me | solution 7 for AvramDividend.Classical.vcstar_deriv_eq_one_at_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:28:03.104684+00:00
-- url     : https://prove2.me/submissions/09526686-b845-4ab3-a75e-a1c5798caaae

import Theorems.Thm_AvramDividend_Classical_vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn
import Theorems.Thm_AvramDividend_Classical_barrierValue_deriv_one_of_differentiableAt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Smooth fit from either process regularity or the given positive-time C2 regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have hregular (hr : 0 < X.σ ∨ X.BoundedVariation) :
      deriv (vcstar W) (cstar W).toReal = 1 := by
    have hd : DifferentiableAt ℝ (vcstar W) (cstar W).toReal :=
      vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
        X hX q hq W hW hc hcpos hr
    have hn : 0 ≤ (cstar W).toReal := ENNReal.toReal_nonneg
    have hbarrier : DifferentiableAt ℝ
        (barrierValue W (cstar W).toReal) (cstar W).toReal := by
      simpa only [vcstar] using hd
    have hderiv := barrierValue_deriv_one_of_differentiableAt
      W (cstar W).toReal hn hbarrier
    simpa only [vcstar] using hderiv
  rcases h_smooth with hgauss | hBV | hc2
  · exact hregular (Or.inl hgauss)
  · exact hregular (Or.inr hBV)
  · exact vcstar_deriv_one_of_contDiffOn W hc hcpos hc2
