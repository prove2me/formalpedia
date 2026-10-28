-- Prove2me | solution 2 for AvramDividend.Classical.chat12_barrierSupValue_eq_scale_ratio_of_eventual_exit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:19:57.432993+00:00
-- url     : https://prove2.me/submissions/cfddec69-017d-496e-9cf5-ddb759cd85ee

import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_of_stopped_renewal_bounds
import Theorems.Thm_AvramDividend_Classical_chat12_upper_eventual_renewal_of_exit_factor
import Theorems.Thm_AvramDividend_Classical_chat12_lower_eventual_renewal_of_exit_factor

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0)
    (hUpExit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε)))
    (hDownExit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a)) :
    barrierSupValue X a q =
      ENNReal.ofReal (W a / deriv W a) := by
  exact barrierSupValue_of_stopped_renewal_bounds X hX q hq W hW a ha hD hd
    (chat12_lower_eventual_renewal_of_exit_factor X hX q hq W hW a ha hD hd hDownExit)
    (chat12_upper_eventual_renewal_of_exit_factor X hX q hq W hW a ha hD hd hUpExit)
