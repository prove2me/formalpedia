-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_stopped_renewal_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:52:20.293514+00:00
-- url     : https://prove2.me/submissions/542422a3-a5b9-43f4-86f5-5085863153c0

import Theorems.Thm_AvramDividend_Classical_stoppedFirstRecord_lower_geometric_budgets
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_left_scale_quotient_of_record_budgets
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_deriv_nonneg
import Theorems.Thm_AvramDividend_Classical_hasDerivAt_pos_eventually_backward_scale_gap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
        barrierSupValue X a q := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hderiv : 0 ≤ deriv W a :=
    scaleFunction_deriv_nonneg X q W hW a ha
  have hdpos : 0 < deriv W a := lt_of_le_of_ne hderiv (Ne.symm hd)
  have hgap : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < W a - W (a - ε) :=
    hasDerivAt_pos_eventually_backward_scale_gap W a (deriv W a) hD hdpos
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < a := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds ha)
  have hpositive : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  filter_upwards [hgap, hsmall, hpositive] with ε hgapε hεa hε
  have hWleft : 0 ≤ W (a - ε) :=
    hW.2.1 (a - ε) (by linarith)
  have hWinc : W (a - ε) < W a := by linarith
  obtain ⟨w, hw, hbudget, hstep⟩ :=
    stoppedFirstRecord_lower_geometric_budgets
      X hX q hq W hW a ε ha hε hεa hWa hWleft hWinc
  exact barrierSupValue_ge_left_scale_quotient_of_record_budgets
    X W a q ε (le_of_lt hε) hWa hWleft hWinc w hw hbudget hstep
