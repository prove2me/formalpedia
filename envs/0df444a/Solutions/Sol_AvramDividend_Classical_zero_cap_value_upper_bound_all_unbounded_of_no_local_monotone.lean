-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_value_upper_bound_all_unbounded_of_no_local_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:44:13.788505+00:00
-- url     : https://prove2.me/submissions/c54b3519-93e0-4c92-bfd2-e8df11f99b2d

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_no_local_monotone_path
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_all_unbounded_of_instant_ruin
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Unbounded-variation zero-cap verification needs only the a.s. exclusion
of nondecreasing sample paths on every initial time interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (hNoMono : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ¬ MonotoneOn (fun t : ℝ≥0 => X.X t ω) (Icc 0 ε)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  have hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0 :=
    hNoMono.mono (fun ω hω =>
      barrierRuinTime_zero_of_no_local_monotone_path X ω hω)
  exact zero_cap_value_upper_bound_all_unbounded_of_instant_ruin
    X hX q hq W hW hnbv hRuin
