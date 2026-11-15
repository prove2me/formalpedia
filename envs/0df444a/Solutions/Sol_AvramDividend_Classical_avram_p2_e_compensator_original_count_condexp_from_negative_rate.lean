-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_count_condexp_from_negative_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:59:49.261969+00:00
-- url     : https://prove2.me/submissions/e8aef4bd-b1db-4c63-b481-cb6f85a044dc

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_count_condexp_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_borel_rate_of_negative_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Given the original process's unconditional marked Levy rate, the
conditional expected marked count at its actual past filtration is that
deterministic rate. This uses original future/past independence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hNegativeRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B ∩ Iio (0 : ℝ))) :
    (condExp (𝓕 s) P (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)) =ᵐ[P]
      (fun _ : Ω => (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) := by
  have hRate := avram_p2_e_compensator_original_borel_rate_of_negative_rate
    X s t hst B hB hNegativeRate
  exact avram_p2_e_compensator_original_count_condexp_rate
    X s t hst B hB hν hRate
