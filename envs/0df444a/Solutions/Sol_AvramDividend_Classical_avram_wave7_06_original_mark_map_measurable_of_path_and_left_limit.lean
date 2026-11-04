-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_mark_map_measurable_of_path_and_left_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:16:47.700544+00:00
-- url     : https://prove2.me/submissions/445999a1-d807-4669-9290-51a98b8e4e9d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact original-X time/mark map is Borel under path-and-left-limit measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hPath : Measurable (fun t : ℝ≥0 => X.X t ω))
    (hLeft : Measurable (fun t : ℝ≥0 =>
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)) :
    Measurable (fun u : ℝ≥0 => (u,
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
  exact measurable_id.prodMk (hPath.sub hLeft)
