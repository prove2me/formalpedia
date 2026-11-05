-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_HJB_generator_continuity_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:48:28.715475+00:00
-- url     : https://prove2.me/submissions/2916bd81-aa11-4581-92fc-f7504bc8bcc0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(w : ℝ → ℝ) (q a b : ℝ)
(hwd : ContinuousOn (deriv w) (Set.Icc a b))
(hw : ContinuousOn w (Set.Icc a b))
(hν : ContinuousOn (fun y : ℝ => ∫ z in Set.Iio (0 : ℝ), w (y + z) - w y ∂X.ν) (Set.Icc a b)) :
ContinuousOn (fun y : ℝ => X.drift * deriv w y +
 (∫ z in Set.Iio (0 : ℝ), w (y + z) - w y ∂X.ν) - q * w y) (Set.Icc a b) := by
  exact ((continuousOn_const.mul hwd).add hν).sub (continuousOn_const.mul hw)
