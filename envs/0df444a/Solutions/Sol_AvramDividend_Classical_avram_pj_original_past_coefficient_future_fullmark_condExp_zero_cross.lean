-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_past_coefficient_future_fullmark_condExp_zero_cross
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:04:02.660221+00:00
-- url     : https://prove2.me/submissions/a4c57bb6-e317-4153-87f8-bbf165c69619

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
open MeasureTheory Set Filter Topology
noncomputable section

/-- A past strongly measurable integrable weighted coefficient is
orthogonal to a future centred compensated marked increment whenever
its conditional expectation vanishes in the true original filtration. -/
theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (U V : Ω → ℝ)
    (hU : StronglyMeasurable[m] U)
    (hUI : Integrable (fun ω => U ω * V ω) P)
    (hVI : Integrable V P)
    (hVcentred : P[V | m] =ᵐ[P] (fun _ => (0 : ℝ))) :
    (∫ ω, U ω * V ω ∂P) = 0 := by
  have hPull : P[(fun ω => U ω * V ω) | m] =ᵐ[P]
      (fun ω => U ω * P[V | m] ω) := by
    exact condExp_mul_of_aestronglyMeasurable_left
      hU.aestronglyMeasurable hUI hVI
  calc
    (∫ ω, U ω * V ω ∂P) =
        ∫ ω, P[(fun ω => U ω * V ω) | m] ω ∂P := by
          symm
          exact integral_condExp hm
    _ = ∫ ω, U ω * P[V | m] ω ∂P :=
        integral_congr_ae hPull
    _ = ∫ ω, (0 : ℝ) ∂P := by
      apply integral_congr_ae
      filter_upwards [hVcentred] with ω hw
      simp [hw]
    _ = 0 := by simp
