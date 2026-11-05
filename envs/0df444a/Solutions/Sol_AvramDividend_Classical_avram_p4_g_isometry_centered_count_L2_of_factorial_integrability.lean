-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_centered_count_L2_of_factorial_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:41:41.701781+00:00
-- url     : https://prove2.me/submissions/42d45180-44ba-4e42-a6fe-6ac192dd7aa0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Second factorial integrability of an original count implies centred L², without a Poisson replacement. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (J : Ω → ℝ) (r : ℝ)
    (hJ : Integrable J P)
    (hFactorial : Integrable (fun ω => J ω * (J ω - 1)) P) :
    MemLp (fun ω => J ω - r) 2 P := by
  have hSquare : Integrable (fun ω => (J ω) ^ 2) P := by
    have hIdent : (fun ω : Ω => (J ω) ^ 2) =
        (fun ω : Ω => J ω * (J ω - 1)) + J := by
      funext ω
      simp only [Pi.add_apply]
      ring
    rw [hIdent]
    exact hFactorial.add hJ
  have hL2 : MemLp J 2 P :=
    (memLp_two_iff_integrable_sq hJ.aestronglyMeasurable).2 hSquare
  have hConst : MemLp (fun _ : Ω => r) 2 P := memLp_const r
  have hIdent : (fun ω : Ω => J ω - r) =
      J - (fun _ : Ω => r) := by
    funext ω
    simp only [Pi.sub_apply]
  rw [hIdent]
  exact hL2.sub hConst
