-- Prove2me | solution 1 for AvramDividend.Classical.avram_a55_stationary_increment_witness_implies_true_identdistrib_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:16:53.457194+00:00
-- url     : https://prove2.me/submissions/f1629f11-4f2c-490a-af05-054a0e545e3a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- A stationary increment map witness at every horizon implies the precise source law of increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (G : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t, Measurable (G t))
    (hZero : ∀ ω, G 0 ω = 0)
    (hShift : ∀ T : ℝ≥0, ∃ Z : Ω → ℝ, Measurable Z ∧
      ∀ s : ℝ≥0,
        Measure.map (fun ω => G (s + T) ω - G s ω) P =
          Measure.map Z P) :
    ∀ s t : ℝ≥0, s ≤ t →
      IdentDistrib (fun ω => G t ω - G s ω) (G (t - s)) P P := by
  intro s t hst
  obtain ⟨Z, hZ, hLaw⟩ := hShift (t - s)
  have hRef : Measure.map (G (t - s)) P = Measure.map Z P := by
    convert hLaw 0 using 1
    · congr 1
      funext ω
      simp [hZero]
  have hMain :
      Measure.map (fun ω => G t ω - G s ω) P = Measure.map Z P := by
    convert hLaw s using 1
    congr 1
    funext ω
    rw [add_tsub_cancel_of_le hst]
  exact ⟨((hMeas t).sub (hMeas s)).aemeasurable,
    (hMeas (t - s)).aemeasurable, hMain.trans hRef.symm⟩
